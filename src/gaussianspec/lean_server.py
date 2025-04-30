from __future__ import annotations
import asyncio
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List

import httpx

try:
    from morphcloud.api import MorphCloudClient, console, InstanceStatus  # type: ignore
except ModuleNotFoundError:  # pragma: no cover – soft dependency
    MorphCloudClient = None  # type: ignore
    console = None  # type: ignore


PANTOGRAPH_PORT = 5326


# -----------------------------------------------------------------------------
# LeanServerClient – thin HTTP wrapper around the Pantograph FastAPI server
# -----------------------------------------------------------------------------


@dataclass(slots=True)
class LeanServerClient:
    """Async HTTP client for interacting with a Pantograph Lean server.

    Parameters
    ----------
    base_url : str
        Root URL of the running Pantograph server, *without* trailing slash.
    timeout : float, default 30.0
        Default request timeout in seconds.
    """

    base_url: str
    timeout: float = 30.0
    _client: httpx.AsyncClient | None = None

    # ------------------------------ lifecycle ------------------------------ #

    async def __aenter__(self):
        self._client = httpx.AsyncClient(base_url=self.base_url, timeout=self.timeout)
        return self

    async def __aexit__(self, exc_type, exc, tb):
        if self._client is not None:
            await self._client.aclose()
            self._client = None

    # ------------------------------ helpers ------------------------------ #

    def _ensure_client(self) -> httpx.AsyncClient:
        if self._client is None:
            raise RuntimeError(
                "LeanServerClient must be used inside an async context manager (async with …)"
            )
        return self._client

    # ------------------------------ endpoints ------------------------------ #

    async def goal_start(self, term: str) -> Dict[str, Any]:
        """Start a new goal state with *term*. Returns the server JSON payload."""
        cl = self._ensure_client()
        resp = await cl.post("/goal_start", json={"term": term})
        resp.raise_for_status()
        return resp.json()

    async def goal_tactic(
        self, handle: str, goal_id: int, tactic: str
    ) -> Dict[str, Any]:
        cl = self._ensure_client()
        resp = await cl.post(
            "/goal_tactic",
            json={"handle": handle, "goal_id": goal_id, "tactic": tactic},
        )
        resp.raise_for_status()
        return resp.json()

    async def goal_state(self, handle: str) -> Dict[str, Any]:
        cl = self._ensure_client()
        resp = await cl.get(f"/goal_state/{handle}")
        resp.raise_for_status()
        return resp.json()

    async def expr_type(self, expr: str) -> str:
        cl = self._ensure_client()
        resp = await cl.post("/expr_type", json={"expr": expr})
        resp.raise_for_status()
        return resp.json()["type"]

    async def compile(self, content: str) -> List[Dict[str, Any]]:
        """Compile Lean *content* (string) with `load_sorry`. Returns units list."""
        cl = self._ensure_client()
        resp = await cl.post("/compile", json={"content": content})
        resp.raise_for_status()
        return resp.json()["units"]

    async def tactic_invocations(
        self, file_name: str = "Agent.lean"
    ) -> List[Dict[str, Any]]:
        cl = self._ensure_client()
        resp = await cl.post("/tactic_invocations", json={"file_name": file_name})
        resp.raise_for_status()
        return resp.json()["units"]

    async def gc(self) -> None:
        cl = self._ensure_client()
        # 204 or 200
        await cl.post("/gc")


# -----------------------------------------------------------------------------
# LeanServerDeployer – provision server on Morph Cloud (optional)
# -----------------------------------------------------------------------------


@dataclass(slots=True)
class LeanServerDeployer:
    """Provision a Pantograph Lean server on Morph Cloud.

    This class replicates the logic in `external/morphcloud-examples-public/lean-server/setup.py`
    but wraps it in a reusable function so orchestrators can forkl with
    non-blocking, programmatic control.

    The deployment is *idempotent*: if a snapshot with the given *snapshot_digest*
    already exists, it will be reused. Likewise, if an instance tagged by
    *instance_tag* is running, its URL will be returned instead of starting a
    new VM.
    """

    # Cloud resource parameters – tweak to taste
    vcpus: int = 2
    memory_mb: int = 4096
    disk_mb: int = 20480
    # Include Lean version + cache suffix so we can roll upgrades explicitly
    snapshot_digest: str = "pantograph-1-1-lean4.18-cache"
    instance_tag: str = "gaussianspec_pantograph"

    # Path to daemon script (already vendored from example)
    daemon_script: Path = (
        Path(__file__).resolve().parents[2]
        / "external"
        / "morphcloud-examples-public"
        / "lean-server"
        / "daemon.py"
    )

    def deploy(self) -> str:
        """Ensure server is running; return public base URL."""
        if MorphCloudClient is None:
            raise RuntimeError(
                "morphcloud SDK is not installed. Add `morphcloud` to project deps or install manually."
            )

        mc = MorphCloudClient()

        # ------------------------------- snapshot ------------------------------- #
        # Try to reuse an existing snapshot with the same digest if present.
        existing = next(
            (s for s in mc.snapshots.list() if s.digest == self.snapshot_digest), None
        )
        if existing is not None:
            snap = existing
        else:
            snap = mc.snapshots.create(
                vcpus=self.vcpus,
                memory=self.memory_mb,
                disk_size=self.disk_mb,
                digest=self.snapshot_digest,
            )
            # Run provisioning commands (identical to example)
            self._provision_snapshot(snap)

        # ------------------------------- instance ------------------------------- #
        running = next(
            (
                i
                for i in mc.instances.list()
                if i.metadata.get("purpose") == self.instance_tag
            ),
            None,
        )
        if running is not None and running.status == InstanceStatus.READY:
            # Ensure the service exists and is running (snapshot may lack it)
            self._ensure_pantograph_service(running)
            return self._ensure_service_url(running)

        # Otherwise start a new instance from snapshot
        inst = mc.instances.start(snap.id, metadata={"purpose": self.instance_tag})
        # Even for fresh instances ensure service setup (idempotent)
        self._ensure_pantograph_service(inst)
        return self._ensure_service_url(inst)

    # --------------------------------------------------------------------- #
    # Internal helpers
    # --------------------------------------------------------------------- #

    def _provision_snapshot(self, snap):
        """Run the provisioning commands defined in the example setup script."""
        # 1) OS deps + uv
        snap.exec(
            "apt-get update && "
            "apt-get install -y git curl python3.11 python3.11-venv build-essential pipx"
        )
        # Install `uv` via the official script (static binary → $HOME/.cargo/bin/uv)
        # This avoids Debian's `pipx` path inconsistencies and gives us an
        # up-to-date release directly from the upstream project.
        snap.exec("curl -LsSf https://astral.sh/uv/install.sh | sh")

        # Install Rust toolchain (needed for maturin when building PyPantograph)
        snap.exec(
            "curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal"
        )

        # 2) Python venv + FastAPI
        # The installer places the binary under `$HOME/.cargo/bin`.
        uv_bin = "$HOME/.cargo/bin/uv"

        snap.exec(f"{uv_bin} venv /opt/venv")
        snap.exec(
            "source /opt/venv/bin/activate && "
            f"{uv_bin} pip install fastapi 'uvicorn[standard]'"
        )

        # 3) Lean toolchain
        snap.exec(
            "curl https://elan.lean-lang.org/elan-init.sh -sSf | "
            "sh -s -- -y --default-toolchain leanprover/lean4:v4.18.0"
        )

        # 4) Mathlib project with lake build (simplified compared to example)
        snap.exec(
            'export PATH="$HOME/.elan/bin:$PATH" && '
            "lake +leanprover/lean4:v4.18.0 new mathlib_project math.toml"
        )
        snap.exec(
            """
            export PATH="$HOME/.elan/bin:$PATH" &&
            cd mathlib_project &&
            echo "leanprover/lean4:v4.18.0" > lean-toolchain &&
            lake exe cache get &&
            lake build &&
            # Package the build artefacts so downstream clones can fetch a single tarball
            lake exe cache pack
            """
        )

        # 5) PyPantograph build & install
        snap.exec(
            "git clone --recurse-submodules https://github.com/stanford-centaur/PyPantograph.git /src/PyPantograph"
        )
        snap.exec(
            'export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH" && '
            "source /opt/venv/bin/activate && "
            f"{uv_bin} pip install /src/PyPantograph"
        )

        # 6) Upload daemon and service file
        snap.upload(str(self.daemon_script), "/opt/pantograph/daemon.py")
        snap.exec(
            """cat > /etc/systemd/system/pantograph.service << 'EOF'
[Unit]
Description=Pantograph Lean Server
After=network.target

[Service]
ExecStart=/opt/venv/bin/python -u /opt/pantograph/daemon.py
WorkingDirectory=/root/mathlib_project
User=root
Group=root
Restart=always
RestartSec=5
Environment="PATH=/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
StandardOutput=journal
StandardError=journal

[Install]
WantedBy=multi-user.target
EOF
"""
        )

        if console:
            console.print(f"[green]Snapshot provisioned successfully[/green]")

    def _ensure_pantograph_service(self, inst):
        """Idempotently install & start the pantograph systemd service.

        Some snapshots created before the service was added will boot without
        `/etc/systemd/system/pantograph.service`.  This helper uploads the
        daemon and service unit **every time** we (re)use an instance so
        subsequent logic can assume the HTTP endpoint is reachable.
        """

        # 1) Upload daemon script unconditionally (cheap and safe)
        try:
            inst.upload(str(self.daemon_script), "/opt/pantograph/daemon.py")
        except Exception:
            # Older morphcloud client versions raise if path unchanged → ignore
            pass

        # 2) Ensure service unit exists
        unit_path = "/etc/systemd/system/pantograph.service"
        has_unit = (
            inst.exec(f"test -f {unit_path} || echo MISSING").stdout.strip()
            != "MISSING"
        )
        if not has_unit:
            inst.exec(
                "cat > /etc/systemd/system/pantograph.service << 'EOF'\n"
                "[Unit]\nDescription=Pantograph Lean Server\nAfter=network.target\n\n"
                "[Service]\nExecStart=/opt/venv/bin/python -u /opt/pantograph/daemon.py\n"
                "WorkingDirectory=/root/mathlib_project\nUser=root\nGroup=root\nRestart=always\n"
                'RestartSec=5\nEnvironment="PATH=/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"\n'
                "StandardOutput=journal\nStandardError=journal\n\n[Install]\nWantedBy=multi-user.target\nEOF"
            )

        # 2.5) Ensure the Python virtual environment exists because the
        # daemon's ExecStart depends on `/opt/venv/bin/python`.  Older
        # snapshots did not include the venv, leading to `203/EXEC` failures
        # when systemd tries to start the service.  The repair is fully
        # idempotent and safe to run on every boot.

        has_py = (
            inst.exec("test -x /opt/venv/bin/python || echo MISSING").stdout.strip()
            != "MISSING"
        )

        if not has_py:
            # Install minimal OS deps in case the base image is missing them
            inst.exec(
                "apt-get update && apt-get install -y python3 python3-venv python3-pip"
            )

            # Create the venv and install runtime Python deps required by the
            # Pantograph daemon.  We purposefully *do not* install build tools
            # (Rust, maturin, etc.) here because this path only runs on old
            # snapshots that already have a working PyPantograph wheel cached
            # on PyPI.  Keeping the footprint minimal speeds up the repair.
            inst.exec("python3 -m venv /opt/venv")

            # Use the venv's pip module directly to avoid sourcing or PATH
            # manipulation which can be brittle inside `inst.exec`.
            pip = "/opt/venv/bin/pip"
            inst.exec(
                f"{pip} install --upgrade pip fastapi 'uvicorn[standard]' pantograph"
            )

        # 3) Reload and (re)start
        inst.exec(
            "systemctl daemon-reload && "
            "systemctl enable pantograph.service && "
            "systemctl restart pantograph.service"
        )

    def _ensure_service_url(self, instance) -> str:
        url = instance.expose_http_service("pantograph", PANTOGRAPH_PORT)
        if console:
            console.print(f"[bold green]Pantograph server ready at:[/bold green] {url}")
        return url


# -----------------------------------------------------------------------------
# Convenience synchronous helpers
# -----------------------------------------------------------------------------


def deploy_and_get_client() -> LeanServerClient:
    """High-level helper: deploy server (if needed) and return *synchronous* client.

    This function blocks until the server is reachable and returns a client
    instance **outside** an async context manger—convenient for quick scripts
    that don't want to `async with`.
    """

    dep = LeanServerDeployer()
    base_url = dep.deploy()

    # Spin until server responds to /gc (simple health-check)
    async def _wait_ready(url: str):
        async with httpx.AsyncClient(base_url=url, timeout=60) as cl:
            for i in range(600):  # wait up to 600s (~10 min) for heavy boots
                if i % 30 == 0 and i > 0:
                    print(
                        f"[deploy_and_get_client] Waiting for Pantograph server to become ready… elapsed {i}s"
                    )
                try:
                    resp = await cl.post("/gc")
                    # A healthy Pantograph server responds with 200 (JSON) or
                    # sometimes 204 for empty responses.  Treat anything else
                    # (including 502 gateway errors) as *not ready* so we keep
                    # polling until the service is actually up.
                    if resp.status_code in (200, 204):
                        return
                except Exception:
                    # Network-level errors (e.g. connection refused) are
                    # expected during the boot-up window.  We simply ignore and
                    # retry with exponential back-off below.
                    pass

                await asyncio.sleep(1)

            raise TimeoutError("Pantograph server did not become ready in time")

    asyncio.run(_wait_ready(base_url))
    return LeanServerClient(base_url)
