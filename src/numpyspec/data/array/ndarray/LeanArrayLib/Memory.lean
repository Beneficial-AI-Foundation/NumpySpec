namespace LeanArrayLib

/-- Minimal `PlainDataType` – **only** `UInt8` provided here to keep
    the demo simple.  You can add more types later. -/
class PlainDataType (α : Type) where
  /-- Serialize a value to a fixed-length byte array -/
  encode          : α → Array UInt8   -- fixed-length serialization
  /-- Deserialize a byte array back to a value -/
  decode          : Array UInt8 → Option α
  /-- All encoded values have the same length (1 byte for UInt8) -/
  encode_length   : ∀ x, (encode x).size = 1
  /-- Decoding an encoded value always succeeds and returns the original -/
  decode_encode   : ∀ x, decode (encode x) = some x

instance : PlainDataType UInt8 where
  encode x        := #[x]
  decode | #[b]    => some b | _ => none
  encode_length _ := rfl
  decode_encode _ := rfl

/-- `Buffer` = thin wrapper around `ByteArray`.  Because we restrict to
    `UInt8`, one element = one byte, so `length = data.size`. -/
structure Buffer (α : Type) [PlainDataType α] where
  /-- The underlying byte storage -/
  data : ByteArray

namespace Buffer

-- Add Inhabited instance for Buffer
instance {α : Type} [PlainDataType α] : Inhabited (Buffer α) where
  default := ⟨ByteArray.empty⟩

/-- Create an empty buffer with no elements -/
def mkEmpty {α : Type} [PlainDataType α] : Buffer α := ⟨ByteArray.empty⟩

/-- Get the number of elements in the buffer -/
@[simp] def length {α} [PlainDataType α] (b : Buffer α) : Nat := b.data.size

/-- Append one element. -/
@[inline] def push [PlainDataType α] (b : Buffer α) (x : α) : Buffer α :=
  let bytes := PlainDataType.encode x
  match bytes with
  | #[u] => ⟨b.data.push u⟩     -- exactly one byte
  | _   => panic! "encode length ≠ 1 (impossible by spec)"

/-- Unsafe read: caller guarantees `i < length`. -/
@[inline, always_inline] unsafe def readUnsafe [PlainDataType α] [Inhabited α]
    (b : Buffer α) (i : Nat) : α :=
  let u : UInt8 := b.data.get! i
  match PlainDataType.decode (α := α) #[u] with
  | some v => v
  | none   => panic! "decode failed – invariant broken"

end Buffer
end LeanArrayLib
