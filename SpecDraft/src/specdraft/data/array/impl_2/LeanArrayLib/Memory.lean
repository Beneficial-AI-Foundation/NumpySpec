namespace LeanArrayLib

/-- Minimal `PlainDataType` – **only** `UInt8` provided here to keep
    the demo simple.  You can add more types later. -/
class PlainDataType (α : Type) where
  encode          : α → List UInt8   -- fixed-length serialization
  decode          : List UInt8 → Option α
  encode_length   : ∀ x, (encode x).length = 1
  decode_encode   : ∀ x, decode (encode x) = some x

instance : PlainDataType UInt8 where
  encode x        := [x]
  decode | [b]    => some b | _ => none
  encode_length _ := rfl
  decode_encode _ := rfl

/-- `Buffer` = thin wrapper around `ByteArray`.  Because we restrict to
    `UInt8`, one element = one byte, so `length = data.size`. -/
structure Buffer (α : Type) [PlainDataType α] where
  data : ByteArray

namespace Buffer

@[simp] def empty [PlainDataType α] : Buffer α := ⟨ByteArray.empty⟩

@[simp] def length [PlainDataType α] (b : Buffer α) : Nat := b.data.size

/-- Append one element. -/
@[inline] def push [PlainDataType α] (b : Buffer α) (x : α) : Buffer α :=
  let bytes := PlainDataType.encode x
  have h : bytes.length = 1 := PlainDataType.encode_length _
  match bytes with
  | [u] => ⟨b.data.push u⟩     -- exactly one byte
  | _   => panic! "encode length ≠ 1 (impossible by spec)"

/-- Unsafe read: caller guarantees `i < length`. -/
@[inline, always_inline] unsafe def readUnsafe [PlainDataType α]
    (b : Buffer α) (i : Nat) : α :=
  let u : UInt8 := b.data.get! i
  match PlainDataType.decode [u] with
  | some v => v
  | none   => panic! "decode failed – invariant broken"

end Buffer
end LeanArrayLib
