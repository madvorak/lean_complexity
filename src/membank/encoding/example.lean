import tactic
import membank.encoding.list

namespace membank
namespace encoding

def nat_cmp: program ℕ :=
[ -- 1 a [1 b _]
  instruction.binary_op (λ a b, ite (a < b) 0 1) [] [source.imm 0] [source.imm 1, source.imm 0],
  -- (a≥b) null [1 b _]
  instruction.clear [source.imm 0],
  -- (a≥b) null null
  instruction.clear [source.imm 1]
]

instance : complexity.has_encoding (runtime_model ℕ) ℕ := ⟨ ⟨ bank.null.setv, begin
  intros x y,
  rw [bank.equiv_iff],
  simp [bank.setv, bank.getv],
  intros h a,
  rw [h],
end ⟩ ⟩

instance (α: Type*): inhabited (frame α) := ⟨ ⟨ [], [], bank.null ⟩ ⟩

def decode_list: bank ℕ → list ℕ
| bank.null := []
| (bank.mem 1 f) := (f 0).getv :: (decode_list (f 1))
| (bank.mem _ _) := []
def mk_list: list ℕ → bank ℕ := complexity.encode (runtime_model ℕ)
def push_list: list ℕ → bank ℕ → bank ℕ := λ xs, push_arg (mk_list xs)

def twenty : list ℕ := [13, 4, 20, 10, 9, 14, 1, 2, 17, 11, 15, 7, 5, 8, 12, 18, 3, 6, 16, 19]
def test: list (frame ℕ) := ((stack.step^[3500]) ((merge_sort nat_cmp).apply (push_list twenty bank.null))).val

#eval (list.length test) -- 1
#eval list.length (frame.current (list.ilast test)) -- 0
#eval decode_list (frame.register (list.ilast test)) -- [1..20]

end encoding
end membank