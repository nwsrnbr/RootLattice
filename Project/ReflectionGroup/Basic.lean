import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.RootSystem.Defs
/-
variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

structure FiniteReflectionGroup where
  W : Subgroup (E ≃ₗᵢ[𝕜] E)
  isFinite : Finite W
  gen_ref : ∃ n : ℕ, ∃ v : Fin n → E, W = Subgroup.closure (Set.range fun i ↦ (Submodule.span 𝕜 {v i}).reflection)
-/
variable (ι R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

structure FiniteReflectionGroup where
  W : Subgroup (M ≃ₗ[R] M)
  isFinite : Finite W
  α : ι ↪ M
  eq_two : ∀ i, ∃ f : Module.Dual R M, f (α i) = 2
  gen_set : Set (M ≃ₗ[R] M) := Set.range fun i ↦ Module.reflection (eq_two i).choose_spec
  gen_ref : W = Subgroup.closure gen_set

structure essFRG extends FiniteReflectionGroup ι R M where
  essential : ∀ v : M, ∀ w : W, w.val v = v ↔ v = 0

namespace FiniteReflectionGroup
variable (P : RootPairing ι R M N)

/-
def essFRG_to_RootSystem (W : essFRG ι R M) (W' : essFRG ι R M) : RootSystem ι R M M where
  toFun := by
    rcases W.eq_two with f
  root := W.v
  coroot := W'.v
  root_coroot_two := by
    intro i
    rcases W.eq_two i with ⟨f, hf⟩
    simp
-/

def RootSystem_to_essFRG (P : RootSystem ι R M N) : essFRG ι R M where
  W := Subgroup.closure (Set.range fun i ↦ P.reflection i)
  isFinite := by sorry
  α := P.root
  eq_two := by
    intro i
    use (P.flip.toLinearMap (P.coroot i))
    apply P.flip.root_coroot_two i
  gen_set := (Set.range fun i ↦ P.reflection i)
  gen_ref := rfl
  essential := by
    intro v w
    constructor
    <;> intro h
    · sorry
    · rw [h]
      simp

end FiniteReflectionGroup
