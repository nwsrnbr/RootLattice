import Mathlib.Analysis.InnerProductSpace.Projection

structure FiniteReflectionGroup (𝕜 E : Type*) [RCLike 𝕜] extends NormedAddCommGroup E, InnerProductSpace 𝕜 E where
  W : Subgroup (E ≃ₗᵢ[𝕜] E)
  isFinite : Finite W
  gen_ref : ∃ n : ℕ, ∃ v : Fin n → E, W = Subgroup.closure (Set.range fun i ↦ (Submodule.span 𝕜 {v i}).reflection)

namespace FiniteReflectionGroup

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

variable (W : FiniteReflectionGroup 𝕜 E)
