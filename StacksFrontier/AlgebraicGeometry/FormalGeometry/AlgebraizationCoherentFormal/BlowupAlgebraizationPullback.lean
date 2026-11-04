module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.BlowupAlgebraizationDistance
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.BaseAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm

/-!
# The pullback of a coherent formal module to the blowup, in the proof of Stacks 0EJK

In Situation [Stacks, Tag 0EHC] let `b : X' ⟶ X` be the blowup of `X = Spec(A)` in `I` and
`U' = b⁻¹(U)`. The proof of [Stacks, Tag 0EJK] works with the pullback `(b|_{U'}^*ℱₙ)` of an
object `(ℱₙ)` of `Coh(U, I𝒪_U)` ([Stacks, Tag 0887]), read as an object of `Coh(U', I𝒪_{U'})`
for the exceptional ideal `I𝒪_{U'}` restricted to `U'`
(`Stacks.Algebraization.blowupPullbackSystem`).

## Main definitions

* `Stacks.Algebraization.blowupRestrict` — the morphism `b|_{U'} : U' ⟶ U`.
* `Stacks.Algebraization.blowupPullbackSystem` — the object `(b|_{U'}^*ℱₙ)` of `Coh(U', I𝒪_{U'})`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- The restriction `b|_{U'} : U' ⟶ U` of the blowup morphism. -/
abbrev blowupRestrict : (situationBlowUpU S).toScheme ⟶ S.U.toScheme :=
  situationBlowUpToBase S ∣_ S.U

/-- The pullback of the ideal sheaf `I𝒪_U` along `b|_{U'} : U' ⟶ U` is the exceptional ideal
`I𝒪_{U'}` on `U'`. -/
theorem comap_idealOnOpen_blowupRestrict :
    (idealOnOpen S).comap (blowupRestrict S) = blowupIdealU S := by
  rw [idealOnOpen_eq_comap_idealOnX, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι,
    Scheme.IdealSheafData.comap_comp]
  rfl

/-- **The pullback `(b|_{U'}^*ℱₙ)`** of an object of `Coh(U, I𝒪_U)`, as an object of
`Coh(U', I𝒪_{U'})` ([Stacks, Tag 0887]). -/
def blowupPullbackSystem (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    Stacks.Coherent.CoherentAdicSystems (blowupIdealU S) :=
  ⟨((Stacks.Coherent.coherentAdicPullback (blowupRestrict S) (idealOnOpen S)).obj F).obj,
    comap_idealOnOpen_blowupRestrict S ▸
      ((Stacks.Coherent.coherentAdicPullback (blowupRestrict S) (idealOnOpen S)).obj F).property⟩

/-- The inverse system underlying `blowupPullbackSystem S F` is `(b|_{U'}^*ℱₙ)`, the termwise
pullback of the system `(ℱₙ)` along `b|_{U'}`. -/
theorem blowupPullbackSystem_obj (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    (blowupPullbackSystem S F).obj = F.obj ⋙ Scheme.Modules.pullback (blowupRestrict S) :=
  rfl

end Stacks.Algebraization

end
