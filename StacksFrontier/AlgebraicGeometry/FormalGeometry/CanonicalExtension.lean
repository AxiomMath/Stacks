module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicPro

/-!
# Canonical extension of a coherent adic system

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)`, and the open complement `U = X \ V(𝔞)`. A coherent `I`-adic system `(F_n)` on
`U` has an associated inverse system of `A`-modules `(H⁰(U, F_n))`, and hence an inverse system
of quasi-coherent sheaves `(H⁰(U, F_n)^~)` on `X`. The system `(F_n)` *canonically extends* to
`X` when that system of sheaves is pro-isomorphic to a coherent `I`-adic system on `X`.

## Main definitions

* `Stacks.Algebraization.idealOnX` — the ideal sheaf `I 𝒪_X` on `X = Spec(A)`.
* `Stacks.Coherent.diagramToPro` — an inverse diagram of quasi-coherent modules as a
  pro-object.
* `Stacks.Algebraization.tildeGlobalSectionsSystem` — the inverse system `(H⁰(U, F_n)^~)` of
  quasi-coherent sheaves on `X`.
* `Stacks.Algebraization.CanonicallyExtends` — the canonical-extension predicate.

## References

* [Stacks Project, Tag 0EIP](https://stacks.math.columbia.edu/tag/0EIP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Coherent

/-- An inverse diagram of quasi-coherent modules as a pro-object, in the ind-opposite
realization of the pro-category. -/
@[implicit_reducible]
public noncomputable def diagramToPro {X : Scheme.{u}}
    (F : ℕᵒᵖ ⥤ Scheme.QuasicoherentModules X) :
    (Ind (Scheme.QuasicoherentModules X)ᵒᵖ)ᵒᵖ :=
  let e : ℕᵒᵖᵒᵖ ≌ ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)) :=
    (Shrink.equivalence.{u} (ℕᵒᵖᵒᵖ)).trans
      (ShrinkHoms.equivalence.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))
  letI : IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) := IsFiltered.of_equivalence e
  op ((Ind.lim (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))).obj (e.inverse ⋙ F.op))

end Stacks.Coherent

namespace Stacks.Algebraization

/-- The ideal sheaf `I 𝒪_X` on `X = Spec(A)` in an algebraization situation. -/
public abbrev idealOnX (S : AlgebraizationSituation.{u}) : S.X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom)

/-- The ideal sheaf `I 𝒪_U` on the open complement is the restriction of `I 𝒪_X`. -/
public theorem idealOnOpen_eq_comap_idealOnX (S : AlgebraizationSituation.{u}) :
    idealOnOpen S = (idealOnX S).comap S.U.ι := rfl

/-- The inverse system of quasi-coherent sheaves on `X` associated to the global sections of a
coherent adic system on `U`. -/
@[implicit_reducible]
public noncomputable def tildeGlobalSectionsSystem (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    ℕᵒᵖ ⥤ Scheme.QuasicoherentModules S.X :=
  ObjectProperty.lift _ (globalSectionsSystem S F ⋙ tilde.functor (.of S.A)) (fun n => by
    change (tilde.{u} (R := CommRingCat.of S.A)
      ((globalSectionsSystem S F).obj n)).IsQuasicoherent
    infer_instance)

/-- A coherent `I`-adic system on `U` *canonically extends* to `X` when the quasi-coherent
sheaves associated to its global sections are pro-isomorphic to a coherent `I`-adic system on
`X`. -/
@[stacks 0EIP]
public abbrev CanonicallyExtends (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) : Prop :=
  ∃ G : Stacks.Coherent.CoherentAdicSystems (idealOnX S),
    Nonempty (Stacks.Coherent.diagramToPro (tildeGlobalSectionsSystem S F) ≅
      (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj G)

end Stacks.Algebraization

end
