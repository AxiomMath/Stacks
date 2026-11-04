module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPerfectDual
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientReduction

/-!
# The cone of [Stacks, Tag 0A0E]'s tower along the completion unit is the derived reduction

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let `ℐ ⊂ 𝒪` be a
sheaf of ideals. Part (1) of [Stacks, Tag 0A0K] presents the completion of `K` as a derived
limit of the tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` by composing the pinned presentation of
[Stacks, Tag 0A0E] over the dual Koszul tower
(`AlgebraicGeometry.RingedSite`
`.isDerivedLimitWithProjections_tensorDerivedDualSystem_koszulPowerSystem_completion`) with a
comparison `ψ` of that tower with the adic quotient tower. Pinning the resulting projections to
the canonical factorizations `AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor` of
[Stacks, Tag 0CQH] amounts, by the uniqueness clause of such a factorization, to one equation:
that the completion unit followed by the `n`-th projection is the derived reduction
`AlgebraicGeometry.RingedSite.adicQuotientReduction`.

This file reduces that equation to a statement **in which the coefficient object `K` does not
appear**: the composite

`𝒪[0] ≅ R𝑆heafHom_𝒪(𝒪[0], 𝒪[0]) ⟶ R𝑆heafHom_𝒪(K^n, 𝒪[0]) ⟶ 𝒪/ℐᵐ[0]`

— the trivialisation of the dual of the structure sheaf, the dual of a morphism
`φ : Q(K^n) ⟶ 𝒪[0]`, and the comparison `ψ` — is the projection `𝒪 ⟶ 𝒪/ℐᵐ` in degree zero.

## Main results

* `AlgebraicGeometry.RingedSite.eq_adicQuotientReduction_of_dual_comp_eq`: granted that
  coefficient-free identity, the cone of the Koszul tower along the completion unit, composed
  with `K ⊗^𝐋_𝒪 ψ`, is the derived reduction `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐᵐ` — at an arbitrary `K`, an
  arbitrary sheaf of ideals and an arbitrary `m`.

## Implementation notes

Two inputs meet. The cone of the pinned presentation of [Stacks, Tag 0A0E] along the completion
unit is computed by
`AlgebraicGeometry.RingedSite.completionUnit_app_comp_tensorDerivedDualSystem_π` as the
trivialisation `K ≅ R𝑆heafHom_𝒪(𝒪[0], K)` followed by the map which one morphism of complexes
`K^n ⟶ 𝒪[0]` induces, read back through the tower identification; and the unit law of the tower
identification,
`RingedSite.derivedStructureSheafHomIso_inv_comp_map_comp_koszulTensorDualSystemIso_inv_app`,
rewrites exactly that expression as the inverse right unit constraint followed by `K ⊗^𝐋_𝒪 -`
applied to a morphism `𝒪[0] ⟶ R𝑆heafHom_𝒪(K^n, 𝒪[0])` built from `φ` alone. The derived reduction
of [Stacks, Tag 0CQH] has the same shape — the inverse right unit constraint followed by
`K ⊗^𝐋_𝒪 -` of the projection — and the right unit constraint of
`AlgebraicGeometry.RingedSite.derivedTensorRightUnitIso` *is* the unit law
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso` the reduction is written against
(`AlgebraicGeometry.RingedSite.derivedTensorRightUnitIso_eq_unitIso`). So the two agree as soon as
the arguments of that functor do, and those mention no `K`.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  {r : ℕ} [HasWeakSheafify X.J CommRingCat.{u}]
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The cone of the pinned presentation of [Stacks, Tag 0A0E] along the completion unit,
composed with a comparison of the dual Koszul tower with the adic quotient tower, is the derived
reduction of [Stacks, Tag 0CQH]** — granted the coefficient-free identity `hψ`, which says that
the comparison, precomposed with the dual of `φ : Q(K^n) ⟶ 𝒪[0]` and with the trivialisation of
`R𝑆heafHom_𝒪(𝒪[0], 𝒪[0])`, is the projection `𝒪 ⟶ 𝒪/ℐᵐ` placed in degree zero.

The coefficient object `K` enters both sides only through the functor `K ⊗^𝐋_𝒪 -`, so the
identity `hψ` carries the whole content; see the module docstring. No hypothesis on `ℐ`, on `K`,
on the site or on `f` is used. -/
theorem eq_adicQuotientReduction_of_dual_comp_eq
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (n m : ℕ)
    (φ : DerivedCategory.Q.obj (koszulPowerComplex X f n) ⟶ derivedStructureSheaf X)
    (ψ : ((derivedSheafHomBifunctor X).obj
        (op (DerivedCategory.Q.obj (koszulPowerComplex X f n)))).obj
          (derivedStructureSheaf X) ⟶ adicQuotientObj X I m)
    (hψ : (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv ≫
        ((derivedSheafHomBifunctor X).map φ.op).app (derivedStructureSheaf X) ≫ ψ =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
        (Stacks.Sites.adicQuotientModuleπ (X := X) I m)) :
    ((derivedStructureSheafHomIso X K).inv ≫
          ((derivedSheafHomBifunctor X).map φ.op).app K ≫
          (koszulTensorDualSystemIso X f K).inv.app (op n)) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map ψ =
      adicQuotientReduction X I K m := by
  have hunit := derivedStructureSheafHomIso_inv_comp_map_comp_koszulTensorDualSystemIso_inv_app
    X f K n φ
  have hψ' : ((derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv ≫
        ((derivedSheafHomBifunctor X).map φ.op).app (derivedStructureSheaf X)) ≫ ψ =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
        (Stacks.Sites.adicQuotientModuleπ (X := X) I m) :=
    (Category.assoc _ _ _).trans hψ
  refine (congrArg (fun z ↦ z ≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map ψ) hunit).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z ↦ (derivedTensorRightUnitIso X K).inv ≫ z)
    (((((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map_comp _ ψ).symm).trans
      (congrArg ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map hψ'))).trans ?_
  rw [derivedTensorRightUnitIso_eq_unitIso, adicQuotientReduction]

end AlgebraicGeometry.RingedSite

end
