module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedCategoryOverField.Decomposition
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# The higher direct images of the structure sheaf of a proper scheme over a field

Let `f : X → Spec k` be a proper morphism to the spectrum of a field. The higher direct image
`Rⁿf_*𝒪_X` is a module on the one-point space `Spec k`; such a module is the module associated
to its global sections, and its global sections are `Hⁿ(X, 𝒪_X)`, a finite dimensional
`k`-vector space (Stacks 02O3 over a field). So `Rⁿf_*𝒪_X` is free of rank `dim_k Hⁿ(X, 𝒪_X)`;
for `n = 1` the rank is the genus of `X` (Stacks 0BY7).

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_zariskiRingedSite_of_iso_free`: a
  module isomorphic to the free module on `Fin r` has rank `r` on the small Zariski ringed site.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_rightDerived_pushforward_unit_of_isProper`: for
  `f : X → Spec k` proper, `Rⁿf_*𝒪_X` has rank `dim_k Hⁿ(X, 𝒪_X)` on the small Zariski ringed site
  of `Spec k`.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_rightDerived_pushforward_unit_genus_of_eq_spec`:
  for `f : X → Y` with `Y = Spec k` and `f` proper, `R¹f_*𝒪_X` has rank the genus of `X`.

## Implementation notes

The global sections functor `moduleSpecΓFunctor` of `Spec k` is an equivalence (its left adjoint
`~` has invertible unit, and invertible counit on a one-point spectrum,
`AlgebraicGeometry.SpecFieldDerived.isIso_tildeAdjunction_counit_of_subsingleton`), so it
preserves homology and passes through right derived functors
(`Stacks.DerivedFunctor.rightDerivedEvaluationIso`): the global sections of `Rⁿf_*𝒪_X` are the
cohomology `AlgebraicGeometry.structureSheafCohomology f n` in which the genus is defined. A basis
of them gives `Rⁿf_*𝒪_X ≅ ~(kʳ) ≅ 𝒪^r` by `tilde_fixed_free_iff_basis`.

The statement over a scheme `Y` equal to `Spec k` is the form in which the result is used on the
big fppf site, whose objects are only equal to `Spec k` through a hypothesis; it reduces to the
statement over `Spec k` by substitution.

## References

* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 02O3](https://stacks.math.columbia.edu/tag/02O3)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A module isomorphic to `𝒪^r` has rank `r` on the small Zariski ringed site**: the top open
alone trivializes it. -/
theorem Scheme.Modules.isFiniteLocallyFreeOfRank_zariskiRingedSite_of_iso_free {Y : Scheme.{u}}
    (M : Y.Modules) (r : ℕ)
    (e : _root_.SheafOfModules.free.{u} (R := Y.ringCatSheaf) (ULift.{u} (Fin r)) ≅ M) :
    RingedSite.IsFiniteLocallyFreeOfRank Y.zariskiRingedSite M r := by
  obtain ⟨ι, ⟨hc⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofan_of_iso_free e
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit
    Y.zariskiRingedSite M r).2
    ⟨PUnit.{u + 1}, fun _ => (⊤ : Y.Opens), Stacks.SheafOfModules.coversTop_top Y, fun _ => ?_⟩
  let T := _root_.SheafOfModules.overFunctor Y.ringCatSheaf (⊤ : Y.Opens)
  let : T.Additive := ⟨rfl⟩
  have hc' := (Cofan.isColimitMapCoconeEquiv T _ _).toFun (isColimitOfPreserves T hc)
  exact ⟨fun j => T.map (ι ⟨j⟩),
    ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _) hc'⟩⟩

variable (k : Type u) [Field k]

/-- On the spectrum of a field the global sections functor is an equivalence. -/
instance isEquivalence_moduleSpecΓFunctor_specField :
    (moduleSpecΓFunctor (R := .of k)).IsEquivalence :=
  (SpecFieldDerived.tildeEquivalenceOfSubsingleton (R := .of k)).isEquivalence_inverse

/-- **The global sections of `Rⁿf_*𝒪_X` over `Spec k` are `Hⁿ(X, 𝒪_X)`**, as `k`-modules. -/
def moduleSpecΓFunctorObjRightDerivedIso {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) :
    (moduleSpecΓFunctor (R := .of k)).obj
        (((Scheme.Modules.pushforward f).rightDerived n).obj
          (SheafOfModules.unit X.ringCatSheaf)) ≅
      structureSheafCohomology f n :=
  letI : (moduleSpecΓFunctor (R := .of k)).Additive := ⟨by intro M N φ ψ; ext x; rfl⟩
  Stacks.DerivedFunctor.rightDerivedEvaluationIso (Scheme.Modules.pushforward f)
    (moduleSpecΓFunctor (R := .of k)) (SheafOfModules.unit X.ringCatSheaf) n

/-- **`Rⁿf_*𝒪_X` of a proper `f : X → Spec k` is free of rank `dim_k Hⁿ(X, 𝒪_X)`** on the small
Zariski ringed site of `Spec k`. -/
theorem isFiniteLocallyFreeOfRank_rightDerived_pushforward_unit_of_isProper {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (n : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank (Spec (.of k)).zariskiRingedSite
      (((Scheme.Modules.pushforward f).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf))
      (Module.finrank k (structureSheafCohomology f n)) := by
  let R := ((Scheme.Modules.pushforward f).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf)
  let V := (moduleSpecΓFunctor (R := .of k)).obj R
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have := finiteDimensional_cohomologyOverField_of_isProper k f
    (SheafOfModules.unit X.ringCatSheaf) n
  let eH : structureSheafCohomology f n ≃ₗ[k]
      cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n :=
    (structureSheafCohomologyIsoCohomologyOverField k f n).toLinearEquiv
  let eV : V ≃ₗ[k] structureSheafCohomology f n :=
    (moduleSpecΓFunctorObjRightDerivedIso k f n).toLinearEquiv
  have : FiniteDimensional k (structureSheafCohomology f n) :=
    LinearEquiv.finiteDimensional eH.symm
  have : FiniteDimensional k V := LinearEquiv.finiteDimensional eV.symm
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank k (structureSheafCohomology f n)))) k V :=
    (Module.finBasisOfFinrankEq k V (LinearEquiv.finrank_eq eV)).reindex Equiv.ulift.symm
  obtain ⟨eFree⟩ := (tilde_fixed_free_iff_basis k V _).2 ⟨b⟩
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_zariskiRingedSite_of_iso_free R _
    (eFree.symm ≪≫ (asIso (tilde.adjunction (R := .of k)).counit).app R)

/-- **`R¹f_*𝒪_X` of a proper scheme over a field has rank the genus**, for `f : X → Y` with
`Y = Spec k` through an equality, on the small Zariski ringed site of `Y`. -/
theorem isFiniteLocallyFreeOfRank_rightDerived_pushforward_unit_genus_of_eq_spec
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : Y = Spec (.of k)) (hf : IsProper f) :
    RingedSite.IsFiniteLocallyFreeOfRank Y.zariskiRingedSite
      (((Scheme.Modules.pushforward f).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf))
      (genus (f ≫ eqToHom hY)) := by
  subst hY
  simp only [eqToHom_refl, Category.comp_id, genus_eq_finrank_structureSheafCohomology]
  exact isFiniteLocallyFreeOfRank_rightDerived_pushforward_unit_of_isProper k f 1

end AlgebraicGeometry

end
