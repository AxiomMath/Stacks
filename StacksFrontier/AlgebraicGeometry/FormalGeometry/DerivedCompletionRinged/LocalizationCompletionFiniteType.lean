module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionOfComplexRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.FiniteTypeExtendedCech
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.FiniteTypeReflector
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalExtendedCechSlice
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalizationCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.OverIdealFiniteType
import StacksCore.Tactic.StacksAttribute

/-!
# Derived completion commutes with localization

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals of finite type and `U` an object of `𝒞`.
This file proves [Stacks, Tag 0A0F]: `K^∧|_U` is the derived completion of `K|_U`, where `K ↦ K^∧`
is the derived completion functor of [Stacks, Tag 099F] on `𝒞` and on the slice `𝒞/U`, the latter
along the restriction `ℐ|_U` of `ℐ`.

## Main results

* `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_overIdeal`: [Stacks, Tag 099F]
  for `ℐ|_U` on the slice.
* `AlgebraicGeometry.RingedSite.isIso_derivedCompletionRestrictComparison_overIdeal_app`: the
  Remark's canonical map `a : (K|_U)^∧ ⟶ K^∧|_U` is an isomorphism.
* `AlgebraicGeometry.RingedSite.derivedCompletionRestrictIso`: the resulting natural isomorphism.
* `AlgebraicGeometry.RingedSite.derivedCompletion_restrict`: **[Stacks, Tag 0A0F].**

## Implementation notes

The map `a` and the restriction of derived completeness it rests on are
`AlgebraicGeometry.RingedSite.derivedCompletionRestrictComparison` and
`AlgebraicGeometry.RingedSite.isDerivedComplete_derivedRestrict_derivedCompletion` of
`LocalizationCompletion.lean`, which hold for an arbitrary sheaf of ideals with a reflector on
either site. Its invertibility is proved by the route the source names first, the construction
in the proof of [Stacks, Tag 099F]. The source's alternative argument goes through a map
`b : K^∧ ⟶ Rj_*((K|_U)^∧)` built from [Stacks, Tag 099J] for the localization morphism `j`, whose
adjoint is the inverse of `a`; that is the second registration of the tag,
`AlgebraicGeometry.RingedSite.derivedCompletion_restrict_secondMap` of
`LocalizationCompletionPushforward.lean`.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (U : X.C)

/-- The chase behind `isIso_derivedCompletionRestrictComparison_overIdeal_app`,
stated for a bare functor so that it applies across the two spellings of the category of sheaves
of modules on a slice. -/
theorem comp_comp_comp_map_eq_map {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {B C : 𝒟} {P P' Q : 𝒞} {u : G.obj Q ⟶ B} {t : B ⟶ C} {c : G.obj Q ⟶ C} (hU : u ≫ t = c)
    {r : C ⟶ G.obj P} {x : Q ⟶ P} (hr : c ≫ r = G.map x) {y : P ⟶ P'} {z : Q ⟶ P'}
    (hX : x ≫ y = z) : u ≫ t ≫ r ≫ G.map y = G.map z := by
  rw [← hX, G.map_comp, ← hr, ← hU]
  simp only [Category.assoc]

variable [I.toSheafOfModules.IsFiniteType]

/-- **[Stacks, Tag 099F] on the slice**: the restriction `ℐ|_U` of a sheaf of ideals of finite
type is of finite type (`isFiniteType_overIdeal`), so the inclusion of the objects of `D(𝒪_U)`
derived complete along it has a left adjoint. -/
instance isRightAdjoint_ι_isDerivedComplete_overIdeal :
    (ObjectProperty.ι
      (IsDerivedComplete.{u, u, u, u} (X.over U) (overIdeal I U))).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete (X.over U) (overIdeal I U)

/-- **The map `a : (K|_U)^∧ ⟶ K^∧|_U` is an isomorphism**, for `ℐ` of finite type, with both
completion functors those of [Stacks, Tag 099F].

Take the map `a : K₀ ⟶ 𝒪` of [Stacks, Tag 099E]. The completion functor on `𝒞` is
`R𝑆heafHom_𝒪(K₀, -)` compatibly with the completion maps
(`derivedCompletionIsoOfIsGlobalExtendedCech`); so is the one on `𝒞/U` for the restriction
`a|_U : K₀|_U ⟶ 𝒪_U`, which has the property of [Stacks, Tag 099E] for `ℐ|_U`
(`isGlobalExtendedCech_restrict`); and `R𝑆heafHom_𝒪(K₀, E)|_U ≅ R𝑆heafHom_{𝒪_U}(K₀|_U, E|_U)`
compatibly with the completion maps
(`completionUnitOfComplex_comp_completionFunctorOfComplexOverIso_inv`).
The composite is an isomorphism `(K|_U)^∧ ≅ K^∧|_U` compatible with the completion maps, which
`isIso_derivedCompletionRestrictComparison_of_unit_comp` identifies with `a`. -/
instance isIso_derivedCompletionRestrictComparison_overIdeal_app
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsIso ((derivedCompletionRestrictComparison X I U (overIdeal I U)
      (fun _ _ hg ↦ hg)).app K) := by
  obtain ⟨K₀, a, ha⟩ := exists_isGlobalExtendedCech X I
  have ha' := isGlobalExtendedCech_restrict X U ha
  let θX := derivedCompletionIsoOfIsGlobalExtendedCech X I ha
  let θU := derivedCompletionIsoOfIsGlobalExtendedCech (X.over U) (overIdeal I U) ha'
  refine isIso_derivedCompletionRestrictComparison_of_unit_comp X I U (overIdeal I U)
    (fun _ _ hg ↦ hg)
    (θU.app ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj K) ≪≫
      (completionFunctorOfComplexOverIso X U K₀ K).symm ≪≫
      ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.mapIso
        (θX.app K)).symm) ?_
  have hX : (completionUnitOfComplex X a).app K ≫ θX.inv.app K =
      (derivedCompletionUnit X I).app K := by
    rw [← derivedCompletionUnit_app_comp_derivedCompletionIsoOfIsGlobalExtendedCech_hom_app X I ha
      K, Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app, Category.comp_id]
  have hU := derivedCompletionUnit_app_comp_derivedCompletionIsoOfIsGlobalExtendedCech_hom_app
    (X.over U) (overIdeal I U) ha'
    ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj K)
  have hρ := completionUnitOfComplex_comp_completionFunctorOfComplexOverIso_inv X U a K
  exact comp_comp_comp_map_eq_map
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory hU hρ hX

/-- **The natural isomorphism `(K|_U)^∧ ≅ K^∧|_U`** of functors `D(𝒪) ⥤ D(𝒪_U)`, for `ℐ` of finite
type: the Remark's canonical map `a`, which is invertible by
`isIso_derivedCompletionRestrictComparison_overIdeal_app`. -/
def derivedCompletionRestrictIso :
    (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory ⋙
        derivedCompletion (X.over U) (overIdeal I U) ≅
      derivedCompletion X I ⋙
        (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory :=
  haveI := NatIso.isIso_of_isIso_app
    (derivedCompletionRestrictComparison X I U (overIdeal I U) (fun _ _ hg ↦ hg))
  asIso (derivedCompletionRestrictComparison X I U (overIdeal I U) (fun _ _ hg ↦ hg))

/-- `derivedCompletionRestrictIso` carries the completion map of `K|_U` to the restriction of the
completion map of `K`. -/
theorem derivedCompletionUnit_app_comp_derivedCompletionRestrictIso_hom_app
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    (derivedCompletionUnit (X.over U) (overIdeal I U)).app
          ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K) ≫
        (derivedCompletionRestrictIso X I U).hom.app K =
      (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.map
        ((derivedCompletionUnit X I).app K) :=
  derivedCompletionUnit_comp_derivedCompletionRestrictComparison X I U (overIdeal I U)
    (fun _ _ hg ↦ hg) K

/-- **[Stacks, Tag 0A0F]: derived completion commutes with localization.** Let `(𝒞, 𝒪)` be a
ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals of finite type, `K ↦ K^∧` the derived completion functor
of [Stacks, Tag 099F] and `U` an object of `𝒞`. Then `K^∧|_U` is the derived completion of `K|_U`
along `ℐ|_U`:

* `K^∧|_U` is derived complete along `ℐ|_U`, for every `K`;
* hence there is a canonical map `a : (K|_U)^∧ ⟶ K^∧|_U`, natural in `K`, compatible with the
  completion maps — its composite with `K|_U ⟶ (K|_U)^∧` is the restriction of `K ⟶ K^∧` — and
  it is the only such map (`eq_derivedCompletionRestrictComparison_of_derivedCompletionUnit_comp`);
* `a` is an isomorphism, for every `K`.

The completion functor on `𝒞/U` is that of [Stacks, Tag 099F] for the ringed site
`(𝒞/U, 𝒪_U)` and the restricted sheaf of ideals `ℐ|_U`, which is of finite type
(`isFiniteType_overIdeal`); `a` is `derivedCompletionRestrictComparison`, and the resulting
natural isomorphism is `derivedCompletionRestrictIso`. The source proves the invertibility of `a`
"from the construction in the proof of the proposition"; so does this library: both completion
functors are `R𝑆heafHom(K₀, -)` for the map `K₀ ⟶ 𝒪` of [Stacks, Tag 099E] on the respective site,
the one on `𝒞/U` may be taken to be the restriction of the one on `𝒞`
(`isGlobalExtendedCech_restrict`), and `R𝑆heafHom` commutes with restriction by
[Stacks, Tag 08JB]. The Remark's second argument — the map `b : K^∧ ⟶ Rj_*((K|_U)^∧)` and the
verification that its adjoint inverts `a` — is the companion registration
`derivedCompletion_restrict_secondMap` of `LocalizationCompletionPushforward.lean`. -/
@[stacks 0A0F]
theorem derivedCompletion_restrict :
    (∀ K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      IsDerivedComplete.{u, u, u, u} (X.over U) (overIdeal I U)
        ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
          ((derivedCompletion X I).obj K))) ∧
    (∀ K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      (derivedCompletionUnit (X.over U) (overIdeal I U)).app
          ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K) ≫
        (derivedCompletionRestrictComparison X I U (overIdeal I U) (fun _ _ hg ↦ hg)).app K =
      (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.map
        ((derivedCompletionUnit X I).app K)) ∧
    (∀ K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      IsIso ((derivedCompletionRestrictComparison X I U (overIdeal I U)
        (fun _ _ hg ↦ hg)).app K)) :=
  ⟨isDerivedComplete_derivedRestrict_derivedCompletion X I U (overIdeal I U) (fun _ _ hg ↦ hg),
    derivedCompletionUnit_comp_derivedCompletionRestrictComparison X I U (overIdeal I U)
      (fun _ _ hg ↦ hg),
    isIso_derivedCompletionRestrictComparison_overIdeal_app X I U⟩

end AlgebraicGeometry.RingedSite

end
