module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.EssentiallySmallDerivedDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.Topology.Simplicial.SliceSite

/-!
# Perfect objects on an essentially small ringed site and on its small model

Let `(C, O)` be a ringed site whose underlying category is essentially small at the universe of
the sections of `O`, and let `v : C₀ ⥤ C` be the inclusion of a small model. Restricting
sheaves of modules along `v` is an equivalence `Mod(O) ≌ Mod(O|_{C₀})` (the Comparison Lemma,
Stacks 00XU), and it induces an equivalence `Φ : D(O) ≌ D(O|_{C₀})`. This file proves that `Φ`
and its inverse preserve perfect objects (Stacks 08G5), so that an object of `D(O)` is perfect
if and only if its restriction to the small model is.

As a consequence the dual `K^∨ = RSheafHom(K, O)` of a perfect object, computed on the small
model as `AlgebraicGeometry.RingedSite.essentiallySmallDerivedDual`, is perfect: this is
Stacks 08JJ on an essentially small ringed site.

## Main definitions

* `AlgebraicGeometry.RingedSite.smallModelOverEquivalence`: restriction of sheaves of modules
  from the slice of `C` at `v(W)` to the slice of the small model at `W`, as an equivalence.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_smallModelDerivedEquivalence_functor_obj`: the
  restriction of a perfect object to the small model is perfect.
* `AlgebraicGeometry.RingedSite.isPerfect_smallModelDerivedEquivalence_inverse_obj`: an object
  of `D(O)` whose restriction is a given perfect object is perfect.
* `AlgebraicGeometry.RingedSite.isPerfect_smallModelDerivedEquivalence_functor_obj_iff`: an
  object of `D(O)` is perfect if and only if its restriction to the small model is.
* `AlgebraicGeometry.RingedSite.isPerfect_essentiallySmallDerivedDual`: **Stacks 08JJ** on an
  essentially small ringed site.

## Implementation notes

Both transfers are instances of
`AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_of_hypotheses`, which carries
perfectness along an exact functor of module categories equipped with exact functors between
the module categories of corresponding slices and localization squares.

* For the inverse of `Φ` the functor of sites is `v` itself, and the slice functor at an object
  `W` of the small model is the inverse of the restriction along `Over.post v`, from the slice of
  `C` at `v(W)` to the slice of the small model at `W`. That restriction is an equivalence by the
  Comparison Lemma for sheaves of modules,
  `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`, since `Over.post v` is an
  equivalence of sites; and restricting to the small model and then to the slice at `W` *is*
  restricting to the slice at `v(W)` and then along `Over.post v`.
* For `Φ` the functor of sites is the quasi-inverse `s` of `v`, and the slice functor at an
  object `U` of `C` is restriction along the isomorphism `v(s(U)) ≅ U` followed by the
  restriction along `Over.post v` at `s(U)`.

In both cases the images of the functor of sites cover the final object because every object is
isomorphic to an image.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Restriction to the small model on the slices -/

/-- Restriction of sheaves of abelian groups along `Over.post v : C₀/W ⥤ C/v(W)` is an
equivalence: `Over.post v` is the functor of an equivalence of sites. -/
instance isEquivalence_sheafPushforward_overPost_smallFunctor (B : SmallModel.{u} X.C) :
    ((Over.post (X := B) (smallFunctor X)).sheafPushforwardContinuous AddCommGrpCat.{u}
      ((smallTopology X).over B) (X.J.over ((smallFunctor X).obj B))).IsEquivalence := by
  have : (Over.postEquiv B (equivSmallModel.{u} X.C).symm).symm.inverse.IsDenseSubsite
      ((smallTopology X).over B) (X.J.over ((smallFunctor X).obj B)) :=
    inferInstanceAs ((Over.post (X := B) (smallFunctor X)).IsDenseSubsite _ _)
  exact ((Over.postEquiv B (equivSmallModel.{u} X.C).symm).symm.sheafCongr
    (X.J.over ((smallFunctor X).obj B)) ((smallTopology X).over B)
    AddCommGrpCat.{u}).isEquivalence_functor

/-- Restriction of sheaves of modules along `Over.post v`, as an equivalence, at an object of
the small model; `smallModelOverEquivalence` is the same with its two categories named at the
ringed site of the small model. -/
abbrev smallModelOverRestrictionEquivalence (B : SmallModel.{u} X.C) :=
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalence ((smallTopology X).over B)
    (X.J.over ((smallFunctor X).obj B)) (Over.post (X := B) (smallFunctor X))
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((smallFunctor X).obj B))

/-- **Restriction of sheaves of modules from the slice of the site at `v(W)` to the slice of the
small model at `W`, as an equivalence of categories.** -/
def smallModelOverEquivalence
    (W : (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over
        ((smallFunctor X).obj W)) ≌
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O).over W) :=
  smallModelOverRestrictionEquivalence X W

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restricting to the small model and then to the slice at `W` is restricting to the slice at
`v(W)` and then to the slice of the small model; the two functors are equal. -/
theorem smallModelModulesEquivalence_functor_comp_overFunctor
    (W : (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).C) :
    (smallModelModulesEquivalence X).functor ⋙ SheafOfModules.overFunctor _ W =
      SheafOfModules.overFunctor _ ((smallFunctor X).obj W) ⋙
        (smallModelOverEquivalence X W).functor :=
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The restriction to a slice of the small model carries the structure sheaf to the structure
sheaf, on the nose. -/
theorem smallModelOverEquivalence_functor_obj_unit
    (W : (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).C) :
    (smallModelOverEquivalence X W).functor.obj (SheafOfModules.unit _) =
      SheafOfModules.unit _ :=
  rfl


/-! ### Covering the final object by the images of an equivalence -/

/-- A family of objects such that every object maps to one of them covers the final object. -/
private theorem coversTop_of_forall_nonempty_hom {D : Type*} [Category D]
    (K : GrothendieckTopology D) {I : Type*} (Y : I → D)
    (h : ∀ Z : D, ∃ i, Nonempty (Z ⟶ Y i)) : K.CoversTop Y := by
  intro Z
  obtain ⟨i, ⟨f⟩⟩ := h Z
  exact K.superset_covering (fun W g _ => ⟨i, ⟨g ≫ f⟩⟩) (K.top_mem Z)

variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### From the small model to the site -/

/-- The localization square for the inverse of the restriction to the small model: restricting a
sheaf of modules on the small model to the slice at `W` and extending to the slice of the site at
`v(W)` is extending to the site and then restricting to `v(W)`. -/
def smallModelInverseOverIso (W : (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).C) :
    SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O) W ⋙
        (smallModelOverEquivalence X W).inverse ≅
      (smallModelModulesEquivalence X).inverse ⋙
        SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((smallFunctor X).obj W) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (smallModelModulesEquivalence X).counitIso.symm _ ≪≫
    Functor.isoWhiskerLeft ((smallModelModulesEquivalence X).inverse ⋙
      SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((smallFunctor X).obj W)) (smallModelOverEquivalence X W).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- **An object of `D(O)` whose restriction to the small model is perfect is perfect**: the
inverse of the restriction carries perfect objects of `D(O|_{C₀})` to perfect objects of
`D(O)`. -/
theorem isPerfect_smallModelDerivedEquivalence_inverse_obj
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O)))
    (hK : (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).IsPerfect K) :
    X.IsPerfect ((smallModelDerivedEquivalence X).inverse.obj K) := by
  have hcont : (smallFunctor X).IsContinuous
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).J X.J :=
    inferInstanceAs ((smallFunctor X).IsContinuous (smallTopology X) X.J)
  have hTop : X.J.CoversTop (smallFunctor X).obj :=
    coversTop_of_forall_nonempty_hom X.J _ fun U =>
      ⟨(equivSmallModel.{u} X.C).functor.obj U, ⟨(equivSmallModel.{u} X.C).unitIso.hom.app U⟩⟩
  exact isPerfect_mapDerivedCategory_of_hypotheses (smallFunctor X)
    (smallModelModulesEquivalence X).inverse (fun W => (smallModelOverEquivalence X W).inverse)
    inferInstance inferInstance inferInstance
    (fun W => Functor.additive_of_preserves_binary_products _)
    (fun _ => inferInstance) (fun _ => inferInstance) hcont hTop
    (fun W => (smallModelOverEquivalence X W).unitIso.symm.app (SheafOfModules.unit _))
    (smallModelInverseOverIso X) K hK

/-! ### From the site to the small model -/

/-- The quasi-inverse `s : C ⥤ C₀` of the inclusion of the small model, with its target named
as the underlying category of the ringed site of the small model. -/
abbrev toSmallModel : X.C ⥤ (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).C :=
  (equivSmallModel.{u} X.C).functor

/-- The slice functor for the restriction to the small model at an object `U` of the site:
restriction along the isomorphism `v(s(U)) ≅ U`, followed by restriction from the slice of the
site at `v(s(U))` to the slice of the small model at `s(U)`. -/
def smallModelOverFunctor (U : X.C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O).over
          ((toSmallModel X).obj U)) :=
  SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      ((equivSmallModel.{u} X.C).unitIso.inv.app U) ⋙
    (smallModelOverEquivalence X ((toSmallModel X).obj U)).functor

/-- `smallModelOverFunctor X U` is additive. -/
instance (U : X.C) : (smallModelOverFunctor X U).Additive :=
  have : (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      ((equivSmallModel.{u} X.C).unitIso.inv.app U)).Additive := ⟨by intros; rfl⟩
  have : (smallModelOverEquivalence X
      ((toSmallModel X).obj U)).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  inferInstanceAs (Functor.Additive (_ ⋙ _))

/-- `smallModelOverFunctor X U` preserves finite limits. -/
instance (U : X.C) : PreservesFiniteLimits (smallModelOverFunctor X U) :=
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((equivSmallModel.{u} X.C).unitIso.inv.app U)
  inferInstanceAs (PreservesFiniteLimits (_ ⋙ _))

/-- `smallModelOverFunctor X U` preserves finite colimits. -/
instance (U : X.C) : PreservesFiniteColimits (smallModelOverFunctor X U) :=
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((equivSmallModel.{u} X.C).unitIso.inv.app U)
  inferInstanceAs (PreservesFiniteColimits (_ ⋙ _))

/-- The localization square for the restriction to the small model: restricting to the slice
at `U` and then by `smallModelOverFunctor` is restricting to the small model and then to the
slice at `s(U)`. -/
def smallModelOverFunctorIso (U : X.C) :
    SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
        smallModelOverFunctor X U ≅
      (smallModelModulesEquivalence X).functor ⋙
        SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O)
          ((toSmallModel X).obj U) :=
  Functor.isoWhiskerRight (SheafOfModules.overFunctorMap.{u} _
      ((equivSmallModel.{u} X.C).unitIso.inv.app U))
    (smallModelOverEquivalence X ((toSmallModel X).obj U)).functor

/-- **The restriction of a perfect object of `D(O)` to the small model is perfect.** -/
theorem isPerfect_smallModelDerivedEquivalence_functor_obj
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).IsPerfect
      ((smallModelDerivedEquivalence X).functor.obj K) := by
  have hcont : (toSmallModel X).IsContinuous X.J
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).J :=
    inferInstanceAs ((equivSmallModel.{u} X.C).functor.IsContinuous X.J (smallTopology X))
  have hTop : (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).J.CoversTop
      (toSmallModel X).obj :=
    coversTop_of_forall_nonempty_hom _ _ fun W =>
      ⟨(smallFunctor X).obj W, ⟨(equivSmallModel.{u} X.C).counitIso.inv.app W⟩⟩
  exact isPerfect_mapDerivedCategory_of_hypotheses (toSmallModel X)
    (smallModelModulesEquivalence X).functor (smallModelOverFunctor X)
    inferInstance inferInstance inferInstance
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance) hcont hTop
    (fun U => (smallModelOverEquivalence X ((toSmallModel X).obj U)).functor.mapIso
      (SheafOfModules.overMapUnitIso ((equivSmallModel.{u} X.C).unitIso.inv.app U)))
    (smallModelOverFunctorIso X) K hK

/-- **An object of `D(O)` is perfect if and only if its restriction to the small model is.** -/
theorem isPerfect_smallModelDerivedEquivalence_functor_obj_iff
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).IsPerfect
        ((smallModelDerivedEquivalence X).functor.obj K) ↔ X.IsPerfect K := by
  refine ⟨fun h => ?_, isPerfect_smallModelDerivedEquivalence_functor_obj X K⟩
  exact IsPerfect.of_iso _ (isPerfect_smallModelDerivedEquivalence_inverse_obj X _ h)
    ((smallModelDerivedEquivalence X).unitIso.symm.app K)

/-! ### Stacks 08JJ on an essentially small ringed site -/

/-- **Stacks 08JJ on an essentially small ringed site.** The dual `K^∨ = RSheafHom(K, O)` of a
perfect object `K` of `D(O)`, computed on a small model of the site, is perfect.

The restriction of `K` to the small model is perfect, its dual there is perfect by Stacks 08JJ
(`AlgebraicGeometry.RingedSite.isPerfect_derivedDual`), and the object of `D(O)` corresponding to
it is perfect. -/
theorem isPerfect_essentiallySmallDerivedDual
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) : X.IsPerfect (essentiallySmallDerivedDual X K) :=
  isPerfect_smallModelDerivedEquivalence_inverse_obj X _
    (isPerfect_derivedDual _ _ (isPerfect_smallModelDerivedEquivalence_functor_obj X K hK))

end AlgebraicGeometry.RingedSite

end
