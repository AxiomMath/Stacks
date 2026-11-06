module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GeometricPointStalkCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableSurjectiveInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.RepresentableFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.CategoryTheory.Triangulated.DimensionShifting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenClosedDevissage
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeTorsionColimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject

/-!
# Derived proper base change for algebraic spaces over an affine base

Let `S` be a scheme and `f : Y ⟶ h_V` a proper morphism of algebraic spaces over `S` to the
space represented by an affine scheme `V`. For every cartesian square over `f`, the base change
map `g⁻¹ R f_* E ⟶ R f'_* (g')⁻¹ E` is invertible at every bounded below `E` with torsion
cohomology sheaves (`AlgebraicGeometry.BigEtaleSpaceSite.affineBaseProperBaseChange`), granted
proper base change for sheaves of sets (Stacks 0DG0, which holds granted Stacks 0A3U) and the
proper base change theorem for schemes read on the spaces-étale sites
(`RepresentableProperBaseChange`, which holds granted Stacks 095T). Over an arbitrary base this
gives Stacks 0DG2 and 0DG3, granted Stacks 0A3U and Stacks 095T.

## Main results

All names are in the namespace `AlgebraicGeometry.BigEtaleSpaceSite`.

* `CohomologyCommutesWithBaseChange`: the base change map is invertible at every torsion sheaf,
  for every cartesian square over a morphism.
* `cohomologyCommutesWithBaseChange_of_yonedaSpace`: this holds for a proper morphism out of a
  represented algebraic space.
* `mono_smallEtaleAbelianAdjunction_unit_app_of_isSurjective`: the unit `A ⟶ h_* h⁻¹ A` along a
  surjection out of a represented space is a monomorphism.
* `isIso_spacesEtaleDerivedBaseChange_app_of_nsmul_id_eq_zero` and
  `isIso_spacesEtaleDerivedBaseChange_app_of_torsionSheafProperty`: the dimension shift along a
  Chow cover, and the passage to torsion sheaves.
* `cohomologyCommutesWithBaseChange_of_isProper_toAffine` and `affineBaseProperBaseChange`: the
  case of an affine base.
* `isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_representable` and
  `isIso_spacesEtaleDerivedBaseChange_app_singleFunctor_of_isProper_of_representable`: Stacks 0DG3
  and Stacks 0DG2, granted Stacks 0A3U and the proper base change theorem for schemes, Stacks
  095T.

## References

* [Stacks Project, Tag 0DG2](https://stacks.math.columbia.edu/tag/0DG2)
* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 07U6](https://stacks.math.columbia.edu/tag/07U6)
* [Stacks Project, Tag 0DFX](https://stacks.math.columbia.edu/tag/0DFX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Homology.DerivedSquare (derivedSquare totalRightDerived totalRightDerivedUnit)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every morphism of represented algebraic spaces is the Yoneda image of a morphism of the
site. -/
theorem exists_yonedaSpaceHom_eq {V W : BigFppfOver B S hS}
    (a : yonedaSpace B S hS W ⟶ yonedaSpace B S hS V) : ∃ m : W ⟶ V, yonedaSpaceHom m = a :=
  ⟨yoneda.preimage a.hom, ObjectProperty.hom_ext _ (yoneda.map_preimage _)⟩

/-- **A fibre product of two represented algebraic spaces over an algebraic space is
represented**, in the form of a cartesian square whose corner is a represented algebraic
space. -/
theorem exists_isPullback_yonedaSpace {Y : AlgebraicSpaces B S hS} {Z V : BigFppfOver B S hS}
    (h : yonedaSpace B S hS Z ⟶ Y) (v : yonedaSpace B S hS V ⟶ Y) :
    ∃ (P : BigFppfOver B S hS) (p : yonedaSpace B S hS P ⟶ yonedaSpace B S hS Z)
      (q : yonedaSpace B S hS P ⟶ yonedaSpace B S hS V), IsPullback p q h v := by
  obtain ⟨P, ⟨r⟩⟩ := (isRepresentable_pullback_algebraicSpaces B S hS
    (Functor.IsRepresentable.mk' (Iso.refl (yoneda.obj Z)))
    (Functor.IsRepresentable.mk' (Iso.refl (yoneda.obj V))) h v).has_representation
  let e : yonedaSpace B S hS P ≅ pullback h v :=
    (ObjectProperty.fullyFaithfulι _).preimageIso r.toIso
  exact ⟨P, e.hom ≫ pullback.fst h v, e.hom ≫ pullback.snd h v,
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, pullback.condition]⟩ e
      rfl rfl⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard smallEtaleAbelianInverseImage_additive

/-- **Cohomology commutes with base change for `f`**: for every cartesian square
```
Y' --g'--> Y
|f'        |f
v          v
X' --g---> X
```
the base change map `g⁻¹ R f_* F ⟶ R f'_* (g')⁻¹ F` is invertible at every torsion abelian sheaf
`F` on the spaces-étale site of `Y`, placed in degree zero. -/
def CohomologyCommutesWithBaseChange {X Y : T.Spaces} (f : Y ⟶ X) : Prop :=
  ∀ ⦃X' Y' : T.Spaces⦄ (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}),
    Stacks.Torsion.torsionSheafProperty _ F →
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
      ((DerivedCategory.singleFunctor _ 0).obj F))

/-- A torsion abelian sheaf placed in degree zero has torsion cohomology sheaves. -/
theorem hasTorsionCohomology_singleFunctor_obj {Y : T.Spaces}
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) :
    HasTorsionCohomology T ((DerivedCategory.singleFunctor _ 0).obj F) := by
  intro q
  by_cases hq : q = 0
  · subst hq
    exact Stacks.Torsion.torsionSheafProperty_of_iso _
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · refine (Stacks.Torsion.torsionSheafProperty _).prop_of_isZero ?_
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact DerivedCategory.isZero_of_isGE _ 0 q hq
    · exact DerivedCategory.isZero_of_isLE _ 0 q hq

/-- If cohomology commutes with base change for `f`, the base change map of every cartesian square
over `f` is invertible at every bounded below object with torsion cohomology sheaves. -/
theorem CohomologyCommutesWithBaseChange.isIso_app {X Y : T.Spaces} {f : Y ⟶ X}
    (hf : CohomologyCommutesWithBaseChange T f) {X' Y' : T.Spaces} (g : X' ⟶ X) (g' : Y' ⟶ Y)
    (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hE : E.IsGE n) (hT : HasTorsionCohomology T E) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app E) :=
  isIso_spacesEtaleDerivedBaseChange_app_of_isGE T f g g' f' sq (hf g g' f' sq) E n hE hT

/-! ### Representable sources -/

/-- **Derived proper base change for a morphism of represented algebraic spaces.** For a morphism
`m : P ⟶ V` of the site whose Yoneda image is proper and every `a : h_W ⟶ h_V`, the base change
map of the cartesian square of represented spaces over `a` built from the fibre product
`P ×_V W` of the site is invertible at every bounded below object with torsion cohomology sheaves,
granted the proper base change theorem for schemes read on the spaces-étale sites (`hrep`). -/
theorem exists_isPullback_isIso_spacesEtaleDerivedBaseChange_yonedaSpaceHom
    (hrep : RepresentableProperBaseChange T) {P V W : BigFppfOver T.fppfSite S T.fppf_mem}
    (m : P ⟶ V) (hm : Space.IsProper T.fppfSite S T.fppf_mem (Space.yonedaSpaceHom m).hom)
    (a : Space.yonedaSpace T.fppfSite S T.fppf_mem W ⟶
      Space.yonedaSpace T.fppfSite S T.fppf_mem V) :
    ∃ (Y'' : T.Spaces) (a' : Y'' ⟶ Space.yonedaSpace T.fppfSite S T.fppf_mem P)
      (f'' : Y'' ⟶ Space.yonedaSpace T.fppfSite S T.fppf_mem W)
      (sqa : IsPullback a' f'' (Space.yonedaSpaceHom m) a),
      ∀ (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
          (Space.yonedaSpace T.fppfSite S T.fppf_mem P)) Ab.{u + 1})) (n : ℤ),
        E.IsGE n → HasTorsionCohomology T E →
        IsIso ((spacesEtaleDerivedBaseChange T (Space.yonedaSpaceHom m) a a' f'' sqa).app E) := by
  obtain ⟨b, rfl⟩ := Space.exists_yonedaSpaceHom_eq a
  have sq₀ := IsPullback.of_hasPullback m b
  have sq : IsPullback (Space.yonedaSpaceHom (pullback.fst m b))
      (Space.yonedaSpaceHom (pullback.snd m b)) (Space.yonedaSpaceHom m)
      (Space.yonedaSpaceHom b) :=
    Space.isPullback_of_isPullback_hom T.fppfSite S T.fppf_mem (sq₀.map yoneda)
  exact ⟨_, _, _, sq, fun E n hE hT ↦ isIso_spacesEtaleDerivedBaseChange_app_of_isGE T _ _ _ _ sq
    (fun F hF ↦ hrep m b _ _ sq₀
      (Space.isProper_toScheme_map_of_isProper_yoneda_map T.fppfSite S T.fppf_mem m hm) sq F hF)
    E n hE hT⟩

/-- **Cohomology commutes with base change for a proper morphism out of a represented algebraic
space.** Granted Stacks 0A3U (`h0A3U`, which gives proper base change for sheaves of sets,
Stacks 0DG0) and the proper base change theorem for schemes on the spaces-étale sites (`hrep`),
cohomology commutes with base change for every proper morphism `h : h_Z ⟶ Y`. -/
theorem cohomologyCommutesWithBaseChange_of_yonedaSpace
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (hrep : RepresentableProperBaseChange T) {Y : T.Spaces}
    {Z : BigFppfOver T.fppfSite S T.fppf_mem}
    (h : Space.yonedaSpace T.fppfSite S T.fppf_mem Z ⟶ Y)
    (hh : Space.IsProper T.fppfSite S T.fppf_mem h.hom) :
    CohomologyCommutesWithBaseChange T h := by
  intro X' Y' g g' f' sq F hF
  refine isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_affineCharts T h0A3U h hh
    (fun V₀ W₀ _ _ v _ a ↦ ?_) g g' f' sq _ 0 inferInstance
    (hasTorsionCohomology_singleFunctor_obj T F hF)
  obtain ⟨P, p, q, sqV⟩ := Space.exists_isPullback_yonedaSpace h v
  obtain ⟨m, rfl⟩ := Space.exists_yonedaSpaceHom_eq q
  have hm : Space.IsProper T.fppfSite S T.fppf_mem (Space.yonedaSpaceHom m).hom :=
    (Space.isProper_isStableUnderBaseChange T.fppfSite S T.fppf_mem).of_isPullback sqV hh
  obtain ⟨Y'', a', f'', sqa, hE⟩ :=
    exists_isPullback_isIso_spacesEtaleDerivedBaseChange_yonedaSpaceHom T hrep m hm a
  exact ⟨_, p, _, sqV, Y'', a', f'', sqa, hE⟩

/-! ### The unit along a surjection out of a represented space -/

/-- **Zero objects on the spaces-étale site of `Y` are detected on affine charts through étale
charts.** An abelian sheaf `G` whose inverse image along every affine chart through an étale chart
`w : h_W ⟶ Y` vanishes is zero. -/
theorem isZero_of_isZero_abelianInverseImage_affineThroughEtaleChart {Y : T.Spaces}
    (G : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (h : ∀ V : Over Y, IsAffineThroughEtaleChart T Y V →
      IsZero ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T V.hom)).obj G)) :
    IsZero G := by
  let M := (CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T Y)).obj G
  have hM : IsIso (0 : M ⟶ M) := by
    refine isIso_of_isIso_smallEtaleRestriction_map_of_affineThroughEtaleChart T 0 fun V hV ↦ ?_
    have hR : IsZero ((smallEtaleRestriction T V.hom).obj M) :=
      (h V hV).of_iso ((pulledAbelianInverseImageIso T V.hom).app G)
    rw [Functor.map_zero]
    exact ⟨⟨0, hR.eq_of_src _ _, hR.eq_of_src _ _⟩⟩
  have hM' : IsZero M := by
    rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : M ⟶ M), comp_zero]
  exact (Functor.map_isZero (bigToSmallEtaleRestriction T Y) hM').of_iso
    ((bigToSmall_abelianInverseImage_comp_restrictionIso T Y).app G).symm

/-- **The unit `A ⟶ h_* h⁻¹ A` is a monomorphism for a surjection `h : h_Z ⟶ Y` out of a
represented space** (the first assertion of Stacks 0DFX, for such `h`). -/
theorem mono_smallEtaleAbelianAdjunction_unit_app_of_isSurjective {Y : T.Spaces}
    {Z : BigFppfOver T.fppfSite S T.fppf_mem} (h : Space.yonedaSpace T.fppfSite S T.fppf_mem Z ⟶ Y)
    (hh : Space.IsSurjective T.fppfSite S T.fppf_mem h.hom)
    (A : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) :
    Mono ((smallEtaleAbelianAdjunction T h).unit.app A) := by
  let adj := smallEtaleAbelianAdjunction T h
  let L := CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T h)
  let η := adj.unit.app A
  have hL : Mono (L.map η) := (SplitMono.mk _ (adj.left_triangle_components A)).mono
  have hK : IsZero (L.obj (kernel η)) :=
    (isZero_kernel_of_mono (L.map η)).of_iso (PreservesKernel.iso L η)
  refine Preadditive.mono_of_isZero_kernel _
    (isZero_of_isZero_abelianInverseImage_affineThroughEtaleChart T _ fun V hV ↦ ?_)
  obtain ⟨W₀, V₀, -, -, v, a, -, rfl⟩ := hV
  obtain ⟨P, p, q, sqV⟩ := Space.exists_isPullback_yonedaSpace h (a ≫ v)
  obtain ⟨m, rfl⟩ := Space.exists_yonedaSpaceHom_eq q
  have hm := Space.surjective_of_isSurjective_yoneda_map T.fppfSite S T.fppf_mem m
    (Space.isSurjective_of_isPullback T.fppfSite S T.fppf_mem sqV hh)
  refine representableSurjectiveReflectsZero T m hm _ ?_
  refine IsZero.of_iso ?_ ((smallEtaleAbelianInverseImageCompIso T (Space.yonedaSpaceHom m)
    (a ≫ v)).app (kernel η)).symm
  refine IsZero.of_iso ?_ (eqToIso (congrArg (fun k ↦
    (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T k)).obj (kernel η)) sqV.w.symm))
  refine IsZero.of_iso ?_ ((smallEtaleAbelianInverseImageCompIso T p h).app (kernel η))
  exact Functor.map_isZero (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T p)) hK

/-! ### Injective sheaves of `ℤ/nℤ`-modules on the spaces-étale sites -/

section ZMod

open Stacks.Cohomology.ZModSheaf

/-- Sheafification of presheaves of commutative rings on the spaces-étale site, at the coefficient
universe `u + 1` of the site. -/
instance hasSheafify_commRingCat_spacesEtale (Y : T.Spaces) :
    HasSheafify (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) CommRingCat.{u + 1} :=
  Stacks.SheafifyCommRing.hasSheafifyCommRingCat.{0} _

/-- Sheafification of presheaves of commutative rings on the spaces-étale site inverts exactly
the locally bijective maps. -/
instance wEqualsLocallyBijective_commRingCat_spacesEtale (Y : T.Spaces) :
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y).WEqualsLocallyBijective
      CommRingCat.{u + 1} :=
  inferInstance

/-- Sheafification of abelian presheaves on the spaces-étale site inverts exactly the locally
bijective maps. -/
instance wEqualsLocallyBijective_addCommGrpCat_spacesEtale (Y : T.Spaces) :
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  inferInstance

/-- Sheaves of `ℤ/nℤ`-modules on the spaces-étale site form an abelian category. -/
instance abelian_zmodModules_spacesEtale (Y : T.Spaces) (n : ℕ) :
    Abelian (SheafOfModules.{u + 1}
      (zmodRingSheaf.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) n)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u + 1, u + 1, u + 1, 0} _

/-- Sheaves of `ℤ/nℤ`-modules on the spaces-étale site have enough injectives. -/
instance enoughInjectives_zmodModules_spacesEtale (Y : T.Spaces) (n : ℕ) :
    EnoughInjectives (SheafOfModules.{u + 1}
      (zmodRingSheaf.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) n)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u + 1, u + 1, 0} _

/-- An abelian sheaf on the spaces-étale site is killed by `n` exactly when `n` times its identity
is zero. -/
private theorem nsmul_id_eq_zero_iff_forall_nsmul_eq_zero {Y : T.Spaces} (n : ℕ)
    (A : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) :
    n • 𝟙 A = 0 ↔ ∀ (U : (Space.SpacesEtale T.fppfSite S T.fppf_mem Y)ᵒᵖ)
      (x : ToType (A.obj.obj U)), n • x = 0 := by
  simp only [← natCast_zsmul]
  exact zsmul_id_eq_zero_iff A n

/-- The underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules on the spaces-étale site is killed
by `n`. -/
theorem nsmul_id_toSheaf_spacesEtale_eq_zero {Y : T.Spaces} (n : ℕ)
    (M : SheafOfModules.{u + 1}
      (zmodRingSheaf.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) n)) :
    n • 𝟙 ((SheafOfModules.toSheaf _).obj M) = 0 := by
  refine (nsmul_id_eq_zero_iff_forall_nsmul_eq_zero T n _).2 fun U x ↦ ?_
  exact nsmul_toSheaf_eq_zero.{u + 1, u + 1} _ n M U x

/-- **An abelian sheaf on the spaces-étale site killed by `n` embeds in the underlying abelian
sheaf of an injective sheaf of `ℤ/nℤ`-modules.** -/
theorem exists_mono_toSheaf_injective_spacesEtale {Y : T.Spaces} (n : ℕ)
    (A : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hA : n • 𝟙 A = 0) :
    ∃ (J : SheafOfModules.{u + 1}
        (zmodRingSheaf.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) n))
      (_ : Injective J) (i : A ⟶ (SheafOfModules.toSheaf _).obj J), Mono i := by
  have hA' := (nsmul_id_eq_zero_iff_forall_nsmul_eq_zero T n A).1 hA
  set M := torsionSheafToModules.{u + 1, u + 1} _ n A hA'
  exact ⟨Injective.under M, inferInstance,
    (torsionSheafToModulesIso.{u + 1, u + 1} _ n A hA').inv ≫
      (SheafOfModules.toSheaf _).map (Injective.ι M), inferInstance⟩

/-- **The direct image of an injective sheaf of `ℤ/nℤ`-modules has no higher cohomology**, read in
the unbounded derived category (Stacks 03FD): `H^q(R h_* (J[0])) = 0` for `q > 0`. -/
theorem isZero_homology_totalRightDerived_smallEtalePushforward_toSheaf {X Y : T.Spaces}
    (h : Y ⟶ X) (n : ℕ)
    (J : SheafOfModules.{u + 1}
      (zmodRingSheaf.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) n))
    [Injective J] (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((totalRightDerived (smallEtalePushforward T h)).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((SheafOfModules.toSheaf _).obj J)))) := by
  have := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u + 1, 0}
    (J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
  let := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem h).isContinuous
  refine Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero
    (smallEtalePushforward T h) _ (totalRightDerivedUnit (smallEtalePushforward T h))
    Stacks.Cohomology.Localization.enoughKInjectives _ (fun p hp ↦ ?_) 0 q hq
  obtain ⟨p, rfl⟩ : ∃ p' : ℕ, p = p' + 1 := ⟨p - 1, by omega⟩
  exact Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{0}
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem h).functor _ J p

end ZMod

/-! ### The base change map at a direct image -/

/-- The direct image of abelian sheaves on the spaces-étale sites preserves K-injective
complexes. -/
theorem isKInjective_smallEtalePushforward {X Y : T.Spaces} (h : Y ⟶ X)
    (I : CochainComplex (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((smallEtalePushforward T h).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact (smallEtalePushforward T h)
    (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T h))
    (smallEtaleAbelianAdjunction T h) I

/-- The direct image along a composite is the composite of the direct images (Stacks 03G2,
part (2)). -/
def smallEtalePushforwardCompIso {X Y Z : T.Spaces} (a : X ⟶ Y) (b : Y ⟶ Z) :
    smallEtalePushforward T a ⋙ smallEtalePushforward T b ≅ smallEtalePushforward T (a ≫ b) :=
  Adjunction.rightAdjointUniq
    (((smallEtaleAbelianAdjunction T b).comp (smallEtaleAbelianAdjunction T a)).ofNatIsoLeft
      (smallEtaleAbelianInverseImageCompIso T a b).symm)
    (smallEtaleAbelianAdjunction T (a ≫ b))

/-- **An abelian sheaf without higher direct images is its own derived direct image**, placed in
degree zero. -/
theorem nonempty_singleFunctor_iso_totalRightDerived_smallEtalePushforward {X Y : T.Spaces}
    (h : Y ⟶ X) (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hF : ∀ q : ℤ, 0 < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((totalRightDerived (smallEtalePushforward T h)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)))) :
    Nonempty ((DerivedCategory.singleFunctor _ 0).obj ((smallEtalePushforward T h).obj F) ≅
      (totalRightDerived (smallEtalePushforward T h)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  set K := (totalRightDerived (smallEtalePushforward T h)).obj
    ((DerivedCategory.singleFunctor _ 0).obj F)
  have : K.IsGE 0 :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj (smallEtalePushforward T h) _ 0
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 fun i hi ↦ hF i hi
  obtain ⟨Y₀, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  have : PreservesFiniteLimits (smallEtalePushforward T h) := by
    have : PreservesLimitsOfSize.{0, 0} (smallEtalePushforward T h) :=
      (smallEtaleAbelianAdjunction T h).rightAdjoint_preservesLimits
    infer_instance
  let e₀ : Y₀ ≅ (smallEtalePushforward T h).obj F :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app Y₀).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso e.symm ≪≫
      Stacks.DerivedFunctor.homologyTotalRightDerivedSingleSelfIso (smallEtalePushforward T h) _
        (totalRightDerivedUnit (smallEtalePushforward T h))
        Stacks.Cohomology.Localization.enoughKInjectives F 0
  exact ⟨(DerivedCategory.singleFunctor _ 0).mapIso e₀.symm ≪≫ e.symm⟩

/-- The underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules, `n > 0`, is torsion. -/
theorem torsionSheafProperty_toSheaf_zmod_spacesEtale {Y : T.Spaces} {n : ℕ} (hn : 0 < n)
    (M : SheafOfModules.{u + 1} (Stacks.Cohomology.ZModSheaf.zmodRingSheaf.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) n)) :
    Stacks.Torsion.torsionSheafProperty _ ((SheafOfModules.toSheaf _).obj M) := fun U _ ↦
  ⟨⊤, GrothendieckTopology.top_mem _ U, fun _ _ _ ↦
    ⟨n, hn, Stacks.Cohomology.ZModSheaf.nsmul_toSheaf_eq_zero.{u + 1, u + 1} _ n M _ _⟩⟩

/-- **The base change map of `f` is invertible at the direct image along `h` of an injective
sheaf of `ℤ/nℤ`-modules**, `n > 0`, when cohomology commutes with base change for `h` and for
`h ≫ f`, granted Stacks 0A3U (`h0A3U`, which gives proper base change for sheaves of sets,
Stacks 0DG0). -/
theorem isIso_spacesEtaleDerivedBaseChange_app_smallEtalePushforward_toSheaf
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    {X Y Z : T.Spaces} (f : Y ⟶ X) (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (h : Z ⟶ Y) (hh : Space.IsProper T.fppfSite S T.fppf_mem h.hom)
    (hch : CohomologyCommutesWithBaseChange T h)
    (hchf : CohomologyCommutesWithBaseChange T (h ≫ f))
    {X' Y' : T.Spaces} (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    {n : ℕ} (hn : 0 < n)
    (J : SheafOfModules.{u + 1} (Stacks.Cohomology.ZModSheaf.zmodRingSheaf.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z) n)) [Injective J] :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
      ((DerivedCategory.singleFunctor _ 0).obj
        ((smallEtalePushforward T h).obj ((SheafOfModules.toSheaf _).obj J)))) := by
  set Jab := (SheafOfModules.toSheaf _).obj J
  have hJ := torsionSheafProperty_toSheaf_zmod_spacesEtale T hn J
  obtain ⟨φ⟩ := nonempty_singleFunctor_iso_totalRightDerived_smallEtalePushforward T h Jab
    (isZero_homology_totalRightDerived_smallEtalePushforward_toSheaf T h n J)
  rw [NatTrans.isIso_app_iff_of_iso _ φ]
  obtain ⟨I, q, hI, hq⟩ :=
    Stacks.Cohomology.Localization.enoughKInjectives ((CochainComplex.singleFunctor _ 0).obj Jab)
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := _) q).2 hq
  let e₁ : (DerivedCategory.singleFunctor _ 0).obj Jab ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app Jab ≪≫ asIso (DerivedCategory.Q.map q) ≪≫
      ((DerivedCategory.quotientCompQhIso _).app I).symm
  have hu : IsIso ((totalRightDerivedUnit (smallEtalePushforward T h)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I
  let I' := ((smallEtalePushforward T h).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let e₂ : (totalRightDerived (smallEtalePushforward T h)).obj
        ((DerivedCategory.singleFunctor _ 0).obj Jab) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I') :=
    (totalRightDerived (smallEtalePushforward T h)).mapIso e₁ ≪≫
      (asIso ((totalRightDerivedUnit (smallEtalePushforward T h)).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm
  rw [NatTrans.isIso_app_iff_of_iso _ e₂]
  have : CochainComplex.IsKInjective I' := isKInjective_smallEtalePushforward T h I
  have := isIso_spacesEtaleAbelianBaseChange T f g g' f' sq
    (Space.isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange T.fppfSite S T.fppf_mem
      h0A3U f hf g g' f' sq)
  rw [isIso_spacesEtaleDerivedBaseChange_app_iff T f g g' f' sq I']
  have sqh := IsPullback.of_hasPullback h g'
  have sqfh : IsPullback (pullback.fst h g') (pullback.snd h g' ≫ f') (h ≫ f) g :=
    sqh.paste_vert sq
  have hhf : Space.IsProper T.fppfSite S T.fppf_mem (h ≫ f).hom :=
    Space.isProper_comp T.fppfSite S T.fppf_mem Z.2 Y.2 X.2 h.hom f.hom hh hf
  have := isIso_spacesEtaleAbelianBaseChange T h g' _ _ sqh
    (Space.isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange T.fppfSite S T.fppf_mem
      h0A3U h hh g' _ _ sqh)
  have := isIso_spacesEtaleAbelianBaseChange T (h ≫ f) g _ _ sqfh
    (Space.isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange T.fppfSite S T.fppf_mem
      h0A3U (h ≫ f) hhf g _ _ sqfh)
  have hτh := (NatTrans.isIso_app_iff_of_iso _ e₁).mp (hch g' _ _ sqh Jab hJ)
  have hτhf := (NatTrans.isIso_app_iff_of_iso _ e₁).mp (hchf g _ _ sqfh Jab hJ)
  rw [isIso_spacesEtaleDerivedBaseChange_app_iff T h g' _ _ sqh I] at hτh
  rw [isIso_spacesEtaleDerivedBaseChange_app_iff T (h ≫ f) g _ _ sqfh I] at hτhf
  let c := asIso (spacesEtaleAbelianBaseChange T h g' _ _ sqh)
  let eM : ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I') ≅
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((smallEtalePushforward T (pullback.snd h g')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((CategoryTheory.Sites.abelianInverseImage
            (smallEtaleMorphism T (pullback.fst h g'))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) :=
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (smallEtalePushforward T h ⋙
            CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')))
          (ComplexShape.up ℤ)).app I ≪≫
        (NatIso.mapHomologicalComplex c (ComplexShape.up ℤ)).app I ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (CategoryTheory.Sites.abelianInverseImage
              (smallEtaleMorphism T (pullback.fst h g')) ⋙
            smallEtalePushforward T (pullback.snd h g')))
          (ComplexShape.up ℤ)).symm.app I)
  rw [NatTrans.isIso_app_iff_of_iso _ eM]
  exact (Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_comp_iff
    (smallEtalePushforward T (pullback.snd h g')) (smallEtalePushforward T f')
    (smallEtalePushforward T (pullback.snd h g' ≫ f'))
    (smallEtalePushforwardCompIso T _ _) (fun I _ ↦ isKInjective_smallEtalePushforward T _ I)
    _ hτh).mp hτhf

/-! ### Sheaves killed by an integer -/

/-- At an object of `D^{≥0}`, the base change map is an isomorphism on cohomology in every
negative degree, where both sides vanish. -/
theorem isIso_homology_spacesEtaleDerivedBaseChange_app_of_isGE {X Y X' Y' : T.Spaces}
    (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) [E.IsGE 0] (q : ℤ) (hq : q < 0) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((spacesEtaleDerivedBaseChange T f g g' f' sq).app E)) := by
  have h₁ : ((totalRightDerived (smallEtalePushforward T f) ⋙
      (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)).mapDerivedCategory).obj
        E).IsGE 0 :=
    Functor.isGE_obj_mapDerivedCategory _ _ 0
      (Stacks.DerivedFunctor.isGE_totalRightDerived_obj _ E 0)
  have : ((CategoryTheory.Sites.abelianInverseImage
      (smallEtaleMorphism T g')).mapDerivedCategory.obj E).IsGE 0 :=
    Functor.isGE_obj_mapDerivedCategory _ E 0 inferInstance
  have h₂ : (((CategoryTheory.Sites.abelianInverseImage
        (smallEtaleMorphism T g')).mapDerivedCategory ⋙
      totalRightDerived (smallEtalePushforward T f')).obj E).IsGE 0 :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj _ _ 0
  have hs := DerivedCategory.isZero_of_isGE ((totalRightDerived
    (smallEtalePushforward T f) ⋙
      (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)).mapDerivedCategory).obj E)
      0 q hq
  have ht := DerivedCategory.isZero_of_isGE (((CategoryTheory.Sites.abelianInverseImage
        (smallEtaleMorphism T g')).mapDerivedCategory ⋙
      totalRightDerived (smallEtalePushforward T f')).obj E) 0 q hq
  exact ⟨⟨0, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩

/-- **A sheaf on `Y_étale` killed by `n` embeds in the direct image along a surjection
`h : h_Z ⟶ Y` of an injective sheaf of `ℤ/nℤ`-modules.** -/
theorem exists_mono_smallEtalePushforward_toSheaf_injective {Y : T.Spaces}
    {Z : BigFppfOver T.fppfSite S T.fppf_mem} (h : Space.yonedaSpace T.fppfSite S T.fppf_mem Z ⟶ Y)
    (hs : Space.IsSurjective T.fppfSite S T.fppf_mem h.hom) (n : ℕ)
    (A : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hA : n • 𝟙 A = 0) :
    ∃ (J : SheafOfModules.{u + 1} (Stacks.Cohomology.ZModSheaf.zmodRingSheaf.{u + 1}
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
          (Space.yonedaSpace T.fppfSite S T.fppf_mem Z)) n)) (_ : Injective J)
      (i : A ⟶ (smallEtalePushforward T h).obj ((SheafOfModules.toSheaf _).obj J)), Mono i := by
  obtain ⟨J, hJ, i₀, hi₀⟩ := exists_mono_toSheaf_injective_spacesEtale T n
    ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T h)).obj A)
    (Stacks.EtaleCohomology.nsmul_id_map_eq_zero _ hA)
  refine ⟨J, hJ, (smallEtaleAbelianAdjunction T h).unit.app A ≫
    (smallEtalePushforward T h).map i₀, ?_⟩
  have := mono_smallEtaleAbelianAdjunction_unit_app_of_isSurjective T h hs A
  have : PreservesLimitsOfSize.{0, 0} (smallEtalePushforward T h) :=
    (smallEtaleAbelianAdjunction T h).rightAdjoint_preservesLimits
  have hc : PreservesLimit (cospan i₀ i₀) (smallEtalePushforward T h) :=
    (PreservesLimitsOfSize.preservesLimitsOfShape (J := WalkingCospan)).preservesLimit
  have : Mono ((smallEtalePushforward T h).map i₀) := preserves_mono_of_preservesLimit _ i₀
  exact mono_comp _ _

/-- **The base change map of `f` is invertible at every sheaf killed by a positive integer `n`**,
given a proper surjection `h : h_Z ⟶ Y` for which cohomology commutes with base change, as it
does for `h ≫ f`, and granted Stacks 0A3U (`h0A3U`). -/
theorem isIso_spacesEtaleDerivedBaseChange_app_of_nsmul_id_eq_zero
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    {X Y : T.Spaces} (f : Y ⟶ X) (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    {Z : BigFppfOver T.fppfSite S T.fppf_mem} (h : Space.yonedaSpace T.fppfSite S T.fppf_mem Z ⟶ Y)
    (hh : Space.IsProper T.fppfSite S T.fppf_mem h.hom)
    (hs : Space.IsSurjective T.fppfSite S T.fppf_mem h.hom)
    (hch : CohomologyCommutesWithBaseChange T h)
    (hchf : CohomologyCommutesWithBaseChange T (h ≫ f))
    {X' Y' : T.Spaces} (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (n : ℕ) (hn : 0 < n)
    (A : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hA : n • 𝟙 A = 0) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
      ((DerivedCategory.singleFunctor _ 0).obj A)) := by
  refine Stacks.Triangulated.isIso_app_of_dimensionShifting
    (spacesEtaleDerivedBaseChange T f g g' f' sq)
    (fun K ↦ ∃ A : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1},
      n • 𝟙 A = 0 ∧ K = (DerivedCategory.singleFunctor _ 0).obj A) ?_ ?_ _ ⟨A, hA, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨J, hJ, i, hi⟩ := exists_mono_smallEtalePushforward_toSheaf_injective T h hs n A hA
    have hc : HasColimit (parallelPair i 0) := HasCokernels.has_colimit i
    have hS := ShortComplex.ShortExact.mk' (S := ShortComplex.mk i (cokernel.π i)
      (cokernel.condition i)) (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i))
      hi inferInstance
    refine ⟨_, _, _, _, _, hS.singleTriangle_distinguished, ?_, cokernel i, ?_, rfl⟩
    · exact isIso_spacesEtaleDerivedBaseChange_app_smallEtalePushforward_toSheaf T h0A3U f hf h
        hh hch hchf g g' f' sq hn J
    · exact Stacks.ConstantSheaf.nsmul_id_zero_of_epi (cokernel.π i) n
        (Stacks.EtaleCohomology.nsmul_id_map_eq_zero (smallEtalePushforward T h)
          (nsmul_id_toSheaf_spacesEtale_eq_zero T n J))
  · rintro _ ⟨A, -, rfl⟩ q hq
    exact isIso_homology_spacesEtaleDerivedBaseChange_app_of_isGE T f g g' f' sq _ q hq

/-! ### Torsion sheaves -/

section Torsion

variable {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
  (sq : IsPullback g' f' f g)

/-- The base change map in degree `q`, as a natural transformation of functors on abelian
sheaves: `H^q(g⁻¹ R f_*(-[0])) ⟶ H^q(R f'_* (g')⁻¹(-[0]))`. -/
abbrev spacesEtaleHigherBaseChange (q : ℤ) :
    (DerivedCategory.singleFunctor
        (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) 0 ⋙
        (totalRightDerived (smallEtalePushforward T f) ⋙
          (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)).mapDerivedCategory)) ⋙
      DerivedCategory.homologyFunctor _ q ⟶
    (DerivedCategory.singleFunctor
        (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) 0 ⋙
        ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')).mapDerivedCategory ⋙
          totalRightDerived (smallEtalePushforward T f'))) ⋙
      DerivedCategory.homologyFunctor _ q :=
  Functor.whiskerRight
    (Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0)
      (spacesEtaleDerivedBaseChange T f g g' f' sq))
    (DerivedCategory.homologyFunctor _ q)

/-- The source of the degree-`p` base change map is `g⁻¹ R^p f_*`. -/
def spacesEtaleHigherBaseChangeSourceIso (p : ℕ) :
    (DerivedCategory.singleFunctor
        (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) 0 ⋙
        (totalRightDerived (smallEtalePushforward T f) ⋙
          (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)).mapDerivedCategory)) ⋙
      DerivedCategory.homologyFunctor _ (p : ℤ) ≅
    (smallEtalePushforward T f).rightDerived p ⋙
      CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g) :=
  Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor _ 0 ⋙ totalRightDerived (smallEtalePushforward T f))
      (Stacks.DerivedFunctor.derivedHomologyIso
        (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)) (p : ℤ)) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (smallEtalePushforward T f) (totalRightDerived (smallEtalePushforward T f))
        (totalRightDerivedUnit (smallEtalePushforward T f))
        Stacks.Cohomology.Localization.enoughKInjectives p)
      (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g))

/-- The target of the degree-`p` base change map is `R^p f'_* (g')⁻¹`. -/
def spacesEtaleHigherBaseChangeTargetIso (p : ℕ) :
    (DerivedCategory.singleFunctor
        (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) 0 ⋙
        ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')).mapDerivedCategory ⋙
          totalRightDerived (smallEtalePushforward T f'))) ⋙
      DerivedCategory.homologyFunctor _ (p : ℤ) ≅
    CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g') ⋙
      (smallEtalePushforward T f').rightDerived p :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        ((CategoryTheory.Sites.abelianInverseImage
          (smallEtaleMorphism T g')).mapDerivedCategorySingleFunctor 0)
        (totalRightDerived (smallEtalePushforward T f')))
      (DerivedCategory.homologyFunctor _ (p : ℤ)) ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g'))
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (smallEtalePushforward T f') (totalRightDerived (smallEtalePushforward T f'))
        (totalRightDerivedUnit (smallEtalePushforward T f'))
        Stacks.Cohomology.Localization.enoughKInjectives p)

/-- **From sheaves killed by an integer to torsion sheaves.** Let `f` be proper. If the base
change map of a cartesian square over `f` is invertible at every sheaf killed by a positive
integer, it is invertible at every torsion sheaf. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_of_torsionSheafProperty
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (hbdd : ∀ n : ℕ, 0 < n →
      ∀ G : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1},
        n • 𝟙 G = 0 →
        IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
          ((DerivedCategory.singleFunctor _ 0).obj G)))
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  have hf' : Space.IsProper T.fppfSite S T.fppf_mem f'.hom :=
    (Space.isProper_isStableUnderBaseChange T.fppfSite S T.fppf_mem).of_isPullback sq hf
  have hcol : ∀ {Y₁ X₁ : T.Spaces} (f₁ : Y₁ ⟶ X₁),
      Space.IsProper T.fppfSite S T.fppf_mem f₁.hom → ∀ (p : ℕ)
      (K : ULift.{u + 1} ℕ ⥤ Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y₁)
        Ab.{u + 1}), PreservesColimit K ((smallEtalePushforward T f₁).rightDerived p) := by
    intro Y₁ X₁ f₁ hf₁ p K
    open Stacks.Topos.AbelianInverseImage Stacks.Topos.AbelianPushforward in
    have hspaces : IsIso (colimit.post K ((abelianPushforward
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y₁)
        (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f₁).morphismOfTopoi
        ).rightDerived p)) := by
      let cY := Space.comparisonAbelianEquivalence T.fppfSite S T.fppf_mem Y₁
      let cX := Space.comparisonAbelianEquivalence T.fppfSite S T.fppf_mem X₁
      let G := abelianPushforward (Space.SmallEtale.topology T.fppfSite S T.fppf_mem Y₁.obj)
        (Space.smallToposMorphism T.fppfSite S T.fppf_mem f₁)
      let G' := abelianPushforward (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y₁)
        (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f₁).morphismOfTopoi
      let α₀ : cY.functor ⋙ G ≅ G' ⋙ cX.functor :=
        StacksTag03LR.abelianBaseChangeIso
          (Space.comparisonToposMorphism T.fppfSite S T.fppf_mem Y₁)
          (Space.smallToposMorphism T.fppfSite S T.fppf_mem f₁)
          (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f₁).morphismOfTopoi
          (Space.comparisonToposMorphism T.fppfSite S T.fppf_mem X₁)
          (Space.smallToposMorphism_comparison T.fppfSite S T.fppf_mem f₁)
      let α : cY.symm.functor ⋙ G' ≅ G ⋙ cX.symm.functor :=
        Functor.isoWhiskerLeft cY.inverse ((Functor.rightUnitor G').symm ≪≫
            Functor.isoWhiskerLeft G' cX.unitIso ≪≫ (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight α₀.symm cX.inverse ≪≫ Functor.associator _ _ _) ≪≫
          cY.invFunIdAssoc (G ⋙ cX.inverse)
      have hsmall := Space.isIso_colimit_post_rightDerived_smallEtaleAbelianPushforward
        T.fppfSite S T.fppf_mem T.fppfSite.contains_terminal f₁ hf₁.2.1.2
        (Space.isQuasiSeparated_of_isSeparated T.fppfSite S T.fppf_mem hf₁.1) p
        (K ⋙ cY.functor)
      exact Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_of_equivalences
        cY.symm cX.symm G G' α p K hsmall
    let := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f₁).isContinuous
    have : ((Space.spacesBaseChange T.fppfSite S T.fppf_mem f₁).functor.sheafPushforwardContinuous
        (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X₁)
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y₁)).IsRightAdjoint :=
      ⟨_,
        ⟨(Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f₁).morphismOfTopoi.adj⟩⟩
    open Stacks.Topos.AbelianPushforward in
    let e : abelianPushforward (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y₁)
          (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f₁).morphismOfTopoi ≅
        smallEtalePushforward T f₁ :=
      Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso
        (Space.spacesBaseChange T.fppfSite S T.fppf_mem f₁).functor
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X₁)
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y₁)
    open Stacks.Topos.AbelianPushforward in
    have := Stacks.Cohomology.isIso_colimit_post_of_natIso K
      ((abelianPushforward (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y₁)
        (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f₁).morphismOfTopoi
        ).rightDerived p) ((smallEtalePushforward T f₁).rightDerived p)
      (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso e p)
    exact preservesColimit_of_isIso_post _ _
  rw [DerivedCategory.isIso_iff]
  intro q
  rcases lt_or_ge q 0 with hq | hq
  · exact isIso_homology_spacesEtaleDerivedBaseChange_app_of_isGE T f g g' f' sq _ q hq
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    let K := Stacks.Torsion.torsionFiltration.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) F
    let c : Cocone K := Cocone.mk F (Stacks.Torsion.torsionFiltrationι.{u + 1} _ F)
    have : IsIso ((colimit.isColimit K).desc c) :=
      Stacks.Torsion.isIso_torsionFiltrationDesc _ F hF
    have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit K)
    have : PreservesColimitsOfSize.{u + 1, u + 1}
        (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)) :=
      (smallEtaleAbelianAdjunction T g).leftAdjoint_preservesColimits
    have : PreservesColimitsOfSize.{u + 1, u + 1}
        (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')) :=
      (smallEtaleAbelianAdjunction T g').leftAdjoint_preservesColimits
    have := hcol f hf p K
    have := hcol f' hf' p (K ⋙ CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g'))
    have : PreservesColimit K ((smallEtalePushforward T f).rightDerived p ⋙
        CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)) := inferInstance
    have : PreservesColimit K (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g') ⋙
        (smallEtalePushforward T f').rightDerived p) := inferInstance
    have : PreservesColimit K
        ((DerivedCategory.singleFunctor _ 0 ⋙
          (totalRightDerived (smallEtalePushforward T f) ⋙
            (CategoryTheory.Sites.abelianInverseImage
              (smallEtaleMorphism T g)).mapDerivedCategory)) ⋙
          DerivedCategory.homologyFunctor _ (p : ℤ)) :=
      preservesColimit_of_natIso K (spacesEtaleHigherBaseChangeSourceIso T f g p).symm
    have : PreservesColimit K
        ((DerivedCategory.singleFunctor _ 0 ⋙
          ((CategoryTheory.Sites.abelianInverseImage
              (smallEtaleMorphism T g')).mapDerivedCategory ⋙
            totalRightDerived (smallEtalePushforward T f'))) ⋙
          DerivedCategory.homologyFunctor _ (p : ℤ)) :=
      preservesColimit_of_natIso K (spacesEtaleHigherBaseChangeTargetIso T g' f' p).symm
    refine Stacks.EtaleCohomology.isIso_app_of_isColimit
      (spacesEtaleHigherBaseChange T f g g' f' sq (p : ℤ)) hc (fun i ↦ ?_)
    have := hbdd (Nat.factorial i.down) (Nat.factorial_pos _) (K.obj i)
      (Stacks.EtaleCohomology.nsmul_id_kernel_eq_zero F _)
    exact Functor.map_isIso (DerivedCategory.homologyFunctor _ (p : ℤ))
      ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
        ((DerivedCategory.singleFunctor _ 0).obj (K.obj i)))

end Torsion

/-! ### Proper base change over an affine base, and Stacks 0DG2 and 0DG3 -/

/-- **Stacks 0DG2 over an affine base.** Granted Stacks 0A3U (`h0A3U`, which gives proper base
change for sheaves of sets, Stacks 0DG0) and the proper base change theorem for schemes on the
spaces-étale sites (`hrep`), cohomology commutes with base change for every proper morphism
`f : Y ⟶ h_V` to the space represented by an affine scheme. -/
theorem cohomologyCommutesWithBaseChange_of_isProper_toAffine
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (hrep : RepresentableProperBaseChange T) {V : BigFppfOver T.fppfSite S T.fppf_mem}
    (hV : IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj V)) {Y : T.Spaces}
    (f : Y ⟶ Space.yonedaSpace T.fppfSite S T.fppf_mem V)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom) :
    CohomologyCommutesWithBaseChange T f := by
  obtain ⟨Z, ρ, hρp, hρs⟩ := Space.exists_properSurjective_schemeCover_of_isProper_toAffine
    T.fppfSite S T.fppf_mem V hV Y.2 f.hom hf
  let h : Space.yonedaSpace T.fppfSite S T.fppf_mem Z ⟶ Y := ObjectProperty.homMk ρ
  have hhf : Space.IsProper T.fppfSite S T.fppf_mem (h ≫ f).hom :=
    Space.isProper_comp T.fppfSite S T.fppf_mem (Space.yonedaSpace T.fppfSite S T.fppf_mem Z).2
      Y.2 (Space.yonedaSpace T.fppfSite S T.fppf_mem V).2 h.hom f.hom hρp hf
  have hch := cohomologyCommutesWithBaseChange_of_yonedaSpace T h0A3U hrep h hρp
  have hchf := cohomologyCommutesWithBaseChange_of_yonedaSpace T h0A3U hrep (h ≫ f) hhf
  intro X' Y' g g' f' sq F hF
  exact isIso_spacesEtaleDerivedBaseChange_app_of_torsionSheafProperty T f g g' f' sq hf
    (fun n hn G hG ↦ isIso_spacesEtaleDerivedBaseChange_app_of_nsmul_id_eq_zero T h0A3U f hf h
      hρp hρs hch hchf g g' f' sq n hn G hG) F hF

/-- **Derived proper base change over an affine base**
(`AlgebraicGeometry.BigEtaleSpaceSite.AffineBaseProperBaseChange`), granted Stacks 0A3U (`h0A3U`,
which gives Stacks 0DG0) and the proper base change theorem for schemes (`hrep`). -/
theorem affineBaseProperBaseChange
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (hrep : RepresentableProperBaseChange T) : AffineBaseProperBaseChange T :=
  fun _ _ hV _ _ _ f hf a a' f'' sq E n hE hT ↦
    (cohomologyCommutesWithBaseChange_of_isProper_toAffine T h0A3U hrep hV f hf).isIso_app T
      a a' f'' sq E n hE hT

/-- **Stacks 0DG3, granted Stacks 0A3U and the proper base change theorem for schemes.** Let
```
Y' --g'--> Y
|f'        |f
v          v
X' --g---> X
```
be a cartesian square of algebraic spaces over `S` with `f` proper. Granted Stacks 0A3U (`h0A3U`,
which gives proper base change for sheaves of sets, Stacks 0DG0) and the proper base change
theorem for schemes (Stacks 095T, as `h095T`: cohomology commutes with base change for every
proper morphism of schemes), the base change map `g⁻¹ R f_* E ⟶ R f'_* (g')⁻¹ E` is an
isomorphism for every `E ∈ D⁺(Y_étale)` with torsion cohomology sheaves.

Both inputs are theorems: `h0A3U` is
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper` and `h095T` is
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`, so Stacks 0DG3 is this
statement with those two supplied. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_representable
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f)
    {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hE : E.IsGE n) (hT : HasTorsionCohomology T E) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app E) :=
  isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_affineBase T h0A3U
    (affineBaseProperBaseChange T h0A3U
      (representableProperBaseChange_of_cohomologyCommutesWithBaseChange T h095T))
    f hf g g' f' sq E n hE hT

/-- **Stacks 0DG2, granted Stacks 0A3U and the proper base change theorem for schemes.** For a
cartesian square of algebraic spaces over `S` with `f` proper and every torsion abelian sheaf `F`
on `Y_étale`, the base change map `g⁻¹ R f_* F ⟶ R f'_* (g')⁻¹ F` is an isomorphism: the case
`E = F[0]` of Stacks 0DG3.

Both inputs are theorems: `h0A3U` is
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper` and `h095T` is
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`, so Stacks 0DG2 is this
statement with those two supplied. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_singleFunctor_of_isProper_of_representable
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f)
    {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
      ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_representable T h0A3U h095T f hf g g' f'
    sq _ 0 inferInstance (hasTorsionCohomology_singleFunctor_obj T F hF)

end AlgebraicGeometry.BigEtaleSpaceSite

end
