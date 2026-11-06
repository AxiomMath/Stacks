module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekCovarianceCompactification
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekAdjunctionCovariance
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompIsoIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekAffineChartsNormalization
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrictComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory

/-!
# The second and third constructions of the covariance map for an open agree

In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism of `FTS_S`, `i : U ⟶ X` an open
immersion and `g = f ∘ i`. [Stacks, Tag 0G56] gives three constructions of the canonical map
`Rg_!(K|_U) ⟶ Rf_! K` and asserts that they agree. Here the second construction
(`AlgebraicGeometry.lowerShriekOpenImmersionMapOfCompactification`: for a compactification
`j : X ⟶ X̄` with `f̄ : X̄ ⟶ Y`, `Rf̄_*` applied to the map `Rj'_!(K|_U) ⟶ Rj_! K` of
[Stacks, Tag 0G4Y], `j' = j ∘ i`) is identified with the third
(`AlgebraicGeometry.lowerShriekOpenImmersionMap`: the map of pro-objects induced, by
[Stacks, Tag 0G2X], by `Hom(Rf_! K, L) = Hom(K, f^! L) ⟶ Hom(K|_U, g^! L) = Hom(Rg_!(K|_U), L)`).

The proof: under the bijections of [Stacks, Tag 0G51], composing with the second construction is
restriction `Hom(K, j^* f̄^! L) ⟶ Hom(K|_U, j'^* f̄^! L)`
(`CategoryTheory.shriekHomEquiv_covariance`), and `j'^* f̄^! = i^* j^* f̄^!` is the identification
`g^! = i^* f^!` used by the third construction.

## Main results

* `AlgebraicGeometry.lowerShriekHomEquiv_lowerShriekOpenImmersionMapOfCompactification`: composing
  with the second construction is restriction, under the bijections of [Stacks, Tag 0G51].
* `AlgebraicGeometry.lowerShriekOpenImmersionMapOfCompactification_eq_lowerShriekOpenImmersionMap`:
  **[Stacks, Tag 0G56]**, constructions (2) and (3) agree.

## References

* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
* [Stacks Project, Tag 0G4Y](https://stacks.math.columbia.edu/tag/0G4Y)
* [Stacks Project, Tag 0G51](https://stacks.math.columbia.edu/tag/0G51)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u

namespace Stacks.DerivedCategoryComparisons

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory C₃]

/-- The comparison of the derived functors of `H` and `F ⋙ G` attached to `e : H ≅ F ⋙ G`,
followed by the composition isomorphism, is the inverse of the composition isomorphism attached
to `e⁻¹`. -/
theorem mapDerivedCategoryIsoOfNatIso_trans_mapDerivedCategoryCompIso (F : C₁ ⥤ C₂)
    (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : H ≅ F ⋙ G) :
    mapDerivedCategoryIsoOfNatIso H (F ⋙ G) e ≪≫ mapDerivedCategoryCompIso F G =
      (Functor.mapDerivedCategoryCompIsoOfCompIso e.symm).symm := by
  ext1
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
  intro P
  rw [Iso.symm_hom, ← cancel_mono ((Functor.mapDerivedCategoryCompIsoOfCompIso e.symm).hom.app _),
    Iso.inv_hom_id_app, Iso.trans_hom, NatTrans.comp_app, mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    mapDerivedCategoryCompIso_hom_app_Q, Functor.mapDerivedCategoryCompIso_hom_app_Q]
  have h : (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P ≫
      (Functor.mapHomologicalComplexCompIso e.symm (ComplexShape.up ℤ)).hom.app P = 𝟙 _ := by
    ext n
    simp
  have h2 : G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) = 𝟙 _ :=
    (G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P)).inv_hom_id
  have h3 : DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e.symm (ComplexShape.up ℤ)).hom.app P) = 𝟙 _ :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map h).trans (DerivedCategory.Q.map_id _))
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, reassoc_of% h2, reassoc_of% h3,
    Iso.hom_inv_id_app]
  rfl

end Stacks.DerivedCategoryComparisons


namespace CategoryTheory

variable {𝒜 : Type*} [Category 𝒜]

/-- Inverting a composite of three isomorphisms in an equation. -/
theorem comp_inv_eq_of_comp_eq_chase {o₀ o₁ o₂ o₃ o₄ : 𝒜} (a : o₀ ⟶ o₁) (ainv : o₁ ⟶ o₀)
    (b : o₁ ⟶ o₂) (binv : o₂ ⟶ o₁) (pc : o₂ ⟶ o₃) (em : o₀ ⟶ o₄) (mk : o₄ ⟶ o₃) (mkinv : o₃ ⟶ o₄)
    (hk : a ≫ b ≫ pc = em ≫ mk) (ha : ainv ≫ a = 𝟙 _) (hb : binv ≫ b = 𝟙 _)
    (hm : mk ≫ mkinv = 𝟙 _) : pc ≫ mkinv = binv ≫ ainv ≫ em := by
  calc pc ≫ mkinv = binv ≫ ainv ≫ (a ≫ b ≫ pc) ≫ mkinv := by
        simp only [Category.assoc, reassoc_of% ha, reassoc_of% hb]
    _ = binv ≫ ainv ≫ em := by rw [hk]; simp only [Category.assoc, hm, Category.comp_id]

/-- An inverse of a composite of four morphisms, three of them invertible and one natural. -/
theorem comp_eq_of_inv_eq_chase {x₀ x₁ x₂ x₃ x₄ y : 𝒜} (c m : x₁ ⟶ x₀) (d : x₀ ⟶ y)
    (dinv : y ⟶ x₀) (p : x₁ ⟶ x₂) (pinv : x₂ ⟶ x₁) (q : x₂ ⟶ x₃) (s : x₃ ⟶ y) (sinv : y ⟶ x₃)
    (t₁ : x₃ ⟶ x₄) (t₂ : x₄ ⟶ x₁) (r : x₁ ⟶ x₄) (H : dinv = sinv ≫ t₁ ≫ t₂ ≫ m) (hm : c = m)
    (hd : dinv ≫ d = 𝟙 _) (hs : s ≫ sinv = 𝟙 _) (hp : p ≫ pinv = 𝟙 _) (hnat : q ≫ t₁ = pinv ≫ r)
    (hr : r ≫ t₂ = 𝟙 _) : c ≫ d = p ≫ q ≫ s := by
  have e : p ≫ q ≫ s ≫ dinv = c := by
    rw [H, reassoc_of% hs, reassoc_of% hnat, reassoc_of% hp, reassoc_of% hr, hm]
  rw [← e]
  simp only [Category.assoc, hd, Category.comp_id]

/-- The chase behind
`AlgebraicGeometry.pullCompIso_hom_app_comp_pullUpperShriekPlusCohIso_hom_app`. -/
theorem precompOpen_upperShriek_chase {ℬ : Type*} [Category ℬ] (P : ℬ ⥤ 𝒜) {b₁ b₂ : ℬ}
    {o₂ o₃ o₄ : 𝒜} (εapp pc : P.obj b₁ ⟶ o₂) (u' mk : o₂ ⟶ o₃) (u mj : b₁ ⟶ b₂)
    (v : P.obj b₂ ⟶ o₃) (mi : P.obj b₂ ⟶ o₄) (dd : o₄ ⟶ o₃) (C : o₃ ⟶ o₃)
    (hε : εapp = 𝟙 _ ≫ pc) (e₁ : u' = mk) (e₂ : u = mj) (e₃ : v = mi ≫ dd ≫ C) (e₄ : C = 𝟙 _)
    (k : pc ≫ mk = P.map mj ≫ mi ≫ dd) : εapp ≫ u' = P.map u ≫ v := by
  subst hε e₁ e₂ e₃ e₄
  simp only [Category.id_comp, Category.comp_id, k]

/-- The last step of
`AlgebraicGeometry.lowerShriekHomEquiv_lowerShriekOpenImmersionMapOfCompactification`. -/
theorem precompOpen_shriekHomEquiv_chase {ℬ : Type*} [Category ℬ] (P : ℬ ⥤ 𝒜) {b₀ b₁ b₂ : ℬ}
    {o₀ o₂ o₃ : 𝒜} (δinv : o₀ ⟶ P.obj b₀) (x : b₀ ⟶ b₁) (εapp : P.obj b₁ ⟶ o₂) (u' : o₂ ⟶ o₃)
    (u : b₁ ⟶ b₂) (v : P.obj b₂ ⟶ o₃) (h : εapp ≫ u' = P.map u ≫ v) :
    (δinv ≫ P.map x ≫ εapp) ≫ u' = δinv ≫ P.map (x ≫ u) ≫ v := by
  simp only [Category.assoc, h, Functor.map_comp]

end CategoryTheory

namespace CategoryTheory.ProSeq

/-- For a functor `ι` and a morphism `μ : P' ⟶ P` of pro-objects, the morphism
`ι P' ⟶ ι(L)` attached to the image under `μ` of a point `x` of `P` at `L` is `ι μ` followed by the
morphism `ι P ⟶ ι(L)` attached to `x`. -/
theorem homConstEquiv_symm_lanUnit_app_app_map {𝒟 : Type*} {𝒟' : Type*} [Category.{v} 𝒟]
    [Category.{v} 𝒟'] (ι : 𝒟 ⥤ 𝒟') [∀ A : 𝒟 ⥤ Type v, ι.HasLeftKanExtension A] {P P' : ProSeq 𝒟}
    (μ : P' ⟶ P) (L : 𝒟) (x : P.points.obj L) :
    (homConstEquiv ((map ι).obj P') (ι.obj L)).symm
        ((ι.lanUnit.app P'.points).app L (μ.unop.hom.app L x)) =
      (map ι).map μ ≫
        (homConstEquiv ((map ι).obj P) (ι.obj L)).symm ((ι.lanUnit.app P.points).app L x) := by
  apply (homConstEquiv _ _).injective
  have h : homConstEquiv ((map ι).obj P') (ι.obj L) ((map ι).map μ ≫
      (homConstEquiv ((map ι).obj P) (ι.obj L)).symm ((ι.lanUnit.app P.points).app L x)) =
      ((map ι).map μ).unop.hom.app (ι.obj L) (homConstEquiv ((map ι).obj P) (ι.obj L)
        ((homConstEquiv ((map ι).obj P) (ι.obj L)).symm ((ι.lanUnit.app P.points).app L x))) :=
    rfl
  rw [h]
  exact (Equiv.apply_symm_apply _ _).trans
    ((ConcreteCategory.congr_hom (congr_app (ι.lanUnit.naturality μ.unop.hom) L) x).trans
      (congrArg (((map ι).map μ).unop.hom.app (ι.obj L)) (Equiv.apply_symm_apply _ _).symm))

/-- A morphism `G' ⟶ G` of functors with values in pro-objects is the transformation of functors
of points it induces. -/
theorem natTransOfPointsFunctor_whiskerRight_leftOp {𝒞 : Type*} [Category.{v} 𝒞] {𝒟 : Type*}
    [Category.{v} 𝒟] {G G' : 𝒞 ⥤ ProSeq 𝒟} (α : G' ⟶ G) :
    natTransOfPointsFunctor (Functor.whiskerRight (NatTrans.leftOp α) (IsSequentialProObject 𝒟).ι) =
      α := by
  ext K
  rfl

end CategoryTheory.ProSeq

namespace Stacks.Duality.UpperShriekDuality

open TwistedInverseImageDuality

/-- **`pullModelConj` and composition, inverted**: `Lh^* Lj^* ≅ L(h ≫ j)^*` at the standard model,
followed by `pullModelConj (h ≫ j)` backwards, is `pullModelConj j` and `pullModelConj h` backwards
followed by the composition isomorphism at the locally small model. -/
theorem pullCompIso_hom_app_comp_pullModelConj_inv_app {A₀ B₀ C₀ : Scheme.{u}} (h : A₀ ⟶ B₀)
    (j : B₀ ⟶ C₀) (E : DerivedCategory C₀.Modules) :
    (pullCompIso h j (h ≫ j) rfl).hom.app ((comparison C₀).inverse.obj E) ≫
        (pullModelConj (h ≫ j)).inv.app E =
      (pull h).map ((pullModelConj j).inv.app E) ≫
        (pullModelConj h).inv.app ((Stacks.Duality.derivedPullback j).obj E) ≫
        (comparison A₀).inverse.map ((Stacks.Duality.derivedPullbackCompIso h j).hom.app E) := by
  have hk := pullModelConj_hom_app_comp_pullCompIso h j (h ≫ j) rfl E
  rw [eqToHom_refl, Category.comp_id] at hk
  exact comp_inv_eq_of_comp_eq_chase _ _ _ _ _ _ _ _ hk (Iso.inv_hom_id_app _ _)
    ((pull h).mapIso ((pullModelConj j).app E)).inv_hom_id (Iso.hom_inv_id_app _ _)

/-- `j^* f̄^! = f^!`, componentwise: `pullModelConj` backwards. -/
theorem pullUpperShriekPlusCohIso_hom_app {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S}
    (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left)) (L : (plusCoh Y.left).FullSubcategory) :
    (AlgebraicGeometry.pullUpperShriekPlusCohIso f c).hom.app L =
      (pullModelConj c.immersion).inv.app ((twistedInverseImage c.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase)).obj
          ((plusCohToQCoh Y.left).obj L)).obj := by
  simp [AlgebraicGeometry.pullUpperShriekPlusCohIso, upperShriekStdIso,
    ObjectProperty.liftCompιIso] <;> rfl

/-- The isomorphism of [Stacks, Tag 0AA0] between `f^!` at a compactification and itself is the
identity, at the standard model. -/
theorem upperShriekStdCompactificationIso_self_hom_app {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FTS S} (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))
    (L : (plusCoh Y.left).FullSubcategory) :
    (upperShriekStdCompactificationIso f c c).hom.app L = 𝟙 _ := by
  rw [upperShriekStdCompactificationIso, upperShriekPlusIso_refl]
  simp

/-- `g^! = j^* ∘ f^!` for `g = f ∘ j`, componentwise. -/
theorem upperShriekStdPrecompOpenIso_hom_app {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S}
    (j : U ⟶ X) [IsOpenImmersion j.left] (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))
    (cU : CompactificationOf (Over.mk (j ≫ f).left)) (L : (plusCoh Y.left).FullSubcategory) :
    (upperShriekStdPrecompOpenIso j f c cU).hom.app L =
      (pullModelConj j.left).inv.app ((upperShriek f c).obj ((plusCohToQCoh Y.left).obj L)).obj ≫
        (comparison U.left).inverse.map
          ((Stacks.Duality.derivedPullbackCompIso j.left c.immersion).hom.app
            ((twistedInverseImage c.toBase
              (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase)).obj
                ((plusCohToQCoh Y.left).obj L)).obj) ≫
        (upperShriekStdCompactificationIso (j ≫ f) (c.precompOpen j.left) cU).hom.app L := by
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, upperShriekStdPrecompOpenIso,
    upperShriekStdPullIso, upperShriekPrecompOpenIso, MorphismProperty.Comma.comp_hom,
    Comma.comp_left, CompactificationOf.precompOpen_space, CompactificationOf.precompOpen_immersion,
    Over.mk_left, quasiCoherentDerivedPullbackCompIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, ObjectProperty.ι_map, NatIso.cancel_natIso_inv_left]
  exact congrArg (fun t => (comparison U.left).inverse.map t ≫
    (upperShriekStdCompactificationIso (j ≫ f) (c.precompOpen j.left) cU).hom.app L)
    (Category.id_comp _)

end Stacks.Duality.UpperShriekDuality

namespace AlgebraicGeometry

open Stacks.Duality Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

attribute [local instance 10000] CategoryTheory.Functor.hasLeftKanExtension_of_type
  CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_type
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

section Restriction

variable {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) [IsOpenImmersion a] [IsOpenImmersion b]

/-- Restriction along `a ≫ b = a ≫ b`, followed by the composition isomorphism, is the
composition isomorphism. -/
theorem restrictFunctorCongr_rfl_trans_restrictFunctorComp :
    Scheme.Modules.restrictFunctorCongr (rfl : a ≫ b = a ≫ b) ≪≫
        Scheme.Modules.restrictFunctorComp a b =
      Scheme.Modules.restrictFunctorComp a b := by
  refine Iso.ext (NatTrans.ext (funext fun M => Scheme.Modules.hom_ext _ _ fun W => ?_))
  simp only [Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id, Scheme.Modules.restrictFunctorComp_hom_app_app, Functor.op_obj,
    eqToHom_op]
  exact Category.id_comp _

/-- **Restriction as derived pullback, along a composite**, read through the composition
isomorphism of restriction on `D(𝒪)` and `Lb^* ⋙ La^* ≅ L(a ≫ b)^*`. -/
theorem restrictFunctorMapDerivedCategoryCompIso_inv_app_comp_derivedRestrictIsoDerivedPullback
    (M : Std C) :
    (restrictFunctorMapDerivedCategoryCompIso a b (a ≫ b) rfl).inv.app M ≫
        (Scheme.Modules.derivedRestrictIsoDerivedPullback (a ≫ b)).hom.app M =
      (Scheme.Modules.derivedRestrictIsoDerivedPullback a).hom.app _ ≫
        (pull a).map ((Scheme.Modules.derivedRestrictIsoDerivedPullback b).hom.app M) ≫
        (pullCompIso a b (a ≫ b) rfl).hom.app M := by
  let : ∀ T : Scheme.{u}, HasDerivedCategory T.Modules := fun _ => HasDerivedCategory.standard _
  refine comp_eq_of_inv_eq_chase
    (c := (restrictFunctorMapDerivedCategoryCompIso a b (a ≫ b) rfl).inv.app M)
    (d := (Scheme.Modules.derivedRestrictIsoDerivedPullback (a ≫ b)).hom.app M)
    (dinv := (Scheme.Modules.derivedRestrictIsoDerivedPullback (a ≫ b)).inv.app M)
    (p := (Scheme.Modules.derivedRestrictIsoDerivedPullback a).hom.app _)
    (pinv := (Scheme.Modules.derivedRestrictIsoDerivedPullback a).inv.app _)
    (q := (pull a).map ((Scheme.Modules.derivedRestrictIsoDerivedPullback b).hom.app M))
    (s := (pullCompIso a b (a ≫ b) rfl).hom.app M)
    (r := (Scheme.Modules.restrictFunctor a).mapDerivedCategory.map
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback b).hom.app M))
    (H := congr_app (Scheme.Modules.derivedRestrictIsoDerivedPullback_inv_comp a b) M) (hm := ?_)
    (hd := Iso.inv_hom_id_app _ _) (hs := ?_) (hp := Iso.hom_inv_id_app _ _)
    (hnat := (Scheme.Modules.derivedRestrictIsoDerivedPullback a).inv.naturality _)
    (hr := ((Scheme.Modules.restrictFunctor a).mapDerivedCategory.mapIso
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback b).app M)).hom_inv_id)
  · have h₁ :=
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_trans_mapDerivedCategoryCompIso
      (Scheme.Modules.restrictFunctor b) (Scheme.Modules.restrictFunctor a)
      (Scheme.Modules.restrictFunctor (a ≫ b))
      (Scheme.Modules.restrictFunctorCongr (rfl : a ≫ b = a ≫ b) ≪≫
        Scheme.Modules.restrictFunctorComp a b)
    have h₂ : Functor.mapDerivedCategoryCompIsoOfCompIso (Scheme.Modules.restrictFunctorCongr
        (rfl : a ≫ b = a ≫ b) ≪≫ Scheme.Modules.restrictFunctorComp a b).symm =
        Functor.mapDerivedCategoryCompIsoOfCompIso (Scheme.Modules.restrictFunctorComp a b).symm := by
      rw [restrictFunctorCongr_rfl_trans_restrictFunctorComp]
    exact congrArg (fun e => e.inv.app M) (h₁.trans (congrArg Iso.symm h₂))
  · exact (congrArg (· ≫ _) (Category.comp_id _)).trans (Iso.hom_inv_id_app _ _)

end Restriction

section FTS

variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S}

/-- The identifications `j'^* ≅ i^* ∘ j^*` of restrictions to `U`, on `D^b_{Coh}` and as derived
pullbacks, are compatible. -/
theorem restrictBoundedCoherentLiftCompIso_compatible (i : U ⟶ X) [IsOpenImmersion i.left]
    {Xb : Scheme.{u}} [IsNoetherian Xb] (j : X.left ⟶ Xb) [IsOpenImmersion j]
    (N : BoundedCoherentDerived Xb) :
    (boundedCoherentDerived U.left).ι.map
        ((restrictBoundedCoherentLiftCompIso i.left j _ rfl).symm.hom.app N) ≫
        (restrictPlusCohIso (i.left ≫ j)).inv.app N =
      (restrictBoundedCoherentPullIso i).inv.app ((restrictBoundedCoherentLift j).obj N) ≫
        (pull i.left).map ((restrictPlusCohIso j).inv.app N) ≫
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (plusCoh Xb).ι
          (pullCompIso i.left j (i.left ≫ j) rfl)).hom.app ((boundedCoherentToPlusCoh Xb).obj N) :=
  (restrictFunctorMapDerivedCategoryCompIso_inv_app_comp_derivedRestrictIsoDerivedPullback i.left j
    N.obj).trans (congrArg (fun t =>
      (Scheme.Modules.derivedRestrictIsoDerivedPullback i.left).hom.app _ ≫
      (pull i.left).map ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).hom.app N.obj) ≫ t)
        (Category.id_comp _).symm)

/-- The identification `j'^* f̄^! = i^* j^* f̄^!` of the derived pullbacks along `j' = j ∘ i` is
the identification `g^! = i^* ∘ f^!` of the third construction of [Stacks, Tag 0G56]. -/
theorem pullCompIso_hom_app_comp_pullUpperShriekPlusCohIso_hom_app (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left]
    (L : (plusCoh Y.left).FullSubcategory) :
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (plusCoh c.space).ι
        (pullCompIso i.left c.immersion (i.left ≫ c.immersion) rfl)).hom.app
          ((upperShriekPlusCoh c.toBase).obj L) ≫
        (pullUpperShriekPlusCohIso (i ≫ f) (c.precompOpen i.left)).hom.app L =
      (pull i.left).map ((pullUpperShriekPlusCohIso f c).hom.app L) ≫
        (upperShriekStdPrecompOpenIso i f c (c.precompOpen i.left)).hom.app L :=
  precompOpen_upperShriek_chase (pull i.left) _ _ _ _ _ _ _ _ _ _ rfl
    (pullUpperShriekPlusCohIso_hom_app (i ≫ f) (c.precompOpen i.left) L)
    (pullUpperShriekPlusCohIso_hom_app f c L)
    (upperShriekStdPrecompOpenIso_hom_app i f c (c.precompOpen i.left) L)
    (upperShriekStdCompactificationIso_self_hom_app (i ≫ f) (c.precompOpen i.left) L)
    (pullCompIso_hom_app_comp_pullModelConj_inv_app i.left c.immersion _)

/-- **Composing with the second construction of [Stacks, Tag 0G56] is restriction**, under the
bijections of [Stacks, Tag 0G51]: for `φ : Rf_! K ⟶ L` corresponding to `ψ : K ⟶ f^! L`, the
composite `Rg_!(K|_U) ⟶ Rf_! K ⟶ L` corresponds to `ψ|_U : K|_U ⟶ (f^! L)|_U = g^! L`, for every
`L` in `D^+_{Coh}(𝒪_Y)`. -/
theorem lowerShriekHomEquiv_lowerShriekOpenImmersionMapOfCompactification (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left]
    (K : BoundedCoherentDerived X.left) (L : (plusCoh Y.left).FullSubcategory)
    (φ : (ProSeq.map (boundedCoherentToPlusCoh Y.left)).obj ((lowerShriek f c).obj K) ⟶
      ProSeq.const.obj L) :
    lowerShriekHomEquiv (i ≫ f) (c.precompOpen i.left)
        ((restrictBoundedCoherentLift i.left).obj K) L
        ((ProSeq.map (boundedCoherentToPlusCoh Y.left)).map
          ((lowerShriekOpenImmersionMapOfCompactification f c i).app K) ≫ φ) =
      (restrictBoundedCoherentPullIso i).inv.app K ≫
        (pull i.left).map (lowerShriekHomEquiv f c K L φ) ≫
        (upperShriekStdPrecompOpenIso i f c (c.precompOpen i.left)).hom.app L := by
  have : IsLocallyNoetherian (Over.mk f.left).left := inferInstanceAs (IsLocallyNoetherian X.left)
  have hB := shriekHomEquiv_covariance (restrictBoundedCoherentLift c.immersion)
    (restrictBoundedCoherentLift (i.left ≫ c.immersion)) (restrictBoundedCoherentLift i.left)
    (restrictBoundedCoherentLiftCompIso i.left c.immersion _ rfl).symm
    (boundedCoherentToPlusCoh c.space) (boundedCoherentDerived X.left).ι
    (boundedCoherentDerived U.left).ι ((plusCoh c.space).ι ⋙ pull c.immersion)
    ((plusCoh c.space).ι ⋙ pull (i.left ≫ c.immersion)) (restrictPlusCohIso c.immersion)
    (restrictPlusCohIso (i.left ≫ c.immersion)) (pull i.left) (restrictBoundedCoherentPullIso i)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (plusCoh c.space).ι
      (pullCompIso i.left c.immersion (i.left ≫ c.immersion) rfl))
    (properPushforwardBoundedCoherent c.toBase) (boundedCoherentToPlusCoh Y.left)
    (pushPlusCoh c.toBase) (properPushforwardPlusCohIso c.toBase) (pushPlusCohAdjunction c.toBase)
    (DeligneSystem.values c.immersion) (DeligneSystem.values (i.left ≫ c.immersion))
    (restrictionLifting_values_plusCoh c.immersion)
    (restrictionLifting_values_plusCoh (i.left ≫ c.immersion))
    (restrictBoundedCoherentLiftCompIso_compatible i c.immersion) K L φ
  exact (congrArg (· ≫ (pullUpperShriekPlusCohIso (i ≫ f) (c.precompOpen i.left)).hom.app L)
    hB).trans (precompOpen_shriekHomEquiv_chase (pull i.left) _ _ _ _ _ _
      (pullCompIso_hom_app_comp_pullUpperShriekPlusCohIso_hom_app f c i L))

end FTS

section Agreement

variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S}

/-- On functors of points, the identification `Hom(Rf_! K, L) = Hom_X(K, f^! L)` of
[Stacks, Tag 0G51] sends a point `x` of `Rf_! K` at `L` to the morphism `K ⟶ f^! L` corresponding
to the morphism `Rf_! K ⟶ L` that `x` is. -/
theorem lowerShriekPointsFunctorIsoStd_hom_app_app (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (K : BoundedCoherentDerived X.left)
    (L : BoundedCoherentDerived Y.left) (x : ((lowerShriek f c).obj K).points.obj L) :
    ((lowerShriekPointsFunctorIsoStd f c).hom.app (op K)).app L x =
      lowerShriekHomEquiv f c K ((boundedCoherentToPlusCoh Y.left).obj L)
        ((ProSeq.homConstEquiv _ _).symm
          (((boundedCoherentToPlusCoh Y.left).lanUnit.app ((lowerShriek f c).obj K).points).app
            L x)) :=
  rfl

/-- On functors of points, construction (2) of [Stacks, Tag 0G56] is restriction
`Hom_X(K, f^! L) ⟶ Hom_U(K|_U, g^! L)`, under the identifications of [Stacks, Tag 0G51]. -/
theorem lowerShriekPointsFunctorIsoStd_hom_app_app_lowerShriekOpenImmersionMapOfCompactification
    (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left]
    (K : BoundedCoherentDerived X.left) (L : BoundedCoherentDerived Y.left)
    (x : ((lowerShriek f c).obj K).points.obj L) :
    ((lowerShriekPointsFunctorIsoStd (i ≫ f) (c.precompOpen i.left)).hom.app
        (op ((restrictBoundedCoherentLift i.left).obj K))).app L
        (((lowerShriekOpenImmersionMapOfCompactification f c i).app K).unop.hom.app L x) =
      (restrictBoundedCoherentPullIso i).inv.app K ≫
        (pull i.left).map (((lowerShriekPointsFunctorIsoStd f c).hom.app (op K)).app L x) ≫
        (upperShriekStdPrecompOpenIso i f c (c.precompOpen i.left)).hom.app
          ((boundedCoherentToPlusCoh Y.left).obj L) := by
  refine (lowerShriekPointsFunctorIsoStd_hom_app_app (i ≫ f) (c.precompOpen i.left) _ L _).trans ?_
  refine (congrArg (lowerShriekHomEquiv (i ≫ f) (c.precompOpen i.left) _ _)
    (ProSeq.homConstEquiv_symm_lanUnit_app_app_map (boundedCoherentToPlusCoh Y.left)
      ((lowerShriekOpenImmersionMapOfCompactification f c i).app K) L x)).trans ?_
  exact lowerShriekHomEquiv_lowerShriekOpenImmersionMapOfCompactification f c i K _ _

/-- The agreement of constructions (2) and (3). In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y`
be a morphism of `FTS_S`, `i : U ⟶ X` an open immersion, `g = f ∘ i`, and `j : X ⟶ X̄` a
compactification of `X` over `Y` with `f̄ : X̄ ⟶ Y`. The canonical map `Rg_!(K|_U) ⟶ Rf_! K` given
by `Rf̄_*` applied to the map `Rj'_!(K|_U) ⟶ Rj_! K` of [Stacks, Tag 0G4Y], `j' = j ∘ i`
(construction (2), `AlgebraicGeometry.lowerShriekOpenImmersionMapOfCompactification`), is the map
induced by `Hom(Rf_! K, L) = Hom_X(K, f^! L) ⟶ Hom_U(K|_U, f^! L|_U)`
`= Hom_U(K|_U, g^! L) = Hom(Rg_!(K|_U), L)` (construction (3),
`AlgebraicGeometry.lowerShriekOpenImmersionMap`), with `Rg_!` computed at the compactification
`j'`. -/
@[stacks 0G56 "constructions (2) and (3) give the same arrow"]
theorem lowerShriekOpenImmersionMapOfCompactification_eq_lowerShriekOpenImmersionMap (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left] :
    lowerShriekOpenImmersionMapOfCompactification f c i =
      lowerShriekOpenImmersionMap f c i (c.precompOpen i.left) := by
  have key : Functor.whiskerRight
        (NatTrans.leftOp (lowerShriekOpenImmersionMapOfCompactification f c i))
        (IsSequentialProObject (BoundedCoherentDerived Y.left)).ι ≫
      (Functor.isoWhiskerLeft (restrictBoundedCoherentLift i.left).op
        (lowerShriekPointsFunctorIsoStd (i ≫ f) (c.precompOpen i.left))).hom =
      (lowerShriekPointsFunctorIsoStd f c).hom ≫ Functor.whiskerRight
        (homMapNatTrans (boundedCoherentDerived X.left).ι (boundedCoherentDerived U.left).ι
          (restrictBoundedCoherentLift i.left) (pull i.left) (restrictBoundedCoherentPullIso i)
          (upperShriekStd f c) (upperShriekStd (i ≫ f) (c.precompOpen i.left))
          (upperShriekStdPrecompOpenIso i f c (c.precompOpen i.left))) _ := by
    ext K L x
    exact lowerShriekPointsFunctorIsoStd_hom_app_app_lowerShriekOpenImmersionMapOfCompactification
      f c i K.unop L x
  have h := ((Iso.eq_comp_inv _).2 key).trans (Category.assoc _ _ _)
  exact (ProSeq.natTransOfPointsFunctor_whiskerRight_leftOp _).symm.trans
    (congrArg ProSeq.natTransOfPointsFunctor h)

end Agreement

end AlgebraicGeometry

end
