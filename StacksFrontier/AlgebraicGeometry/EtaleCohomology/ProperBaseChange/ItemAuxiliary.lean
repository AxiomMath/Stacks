module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap

/-!
# Shared lemmas for the proper base change development

Lemmas used by more than one statement of the proper base change chapter (Tags 0A4C and 0A4D),
gathered here so that each has one home.

## Main results

* `Stacks.EtaleCohomology.nsmul_id_toSheaf_eq_zero` — the underlying abelian sheaf of a sheaf of
  `ℤ/nℤ`-modules on the small étale site is killed by `n`.
* `Stacks.EtaleCohomology.isIso_homology_etaleAbelianDerivedBaseChange_single_of_neg` — both sides
  of a base change map have no cohomology in negative degrees at a sheaf placed in degree zero.

## Main definitions

* `Stacks.Cohomology.GlobalKunneth.sectionsPullbackMap` — the pullback map on `A`-linear derived
  global sections `RΓ(V, K) ⟶ RΓ(W, Li^*K)` along `i : W ⟶ V` over `c : V ⟶ T`, the map "by
  functoriality of cohomology" of the proofs of Tags 0BF1 and 0BF2.

## Main results (pullback maps)

* `Stacks.Cohomology.GlobalKunneth.sectionsPullbackMap_naturality` — the pullback map is natural
  in the complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

section Torsion

variable {X : Scheme.{u}}

/-- The underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules on the small étale site is killed
by `n`. -/
public theorem nsmul_id_toSheaf_eq_zero (n : ℕ)
    (M : SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) :
    n • 𝟙 ((SheafOfModules.toSheaf _).obj M) = 0 := by
  rw [← natCast_zsmul, zsmul_id_eq_zero_iff]
  intro U x
  rw [natCast_zsmul]
  exact nsmul_toSheaf_eq_zero.{max (u + 1) v, max (u + 1) v} _ n M U x

end Torsion

section Negative

variable {Y Z Y' Z' : Scheme.{u}}

/-- Both sides of the base change map of a commutative square have no cohomology in negative
degrees at a sheaf placed in degree zero: inverse image is exact and the unbounded derived
direct image is left t-exact. -/
public theorem isIso_homology_etaleAbelianDerivedBaseChange_single_of_neg (g : Y ⟶ Z)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (w : d ≫ g = g' ≫ c)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℤ) (hq : q < 0) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((etaleAbelianDerivedBaseChange.{u, v} g c d g' w).app
        ((DerivedCategory.singleFunctor _ 0).obj A))) := by
  have hinv : ∀ {S T : Scheme.{u}} (f : S ⟶ T) (K) (i : ℤ),
      (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})).IsGE 0 →
      i < 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((etaleAbelianDerivedInverseImage.{u, v} f).obj K)) := fun f K i _ hi =>
    IsZero.of_iso (Functor.map_isZero (etaleAbelianInverseImage.{u, v} f)
        (DerivedCategory.isZero_of_isGE _ 0 i hi))
      ((Stacks.DerivedFunctor.derivedHomologyIso (etaleAbelianInverseImage.{u, v} f) i).app _)
  have hGE' : ((etaleAbelianDerivedInverseImage.{u, v} d).obj
      ((DerivedCategory.singleFunctor _ 0).obj A)).IsGE 0 :=
    (DerivedCategory.isGE_iff _ _).2 fun i hi => hinv d _ i inferInstance hi
  have hGE'' : ((etaleAbelianDerivedDirectImage.{u, v} g').obj
      ((etaleAbelianDerivedInverseImage.{u, v} d).obj
        ((DerivedCategory.singleFunctor _ 0).obj A))).IsGE 0 :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj (etaleAbelianDirectImage.{u, v} g') _ 0
  exact isIso_of_source_target_iso_zero _
    (hinv c _ q (Stacks.DerivedFunctor.isGE_totalRightDerived_obj
      (etaleAbelianDirectImage.{u, v} g) _ 0) hq).isoZero
    (DerivedCategory.isZero_of_isGE ((etaleAbelianDerivedDirectImage.{u, v} g').obj
      ((etaleAbelianDerivedInverseImage.{u, v} d).obj _)) 0 q hq).isoZero

end Negative

end Stacks.EtaleCohomology

/-! ### The pullback map on derived global sections -/

namespace Stacks.Cohomology.GlobalKunneth

open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction derivedPushforwardCompIso)

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The pullback map on `A`-linear derived global sections** along `i : W ⟶ V`, for `V` over
`c : V ⟶ T` and `A = Γ(T, 𝒪_T)`: the morphism `RΓ(V, K) ⟶ RΓ(W, Li^*K)` in `D(A)`.

It is the composite of the Leray isomorphism `RΓ(V, -) ≅ RΓ(T, Rc_*(-))` of Tag 0D5W, of
`RΓ(T, Rc_*(-))` applied to the unit `K ⟶ Ri_* Li^* K` of the derived adjunction
`Li^* ⊣ Ri_*`, of the composition isomorphism `Rc_* ∘ Ri_* ≅ R(i ≫ c)_*`, and of the Leray
isomorphism for `i ≫ c`. This is the map "by functoriality of cohomology" of the proofs of
[Stacks, Tag 0BF1](https://stacks.math.columbia.edu/tag/0BF1) and
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2). -/
def sectionsPullbackMap {T V W : RingedSpace.{u, u}} (c : V ⟶ T) (i : W ⟶ V)
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing V))) :
    (sectionsOverBase c).obj K ⟶ (sectionsOverBase (i ≫ c)).obj ((derivedPullback i).obj K) :=
  (lerayIso c).inv.app K ≫
    (baseSections T).map ((derivedPushforward c).map ((derivedAdjunction i).unit.app K)) ≫
    (baseSections T).map ((derivedPushforwardCompIso i c).hom.app ((derivedPullback i).obj K)) ≫
    (lerayIso (i ≫ c)).hom.app ((derivedPullback i).obj K)

section PullbackMapFunctoriality

variable {T V W : RingedSpace.{u, u}} (c : V ⟶ T) (i : W ⟶ V)

/-- **The pullback map is natural in the complex.** -/
@[reassoc]
theorem sectionsPullbackMap_naturality
    {K K' : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing V))} (φ : K ⟶ K') :
    (sectionsOverBase c).map φ ≫ sectionsPullbackMap c i K' =
      sectionsPullbackMap c i K ≫ (sectionsOverBase (i ≫ c)).map ((derivedPullback i).map φ) := by
  have h₁ := (lerayIso c).inv.naturality φ
  have h₂ := (derivedAdjunction i).unit.naturality φ
  have h₃ := (derivedPushforwardCompIso i c).hom.naturality ((derivedPullback i).map φ)
  have h₄ := (lerayIso (i ≫ c)).hom.naturality ((derivedPullback i).map φ)
  simp only [Functor.comp_map, Functor.id_map] at h₁ h₂ h₃ h₄
  have s₂ := congrArg (fun z => (baseSections T).map ((derivedPushforward c).map z)) h₂
  have s₃ := congrArg (baseSections T).map h₃
  simp only [Functor.map_comp] at s₂ s₃
  rw [sectionsPullbackMap, sectionsPullbackMap, reassoc_of% h₁, reassoc_of% s₂, reassoc_of% s₃,
    h₄]
  simp only [Category.assoc]

end PullbackMapFunctoriality

end Stacks.Cohomology.GlobalKunneth

end
