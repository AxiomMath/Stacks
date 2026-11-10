module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionComparison
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.OpenBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonicalMaps

/-!
# The map `μ_{f,K}` does not depend on the compactification

Let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S` and let `μ_{f,K}` be the map
`Stacks.Duality.upperShriekCompareWithPullbackCanonical` of [Stacks, Tag 0B6T], built from a
compactification of `X` over `Y`. For a morphism `g : X̄₁ ⟶ X̄₂` of compactifications with
`g⁻¹(X) = X`, `μ_{f,K}` for `X̄₁` followed by the transformation `α_g` of the proof of
[Stacks, Tag 0AA0] is `μ_{f,K}` for `X̄₂` preceded by `Lf^*K ⊗ α_g`; consequently `μ_{f,K}` is
compatible with the isomorphisms `f^!_{j₁} ≅ f^!_{j₂}` between the upper shriek functors of any two
compactifications.

## Main results

* `Stacks.Duality.upperShriekCompareWithPullback_eq_comparisonMapAlong` — `μ_{f,K}` is the
  abstract one-variable comparison map read along `Lj^*`.
* `Stacks.Duality.upperShriekCompactificationMap_app_eq` — `α_g` through the base change map of
  the right adjoints along derived pullback.
* `Stacks.Duality.upperShriekCompareWithPullback_comp_upperShriekCompactificationMap` — the
  compatibility of `μ_{f,K}` with `α_g`.
* `Stacks.Duality.comparisonMap_comp_upperShriekCompactificationMap` — the same for the
  two-variable comparison maps `Lf^*E ⊗ f^!L ⟶ f^!(E ⊗ L)`.

## References

* [Stacks Project, Tag 0B6T](https://stacks.math.columbia.edu/tag/0B6T)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

/-- The cancellation behind `upperShriekCompareWithPullback_eq_comparisonMapAlong`, over abstract
monoidal categories with bifunctors identified with the tensor products. -/
lemma comparisonMapAlong_bridge {B C : Type*} [Category B] [Category C] [MonoidalCategory B]
    [MonoidalCategory C] (TC : C ⥤ C ⥤ C) (ιC : TC ≅ curriedTensor C) (TB : B ⥤ B ⥤ B)
    (ιB : TB ≅ curriedTensor B) (J : B ⥤ C) [J.Monoidal] {A' : C} {M N Z : B}
    (k : A' ⟶ J.obj M) (c : M ⊗ N ⟶ Z) :
    (TC.map k).app (J.obj N) ≫ ((ιC.hom.app (J.obj M)).app (J.obj N) ≫
        inv (Functor.OplaxMonoidal.δ J M N) ≫ J.map ((ιB.inv.app M).app N)) ≫
      J.map ((ιB.hom.app M).app N ≫ c) =
    (ιC.hom.app A').app (J.obj N) ≫ k ▷ J.obj N ≫ inv (Functor.OplaxMonoidal.δ J M N) ≫
      J.map c := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← J.map_comp_assoc ((ιB.inv.app M).app N), tensorIso_inv_hom_app_app,
    CategoryTheory.Functor.map_id, Category.id_comp, tensorIso_hom_naturality_left_assoc]

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y : FTS S} (f : X ⟶ Y)

/-- The inverse of the monoidality isomorphism of derived pullback, through the identification of
`Stacks.Duality.quasiCoherentDerivedTensor` with the tensor product. -/
theorem quasiCoherentDerivedPullbackTensorIso_inv_app {Z W : Scheme.{u}} (q : Z ⟶ W)
    (P Q : quasiCoherentDerivedCategory W) :
    (quasiCoherentDerivedPullbackTensorIso q).inv.app (P, Q) =
      ((quasiCoherentDerivedTensorIsoCurriedTensor Z).hom.app
          ((quasiCoherentDerivedPullback' q).obj Q)).app ((quasiCoherentDerivedPullback' q).obj P) ≫
        inv (Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' q) Q P) ≫
        (quasiCoherentDerivedPullback' q).map
          (((quasiCoherentDerivedTensorIsoCurriedTensor W).inv.app Q).app P) := by
  rw [IsIso.inv_eq_of_hom_inv_id (Functor.Monoidal.δ_μ (quasiCoherentDerivedPullback' q) Q P)]
  simp only [quasiCoherentDerivedPullbackTensorIso, Functor.Monoidal.swapTensorIso,
    NatIso.ofComponents_inv_app, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv,
    Functor.Monoidal.μIso_hom, Category.assoc]

/-- **`μ_{f,K}` is the one-variable comparison map read along `Lj^*`**
(`Stacks.CategoryTheory.comparisonMapAlong`), once `quasiCoherentDerivedTensor` is identified with
the tensor product of `D_QCoh(𝒪_X)`. -/
theorem upperShriekCompareWithPullback_eq_comparisonMapAlong
    (j : CompactificationOf (Over.mk f.left)) (K : quasiCoherentDerivedCategory Y.left) :
    upperShriekCompareWithPullbackCanonical f j K =
      ((quasiCoherentDerivedTensorIsoCurriedTensor X.left).hom.app
          ((quasiCoherentDerivedPullback' f.left).obj K)).app
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≫
        Stacks.CategoryTheory.comparisonMapAlong
          (quasiCoherentDerivedAdjunction j.toBase (isQuasicoherent_homology_derivedPullback' _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
          (twistedInverseImageAdjunction j.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
          (quasiCoherentDerivedPullback' j.immersion)
          (quasiCoherentDerivedPullbackCompactificationIsoOfComp f j)
          (tensorUnit_quasiCoherentDerivedCategory Y.left) K := by
  rw [upperShriekCompareWithPullbackCanonical,
    quasiCoherentDerivedPullbackTensorIso_inv_app (Z := X.left) (W := j.space) j.immersion,
    twistedInverseImageCompareWithPullback_eq_comparisonMap,
    Stacks.CategoryTheory.comparisonMapAlong]
  exact comparisonMapAlong_bridge (quasiCoherentDerivedTensor X.left)
    (quasiCoherentDerivedTensorIsoCurriedTensor X.left) (quasiCoherentDerivedTensor j.space)
    (quasiCoherentDerivedTensorIsoCurriedTensor j.space) (quasiCoherentDerivedPullback' j.immersion)
    (M := (quasiCoherentDerivedPullback' j.toBase).obj K)
    (N := (twistedInverseImage j.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj (derivedStructureSheaf Y.left))
    ((quasiCoherentDerivedPullbackCompactificationIsoOfComp f j).inv.app K)
    ((quasiCoherentDerivedAdjunction j.toBase (isQuasicoherent_homology_derivedPullback' _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).comparisonMap
      (twistedInverseImageAdjunction j.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)) K (derivedStructureSheaf Y.left) ≫
      (twistedInverseImage j.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        (K ◁ eqToHom (tensorUnit_quasiCoherentDerivedCategory Y.left).symm ≫ (ρ_ K).hom))

/-! ### Coherence of the composition isomorphisms of derived pullback -/

section Coherence

omit [CompactSpace S] [QuasiSeparatedSpace S] in
private lemma chase_of_mono {C : Type*} [Category C] {P Q R R' Q' T : C} (a : P ⟶ Q) (b : Q ⟶ R)
    (m : P ⟶ T) (c : T ⟶ R) (e : R ⟶ R') (e' : Q ⟶ Q') (k : Q' ⟶ R') (n : T ⟶ Q') [Mono k]
    (A : a ≫ b = m ≫ c) (L : b ≫ e = e' ≫ k) (R : n ≫ k = c ≫ e) : a ≫ e' = m ≫ n := by
  rw [← cancel_mono k, Category.assoc, ← L, reassoc_of% A, Category.assoc, R]

/-- **`L𝟙^* ∘ L𝟙^* ≅ L𝟙^*` at `Ld^* N` is `L𝟙^*` of `L𝟙^* ∘ Ld^* ≅ Ld^*`**, a consequence of the
cocycle identity of [Stacks, Tag 0D5S] at `(𝟙, 𝟙, d)` alone. -/
theorem derivedPullbackCompIso_id_id_hom_app {X Z : Scheme.{u}} (d : X ⟶ Z)
    (N : DerivedCategory Z.Modules) :
    (derivedPullbackCompIso (𝟙 X) (𝟙 X)).hom.app ((derivedPullback d).obj N) ≫
        eqToHom (congrArg (fun h : X ⟶ X => (derivedPullback h).obj ((derivedPullback d).obj N))
          (Category.id_comp (𝟙 X))) =
      (derivedPullback (𝟙 X)).map ((derivedPullbackCompIso (𝟙 X) d).hom.app N ≫
        eqToHom (congrArg (fun h : X ⟶ Z => (derivedPullback h).obj N) (Category.id_comp d))) := by
  have A := derivedPullbackCompIso_assoc_app (𝟙 X) (𝟙 X) d N
  have L := derivedPullbackCompIso_hom_app_eqToHom_left d (Category.id_comp (𝟙 X)) N
  have R := map_eqToHom_derivedPullbackCompIso_hom_app (𝟙 X) (Category.id_comp d) N
  rw [Functor.map_comp]
  exact chase_of_mono _ _ _ _ _ _ _ _ A L R

/-- The identification `Stacks.Duality.quasiCoherentDerivedPullbackIdIsoOfComp` of `L𝟙^*` with
the identity undoes the composition isomorphism `L𝟙^* ∘ Ld^* ≅ L(𝟙 ≫ d)^*`. -/
theorem quasiCoherentDerivedPullbackCompIso_inv_app_comp_idIsoOfComp {X Z : Scheme.{u}}
    (d : X ⟶ Z) (N : quasiCoherentDerivedCategory Z) :
    ((quasiCoherentDerivedPullbackCompIso (𝟙 X) d).inv.app N ≫
        (quasiCoherentDerivedPullbackIdIsoOfComp X).hom.app
          ((quasiCoherentDerivedPullback' d).obj N)).hom =
      eqToHom (congrArg (fun h : X ⟶ Z => (derivedPullback h).obj N.obj) (Category.id_comp d)) := by
  have : (derivedPullback (𝟙 X)).Faithful :=
    Functor.Faithful.of_iso (derivedPullbackIdIso X).symm
  have h₁ := congrArg (fun φ => φ.hom) (Functor.FullyFaithful.map_preimage
    ((Functor.FullyFaithful.id _).ofIso (quasiCoherentDerivedPullbackIdIso X
      (isQuasicoherent_homology_derivedPullback' _)).symm)
    ((quasiCoherentDerivedPullbackCompIso (𝟙 X) (𝟙 X) ≪≫
      quasiCoherentDerivedPullbackCongr (Category.id_comp _)).hom.app
      ((quasiCoherentDerivedPullback' d).obj N)))
  have K := derivedPullbackCompIso_id_id_hom_app d N.obj
  apply (derivedPullback (𝟙 X)).map_injective
  rw [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
  refine (congrArg (fun t => (derivedPullback (𝟙 X)).map
    ((derivedPullbackCompIso (𝟙 X) d).inv.app N.obj) ≫ t) (h₁.trans K)).trans ?_
  rw [← Functor.map_comp, Iso.inv_hom_id_app_assoc]

omit [CompactSpace S] [QuasiSeparatedSpace S] in
private lemma iso_chase {C : Type*} [Category C] {P Q R T : C} (x : Q ≅ R) (y : P ≅ Q)
    (z : P ⟶ T) (w : T ≅ R) (A : z ≫ w.hom = y.hom ≫ x.hom) :
    x.inv ≫ y.inv ≫ z = 𝟙 R ≫ w.inv := by
  rw [Category.id_comp, Iso.inv_comp_eq, Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, A]

/-- **The composition isomorphisms of derived pullback around a morphism of factorisations**:
for `f = c₁ ≫ f₁ = c₂ ≫ f₂` with `f₁ = g ≫ f₂` and `c₂ = c₁ ≫ g`, the two identifications of
`Lf^*` with a composite, through `Lc₁^* ∘ Lf₁^*` and `Lc₁^* ∘ Lg^* ∘ Lf₂^*` or through
`Lc₂^* ∘ Lf₂^*`, agree. -/
theorem derivedPullbackCompIso_factorisation_coherence {X X₁ X₂ Y : Scheme.{u}} (c₁ : X ⟶ X₁)
    (c₂ : X ⟶ X₂) (g : X₁ ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (f : X ⟶ Y) (hg : g ≫ f₂ = f₁)
    (w : c₁ ≫ g = c₂) (h₁ : c₁ ≫ f₁ = f) (h₂ : c₂ ≫ f₂ = f) (M : DerivedCategory Y.Modules) :
    eqToHom (congrArg (fun h : X ⟶ Y => (derivedPullback h).obj M) h₁.symm) ≫
        (derivedPullbackCompIso c₁ f₁).inv.app M ≫
        (derivedPullback c₁).map
          (eqToHom (congrArg (fun h : X₁ ⟶ Y => (derivedPullback h).obj M) hg.symm) ≫
            (derivedPullbackCompIso g f₂).inv.app M) ≫
        (derivedPullbackCompIso c₁ g).hom.app ((derivedPullback f₂).obj M) ≫
        eqToHom (congrArg (fun h : X ⟶ X₂ => (derivedPullback h).obj ((derivedPullback f₂).obj M))
          w) =
      eqToHom (congrArg (fun h : X ⟶ Y => (derivedPullback h).obj M) h₂.symm) ≫
        (derivedPullbackCompIso c₂ f₂).inv.app M := by
  subst hg w h₁
  have A := derivedPullbackCompIso_assoc_app c₁ g f₂ M
  have e : eqToHom (congrArg (fun h : X ⟶ Y => (derivedPullback h).obj M) h₂.symm) = 𝟙 _ := rfl
  rw [e]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact iso_chase ((derivedPullbackCompIso c₁ (g ≫ f₂)).app M)
    ((derivedPullback c₁).mapIso ((derivedPullbackCompIso g f₂).app M)) _
    ((derivedPullbackCompIso (c₁ ≫ g) f₂).app M) A

end Coherence

/-! ### The composite adjunction of `g` and `f̄₂` and that of `f̄₁ = g ≫ f̄₂` -/

section CompCongr

variable {Z W Y : Scheme.{u}} [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace W]
  [QuasiSeparatedSpace W] [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Z ⟶ W) (q₂ : W ⟶ Y)
  (q₁ : Z ⟶ Y) (h : g ≫ q₂ = q₁)

/-- The counit of `Lq₁^* ⊣ Rq₁_*` through `Rq₁_* ≅ Rq₂_* ∘ Rg_*` and `Lq₁^* ≅ Lg^* ∘ Lq₂^*`, for
`q₁ = g ≫ q₂`. -/
theorem map_pushforwardCompCongr_comp_counit (M : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedPullback' q₁).map
        ((quasiCoherentDerivedPushforwardCompIso g q₂
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs q₂)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ q₂)) ≪≫
          quasiCoherentDerivedPushforwardCongr h _
            (isQuasicoherent_homology_derivedPushforward_of_qcqs q₁)).hom.app M) ≫
      (quasiCoherentDerivedAdjunction q₁ (isQuasicoherent_homology_derivedPullback' q₁)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs q₁)).counit.app M =
    (quasiCoherentDerivedPullbackCompIso g q₂ ≪≫ quasiCoherentDerivedPullbackCongr h).inv.app _ ≫
      ((quasiCoherentDerivedAdjunction q₂ (isQuasicoherent_homology_derivedPullback' q₂)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs q₂)).comp
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))).counit.app M := by
  subst h
  have e := map_quasiCoherentDerivedPushforwardCompIso_comp_counit g q₂ M
  simp only [quasiCoherentDerivedPushforwardCongr, Iso.trans_hom, Iso.refl_hom, Category.comp_id,
    Iso.trans_inv] at e ⊢
  rw [e]
  congr 1
  apply ObjectProperty.hom_ext
  simp only [Functor.comp_obj, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    quasiCoherentDerivedPullbackCongr_inv_app_hom, eqToHom_refl]
  exact (Category.id_comp _).symm

/-- The counit of `Rq₁_* ⊣ a_{q₁}` through `a_{q₁} ≅ a_g ∘ a_{q₂}` and
`Rq₁_* ≅ Rq₂_* ∘ Rg_*`, for `q₁ = g ≫ q₂`. -/
theorem map_twistedInverseImageCompCongr_inv_comp_counit (L : quasiCoherentDerivedCategory Y) :
    (quasiCoherentDerivedPushforward q₁
      (isQuasicoherent_homology_derivedPushforward_of_qcqs q₁)).map
        ((twistedInverseImageCongr h.symm _
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≪≫
          twistedInverseImageCompIso g q₂ _ _ _).inv.app L) ≫
      (twistedInverseImageAdjunction q₁
        (isQuasicoherent_homology_derivedPushforward_of_qcqs q₁)).counit.app L =
    (quasiCoherentDerivedPushforwardCompIso g q₂
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs q₂)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ q₂)) ≪≫
      quasiCoherentDerivedPushforwardCongr h _
        (isQuasicoherent_homology_derivedPushforward_of_qcqs q₁)).inv.app _ ≫
      ((twistedInverseImageAdjunction g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).comp
        (twistedInverseImageAdjunction q₂
          (isQuasicoherent_homology_derivedPushforward_of_qcqs q₂))).counit.app L := by
  subst h
  have e := map_twistedInverseImageCompIso_inv_comp_counit g q₂ L
  simp only [quasiCoherentDerivedPushforwardCongr, twistedInverseImageCongr, Iso.refl_inv,
    Category.comp_id, Category.id_comp, Iso.trans_inv, Iso.symm_hom] at e ⊢
  exact e

end CompCongr

/-! ### `α_g` through the base change map along derived pullback -/

section CompactificationMap

variable (c₁ c₂ : CompactificationOf (Over.mk f.left)) (g : c₁.space ⟶ c₂.space)
  (hg : g ≫ c₂.toBase = c₁.toBase) (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)

/-- The base change map `a_g ⋙ L(c₁)^* ⟶ L(c₂)^* ⋙ a_{𝟙_X}` of the right adjoints for the open
square `X ⊆ X̄₁` over `X ⊆ X̄₂`, built with derived pullback. -/
abbrev compactificationBaseChange :=
  haveI := isIso_rightAdjointSquare_of_isOpenImmersion c₁.immersion (𝟙 X.left) g c₂.immersion sq
  Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange
    (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (quasiCoherentDerivedAdjunction (𝟙 X.left) (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction c₂.immersion (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction c₁.immersion (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedPullbackCompIso (𝟙 X.left) c₂.immersion)
    (quasiCoherentDerivedPullbackCompIso c₁.immersion g ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
    (twistedInverseImageAdjunction g (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (twistedInverseImageAdjunction (𝟙 X.left)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))

/-- The identification `ā₁ = a_{g ≫ f̄₂} ≅ a_g ∘ ā₂` used by `α_g`. -/
abbrev compactificationMapCompIso :
    twistedInverseImage c₁.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≅
      twistedInverseImage c₂.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs _) :=
  twistedInverseImageCongr hg.symm _ (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≪≫
    twistedInverseImageCompIso g c₂.toBase _ _ _

/-- **`α_g` through derived pullback**: the transformation `α_g` of the proof of
[Stacks, Tag 0AA0] is `L(c₁)^*` of `ā₁ ≅ a_g ∘ ā₂`, followed by the base change map of the right
adjoints along derived pullback for the open square `X ⊆ X̄₁` over `X ⊆ X̄₂` and the
identification of `a_{𝟙_X}` with the identity. -/
theorem upperShriekCompactificationMap_app_eq (K : quasiCoherentDerivedCategory Y.left) :
    (upperShriekCompactificationMap f c₁ c₂ g hg sq).app K =
      (quasiCoherentDerivedPullback' c₁.immersion).map
          ((compactificationMapCompIso f c₁ c₂ g hg).hom.app K) ≫
        (compactificationBaseChange f c₁ c₂ g sq).app
          ((twistedInverseImage c₂.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
        (twistedInverseImageIdIsoOfComp X.left).hom.app
          ((quasiCoherentDerivedPullback' c₂.immersion).obj ((twistedInverseImage c₂.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) := by
  have hs : (upperShriekCompactificationMapSrcIso f c₁ c₂ g hg).hom.app K =
      (quasiCoherentDerivedPullback' c₁.immersion).map
          ((compactificationMapCompIso f c₁ c₂ g hg).hom.app K) ≫
        (Adjunction.leftAdjointUniq
          (quasiCoherentDerivedAdjunction c₁.immersion (isQuasicoherent_homology_derivedPullback' _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
          (OpenImmersion.quasiCoherentDerivedRestrictAdjunction c₁.immersion
            (OpenImmersion.isQuasicoherent_homology_derivedRestrict _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _))).hom.app _ ≫ 𝟙 _ :=
    rfl
  have ht : (upperShriekCompactificationMapTgtIso f c₂).hom.app K =
      (twistedInverseImageIdIsoOfComp X.left).hom.app
          ((OpenImmersion.restrictedDerivedRestrict c₂.immersion).obj
            ((twistedInverseImage c₂.toBase
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫ 𝟙 _ ≫
        (Adjunction.leftAdjointUniq
          (OpenImmersion.quasiCoherentDerivedRestrictAdjunction c₂.immersion
            (OpenImmersion.isQuasicoherent_homology_derivedRestrict _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
          (quasiCoherentDerivedAdjunction c₂.immersion (isQuasicoherent_homology_derivedPullback' _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _))).hom.app _ :=
    rfl
  rw [upperShriekCompactificationMap_app, hs, ht, compactificationBaseChange,
    rightAdjointBaseChange_app_eq_twistedInverseImageRestrictionMap c₁.immersion (𝟙 X.left) g
      c₂.immersion sq]
  have hn : (twistedInverseImageIdIsoOfComp X.left).hom.app
        ((OpenImmersion.restrictedDerivedRestrict c₂.immersion).obj ((twistedInverseImage c₂.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
      (Adjunction.leftAdjointUniq
          (OpenImmersion.quasiCoherentDerivedRestrictAdjunction c₂.immersion
            (OpenImmersion.isQuasicoherent_homology_derivedRestrict _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
          (quasiCoherentDerivedAdjunction c₂.immersion (isQuasicoherent_homology_derivedPullback' _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _))).hom.app ((twistedInverseImage
              c₂.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) =
      (twistedInverseImage (𝟙 X.left) (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
          ((Adjunction.leftAdjointUniq
            (OpenImmersion.quasiCoherentDerivedRestrictAdjunction c₂.immersion
              (OpenImmersion.isQuasicoherent_homology_derivedRestrict _)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
            (quasiCoherentDerivedAdjunction c₂.immersion
              (isQuasicoherent_homology_derivedPullback' _)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _))).hom.app
            ((twistedInverseImage c₂.toBase
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
        (twistedInverseImageIdIsoOfComp X.left).hom.app
          ((quasiCoherentDerivedPullback' c₂.immersion).obj ((twistedInverseImage c₂.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) :=
    ((twistedInverseImageIdIsoOfComp X.left).hom.naturality _).symm
  simp only [Category.assoc, Category.id_comp, Category.comp_id]
  rw [hn]
  exact Category.assoc _ _ _

omit [CompactSpace S] [QuasiSeparatedSpace S] in
private lemma assoc_chase₅ {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ : C} (a : P₀ ⟶ P₁)
    (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (d : P₃ ⟶ P₄) (e₁ : P₄ ⟶ P₅) (e₂ : P₅ ⟶ P₆) (e : P₄ ⟶ P₆)
    (r : P₀ ⟶ P₆) (he : e₁ ≫ e₂ = e) (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    (a ≫ b) ≫ c ≫ (d ≫ e₁) ≫ e₂ = r := by
  rw [← h, ← he]; simp only [Category.assoc]

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- **The identifications `Lf^* ≅ Lf̄ᵢ^* ⋙ Lcᵢ^*` of two compactifications are compatible**
along a morphism `g : X̄₁ ⟶ X̄₂` of compactifications: going through `Lf̄₁^* ≅ Lf̄₂^* ⋙ Lg^*`,
the square `X ⊆ X̄₁` over `X ⊆ X̄₂` and `L(𝟙_X)^* ≅ 𝟭` is going through `Lf̄₂^* ⋙ Lc₂^*`. -/
theorem quasiCoherentDerivedPullbackCompactificationIso_coherence
    (K : quasiCoherentDerivedCategory Y.left) :
    (quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₁).inv.app K ≫
        (quasiCoherentDerivedPullback' c₁.immersion).map
          ((quasiCoherentDerivedPullbackCompIso g c₂.toBase ≪≫
            quasiCoherentDerivedPullbackCongr hg).inv.app K) ≫
        (Stacks.AffineProjectionFormula.squareCompositeIso
          (quasiCoherentDerivedPullbackCompIso (𝟙 X.left) c₂.immersion)
          (quasiCoherentDerivedPullbackCompIso c₁.immersion g ≪≫
            quasiCoherentDerivedPullbackCongr sq.w)).inv.app
          ((quasiCoherentDerivedPullback' c₂.toBase).obj K) ≫
        (quasiCoherentDerivedPullbackIdIsoOfComp X.left).hom.app _ =
      (quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₂).inv.app K := by
  apply ObjectProperty.hom_ext
  have hid := quasiCoherentDerivedPullbackCompIso_inv_app_comp_idIsoOfComp (X := X.left)
    c₂.immersion
    ((quasiCoherentDerivedPullback' c₂.toBase).obj K)
  have hc := derivedPullbackCompIso_factorisation_coherence (X := X.left) c₁.immersion
    c₂.immersion g c₁.toBase
    c₂.toBase f.left hg (sq.w.trans (Category.id_comp _)) (immersion_comp_toBase f c₁)
    (immersion_comp_toBase f c₂) K.obj
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    Stacks.AffineProjectionFormula.squareCompositeIso_inv_app, Category.assoc] at hid ⊢
  have k₁ : ((quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₁).inv.app K).hom =
      eqToHom (congrArg (fun h : X.left ⟶ Y.left => (derivedPullback h).obj K.obj)
        (immersion_comp_toBase f c₁).symm) ≫
        (derivedPullbackCompIso c₁.immersion c₁.toBase).inv.app K.obj := by
    simp only [quasiCoherentDerivedPullbackCompactificationIsoOfComp, Iso.trans_inv,
      NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
      quasiCoherentDerivedPullbackCongr_inv_app_hom,
      quasiCoherentDerivedPullbackCompIso_inv_app_hom]
  have k₂ : ((quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₂).inv.app K).hom =
      eqToHom (congrArg (fun h : X.left ⟶ Y.left => (derivedPullback h).obj K.obj)
        (immersion_comp_toBase f c₂).symm) ≫
        (derivedPullbackCompIso c₂.immersion c₂.toBase).inv.app K.obj := by
    simp only [quasiCoherentDerivedPullbackCompactificationIsoOfComp, Iso.trans_inv,
      NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
      quasiCoherentDerivedPullbackCongr_inv_app_hom,
      quasiCoherentDerivedPullbackCompIso_inv_app_hom]
  have k₃ : ((quasiCoherentDerivedPullback' c₁.immersion).map
      ((quasiCoherentDerivedPullbackCompIso g c₂.toBase ≪≫
        quasiCoherentDerivedPullbackCongr hg).inv.app K)).hom =
      (derivedPullback c₁.immersion).map
        (eqToHom (congrArg (fun h : c₁.space ⟶ Y.left => (derivedPullback h).obj K.obj) hg.symm) ≫
          (derivedPullbackCompIso g c₂.toBase).inv.app K.obj) := by
    simp only [quasiCoherentDerivedPullback_map_hom, Iso.trans_inv, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom, quasiCoherentDerivedPullbackCongr_inv_app_hom,
      quasiCoherentDerivedPullbackCompIso_inv_app_hom]
  have k₄ : ((quasiCoherentDerivedPullbackCompIso c₁.immersion g ≪≫
      quasiCoherentDerivedPullbackCongr sq.w).hom.app
        ((quasiCoherentDerivedPullback' c₂.toBase).obj K)).hom =
      (derivedPullbackCompIso c₁.immersion g).hom.app ((derivedPullback c₂.toBase).obj K.obj) ≫
        eqToHom (congrArg (fun h : X.left ⟶ c₂.space =>
          (derivedPullback h).obj ((derivedPullback c₂.toBase).obj K.obj)) sq.w) := by
    simp only [Iso.trans_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
      quasiCoherentDerivedPullbackCongr_hom_app_hom,
      quasiCoherentDerivedPullbackCompIso_hom_app_hom]
    rfl
  rw [k₁, k₂, k₃, k₄, hid]
  exact assoc_chase₅ _ _ _ _ _ _ _ _ (eqToHom_trans _ _) hc

/-- The composition isomorphism of derived pullback followed by a congruence is monoidal. -/
private instance isMonoidal_pullbackCompIso_trans_congr {Z W V : Scheme.{u}} (a : Z ⟶ W)
    (b : W ⟶ V) (c : Z ⟶ V) (h : a ≫ b = c) :
    NatTrans.IsMonoidal (quasiCoherentDerivedPullbackCompIso a b ≪≫
      quasiCoherentDerivedPullbackCongr h).hom :=
  inferInstanceAs (NatTrans.IsMonoidal ((quasiCoherentDerivedPullbackCompIso a b).hom ≫
    (quasiCoherentDerivedPullbackCongr h).hom))

omit [CompactSpace S] [QuasiSeparatedSpace S] in
private lemma naturality_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ P₅ : C} {ι : P₀ ⟶ P₁}
    {A : P₁ ⟶ P₂} {B : P₂ ⟶ P₃} {Tb : P₀ ⟶ P₄} {ι' : P₄ ⟶ P₅} {Wb : P₁ ⟶ P₅} {D : P₅ ⟶ P₃}
    (hn : Tb ≫ ι' = ι ≫ Wb) (key : A ≫ B = Wb ≫ D) : (ι ≫ A) ≫ B = Tb ≫ ι' ≫ D := by
  rw [reassoc_of% hn, Category.assoc, key]

/-- **`μ_{f,K}` does not depend on the compactification, along a morphism of compactifications**
(the commutative diagram of the proof of [Stacks, Tag 0B6T]): for a morphism `g : X̄₁ ⟶ X̄₂` of
compactifications of `X` over `Y` with `g⁻¹(X) = X`, `μ_{f,K}` for `X̄₁` followed by `α_g` at `K`
is `Lf^*K ⊗ α_g(𝒪_Y)` followed by `μ_{f,K}` for `X̄₂`. -/
theorem upperShriekCompareWithPullback_comp_upperShriekCompactificationMap
    (K : quasiCoherentDerivedCategory Y.left) :
    upperShriekCompareWithPullbackCanonical f c₁ K ≫
        (upperShriekCompactificationMap f c₁ c₂ g hg sq).app K =
      ((quasiCoherentDerivedTensor X.left).obj ((quasiCoherentDerivedPullback' f.left).obj K)).map
          ((upperShriekCompactificationMap f c₁ c₂ g hg sq).app (derivedStructureSheaf Y.left)) ≫
        upperShriekCompareWithPullbackCanonical f c₂ K := by
  have := isIso_twoSquare_of_isOpenImmersion c₁.immersion (𝟙 X.left) g c₂.immersion sq
  have key := Stacks.CategoryTheory.BaseChange.comparisonMapAlong_comp_rightAdjointBaseChange
    (quasiCoherentDerivedAdjunction c₂.toBase (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (twistedInverseImageAdjunction c₂.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (twistedInverseImageAdjunction g (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (quasiCoherentDerivedAdjunction c₂.immersion (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction c₁.immersion (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction (𝟙 X.left) (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (twistedInverseImageAdjunction (𝟙 X.left)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedPullbackCompIso (𝟙 X.left) c₂.immersion)
    (quasiCoherentDerivedPullbackCompIso c₁.immersion g ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
    (Stacks.CategoryTheory.BaseChange.squareComposite_δ_compat _ _
      (NatTrans.IsMonoidal.δ_comp_tensorHom
        (quasiCoherentDerivedPullbackCompIso (𝟙 X.left) c₂.immersion).hom)
      (NatTrans.IsMonoidal.δ_comp_tensorHom
        (quasiCoherentDerivedPullbackCompIso c₁.immersion g ≪≫
          quasiCoherentDerivedPullbackCongr sq.w).hom))
    (quasiCoherentDerivedPullbackIdIsoOfComp X.left)
    (δ_comp_quasiCoherentDerivedPullbackIdIsoOfComp X.left)
    (quasiCoherentDerivedAdjunction c₁.toBase (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (twistedInverseImageAdjunction c₁.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedPullbackCompIso g c₂.toBase ≪≫ quasiCoherentDerivedPullbackCongr hg)
    (quasiCoherentDerivedPushforwardCompIso g c₂.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ c₂.toBase)) ≪≫
      quasiCoherentDerivedPushforwardCongr hg _
        (isQuasicoherent_homology_derivedPushforward_of_qcqs c₁.toBase))
    (compactificationMapCompIso f c₁ c₂ g hg)
    (NatTrans.IsMonoidal.δ_comp_tensorHom
      (quasiCoherentDerivedPullbackCompIso g c₂.toBase ≪≫ quasiCoherentDerivedPullbackCongr hg).hom)
    (map_pushforwardCompCongr_comp_counit g c₂.toBase c₁.toBase hg)
    (map_twistedInverseImageCompCongr_inv_comp_counit g c₂.toBase c₁.toBase hg)
    (quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₁)
    (quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₂)
    (quasiCoherentDerivedPullbackCompactificationIso_coherence f c₁ c₂ g hg sq)
    (tensorUnit_quasiCoherentDerivedCategory Y.left) K
  rw [upperShriekCompareWithPullback_eq_comparisonMapAlong,
    upperShriekCompareWithPullback_eq_comparisonMapAlong, upperShriekCompactificationMap_app_eq,
    upperShriekCompactificationMap_app_eq]
  exact naturality_chase (tensorIso_hom_naturality_right _ _ _ _) key

/-- `upperShriekCompareWithPullback_comp_upperShriekCompactificationMap` followed by `f^!` of a
morphism `h : N ⟶ M`: `μ_{f,N}` for `X̄₁`, `f^!h` and `α_g` at `M` is `Lf^*N ⊗ α_g(𝒪_Y)`, `μ_{f,N}`
for `X̄₂` and `f^!h`. -/
theorem upperShriekCompareWithPullback_comp_map_comp_upperShriekCompactificationMap
    {N M : quasiCoherentDerivedCategory Y.left} (h : N ⟶ M) :
    (upperShriekCompareWithPullbackCanonical f c₁ N ≫ (upperShriek f c₁).map h) ≫
        (upperShriekCompactificationMap f c₁ c₂ g hg sq).app M =
      ((quasiCoherentDerivedTensor X.left).obj ((quasiCoherentDerivedPullback' f.left).obj N)).map
          ((upperShriekCompactificationMap f c₁ c₂ g hg sq).app (derivedStructureSheaf Y.left)) ≫
        upperShriekCompareWithPullbackCanonical f c₂ N ≫ (upperShriek f c₂).map h := by
  rw [Category.assoc, (upperShriekCompactificationMap f c₁ c₂ g hg sq).naturality h,
    reassoc_of% (upperShriekCompareWithPullback_comp_upperShriekCompactificationMap f c₁ c₂ g hg sq
      N)]

/-- **The two-variable comparison maps of two compactifications are compatible with `α_g`**: for
`E`, `L` in `D_QCoh(𝒪_Y)`, the map `Lf^*E ⊗ f^!L ⟶ f^!(E ⊗ L)` given by `Lj^*` of the comparison
map `Lf̄^*E ⊗ ā(L) ⟶ ā(E ⊗ L)` for `X̄₁`, followed by `α_g` at `E ⊗ L`, is `Lf^*E ⊗ α_g(L)`
followed by the same map for `X̄₂`. At `L = 𝒪_Y` this is
`upperShriekCompareWithPullback_comp_upperShriekCompactificationMap`. -/
theorem comparisonMap_comp_upperShriekCompactificationMap
    (E L : quasiCoherentDerivedCategory Y.left) :
    (quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₁).inv.app E ▷
          (upperShriek f c₁).obj L ≫
        Functor.LaxMonoidal.μ (quasiCoherentDerivedPullback' c₁.immersion) _ _ ≫
        (quasiCoherentDerivedPullback' c₁.immersion).map
          ((quasiCoherentDerivedAdjunction c₁.toBase (isQuasicoherent_homology_derivedPullback' _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).comparisonMap
            (twistedInverseImageAdjunction c₁.toBase
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)) E L) ≫
        (upperShriekCompactificationMap f c₁ c₂ g hg sq).app (E ⊗ L) =
    (quasiCoherentDerivedPullback' f.left).obj E ◁
        (upperShriekCompactificationMap f c₁ c₂ g hg sq).app L ≫
      (quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₂).inv.app E ▷
          (upperShriek f c₂).obj L ≫
        Functor.LaxMonoidal.μ (quasiCoherentDerivedPullback' c₂.immersion) _ _ ≫
        (quasiCoherentDerivedPullback' c₂.immersion).map
          ((quasiCoherentDerivedAdjunction c₂.toBase (isQuasicoherent_homology_derivedPullback' _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).comparisonMap
            (twistedInverseImageAdjunction c₂.toBase
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)) E L) := by
  have := isIso_twoSquare_of_isOpenImmersion c₁.immersion (𝟙 X.left) g c₂.immersion sq
  have key := Stacks.CategoryTheory.BaseChange.comparisonMap_comp_rightAdjointBaseChange_of_iso
    (quasiCoherentDerivedAdjunction c₂.toBase (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (twistedInverseImageAdjunction c₂.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (twistedInverseImageAdjunction g (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (quasiCoherentDerivedAdjunction c₂.immersion (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction c₁.immersion (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction (𝟙 X.left) (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (twistedInverseImageAdjunction (𝟙 X.left)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedPullbackCompIso (𝟙 X.left) c₂.immersion)
    (quasiCoherentDerivedPullbackCompIso c₁.immersion g ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
    (Stacks.CategoryTheory.BaseChange.squareComposite_δ_compat _ _
      (NatTrans.IsMonoidal.δ_comp_tensorHom
        (quasiCoherentDerivedPullbackCompIso (𝟙 X.left) c₂.immersion).hom)
      (NatTrans.IsMonoidal.δ_comp_tensorHom
        (quasiCoherentDerivedPullbackCompIso c₁.immersion g ≪≫
          quasiCoherentDerivedPullbackCongr sq.w).hom))
    (quasiCoherentDerivedPullbackIdIsoOfComp X.left)
    (δ_comp_quasiCoherentDerivedPullbackIdIsoOfComp X.left)
    (quasiCoherentDerivedAdjunction c₁.toBase (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (twistedInverseImageAdjunction c₁.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedPullbackCompIso g c₂.toBase ≪≫ quasiCoherentDerivedPullbackCongr hg)
    (quasiCoherentDerivedPushforwardCompIso g c₂.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ c₂.toBase)) ≪≫
      quasiCoherentDerivedPushforwardCongr hg _
        (isQuasicoherent_homology_derivedPushforward_of_qcqs c₁.toBase))
    (compactificationMapCompIso f c₁ c₂ g hg)
    (NatTrans.IsMonoidal.δ_comp_tensorHom
      (quasiCoherentDerivedPullbackCompIso g c₂.toBase ≪≫ quasiCoherentDerivedPullbackCongr hg).hom)
    (map_pushforwardCompCongr_comp_counit g c₂.toBase c₁.toBase hg)
    (map_twistedInverseImageCompCongr_inv_comp_counit g c₂.toBase c₁.toBase hg)
    (quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₁)
    (quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₂)
    (quasiCoherentDerivedPullbackCompactificationIso_coherence f c₁ c₂ g hg sq)
    E L
  have hμ : ∀ {Z W : Scheme.{u}} (q : Z ⟶ W) (A B : quasiCoherentDerivedCategory W),
      Functor.LaxMonoidal.μ (quasiCoherentDerivedPullback' q) A B =
        inv (Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' q) A B) := fun q A B =>
    (IsIso.inv_eq_of_hom_inv_id (Functor.Monoidal.δ_μ (quasiCoherentDerivedPullback' q) A B)).symm
  rw [hμ, hμ, upperShriekCompactificationMap_app_eq, upperShriekCompactificationMap_app_eq]
  exact key

end CompactificationMap

/-! ### Independence of the compactification -/

section Noetherian

variable [AlgebraicGeometry.IsNoetherian S]

/-- `𝒪_Y` as an object of `D⁺_QCoh(𝒪_Y)`. -/
abbrev derivedStructureSheafPlus (Z : Scheme.{u}) : quasiCoherentDerivedCategoryPlusOfModel Z :=
  ⟨derivedStructureSheaf Z, Stacks.Duality.KoszulRegular.isBoundedBelow_singleFunctor_obj _⟩

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
private lemma iso_pair_chase {C D : Type*} [Category C] [Category D] (T : C ⥤ D) {O₁ OZ O₂ : C}
    {Q₁ QZ Q₂ : D} (μ₁ : T.obj O₁ ⟶ Q₁) (μZ : T.obj OZ ⟶ QZ) (μ₂ : T.obj O₂ ⟶ Q₂)
    (aO : OZ ⟶ O₁) (xO : O₁ ⟶ OZ) (bO : OZ ⟶ O₂) (aK : QZ ⟶ Q₁) (xK : Q₁ ⟶ QZ) (bK : QZ ⟶ Q₂)
    (hxO : xO ≫ aO = 𝟙 _) (hxK : aK ≫ xK = 𝟙 _) (hF : μZ ≫ aK = T.map aO ≫ μ₁)
    (hS : μZ ≫ bK = T.map bO ≫ μ₂) : μ₁ ≫ xK ≫ bK = T.map (xO ≫ bO) ≫ μ₂ := by
  have h : μ₁ ≫ xK = T.map xO ≫ μZ := by
    rw [← Category.comp_id μZ, ← hxK, reassoc_of% hF, ← T.map_comp_assoc, hxO, T.map_id,
      Category.id_comp]
  rw [reassoc_of% h, hS, T.map_comp_assoc]

open DominatingCompactification in
/-- `upperShriekCompareWithPullback_comp_upperShriekPlusIso` followed by `f^!` of a morphism
`h : N ⟶ M` into an object of `D⁺_QCoh(𝒪_Y)`; `N` itself is arbitrary. -/
theorem upperShriekCompareWithPullback_comp_map_comp_upperShriekPlusIso
    (j₁ j₂ : CompactificationOf (Over.mk f.left)) {N : quasiCoherentDerivedCategory Y.left}
    {M : quasiCoherentDerivedCategoryPlusOfModel Y.left} (h : N ⟶ M.obj) :
    upperShriekCompareWithPullbackCanonical f j₁ N ≫ (upperShriek f j₁).map h ≫
        ((upperShriekPlusIso f j₁ j₂).hom.app M).hom =
      ((quasiCoherentDerivedTensor X.left).obj ((quasiCoherentDerivedPullback' f.left).obj N)).map
          ((upperShriekPlusIso f j₁ j₂).hom.app (derivedStructureSheafPlus Y.left)).hom ≫
        upperShriekCompareWithPullbackCanonical f j₂ N ≫ (upperShriek f j₂).map h := by
  have : IsProper (X := (compactification f j₁ j₂).space) (fst f j₁ j₂) :=
    (inferInstance : IsProper (fst f j₁ j₂))
  have : IsProper (X := (compactification f j₁ j₂).space) (snd f j₁ j₂) :=
    (inferInstance : IsProper (snd f j₁ j₂))
  set eF := upperShriekCompactificationIso f (compactification f j₁ j₂) j₁ (fst f j₁ j₂) rfl
    (isPullback_fst f j₁ j₂)
  set eS := upperShriekCompactificationIso f (compactification f j₁ j₂) j₂ (snd f j₁ j₂)
    (fst_comp_toBase f j₁ j₂).symm (isPullback_snd f j₁ j₂)
  have hxK : (eF.hom.app M).hom ≫ (eF.inv.app M).hom = 𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]; rfl
  have hxO : (eF.inv.app (derivedStructureSheafPlus Y.left)).hom ≫
      (eF.hom.app (derivedStructureSheafPlus Y.left)).hom = 𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]; rfl
  have e := iso_pair_chase _ _ _ _ _ _ _ _ _ _ hxO hxK
    (upperShriekCompareWithPullback_comp_map_comp_upperShriekCompactificationMap f
      (compactification f j₁ j₂) j₁ (fst f j₁ j₂) rfl (isPullback_fst f j₁ j₂) h)
    (upperShriekCompareWithPullback_comp_map_comp_upperShriekCompactificationMap f
      (compactification f j₁ j₂) j₂ (snd f j₁ j₂) (fst_comp_toBase f j₁ j₂).symm
      (isPullback_snd f j₁ j₂) h)
  exact (Category.assoc _ _ _).symm.trans e

open DominatingCompactification in
/-- **[Stacks, Tag 0B6T]: `μ_{f,K}` does not depend on the compactification.** For two
compactifications `j₁`, `j₂` of `X` over `Y` and `K ∈ D⁺_QCoh(𝒪_Y)`, `μ_{f,K}` for `j₁`, followed
by the isomorphism `f^!_{j₁} ≅ f^!_{j₂}` of [Stacks, Tag 0AA0] at `K`, is `Lf^*K` tensored with
that isomorphism at `𝒪_Y`, followed by `μ_{f,K}` for `j₂`. -/
@[stacks 0B6T "independence of the compactification"]
theorem upperShriekCompareWithPullback_comp_upperShriekPlusIso
    (j₁ j₂ : CompactificationOf (Over.mk f.left))
    (K : quasiCoherentDerivedCategoryPlusOfModel Y.left) :
    upperShriekCompareWithPullbackCanonical f j₁ K.obj ≫
        ((upperShriekPlusIso f j₁ j₂).hom.app K).hom =
      ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj K.obj)).map
          ((upperShriekPlusIso f j₁ j₂).hom.app (derivedStructureSheafPlus Y.left)).hom ≫
        upperShriekCompareWithPullbackCanonical f j₂ K.obj := by
  have e := upperShriekCompareWithPullback_comp_map_comp_upperShriekPlusIso f j₁ j₂ (𝟙 K.obj)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at e
  erw [Category.id_comp, Category.comp_id] at e
  exact e

end Noetherian

end Stacks.Duality

end
