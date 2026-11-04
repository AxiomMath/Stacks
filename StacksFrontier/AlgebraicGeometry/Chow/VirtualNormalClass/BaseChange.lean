module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.ConeBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Construction
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ProperModification
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess

/-!
# The bivariant class of a virtual normal bundle is compatible with base change

Let `i : Z ⟶ X` be a closed immersion, `𝒩` a virtual normal bundle for `i` of constant rank `r`,
`h : X' ⟶ X` a morphism locally of finite type, `i' : Z' = Z ×_X X' ⟶ X'` the base change and
`𝒩' = g^*𝒩` the virtual normal bundle of Stacks 0FBJ. The second statement of Stacks 0FBK says
that `c(Z' ⟶ X', 𝒩')` is the restriction of `c(Z ⟶ X, 𝒩)` of Stacks 0F9Z.

Following the source, it suffices to compare the caps on `α ∈ A_k(T)` for a test scheme
`T ⟶ X'`. The vector bundle `N' = 𝐕(𝒩'^∨)` is `N ×_Z Z'`, so `T ×_{X'} N' = T ×_X N` and flat
pullback along the projections agrees (Stacks 02RG). The class at infinity of `D(Z' ⊆ X')` pushes
forward to the one of `D(Z ⊆ X)` along the closed immersion of special fibres (Stacks 0FAQ,
`Stacks.Chow.GysinAtInfinity.properChowPushforward_infinityCap`), and the closed immersions of the
special fibres into `N'` and `N` are compatible
(`Stacks.Chow.VirtualNormalBundle.Comparison.specialFibreEmbedding_comp_bundleMap`). Hence the
transport of `c ∩ α` satisfies the defining equation `p'^*(c' ∩ α) = ι'_* j'^*(C' ∩ α)`, and the
uniqueness of Stacks 0FBK gives `c' ∩ α = c ∩ α`, that is `c' = res(c)`.

Everything is stated for a cartesian square of closed immersions and a comparison of virtual
normal bundles over it (`Stacks.Chow.VirtualNormalBundle.Comparison`), the base change `g^*𝒩` of
Stacks 0FBJ being one.

## Main results

* `Stacks.Chow.VirtualNormalBundle.Comparison.isPullback_bundleMap` — `N' = N ×_Z Z'`.
* `Stacks.Chow.VirtualNormalBundle.eq_virtualNormalClass_of_middleCap` — uniqueness, in the form
  of the defining equation.
* `Stacks.Chow.VirtualNormalBundle.Comparison.virtualNormalClass_cap` — `c' ∩ α = c ∩ α`.
* `Stacks.Chow.VirtualNormalBundle.bivariantRestriction_virtualNormalClass` — `c' = res(c)` for
  the chosen fibre product.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.Conormal (coborderIdeal)

universe u

namespace Stacks.Chow.VirtualNormalBundle

section RestrictionTest

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {h : X' ⟶ X}
  (sq : IsPullback i' g h i) {T : Scheme.{u}} (t : T ⟶ X')

include sq in
/-- `Z' ×_{X'} T`, with the projection to `Z` through `g` and the projection to `T`, is a fibre
product of `i` and `t ≫ h`. -/
theorem isPullback_restrictionTest :
    IsPullback (pullback.fst i' t ≫ g) (pullback.snd i' t) i (t ≫ h) :=
  (IsPullback.of_hasPullback i' t).paste_horiz sq.flip

/-- The comparison `e₁ : T ×_{X'} Z' ≅ T ×_X Z` of the restriction. -/
def restrictionTestIso : pullback i' t ≅ pullback i (t ≫ h) :=
  (isPullback_restrictionTest sq t).isoPullback

/-- `e₁` followed by the projection to `Z` is the projection to `Z'` followed by `g`. -/
@[reassoc (attr := simp)]
theorem restrictionTestIso_hom_fst :
    (restrictionTestIso sq t).hom ≫ pullback.fst i (t ≫ h) = pullback.fst i' t ≫ g :=
  IsPullback.isoPullback_hom_fst _

/-- `e₁` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem restrictionTestIso_hom_snd :
    (restrictionTestIso sq t).hom ≫ pullback.snd i (t ≫ h) = pullback.snd i' t :=
  IsPullback.isoPullback_hom_snd _

/-- `e₁⁻¹` followed by the projection to `Z'` and `g` is the projection to `Z`. -/
@[reassoc (attr := simp)]
theorem restrictionTestIso_inv_fst :
    (restrictionTestIso sq t).inv ≫ pullback.fst i' t ≫ g = pullback.fst i (t ≫ h) :=
  (Iso.inv_comp_eq _).2 (restrictionTestIso_hom_fst sq t).symm

/-- `e₁⁻¹` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem restrictionTestIso_inv_snd :
    (restrictionTestIso sq t).inv ≫ pullback.snd i' t = pullback.snd i (t ≫ h) :=
  (Iso.inv_comp_eq _).2 (restrictionTestIso_hom_snd sq t).symm

end RestrictionTest

section Geometry

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] {i' : Z' ⟶ X'}
  [IsClosedImmersion i'] {g : Z' ⟶ Z} {h : X' ⟶ X} {sq : IsPullback i' g h i}
  {𝒩 : VirtualNormalBundle i} {𝒩' : VirtualNormalBundle i'} (Φ : Comparison sq 𝒩 𝒩')

/-- `𝐕(𝒩'^∨) ⟶ 𝐕(g^*(𝒩^∨))` is an isomorphism, the comparison being one. -/
instance Comparison.isIso_vectorBundleMap :
    IsIso (Scheme.Modules.vectorBundleMap Z'
      (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
      (G := dualSheaf 𝒩'.bundle) Φ.map).left := by
  let e := asIso Φ.map
  refine ⟨⟨(Scheme.Modules.vectorBundleMap Z' (F := dualSheaf 𝒩'.bundle)
    (G := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle)) e.inv).left, ?_, ?_⟩⟩
  · refine (Over.comp_left _ _ _ _ _).symm.trans ?_
    refine (congrArg Over.Hom.left (Scheme.Modules.vectorBundleMap_comp Z'
      (F := dualSheaf 𝒩'.bundle)
      (G := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
      (H := dualSheaf 𝒩'.bundle) e.inv e.hom).symm).trans ?_
    refine (congrArg (fun φ => (Scheme.Modules.vectorBundleMap Z' φ).left)
      e.inv_hom_id).trans ?_
    exact congrArg Over.Hom.left (Scheme.Modules.vectorBundleMap_id Z')
  · refine (Over.comp_left _ _ _ _ _).symm.trans ?_
    refine (congrArg Over.Hom.left (Scheme.Modules.vectorBundleMap_comp Z'
      (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
      (G := dualSheaf 𝒩'.bundle)
      (H := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
      e.hom e.inv).symm).trans ?_
    refine (congrArg (fun φ => (Scheme.Modules.vectorBundleMap Z' φ).left)
      e.hom_inv_id).trans ?_
    exact congrArg Over.Hom.left (Scheme.Modules.vectorBundleMap_id Z')

/-- **`N' = N ×_Z Z'`**: the square of `Ψ : N' ⟶ N` over `g : Z' ⟶ Z` is cartesian. -/
theorem Comparison.isPullback_bundleMap :
    IsPullback (Φ.bundleMap) 𝒩'.proj 𝒩.proj
      g := by
  have h1 : IsPullback (Scheme.Modules.vectorBundleMap Z'
      (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
      (G := dualSheaf 𝒩'.bundle) Φ.map).left 𝒩'.proj
      (Scheme.Modules.vectorBundleToBase Z'
        ((Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      exact Scheme.Modules.vectorBundleMap_left_comp _ _⟩
  have h2 := h1.paste_horiz (Scheme.Modules.isPullback_vectorBundleBaseChangeMap
    g (dualSheaf 𝒩.bundle))
  rw [Category.id_comp] at h2
  exact h2

/-- **`N' = N ×_X X'`**, through `Z' = Z ×_X X'`. -/
theorem Comparison.isPullback_bundleMap_comp :
    IsPullback (Φ.bundleMap) (𝒩'.proj ≫ i')
      (𝒩.proj ≫ i) h :=
  (Φ.isPullback_bundleMap).paste_vert sq.flip

variable {T : Scheme.{u}} (t : T ⟶ X')

/-- **`T ×_{X'} N' ≅ T ×_X N`.** -/
def Comparison.bundleTestIso :
    pullback (𝒩'.proj ≫ i') t ≅ pullback (𝒩.proj ≫ i) (t ≫ h) :=
  (((IsPullback.of_hasPullback (𝒩'.proj ≫ i') t).flip.paste_vert
    (Φ.isPullback_bundleMap_comp).flip).flip).isoPullback

/-- `T ×_{X'} N' ≅ T ×_X N` followed by the projection to `N` is the projection to `N'` followed
by `Ψ : N' ⟶ N`. -/
@[reassoc (attr := simp)]
theorem Comparison.bundleTestIso_hom_fst :
    (Φ.bundleTestIso t).hom ≫ pullback.fst (𝒩.proj ≫ i) (t ≫ h) =
      pullback.fst _ t ≫ Φ.bundleMap :=
  IsPullback.isoPullback_hom_fst _

/-- `T ×_{X'} N' ≅ T ×_X N` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem Comparison.bundleTestIso_hom_snd :
    (Φ.bundleTestIso t).hom ≫ pullback.snd (𝒩.proj ≫ i) (t ≫ h) = pullback.snd _ t :=
  IsPullback.isoPullback_hom_snd _

/-- **`N' ×_{Z'} (Z' ×_{X'} T) ≅ N ×_Z (Z ×_X T)`.** -/
def Comparison.fibreTestMap :
    pullback 𝒩'.proj (pullback.fst i' t) ⟶
      pullback 𝒩.proj (pullback.fst i (t ≫ h)) :=
  pullback.map _ _ _ _ (Φ.bundleMap) (restrictionTestIso sq t).hom g
    (Φ.isPullback_bundleMap).w.symm (by simp)

/-- `N' ×_{Z'} (Z' ×_{X'} T) ⟶ N ×_Z (Z ×_X T)` is an isomorphism. -/
instance Comparison.isIso_fibreTestMap : IsIso (Φ.fibreTestMap t) := by
  have hP : IsPullback (pullback.fst 𝒩'.proj (pullback.fst i' t)
      ≫ Φ.bundleMap)
      (pullback.snd _ _ ≫ (restrictionTestIso sq t).hom) 𝒩.proj (pullback.fst i (t ≫ h)) := by
    have h1 := (IsPullback.of_hasPullback 𝒩'.proj
      (pullback.fst i' t)).flip.paste_vert
        (Φ.isPullback_bundleMap).flip
    refine h1.flip.of_iso (Iso.refl _) (Iso.refl _) (restrictionTestIso sq t) (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    simp
  have he : Φ.fibreTestMap t = hP.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [IsPullback.isoPullback_hom_fst]
      simp [fibreTestMap]
    · rw [IsPullback.isoPullback_hom_snd]
      simp [fibreTestMap]
  rw [he]
  infer_instance

end Geometry

/-- The cap of the proper pushforward of Stacks 0EPK of a class read for a morphism equal to the
composite `f ≫ g` and a degree equal to its own. -/
theorem canonicalBivariantProperPushforward_copy_cap_heq (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f]
    (g : Y ⟶ Z)
    [LocallyOfFiniteType g] (q : X ⟶ Z) [LocallyOfFiniteType q] (hq : q = f ≫ g)
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (hqs : q ≫ sZ = sX) {p p' : ℤ} (hpp : p = p')
    (c : CanonicalBivariantClass C sX sZ q hqs p) {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (m : pullback q t ⟶ pullback g t) [IsProper m]
    (hm₁ : m ≫ pullback.fst g t = pullback.fst q t ≫ f)
    (hm₂ : m ≫ pullback.snd g t = pullback.snd q t)
    (hms : m ≫ (pullback.fst g t ≫ sY) = pullback.fst q t ≫ sX) (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k) :
    (canonicalBivariantProperPushforward C sX sY sZ f g hf hg p'
        (BivariantClass.copy C (canonicalGysinSystem C) sX sZ hq hqs
          (comp_comp_structureMorphism_eq hf hg) hpp c)).cap t k α ≍
      properChowPushforward C (pullback.fst q t ≫ sX) (pullback.fst g t ≫ sY) m hms (k - p)
        (properPushforwardDescends C _ _ _ _ _) (c.cap t k α) := by
  subst hpp
  exact heq_of_eq (GysinAtInfinity.canonicalBivariantProperPushforward_copy_cap C sX sY sZ f g q
    hq hf hg hqs p c t m hm₁ hm₂ hms k α)

section Uniqueness

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] (𝒩 : VirtualNormalBundle i)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)
  (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **Uniqueness in Stacks 0FBK, in the form of the defining equation**: a class `c` with
`p^*(c ∩ α) = ι_* j^*(C ∩ α)` on every test scheme is `c(Z ⟶ X, 𝒩)`. -/
theorem eq_virtualNormalClass_of_middleCap
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hZ r)
    (hc : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      haveI := 𝒩.locallyOfFiniteType_projection r
      haveI := 𝒩.flat_projection r
      middleCap C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ) sZ 𝒩.proj i
          rfl (-(r : ℤ)) (𝒩.pullbackClass C sZ r) t (k - r) (c.cap t k α) =
        chowGroupDegreeEquiv C (pullback.fst (𝒩.proj ≫ i) t ≫ (𝒩.proj ≫ sZ))
          (by ring : k - (-(r : ℤ) + r) = k - r - -(r : ℤ))
          ((𝒩.pushforwardClass C sX sZ hZ r).cap t k α)) :
    c = 𝒩.virtualNormalClass C sX sZ hZ r := by
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩.flat_projection r
  refine BivariantClass.ext C _ sZ sX i hZ r ?_
  intro T t _ k α
  exact (𝒩.middleCap_pullbackClass_bijective C sZ r t (k - r)).1
    ((hc t k α).trans (𝒩.middleCap_virtualNormalClass_cap C sX sZ hZ r t k α).symm)

/-- **The cap of `ι_* ∘ j^* ∘ C`**: `(ι_* ∘ j^* ∘ C) ∩ α = ι_{T,*}(j^*(C ∩ α))`, along any
morphism `T ×_X Z(t⁻¹) ⟶ T ×_X N` over `ι` and `T`. -/
theorem pushforwardClass_cap_heq {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]
    [LocallyOfFiniteType 𝒩.proj] (m : pullback ((Stacks.Deformation.specialFibre i).subschemeι ≫
      Stacks.Deformation.deformationProjection i) t ⟶ pullback (𝒩.proj ≫ i) t) [IsProper m]
    (hm₁ : m ≫ pullback.fst (𝒩.proj ≫ i) t = pullback.fst _ t ≫ 𝒩.specialFibreEmbedding)
    (hm₂ : m ≫ pullback.snd (𝒩.proj ≫ i) t = pullback.snd _ t)
    (hms : m ≫ (pullback.fst (𝒩.proj ≫ i) t ≫ (𝒩.proj ≫ sZ)) =
      pullback.fst _ t ≫ ((Stacks.Deformation.specialFibre i).subschemeι ≫
        (Stacks.Deformation.deformationProjection i ≫ sX)))
    (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    (𝒩.pushforwardClass C sX sZ hZ r).cap t k α ≍
      properChowPushforward C _ (pullback.fst (𝒩.proj ≫ i) t ≫ (𝒩.proj ≫ sZ)) m hms (k - 0)
        (properPushforwardDescends C _ _ _ _ _)
        ((Stacks.Deformation.normalConeClass C sX i).cap t k α) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  refine (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).trans
    (canonicalBivariantProperPushforward_copy_cap_heq C _ (𝒩.proj ≫ sZ) sX
      𝒩.specialFibreEmbedding (𝒩.proj ≫ i) _ (𝒩.specialFibreEmbedding_projection_comp).symm
      (𝒩.specialFibreEmbedding_comp_structure C sX sZ hZ) (𝒩.projection_comp_structure C sX sZ hZ)
      (Category.assoc _ _ _) rfl (Stacks.Deformation.normalConeClass C sX i) t m hm₁ hm₂ hms k α)

end Uniqueness

section ChowHelpers

variable (C : ChowSituation.{u}) {A B D E : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]
  (sE : E ⟶ C.S) [LocallyOfFiniteType sE]

/-- An isomorphism, a proper morphism and an isomorphism push forward as their composite. -/
theorem chowPushforwardOfIso_properChowPushforward_chowPushforwardOfIso (u : A ⟶ B) [IsIso u]
    (v : B ⟶ D) [IsProper v] (w : D ⟶ E) [IsIso w] (z : A ⟶ E) [IsProper z]
    (hz : u ≫ v ≫ w = z) (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hw : w ≫ sE = sD)
    (hzs : z ≫ sE = sA) (k : ℤ)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv k)
    (hfacz : ProperPushforwardFactorsThroughRationalEquivalence C sA sE z hzs k)
    (x : chowGroup C sA k) :
    chowPushforwardOfIso C sD sE w hw k
        (properChowPushforward C sB sD v hv k hfacv (chowPushforwardOfIso C sA sB u hu k x)) =
      properChowPushforward C sA sE z hzs k hfacz x := by
  subst hz
  rw [chowPushforwardOfIso, chowPushforwardOfIso,
    ← properChowPushforward_comp_apply C sA sB sD u v (u ≫ v) rfl hu hv
      (by rw [Category.assoc, hv, hu]) k _ hfacv
      (properPushforwardFactorsThroughRationalEquivalence_comp C sA sB sD u v hu hv k
        (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sB u hu k) hfacv),
    ← properChowPushforward_comp_apply C sA sD sE (u ≫ v) w (u ≫ v ≫ w)
      (Category.assoc _ _ _) (by rw [Category.assoc, hv, hu]) hw hzs k]

/-- Pushforward along an isomorphism respects heterogeneous equality across two readings of the
degree. -/
theorem chowPushforwardOfIso_heq_of_heq (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA) {n n' : ℤ}
    (hn : n = n') {x : chowGroup C sA n} {y : chowGroup C sA n'} (hxy : x ≍ y) :
    chowPushforwardOfIso C sA sB u hu n x ≍ chowPushforwardOfIso C sA sB u hu n' y := by
  subst hn
  rw [eq_of_heq hxy]

/-- The base change of a proper morphism `f` along a test scheme, read for a morphism `q` equal to
`f ≫ g`, is proper. -/
theorem isProper_of_pullback_map_eq {X Y Z T : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z)
    (q : X ⟶ Z) (hq : q = f ≫ g) (t : T ⟶ Z) (m : pullback q t ⟶ pullback g t)
    (hm₁ : m ≫ pullback.fst g t = pullback.fst q t ≫ f)
    (hm₂ : m ≫ pullback.snd g t = pullback.snd q t) : IsProper m := by
  subst hq
  obtain rfl : m = bivariantPushforwardBaseChange f g t :=
    pullback.hom_ext (by rw [hm₁, bivariantPushforwardBaseChange_fst])
      (by rw [hm₂, bivariantPushforwardBaseChange_snd])
  infer_instance

end ChowHelpers

section SpecialFibre

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] {i' : Z' ⟶ X'}
  [IsClosedImmersion i'] {g : Z' ⟶ Z} {h : X' ⟶ X} (sq : IsPullback i' g h i)

/-- `φ⁻¹(Z(t⁻¹)) = Z(t'⁻¹)`: the zero scheme of the pulled-back parameter is the special fibre of
`D(Z' ⊆ X')`. -/
theorem zeroScheme_pullback_paramGlobal :
    Stacks.Divisors.zeroScheme (Stacks.Deformation.deformationSpace (coborderIdeal i'))
        ((Scheme.Modules.pullback (Stacks.Deformation.deformationMapOver sq)).obj
          (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i))))
        (AlgebraicGeometry.pullbackGlobalSections (Stacks.Deformation.deformationMapOver sq)
          (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
          (Stacks.Deformation.paramGlobal (coborderIdeal i))) =
      Stacks.Deformation.specialFibre i' :=
  (Stacks.Divisors.zeroScheme_pullback _ _ _).trans
    (Stacks.Deformation.comap_zeroScheme_paramGlobal (Stacks.Deformation.coborderMapOver i i' h)
      (coborderIdeal i) (coborderIdeal i')
      (Stacks.Deformation.coborderIdeal_baseChange sq).le)

/-- **The morphism of special fibres `χ : Z(t'⁻¹) ⟶ Z(t⁻¹)`** over `D(Z' ⊆ X') ⟶ D(Z ⊆ X)`. -/
def specialFibreMap :
    (Stacks.Deformation.specialFibre i').subscheme ⟶
      (Stacks.Deformation.specialFibre i).subscheme :=
  eqToHom (congrArg Scheme.IdealSheafData.subscheme (zeroScheme_pullback_paramGlobal sq).symm) ≫
    zeroSchemePullbackHom (Stacks.Deformation.deformationMapOver sq)
      (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
      (Stacks.Deformation.paramGlobal (coborderIdeal i))

/-- `χ` commutes with the closed immersions of the special fibres into `D(Z' ⊆ X')` and
`D(Z ⊆ X)`. -/
theorem specialFibreMap_subschemeι :
    specialFibreMap sq ≫ (Stacks.Deformation.specialFibre i).subschemeι =
      (Stacks.Deformation.specialFibre i').subschemeι ≫
        Stacks.Deformation.deformationMapOver sq := by
  rw [specialFibreMap, Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc,
    Stacks.Chow.subschemeι_eqToHom (zeroScheme_pullback_paramGlobal sq).symm]

/-- `χ` commutes with the projections of the special fibres to `X'` and `X`. -/
theorem specialFibreMap_comp_projection :
    ((Stacks.Deformation.specialFibre i').subschemeι ≫
        Stacks.Deformation.deformationProjection i') ≫ h =
      specialFibreMap sq ≫ ((Stacks.Deformation.specialFibre i).subschemeι ≫
        Stacks.Deformation.deformationProjection i) :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (Stacks.Deformation.deformationMapOver_projection sq).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (specialFibreMap_subschemeι sq).symm).trans (Category.assoc _ _ _))))

variable {T : Scheme.{u}} (t : T ⟶ X')

/-- The base change `T ×_{X'} Z(t'⁻¹) ⟶ T ×_X Z(t⁻¹)` of `χ`. -/
abbrev specialFibreTestMap :
    pullback ((Stacks.Deformation.specialFibre i').subschemeι ≫
        Stacks.Deformation.deformationProjection i') t ⟶
      pullback ((Stacks.Deformation.specialFibre i).subschemeι ≫
        Stacks.Deformation.deformationProjection i) (t ≫ h) :=
  pullback.map _ _ _ _ (specialFibreMap sq) (𝟙 T) h (specialFibreMap_comp_projection sq)
    (by simp)

/-- The base change `T ×_{X'} D(Z' ⊆ X') ⟶ T ×_X D(Z ⊆ X)` is proper. -/
instance isProper_testMapOver_deformation :
    IsProper (GysinAtInfinity.testMapOver h (Stacks.Deformation.deformationProjection i)
      (Stacks.Deformation.deformationProjection i')
      (Stacks.Deformation.deformationMapOver sq)
      (Stacks.Deformation.deformationMapOver_projection sq) t) :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (GysinAtInfinity.isPullback_testMapOver h _ _ _ _ t) inferInstance

/-- The map from the base change of the complement of the special fibre of `D(Z' ⊆ X')` to that
of `D(Z ⊆ X)` along a test scheme `T ⟶ X'` is an isomorphism. -/
instance isIso_openMapOver_deformation :
    IsIso (GysinAtInfinity.openMapOver h (Stacks.Deformation.deformationProjection i)
      (Stacks.Deformation.complementOpen (coborderIdeal i)).ι
      (Stacks.Deformation.deformationProjection i')
      (Stacks.Deformation.complementOpen (coborderIdeal i')).ι
      (Stacks.Deformation.deformationMapOver sq)
      (Stacks.Deformation.deformationMapOver_projection sq)
      (Stacks.Deformation.complementMapOver sq) (Stacks.Deformation.complementMapOver_ι sq) t) :=
  (GysinAtInfinity.isPullback_testMapOver h
    ((Stacks.Deformation.complementOpen (coborderIdeal i)).ι ≫
      Stacks.Deformation.deformationProjection i)
    ((Stacks.Deformation.complementOpen (coborderIdeal i')).ι ≫
      Stacks.Deformation.deformationProjection i')
    (Stacks.Deformation.complementMapOver sq)
    (GysinAtInfinity.openMapOver_eq h _ _ _ _ _
      (Stacks.Deformation.deformationMapOver_projection sq)
      _ (Stacks.Deformation.complementMapOver_ι sq)).symm t).isIso_snd_of_isIso

/-- Over a test scheme `T ⟶ X'`, the base changes of the complements of the special fibres form a
cartesian square with the base change `T ×_{X'} D(Z' ⊆ X') ⟶ T ×_X D(Z ⊆ X)`. -/
theorem isPullback_openMapOver_deformation :
    IsPullback (Stacks.Chow.GysinAtInfinity.openBaseChange
        (Stacks.Deformation.deformationProjection i')
        (Stacks.Deformation.complementOpen (coborderIdeal i')).ι t)
      (GysinAtInfinity.openMapOver h (Stacks.Deformation.deformationProjection i)
        (Stacks.Deformation.complementOpen (coborderIdeal i)).ι
        (Stacks.Deformation.deformationProjection i')
        (Stacks.Deformation.complementOpen (coborderIdeal i')).ι
        (Stacks.Deformation.deformationMapOver sq)
        (Stacks.Deformation.deformationMapOver_projection sq)
        (Stacks.Deformation.complementMapOver sq) (Stacks.Deformation.complementMapOver_ι sq) t)
      (GysinAtInfinity.testMapOver h (Stacks.Deformation.deformationProjection i)
        (Stacks.Deformation.deformationProjection i')
        (Stacks.Deformation.deformationMapOver sq)
        (Stacks.Deformation.deformationMapOver_projection sq) t)
      (Stacks.Chow.GysinAtInfinity.openBaseChange (Stacks.Deformation.deformationProjection i)
        (Stacks.Deformation.complementOpen (coborderIdeal i)).ι (t ≫ h)) :=
  GysinAtInfinity.isPullback_openMapOver h _ _ _ _ _ _ _ _
    (Stacks.Deformation.isPullback_complementMapOver sq) t

/-- The base change of `χ` along `T ⟶ X'`, precomposed with the identification of the zero
scheme of the pulled-back parameter with `Z(t'⁻¹)`, is the map of zero schemes induced by
`T ×_{X'} D(Z' ⊆ X') ⟶ T ×_X D(Z ⊆ X)`. -/
theorem divisorChangeMap_comp_specialFibreTestMap [IsLocallyNoetherian X]
    [IsLocallyNoetherian X'] :
    GysinAtInfinity.divisorChangeMap (Stacks.Deformation.deformationProjection i')
        _ _ _ _ (zeroScheme_pullback_paramGlobal sq) t ≫ specialFibreTestMap sq t =
      GysinAtInfinity.infinityMapOver h (Stacks.Deformation.deformationProjection i)
        (Stacks.Deformation.deformationProjection i')
        (Stacks.Deformation.deformationMapOver sq)
        (Stacks.Deformation.deformationMapOver_projection sq)
        (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
        (Stacks.Deformation.paramGlobal (coborderIdeal i)) t := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, specialFibreMap,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · simp

/-- `T ×_{X'} Z(t'⁻¹) ⟶ T ×_X Z(t⁻¹)` is proper. -/
instance isProper_specialFibreTestMap [IsLocallyNoetherian X] [IsLocallyNoetherian X'] :
    IsProper (specialFibreTestMap sq t) := by
  have hc := divisorChangeMap_comp_specialFibreTestMap sq t
  have e : specialFibreTestMap sq t = inv (GysinAtInfinity.divisorChangeMap
      (Stacks.Deformation.deformationProjection i')
        _ _ _ _ (zeroScheme_pullback_paramGlobal sq) t) ≫
      GysinAtInfinity.infinityMapOver h (Stacks.Deformation.deformationProjection i)
        (Stacks.Deformation.deformationProjection i')
        (Stacks.Deformation.deformationMapOver sq)
        (Stacks.Deformation.deformationMapOver_projection sq)
        (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
        (Stacks.Deformation.paramGlobal (coborderIdeal i)) t := by
    rw [← hc, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [LocallyOfFiniteType h]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType h] in
/-- `T ×_{X'} Z(t'⁻¹) ⟶ T ×_X Z(t⁻¹)` is a morphism over the base `C.S`. -/
theorem specialFibreTestMap_comp_structure :
    specialFibreTestMap sq t ≫ (pullback.fst ((Stacks.Deformation.specialFibre i).subschemeι ≫
        Stacks.Deformation.deformationProjection i) (t ≫ h) ≫
          ((Stacks.Deformation.specialFibre i).subschemeι ≫
            (Stacks.Deformation.deformationProjection i ≫ sX))) =
      pullback.fst ((Stacks.Deformation.specialFibre i').subschemeι ≫
        Stacks.Deformation.deformationProjection i') t ≫
          ((Stacks.Deformation.specialFibre i').subschemeι ≫
            (Stacks.Deformation.deformationProjection i' ≫ (h ≫ sX))) := by
  rw [pullback.lift_fst_assoc]
  have := congrArg (· ≫ sX) (specialFibreMap_comp_projection sq)
  simp only [Category.assoc] at this ⊢
  rw [this]

/-- **Stacks 0FAQ for the deformation spaces of `Z ⊆ X` and of its base change**: pushing
`C' ∩ α` forward along `T ×_{X'} Z(t'⁻¹) ⟶ T ×_X Z(t⁻¹)` gives `C ∩ α`. -/
theorem properChowPushforward_specialFibreTestMap_normalConeClass [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ (h ≫ sX)) k) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sX)
    properChowPushforward C _ _ (specialFibreTestMap sq t)
        (specialFibreTestMap_comp_structure sq t C sX) (k - 0)
        (properPushforwardDescends C _ _ _ _ _)
        ((Stacks.Deformation.normalConeClass C (h ≫ sX) i').cap t k α) =
      (Stacks.Deformation.normalConeClass C sX i).cap (t ≫ h) k
        (chowGroupCongr C (Category.assoc t h sX).symm k α) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sX)
  have hcompl₁ : Set.range (pullbackZeroScheme (Stacks.Deformation.deformationMapOver sq)
      (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
      (Stacks.Deformation.paramGlobal (coborderIdeal i))).subschemeι.base =
      (Set.range (Stacks.Deformation.complementOpen
        (coborderIdeal i')).ι.base)ᶜ :=
    (congrArg (fun I : Scheme.IdealSheafData _ => Set.range I.subschemeι.base)
      (zeroScheme_pullback_paramGlobal sq)).trans
      (Stacks.Deformation.range_zeroScheme_paramGlobal _)
  have htriv₁ : AlgebraicGeometry.SheafOfModules.IsTrivial
      (pullbackZeroScheme (Stacks.Deformation.deformationMapOver sq)
        (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
        (Stacks.Deformation.paramGlobal (coborderIdeal i))).subscheme.sheaf.obj
      (pullbackZeroScheme (Stacks.Deformation.deformationMapOver sq)
        (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
        (Stacks.Deformation.paramGlobal (coborderIdeal i))).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (pullbackZeroScheme (Stacks.Deformation.deformationMapOver sq)
        (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
        (Stacks.Deformation.paramGlobal (coborderIdeal i))).subschemeι).obj
          ((Scheme.Modules.pullback (Stacks.Deformation.deformationMapOver sq)).obj
            (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i))))) :=
    ⟨(Scheme.Modules.pullback _).mapIso (Scheme.Modules.pullbackUnitIso _) ≪≫
      Scheme.Modules.pullbackUnitIso _⟩
  have hchg := GysinAtInfinity.chowPushforwardOfIso_infinityCap_change (C := C) (f := h ≫ sX)
    (π := Stacks.Deformation.deformationProjection i')
    (j := (Stacks.Deformation.complementOpen (coborderIdeal i')).ι)
    (hU := Stacks.Deformation.relativeDimension_complementOpen_deformationProjection _)
    (s := AlgebraicGeometry.pullbackGlobalSections (Stacks.Deformation.deformationMapOver sq)
      (Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
      (Stacks.Deformation.paramGlobal (coborderIdeal i)))
    (s₂ := Stacks.Deformation.paramGlobal (coborderIdeal i'))
    (hz := zeroScheme_pullback_paramGlobal sq) (hcompl := hcompl₁) (htriv := htriv₁)
    (hcompl₂ := Stacks.Deformation.range_zeroScheme_paramGlobal _)
    (htriv₂ := Stacks.Chow.isTrivial_pullback_unitModule _)
    (e := Scheme.Modules.pullbackUnitIso _) (g := t) (k := k) (α := α)
  have hL1 := GysinAtInfinity.properChowPushforward_infinityCap (C := C) (f := sX) (h := h)
    (π := Stacks.Deformation.deformationProjection i)
    (j := (Stacks.Deformation.complementOpen (coborderIdeal i)).ι)
    (π' := Stacks.Deformation.deformationProjection i')
    (j' := (Stacks.Deformation.complementOpen (coborderIdeal i')).ι)
    (φ := Stacks.Deformation.deformationMapOver sq)
    (hφ := Stacks.Deformation.deformationMapOver_projection sq)
    (e := Stacks.Deformation.complementMapOver sq)
    (he := Stacks.Deformation.complementMapOver_ι sq)
    (L := Scheme.unitModule (Stacks.Deformation.deformationSpace (coborderIdeal i)))
    (s := Stacks.Deformation.paramGlobal (coborderIdeal i))
    (hU := Stacks.Deformation.relativeDimension_complementOpen_deformationProjection _)
    (hU' := Stacks.Deformation.relativeDimension_complementOpen_deformationProjection _)
    (hcompl := Stacks.Deformation.range_zeroScheme_paramGlobal _)
    (htriv := Stacks.Chow.isTrivial_pullback_unitModule _)
    (hcompl' := hcompl₁) (htriv' := htriv₁) (g := t)
    (hsq := isPullback_openMapOver_deformation sq t) (k := k) (α := α)
  refine (congrArg (properChowPushforward C _ _ (specialFibreTestMap sq t)
    (specialFibreTestMap_comp_structure sq t C sX) (k - 0)
    (properPushforwardDescends C _ _ _ _ _)) hchg.symm).trans ?_
  refine (properChowPushforward_comp_apply C _ _ _ _ _ _
    (divisorChangeMap_comp_specialFibreTestMap sq t) _ _
    (GysinAtInfinity.infinityMapOver_comp_structure C sX h _ _ _ _ _ _ t) (k - 0) _
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _).symm.trans ?_
  refine hL1.trans ?_
  exact congrArg _ (chowPushforwardOfIso_id_eq_chowGroupCongr C _ k α)

end SpecialFibre

section Test

/-- The base change `T ×_X Z(t⁻¹) ⟶ T ×_X N` of `ι : Z(t⁻¹) ⟶ N`. -/
abbrev specialFibreEmbeddingTest {Z₀ X₀ : Scheme.{u}} {i₀ : Z₀ ⟶ X₀} [IsImmersion i₀]
    (𝒩₀ : VirtualNormalBundle i₀) {T : Scheme.{u}} (t : T ⟶ X₀) :
    pullback ((Stacks.Deformation.specialFibre i₀).subschemeι ≫
      Stacks.Deformation.deformationProjection i₀) t ⟶ pullback (𝒩₀.proj ≫ i₀) t :=
  pullback.map _ _ _ _ 𝒩₀.specialFibreEmbedding (𝟙 T) (𝟙 X₀)
    (by rw [Category.comp_id, 𝒩₀.specialFibreEmbedding_projection_comp]) (by simp)

/-- `T ×_X Z(t⁻¹) ⟶ T ×_X N` is proper. -/
instance isProper_specialFibreEmbeddingTest {Z₀ X₀ : Scheme.{u}} {i₀ : Z₀ ⟶ X₀} [IsImmersion i₀]
    (𝒩₀ : VirtualNormalBundle i₀) {T : Scheme.{u}} (t : T ⟶ X₀) :
    IsProper (specialFibreEmbeddingTest 𝒩₀ t) :=
  isProper_of_pullback_map_eq 𝒩₀.specialFibreEmbedding (𝒩₀.proj ≫ i₀) _
    𝒩₀.specialFibreEmbedding_projection_comp.symm t _ (by simp) (by simp)

/-- `T ×_X Z(t⁻¹) ⟶ T ×_X N` is a morphism over the base `C.S`. -/
theorem specialFibreEmbeddingTest_comp_structure {Z₀ X₀ : Scheme.{u}} {i₀ : Z₀ ⟶ X₀}
    [IsImmersion i₀] (𝒩₀ : VirtualNormalBundle i₀) (C : ChowSituation.{u}) (sX₀ : X₀ ⟶ C.S)
    [LocallyOfFiniteType sX₀] (sZ₀ : Z₀ ⟶ C.S) [LocallyOfFiniteType sZ₀] (hZ₀ : i₀ ≫ sX₀ = sZ₀)
    {T : Scheme.{u}} (t : T ⟶ X₀) :
    specialFibreEmbeddingTest 𝒩₀ t ≫ (pullback.fst (𝒩₀.proj ≫ i₀) t ≫ (𝒩₀.proj ≫ sZ₀)) =
      pullback.fst _ t ≫ ((Stacks.Deformation.specialFibre i₀).subschemeι ≫
        (Stacks.Deformation.deformationProjection i₀ ≫ sX₀)) := by
  rw [pullback.lift_fst_assoc]
  exact (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (𝒩₀.specialFibreEmbedding_comp_structure C sX₀ sZ₀ hZ₀))

end Test

section ChowPrelim

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] {i' : Z' ⟶ X'}
  [IsClosedImmersion i'] {g : Z' ⟶ Z} {h : X' ⟶ X} (sq : IsPullback i' g h i)
  [LocallyOfFiniteType h]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)

include sq in
omit [IsClosedImmersion i] [IsClosedImmersion i'] in
/-- The base change of a morphism locally of finite type is locally of finite type. -/
theorem locallyOfFiniteType_baseChange_fst : LocallyOfFiniteType g :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance

include sq hZ in
omit [IsClosedImmersion i] [IsClosedImmersion i'] [LocallyOfFiniteType h]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] in
/-- The structure morphisms of `Z'` through `i'` and through `g` agree. -/
theorem baseChange_structure : i' ≫ (h ≫ sX) = g ≫ sZ := by
  rw [← Category.assoc, sq.w, Category.assoc, hZ]

omit [IsClosedImmersion i] [IsClosedImmersion i'] [LocallyOfFiniteType h]
    [LocallyOfFiniteType sZ] in
/-- `e₁⁻¹ : T ×_X Z ≅ T ×_{X'} Z'` is an isomorphism over the base `C.S`. -/
theorem restrictionTestIso_inv_comp_structure {T : Scheme.{u}} (t : T ⟶ X') :
    (restrictionTestIso sq t).inv ≫ (pullback.fst i' t ≫ (g ≫ sZ)) = pullback.fst i (t ≫ h) ≫ sZ :=
  restrictionTestIso_inv_fst_assoc sq t sZ

end ChowPrelim

section Chow

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] {i' : Z' ⟶ X'}
  [IsClosedImmersion i'] {g : Z' ⟶ Z} {h : X' ⟶ X} {sq : IsPullback i' g h i}
  [LocallyOfFiniteType h] {𝒩 : VirtualNormalBundle i} {𝒩' : VirtualNormalBundle i'}
  (Φ : Comparison sq 𝒩 𝒩')
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)
  (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle r]

omit [LocallyOfFiniteType h] [LocallyOfFiniteType sZ] in
/-- `T ×_{X'} N' ≅ T ×_X N` is an isomorphism over the base `C.S`. -/
theorem Comparison.bundleTestIso_hom_comp_structure {T : Scheme.{u}} (t : T ⟶ X') :
    (Φ.bundleTestIso t).hom ≫ (pullback.fst (𝒩.proj ≫ i) (t ≫ h) ≫ (𝒩.proj ≫ sZ)) =
      pullback.fst (𝒩'.proj ≫ i') t ≫
        (𝒩'.proj ≫ (g ≫ sZ)) := by
  rw [Comparison.bundleTestIso_hom_fst_assoc, reassoc_of% Φ.isPullback_bundleMap.w]

/-- **The flat pullback side of the defining equation is compatible with base change**: under
`T ×_{X'} N' ≅ T ×_X N`, `p'^*(e_* y)` is `p^* y` for `y ∈ A_*(T ×_X Z)` and
`e : T ×_X Z ≅ T ×_{X'} Z'`. -/
theorem Comparison.chowPushforwardOfIso_middleCap_restriction {T : Scheme.{u}}
    (t : T ⟶ X') [LocallyOfFiniteType t] (k : ℤ)
    (y : chowGroup C (pullback.fst i (t ≫ h) ≫ sZ) k) :
    haveI := locallyOfFiniteType_baseChange_fst sq
    haveI := 𝒩.locallyOfFiniteType_projection r
    haveI := 𝒩.flat_projection r
    haveI := 𝒩'.locallyOfFiniteType_projection r
    haveI := 𝒩'.flat_projection r
    chowPushforwardOfIso C _ _ (Φ.bundleTestIso t).hom
        (Φ.bundleTestIso_hom_comp_structure C sZ t) (k - -(r : ℤ))
        (middleCap C (gysinSystemOfInvertible C)
          (𝒩'.proj ≫ (g ≫ sZ)) (g ≫ sZ)
          𝒩'.proj i' rfl (-(r : ℤ))
          (𝒩'.pullbackClass C (g ≫ sZ) r) t k
          (chowPushforwardOfIso C _ _ (restrictionTestIso sq t).inv
            (restrictionTestIso_inv_comp_structure sq C sZ t) k y)) =
      middleCap C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ) sZ 𝒩.proj i rfl (-(r : ℤ))
        (𝒩.pullbackClass C sZ r) (t ≫ h) k y := by
  have := locallyOfFiniteType_baseChange_fst sq
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩.flat_projection r
  have := 𝒩'.locallyOfFiniteType_projection r
  have := 𝒩'.flat_projection r
  have hd := pullbackSnd_comp_structureMorphism_eq C (𝒩.proj ≫ sZ) sZ 𝒩.proj rfl
    (pullback.fst i (t ≫ h))
  have hv := pullbackSnd_comp_structureMorphism_eq C
    (𝒩'.proj ≫ (g ≫ sZ)) (g ≫ sZ)
    𝒩'.proj rfl (pullback.fst i' t)
  have he1 := restrictionTestIso_inv_comp_structure sq C sZ t
  have hw : inv (Φ.fibreTestMap t) ≫ (pullback.fst 𝒩'.proj
      (pullback.fst i' t) ≫ (𝒩'.proj ≫
        (g ≫ sZ))) = pullback.fst 𝒩.proj (pullback.fst i (t ≫ h)) ≫
          (𝒩.proj ≫ sZ) := by
    rw [IsIso.inv_comp_eq, fibreTestMap, pullback.lift_fst_assoc,
      Category.assoc, reassoc_of% Φ.isPullback_bundleMap.w]
  have hsq : pullback.snd 𝒩.proj (pullback.fst i (t ≫ h)) ≫ (restrictionTestIso sq t).inv =
      inv (Φ.fibreTestMap t) ≫ pullback.snd 𝒩'.proj
        (pullback.fst i' t) := by
    rw [IsIso.eq_inv_comp, fibreTestMap, pullback.lift_snd_assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hflat := flatPullbackChow_chowPushforwardOfIso C _ _ _ _ (restrictionTestIso sq t).inv he1
    (inv (Φ.fibreTestMap t)) hw _ hd _ hv hsq r
    (relativeDimension_pullback_snd _ _ r (𝒩.relativeDimension_projection r))
    (relativeDimension_pullback_snd _ _ r (𝒩'.relativeDimension_projection r))
    k (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) y
  have hmor : inv (Φ.fibreTestMap t) ≫
      ((pullbackRightPullbackFstIso i' t 𝒩'.proj).hom ≫
        (Φ.bundleTestIso t).hom) =
      (pullbackRightPullbackFstIso i (t ≫ h) 𝒩.proj).hom := by
    rw [IsIso.inv_comp_eq]
    refine pullback.hom_ext ?_ ?_
    · simp [fibreTestMap]
    · simp [fibreTestMap]
  refine (congrArg (fun z => chowPushforwardOfIso C _ _ (Φ.bundleTestIso t).hom
    (Φ.bundleTestIso_hom_comp_structure C sZ t) (k - -(r : ℤ))
    (properChowPushforward C _ _
      (pullbackRightPullbackFstIso i' t 𝒩'.proj).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp _ _ _ t) (k - -(r : ℤ))
      (properPushforwardDescends C _ _ _ _ _)
      (chowGroupDegreeEquiv C _ (by ring : k + r = k - -(r : ℤ)) z))) hflat).trans ?_
  rw [chowGroupDegreeEquiv_chowPushforwardOfIso]
  exact chowPushforwardOfIso_properChowPushforward_chowPushforwardOfIso C _ _ _ _
    (inv (Φ.fibreTestMap t))
    (pullbackRightPullbackFstIso i' t 𝒩'.proj).hom
    (Φ.bundleTestIso t).hom (pullbackRightPullbackFstIso i (t ≫ h) 𝒩.proj).hom hmor _ _ _ _
    _ (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _

omit [LocallyOfFiniteType h] in
/-- The base changes of the closed immersions of the special fibres into `N'` and `N` commute with
`T ×_{X'} Z(t'⁻¹) ⟶ T ×_X Z(t⁻¹)` and `T ×_{X'} N' ≅ T ×_X N`. -/
theorem Comparison.specialFibreEmbeddingTest_comp_bundleTestIso {T : Scheme.{u}} (t : T ⟶ X') :
    specialFibreEmbeddingTest 𝒩' t ≫ (Φ.bundleTestIso t).hom =
      specialFibreTestMap sq t ≫ specialFibreEmbeddingTest 𝒩 (t ≫ h) := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, bundleTestIso_hom_fst, pullback.lift_fst_assoc,
      pullback.lift_fst]
    rw [Φ.specialFibreEmbedding_comp_bundleMap (specialFibreMap sq) (specialFibreMap_subschemeι sq)]
  · simp

/-- **The proper pushforward side of the defining equation is compatible with base change**: under
`T ×_{X'} N' ≅ T ×_X N`, `ι'_* j'^*(C' ∩ α)` is `ι_* j^*(C ∩ α)`. -/
theorem Comparison.chowPushforwardOfIso_pushforwardClass {T : Scheme.{u}} (t : T ⟶ X')
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (h ≫ sX)) k) :
    haveI := locallyOfFiniteType_baseChange_fst sq
    haveI := 𝒩.locallyOfFiniteType_projection r
    haveI := 𝒩'.locallyOfFiniteType_projection r
    chowPushforwardOfIso C _ _ (Φ.bundleTestIso t).hom
        (Φ.bundleTestIso_hom_comp_structure C sZ t) (k - (-(r : ℤ) + r))
        ((𝒩'.pushforwardClass C (h ≫ sX) (g ≫ sZ)
          (baseChange_structure sq C sX sZ hZ) r).cap t k α) =
      (𝒩.pushforwardClass C sX sZ hZ r).cap (t ≫ h) k
        (chowGroupCongr C (Category.assoc t h sX).symm k α) := by
  have := locallyOfFiniteType_baseChange_fst sq
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩'.locallyOfFiniteType_projection r
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sX)
  have hL' := 𝒩'.pushforwardClass_cap_heq C (h ≫ sX) (g ≫ sZ)
    (baseChange_structure sq C sX sZ hZ) r t
    (specialFibreEmbeddingTest 𝒩' t) (by simp) (by simp)
    (specialFibreEmbeddingTest_comp_structure _ C _ _
      (baseChange_structure sq C sX sZ hZ) t) k α
  have hL := 𝒩.pushforwardClass_cap_heq C sX sZ hZ r (t ≫ h)
    (specialFibreEmbeddingTest 𝒩 (t ≫ h)) (by simp) (by simp)
    (specialFibreEmbeddingTest_comp_structure _ C _ _ hZ (t ≫ h)) k
    (chowGroupCongr C (Category.assoc t h sX).symm k α)
  have hσ := properChowPushforward_specialFibreTestMap_normalConeClass sq t C sX k α
  refine eq_of_heq ((chowPushforwardOfIso_heq_of_heq C _ _ _ _ (by ring) hL').trans
    (HEq.trans (heq_of_eq ?_) hL.symm))
  refine (properChowPushforward_comp_apply C _ _ _ _ _ _
    (Φ.specialFibreEmbeddingTest_comp_bundleTestIso t) _ _
    (by rw [Category.assoc, specialFibreEmbeddingTest_comp_structure _ C _ _ hZ (t ≫ h),
      specialFibreTestMap_comp_structure]) (k - 0)
    (properPushforwardDescends C _ _ _ _ _) _
    (properPushforwardDescends C _ _ _ _ _) _).symm.trans ?_
  refine (properChowPushforward_comp_apply C _
    (pullback.fst ((Stacks.Deformation.specialFibre i).subschemeι ≫
      Stacks.Deformation.deformationProjection i) (t ≫ h) ≫
        ((Stacks.Deformation.specialFibre i).subschemeι ≫
          (Stacks.Deformation.deformationProjection i ≫ sX))) _
    (specialFibreTestMap sq t) (specialFibreEmbeddingTest 𝒩 (t ≫ h)) _ rfl
    (specialFibreTestMap_comp_structure sq t C sX)
    (specialFibreEmbeddingTest_comp_structure _ C _ _ hZ (t ≫ h)) _ (k - 0)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _).trans ?_
  exact congrArg _ hσ

include Φ in
/-- **Stacks 0FBK, compatibility with base change, on caps**: for a cartesian square of closed
immersions `i' : Z' ⟶ X'`, `i : Z ⟶ X` over `h : X' ⟶ X` locally of finite type and a virtual
normal bundle `𝒩` for `i` of constant rank `r`, the class `c(Z' ⟶ X', 𝒩')` of the virtual normal
bundle `𝒩' = g^*𝒩` of Stacks 0FBJ caps by `c' ∩ α = c ∩ α`, read through
`T ×_X Z ≅ T ×_{X'} Z'`. -/
theorem Comparison.virtualNormalClass_cap {T : Scheme.{u}} (t : T ⟶ X') [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ (h ≫ sX)) k) :
    haveI := locallyOfFiniteType_baseChange_fst sq
    (𝒩'.virtualNormalClass C (h ≫ sX) (g ≫ sZ)
        (baseChange_structure sq C sX sZ hZ) r).cap t k α =
      chowPushforwardOfIso C _ _ (restrictionTestIso sq t).inv
        (restrictionTestIso_inv_comp_structure sq C sZ t) (k - r)
        ((𝒩.virtualNormalClass C sX sZ hZ r).cap (t ≫ h) k
          (chowGroupCongr C (Category.assoc t h sX).symm k α)) := by
  have := locallyOfFiniteType_baseChange_fst sq
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩.flat_projection r
  have := 𝒩'.locallyOfFiniteType_projection r
  have := 𝒩'.flat_projection r
  apply (𝒩'.middleCap_pullbackClass_bijective C (g ≫ sZ) r t (k - r)).1
  apply chowPushforwardOfIso_injective C _ _ (Φ.bundleTestIso t).hom
    (Φ.bundleTestIso_hom_comp_structure C sZ t) (k - r - -(r : ℤ))
  refine Eq.trans ?_ (Φ.chowPushforwardOfIso_middleCap_restriction C sZ r t (k - r)
    _).symm
  refine (congrArg _ (𝒩'.middleCap_virtualNormalClass_cap C (h ≫ sX) (g ≫ sZ)
    (baseChange_structure sq C sX sZ hZ) r t k α)).trans ?_
  refine Eq.trans ?_ (𝒩.middleCap_virtualNormalClass_cap C sX sZ hZ r (t ≫ h) k _).symm
  refine (chowGroupDegreeEquiv_chowPushforwardOfIso C _ _ _ _ _ _).symm.trans ?_
  exact congrArg _ (Φ.chowPushforwardOfIso_pushforwardClass C sX sZ hZ r t k α)

end Chow

section Restriction

variable {Z X X' : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (h : X' ⟶ X)
  [LocallyOfFiniteType h] (𝒩 : VirtualNormalBundle i)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)
  (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

omit [IsClosedImmersion i] [LocallyOfFiniteType h] in
/-- For the chosen fibre product `Z ×_X X'`, the inverse of `e₁` is the canonical isomorphism
`T ×_X Z ≅ (Z ×_X X') ×_{X'} T`. -/
theorem restrictionTestIso_eq {T : Scheme.{u}} (t : T ⟶ X') :
    (restrictionTestIso (IsPullback.of_hasPullback i h).flip t).inv =
      (pullbackLeftPullbackSndIso i h t).inv := by
  rw [← cancel_epi (restrictionTestIso (IsPullback.of_hasPullback i h).flip t).hom,
    Iso.hom_inv_id]
  refine (Iso.eq_comp_inv _).2 (pullback.hom_ext ?_ ?_)
  · simp
  · simp

/-- The base change `g^*𝒩` of a virtual normal bundle of constant rank `r` has constant rank
`r`. -/
instance isFiniteLocallyFreeOfRank_baseChange_bundle :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (𝒩.baseChangeAlong (IsPullback.of_hasPullback i h).flip).bundle r :=
  isFiniteLocallyFreeOfRank_modulePullback (pullback.fst i h) 𝒩.bundle r ‹_›

/-- **Compatibility with base change**: for a closed immersion `i : Z ⟶ X`, a virtual normal
bundle `𝒩` for `i` of constant rank `r` and `h : X' ⟶ X` locally of finite type, the class
`c(Z' ⟶ X', 𝒩')` of the virtual normal bundle `𝒩' = g^*𝒩` for `Z' = Z ×_X X' ⟶ X'` is the
restriction of `c(Z ⟶ X, 𝒩)`. -/
@[stacks 0FBK "compatibility with base change at constant rank r: for X' → X locally of finite \
type, c(Z ×_X X' → X', g^*𝒩) = res(c(Z → X, 𝒩)) in A^r(Z ×_X X' → X') (Stacks 0FBJ, 0F9Z)"]
theorem bivariantRestriction_virtualNormalClass :
    bivariantRestrictionOfInvertible C sZ sX i hZ h (r : ℤ) (𝒩.virtualNormalClass C sX sZ hZ r) =
      (𝒩.baseChangeAlong (IsPullback.of_hasPullback i h).flip).virtualNormalClass C (h ≫ sX)
        (pullback.fst i h ≫ sZ) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) r := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun t _ k α => ?_
  refine (bivariantRestrictionOfInvertible_cap C sZ sX i hZ h (r : ℤ) _ t k α).trans ?_
  refine Eq.trans ?_ ((Comparison.ofBaseChange (IsPullback.of_hasPullback i h).flip
    𝒩).virtualNormalClass_cap C sX sZ hZ r t k α).symm
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (restrictionTestIso_eq h t).symm _ _ _ _

end Restriction

end Stacks.Chow.VirtualNormalBundle

end
