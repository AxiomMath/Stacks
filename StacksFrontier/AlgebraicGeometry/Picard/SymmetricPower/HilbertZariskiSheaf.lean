module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorZariskiGluing
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.HilbertPresheaf
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.IdealSheafGlue
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# The Hilbert functor of points is a Zariski sheaf

Let `X` be a scheme over `S`. Degree-`d` Hilbert families in `X` glue along open covers of the
base: given an open cover `{T_i ⟶ T}` of an `S`-scheme and families over the `T_i` agreeing on
overlaps, there is a family over `T` restricting to them. Together with the separatedness
clause already proved (`Stacks.Hilbert.hilbertFamily_ext_of_baseChange_eq`) this says the Hilbert
functor satisfies the sheaf property for the Zariski topology, the Zariski case of Stacks
Tag 0B95, which is condition (1) of the representability criterion of Stacks Tag 01JJ used in
the proofs of Stacks Tags 0B99 and 0B9A.

## Main results

* `Stacks.Hilbert.exists_baseChange_eq_of_openCover`: families over an open cover agreeing on
  overlaps glue.
* `Stacks.Hilbert.isSheaf_hilbPresheaf`: the Hilbert presheaf is a sheaf for the Zariski topology
  on schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}} (X : Over S) {d : ℕ}

/-- A property of morphisms respecting isomorphisms, satisfied by one side of a cartesian
square, is satisfied by the chosen pullback. -/
theorem _root_.CategoryTheory.MorphismProperty.pullback_snd_of_isPullback
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {A B C D : Scheme.{u}} {a : A ⟶ B}
    {b : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D} (h : IsPullback a b f g) (hb : P b) :
    P (pullback.snd f g) := by
  have e : h.isoPullback.inv ≫ b = pullback.snd f g := h.isoPullback_inv_snd
  rw [← e]
  exact (P.cancel_left_of_respectsIso _ _).mpr hb

/-- **Hilbert families glue along open covers of the base.** -/
theorem exists_baseChange_eq_of_openCover {T : Over S} {ι : Type*} {U : ι → Over S}
    (π : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (π i).left]
    (hcov : ∀ t : T.left, ∃ i, ∃ u : (U i).left, (π i).left u = t)
    (Z : ∀ i, HilbertFamily X (U i) d)
    (hZ : ∀ i j (P : Over S) (a : P ⟶ U i) (b : P ⟶ U j), a ≫ π i = b ≫ π j →
      baseChange X a (Z i) = baseChange X b (Z j)) :
    ∃ W : HilbertFamily X T d, ∀ i, baseChange X (π i) W = Z i := by
  let Y := ((Over.pullback T.hom).obj X).left
  let pr : Y ⟶ T.left := ((Over.pullback T.hom).obj X).hom
  let g : ∀ i, ((Over.pullback (U i).hom).obj X).left ⟶ Y := fun i ↦ familyBaseChangeMap X (π i)
  have hcovY : ∀ y : Y, ∃ i, y ∈ (g i).opensRange := by
    intro y
    obtain ⟨i, u, hu⟩ := hcov (pr y)
    obtain ⟨v, hv⟩ := exists_preimage_of_isPullback (isPullback_familyBaseChangeMap X (π i)) y u
      hu.symm
    exact ⟨i, v, hv⟩
  -- the overlap of two members of the cover, as an `S`-scheme
  let P : ι → ι → Over S := fun i j ↦
    Over.mk (pullback.fst (π i).left (π j).left ≫ (U i).hom)
  let a : ∀ i j, P i j ⟶ U i := fun i j ↦ Over.homMk (pullback.fst (π i).left (π j).left) rfl
  let b : ∀ i j, P i j ⟶ U j := fun i j ↦ Over.homMk (pullback.snd (π i).left (π j).left) (by
    change pullback.snd (π i).left (π j).left ≫ (U j).hom =
      pullback.fst (π i).left (π j).left ≫ (U i).hom
    rw [← Over.w (π i), ← Over.w (π j), ← Category.assoc, ← Category.assoc, pullback.condition])
  have hab : ∀ i j, a i j ≫ π i = b i j ≫ π j := fun i j ↦ by
    ext
    exact pullback.condition
  have hcompat : ∀ i k (V : Y.affineOpens) (hi : (V : Y.Opens) ≤ (g i).opensRange)
      (hk : (V : Y.Opens) ≤ (g k).opensRange),
      Scheme.IdealSheafData.localIdeal (g i) (Z i).ideal V hi =
        Scheme.IdealSheafData.localIdeal (g k) (Z k).ideal V hk := by
    intro i k V hi hk
    have : IsOpenImmersion (a i k).left :=
      inferInstanceAs (IsOpenImmersion (pullback.fst (π i).left (π k).left))
    have : IsOpenImmersion (b i k).left :=
      inferInstanceAs (IsOpenImmersion (pullback.snd (π i).left (π k).left))
    refine Scheme.IdealSheafData.localIdeal_eq_of_comap_eq (g i) (g k)
      (familyBaseChangeMap X (a i k)) (familyBaseChangeMap X (b i k)) ?_ ?_ _ _ ?_ V hi hk
    · simp only [g]
      rw [← familyBaseChangeMap_comp, ← familyBaseChangeMap_comp, hab]
    · rintro y ⟨v, rfl⟩ ⟨w, hw⟩
      have e : (π i).left (((Over.pullback (U i).hom).obj X).hom v) =
          (π k).left (((Over.pullback (U k).hom).obj X).hom w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
          ← (isPullback_familyBaseChangeMap X (π i)).w,
          ← (isPullback_familyBaseChangeMap X (π k)).w, Scheme.Hom.comp_apply,
          Scheme.Hom.comp_apply]
        exact congrArg pr hw.symm
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
      obtain ⟨q, hq⟩ := exists_preimage_of_isPullback
        (isPullback_familyBaseChangeMap X (a i k ≫ π i)) (g i v) z (by
          change pr (g i v) = (pullback.fst (π i).left (π k).left ≫ (π i).left) z
          rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
            (isPullback_familyBaseChangeMap X (π i)).w])
      refine ⟨q, ?_⟩
      rw [← hq, familyBaseChangeMap_comp]
    · have := congrArg HilbertFamily.ideal (hZ i k (P i k) (a i k) (b i k) (hab i k))
      simpa only [baseChange_ideal] using this
  let K := Scheme.IdealSheafData.glue g (fun i ↦ (Z i).ideal) hcompat hcovY
  have hK : ∀ i, K.comap (g i) = (Z i).ideal :=
    Scheme.IdealSheafData.comap_glue g _ hcompat hcovY
  refine ⟨⟨K, ?_⟩, fun i ↦ HilbertFamily.ext (by rw [baseChange_ideal]; exact hK i)⟩
  -- finite local freeness is local on the base
  let 𝒰 : T.left.OpenCover := Scheme.Cover.mkOfCovers ι (fun i ↦ (U i).left) (fun i ↦ (π i).left)
    hcov
  have key : ∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d
      (𝒰.pullbackHom (K.subschemeι ≫ pr) i) := by
    intro i
    have hsq := isPullback_familyBaseChangeMap_subschemeι X (π i) K
    have hZi := (Z i).isFiniteLocallyFreeOfRank
    rw [← hK i] at hZi
    exact MorphismProperty.pullback_snd_of_isPullback hsq hZi
  exact IsZariskiLocalAtTarget.of_openCover
    (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d) 𝒰 key

/-- The base change map of `X` along a morphism of `S`-schemes depends only on the underlying
morphism of schemes. -/
theorem familyBaseChangeMap_congr {T₁ T₂ : Over S} (g g' : T₁ ⟶ T₂) (h : g.left = g'.left) :
    familyBaseChangeMap X g = familyBaseChangeMap X g' := by
  congr 1
  exact Over.OverMorphism.ext h

/-- Pulling back an ideal sheaf on `X ×_S C` along the base change maps for `g₂` and then `g₁`
is pulling it back along the base change map for `g₁ ≫ g₂`. -/
theorem comap_comap_familyBaseChangeMap {A B C : Over S}
    (I : ((Over.pullback C.hom).obj X).left.IdealSheafData) (g₁ : A ⟶ B) (g₂ : B ⟶ C) :
    (I.comap (familyBaseChangeMap X g₂)).comap (familyBaseChangeMap X g₁) =
      I.comap (familyBaseChangeMap X (g₁ ≫ g₂)) := by
  rw [familyBaseChangeMap_comp, Scheme.IdealSheafData.comap_comp]

/-- **The Hilbert presheaf satisfies the sheaf condition for an open cover.** -/
theorem isSheafFor_hilbPresheaf {T : Scheme.{u}} {ι : Type*} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ T) [hf : ∀ i, IsOpenImmersion (f i)] (hcov : ∀ t, ∃ i, t ∈ Set.range (f i)) :
    Presieve.IsSheafFor (hilbPresheaf X d) (Presieve.ofArrows Y f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers ι Y f hcov
  have hx1 : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (x i).1 = pullback.snd _ _ ≫ (x j).1 :=
    fun i j ↦ congrArg Sigma.fst (hx i j _ (pullback.fst (f i) (f j)) (pullback.snd (f i) (f j))
      pullback.condition)
  let s : T ⟶ S := 𝒰.glueMorphisms (fun i ↦ (x i).1) hx1
  have hs : ∀ i, f i ≫ s = (x i).1 := fun i ↦ 𝒰.ι_glueMorphisms _ hx1 i
  let U : ι → Over S := fun i ↦ Over.mk (f i ≫ s)
  let π : ∀ i, U i ⟶ Over.mk s := fun i ↦ Over.homMk (f i) rfl
  have : ∀ i, IsOpenImmersion (π i).left := fun i ↦ hf i
  let Z : ∀ i, HilbertFamily X (U i) d := fun i ↦
    familyPullback X d (𝟙 _) (by rw [Category.id_comp]; exact (hs i).symm) (x i).2
  have hZ : ∀ i j (P : Over S) (a : P ⟶ U i) (b : P ⟶ U j), a ≫ π i = b ≫ π j →
      baseChange X a (Z i) = baseChange X b (Z j) := by
    intro i j P a b hab
    have hab' : a.left ≫ f i = b.left ≫ f j := congrArg CommaMorphism.left hab
    have h := hx i j P.left a.left b.left hab'
    change (⟨a.left ≫ (x i).1, familyPullback X d a.left rfl (x i).2⟩ : HilbSections X d P.left) =
      ⟨b.left ≫ (x j).1, familyPullback X d b.left rfl (x j).2⟩ at h
    obtain ⟨e, h⟩ := (sigma_eq_iff X d _ _).mp h
    refine HilbertFamily.ext ?_
    rw [baseChange_ideal, baseChange_ideal]
    change ((x i).2.ideal.comap _).comap _ = ((x j).2.ideal.comap _).comap _
    rw [comap_comap_familyBaseChangeMap, comap_comap_familyBaseChangeMap]
    rw [familyPullback_ideal, familyPullback_ideal, comap_comap_familyBaseChangeMap] at h
    have h' := congrArg (Scheme.IdealSheafData.comap · (familyBaseChangeMap X
      (Over.homMk (𝟙 P.left) (by
        change 𝟙 P.left ≫ b.left ≫ (x j).1 = P.hom
        rw [Category.id_comp, ← hs j]
        exact Over.w b) : P ⟶ Over.mk (b.left ≫ (x j).1)))) h
    simp only [comap_comap_familyBaseChangeMap] at h'
    convert h'.symm using 2 <;> apply familyBaseChangeMap_congr <;> simp
  obtain ⟨W, hW⟩ := exists_baseChange_eq_of_openCover X π hcov Z hZ
  have hamalg : ∀ i, (hilbPresheaf X d).map (f i).op ⟨s, W⟩ = x i := by
    intro i
    change (⟨f i ≫ s, baseChange X (π i) W⟩ : HilbSections X d (Y i)) = ⟨(x i).1, (x i).2⟩
    rw [hW i, sigma_eq_iff]
    refine ⟨hs i, ?_⟩
    change _ = ((x i).2.ideal.comap _).comap _
    rw [comap_comap_familyBaseChangeMap, familyBaseChangeMap_congr X _ (𝟙 _) (by simp),
      familyBaseChangeMap_id, Scheme.IdealSheafData.comap_id]
  refine ⟨⟨s, W⟩, hamalg, ?_⟩
  rintro ⟨s', W'⟩ ht
  have hs' : s' = s := 𝒰.hom_ext _ _ fun i ↦ by
    change f i ≫ s' = f i ≫ s
    rw [hs i]
    exact congrArg Sigma.fst (ht i)
  subst hs'
  congr 1
  refine hilbertFamily_ext_of_baseChange_eq X π (fun i ↦ inferInstanceAs (Flat (f i)))
    hcov fun i ↦ ?_
  have h := (ht i).trans (hamalg i).symm
  change (⟨f i ≫ _, baseChange X (π i) W'⟩ : HilbSections X d (Y i)) =
    ⟨f i ≫ _, baseChange X (π i) W⟩ at h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2


/-- **The Hilbert presheaf is a Zariski sheaf**: the Zariski case of the sheaf property of
Stacks Tag 0B95, condition (1) of the representability criterion of Stacks Tag 01JJ. -/
theorem isSheaf_hilbPresheaf (d : ℕ) :
    Presheaf.IsSheaf Scheme.zariskiTopology (hilbPresheaf X d) := by
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro T R hR
  obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
  rw [PreZeroHypercover.presieve₀, Scheme.ofArrows_mem_precoverage_iff] at hR
  have := hR.2
  exact isSheafFor_hilbPresheaf X E.f hR.1

/-- The Hilbert presheaf as a sheaf for the Zariski topology. -/
def hilbSheaf (d : ℕ) : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
  ⟨hilbPresheaf X d, isSheaf_hilbPresheaf X d⟩

end Stacks.Hilbert

end
