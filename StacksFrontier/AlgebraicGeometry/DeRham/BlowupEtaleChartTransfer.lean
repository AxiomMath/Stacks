module

public import StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateExceptionalBundle
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
import all StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre

/-!
# Étale charts of a blowup with smooth centre over the coordinate model

Let `S` be a scheme and let `i : Z ⟶ X` be a closed immersion of schemes smooth over `S`, with
blowup `b : X' ⟶ X` along `Z`.  The proofs of [Stacks, Tags 0FUU and 0G5J] work étale locally on
`X`: by [Stacks, Tag 0FUE] every point of `Z` has an open neighbourhood `U` with an étale
morphism `U ⟶ 𝐀^{m+n}` under which `Z ∩ U` is the inverse image of the coordinate subspace
`𝐀^m`, and blowing up commutes with flat base change ([Stacks, Tag 0805]), so over `U` the blowup
is the base change of the standard coordinate blowup of Section 0FUB.

This file packages that reduction once, for every consumer, in the coordinate model of
`StacksFrontier/AlgebraicGeometry/DeRham/BlowupDifferentialFormsComparison.lean`:
`coordinateAmbient R m n = Spec R[x₁, …, x_m, y₁, …, y_n]`, its blowup `coordinateBlowup R m n`
along the coordinate ideal, and the exceptional ideal `coordinateExceptional R m n`.

## Main definitions

* `Stacks.DeRham.BlowupEtaleChart f i`:  an **étale chart** of the pair `(X, Z)` over the
  coordinate model.  It is an open `U ⊆ X`, a ring `R` with an open immersion `Spec R ⟶ S`, and
  an étale `g : U ⟶ coordinateAmbient R m n` over `S` under which the ideal sheaf of `Z`
  restricted to `U` is the inverse image of the coordinate ideal.
* `Stacks.DeRham.BlowupEtaleChart.blowupMap`:  the induced morphism `b⁻¹(U) ⟶ coordinateBlowup`.

## Main results

* `Stacks.DeRham.exists_blowupEtaleChart`:  **[Stacks, Tag 0FUE] in the coordinate model**;
  every point of `Z` has étale charts inside every neighbourhood.
* `Stacks.DeRham.BlowupEtaleChart.isPullback_blowupMap`:  **[Stacks, Tag 0805] on a chart**;
  the square formed by `b⁻¹(U) ⟶ U`, `blowupMap`, `g` and the coordinate blowup is cartesian.
* `Stacks.DeRham.BlowupEtaleChart.comap_exceptionalIdeal`:  on a chart the exceptional ideal
  of `b` is the inverse image of the coordinate exceptional ideal.
* `Stacks.DeRham.BlowupEtaleChart.one_le_n`:  if `Z` has empty interior in `X`, every chart
  through a point has `n ≥ 1`.

## Implementation notes

The chart takes its values in `coordinateAmbient R m n` over an affine open `Spec R ⊆ S`, rather
than in relative affine space `𝐀^{m+n}_S` as [Stacks, Tag 0FUE] does, because that is where the
coordinate statements of Section 0FUB live.  The passage is made by restricting the chart of
`Stacks.AlgebraicGeometry` `.exists_etale_coordinateSubspaceEmbedding_isPullback` over an affine
open of `S` and composing with the identification of `𝐀^{m+n}` over an affine base with the
spectrum of a polynomial ring, which `StacksFrontier/AlgebraicGeometry/Blowup/SmoothCentre.lean`
records privately; that module is imported with `import all` for it.

The morphism `blowupMap` is chosen once and for all; the exceptional ideal identification holds
for any morphism making the square commute, and is proved from that alone.

## References

* [Stacks Project, Tag 0FUE](https://stacks.math.columbia.edu/tag/0FUE)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DeRham

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)

/-- An **étale chart** of a closed immersion `i : Z ⟶ X` over a scheme `S`, valued in the
coordinate model of Section 0FUB: an open `U ⊆ X`, a ring `R` whose spectrum is an open of `S`,
and an étale morphism `g : U ⟶ 𝐀^{m+n}_R = coordinateAmbient R m n` over `S` under which the
ideal sheaf of `Z` restricted to `U` is the inverse image of the ideal of the coordinate subspace
`𝐀^m_R`. -/
structure BlowupEtaleChart where
  /-- The coefficient ring; its spectrum is an affine open of `S`. -/
  R : Type u
  [commRing : CommRing R]
  /-- The dimension of the coordinate subspace. -/
  m : ℕ
  /-- The codimension of the coordinate subspace. -/
  n : ℕ
  /-- The open of `X` the chart lives on. -/
  U : X.Opens
  /-- The étale coordinate map. -/
  g : U.toScheme ⟶ coordinateAmbient R m n
  [etale : Etale g]
  /-- The open immersion of `Spec R` into `S`. -/
  base : Spec (.of R) ⟶ S
  [isOpenImmersion_base : IsOpenImmersion base]
  /-- The chart is a morphism over `S`. -/
  comm : g ≫ coordinateAmbientToBase R m n ≫ base = U.ι ≫ f
  /-- The ideal sheaf of `Z` on `U` is the inverse image of the coordinate ideal. -/
  ker_comap : i.ker.comap U.ι = (Stacks.MoreMorphisms.coordinateIdeal R m n).comap g

attribute [instance] BlowupEtaleChart.commRing BlowupEtaleChart.etale
  BlowupEtaleChart.isOpenImmersion_base

namespace BlowupEtaleChart

variable {f i} (c : BlowupEtaleChart f i)

/-- On a chart, the blowup of `X` along `Z`, restricted over `U`, is the base change of the
coordinate blowup along the chart map: the existence half of `isPullback_blowupMap`. -/
theorem exists_isPullback :
    ∃ h : (blowUpToBase i.ker ⁻¹ᵁ c.U).toScheme ⟶ coordinateBlowup c.R c.m c.n,
      IsPullback (blowUpToBase i.ker ∣_ c.U) h c.g (coordinateBlowupToAmbient c.R c.m c.n) := by
  obtain ⟨h₂, hsq₂⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap c.g
    (Stacks.MoreMorphisms.coordinateIdeal c.R c.m c.n)
  obtain ⟨h₁, hsq₁⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap c.U.ι i.ker
  revert h₁ hsq₁
  rw [c.ker_comap]
  intro h₁ hsq₁
  let e := hsq₁.isoIsPullback _ _ (AlgebraicGeometry.isPullback_morphismRestrict
    (blowUpToBase i.ker) c.U)
  refine ⟨e.inv ≫ h₂, IsPullback.of_iso hsq₂ e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_⟩
  · simp [e]
  · simp
  · simp
  · simp

/-- The morphism from the part of the blowup over a chart to the coordinate blowup, making the
square `isPullback_blowupMap` cartesian. -/
def blowupMap : (blowUpToBase i.ker ⁻¹ᵁ c.U).toScheme ⟶ coordinateBlowup c.R c.m c.n :=
  c.exists_isPullback.choose

/-- **[Stacks, Tag 0805] on an étale chart.**  The square
```
b⁻¹(U) --blowupMap--> coordinateBlowup
  |b|_U                     |b
  U --------g--------> coordinateAmbient
```
is cartesian. -/
theorem isPullback_blowupMap :
    IsPullback (blowUpToBase i.ker ∣_ c.U) c.blowupMap c.g
      (coordinateBlowupToAmbient c.R c.m c.n) :=
  c.exists_isPullback.choose_spec

/-- The chart square commutes. -/
@[reassoc]
theorem blowupMap_comm :
    (blowUpToBase i.ker ∣_ c.U) ≫ c.g = c.blowupMap ≫ coordinateBlowupToAmbient c.R c.m c.n :=
  c.isPullback_blowupMap.w

/-- The morphism `blowupMap` is étale, as a base change of the étale chart map. -/
instance etale_blowupMap : Etale c.blowupMap :=
  MorphismProperty.of_isPullback (P := @Etale) c.isPullback_blowupMap c.etale

/-- **The exceptional ideal on a chart.**  Over a chart, the exceptional ideal of the blowup of
`X` along `Z` is the inverse image of the exceptional ideal of the coordinate blowup.  This uses
only the commutativity of the chart square. -/
theorem comap_exceptionalIdeal :
    (exceptionalIdeal i.ker).comap (blowUpToBase i.ker ⁻¹ᵁ c.U).ι =
      (coordinateExceptional c.R c.m c.n).comap c.blowupMap := by
  change (i.ker.comap (blowUpToBase i.ker)).comap _ =
    ((Stacks.MoreMorphisms.coordinateIdeal c.R c.m c.n).comap
      (coordinateBlowupToAmbient c.R c.m c.n)).comap c.blowupMap
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp, c.ker_comap,
    ← Scheme.IdealSheafData.comap_comp, c.blowupMap_comm]

/-- For `n = 0` the coordinate projection is bijective. -/
theorem _root_.Stacks.MoreMorphisms.coordinateProjection_bijective_zero (R : Type u) [CommRing R]
    (m : ℕ) : Function.Bijective (Stacks.MoreMorphisms.coordinateProjection R m 0) := by
  refine ⟨fun p q hpq => ?_, Stacks.MoreMorphisms.coordinateProjection_surjective R m 0⟩
  have hid : (MvPolynomial.rename (R := R) (Sum.inl : Fin m → Fin m ⊕ Fin 0)).toRingHom.comp
      (Stacks.MoreMorphisms.coordinateProjection R m 0) = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp [Stacks.MoreMorphisms.coordinateProjection]
    · rcases k with k | k
      · simp [Stacks.MoreMorphisms.coordinateProjection]
      · exact k.elim0
  have h := RingHom.congr_fun hid
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [← h p, ← h q, hpq]

/-- For `n = 0` the coordinate ideal is zero: the coordinate subspace is everything. -/
theorem _root_.Stacks.MoreMorphisms.coordinateIdeal_zero (R : Type u) [CommRing R] (m : ℕ) :
    Stacks.MoreMorphisms.coordinateIdeal R m 0 = ⊥ := by
  have : IsIso (Stacks.MoreMorphisms.coordinateEmbedding R m 0) := by
    let e := RingEquiv.ofBijective _ (Stacks.MoreMorphisms.coordinateProjection_bijective_zero R m)
    exact inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  exact Scheme.Hom.ker_eq_bot_of_isIso _

/-- For `n = 0` the inverse image of the coordinate ideal along any morphism is zero. -/
theorem _root_.Stacks.MoreMorphisms.comap_coordinateIdeal_eq_bot {R : Type u} [CommRing R]
    {m n : ℕ} (hn : n = 0) {Y : Scheme.{u}} (g : Y ⟶ coordinateAmbient R m n) :
    (Stacks.MoreMorphisms.coordinateIdeal R m n).comap g = ⊥ := by
  subst hn
  rw [Stacks.MoreMorphisms.coordinateIdeal_zero, Scheme.IdealSheafData.comap_bot]

/-- If `Z` has empty interior in `X`, a chart through a point has positive codimension `n ≥ 1`:
for `n = 0` the coordinate ideal is zero, so `Z` would contain the nonempty open `U`. -/
theorem one_le_n [IsClosedImmersion i] (hint : interior (Set.range i.base) = ∅) {x : X}
    (hx : x ∈ c.U) : 1 ≤ c.n := by
  by_contra h0
  have hn : c.n = 0 := by omega
  have hsub : (c.U : Set X) ⊆ Set.range i.base := by
    intro y hy
    have hbot : i.ker.comap c.U.ι = ⊥ :=
      c.ker_comap.trans (Stacks.MoreMorphisms.comap_coordinateIdeal_eq_bot hn c.g)
    have hs := congrArg (fun J => (J.support : Set c.U.toScheme)) hbot
    simp only [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_bot] at hs
    have hy' : (⟨y, hy⟩ : c.U.toScheme) ∈ ((⊤ : TopologicalSpace.Closeds c.U.toScheme) :
        Set c.U.toScheme) := trivial
    rw [← hs] at hy'
    have hmem : y ∈ (i.ker.support : Set X) := hy'
    rwa [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq] at hmem
  have : x ∈ interior (Set.range i.base) :=
    mem_interior.mpr ⟨c.U, hsub, c.U.isOpen, hx⟩
  rw [hint] at this
  exact this

/-! ### Differential forms on a chart -/

section Forms

open Scheme.Hom

/-- The chart is a morphism over the base on the blowup side as well: the part of the blowup over
`U` maps to `S` through the coordinate blowup and `Spec R`. -/
theorem blowup_comm :
    (blowUpToBase i.ker ⁻¹ᵁ c.U).ι ≫ blowUpToBase i.ker ≫ f =
      (c.blowupMap ≫ coordinateBlowupToBase c.R c.m c.n) ≫ c.base := by
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc, ← c.comm, Category.assoc,
    ← Category.assoc (blowUpToBase i.ker ∣_ c.U), c.blowupMap_comm]
  simp only [coordinateBlowupToBase, Category.assoc]

/-- The forms map of a square depends on its upper edge only through that morphism: equal upper
edges give maps that differ by the transport `Scheme.Modules.pullbackCongr`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_congr_left
    {X' X S' S : Scheme.{u}} {f₁ f₂ : X' ⟶ X} (h : f₁ = f₂) (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) (h₁ : f₁ ≫ p = p' ≫ g) (h₂ : f₂ ≫ p = p' ≫ g) (n : ℤ) :
    relativeDifferentialFormsMap f₁ p p' g h₁ n =
      (Scheme.Modules.pullbackCongr h).hom.app _ ≫ relativeDifferentialFormsMap f₂ p p' g h₂ n := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- The forms map of a composite square factors through the two maps of a commuting square of
schemes: the common shape of `restrict_blowupFormsMap` and `chart_blowupFormsMap`. -/
private theorem pullback_map_formsMap_comp {A A' B B' S₀ T : Scheme.{u}} (b : A' ⟶ A)
    (w : B' ⟶ A') (v : B ⟶ A) (b' : B' ⟶ B) (p : A ⟶ S₀) (p' : A' ⟶ S₀) (pB : B ⟶ T)
    (pB' : B' ⟶ T) (q : T ⟶ S₀) (hb : b ≫ p = p' ≫ 𝟙 S₀) (hw : w ≫ b = b' ≫ v)
    (hv : v ≫ p = pB ≫ q) (hB : b' ≫ pB = pB' ≫ 𝟙 T) (hw' : w ≫ p' = pB' ≫ q) (a : ℤ) :
    (Scheme.Modules.pullback w).map (relativeDifferentialFormsMap b p p' (𝟙 S₀) hb a) ≫
        relativeDifferentialFormsMap w p' pB' q hw' a =
      (Scheme.Modules.pullbackComp w b).hom.app _ ≫
        (Scheme.Modules.pullbackCongr hw).hom.app _ ≫
        (Scheme.Modules.pullbackComp b' v).inv.app _ ≫
        (Scheme.Modules.pullback b').map (relativeDifferentialFormsMap v p pB q hv a) ≫
        relativeDifferentialFormsMap b' pB pB' (𝟙 T) hB a := by
  have h₀ : (w ≫ b) ≫ p = pB' ≫ q := by rw [Category.assoc, hb, Category.comp_id, hw']
  have h₀' : (b' ≫ v) ≫ p = pB' ≫ q := by
    rw [Category.assoc, hv, ← Category.assoc, hB, Category.comp_id]
  have h₁ := relativeDifferentialFormsMap_comp b w p p' pB' (𝟙 S₀) q q hb hw' h₀ a
  have h₂ := relativeDifferentialFormsMap_comp v b' p pB pB' q (𝟙 T) q hv hB h₀' a
  have h₃ := relativeDifferentialFormsMap_congr_left hw p pB' q h₀ h₀' a
  exact (Iso.hom_inv_id_app_assoc (Scheme.Modules.pullbackComp w b)
    (relativeDifferentialForms p a) _).symm.trans
    (congrArg _ (h₁.symm.trans (h₃.trans (congrArg _ h₂))))

/-- On the ambient side of a chart, the restriction of `Ω^a_{X/S}` to `U` maps to the forms of
`U` relative to `Spec R`: the forms map of the square `U ⟶ X` over `Spec R ⟶ S`.  It is an
isomorphism, both horizontal edges being open immersions. -/
noncomputable abbrev ambientFormsRestrict (a : ℤ) :
    (Scheme.Modules.pullback c.U.ι).obj (relativeDifferentialForms f a) ⟶
      relativeDifferentialForms (c.g ≫ coordinateAmbientToBase c.R c.m c.n) a :=
  relativeDifferentialFormsMap c.U.ι f (c.g ≫ coordinateAmbientToBase c.R c.m c.n) c.base
    (by rw [Category.assoc, c.comm]) a

/-- On the ambient side of a chart, the pullback of the forms of the coordinate model maps to the
forms of `U` relative to `Spec R`: the forms map of the étale chart map.  It is an isomorphism. -/
noncomputable abbrev ambientFormsChart (a : ℤ) :
    (Scheme.Modules.pullback c.g).obj
        (relativeDifferentialForms (coordinateAmbientToBase c.R c.m c.n) a) ⟶
      relativeDifferentialForms (c.g ≫ coordinateAmbientToBase c.R c.m c.n) a :=
  relativeDifferentialFormsMap c.g (coordinateAmbientToBase c.R c.m c.n)
    (c.g ≫ coordinateAmbientToBase c.R c.m c.n) (𝟙 _) (by simp) a

/-- On the blowup side of a chart, the restriction of `Ω^a_{X'/S}` to `b⁻¹(U)` maps to the forms
of `b⁻¹(U)` relative to `Spec R`.  It is an isomorphism. -/
noncomputable abbrev blowupFormsRestrict (a : ℤ) :
    (Scheme.Modules.pullback (blowUpToBase i.ker ⁻¹ᵁ c.U).ι).obj
        (relativeDifferentialForms (blowUpToBase i.ker ≫ f) a) ⟶
      relativeDifferentialForms (c.blowupMap ≫ coordinateBlowupToBase c.R c.m c.n) a :=
  relativeDifferentialFormsMap (blowUpToBase i.ker ⁻¹ᵁ c.U).ι (blowUpToBase i.ker ≫ f)
    (c.blowupMap ≫ coordinateBlowupToBase c.R c.m c.n) c.base c.blowup_comm a

/-- On the blowup side of a chart, the pullback of the forms of the coordinate blowup maps to the
forms of `b⁻¹(U)` relative to `Spec R`.  It is an isomorphism. -/
noncomputable abbrev blowupFormsChart (a : ℤ) :
    (Scheme.Modules.pullback c.blowupMap).obj
        (relativeDifferentialForms (coordinateBlowupToBase c.R c.m c.n) a) ⟶
      relativeDifferentialForms (c.blowupMap ≫ coordinateBlowupToBase c.R c.m c.n) a :=
  relativeDifferentialFormsMap c.blowupMap (coordinateBlowupToBase c.R c.m c.n)
    (c.blowupMap ≫ coordinateBlowupToBase c.R c.m c.n) (𝟙 _) (by simp) a

/-- The restriction map `ambientFormsRestrict` on forms of the ambient side is an isomorphism. -/
instance isIso_ambientFormsRestrict (a : ℤ) : IsIso (c.ambientFormsRestrict a) :=
  isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ a

/-- The chart map `ambientFormsChart` on the forms of the ambient side is an isomorphism. -/
instance isIso_ambientFormsChart (a : ℤ) : IsIso (c.ambientFormsChart a) :=
  isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ a

/-- The restriction map `blowupFormsRestrict` on the forms of the blowup side is an isomorphism. -/
instance isIso_blowupFormsRestrict (a : ℤ) : IsIso (c.blowupFormsRestrict a) :=
  isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ a

/-- The chart map `blowupFormsChart` on the forms of the blowup side is an isomorphism. -/
instance isIso_blowupFormsChart (a : ℤ) : IsIso (c.blowupFormsChart a) :=
  isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ a

/-- **The forms isomorphism on the ambient side of a chart**:
`Ω^a_{X/S}|_U ≅ g^*Ω^a_{𝐀^{m+n}_R/R}`. -/
noncomputable def ambientFormsIso (a : ℤ) :
    (Scheme.Modules.pullback c.U.ι).obj (relativeDifferentialForms f a) ≅
      (Scheme.Modules.pullback c.g).obj
        (relativeDifferentialForms (coordinateAmbientToBase c.R c.m c.n) a) :=
  asIso (c.ambientFormsRestrict a) ≪≫ (asIso (c.ambientFormsChart a)).symm

/-- **The forms isomorphism on the blowup side of a chart**:
`Ω^a_{X'/S}|_{b⁻¹(U)} ≅ (blowupMap)^*Ω^a_{L/R}`, with `L` the coordinate blowup. -/
noncomputable def blowupFormsIso (a : ℤ) :
    (Scheme.Modules.pullback (blowUpToBase i.ker ⁻¹ᵁ c.U).ι).obj
        (relativeDifferentialForms (blowUpToBase i.ker ≫ f) a) ≅
      (Scheme.Modules.pullback c.blowupMap).obj
        (relativeDifferentialForms (coordinateBlowupToBase c.R c.m c.n) a) :=
  asIso (c.blowupFormsRestrict a) ≪≫ (asIso (c.blowupFormsChart a)).symm

/-- The common model of the first canonical map on a chart: the forms map
`b|_U^*Ω^a_{U/R} ⟶ Ω^a_{b⁻¹(U)/R}` of the blowup restricted over `U`, relative to `Spec R`. -/
noncomputable abbrev chartFormsMap (a : ℤ) :
    (Scheme.Modules.pullback (blowUpToBase i.ker ∣_ c.U)).obj
        (relativeDifferentialForms (c.g ≫ coordinateAmbientToBase c.R c.m c.n) a) ⟶
      relativeDifferentialForms (c.blowupMap ≫ coordinateBlowupToBase c.R c.m c.n) a :=
  relativeDifferentialFormsMap (blowUpToBase i.ker ∣_ c.U)
    (c.g ≫ coordinateAmbientToBase c.R c.m c.n)
    (c.blowupMap ≫ coordinateBlowupToBase c.R c.m c.n) (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc, c.blowupMap_comm]; simp) a

/-- **The first canonical map `b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S}`, restricted over a chart**, is the
common model `chartFormsMap` up to the restriction isomorphisms on either side: read in
`Ω^a_{b⁻¹(U)/R}`, it is the coherence isomorphism
`(b⁻¹(U) ⟶ X')^* b^* ≅ (b|_U)^* (U ⟶ X)^*`, followed by `(b|_U)^*` of `ambientFormsRestrict`,
followed by `chartFormsMap`. -/
theorem restrict_blowupFormsMap (a : ℤ) :
    (Scheme.Modules.pullback (blowUpToBase i.ker ⁻¹ᵁ c.U).ι).map
        (relativeDifferentialFormsMap (blowUpToBase i.ker) f (blowUpToBase i.ker ≫ f) (𝟙 S)
          (by simp) a) ≫ c.blowupFormsRestrict a =
      (Scheme.Modules.pullbackComp (blowUpToBase i.ker ⁻¹ᵁ c.U).ι (blowUpToBase i.ker)).hom.app _ ≫
        (Scheme.Modules.pullbackCongr (morphismRestrict_ι (blowUpToBase i.ker) c.U).symm).hom.app
          _ ≫
        (Scheme.Modules.pullbackComp (blowUpToBase i.ker ∣_ c.U) c.U.ι).inv.app _ ≫
        (Scheme.Modules.pullback (blowUpToBase i.ker ∣_ c.U)).map (c.ambientFormsRestrict a) ≫
        c.chartFormsMap a := by
  exact pullback_map_formsMap_comp _ _ _ _ _ _ _ _ _ _ (morphismRestrict_ι _ _).symm _ _ _ a

/-- **The first canonical map `b_L^*Ω^a ⟶ Ω^a_L` of the coordinate blowup, pulled back along a
chart**, is the common model `chartFormsMap` up to the chart isomorphisms on either side: read
in `Ω^a_{b⁻¹(U)/R}`, it is the coherence isomorphism
`(blowupMap)^* b_L^* ≅ (b|_U)^* g^*`, followed by `(b|_U)^*` of `ambientFormsChart`, followed
by `chartFormsMap`. -/
theorem chart_blowupFormsMap (a : ℤ) :
    (Scheme.Modules.pullback c.blowupMap).map
        (relativeDifferentialFormsMap (coordinateBlowupToAmbient c.R c.m c.n)
          (coordinateAmbientToBase c.R c.m c.n) (coordinateBlowupToBase c.R c.m c.n)
          (𝟙 _) (by simp) a) ≫ c.blowupFormsChart a =
      (Scheme.Modules.pullbackComp c.blowupMap (coordinateBlowupToAmbient c.R c.m c.n)).hom.app
          _ ≫
        (Scheme.Modules.pullbackCongr c.blowupMap_comm.symm).hom.app _ ≫
        (Scheme.Modules.pullbackComp (blowUpToBase i.ker ∣_ c.U) c.g).inv.app _ ≫
        (Scheme.Modules.pullback (blowUpToBase i.ker ∣_ c.U)).map (c.ambientFormsChart a) ≫
        c.chartFormsMap a := by
  exact pullback_map_formsMap_comp _ _ _ _ _ _ _ _ _ _ c.blowupMap_comm.symm _ _ _ a

end Forms

/-! ### The centre and the exceptional divisor on a chart -/

section Subschemes

attribute [local instance] Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion

variable [IsClosedImmersion i]

/-- **The centre of a chart over the coordinate centre**: the morphism `Z ∩ U ⟶ 𝐀^m_R` induced
by the chart map.  It makes `isPullback_centreMap` cartesian. -/
noncomputable def centreMap :
    (i ⁻¹ᵁ c.U).toScheme ⟶ coordinateBlowupCentre c.R c.m :=
  IsClosedImmersion.lift (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n)
    ((i ∣_ c.U) ≫ c.g)
    (by
      rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le,
        AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
          (AlgebraicGeometry.isPullback_morphismRestrict i c.U), c.ker_comap]
      rfl)

/-- The square of the centre over a chart commutes. -/
@[reassoc]
theorem centreMap_comm :
    c.centreMap ≫ Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n = (i ∣_ c.U) ≫ c.g :=
  IsClosedImmersion.lift_fac _ _ _

/-- **The centre on a chart is the base change of the coordinate centre.**  The square
```
Z ∩ U --centreMap--> 𝐀^m_R
  |i|_U                |
  U -------g------> 𝐀^{m+n}_R
```
is cartesian. -/
theorem isPullback_centreMap :
    IsPullback (i ∣_ c.U) c.centreMap c.g (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n) :=
  AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _ c.centreMap_comm.symm
    (by
      rw [AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
        (AlgebraicGeometry.isPullback_morphismRestrict i c.U), c.ker_comap]
      rfl)

/-- The morphism `centreMap` is étale, as a base change of the étale chart map. -/
instance etale_centreMap : Etale c.centreMap :=
  MorphismProperty.of_isPullback (P := @Etale) c.isPullback_centreMap c.etale

/-- The part `E_U = j⁻¹(b⁻¹(U))` of the exceptional divisor `E` over a chart, as an open of `E`;
here `j : E ⟶ X'` is the inclusion of the exceptional divisor. -/
abbrev exceptionalOpen : (exceptionalDivisor i.ker).Opens :=
  (exceptionalIdeal i.ker).subschemeι ⁻¹ᵁ (blowUpToBase i.ker ⁻¹ᵁ c.U)

omit [IsClosedImmersion i] in
/-- The ideal of `E_U ⊆ b⁻¹(U)` is the inverse image of the coordinate exceptional ideal. -/
theorem ker_exceptionalOpen :
    ((exceptionalIdeal i.ker).subschemeι ∣_ (blowUpToBase i.ker ⁻¹ᵁ c.U)).ker =
      (coordinateExceptional c.R c.m c.n).comap c.blowupMap := by
  rw [AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
    (AlgebraicGeometry.isPullback_morphismRestrict _ _), Scheme.IdealSheafData.ker_subschemeι,
    c.comap_exceptionalIdeal]

/-- **The exceptional divisor of a chart over the coordinate exceptional divisor**: the
morphism `E_U ⟶ E_L` induced by `blowupMap`.  It makes `isPullback_exceptionalMap`
cartesian. -/
noncomputable def exceptionalMap :
    c.exceptionalOpen.toScheme ⟶ coordinateExceptionalScheme c.R c.m c.n :=
  IsClosedImmersion.lift (coordinateExceptionalι c.R c.m c.n)
    (((exceptionalIdeal i.ker).subschemeι ∣_ (blowUpToBase i.ker ⁻¹ᵁ c.U)) ≫ c.blowupMap)
    (by
      rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le, c.ker_exceptionalOpen,
        Scheme.IdealSheafData.ker_subschemeι])

omit [IsClosedImmersion i] in
/-- The square of the exceptional divisor over a chart commutes. -/
@[reassoc]
theorem exceptionalMap_comm :
    c.exceptionalMap ≫ coordinateExceptionalι c.R c.m c.n =
      ((exceptionalIdeal i.ker).subschemeι ∣_ (blowUpToBase i.ker ⁻¹ᵁ c.U)) ≫ c.blowupMap :=
  IsClosedImmersion.lift_fac _ _ _

omit [IsClosedImmersion i] in
/-- **The exceptional divisor on a chart is the base change of the coordinate exceptional
divisor.**  The square
```
E_U --exceptionalMap--> E_L
 |j|                      |
b⁻¹(U) --blowupMap-----> L
```
is cartesian. -/
theorem isPullback_exceptionalMap :
    IsPullback ((exceptionalIdeal i.ker).subschemeι ∣_ (blowUpToBase i.ker ⁻¹ᵁ c.U))
      c.exceptionalMap c.blowupMap (coordinateExceptionalι c.R c.m c.n) :=
  AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _ c.exceptionalMap_comm.symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, c.ker_exceptionalOpen])

/-- The morphism `exceptionalMap` is étale, as a base change of `blowupMap`. -/
instance etale_exceptionalMap : Etale c.exceptionalMap :=
  MorphismProperty.of_isPullback (P := @Etale) c.isPullback_exceptionalMap c.etale_blowupMap

/-- `E_U` is the inverse image of the centre `Z ∩ U` under `p : E ⟶ Z`. -/
theorem exceptionalOpen_le :
    c.exceptionalOpen ≤ exceptionalDivisorToCentre i ⁻¹ᵁ (i ⁻¹ᵁ c.U) := by
  intro x hx
  change ((exceptionalDivisorToCentre i ≫ i) x) ∈ c.U
  rwa [exceptionalDivisorToCentre_comp]

/-- The structure morphism `p : E ⟶ Z` restricted to `E_U ⟶ Z ∩ U`. -/
noncomputable abbrev exceptionalToCentreRestrict :
    c.exceptionalOpen.toScheme ⟶ (i ⁻¹ᵁ c.U).toScheme :=
  (exceptionalDivisorToCentre i).resLE (i ⁻¹ᵁ c.U) c.exceptionalOpen c.exceptionalOpen_le

/-- **The exceptional divisor of a chart lies over the centre of the chart compatibly with the
coordinate model**: `exceptionalMap` followed by the projection `E_L ⟶ 𝐀^m_R` is `p|_{E_U}`
followed by `centreMap`. -/
theorem exceptionalMap_comp_toCentre :
    c.exceptionalMap ≫ coordinateExceptionalToCentre c.R c.m c.n =
      c.exceptionalToCentreRestrict ≫ c.centreMap := by
  rw [← cancel_mono (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n), Category.assoc,
    ← coordinateExceptionalι_comp_blowupToAmbient, reassoc_of% c.exceptionalMap_comm,
    Category.assoc, c.centreMap_comm, ← c.blowupMap_comm]
  have h : ((exceptionalIdeal i.ker).subschemeι ∣_ (blowUpToBase i.ker ⁻¹ᵁ c.U)) ≫
      (blowUpToBase i.ker ∣_ c.U) = c.exceptionalToCentreRestrict ≫ (i ∣_ c.U) := by
    rw [← cancel_mono c.U.ι]
    simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      Scheme.Hom.resLE_comp_ι_assoc, exceptionalDivisorToCentre_comp]
  rw [reassoc_of% h]

end Subschemes

end BlowupEtaleChart

open Stacks.AlgebraicGeometry in
/-- **[Stacks, Tag 0FUE] in the coordinate model.**  Let `i : Z ⟶ X` be a closed immersion of
schemes smooth over `S`.  Every point of `Z` has étale charts over the coordinate model inside any
neighbourhood of its image: there is a chart whose open `U` contains `i z` and is contained in the
given neighbourhood. -/
theorem exists_blowupEtaleChart [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)] (z : Z)
    (N : X.Opens) (hz : i z ∈ N) :
    ∃ c : BlowupEtaleChart f i, i z ∈ c.U ∧ c.U ≤ N := by
  obtain ⟨m, n, U, hyU, π, q, hπ, hπS, hpb⟩ :=
    exists_etale_coordinateSubspaceEmbedding_isPullback f i z
  have : IsClosedImmersion (coordinateSubspaceEmbedding S m n) :=
    coordinateSubspaceEmbedding_isClosedImmersion S m n
  have hker₀ : i.ker.comap U.ι = (coordinateSubspaceEmbedding S m n).ker.comap π := by
    rw [← AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
        (AlgebraicGeometry.isPullback_morphismRestrict i U),
      ← Scheme.Hom.resLE_eq_morphismRestrict,
      AlgebraicGeometry.ker_eq_comap_ker_of_isPullback hpb]
  -- an affine open of `S` around the image of `z`
  obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (x := f (i z))
    (U := ⊤) trivial
  have : IsAffine W.toScheme := hW
  let pA : AffineSpace (ULift.{u} (Fin (m + n))) S ⟶ S :=
    (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom
  let V : (AffineSpace (ULift.{u} (Fin (m + n))) S).Opens := pA ⁻¹ᵁ W
  let U' : X.Opens := U ⊓ N ⊓ f ⁻¹ᵁ W
  have hU'U : U' ≤ U := fun x hx => hx.1.1
  have hmem : i z ∈ U' := ⟨⟨hyU, hz⟩, hzW⟩
  let j : U'.toScheme ⟶ U.toScheme := X.homOfLE hU'U
  have hrange : Set.range (j ≫ π).base ⊆ Set.range V.ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change pA ((j ≫ π) x) ∈ W
    have hx : ((j ≫ π) ≫ pA) x = ((j ≫ U.ι) ≫ f) x := by
      rw [Category.assoc, hπS, ← Category.assoc]
    rw [Scheme.Hom.comp_apply] at hx
    rw [hx, Scheme.homOfLE_ι]
    exact x.2.2
  let l : U'.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (j ≫ π) hrange
  have hl : l ≫ V.ι = j ≫ π := IsOpenImmersion.lift_fac _ _ _
  have : Etale (l ≫ V.ι) := by
    rw [hl]
    infer_instance
  have : Etale l := Etale.of_comp l V.ι
  -- `V` is relative affine space over `W`
  have hsqV := AlgebraicGeometry.isPullback_morphismRestrict pA W
  have hsqA := (AffineSpace.isPullback_map (n := ULift.{u} (Fin (m + n))) W.ι).flip
  let eV : V.toScheme ≅ AffineSpace (ULift.{u} (Fin (m + n))) W.toScheme :=
    hsqV.isoIsPullback _ _ hsqA
  let eS := affineSpaceIsoSpec W.toScheme (coordinateIndexEquiv.{u} m n)
  let g : U'.toScheme ⟶ coordinateAmbient Γ(W.toScheme, ⊤) m n :=
    l ≫ eV.hom ≫ eS.hom
  have : Etale g := inferInstance
  have hVι : eV.hom ≫ AffineSpace.map (ULift.{u} (Fin (m + n))) W.ι = V.ι :=
    hsqV.isoIsPullback_hom_snd _ _ hsqA
  have := coordinateSubspaceEmbedding_isClosedImmersion W.toScheme m n
  let base : Spec Γ(W.toScheme, ⊤) ⟶ S := W.toScheme.isoSpec.inv ≫ W.ι
  refine ⟨BlowupEtaleChart.mk Γ(W.toScheme, ⊤) m n U' g base ?_ ?_, hmem, fun x hx => hx.1.2⟩
  · -- the chart is a morphism over `S`
    have hover : eS.hom ≫ coordinateAmbientToBase _ m n ≫
        W.toScheme.isoSpec.inv =
        (AffineSpace.over (ULift.{u} (Fin (m + n))) W.toScheme).hom := by
      rw [← Iso.eq_inv_comp]
      exact (affineSpaceIsoSpec_inv_over W.toScheme (coordinateIndexEquiv.{u} m n)).symm
    calc g ≫ coordinateAmbientToBase _ m n ≫ W.toScheme.isoSpec.inv ≫
          W.ι
        = l ≫ eV.hom ≫ (eS.hom ≫ coordinateAmbientToBase _ m n ≫
            W.toScheme.isoSpec.inv) ≫ W.ι := by
          simp only [g, Category.assoc]
      _ = l ≫ V.ι ≫ pA := by
          rw [hover, ← hVι, Category.assoc]
          simp only [pA]
          congr 2
          exact (AffineSpace.map_over (n := ULift.{u} (Fin (m + n))) W.ι).symm
      _ = U'.ι ≫ f := by
          rw [← Category.assoc, hl, Category.assoc, hπS, ← Category.assoc, Scheme.homOfLE_ι]
  · -- the ideal of `Z` is the inverse image of the coordinate ideal
    have hkerW : (coordinateSubspaceEmbedding W.toScheme m n).ker.comap eS.inv =
        Stacks.MoreMorphisms.coordinateIdeal Γ(W.toScheme, ⊤) m n :=
      (AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
        (IsPullback.of_horiz_isIso
          (CommSq.mk (affineSpaceIsoSpec_coordinate_sq W.toScheme m n))).flip).symm
    have hkerA : (coordinateSubspaceEmbedding W.toScheme m n).ker =
        (coordinateSubspaceEmbedding S m n).ker.comap
          (AffineSpace.map (ULift.{u} (Fin (m + n))) W.ι) :=
      AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
        (isPullback_coordinateSubspaceEmbedding_map W.ι m n)
    calc i.ker.comap U'.ι = (i.ker.comap U.ι).comap j := by
          rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
      _ = (coordinateSubspaceEmbedding S m n).ker.comap (l ≫ eV.hom ≫
            AffineSpace.map (ULift.{u} (Fin (m + n))) W.ι) := by
          rw [hker₀, ← Scheme.IdealSheafData.comap_comp, hVι, hl]
      _ = ((coordinateSubspaceEmbedding W.toScheme m n).ker.comap eS.inv).comap g := by
          rw [hkerA, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
          congr 1
          simp [g]
      _ = _ := by rw [hkerW]

end Stacks.DeRham

end
