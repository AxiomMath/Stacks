module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratification
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.RetrocompactOpen
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.FiniteTypeIdealSheaf
public import StacksFrontier.CategoryTheory.MorphismProperty.BaseChangeCommSquare

/-!
# Flat stratifications of a fixed length

`AlgebraicGeometry.HasFlatStratification` records the conclusion of Stacks 0H3Z for a morphism
`f : X ⟶ S`: the base carries a finite descending chain of closed subschemes
`S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` along which `f` becomes flat. It is an existential statement, so the
number `t` of strata is hidden. The sufficiency direction of Stacks 0EVF is proved by induction
on that number, which is why this file introduces
`AlgebraicGeometry.IsFlatStratification f t I`: the very same conclusion with the length `t` and
the chain `I` exposed as explicit arguments.

Besides the translation between the two forms, the file records what can be read off a
stratification of a given length: a stratification with no strata at all forces the base to be
empty, a stratification with one stratum makes the base change of `f` to the first member of the
chain flat, and the first stratum of a stratification of a quasi-compact base is quasi-compact.
It also provides the two operations the induction uses: restricting a stratification along a
closed immersion, and dropping the first member of the chain.

## Main definitions

* `AlgebraicGeometry.IsFlatStratification`: the conclusion of Stacks 0H3Z for `f : X ⟶ S`, with
  the length of the stratification and the chain of ideal sheaves exposed as data.

## Main results

* `AlgebraicGeometry.hasFlatStratification_iff`: `AlgebraicGeometry.HasFlatStratification` is the
  existence of an `AlgebraicGeometry.IsFlatStratification` of some length.
* `AlgebraicGeometry.IsFlatStratification.isEmpty`: a stratification of length `0` forces the
  base to be empty.
* `AlgebraicGeometry.IsFlatStratification.flat_of_eq_one`: a stratification of length `1` makes
  the base change of `f` to the first member of the chain flat.
* `AlgebraicGeometry.IsFlatStratification.isCompact_stratum`: over a quasi-compact base, the
  first stratum of a stratification is quasi-compact.
* `AlgebraicGeometry.IsFlatStratification.comap`: a stratification restricts along a closed
  immersion whose first member stays a thickening.
* `AlgebraicGeometry.IsFlatStratification.succ`: dropping the first member of the chain shortens
  a stratification by one stratum, provided the second member is again a thickening.

## Implementation notes

The encoding is the one fixed by `AlgebraicGeometry.HasFlatStratification`, and is explained in
detail in the module documentation of
`StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratification`. In short: a closed subscheme
of `S` is recorded by its quasi-coherent ideal sheaf, an
`AlgebraicGeometry.Scheme.IdealSheafData`, so the descending chain of closed subschemes
`S ⊇ S₀ ⊇ ⋯ ⊇ S_t = ∅` is recorded by the *ascending* chain
`I : Fin (t + 1) → S.IdealSheafData` of their ideal sheaves; the empty last member `S_t = ∅` is
`I (Fin.last t) = ⊤`; that `S₀ ⊆ S` is a thickening is `Stacks.Thickenings.IsThickening` of
`(I 0).subschemeι`, equivalently (by
`AlgebraicGeometry.Scheme.IdealSheafData.isThickening_subschemeι_iff`) that `I 0` is supported on
all of `S`; and the stratum `S_i ∖ S_{i+1}` is the open subscheme
`(I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl` of `S_i`, the complement inside `S_i` of
the support of the next member of the chain. The only difference from
`AlgebraicGeometry.HasFlatStratification` is that the `let`-bindings naming the stratum are
inlined, so `AlgebraicGeometry.hasFlatStratification_iff` holds by definitional unfolding.

Every flatness statement below is flatness of `pullback.snd f g` for various `g` into `S`, i.e.
flatness of the base change of `f` along `g`, and all of them are instances of
`CategoryTheory.MorphismProperty.pullbackSnd_of_comm`: a commuting square `a ≫ g = b ≫ h`
transports flatness of the base change along `g` to flatness of the base change along `b` of the
base change along `h`, because both are base changes of `f` along the common composite. In
particular no square has to be exhibited as a pullback: a commuting triangle is enough. For
`AlgebraicGeometry.IsFlatStratification.comap` the triangle comes from
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap`, which maps the inverse image
`(I i).comap K.subschemeι` of a member of the chain to that member over `K.subschemeι`, together
with `AlgebraicGeometry.Scheme.IdealSheafData.support_comap`, which identifies the stratum of the
inverse-image chain with the preimage of the original stratum, so that
`AlgebraicGeometry.Scheme.Hom.resLE` restricts `subschemeMap` to the strata.

Quasi-compactness of the first stratum is Stacks 01PH: the stratum is the complement, inside the
closed subscheme `(I 0).subscheme`, of the support of the finite type ideal sheaf
`(I 1).comap (I 0).subschemeι`, and
`AlgebraicGeometry.isCompact_of_isFiniteType_idealSheafData` turns that into quasi-compactness.
Finite type is inherited by inverse images
(`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType.comap`) and supports are computed by
`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`.

## References

* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **The conclusion of Stacks 0H3Z for `f : X ⟶ S`, with the length of the stratification and
the chain of ideal sheaves exposed as data.** The closed subschemes
`S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` of the base are recorded by the ascending chain `I` of their ideal
sheaves, so that `S_i` is `(I i).subscheme`; the conditions are that

* `S₀ ⊆ S` is a thickening, i.e. `I 0` is supported on all of `S`,
* each `S_i → S` is defined by an ideal sheaf of finite type,
* the chain `I` is ascending, i.e. the chain `S_i` is descending,
* the last member `S_t` is empty, which is `I (Fin.last t) = ⊤`, and
* the base change `X ×_S (S_i ∖ S_{i+1})` is flat over the stratum `S_i ∖ S_{i+1}`, which is
  the open subscheme `(I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl` of `S_i` cut out by
  removing the support of the next member of the chain.

This is `AlgebraicGeometry.HasFlatStratification` with `t` and `I` no longer existentially
quantified; see `AlgebraicGeometry.hasFlatStratification_iff`. -/
public def IsFlatStratification (f : X ⟶ S) (t : ℕ) (I : Fin (t + 1) → S.IdealSheafData) :
    Prop :=
  Stacks.Thickenings.IsThickening (I 0).subschemeι ∧
    (∀ i, (I i).IsFiniteType) ∧
    (∀ i : Fin t, I i.castSucc ≤ I i.succ) ∧
    I (Fin.last t) = ⊤ ∧
    ∀ i : Fin t,
      Flat (pullback.snd f
        (((I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl).ι ≫
          (I i.castSucc).subschemeι))

/-- Base changing `f` along `e ≫ k` is the same as base changing it along `k` when `e` is an
isomorphism: the two base changes differ by the base change of `e`, which is again an
isomorphism. -/
private theorem flat_pullback_snd_of_iso_comp {Y W : Scheme.{u}} (f : X ⟶ S) (k : Y ⟶ S)
    (e : W ⟶ Y) [IsIso e] (hf : Flat (pullback.snd f (e ≫ k))) : Flat (pullback.snd f k) := by
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h := MorphismProperty.pullbackSnd_of_comm (@Flat : MorphismProperty Scheme.{u}) f
    (e ≫ k) k (𝟙 W) e (Category.id_comp _) hf
  rw [← MorphismProperty.cancel_right_of_respectsIso
      (@Flat : MorphismProperty Scheme.{u}) _ e,
    ← pullback.condition,
    MorphismProperty.cancel_left_of_respectsIso (@Flat : MorphismProperty Scheme.{u})] at h
  exact h

/-- The complement of the support of an inverse image is the preimage of the complement of the
support. -/
private theorem compl_support_comap {Y : Scheme.{u}} (K : Y.IdealSheafData) (g : X ⟶ Y) :
    (K.comap g).support.compl = g ⁻¹ᵁ K.support.compl := by
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  simp

/-- An ideal sheaf supported on all of the scheme defines a thickening. -/
private theorem isThickening_subschemeι_of_support_eq_univ (I : S.IdealSheafData)
    (h : (I.support : Set S) = Set.univ) : Stacks.Thickenings.IsThickening I.subschemeι := by
  rw [Scheme.IdealSheafData.isThickening_subschemeι_iff]
  exact TopologicalSpace.Closeds.ext (by rw [h]; rfl)

/-- The stratum cut out of the inverse image `Z.comap K.subschemeι` by removing the support of
`N.comap K.subschemeι` is the base change, along `K.subschemeι`, of the stratum cut out of `Z` by
removing the support of `N`. Its flatness over `X ×_S K.subscheme` therefore follows from the
flatness of the original stratum over `X`. -/
private theorem flat_stratum_comap (f : X ⟶ S) (Z N K : S.IdealSheafData)
    (hflat : Flat (pullback.snd f ((Z.subschemeι ⁻¹ᵁ N.support.compl).ι ≫ Z.subschemeι))) :
    Flat (pullback.snd (pullback.snd f K.subschemeι)
      (((Z.comap K.subschemeι).subschemeι ⁻¹ᵁ (N.comap K.subschemeι).support.compl).ι ≫
        (Z.comap K.subschemeι).subschemeι)) := by
  have hbι : Scheme.IdealSheafData.subschemeMap (Z.comap K.subschemeι) Z K.subschemeι
        (Z.le_map_comap K.subschemeι) ≫ Z.subschemeι =
      (Z.comap K.subschemeι).subschemeι ≫ K.subschemeι :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have hV : ((Z.comap K.subschemeι).subschemeι ⁻¹ᵁ (N.comap K.subschemeι).support.compl) ≤
      Scheme.IdealSheafData.subschemeMap (Z.comap K.subschemeι) Z K.subschemeι
        (Z.le_map_comap K.subschemeι) ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ N.support.compl) := by
    rw [← Scheme.Hom.comp_preimage, hbι, Scheme.Hom.comp_preimage, compl_support_comap]
  refine MorphismProperty.pullbackSnd_of_comm (@Flat : MorphismProperty Scheme.{u}) f _
    K.subschemeι (Scheme.Hom.resLE _ _ _ hV) _ ?_ hflat
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc]
  rw [hbι]

/-- `AlgebraicGeometry.HasFlatStratification` is the existence of a flat stratification of some
length. -/
public theorem hasFlatStratification_iff (f : X ⟶ S) :
    HasFlatStratification f ↔ ∃ (t : ℕ) (I : Fin (t + 1) → S.IdealSheafData),
      IsFlatStratification f t I := Iff.rfl

/-- A flat stratification with no strata forces the base to be empty: its chain consists of the
single member `I 0 = I (Fin.last 0) = ⊤`, which is supported nowhere, while being a thickening
asks it to be supported everywhere. -/
public theorem IsFlatStratification.isEmpty {f : X ⟶ S} {I : Fin 1 → S.IdealSheafData}
    (h : IsFlatStratification f 0 I) : IsEmpty S := by
  obtain ⟨hthick, -, -, hlast, -⟩ := h
  have h0 : I 0 = ⊤ := hlast
  rw [Scheme.IdealSheafData.isThickening_subschemeι_iff] at hthick
  refine ⟨fun x ↦ ?_⟩
  have hx : x ∈ (I 0).support := by rw [hthick]; trivial
  rw [h0, Scheme.IdealSheafData.support_top] at hx
  exact hx

/-- A flat stratification with one stratum makes the morphism flat over the first closed
subscheme of the chain: the second member of the chain is `⊤`, so the only stratum is all of
the first closed subscheme. -/
public theorem IsFlatStratification.flat_of_eq_one {f : X ⟶ S} {I : Fin 2 → S.IdealSheafData}
    (h : IsFlatStratification f 1 I) : Flat (pullback.snd f (I 0).subschemeι) := by
  obtain ⟨-, -, -, hlast, hflat⟩ := h
  have h1 : I 1 = ⊤ := hlast
  have hU : ((I 0).subschemeι ⁻¹ᵁ (I 1).support.compl : (I 0).subscheme.Opens) = ⊤ := by
    rw [h1, Scheme.IdealSheafData.support_top]
    ext x
    simp
  have key : Flat (pullback.snd f
      (((I 0).subschemeι ⁻¹ᵁ (I 1).support.compl).ι ≫ (I 0).subschemeι)) := hflat 0
  rw [hU] at key
  have : IsIso (Scheme.Opens.ι (⊤ : (I 0).subscheme.Opens)) := by
    rw [← Scheme.topIso_hom]
    infer_instance
  exact flat_pullback_snd_of_iso_comp f (I 0).subschemeι
    (Scheme.Opens.ι (⊤ : (I 0).subscheme.Opens)) key

/-- The complement of the support of the second member of a flat stratification is a
quasi-compact open of the first closed subscheme of the chain: it is the complement of the
support of the finite type ideal sheaf `(I 1).comap (I 0).subschemeι` on the quasi-compact
scheme `(I 0).subscheme`. -/
public theorem IsFlatStratification.isCompact_stratum {t : ℕ} {f : X ⟶ S}
    {I : Fin (t + 2) → S.IdealSheafData} (h : IsFlatStratification f (t + 1) I)
    [CompactSpace S] :
    IsCompact (((I 0).subschemeι ⁻¹ᵁ (I 1).support.compl :
      (I 0).subscheme.Opens) : Set (I 0).subscheme) := by
  have : CompactSpace (I 0).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (I 0).subschemeι
  refine isCompact_of_isFiniteType_idealSheafData _ ((I 1).comap (I 0).subschemeι)
    ((h.2.1 1).comap _) ?_
  rw [← compl_support_comap]
  simp

/-- A flat stratification restricts to a closed subscheme whose first member stays a
thickening. The chain of the restriction is the chain of inverse images, which stays of finite
type and ascending, and each of its strata is the base change of the corresponding original
stratum. -/
public theorem IsFlatStratification.comap {t : ℕ} {f : X ⟶ S}
    {I : Fin (t + 1) → S.IdealSheafData} (h : IsFlatStratification f t I)
    (K : S.IdealSheafData)
    (hK : (((I 0).comap K.subschemeι).support : Set K.subscheme) = Set.univ) :
    IsFlatStratification (pullback.snd f K.subschemeι) t
      (fun k ↦ (I k).comap K.subschemeι) := by
  obtain ⟨-, hft, hmono, hlast, hflat⟩ := h
  refine ⟨?_, fun k ↦ (hft k).comap _, fun i ↦ Scheme.IdealSheafData.comap_mono _ (hmono i),
    ?_, fun i ↦ flat_stratum_comap f _ _ K (hflat i)⟩
  · exact isThickening_subschemeι_of_support_eq_univ _ hK
  · simp only [hlast, Scheme.IdealSheafData.comap_top]

/-- Dropping the first member of a flat stratification whose second member is again a
thickening shortens it by one stratum: the remaining chain `k ↦ I k.succ` satisfies every clause,
and its strata are the strata of the original chain other than the first one. -/
public theorem IsFlatStratification.succ {t : ℕ} {f : X ⟶ S}
    {I : Fin (t + 2) → S.IdealSheafData} (h : IsFlatStratification f (t + 1) I)
    (hthick : ((I 1).support : Set S) = Set.univ) :
    IsFlatStratification f t (fun k : Fin (t + 1) ↦ I k.succ) := by
  obtain ⟨-, hft, hmono, hlast, hflat⟩ := h
  refine ⟨?_, fun k ↦ hft k.succ, fun i ↦ ?_, ?_, fun i ↦ ?_⟩
  · exact isThickening_subschemeι_of_support_eq_univ _ hthick
  · simp only [Fin.succ_castSucc]
    exact hmono i.succ
  · simp only [Fin.succ_last]
    exact hlast
  · simp only [Fin.succ_castSucc]
    exact hflat i.succ

end AlgebraicGeometry

end
