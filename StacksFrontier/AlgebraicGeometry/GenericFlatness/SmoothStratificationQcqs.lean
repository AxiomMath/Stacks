module

public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageStratification
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.SmoothStratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.FiniteTypeIdealSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stratifying a morphism of finite presentation over a quasi-compact quasi-separated base

Let `f : X ⟶ S` be a morphism of finite presentation between quasi-compact and quasi-separated
schemes. Then the base carries a finite descending chain of closed subschemes
`S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅`, each cut out by a finite type ideal sheaf and with `S₀ ⊆ S` a
thickening, such that every stratum `S_i ∖ S_{i+1}` admits a surjective finite locally free cover
`T_i` over which `X ×_S T_i` is itself filtered by closed subschemes cut out by finite type ideal
sheaves, the first a thickening and the last empty, with smooth successive differences.

This is [Stacks, Tag 0H44]. The generic case over a reduced base is
`AlgebraicGeometry.exists_smooth_stratification_at_generic_point`, Tag 0H43, and the content of
this file is the passage from it to the global statement: Noetherian induction on the base
produces the chain over a Noetherian base, and absolute Noetherian approximation transports it
to a quasi-compact quasi-separated one.

## Main definitions

* `Stacks.GenericFlatness.HasSmoothStratification`: a morphism `q : A ⟶ B` admits a finite chain
  of closed subschemes of `A`, cut out by finite type ideal sheaves, the first a thickening and
  the last empty, with all strata smooth over `B`.
* `AlgebraicGeometry.HasSmoothStratificationAfterFiniteLocallyFreeCover`: the conclusion of
  Tag 0H44 for `f`.

## Main results

* `Stacks.GenericFlatness.HasSmoothStratification.of_isPullback`: a smooth stratification base
  changes.
* `Stacks.GenericFlatness.hasSmoothStratification_of_closedImmersionChain`: a chain of closed
  immersions with finite type ideal sheaves and smooth strata is a smooth stratification.
* `AlgebraicGeometry.hasSmoothStratificationAfterFiniteLocallyFreeCover`: **[Stacks, Tag 0H44]**.

## Implementation notes

Both chains are recorded in the library's existing shape
`Stacks.GenericFlatness.HasStratification`, the conclusion of Tags 0H3Z, 0H41 and 0ASY: a
descending chain of closed subschemes is the ascending chain of their quasi-coherent ideal
sheaves, `S_t = ∅` is `I (Fin.last t) = ⊤`, and the stratum `S_i ∖ S_{i+1}` is the open subscheme
of `S_i` cut out by removing the support of `I (i + 1)`. The inner chain of Tag 0H44 is the same
shape over `X ×_S T_i` with the strata required to be smooth over `T_i`, so no second notion of
stratification is introduced.

Tag 0H43 presents its chain by closed immersions `Z_j ⟶ X_i` with the finite type condition on
`Stacks.ClosedImmersion.idealSheaf`, so
`hasSmoothStratification_of_closedImmersionChain` converts that presentation into ideal sheaf
data: `AlgebraicGeometry.Scheme.Hom.ker` is the ideal sheaf,
`AlgebraicGeometry.Scheme.Hom.toImage` is the isomorphism onto the closed subscheme it cuts out,
and finite type of the ideal sheaf matches finite presentation of the closed immersion through
Tag 01TV and `Stacks.Flatness.locallyOfFinitePresentation_subschemeι_iff`.

The base change of a smooth stratification is `Stacks.GenericFlatness.HasStratification.comap` on
the chain, together with the observation that each stratum of the pulled back chain is the base
change of the corresponding stratum, so that smoothness over the new base follows from stability
of smoothness under base change rather than from stability under precomposition — which is what
`HasStratification.comap` asks for and which smoothness does not have. The cover condition of
Tag 0H44 *is* stable under precomposition, by pulling the cover back along the new base, and that
is what makes the outer chain descend from the Noetherian model.

## References

* [Stacks Project, Tag 0H44](https://stacks.math.columbia.edu/tag/0H44)
* [Stacks Project, Tag 0H43](https://stacks.math.columbia.edu/tag/0H43)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- Smoothness is invariant under pre- and postcomposition with an isomorphism, being stable
under base change. -/
private local instance smooth_respectsIso :
    MorphismProperty.RespectsIso (@Smooth.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Local finite presentation is invariant under pre- and postcomposition with an isomorphism,
being stable under base change. -/
private local instance locallyOfFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

namespace Stacks.GenericFlatness

/-! ### Smooth stratifications -/

/-- **A smooth stratification of `q : A ⟶ B`.** A finite descending chain of closed subschemes
`A ⊇ Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t = ∅`, recorded by the ascending chain of their quasi-coherent ideal
sheaves, with each `Z_j → A` defined by a finite type ideal sheaf, `Z₀ ⊆ A` a thickening, and
each stratum `Z_j ∖ Z_{j+1}` smooth over `B`. -/
def HasSmoothStratification {A B : Scheme.{u}} (q : A ⟶ B) : Prop :=
  HasStratification A fun _ b ↦ Smooth (b ≫ q)

/-- **A smooth stratification base changes.** If `A' = A ×_B B'`, a smooth stratification of
`A ⟶ B` pulls back to one of `A' ⟶ B'`: the chain is pulled back along `A' ⟶ A` and each new
stratum is the base change of the old one, hence still smooth over `B'`. -/
theorem HasSmoothStratification.of_isPullback {A B A' B' : Scheme.{u}}
    {q : A ⟶ B} {q' : A' ⟶ B'} {p : A' ⟶ A} {u : B' ⟶ B}
    (hsq : IsPullback p q' q u) (h : HasSmoothStratification q) :
    HasSmoothStratification q' := by
  obtain ⟨t, I, hthick, hfin, hmono, hlast, hstrat⟩ := h
  rw [Scheme.IdealSheafData.isThickening_subschemeι_iff] at hthick
  refine ⟨t, fun i ↦ (I i).comap p, ?_, fun i ↦ (hfin i).comap p,
    fun i ↦ Scheme.IdealSheafData.comap_mono p (hmono i), ?_, ?_⟩
  · show Stacks.Thickenings.IsThickening ((I 0).comap p).subschemeι
    rw [Scheme.IdealSheafData.isThickening_subschemeι_iff,
      Scheme.IdealSheafData.support_comap, hthick]
    exact TopologicalSpace.Closeds.ext (by simp)
  · show (I (Fin.last t)).comap p = ⊤
    rw [hlast, Scheme.IdealSheafData.comap_top]
  · intro i
    dsimp only
    set J := I i.castSucc
    set ψ := ((J.comapIso p).hom ≫ pullback.snd p J.subschemeι) with hψ
    have hq : (J.comap p).subschemeι ≫ p = ψ ≫ J.subschemeι := by
      rw [hψ, ← Scheme.IdealSheafData.comapIso_hom_fst J p, Category.assoc, Category.assoc,
        ← pullback.condition]
    have hpb : IsPullback ψ (J.comap p).subschemeι J.subschemeι p :=
      (isPullback_of_isClosedImmersion _ _ _ _ hq
        (by simp [Scheme.IdealSheafData.ker_subschemeι])).flip
    have hW : (J.comap p).subschemeι ⁻¹ᵁ ((I i.succ).comap p).support.compl =
        ψ ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ (I i.succ).support.compl) := by
      refine TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_)
      show (J.comap p).subschemeι.base x ∉ (((I i.succ).comap p).support : Set A') ↔
        (ψ ≫ J.subschemeι).base x ∉ ((I i.succ).support : Set A)
      rw [Scheme.IdealSheafData.support_comap, ← hq]
      rfl
    rw [hW]
    refine MorphismProperty.of_isPullback (P := @Smooth.{u})
      ((isPullback_morphismRestrict ψ
        (J.subschemeι ⁻¹ᵁ (I i.succ).support.compl)).paste_vert hpb |>.paste_vert hsq) ?_
    simpa only [Category.assoc] using hstrat i

/-- **Transporting a smooth stratification between two fibre products.** If `A` and `A'` are the
fibre products of `f` with `c` and with `c'`, and `c'` factors through `c` by `u`, then a smooth
stratification of `A ⟶ T` gives one of `A' ⟶ T'`. -/
theorem HasSmoothStratification.of_squares {X Y A A' T T' : Scheme.{u}}
    {f : X ⟶ Y} {c : T ⟶ Y} {c' : T' ⟶ Y} {u : T' ⟶ T}
    {a : A ⟶ X} {q : A ⟶ T} {a' : A' ⟶ X} {q' : A' ⟶ T'}
    (hu : u ≫ c = c') (hsq : IsPullback a q f c) (hsq' : IsPullback a' q' f c')
    (h : HasSmoothStratification q) : HasSmoothStratification q' :=
  HasSmoothStratification.of_isPullback
    (IsPullback.of_right' (show IsPullback a' q' f (u ≫ c) by rwa [hu]) hsq) h

/-- If the open `W ⊆ Z₁` off the image of a closed immersion `j₂` is smooth over `B` via
`j₁ ≫ q`, then so is the corresponding open of the closed subscheme cut out by `j₁.ker`. -/
theorem smooth_subschemeι_ker_stratum {A B Z₁ Z₂ : Scheme.{u}} (q : A ⟶ B) (j₁ : Z₁ ⟶ A)
    (j₂ : Z₂ ⟶ A) [IsClosedImmersion j₁] [IsClosedImmersion j₂] (W : Z₁.Opens)
    (hW : ∀ x : Z₁, x ∈ W ↔ j₁ x ∉ Set.range j₂) (hs : Smooth (W.ι ≫ j₁ ≫ q)) :
    Smooth ((j₁.ker.subschemeι ⁻¹ᵁ j₂.ker.support.compl).ι ≫ j₁.ker.subschemeι ≫ q) := by
  have hφ : j₁.toImage ≫ j₁.ker.subschemeι = j₁ := j₁.toImage_imageι
  set V := j₁.ker.subschemeι ⁻¹ᵁ j₂.ker.support.compl
  have hmem : ∀ x : Z₁, j₁.toImage x ∈ V ↔ x ∈ W := by
    intro x
    rw [hW x]
    show j₁.ker.subschemeι (j₁.toImage x) ∉ (j₂.ker.support : Set A) ↔ _
    rw [Scheme.Hom.support_ker, j₂.isClosedEmbedding.isClosed_range.closure_eq,
      ← Scheme.Hom.comp_apply, hφ]
  have hr : Set.range (W.ι ≫ j₁.toImage).base = Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    refine Set.ext fun y ↦ ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨x, rfl⟩
      show j₁.toImage x.1 ∈ V
      exact (hmem x.1).mpr x.2
    · obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso j₁.toImage.base).2 y
      exact ⟨⟨x, (hmem x).mp hy⟩, rfl⟩
  let ε : W.toScheme ≅ V.toScheme := IsOpenImmersion.isoOfRangeEq (W.ι ≫ j₁.toImage) V.ι hr
  have hε : ε.hom ≫ V.ι = W.ι ≫ j₁.toImage := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr
  rw [← hφ] at hs
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{u}) ε.hom]
  simpa only [Category.assoc, reassoc_of% hε] using hs

/-- **A chain of closed immersions with smooth strata is a smooth stratification.** The chain
`A ⊇ Z 0 ⊇ Z 1 ⊇ ⋯ ⊇ Z t = ∅` is given by closed immersions `j i : Z i ⟶ A` with finite type
ideal sheaves, with `j 0` a thickening, with inclusions `k i` between successive terms, and with
the stratum `W i ⊆ Z i.castSucc` on the complement of the image of `j i.succ` smooth over `B`. -/
theorem hasSmoothStratification_of_closedImmersionChain {A B : Scheme.{u}} (q : A ⟶ B)
    (t : ℕ) (Z : Fin (t + 1) → Scheme.{u}) (j : (i : Fin (t + 1)) → Z i ⟶ A)
    (k : (i : Fin t) → Z i.succ ⟶ Z i.castSucc) (W : (i : Fin t) → (Z i.castSucc).Opens)
    (hj : ∀ i, IsClosedImmersion (j i))
    (hjfin : ∀ i, (Stacks.ClosedImmersion.idealSheaf (j i).toLRSHom.toShHom).IsFiniteType)
    (hthick : Stacks.Thickenings.IsThickening (j 0))
    (hempty : IsEmpty (Z (Fin.last t)))
    (hkj : ∀ i : Fin t, k i ≫ j i.castSucc = j i.succ)
    (hW : ∀ (i : Fin t) (x : Z i.castSucc), x ∈ W i ↔ j i.castSucc x ∉ Set.range (j i.succ))
    (hsmooth : ∀ i : Fin t, Smooth ((W i).ι ≫ j i.castSucc ≫ q)) :
    HasSmoothStratification q := by
  refine ⟨t, fun i ↦ (j i).ker, ?_, ?_, ?_, ?_, ?_⟩
  · show Stacks.Thickenings.IsThickening (j 0).ker.subschemeι
    rw [Scheme.IdealSheafData.isThickening_subschemeι_iff]
    refine TopologicalSpace.Closeds.ext ?_
    have := hj 0
    rw [Scheme.Hom.support_ker, (j 0).isClosedEmbedding.isClosed_range.closure_eq,
      Set.range_eq_univ.mpr hthick.2]
    simp
  · intro i
    have := hj i
    have hfp : FinitePresentation (j i) :=
      (finitePresentation_iff_isFiniteType_idealSheaf (j i)).mpr (hjfin i)
    have h1 : LocallyOfFinitePresentation ((j i).toImage ≫ (j i).ker.subschemeι) := by
      rw [(j i).toImage_imageι]
      exact hfp.1
    exact (Stacks.Flatness.locallyOfFinitePresentation_subschemeι_iff (j i).ker).mp
      ((MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation.{u})
        (j i).toImage (j i).ker.subschemeι).mp h1)
  · intro i
    show (j i.castSucc).ker ≤ (j i.succ).ker
    rw [← hkj i]
    exact Scheme.Hom.le_ker_comp (k i) (j i.castSucc)
  · show (j (Fin.last t)).ker = ⊤
    exact (Scheme.Hom.ker_eq_top_iff_isEmpty _).mpr hempty
  · intro i
    have := hj i.castSucc
    have := hj i.succ
    exact smooth_subschemeι_ker_stratum q (j i.castSucc) (j i.succ) (W i) (hW i) (hsmooth i)

end Stacks.GenericFlatness

namespace AlgebraicGeometry

open Stacks.GenericFlatness

/-! ### The conclusion of Stacks 0H44 -/

/-- **The conclusion of Stacks 0H44 for `f : X ⟶ S`.** There is a finite descending chain of
closed subschemes `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` of the base, recorded by the ascending chain of
their ideal sheaves, such that each `S_i → S` is defined by a finite type ideal sheaf, `S₀ ⊆ S`
is a thickening, and each stratum `S_i ∖ S_{i+1}` carries a surjective finite locally free cover
`T_i` over which `X ×_S T_i` has a smooth stratification. -/
def HasSmoothStratificationAfterFiniteLocallyFreeCover {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  HasStratification S fun (U : Scheme.{u}) (a : U ⟶ S) ↦
    ∃ (T : Scheme.{u}) (g : T ⟶ U), Function.Surjective g ∧
      Stacks.Morphisms.IsFiniteLocallyFree g ∧
      HasSmoothStratification (pullback.snd f (g ≫ a))

/-! ### Stability of the stratum condition under precomposition -/

/-- **The stratum condition of Stacks 0H44 is stable under precomposition.** Pulling the finite
locally free cover back along `b` covers the smaller stratum, and the smooth stratification over
it is the base change of the given one. -/
private theorem coverSmoothStratification_comp {X S : Scheme.{u}} (f : X ⟶ S)
    {U V : Scheme.{u}} (a : U ⟶ S) (b : V ⟶ U)
    (h : ∃ (T : Scheme.{u}) (g : T ⟶ U), Function.Surjective g ∧
      Stacks.Morphisms.IsFiniteLocallyFree g ∧
      HasSmoothStratification (pullback.snd f (g ≫ a))) :
    ∃ (T : Scheme.{u}) (g : T ⟶ V), Function.Surjective g ∧
      Stacks.Morphisms.IsFiniteLocallyFree g ∧
      HasSmoothStratification (pullback.snd f (g ≫ b ≫ a)) := by
  obtain ⟨T, g, hgsurj, hgflf, hstrat⟩ := h
  have hpb := (IsPullback.of_hasPullback b g).flip
  refine ⟨pullback b g, pullback.fst b g, ?_, ?_, ?_⟩
  · exact (MorphismProperty.of_isPullback (P := @Surjective.{u}) hpb ⟨hgsurj⟩).surj
  · rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
      at hgflf ⊢
    exact ⟨MorphismProperty.of_isPullback hpb hgflf.1,
      MorphismProperty.of_isPullback hpb hgflf.2.1, MorphismProperty.of_isPullback hpb hgflf.2.2⟩
  · refine HasSmoothStratification.of_squares (u := pullback.snd b g) ?_
      (IsPullback.of_hasPullback f (g ≫ a)) (IsPullback.of_hasPullback f _) hstrat
    rw [← Category.assoc, ← pullback.condition, Category.assoc]

/-! ### Finite presentation of a base change -/

/-- A base change of a morphism of finite presentation is of finite presentation. -/
private theorem finitePresentation_pullback_snd {X S T : Scheme.{u}} {f : X ⟶ S}
    (hf : FinitePresentation f) (c : T ⟶ S) : FinitePresentation (pullback.snd f c) :=
  ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback f c) hf.1,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f c) hf.2.1,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f c) hf.2.2⟩

/-! ### The Noetherian case -/

/-- **Stacks 0H44 over a Noetherian base.** Noetherian induction on the base, the generic step
being Tag 0H43 applied at a generic point of an irreducible component of the reduced closed
subscheme on the current stratum. -/
private theorem hasSmoothStratificationAfterFiniteLocallyFreeCover_of_isNoetherian
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) (hf : FinitePresentation f) :
    HasSmoothStratificationAfterFiniteLocallyFreeCover f := by
  refine exists_stratification_of_isNoetherian _ fun C hC ↦ ?_
  set J := Scheme.IdealSheafData.vanishingIdeal C
  have : IsReduced J.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
  have : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  have : IsNoetherian J.subscheme := ⟨⟩
  have hne : Nonempty J.subscheme := by
    have hCne : (C : Set S).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun h ↦ hC (SetLike.coe_injective h)
    have hr : Set.range J.subschemeι.base = (C : Set S) :=
      (Scheme.IdealSheafData.range_subschemeι J).trans
        (Scheme.IdealSheafData.coe_support_vanishingIdeal C)
    rw [← hr] at hCne
    obtain ⟨-, y, -⟩ := hCne
    exact ⟨y⟩
  obtain ⟨x⟩ := hne
  obtain ⟨η, hη⟩ := QuasiSober.sober (α := J.subscheme)
    (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
  obtain ⟨U, hηU, V, g, hgsurj, -, hgflf, t, Z, jc, kc, W, hjc, hjfin, hth, hemp, -,
    hkj, hWc, hsm⟩ :=
    exists_smooth_stratification_at_generic_point (pullback.snd f J.subschemeι)
      (finitePresentation_pullback_snd hf J.subschemeι) η
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, hη⟩
  refine ⟨U, ⟨⟨η, hηU⟩⟩, V, g, hgsurj, hgflf, ?_⟩
  refine HasSmoothStratification.of_squares (u := 𝟙 V) (by simp)
    ((IsPullback.of_hasPullback (pullback.snd f J.subschemeι) (g ≫ U.ι)).paste_horiz
      (IsPullback.of_hasPullback f J.subschemeι))
    (IsPullback.of_hasPullback f (g ≫ U.ι ≫ J.subschemeι))
    (hasSmoothStratification_of_closedImmersionChain _ t Z jc kc W hjc hjfin hth hemp hkj
      hWc hsm)

/-! ### Descent to a Noetherian base -/

/-- **A morphism of finite presentation over a quasi-compact quasi-separated base is a base
change of one over a Noetherian base.** Absolute Noetherian approximation, Tag 01ZA, together
with the descent of a finitely presented morphism, Tag 01ZM. -/
@[sga "1 VIII 6.6" "partial"]
private theorem exists_noetherian_isPullback_model {X S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) (hf : FinitePresentation f) :
    ∃ (T X₀ : Scheme.{u}) (f₀ : X₀ ⟶ T) (s : S ⟶ T) (x : X ⟶ X₀),
      IsNoetherian T ∧ FinitePresentation f₀ ∧ IsPullback x f f₀ s := by
  let apx := finiteTypeApproximation (S := S)
  let _ := apx.indexPreorder
  have := apx.indexNonempty
  have := apx.indexDirected
  let c : Cone apx.ambient := Cone.mk S apx.ambientCone
  have : ∀ {i j : apx.indexTypeᵒᵈ} (e : i ⟶ j), IsAffineHom (apx.ambient.map e) :=
    apx.transition_affine
  have : ∀ i, LocallyOfFiniteType (terminal.from (apx.ambient.obj i)) :=
    apx.locallyOfFiniteType
  have : ∀ i, QuasiCompact (terminal.from (apx.ambient.obj i)) := apx.quasiCompact
  have hnoeth : ∀ i, IsNoetherian (apx.ambient.obj i) := fun i ↦
    AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from (apx.ambient.obj i)
  obtain ⟨i, X₀, f₀, x, hf₀, hpb⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall apx.ambient c
      apx.ambientCone_isLimit f hf
  exact ⟨apx.ambient.obj i, X₀, f₀, c.π.app i, x, hnoeth i, hf₀, hpb⟩

/-! ### Stacks 0H44 -/

/-- **Stacks Project, Tag 0H44.** Let `f : X ⟶ S` be a morphism of finite presentation between
quasi-compact and quasi-separated schemes. Then there are a `t ≥ 0` and closed subschemes
`S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` such that each `S_i → S` is defined by a finite type ideal sheaf,
`S₀ ⊆ S` is a thickening, each stratum `S_i ∖ S_{i+1}` carries a surjective finite locally free
morphism `T_i → S_i ∖ S_{i+1}`, and `X ×_S T_i` carries closed subschemes
`X ×_S T_i ⊇ Z_{i,0} ⊇ ⋯ ⊇ Z_{i,t_i} = ∅`, each defined by a finite type ideal sheaf, with
`Z_{i,0} ⊆ X ×_S T_i` a thickening and each `Z_{i,j} ∖ Z_{i,j+1} → T_i` smooth. -/
@[stacks 0H44]
theorem hasSmoothStratificationAfterFiniteLocallyFreeCover {X S : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) (hf : FinitePresentation f) :
    HasSmoothStratificationAfterFiniteLocallyFreeCover f := by
  obtain ⟨T, X₀, f₀, s, x, hT, hf₀, hpbX⟩ := exists_noetherian_isPullback_model f hf
  have := hT
  have hstrat := HasStratification.comap
    (P := fun (U : Scheme.{u}) (a : U ⟶ T) ↦
      ∃ (T' : Scheme.{u}) (g : T' ⟶ U), Function.Surjective g ∧
        Stacks.Morphisms.IsFiniteLocallyFree g ∧
        HasSmoothStratification (pullback.snd f₀ (g ≫ a)))
    (fun a b h ↦ coverSmoothStratification_comp f₀ a b h)
    (hasSmoothStratificationAfterFiniteLocallyFreeCover_of_isNoetherian f₀ hf₀) s
  refine HasStratification.mono ?_ hstrat
  rintro U a ⟨T', g, hgsurj, hgflf, hinner⟩
  refine ⟨T', g, hgsurj, hgflf, ?_⟩
  refine HasSmoothStratification.of_squares (u := 𝟙 T') (by simp)
    (IsPullback.of_hasPullback f₀ (g ≫ a ≫ s))
    ((IsPullback.of_hasPullback f (g ≫ a)).paste_horiz hpbX) hinner

end AlgebraicGeometry

end
