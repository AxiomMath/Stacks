module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.NagataInputs
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper extensions, their sections and their boundaries

The construction of a compactification out of two compactifiable open subschemes manipulates
*proper extensions*: an open `W` of a scheme `U`, an open `V` of an ambient scheme `Y`, an open
immersion `e : W ⟶ V` and a proper morphism `p : V ⟶ U` with `e ≫ p = W.ι`. This file collects
the elementary facts about such data that the construction uses: that `e` is a closed immersion
into suitable opens of `V`, that `p` is an isomorphism over `W` when `e` is dense, that the
*boundary* `V.ι '' (p ⁻¹' Wᶜ)` is disjoint from the range of `e`, and that these properties are
transported along admissible blowups and into fibre products.

## Main results

* `Stacks.Compactification.exists_dense_compactification_of_compactification`: a compactification
  may be shrunk to one whose interior is scheme-theoretically dense.
* `Stacks.Compactification.proper_graph_closedImmersion` and
  `Stacks.Compactification.proper_graph_restrict_closedImmersion`: the graph of a proper extension
  is a closed immersion into the fibre product, and remains one after restricting the ambient
  scheme to an open.
* `Stacks.Compactification.section_closedImmersion_of_isSeparated`,
  `Stacks.Compactification.section_closedImmersion_in_open`,
  `Stacks.Compactification.section_closedImmersion_in_fiberProduct` and
  `Stacks.Compactification.section_closedImmersion_away_from_boundary`: a section of a separated
  morphism is a closed immersion, and the section `e` of a proper extension is a closed immersion
  into any open of `V` that contains its range and lies over `W`.
* `Stacks.Compactification.isIso_restrict_of_proper_dense_open_section` and
  `Stacks.Compactification.isIso_restrict_proper_extension_image`: a proper morphism with a dense
  open section is an isomorphism over the section's target; cutting a proper extension down to
  the scheme-theoretic image of its section achieves this.
* `Stacks.Compactification.isOpenImmersion_lift_admissibleBlowup` and
  `Stacks.Compactification.transport_proper_extension_across_blowup`: proper extensions and their
  sections are carried along an admissible blowup of the ambient scheme.
* `Stacks.Compactification.blowup_separates_proper_preimages_of_open_complements`: for a cover of
  `U` by two quasi-compact opens, an admissible blowup separates the closures of the two
  corresponding boundaries.
* `Stacks.Compactification.isImmersion_fiberProduct_of_proper_open_extensions`: the fibre product
  of two proper extensions is an immersion into the fibre product of the ambient schemes.
* `Stacks.Compactification.disjoint_boundaries_from_fiberProduct`: cross-boundary separation,
  obtained from the fibre product together with an isomorphism near one boundary's closure.

## Implementation notes

The boundary of a proper extension is written out as the set `V.ι.base '' (p.base ⁻¹' Wᶜ)` and
the open complement of its closure as the bundled open `⟨(closure B)ᶜ, _⟩`; the statements that
mention it therefore open with `let` bindings reproducing those two definitions, so that the
consumers can discharge them by `rfl`.

`Stacks.Compactification.preimage_subset_of_injOn_and_range` is purely topological (indeed purely
set-theoretic) and is stated for bare functions; the scheme-level consequence is
`Stacks.Compactification.disjoint_image_boundaries_of_isIso_near_closure`.

## References

* [Stacks Project, Tag 0F40](https://stacks.math.columbia.edu/tag/0F40)
* [Stacks Project, Tag 0F3V](https://stacks.math.columbia.edu/tag/0F3V)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Compactification

/-- A quasi-compact compactification may be replaced by one whose interior is
scheme-theoretically dense: take the scheme-theoretic image of the open immersion. -/
theorem exists_dense_compactification_of_compactification
    {S X : Scheme.{u}} (f : X ⟶ S)
    (h : ∃ j : AlgebraicGeometry.CompactificationOf (Over.mk f),
      QuasiCompact j.immersion) :
    ∃ j : AlgebraicGeometry.CompactificationOf (Over.mk f),
      QuasiCompact j.immersion ∧
        AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense j.immersion.opensRange := by
  classical
  obtain ⟨j, hj⟩ := h
  let m : j.immersion.image ⟶ S := j.immersion.imageι ≫ j.toBase
  have hcomm : j.immersion ≫ j.toBase = f := by
    simp [AlgebraicGeometry.CompactificationOf.immersion,
      AlgebraicGeometry.CompactificationOf.toBase]
  have hkm : j.immersion.toImage ≫ m = f := by
    dsimp [m]
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact hcomm
  have hopen : IsOpenImmersion j.immersion.toImage :=
    AlgebraicGeometry.isOpenImmersion_toImage j.immersion (Or.inl hj)
  have hproper : IsProper m := by
    dsimp [m]
    infer_instance
  let j' : AlgebraicGeometry.CompactificationOf (Over.mk f) :=
    ⟨StructuredArrow.mk
      (Over.homMk j.immersion.toImage hkm : Over.mk f ⟶ Over.mk m),
      ⟨hopen, hproper⟩⟩
  have hqc : QuasiCompact j'.immersion := by
    change QuasiCompact j.immersion.toImage
    infer_instance
  refine ⟨j', hqc, ?_⟩
  simpa [j', AlgebraicGeometry.CompactificationOf.immersion,
    AlgebraicGeometry.CompactificationOf.space] using
    AlgebraicGeometry.isSchemeTheoreticallyDense_toImage j.immersion (Or.inl hj)

/-- Applying the underlying maps of an equality of composites to a point. -/
private theorem comp_base_apply_eq {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (H : f ≫ g = h) (x : X) : g.base (f.base x) = h.base x := by
  rw [← H]
  rfl

/-- A map whose image lies over `V` factors set-theoretically through `c ⁻¹ᵁ V`. -/
private theorem range_subset_range_ι_preimage {A X Y : Scheme.{u}} (c : X ⟶ Y) (V : Y.Opens)
    (v : A ⟶ X) (h : ∀ a, c.base (v.base a) ∈ V) :
    Set.range v.base ⊆ Set.range (c ⁻¹ᵁ V).ι.base := by
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨v.base a, h a⟩, rfl⟩

/-- A section of `p` over `W` factors through `p ⁻¹ᵁ W` as a section of `p ∣_ W`. -/
private theorem exists_section_restrict {U Z : Scheme.{u}} (W : U.Opens) (p : Z ⟶ U)
    (e : W.toScheme ⟶ Z) [IsOpenImmersion e] (he : e ≫ p = W.ι) :
    ∃ s : W.toScheme ⟶ (p ⁻¹ᵁ W).toScheme, IsOpenImmersion s ∧
      s ≫ (p ⁻¹ᵁ W).ι = e ∧ s ≫ (p ∣_ W) = 𝟙 W.toScheme := by
  have hsub := range_subset_range_ι_preimage p W e fun w => by
    rw [comp_base_apply_eq he]
    exact w.2
  refine ⟨IsOpenImmersion.lift _ e hsub, inferInstance, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  apply (cancel_mono W.ι).1
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac, he,
    Category.id_comp]

/-- If the intersection of two opens is dense, then each of them is dense. -/
theorem dense_of_dense_intersection {X : Scheme.{u}}
    (U₁ U₂ : X.Opens) (hdense : Dense (↑(U₁ ⊓ U₂) : Set X)) :
    Dense (U₁ : Set X) ∧ Dense (U₂ : Set X) :=
  ⟨hdense.mono fun _ hx => hx.1, hdense.mono fun _ hx => hx.2⟩

/-- The graph of a proper morphism `p : V ⟶ U` defined on an open `V` of a scheme `Y` separated
over `S` is a closed immersion into `U ×_S Y`: it is proper because its composite with the first
projection is `p`, and a monomorphism because its composite with the second projection is the
inclusion of `V`. -/
theorem proper_graph_closedImmersion {S U Y : Scheme.{u}}
    (f : U ⟶ S) (q : Y ⟶ S) [IsSeparated q]
    (V : Y.Opens) (p : V.toScheme ⟶ U) [IsProper p]
    (h : p ≫ f = V.ι ≫ q) :
    IsClosedImmersion (pullback.lift p V.ι h) := by
  let m : V.toScheme ⟶ pullback f q := pullback.lift p V.ι h
  have : IsProper (m ≫ pullback.fst f q) := by
    rw [show m ≫ pullback.fst f q = p from pullback.lift_fst _ _ _]
    infer_instance
  have : Mono (m ≫ pullback.snd f q) := by
    rw [show m ≫ pullback.snd f q = V.ι from pullback.lift_snd _ _ _]
    infer_instance
  exact (IsClosedImmersion.iff_isProper_and_mono m).2
    ⟨IsProper.of_comp m (pullback.fst f q), mono_of_mono m (pullback.snd f q)⟩

/-- Restricting the ambient scheme to an open `T` turns the graph of a proper morphism
`p : V ⟶ U` into a closed immersion of `V ∩ T` into `U ×_S T`, compatibly with both
projections. -/
theorem proper_graph_restrict_closedImmersion {S U Y : Scheme.{u}}
    (f : U ⟶ S) (q : Y ⟶ S) [IsSeparated q]
    (V : Y.Opens) (p : V.toScheme ⟶ U) [IsProper p]
    (h : p ≫ f = V.ι ≫ q) (T : Y.Opens) :
    ∃ g : (V.ι ⁻¹ᵁ T).toScheme ⟶ pullback f (T.ι ≫ q),
      IsClosedImmersion g ∧
      g ≫ pullback.fst f (T.ι ≫ q) = (V.ι ⁻¹ᵁ T).ι ≫ p ∧
      g ≫ pullback.snd f (T.ι ≫ q) = V.ι ∣_ T := by
  let m : V.toScheme ⟶ pullback f q := pullback.lift p V.ι h
  have : IsClosedImmersion m := proper_graph_closedImmersion f q V p h
  let R : (pullback f q).Opens := (pullback.snd f q) ⁻¹ᵁ T
  have hEq : m ⁻¹ᵁ R = V.ι ⁻¹ᵁ T := by
    ext x
    change (m ≫ pullback.snd f q).base x ∈ (T : Set Y) ↔
      V.ι.base x ∈ (T : Set Y)
    rw [show m ≫ pullback.snd f q = V.ι from pullback.lift_snd _ _ _]
  let β : (V.ι ⁻¹ᵁ T).toScheme ≅ (m ⁻¹ᵁ R).toScheme :=
    (V.toScheme).isoOfEq hEq.symm
  let α : pullback f (T.ι ≫ q) ≅ R.toScheme :=
    (pullbackLeftPullbackSndIso f q T.ι).symm ≪≫
      pullbackRestrictIsoRestrict (pullback.snd f q) T
  let g : (V.ι ⁻¹ᵁ T).toScheme ⟶ pullback f (T.ι ≫ q) :=
    β.hom ≫ (m ∣_ R) ≫ α.inv
  have : IsClosedImmersion g := by dsimp [g]; infer_instance
  refine ⟨g, inferInstance, ?_, ?_⟩
  · have hαfst : α.inv ≫ pullback.fst f (T.ι ≫ q) =
        R.ι ≫ pullback.fst f q := by
      dsimp [α]
      simp only [Category.assoc,
        pullbackLeftPullbackSndIso_hom_fst]
      simpa only [Category.assoc] using congrArg
        (fun z : R.toScheme ⟶ pullback f q => z ≫ pullback.fst f q)
        (pullbackRestrictIsoRestrict_inv_fst (pullback.snd f q) T)
    calc
      g ≫ pullback.fst f (T.ι ≫ q) =
          β.hom ≫ (m ∣_ R) ≫ (R.ι ≫ pullback.fst f q) := by
            simp only [g, Category.assoc, hαfst]
      _ = (V.ι ⁻¹ᵁ T).ι ≫ p := by
        simp [β, m]
  · have hαsnd : α.inv ≫ pullback.snd f (T.ι ≫ q) =
        pullback.snd f q ∣_ T := by
      dsimp [α, morphismRestrict]
      simp only [Category.assoc,
        pullbackLeftPullbackSndIso_hom_snd]
    calc
      g ≫ pullback.snd f (T.ι ≫ q) =
          β.hom ≫ (m ∣_ R) ≫ (pullback.snd f q ∣_ T) := by
            simp only [g, Category.assoc, hαsnd]
      _ = V.ι ∣_ T := by
        apply (cancel_mono T.ι).1
        simp [β, R, m, Category.assoc, morphismRestrict_ι]

/-- A section of a separated morphism is a closed immersion: it is the base change of the
diagonal along the graph of the section. -/
@[ega "I 5.4.2" "special case", ega "I 5.4.6", sga "3 VIB 5.6.3" "(i) ⇒ (ii)"]
theorem section_closedImmersion_of_isSeparated {T U : Scheme.{u}}
    (p : T ⟶ U) [IsSeparated p] (s : U ⟶ T)
    (hs : s ≫ p = 𝟙 U) : IsClosedImmersion s := by
  let graph : U ⟶ pullback (s ≫ p) p :=
    pullback.lift (𝟙 U) s (Category.id_comp (s ≫ p))
  have hgraph : IsClosedImmersion graph := by infer_instance
  have : IsIso (pullback.snd (s ≫ p) p) := by rw [hs]; infer_instance
  have hcomp : IsClosedImmersion (graph ≫ pullback.snd (s ≫ p) p) := inferInstance
  rwa [show graph ≫ pullback.snd (s ≫ p) p = s from pullback.lift_snd _ _ _] at hcomp

/-- The section `e` of a proper morphism `p : Z ⟶ U` defined over an open `W` is a closed
immersion into any open `T` of `Z` which contains the range of `e` and lies over `W`. -/
theorem section_closedImmersion_in_open {U Z : Scheme.{u}}
    (W : U.Opens) (p : Z ⟶ U) [IsProper p]
    (e : W.toScheme ⟶ Z) [IsOpenImmersion e] (he : e ≫ p = W.ι)
    (T : Z.Opens) (hET : Set.range e.base ⊆ (T : Set Z))
    (hTW : T ≤ p ⁻¹ᵁ W) :
    IsClosedImmersion (IsOpenImmersion.lift T.ι e (by simpa using hET)) := by
  obtain ⟨s, -, hse, hs⟩ := exists_section_restrict W p e he
  have hsclosed : IsClosedImmersion s :=
    section_closedImmersion_of_isSeparated (p ∣_ W) s hs
  let eT : W.toScheme ⟶ T.toScheme :=
    IsOpenImmersion.lift T.ι e (by simpa using hET)
  let i : T.toScheme ⟶ (p ⁻¹ᵁ W).toScheme := Z.homOfLE hTW
  have heTi : eT ≫ i = s := by
    apply (cancel_mono (p ⁻¹ᵁ W).ι).1
    calc
      (eT ≫ i) ≫ (p ⁻¹ᵁ W).ι = eT ≫ T.ι := by
        rw [Category.assoc, Scheme.homOfLE_ι]
      _ = e := IsOpenImmersion.lift_fac _ _ _
      _ = s ≫ (p ⁻¹ᵁ W).ι := hse.symm
  have : IsClosedImmersion (eT ≫ i) := by rw [heTi]; exact hsclosed
  exact IsClosedImmersion.of_comp eT i

/-- Density of a dense map persists after factoring it through an open `N` of its target. -/
private theorem denseRange_of_comp_ι_eq {A Y : Scheme.{u}} (N : Y.Opens) (e : A ⟶ Y)
    (l : A ⟶ N.toScheme) (hl : l ≫ N.ι = e) (hdense : DenseRange e) : DenseRange l := by
  have hpre : N.ι.base ⁻¹' Set.range e.base = Set.range l.base := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, N.ι.isOpenEmbedding.injective (by rw [comp_base_apply_eq hl, ha])⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, (comp_base_apply_eq hl a).symm⟩
  rw [denseRange_iff_closure_range]
  have hclosed := N.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    N.ι.continuous (Set.range e.base)
  rw [hpre, hdense.closure_range] at hclosed
  simpa using hclosed.symm

/-- A proper map with a dense open section is an isomorphism above the
section's open target. -/
theorem isIso_restrict_of_proper_dense_open_section
    {U Z : Scheme.{u}} (W : U.Opens) (p : Z ⟶ U) [IsProper p]
    (e : W.toScheme ⟶ Z) [IsOpenImmersion e]
    (he : e ≫ p = W.ι) (hdense : DenseRange e) : IsIso (p ∣_ W) := by
  let O : Z.Opens := p ⁻¹ᵁ W
  obtain ⟨s, _, hsO, hs⟩ := exists_section_restrict W p e he
  have : IsClosedImmersion s :=
    section_closedImmersion_of_isSeparated (p ∣_ W) s hs
  have hdenseS : DenseRange s := denseRange_of_comp_ι_eq O e s hsO hdense
  have hsurj : Surjective s := by
    rw [surjective_iff]
    have hclosed : IsClosed (Set.range s.base) := s.isClosedEmbedding.isClosed_range
    exact Set.range_eq_univ.mp (by
      rw [← hclosed.closure_eq]
      exact hdenseS.closure_range)
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).2
    ⟨inferInstance, hsurj⟩
  have hcomp : IsIso (s ≫ (p ∣_ W)) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s (p ∣_ W)

/-- Density of an open immersion persists after restricting its target to an
open containing its image. -/
theorem denseRange_lift_open_of_denseRange
    {A Y : Scheme.{u}} (N : Y.Opens) (e : A ⟶ Y)
    [IsOpenImmersion e] (hdense : DenseRange e)
    (hsub : Set.range e.base ⊆ Set.range N.ι.base) :
    DenseRange (IsOpenImmersion.lift N.ι e hsub) :=
  denseRange_of_comp_ι_eq N e _ (IsOpenImmersion.lift_fac _ _ _) hdense

/-- Cutting a proper extension to the scheme-theoretic image of its open
section makes the extension an isomorphism above the section's target. -/
theorem isIso_restrict_proper_extension_image
    {U Y : Scheme.{u}} (W : U.Opens) (V : Y.Opens)
    (e : W.toScheme ⟶ V.toScheme) [IsOpenImmersion e]
    (p : V.toScheme ⟶ U) [IsProper p]
    (he : e ≫ p = W.ι)
    (hqc : QuasiCompact (e ≫ V.ι)) :
    let a : W.toScheme ⟶ Y := e ≫ V.ι
    let i : a.image ⟶ Y := a.imageι
    let _ : a.image.Opens := i ⁻¹ᵁ V
    IsIso (((i ∣_ V) ≫ p) ∣_ W) := by
  let a : W.toScheme ⟶ Y := e ≫ V.ι
  let i : a.image ⟶ Y := a.imageι
  let O : a.image.Opens := i ⁻¹ᵁ V
  let k : O.toScheme ⟶ V.toScheme := i ∣_ V
  let pE : O.toScheme ⟶ U := k ≫ p
  let : QuasiCompact a := hqc
  have : IsOpenImmersion a := by dsimp [a]; infer_instance
  have : IsOpenImmersion a.toImage :=
    AlgebraicGeometry.isOpenImmersion_toImage a (Or.inl inferInstance)
  have hsub : Set.range a.toImage.base ⊆ Set.range O.ι.base :=
    range_subset_range_ι_preimage i V a.toImage fun x => by
      rw [comp_base_apply_eq (Scheme.Hom.toImage_imageι a)]
      exact (e.base x).2
  let eE : W.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι a.toImage hsub
  have heEO : eE ≫ O.ι = a.toImage := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (eE ≫ O.ι) := by rw [heEO]; infer_instance
  have : IsOpenImmersion eE := IsOpenImmersion.of_comp eE O.ι
  have hdenseE : DenseRange eE :=
    denseRange_lift_open_of_denseRange O a.toImage a.toImage.denseRange hsub
  have : IsProper pE := by dsimp [pE, k, i]; infer_instance
  have heEk : eE ≫ k = e := by
    apply (cancel_mono V.ι).1
    calc
      (eE ≫ k) ≫ V.ι = eE ≫ O.ι ≫ i := by
        rw [Category.assoc, morphismRestrict_ι]
      _ = a.toImage ≫ i := by rw [← Category.assoc, heEO]
      _ = a := Scheme.Hom.toImage_imageι a
      _ = e ≫ V.ι := rfl
  have heEp : eE ≫ pE = W.ι := by
    change eE ≫ (k ≫ p) = W.ι
    rw [← Category.assoc, heEk]
    exact he
  exact isIso_restrict_of_proper_dense_open_section W pE eE heEp hdenseE

/-- The section of a proper extension lifts to a closed immersion into the fibre product
`U ×_S T`, for an open `T` of the ambient scheme containing the section's range and lying
over `W`. -/
theorem section_closedImmersion_in_fiberProduct {S U Y : Scheme.{u}}
    (f : U ⟶ S) (q : Y ⟶ S) [IsSeparated q]
    (W : U.Opens) (V T : Y.Opens)
    (e : W.toScheme ⟶ V.toScheme) [IsOpenImmersion e]
    (p : V.toScheme ⟶ U) [IsProper p] (he : e ≫ p = W.ι)
    (h : p ≫ f = V.ι ≫ q)
    (gT : W.toScheme ⟶ T.toScheme)
    (hgT : gT ≫ T.ι = e ≫ V.ι)
    (hcross : W.ι ≫ f = gT ≫ (T.ι ≫ q))
    (hET : Set.range e.base ⊆ Set.range (V.ι ⁻¹ᵁ T).ι)
    (hTW : V.ι ⁻¹ᵁ T ≤ p ⁻¹ᵁ W) :
    IsClosedImmersion (pullback.lift W.ι gT hcross) := by
  let s : W.toScheme ⟶ (V.ι ⁻¹ᵁ T).toScheme :=
    IsOpenImmersion.lift (V.ι ⁻¹ᵁ T).ι e hET
  have : IsClosedImmersion s :=
    section_closedImmersion_in_open W p e he (V.ι ⁻¹ᵁ T)
      (by simpa only [Scheme.Opens.range_ι] using hET) hTW
  obtain ⟨g, hg, hgfst, hgsnd⟩ :=
    proper_graph_restrict_closedImmersion f q V p h T
  let : IsClosedImmersion g := hg
  have hsg : s ≫ g = pullback.lift W.ι gT hcross := by
    apply pullback.hom_ext
    · calc
        s ≫ g ≫ pullback.fst f (T.ι ≫ q) =
            s ≫ (V.ι ⁻¹ᵁ T).ι ≫ p := by
              simpa only [Category.assoc] using congrArg (fun k => s ≫ k) hgfst
        _ = e ≫ p := by rw [← Category.assoc, IsOpenImmersion.lift_fac]
        _ = W.ι := he
        _ = pullback.lift W.ι gT hcross ≫ pullback.fst f (T.ι ≫ q) :=
          (pullback.lift_fst _ _ _).symm
    · have hsgT : s ≫ (V.ι ∣_ T) = gT := by
        apply (cancel_mono T.ι).1
        calc
          (s ≫ (V.ι ∣_ T)) ≫ T.ι =
              s ≫ (V.ι ⁻¹ᵁ T).ι ≫ V.ι := by
                rw [Category.assoc, morphismRestrict_ι]
          _ = e ≫ V.ι := by rw [← Category.assoc, IsOpenImmersion.lift_fac]
          _ = gT ≫ T.ι := hgT.symm
      calc
        s ≫ g ≫ pullback.snd f (T.ι ≫ q) = s ≫ (V.ι ∣_ T) := by
          simpa only [Category.assoc] using congrArg (fun k => s ≫ k) hgsnd
        _ = gT := hsgT
        _ = pullback.lift W.ι gT hcross ≫ pullback.snd f (T.ι ≫ q) :=
          (pullback.lift_snd _ _ _).symm
  rw [← hsg]
  infer_instance

/-- The section of a proper extension is a closed immersion into the open complement of the
closure of the boundary, as soon as its range misses that closure. -/
theorem section_closedImmersion_away_from_boundary {U Y : Scheme.{u}}
    (W : U.Opens) (V : Y.Opens)
    (e : W.toScheme ⟶ V.toScheme) [IsOpenImmersion e]
    (p : V.toScheme ⟶ U) [IsProper p] (he : e ≫ p = W.ι)
    (hsection : Disjoint (Set.range (e ≫ V.ι).base)
      (closure (V.ι.base '' (p.base ⁻¹' ((W : Set U)ᶜ))))) :
    let B : Set Y := V.ι.base '' (p.base ⁻¹' ((W : Set U)ᶜ))
    let T : Y.Opens := ⟨(closure B)ᶜ, isClosed_closure.isOpen_compl⟩
    ∃ hET : Set.range e.base ⊆ Set.range (V.ι ⁻¹ᵁ T).ι,
      IsClosedImmersion (IsOpenImmersion.lift (V.ι ⁻¹ᵁ T).ι e hET) := by
  let B : Set Y := V.ι.base '' (p.base ⁻¹' ((W : Set U)ᶜ))
  let T : Y.Opens := ⟨(closure B)ᶜ, isClosed_closure.isOpen_compl⟩
  have hET : Set.range e.base ⊆ (V.ι ⁻¹ᵁ T : Set V.toScheme) := by
    rintro y ⟨w, rfl⟩
    change V.ι.base (e.base w) ∉ closure B
    exact Set.disjoint_left.mp hsection ⟨w, rfl⟩
  have hTW : V.ι ⁻¹ᵁ T ≤ p ⁻¹ᵁ W := by
    intro y hy
    change p.base y ∈ (W : Set U)
    by_contra hnot
    exact (hy : V.ι.base y ∉ closure B) (subset_closure ⟨y, hnot, rfl⟩)
  exact ⟨by simpa only [Scheme.Opens.range_ι] using hET,
    section_closedImmersion_in_open W p e he (V.ι ⁻¹ᵁ T) hET hTW⟩

/-- The source of a proper morphism to a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_isProper {X S : Scheme.{u}}
    (f : X ⟶ S) [IsNoetherian S] [IsProper f] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  exact ⟨⟩

/-- The lift of an open immersion through a blowup that is trivial over its
range is again an open immersion. -/
theorem isOpenImmersion_lift_admissibleBlowup
    {U X X' : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (b : X' ⟶ X) (v : U ⟶ X')
    (hb : Stacks.Blowup.IsAdmissibleBlowup u.opensRange b)
    (hvb : v ≫ b = u) : IsOpenImmersion v := by
  let O : X'.Opens := b ⁻¹ᵁ u.opensRange
  have hrange : Set.range v.base ⊆ Set.range O.ι.base :=
    range_subset_range_ι_preimage b u.opensRange v fun y => by
      rw [comp_base_apply_eq hvb]
      exact ⟨y, rfl⟩
  let l : U ⟶ O.toScheme := IsOpenImmersion.lift O.ι v hrange
  let m : O.toScheme ⟶ u.opensRange.toScheme := b ∣_ u.opensRange
  have : IsIso m :=
    AlgebraicGeometry.isIso_morphismRestrict_of_isAdmissibleBlowup u.opensRange b hb
  have : IsOpenImmersion m := IsOpenImmersion.of_isIso _
  have hlm : (l ≫ m) ≫ u.opensRange.ι = u :=
    calc
      (l ≫ m) ≫ u.opensRange.ι = l ≫ O.ι ≫ b := by
        rw [Category.assoc, morphismRestrict_ι]
      _ = v ≫ b := by rw [← Category.assoc, IsOpenImmersion.lift_fac]
      _ = u := hvb
  have : IsOpenImmersion ((l ≫ m) ≫ u.opensRange.ι) := by rw [hlm]; infer_instance
  have : IsOpenImmersion (l ≫ m) :=
    IsOpenImmersion.of_comp (l ≫ m) u.opensRange.ι
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l m
  rw [← IsOpenImmersion.lift_fac O.ι v hrange]
  infer_instance

/-- A proper extension of `W` inside `V` is carried along a `V`-admissible blowup `c : Y' ⟶ Y`
to a proper extension inside the inverse image of `V`, isomorphically and compatibly with all
the structure morphisms. -/
theorem transport_proper_extension_across_blowup {U Y Y' : Scheme.{u}}
    (W : U.Opens) (V : Y.Opens)
    (e : W.toScheme ⟶ V.toScheme) [IsOpenImmersion e]
    (p : V.toScheme ⟶ U) [IsProper p] (he : e ≫ p = W.ι)
    (c : Y' ⟶ Y) (hc : Stacks.Blowup.IsAdmissibleBlowup V c) :
    ∃ (V' : Y'.Opens) (k : V'.toScheme ⟶ V.toScheme)
      (e' : W.toScheme ⟶ V'.toScheme)
      (p' : V'.toScheme ⟶ U),
      V' = c ⁻¹ᵁ V ∧ IsIso k ∧ k ≫ V.ι = V'.ι ≫ c ∧
      e' ≫ k = e ∧ p' = k ≫ p ∧
      IsOpenImmersion e' ∧ IsProper p' ∧ e' ≫ p' = W.ι ∧
      e' ≫ V'.ι ≫ c = e ≫ V.ι := by
  let V' : Y'.Opens := c ⁻¹ᵁ V
  let cV : V'.toScheme ⟶ V.toScheme := c ∣_ V
  let : IsIso cV := AlgebraicGeometry.isIso_morphismRestrict_of_isAdmissibleBlowup V c hc
  let e' : W.toScheme ⟶ V'.toScheme := e ≫ inv cV
  let p' : V'.toScheme ⟶ U := cV ≫ p
  have : IsOpenImmersion e' := by dsimp [e']; infer_instance
  have : IsProper p' := by dsimp [p']; infer_instance
  have he' : e' ≫ p' = W.ι := by simp [e', p', he]
  have hcomm : e' ≫ V'.ι ≫ c = e ≫ V.ι := by
    calc
      e' ≫ V'.ι ≫ c = e' ≫ (V'.ι ≫ c) := by simp only
      _ = e' ≫ (cV ≫ V.ι) := by rw [morphismRestrict_ι c V]
      _ = e ≫ V.ι := by simp [e', Category.assoc]
  have he'k : e' ≫ cV = e := by simp [e', Category.assoc]
  exact ⟨V', cV, e', p', rfl, inferInstance,
    morphismRestrict_ι c V, he'k, rfl,
    inferInstance, inferInstance, he', hcomm⟩

/-- The boundary of a proper extension is carried to the boundary of its transport along a
blowup: the inverse image of the image of `p ⁻¹' T` is the image of `p' ⁻¹' T`. -/
theorem preimage_image_transport {U Y Y' : Scheme.{u}}
    (V : Y.Opens) (V' : Y'.Opens) (c : Y' ⟶ Y)
    (hV' : V' = c ⁻¹ᵁ V) (k : V'.toScheme ⟶ V.toScheme) [IsIso k]
    (hk : k ≫ V.ι = V'.ι ≫ c)
    (p : V.toScheme ⟶ U) (p' : V'.toScheme ⟶ U) (hp : p' = k ≫ p)
    (T : Set U) :
    c.base ⁻¹' (V.ι.base '' (p.base ⁻¹' T)) =
      V'.ι.base '' (p'.base ⁻¹' T) := by
  subst hp
  ext x
  constructor
  · rintro ⟨v, hvT, hvx⟩
    have hxV : c.base x ∈ (V : Set Y) := by
      rw [← hvx]
      exact v.2
    have hxV' : x ∈ (V' : Set Y') := by
      rw [hV']
      exact hxV
    let x' : V'.toScheme := ⟨x, hxV'⟩
    have hkx : k.base x' = v := by
      apply V.ι.isOpenEmbedding.injective
      exact (comp_base_apply_eq hk x').trans hvx.symm
    refine ⟨x', ?_, rfl⟩
    change p.base (k.base x') ∈ T
    rwa [hkx]
  · rintro ⟨x', hx'T, rfl⟩
    refine ⟨k.base x', ?_, comp_base_apply_eq hk x'⟩
    exact hx'T

/-- An open subscheme which is a compact space is a compact subset. -/
private theorem isCompact_of_compactSpace_toScheme {X : Scheme.{u}} (U : X.Opens)
    [CompactSpace U.toScheme] : IsCompact (U : Set X) := by
  simpa [Scheme.Hom.coe_opensRange] using isCompact_univ.image U.ι.continuous

/-- For a cover of a quasi-compact quasi-separated scheme by two quasi-compact opens, the
inverse images of the two complements are disjoint closed constructible subsets. -/
theorem preimage_complements_closed_constructible_disjoint
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (p : Y ⟶ X)
    (U₁ U₂ : X.Opens) [QuasiCompact U₁.ι] [QuasiCompact U₂.ι]
    (hcover : U₁ ⊔ U₂ = ⊤) :
    IsClosed (p.base ⁻¹' ((U₁ : Set X)ᶜ)) ∧
      IsClosed (p.base ⁻¹' ((U₂ : Set X)ᶜ)) ∧
      Topology.IsConstructible (p.base ⁻¹' ((U₁ : Set X)ᶜ)) ∧
      Topology.IsConstructible (p.base ⁻¹' ((U₂ : Set X)ᶜ)) ∧
      Disjoint (p.base ⁻¹' ((U₁ : Set X)ᶜ)) (p.base ⁻¹' ((U₂ : Set X)ᶜ)) := by
  have hclosed₁ : IsClosed ((U₁ : Set X)ᶜ) := U₁.isOpen.isClosed_compl
  have hclosed₂ : IsClosed ((U₂ : Set X)ᶜ) := U₂.isOpen.isClosed_compl
  have hconstructible : ∀ (U' : X.Opens) [QuasiCompact U'.ι],
      Topology.IsConstructible ((U' : Set X)ᶜ) := fun U' _ => by
    have : CompactSpace U'.toScheme := (quasiCompact_iff_compactSpace U'.ι).mp inferInstance
    exact ((isCompact_of_compactSpace_toScheme U').isConstructible U'.isOpen).compl
  have hdisjoint : Disjoint ((U₁ : Set X)ᶜ) ((U₂ : Set X)ᶜ) := by
    apply Set.disjoint_left.mpr
    intro x hx₁ hx₂
    have hx : x ∈ U₁ ⊔ U₂ := by simp [hcover]
    rcases hx with hx | hx
    · exact hx₁ hx
    · exact hx₂ hx
  exact ⟨hclosed₁.preimage p.continuous, hclosed₂.preimage p.continuous,
    p.isConstructible_preimage (hconstructible U₁),
    p.isConstructible_preimage (hconstructible U₂), hdisjoint.preimage _⟩

/-- Given a cover of `U` by two quasi-compact opens, a `V`-admissible blowup of the ambient
scheme separates the closures of the two boundaries of a proper extension. -/
theorem blowup_separates_proper_preimages_of_open_complements
    {S U Y : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (V : Y.Opens) (p : V.toScheme ⟶ U) (hp : IsProper p)
    (U₁ U₂ : U.Opens) [QuasiCompact U₁.ι] [QuasiCompact U₂.ι]
    (hcover : U₁ ⊔ U₂ = ⊤) :
    ∃ (Y' : Scheme.{u}) (b : Y' ⟶ Y),
      Stacks.Blowup.IsAdmissibleBlowup V b ∧
        Disjoint
          (closure (b.base ⁻¹' (V.ι.base ''
            (p.base ⁻¹' ((U₁ : Set U)ᶜ)))))
          (closure (b.base ⁻¹' (V.ι.base ''
            (p.base ⁻¹' ((U₂ : Set U)ᶜ))))) := by
  let : IsProper p := hp
  have : CompactSpace V.toScheme := (quasiCompact_iff_compactSpace p).mp inferInstance
  have hVcompact := isCompact_of_compactSpace_toScheme V
  have hsets := preimage_complements_closed_constructible_disjoint p U₁ U₂ hcover
  exact AlgebraicGeometry.exists_isAdmissibleBlowup_disjoint_closures
    V hVcompact _ _ hsets.1 hsets.2.1 hsets.2.2.1 hsets.2.2.2.1 hsets.2.2.2.2

/-- The range of the section of a proper extension is disjoint from the closure of the
boundary: it is an open set disjoint from the boundary itself. -/
theorem section_range_disjoint_boundary_closure
    {U Y : Scheme.{u}} (W : U.Opens) (V : Y.Opens)
    (e : W.toScheme ⟶ V.toScheme) (p : V.toScheme ⟶ U)
    [IsOpenImmersion e] (he : e ≫ p = W.ι) :
    Disjoint (Set.range (e ≫ V.ι).base)
      (closure (V.ι.base '' (p.base ⁻¹' ((W : Set U)ᶜ)))) := by
  let E : Set Y := Set.range (e ≫ V.ι).base
  let B : Set Y := V.ι.base '' (p.base ⁻¹' ((W : Set U)ᶜ))
  have hE : IsOpen E := (e ≫ V.ι).isOpenEmbedding.isOpen_range
  have hEB : Disjoint E B := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ ⟨z, hzW, hzY⟩
    have hzY' : V.ι z = V.ι (e.base x) := by
      simpa only [Scheme.Hom.comp_base, TopCat.hom_comp,
        ContinuousMap.coe_comp, Function.comp_apply] using hzY
    have hzx : z = e.base x := V.ι.isOpenEmbedding.injective hzY'
    exact hzW (by rw [hzx, comp_base_apply_eq he]; exact x.2)
  exact hEB.closure_right hE

/-- The part of `V` lying in the open complement of the closure of the boundary lies over
`W`. -/
theorem open_compl_closure_boundary_le_preimage
    {U Y : Scheme.{u}} (W : U.Opens) (V : Y.Opens)
    (p : V.toScheme ⟶ U) :
    let B : Set Y := V.ι.base '' (p.base ⁻¹' ((W : Set U)ᶜ))
    let T : Y.Opens := ⟨(closure B)ᶜ, isClosed_closure.isOpen_compl⟩
    V.ι ⁻¹ᵁ T ≤ p ⁻¹ᵁ W := by
  dsimp
  intro y hy
  change p.base y ∈ (W : Set U)
  by_contra hnot
  have hB : V.ι.base y ∈
      V.ι.base '' (p.base ⁻¹' ((W : Set U)ᶜ)) := ⟨y, hnot, rfl⟩
  exact hy (subset_closure hB)

/-- The fibre product of two proper open extensions sits as an immersion in
the fibre product of their ambient schemes. -/
theorem isImmersion_fiberProduct_of_proper_open_extensions
    {S U Y₁ Y₂ : Scheme.{u}} (f : U ⟶ S) [IsSeparated f]
    (Q₁ : Y₁ ⟶ S) (Q₂ : Y₂ ⟶ S)
    (V₁ : Y₁.Opens) (V₂ : Y₂.Opens)
    (p₁ : V₁.toScheme ⟶ U) (p₂ : V₂.toScheme ⟶ U)
    (hbase₁ : p₁ ≫ f = V₁.ι ≫ Q₁)
    (hbase₂ : p₂ ≫ f = V₂.ι ≫ Q₂)
    (h : (pullback.fst p₁ p₂ ≫ V₁.ι) ≫ Q₁ =
      (pullback.snd p₁ p₂ ≫ V₂.ι) ≫ Q₂) :
    IsImmersion
      (pullback.lift
        (pullback.fst p₁ p₂ ≫ V₁.ι)
        (pullback.snd p₁ p₂ ≫ V₂.ι) h) := by
  let a : pullback p₁ p₂ ⟶ pullback Q₁ Q₂ :=
    pullback.lift (pullback.fst p₁ p₂ ≫ V₁.ι)
      (pullback.snd p₁ p₂ ≫ V₂.ι) h
  let m : pullback p₁ p₂ ⟶ pullback (p₁ ≫ f) (p₂ ≫ f) :=
    pullback.mapDesc p₁ p₂ f
  let e := pullback.congrHom hbase₁ hbase₂
  let n : pullback (V₁.ι ≫ Q₁) (V₂.ι ≫ Q₂) ⟶ pullback Q₁ Q₂ :=
    pullback.map (V₁.ι ≫ Q₁) (V₂.ι ≫ Q₂) Q₁ Q₂
      V₁.ι V₂.ι (𝟙 S) (by simp) (by simp)
  have : IsClosedImmersion m := by dsimp [m]; infer_instance
  have : IsOpenImmersion n := by dsimp [n]; infer_instance
  have : IsImmersion (m ≫ e.hom ≫ n) := inferInstance
  have hn₁ : n ≫ pullback.fst Q₁ Q₂ =
      pullback.fst (V₁.ι ≫ Q₁) (V₂.ι ≫ Q₂) ≫ V₁.ι := by
    simp only [n, pullback.map, pullback.lift_fst]
  have hn₂ : n ≫ pullback.snd Q₁ Q₂ =
      pullback.snd (V₁.ι ≫ Q₁) (V₂.ι ≫ Q₂) ≫ V₂.ι := by
    simp only [n, pullback.map, pullback.lift_snd]
  have he₁ : e.hom ≫ pullback.fst (V₁.ι ≫ Q₁) (V₂.ι ≫ Q₂) =
      pullback.fst (p₁ ≫ f) (p₂ ≫ f) := by
    simp only [e, pullback.congrHom_hom, pullback.map,
      pullback.lift_fst, Category.comp_id]
  have he₂ : e.hom ≫ pullback.snd (V₁.ι ≫ Q₁) (V₂.ι ≫ Q₂) =
      pullback.snd (p₁ ≫ f) (p₂ ≫ f) := by
    simp only [e, pullback.congrHom_hom, pullback.map,
      pullback.lift_snd, Category.comp_id]
  have hm₁ : m ≫ pullback.fst (p₁ ≫ f) (p₂ ≫ f) =
      pullback.fst p₁ p₂ := by
    simp only [m, pullback.mapDesc, pullback.map,
      pullback.lift_fst, Category.comp_id]
  have hm₂ : m ≫ pullback.snd (p₁ ≫ f) (p₂ ≫ f) =
      pullback.snd p₁ p₂ := by
    simp only [m, pullback.mapDesc, pullback.map,
      pullback.lift_snd, Category.comp_id]
  have heq : m ≫ e.hom ≫ n = a := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hn₁, reassoc_of% he₁, reassoc_of% hm₁]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, hn₂, reassoc_of% he₂, reassoc_of% hm₂]
      exact (pullback.lift_snd _ _ _).symm
  change IsImmersion a
  rw [← heq]
  infer_instance

/-- The closed image of one boundary piece excludes the other boundary
piece, provided the first projection pulls closure back to closure. -/
theorem disjoint_cross_boundary_of_closure_preimage
    {X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (A : Set X) (B C : Set Y) (hB : IsClosed B) (hBC : Disjoint B C)
    (hAB : p.base ⁻¹' A ⊆ q.base ⁻¹' B)
    (hclosure : p.base ⁻¹' closure A ⊆ closure (p.base ⁻¹' A)) :
    Disjoint (p.base ⁻¹' closure A) (q.base ⁻¹' C) :=
  (hBC.preimage _).mono_left <|
    hclosure.trans <| (closure_mono hAB).trans (hB.preimage q.continuous).closure_subset

/-- An isomorphism above a neighbourhood of a closure pulls that closure
back inside the closure of the pulled-back set. -/
theorem preimage_closure_subset_of_isIso_restrict
    {X Y : Scheme.{u}} (p : X ⟶ Y) (N : Y.Opens) (A : Set Y)
    (hAN : closure A ⊆ (N : Set Y)) [IsIso (p ∣_ N)] :
    p.base ⁻¹' closure A ⊆ closure (p.base ⁻¹' A) := by
  let O : X.Opens := p ⁻¹ᵁ N
  let r : O.toScheme ⟶ N.toScheme := p ∣_ N
  have : IsOpenImmersion r := by dsimp [r]; infer_instance
  intro x hx
  have hxO : x ∈ (O : Set X) := hAN hx
  let y : O.toScheme := ⟨x, hxO⟩
  have hpy : N.ι.base (r.base y) = p.base x := comp_base_apply_eq (morphismRestrict_ι p N) y
  have hN : r.base y ∈ N.ι.base ⁻¹' closure A := by
    change N.ι.base (r.base y) ∈ closure A
    rw [hpy]
    exact hx
  have hNcl : r.base y ∈ closure (N.ι.base ⁻¹' A) :=
    N.ι.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage hN
  have hOcl : y ∈ closure (r.base ⁻¹' (N.ι.base ⁻¹' A)) :=
    r.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage hNcl
  have hXcl : O.ι.base y ∈
      closure (O.ι.base '' (r.base ⁻¹' (N.ι.base ⁻¹' A))) :=
    image_closure_subset_closure_image O.ι.continuous ⟨y, hOcl, rfl⟩
  have hsub : O.ι.base '' (r.base ⁻¹' (N.ι.base ⁻¹' A)) ⊆
      p.base ⁻¹' A := by
    rintro z ⟨z', hz', rfl⟩
    change p.base (O.ι.base z') ∈ A
    exact comp_base_apply_eq (morphismRestrict_ι p N) z' ▸ hz'
  exact closure_mono hsub hXcl

/-- An isomorphism on an open has at most one point over each point of that open. -/
theorem injOn_preimage_of_isIso_restrict
    {X Y : Scheme.{u}} (p : X ⟶ Y) (N : Y.Opens) [IsIso (p ∣_ N)] :
    Set.InjOn p.base (p.base ⁻¹' (N : Set Y)) := by
  intro x hx y hy hxy
  let O := p ⁻¹ᵁ N
  let x' : O.toScheme := ⟨x, hx⟩
  let y' : O.toScheme := ⟨y, hy⟩
  have hxy' : (p ∣_ N).base x' = (p ∣_ N).base y' := by
    apply N.ι.isOpenEmbedding.injective
    rw [comp_base_apply_eq (morphismRestrict_ι p N) x',
      comp_base_apply_eq (morphismRestrict_ι p N) y']
    exact hxy
  exact congrArg Subtype.val ((p ∣_ N).isOpenEmbedding.injective hxy')

/-- If the first projection is injective near a boundary set, points of the
scheme-theoretic image over that set come from any family covering it. -/
theorem preimage_subset_of_injOn_and_range
    {X Y Z W : Type*} (p : Z → X) (q : Z → Y) (a : W → Z)
    (B : Set X) (C : Set Y) (N : Set X)
    (hBN : B ⊆ N) (hinj : Set.InjOn p (p ⁻¹' N))
    (hsurj : B ⊆ Set.range (p ∘ a))
    (hmap : a ⁻¹' (p ⁻¹' B) ⊆ a ⁻¹' (q ⁻¹' C)) :
    p ⁻¹' B ⊆ q ⁻¹' C := by
  intro z hz
  obtain ⟨w, hw⟩ := hsurj hz
  have hpa : p (a w) = p z := hw
  have haw : p (a w) ∈ B := by rw [hpa]; exact hz
  have haz : a w = z := hinj (hBN haw) (hBN hz) hpa
  rw [← haz]
  exact hmap haw

/-- Boundary separation on the second factor pulls back to the image once the
first projection is an isomorphism near the closure of its boundary. -/
theorem disjoint_image_boundaries_of_isIso_near_closure
    {X Y Z W : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y) (a : W ⟶ Z)
    (N : X.Opens) (B : Set X) (C D : Set Y)
    [IsIso (p ∣_ N)]
    (hBN : closure B ⊆ (N : Set X))
    (hsurj : B ⊆ Set.range (p.base ∘ a.base))
    (hmap : a.base ⁻¹' (p.base ⁻¹' B) ⊆
      a.base ⁻¹' (q.base ⁻¹' closure C))
    (hdisj : Disjoint (closure C) (closure D)) :
    Disjoint (p.base ⁻¹' closure B) (q.base ⁻¹' closure D) := by
  have hB : B ⊆ (N : Set X) := fun _ hx => hBN (subset_closure hx)
  have hpre : p.base ⁻¹' B ⊆ q.base ⁻¹' closure C :=
    preimage_subset_of_injOn_and_range p.base q.base a.base B
      (closure C) (N : Set X) hB
      (injOn_preimage_of_isIso_restrict p N) hsurj hmap
  exact disjoint_cross_boundary_of_closure_preimage p q B (closure C)
    (closure D) isClosed_closure hdisj hpre
    (preimage_closure_subset_of_isIso_restrict p N B hBN)

/-- The section of one proper extension supplies a point of the fibre product
over every point of the other extension lying above its open. -/
theorem exists_fiberProduct_point_over_section
    {U X Y : Scheme.{u}} (p : X ⟶ U) (q : Y ⟶ U)
    (T : U.Opens) (e : T.toScheme ⟶ Y) (he : e ≫ q = T.ι)
    (x : X) (hx : p.base x ∈ T) :
    ∃ z : pullback (C := Scheme.{u}) p q,
      (pullback.fst p q).base z = x ∧
      (pullback.snd p q).base z = e.base ⟨p.base x, hx⟩ := by
  let y : Y := e.base ⟨p.base x, hx⟩
  have hxy : p.base x = q.base y := by
    exact (comp_base_apply_eq he ⟨p.base x, hx⟩).symm
  exact Scheme.Pullback.exists_preimage_pullback x y hxy

/-- The fibre product of two proper extensions covers the first boundary and
maps that boundary into the corresponding boundary of the second extension.
An isomorphism near its closure turns this into cross-boundary separation. -/
theorem disjoint_boundaries_from_fiberProduct
    {U Y₁ Y₂ Z : Scheme.{u}}
    (V₁ : Y₁.Opens) (V₂ : Y₂.Opens)
    (p₁ : V₁.toScheme ⟶ U) (p₂ : V₂.toScheme ⟶ U)
    (U₁ U₂ : U.Opens) (hcover : U₁ ⊔ U₂ = ⊤)
    (e₂ : U₂.toScheme ⟶ V₂.toScheme) (he₂ : e₂ ≫ p₂ = U₂.ι)
    (a : pullback p₁ p₂ ⟶ Z) (P₁ : Z ⟶ Y₁) (P₂ : Z ⟶ Y₂)
    (ha₁ : a ≫ P₁ = pullback.fst p₁ p₂ ≫ V₁.ι)
    (ha₂ : a ≫ P₂ = pullback.snd p₁ p₂ ≫ V₂.ι)
    (N : Y₁.Opens) (B : Set Y₁) (C D : Set Y₂)
    [IsIso (P₁ ∣_ N)]
    (hB : B ⊆ V₁.ι.base '' (p₁.base ⁻¹' ((U₁ : Set U)ᶜ)))
    (hC : V₂.ι.base '' (p₂.base ⁻¹' ((U₁ : Set U)ᶜ)) ⊆ closure C)
    (hnear : closure B ⊆ (N : Set Y₁))
    (hdisj : Disjoint (closure C) (closure D)) :
    Disjoint (P₁.base ⁻¹' closure B) (P₂.base ⁻¹' closure D) := by
  have hsurj : B ⊆ Set.range (P₁.base ∘ a.base) := by
    intro y hy
    obtain ⟨v₁, hv₁, rfl⟩ := hB hy
    have hcov : p₁.base v₁ ∈ U₁ ⊔ U₂ := by simp [hcover]
    have hv₂ : p₁.base v₁ ∈ U₂ := Or.resolve_left hcov hv₁
    obtain ⟨z, hz₁, _⟩ :=
      exists_fiberProduct_point_over_section p₁ p₂ U₂ e₂ he₂ v₁ hv₂
    refine ⟨z, ?_⟩
    simpa [hz₁] using comp_base_apply_eq ha₁ z
  have hmap : a.base ⁻¹' (P₁.base ⁻¹' B) ⊆
      a.base ⁻¹' (P₂.base ⁻¹' closure C) := by
    intro z hz
    change P₁.base (a.base z) ∈ B at hz
    rw [comp_base_apply_eq ha₁ z] at hz
    obtain ⟨v₁, hv₁, hv₁eq⟩ := hB hz
    have hsame : v₁ = (pullback.fst p₁ p₂).base z :=
      V₁.ι.isOpenEmbedding.injective hv₁eq
    have hbad : p₂.base ((pullback.snd p₁ p₂).base z) ∈ (U₁ : Set U)ᶜ := by
      have hpb : p₁.base ((pullback.fst p₁ p₂).base z) = p₂.base ((pullback.snd p₁ p₂).base z) :=
        comp_base_apply_eq (pullback.condition (f := p₁) (g := p₂)) z
      rw [← hpb, ← hsame]
      exact hv₁
    change P₂.base (a.base z) ∈ closure C
    rw [comp_base_apply_eq ha₂ z]
    exact hC ⟨(pullback.snd p₁ p₂).base z, hbad, rfl⟩
  exact disjoint_image_boundaries_of_isIso_near_closure P₁ P₂ a N B C D
    hnear hsurj hmap hdisj

/-- Precomposing with an isomorphism preserves being an isomorphism over an open. -/
theorem isIso_restrict_of_iso_over {X Y Z : Scheme.{u}}
    (e : X ≅ Y) (p : Y ⟶ Z) (U : Z.Opens)
    [IsIso (p ∣_ U)] : IsIso ((e.hom ≫ p) ∣_ U) := by
  have : IsIso e.hom := Iso.isIso_hom e
  have he : IsIso (e.hom ∣_ (p ⁻¹ᵁ U)) := inferInstance
  rw [morphismRestrict_comp]
  exact IsIso.comp_isIso' he inferInstance

end Stacks.Compactification

end
