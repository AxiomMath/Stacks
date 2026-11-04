module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.RingTheory.Extension.Generators
public import StacksFrontier.AlgebraicGeometry.FiniteTypeClosedInFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.AbsoluteNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian

/-!
# Immersing a limit of finite-type schemes into a scheme of finite presentation

Write a quasi-compact quasi-separated scheme `X` as `X = lim X_i` with every `X_i` of finite type
over the integers and every transition morphism affine. Then, for a morphism `f : X ⟶ S` locally
of finite type, `X` immerses over `S` into `X_{i,S} = X_i ×_{Spec ℤ} S` for a sufficiently large
stage `i`, and that scheme is of finite presentation over `S`.

This is the second paragraph of the proof of Tag 01ZE — the paragraph that glues the affine-chart
closed immersions into one immersion of `X`. The argument is:

* choose a finite affine open cover `X = V_1 ∪ … ∪ V_n` with `f` carrying each `V_j` into an
  affine open `U_j ⊆ S`;
* the cover comes from a stage: `V_j = (X → X_i)⁻¹ V_{j,i}` with `V_{j,i} ⊆ X_i` affine open
  (Tag 01Z4, Tag 01Z6, available in Mathlib as
  `AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine`);
* finitely many algebra generators of `𝒪_X(V_j)` over `𝒪_S(U_j)` descend to one further stage
  (Tag 01Z0, available as `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit`), so the chart maps
  `V_j ⟶ U_j ×_{Spec ℤ} V_{j,i}` become closed immersions;
* the opens `U_j ×_{Spec ℤ} V_{j,i}` of `X_{i,S}` cover the image of `X` and the preimage of the
  `j`-th one is exactly `V_j`, so `X ⟶ X_{i,S}` is an immersion.

The last of those four steps is the glueing proper, and it is isolated as
`AlgebraicGeometry.isImmersion_of_forall_exists_isClosedImmersion_resLE`: being an immersion is
Zariski-local on the target.

## Main results

* `AlgebraicGeometry.isImmersion_of_forall_exists_isClosedImmersion_resLE`: a morphism whose
  restriction over each member of a family of opens covering the image is a closed immersion is an
  immersion.
* `AlgebraicGeometry.exists_finite_isAffineOpen_cover_mapsTo`: a quasi-compact scheme has a finite
  affine open cover each of whose members is carried into an affine open of the target.
* `AlgebraicGeometry.exists_common_stage_appTop_eq`: finitely many sections over affine opens of a
  limit of schemes with affine transition morphisms all descend to one common stage.
* `AlgebraicGeometry.exists_finitePresentation_isImmersion_of_isLimit`: the glueing paragraph
  itself.
* `AlgebraicGeometry.exists_finitePresentation_isImmersion_of_isOneAffineOpenStep` and
  `AlgebraicGeometry.exists_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep`: the
  conclusions of Tag 01ZE and Tag 01ZG for a quasi-compact quasi-separated source, granted the
  single-affine step of Noetherian approximation relative to a quasi-compact open.

## Implementation notes

The limit presentation of `X` is the conclusion of Tag 01ZA, absolute Noetherian approximation,
which this file does **not** prove: the only route to it in the library is the theorem
`exists_limitNoetherianSituation_of_isOneAffineOpenStep` of the namespace
`AlgebraicGeometry.Scheme.FiniteTypeApproximation`, which carries the predicate
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep` as a hypothesis. So the
glueing paragraph is stated here against the limit presentation as explicit data
(`exists_finitePresentation_isImmersion_of_isLimit`), and the two assembled statements carry
`IsOneAffineOpenStep` as a hypothesis. **No attribute for Tag 01ZE or Tag 01ZG is attached to
anything in this file**, because both tags assert their conclusions outright while every statement
here assumes either the limit presentation or the predicate that produces it. Proving that one
predicate makes both unconditional.

Note that the glueing paragraph assumes **less** than Tag 01ZE does about `X`: quasi-compactness
of `X` is obtained from the stages by `AlgebraicGeometry.Scheme.compactSpace_of_isLimit`, and
quasi-separatedness of `X` is never used at all — only quasi-separatedness of the stages, which
follows from their being of finite type over the integers, hence Noetherian
(`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from`).

Finite type over the integers is expressed, as in Tag 01T1, as local finiteness of type together
with quasi-compactness of the structural morphism to the terminal scheme, the terminal scheme
being `Spec (ULift ℤ)`. "Of finite presentation" is `AlgebraicGeometry.FinitePresentation`, the
bundled conjunction of the three conditions.

Three morphism-property instances that `IsZariskiLocalAtTarget.of_forall_source_exists_preimage`
needs for immersions — `MorphismProperty.RespectsIso`, `MorphismProperty.RespectsRight` against
open immersions and `MorphismProperty.HasOfPostcompProperty` against open immersions — are not
instances in Mathlib for `AlgebraicGeometry.IsImmersion` and are supplied inside the proof of the
glueing lemma. The first two follow from multiplicativity of immersions, the third from Zariski
locality at the target.

## References

* [Stacks Project, Tag 01ZE](https://stacks.math.columbia.edu/tag/01ZE)
* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The glueing step -/

/-- **The glueing step of Tag 01ZE.** A morphism `f : X ⟶ Y` is an immersion as soon as there is a
family of opens of `Y` covering the image of `f` over each of which `f` restricts to a closed
immersion.

This is the last sentence of the proof of Tag 01ZE: the `(V_{j,i})_{U_j}` form an open of
`X_{i,S}`, the inverse image of the `j`-th one is `V_j`, each `V_j ⟶ (V_{j,i})_{U_j}` is a closed
immersion, and therefore `X ⟶ X_{i,S}` is an immersion. The condition "the inverse image of the
`j`-th open is `V_j`" is built into the spelling: the source of the restriction is
`f ⁻¹ᵁ U i` by construction. -/
theorem isImmersion_of_forall_exists_isClosedImmersion_resLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type*} (U : ι → Y.Opens) (hcover : ∀ x : X, ∃ i, f.base x ∈ U i)
    (hclosed : ∀ i, IsClosedImmersion (f.resLE (U i) (f ⁻¹ᵁ U i) le_rfl)) :
    IsImmersion f := by
  have : MorphismProperty.RespectsIso @IsImmersion :=
    MorphismProperty.RespectsIso.mk _ (fun e g _ ↦ IsImmersion.comp e.hom g)
      (fun e g _ ↦ IsImmersion.comp g e.hom)
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion := ⟨by
    intro _ _ _ i _ g hg
    have : IsImmersion g := hg
    have : IsImmersion i := inferInstance
    infer_instance⟩
  have : MorphismProperty.HasOfPostcompProperty @IsImmersion @IsOpenImmersion :=
    hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict _
      (fun g V hg ↦ IsZariskiLocalAtTarget.restrict hg V)
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion) f ?_
  intro x
  obtain ⟨i, hx⟩ := hcover x
  refine ⟨U i, hx, ?_⟩
  have hcomp : IsImmersion (f.resLE (U i) (f ⁻¹ᵁ U i) le_rfl ≫ (U i).ι) := by
    have := hclosed i
    infer_instance
  simpa only [Scheme.Hom.resLE_comp_ι] using hcomp

/-! ### The affine cover of the source subordinate to an affine cover of the target -/

/-- A quasi-compact scheme has a finite affine open cover each of whose members is carried by a
given morphism into an affine open of the target.

This is the choice of the covering `X = V_1 ∪ … ∪ V_n` with `f(V_j) ⊆ U_j` opening the second
paragraph of the proof of Tag 01ZE. The affine opens of a scheme form a basis of its topology, so
an affine open around `f x` and then an affine open around `x` inside its preimage exist for every
point; quasi-compactness extracts a finite subcover. -/
theorem exists_finite_isAffineOpen_cover_mapsTo {X S : Scheme.{u}} [CompactSpace X] (f : X ⟶ S) :
    ∃ (s : Finset X) (U : s → S.Opens) (V : s → X.Opens),
      (∀ j, IsAffineOpen (U j) ∧ IsAffineOpen (V j) ∧ V j ≤ f ⁻¹ᵁ U j) ∧ IsOpenCover V := by
  classical
  have htarget (x : X) : ∃ U : S.Opens, IsAffineOpen U ∧ f.base x ∈ U := by
    obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hfx, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    exact ⟨U, hU, hfx⟩
  choose U hU hfx using htarget
  have hsource (x : X) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ f ⁻¹ᵁ U x := by
    obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hfx x) (f ⁻¹ᵁ U x).2
    exact ⟨V, hV, hx, hle⟩
  choose V hV hx hle using hsource
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ (V x : Set X))
    (fun x ↦ (V x).2) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨s, fun j ↦ U j.1, fun j ↦ V j.1, fun j ↦ ⟨hU j.1, hV j.1, hle j.1⟩, ?_⟩
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨y, hyS, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨⟨y, hyS⟩, hy⟩

/-- An algebra map hitting every member of a finite generating family is surjective. -/
private theorem surjective_of_range_generators_subset_range {R C A : Type*} [CommRing R]
    [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] (ψ : C →ₐ[R] A) {n : ℕ}
    (P : Algebra.Generators R A (Fin n)) (hgen : ∀ i, ∃ z : C, ψ z = P.val i) :
    Function.Surjective ψ := by
  have hp : Algebra.adjoin R (Set.range P.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).2 P.aeval_val_surjective
  have hmem : Set.range P.val ⊆ ψ.range := by
    rintro _ ⟨i, rfl⟩
    exact hgen i
  refine (AlgHom.range_eq_top ψ).mp (top_unique ?_)
  rw [← hp]
  exact Algebra.adjoin_le_iff.mpr hmem

/-- A morphism locally of finite type between affine schemes makes the global sections of the
source a finitely generated algebra over those of the target. -/
theorem exists_generators_of_locallyOfFiniteType {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Algebra Γ(Y, ⊤) Γ(X, ⊤)]
    (hf : algebraMap Γ(Y, ⊤) Γ(X, ⊤) = f.appTop.hom) :
    ∃ n, Nonempty (Algebra.Generators Γ(Y, ⊤) Γ(X, ⊤) (Fin n)) := by
  have : Algebra.FiniteType Γ(Y, ⊤) Γ(X, ⊤) := RingHom.finiteType_algebraMap.mp <| by
    rw [hf]
    exact HasRingHomProperty.appTop (@LocallyOfFiniteType) f inferInstance
  exact Algebra.FiniteType.iff_exists_generators.mp inferInstance

/-- Let `a : V ⟶ W` and `b : V ⟶ U` agree over `Z`, with `V`, `U` affine and `W ⟶ Z` affine. If
`Γ(V, ⊤)` is generated over `Γ(U, ⊤)` by sections pulled back along `a`, then `pullback.lift a b`
is a closed immersion. -/
theorem isClosedImmersion_pullback_lift_of_generators {V W U Z : Scheme.{u}} [IsAffine V]
    [IsAffine U] (w : W ⟶ Z) (u : U ⟶ Z) [IsAffineHom w] (a : V ⟶ W) (b : V ⟶ U)
    (hab : a ≫ w = b ≫ u) [Algebra Γ(U, ⊤) Γ(V, ⊤)]
    (hb : algebraMap Γ(U, ⊤) Γ(V, ⊤) = b.appTop.hom) {n : ℕ}
    (P : Algebra.Generators Γ(U, ⊤) Γ(V, ⊤) (Fin n))
    (hgen : ∀ i, ∃ z : Γ(W, ⊤), a.appTop.hom z = P.val i) :
    IsClosedImmersion (pullback.lift a b hab) := by
  have : IsAffine (pullback w u) := isAffine_of_isAffineHom (pullback.snd w u)
  let : Algebra Γ(U, ⊤) Γ(pullback w u, ⊤) := (pullback.snd w u).appTop.hom.toAlgebra
  let ψ : Γ(pullback w u, ⊤) →ₐ[Γ(U, ⊤)] Γ(V, ⊤) :=
    { toRingHom := (pullback.lift a b hab).appTop.hom
      commutes' := by
        intro r
        show (pullback.lift a b hab ≫ pullback.snd w u).appTop.hom r =
          algebraMap Γ(U, ⊤) Γ(V, ⊤) r
        rw [pullback.lift_snd, hb] }
  refine IsClosedImmersion.of_surjective_of_isAffine _
    (surjective_of_range_generators_subset_range ψ P fun i ↦ ?_)
  obtain ⟨z, hz⟩ := hgen i
  refine ⟨(pullback.fst w u).appTop.hom z, ?_⟩
  show (pullback.lift a b hab ≫ pullback.fst w u).appTop.hom z = _
  rw [pullback.lift_fst]
  exact hz

/-- The image of `W ×_Z U ⟶ Y ×_Z S`, for opens `W ⊆ Y` and `U ⊆ S`, is the intersection of the
preimages of `W` and `U`. -/
theorem opensRange_pullback_map_ι {Y S Z : Scheme.{u}} (g : Y ⟶ Z) (h : S ⟶ Z) (W : Y.Opens)
    (U : S.Opens) :
    (pullback.map (W.ι ≫ g) (U.ι ≫ h) g h W.ι U.ι (𝟙 _) (by simp) (by simp)).opensRange =
      pullback.fst g h ⁻¹ᵁ W ⊓ pullback.snd g h ⁻¹ᵁ U := by
  refine TopologicalSpace.Opens.ext ?_
  show Set.range (pullback.map (W.ι ≫ g) (U.ι ≫ h) g h W.ι U.ι (𝟙 _) _ _).base = _
  rw [Scheme.Pullback.range_map,
    show Set.range W.ι.base = (W : Set Y) from Scheme.Opens.range_ι _,
    show Set.range U.ι.base = (U : Set S) from Scheme.Opens.range_ι _]
  rfl

/-- A morphism `q` into `Y ×_Z S` restricts to a closed immersion over the open `W ×_Z U` as soon
as the induced map from the preimage `V` into `W ×_Z U` is one. -/
theorem isClosedImmersion_resLE_of_isClosedImmersion_pullback_lift {X Y S Z : Scheme.{u}}
    {g : Y ⟶ Z} {h : S ⟶ Z} (q : X ⟶ pullback g h) (W : Y.Opens) (U : S.Opens) (V : X.Opens)
    (hV : q ⁻¹ᵁ (pullback.fst g h ⁻¹ᵁ W ⊓ pullback.snd g h ⁻¹ᵁ U) = V)
    (a : (V : Scheme) ⟶ W) (b : (V : Scheme) ⟶ U)
    (ha : a ≫ W.ι = V.ι ≫ q ≫ pullback.fst g h) (hb : b ≫ U.ι = V.ι ≫ q ≫ pullback.snd g h)
    (hab : a ≫ W.ι ≫ g = b ≫ U.ι ≫ h) (hl : IsClosedImmersion (pullback.lift a b hab)) :
    IsClosedImmersion (q.resLE (pullback.fst g h ⁻¹ᵁ W ⊓ pullback.snd g h ⁻¹ᵁ U)
      (q ⁻¹ᵁ (pullback.fst g h ⁻¹ᵁ W ⊓ pullback.snd g h ⁻¹ᵁ U)) le_rfl) := by
  let t := pullback.map (W.ι ≫ g) (U.ι ≫ h) g h W.ι U.ι (𝟙 _) (by simp) (by simp)
  have : IsOpenImmersion t := by
    show IsOpenImmersion (pullback.map (W.ι ≫ g) (U.ι ≫ h) g h W.ι U.ι (𝟙 _) _ _)
    infer_instance
  let e := t.isoOpensRange ≪≫ (pullback g h).isoOfEq (opensRange_pullback_map_ι g h W U)
  have hfst : t ≫ pullback.fst g h = pullback.fst _ _ ≫ W.ι := pullback.lift_fst _ _ _
  have hsnd : t ≫ pullback.snd g h = pullback.snd _ _ ≫ U.ι := pullback.lift_snd _ _ _
  let O := pullback.fst g h ⁻¹ᵁ W ⊓ pullback.snd g h ⁻¹ᵁ U
  have hfac : q.resLE _ V hV.symm.le = pullback.lift a b hab ≫ e.hom := by
    refine (cancel_mono O.ι).1 ?_
    calc q.resLE _ V hV.symm.le ≫ O.ι = V.ι ≫ q := Scheme.Hom.resLE_comp_ι _ _
      _ = pullback.lift a b hab ≫ t := by
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, ← ha, Category.assoc, hfst, pullback.lift_fst_assoc]
        · rw [Category.assoc, ← hb, Category.assoc, hsnd, pullback.lift_snd_assoc]
      _ = pullback.lift a b hab ≫ e.hom ≫ O.ι := by simp [e, O]
      _ = _ := (Category.assoc _ _ _).symm
  refine (q.resLE_congr le_rfl rfl hV (P := @IsClosedImmersion)).mpr ?_
  rw [hfac]
  exact MorphismProperty.RespectsIso.postcomp (@IsClosedImmersion) e.hom _ hl

/-- Let `p : X ⟶ Y` and `f : X ⟶ S` agree over an affine `Z`, and let `W j ⊆ Y`, `U j ⊆ S` be
affine opens whose preimages `V j = p ⁻¹ᵁ W j ≤ f ⁻¹ᵁ U j` are affine and cover `X`. If each
`Γ(V j, ⊤)` is generated over `Γ(U j, ⊤)` by sections pulled back from `Γ(W j, ⊤)`, then the
induced morphism `X ⟶ Y ×_Z S` is an immersion. -/
theorem isImmersion_pullback_lift_of_generators {X Y S Z : Scheme.{u}} [IsAffine Z]
    {p : X ⟶ Y} {f : X ⟶ S} {g : Y ⟶ Z} {h : S ⟶ Z} (hpf : p ≫ g = f ≫ h) {t : Type*}
    (W : t → Y.Opens) (U : t → S.Opens) (V : t → X.Opens) [∀ j, IsAffine (W j : Scheme)]
    [∀ j, IsAffine (U j : Scheme)] [∀ j, IsAffine (V j : Scheme)] (hV : ∀ j, p ⁻¹ᵁ W j = V j)
    (hle : ∀ j, V j ≤ f ⁻¹ᵁ U j) (hcov : ∀ x, ∃ j, x ∈ V j)
    [∀ j, Algebra Γ(U j, ⊤) Γ(V j, ⊤)]
    (halg : ∀ j, algebraMap Γ(U j, ⊤) Γ(V j, ⊤) = (f.resLE (U j) (V j) (hle j)).appTop.hom)
    {n : t → ℕ} (P : ∀ j, Algebra.Generators Γ(U j, ⊤) Γ(V j, ⊤) (Fin (n j)))
    (hgen : ∀ j i, ∃ z : Γ(W j, ⊤), (p.resLE (W j) (V j) (hV j).ge).appTop.hom z = (P j).val i) :
    IsImmersion (pullback.lift p f hpf) := by
  let O (j : t) := pullback.fst g h ⁻¹ᵁ W j ⊓ pullback.snd g h ⁻¹ᵁ U j
  have hpreV (j : t) : pullback.lift p f hpf ⁻¹ᵁ O j = V j := by
    show pullback.lift p f hpf ⁻¹ᵁ (pullback.fst g h ⁻¹ᵁ W j) ⊓
      pullback.lift p f hpf ⁻¹ᵁ (pullback.snd g h ⁻¹ᵁ U j) = V j
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.lift_fst,
      pullback.lift_snd, hV j]
    exact inf_eq_left.mpr (hle j)
  refine isImmersion_of_forall_exists_isClosedImmersion_resLE _ O (fun x ↦ ?_) fun j ↦ ?_
  · obtain ⟨j, hj⟩ := hcov x
    exact ⟨j, (hpreV j).ge hj⟩
  let a := p.resLE (W j) (V j) (hV j).ge
  let b := f.resLE (U j) (V j) (hle j)
  have ha : a ≫ (W j).ι = (V j).ι ≫ p := Scheme.Hom.resLE_comp_ι _ _
  have hb : b ≫ (U j).ι = (V j).ι ≫ f := Scheme.Hom.resLE_comp_ι _ _
  have hab : a ≫ (W j).ι ≫ g = b ≫ (U j).ι ≫ h := by
    rw [reassoc_of% ha, hpf, reassoc_of% hb]
  exact isClosedImmersion_resLE_of_isClosedImmersion_pullback_lift _ (W j) (U j) (V j) (hpreV j)
    a b (by rw [pullback.lift_fst, ha]) (by rw [pullback.lift_snd, hb]) hab
    (isClosedImmersion_pullback_lift_of_generators _ _ a b hab (halg j) (P j) (hgen j))

/-! ### Finitely many sections descend to one stage -/

variable {I : Type u} [Category.{u} I]

/-- Finitely many global sections, each over the preimage in the limit of an affine open of one
fixed stage, all descend to a single common stage.

This is Tag 01Z0 for a finite family. Mathlib's `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit`
descends one section; the stages it produces are then dominated by a single one because the index
category is cofiltered. The sections are taken over the preimages of affine opens so that each
one is a global section of an affine scheme, which is where the descent happens. -/
theorem exists_common_stage_appTop_eq [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type u} [Finite J] (W : J → (D.obj i).Opens) (hW : ∀ j, IsAffineOpen (W j))
    (s : ∀ j, Γ((c.π.app i ⁻¹ᵁ W j : c.pt.Opens), ⊤)) :
    ∃ (k : Over i) (t : ∀ j, Γ((opensDiagram D i (W j)).obj k, ⊤)),
      ∀ j, s j = ((opensCone D c i (W j)).π.app k).appTop (t j) := by
  classical
  let E (j : J) := opensDiagram D i (W j)
  let d (j : J) := opensCone D c i (W j)
  have hLim (j : J) : IsLimit (d j) := isLimitOpensCone D c hc i (W j)
  have hAff (j : J) (k : Over i) : IsAffine ((E j).obj k) := (hW j).preimage (D.map k.hom)
  choose a t ht using fun j ↦
    have := hAff j
    exists_appTop_π_eq_of_isLimit (E j) (d j) (hLim j) (s j)
  have : Fintype J := Fintype.ofFinite J
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image a)
  let m (j : J) : k ⟶ a j := (hk (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).some
  refine ⟨k, fun j ↦ ((E j).map (m j)).appTop (t j), fun j ↦ ?_⟩
  have hn : (d j).π.app (a j) = (d j).π.app k ≫ (E j).map (m j) := ((d j).w (m j)).symm
  rw [ht j, hn]
  rfl

/-! ### The glueing paragraph -/

/-- **The glueing paragraph of Tag 01ZE.** Let `X` be the limit of a cofiltered system of schemes
of finite type over the integers with affine transition morphisms, and let `f : X ⟶ S` be locally
of finite type. Then `X` admits an immersion over `S` into a scheme of finite presentation over
`S`.

The scheme constructed is `X_i ×_{Spec ℤ} S` for a sufficiently large stage `i`; it is of finite
presentation over `S` because `X_i ⟶ Spec ℤ` is of finite type over a Noetherian base, hence of
finite presentation (Tag 01TX), and finite presentation is stable under base change (Tag 01TS).

The limit presentation is the conclusion of Tag 01ZA and is taken as data; see the implementation
notes for why no attribute for Tag 01ZE is attached. -/
theorem exists_finitePresentation_isImmersion_of_isLimit [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
    [∀ i, QuasiCompact (terminal.from (D.obj i))]
    (c : Cone D) (hc : IsLimit c) {S : Scheme.{u}} (f : c.pt ⟶ S) [LocallyOfFiniteType f] :
    ∃ (X' : Scheme.{u}) (f' : X' ⟶ S) (i : c.pt ⟶ X'),
      FinitePresentation f' ∧ IsImmersion i ∧ i ≫ f' = f := by
  classical
  have hNoeth (j : I) : IsNoetherian (D.obj j) :=
    isNoetherian_of_locallyOfFiniteType_terminal_from _
  have := hNoeth
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have hZ : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).symm
  let hS : S ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) := terminal.from S ≫ e.hom
  -- a finite affine open cover of `X` carried into affine opens of `S`
  obtain ⟨s, U, V, hcharts, hcover⟩ := exists_finite_isAffineOpen_cover_mapsTo f
  -- the cover comes from a stage `i`
  obtain ⟨i, W, -, hW⟩ :=
    Scheme.exists_isOpenCover_and_isAffine_of_finite D c hc V hcover (fun j ↦ (hcharts j).2.1)
  obtain rfl : V = fun j ↦ c.π.app i ⁻¹ᵁ W j := funext fun j ↦ (hW j).2
  let Vlim (j : s) : c.pt.Opens := c.π.app i ⁻¹ᵁ W j
  have hle (j : s) : Vlim j ≤ f ⁻¹ᵁ U j := (hcharts j).2.2
  let fchart (j : s) : (Vlim j : Scheme) ⟶ (U j : Scheme) := f.resLE (U j) (Vlim j) (hle j)
  have hUaff (j : s) : IsAffine (U j : Scheme) := (hcharts j).1
  have hVaff (j : s) : IsAffine (Vlim j : Scheme) := (hcharts j).2.1
  have hftchart (j : s) : LocallyOfFiniteType (fchart j) :=
    inferInstanceAs (LocallyOfFiniteType (f.resLE (U j) (Vlim j) (hle j)))
  let algChart (j : s) : Algebra Γ((U j : Scheme), ⊤) Γ((Vlim j : Scheme), ⊤) :=
    (fchart j).appTop.hom.toAlgebra
  -- finitely many algebra generators on each chart
  choose n hP using fun j ↦ exists_generators_of_locallyOfFiniteType (fchart j) rfl
  let P (j : s) := (hP j).some
  -- the generators descend to a common stage `k`
  obtain ⟨k, tgen, htgen⟩ := exists_common_stage_appTop_eq D c hc i
    (fun a : Σ j : s, Fin (n j) ↦ W a.1) (fun a ↦ (hW a.1).1) (fun a ↦ (P a.1).val a.2)
  -- the model: the base change of the stage `D.obj k.left` to `S`
  let g : D.obj k.left ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    terminal.from (D.obj k.left) ≫ e.hom
  have hgft : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  have hgqc : QuasiCompact g := by dsimp only [g]; infer_instance
  have hbase : c.π.app k.left ≫ g = f ≫ hS := specULiftZIsTerminal.hom_ext _ _
  let Wk (j : s) : (D.obj k.left).Opens := D.map k.hom ⁻¹ᵁ W j
  have hWkaff (j : s) : IsAffine (Wk j : Scheme) := (hW j).1.preimage (D.map k.hom)
  have hWlim (j : s) : c.π.app k.left ⁻¹ᵁ Wk j = Vlim j := by
    show c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ W j) = c.π.app i ⁻¹ᵁ W j
    rw [← Scheme.Hom.comp_preimage, c.w]
  have hcov (x : c.pt) : ∃ j, x ∈ Vlim j :=
    TopologicalSpace.Opens.mem_iSup.mp (hcover.iSup_eq_top.ge trivial)
  exact ⟨pullback g hS, pullback.snd g hS, pullback.lift _ _ hbase,
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback g hS)
      (finitePresentation_of_finiteType g),
    isImmersion_pullback_lift_of_generators hbase Wk U Vlim hWlim hle hcov
      (fun _ ↦ rfl) P fun j a' ↦ ⟨tgen ⟨j, a'⟩, (htgen ⟨j, a'⟩).symm⟩,
    pullback.lift_snd _ _ _⟩

/-! ### Tag 01ZE and Tag 01ZG, granted the single-affine step -/

/-- The conclusion of **Tag 01ZE** for a quasi-compact quasi-separated source, granted the
single-affine step `AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep` of
Noetherian approximation relative to a quasi-compact open.

The predicate is the only hypothesis beyond those of the tag: it produces the limit presentation
of `X` by schemes of finite type over the integers (Tag 01ZA), and the glueing paragraph
`AlgebraicGeometry.exists_finitePresentation_isImmersion_of_isLimit` does the rest. No attribute
for Tag 01ZE is attached, because the tag asserts the conclusion outright. -/
theorem exists_finitePresentation_isImmersion_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (X' : Scheme.{u}) (f' : X' ⟶ S) (i : X ⟶ X'),
      FinitePresentation f' ∧ IsImmersion i ∧ i ≫ f' = f := by
  obtain ⟨Jx, hpre, hne, hdir, Dsit, hEq, hFT⟩ :=
    Scheme.FiniteTypeApproximation.exists_limitNoetherianSituation_of_isOneAffineOpenStep hstep X
  subst hEq
  have hFTop : ∀ m : Jxᵒᵖ, LocallyOfFiniteType (terminal.from (Dsit.system.obj m)) :=
    fun m ↦ hFT m.unop
  have hCS : ∀ m : Jxᵒᵖ, CompactSpace (Dsit.system.obj m) := fun m ↦
    have := Dsit.noetherian m.unop; inferInstance
  have hQC : ∀ m : Jxᵒᵖ, QuasiCompact (terminal.from (Dsit.system.obj m)) := fun m ↦
    have := hCS m; inferInstance
  have hAffT : ∀ {m m' : Jxᵒᵖ} (v : m ⟶ m'), IsAffineHom (Dsit.system.map v) :=
    fun v ↦ Dsit.transition_affine v
  exact exists_finitePresentation_isImmersion_of_isLimit Dsit.system Dsit.limitCone Dsit.isLimit f

/-- The conclusion of **Tag 01ZG** for a quasi-compact quasi-separated source over a
quasi-separated base, granted the single-affine step
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`.

This is the immersion above fed to the passage from an immersion to a closed immersion,
`AlgebraicGeometry.exists_finitePresentation_isClosedImmersion_of_exists_immersion`, with no
bridging lemma. No attribute for Tag 01ZG is attached, for the same reason as above. -/
theorem exists_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ S) (ι : X ⟶ X'),
      FinitePresentation p ∧ IsClosedImmersion ι ∧ ι ≫ p = f :=
  exists_finitePresentation_isClosedImmersion_of_exists_immersion f
    (exists_finitePresentation_isImmersion_of_isOneAffineOpenStep hstep f)

end AlgebraicGeometry

end
