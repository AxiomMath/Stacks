module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.ValuativeCriterionRefined
public import StacksFrontier.Examples.GroupSchemes.DoubleGlue

/-!
# The uniqueness hypothesis of the refined valuative criterion

The refined valuative criterion `AlgebraicGeometry.universallyClosed_of_unique_lift_of_denseRange`
asks that every valuative square for `f : X ⟶ S` whose generic-point map factors through a dense
quasi-compact `h : U ⟶ X` has a *unique* lift. The uniqueness cannot be dropped: there are
quasi-compact `f` and `h`, with `f` quasi-separated and `h` of dense image, for which every such
square has a lift, and yet `f` is neither universally closed nor separated. On the other hand, the
uniqueness is automatic when `f` is separated.

The example is the affine plane `Y = 𝔸²` glued with its open subscheme `W = D(y)` along
`V = D(xy)`, mapping to `Y` by the identity on `Y` and the inclusion on `W`. The copy of `Y` is a
section of this morphism with dense image, so every square through it has a lift. The complement
of that section is closed and maps onto `D(y) ∩ V(x)`, which is not closed in `𝔸²`, so the morphism
is not closed. Being quasi-compact, it is then not separated either, since otherwise the lifts
would be unique and the refined criterion would make it universally closed.

## Main results

* `AlgebraicGeometry.refinedValuative_unique_iff_hasLift_of_isSeparated`: for separated `f`,
  the hypothesis of the refined criterion is equivalent to the existence of the lifts.
* `AlgebraicGeometry.universallyClosed_of_hasLift_of_denseRange_of_isSeparated`: for separated
  `f`, the refined criterion with existence of the lifts only.
* `AlgebraicGeometry.RefinedValuativeNecessity.plane_counterexample`: the glued affine plane over
  a field is a counterexample to the refined criterion without uniqueness.
* `AlgebraicGeometry.exists_hasLift_of_denseRange_not_universallyClosed_not_isSeparated`: the
  counterexample showing that uniqueness is necessary.

## References

* [Stacks Project, Tag 0895](https://stacks.math.columbia.edu/tag/0895)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- If `f` is separated, the dotted arrows in the refined valuative criterion are automatically
unique: every valuative square for `f` whose generic-point map factors through `h` has a unique
lift as soon as it has one. -/
@[stacks 0895 "uniqueness of the dotted arrows is guaranteed when f is separated"]
public theorem refinedValuative_unique_iff_hasLift_of_isSeparated
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) [IsSeparated f] :
    (∀ (D : ValuativeCommSq f) (g : Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct)) ↔
    (∀ (D : ValuativeCommSq f) (g : Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → D.commSq.HasLift) := by
  refine ⟨fun H D g hg => ?_, fun H D g hg => ?_⟩
  · obtain ⟨l⟩ := H D g hg
    exact ⟨⟨l.default⟩⟩
  · have : Subsingleton D.commSq.LiftStruct := IsSeparated.valuativeCriterion f D
    obtain ⟨⟨l⟩⟩ := H D g hg
    exact ⟨uniqueOfSubsingleton l⟩

/-- For a separated morphism the refined valuative criterion needs only the existence of the
lifts. -/
public theorem universallyClosed_of_hasLift_of_denseRange_of_isSeparated
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) [QuasiCompact f] [QuasiCompact h]
    [IsSeparated f] (hdense : DenseRange h)
    (hlift : ∀ (D : ValuativeCommSq f) (g : Spec (.of D.K) ⟶ U),
      g ≫ h = D.i₁ → D.commSq.HasLift) :
    UniversallyClosed f :=
  universallyClosed_of_unique_lift_of_denseRange h f hdense
    ((refinedValuative_unique_iff_hasLift_of_isSeparated h f).2 hlift)

namespace RefinedValuativeNecessity

open Stacks.Examples

attribute [local instance] SectionCoverData.isOpenImmersion_chart

variable (Y : Scheme.{u}) (V W : Y.Opens)

/-- In two copies of `Y` glued along `V`, the open subscheme formed by the first copy and the
image of `W` in the second copy. -/
public noncomputable def opens : (doubleSectionCover Y V).total.Opens :=
  ((doubleSectionCover Y V).chart false).opensRange ⊔ (doubleSectionCover Y V).chart true ''ᵁ W

/-- The morphism to `Y`, restricting to the identity on the first copy and to the inclusion on
`W`. -/
public noncomputable def proj : (opens Y V W).toScheme ⟶ Y :=
  (opens Y V W).ι ≫ (doubleSectionCover Y V).proj

/-- The first copy of `Y`, as a section of `proj`. -/
public noncomputable def sec : Y ⟶ (opens Y V W).toScheme :=
  IsOpenImmersion.lift (opens Y V W).ι ((doubleSectionCover Y V).chart false) (by
    rw [Scheme.Opens.range_ι]
    intro x hx
    exact Opens.mem_sup.2 (Or.inl (Scheme.Hom.mem_opensRange.2 hx)))

/-- The section followed by the inclusion of the open subscheme is the first copy of `Y`. -/
@[reassoc (attr := simp)]
public lemma sec_ι : sec Y V W ≫ (opens Y V W).ι = (doubleSectionCover Y V).chart false :=
  IsOpenImmersion.lift_fac _ _ _

/-- The section is a section of `proj`. -/
@[reassoc (attr := simp)]
public lemma sec_proj : sec Y V W ≫ proj Y V W = 𝟙 Y := by
  simp [proj, (doubleSectionCover Y V).chart_comp_proj]

/-- A point of the open subscheme lies in the image of the section exactly when it lies in the
first copy. -/
public lemma mem_range_sec_iff (z : (opens Y V W).toScheme) :
    z ∈ Set.range (sec Y V W) ↔
      (opens Y V W).ι z ∈ Set.range ((doubleSectionCover Y V).chart false) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [← Scheme.Hom.comp_apply, sec_ι]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (opens Y V W).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, sec_ι, hy]

/-- A point of the open subscheme lies in the image of the section or over a point of `W` in the
second copy. -/
private lemma mem_range_sec_or (z : (opens Y V W).toScheme) :
    z ∈ Set.range (sec Y V W) ∨
      ∃ w ∈ W, (doubleSectionCover Y V).chart true w = (opens Y V W).ι z := by
  rcases Opens.mem_sup.1 z.2 with h0 | h1
  · exact Or.inl ((mem_range_sec_iff Y V W z).2 (Scheme.Hom.mem_opensRange.1 h0))
  · rw [← SetLike.mem_coe, Scheme.Hom.coe_image] at h1
    obtain ⟨w, hw, hwz⟩ := h1
    exact Or.inr ⟨w, hw, hwz⟩

/-- The two copies of a point of `V` are the same point of the glued scheme. -/
public lemma chart_true_apply_eq (v : V.toScheme) :
    (doubleSectionCover Y V).chart true (V.ι v) = (doubleSectionCover Y V).chart false (V.ι v) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, doubleSectionCover_chart_agree]

/-- A point lying on both copies lies over `V`. -/
public lemma mem_of_chart_true_eq_chart_false {y y' : Y}
    (e : (doubleSectionCover Y V).chart true y = (doubleSectionCover Y V).chart false y') :
    y ∈ V := by
  have hp := doubleSectionCover_isPullback_chart Y V (b := true) (c := false) (by decide)
  have hx : (doubleSectionCover Y V).chart true y ∈ Set.range
      (pullback.fst ((doubleSectionCover Y V).chart true) ((doubleSectionCover Y V).chart false) ≫
        (doubleSectionCover Y V).chart true) := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left]
    exact ⟨⟨y, rfl⟩, ⟨y', e.symm⟩⟩
  obtain ⟨q, hq⟩ := hx
  rw [← hp.isoPullback_inv_fst, Category.assoc, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply] at hq
  have hy := ((doubleSectionCover Y V).chart true).isOpenEmbedding.injective hq
  rw [← hy, ← SetLike.mem_coe, ← Scheme.Opens.range_ι]
  exact Set.mem_range_self _

/-- The complement of the section maps onto `W \ V`. -/
public lemma proj_image_compl_range_sec :
    proj Y V W '' (Set.range (sec Y V W))ᶜ = (W : Set Y) \ V := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases mem_range_sec_or Y V W z with h0 | ⟨w, hw, hwz⟩
    · exact absurd h0 hz
    · have hproj : proj Y V W z = w := by
        rw [proj, Scheme.Hom.comp_apply, ← hwz, ← Scheme.Hom.comp_apply,
          (doubleSectionCover Y V).chart_comp_proj]
        rfl
      rw [hproj]
      refine ⟨hw, fun hwV => hz ((mem_range_sec_iff Y V W z).2 ⟨w, ?_⟩)⟩
      rw [← hwz]
      simpa using (chart_true_apply_eq Y V ⟨w, hwV⟩).symm
  · rintro ⟨hyW, hyV⟩
    have hmem : (doubleSectionCover Y V).chart true y ∈ opens Y V W :=
      Opens.mem_sup.2 (Or.inr (by
        rw [← SetLike.mem_coe, Scheme.Hom.coe_image]
        exact ⟨y, hyW, rfl⟩))
    let z : (opens Y V W).toScheme := ⟨(doubleSectionCover Y V).chart true y, hmem⟩
    refine ⟨z, fun hz => hyV ?_, ?_⟩
    · obtain ⟨y', hy'⟩ := (mem_range_sec_iff Y V W z).1 hz
      exact mem_of_chart_true_eq_chart_false Y V hy'.symm
    · show (doubleSectionCover Y V).proj ((doubleSectionCover Y V).chart true y) = y
      rw [← Scheme.Hom.comp_apply, (doubleSectionCover Y V).chart_comp_proj]
      rfl

/-- If `W \ V` is not closed in `Y`, the morphism is not universally closed: it is not even
closed. -/
public theorem not_universallyClosed_proj (hWV : ¬ IsClosed ((W : Set Y) \ V)) :
    ¬ UniversallyClosed (proj Y V W) := by
  intro _
  have hrange : Set.range (sec Y V W) =
      (opens Y V W).ι ⁻¹' Set.range ((doubleSectionCover Y V).chart false) :=
    Set.ext (mem_range_sec_iff Y V W)
  have hopen : IsOpen (Set.range (sec Y V W)) := by
    rw [hrange]
    exact ((doubleSectionCover Y V).chart false).isOpenEmbedding.isOpen_range.preimage
      (opens Y V W).ι.continuous
  exact hWV (proj_image_compl_range_sec Y V W ▸ (proj Y V W).isClosedMap _ hopen.isClosed_compl)

/-- If `V` is dense in `Y`, the section has dense image. -/
public theorem denseRange_sec (hV : Dense (V : Set Y)) : DenseRange (sec Y V W) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro N hN ⟨z, hzN⟩
  rcases mem_range_sec_or Y V W z with h0 | ⟨w, -, hwz⟩
  · exact ⟨z, hzN, h0⟩
  · let N' : Set Y := (doubleSectionCover Y V).chart true ⁻¹' ((opens Y V W).ι '' N)
    have hN' : IsOpen N' :=
      ((opens Y V W).ι.isOpenEmbedding.isOpenMap _ hN).preimage
        ((doubleSectionCover Y V).chart true).continuous
    obtain ⟨v, hvN', hvV⟩ := hV.inter_open_nonempty N' hN' ⟨w, ⟨z, hzN, hwz.symm⟩⟩
    obtain ⟨n, hnN, hn⟩ := hvN'
    refine ⟨n, hnN, (mem_range_sec_iff Y V W n).2 ⟨v, ?_⟩⟩
    rw [hn]
    simpa using (chart_true_apply_eq Y V ⟨v, hvV⟩).symm

/-- Every valuative square for `proj` whose generic-point map factors through the section has a
lift, since the section splits `proj`. -/
public theorem hasLift (D : ValuativeCommSq (proj Y V W)) (g : Spec (.of D.K) ⟶ Y)
    (hg : g ≫ sec Y V W = D.i₁) : D.commSq.HasLift := by
  refine ⟨⟨⟨D.i₂ ≫ sec Y V W, ?_, by simp⟩⟩⟩
  rw [← Category.assoc, ← D.commSq.w, ← hg]
  simp

section Noetherian

variable [IsNoetherian Y]

/-- Two copies of a noetherian scheme glued along an open form a locally noetherian scheme. -/
instance isLocallyNoetherian_total : IsLocallyNoetherian (doubleSectionCover Y V).total := by
  rw [isLocallyNoetherian_iff_openCover (doubleSectionCover Y V).cover]
  intro _
  change IsLocallyNoetherian Y
  infer_instance

/-- Two copies of a noetherian scheme glued along an open form a noetherian scheme. -/
instance isNoetherian_total : IsNoetherian (doubleSectionCover Y V).total where
  toCompactSpace := (doubleSectionCover Y V).compactSpace_total

/-- The open subscheme `opens Y V W` is quasi-compact when `Y` is noetherian. -/
instance compactSpace_opens : CompactSpace (opens Y V W).toScheme := by
  rw [← isCompact_univ_iff, (opens Y V W).ι.isOpenEmbedding.isCompact_iff, Set.image_univ,
    Scheme.Opens.range_ι]
  exact NoetherianSpace.isCompact _

/-- For noetherian `Y`, the morphism `proj` is quasi-compact. -/
public lemma quasiCompact_proj : QuasiCompact (proj Y V W) := quasiCompact_of_compactSpace _

/-- For noetherian `Y`, the section `sec` is quasi-compact. -/
public lemma quasiCompact_sec : QuasiCompact (sec Y V W) := quasiCompact_of_compactSpace _

end Noetherian

end RefinedValuativeNecessity

section Plane

variable (k : Type u) [Field k]

/-- The open subscheme `D(xy)` of the affine plane. -/
public noncomputable def planeBasicOpenXY : (Spec (.of (MvPolynomial (Fin 2) k))).Opens :=
  PrimeSpectrum.basicOpen (MvPolynomial.X 0 * MvPolynomial.X 1)

/-- The open subscheme `D(y)` of the affine plane. -/
public noncomputable def planeBasicOpenY : (Spec (.of (MvPolynomial (Fin 2) k))).Opens :=
  PrimeSpectrum.basicOpen (MvPolynomial.X 1)

/-- `D(xy)` is dense in the affine plane. -/
public theorem dense_planeBasicOpenXY :
    Dense (planeBasicOpenXY k : Set (Spec (.of (MvPolynomial (Fin 2) k)))) := by
  refine (planeBasicOpenXY k).2.dense ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  show MvPolynomial.X 0 * MvPolynomial.X 1 ∉ (⊥ : Ideal (MvPolynomial (Fin 2) k))
  rw [Ideal.mem_bot]
  exact mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)

/-- `D(y) \ D(xy) = D(y) ∩ V(x)` is not closed in the affine plane: the point `(x)` lies in it and
specialises to the origin, which does not. -/
public theorem not_isClosed_planeBasicOpenY_sdiff :
    ¬ IsClosed ((planeBasicOpenY k : Set (Spec (.of (MvPolynomial (Fin 2) k)))) \
      planeBasicOpenXY k) := by
  let φ : MvPolynomial (Fin 2) k →+* Polynomial k :=
    MvPolynomial.eval₂Hom Polynomial.C ![0, Polynomial.X]
  let ε : MvPolynomial (Fin 2) k →+* k := MvPolynomial.eval 0
  have hcomp : (Polynomial.evalRingHom 0).comp φ = ε := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [φ, ε]
    · fin_cases i <;> simp [φ, ε]
  let p : PrimeSpectrum (↑(CommRingCat.of (MvPolynomial (Fin 2) k))) :=
    ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  let m : PrimeSpectrum (↑(CommRingCat.of (MvPolynomial (Fin 2) k))) :=
    ⟨RingHom.ker ε, RingHom.ker_isPrime ε⟩
  have hpY : p ∈ (planeBasicOpenY k : Set (Spec (.of (MvPolynomial (Fin 2) k)))) := by
    show MvPolynomial.X 1 ∉ RingHom.ker φ
    simp [φ]
  have hpXY : p ∉ (planeBasicOpenXY k : Set (Spec (.of (MvPolynomial (Fin 2) k)))) := by
    show ¬ (MvPolynomial.X 0 * MvPolynomial.X 1 ∉ RingHom.ker φ)
    simp [φ]
  have hmY : m ∉ (planeBasicOpenY k : Set (Spec (.of (MvPolynomial (Fin 2) k)))) := by
    show ¬ (MvPolynomial.X 1 ∉ RingHom.ker ε)
    simp [ε]
  have hpm : m ∈ closure ({p} : Set (Spec (.of (MvPolynomial (Fin 2) k)))) := by
    show m ∈ closure ({p} : Set (PrimeSpectrum (↑(CommRingCat.of (MvPolynomial (Fin 2) k)))))
    rw [← PrimeSpectrum.le_iff_mem_closure]
    intro q hq
    show ε q = 0
    rw [← hcomp, RingHom.comp_apply, RingHom.mem_ker.1 hq, map_zero]
  intro hcl
  have hp : p ∈ (planeBasicOpenY k : Set (Spec (.of (MvPolynomial (Fin 2) k)))) \
      planeBasicOpenXY k := ⟨hpY, hpXY⟩
  exact hmY (closure_minimal (Set.singleton_subset_iff.2 hp) hcl hpm).1

end Plane

/-- Over any field `k`, the affine plane glued with `D(y)` along `D(xy)` is a counterexample to
the refined valuative criterion without uniqueness: its morphism to the plane is quasi-compact
and quasi-separated, the section given by the plane is quasi-compact with dense image, every
valuative square through the section has a lift, and the morphism is neither universally closed
nor separated. -/
public theorem RefinedValuativeNecessity.plane_counterexample (k : Type u) [Field k] :
    QuasiCompact (RefinedValuativeNecessity.proj _ (planeBasicOpenXY k) (planeBasicOpenY k)) ∧
      QuasiCompact (RefinedValuativeNecessity.sec _ (planeBasicOpenXY k) (planeBasicOpenY k)) ∧
      QuasiSeparated (RefinedValuativeNecessity.proj _ (planeBasicOpenXY k) (planeBasicOpenY k)) ∧
      DenseRange (RefinedValuativeNecessity.sec _ (planeBasicOpenXY k) (planeBasicOpenY k)) ∧
      (∀ (D : ValuativeCommSq
          (RefinedValuativeNecessity.proj _ (planeBasicOpenXY k) (planeBasicOpenY k)))
        (g : Spec (.of D.K) ⟶ Spec (.of (MvPolynomial (Fin 2) k))),
        g ≫ RefinedValuativeNecessity.sec _ (planeBasicOpenXY k) (planeBasicOpenY k) = D.i₁ →
          D.commSq.HasLift) ∧
      ¬ UniversallyClosed
        (RefinedValuativeNecessity.proj _ (planeBasicOpenXY k) (planeBasicOpenY k)) ∧
      ¬ IsSeparated
        (RefinedValuativeNecessity.proj _ (planeBasicOpenXY k) (planeBasicOpenY k)) := by
  have hqcf := RefinedValuativeNecessity.quasiCompact_proj _ (planeBasicOpenXY k)
    (planeBasicOpenY k)
  have hqch := RefinedValuativeNecessity.quasiCompact_sec _ (planeBasicOpenXY k)
    (planeBasicOpenY k)
  have hdense := RefinedValuativeNecessity.denseRange_sec _ (planeBasicOpenXY k)
    (planeBasicOpenY k) (dense_planeBasicOpenXY k)
  have hlift := RefinedValuativeNecessity.hasLift _ (planeBasicOpenXY k) (planeBasicOpenY k)
  have hnuc := RefinedValuativeNecessity.not_universallyClosed_proj _ (planeBasicOpenXY k)
    (planeBasicOpenY k) (not_isClosed_planeBasicOpenY_sdiff k)
  refine ⟨hqcf, hqch, inferInstance, hdense, hlift, hnuc,
    fun hsep => hnuc ?_⟩
  have := hsep
  exact universallyClosed_of_hasLift_of_denseRange_of_isSeparated _ _ hdense hlift

/-- The uniqueness of the dotted arrows in the refined valuative criterion
`universallyClosed_of_unique_lift_of_denseRange` cannot be dropped. There are quasi-compact
morphisms `f : X ⟶ S` and `h : U ⟶ X`, with `f` quasi-separated and `h(U)` dense in `X`, such
that every commutative square from `Spec K ⟶ Spec A` (with `A` a valuation ring with fraction
field `K`) whose top map factors through `h` admits a dotted arrow, while `f` is neither
universally closed nor separated. -/
@[stacks 0895 "the uniqueness assumption of Lemma 0894 is necessary"]
public theorem exists_hasLift_of_denseRange_not_universallyClosed_not_isSeparated :
    ∃ (U X S : Scheme.{u}) (h : U ⟶ X) (f : X ⟶ S),
      QuasiCompact f ∧ QuasiCompact h ∧ QuasiSeparated f ∧ DenseRange h ∧
      (∀ (D : ValuativeCommSq f) (g : Spec (.of D.K) ⟶ U),
        g ≫ h = D.i₁ → D.commSq.HasLift) ∧
      ¬ UniversallyClosed f ∧ ¬ IsSeparated f :=
  ⟨_, _, _, _, _, RefinedValuativeNecessity.plane_counterexample (ULift.{u} ℚ)⟩

end AlgebraicGeometry

end
