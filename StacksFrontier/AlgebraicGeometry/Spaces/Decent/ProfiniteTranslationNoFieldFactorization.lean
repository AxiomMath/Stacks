module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedToResidualSpaceFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteFreeActionSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceFieldSpectrum

/-!
# A reduced singleton algebraic space with no field-valued point

Let `k` be a field, let `G` be an infinite profinite group and let `A` be the ring of locally
constant maps `G → k`. The spectrum `Y = Spec A` is a zero-dimensional affine `k`-scheme, the
group `G` viewed as a discrete `k`-group scheme `Γ` acts on it by translations, and the
quotient `X = Y/Γ` is a one-point algebraic space with projection `q : Y ⟶ X`. The origin of
`G` gives a `k`-point `x` of `X`, a monomorphism because it is a section of `X → Spec k`.

Although `Y` is affine and reduced and `|X| = {x}`, the morphism `q` factors through no
morphism `Spec K → X` with `K` a field. So the conclusion of Stacks 0H1S and of Stacks 0H1T
fails for `q`, and `X` is neither locally Noetherian nor decent: the hypotheses of those two
lemmas cannot be dropped.

## Main definitions

* `AlgebraicGeometry.ProfiniteTranslation.evaluationPrime`: the prime of `A` of locally
  constant functions vanishing at a point of `G`, that is, the `k`-point of `Y` there.
* `AlgebraicGeometry.ProfiniteTranslation.translationAction`: the translation action of `G`
  on `Y` over `Spec k`.
* `AlgebraicGeometry.ProfiniteTranslation.profiniteTranslationQuotient`: the quotient `X = Y/Γ`,
  with projection `AlgebraicGeometry.ProfiniteTranslation.profiniteQuotientMap`.
* `AlgebraicGeometry.ProfiniteTranslation.originQuotientPoint`: the `k`-point `x` of `X`
  coming from the origin of `G`.

## Main results

* `AlgebraicGeometry.ProfiniteTranslation.evaluationPrime_bijective`: the points of `Y` are
  the points of `G`.
* `AlgebraicGeometry.ProfiniteTranslation.actsFreelyOnNonemptyPoints_translationAction`: the
  translation action is free.
* `AlgebraicGeometry.ProfiniteTranslation.subsingleton_points_profiniteTranslationQuotient`:
  `X` has exactly one point.
* `AlgebraicGeometry.Space.not_isLocallyNoetherian_and_not_isDecentSpace_of_not_exists_section`:
  `X` is a one-point algebraic space over the reduced affine `Y`, the `k`-point of `X` is a
  monomorphism, and `q` factors through no field-valued point of `X`.
* `AlgebraicGeometry.Space.not_isLocallyNoetherian_and_not_isDecentSpace`: consequently `X`
  is neither locally Noetherian nor decent, and `q` factors through no residual space of `X`.

## References

* [Stacks Project, Tag 0H2Y](https://stacks.math.columbia.edu/tag/0H2Y)
* [Stacks Project, Tag 0H1R](https://stacks.math.columbia.edu/tag/0H1R)
* [Stacks Project, Tag 0H1S](https://stacks.math.columbia.edu/tag/0H1S)
* [Stacks Project, Tag 0H1T](https://stacks.math.columbia.edu/tag/0H1T)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ProfiniteTranslation

variable (k G : Type u) [Field k] [TopologicalSpace G]

/-! ### The ring of locally constant functions -/

/-- The locally constant function taking the value `1` on a clopen set and `0` off it. -/
def clopenIndicator (U : Set G) [DecidablePred (· ∈ U)] (hU : IsClopen U) :
    LocallyConstant G k where
  toFun x := if x ∈ U then 1 else 0
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ U
    · exact ⟨U, hU.2, hx, fun y hy => by simp [hx, hy]⟩
    · exact ⟨Uᶜ, hU.1.isOpen_compl, hx, fun y hy => by simpa [hx] using hy⟩

/-- The prime ideal of locally constant functions `G → k` vanishing at `g`. Equivalently, the
`k`-point of `Spec (LocallyConstant G k)` given by evaluation at `g`; for `G` profinite these
are all the points. -/
def evaluationPrime (g : G) : PrimeSpectrum (LocallyConstant G k) :=
  PrimeSpectrum.comap (LocallyConstant.evalRingHom g) ⟨⊥, inferInstance⟩

/-- A locally constant function lies in the evaluation prime at `g` exactly when it vanishes
at `g`. -/
theorem mem_evaluationPrime_iff (g : G) (f : LocallyConstant G k) :
    f ∈ (evaluationPrime k G g).asIdeal ↔ f g = 0 := by
  simp [evaluationPrime, PrimeSpectrum.comap, Ideal.mem_comap]

/-- The evaluation prime at `g` lies in the basic open of `f` exactly when `f g ≠ 0`. -/
theorem evaluationPrime_mem_basicOpen_iff (g : G) (f : LocallyConstant G k) :
    evaluationPrime k G g ∈ PrimeSpectrum.basicOpen f ↔ f g ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen, mem_evaluationPrime_iff]

/-- On a profinite space, distinct points have distinct evaluation primes: a clopen set
separating them gives a locally constant function vanishing at one and not the other. -/
theorem evaluationPrime_injective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    Function.Injective (evaluationPrime k G) := by
  classical
  intro g h hgh
  by_contra hne
  obtain ⟨U, hU, hgU, hhU⟩ := exists_isClopen_of_totally_separated hne
  have h1 : clopenIndicator k G U hU g = 1 := by simp [clopenIndicator, hgU]
  have h0 : clopenIndicator k G U hU g = 0 := by
    rw [← mem_evaluationPrime_iff, hgh, mem_evaluationPrime_iff]
    simp only [clopenIndicator, LocallyConstant.coe_mk, ite_eq_right_iff, one_ne_zero,
      imp_false]
    exact hhU
  exact one_ne_zero (h1 ▸ h0 : (1 : k) = 0)

open scoped Classical in
/-- The indicator of a clopen set as a locally constant function, with membership decided
classically. -/
def clopenInd (U : Set G) (hU : IsClopen U) : LocallyConstant G k :=
  clopenIndicator k G U hU

open scoped Classical in
/-- The indicator of a clopen set `U` takes the value `1` at points of `U` and `0` elsewhere. -/
@[simp]
theorem clopenInd_apply (U : Set G) (hU : IsClopen U) (x : G) :
    clopenInd k G U hU x = if x ∈ U then 1 else 0 := rfl

/-- The indicator of the whole space is the constant function `1`. -/
@[simp]
theorem clopenInd_univ : clopenInd k G Set.univ isClopen_univ = 1 := by
  ext x; simp

/-- The indicator of the empty set is the zero function. -/
@[simp]
theorem clopenInd_empty : clopenInd k G (∅ : Set G) isClopen_empty = 0 := by
  ext x; simp

/-- Indicators multiply to the indicator of the intersection. -/
theorem clopenInd_mul (U V : Set G) (hU : IsClopen U) (hV : IsClopen V) :
    clopenInd k G U hU * clopenInd k G V hV = clopenInd k G (U ∩ V) (hU.inter hV) := by
  ext x
  by_cases hx : x ∈ U <;> by_cases hy : x ∈ V <;> simp [hx, hy]

/-- The indicators of a clopen set and of its complement sum to `1`. -/
theorem clopenInd_add_compl (U : Set G) (hU : IsClopen U) :
    clopenInd k G U hU + clopenInd k G Uᶜ hU.compl = 1 := by
  ext x
  by_cases hx : x ∈ U <;> simp [hx]

/-- On a profinite space the evaluation primes exhaust the spectrum: every prime of the ring
of locally constant maps `G → k` is the prime of functions vanishing at some point. -/
theorem evaluationPrime_surjective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    Function.Surjective (evaluationPrime k G) := by
  intro P
  let good : Set G → Prop := fun U => ∃ h : IsClopen U, clopenInd k G U h ∉ P.asIdeal
  have hone : (1 : LocallyConstant G k) ∉ P.asIdeal := fun h =>
    P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  have huniv : good Set.univ := ⟨isClopen_univ, by rwa [clopenInd_univ]⟩
  have : Nonempty {U : Set G // good U} := ⟨⟨Set.univ, huniv⟩⟩
  have hinter : ∀ U V : Set G, good U → good V → good (U ∩ V) := by
    rintro U V ⟨hU, hUP⟩ ⟨hV, hVP⟩
    refine ⟨hU.inter hV, fun hmem => ?_⟩
    rw [← clopenInd_mul k G U V hU hV] at hmem
    exact (P.isPrime.mem_or_mem hmem).elim hUP hVP
  have hne : ∀ U : Set G, good U → U.Nonempty := by
    rintro U ⟨hU, hUP⟩
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    refine hUP ?_
    rw [show clopenInd k G (∅ : Set G) hU = 0 from clopenInd_empty k G]
    exact Ideal.zero_mem _
  obtain ⟨g, hg⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (t := fun U : {U : Set G // good U} => U.1)
      (fun U V => ⟨⟨U.1 ∩ V.1, hinter U.1 V.1 U.2 V.2⟩,
        Set.inter_subset_left, Set.inter_subset_right⟩)
      (fun U => hne U.1 U.2) (fun U => U.2.choose.1.isCompact) (fun U => U.2.choose.1)
  simp only [Set.mem_iInter] at hg
  have hmem : ∀ (U : Set G) (hU : IsClopen U), g ∈ U → clopenInd k G U hU ∉ P.asIdeal := by
    intro U hU hgU hP
    refine absurd (hg ⟨Uᶜ, hU.compl, fun hP' => ?_⟩) (by simpa using hgU)
    refine hone ?_
    rw [← clopenInd_add_compl k G U hU]
    exact Ideal.add_mem _ hP hP'
  refine ⟨g, PrimeSpectrum.ext (Ideal.ext fun f => ?_)⟩
  rw [mem_evaluationPrime_iff]
  constructor
  · intro hfg
    have hV : IsClopen {x : G | (f : G → k) x = 0} := f.isLocallyConstant.isClopen_fiber _
    have hzero : f * clopenInd k G _ hV = 0 := by
      ext x
      by_cases hx : (f : G → k) x = 0 <;> simp [hx]
    exact (P.isPrime.mem_or_mem (hzero ▸ Ideal.zero_mem P.asIdeal)).resolve_right (hmem _ hV hfg)
  · intro hf
    by_contra hfg
    have hU : IsClopen {x : G | (f : G → k) x = (f : G → k) g} :=
      f.isLocallyConstant.isClopen_fiber _
    have hkey : LocallyConstant.const G ((f : G → k) g) * clopenInd k G _ hU =
        f * clopenInd k G _ hU := by
      ext x
      by_cases hx : (f : G → k) x = (f : G → k) g <;> simp [hx]
    have h1 : LocallyConstant.const G ((f : G → k) g) * clopenInd k G _ hU ∈ P.asIdeal :=
      hkey ▸ Ideal.mul_mem_right _ _ hf
    refine hmem _ hU rfl ?_
    have h2 : clopenInd k G _ hU = LocallyConstant.const G ((f : G → k) g)⁻¹ *
        (LocallyConstant.const G ((f : G → k) g) * clopenInd k G _ hU) := by
      ext x
      simp [inv_mul_cancel₀ hfg]
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1

/-- On a profinite space the evaluation primes are exactly the points: the spectrum of the
ring of locally constant maps `G → k` is `G` as a set. -/
theorem evaluationPrime_bijective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    Function.Bijective (evaluationPrime k G) :=
  ⟨evaluationPrime_injective k G, evaluationPrime_surjective k G⟩

/-! ### Reading off the summand of a coproduct -/

/-- The base map of a descent out of a coproduct, on the summand indexed by `i`. -/
theorem sigmaDesc_base_sigmaMk {ι : Type u} (X : ι → Scheme.{u}) {W : Scheme.{u}}
    (f : ∀ i, X i ⟶ W) (i : ι) (y : ↥(X i)) :
    (Sigma.desc f) (AlgebraicGeometry.sigmaMk X ⟨i, y⟩) = (f i) y := by
  rw [AlgebraicGeometry.sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_desc]

/-- The index of the summand into which a morphism to a coproduct of schemes sends a
point. -/
def sigmaIndexOf {ι : Type u} (X : ι → Scheme.{u}) {W : Scheme.{u}} (ρ : W ⟶ ∐ X)
    (z : ↥W) : ι :=
  ((AlgebraicGeometry.sigmaMk X).symm (ρ z)).1

/-- The summands of a coproduct of schemes are open, so the index map has open fibres. -/
theorem isOpen_preimage_sigmaIndexOf {ι : Type u} (X : ι → Scheme.{u}) {W : Scheme.{u}}
    (ρ : W ⟶ ∐ X) (i : ι) : IsOpen (sigmaIndexOf X ρ ⁻¹' {i}) := by
  classical
  have hsig : IsOpen {p : (j : ι) × ↥(X j) | p.1 = i} := by
    rw [isOpen_sigma_iff]
    intro j
    by_cases hj : j = i <;> simp [hj, Set.preimage_ofPred_eq]
  have hpre : sigmaIndexOf X ρ ⁻¹' {i} =
      (fun z => ρ z) ⁻¹' (AlgebraicGeometry.sigmaMk X '' {p | p.1 = i}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ← Homeomorph.preimage_symm]
    rfl
  rw [hpre]
  exact ((AlgebraicGeometry.sigmaMk X).isOpen_image.mpr hsig).preimage ρ.base.hom.continuous

/-- A morphism to a coproduct of copies of `W` which splits the codiagonal sends a point to
itself in the summand its index names. -/
theorem base_eq_sigmaMk_sigmaIndexOf {ι : Type u} {W : Scheme.{u}}
    (ρ : W ⟶ ∐ fun _ : ι => W) (hρ : ρ ≫ Sigma.desc (fun _ : ι => 𝟙 W) = 𝟙 W) (z : ↥W) :
    ρ z =
      AlgebraicGeometry.sigmaMk (fun _ : ι => W) ⟨sigmaIndexOf (fun _ : ι => W) ρ z, z⟩ := by
  have hz : (Sigma.desc fun _ : ι => 𝟙 W) (ρ z) = z := by
    rw [← Scheme.Hom.comp_apply, hρ]
    simp
  conv_lhs => rw [← Homeomorph.apply_symm_apply
    (AlgebraicGeometry.sigmaMk (fun _ : ι => W)) (ρ z)]
  congr 1
  refine Sigma.ext rfl ?_
  rw [heq_eq_eq]
  have := sigmaDesc_base_sigmaMk (fun _ : ι => W) (fun _ : ι => 𝟙 W)
    (((AlgebraicGeometry.sigmaMk (fun _ : ι => W)).symm (ρ z)).1)
    (((AlgebraicGeometry.sigmaMk (fun _ : ι => W)).symm (ρ z)).2)
  rw [Sigma.eta, Homeomorph.apply_symm_apply, hz] at this
  simpa using this.symm

/-! ### Field-valued points of the spectrum -/

/-- Evaluation at a point splits the structure map of `LocallyConstant G k` as a
`k`-algebra: a constant function takes its own value everywhere. -/
theorem evalRingHom_comp_algebraMap (w : G) :
    (LocallyConstant.evalRingHom w : LocallyConstant G k →+* k).comp
        (algebraMap k (LocallyConstant G k)) =
      RingHom.id k :=
  RingHom.ext fun _ => rfl

/-- The `k`-point of `Y = Spec (LocallyConstant G k)` at `w` is a section of the structure
morphism of `Y` over `Spec k`. -/
theorem specMap_evalRingHom_comp_specMap_algebraMap (w : G) :
    Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom w)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (LocallyConstant G k))) =
      𝟙 (Spec (CommRingCat.of k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, evalRingHom_comp_algebraMap]
  simp

section Profinite

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A ring map from the locally constant maps `G → k` to a field is evaluation at a point of
`G` followed by a map of fields. -/
theorem exists_eq_comp_evalRingHom {K : Type v} [Field K] (φ : LocallyConstant G k →+* K) :
    ∃ (w : G) (ι : k →+* K), φ = ι.comp (LocallyConstant.evalRingHom w) := by
  obtain ⟨w, hw⟩ := evaluationPrime_surjective k G
    (PrimeSpectrum.comap φ (⟨⊥, inferInstance⟩ : PrimeSpectrum K))
  have hvanish : ∀ f : LocallyConstant G k,
      LocallyConstant.evalRingHom w f = 0 → φ f = 0 := by
    intro f hf
    have hmem : f ∈ (evaluationPrime k G w).asIdeal :=
      (mem_evaluationPrime_iff k G w f).2 hf
    rw [hw] at hmem
    simpa [PrimeSpectrum.comap, Ideal.mem_comap] using hmem
  refine ⟨w, φ.comp LocallyConstant.constRingHom, RingHom.ext fun f => ?_⟩
  have hdiff : φ (f - LocallyConstant.const G (LocallyConstant.evalRingHom w f)) = 0 := by
    refine hvanish _ ?_
    rw [map_sub, sub_eq_zero]
    rfl
  rwa [map_sub, sub_eq_zero] at hdiff

/-- Every morphism from the spectrum of a field to `Y = Spec (LocallyConstant G k)` factors
through the `k`-point of `Y` at some point of `G`. -/
theorem exists_eq_comp_specMap_evalRingHom {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ Spec (.of (LocallyConstant G k))) :
    ∃ (w : G) (g : Spec (.of K) ⟶ Spec (.of k)),
      f = g ≫ Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom w)) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨w, ι, hι⟩ := exists_eq_comp_evalRingHom k G φ.hom
  refine ⟨w, Spec.map (CommRingCat.ofHom ι), ?_⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hι, CommRingCat.ofHom_hom]

/-- A field-valued point of `Y` lying over a given point of the base factors through the
`k`-point of `Y` at some `w`, and the factoring morphism is the structure morphism itself,
because the `k`-point at `w` is a section of `Y → Spec k`. -/
theorem exists_eq_comp_specMap_evalRingHom_of_comp_eq {K : Type u} [Field K]
    (p : Spec (.of K) ⟶ Spec (.of k))
    (f : Spec (.of K) ⟶ Spec (.of (LocallyConstant G k)))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap k (LocallyConstant G k))) = p) :
    ∃ w : G, f = p ≫ Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom w)) := by
  obtain ⟨w, g, hg⟩ := exists_eq_comp_specMap_evalRingHom k G f
  refine ⟨w, ?_⟩
  rw [show p = g from ?_, ← hg]
  rw [← hf, hg, Category.assoc, specMap_evalRingHom_comp_specMap_algebraMap, Category.comp_id]

end Profinite

/-! ### The translation action on the spectrum -/

section Translation

variable [Group G] [ContinuousMul G]

/-- Translation by `g` as a ring automorphism of the locally constant maps `G → k`: it
carries `f` to `x ↦ f (g * x)`. -/
def translationRingEquiv (g : G) : LocallyConstant G k ≃+* LocallyConstant G k :=
  LocallyConstant.congrLeftRingEquiv (Homeomorph.mulLeft g).symm

/-- Translation by `g` carries `f` to the function `x ↦ f (g * x)`. -/
@[simp]
theorem translationRingEquiv_apply (g : G) (f : LocallyConstant G k) (x : G) :
    translationRingEquiv k G g f x = f (g * x) := rfl

/-- Translating by `g` and then by `h` is translating by `h * g`. -/
theorem translationRingEquiv_translationRingEquiv (g h : G) (f : LocallyConstant G k) :
    translationRingEquiv k G g (translationRingEquiv k G h f) =
      translationRingEquiv k G (h * g) f := by
  ext x; simp [mul_assoc]

/-- Translation by the origin is the identity. -/
theorem translationRingEquiv_one (f : LocallyConstant G k) :
    translationRingEquiv k G 1 f = f := by
  ext x; simp

/-- Translation by `g` carries the evaluation prime at `h` to the evaluation prime at the
translate `g * h`: on the spectrum the translation action is the translation action of `G`
on itself. -/
theorem comap_translationRingEquiv_evaluationPrime (g h : G) :
    PrimeSpectrum.comap (translationRingEquiv k G g).toRingHom (evaluationPrime k G h) =
      evaluationPrime k G (g * h) := by
  refine PrimeSpectrum.ext (Ideal.ext fun f => ?_)
  show (translationRingEquiv k G g) f ∈ (evaluationPrime k G h).asIdeal ↔ _
  rw [mem_evaluationPrime_iff, mem_evaluationPrime_iff, translationRingEquiv_apply]

/-- The translation action is transitive on the spectrum: for `G` profinite every point of
`Spec (LocallyConstant G k)` is a translate of the evaluation prime at the origin. -/
theorem exists_comap_translationRingEquiv_evaluationPrime_one_eq [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (z : PrimeSpectrum (LocallyConstant G k)) :
    ∃ g : G, PrimeSpectrum.comap (translationRingEquiv k G g).toRingHom
      (evaluationPrime k G 1) = z := by
  obtain ⟨g, rfl⟩ := evaluationPrime_surjective k G z
  exact ⟨g, by rw [comap_translationRingEquiv_evaluationPrime, mul_one]⟩

/-- Translating by `h` and then by `g`, as a composite of ring maps. -/
theorem translationRingEquiv_comp (g h : G) :
    (translationRingEquiv k G g).toRingHom.comp (translationRingEquiv k G h).toRingHom =
      (translationRingEquiv k G (h * g)).toRingHom :=
  RingHom.ext fun f => translationRingEquiv_translationRingEquiv k G g h f

/-- Translation by the origin is the identity ring map. -/
theorem translationRingEquiv_one_eq :
    (translationRingEquiv k G 1).toRingHom = RingHom.id (LocallyConstant G k) :=
  RingHom.ext fun f => translationRingEquiv_one k G f

/-- Translation fixes the constants, so it is a map of `k`-algebras. -/
theorem translationRingEquiv_comp_algebraMap (g : G) :
    (translationRingEquiv k G g).toRingHom.comp (algebraMap k (LocallyConstant G k)) =
      algebraMap k (LocallyConstant G k) :=
  RingHom.ext fun _ => rfl

end Translation

/-- On an infinite profinite group, an open set of the spectrum containing the evaluation prime
at the origin contains the evaluation prime at some other point: a basic open neighbourhood of
the origin is the nonvanishing locus of a locally constant function, and if it met no other
evaluation prime the origin would be open in `G`, hence `G` discrete and so finite. -/
private theorem exists_ne_one_evaluationPrime_mem_of_isOpen [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Infinite G]
    {O : Set (PrimeSpectrum (LocallyConstant G k))} (hO : IsOpen O)
    (h1 : evaluationPrime k G 1 ∈ O) : ∃ g : G, g ≠ 1 ∧ evaluationPrime k G g ∈ O := by
  by_contra hno
  push Not at hno
  obtain ⟨v, hv, hmem, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h1 hO
  obtain ⟨f, rfl⟩ := hv
  have hf1 : (f : G → k) 1 ≠ 0 := (evaluationPrime_mem_basicOpen_iff k G 1 f).mp hmem
  have hsingle : {x : G | (f : G → k) x ≠ 0} = {1} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hf1, fun g hg => ?_⟩
    by_contra hg1
    exact hno g hg1 (hsub ((evaluationPrime_mem_basicOpen_iff k G g f).mpr hg))
  have hopen1 : IsOpen ({1} : Set G) := by
    rw [← hsingle]
    exact f.isLocallyConstant {0}ᶜ
  have : DiscreteTopology G := discreteTopology_iff_isOpen_singleton_one.mpr hopen1
  have : Finite G := finite_of_compact_of_discrete
  exact not_finite G

/-- On an infinite profinite group the origin is not an open point of the spectrum: a basic
open neighbourhood of it would be the nonvanishing locus of a locally constant function
supported at the origin, making the origin open in `G`, hence `G` discrete and so finite. -/
theorem not_isOpen_singleton_evaluationPrime [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] [Infinite G] :
    ¬ IsOpen ({evaluationPrime k G 1} : Set (PrimeSpectrum (LocallyConstant G k))) := by
  intro hopen
  obtain ⟨g, hg, hmem⟩ := exists_ne_one_evaluationPrime_mem_of_isOpen k G hopen rfl
  exact hg (evaluationPrime_injective k G hmem)

/-! ### The spectrum as a scheme over `Spec k`, and the translation action on it -/

section Action

variable [Group G] [ContinuousMul G]

/-- `Y = Spec (LocallyConstant G k)`, the group `G` viewed as a zero-dimensional affine
`k`-scheme, as an object over `Spec k`. -/
def profiniteSpec : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (LocallyConstant G k))))

/-- The underlying scheme of `profiniteSpec k G` is `Spec (LocallyConstant G k)`. -/
theorem profiniteSpec_left : (profiniteSpec k G).left = Spec (.of (LocallyConstant G k)) := rfl

/-- Translation by `g` as an automorphism of the scheme `Y = Spec (LocallyConstant G k)`. On
points it carries the evaluation prime at `w` to the evaluation prime at `g * w`. -/
def translationSpecIso (g : G) :
    Spec (.of (LocallyConstant G k)) ≅ Spec (.of (LocallyConstant G k)) where
  hom := Spec.map (CommRingCat.ofHom (translationRingEquiv k G g).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (translationRingEquiv k G g⁻¹).toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, translationRingEquiv_comp,
      inv_mul_cancel, translationRingEquiv_one_eq]
    simp
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, translationRingEquiv_comp,
      mul_inv_cancel, translationRingEquiv_one_eq]
    simp

/-- Translation by `g` as an automorphism of `Y` over `Spec k`. -/
def translationAut (g : G) : Aut (profiniteSpec k G) :=
  Over.isoMk (translationSpecIso k G g)
    (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, translationRingEquiv_comp_algebraMap])

/-- The underlying morphism of schemes of `translationAut k G g` is the spectrum of translation by
`g`. -/
theorem translationAut_hom_left (g : G) :
    (translationAut k G g).hom.left =
      Spec.map (CommRingCat.ofHom (translationRingEquiv k G g).toRingHom) := rfl

/-- The translation action of `G` on `Y = Spec (LocallyConstant G k)` over `Spec k`. -/
def translationAction : G →* Aut (profiniteSpec k G) where
  toFun := translationAut k G
  map_one' := by
    apply Iso.ext
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (translationRingEquiv k G 1).toRingHom) = _
    rw [translationRingEquiv_one_eq, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  map_mul' g h := by
    apply Iso.ext
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (translationRingEquiv k G (g * h)).toRingHom) =
      Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, translationRingEquiv_comp]

/-- The underlying morphism of schemes of the translation action of `g` is the spectrum of
translation by `g`. -/
theorem translationAction_hom_left (g : G) :
    (translationAction k G g).hom.left =
      Spec.map (CommRingCat.ofHom (translationRingEquiv k G g).toRingHom) := rfl

/-- Translation by `g` carries the evaluation prime at `w` to the evaluation prime at
`g * w`. -/
theorem translationAction_base_evaluationPrime (g w : G) :
    (translationAction k G g).hom.left (evaluationPrime k G w) =
      evaluationPrime k G (g * w) :=
  comap_translationRingEquiv_evaluationPrime k G g w

/-- The translation action of a profinite group on its own spectrum is free: on a nonempty
scheme a point of the spectrum determines the translating element, because the action on the
evaluation primes is the translation action of `G` on itself. -/
theorem actsFreelyOnNonemptyPoints_translationAction [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] :
    Space.ActsFreelyOnNonemptyPoints (profiniteSpec k G) G (translationAction k G) := by
  intro T hT x g g' hgg
  obtain ⟨t⟩ := hT
  have hleft : x.left ≫ (translationAction k G g).hom.left =
      x.left ≫ (translationAction k G g').hom.left := congrArg CommaMorphism.left hgg
  have hbase : (translationAction k G g).hom.left.base (x.left.base t) =
      (translationAction k G g').hom.left.base (x.left.base t) := by
    simpa using congrArg (fun m : T.left ⟶ (profiniteSpec k G).left => m.base t) hleft
  obtain ⟨w, hw⟩ := evaluationPrime_surjective k G (x.left.base t)
  rw [← hw, translationAction_base_evaluationPrime,
    translationAction_base_evaluationPrime] at hbase
  exact mul_right_cancel (evaluationPrime_injective k G hbase)

end Action

/-- The ring of locally constant maps from a space to a field is reduced. -/
instance isReduced_locallyConstant : _root_.IsReduced (LocallyConstant G k) :=
  ⟨fun f hf => by
    ext x
    exact (hf.map (LocallyConstant.evalRingHom (Y := k) x)).eq_zero⟩

/-- The `k`-point of `Y` at `w`, as a morphism of schemes, hits the evaluation prime
at `w`. -/
theorem evalSpecMap_base (w : G) (z : ↥(Spec (.of k))) :
    (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (Y := k) w))) z =
      evaluationPrime k G w := by
  rw [Spec.map_apply]
  congr 1
  exact Subsingleton.elim _ _

/-! ### The quotient algebraic space `X = Y/Γ` -/

section Quotient

variable [Group G] [ContinuousMul G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
  (hY : B.Contains (Spec (.of (LocallyConstant G k))))

/-- `Y = Spec (LocallyConstant G k)` as an object of a big fppf site over `Spec k` which
contains it. -/
def profiniteChart : BigFppfOver B (Spec (.of k)) hS :=
  Over.mk (ObjectProperty.homMk (profiniteSpec k G).hom : B.obj hY ⟶ B.obj hS)

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

/-- `X = Y/Γ`, the fppf sheaf quotient of `Y = Spec (LocallyConstant G k)` by the translation
action of `Γ`, the group `G` viewed as a discrete `k`-group scheme. -/
abbrev profiniteTranslationQuotient : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u :=
  Space.actionQuotient G B hS (profiniteChart k G B hS hY) (translationAction k G)

/-- The `k`-point of `Y` at `w`: the morphism `Spec k ⟶ Y` of the site given by evaluation
at `w`. It is a section of the structure morphism of `Y`. -/
def evalPoint (w : G) :
    (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B (Spec (.of k)) hS) ⟶ profiniteChart k G B hS hY :=
  Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (Y := k) w))))
    (ObjectProperty.hom_ext _ (specMap_evalRingHom_comp_specMap_algebraMap k G w))

/-- The underlying morphism of schemes of `evalPoint k G B hS hY w` is the spectrum of evaluation
at `w`. -/
theorem evalPoint_left (w : G) :
    ((evalPoint k G B hS hY w).left : B.obj hS ⟶ B.obj hY).hom =
      Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (Y := k) w)) := rfl

/-- The quotient of `Y` by the translation action is an algebraic space over `Spec k`: the
action is free, so Stacks 071S applies. -/
theorem isAlgebraicSpace_profiniteTranslationQuotient :
    IsAlgebraicSpace B (Spec (.of k)) hS (profiniteTranslationQuotient k G B hS hY) :=
  Space.isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints G B hS
    (profiniteChart k G B hS hY) (translationAction k G)
    (actsFreelyOnNonemptyPoints_translationAction k G)


/-- The relation scheme of the translation action satisfies the size cutoff of the site. -/
theorem contains_profiniteRelationScheme :
    B.Contains (Space.actionRelationScheme
      (Space.underlyingOver B hS (profiniteChart k G B hS hY)) G).left :=
  Space.contains_actionRelationScheme_of_actsFreely G B (Spec (.of k)) hS
    (profiniteChart k G B hS hY) (translationAction k G)
    (actsFreelyOnNonemptyPoints_translationAction k G)

/-- The projection `q : Y ⟶ X` onto the quotient. -/
def profiniteQuotientMap :
    yoneda.obj (profiniteChart k G B hS hY) ⟶ profiniteTranslationQuotient k G B hS hY :=
  Space.freeActionQuotientMap G B (Spec (.of k)) hS (profiniteChart k G B hS hY)
    (translationAction k G) (actsFreelyOnNonemptyPoints_translationAction k G)

/-- The inclusion of the summand of the relation scheme indexed by `g`. -/
def summandInclusion (g : G) :
    profiniteChart k G B hS hY ⟶
      Space.siteActionRelationScheme G B hS (profiniteChart k G B hS hY)
        (contains_profiniteRelationScheme k G B hS hY) :=
  Over.homMk (ObjectProperty.homMk
      (Sigma.ι (fun _ : G => Space.underlyingOver B hS (profiniteChart k G B hS hY)) g).left)
    (ObjectProperty.hom_ext _
      (Sigma.ι (fun _ : G => Space.underlyingOver B hS (profiniteChart k G B hS hY)) g).w)

/-- Translation by `g` as an automorphism of `Y` inside the site. -/
def siteTranslation (g : G) :
    profiniteChart k G B hS hY ⟶ profiniteChart k G B hS hY :=
  Over.homMk (ObjectProperty.homMk (translationSpecIso k G g).hom)
    (ObjectProperty.hom_ext _ (translationAut k G g).hom.w)

/-- The summand inclusion splits the source map of the relation. -/
theorem summandInclusion_comp_source (g : G) :
    summandInclusion k G B hS hY g ≫
        Space.siteActionRelationSource G B hS (profiniteChart k G B hS hY)
          (contains_profiniteRelationScheme k G B hS hY) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact congrArg Over.Hom.left (Sigma.ι_desc _ g)

/-- The summand inclusion carries the target map of the relation to translation by `g`. -/
theorem summandInclusion_comp_target (g : G) :
    summandInclusion k G B hS hY g ≫
        Space.siteActionRelationTarget G B hS (profiniteChart k G B hS hY)
          (contains_profiniteRelationScheme k G B hS hY) (translationAction k G) =
      siteTranslation k G B hS hY g := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact congrArg Over.Hom.left (Sigma.ι_desc _ g)

/-- Translating the `k`-point at the origin by `w` gives the `k`-point at `w`: the
translation action is transitive on the `k`-points of `Y`. -/
theorem evalPoint_comp_siteTranslation (w : G) :
    evalPoint k G B hS hY 1 ≫ siteTranslation k G B hS hY w = evalPoint k G B hS hY w := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (Y := k) (1 : G))) ≫
      Spec.map (CommRingCat.ofHom (translationRingEquiv k G w).toRingHom) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun f => congrArg f (mul_one w)

/-- The projection onto the quotient is invariant under the translation action. -/
theorem siteTranslation_comp_profiniteQuotientMap (g : G) :
    yoneda.map (siteTranslation k G B hS hY g) ≫ profiniteQuotientMap k G B hS hY =
      profiniteQuotientMap k G B hS hY := by
  have hw := (Space.isPullback_freeActionQuotientMap G B (Spec (.of k)) hS
    (profiniteChart k G B hS hY) (translationAction k G)
    (actsFreelyOnNonemptyPoints_translationAction k G)).w
  have h := congrArg (fun m => yoneda.map (summandInclusion k G B hS hY g) ≫ m) hw
  simp only [← Category.assoc, ← Functor.map_comp, summandInclusion_comp_source,
    summandInclusion_comp_target] at h
  exact h

/-! ### The relation scheme as a disjoint union of copies of `Y` -/

/-- `Y` as a scheme over `Spec k`, in the form the quotient machinery uses. -/
abbrev profiniteOver : Over (Spec (.of k)) :=
  Space.underlyingOver B hS (profiniteChart k G B hS hY)

/-- A morphism out of the relation scheme is the descent, through the identification with a
disjoint union of copies of `U`, of its restrictions to the copies. -/
private theorem relation_left_eq_iso_hom_comp_desc {S T : Scheme.{u}} {H : Type u}
    (U : Over S) (f : (Space.actionRelationScheme U H).left ⟶ T) (d : H → (U.left ⟶ T))
    (h : ∀ g : H, (Sigma.ι (fun _ : H => U) g).left ≫ f = d g) :
    f = (Space.actionRelationUnderlyingIso U H).hom ≫ Sigma.desc d := by
  rw [← Iso.inv_comp_eq]
  refine Sigma.hom_ext _ _ fun g => ?_
  rw [Sigma.ι_desc, ← Category.assoc, Space.actionRelationUnderlyingIso_inv_ι]
  exact h g

/-- Through the identification of the relation scheme with a disjoint union of copies of `Y`,
the source map of the graph relation is the codiagonal. -/
theorem actionRelationSource_left_eq :
    (Space.actionRelationSource (profiniteOver k G B hS hY) G).left =
      (Space.actionRelationUnderlyingIso (profiniteOver k G B hS hY) G).hom ≫
        Sigma.desc fun _ : G => 𝟙 (profiniteOver k G B hS hY).left :=
  relation_left_eq_iso_hom_comp_desc _ _ _ fun g =>
    congrArg Over.Hom.left (Sigma.ι_desc _ g)

/-- Through the same identification, the target map of the graph relation is the morphism
induced by the individual translations. -/
theorem actionRelationTarget_left_eq :
    (Space.actionRelationTarget (profiniteOver k G B hS hY) G (translationAction k G)).left =
      (Space.actionRelationUnderlyingIso (profiniteOver k G B hS hY) G).hom ≫
        Sigma.desc fun g : G => ((translationAction k G g).hom.left :
          (profiniteOver k G B hS hY).left ⟶ (profiniteOver k G B hS hY).left) :=
  relation_left_eq_iso_hom_comp_desc _ _ _ fun g =>
    congrArg Over.Hom.left (Sigma.ι_desc _ g)

/-! ### `X` is a one-point space -/

/-- The `k`-point of `Y` at `w`, as a field-valued point of `Y`. -/
def evalFieldPoint (w : G) :
    Space.FieldValuedPoint B (Spec (.of k)) hS (yoneda.obj (profiniteChart k G B hS hY)) where
  carrier := k
  contained := hS
  toBase := 𝟙 _
  value := evalPoint k G B hS hY w

/-- Every field-valued point of `Y` has the class of a `k`-point at some element of `G`,
because a field-valued point of `Y` factors through evaluation at a point of `G`. -/
theorem exists_class_eq_evalFieldPoint
    (p : Space.FieldValuedPoint B (Spec (.of k)) hS
      (yoneda.obj (profiniteChart k G B hS hY))) :
    ∃ w : G, p.class B (Spec (.of k)) hS _ =
      (evalFieldPoint k G B hS hY w).class B (Spec (.of k)) hS _ := by
  have hw0 : (p.value.left : B.obj p.contained ⟶ B.obj hY).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (LocallyConstant G k))) = p.toBase :=
    congrArg (fun m : B.obj p.contained ⟶ B.obj hS => m.hom) (Over.w p.value)
  obtain ⟨w, hw⟩ := exists_eq_comp_specMap_evalRingHom_of_comp_eq k G p.toBase _ hw0
  refine ⟨w, Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension _ _ _ _
    ⟨p, Space.FieldValuedPoint.dominates_refl _ _ _ _ p, ?_⟩⟩
  exact ⟨Over.homMk ⟨p.toBase⟩ (ObjectProperty.hom_ext _ (Category.comp_id p.toBase)),
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hw.symm)⟩

/-- The projection sends every `k`-point of `Y` to the same point of `X`: the translation
action is transitive on them and the projection is invariant under it. -/
theorem pointsMap_evalFieldPoint_eq (w : G) :
    Space.pointsMap B (Spec (.of k)) hS _ (profiniteQuotientMap k G B hS hY)
        ((evalFieldPoint k G B hS hY w).class B (Spec (.of k)) hS _) =
      Space.pointsMap B (Spec (.of k)) hS _ (profiniteQuotientMap k G B hS hY)
        ((evalFieldPoint k G B hS hY 1).class B (Spec (.of k)) hS _) := by
  have h : (profiniteQuotientMap k G B hS hY).app
        (Opposite.op (Over.mk (𝟙 (B.obj hS)))) (evalPoint k G B hS hY w) =
      (profiniteQuotientMap k G B hS hY).app
        (Opposite.op (Over.mk (𝟙 (B.obj hS)))) (evalPoint k G B hS hY 1) := by
    rw [← evalPoint_comp_siteTranslation k G B hS hY w]
    exact congrArg
      (fun m : yoneda.obj (profiniteChart k G B hS hY) ⟶
          profiniteTranslationQuotient k G B hS hY =>
        m.app (Opposite.op (Over.mk (𝟙 (B.obj hS)))) (evalPoint k G B hS hY 1))
      (siteTranslation_comp_profiniteQuotientMap k G B hS hY w)
  rw [Space.pointsMap_class, Space.pointsMap_class]
  congr 1
  unfold Space.FieldValuedPoint.map
  congr 1

/-- **`X = Y/Γ` has exactly one point.** Every point of `X` comes from a field-valued point
of `Y`, every such point is a `k`-point at some element of `G`, and the translation action
carries any one of those to any other. -/
theorem subsingleton_points_profiniteTranslationQuotient :
    Subsingleton (Space.points B (Spec (.of k)) hS
      (profiniteTranslationQuotient k G B hS hY)) := by
  have hsurj : Function.Surjective (Space.pointsMap B (Spec (.of k)) hS _
      (profiniteQuotientMap k G B hS hY)) :=
    Space.surjective_pointsMap_of_presheaf_surjective B (Spec (.of k)) hS _
      (Space.surjective_presheaf_freeActionQuotientMap G B (Spec (.of k)) hS
        (profiniteChart k G B hS hY) (translationAction k G)
        (actsFreelyOnNonemptyPoints_translationAction k G))
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  induction a' using Quot.ind with
  | _ pa =>
  induction b' using Quot.ind with
  | _ pb =>
  obtain ⟨wa, ha⟩ := exists_class_eq_evalFieldPoint k G B hS hY pa
  obtain ⟨wb, hb⟩ := exists_class_eq_evalFieldPoint k G B hS hY pb
  show Space.pointsMap B (Spec (.of k)) hS _ (profiniteQuotientMap k G B hS hY)
      (pa.class B (Spec (.of k)) hS _) =
    Space.pointsMap B (Spec (.of k)) hS _ (profiniteQuotientMap k G B hS hY)
      (pb.class B (Spec (.of k)) hS _)
  rw [ha, hb, pointsMap_evalFieldPoint_eq]
  exact (pointsMap_evalFieldPoint_eq k G B hS hY wb).symm

/-! ### The projection does not factor through the `k`-point -/

/-- **The projection `q : Y ⟶ X` admits no factorization through the `k`-point of `X`.** -/
theorem not_exists_comp_evalPoint_comp_quotientMap_eq [IsTopologicalGroup G] [Infinite G] :
    ¬ ∃ σ : profiniteChart k G B hS hY ⟶
        (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B (Spec (.of k)) hS),
      yoneda.map (σ ≫ evalPoint k G B hS hY 1) ≫ profiniteQuotientMap k G B hS hY =
        profiniteQuotientMap k G B hS hY := by
  rintro ⟨σ, hσ⟩
  have hpb := Space.isPullback_freeActionQuotientMap G B (Spec (.of k)) hS
    (profiniteChart k G B hS hY) (translationAction k G)
    (actsFreelyOnNonemptyPoints_translationAction k G)
  have hcomm : yoneda.map (σ ≫ evalPoint k G B hS hY 1) ≫
      profiniteQuotientMap k G B hS hY =
      𝟙 (yoneda.obj (profiniteChart k G B hS hY)) ≫ profiniteQuotientMap k G B hS hY := by
    rwa [Category.id_comp]
  obtain ⟨ρ', hfst, hsnd⟩ :
      ∃ r : yoneda.obj (profiniteChart k G B hS hY) ⟶
          yoneda.obj (Space.siteActionRelationScheme G B hS (profiniteChart k G B hS hY)
            (contains_profiniteRelationScheme k G B hS hY)),
        r ≫ yoneda.map (Space.siteActionRelationTarget G B hS (profiniteChart k G B hS hY)
            (contains_profiniteRelationScheme k G B hS hY) (translationAction k G)) =
          yoneda.map (σ ≫ evalPoint k G B hS hY 1) ∧
        r ≫ yoneda.map (Space.siteActionRelationSource G B hS (profiniteChart k G B hS hY)
            (contains_profiniteRelationScheme k G B hS hY)) = 𝟙 _ :=
    ⟨hpb.lift _ _ hcomm, hpb.lift_fst _ _ hcomm, hpb.lift_snd _ _ hcomm⟩
  obtain ⟨ρ, rfl⟩ : ∃ r, yoneda.map r = ρ' := ⟨yoneda.preimage ρ', yoneda.map_preimage _⟩
  have hρs : ρ ≫ Space.siteActionRelationSource G B hS (profiniteChart k G B hS hY)
      (contains_profiniteRelationScheme k G B hS hY) = 𝟙 _ := by
    apply yoneda.map_injective
    rwa [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  have hρt : ρ ≫ Space.siteActionRelationTarget G B hS (profiniteChart k G B hS hY)
      (contains_profiniteRelationScheme k G B hS hY) (translationAction k G) =
      σ ≫ evalPoint k G B hS hY 1 := by
    apply yoneda.map_injective
    rwa [CategoryTheory.Functor.map_comp]
  have hbs : ρ.left.hom ≫ (Space.actionRelationSource (profiniteOver k G B hS hY) G).left
      = 𝟙 _ :=
    congrArg (fun m : profiniteChart k G B hS hY ⟶ profiniteChart k G B hS hY =>
      m.left.hom) hρs
  rw [actionRelationSource_left_eq k G B hS hY] at hbs
  have hsplit := (Category.assoc _ _ _).trans hbs
  have hbt : ρ.left.hom ≫
      (Space.actionRelationTarget (profiniteOver k G B hS hY) G (translationAction k G)).left =
      σ.left.hom ≫
        Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (Y := k) (1 : G))) :=
    congrArg (fun m : profiniteChart k G B hS hY ⟶ profiniteChart k G B hS hY =>
      m.left.hom) hρt
  rw [actionRelationTarget_left_eq k G B hS hY] at hbt
  have htarget := (Category.assoc _ _ _).trans hbt
  obtain ⟨ρt, hsp, htg⟩ : ∃ r : (profiniteOver k G B hS hY).left ⟶
      ∐ fun _ : G => (profiniteOver k G B hS hY).left,
      (r ≫ Sigma.desc fun _ : G => 𝟙 (profiniteOver k G B hS hY).left) = 𝟙 _ ∧
      (r ≫ Sigma.desc fun g : G => ((translationAction k G g).hom.left :
          (profiniteOver k G B hS hY).left ⟶ (profiniteOver k G B hS hY).left)) =
        σ.left.hom ≫
          Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (Y := k) (1 : G))) :=
    ⟨_, hsplit, htarget⟩
  have hindex : ∀ w : G,
      sigmaIndexOf (fun _ : G => (profiniteOver k G B hS hY).left) ρt
        (evaluationPrime k G w) = w⁻¹ := by
    intro w
    have hbase := base_eq_sigmaMk_sigmaIndexOf ρt hsp (evaluationPrime k G w)
    have hLHS := Scheme.Hom.comp_apply ρt
      (Sigma.desc fun g : G => ((translationAction k G g).hom.left :
        (profiniteOver k G B hS hY).left ⟶ (profiniteOver k G B hS hY).left))
      (evaluationPrime k G w)
    have hRHS := Scheme.Hom.comp_apply σ.left.hom
      (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (Y := k) (1 : G))))
      (evaluationPrime k G w)
    have heq := congrArg (fun m : (profiniteOver k G B hS hY).left ⟶
      (profiniteOver k G B hS hY).left => m.base (evaluationPrime k G w)) htg
    have h2 := hLHS.symm.trans (heq.trans hRHS)
    have e1 := congrArg
      (fun z : ↥(∐ fun _ : G => (profiniteOver k G B hS hY).left) =>
        (Sigma.desc fun g : G => ((translationAction k G g).hom.left :
          (profiniteOver k G B hS hY).left ⟶ (profiniteOver k G B hS hY).left)) z) hbase
    have e2 := sigmaDesc_base_sigmaMk (fun _ : G => (profiniteOver k G B hS hY).left)
      (fun g : G => ((translationAction k G g).hom.left :
        (profiniteOver k G B hS hY).left ⟶ (profiniteOver k G B hS hY).left))
      (sigmaIndexOf (fun _ : G => (profiniteOver k G B hS hY).left) ρt
        (evaluationPrime k G w))
      (evaluationPrime k G w)
    have e3 := evalSpecMap_base k G (1 : G) (σ.left.hom (evaluationPrime k G w))
    have e4 := translationAction_base_evaluationPrime k G
      (sigmaIndexOf (fun _ : G => (profiniteOver k G B hS hY).left) ρt
        (evaluationPrime k G w)) w
    exact eq_inv_of_mul_eq_one_left (evaluationPrime_injective k G
      (e4.symm.trans (e2.symm.trans ((e1.symm.trans h2).trans e3))))
  refine not_isOpen_singleton_evaluationPrime k G ?_
  have hopen := isOpen_preimage_sigmaIndexOf
    (fun _ : G => (profiniteOver k G B hS hY).left) ρt 1
  have hfib : sigmaIndexOf (fun _ : G => (profiniteOver k G B hS hY).left) ρt ⁻¹' {1} =
      {evaluationPrime k G 1} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun z hz => ?_⟩
    · show sigmaIndexOf (fun _ : G => (profiniteOver k G B hS hY).left) ρt
        (evaluationPrime k G 1) = 1
      rw [hindex 1, inv_one]
    · obtain ⟨w, hw⟩ := evaluationPrime_surjective k G z
      have hz' : sigmaIndexOf (fun _ : G => (profiniteOver k G B hS hY).left) ρt z = 1 := hz
      rw [← hw, hindex w] at hz'
      rw [← hw, inv_eq_one.mp hz']
  rwa [hfib] at hopen

/-! ### The `k`-point of `X` -/

/-- The `k`-point of `X` coming from the origin of `G`: the image under the projection of the
`k`-point of `Y` at the origin. -/
def originQuotientPoint : Space.FieldValuedPoint B (Spec (.of k)) hS
    (profiniteTranslationQuotient k G B hS hY) :=
  Space.FieldValuedPoint.map B (Spec (.of k)) hS _ (profiniteQuotientMap k G B hS hY)
    (evalFieldPoint k G B hS hY 1)

/-- The morphism presented by the `k`-point of `X` is the `k`-point of `Y` at the origin
followed by the projection. -/
theorem fieldMorphism_originQuotientPoint :
    Space.fieldMorphism B (Spec (.of k)) hS _ (originQuotientPoint k G B hS hY) =
      yoneda.map (evalPoint k G B hS hY 1) ≫ profiniteQuotientMap k G B hS hY :=
  Space.fieldMorphism_map_yoneda B (Spec (.of k)) hS _ _ _

/-- The `k`-point of `X` is a monomorphism. It is a section of the structure morphism of `X`
over `Spec k`, because its source is the terminal presheaf of the site, so it is even a split
monomorphism. -/
theorem mono_fieldMorphism_originQuotientPoint :
    Mono (Space.fieldMorphism B (Spec (.of k)) hS _ (originQuotientPoint k G B hS hY)) := by
  have hT := Space.isTerminal_yoneda_obj_base B (Spec (.of k)) hS
  have : IsSplitMono (Space.fieldMorphism B (Spec (.of k)) hS _
      (originQuotientPoint k G B hS hY)) :=
    IsSplitMono.mk' ⟨hT.from _, hT.hom_ext _ _⟩
  infer_instance

end Quotient

/-! ### The orbit map of the origin -/

/-- The orbit map `Γ → Y` of the origin, where `Y = Spec (LocallyConstant G k)` is `G` as a
zero-dimensional affine `k`-scheme and `Γ = ∐_{g ∈ G} Spec k` is `G` as a discrete
`k`-scheme. On the summand indexed by `g` it is the `k`-point of `Y` given by evaluation at
`g`, which is the translate `g · e` of the origin. -/
def orbitMap :
    (∐ fun _ : G => Spec (.of k)) ⟶ Spec (.of (LocallyConstant G k)) :=
  Sigma.desc fun g => Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom g))

/-- The orbit map sends the summand of `Γ` indexed by `g` to the evaluation prime at `g`. -/
theorem orbitMap_base_sigmaMk (g : G) (z : ↥(Spec (.of k))) :
    (orbitMap k G).base (AlgebraicGeometry.sigmaMk (fun _ : G => Spec (.of k)) ⟨g, z⟩) =
      evaluationPrime k G g := by
  rw [AlgebraicGeometry.sigmaMk_mk, ← Scheme.Hom.comp_apply]
  have h : Sigma.ι (fun _ : G => Spec (.of k)) g ≫ orbitMap k G =
      Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom g)) := by
    simp [orbitMap]
  rw [h]
  exact evalSpecMap_base k G g z

/-- **The orbit map of the origin admits no section.** For an infinite profinite group `G` and a
field `k`, the orbit map of the origin from the discrete `k`-scheme `Γ = ∐_{g ∈ G} Spec k` to the
zero-dimensional affine `k`-scheme `Y = Spec (LocallyConstant G k)` admits no section. -/
@[stacks 0H2Y "the orbit map of the origin has no section"]
theorem not_exists_comp_orbitMap_eq_id [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Infinite G] :
    ¬ ∃ s : Spec (.of (LocallyConstant G k)) ⟶ ∐ (fun _ : G => Spec (.of k)),
        s ≫ orbitMap k G = 𝟙 _ := by
  classical
  rintro ⟨s, hs⟩
  let e := AlgebraicGeometry.sigmaMk (fun _ : G => Spec (.of k))
  let r : PrimeSpectrum (LocallyConstant G k) → G := fun z => (e.symm (s.base z)).1
  have hid : ∀ z, (orbitMap k G).base (s.base z) = z := by
    intro z
    rw [← Scheme.Hom.comp_apply, hs]
    simp
  have hr : ∀ g : G, r (evaluationPrime k G g) = g := by
    intro g
    have h1 : (orbitMap k G).base (e (e.symm (s.base (evaluationPrime k G g)))) =
        evaluationPrime k G g := by
      rw [Homeomorph.apply_symm_apply]; exact hid _
    rw [show (e.symm (s.base (evaluationPrime k G g))) =
        ⟨r (evaluationPrime k G g), (e.symm (s.base (evaluationPrime k G g))).2⟩ from rfl,
      orbitMap_base_sigmaMk] at h1
    exact evaluationPrime_injective k G h1
  obtain ⟨g, hg, hmem⟩ := exists_ne_one_evaluationPrime_mem_of_isOpen k G
    (isOpen_preimage_sigmaIndexOf (fun _ : G => Spec (.of k)) s 1) (hr 1)
  exact hg ((hr g).symm.trans hmem)

end AlgebraicGeometry.ProfiniteTranslation

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The conclusion of Stacks 0H1S and of Stacks 0H1T fails at every residual space: if
`q : Y ⟶ X` factors through no field-valued point of `X`, and the point `x` of `|X|` has a
monomorphic field-valued representative, then `q` factors through no residual space of `X`
at `x` either. -/
theorem forall_not_comp_eq_of_isResidualSpaceAt (hX : IsAlgebraicSpace B S hS X)
    (q : Y ⟶ X) (x : points B S hS X)
    (hmono : HasMonomorphicFieldRepresentative B S hS X x)
    (hnofactor : ∀ (p : FieldValuedPoint B S hS X)
      (g : Y ⟶ yoneda.obj (p.siteObject B S hS X)),
      g ≫ fieldMorphism B S hS X p ≠ q)
    (i : Z ⟶ X) (hi : IsResidualSpaceAt B S hS X x i) :
    ¬ ∃ g : Y ⟶ Z, g ≫ i = q := by
  rintro ⟨g, hg⟩
  obtain ⟨w, hw⟩ :=
    (exists_isIso_fieldMorphism_iff_hasMonomorphicFieldRepresentative B S hS hX x i hi).2 hmono
  obtain ⟨u, -, hu⟩ := hw.out
  have hcomp : (g ≫ u) ≫ (fieldMorphism B S hS Z w ≫ i) = q := by
    rwa [Category.assoc, ← Category.assoc u, hu, Category.id_comp]
  refine hnofactor (FieldValuedPoint.map B S hS Z i w) (g ≫ u) ?_
  rwa [fieldMorphism_map]

/-- A morphism onto a single point from a reduced algebraic space which factors through no
field-valued point of the target refutes Stacks 0H1T: the target is not decent. -/
theorem not_isDecentSpace (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (q : Y ⟶ X) (x : points B S hS X)
    (himage : Set.range (pointsMap B S hS Y q) ⊆ {x})
    (hred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (hnofactor : ∀ (p : FieldValuedPoint B S hS X)
      (g : Y ⟶ yoneda.obj (p.siteObject B S hS X)),
      g ≫ fieldMorphism B S hS X p ≠ q) :
    ¬ IsDecentSpace B S hS X := by
  intro hdecent
  obtain ⟨p, -, g, hg⟩ := exists_isResidualSpaceAt_comp_fieldMorphism_eq_of_isDecentSpace
    B S hS hX hY q x himage hred hdecent
  exact hnofactor p g hg

/-- A morphism onto a single point from a reduced algebraic space which factors through no
field-valued point of the target refutes Stacks 0H1S, provided the point has a monomorphic
field-valued representative: the target is not locally Noetherian. -/
theorem not_hasEtaleLocalProperty_isLocallyNoetherian (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (q : Y ⟶ X) (x : points B S hS X)
    (himage : Set.range (pointsMap B S hS Y q) ⊆ {x})
    (hred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (hmono : HasMonomorphicFieldRepresentative B S hS X x)
    (hnofactor : ∀ (p : FieldValuedPoint B S hS X)
      (g : Y ⟶ yoneda.obj (p.siteObject B S hS X)),
      g ≫ fieldMorphism B S hS X p ≠ q) :
    ¬ HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  intro hN
  obtain ⟨W, i, hi, g, hg, -⟩ := exists_isResidualSpaceAt_and_existsUnique_comp_eq
    B S hS hX hY q x himage hred hN
  exact forall_not_comp_eq_of_isResidualSpaceAt B S hS hX q x hmono hnofactor i hi ⟨g, hg⟩

/-! ### Reducing the non-factorization to the pullback of the projection -/

/-- On an algebraic space with exactly one point, every field-valued point factors through a
monomorphic field-valued representative, by Stacks 0H2X. -/
theorem exists_comp_fieldMorphism_eq_of_subsingleton_points (hX : IsAlgebraicSpace B S hS X)
    (hsub : Subsingleton (points B S hS X)) (px p : FieldValuedPoint B S hS X)
    (hpxmono : Mono (fieldMorphism B S hS X px)) :
    ∃ f : yoneda.obj (p.siteObject B S hS X) ⟶ yoneda.obj (px.siteObject B S hS X),
      f ≫ fieldMorphism B S hS X px = fieldMorphism B S hS X p := by
  have hmono : Mono (yonedaEquiv.symm px.value) := hpxmono
  obtain ⟨f, hf, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS X hX
    px p (hsub.elim _ _)
  refine ⟨yoneda.map f, ?_⟩
  have h := yonedaEquiv_symm_naturality_left f X px.value
  rwa [hf] at h

/-- If `X` is a one-point algebraic space over `S` whose point `x` has a monomorphic field-valued
representative `px`, and the projection of `q : Y ⟶ X` to `Y` from the fibre product `Y ×_X px`
admits no section, then `q` factors through no field-valued point of `X` at all. -/
theorem forall_not_comp_fieldMorphism_eq_of_not_exists_section (hX : IsAlgebraicSpace B S hS X)
    (q : Y ⟶ X) (hsub : Subsingleton (points B S hS X)) (px : FieldValuedPoint B S hS X)
    (hpxmono : Mono (fieldMorphism B S hS X px))
    (hsection : ¬ ∃ s : Y ⟶ pullback q (fieldMorphism B S hS X px),
      s ≫ pullback.fst q (fieldMorphism B S hS X px) = 𝟙 Y) :
    ∀ (p : FieldValuedPoint B S hS X) (g : Y ⟶ yoneda.obj (p.siteObject B S hS X)),
      g ≫ fieldMorphism B S hS X p ≠ q := by
  intro p g hg
  obtain ⟨f, hf⟩ :=
    exists_comp_fieldMorphism_eq_of_subsingleton_points B S hS hX hsub px p hpxmono
  refine hsection ⟨pullback.lift (𝟙 Y) (g ≫ f) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.id_comp, Category.assoc, hf]
  exact hg.symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

/-! ### The example -/

variable (k G : Type u) [Field k] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Infinite G]
  (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
  (hY : B.Contains (Spec (.of (LocallyConstant G k))))
  [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

open ProfiniteTranslation

/-- `Y = Spec (LocallyConstant G k)` is reduced. -/
theorem hasEtaleLocalProperty_isReduced_profiniteChart :
    HasEtaleLocalProperty B (Spec (.of k)) hS
      (yoneda.obj (profiniteChart k G B hS hY)) (fun T : Scheme.{u} => IsReduced T) :=
  hasEtaleLocalProperty_of_representable B (Spec (.of k)) hS _ _
    (profiniteChart k G B hS hY) (Iso.refl _)
    (inferInstanceAs (IsReduced (Spec (.of (LocallyConstant G k)))))

/-- **The one-point quotient of an infinite profinite group by translation.** Let `k` be a field
and let `G` be an infinite profinite group. Let `Y = Spec (LocallyConstant G k)` be `G` as a
zero-dimensional affine `k`-scheme, let `Γ` be `G` as a discrete `k`-group scheme acting on `Y` by
translations, and let `X = Y/Γ` with projection `q : Y ⟶ X`. Then `X` is an algebraic space with a
single point, `Y` is reduced, the `k`-point of `X` at the origin is a monomorphism, and `q` factors
through no field-valued point of `X` whatsoever. -/
@[stacks 0H2Y "the one-point algebraic space and the non-factorization"]
theorem not_isLocallyNoetherian_and_not_isDecentSpace_of_not_exists_section :
    IsAlgebraicSpace B (Spec (.of k)) hS (profiniteTranslationQuotient k G B hS hY) ∧
      Subsingleton (points B (Spec (.of k)) hS
        (profiniteTranslationQuotient k G B hS hY)) ∧
      HasEtaleLocalProperty B (Spec (.of k)) hS
        (yoneda.obj (profiniteChart k G B hS hY)) (fun T : Scheme.{u} => IsReduced T) ∧
      Mono (fieldMorphism B (Spec (.of k)) hS _ (originQuotientPoint k G B hS hY)) ∧
      ∀ (p : FieldValuedPoint B (Spec (.of k)) hS
          (profiniteTranslationQuotient k G B hS hY))
        (g : yoneda.obj (profiniteChart k G B hS hY) ⟶
          yoneda.obj (p.siteObject B (Spec (.of k)) hS _)),
        g ≫ fieldMorphism B (Spec (.of k)) hS _ p ≠ profiniteQuotientMap k G B hS hY := by
  refine ⟨isAlgebraicSpace_profiniteTranslationQuotient k G B hS hY,
    subsingleton_points_profiniteTranslationQuotient k G B hS hY,
    hasEtaleLocalProperty_isReduced_profiniteChart k G B hS hY,
    mono_fieldMorphism_originQuotientPoint k G B hS hY, ?_⟩
  intro p g hg
  obtain ⟨f, hf⟩ := exists_comp_fieldMorphism_eq_of_subsingleton_points B (Spec (.of k)) hS
    (isAlgebraicSpace_profiniteTranslationQuotient k G B hS hY)
    (subsingleton_points_profiniteTranslationQuotient k G B hS hY)
    (originQuotientPoint k G B hS hY) p (mono_fieldMorphism_originQuotientPoint k G B hS hY)
  have hcomp : (g ≫ f) ≫
      fieldMorphism B (Spec (.of k)) hS _ (originQuotientPoint k G B hS hY) =
      profiniteQuotientMap k G B hS hY := by
    rw [Category.assoc, hf]
    exact hg
  obtain ⟨σ, hσ⟩ : ∃ σ, yoneda.map σ = g ≫ f := ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  refine not_exists_comp_evalPoint_comp_quotientMap_eq k G B hS hY ⟨σ, ?_⟩
  calc yoneda.map (σ ≫ evalPoint k G B hS hY 1) ≫ profiniteQuotientMap k G B hS hY
      = (yoneda.map σ ≫ yoneda.map (evalPoint k G B hS hY 1)) ≫
          profiniteQuotientMap k G B hS hY :=
        congrArg (fun m : yoneda.obj (profiniteChart k G B hS hY) ⟶
            profiniteTranslationQuotient k G B hS hY => m)
          (congrArg (fun m : yoneda.obj (profiniteChart k G B hS hY) ⟶
              yoneda.obj (profiniteChart k G B hS hY) =>
            m ≫ profiniteQuotientMap k G B hS hY)
            (yoneda.map_comp σ (evalPoint k G B hS hY 1)))
    _ = yoneda.map σ ≫ (yoneda.map (evalPoint k G B hS hY 1) ≫
          profiniteQuotientMap k G B hS hY) := Category.assoc _ _ _
    _ = (g ≫ f) ≫ (yoneda.map (evalPoint k G B hS hY 1) ≫
          profiniteQuotientMap k G B hS hY) := by rw [hσ]
    _ = (g ≫ f) ≫
          fieldMorphism B (Spec (.of k)) hS _ (originQuotientPoint k G B hS hY) :=
        congrArg (fun m : yoneda.obj (Over.mk (𝟙 (B.obj hS))) ⟶
            profiniteTranslationQuotient k G B hS hY => (g ≫ f) ≫ m)
          (fieldMorphism_originQuotientPoint k G B hS hY).symm
    _ = profiniteQuotientMap k G B hS hY := hcomp

/-- **The quotient of an infinite profinite group by translation is neither locally Noetherian nor
decent.** For the quotient `X = Y/Γ` of the previous theorem, the conclusion of Stacks 0H1S and of
Stacks 0H1T fails for the projection `q : Y ⟶ X` at every residual space of `X` at its point. -/
@[stacks 0H2Y "the conclusion for the quotient of a profinite group by translation"]
theorem not_isLocallyNoetherian_and_not_isDecentSpace :
    ¬ HasEtaleLocalProperty B (Spec (.of k)) hS (profiniteTranslationQuotient k G B hS hY)
        (fun T : Scheme.{u} => IsLocallyNoetherian T) ∧
      ¬ IsDecentSpace B (Spec (.of k)) hS (profiniteTranslationQuotient k G B hS hY) ∧
      ∀ {W : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u}
        (i : W ⟶ profiniteTranslationQuotient k G B hS hY),
        IsResidualSpaceAt B (Spec (.of k)) hS (profiniteTranslationQuotient k G B hS hY)
          ((originQuotientPoint k G B hS hY).class B (Spec (.of k)) hS _) i →
        ¬ ∃ g : yoneda.obj (profiniteChart k G B hS hY) ⟶ W,
            g ≫ i = profiniteQuotientMap k G B hS hY := by
  obtain ⟨hX, hsub, hred, hpxmono, hnofactor⟩ :=
    not_isLocallyNoetherian_and_not_isDecentSpace_of_not_exists_section k G B hS hY
  have hYalg : IsAlgebraicSpace B (Spec (.of k)) hS
      (yoneda.obj (profiniteChart k G B hS hY)) :=
    isAlgebraicSpace_yoneda B (Spec (.of k)) hS _
  have himage : Set.range (pointsMap B (Spec (.of k)) hS _
      (profiniteQuotientMap k G B hS hY)) ⊆
      {(originQuotientPoint k G B hS hY).class B (Spec (.of k)) hS _} :=
    Set.range_subset_iff.mpr fun _ => hsub.elim _ _
  have hmono : HasMonomorphicFieldRepresentative B (Spec (.of k)) hS
      (profiniteTranslationQuotient k G B hS hY)
      ((originQuotientPoint k G B hS hY).class B (Spec (.of k)) hS _) :=
    ⟨originQuotientPoint k G B hS hY, rfl, hpxmono⟩
  exact ⟨not_hasEtaleLocalProperty_isLocallyNoetherian B (Spec (.of k)) hS hX hYalg _ _
      himage hred hmono hnofactor,
    not_isDecentSpace B (Spec (.of k)) hS hX hYalg _ _ himage hred hnofactor,
    fun i hi => forall_not_comp_eq_of_isResidualSpaceAt B (Spec (.of k)) hS hX _ _ hmono
      hnofactor i hi⟩

end AlgebraicGeometry.Space

end
