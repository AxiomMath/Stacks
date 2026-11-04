module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.DoubledOriginNotAlgebraic.NotAlgebraic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The four points of the finite part of the doubled origin

The finite part of the doubled origin has exactly four points over the origin
(`exists_equiv_originPoints`, `card_originPoints`), of which exactly three lift to an étale
neighbourhood (`setOf_isEtaleLiftablePoint`), and **Stacks 04QI**
(`doubledOrigin_finitePart`), all claims of the remark.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-! ### The four points of the finite part over the origin -/

section FourPoints

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  Space.preservesLimitsOfShape_walkingCospan_toScheme

variable {B : BigFppfSite.{u}} {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {n : ℕ}

/-- The fibre over the origin of the base change of the coordinate morphism along a morphism to
the origin consists of the values of the two chart sections. -/
theorem eq_or_eq_of_originHom
    (x : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj
      (pullback (originHom B k hk n) (doubledCoordHom B k hk n)))
    (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (pointObj B k hk)) :
    ∃ i : Fin 2, x = (BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (siteChartSection (originHom B k hk n) i) pt := by
  obtain ⟨⟨i⟩, y, hy⟩ := (doubledZeroGlueData k n).ι_jointly_surjective
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (pullback.snd _ _) x)
  have hr := range_chartSectionOfIsPullback
    (isPullback_toScheme_pullback_doubledCoordHom (originHom B k hk n)) i
  rw [chartSectionOfIsPullback_toScheme] at hr
  have hx : x ∈ Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (siteChartSection (originHom B k hk n) i)) := hr ▸ ⟨y, hy⟩
  obtain ⟨p, rfl⟩ := hx
  exact ⟨i, congrArg _ (Subsingleton.elim (α := PrimeSpectrum k) p pt)⟩

/-- Over a point lying off the complement of the origin, the chart sections take equal values
only for equal indices. -/
private theorem eq_of_siteChartSection_apply_eq {U : BigFppfOver B (Spec (.of k)) hk}
    (b : U ⟶ affineSpaceObj B k hk n) (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj U)
    (hpt : (BigFppfOver.toScheme B (Spec (.of k)) hk).map b pt ∉ puncturedAffineSpace k n)
    {i i' : Fin 2} (h : (BigFppfOver.toScheme B (Spec (.of k)) hk).map (siteChartSection b i) pt =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (siteChartSection b i') pt) : i = i' := by
  have hne := chartSectionOfIsPullback_apply_ne
    (isPullback_toScheme_pullback_doubledCoordHom b) pt hpt
  rw [chartSectionOfIsPullback_toScheme, chartSectionOfIsPullback_toScheme] at hne
  fin_cases i <;> fin_cases i'
  · rfl
  · exact absurd h hne
  · exact absurd h.symm hne
  · rfl

/-- The chart sections of the base change along `b` are open immersions on the schemes. -/
private theorem isOpenImmersion_map_siteChartSection {U : BigFppfOver B (Spec (.of k)) hk}
    (b : U ⟶ affineSpaceObj B k hk n) (i : Fin 2) :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (siteChartSection b i)) :=
  (congrArg (fun f => _root_.AlgebraicGeometry.IsOpenImmersion f)
    (chartSectionOfIsPullback_toScheme b i)).mp (isOpenImmersion_chartSectionOfIsPullback _ i)

/-- A set contains the range of a map out of the point iff it contains the image of one point. -/
private theorem range_subset_iff_apply_mem {Z : Scheme.{u}}
    (f : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (pointObj B k hk) ⟶ Z) (S : Set Z)
    (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (pointObj B k hk)) :
    Set.range f ⊆ S ↔ f pt ∈ S := by
  refine ⟨fun h => h ⟨pt, rfl⟩, ?_⟩
  rintro h _ ⟨p, rfl⟩
  rwa [Subsingleton.elim (α := PrimeSpectrum k) p pt]

/-- The two chart sections take distinct values over the origin. -/
theorem siteChartSection_originHom_ne
    (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (pointObj B k hk)) :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (siteChartSection (originHom B k hk n) 0) pt ≠
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (siteChartSection (originHom B k hk n) 1) pt := fun h =>
  zero_ne_one (eq_of_siteChartSection_apply_eq _ pt
    (originHom_notMem_puncturedAffineSpace B k hk n pt) h)

/-- The points of the finite part `(X/Y)_fin` over the origin: its sections over `Spec k` whose
morphism to `Y` is the origin. -/
abbrev originPoints : Type u :=
  {ξ : (doubledOriginFinitePart B k hk n).toFunctor.obj (op (pointObj B k hk)) //
    ((doubledOriginFinitePart B k hk n).sections _ ξ).toBase = schemeSpaceMap (originHom B k hk n)}

/-- The set of chart indices whose chart section lies in the open subspace of a pair of
Stacks 04PC for the coordinate morphism. Over a point above the origin it is the subset
`{0₁, 0₂} ∩ Z` of the fibre of the coordinate morphism cut out by the open subspace `Z`. -/
def chartIndices {T : BigFppfOver B (Spec (.of k)) hk}
    (z : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace T)) : Set (Fin 2) :=
  {i | ∃ l, l ≫ z.subspace.ι = chartSection z i}

/-- Membership in `chartIndices`, unfolded. -/
theorem mem_chartIndices {T : BigFppfOver B (Spec (.of k)) hk}
    (z : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace T)) (i : Fin 2) :
    i ∈ chartIndices z ↔ ∃ l, l ≫ z.subspace.ι = chartSection z i :=
  Iff.rfl

/-- Membership in `chartIndices` over the origin, read on the open subscheme representing the
open subspace of the pair: the `i`-th chart origin lies in that open subscheme. -/
theorem mem_chartIndices_iff
    (z : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace (pointObj B k hk)))
    (hz : z.toBase = schemeSpaceMap (originHom B k hk n))
    {W : BigFppfOver B (Spec (.of k)) hk}
    {j : W ⟶ pullback (originHom B k hk n) (doubledCoordHom B k hk n)}
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of k)) hk).map j)]
    (hzj : z.subspace = Subfunctor.range ((schemeSpaceMap j).hom ≫ (ambientIso _ _ hz).hom))
    (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (pointObj B k hk)) (i : Fin 2) :
    i ∈ chartIndices z ↔ (BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (siteChartSection (originHom B k hk n) i) pt ∈
        Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map j) := by
  rw [mem_chartIndices, chartSection_eq _ _ hz i,
    FiniteOpenSubspace.exists_comp_ι_eq_iff_range_subset _ hz hzj]
  exact range_subset_iff_apply_mem _ _ pt

/-- The open subset of the fibre `{0₁, 0₂}` of the coordinate morphism over the origin consisting
of the chart origins indexed by `T`; it is also closed. -/
theorem exists_opens_fibre (T : Set (Fin 2))
    (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (pointObj B k hk)) :
    ∃ WT : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
        (pullback (originHom B k hk n) (doubledCoordHom B k hk n))).Opens,
      IsClosed (WT : Set ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
        (pullback (originHom B k hk n) (doubledCoordHom B k hk n)))) ∧
      ∀ i, (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (siteChartSection (originHom B k hk n) i) pt ∈ WT ↔ i ∈ T := by
  classical
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  let P := pullback (originHom B k hk n) (doubledCoordHom B k hk n)
  let s := fun i : Fin 2 => q.map (siteChartSection (originHom B k hk n) i)
  have := isOpenImmersion_map_siteChartSection (originHom B k hk n)
  have hidx : ∀ i i' : Fin 2, s i pt = s i' pt → i = i' := fun i i' =>
    eq_of_siteChartSection_apply_eq _ pt (originHom_notMem_puncturedAffineSpace B k hk n pt)
  let WT : (q.obj P).Opens := ⨆ (i : Fin 2) (_ : i ∈ T), Scheme.Hom.opensRange (s i)
  have hmem : ∀ x : q.obj P, x ∈ WT ↔ ∃ i ∈ T, x = s i pt := by
    intro x
    simp only [WT, Opens.mem_iSup, Scheme.Hom.mem_opensRange]
    constructor
    · rintro ⟨i, hi, p, rfl⟩
      exact ⟨i, hi, congrArg _ (Subsingleton.elim (α := PrimeSpectrum k) p pt)⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, pt, rfl⟩
  refine ⟨WT, ?_, fun i => (hmem _).trans ⟨fun ⟨i', hi', he⟩ => hidx i i' he ▸ hi',
    fun hi => ⟨i, hi, rfl⟩⟩⟩
  have hcompl : (WT : Set (q.obj P))ᶜ = ⋃ (i : Fin 2) (_ : i ∉ T), Set.range (s i) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, hmem, Set.mem_iUnion, Set.mem_range]
    obtain ⟨i, rfl⟩ := eq_or_eq_of_originHom x pt
    constructor
    · intro h
      exact ⟨i, fun hi => h ⟨i, hi, rfl⟩, pt, rfl⟩
    · rintro ⟨l, hl, p, hp⟩ ⟨i', hi', he⟩
      rw [Subsingleton.elim (α := PrimeSpectrum k) p pt] at hp
      exact hl ((hidx l i hp).trans (hidx i i' he) ▸ hi')
  rw [← isOpen_compl_iff, hcompl]
  exact isOpen_iUnion fun i => isOpen_iUnion fun _ => (s i).isOpenEmbedding.isOpen_range

/-- Every subset of the two chart indices is cut out by a point of the finite part over the
origin: the open subspace of the pair is the union of the chart neighbourhoods it indexes, which
is open and closed in the fibre `{0₁, 0₂}`, hence finite over `Spec k`. -/
theorem exists_chartIndices_eq (T : Set (Fin 2)) :
    ∃ ξ : originPoints (B := B) (k := k) (hk := hk) (n := n),
      chartIndices ((doubledOriginFinitePart B k hk n).sections _ ξ.1) = T := by
  let F := doubledOriginFinitePart B k hk n
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  let P := pullback (originHom B k hk n) (doubledCoordHom B k hk n)
  let pt : q.obj (pointObj B k hk) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  obtain ⟨WT, hclosed, hmem⟩ := exists_opens_fibre (n := n) T pt
  let j : Stacks.SeparationLocal.openObj B (Spec (.of k)) hk P WT.ι ⟶ P :=
    Stacks.SeparationLocal.openObjHom B (Spec (.of k)) hk P WT.ι
  have hj : _root_.AlgebraicGeometry.IsOpenImmersion (q.map j) :=
    (inferInstance : _root_.AlgebraicGeometry.IsOpenImmersion WT.ι)
  have : _root_.AlgebraicGeometry.IsClosedImmersion WT.ι :=
    _root_.AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _ (by
      rwa [Scheme.Opens.range_ι])
  have : _root_.AlgebraicGeometry.IsFinite (q.map (pullback.fst (originHom B k hk n)
      (doubledCoordHom B k hk n))) :=
    isFinite_of_isPullback_of_forall_notMem (isPullback_toScheme_pullback_doubledCoordHom _)
      (originHom_notMem_puncturedAffineSpace B k hk n)
  have hfin : _root_.AlgebraicGeometry.IsFinite (q.map (j ≫ pullback.fst _ _)) := by
    rw [CategoryTheory.Functor.map_comp]
    exact (inferInstance : _root_.AlgebraicGeometry.IsFinite
      (WT.ι ≫ q.map (pullback.fst (originHom B k hk n) (doubledCoordHom B k hk n))))
  let z := FiniteOpenSubspace.ofOpenImmersion (doubledCoordHom B k hk n) (originHom B k hk n) j hfin
  have hsec : F.sections _ ((F.sections _).symm z) = z := Equiv.apply_symm_apply _ _
  refine ⟨⟨(F.sections _).symm z, by rw [hsec]; rfl⟩, ?_⟩
  dsimp only
  rw [hsec]
  have hrj : Set.range (q.map j) = (WT : Set (q.obj P)) := Scheme.Opens.range_ι WT
  exact Set.ext fun i => (mem_chartIndices_iff z rfl (j := j) rfl pt i).trans
    ((iff_of_eq (congrArg (_ ∈ ·) hrj)).trans (hmem i))

/-- A point of the finite part over the origin is determined by the chart origins its open
subspace contains: the open subscheme of the fibre `{0₁, 0₂}` representing it is determined by
which of the two points it contains, and it determines the open subspace. -/
theorem chartIndices_injective :
    Function.Injective fun ξ : originPoints (B := B) (k := k) (hk := hk) (n := n) =>
      chartIndices ((doubledOriginFinitePart B k hk n).sections _ ξ.1) := by
  intro ξ ξ' h
  dsimp only at h
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  let pt : q.obj (pointObj B k hk) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  obtain ⟨W, j, hj, hzj, -⟩ :=
    ((doubledOriginFinitePart B k hk n).sections _ ξ.1).exists_eq_range _ _ ξ.2
  obtain ⟨W', j', hj', hzj', -⟩ :=
    ((doubledOriginFinitePart B k hk n).sections _ ξ'.1).exists_eq_range _ _ ξ'.2
  have hrange : Set.range (q.map j) = Set.range (q.map j') := by
    ext x
    obtain ⟨i, rfl⟩ := eq_or_eq_of_originHom x pt
    rw [← mem_chartIndices_iff _ ξ.2 hzj pt i, ← mem_chartIndices_iff _ ξ'.2 hzj' pt i, h]
  refine Subtype.ext (((doubledOriginFinitePart B k hk n).sections _).injective ?_)
  refine FiniteOpenSubspace.ext_of_iff _ ξ.2 ξ'.2 (fun A y => ?_)
  rw [FiniteOpenSubspace.exists_comp_ι_eq_iff_range_subset _ ξ.2 hzj,
    FiniteOpenSubspace.exists_comp_ι_eq_iff_range_subset _ ξ'.2 hzj', hrange]

/-- **The four points of the finite part over the origin.** The points of `(X/Y)_fin` over the
origin, i.e. its sections over `Spec k` lying over the origin of `Y`, correspond bijectively to
the subsets of the fibre `{0₁, 0₂}` of the coordinate morphism over the origin, a point
corresponding to the set of chart origins its open subspace contains. -/
theorem exists_equiv_originPoints :
    ∃ e : originPoints (B := B) (k := k) (hk := hk) (n := n) ≃ Set (Fin 2),
      ∀ ξ, e ξ = chartIndices ((doubledOriginFinitePart B k hk n).sections _ ξ.1) :=
  ⟨Equiv.ofBijective _ ⟨chartIndices_injective, exists_chartIndices_eq⟩, fun _ => rfl⟩

/-- The finite part `(X/Y)_fin` has exactly four points over the origin. -/
theorem card_originPoints : Nat.card (originPoints (B := B) (k := k) (hk := hk) (n := n)) = 4 := by
  obtain ⟨e, -⟩ := exists_equiv_originPoints (B := B) (k := k) (hk := hk) (n := n)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin]
  rfl

end FourPoints



/-! ### Exactly three of the four points lift to an étale neighbourhood -/

section Lift

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  Space.preservesLimitsOfShape_walkingCospan_toScheme

variable {B : BigFppfSite.{u}} {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {n : ℕ}

variable (B k hk n) in
/-- The point of `(X/Y)_fin` over the origin given by a subset `T` of the fibre `{0₁, 0₂}`
*lifts to an étale neighbourhood*: there are an étale `h : U ⟶ Y`, a `k`-point `x` of `U` over
the origin, and a section of `(X/Y)_fin` over `U` with morphism `h` to `Y`, that is an open
subscheme of `U ×_Y X` finite over `U`, whose restriction along `x` is the point given by `T`
(compare `AlgebraicGeometry.Space.exists_equiv_originPoints`). -/
def IsEtaleLiftablePoint (T : Set (Fin 2)) : Prop :=
  ∃ (U : BigFppfOver B (Spec (.of k)) hk) (h : U ⟶ affineSpaceObj B k hk n)
    (_ : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B (Spec (.of k)) hk).map h))
    (x : pointObj B k hk ⟶ U) (τ : (doubledOriginFinitePart B k hk n).toFunctor.obj (op U)),
    x ≫ h = originHom B k hk n ∧
      ((doubledOriginFinitePart B k hk n).sections U τ).toBase = schemeSpaceMap h ∧
      chartIndices ((doubledOriginFinitePart B k hk n).sections _
        ((doubledOriginFinitePart B k hk n).toFunctor.map x.op τ)) = T

/-- The chart indices of the restriction of a section of the finite part along `x`: those `i`
for which the `i`-th chart section, pulled back along `x`, lies in the open subspace. -/
theorem mem_chartIndices_map_iff {U A : BigFppfOver B (Spec (.of k)) hk}
    (τ : (doubledOriginFinitePart B k hk n).toFunctor.obj (op U)) (x : A ⟶ U) (i : Fin 2) :
    i ∈ chartIndices ((doubledOriginFinitePart B k hk n).sections _
        ((doubledOriginFinitePart B k hk n).toFunctor.map x.op τ)) ↔
      ∃ l, l ≫ ((doubledOriginFinitePart B k hk n).sections U τ).subspace.ι =
        (schemeSpaceMap x).hom ≫
          chartSection ((doubledOriginFinitePart B k hk n).sections U τ) i := by
  have hbc := (doubledOriginFinitePart B k hk n).map_isBaseChange x τ
  rw [mem_chartIndices, ← hbc.chartSection_ambientMap]
  exact hbc.exists_comp_ι_eq_iff _

/-- **The fourth point does not lift.** In positive dimension the point `{0₁, 0₂}` of the finite
part over the origin does not lift to an étale neighbourhood: both chart sections would lie in the
open subspace of the lift over its `k`-point, so a neighbourhood of that point would be mapped by
the étale, hence open, morphism to `Y` entirely to the origin. -/
theorem not_isEtaleLiftablePoint_univ (hn : 0 < n) :
    ¬ IsEtaleLiftablePoint B k hk n Set.univ := by
  rintro ⟨U, h, het, x, τ, hxh, hτ, hT⟩
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  have hmem : ∀ i, ∃ l, l ≫ ((doubledOriginFinitePart B k hk n).sections U τ).subspace.ι =
      (schemeSpaceMap x).hom ≫ chartSection ((doubledOriginFinitePart B k hk n).sections U τ) i :=
    fun i => (mem_chartIndices_map_iff τ x i).mp (by rw [hT]; trivial)
  let pt : q.obj (pointObj B k hk) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hu : q.map h (q.map x pt) ∉ puncturedAffineSpace k n := by
    rw [← Scheme.Hom.comp_apply, ← CategoryTheory.Functor.map_comp, hxh]
    exact originHom_notMem_puncturedAffineSpace B k hk n pt
  obtain ⟨O, huO, hO⟩ := exists_opens_forall_notMem h _ hτ x hmem pt hu
  have hbo : _root_.AlgebraicGeometry.UniversallyOpen (q.map h) := inferInstance
  obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp
    (@mem_closure_preimage_puncturedAffineSpace k _ n hn _ (q.map h) hbo _) O O.2 huO
  exact hO y hyO hy

/-- A subset of `Fin 2` is empty, one of the two singletons, or everything. -/
theorem set_fin_two_eq (T : Set (Fin 2)) : T = ∅ ∨ T = {0} ∨ T = {1} ∨ T = Set.univ := by
  by_cases h0 : (0 : Fin 2) ∈ T <;> by_cases h1 : (1 : Fin 2) ∈ T
  · exact Or.inr (Or.inr (Or.inr (Set.eq_univ_of_forall fun i => by fin_cases i <;> assumption)))
  · refine Or.inr (Or.inl (Set.ext fun i => ?_))
    fin_cases i
    · exact iff_of_true h0 rfl
    · exact iff_of_false h1 (by simp)
  · refine Or.inr (Or.inr (Or.inl (Set.ext fun i => ?_)))
    fin_cases i
    · exact iff_of_false h0 (by simp)
    · exact iff_of_true h1 rfl
  · refine Or.inl (Set.ext fun i => iff_of_false ?_ (fun h => h))
    fin_cases i
    · exact h0
    · exact h1

/-- The open subschemes of `Y ×_Y X` through which `∅`, `{0₁}` or `{0₂}` lifts: the empty one
and the images of the two chart sections, all finite over `Y`. -/
theorem exists_opens_lift (T : Set (Fin 2)) (hT : T ≠ Set.univ)
    (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (pointObj B k hk)) :
    ∃ D : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
        (pullback (𝟙 (affineSpaceObj B k hk n)) (doubledCoordHom B k hk n))).Opens,
      _root_.AlgebraicGeometry.IsFinite (D.ι ≫ (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (pullback.fst (𝟙 (affineSpaceObj B k hk n)) (doubledCoordHom B k hk n))) ∧
      ∀ l, (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (siteChartSection (𝟙 (affineSpaceObj B k hk n)) l)
          ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (originHom B k hk n) pt) ∈ D ↔
            l ∈ T := by
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  let Y := affineSpaceObj B k hk n
  let s := fun i : Fin 2 => q.map (siteChartSection (𝟙 Y) i)
  have := isOpenImmersion_map_siteChartSection (𝟙 Y)
  have hsfst : ∀ i, s i ≫ q.map (pullback.fst (𝟙 Y) (doubledCoordHom B k hk n)) = 𝟙 _ := by
    intro i
    rw [← CategoryTheory.Functor.map_comp, siteChartSection_fst, CategoryTheory.Functor.map_id]
  let o := q.map (originHom B k hk n) pt
  have hidx : ∀ i l : Fin 2, s l o ∈ Set.range (s i) → l = i := by
    rintro i l ⟨y, hy⟩
    have hyo : y = o := by
      have := congrArg (q.map (pullback.fst (𝟙 Y) (doubledCoordHom B k hk n))) hy
      rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsfst, hsfst] at this
    rw [hyo] at hy
    refine eq_of_siteChartSection_apply_eq (𝟙 Y) o ?_ hy.symm
    rw [CategoryTheory.Functor.map_id]
    exact originHom_notMem_puncturedAffineSpace B k hk n pt
  have hsingle : ∀ i : Fin 2, ∃ D : (q.obj (pullback (𝟙 Y) (doubledCoordHom B k hk n))).Opens,
      _root_.AlgebraicGeometry.IsFinite
        (D.ι ≫ q.map (pullback.fst (𝟙 Y) (doubledCoordHom B k hk n))) ∧
      ∀ l, s l o ∈ D ↔ l ∈ ({i} : Set (Fin 2)) := by
    intro i
    refine ⟨(s i).opensRange, ?_, fun l => ⟨fun hl => hidx i l hl, ?_⟩⟩
    · rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, hsfst, Category.comp_id]
      infer_instance
    · rintro rfl
      exact ⟨o, rfl⟩
  rcases set_fin_two_eq T with rfl | rfl | rfl | rfl
  · have : IsEmpty (⊥ : (q.obj (pullback (𝟙 Y) (doubledCoordHom B k hk n))).Opens).toScheme :=
      ⟨fun x => by simpa using x.2⟩
    exact ⟨⊥, inferInstance, fun l => iff_of_false (fun h => h) (fun h => h)⟩
  · exact hsingle 0
  · exact hsingle 1
  · exact absurd rfl hT

/-- **Three of the four points lift.** The points `∅`, `{0₁}` and `{0₂}` of the finite part over
the origin lift to the étale neighbourhood `𝟙 : Y ⟶ Y` of the origin, through the empty open
subscheme of `Y ×_Y X = X` and the two charts. -/
theorem isEtaleLiftablePoint_of_ne_univ (T : Set (Fin 2)) (hT : T ≠ Set.univ) :
    IsEtaleLiftablePoint B k hk n T := by
  let F := doubledOriginFinitePart B k hk n
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  let Y := affineSpaceObj B k hk n
  let P := pullback (𝟙 Y) (doubledCoordHom B k hk n)
  let pt : q.obj (pointObj B k hk) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  obtain ⟨D, hD, hDm⟩ := exists_opens_lift (n := n) T hT pt
  let j : Stacks.SeparationLocal.openObj B (Spec (.of k)) hk P D.ι ⟶ P :=
    Stacks.SeparationLocal.openObjHom B (Spec (.of k)) hk P D.ι
  have hj : _root_.AlgebraicGeometry.IsOpenImmersion (q.map j) :=
    (inferInstance : _root_.AlgebraicGeometry.IsOpenImmersion D.ι)
  have hfin : _root_.AlgebraicGeometry.IsFinite (q.map (j ≫ pullback.fst _ _)) := by
    rw [CategoryTheory.Functor.map_comp]
    exact hD
  let z := FiniteOpenSubspace.ofOpenImmersion (doubledCoordHom B k hk n) (𝟙 Y) j hfin
  have hsec : F.sections _ ((F.sections _).symm z) = z := Equiv.apply_symm_apply _ _
  refine ⟨Y, 𝟙 Y, by rw [CategoryTheory.Functor.map_id]; infer_instance, originHom B k hk n,
    (F.sections _).symm z, Category.comp_id _, by rw [hsec]; rfl, Set.ext fun l => ?_⟩
  rw [mem_chartIndices_map_iff, hsec, chartSection_eq z (𝟙 Y) rfl l, ← Category.assoc,
    schemeSpaceMap_hom_comp, FiniteOpenSubspace.exists_comp_ι_eq_iff_range_subset _ rfl rfl,
    ← hDm l]
  have hrj : Set.range (q.map j) = (D : Set (q.obj P)) := Scheme.Opens.range_ι D
  rw [hrj]
  rw [range_subset_iff_apply_mem _ _ pt, CategoryTheory.Functor.map_comp, Scheme.Hom.comp_apply]
  rfl

/-- **Exactly three of the four points lift.** In positive dimension the points of the finite
part `(X/Y)_fin` over the origin which lift to an étale neighbourhood of the origin are exactly
`∅`, `{0₁}` and `{0₂}`. -/
theorem setOf_isEtaleLiftablePoint (hn : 0 < n) :
    {T : Set (Fin 2) | IsEtaleLiftablePoint B k hk n T} = {∅, {0}, {1}} := by
  ext T
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hT
    rcases set_fin_two_eq T with h | h | h | rfl
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h),
      absurd hT (not_isEtaleLiftablePoint_univ hn)]
  · rintro (rfl | rfl | rfl) <;> refine isEtaleLiftablePoint_of_ne_univ _ fun h => ?_
    · exact absurd (h.ge (Set.mem_univ (0 : Fin 2))) (by simp)
    · exact absurd (h.ge (Set.mem_univ (1 : Fin 2))) (by simp)
    · exact absurd (h.ge (Set.mem_univ (0 : Fin 2))) (by simp)

end Lift

/-! ### The remark -/

section Remark

variable {B : BigFppfSite.{u}} {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {n : ℕ}

/-- The coordinate morphism of affine space with doubled origin, as a morphism of algebraic
spaces over `Spec k`, is locally of finite type. -/
theorem isLocallyOfFiniteType_doubledCoordHom :
    IsLocallyOfFiniteType B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n)).hom :=
  holdsOnEveryEtaleChart_yoneda_map B (Spec (.of k)) hk
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (doubledCoordHom B k hk n) (by
      have := locallyOfFinitePresentation_coordinateMorphism k n
      exact (inferInstance : LocallyOfFiniteType (coordinateMorphism k n)))

/-- **Stacks Project, Tag 04QI.** The condition that `f` be separated cannot be dropped from
Stacks 04QH. Let `X` be affine `n`-space over a field `k` with its origin doubled, `n > 0`
(the remark takes `n = 1`, the affine line with zero doubled), `Y` affine `n`-space, and
`f : X ⟶ Y` the coordinate morphism, read as a morphism of algebraic spaces over `Spec k` in a
big fppf site containing `Spec k`. Then:

1. `f` is locally of finite type but not separated, so it satisfies every hypothesis of Stacks
   04QH except separatedness;
2. over the origin of `Y` there are exactly two points `0₁ ≠ 0₂` of `X`, the chart origins, and
   `(X/Y)_fin` has exactly four points over the origin, its sections over `Spec k` lying over the
   origin, which correspond to the four subsets `∅`, `{0₁}`, `{0₂}`, `{0₁, 0₂}` of that fibre
   (`AlgebraicGeometry.Space.exists_equiv_originPoints`);
3. of these, exactly the three subsets `∅`, `{0₁}`, `{0₂}` lift to an open subscheme of
   `U ×_Y X` finite over `U` for an étale `U ⟶ Y`
   (`AlgebraicGeometry.Space.IsEtaleLiftablePoint`, chart index `i` standing for the chart
   origin `0ᵢ`);
4. hence `(X/Y)_fin`, if it is an algebraic space, is not étale over `Y`;
5. in fact `(X/Y)_fin` is not an algebraic space ("Details omitted" in the source).

The second clause of (1) also follows from (5) and Stacks 04QH, which is how it is proved here;
(4) is proved by the argument of the remark, independently of (5). -/
@[stacks 04QI, ega "I 5.5.11" "partial"]
theorem doubledOrigin_finitePart (hn : 0 < n) :
    (IsLocallyOfFiniteType B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n)).hom ∧
      ¬ IsSeparated B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n)).hom) ∧
    ((coordinateMorphism k n).base ⁻¹' {affineOrigin k n} =
        {chartInclusion k n 0 (affineOrigin k n), chartInclusion k n 1 (affineOrigin k n)} ∧
      chartInclusion k n 0 (affineOrigin k n) ≠ chartInclusion k n 1 (affineOrigin k n)) ∧
    (∃ e : originPoints (B := B) (k := k) (hk := hk) (n := n) ≃ Set (Fin 2),
      ∀ ξ, e ξ = chartIndices ((doubledOriginFinitePart B k hk n).sections _ ξ.1)) ∧
    Nat.card (originPoints (B := B) (k := k) (hk := hk) (n := n)) = 4 ∧
    {T : Set (Fin 2) | IsEtaleLiftablePoint B k hk n T} = {∅, {0}, {1}} ∧
    (IsAlgebraicSpace B (Spec (.of k)) hk (doubledOriginFinitePart B k hk n).toFunctor →
      ¬ IsEtale B (Spec (.of k)) hk (doubledOriginFinitePart B k hk n).baseMap) ∧
    ¬ IsAlgebraicSpace B (Spec (.of k)) hk (doubledOriginFinitePart B k hk n).toFunctor :=
  ⟨⟨isLocallyOfFiniteType_doubledCoordHom, fun hsep =>
      not_isAlgebraicSpace_doubledOriginFinitePart hn
        (isAlgebraicSpace_finiteOpenSubspacePresheaf B (Spec (.of k)) hk _ hsep
          isLocallyOfFiniteType_doubledCoordHom)⟩,
    ⟨coordinateMorphism_preimage_affineOrigin k n, chartInclusion_origin_ne k n⟩,
    exists_equiv_originPoints, card_originPoints, setOf_isEtaleLiftablePoint hn,
    not_isEtale_baseMap_doubledOriginFinitePart hn, not_isAlgebraicSpace_doubledOriginFinitePart hn⟩

end Remark

end AlgebraicGeometry.Space

end
