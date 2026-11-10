module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeDoubledLineFamilies
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.DegreeDecomposition
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The Hilbert schemes of points of the affine line with doubled points

Let `S` be a scheme, `W ⊆ S` open, and let `z : Z ⟶ S` be a closed immersion of an affine scheme
which represents the `S`-schemes landing outside `W`: a morphism `T ⟶ S` factors through `z` as
soon as its image misses `W`. Let `X` be two copies of `𝔸¹_S` glued along `𝔸¹_W`
(`Stacks.Hilbert.DoubledLine.doubledLine`). This file shows that for `d ≥ 1` the degree-`d`
Hilbert functor of `X` is represented by

  `𝔸^d_W ⊔ ∐_{a = 0}^{d} 𝔸^{a + (d - a)}_Z`,

where a point of `𝔸^d_W` is a monic polynomial of degree `d` (the family it cuts out lies in
both charts, which agree over `W`) and a point of the `a`-th piece over `Z` is a pair of monic
polynomials of degrees `a` and `d - a` (the family is their zero scheme in the first chart
together with the zero scheme of the second one in the second chart, the two charts being
disjoint over `Z`).

## Main definitions

* `Stacks.Hilbert.DoubledLine.component` — the pieces of the representing scheme.
* `Stacks.Hilbert.DoubledLine.hilb` — the representing scheme.
* `Stacks.Hilbert.DoubledLine.universalFamily` — its universal family.

## Main results

* `Stacks.Hilbert.DoubledLine.representsHilbertFunctorOfRank` — `hilb` represents the degree-`d`
  Hilbert functor of the doubled line, for `d ≥ 1`.

## Implementation notes

The proof goes through the local criterion `Stacks.Hilbert.bijective_baseChange_of_local`. Two
inputs are geometric. Families of positive degree split the base into the parts over `W` and
outside `W` (`Stacks.Hilbert.DoubledLine.isClosed_preimage_of_family`); this is where the
finiteness of a family enters. Over a base outside `W` the two chart pieces of a family have
locally constant degrees, which are made constant by shrinking to a stratum of the rank
function (`Stacks.Morphisms.rankStratum`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms Polynomial

universe u

namespace Stacks.Hilbert.DoubledLine

open AffineLine

variable {S : Scheme.{u}} (W : S.Opens) {Z : Scheme.{u}} (z : Z ⟶ S)

/-! ### The representing scheme -/

/-- Affine space over a scheme `B ⟶ S`, as an `S`-scheme. -/
abbrev affOver {B : Scheme.{u}} (j : B ⟶ S) (n : Type u) : Over S := Over.mk (𝔸(n; B) ↘ B ≫ j)

/-- The pieces of the degree-`d` Hilbert scheme of the doubled line: affine `d`-space over `W`,
and for each `a ≤ d` an affine `d`-space over `Z` whose coordinates are split into `a` and
`d - a` of them. -/
def component (d : ℕ) : Option (Fin (d + 1)) → Over S
  | none => affOver W.ι (ULift.{u} (Fin d))
  | some a => affOver z (ULift.{u} (Fin a ⊕ Fin (d - a)))

/-- **The degree-`d` Hilbert scheme of the doubled line**, as the disjoint union of its pieces. -/
def hilb (d : ℕ) : Over S :=
  Over.mk (Sigma.desc fun τ ↦ (component W z d τ).hom)

/-- The inclusion of a piece. -/
def ιH (d : ℕ) (τ : Option (Fin (d + 1))) : component W z d τ ⟶ hilb W z d :=
  Over.homMk (Sigma.ι (fun τ ↦ (component W z d τ).left) τ) (Sigma.ι_comp_desc _ _)

/-- The inclusion of a piece into the Hilbert scheme is an open immersion. -/
instance (d : ℕ) (τ : Option (Fin (d + 1))) : IsOpenImmersion (ιH W z d τ).left :=
  inferInstanceAs (IsOpenImmersion (Sigma.ι (fun τ ↦ (component W z d τ).left) τ))

/-- The piece over `W` lies over `W`. -/
theorem component_none_hom_mem (d : ℕ) (x : (component W z d none).left) :
    (component W z d none).hom x ∈ W := by
  change (W.ι ((𝔸(ULift.{u} (Fin d); W.toScheme) ↘ W.toScheme) x)) ∈ W
  exact ((𝔸(ULift.{u} (Fin d); W.toScheme) ↘ W.toScheme) x).2

/-- The pieces over `Z` lie outside `W`. -/
theorem component_some_hom_not_mem (hzW : ∀ x, z x ∉ W) (d : ℕ) (a : Fin (d + 1))
    (x : (component W z d (some a)).left) : (component W z d (some a)).hom x ∉ W :=
  hzW _

/-- A morphism of `S`-schemes commutes with the structure maps on points. -/
private theorem hom_left_apply {V U : Over S} (h : V ⟶ U) (v : V.left) :
    U.hom (h.left v) = V.hom v := by
  rw [← Scheme.Hom.comp_apply, Over.w h]

/-- An `S`-scheme mapping to the piece over `W` lies over `W`. -/
private theorem hom_mem_of_hom_none {V : Over S} {d : ℕ} (h : V ⟶ component W z d none)
    (v : V.left) : V.hom v ∈ W := by
  rw [← hom_left_apply h v]
  exact component_none_hom_mem W z d _

/-- An `S`-scheme mapping to a piece over `Z` lies outside `W`. -/
private theorem hom_not_mem_of_hom_some (hzW : ∀ x, z x ∉ W) {V : Over S} {d : ℕ} {a : Fin (d + 1)}
    (h : V ⟶ component W z d (some a)) (v : V.left) : V.hom v ∉ W := by
  rw [← hom_left_apply h v]
  exact component_some_hom_not_mem W z hzW d a _

/-! ### Morphisms into the pieces -/

variable {W z}

/-- A morphism to the piece over `W` from an `S`-scheme landing in `W`, given its coordinates. -/
def homNone {V : Over S} (hV : ∀ v, V.hom v ∈ W) {d : ℕ} (c : Fin d → Γ(V.left, ⊤)) :
    V ⟶ component W z d none :=
  Over.homMk (AffineSpace.homOfVector
    (IsOpenImmersion.lift W.ι V.hom (by rintro _ ⟨v, rfl⟩; simpa using hV v))
    fun i ↦ c i.down) (by
      change AffineSpace.homOfVector _ _ ≫ (𝔸(ULift.{u} (Fin d); W.toScheme) ↘ W.toScheme) ≫
        W.ι = V.hom
      rw [AffineSpace.homOfVector_over_assoc, IsOpenImmersion.lift_fac])

/-- The coordinates of `homNone hV c` are `c`. -/
theorem homNone_coord {V : Over S} (hV : ∀ v, V.hom v ∈ W) {d : ℕ} (c : Fin d → Γ(V.left, ⊤))
    (i : Fin d) : (homNone (z := z) hV c).left.appTop (AffineSpace.coord W.toScheme ⟨i⟩) = c i :=
  AffineSpace.homOfVector_appTop_coord _ _ _

variable (hfac : ∀ {T : Scheme.{u}} (f : T ⟶ S), (∀ t, f t ∉ W) → ∃ g : T ⟶ Z, g ≫ z = f)
include hfac

/-- A morphism to the `a`-th piece over `Z` from an `S`-scheme landing outside `W`, given its
coordinates. -/
def homSome {V : Over S} (hV : ∀ v, V.hom v ∉ W) {d : ℕ} (a : Fin (d + 1))
    (c₁ : Fin a → Γ(V.left, ⊤)) (c₂ : Fin (d - a) → Γ(V.left, ⊤)) :
    V ⟶ component W z d (some a) :=
  Over.homMk (AffineSpace.homOfVector (hfac V.hom hV).choose fun i ↦ Sum.elim c₁ c₂ i.down) (by
    change AffineSpace.homOfVector _ _ ≫ (𝔸(ULift.{u} (Fin a ⊕ Fin (d - a)); Z) ↘ Z) ≫ z = V.hom
    rw [AffineSpace.homOfVector_over_assoc, (hfac V.hom hV).choose_spec])

/-- The coordinates of `homSome hfac hV a c₁ c₂` are `c₁` followed by `c₂`. -/
theorem homSome_coord {V : Over S} (hV : ∀ v, V.hom v ∉ W) {d : ℕ} (a : Fin (d + 1))
    (c₁ : Fin a → Γ(V.left, ⊤)) (c₂ : Fin (d - a) → Γ(V.left, ⊤)) (i : Fin a ⊕ Fin (d - a)) :
    (homSome hfac hV a c₁ c₂).left.appTop (AffineSpace.coord Z ⟨i⟩) = Sum.elim c₁ c₂ i :=
  AffineSpace.homOfVector_appTop_coord _ _ _

omit hfac

/-- Morphisms into affine space over `B`, viewed as an `S`-scheme through a monomorphism
`B ⟶ S`, agree when their coordinates agree. -/
private theorem affOver_hom_ext {B : Scheme.{u}} {j : B ⟶ S} [Mono j] {n : Type u} {V : Over S}
    {g g' : V ⟶ affOver j n}
    (h : ∀ i, g.left.appTop (AffineSpace.coord B i) = g'.left.appTop (AffineSpace.coord B i)) :
    g = g' := by
  let g₀ : V.left ⟶ 𝔸(n; B) := g.left
  let g₀' : V.left ⟶ 𝔸(n; B) := g'.left
  have hw : g₀ ≫ ((𝔸(n; B) ↘ B) ≫ j) = g₀' ≫ ((𝔸(n; B) ↘ B) ≫ j) :=
    (Over.w g).trans (Over.w g').symm
  exact Over.OverMorphism.ext (AffineSpace.hom_ext
    ((cancel_mono j).mp (by simpa only [Category.assoc] using hw)) h)

/-- Morphisms into the piece over `W` agree when their coordinates agree. -/
theorem component_none_hom_ext {V : Over S} {d : ℕ} {g g' : V ⟶ component W z d none}
    (h : ∀ i, g.left.appTop (AffineSpace.coord W.toScheme i) =
      g'.left.appTop (AffineSpace.coord W.toScheme i)) : g = g' :=
  affOver_hom_ext (j := W.ι) h

/-- Morphisms into a piece over `Z` agree when their coordinates agree. -/
theorem component_some_hom_ext [Mono z] {V : Over S} {d : ℕ} {a : Fin (d + 1)}
    {g g' : V ⟶ component W z d (some a)}
    (h : ∀ i, g.left.appTop (AffineSpace.coord Z i) = g'.left.appTop (AffineSpace.coord Z i)) :
    g = g' :=
  affOver_hom_ext (j := z) h

/-! ### The universal family -/

/-- In a cartesian square of schemes, the image of the first projection is the inverse image of
the image of the opposite side. -/
theorem range_fst_of_isPullback {P A B C : Scheme.{u}} {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ C}
    {g : B ⟶ C} (h : IsPullback fst snd f g) : Set.range fst = f ⁻¹' Set.range g := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso h.isoPullback.hom.base).2.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]

variable (W z)

/-- Distinct pieces of the Hilbert scheme have disjoint images. -/
theorem range_sigmaι_disjoint (d : ℕ) {τ τ' : Option (Fin (d + 1))} (h : τ ≠ τ') :
    Disjoint (Set.range (ιH W z d τ).left) (Set.range (ιH W z d τ').left) :=
  TopologicalSpace.Opens.coe_disjoint.mpr
    (disjoint_opensRange_sigmaι (g := fun τ ↦ (component W z d τ).left) τ τ' h)

/-- Every point of the Hilbert scheme lies in one of its pieces. -/
theorem exists_ιH_eq (d : ℕ) (x : (hilb W z d).left) :
    ∃ τ y, (ιH W z d τ).left y = x :=
  (sigmaOpenCover (fun τ ↦ (component W z d τ).left)).exists_eq x

/-- Each piece of the Hilbert scheme has closed image. -/
theorem isClosed_range_ιH (d : ℕ) (τ : Option (Fin (d + 1))) :
    IsClosed (Set.range (ιH W z d τ).left) := by
  have hc : (Set.range (ιH W z d τ).left)ᶜ =
      ⋃ τ' ∈ ({τ}ᶜ : Set _), Set.range (ιH W z d τ').left := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨τ', y, rfl⟩ := exists_ιH_eq W z d x
      refine ⟨τ', ?_, y, rfl⟩
      rintro rfl
      exact hx ⟨y, rfl⟩
    · rintro ⟨τ', hτ', hx⟩ hx'
      exact Set.disjoint_left.mp (range_sigmaι_disjoint W z d (Ne.symm hτ')) hx' hx
  rw [← isOpen_compl_iff, hc]
  exact isOpen_biUnion fun τ' _ ↦ (ιH W z d τ').left.isOpenEmbedding.isOpen_range

/-- The doubled line over a piece of the Hilbert scheme, inside the doubled line over the whole
Hilbert scheme. -/
abbrev ε (d : ℕ) (τ : Option (Fin (d + 1))) :
    total W (component W z d τ) ⟶ total W (hilb W z d) :=
  familyBaseChangeMap (doubledLine W) (ιH W z d τ)

/-- The doubled line over a piece is an open subscheme of the doubled line over `hilb W z d`. -/
instance (d : ℕ) (τ : Option (Fin (d + 1))) : IsOpenImmersion (ε W z d τ) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_familyBaseChangeMap (doubledLine W) (ιH W z d τ)).flip
    (inferInstanceAs (IsOpenImmersion (ιH W z d τ).left))

/-- The image of `ε W z d τ` is the inverse image of the image of the `τ`-th piece. -/
theorem range_ε (d : ℕ) (τ : Option (Fin (d + 1))) :
    Set.range (ε W z d τ) = ((Over.pullback (hilb W z d).hom).obj (doubledLine W)).hom ⁻¹'
      Set.range (ιH W z d τ).left :=
  range_fst_of_isPullback (isPullback_familyBaseChangeMap (doubledLine W) (ιH W z d τ))

/-- The doubled line over a piece is a closed subscheme of the doubled line over `hilb W z d`. -/
instance (d : ℕ) (τ : Option (Fin (d + 1))) : IsClosedImmersion (ε W z d τ) := by
  refine isClosedImmersion_of_isOpenImmersion _ ?_
  rw [range_ε]
  exact (isClosed_range_ιH W z d τ).preimage (Scheme.Hom.continuous _)

/-- The doubled lines over distinct pieces have disjoint images. -/
theorem ε_disjoint (d : ℕ) :
    Pairwise fun τ τ' ↦ Disjoint (Set.range (ε W z d τ)) (Set.range (ε W z d τ')) := by
  intro τ τ' h
  rw [range_ε, range_ε]
  exact (range_sigmaι_disjoint W z d h).preimage _

/-- The coordinates on the piece over `W`. -/
def coordsNone (d : ℕ) : Fin d → Γ((component W z d none).left, ⊤) :=
  fun i ↦ AffineSpace.coord W.toScheme ⟨i⟩

/-- The first `a` coordinates on the `a`-th piece over `Z`. -/
def coords₁ (d : ℕ) (a : Fin (d + 1)) : Fin a → Γ((component W z d (some a)).left, ⊤) :=
  fun i ↦ AffineSpace.coord Z ⟨Sum.inl i⟩

/-- The last `d - a` coordinates on the `a`-th piece over `Z`. -/
def coords₂ (d : ℕ) (a : Fin (d + 1)) : Fin (d - a) → Γ((component W z d (some a)).left, ⊤) :=
  fun i ↦ AffineSpace.coord Z ⟨Sum.inr i⟩

/-- The universal family over the piece over `W`: the zero scheme, in both charts, of the
universal monic polynomial of degree `d`. -/
def familyNone (d : ℕ) : HilbertFamily (doubledLine W) (component W z d none) d where
  ideal := (zeroIdeal _ (monicOfCoeffs (coordsNone W z d))).comap (foldT W _)
  isFiniteLocallyFreeOfRank := by
    have := isIso_chartT W _ (component_none_hom_mem W z d) true
    refine (isFiniteLocallyFreeOfRank_comap_iff_of_isIso (chartT W _ true) _ _
      (chartT_hom W _ true) _ d).mp ?_
    rw [← Scheme.IdealSheafData.comap_comp, chartT_foldT, Scheme.IdealSheafData.comap_id]
    exact isFiniteLocallyFreeOfRank_zeroIdeal _ _

/-- In either chart, the universal family over the piece over `W` is the zero scheme of the
universal monic polynomial of degree `d`. -/
theorem familyNone_comap (d : ℕ) (b : Bool) :
    (familyNone W z d).ideal.comap (chartT W _ b) =
      zeroIdeal _ (monicOfCoeffs (coordsNone W z d)) := by
  rw [familyNone, ← Scheme.IdealSheafData.comap_comp, chartT_foldT,
    Scheme.IdealSheafData.comap_id]

/-- The chart ideals of the universal family over the `a`-th piece over `Z`. -/
def chartIdeals (d : ℕ) (a : Fin (d + 1)) :
    Bool → (ambient (component W z d (some a))).IdealSheafData
  | true => zeroIdeal _ (monicOfCoeffs (coords₁ W z d a))
  | false => zeroIdeal _ (monicOfCoeffs (coords₂ W z d a))

variable (hzW : ∀ x, z x ∉ W)
include hzW

/-- Over a piece over `Z`, the two charts of the doubled line have disjoint images. -/
theorem chartT_disjoint (d : ℕ) (a : Fin (d + 1)) :
    Pairwise fun b b' : Bool ↦ Disjoint (Set.range (chartT W (component W z d (some a)) b))
      (Set.range (chartT W (component W z d (some a)) b')) := by
  have h := range_chartT_false_eq_compl W _ (component_some_hom_not_mem W z hzW d a)
  intro b b' hbb'
  cases b <;> cases b'
  · exact absurd rfl hbb'
  · rw [h]
    exact disjoint_compl_left
  · rw [h]
    exact disjoint_compl_right
  · exact absurd rfl hbb'

/-- Over a piece over `Z`, each chart of the doubled line is a closed immersion. -/
theorem chartT_isClosedImmersion (d : ℕ) (a : Fin (d + 1)) (b : Bool) :
    IsClosedImmersion (chartT W (component W z d (some a)) b) :=
  isClosedImmersion_chartT W _ (component_some_hom_not_mem W z hzW d a) b

/-- The ideal glued from `chartIdeals W z d a` restricts to `chartIdeals W z d a b` on the chart
`b`. -/
theorem glue_chartIdeals_comap (d : ℕ) (a : Fin (d + 1)) (b : Bool) :
    (glueIdeal (chartT W _) (chartIdeals W z d a)).comap
      (chartT W (component W z d (some a)) b) = chartIdeals W z d a b :=
  have := chartT_isClosedImmersion W z hzW d a
  comap_glueIdeal (chartT W _) (chartT_disjoint W z hzW d a) (chartIdeals W z d a) b

variable [IsAffine Z]

/-- The pieces over `Z` are affine. -/
instance (d : ℕ) (a : Fin (d + 1)) : IsAffine (component W z d (some a)).left :=
  inferInstanceAs (IsAffine 𝔸(ULift.{u} (Fin a ⊕ Fin (d - a)); Z))

omit hzW in
/-- For `a ≤ d`, `a + (d - a) = d`. -/
theorem a_add_sub (d : ℕ) (a : Fin (d + 1)) : (a : ℕ) + (d - a) = d :=
  Nat.add_sub_cancel' (Nat.lt_succ_iff.mp a.2)

/-- The universal family over the `a`-th piece over `Z`: the zero scheme of the first universal
monic polynomial in the first chart together with the zero scheme of the second one in the second
chart. -/
def familySome (d : ℕ) (a : Fin (d + 1)) :
    HilbertFamily (doubledLine W) (component W z d (some a)) d where
  ideal := glueIdeal (chartT W _) (chartIdeals W z d a)
  isFiniteLocallyFreeOfRank := by
    have h := isFiniteLocallyFreeOfRank_of_charts (component_some_hom_not_mem W z hzW d a)
      (glueIdeal (chartT W _) (chartIdeals W z d a)) (r₁ := a) (r₂ := d - a)
      (by rw [glue_chartIdeals_comap W z hzW]; exact isFiniteLocallyFreeOfRank_zeroIdeal _ _)
      (by rw [glue_chartIdeals_comap W z hzW]; exact isFiniteLocallyFreeOfRank_zeroIdeal _ _)
    rwa [a_add_sub] at h

/-- The universal families over the pieces. -/
def familyComponent (d : ℕ) :
    (τ : Option (Fin (d + 1))) → HilbertFamily (doubledLine W) (component W z d τ) d
  | none => familyNone W z d
  | some a => familySome W z hzW d a

/-- **The universal family** over the Hilbert scheme of the doubled line, glued from the universal
families over its pieces. -/
def universalFamily (d : ℕ) : HilbertFamily (doubledLine W) (hilb W z d) d where
  ideal := glueIdeal (ε W z d) fun τ ↦ (familyComponent W z hzW d τ).ideal
  isFiniteLocallyFreeOfRank := by
    refine isFiniteLocallyFreeOfRank_of_cover (doubledLine W) _ d (component W z d) (ιH W z d)
      (exists_ιH_eq W z d) fun τ ↦ ?_
    rw [comap_glueIdeal (ε W z d) (ε_disjoint W z d)]
    exact (familyComponent W z hzW d τ).isFiniteLocallyFreeOfRank

/-- The universal family restricts to the universal family of each piece. -/
theorem baseChange_ιH_universalFamily (d : ℕ) (τ : Option (Fin (d + 1))) :
    baseChange (doubledLine W) (ιH W z d τ) (universalFamily W z hzW d) =
      familyComponent W z hzW d τ := by
  refine HilbertFamily.ext ?_
  rw [baseChange_ideal]
  exact comap_glueIdeal (ε W z d) (ε_disjoint W z d) _ τ

/-! ### Comparing families through the charts -/

omit hzW [IsAffine Z] in
/-- **A family in the doubled line is determined by its two chart pieces.** -/
theorem family_ext_of_charts {V : Over S} {d : ℕ} {D D' : HilbertFamily (doubledLine W) V d}
    (h : ∀ b, D.ideal.comap (chartT W V b) = D'.ideal.comap (chartT W V b)) : D = D' :=
  HilbertFamily.ext (idealSheafData_eq_of_comap_eq (chartT W V)
    (fun b ↦ inferInstanceAs (Flat (chartT W V b)))
    (exists_chartT_eq W V) h)

omit hzW [IsAffine Z] in
/-- The chart pieces of a base change of a family are the base changes of its chart pieces. -/
theorem comap_chartT_baseChange {V T : Over S} (g : V ⟶ T) {d : ℕ}
    (D : HilbertFamily (doubledLine W) T d) (b : Bool) :
    (baseChange (doubledLine W) g D).ideal.comap (chartT W V b) =
      (D.ideal.comap (chartT W T b)).comap (familyBaseChangeMap (line S) g) := by
  rw [baseChange_ideal, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    chartT_naturality]

omit hzW [IsAffine Z] in
/-- Over a nonempty base, a finite locally free morphism has only one rank. -/
theorem eq_of_isFiniteLocallyFreeOfRank {A B : Scheme.{u}} (f : A ⟶ B) {a b : ℕ}
    (ha : IsFiniteLocallyFreeOfRank f a) (hb : IsFiniteLocallyFreeOfRank f b) (t : B) : a = b := by
  obtain ⟨hfin, hflat, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f a)
  exact ((isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f a).mp ha t).symm.trans
    ((isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f b).mp hb t)

omit hzW [IsAffine Z] in
/-- Over an affine base, monic polynomials cutting out the same subscheme of the affine line have
the same coefficients. -/
theorem eq_of_zeroIdeal_eq {V : Over S} [IsAffine V.left] {d : ℕ} {c c' : Fin d → Γ(V.left, ⊤)}
    (h : zeroIdeal V (monicOfCoeffs c) = zeroIdeal V (monicOfCoeffs c')) : c = c' := by
  obtain ⟨c₀, -, huniq⟩ := existsUnique_eq_monicFamily V (monicFamily V c')
  exact (huniq c (HilbertFamily.ext h)).trans (huniq c' rfl).symm

omit hzW [IsAffine Z] in
/-- The base change along `g` of the zero scheme of the monic polynomial with coefficients `c`
is the zero scheme of the monic polynomial with coefficients the pullbacks of `c` along `g`. -/
theorem comap_zeroIdeal_coords {V : Over S} {C : Over S} (g : V ⟶ C) {n : ℕ}
    (c : Fin n → Γ(C.left, ⊤)) :
    (zeroIdeal C (monicOfCoeffs c)).comap (familyBaseChangeMap (line S) g) =
      zeroIdeal V (monicOfCoeffs fun i ↦ g.left.appTop (c i)) := by
  rw [comap_zeroIdeal, map_monicOfCoeffs]

/-- The chart pieces of the pullback of the universal family over a piece over `Z` along `h` are
the zero schemes of the monic polynomials whose coefficients are the pullbacks along `h` of the
first and of the last coordinates. -/
theorem comap_chartT_baseChange_some {V : Over S} {d : ℕ} {a : Fin (d + 1)}
    (h : V ⟶ component W z d (some a)) :
    (baseChange (doubledLine W) h (familySome W z hzW d a)).ideal.comap (chartT W V true) =
        zeroIdeal V (monicOfCoeffs fun i ↦ h.left.appTop (coords₁ W z d a i)) ∧
      (baseChange (doubledLine W) h (familySome W z hzW d a)).ideal.comap (chartT W V false) =
        zeroIdeal V (monicOfCoeffs fun i ↦ h.left.appTop (coords₂ W z d a i)) := by
  refine ⟨?_, ?_⟩ <;> rw [comap_chartT_baseChange, familySome, glue_chartIdeals_comap W z hzW] <;>
    exact comap_zeroIdeal_coords h _

omit hzW [IsAffine Z] in
/-- Both chart pieces of the pullback of the universal family over the piece over `W` along `h`
are the zero scheme of the monic polynomial whose coefficients are the pullbacks of the
coordinates along `h`. -/
theorem comap_chartT_baseChange_none {V : Over S} {d : ℕ} (h : V ⟶ component W z d none)
    (b : Bool) :
    (baseChange (doubledLine W) h (familyNone W z d)).ideal.comap (chartT W V b) =
      zeroIdeal V (monicOfCoeffs fun i ↦ h.left.appTop (coordsNone W z d i)) := by
  rw [comap_chartT_baseChange, familyNone_comap]
  exact comap_zeroIdeal_coords h _

/-! ### Local uniqueness of classifying morphisms -/

omit hzW [IsAffine Z] in
/-- A morphism into the Hilbert scheme whose image lies in a piece factors through that piece. -/
theorem exists_lift_ιH {V : Over S} {d : ℕ} (g : V ⟶ hilb W z d) (τ : Option (Fin (d + 1)))
    (hg : Set.range g.left ⊆ Set.range (ιH W z d τ).left) :
    ∃ h : V ⟶ component W z d τ, h ≫ ιH W z d τ = g := by
  let l := IsOpenImmersion.lift (ιH W z d τ).left g.left hg
  have hl : l ≫ (ιH W z d τ).left = g.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
  rw [← Over.w (ιH W z d τ), ← Category.assoc, hl, Over.w g]

/-- The pullback of the universal family along `h ≫ ιH W z d τ` is the pullback along `h` of the
universal family of the `τ`-th piece. -/
theorem baseChange_comp_ιH {V : Over S} {d : ℕ} {τ : Option (Fin (d + 1))}
    (h : V ⟶ component W z d τ) :
    baseChange (doubledLine W) (h ≫ ιH W z d τ) (universalFamily W z hzW d) =
      baseChange (doubledLine W) h (familyComponent W z hzW d τ) := by
  rw [baseChange_comp, baseChange_ιH_universalFamily]

variable [Mono z]

/-- Two morphisms into pieces of the Hilbert scheme along which the universal families pull back
to the same family agree as morphisms into the Hilbert scheme. -/
private theorem ιH_comp_eq_of_baseChange_eq {V : Over S} [IsAffine V.left] {d : ℕ}
    {τ τ' : Option (Fin (d + 1))} (h : V ⟶ component W z d τ) (h' : V ⟶ component W z d τ')
    (hb : baseChange (doubledLine W) h (familyComponent W z hzW d τ) =
      baseChange (doubledLine W) h' (familyComponent W z hzW d τ')) (v : V.left) :
    h ≫ ιH W z d τ = h' ≫ ιH W z d τ' := by
  have hc := fun b ↦ congrArg (fun D ↦ D.ideal.comap (chartT W V b)) hb
  cases τ with
  | none =>
    cases τ' with
    | none =>
      congr 1
      refine component_none_hom_ext fun i ↦ ?_
      have hc := hc true
      simp only [familyComponent, comap_chartT_baseChange_none] at hc
      exact congrFun (eq_of_zeroIdeal_eq hc) i.down
    | some a' =>
      exact absurd (hom_mem_of_hom_none W z h v) (hom_not_mem_of_hom_some W z hzW h' v)
  | some a =>
    cases τ' with
    | none =>
      exact absurd (hom_mem_of_hom_none W z h' v) (hom_not_mem_of_hom_some W z hzW h v)
    | some a' =>
      have hc₁ := hc true
      have hc₂ := hc false
      simp only [familyComponent, comap_chartT_baseChange_some W z hzW h,
        comap_chartT_baseChange_some W z hzW h'] at hc₁ hc₂
      obtain rfl : a = a' := by
        have r₁ := isFiniteLocallyFreeOfRank_zeroIdeal V
          (fun i ↦ h.left.appTop (coords₁ W z d a i))
        have r₂ := isFiniteLocallyFreeOfRank_zeroIdeal V
          (fun i ↦ h'.left.appTop (coords₁ W z d a' i))
        rw [← hc₁] at r₂
        exact Fin.ext (eq_of_isFiniteLocallyFreeOfRank _ r₁ r₂ v)
      congr 1
      refine component_some_hom_ext fun i ↦ ?_
      obtain ⟨i | i⟩ := i
      · exact congrFun (eq_of_zeroIdeal_eq hc₁) i
      · exact congrFun (eq_of_zeroIdeal_eq hc₂) i

/-- **Classifying morphisms are locally unique.** -/
theorem hom_locally_eq {T : Over S} {d : ℕ} (g g' : T ⟶ hilb W z d)
    (hgg' : baseChange (doubledLine W) g (universalFamily W z hzW d) =
      baseChange (doubledLine W) g' (universalFamily W z hzW d)) (t : T.left) :
    ∃ V : T.left.Opens, t ∈ V ∧ Over.restrictι T V ≫ g = Over.restrictι T V ≫ g' := by
  obtain ⟨τ, y, hy⟩ := exists_ιH_eq W z d (g.left t)
  obtain ⟨τ', y', hy'⟩ := exists_ιH_eq W z d (g'.left t)
  let O : T.left.Opens := g.left ⁻¹ᵁ (ιH W z d τ).left.opensRange ⊓
    g'.left ⁻¹ᵁ (ιH W z d τ').left.opensRange
  have htO : t ∈ O := ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
  obtain ⟨_, ⟨V, hVaff, rfl⟩, htV, hVO⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open htO O.2
  have : IsAffine (Over.restrict T V).left := hVaff
  refine ⟨V, htV, ?_⟩
  obtain ⟨h, hh⟩ := exists_lift_ιH W z (Over.restrictι T V ≫ g) τ
    (Set.range_subset_iff.mpr fun v ↦ (hVO v.2).1)
  obtain ⟨h', hh'⟩ := exists_lift_ιH W z (Over.restrictι T V ≫ g') τ'
    (Set.range_subset_iff.mpr fun v ↦ (hVO v.2).2)
  have hb : baseChange (doubledLine W) h (familyComponent W z hzW d τ) =
      baseChange (doubledLine W) h' (familyComponent W z hzW d τ') := by
    rw [← baseChange_comp_ιH, ← baseChange_comp_ιH, hh, hh', baseChange_comp, baseChange_comp,
      hgg']
  rw [← hh, ← hh']
  exact ιH_comp_eq_of_baseChange_eq W z hzW h h' hb ⟨t, htV⟩

/-! ### Local existence of classifying morphisms -/

omit [Mono z] in
/-- **Over a base landing in `W`, every family is classified, locally on the base.** -/
theorem exists_classifying_of_mem {T : Over S} {d : ℕ} (D : HilbertFamily (doubledLine W) T d)
    (t : T.left) (ht : T.hom t ∈ W) :
    ∃ (V : Over S) (i : V ⟶ T) (_ : IsOpenImmersion i.left) (v : V.left), i.left v = t ∧
      ∃ g : V ⟶ hilb W z d, baseChange (doubledLine W) g (universalFamily W z hzW d) =
        baseChange (doubledLine W) i D := by
  obtain ⟨V, hVaff, htV, hVO⟩ := exists_isAffineOpen_mem_le T.left (T.hom ⁻¹ᵁ W) t ht
  have : IsAffine (Over.restrict T V).left := hVaff
  have hV : ∀ v, (Over.restrict T V).hom v ∈ W := fun v ↦ hVO v.2
  obtain ⟨c, hc, -⟩ := existsUnique_eq_monicFamily (Over.restrict T V)
    (familyToLine W hV (baseChange (doubledLine W) (Over.restrictι T V) D))
  refine ⟨Over.restrict T V, Over.restrictι T V, inferInstanceAs (IsOpenImmersion V.ι),
    ⟨t, htV⟩, rfl, homNone hV c ≫ ιH W z d none, ?_⟩
  rw [baseChange_comp_ιH]
  refine family_ext_of_charts W fun b ↦ ?_
  have hcoord : (fun i ↦ (homNone (z := z) hV c).left.appTop (coordsNone W z d i)) = c :=
    funext fun i ↦ homNone_coord hV c i
  change _ = (baseChange (doubledLine W) (Over.restrictι T V) D).ideal.comap _
  rw [familyComponent, comap_chartT_baseChange_none, hcoord,
    ← chartT_true_eq_false' W (Over.restrict T V) hV b]
  exact congrArg HilbertFamily.ideal hc

include hfac

omit [Mono z] in
/-- **Over a base landing outside `W`, every family is classified, locally on the base.** -/
theorem exists_classifying_of_not_mem {T : Over S} {d : ℕ}
    (D : HilbertFamily (doubledLine W) T d) (O : T.left.Opens) (hO : ∀ v ∈ O, T.hom v ∉ W)
    (t : T.left) (ht : t ∈ O) :
    ∃ (V : Over S) (i : V ⟶ T) (_ : IsOpenImmersion i.left) (v : V.left), i.left v = t ∧
      ∃ g : V ⟶ hilb W z d, baseChange (doubledLine W) g (universalFamily W z hzW d) =
        baseChange (doubledLine W) i D := by
  set O' := Over.restrict T O
  have hO' : ∀ v, O'.hom v ∉ W := fun v ↦ hO v.1 v.2
  set DO := baseChange (doubledLine W) (Over.restrictι T O) D
  have hfin := fun b ↦ finite_flat_lfp_of_isFiniteLocallyFreeOfRank hO' DO.ideal
    DO.isFiniteLocallyFreeOfRank b
  let κ := fun b : Bool ↦ (DO.ideal.comap (chartT W O' b)).subschemeι ≫ proj O'
  have : ∀ b, IsFinite (κ b) := fun b ↦ (hfin b).1
  have : ∀ b, Flat (κ b) := fun b ↦ (hfin b).2.1
  have : ∀ b, LocallyOfFinitePresentation (κ b) := fun b ↦ (hfin b).2.2
  let t₀ : O'.left := ⟨t, ht⟩
  obtain ⟨r₁, hr₁⟩ : ∃ r, (κ true).finrank t₀ = r := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r, (κ false).finrank t₀ = r := ⟨_, rfl⟩
  let N : O'.left.Opens := rankStratum (κ true) r₁ ⊓ rankStratum (κ false) r₂
  have htN : t₀ ∈ N := ⟨hr₁, hr₂⟩
  obtain ⟨V, hVaff, htV, hVN⟩ := exists_isAffineOpen_mem_le O'.left N t₀ htN
  set V' := Over.restrict O' V
  have : IsAffine V'.left := hVaff
  have hV' : ∀ v, V'.hom v ∉ W := fun v ↦ hO' _
  set i := Over.restrictι O' V ≫ Over.restrictι T O
  have hi : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (V.ι ≫ O.ι))
  set DV := baseChange (doubledLine W) i D
  have hDV : DV = baseChange (doubledLine W) (Over.restrictι O' V) DO := baseChange_comp _ _ _ _
  have hrank : ∀ (b : Bool) (r : ℕ), (∀ x ∈ V, (κ b).finrank x = r) →
      IsFiniteLocallyFreeOfRank ((DV.ideal.comap (chartT W V' b)).subschemeι ≫ proj V') r := by
    intro b r hr
    rw [hDV, comap_chartT_baseChange]
    have sq := isPullback_familyBaseChangeMap_subschemeι (line S) (Over.restrictι O' V)
      (DO.ideal.comap (chartT W O' b))
    have : IsFinite ((DO.ideal.comap (chartT W O' b)).subschemeι ≫ proj O') := (hfin b).1
    have : Flat ((DO.ideal.comap (chartT W O' b)).subschemeι ≫ proj O') := (hfin b).2.1
    have : IsFinite ((((DO.ideal.comap (chartT W O' b))).comap
        (familyBaseChangeMap (line S) (Over.restrictι O' V))).subschemeι ≫ proj V') :=
      MorphismProperty.of_isPullback sq inferInstance
    have : Flat ((((DO.ideal.comap (chartT W O' b))).comap
        (familyBaseChangeMap (line S) (Over.restrictι O' V))).subschemeι ≫ proj V') :=
      MorphismProperty.of_isPullback sq inferInstance
    refine (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ r).mpr fun v ↦ ?_
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq]
    exact hr _ v.2
  have h₁ := hrank true r₁ fun x hx ↦ (hVN hx).1
  have h₂ := hrank false r₂ fun x hx ↦ (hVN hx).2
  have hsum : r₁ + r₂ = d := eq_of_isFiniteLocallyFreeOfRank _
    (isFiniteLocallyFreeOfRank_of_charts hV' DV.ideal h₁ h₂) DV.isFiniteLocallyFreeOfRank
    ⟨t₀, htV⟩
  let a : Fin (d + 1) := ⟨r₁, by omega⟩
  rw [show r₂ = d - a by simp only [a]; omega] at h₂
  obtain ⟨c₁, hc₁, -⟩ := existsUnique_eq_monicFamily V'
    (⟨_, h₁⟩ : HilbertFamily (line S) V' (a : ℕ))
  obtain ⟨c₂, hc₂, -⟩ := existsUnique_eq_monicFamily V'
    (⟨_, h₂⟩ : HilbertFamily (line S) V' (d - a))
  refine ⟨V', i, hi, ⟨t₀, htV⟩, rfl, homSome hfac hV' a c₁ c₂ ≫ ιH W z d (some a), ?_⟩
  rw [baseChange_comp_ιH]
  have e₁ : (fun j ↦ (homSome hfac hV' a c₁ c₂).left.appTop (coords₁ W z d a j)) = c₁ :=
    funext fun j ↦ homSome_coord hfac hV' a c₁ c₂ (Sum.inl j)
  have e₂ : (fun j ↦ (homSome hfac hV' a c₁ c₂).left.appTop (coords₂ W z d a j)) = c₂ :=
    funext fun j ↦ homSome_coord hfac hV' a c₁ c₂ (Sum.inr j)
  refine family_ext_of_charts W fun b ↦ ?_
  cases b
  · rw [familyComponent, (comap_chartT_baseChange_some W z hzW _).2, e₂]
    exact congrArg HilbertFamily.ideal hc₂
  · rw [familyComponent, (comap_chartT_baseChange_some W z hzW _).1, e₁]
    exact congrArg HilbertFamily.ideal hc₁

/-- **The Hilbert scheme of points of the doubled line.** For `d ≥ 1`, the degree-`d` Hilbert
functor of the doubled line is represented by `hilb W z d`. -/
def representsHilbertFunctorOfRank (d : ℕ) (hd : 0 < d) :
    RepresentsHilbertFunctorOfRank (doubledLine W) (hilb W z d) d :=
  RepresentsHilbertFunctorOfRank.ofUniversal (doubledLine W) (universalFamily W z hzW d)
    (bijective_baseChange_of_local (doubledLine W) (universalFamily W z hzW d)
      (fun _ ↦ hom_locally_eq W z hzW)
      (fun T D t ↦ by
        by_cases ht : T.hom t ∈ W
        · exact exists_classifying_of_mem W z hzW D t ht
        · exact exists_classifying_of_not_mem W z hfac hzW D
            ⟨(T.hom ⁻¹' (W : Set S))ᶜ, (isClosed_preimage_of_family hd D).isOpen_compl⟩
            (fun v hv ↦ hv) t ht))

omit hfac [Mono z] [IsAffine Z] in
/-- **The Hilbert schemes of the doubled line are not smooth** when `W` is dense and `Z` is
nonempty: the pieces over `Z` are open, but their images lie in the complement of `W`, which has
empty interior, while a smooth morphism is open. -/
theorem not_smooth_hilb [Nonempty Z]
    (hdense : ∀ (U : S.Opens) (x : S), x ∈ U → ∃ y ∈ U, y ∈ W) (d : ℕ) :
    ¬ Smooth (hilb W z d).hom := by
  intro hsm
  let τ : Option (Fin (d + 1)) := some 0
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  obtain ⟨x, -⟩ := (𝔸(ULift.{u} (Fin (0 : Fin (d + 1)) ⊕ Fin (d - 0)); Z) ↘ Z).surjective z₀
  let U : (hilb W z d).left.Opens := (ιH W z d τ).left.opensRange
  let V : S.Opens := ⟨(hilb W z d).hom '' U, (hilb W z d).hom.isOpenMap _ U.2⟩
  obtain ⟨y, ⟨_, ⟨x', rfl⟩, rfl⟩, hyW⟩ :=
    hdense V _ ⟨(ιH W z d τ).left x, ⟨x, rfl⟩, rfl⟩
  rw [hom_left_apply] at hyW
  exact component_some_hom_not_mem W z hzW d 0 x' hyW

end Stacks.Hilbert.DoubledLine

end
