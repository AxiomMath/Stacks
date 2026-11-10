module

public import StacksFrontier.AlgebraicGeometry.Smooth.CechCocycle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The infinitesimal lifting criterion for smoothness

A morphism of schemes is smooth if and only if it is locally of finite presentation and formally
smooth. This is [Stacks Project, Tag 02H6], and this file completes its proof: the hard
direction `Stacks.Smooth.smooth_of_formallySmoothScheme` is proved elsewhere, and the remaining
implication — a smooth morphism, with no affineness hypothesis, is formally smooth — is step (II)
of the Stacks proof, carried out here.

## Main results

* `Stacks.Smooth.formallySmoothScheme_of_smooth`: a smooth morphism of schemes is formally
  smooth.
* `Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth`: **Tag 02H6.**

## Implementation notes

Fix a first-order thickening `i : T ⟶ T'` of affine schemes and a lifting problem presented by
`a : T ⟶ X` and `h : T' ⟶ S`. Step (I),
`Stacks.Smooth.exists_fin_basicOpen_chart_lift`, produces a standard covering `T' = ⋃ D(g j)` and
over each member a solution `b j` of the restricted problem mapping into an affine chart `W j` of
`f` lying over an affine open `V j` of `S`. The solutions need not agree on the overlaps, and the
whole of step (II) is the statement that they can be corrected so that they do.

The differences are organized by the Čech complex of the family `g` with coefficients in the
single `Γ(T, ⊤)`-module `N = Γ(a^*Ω_{X/S}, ⊤) →ₗ[Γ(T, ⊤)] 𝒞_{T/T'}`. Over the member attached to
a tuple `x` the difference of two of the solutions is a `Γ(T, i ⁻¹ᵁ D(x))`-linear map out of
`Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(x))`, by
`Stacks.Smooth.existsUnique_linearMap_liftDiffDerivation`, and
`Stacks.Smooth.exists_cechHom` identifies the module of those maps with the Čech term of `N` at
that tuple, compatibly with the Čech restriction maps
(`Stacks.Smooth.cechHom_resAway`). The resulting 1-cochain is a cocycle: at a triple overlap the
three differences being compared live over three different members and in the charts of two
different indices, and `Stacks.Smooth.liftDiffDerivation_spec_restrict_chart` brings all three
into the chart of the first index over the triple overlap, where
`Stacks.Smooth.liftDiffDerivation_add` applies. Then
`Stacks.RingTheory.CechAcyclicity.cech_exact` at `p = 0` writes the cocycle as a coboundary,
`Stacks.Smooth.derivationOfLinearMapOpensTop` turns each component of the 0-cochain back into a
derivation in the chart of its member, `Stacks.Smooth.exists_lift_of_derivation` corrects the
local solutions by those derivations,
`Stacks.Smooth.eq_of_liftDiffDerivation_eq_zero` shows that the corrected solutions agree on the
overlaps and `Stacks.Smooth.exists_lift_of_isOpenCover` glues them.

Two indexing points. The member of the covering attached to a tuple is cut out by
`Stacks.Smooth.cechSection`, which carries the factor `1` that the untwisted Čech complex
localizes at; so the member attached to a one-element tuple is `D(g j)` only up to the equality
`Stacks.Smooth.basicOpen_cechSection_single`, and the solutions are restricted to it rather than
used directly. And the local solutions are indexed by an element of `Fin n` rather than by a
position in the tuple, `Stacks.Smooth.cechLiftAt`, because the position occurs in the type of the
solution and so could not be rewritten along the face maps.

## References

* [Stacks Project, Tag 01EO](https://stacks.math.columbia.edu/tag/01EO)
* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.RingTheory.CechAcyclicity

universe u

namespace Stacks.Smooth

/-! ### The local solutions, restricted to the members of the Čech covering -/

section Assembly

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) [IsAffine T'] {i : T ⟶ T'}
  (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S}
  {n : ℕ} (g : Fin n → Γ(T', (⊤ : T'.Opens))) {V : Fin n → S.Opens} {W : Fin n → X.Opens}
  (b : ∀ j, ((T'.basicOpen (g j) : T'.Opens) : Scheme.{u}) ⟶ X)
  (hbf : ∀ j, b j ≫ f = (T'.basicOpen (g j)).ι ≫ h)
  (hba : ∀ j, (i ∣_ T'.basicOpen (g j)) ≫ b j = (i ⁻¹ᵁ T'.basicOpen (g j)).ι ≫ a)
  (hbW : ∀ j, (⊤ : ((T'.basicOpen (g j) : T'.Opens) : Scheme.{u}).Opens) ≤ (b j) ⁻¹ᵁ W j)

/-- **The local solution of index `j`, restricted to the member of the Čech covering attached to
a tuple.** The index `j` is an explicit argument rather than a position in the tuple because it
occurs in the type of the solution, so a statement indexed by a position could not be rewritten
along the face maps of the Čech complex. -/
noncomputable def cechLiftAt {m : ℕ} (x : Fin (m + 1) → Fin n) (j : Fin n)
    (hj : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j)) :
    ((T'.basicOpen (cechSection g x) : T'.Opens) : Scheme.{u}) ⟶ X :=
  T'.homOfLE hj ≫ b j

omit [IsAffine T'] in
/-- The restrictions of one local solution to two nested members of the Čech covering are
compatible. -/
theorem homOfLE_comp_cechLiftAt {m m' : ℕ} (x : Fin (m + 1) → Fin n) (y : Fin (m' + 1) → Fin n)
    (hxy : T'.basicOpen (cechSection g y) ≤ T'.basicOpen (cechSection g x)) (j : Fin n)
    (hjx : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j))
    (hjy : T'.basicOpen (cechSection g y) ≤ T'.basicOpen (g j)) :
    T'.homOfLE hxy ≫ cechLiftAt g b x j hjx = cechLiftAt g b y j hjy := by
  rw [cechLiftAt, cechLiftAt, ← Category.assoc, Scheme.homOfLE_homOfLE]

omit [IsAffine T'] in
/-- A restricted local solution still lies over `h`. -/
theorem cechLiftAt_comp (hbf : ∀ j, b j ≫ f = (T'.basicOpen (g j)).ι ≫ h) {m : ℕ}
    (x : Fin (m + 1) → Fin n) (j : Fin n)
    (hj : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j)) :
    cechLiftAt g b x j hj ≫ f = (T'.basicOpen (cechSection g x)).ι ≫ h := by
  rw [cechLiftAt, Category.assoc, hbf, ← Category.assoc, Scheme.homOfLE_ι]

omit [IsAffine T'] in
/-- A restricted local solution still solves the restricted lifting problem. -/
theorem morphismRestrict_comp_cechLiftAt
    (hba : ∀ j, (i ∣_ T'.basicOpen (g j)) ≫ b j = (i ⁻¹ᵁ T'.basicOpen (g j)).ι ≫ a) {m : ℕ}
    (x : Fin (m + 1) → Fin n) (j : Fin n)
    (hj : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j)) :
    (i ∣_ T'.basicOpen (cechSection g x)) ≫ cechLiftAt g b x j hj
      = (i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a := by
  rw [cechLiftAt, ← Category.assoc, morphismRestrict_comp_homOfLE, Category.assoc, hba,
    ← Category.assoc, Scheme.homOfLE_ι]

omit [IsAffine T'] in
/-- A restricted local solution maps into its own chart. -/
theorem top_le_preimage_cechLiftAt_self
    (hbW : ∀ j, (⊤ : ((T'.basicOpen (g j) : T'.Opens) : Scheme.{u}).Opens) ≤ (b j) ⁻¹ᵁ W j)
    {m : ℕ} (x : Fin (m + 1) → Fin n) (j : Fin n)
    (hj : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j)) :
    (⊤ : ((T'.basicOpen (cechSection g x) : T'.Opens) : Scheme.{u}).Opens) ≤
      (cechLiftAt g b x j hj) ⁻¹ᵁ W j := by
  intro y _
  change (b j).base ((T'.homOfLE hj).base y) ∈ W j
  exact hbW j (Set.mem_univ _)

omit [IsAffine T'] in
include hi in
/-- **A restricted local solution maps into the chart of every index of the covering.** All the
restricted solutions over one member of the covering solve the same restricted lifting problem,
so by the rigidity `Stacks.Smooth.le_preimage_of_lift` of the underlying map of a solution they
all map wherever any one of them maps. -/
theorem top_le_preimage_cechLiftAt
    (hba : ∀ j, (i ∣_ T'.basicOpen (g j)) ≫ b j = (i ⁻¹ᵁ T'.basicOpen (g j)).ι ≫ a)
    (hbW : ∀ j, (⊤ : ((T'.basicOpen (g j) : T'.Opens) : Scheme.{u}).Opens) ≤ (b j) ⁻¹ᵁ W j)
    {m : ℕ} (x : Fin (m + 1) → Fin n) (j : Fin n)
    (hj : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j)) (j' : Fin n)
    (hj' : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j')) :
    (⊤ : ((T'.basicOpen (cechSection g x) : T'.Opens) : Scheme.{u}).Opens) ≤
      (cechLiftAt g b x j hj) ⁻¹ᵁ W j' :=
  le_preimage_of_lift
    (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen (cechSection g x))).isThickening.2
    (morphismRestrict_comp_cechLiftAt g b hba x j' hj')
    (morphismRestrict_comp_cechLiftAt g b hba x j hj)
    (top_le_preimage_cechLiftAt_self g b hbW x j' hj')

omit [IsAffine T'] in
include hi in
/-- The closed subscheme cut out by a member of the Čech covering maps into the chart of every
index of the covering. -/
theorem top_le_preimage_comp_cechSection
    (hba : ∀ j, (i ∣_ T'.basicOpen (g j)) ≫ b j = (i ⁻¹ᵁ T'.basicOpen (g j)).ι ≫ a)
    (hbW : ∀ j, (⊤ : ((T'.basicOpen (g j) : T'.Opens) : Scheme.{u}).Opens) ≤ (b j) ⁻¹ᵁ W j)
    {m : ℕ} (x : Fin (m + 1) → Fin n) (j : Fin n)
    (hj : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j)) (j' : Fin n)
    (hj' : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j')) :
    (⊤ : ((i ⁻¹ᵁ T'.basicOpen (cechSection g x) : T.Opens) : Scheme.{u}).Opens) ≤
      ((i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a) ⁻¹ᵁ W j' := by
  intro y _
  rw [← morphismRestrict_comp_cechLiftAt g b hba x j hj]
  exact top_le_preimage_cechLiftAt hi g b hba hbW x j hj j' hj' (Set.mem_univ _)

omit [IsAffine T'] in
include hi in
/-- A member of the Čech covering is carried by `a` into the chart of every index. -/
theorem le_preimage_cechSection
    (hba : ∀ j, (i ∣_ T'.basicOpen (g j)) ≫ b j = (i ⁻¹ᵁ T'.basicOpen (g j)).ι ≫ a)
    (hbW : ∀ j, (⊤ : ((T'.basicOpen (g j) : T'.Opens) : Scheme.{u}).Opens) ≤ (b j) ⁻¹ᵁ W j)
    {m : ℕ} (x : Fin (m + 1) → Fin n) (j : Fin n)
    (hj : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j)) (j' : Fin n)
    (hj' : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j')) :
    i ⁻¹ᵁ T'.basicOpen (cechSection g x) ≤ a ⁻¹ᵁ W j' := fun y hy ↦
  top_le_preimage_comp_cechSection hi g b hba hbW x j hj j' hj'
    (Set.mem_univ (⟨y, hy⟩ : ((i ⁻¹ᵁ T'.basicOpen (cechSection g x) : T.Opens) : Scheme.{u})))

omit [IsAffine T'] in
include hi in
/-- A member of the Čech covering lies over the affine open of `S` attached to every index. -/
theorem top_le_preimage_base_cechSection
    (hbf : ∀ j, b j ≫ f = (T'.basicOpen (g j)).ι ≫ h)
    (hba : ∀ j, (i ∣_ T'.basicOpen (g j)) ≫ b j = (i ⁻¹ᵁ T'.basicOpen (g j)).ι ≫ a)
    (hbW : ∀ j, (⊤ : ((T'.basicOpen (g j) : T'.Opens) : Scheme.{u}).Opens) ≤ (b j) ⁻¹ᵁ W j)
    (hWV : ∀ j, W j ≤ f ⁻¹ᵁ V j) {m : ℕ} (x : Fin (m + 1) → Fin n) (j : Fin n)
    (hj : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j)) (j' : Fin n)
    (hj' : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j')) :
    (⊤ : ((T'.basicOpen (cechSection g x) : T'.Opens) : Scheme.{u}).Opens) ≤
      ((T'.basicOpen (cechSection g x)).ι ≫ h) ⁻¹ᵁ V j' :=
  top_le_preimage_of_comp f (cechLiftAt_comp f g b hbf x j hj) (hWV j')
    (top_le_preimage_cechLiftAt hi g b hba hbW x j hj j' hj')

omit [IsAffine T'] in
/-- The restricted lifting problem over a member of the Čech covering commutes. -/
theorem comm_cechSection (hbf : ∀ j, b j ≫ f = (T'.basicOpen (g j)).ι ≫ h)
    (hba : ∀ j, (i ∣_ T'.basicOpen (g j)) ≫ b j = (i ⁻¹ᵁ T'.basicOpen (g j)).ι ≫ a) {m : ℕ}
    (x : Fin (m + 1) → Fin n) (j : Fin n)
    (hj : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j)) :
    ((i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a) ≫ f
      = (i ∣_ T'.basicOpen (cechSection g x)) ≫
        ((T'.basicOpen (cechSection g x)).ι ≫ h) := by
  rw [← cechLiftAt_comp f g b hbf x j hj, ← Category.assoc,
    morphismRestrict_comp_cechLiftAt g b hba x j hj]

end Assembly

/-! ### The infinitesimal lifting criterion -/

/-- **A smooth morphism of schemes is formally smooth.** This is step (II) of the proof of
[Stacks Project, Tag 02H6], and with
`Stacks.Smooth.smooth_of_formallySmoothScheme` it completes that tag.

Step (I), `Stacks.Smooth.exists_fin_basicOpen_chart_lift`, solves the lifting problem over the
members of a standard covering of the affine thickening, inside an affine chart of `f` for each
member. The differences of those solutions are read, by
`Stacks.Smooth.exists_linearMap_liftDiffDerivation_basicOpen`, as a 1-cochain of the Čech complex
of the covering with coefficients in the module of `Γ(T, ⊤)`-linear maps
`Γ(a^*Ω_{X/S}, ⊤) ⟶ 𝒞_{T/T'}`, the identification of the Čech terms being
`Stacks.Smooth.exists_cechHom` and of the Čech restriction maps
`Stacks.Smooth.cechHom_resAway`. It is a cocycle because, after
`Stacks.Smooth.liftDiffDerivation_spec_restrict_chart` has brought the three differences at a
triple overlap into one chart over that overlap,
`Stacks.Smooth.liftDiffDerivation_add` applies; so
`Stacks.RingTheory.CechAcyclicity.cech_exact` writes it as a coboundary.
`Stacks.Smooth.derivationOfLinearMapOpensTop` turns the components of the resulting 0-cochain
into derivations in the charts of their members and
`Stacks.Smooth.exists_lift_of_derivation` corrects the local solutions by them; the corrected
solutions agree on the overlaps, by `Stacks.Smooth.eq_of_liftDiffDerivation_eq_zero`, and
`Stacks.Smooth.exists_lift_of_isOpenCover` glues them. -/
@[ega "IV 17.14.1" "partial", sga "3 III 0.16" "more general", sga "3 III 0.17" "more general"]
theorem formallySmoothScheme_of_smooth {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] : FormallySmoothScheme f := by
  intro T T' hT hT' i hi a h hcomm
  have hci : IsClosedImmersion i := hi.1
  let := thickeningKerModule hi
  obtain ⟨n, g, hspan, hdata⟩ := exists_fin_basicOpen_chart_lift f hi a h hcomm
  choose V W hV hW hWV b hbf hba hbW using hdata
  have hGspan : Ideal.span (Set.range fun j ↦ i.appTop.hom (g j)) = ⊤ := by
    refine (Ideal.eq_top_iff_one _).mpr ?_
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
      (hspan.ge (Submodule.mem_top : (1 : Γ(T', (⊤ : T'.Opens))) ∈ ⊤))
    refine (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨fun j ↦ i.appTop.hom (c j), ?_⟩
    simp only [smul_eq_mul] at hc ⊢
    rw [← map_one i.appTop.hom, ← hc, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ (map_mul i.appTop.hom (c j) (g j)).symm
  -- the derived data of the restricted lifting problem over each member of the covering
  have hUWa : ∀ (m : ℕ) (x : Fin (m + 1) → Fin n) (j' : Fin n)
      (_ : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j')),
      i ⁻¹ᵁ T'.basicOpen (cechSection g x) ≤ a ⁻¹ᵁ W j' := fun m x j' hj' ↦
    le_preimage_cechSection hi g b hba hbW x (x 0) (basicOpen_cechSection_le g x 0) j' hj'
  have hUWt : ∀ (m : ℕ) (x : Fin (m + 1) → Fin n) (j' : Fin n)
      (_ : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j')),
      (⊤ : ((i ⁻¹ᵁ T'.basicOpen (cechSection g x) : T.Opens) : Scheme.{u}).Opens) ≤
        ((i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a) ⁻¹ᵁ W j' := fun m x j' hj' ↦
    top_le_preimage_comp_cechSection hi g b hba hbW x (x 0)
      (basicOpen_cechSection_le g x 0) j' hj'
  have hVb : ∀ (m : ℕ) (x : Fin (m + 1) → Fin n) (j' : Fin n)
      (_ : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j')),
      (⊤ : ((T'.basicOpen (cechSection g x) : T'.Opens) : Scheme.{u}).Opens) ≤
        ((T'.basicOpen (cechSection g x)).ι ≫ h) ⁻¹ᵁ V j' := fun m x j' hj' ↦
    top_le_preimage_base_cechSection f hi g b hbf hba hbW hWV x (x 0)
      (basicOpen_cechSection_le g x 0) j' hj'
  have hcm : ∀ (m : ℕ) (x : Fin (m + 1) → Fin n),
      ((i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a) ≫ f
        = (i ∣_ T'.basicOpen (cechSection g x)) ≫
          ((T'.basicOpen (cechSection g x)).ι ≫ h) := fun m x ↦
    comm_cechSection f g b hbf hba x (x 0) (basicOpen_cechSection_le g x 0)
  have hBf : ∀ (m : ℕ) (x : Fin (m + 1) → Fin n) (k : Fin n)
      (hk : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g k)),
      cechLiftAt g b x k hk ≫ f = (T'.basicOpen (cechSection g x)).ι ≫ h := fun m x k hk ↦
    cechLiftAt_comp f g b hbf x k hk
  have hBa : ∀ (m : ℕ) (x : Fin (m + 1) → Fin n) (k : Fin n)
      (hk : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g k)),
      (i ∣_ T'.basicOpen (cechSection g x)) ≫ cechLiftAt g b x k hk
        = (i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a := fun m x k hk ↦
    morphismRestrict_comp_cechLiftAt g b hba x k hk
  have hBW : ∀ (m : ℕ) (x : Fin (m + 1) → Fin n) (k : Fin n)
      (hk : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g k)) (j' : Fin n)
      (_ : T'.basicOpen (cechSection g x) ≤ T'.basicOpen (g j')),
      (⊤ : ((T'.basicOpen (cechSection g x) : T'.Opens) : Scheme.{u}).Opens) ≤
        (cechLiftAt g b x k hk) ⁻¹ᵁ W j' := fun m x k hk j' hj' ↦
    top_le_preimage_cechLiftAt hi g b hba hbW x k hk j' hj'
  -- the chart-local differences over the overlaps
  choose θ hθ using fun x : Fin 2 → Fin n ↦
    exists_linearMap_liftDiffDerivation_basicOpen f hi (cechSection g x) (hV (x 0)) (hW (x 0))
      (hWV (x 0)) (hUWa 1 x (x 0) (basicOpen_cechSection_le g x 0))
      (hUWt 1 x (x 0) (basicOpen_cechSection_le g x 0))
      (hVb 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hcm 1 x)
      (hBf 1 x (x 0) (basicOpen_cechSection_le g x 0))
      (hBf 1 x (x 1) (basicOpen_cechSection_le g x 1))
      (hBa 1 x (x 0) (basicOpen_cechSection_le g x 0))
      (hBa 1 x (x 1) (basicOpen_cechSection_le g x 1))
      (hBW 1 x (x 0) (basicOpen_cechSection_le g x 0) (x 0) (basicOpen_cechSection_le g x 0))
      (hBW 1 x (x 1) (basicOpen_cechSection_le g x 1) (x 0) (basicOpen_cechSection_le g x 0))
  choose Φ hΦ using fun (c : Γ(T', (⊤ : T'.Opens))) (bb : Γ(T, (⊤ : T.Opens)))
    (hbb : i.appTop.hom c = bb) ↦ exists_cechHom f a hi c bb hbb
  have hcocycle : cechD _ (fun j ↦ i.appTop.hom (g j)) 1 1
      (fun x ↦ (Φ (cechSection g x) _ (appTop_cechSection i g x)).symm (θ x)) = 0 := by
    refine funext fun y ↦ ?_
    have hOA : IsAffine ((T'.basicOpen (cechSection g y) : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen (cechSection g y)
    let := algebraAppLE f (hWV (y 0))
    let := thickeningKerModule
      (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen (cechSection g y)))
    let := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen (cechSection g y)).ι ≫ a)
      (hUWt 2 y (y 0) (basicOpen_cechSection_le g y 0))
      (RingHom.ker (i ∣_ T'.basicOpen (cechSection g y)).appTop.hom)
    let := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen (cechSection g y)).ι ≫ a) (hWV (y 0))
      (hUWt 2 y (y 0) (basicOpen_cechSection_le g y 0))
      (RingHom.ker (i ∣_ T'.basicOpen (cechSection g y)).appTop.hom)
    let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen (cechSection g y)).ι ≫ a) (hWV (y 0))
      (hUWt 2 y (y 0) (basicOpen_cechSection_le g y 0))
      (RingHom.ker (i ∣_ T'.basicOpen (cechSection g y)).appTop.hom)
    let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen (cechSection g y))
      (RingHom.ker (i ∣_ T'.basicOpen (cechSection g y)).appTop.hom)
    have hres := fun (k : Fin 3) w ↦ (cechHom_resAway f a hi (cechSection g
      (fun l ↦ y (k.succAbove l)))
        (cechSection g y) (basicOpen_cechSection_le_face g y k) _ _
        (appTop_cechSection i g (fun l ↦ y (k.succAbove l))) (appTop_cechSection i g y)
        (dvd_face (fun j ↦ i.appTop.hom (g j)) 1 y k)
        (Φ (cechSection g (fun l ↦ y (k.succAbove l))) _ (appTop_cechSection i g
          (fun l ↦ y (k.succAbove l))))
        (hΦ (cechSection g (fun l ↦ y (k.succAbove l))) _ (appTop_cechSection i g
          (fun l ↦ y (k.succAbove l))))
        (Φ (cechSection g y) _ (appTop_cechSection i g y))
        (hΦ (cechSection g y) _ (appTop_cechSection i g y))
        ((Φ (cechSection g (fun l ↦ y (k.succAbove l))) _ (appTop_cechSection i g
          (fun l ↦ y (k.succAbove l)))).symm
          (θ (fun l ↦ y (k.succAbove l)))) w).trans
      (congrArg (conormalResLE hi (basicOpen_cechSection_le_face g y k))
        (congrArg (fun φ ↦ φ w) ((Φ (cechSection g (fun l ↦ y (k.succAbove l))) _
          (appTop_cechSection i g (fun l ↦ y (k.succAbove l)))).apply_symm_apply (θ
            (fun l ↦ y (k.succAbove l))))))
    have hspec := fun k : Fin 3 ↦ liftDiffDerivation_spec_restrict_chart f hi (cechSection g
      (fun l ↦ y (k.succAbove l)))
      (cechSection g y) (basicOpen_cechSection_le_face g y k) (hV (y (k.succAbove 0)))
      (hW (y (k.succAbove 0))) (hWV (y (k.succAbove 0))) (hWV (y 0))
      (hUWa 1 (fun l ↦ y (k.succAbove l)) (y (k.succAbove 0))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 0))
      (hUWt 1 (fun l ↦ y (k.succAbove l)) (y (k.succAbove 0))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 0))
      (hVb 1 (fun l ↦ y (k.succAbove l)) (y (k.succAbove 0))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 0))
      (hcm 1 (fun l ↦ y (k.succAbove l)))
      (hBf 1 (fun l ↦ y (k.succAbove l)) (y (k.succAbove 0))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 0))
      (hBf 1 (fun l ↦ y (k.succAbove l)) (y (k.succAbove 1))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 1))
      (hBa 1 (fun l ↦ y (k.succAbove l)) (y (k.succAbove 0))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 0))
      (hBa 1 (fun l ↦ y (k.succAbove l)) (y (k.succAbove 1))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 1))
      (hBW 1 (fun l ↦ y (k.succAbove l)) (y (k.succAbove 0))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 0) (y (k.succAbove 0))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 0))
      (hBW 1 (fun l ↦ y (k.succAbove l)) (y (k.succAbove 1))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 1) (y (k.succAbove 0))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 0))
      (homOfLE_comp_cechLiftAt g b (fun l ↦ y (k.succAbove l)) y
        (basicOpen_cechSection_le_face g y k) (y (k.succAbove 0))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 0)
        (basicOpen_cechSection_le g y (k.succAbove 0)))
      (homOfLE_comp_cechLiftAt g b (fun l ↦ y (k.succAbove l)) y
        (basicOpen_cechSection_le_face g y k) (y (k.succAbove 1))
        (basicOpen_cechSection_le g (fun l ↦ y (k.succAbove l)) 1)
        (basicOpen_cechSection_le g y (k.succAbove 1)))
      (hUWa 2 y (y 0) (basicOpen_cechSection_le g y 0))
      (hUWt 2 y (y 0) (basicOpen_cechSection_le g y 0))
      (hVb 2 y (y 0) (basicOpen_cechSection_le g y 0)) (hcm 2 y)
      (hBf 2 y (y (k.succAbove 0)) (basicOpen_cechSection_le g y (k.succAbove 0)))
      (hBf 2 y (y (k.succAbove 1)) (basicOpen_cechSection_le g y (k.succAbove 1)))
      (hBa 2 y (y (k.succAbove 0)) (basicOpen_cechSection_le g y (k.succAbove 0)))
      (hBa 2 y (y (k.succAbove 1)) (basicOpen_cechSection_le g y (k.succAbove 1)))
      (hBW 2 y (y (k.succAbove 0)) (basicOpen_cechSection_le g y (k.succAbove 0)) (y 0)
        (basicOpen_cechSection_le g y 0))
      (hBW 2 y (y (k.succAbove 1)) (basicOpen_cechSection_le g y (k.succAbove 1)) (y 0)
        (basicOpen_cechSection_le g y 0))
      (θ (fun l ↦ y (k.succAbove l))) (hθ (fun l ↦ y (k.succAbove l)))
      ((Φ (cechSection g y) _ (appTop_cechSection i g y))
        (resAway _ (dvd_face (fun j ↦ i.appTop.hom (g j)) 1 y k)
          ((Φ (cechSection g (fun l ↦ y (k.succAbove l))) _ (appTop_cechSection i g
            (fun l ↦ y (k.succAbove l)))).symm (θ
            (fun l ↦ y (k.succAbove l))))))
      (hres k)
    refine (cechD_apply (fun j ↦ i.appTop.hom (g j)) 1 1 _ y).trans ?_
    refine (Φ (cechSection g y) _ (appTop_cechSection i g y)).injective ?_
    refine (map_sum _ _ _).trans (Eq.trans ?_ (map_zero _).symm)
    refine hom_ext_pullbackD f a
      (isAffine_preimage_of_isAffine hi (T'.basicOpen (cechSection g y))) (hV (y 0)) (hW (y 0))
      (hWV (y 0)) (hUWa 2 y (y 0) (basicOpen_cechSection_le g y 0)) _ fun bb ↦ ?_
    refine ((LinearMap.sum_apply _ _ _).trans (Fin.sum_univ_three _)).trans
      (Eq.trans ?_ (LinearMap.zero_apply _).symm)
    have hd := fun (k : Fin 3) ↦ liftDiffDerivation_apply f
      (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen (cechSection g y))) (hWV (y 0))
      (hUWt 2 y (y 0) (basicOpen_cechSection_le g y 0))
      (hVb 2 y (y 0) (basicOpen_cechSection_le g y 0)) (hcm 2 y)
      (hBf 2 y (y (k.succAbove 0)) (basicOpen_cechSection_le g y (k.succAbove 0)))
      (hBf 2 y (y (k.succAbove 1)) (basicOpen_cechSection_le g y (k.succAbove 1)))
      (hBa 2 y (y (k.succAbove 0)) (basicOpen_cechSection_le g y (k.succAbove 0)))
      (hBa 2 y (y (k.succAbove 1)) (basicOpen_cechSection_le g y (k.succAbove 1)))
      (hBW 2 y (y (k.succAbove 0)) (basicOpen_cechSection_le g y (k.succAbove 0)) (y 0)
        (basicOpen_cechSection_le g y 0))
      (hBW 2 y (y (k.succAbove 1)) (basicOpen_cechSection_le g y (k.succAbove 1)) (y 0)
        (basicOpen_cechSection_le g y 0)) bb
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_one_smul,
      neg_one_sq, map_neg, LinearMap.neg_apply, hspec _ bb]
    refine Subtype.ext ?_
    simp only [ZeroMemClass.coe_zero, AddMemClass.coe_add, NegMemClass.coe_neg, hd]
    simp only [Fin.succAbove_zero_apply, Fin.one_succAbove_zero, Fin.one_succAbove_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, show (Fin.succAbove 2 0 : Fin 3) = 0 from rfl,
      show (Fin.succAbove 2 1 : Fin 3) = 1 from rfl]
    ring
  obtain ⟨u, hu⟩ := cech_exact (fun j ↦ i.appTop.hom (g j)) hGspan 1 0 _ hcocycle
  choose b' hb'W hb'f hb'a hb'd using fun c : Fin 1 → Fin n ↦
    let : IsAffine ((T'.basicOpen (cechSection g c) : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen (cechSection g c)
    let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi
      (T'.basicOpen (cechSection g c)))
    exists_lift_of_derivation f
      (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen (cechSection g c)))
      (hWV (c 0)) (hUWt 0 c (c 0) (basicOpen_cechSection_le g c 0))
      (hVb 0 c (c 0) (basicOpen_cechSection_le g c 0)) (hV (c 0)) (hW (c 0)) (hcm 0 c)
      (derivationOfLinearMapOpensTop f a (hWV (c 0))
        (hUWa 0 c (c 0) (basicOpen_cechSection_le g c 0))
        (hUWt 0 c (c 0) (basicOpen_cechSection_le g c 0))
        (RingHom.ker (i ∣_ T'.basicOpen (cechSection g c)).appTop.hom)
        ((Φ (cechSection g c) _ (appTop_cechSection i g c)) (u c)))
      (hBf 0 c (c 0) (basicOpen_cechSection_le g c 0))
      (hBa 0 c (c 0) (basicOpen_cechSection_le g c 0))
      (hBW 0 c (c 0) (basicOpen_cechSection_le g c 0) (c 0) (basicOpen_cechSection_le g c 0))
  have hagree : ∀ (x : Fin 2 → Fin n) (c c' : Fin 1 → Fin n),
      c = (fun m ↦ x ((1 : Fin 2).succAbove m)) → c' = (fun m ↦ x ((0 : Fin 2).succAbove m)) →
      ∀ (O : T'.Opens) (h₁ : O ≤ T'.basicOpen (cechSection g c))
        (h₂ : O ≤ T'.basicOpen (cechSection g c')),
      O = T'.basicOpen (cechSection g x) →
      T'.homOfLE h₁ ≫ b' c = T'.homOfLE h₂ ≫ b' c' := by
    rintro x c c' rfl rfl O h₁ h₂ rfl
    have hOA : IsAffine ((T'.basicOpen (cechSection g x) : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen (cechSection g x)
    have hOAj : IsAffine ((T'.basicOpen (cechSection g (fun m ↦ x ((1 : Fin 2).succAbove m))) :
      T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen (cechSection g (fun m ↦ x ((1 : Fin 2).succAbove m)))
    have hOAk : IsAffine ((T'.basicOpen (cechSection g (fun m ↦ x ((0 : Fin 2).succAbove m))) :
      T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen (cechSection g (fun m ↦ x ((0 : Fin 2).succAbove m)))
    let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi
      (T'.basicOpen (cechSection g (fun m ↦ x ((1 : Fin 2).succAbove m)))))
    let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi
      (T'.basicOpen (cechSection g (fun m ↦ x ((0 : Fin 2).succAbove m)))))
    let := algebraAppLE f (hWV (x 0))
    let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi
      (T'.basicOpen (cechSection g x)))
    let := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a)
      (hUWt 1 x (x 0) (basicOpen_cechSection_le g x 0))
        (RingHom.ker (i ∣_ T'.basicOpen (cechSection g x)).appTop.hom)
    let := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a) (hWV (x 0))
      (hUWt 1 x (x 0) (basicOpen_cechSection_le g x 0))
        (RingHom.ker (i ∣_ T'.basicOpen (cechSection g x)).appTop.hom)
    let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a)
      (hWV (x 0)) (hUWt 1 x (x 0) (basicOpen_cechSection_le g x 0))
        (RingHom.ker (i ∣_ T'.basicOpen (cechSection g x)).appTop.hom)
    let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen (cechSection g x))
      (RingHom.ker (i ∣_ T'.basicOpen (cechSection g x)).appTop.hom)
    have hp : (T'.homOfLE h₁ ≫ b' (fun m ↦ x ((1 : Fin 2).succAbove m))) ≫ f =
      (T'.basicOpen (cechSection g x)).ι ≫ h := by
      rw [Category.assoc, hb'f (fun m ↦ x ((1 : Fin 2).succAbove m)), ← Category.assoc,
        Scheme.homOfLE_ι]
    have ht : (T'.homOfLE h₂ ≫ b' (fun m ↦ x ((0 : Fin 2).succAbove m))) ≫ f =
      (T'.basicOpen (cechSection g x)).ι ≫ h := by
      rw [Category.assoc, hb'f (fun m ↦ x ((0 : Fin 2).succAbove m)), ← Category.assoc,
        Scheme.homOfLE_ι]
    have hpa : (i ∣_ T'.basicOpen (cechSection g x)) ≫ (T'.homOfLE h₁ ≫ b'
      (fun m ↦ x ((1 : Fin 2).succAbove m)))
        = (i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a := by
      rw [← Category.assoc, morphismRestrict_comp_homOfLE, Category.assoc, hb'a
        (fun m ↦ x ((1 : Fin 2).succAbove m)),
        ← Category.assoc, Scheme.homOfLE_ι]
    have hta : (i ∣_ T'.basicOpen (cechSection g x)) ≫ (T'.homOfLE h₂ ≫ b'
      (fun m ↦ x ((0 : Fin 2).succAbove m)))
        = (i ⁻¹ᵁ T'.basicOpen (cechSection g x)).ι ≫ a := by
      rw [← Category.assoc, morphismRestrict_comp_homOfLE, Category.assoc, hb'a
        (fun m ↦ x ((0 : Fin 2).succAbove m)),
        ← Category.assoc, Scheme.homOfLE_ι]
    have hpW : (⊤ : ((T'.basicOpen (cechSection g x) : T'.Opens) : Scheme.{u}).Opens) ≤
        (T'.homOfLE h₁ ≫ b' (fun m ↦ x ((1 : Fin 2).succAbove m))) ⁻¹ᵁ W (x 0) := fun _ _ ↦ hb'W
          (fun m ↦ x ((1 : Fin 2).succAbove m)) (Set.mem_univ _)
    have htW : (⊤ : ((T'.basicOpen (cechSection g x) : T'.Opens) : Scheme.{u}).Opens) ≤
        (T'.homOfLE h₂ ≫ b' (fun m ↦ x ((0 : Fin 2).succAbove m))) ⁻¹ᵁ W (x 0) :=
          le_preimage_of_lift (isFirstOrderThickening_morphismRestrict hi
          (T'.basicOpen (cechSection g x))).isThickening.2 hpa hta hpW
    have hspecj := liftDiffDerivation_spec_restrict_chart f hi (cechSection g
      (fun m ↦ x ((1 : Fin 2).succAbove m)))
      (cechSection g x) h₁ (hV ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)) (hW
        ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)) (hWV ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0))
        (hWV (x 0))
      (hUWa 0 (fun m ↦ x ((1 : Fin 2).succAbove m)) ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((1 : Fin 2).succAbove m)) 0)) (hUWt 0
        (fun m ↦ x ((1 : Fin 2).succAbove m)) ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((1 : Fin 2).succAbove m)) 0)) (hVb 0
        (fun m ↦ x ((1 : Fin 2).succAbove m)) ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((1 : Fin 2).succAbove m)) 0))
      (hcm 0 (fun m ↦ x ((1 : Fin 2).succAbove m))) (hb'f (fun m ↦ x ((1 : Fin 2).succAbove m)))
        (hBf 0 (fun m ↦ x ((1 : Fin 2).succAbove m)) ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((1 : Fin 2).succAbove m)) 0)) (hb'a
        (fun m ↦ x ((1 : Fin 2).succAbove m)))
      (hBa 0 (fun m ↦ x ((1 : Fin 2).succAbove m)) ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((1 : Fin 2).succAbove m)) 0)) (hb'W
        (fun m ↦ x ((1 : Fin 2).succAbove m))) (hBW 0 (fun m ↦ x ((1 : Fin 2).succAbove m))
        ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0) (basicOpen_cechSection_le g
        (fun m ↦ x ((1 : Fin 2).succAbove m)) 0) ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((1 : Fin 2).succAbove m)) 0)) rfl
      (homOfLE_comp_cechLiftAt g b (fun m ↦ x ((1 : Fin 2).succAbove m)) x h₁ (x 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((1 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g x 0))
      (hUWa 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hUWt 1 x (x 0) (basicOpen_cechSection_le g
        x 0)) (hVb 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hcm 1 x)
      hp (hBf 1 x (x 0) (basicOpen_cechSection_le g x 0)) hpa (hBa 1 x (x 0)
        (basicOpen_cechSection_le g x 0)) hpW (hBW 1 x (x 0) (basicOpen_cechSection_le g x 0) (x 0)
        (basicOpen_cechSection_le g x 0))
      ((Φ (cechSection g (fun m ↦ x ((1 : Fin 2).succAbove m))) _ (appTop_cechSection i g
        (fun m ↦ x ((1 : Fin 2).succAbove m)))) (u (fun m ↦ x ((1 : Fin 2).succAbove m))))
      (fun bb ↦ (derivationOfLinearMapOpensTop_apply f a (hWV ((fun m ↦ x ((1 : Fin 2).succAbove m))
        0))
        (hUWa 0 (fun m ↦ x ((1 : Fin 2).succAbove m)) ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)
          (basicOpen_cechSection_le g (fun m ↦ x ((1 : Fin 2).succAbove m)) 0)) (hUWt 0
          (fun m ↦ x ((1 : Fin 2).succAbove m)) ((fun m ↦ x ((1 : Fin 2).succAbove m)) 0)
          (basicOpen_cechSection_le g (fun m ↦ x ((1 : Fin 2).succAbove m)) 0))
        (RingHom.ker (i ∣_ T'.basicOpen (cechSection g
          (fun m ↦ x ((1 : Fin 2).succAbove m)))).appTop.hom)
        ((Φ (cechSection g (fun m ↦ x ((1 : Fin 2).succAbove m))) _ (appTop_cechSection i g
          (fun m ↦ x ((1 : Fin 2).succAbove m)))) (u (fun m ↦ x ((1 : Fin 2).succAbove m))))
          bb).symm.trans (congrArg (fun d ↦ d bb) (hb'd
          (fun m ↦ x ((1 : Fin 2).succAbove m))).symm))
      ((Φ (cechSection g x) _ (appTop_cechSection i g x)) (resAway _ (dvd_face (fun j₀ ↦
        i.appTop.hom (g j₀)) 1 x 1) (u (fun m ↦ x ((1 : Fin 2).succAbove m)))))
      (fun w ↦ cechHom_resAway f a hi (cechSection g (fun m ↦ x ((1 : Fin 2).succAbove m)))
        (cechSection g x) h₁ _ _
        (appTop_cechSection i g (fun m ↦ x ((1 : Fin 2).succAbove m))) (appTop_cechSection i g x)
          (dvd_face (fun j₀ ↦ i.appTop.hom (g j₀)) 1 x 1)
        (Φ (cechSection g (fun m ↦ x ((1 : Fin 2).succAbove m))) _ (appTop_cechSection i g
          (fun m ↦ x ((1 : Fin 2).succAbove m)))) (hΦ (cechSection g
          (fun m ↦ x ((1 : Fin 2).succAbove m))) _ (appTop_cechSection i g
          (fun m ↦ x ((1 : Fin 2).succAbove m))))
        (Φ (cechSection g x) _ (appTop_cechSection i g x)) (hΦ (cechSection g x) _
          (appTop_cechSection i g x)) (u (fun m ↦ x ((1 : Fin 2).succAbove m))) w)
    have hspeck := liftDiffDerivation_spec_restrict_chart f hi (cechSection g
      (fun m ↦ x ((0 : Fin 2).succAbove m)))
      (cechSection g x) h₂ (hV ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)) (hW
        ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)) (hWV ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0))
        (hWV (x 0))
      (hUWa 0 (fun m ↦ x ((0 : Fin 2).succAbove m)) ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((0 : Fin 2).succAbove m)) 0)) (hUWt 0
        (fun m ↦ x ((0 : Fin 2).succAbove m)) ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((0 : Fin 2).succAbove m)) 0)) (hVb 0
        (fun m ↦ x ((0 : Fin 2).succAbove m)) ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((0 : Fin 2).succAbove m)) 0))
      (hcm 0 (fun m ↦ x ((0 : Fin 2).succAbove m))) (hb'f (fun m ↦ x ((0 : Fin 2).succAbove m)))
        (hBf 0 (fun m ↦ x ((0 : Fin 2).succAbove m)) ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((0 : Fin 2).succAbove m)) 0)) (hb'a
        (fun m ↦ x ((0 : Fin 2).succAbove m)))
      (hBa 0 (fun m ↦ x ((0 : Fin 2).succAbove m)) ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((0 : Fin 2).succAbove m)) 0)) (hb'W
        (fun m ↦ x ((0 : Fin 2).succAbove m))) (hBW 0 (fun m ↦ x ((0 : Fin 2).succAbove m))
        ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0) (basicOpen_cechSection_le g
        (fun m ↦ x ((0 : Fin 2).succAbove m)) 0) ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g (fun m ↦ x ((0 : Fin 2).succAbove m)) 0)) rfl
      (homOfLE_comp_cechLiftAt g b (fun m ↦ x ((0 : Fin 2).succAbove m)) x h₂ (x 1)
        (basicOpen_cechSection_le g (fun m ↦ x ((0 : Fin 2).succAbove m)) 0)
        (basicOpen_cechSection_le g x 1))
      (hUWa 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hUWt 1 x (x 0) (basicOpen_cechSection_le g
        x 0)) (hVb 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hcm 1 x)
      ht (hBf 1 x (x 1) (basicOpen_cechSection_le g x 1)) hta (hBa 1 x (x 1)
        (basicOpen_cechSection_le g x 1)) htW (hBW 1 x (x 1) (basicOpen_cechSection_le g x 1) (x 0)
        (basicOpen_cechSection_le g x 0))
      ((Φ (cechSection g (fun m ↦ x ((0 : Fin 2).succAbove m))) _ (appTop_cechSection i g
        (fun m ↦ x ((0 : Fin 2).succAbove m)))) (u (fun m ↦ x ((0 : Fin 2).succAbove m))))
      (fun bb ↦ (derivationOfLinearMapOpensTop_apply f a (hWV ((fun m ↦ x ((0 : Fin 2).succAbove m))
        0))
        (hUWa 0 (fun m ↦ x ((0 : Fin 2).succAbove m)) ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)
          (basicOpen_cechSection_le g (fun m ↦ x ((0 : Fin 2).succAbove m)) 0)) (hUWt 0
          (fun m ↦ x ((0 : Fin 2).succAbove m)) ((fun m ↦ x ((0 : Fin 2).succAbove m)) 0)
          (basicOpen_cechSection_le g (fun m ↦ x ((0 : Fin 2).succAbove m)) 0))
        (RingHom.ker (i ∣_ T'.basicOpen (cechSection g
          (fun m ↦ x ((0 : Fin 2).succAbove m)))).appTop.hom)
        ((Φ (cechSection g (fun m ↦ x ((0 : Fin 2).succAbove m))) _ (appTop_cechSection i g
          (fun m ↦ x ((0 : Fin 2).succAbove m)))) (u (fun m ↦ x ((0 : Fin 2).succAbove m))))
          bb).symm.trans (congrArg (fun d ↦ d bb) (hb'd
          (fun m ↦ x ((0 : Fin 2).succAbove m))).symm))
      ((Φ (cechSection g x) _ (appTop_cechSection i g x)) (resAway _ (dvd_face (fun j₀ ↦
        i.appTop.hom (g j₀)) 1 x 0) (u (fun m ↦ x ((0 : Fin 2).succAbove m)))))
      (fun w ↦ cechHom_resAway f a hi (cechSection g (fun m ↦ x ((0 : Fin 2).succAbove m)))
        (cechSection g x) h₂ _ _
        (appTop_cechSection i g (fun m ↦ x ((0 : Fin 2).succAbove m))) (appTop_cechSection i g x)
          (dvd_face (fun j₀ ↦ i.appTop.hom (g j₀)) 1 x 0)
        (Φ (cechSection g (fun m ↦ x ((0 : Fin 2).succAbove m))) _ (appTop_cechSection i g
          (fun m ↦ x ((0 : Fin 2).succAbove m)))) (hΦ (cechSection g
          (fun m ↦ x ((0 : Fin 2).succAbove m))) _ (appTop_cechSection i g
          (fun m ↦ x ((0 : Fin 2).succAbove m))))
        (Φ (cechSection g x) _ (appTop_cechSection i g x)) (hΦ (cechSection g x) _
          (appTop_cechSection i g x)) (u (fun m ↦ x ((0 : Fin 2).succAbove m))) w)
    have e7 : θ x = ((Φ (cechSection g x) _ (appTop_cechSection i g x)) (resAway _ (dvd_face (fun j₀
      ↦ i.appTop.hom (g j₀)) 1 x 0) (u (fun m ↦ x ((0 : Fin 2).succAbove m))))) - ((Φ (cechSection g
      x) _ (appTop_cechSection i g x)) (resAway _ (dvd_face (fun j₀ ↦ i.appTop.hom (g j₀)) 1 x 1) (u
      (fun m ↦ x ((1 : Fin 2).succAbove m))))) :=
      ((Φ (cechSection g x) _ (appTop_cechSection i g x)).apply_symm_apply (θ x)).symm.trans
        ((congrArg (fun z ↦ (Φ (cechSection g x) _ (appTop_cechSection i g x)) z) (congrFun hu
          x).symm).trans
          ((congrArg (fun z ↦ (Φ (cechSection g x) _ (appTop_cechSection i g x)) z)
              (cechD_apply (fun j ↦ i.appTop.hom (g j)) 1 0 u x)).trans
            ((map_sum (Φ (cechSection g x) _ (appTop_cechSection i g x)) _ Finset.univ).trans
              ((Fin.sum_univ_two _).trans (by
                simp only [Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
                  neg_one_smul, map_neg, sub_eq_add_neg])))))
    refine eq_of_liftDiffDerivation_eq_zero f (isFirstOrderThickening_morphismRestrict hi
      (T'.basicOpen (cechSection g x))) (hWV (x 0)) (hUWt 1 x (x 0) (basicOpen_cechSection_le g x
      0))
      (hVb 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hW (x 0)) (hcm 1 x) hp ht hpa hta hpW htW ?_
    refine Derivation.ext fun bb ↦ ?_
    have e1 := liftDiffDerivation_add_apply f (isFirstOrderThickening_morphismRestrict hi
      (T'.basicOpen (cechSection g x))) (hWV (x 0)) (hUWt 1 x (x 0) (basicOpen_cechSection_le g x
      0))
      (hVb 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hcm 1 x) hp (hBf 1 x (x 0)
        (basicOpen_cechSection_le g x 0)) ht hpa (hBa 1 x (x 0) (basicOpen_cechSection_le g x 0))
        hta
      hpW (hBW 1 x (x 0) (basicOpen_cechSection_le g x 0) (x 0) (basicOpen_cechSection_le g x 0))
        htW bb
    have e2 := liftDiffDerivation_add_apply f (isFirstOrderThickening_morphismRestrict hi
      (T'.basicOpen (cechSection g x))) (hWV (x 0)) (hUWt 1 x (x 0) (basicOpen_cechSection_le g x
      0))
      (hVb 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hcm 1 x) (hBf 1 x (x 0)
        (basicOpen_cechSection_le g x 0)) (hBf 1 x (x 1) (basicOpen_cechSection_le g x 1)) ht
      (hBa 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hBa 1 x (x 1) (basicOpen_cechSection_le g x
        1)) hta (hBW 1 x (x 0) (basicOpen_cechSection_le g x 0) (x 0) (basicOpen_cechSection_le g x
        0))
      (hBW 1 x (x 1) (basicOpen_cechSection_le g x 1) (x 0) (basicOpen_cechSection_le g x 0)) htW bb
    have e3 := liftDiffDerivation_neg_apply f (isFirstOrderThickening_morphismRestrict hi
      (T'.basicOpen (cechSection g x))) (hWV (x 0)) (hUWt 1 x (x 0) (basicOpen_cechSection_le g x
      0))
      (hVb 1 x (x 0) (basicOpen_cechSection_le g x 0)) (hcm 1 x) ht (hBf 1 x (x 1)
        (basicOpen_cechSection_le g x 1)) hta (hBa 1 x (x 1) (basicOpen_cechSection_le g x 1)) htW
      (hBW 1 x (x 1) (basicOpen_cechSection_le g x 1) (x 0) (basicOpen_cechSection_le g x 0)) bb
    have e4 := hspecj bb
    have e5 := hθ x bb
    have e6 := hspeck bb
    simp only [Derivation.zero_apply, e1, e2, e3, ← e4, ← e5, ← e6, e7, LinearMap.sub_apply]
    abel
  refine exists_lift_of_isOpenCover f i a h (fun c : Fin 1 → Fin n ↦ T'.basicOpen (cechSection g c))
    ?_ b' hb'f hb'a ?_
  · refine top_le_iff.mp fun z _ ↦ ?_
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (((iSup_basicOpen_eq_top_iff_span_range_eq_top g).mpr hspan).ge
        (TopologicalSpace.Opens.mem_top z))
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨fun _ ↦ j, (basicOpen_cechSection_single g (fun _ ↦ j)).ge hj⟩
  · intro c c'
    refine hagree (fun l : Fin 2 ↦ if l = 0 then c 0 else c' 0) c c'
      (funext fun m ↦ by rw [Subsingleton.elim m 0]; rfl) (funext fun m ↦ by
        rw [Subsingleton.elim m 0]; rfl) _ inf_le_left inf_le_right ?_
    rw [basicOpen_cechSection_single, basicOpen_cechSection_single,
      basicOpen_cechSection_double]
    rfl

/-- **A scheme morphism is smooth exactly when it is locally of finite presentation and formally
smooth.** This is the infinitesimal lifting criterion for smoothness.

The implication from the right is `Stacks.Smooth.smooth_of_formallySmoothScheme`, and
the implication to the right is `Stacks.Smooth.formallySmoothScheme_of_smooth` together with the
fact that a smooth morphism is locally of finite presentation. -/
@[stacks 02H6,
  ega "IV 17.3.2" "(ii) smooth",
  ega "0 19.0.1",
  ega "IV 17.3.1",
  sga "3 XI 1.1",
  sga "3 XV 1.1" "more general"]
theorem smooth_iff_locallyOfFinitePresentation_and_formallySmooth {X S : Scheme.{u}}
    (f : X ⟶ S) :
    AlgebraicGeometry.Smooth f ↔
      (AlgebraicGeometry.LocallyOfFinitePresentation f ∧ FormallySmoothScheme f) := by
  refine ⟨fun hf ↦ ⟨inferInstance, formallySmoothScheme_of_smooth f⟩, fun hf ↦ ?_⟩
  have := hf.1
  exact smooth_of_formallySmoothScheme f hf.2

end Stacks.Smooth

end
