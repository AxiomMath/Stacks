module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus.ChartRing
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSectionsBaseChange
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# The locus of the base over which an open of the source contains the whole fibre

For a closed morphism `p : X ⟶ Y` and an open `U` of `X`, the points of `Y` all of whose preimages
lie in `U` form an open `fibreInsideOpen p U`, the complement of `p (X ∖ U)`. For a cartesian
square with top `h : X_T ⟶ X` over `l : T ⟶ Y`, `h` lands in `U` exactly when `l` lands in
`fibreInsideOpen p U`.

Composed with an immersion `j : Y ⟶ W` this gives a scheme `chartOver p U j` over `W`, through
which a morphism factors exactly when it factors through `j` by a morphism landing in that open.

## Main definitions

* `AlgebraicGeometry.DescentLocus.fibreInsideOpen`: the open of `Y` over which `U` contains the
  fibre.
* `AlgebraicGeometry.DescentLocus.chartOver`: that open as a scheme over `W`.

## Main results

* `AlgebraicGeometry.DescentLocus.range_subset_iff_of_isPullback`: base change of the condition.
* `AlgebraicGeometry.DescentLocus.exists_lift_chartOver_iff`: factorization through `chartOver`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentLocus

variable {X Y : Scheme.{u}} (p : X ⟶ Y) [UniversallyClosed p] (U : X.Opens)

/-- The open of `Y` consisting of the points all of whose preimages under the closed morphism `p`
lie in `U`. -/
def fibreInsideOpen : Y.Opens :=
  ⟨(p '' (U : Set X)ᶜ)ᶜ, (p.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_fibreInsideOpen_iff {y : Y} :
    y ∈ fibreInsideOpen p U ↔ ∀ x : X, p x = y → x ∈ U := by
  change y ∉ p '' (U : Set X)ᶜ ↔ _
  simp only [Set.mem_image, Set.mem_compl_iff, SetLike.mem_coe, not_exists, not_and]
  exact ⟨fun h x hx ↦ by_contra fun hx' ↦ h x hx' hx, fun h x hx' hx ↦ hx' (h x hx)⟩

/-- **The condition is compatible with base change.** For a cartesian square with top
`h : P ⟶ X` over `l : T ⟶ Y`, `h` lands in `U` exactly when `l` lands in `fibreInsideOpen p U`. -/
theorem range_subset_iff_of_isPullback {T P : Scheme.{u}} {h : P ⟶ X} {q : P ⟶ T} {l : T ⟶ Y}
    (H : IsPullback h q p l) :
    Set.range h ⊆ U ↔ Set.range l ⊆ fibreInsideOpen p U := by
  constructor
  · rintro hU _ ⟨t, rfl⟩
    refine (mem_fibreInsideOpen_iff p U).2 fun x hx ↦ ?_
    obtain ⟨z, rfl, -⟩ := IsPullback.exists_preimage H x t hx
    exact hU ⟨z, rfl⟩
  · rintro hl _ ⟨z, rfl⟩
    refine (mem_fibreInsideOpen_iff p U).1 (hl ⟨q z, rfl⟩) _ ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, H.w]

variable {W : Scheme.{u}} (j : Y ⟶ W)

/-- The open `fibreInsideOpen p U` as a scheme over `W`, through `j`. -/
def chartOver : Over W := Over.mk ((fibreInsideOpen p U).ι ≫ j)

instance isImmersion_chartOver_hom [IsImmersion j] : IsImmersion (chartOver p U j).hom := by
  dsimp only [chartOver, Over.mk_hom]
  infer_instance

theorem finitePresentation_chartOver_hom [TopologicalSpace.NoetherianSpace Y]
    (hj : FinitePresentation j) :
    FinitePresentation (chartOver p U j).hom := by
  have : LocallyOfFinitePresentation j := hj.1
  have : QuasiCompact j := hj.2.1
  have : QuasiSeparated j := hj.2.2
  have : TopologicalSpace.NoetherianSpace (fibreInsideOpen p U : Scheme.{u}) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (fibreInsideOpen p U : Set Y))
  have : QuasiCompact (fibreInsideOpen p U).ι := quasiCompact_of_noetherianSpace_source _
  dsimp only [chartOver, Over.mk_hom]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Factoring through `chartOver`.** A morphism `t : T ⟶ W` factors through `chartOver p U j`
exactly when it factors through the monomorphism `j` by a morphism landing in
`fibreInsideOpen p U`. -/
theorem exists_lift_chartOver_iff [Mono j] {T : Scheme.{u}} (t : T ⟶ W) :
    (∃ m : T ⟶ (chartOver p U j).left, m ≫ (chartOver p U j).hom = t) ↔
      ∃ l : T ⟶ Y, l ≫ j = t ∧ Set.range l ⊆ fibreInsideOpen p U := by
  constructor
  · rintro ⟨m, hm⟩
    let m' : T ⟶ (fibreInsideOpen p U : Scheme.{u}) := m
    refine ⟨m' ≫ (fibreInsideOpen p U).ι, by rw [Category.assoc]; exact hm, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (m' x).2
  · rintro ⟨l, hl, hrange⟩
    have : IsOpenImmersion (fibreInsideOpen p U).ι := inferInstance
    have hr : Set.range l ⊆ Set.range (fibreInsideOpen p U).ι := by
      rw [Scheme.Opens.range_ι]; exact hrange
    refine ⟨@IsOpenImmersion.lift _ _ _ (fibreInsideOpen p U).ι l this hr, ?_⟩
    change @IsOpenImmersion.lift _ _ _ (fibreInsideOpen p U).ι l this hr ≫
      (fibreInsideOpen p U).ι ≫ j = t
    rw [← Category.assoc, @IsOpenImmersion.lift_fac _ _ _ (fibreInsideOpen p U).ι l this hr, hl]

end AlgebraicGeometry.DescentLocus
