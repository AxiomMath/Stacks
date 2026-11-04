module

public import StacksFrontier.AlgebraicGeometry.Smooth.ConormalLocalization
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Charted local lifts, and the torsor identities of the correction step

This file carries out the part of step (II) of the proof of the infinitesimal lifting criterion
[Stacks Project, Tag 02H6] that does not need the Čech argument: the bookkeeping that makes the
local solutions of step (I) and their differences into a candidate Čech cocycle.

Two things are supplied.

The first is a **chart-exporting** refinement of `Stacks.Smooth.exists_isAffineOpen_lift`. That
lemma produces, around every point of the thickening `T'`, an affine open `V'` and a solution of
the restricted lifting problem over it, but discards the pair of affine charts `V ⊆ S`, `W ⊆ X`
that its proof chose, and with them the information that the solution produced maps `V'` into `W`.
Both are needed downstream, because `Stacks.Smooth.liftDiffDerivation` — the difference of two
solutions — is a derivation of `Γ(X, W)` over `Γ(S, V)` and can only be formed once a chart is
fixed. `Stacks.Smooth.exists_isAffineOpen_chart_lift` returns all of it.

The second is the **torsor arithmetic** of the differences. The differences of local solutions
satisfy the cocycle identity, `Stacks.Smooth.liftDiffDerivation_add`, and the action of the
derivations on the solutions is free, `Stacks.Smooth.eq_of_liftDiffDerivation_eq_zero`. These are
the two identities the correction step consumes: the first is what says the local differences are
a Čech 1-cocycle, and the second is what will say that correcting the local solutions by a
0-cochain whose coboundary is that cocycle makes them agree, so that
`Stacks.Smooth.exists_lift_of_isOpenCover` applies.

The Čech argument itself is **not** carried out here, and the unrestricted equivalence of
[Stacks Project, Tag 02H6] is still not proved; see the implementation notes for what is left.

## Main results

* `Stacks.Smooth.le_preimage_of_base_surjective`: along a morphism which is surjective on points,
  a solution of a lifting problem maps into any open that the problem itself maps into. This is the
  reason the chart condition in `Stacks.Smooth.exists_isAffineOpen_chart_lift` comes for free.
* `Stacks.Smooth.top_le_preimage_of_comp`: a morphism over `S` whose source maps into a chart `W`
  of `X` maps into any open of `S` containing the image of `W`.
* `Stacks.Smooth.exists_isAffineOpen_chart_lift`: the chart-exporting form of step (I).
* `Stacks.Smooth.exists_fin_basicOpen_chart_lift`: the same over a standard covering of `T'`
  indexed by `Fin n`, which is the shape `Stacks.RingTheory.CechAcyclicity.cech_exact` consumes.
* `Stacks.Smooth.liftDiffDerivation_add`: the cocycle identity for the differences of three
  solutions of one lifting problem in one chart.
* `Stacks.Smooth.eq_of_liftDiffDerivation_eq_zero`: two solutions in one chart whose difference
  vanishes are equal.

## Implementation notes

`Stacks.Smooth.exists_isAffineOpen_chart_lift` repeats the construction of
`Stacks.Smooth.exists_isAffineOpen_lift` rather than deriving its conclusion from it, because the
charts `V` and `W` are chosen inside that proof and are not recoverable from its statement. The
one new ingredient is the final conclusion `⊤ ≤ b ⁻¹ᵁ W`, and it is not proved by inspecting the
construction of `b`: a thickening is surjective on points, so the underlying map of *any* solution
of the restricted lifting problem is determined by the problem, and the problem maps into `W` by
construction. That is `Stacks.Smooth.le_preimage_of_base_surjective`, the absolute form of the
relative `Stacks.Smooth.le_preimage_of_lift`.

The two torsor identities are formal consequences of `Stacks.Smooth.liftDiffDerivation_apply`,
which computes the difference on sections; the only care needed is that all the module structures
in play — `Stacks.Smooth.thickeningKerModule` on the conormal module and the two restrictions of
scalars `Stacks.Smooth.moduleOfAppLE` and `Stacks.Smooth.moduleOfAppLEBase` — are the ones fixed by
`StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor`, so that the derivations being compared live in
the same type. Freeness is stated as equality of the two morphisms rather than of their sections,
which needs `Stacks.Smooth.hom_ext_of_appLE`.

What is still missing for the implication `Smooth f → FormallySmoothScheme f`, and hence for the
unrestricted Tag 02H6, is the Čech step proper. Its two coefficient inputs are now both available
with no hypothesis on the lifting problem:
`Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'` localizes
`Γ(a^*Ω_{X/S}, ⊤)` and `Stacks.Smooth.isLocalizedModule_conormalRestrict` localizes the conormal
module, while `Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_of_isAffine` makes
`Module.FinitePresentation.isLocalizedModule_map` apply, so that the module of
`Γ(T, ⊤)`-linear maps `Γ(a^*Ω_{X/S}, ⊤) ⟶ 𝒞_{T/T'}` localizes as well. What remains is the
identification of the chart-local differences with the sections of that `Hom` module over the
members of the covering: concretely, the comparison of
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module` applied over
`T'.basicOpen (g j) ⊓ T'.basicOpen (g k)` with
`Stacks.RingTheory.CechAcyclicity.resAway`, which has to pass through the identification of
`Γ(a^*Ω_{X/S}, U)` with `Γ((U.ι ≫ a)^*Ω_{X/S}, ⊤)` of
`Stacks.Smooth.restrictPullbackCotangentSheafIso` and the ring isomorphism comparing the
`Γ(T, U)`- and `Γ(U, ⊤)`-module structures, exactly as in
`Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_isAffineOpen`. Once the differences are a
`Stacks.RingTheory.CechAcyclicity.CechTerm` 1-cocycle — the cocycle identity being
`Stacks.Smooth.liftDiffDerivation_add`, formed in a single chart on each triple overlap by
`Stacks.Smooth.le_preimage_of_lift` — `Stacks.RingTheory.CechAcyclicity.cech_exact` at `p = 0`
produces the 0-cochain, `Stacks.Smooth.exists_lift_of_derivation` corrects the local solutions by
it, `Stacks.Smooth.eq_of_liftDiffDerivation_eq_zero` shows the corrected solutions agree and
`Stacks.Smooth.exists_lift_of_isOpenCover` glues them.

## References

* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-! ### Charted local lifts -/

/-- **A solution of a lifting problem maps where the problem maps.** If `i` is surjective on
points and `i ≫ b = a` with `a` mapping into the open `W`, then `b` maps into `W`. This is the
absolute form of `Stacks.Smooth.le_preimage_of_lift`: there the open is transported between two
solutions of one problem, here from the problem to a solution. -/
theorem le_preimage_of_base_surjective {X Y Y' : Scheme.{u}} {i : Y ⟶ Y'} {a : Y ⟶ X}
    {b : Y' ⟶ X} (hi : Function.Surjective i.base) (hba : i ≫ b = a) {W : X.Opens}
    (ha : (⊤ : Y.Opens) ≤ a ⁻¹ᵁ W) : (⊤ : Y'.Opens) ≤ b ⁻¹ᵁ W := by
  intro y _
  obtain ⟨y₀, rfl⟩ := hi y
  show b.base (i.base y₀) ∈ W
  rw [← Scheme.Hom.comp_apply, hba]
  exact ha (Set.mem_univ y₀)

/-- **A morphism over `S` lands in a chart of `S` as soon as it factors through a chart of `X`.**
If `b ≫ f = c` and `b` maps into `W` with `W ≤ f ⁻¹ᵁ V`, then `c` maps into `V`. -/
theorem top_le_preimage_of_comp {X S Y : Scheme.{u}} (f : X ⟶ S) {b : Y ⟶ X} {c : Y ⟶ S}
    (hbf : b ≫ f = c) {V : S.Opens} {W : X.Opens} (hWV : W ≤ f ⁻¹ᵁ V)
    (hb : (⊤ : Y.Opens) ≤ b ⁻¹ᵁ W) : (⊤ : Y.Opens) ≤ c ⁻¹ᵁ V := by
  subst hbf
  exact fun y _ ↦ hWV (hb (Set.mem_univ y))

/-- **Lifts along a thickening exist locally, in an explicit pair of charts.** Let `f : X ⟶ S` be
smooth, let `i : T ⟶ T'` be a first-order thickening and let `a : T ⟶ X`, `h : T' ⟶ S` present a
lifting problem for `f`. Then every point `t` of `T'` has an affine open neighbourhood `V'`,
together with affine opens `V` of `S` and `W` of `X` with `W ≤ f ⁻¹ᵁ V`, over which the restricted
lifting problem has a solution `b` **mapping `V'` into `W`**.

This is `Stacks.Smooth.exists_isAffineOpen_lift` with the pair of charts chosen in its proof, and
the chart condition on the solution, retained in the statement. Those are what
`Stacks.Smooth.liftDiffDerivation` needs in order to compare two such solutions on an overlap. -/
theorem exists_isAffineOpen_chart_lift {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i)
    (a : T ⟶ X) (h : T' ⟶ S) (hcomm : a ≫ f = i ≫ h) (t : T') :
    ∃ (V' : T'.Opens) (V : S.Opens) (W : X.Opens),
      IsAffineOpen V' ∧ t ∈ V' ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ W ≤ f ⁻¹ᵁ V ∧
        ∃ b : (V' : Scheme.{u}) ⟶ X, b ≫ f = V'.ι ≫ h ∧
          (i ∣_ V') ≫ b = (i ⁻¹ᵁ V').ι ≫ a ∧
          (⊤ : (V' : Scheme.{u}).Opens) ≤ b ⁻¹ᵁ W := by
  have hci : IsClosedImmersion i := hi.1
  obtain ⟨t₀, rfl⟩ := hi.isThickening.2 t
  obtain ⟨V, hV, hsV⟩ : ∃ V : S.Opens, IsAffineOpen V ∧ f.base (a.base t₀) ∈ V := by
    obtain ⟨V, hV, hsV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (f.base (a.base t₀)))
    exact ⟨V, hV, hsV⟩
  obtain ⟨W, hW, hxW, hWV⟩ : ∃ W : X.Opens, IsAffineOpen W ∧ a.base t₀ ∈ W ∧ W ≤ f ⁻¹ᵁ V :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) (x := a.base t₀) hsV
  have homeo : IsHomeomorph i.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨i.isClosedEmbedding.isEmbedding, hi.isThickening.2⟩
  obtain ⟨V', hV', htV', hV'le⟩ : ∃ V' : T'.Opens, IsAffineOpen V' ∧ i.base t₀ ∈ V' ∧
      V' ≤ (⟨i.base '' (a ⁻¹ᵁ W : Set T), homeo.isOpenMap _ (a ⁻¹ᵁ W).isOpen⟩ : T'.Opens) :=
    exists_isAffineOpen_mem_and_subset (x := i.base t₀) ⟨t₀, hxW, rfl⟩
  have hpre : i ⁻¹ᵁ V' ≤ a ⁻¹ᵁ W := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hV'le hx
    exact homeo.injective hxy ▸ hy
  have hV'a : IsAffine (V' : Scheme.{u}) := hV'
  have hi' := isFirstOrderThickening_morphismRestrict hi V'
  have hran : Set.range ((i ⁻¹ᵁ V').ι ≫ a).base ⊆ (W : Set X) := by
    rintro y ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hpre x.2
  obtain ⟨b, hb₁, hb₂⟩ := exists_lift_of_range_subset f hi' ((i ⁻¹ᵁ V').ι ≫ a) (V'.ι ≫ h)
    (by rw [Category.assoc, hcomm, ← Category.assoc, ← morphismRestrict_ι, Category.assoc])
    hV hW hWV hran
  exact ⟨V', V, W, hV', htV', hV, hW, hWV, b, hb₁, hb₂,
    le_preimage_of_base_surjective hi'.isThickening.2 hb₂ fun x _ ↦ hran ⟨x, rfl⟩⟩

/-- **The charted local lifts may be taken over a standard covering indexed by `Fin n`.** Let
`f : X ⟶ S` be smooth, let `i : T ⟶ T'` be a first-order thickening with `T'` affine and let
`a : T ⟶ X`, `h : T' ⟶ S` present a lifting problem. Then there are finitely many global sections
`g : Fin n → Γ(T', ⊤)` generating the unit ideal such that over each `T'.basicOpen (g j)` the
restricted lifting problem has a solution mapping into an affine chart `W` of `X` lying over an
affine open `V` of `S`.

This is `Stacks.Smooth.exists_isAffineOpen_chart_lift` shrunk to basic opens by
`Stacks.Smooth.exists_finset_basicOpen_le` and reindexed by `Fin n`, which is the form the Čech
complex of `Stacks.RingTheory.CechAcyclicity.cech_exact` consumes. It is the chart-exporting
refinement of `Stacks.Smooth.exists_finset_basicOpen_lift`. -/
theorem exists_fin_basicOpen_chart_lift {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] [IsAffine T'] {i : T ⟶ T'}
    (hi : Thickenings.IsFirstOrderThickening i) (a : T ⟶ X) (h : T' ⟶ S)
    (hcomm : a ≫ f = i ≫ h) :
    ∃ (n : ℕ) (g : Fin n → Γ(T', ⊤)), Ideal.span (Set.range g) = ⊤ ∧
      ∀ j : Fin n, ∃ (V : S.Opens) (W : X.Opens),
        IsAffineOpen V ∧ IsAffineOpen W ∧ W ≤ f ⁻¹ᵁ V ∧
          ∃ b : (T'.basicOpen (g j) : Scheme.{u}) ⟶ X,
            b ≫ f = (T'.basicOpen (g j)).ι ≫ h ∧
            (i ∣_ T'.basicOpen (g j)) ≫ b = (i ⁻¹ᵁ T'.basicOpen (g j)).ι ≫ a ∧
            (⊤ : (T'.basicOpen (g j) : Scheme.{u}).Opens) ≤ b ⁻¹ᵁ W := by
  choose V' V W hV' htV' hV hW hWV b hbf hba hbW using
    exists_isAffineOpen_chart_lift f hi a h hcomm
  obtain ⟨g, s, hgle, hspan⟩ := exists_finset_basicOpen_le V' htV'
  refine ⟨s.card, fun j ↦ g (s.equivFin.symm j : ↥T'), ?_, fun j ↦ ?_⟩
  · rw [show (Set.range fun j ↦ g (s.equivFin.symm j : ↥T')) = Set.range fun t : s ↦ g t from
      s.equivFin.symm.surjective.range_comp fun t : s ↦ g t]
    exact hspan
  · set t : ↥T' := (s.equivFin.symm j : ↥T') with ht
    refine ⟨V t, W t, hV t, hW t, hWV t, T'.homOfLE (hgle t) ≫ b t, ?_, ?_, ?_⟩
    · rw [Category.assoc, hbf t, ← Category.assoc, Scheme.homOfLE_ι]
    · rw [← Category.assoc, morphismRestrict_comp_homOfLE, Category.assoc, hba t,
        ← Category.assoc, Scheme.homOfLE_ι]
    · exact fun x _ ↦ hbW t (Set.mem_univ _)

/-! ### The torsor identities for the differences of local solutions -/

section Torsor

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {W : X.Opens} [IsAffine T']
  {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S}
  (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (hV' : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ V)
  {b₁ b₂ b₃ : T' ⟶ X}

/-- **The cocycle identity for the differences of solutions of a lifting problem.** For three
solutions of one lifting problem, all mapping into the affine chart `W`, the difference of the
first and the third is the sum of the difference of the first and the second and the difference of
the second and the third.

This is what makes the family of pairwise differences of the local solutions of step (I) of
[Stacks Project, Tag 02H6] a Čech 1-cocycle. -/
theorem liftDiffDerivation_add (hcomm : a ≫ f = i ≫ h) (hb₁f : b₁ ≫ f = h) (hb₂f : b₂ ≫ f = h)
    (hb₃f : b₃ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a) (hb₃a : i ≫ b₃ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W)
    (hb₃ : (⊤ : T'.Opens) ≤ b₃ ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule hi
    letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    liftDiffDerivation f hi hWV hUW hV' hcomm hb₁f hb₃f hb₁a hb₃a hb₁ hb₃ =
      liftDiffDerivation f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ +
        liftDiffDerivation f hi hWV hUW hV' hcomm hb₂f hb₃f hb₂a hb₃a hb₂ hb₃ := by
  let := algebraAppLE f hWV
  let := thickeningKerModule hi
  let := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  let := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  let := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  refine Derivation.ext fun x ↦ Subtype.ext ?_
  rw [Derivation.add_apply, Submodule.coe_add, liftDiffDerivation_apply, liftDiffDerivation_apply,
    liftDiffDerivation_apply]
  ring

/-- **The action of the derivations on the solutions of a lifting problem is free.** Two solutions
of one lifting problem, both mapping into the affine chart `W`, whose difference derivation
vanishes are equal.

Together with `Stacks.Smooth.exists_lift_of_derivation` this exhibits the solutions in a chart as
a torsor, and it is the step of [Stacks Project, Tag 02H6] at which the corrected local solutions
are shown to agree on overlaps. -/
@[ega "IV 16.5.14" "Affine chart"]
theorem eq_of_liftDiffDerivation_eq_zero (hW : IsAffineOpen W) (hcomm : a ≫ f = i ≫ h)
    (hb₁f : b₁ ≫ f = h) (hb₂f : b₂ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W)
    (hzero : letI := algebraAppLE f hWV
      letI := thickeningKerModule hi
      letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
      letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
      letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
      liftDiffDerivation f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ = 0) :
    b₁ = b₂ := by
  let := algebraAppLE f hWV
  let := thickeningKerModule hi
  let := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  let := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  let := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  refine hom_ext_of_appLE hW hb₁ hb₂ (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
  have hx := congrArg
    (fun δ : Derivation Γ(S, V) Γ(X, W) (RingHom.ker i.appTop.hom) ↦
      ((δ x : RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens)))) hzero
  rw [liftDiffDerivation_apply] at hx
  simp only [Derivation.zero_apply, ZeroMemClass.coe_zero] at hx
  exact sub_eq_zero.mp hx

end Torsor

end Stacks.Smooth

end
