module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.CategoryTheory.Countable
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.UrysohnsLemma
public import StacksFrontier.SetTheory.Cardinal.SizeBound
public import StacksFrontier.Topology.Compact.LocallyQuasiCompactHausdorffCat
import StacksCore.Tactic.StacksAttribute

/-!
# A bounded full subcategory of `LC`

`LC` is the category `Stacks.Topology.LocallyQuasiCompactHausdorff` of Hausdorff, locally
quasi-compact topological spaces. Its objects form a proper class, so before it can carry a
site one must cut it down to a small piece which is still closed under the constructions that
the coverings use. Stacks 09X2 does this by intersecting `LC` with a rank `V_α` for a suitably
chosen limit ordinal `α`; here the cut is by cardinality of the set of points, which is
equivalent and easier to compute with.

Given any small set `S₀` of objects of `LC` we choose a cardinal `κ` which is a strong prelimit
of uncountable cofinality and bounds the sizes of all members of `S₀`. The full subcategory
`LCSizeCutoff κ` of spaces with fewer than `κ` points then contains `S₀`, is essentially small,
is closed under every countable limit and every countable colimit that exists in `LC`, and
contains a representative of every space whose size is at most `Cardinal.stacksBound` of the
size of one of its objects.

Closure under countable limits is a cardinality estimate: the apex of a limit cone injects into
the product of the sizes of the objects of the diagram, and a countable product of cardinals
below `κ` stays below `κ` when `κ` is a strong prelimit of uncountable cofinality. Closure
under countable colimits is the dual estimate run through the functor `X ↦ (X ⟶ ℝ)`, which is
injective on points because a locally compact Hausdorff space is completely regular
(Urysohn), and which turns the colimit into a limit.

## Main definitions

* `Stacks.Topology.lcSize`: the number of points of an object of `LC`, as a cardinal.
* `Stacks.Topology.LCSizeCutoff`: the full subcategory of `LC` of objects of size below a
  given cardinal.
* `Stacks.Topology.BoundedLCSubcategory`: a cutoff together with all the closure properties
  Stacks 09X2 requires of `LC_α`.

## Main results

* `Stacks.Topology.exists_boundedLCSubcategory`: every small set of objects of `LC` is
  contained in such a bounded subcategory.

## Implementation notes

The intersection `LC ∩ V_α` of the source is modelled by the cardinal-size cutoff, as in the
formalization of Stacks 000J. An object below the cutoff therefore serves as its own
isomorphic representative, which is what makes `bounded_representative` immediate from
`Cardinal.stacksBound_lt_of_isStrongPrelimit`.

Countability of a diagram is `CategoryTheory.CountableCategory`, which asks that both the
objects and all the morphism types be countable; that is what the cofinality hypothesis on the
cutoff is matched against.

That `LC` and its class of coverings are "big" is expressed by universe polymorphism rather
than by an internal proper-class predicate, so no statement here asserts bigness.

## References

* [Stacks Project, Tag 09X2](https://stacks.math.columbia.edu/tag/09X2)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Equation 046U](https://stacks.math.columbia.edu/tag/046U)
-/

@[expose] public section

open CategoryTheory Cardinal

namespace Stacks.Topology

universe u

/-- The cardinality of the set of points of a Hausdorff, locally quasi-compact space. -/
abbrev lcSize (X : LocallyQuasiCompactHausdorff.{u}) : Cardinal.{u} :=
  Cardinal.mk X

/-- The full subcategory of Hausdorff, locally quasi-compact spaces whose sets of points have
cardinality strictly below `κ`. This is the model of the intersection `LC ∩ V_α` of
Stacks 09X2. -/
abbrev LCSizeCutoff (κ : Cardinal.{u}) :=
  ObjectProperty.FullSubcategory
    (fun X : LocallyQuasiCompactHausdorff.{u} => lcSize X < κ)

/-- The objects of size below `κ` form a set up to isomorphism: each is homeomorphic to a
subset of a fixed type of cardinality `κ` carrying some topology. -/
private lemma essentiallySmall_lcSizeCutoff (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u}
      (fun X : LocallyQuasiCompactHausdorff.{u} => lcSize X < κ) := by
  let U : Type u := κ.ord.ToType
  let A : Type u := Σ (S : Set U) (t : TopologicalSpace S),
    PLift (@T2Space S t ∧ @LocallyCompactSpace S t)
  let F : A → LocallyQuasiCompactHausdorff.{u} := fun a => by
    let : TopologicalSpace a.1 := a.2.1
    let : T2Space a.1 := a.2.2.down.1
    exact LocallyQuasiCompactHausdorff.of a.1 a.2.2.down.2
  refine ⟨ObjectProperty.ofObj F, inferInstance, ?_⟩
  rintro X hX
  have hm : Cardinal.mk X ≤ Cardinal.mk U := by
    simpa [U] using hX.le
  obtain ⟨f⟩ := hm
  let e : X ≃ Set.range f := Equiv.ofInjective f f.injective
  let t : TopologicalSpace (Set.range f) := TopologicalSpace.coinduced e inferInstance
  let he : X ≃ₜ Set.range f :=
    { e with
      continuous_toFun := continuous_coinduced_rng
      continuous_invFun := by
        rw [continuous_iff_coinduced_le]
        simp [t, coinduced_compose, coinduced_id] }
  let _ : TopologicalSpace (Set.range f) := t
  let _ : T2Space (Set.range f) := he.t2Space
  let _ : LocallyCompactSpace (Set.range f) := (he.locallyCompactSpace_iff).mp inferInstance
  let a : A := ⟨Set.range f, t, ⟨inferInstance, inferInstance⟩⟩
  refine ⟨F a, ObjectProperty.ofObj.mk a, ?_⟩
  let eTop : X.obj ≅ (F a).obj := TopCat.isoOfHomeo he
  exact ⟨ObjectProperty.isoMk _ eTop⟩

/-- The objects of size below `κ` form a set up to isomorphism: each is homeomorphic to a
subset of a fixed type of cardinality `κ` carrying some topology. -/
alias essentiallySmall_lcSizeCutoff' := essentiallySmall_lcSizeCutoff

/-- The bounded subcategory cut out by a size cutoff is essentially small at the universe of the
spaces, for *every* cutoff: `essentiallySmall_lcSizeCutoff'` exhibits a set of representatives,
and a full subcategory whose defining property is essentially small is essentially small. This is
what lets the cutoff be replaced by a genuinely small model, one universe below its objects. -/
instance essentiallySmall_LCSizeCutoff (κ : Cardinal.{u}) :
    EssentiallySmall.{u} (LCSizeCutoff κ) :=
  let _ := essentiallySmall_lcSizeCutoff' κ
  inferInstance

/-- A countable product of types of size below a strong prelimit `κ` of uncountable cofinality
has size below `κ`: bound every factor by the supremum, then use `μ ^ ℵ₀ < κ`. -/
private lemma mk_pi_lt_of_countable {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) (hcof : ℵ₀ < κ.ord.cof)
    {J : Type u} [Countable J] {α : J → Type u} (hf : ∀ j, Cardinal.mk (α j) < κ) :
    Cardinal.mk (∀ j, α j) < κ := by
  rw [Cardinal.mk_pi]
  let f := fun j => Cardinal.mk (α j)
  let μ := max ℵ₀ (⨆ j, f j)
  calc
    Cardinal.prod f ≤ Cardinal.prod (fun _ : J => μ) :=
      Cardinal.prod_le_prod _ _ fun j =>
        (le_ciSup Cardinal.bddAbove_of_small j).trans (le_max_right _ _)
    _ = μ ^ #J := by simp
    _ ≤ μ ^ ℵ₀ := Cardinal.power_le_power_left
      (aleph0_pos.trans_le (le_max_left _ _)).ne' Cardinal.mk_le_aleph0
    _ < κ := Cardinal.power_aleph0_lt_of_isStrongPrelimit hκ hsl
      (max_lt hκ (iSup_lt_of_lt_cof_ord ((Cardinal.mk_le_aleph0 : #J ≤ ℵ₀).trans_lt hcof) hf))

/-- The apex of a limit cone over a countable diagram of spaces of size below `κ` again has
size below `κ`: its points inject into the product of the points of the diagram, because a
point is detected by the maps out of a one-point space. -/
private lemma lcSize_limit_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ)
    (hcof : ℵ₀ < κ.ord.cof) {J : Type u} [Category.{u} J] [CountableCategory J]
    {X : LocallyQuasiCompactHausdorff.{u}}
    (p : ObjectProperty.LimitOfShape
      (fun X : LocallyQuasiCompactHausdorff.{u} => lcSize X < κ) J X) :
    lcSize X < κ := by
  have hf : Function.Injective (fun (x : X) (j : J) => p.π.app j x) := by
    intro x y hxy
    let P : LocallyQuasiCompactHausdorff.{u} := .of (ULift.{u} PUnit) inferInstance
    let g (z : X) : P ⟶ X := ObjectProperty.homMk (TopCat.ofHom ⟨fun _ => z, continuous_const⟩)
    have hg : g x = g y :=
      p.isLimit.hom_ext fun j => ConcreteCategory.hom_ext _ _ fun _ => congr_fun hxy j
    exact ConcreteCategory.congr_hom hg ⟨PUnit.unit⟩
  exact (Cardinal.mk_le_of_injective hf).trans_lt
    (mk_pi_lt_of_countable hκ hsl hcof (α := fun j => p.diag.obj j) p.prop_diag_obj)

/-- Below a strong prelimit `κ` above `ℵ₀`, cardinal exponentiation does not escape: if
`a, b < κ` then `a ^ b < κ`. -/
private lemma power_lt_of_isStrongPrelimit {κ a b : Cardinal.{u}}
    (hκ : ℵ₀ < κ) (hsl : Cardinal.IsStrongPrelimit κ) (ha : a < κ) (hb : b < κ) :
    a ^ b < κ := by
  calc
    a ^ b ≤ (2 ^ a) ^ b := Cardinal.power_le_power_right (Cardinal.cantor a).le
    _ = 2 ^ (a * b) := Cardinal.power_mul.symm
    _ < κ := hsl (Cardinal.mul_lt_of_lt hκ.le ha hb)

/-- Below a strong prelimit `κ` above `ℵ₀`, a type of functions between two types of size
below `κ` again has size below `κ`. -/
private lemma mk_arrow_lt_of_isStrongPrelimit {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) {α β : Type u} (hα : Cardinal.mk α < κ)
    (hβ : Cardinal.mk β < κ) :
    Cardinal.mk (α → β) < κ := by
  simpa [Cardinal.mk_arrow] using power_lt_of_isStrongPrelimit hκ hsl hβ hα

/-- The apex of a colimit cocone over a countable diagram of spaces of size below `κ` again
has size below `κ`. The points of a space `X` in `LC` inject into `X ⟶ ℝ` by evaluation, since
`X` is locally compact Hausdorff and so Urysohn's lemma separates a point from another point;
and `X ⟶ ℝ` injects into the product over the diagram of the function spaces, because a
morphism out of a colimit is determined by its restrictions. -/
private lemma lcSize_colimit_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) (hcof : ℵ₀ < κ.ord.cof)
    {J : Type u} [Category.{u} J] [CountableCategory J]
    {X : LocallyQuasiCompactHausdorff.{u}}
    (p : ObjectProperty.ColimitOfShape
      (fun X : LocallyQuasiCompactHausdorff.{u} => lcSize X < κ) J X) :
    lcSize X < κ := by
  let _ : LocallyCompactSpace (ULift.{u} ℝ) :=
    (Homeomorph.ulift (X := ℝ)).locallyCompactSpace_iff.mpr inferInstance
  let R : LocallyQuasiCompactHausdorff.{u} := .of (ULift.{u} ℝ) inferInstance
  have hR : Cardinal.mk (ULift.{u} ℝ) < κ := by
    simpa [Cardinal.mk_uLift, Cardinal.mk_real, ← Cardinal.two_power_aleph0] using hsl hκ
  have hev : Function.Injective (fun (x : X) (f : X ⟶ R) => f x) := by
    intro x y h
    by_contra hxy
    obtain ⟨g, hgx, hgy, _⟩ := exists_continuous_zero_one_of_isCompact
      (isCompact_singleton : IsCompact ({x} : Set X))
      (isClosed_singleton : IsClosed ({y} : Set X))
      (Set.disjoint_singleton.2 hxy)
    let g' : X ⟶ R := ObjectProperty.homMk (TopCat.ofHom
      ⟨fun z => ULift.up (g z), continuous_uliftUp.comp g.continuous⟩)
    exact zero_ne_one <| ((hgx rfl : g x = 0).symm.trans
      (congr_arg ULift.down (congr_fun h g'))).trans (hgy rfl : g y = 1)
  have hres : Function.Injective (fun (f : X ⟶ R) j (x : p.diag.obj j) => f (p.ι.app j x)) :=
    fun f g h => p.isColimit.hom_ext fun j =>
      ConcreteCategory.hom_ext _ _ (congr_fun (congr_fun h j))
  have hprod : Cardinal.mk (∀ j, p.diag.obj j → ULift.{u} ℝ) < κ :=
    mk_pi_lt_of_countable hκ hsl hcof
      fun j => mk_arrow_lt_of_isStrongPrelimit hκ hsl (p.prop_diag_obj j) hR
  exact (Cardinal.mk_le_of_injective hev).trans_lt (mk_arrow_lt_of_isStrongPrelimit hκ hsl
    ((Cardinal.mk_le_of_injective hres).trans_lt hprod) hR)

/-- The data and properties of the bounded subcategory `LC_α` of Stacks 09X2, out of which the
big quasi-compact site is built: a size cutoff containing a prescribed set of spaces, closed
under countable limits and colimits and under the cardinal bound of Equation 046U. -/
structure BoundedLCSubcategory (S₀ : Set LocallyQuasiCompactHausdorff.{u}) where
  /-- The cardinal-size cutoff representing the chosen limit rank. -/
  cutoff : Cardinal.{u}
  /-- The cutoff is uncountable. -/
  aleph0_lt_cutoff : ℵ₀ < cutoff
  /-- The cutoff is a strong prelimit cardinal, so it is closed under `stacksBound`. -/
  cutoff_isStrongPrelimit : Cardinal.IsStrongPrelimit cutoff
  /-- The cutoff has uncountable cofinality, as required for countable diagrams. -/
  aleph0_lt_cutoff_cof : ℵ₀ < cutoff.ord.cof
  /-- Every initially prescribed object belongs to the bounded subcategory. -/
  contains_initial : ∀ X ∈ S₀, lcSize X < cutoff
  /-- Up to isomorphism, the objects below the cutoff form a set. -/
  category_essentiallySmall : EssentiallySmall.{u} (LCSizeCutoff cutoff)
  /-- The bounded subcategory is closed under every existing countable limit in `LC`. -/
  closedUnderCountableLimits :
    ∀ (J : Type u) [Category.{u} J] [CountableCategory J],
      ObjectProperty.IsClosedUnderLimitsOfShape
        (fun X : LocallyQuasiCompactHausdorff.{u} => lcSize X < cutoff) J
  /-- The bounded subcategory is closed under every existing countable colimit in `LC`. -/
  closedUnderCountableColimits :
    ∀ (J : Type u) [Category.{u} J] [CountableCategory J],
      ObjectProperty.IsClosedUnderColimitsOfShape
        (fun X : LocallyQuasiCompactHausdorff.{u} => lcSize X < cutoff) J
  /-- An object whose size is bounded in terms of an object in the subcategory is isomorphic
  to an object of the subcategory. -/
  bounded_representative :
    ∀ {X Y : LocallyQuasiCompactHausdorff.{u}}, lcSize X < cutoff →
      lcSize Y ≤ Cardinal.stacksBound (lcSize X) →
        ∃ Z : LCSizeCutoff cutoff, Nonempty (Y ≅ Z.1)

/-- **Stacks 09X2, the bounded-subcategory clause.** Any prescribed small set of Hausdorff,
locally quasi-compact spaces is contained in a bounded full subcategory of `LC` which is
closed under existing countable limits and colimits and under the cardinal bound of
Equation 046U. -/
@[stacks 09X2 "the bounded subcategory LC_α"]
theorem exists_boundedLCSubcategory
    (S₀ : Set LocallyQuasiCompactHausdorff.{u}) [Small.{u} S₀] :
    Nonempty (BoundedLCSubcategory S₀) := by
  classical
  obtain ⟨κ, hμκ, hκ, hcof⟩ := Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof
    (max ℵ₀ (⨆ X : S₀, lcSize X) : Cardinal.{u})
  have hℵ : ℵ₀ < κ := (le_max_left _ _).trans_lt hμκ
  exact ⟨⟨κ, hℵ, hκ, hcof, fun X hX => (le_ciSup (f := fun X : S₀ => lcSize X)
      Cardinal.bddAbove_of_small ⟨X, hX⟩).trans_lt ((le_max_right _ _).trans_lt hμκ),
    inferInstance,
    fun J _ _ => ⟨fun X ⟨p⟩ => lcSize_limit_lt hℵ hκ hcof p⟩,
    fun J _ _ => ⟨fun X ⟨p⟩ => lcSize_colimit_lt hℵ hκ hcof p⟩,
    fun hX hY => ⟨⟨_, hY.trans_lt (Cardinal.stacksBound_lt_of_isStrongPrelimit hℵ hκ hX)⟩,
      ⟨Iso.refl _⟩⟩⟩⟩

end Stacks.Topology

end
