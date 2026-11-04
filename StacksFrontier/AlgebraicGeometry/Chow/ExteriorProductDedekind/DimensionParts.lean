module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.RespectsRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.OpenPieceDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.PreconnectedRelativeDimension

/-!
# The zero- and one-dimensional parts of a base as in section 42.63

Let `(S, δ)` be a base as in Stacks section 42.63: `S` is locally the spectrum of a Dedekind
domain, `δ = 0` at the closed points and `δ = 1` elsewhere. A field is a Dedekind domain, so `S`
may have components which are points: a point `s` which is closed and is the generic point of an
irreducible component of `S`. Call such a point *zero-dimensional*. The zero-dimensional points
form an open and closed subset `S₀` of `S`, and its complement `S₁` is the union of the
components of dimension one, so

  `S = S₀ ⊔ S₁`

is a decomposition into open and closed subschemes. A scheme `X` over `S` decomposes accordingly
as `X = X₀ ⊔ X₁`.

For `X` smooth over `S` and equidimensional of dimension `d` (every irreducible component of `X`
has δ-dimension `d`), the part `X₀` has relative dimension `d` over `S` and the part `X₁` has
relative dimension `d - 1`.

## Main definitions

* `Stacks.Chow.IsZeroDimensionalBasePoint` — a point of the base which is closed and the generic
  point of an irreducible component.
* `Stacks.Chow.IsDedekindChowBase.zeroDimensionalPart`,
  `Stacks.Chow.IsDedekindChowBase.oneDimensionalPart` — the open subschemes `S₀` and `S₁`.
* `Stacks.Chow.IsDedekindChowBase.dimensionPart` — the two parts as a family indexed by
  `ULift Bool`, `true` giving `S₁`.

## Main results

* `Stacks.Chow.IsDedekindChowBase.isClopenDecomposition_dimensionPart` — `S = S₀ ⊔ S₁`.
* `Stacks.Chow.IsDedekindChowBase.relativeDimension_of_forall_isZeroDimensionalBasePoint`,
  `Stacks.Chow.IsDedekindChowBase.relativeDimension_of_forall_not_isZeroDimensionalBasePoint` —
  a smooth scheme over `S`, equidimensional of dimension `d`, has relative dimension `d` over `S₀`
  and `d - 1` over `S₁`.

## References

* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Tag 0FCB](https://stacks.math.columbia.edu/tag/0FCB)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- A point of the base of a Chow situation is **zero-dimensional** if it is closed and is the
generic point of an irreducible component: its closure is a component consisting of one point. -/
def IsZeroDimensionalBasePoint (C : ChowSituation.{u}) (s : C.S) : Prop :=
  IsClosed ({s} : Set C.S) ∧ s ∈ genericPoints C.S

namespace IsDedekindChowBase

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C)

/-- **A zero-dimensional point is open.** If `s` is zero-dimensional and lies in an affine open
`U` whose ring of sections is a domain, then `U = {s}`. -/
theorem eq_of_isZeroDimensionalBasePoint_of_mem {s : C.S} (hs : IsZeroDimensionalBasePoint C s)
    {U : C.S.Opens} (hU : IsAffineOpen U) [IsDomain Γ(C.S, U)]
    (hsU : s ∈ (U : Set C.S)) {t : C.S} (htU : t ∈ (U : Set C.S)) : t = s := by
  have hgen : ∀ y, y ⤳ s → y = s :=
    (mem_genericPoints_iff_forall_specializes_eq s).1 hs.2
  have : IrreducibleSpace (Spec Γ(C.S, U)) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum Γ(C.S, U)))
  have : IrreducibleSpace U :=
    Function.Surjective.irreducibleSpace hU.isoSpec.inv.base.hom.continuous
      hU.isoSpec.inv.homeomorph.surjective
  set ξ : U := genericPoint U
  have hξ : ∀ y : U, ξ ⤳ y := fun y ↦ (genericPoint_spec U).specializes (Set.mem_univ y)
  have hξs : ξ.1 = s := hgen _ ((hξ ⟨s, hsU⟩).map continuous_subtype_val)
  have hst : s ⤳ t := hξs ▸ (hξ ⟨t, htU⟩).map continuous_subtype_val
  have hmem : t ∈ closure ({s} : Set C.S) := specializes_iff_mem_closure.mp hst
  rwa [hs.1.closure_eq, Set.mem_singleton_iff] at hmem

include hS in
/-- On a base as in section 42.63 the zero-dimensional points form an open set. -/
theorem isOpen_setOf_isZeroDimensionalBasePoint :
    IsOpen {s : C.S | IsZeroDimensionalBasePoint C s} := by
  refine isOpen_iff_forall_mem_open.mpr fun s hs ↦ ?_
  obtain ⟨U, hsU, hU, hded⟩ := hS.1 s
  have : IsDomain Γ(C.S, U) := hded.toIsDomain
  refine ⟨U, fun t htU ↦ ?_, U.isOpen, hsU⟩
  rwa [Set.mem_setOf_eq, eq_of_isZeroDimensionalBasePoint_of_mem hs hU hsU htU]

include hS in
/-- On a base as in section 42.63 the points which are not zero-dimensional form an open set. -/
theorem isOpen_setOf_not_isZeroDimensionalBasePoint :
    IsOpen {s : C.S | ¬ IsZeroDimensionalBasePoint C s} := by
  refine isOpen_iff_forall_mem_open.mpr fun s hs ↦ ?_
  obtain ⟨U, hsU, hU, hded⟩ := hS.1 s
  have : IsDomain Γ(C.S, U) := hded.toIsDomain
  refine ⟨U, fun t htU ht ↦ hs ?_, U.isOpen, hsU⟩
  rwa [eq_of_isZeroDimensionalBasePoint_of_mem ht hU htU hsU]

/-- **The zero-dimensional part `S₀`** of a base as in section 42.63: the open subscheme of its
zero-dimensional points, the union of its components which are points. -/
def zeroDimensionalPart : C.S.Opens :=
  ⟨{s | IsZeroDimensionalBasePoint C s}, hS.isOpen_setOf_isZeroDimensionalBasePoint⟩

/-- **The one-dimensional part `S₁`** of a base as in section 42.63: the open subscheme of its
points which are not zero-dimensional, the union of its components of dimension one. -/
def oneDimensionalPart : C.S.Opens :=
  ⟨{s | ¬ IsZeroDimensionalBasePoint C s}, hS.isOpen_setOf_not_isZeroDimensionalBasePoint⟩

/-- A point lies in `S₀` if and only if it is zero-dimensional. -/
@[simp]
theorem mem_zeroDimensionalPart {s : C.S} :
    s ∈ hS.zeroDimensionalPart ↔ IsZeroDimensionalBasePoint C s :=
  Iff.rfl

/-- A point lies in `S₁` if and only if it is not zero-dimensional. -/
@[simp]
theorem mem_oneDimensionalPart {s : C.S} :
    s ∈ hS.oneDimensionalPart ↔ ¬ IsZeroDimensionalBasePoint C s :=
  Iff.rfl

/-- The two dimension parts of a base as in section 42.63, indexed by `ULift Bool`: `true` gives
the one-dimensional part `S₁` and `false` the zero-dimensional part `S₀`. -/
def dimensionPart (i : ULift.{u} Bool) : C.S.Opens :=
  cond i.down hS.oneDimensionalPart hS.zeroDimensionalPart

/-- The dimension part indexed by `true` is `S₁`. -/
@[simp]
theorem dimensionPart_true : hS.dimensionPart ⟨true⟩ = hS.oneDimensionalPart :=
  rfl

/-- The dimension part indexed by `false` is `S₀`. -/
@[simp]
theorem dimensionPart_false : hS.dimensionPart ⟨false⟩ = hS.zeroDimensionalPart :=
  rfl

/-- **`S = S₀ ⊔ S₁`.** The zero- and one-dimensional parts of a base as in section 42.63 form a
decomposition into open and closed subschemes. -/
theorem isClopenDecomposition_dimensionPart : IsClopenDecomposition hS.dimensionPart where
  disjoint i j hij := by
    rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩ <;> first
      | exact absurd rfl hij
      | exact disjoint_iff.mpr (Opens.ext (Set.eq_empty_of_forall_notMem fun s hs ↦ by
          first | exact hs.2 hs.1 | exact hs.1 hs.2))
  iSup_eq_top := by
    refine Opens.ext (Set.eq_univ_of_forall fun s ↦ ?_)
    rw [Opens.coe_iSup, Set.mem_iUnion]
    by_cases hs : IsZeroDimensionalBasePoint C s
    · exact ⟨⟨false⟩, hs⟩
    · exact ⟨⟨true⟩, hs⟩

/-! ### Relative dimension over the two parts -/

section RelativeDimension

variable {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]

omit hS in
/-- **Pure relative dimension from the generic points.** Let `f : X ⟶ S` be smooth and suppose
that at every generic point `η` of an irreducible component of `X` the relative dimension
`δ_X(η)` of Stacks 02JW exceeds `δ(f η)` by `n`. Then `f` has relative dimension `n`. -/
theorem relativeDimension_of_forall_mem_genericPoints [Smooth f] (n : ℕ)
    (h : ∀ η ∈ genericPoints X,
      relativeDimension C.dimensionFunction f η = C.dimensionFunction (f.base η) + n) :
    AlgebraicGeometry.RelativeDimension f n := by
  obtain ⟨U, hclopen, hcover, -, hrel⟩ :=
    exists_clopen_relativeDimension f (isCohenMacaulay_fiber_of_smooth f)
  have key : ∀ (m : ℕ) (x : X), x ∈ U m → m = n := by
    intro m x hx
    set Z : irreducibleComponents X := ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩
    set η : genericPoints X := genericPoints.ofComponent Z
    have hηx : η.1 ⤳ x := specializes_iff_mem_closure.mpr
      ((genericPoints.isGenericPoint_ofComponent Z).symm ▸ mem_irreducibleComponent)
    have hηU : η.1 ∈ U m := hηx.mem_open (U m).isOpen hx
    set η' : (U m : Scheme.{u}) := ⟨η.1, hηU⟩
    have hη'gen : η' ∈ genericPoints (U m : Scheme.{u}) := by
      rw [mem_genericPoints_iff_forall_specializes_eq]
      intro y hy
      have hy' : y.1 ⤳ η.1 := hy.map continuous_subtype_val
      exact Subtype.ext ((mem_genericPoints_iff_forall_specializes_eq η.1).1 η.2 y.1 hy')
    set W := genericPoints.component (⟨η', hη'gen⟩ : genericPoints (U m : Scheme.{u}))
    have hW : W.2.1.genericPoint = η' :=
      (W.2.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents W.1 W.2)).eq
        (genericPoints.isGenericPoint ⟨η', hη'gen⟩)
    have htr := toNat_residueTrdeg_genericPoint ((U m).ι ≫ f) W m (hrel m)
    rw [hW] at htr
    have hδ := relativeDimension_opensι_comp C.dimensionFunction f (U m) η'
    have hη := h η.1 η.2
    change C.dimensionFunction (((U m).ι ≫ f).base η') +
        (Cardinal.toNat (residueTrdeg ((U m).ι ≫ f) η') : ℤ) = _ at hδ
    rw [htr] at hδ
    change _ = relativeDimension C.dimensionFunction f η.1 at hδ
    rw [hη] at hδ
    have hfη : ((U m).ι ≫ f).base η' = f.base η.1 := rfl
    rw [hfη] at hδ
    exact_mod_cast (add_left_cancel hδ : ((m : ℕ) : ℤ) = n)
  have htop : U n = ⊤ := by
    refine Opens.ext (Set.eq_univ_of_forall fun x ↦ ?_)
    have hx : x ∈ iSup U := hcover ▸ trivial
    obtain ⟨m, hm⟩ := Opens.mem_iSup.1 hx
    exact key m x hm ▸ hm
  have hrn := hrel n
  rw [htop] at hrn
  have hcomp := RelativeDimension.comp_isOpenImmersion X.topIso.inv _ hrn
  have e : X.topIso.inv ≫ (⊤ : X.Opens).ι ≫ f = f := by
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  have aux : ∀ {g : X ⟶ C.S} [LocallyOfFiniteType g], g = f →
      AlgebraicGeometry.RelativeDimension g n → AlgebraicGeometry.RelativeDimension f n := by
    intro g _ hg hgn
    subst hg
    exact hgn
  exact aux e hcomp

omit [LocallyOfFiniteType f] in
/-- A flat morphism carries the generic point of an irreducible component of its source to the
generic point of an irreducible component of the base. -/
theorem mem_genericPoints_of_flat [Flat f] {η : X} (hη : η ∈ genericPoints X) :
    f.base η ∈ genericPoints C.S := by
  rw [mem_genericPoints_iff_forall_specializes_eq]
  intro t ht
  obtain ⟨η', hη'η, hη't⟩ := AlgebraicGeometry.Flat.generalizingMap f ht
  rw [← hη't, (mem_genericPoints_iff_forall_specializes_eq η).1 hη η' hη'η]

include hS in
/-- **Over the zero-dimensional part a smooth equidimensional scheme has relative dimension
`d`.** Let `f : X ⟶ S` be smooth over a base as in section 42.63, with every irreducible component
of `X` of δ-dimension `d`, and with `X` lying over the zero-dimensional part `S₀`. Then `f` has
relative dimension `d`. -/
theorem relativeDimension_of_forall_isZeroDimensionalBasePoint [Smooth f] (d : ℕ)
    (hd : ∀ η ∈ genericPoints X, relativeDimension C.dimensionFunction f η = d)
    (hX : ∀ x : X, IsZeroDimensionalBasePoint C (f.base x)) :
    AlgebraicGeometry.RelativeDimension f d := by
  refine relativeDimension_of_forall_mem_genericPoints f d fun η hη ↦ ?_
  rw [hd η hη, hS.2.1 _ (hX η).1, zero_add]

include hS in
/-- **Over the one-dimensional part a smooth equidimensional scheme has relative dimension
`d - 1`.** Let `f : X ⟶ S` be smooth over a base as in section 42.63, with every irreducible
component of `X` of δ-dimension `d`, and with no point of `X` over the zero-dimensional part `S₀`.
Then `f` has relative dimension `d - 1`. -/
theorem relativeDimension_of_forall_not_isZeroDimensionalBasePoint [Smooth f] (d : ℕ)
    (hd : ∀ η ∈ genericPoints X, relativeDimension C.dimensionFunction f η = d)
    (hX : ∀ x : X, ¬ IsZeroDimensionalBasePoint C (f.base x)) :
    AlgebraicGeometry.RelativeDimension f (d - 1) := by
  have hδ : ∀ η ∈ genericPoints X, C.dimensionFunction (f.base η) = 1 := fun η hη ↦
    hS.2.2 _ fun hcl ↦ hX η ⟨hcl, mem_genericPoints_of_flat f hη⟩
  refine relativeDimension_of_forall_mem_genericPoints f (d - 1) fun η hη ↦ ?_
  have hge : C.dimensionFunction (f.base η) ≤ relativeDimension C.dimensionFunction f η := by
    show _ ≤ C.dimensionFunction (f.base η) + (Cardinal.toNat (residueTrdeg f η) : ℤ)
    lia
  rw [hd η hη, hδ η hη] at hge ⊢
  lia

end RelativeDimension

end IsDedekindChowBase

end Stacks.Chow

end
