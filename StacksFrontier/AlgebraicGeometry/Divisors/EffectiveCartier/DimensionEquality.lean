module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Divisors.ClosedSubschemeDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.Topology.Dimension.Krull

/-!
# An effective Cartier divisor has dimension exactly one less

Let `X` be an integral scheme locally of finite type over the base scheme `S` of a Chow situation
and let `D ⊆ X` be a **nonempty** effective Cartier divisor. Then

  `dim D = dim X - 1`.

The inequality `dim D + 1 ≤ dim X` is available already, and topologically: the support of an
effective Cartier divisor is nowhere dense, so
`Stacks.Divisors.topologicalKrullDim_subscheme_add_one_le_of_forall_genericPoints_notMem` applies.
The reverse inequality is the content of this file, and it is *not* topological — it is the
statement that `D` meets every chain realising the dimension of `X` in codimension one, which is
false on a space with no dimension theory. What supplies that dimension theory here is the
relative dimension of [Stacks, Tag 02JW]: a Chow situation carries a universally catenary base
with a dimension function, and `Stacks.Chow.relativeDimension` is the resulting dimension function
on any `X` locally of finite type over it.

## Main results

* `Stacks.Chow.toNat_relativeDimension_le_topologicalKrullDim_of_mem` — the lower bound a single
  point gives: a closed set containing a point of relative dimension `m` has dimension at least
  `m`.
* `Stacks.Chow.schemeDeltaDimension_subscheme_of_isEffectiveCartierDivisor` — the
  delta-dimension of a nonempty effective Cartier divisor is one less than that of `X`.
* `Stacks.Chow.topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor` — **the dimension
  equality**, over an arbitrary Chow situation with Jacobson base.
* `Stacks.Chow.topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor_field` — the same
  over a field, with the ambient dimension given topologically. This is the shape an induction
  on the dimension consumes.
* `Stacks.Chow.topologicalKrullDim_zeroScheme_eq_of_ne_zero` — the specialisation to the zero
  scheme of a nonzero global section of an invertible module.

## The argument

Both directions run through the delta-dimension, which is what makes them symmetric.

Write `n = dim_δ(X)`. [Stacks, Tag 02RK], available as
`Stacks.Chow.deltaDimension_irreducibleComponent_isEffectiveCartierDivisor`, says that *every*
irreducible component of `D` has delta-dimension `n - 1`: the generic point of such a component
has ambient local ring of Krull dimension one by Krull's height theorem, hence coheight one, and
the relative dimension drops by exactly one along an immediate specialisation. Since
`dim_δ` of a scheme is the supremum of `dim_δ` over its irreducible components, and `D` is
nonempty so that supremum is over a nonempty index type, `dim_δ(D) = n - 1` exactly.

* For `dim D ≤ n - 1`: `Stacks.Chow.topologicalKrullDim_le_of_schemeDeltaDimension_le` is
  [Stacks, Tag 02QO] read as a bound on the topological dimension.
* For `dim D ≥ n - 1`: pick one irreducible component of `D` and let `x` be the image in `X` of
  its generic point. The reduced closed subscheme supported on `closure {x}` is integral, and
  [Stacks, Tag 02QO] computes its dimension as the relative dimension at `x`, which is `n - 1`.
  That subscheme sits inside the support of `D`, so the dimension of the support is at least
  `n - 1`.

Finally, over `Stacks.Chow.fieldChowSituation k` the delta-dimension of an integral scheme is its
topological dimension
(`Stacks.Chow.schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq`), which turns
the hypothesis and the conclusion into statements about `topologicalKrullDim` alone.

## The hypotheses, and why each is needed

* `[IsIntegral X]`, and `X` locally of finite type over the base. Integrality gives `X` a generic
  point at which `dim_δ(X)` is attained, which is what [Stacks, Tag 02RK] subtracts one from;
  finite type is what makes the relative dimension a dimension function at all. Both are consumed
  by `Stacks.Chow.deltaDimension_irreducibleComponent_isEffectiveCartierDivisor`.
* `[Nonempty D.subscheme]`. **The statement is false without it.** The empty subscheme is an
  effective Cartier divisor — it is cut out by the unit section — and has
  `topologicalKrullDim = ⊥`, not `d`. Nonemptiness is consumed exactly once, to know that the
  supremum over the irreducible components of `D` is not a supremum over an empty type, and to
  produce the component used for the lower bound.
* `[JacobsonSpace C.S]` and the vanishing `hδ` of the dimension function at closed points. These
  are the hypotheses of [Stacks, Tag 02QO] in both of its uses. Over the spectrum of a field they
  are free, which is why the field specialisation carries neither.
* A finite ambient dimension, in the form `dim_δ(X) = d + 1` with `d : ℕ`. This is what makes the
  subtraction meaningful; see the implementation notes.

Noetherianness of the underlying space is **not** required, although the topological route to the
upper bound needs it: `Stacks.Chow.topologicalKrullDim_le_of_schemeDeltaDimension_le` does not.
What is used instead is `IsLocallyNoetherian X`, which is free from `LocallyOfFiniteType`.

## Implementation notes

The arithmetic is stated as `dim D = d` under the hypothesis `dim X = d + 1` for a natural
number `d`, rather than as `dim D = dim X - 1`. `topologicalKrullDim` is valued in `WithBot ℕ∞`,
where subtraction is truncated and `⊥ - 1 = ⊥`, so an equation written with `-` would be true for
the empty divisor as well and would therefore assert strictly less than the theorem below. The
`d + 1` form also avoids committing to a subtraction on `WithBot ℕ∞` at all, and it is the form
the neighbouring bounded statements already use —
`Stacks.Divisors.topologicalKrullDim_subscheme_le_of_forall_genericPoints_notMem` and
`AlgebraicGeometry.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor` both index by a
natural number `d` with the hypothesis at `d + 1`. The additive form `dim D + 1 = dim X` was the
other candidate; it is weaker here, because it does not pin `dim D` to a natural number and so is
again satisfied by `⊥`.

No `@[stacks]` attribute is placed. The closest tags say something else: [Stacks, Tag 056N] is
the *local* strict drop at a point, proved in
`StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionDrop`, and [Stacks, Tag 02RK]
is the delta-dimension statement about the components of a divisor, proved in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension` and used here. The global
topological equality below is a consequence of the latter rather than a tag of its own.

## References

* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The lower bound a single point gives -/

/-- **A closed set containing a point of relative dimension `m` has dimension at least `m`.**

The reduced closed subscheme supported on `closure {x}` is integral, so [Stacks, Tag 02QO]
(`Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat`) computes its topological dimension
as the relative dimension of `x`; and that subscheme has underlying space `closure {x}`, which is
contained in any closed set containing `x`.

This is the half of the dimension theory that an inequality in the other direction cannot supply:
it exhibits a chain, rather than bounding one. -/
theorem toNat_relativeDimension_le_topologicalKrullDim_of_mem (C : ChowSituation.{u})
    [JacobsonSpace C.S] (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] {S : Set X} (hS : IsClosed S) {x : X}
    (hx : x ∈ S) :
    (((relativeDimension C.dimensionFunction f x).toNat : ℕ) : WithBot ℕ∞) ≤
      topologicalKrullDim S := by
  have hint := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hgen : I.subschemeι (genericPoint I.subscheme) = x :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x
  have hdim : topologicalKrullDim I.subscheme =
      (((relativeDimension C.dimensionFunction f x).toNat : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_relativeDimension_toNat C hδ f I.subschemeι
      (genericPoint I.subscheme) (genericPoint_spec I.subscheme), hgen]
  have hrange : Set.range I.subschemeι.base = closure ({x} : Set X) := by
    rw [I.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  calc (((relativeDimension C.dimensionFunction f x).toNat : ℕ) : WithBot ℕ∞)
      = topologicalKrullDim I.subscheme := hdim.symm
    _ = topologicalKrullDim (Set.range I.subschemeι.base) :=
        Stacks.Divisors.topologicalKrullDim_eq_range_of_isClosedImmersion I.subschemeι
    _ = topologicalKrullDim (closure ({x} : Set X)) := by rw [hrange]
    _ ≤ topologicalKrullDim S :=
        topologicalKrullDim_le_of_subset
          (hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx))

/-! ### The delta-dimension of an effective Cartier divisor -/

/-- A nonempty topological space has an irreducible component. -/
private theorem exists_mem_irreducibleComponents_of_nonempty (Y : Type u) [TopologicalSpace Y]
    [Nonempty Y] : ∃ W, W ∈ irreducibleComponents Y := by
  obtain ⟨W, hW, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({Classical.arbitrary Y} : Set Y)) isIrreducible_singleton.closure
  exact ⟨W, hW⟩

/-- **The delta-dimension of a nonempty effective Cartier divisor is one less than that of the
ambient integral scheme.**

[Stacks, Tag 02RK] gives the value `dim_δ(X) - 1` at *every* irreducible component of `D`, and
`dim_δ` is by definition the supremum over the components; nonemptiness of `D` is what makes that
supremum a supremum over a nonempty type, hence equal to the common value rather than to `⊥`. -/
theorem schemeDeltaDimension_subscheme_of_isEffectiveCartierDivisor (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsIntegral X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) [Nonempty D.subscheme] :
    schemeDeltaDimension C (D.subschemeι ≫ f) = schemeDeltaDimension C f + (-1 : ℤ) := by
  have hne : Nonempty (irreducibleComponents (D.subscheme : Type u)) := by
    obtain ⟨W, hW⟩ := exists_mem_irreducibleComponents_of_nonempty (D.subscheme : Type u)
    exact ⟨⟨W, hW⟩⟩
  rw [schemeDeltaDimension_eq_iSup C (D.subschemeι ≫ f)]
  refine (iSup_congr fun Z => ?_).trans (ciSup_const (ι := irreducibleComponents
    (D.subscheme : Type u)))
  exact deltaDimension_irreducibleComponent_isEffectiveCartierDivisor C f D hD Z

/-! ### The dimension equality -/

/-- **A nonempty effective Cartier divisor on an integral scheme has dimension exactly one less
than the ambient scheme.**

The ambient dimension enters as `dim_δ(X) = d + 1` with `d : ℕ`; see the module documentation for
why the statement is indexed by `d` rather than written with a subtraction, and for why each
hypothesis — integrality, nonemptiness of `D`, and the two hypotheses of [Stacks, Tag 02QO] — is
needed.

Both bounds come from `Stacks.Chow.schemeDeltaDimension_subscheme_of_isEffectiveCartierDivisor`:
the upper one through [Stacks, Tag 02QO] read as a bound
(`Stacks.Chow.topologicalKrullDim_le_of_schemeDeltaDimension_le`), the lower one through
`Stacks.Chow.toNat_relativeDimension_le_topologicalKrullDim_of_mem` at the generic point of one
irreducible component of `D`, whose coheight in `X` is one by [Stacks, Tag 0BCN]. -/
theorem topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor (C : ChowSituation.{u})
    [JacobsonSpace C.S] (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsIntegral X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) [Nonempty D.subscheme] {d : ℕ}
    (hn : schemeDeltaDimension C f = (((d + 1 : ℕ) : ℤ) : EInt)) :
    topologicalKrullDim (D.subscheme : Type u) = (d : WithBot ℕ∞) := by
  have hlocNoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdelta : schemeDeltaDimension C (D.subschemeι ≫ f) = ((d : ℤ) : EInt) := by
    rw [schemeDeltaDimension_subscheme_of_isEffectiveCartierDivisor C f D hD, hn,
      ← coe_add_coe_eq_coe_add]
    norm_num
  refine le_antisymm
    (topologicalKrullDim_le_of_schemeDeltaDimension_le C hδ (D.subschemeι ≫ f) d hdelta.le) ?_
  -- The lower bound: one irreducible component of `D` has coheight one in `X`.
  obtain ⟨W, hW⟩ := exists_mem_irreducibleComponents_of_nonempty (D.subscheme : Type u)
  have hrangeSupp : Set.range D.subschemeι.base = (D.supportSet : Set X) := D.range_subschemeι
  have hco : Order.coheight (D.subschemeι.base hW.1.genericPoint) = 1 := by
    exact_mod_cast
      (ringKrullDim_stalk_eq_coheight (D.subschemeι.base hW.1.genericPoint)).symm.trans
        (ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hD hW.1.genericPoint
          ⟨⟨W, hW⟩, hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)⟩)
  have hrel : relativeDimension C.dimensionFunction f
      (D.subschemeι.base hW.1.genericPoint) = ((d + 1 : ℕ) : ℤ) - 1 :=
    relativeDimension_eq_sub_one_of_coheight_eq_one C f hn hco
  have hmem : D.subschemeι.base hW.1.genericPoint ∈ D.supportSet := by
    rw [← hrangeSupp]
    exact Set.mem_range_self _
  have hlow := toNat_relativeDimension_le_topologicalKrullDim_of_mem C hδ f
    (Scheme.IdealSheafData.isClosed_supportSet D) hmem
  rw [hrel, show (((((d + 1 : ℕ) : ℤ) - 1).toNat : ℕ) : WithBot ℕ∞) = (d : WithBot ℕ∞) by
    norm_num] at hlow
  rwa [Stacks.Divisors.topologicalKrullDim_eq_range_of_isClosedImmersion D.subschemeι,
    hrangeSupp]

/-! ### Over a field -/

/-- **Over a field, a nonempty effective Cartier divisor on an integral scheme of dimension
`d + 1` has dimension `d`.**

This is `Stacks.Chow.topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor` with both the
hypothesis and the conclusion read topologically: over `Stacks.Chow.fieldChowSituation k` the
delta-dimension of an integral scheme is its topological dimension, by
`Stacks.Chow.schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq`. The spectrum
of a field is a Jacobson space and its dimension function vanishes identically, so neither
hypothesis of [Stacks, Tag 02QO] has to be carried.

This is the shape an induction on the dimension of a variety consumes: the ambient dimension is
pinned by an equality at `d + 1` and the divisor's dimension comes out as the equality at `d`,
with no case analysis. -/
theorem topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor_field {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f] [IsIntegral X]
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    [Nonempty D.subscheme] {d : ℕ}
    (hdim : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim (D.subscheme : Type u) = (d : WithBot ℕ∞) :=
  topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor (fieldChowSituation k)
    (fun _ _ => rfl) f D hD
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq f hdim)

/-! ### The zero scheme of a nonzero section -/

/-- **The zero scheme of a nonzero global section of an invertible module on an integral scheme
of dimension `d + 1` over a field has dimension `d`**, provided it is nonempty.

The zero scheme of a nonzero section on an integral scheme is an effective Cartier divisor
(`AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero`, the section being a
nonzerodivisor), so this is
`Stacks.Chow.topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor_field` with that
bridge supplied.

Nonemptiness is still a hypothesis and is still not removable: on projective space a section of
a line bundle has nonempty zero scheme, but on an affine scheme a unit section has empty zero
scheme while being nonzero. -/
theorem topologicalKrullDim_zeroScheme_eq_of_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0)
    [Nonempty (Stacks.Divisors.zeroScheme X L s).subscheme] {d : ℕ}
    (hdim : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim ((Stacks.Divisors.zeroScheme X L s).subscheme : Type u) =
      (d : WithBot ℕ∞) :=
  topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor_field f
    (Stacks.Divisors.zeroScheme X L s)
    (AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero L s hs) hdim

end Stacks.Chow

end
