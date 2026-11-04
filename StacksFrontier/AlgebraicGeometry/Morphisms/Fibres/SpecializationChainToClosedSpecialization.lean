module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsBetweenInFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsInFibresGeneral
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SpecializationChainInFibre

/-!
# The chain inside a fibre reaches a prescribed fibrewise closed specialization

Let `f : X ⟶ S` be locally of finite type, let `x ⤳ x'` be a specialization in `X` with `x'`
closed in its own fibre, and set `s = f x`. Writing `d = trdeg_{κ(s)}(κ(x))`, there is a chain

`x = x₀ ⤳ x₁ ⤳ ⋯ ⤳ x_d ⤳ x'`

whose first `d` steps are *immediate* specializations inside the fibre `X_s`, whose last term
`x_d` is a closed point of `X_s`, and which avoids any prescribed closed subset of `X_s` not
containing `x`. What is new here is the final link `x_d ⤳ x'` to the prescribed point of
Stacks 053U.

All of that together is false in exactly one configuration, a nontrivial specialization inside
a single fibre, where `x'` is itself a closed point of `X_s` and the closed set to be avoided may
be taken to be `{x'}`. So the remark is stated here at the hypotheses of the tag and no others,
as an equivalence —
`AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber_iff`: every assertion
of the remark holds if and only if `x = x'` or `f x ≠ f x'`. Its reverse implication is the
content of the remark, its forward implication the refutation of the printed statement, and both
are proved here. The defect is inherited from Stacks 053U, which
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff` states with the same range of
validity.

The two identities `d = dim(closure of x in X_s)` and
`d = trdeg_{κ(s)}(κ(x))` are
`AlgebraicGeometry.natTrdegFiber_eq_topologicalKrullDim_closure` and
`AlgebraicGeometry.natTrdegFiber_eq_toNat_trdeg_residueField` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SpecializationChainInFibre`, which also has the
chain without the final link.

The final link is what needed Stacks 053U, and it is what the proof supplies here. The density
conclusion of Stacks 053U, `AlgebraicGeometry.closure_closedPoints_between_fiber_eq` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsBetweenInFibres`, says that the
points of `X_s` closed
in `X_s` and lying between `x` and `x'` are dense in the closure of `x` in `X_s`. Applied to the
open complement of the closed set to be avoided — which contains `x`, hence meets that closure —
it produces one such point `y` outside that set. It remains to walk from `x` down to `y`
specifically, rather than to some closed point, and that is possible because the residue-field
transcendence degree is a dimension function on a scheme locally of finite type over a field: it
drops by exactly one along an immediate specialization, so from `x ⤳ y` with `y` of degree zero
one extracts a chain of exactly `d` immediate steps ending at `y`.

As in `SpecializationChainInFibre`, the avoidance clause is obtained by running the whole
argument inside the open subscheme complementary to the prescribed closed set; residue fields,
hence transcendence degrees, are unchanged by an open immersion, so the length of the chain and
the closedness of its last term remain assertions about `X_s`.

## Main results

* `AlgebraicGeometry.exists_chain_isImmediateSpecialization_eq_of_natTrdegResidueField_eq_zero`:
  on a scheme locally of finite type over a field, a specialization `x ⤳ y` whose target has
  residue-field transcendence degree zero is realized by a chain of exactly
  `trdeg_k κ(x)` immediate specializations **ending at `y`**.
* `AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber`: **every
  assertion of Stacks 053V at once** — the chain, its last term closed in the fibre, the final
  link `x_d ⤳ x'` and the avoidance clause — when `x = x'` or `f x ≠ f x'`. This is the reverse
  implication of the equivalence below.
* `AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber_iff`:
  **Stacks 053V at the hypotheses of the tag and no others** — every assertion of the remark,
  for every closed subset of `X_s` missing `x`, holds if and only if `x = x'` or `f x ≠ f x'`.
  This is what carries the tag for the remark as a whole; the forward implication refutes the
  printed statement, by taking `{x'}` as the set to avoid when `x'` lies in the fibre of `x`.
* `AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber_of_isClosed`:
  **Stacks 053V without its avoidance clause**, unconditionally.
* `AlgebraicGeometry.Stacks053UAsPrinted`, and
  `AlgebraicGeometry.isClosed_asFiber_of_stacks053UAsPrinted`: Stacks 053U with nothing added,
  and the proof that it forces **every** point of **every** fibre of **every** morphism locally
  of finite type to be closed in that fibre.
* `AlgebraicGeometry.not_stacks053UAsPrinted`: consequently one point not closed in its own
  fibre refutes Stacks 053U as printed.

## On the range of validity of Stacks 053U, and the suspected erratum

The condition `x = x'` or `f x ≠ f x'` is exactly the range of validity of Stacks 053U, and it
is exactly the range of validity of this remark too, for a second reason: when `x'` lies in the
fibre of `x` and is closed there, the last term of the chain is forced to be `x'` itself, so
`x'` would have to avoid the prescribed closed set, which is assumed only to miss `x`. When
`f x ≠ f x'` the point `x'` is not in `X_s` at all and no such clash can arise. Neither tag is
registered on the statement as printed; both are registered on the equivalence that states the
conclusion together with the condition.

That the tag as printed is not merely unproved but false is recorded here rather than asserted
in an attribute: `AlgebraicGeometry.isClosed_asFiber_of_stacks053UAsPrinted` derives from it
that every morphism locally of finite type has discrete fibres, so that
`AlgebraicGeometry.not_stacks053UAsPrinted` needs only a single morphism locally of finite type
with a point not closed in its own fibre — any variety of positive dimension over a field — to
refute it. Supplying that witness in Lean is the one step left; the intended one is the fibre of
`Algebra.PointAndAffineLine`, which
`Algebra.PointAndAffineLine.one_le_topologicalKrullDim_fibreLine` shows has dimension at least
one, and a sober space of positive dimension has a point that is not closed. Neither this file
nor `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsInFibresGeneral` registers
anything under 053U: the registration is on
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsBetweenInFibres`, which states the
tag's conclusion together with its exact range of validity and so records the overreach of the
statement as printed rather than the statement as printed.

## References

* [Stacks Project, Tag 053V](https://stacks.math.columbia.edu/tag/053V)
* [Stacks Project, Tag 053U](https://stacks.math.columbia.edu/tag/053U)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A chain of immediate specializations from `x` down to a *prescribed* point `y` of
residue-field transcendence degree zero, of length `trdeg_k κ(x)`, on a scheme locally of finite
type over a field. The degree drops by one along each immediate step, so the length is forced;
the induction is on it, using that a dimension function turns any nontrivial specialization
`x ⤳ y` into an immediate one `x ⤳ z` with `z ⤳ y`. -/
public theorem exists_chain_isImmediateSpecialization_eq_of_natTrdegResidueField_eq_zero
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x y : X) (hxy : x ⤳ y) (hy : natTrdegResidueField k X f y = 0) :
    ∃ c : Fin (natTrdegResidueField k X f x + 1) → X, c 0 = x ∧
      (∀ i : Fin (natTrdegResidueField k X f x),
        IsImmediateSpecialization (c i.castSucc) (c i.succ)) ∧
      c (Fin.last (natTrdegResidueField k X f x)) = y := by
  suffices h : ∀ n : ℕ, ∀ x : X, natTrdegResidueField k X f x = n → x ⤳ y →
      ∃ c : Fin (n + 1) → X, c 0 = x ∧
        (∀ i : Fin n, IsImmediateSpecialization (c i.castSucc) (c i.succ)) ∧
        c (Fin.last n) = y from h _ x rfl hxy
  intro n
  induction n with
  | zero =>
    intro x hx hxy
    have hyx : y = x := by
      simpa [(isClosed_singleton_of_natTrdegResidueField_eq_zero k X f x hx).closure_eq] using
        specializes_iff_mem_closure.mp hxy
    exact ⟨fun _ ↦ x, rfl, fun i ↦ i.elim0, hyx.symm⟩
  | succ n ih =>
    intro x hx hxy
    have hne : x ≠ y := by
      rintro rfl
      omega
    obtain ⟨z, hz, hzy⟩ :=
      (residueFieldTrdegDimensionFunction k X f).exists_isImmediateSpecialization hxy hne
    have hzn : natTrdegResidueField k X f z = n := by
      have := natTrdegResidueField_eq_add_one_of_isImmediateSpecialization k X f hz
      omega
    obtain ⟨c, hc0, hcstep, hclast⟩ := ih z hzn hzy
    refine ⟨Fin.cons x c, rfl, ?_, ?_⟩
    · refine Fin.cases ?_ ?_
      · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hc0] using hz
      · intro j
        simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hcstep j
    · simpa only [← Fin.succ_last, Fin.cons_succ] using hclast

variable {X S : Scheme.{u}}

/-- For `f` locally of finite type, a point `x` and a point `y` closed in the fibre `X_{f x}` with
`x ⤳ y`, there is a chain of `natTrdegFiber f x` immediate specializations inside `X_{f x}` from
`x` to `y`, avoiding any closed subset of `X_{f x}` which misses both `x` and `y`. -/
public theorem exists_chain_isImmediateSpecialization_fiber_eq_of_isClosed
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) (y : f.fiber (f x))
    (hy : IsClosed ({y} : Set (f.fiber (f x)))) (hxy : x ⤳ f.fiberι (f x) y)
    {W : Set (f.fiber (f x))} (hW : IsClosed W) (hxW : f.asFiber x ∉ W) (hyW : y ∉ W) :
    ∃ c : Fin (natTrdegFiber f x + 1) → f.fiber (f x), c 0 = f.asFiber x ∧
      (∀ i : Fin (natTrdegFiber f x), IsImmediateSpecialization (c i.castSucc) (c i.succ)) ∧
      c (Fin.last _) = y ∧ ∀ i, c i ∉ W := by
  let k := S.residueField (f x)
  let T := f.fiber (f x)
  let g : T ⟶ Spec (.of k) := f.fiberToSpecResidueField (f x)
  let V : T.Opens := ⟨Wᶜ, hW.isOpen_compl⟩
  let p : V.toScheme := ⟨f.asFiber x, hxW⟩
  let q : V.toScheme := ⟨y, hyW⟩
  have hιp : V.ι p = f.asFiber x := rfl
  have hιq : V.ι q = y := rfl
  have hdeg : ∀ w : V.toScheme,
      natTrdegResidueField k V.toScheme (V.ι ≫ g) w =
        natTrdegResidueField k T g (V.ι w) := fun w ↦
    (congrArg Cardinal.toNat (trdeg_residueField_of_surjectiveOnStalks k g V.ι w)).symm
  have hp : natTrdegResidueField k V.toScheme (V.ι ≫ g) p = natTrdegFiber f x := by
    rw [hdeg p, hιp]
    rfl
  have hq : natTrdegResidueField k V.toScheme (V.ι ≫ g) q = 0 := by
    rw [hdeg q, hιq]
    exact natTrdegResidueField_eq_zero_of_isClosed k T g y hy
  have hpq : p ⤳ q := V.ι.isEmbedding.specializes_iff.mp
    (show f.asFiber x ⤳ y from (f.fiberι (f x)).isEmbedding.specializes_iff.mp
      (by simpa only [Scheme.Hom.fiberι_asFiber] using hxy))
  rw [← hp]
  obtain ⟨c, hc0, hcstep, hclast⟩ :=
    exists_chain_isImmediateSpecialization_eq_of_natTrdegResidueField_eq_zero k V.toScheme
      (V.ι ≫ g) p q hpq hq
  exact ⟨fun i ↦ V.ι (c i), by simpa only [hc0] using hιp,
    fun i ↦ isImmediateSpecialization_val_of_isOpen V.isOpen (hcstep i),
    by simpa only [hclast] using hιq, fun i ↦ (c i).2⟩

/-- **Stacks 053V.** Let `f : X ⟶ S` be locally of finite type, let `x ⤳ x'` with `x'` closed in
its own fibre and `x = x'` or `f x ≠ f x'`, and let `W` be a closed subset of the fibre `X_{f x}`
not containing `x`. Then there is a chain

`x = c 0 ⤳ c 1 ⤳ ⋯ ⤳ c d`

of `d = natTrdegFiber f x` immediate specializations inside `X_{f x}`, avoiding `W`, whose last
term is a closed point of `X_{f x}` which specializes to `x'`.

**This is every assertion of Stacks 053V at once**, and the hypothesis `x = x'` or
`f x ≠ f x'` cannot be dropped, because the remark as printed is false without it. Suppose
`f x = f x'` and `x ≠ x'`, and take `W = {x'}`: it is closed in `X_{f x}` because `x'` is closed
in its own fibre, which is `X_{f x}`, and it does not contain `x`. The conclusion would give a
closed point `x_d` of `X_{f x}` with `x_d ⤳ x'` and `x_d ∉ W`; but `x'` lies in `X_{f x}` and
`{x_d}` is closed there, so `x_d ⤳ x'` forces `x' = x_d`, contradicting `x_d ∉ W`. The generic
point of `A¹` over a field, specializing to a closed point, is such a configuration.

Because that refutation is available, the remark is registered at the hypotheses of the tag
instead, as the equivalence
`AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber_iff`, of which this
theorem is the reverse implication. -/
public theorem exists_chain_isImmediateSpecialization_specializes_fiber
    (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X) (hxx' : x ⤳ x')
    (hx' : IsClosed ({f.asFiber x'} : Set (f.fiber (f x'))))
    (hbase : x = x' ∨ f x ≠ f x')
    {W : Set (f.fiber (f x))} (hW : IsClosed W) (hxW : f.asFiber x ∉ W) :
    ∃ c : Fin (natTrdegFiber f x + 1) → f.fiber (f x),
      c 0 = f.asFiber x ∧
      (∀ i : Fin (natTrdegFiber f x),
        IsImmediateSpecialization (c i.castSucc) (c i.succ)) ∧
      IsClosed ({c (Fin.last (natTrdegFiber f x))} : Set (f.fiber (f x))) ∧
      f.fiberι (f x) (c (Fin.last (natTrdegFiber f x))) ⤳ x' ∧
      ∀ i, c i ∉ W := by
  have hmem : f.asFiber x ∈ closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
      x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'} := by
    rw [closure_closedPoints_between_fiber_eq f x x' hxx' hx' hbase]
    exact subset_closure (Set.mem_singleton _)
  obtain ⟨y, hyW, hyclosed, hxy, hyx'⟩ := mem_closure_iff.mp hmem Wᶜ hW.isOpen_compl hxW
  obtain ⟨c, hc0, hcstep, rfl, hcW⟩ :=
    exists_chain_isImmediateSpecialization_fiber_eq_of_isClosed f x y hyclosed hxy hW hxW hyW
  exact ⟨c, hc0, hcstep, hyclosed, hyx', hcW⟩

/-- A point of a fibre is closed there iff its image is closed in the fibre through it. -/
private lemma isClosed_fiber_iff_isClosed_asFiber {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    {w : X} (hw : f w = s) (y : f.fiber s) (hy : f.fiberι s y = w) :
    IsClosed ({y} : Set (f.fiber s)) ↔ IsClosed ({f.asFiber w} : Set (f.fiber (f w))) := by
  subst hw
  have hyw : y = f.asFiber w :=
    (f.fiberι (f w)).isEmbedding.injective (by rw [hy, Scheme.Hom.fiberι_asFiber])
  rw [hyw]

/-- **Stacks 053V without its avoidance clause**, and with no hypothesis added to the tag. For
`f` locally of finite type and `x ⤳ x'` with `x'` closed in its own fibre there is a chain

`x = c 0 ⤳ c 1 ⤳ ⋯ ⤳ c d`

of `d = natTrdegFiber f x` immediate specializations inside `X_{f x}` whose last term is a closed
point of `X_{f x}` specializing to `x'`.

This needs no non-degeneracy hypothesis because the point to walk down to can be produced without
Stacks 053U when `x'` already lies in the fibre of `x`: it is then `x'` itself. It is the
avoidance clause that fails in that case, which is why the remark as a whole is registered on
the equivalence
`AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber_iff` above. -/
@[stacks 053V "the chain of immediate specializations inside the fibre, of length `d`, ending in \
  a closed point of the fibre which specializes to the prescribed `x'` — unconditionally, the \
  avoidance clause aside. The remark as a whole, avoidance clause included, is \
  `AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber_iff` above, which \
  states it at the hypotheses of the tag together with its exact range of validity"]
public theorem exists_chain_isImmediateSpecialization_specializes_fiber_of_isClosed
    (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X) (hxx' : x ⤳ x')
    (hx' : IsClosed ({f.asFiber x'} : Set (f.fiber (f x')))) :
    ∃ c : Fin (natTrdegFiber f x + 1) → f.fiber (f x),
      c 0 = f.asFiber x ∧
      (∀ i : Fin (natTrdegFiber f x),
        IsImmediateSpecialization (c i.castSucc) (c i.succ)) ∧
      IsClosed ({c (Fin.last (natTrdegFiber f x))} : Set (f.fiber (f x))) ∧
      f.fiberι (f x) (c (Fin.last (natTrdegFiber f x))) ⤳ x' := by
  by_cases hb : f x = f x' ∧ x ≠ x'
  · obtain ⟨z, hz⟩ : x' ∈ Set.range (f.fiberι (f x)) := (f.range_fiberι (f x)).ge hb.1.symm
    have hzc := (isClosed_fiber_iff_isClosed_asFiber f hb.1.symm z hz).2 hx'
    obtain ⟨c, hc0, hcstep, rfl, -⟩ :=
      exists_chain_isImmediateSpecialization_fiber_eq_of_isClosed f x z hzc (by rwa [hz])
        isClosed_empty (Set.notMem_empty _) (Set.notMem_empty _)
    exact ⟨c, hc0, hcstep, hzc, by rw [hz]⟩
  · obtain ⟨c, hc0, hcstep, hcl, hsp, -⟩ :=
      exists_chain_isImmediateSpecialization_specializes_fiber f x x' hxx' hx' (by tauto)
        isClosed_empty (Set.notMem_empty _)
    exact ⟨c, hc0, hcstep, hcl, hsp⟩

/-- **Stacks 053V, under the hypotheses of the tag and no others.** Let `f : X ⟶ S` be locally
of finite type, let `x ⤳ x'` be a specialization in `X` with `x'` closed in its own fibre
`X_{f x'}`, and write `d = natTrdegFiber f x`. Then the remark holds — for *every* closed subset
`W` of the fibre `X_{f x}` not containing `x` there is a chain

`x = c 0 ⤳ c 1 ⤳ ⋯ ⤳ c d ⤳ x'`

whose first `d` steps are immediate specializations inside `X_{f x}`, which avoids `W`, and whose
last term `c d` is a closed point of `X_{f x}` — if and only if `x = x'` or `f x ≠ f x'`.

The reverse implication is the assertion of the remark and carries its mathematical content: it
is `AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber`, which runs the
argument of the source.

The forward implication settles the one remaining situation, a nontrivial specialization inside
one fibre, where the remark fails. If `f x = f x'` then `x'` is a point `z` of `X_{f x}`, closed
there, so `{z}` is a closed subset of `X_{f x}`; were `x ≠ x'` it would not contain `x`, hence
would be a legitimate set to avoid, and the chain avoiding it would end in a point of `X_{f x}`,
closed there, specializing to `x'` and different from `z`. But a point of a fibre closed in that
fibre is the only point of the fibre it specializes to
(`AlgebraicGeometry.eq_of_fiberι_specializes_of_isClosed`), so that last term is `z` after all.
For `X = 𝔸¹` over a field, `x` its generic point and `x'` a closed point, every hypothesis of
the remark holds and its conclusion is therefore false. This is the gap inherited from
Stacks 053U, whose density conclusion supplies the point to walk down to and which is stated
with the same range of validity in
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff`; the source's own proof draws the
same line, at the prime-avoidance step (see the module docstring).

The closed set to be avoided is quantified inside the existence statement because that is where
the source puts it: the points `x_i` can be chosen to avoid *any* closed subset of `X_s` not
containing `x`. Fixing a single `W` instead would make the equivalence false, `W = ∅` being
avoided by a chain in every configuration. -/
@[stacks 053V "EVERY assertion of the remark at once — the chain of `d` immediate \
specializations inside the fibre, its last term closed in the fibre, the final link \
`x_d ⤳ x'`, the avoidance of any closed subset of the fibre which misses `x`, and \
`d = natTrdegFiber f x` — under the tag's own hypotheses, namely `f` locally of finite type, \
`x ⤳ x'` and `x'` closed in `X_{f x'}`, together with its exact range of validity: all of that \
holds if and only if `x = x'` or `f x ≠ f x'`. The reverse implication is the remark itself, by \
the argument of the source in \
`exists_chain_isImmediateSpecialization_specializes_fiber`; the forward implication disposes of \
the one remaining situation, a nontrivial specialization inside a single fibre, where `{x'}` is \
a closed subset of the fibre missing `x` which the last term of the chain cannot avoid, since a \
closed point specializing to `x'` is `x'`. That is the gap inherited from Stacks 053U, recorded \
there in `closure_closedPoints_between_fiber_eq_iff`, and respected by the source's own proof."]
public theorem exists_chain_isImmediateSpecialization_specializes_fiber_iff
    (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X) (hxx' : x ⤳ x')
    (hx' : IsClosed ({f.asFiber x'} : Set (f.fiber (f x')))) :
    (∀ W : Set (f.fiber (f x)), IsClosed W → f.asFiber x ∉ W →
        ∃ c : Fin (natTrdegFiber f x + 1) → f.fiber (f x),
          c 0 = f.asFiber x ∧
          (∀ i : Fin (natTrdegFiber f x),
            IsImmediateSpecialization (c i.castSucc) (c i.succ)) ∧
          IsClosed ({c (Fin.last (natTrdegFiber f x))} : Set (f.fiber (f x))) ∧
          f.fiberι (f x) (c (Fin.last (natTrdegFiber f x))) ⤳ x' ∧
          ∀ i, c i ∉ W) ↔
      x = x' ∨ f x ≠ f x' := by
  refine ⟨fun h ↦ ?_, fun hbase W hW hxW ↦
    exists_chain_isImmediateSpecialization_specializes_fiber f x x' hxx' hx' hbase hW hxW⟩
  rcases ne_or_eq (f x) (f x') with hfe | hfe
  · exact Or.inr hfe
  refine Or.inl ?_
  obtain ⟨z, hz⟩ : x' ∈ Set.range (f.fiberι (f x)) := (f.range_fiberι (f x)).ge hfe.symm
  by_contra hne
  have hxz : f.asFiber x ∉ ({z} : Set (f.fiber (f x))) := fun hmem ↦
    hne (by rw [← hz, ← Set.mem_singleton_iff.mp hmem, Scheme.Hom.fiberι_asFiber])
  obtain ⟨c, -, -, hclosed, hclast, hcavoid⟩ :=
    h {z} ((isClosed_fiber_iff_isClosed_asFiber f hfe.symm z hz).2 hx') hxz
  rw [← hz] at hclast
  exact hcavoid (Fin.last _)
    (Set.mem_singleton_iff.mpr (eq_of_fiberι_specializes_of_isClosed f hclosed hclast).symm)

/-! ### Stacks 053U as printed -/

/-- The statement of Stacks 053U **exactly as printed**, with nothing added: for every morphism
locally of finite type and every specialization `x ⤳ x'` whose target is closed in its own fibre,
the points of `X_{f x}` closed in `X_{f x}` and lying between `x` and `x'` are dense in the
closure of `x` in `X_{f x}`.

This is the statement the tag is not registered on, and the one
`AlgebraicGeometry.not_stacks053UAsPrinted` refutes. -/
public abbrev Stacks053UAsPrinted : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X), x ⤳ x' →
    IsClosed ({f.asFiber x'} : Set (f.fiber (f x'))) →
    closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x)))

/-- **Stacks 053U as printed implies that every point of every fibre of every morphism locally of
finite type is closed in that fibre.**

The fibre `X_s` is a Jacobson space, so some point `x'` of it is closed there and `x ⤳ x'`
(`AlgebraicGeometry.closure_closedPoints_specializing_fiber_eq`, the tag with the condition
`x₁ ⤳ x'` dropped, which is true). That `x'` lies in the *same* fibre as `x`, and for such a pair
the conclusion of the tag forces `x` to be closed in its fibre
(`AlgebraicGeometry.isClosed_asFiber_of_closure_closedPoints_between_fiber_eq`).

The consequence is absurd — it says every morphism locally of finite type has discrete fibres,
so for instance that no variety of positive dimension exists — which is why Stacks 053U is
recorded here as a suspected erratum rather than as an unproved tag. The hypothesis
`x = x'` or `f x ≠ f x'` carried by
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq` is exactly what blocks this argument,
`x'` there being in another fibre. -/
public theorem isClosed_asFiber_of_stacks053UAsPrinted (h : Stacks053UAsPrinted.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
  have hjac := closure_closedPoints_specializing_fiber_eq f x
  rcases Set.eq_empty_or_nonempty {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
      x ⤳ f.fiberι (f x) y} with hempty | ⟨y, hyclosed, hxy⟩
  · rw [hempty, closure_empty] at hjac
    exact absurd (hjac.symm.le (subset_closure (Set.mem_singleton (f.asFiber x))))
      (Set.notMem_empty (f.asFiber x))
  · obtain ⟨x', hx'eq⟩ : ∃ w : X, f.fiberι (f x) y = w := ⟨_, rfl⟩
    have hfib : f x' = f x := by
      rw [← hx'eq]
      exact (f.range_fiberι (f x)).le ⟨y, rfl⟩
    exact isClosed_asFiber_of_closure_closedPoints_between_fiber_eq f x x' hfib
      (h f x x' (hx'eq ▸ hxy) ((isClosed_fiber_iff_isClosed_asFiber f hfib y hx'eq).1 hyclosed))

/-- **Stacks 053U as printed is refuted by a single point not closed in its own fibre.** Any
morphism locally of finite type with a fibre of positive dimension supplies one. -/
public theorem not_stacks053UAsPrinted {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) (hx : ¬ IsClosed ({f.asFiber x} : Set (f.fiber (f x)))) :
    ¬ Stacks053UAsPrinted.{u} :=
  fun h ↦ hx (isClosed_asFiber_of_stacks053UAsPrinted h f x)

end AlgebraicGeometry

end
