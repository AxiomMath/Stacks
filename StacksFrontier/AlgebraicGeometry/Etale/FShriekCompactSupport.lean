module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekSubsheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Sections with compact support

Let `X` be a scheme locally of finite type over a field `k` and let `F` be an abelian sheaf on
the small étale site of `X` inside a big étale site `B` containing `X`. A global section of
`F` — a section over the final object `X / X` of that site — has *compact support* when its
support, a closed subset of `X`, is proper over `k`. These sections form a subgroup of the
group of global sections.

## Main definitions

* `AlgebraicGeometry.SmallEtale.compactlySupportedSections` — the subgroup of global sections
  with support proper over the base field.

## Main results

* `AlgebraicGeometry.SmallEtale.mem_compactlySupportedSections` — membership is properness of
  the support.

## Implementation notes

Global sections are the sections over the final object `AlgebraicGeometry.SmallEtale.final` of
the small étale site, so no separate global-sections functor is needed. The support is the
complement of the maximal zero open of `AlgebraicGeometry.SmallEtale.zeroOpen`, taken as a
`TopologicalSpace.Closeds` so that `AlgebraicGeometry.IsProperOver` applies to it directly.

The three subgroup axioms are exactly the three stability properties of supports already
available: the zero section has empty support, so the empty closed subset suffices; the
support of a sum lies in the union of the two supports, which is proper by
`AlgebraicGeometry.isProperOver_sup` and then
`AlgebraicGeometry.isProperOver_of_le`; and a section and its negative have the same support.

The separatedness hypothesis which the source carries for its main construction is not needed
to define this subgroup, and is therefore omitted; only local finite presentation of the
structure morphism is used, through `AlgebraicGeometry.IsProperOver`.

## References

* [Stacks Project, Tag 0F72](https://stacks.math.columbia.edu/tag/0F72)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] (B : BigEtaleSite.{u}) (hX : B.Contains X)
  (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})

/-- **Stacks 0F72.** The subgroup of global sections of an abelian sheaf on the small étale
site whose support is proper over the base field. -/
@[stacks 0F72]
public def compactlySupportedSections :
    AddSubgroup (F.obj.obj (op (SmallEtale.final B X hX))) where
  carrier := {s | IsProperOver f (zeroOpen B X hX F (SmallEtale.final B X hX) s).compl}
  zero_mem' := by
    have hmem : ∀ x, x ∈ zeroOpen B X hX F (SmallEtale.final B X hX)
        (0 : F.obj.obj (op (SmallEtale.final B X hX))) := by
      rw [zeroOpen_zero]
      exact fun _ => trivial
    exact isProperOver_of_le f (Z := ⊥) (fun x hx => absurd (hmem x) hx) (isProperOver_bot f)
  add_mem' := by
    intro s t hs ht
    refine isProperOver_of_le f ?_ (isProperOver_sup f _ _ hs ht)
    intro x hx
    exact supportSection_add_subset B X hX F (SmallEtale.final B X hX) s t hx
  neg_mem' := by
    intro s hs
    change IsProperOver f (zeroOpen B X hX F (SmallEtale.final B X hX) (-s)).compl
    rwa [zeroOpen_neg]

/-- Membership in the compactly supported sections is properness of the support. -/
@[simp]
public theorem mem_compactlySupportedSections
    (s : F.obj.obj (op (SmallEtale.final B X hX))) :
    s ∈ compactlySupportedSections k X f B hX F ↔
      IsProperOver f (zeroOpen B X hX F (SmallEtale.final B X hX) s).compl :=
  Iff.rfl

end AlgebraicGeometry.SmallEtale

end
