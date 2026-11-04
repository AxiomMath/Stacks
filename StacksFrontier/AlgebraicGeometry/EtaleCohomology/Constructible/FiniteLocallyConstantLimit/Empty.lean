module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering

/-!
# Sheaves on the small étale site of the empty scheme

Over a scheme with no points every object of the small étale site is covered by the empty sieve,
so every sheaf takes terminal values and any two morphisms of sheaves with the same source and
target agree. This is the degenerate case of the descent of finite locally constant sheaves along
a limit of schemes (Stacks Tag 0GL2): when the limit is empty, so is every sufficiently late
stage.

## Main results

* `AlgebraicGeometry.SmallEtale.bot_mem_topology_of_isEmpty` — over an empty scheme the empty
  sieve covers every object.
* `AlgebraicGeometry.SmallEtale.sheaf_hom_ext_of_isEmpty` — over an empty scheme any two
  morphisms of sheaves agree.

## References

* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Over an empty scheme the empty sieve covers every object** of the small étale site: an
object maps to the scheme, so it has no points, and the empty family is jointly surjective. -/
public theorem bot_mem_topology_of_isEmpty [IsEmpty S] (V : SmallEtale B S hS) :
    (⊥ : Sieve V) ∈ SmallEtale.topology B S hS V := by
  refine mem_topology_of_jointlySurjective fun x => ?_
  exact (IsEmpty.false (α := S) ((B.inclusion.map V.obj.hom).base x)).elim

/-- **Over an empty scheme any two morphisms of sheaves agree.** Every section set of the target
is terminal, the empty sieve covering every object. -/
public theorem sheaf_hom_ext_of_isEmpty [IsEmpty S] {A : Type t} [Category.{v} A]
    {F G : Sheaf (SmallEtale.topology B S hS) A} (a b : F ⟶ G) : a = b := by
  ext V
  exact (G.isTerminalOfBotCover V.unop (bot_mem_topology_of_isEmpty B S hS V.unop)).hom_ext _ _

end AlgebraicGeometry.SmallEtale
