module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemEssSurj
public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemOpensFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemOpensFull
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.BigHOverOpensSieve

/-!
# Sheaves of modules over a system of sheaves of rings form a Zariski stack

Let `𝓡` be a system of sheaves of rings on the big h category over `S`
(`AlgebraicGeometry.BigHOver.RingSheafSystem`) with the restriction property
(`AlgebraicGeometry.BigHOver.RingSheafSystem.UnitBijective`): extension of scalars to an open is
restriction to it. Then the pseudofunctor of sheaves of `𝓡`-modules is a stack for every Zariski
family of the site.

For a family of inclusions of opens covering an object, the canonical descent functor is
faithful (`AlgebraicGeometry.BigHOver.RingSheafSystem.faithful_toDescentData_opens`), full
(`AlgebraicGeometry.BigHOver.RingSheafSystem.full_toDescentData_opens`) and essentially
surjective — every descent datum is the canonical datum of the module glued from it by Stacks
00AM (`AlgebraicGeometry.BigHOver.RingSheafSystem.essSurj_toDescentData_opens`). An arbitrary
Zariski family generates the same sieve as the inclusions of the images of its members
(`AlgebraicGeometry.BigHOver.isStackFor_of_isStackFor_opens`).

## Main results

* `AlgebraicGeometry.BigHOver.RingSheafSystem.isStackFor_opens`: the stack condition along a
  covering family of opens.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.isStackFor_of_mem_zariskiPrecoverage`: **the stack
  condition along every Zariski family of the big h category over `S`.**

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.BigHOver.RingSheafSystem

universe t u

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {𝓡 : RingSheafSystem B S hS}

/-- **The pseudofunctor of modules of a system with the restriction property is a stack for every
covering family of opens.** -/
theorem isStackFor_opens (h𝓡 : 𝓡.UnitBijective) {U : BigHOver B S hS} {ι : Type u}
    (W : ι → ((toScheme B S hS).obj U).Opens) (hW : ⨆ i, W i = ⊤) :
    𝓡.modulePseudofunctor.IsStackFor
      (Presieve.ofArrows (fun i => opensObj B S hS (W i)) (fun i => opensι B S hS (W i))) := by
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  have := faithful_toDescentData_opens h𝓡 W hW
  have := full_toDescentData_opens h𝓡 W hW
  have := essSurj_toDescentData_opens W h𝓡
  exact { }

/-- **The pseudofunctor of modules of a system with the restriction property is a stack for every
Zariski family of the big h category over `S`**, whatever the universe of its index type. -/
theorem isStackFor_of_mem_zariskiPrecoverage (h𝓡 : 𝓡.UnitBijective) {U : BigHOver B S hS}
    {ι : Type t} {X : ι → BigHOver B S hS} (f : ∀ i, X i ⟶ U)
    (hf : Presieve.ofArrows X f ∈ (BigHOver.zariskiPrecoverage B S hS).coverings U) :
    𝓡.modulePseudofunctor.IsStackFor (Presieve.ofArrows X f) :=
  isStackFor_of_isStackFor_opens _ f hf fun W hW => isStackFor_opens h𝓡 W hW

end AlgebraicGeometry.BigHOver.RingSheafSystem

end
