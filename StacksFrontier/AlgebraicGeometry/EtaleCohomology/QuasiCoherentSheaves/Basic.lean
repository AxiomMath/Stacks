module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality

/-!
# Quasi-coherence on a ringed site with a final object

Quasi-coherence of a sheaf of modules on a ringed site asks of *every* object `U` of the site a
covering `{Uᵢ → U}` on whose members the restricted module is a cokernel of a map of free
modules, that is, has a global presentation: this is Stacks 03OH, which is part (6) of
Stacks 03DL. When the site has a final object `S`, that condition need only be checked at
`U = S`. Indeed a covering of `S` covers the whole site, and a global presentation is inherited
along an arbitrary morphism of the site, so the covering of an arbitrary `U` can be taken to be
the sieve of the objects carrying a global presentation.

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_of_isTerminal` says that on a site with a
  final object `S`, a sheaf of modules is quasi-coherent if and only if the defining condition
  of Stacks 03OH holds at `U = S`.

## Implementation notes

The quasi-coherence predicate used here is `SheafOfModules.IsQuasicoherentOnSite`, the condition
of Stacks 03OH on an arbitrary site, which quantifies over every object. Mathlib's
`SheafOfModules.IsQuasicoherent` is not that condition: it is by definition the existence of a
`SheafOfModules.QuasicoherentData`, namely of a single family of objects covering the final
object together with a presentation of the module over each member. That is the shape of the
right-hand side below, so reducing the one to the other is what this remark asserts, and
`SheafOfModules.QuasicoherentData.isQuasicoherent`, which only repackages a
`QuasicoherentData` after shrinking its index type, carries no part of it.

The equivalence is deduced from the intrinsic form
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation`, which asks for
a family covering the whole site in the sense of `GrothendieckTopology.CoversTop` and therefore
needs no final object; `GrothendieckTopology.coversTop_iff_of_isTerminal` identifies covering the
whole site with covering `S`.

## References

* [Stacks Project, Tag 03OI](https://stacks.math.columbia.edu/tag/03OI)
* [Stacks Project, Tag 03OH](https://stacks.math.columbia.edu/tag/03OH)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m

add_to_stacks 03OH SheafOfModules.IsQuasicoherentOnSite

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **Stacks 03OI.** On a site with a final object `S`, the defining condition of Stacks 03OH
for quasi-coherence of a sheaf of modules need only be checked at `U = S`: the module is
quasi-coherent if and only if some covering of `S` admits a global presentation of the module
on each of its members. -/
@[stacks 03OI "quasi_coherent"]
theorem isQuasicoherentOnSite_iff_of_isTerminal (M : SheafOfModules.{m} R)
    {S : C} (hS : IsTerminal S) :
    M.IsQuasicoherentOnSite ↔
      ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ S),
        Sieve.ofArrows V f ∈ J S ∧ ∀ i, (M.over (V i)).HasGlobalPresentation := by
  refine ⟨fun hM ↦ hM.locally_hasGlobalPresentation S, ?_⟩
  rintro ⟨I, V, f, hV, hP⟩
  refine (isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation M).mpr
    ⟨{W : C | (M.over W).HasGlobalPresentation}, fun i ↦ i.1, ?_, fun i ↦ i.2⟩
  rw [J.coversTop_iff_of_isTerminal S hS]
  refine J.superset_covering ((Sieve.ofArrows_le_ofObjects V f).trans
    (Sieve.ofObjects_mono ?_)) hV
  rintro x ⟨i, rfl⟩
  exact ⟨⟨V i, hP i⟩, rfl⟩

end Stacks.SheafOfModules

end
