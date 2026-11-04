module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.RingTheory.WeaklyEtale.Descent

/-!
# An ind-Zariski algebra is weakly étale

An ind-Zariski `A`-algebra is a filtered colimit of `A`-algebras whose structure maps are local
isomorphisms (Tag 096N). A local isomorphism is étale, hence weakly étale, and weak étaleness
passes to filtered colimits; so an ind-Zariski algebra is weakly étale.

## Main results

* `Algebra.WeaklyEtale.of_isIndZariski`: an ind-Zariski algebra is weakly étale.

## Implementation notes

The colimit presentation is the one packaged in `Algebra.IsIndZariski` itself, read off through
`Algebra.isIndZariski_iff` so that no `ULift` intervenes. Its stages are local isomorphisms,
hence étale by the instance `Algebra.IsLocalIso.etale`, and the closure of weak étaleness under
filtered colimits is the third assertion of `weaklyEtale_of_isLocalization_etale_filteredColimit`
(Tag 092N).

## References

* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
* [Stacks Project, Tag 092N](https://stacks.math.columbia.edu/tag/092N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- An ind-Zariski algebra is weakly étale: it is a filtered colimit of local isomorphisms, local
isomorphisms are étale, and weakly étale algebras are closed under filtered colimits. -/
theorem Algebra.WeaklyEtale.of_isIndZariski {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (h : Algebra.IsIndZariski A B) : Algebra.WeaklyEtale A B := by
  obtain ⟨J, _, _, pres, hpres⟩ := Algebra.isIndZariski_iff.mp h
  exact (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} A).2.2
    J pres.diag pres.cocone pres.isColimit fun j ↦ by
      have : Algebra.IsLocalIso A (pres.diag.obj j) := hpres j
      infer_instance

end
