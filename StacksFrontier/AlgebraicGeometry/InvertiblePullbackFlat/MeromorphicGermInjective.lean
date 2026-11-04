module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.Stalk
public import StacksFrontier.AlgebraicGeometry.RationalFunctions.Meromorphic

/-!
# A meromorphic function on an integral scheme is determined by any one of its germs

On an integral scheme the sheaf `𝒦_Y` of total quotient rings is the constant sheaf on the
function field, so its restriction maps to nonempty opens are bijective and a section of `𝒦_Y`
is determined by its germ at a single point. The penultimate paragraph of [Stacks, Tag 0BD7]
needs exactly this: the ratio of two meromorphic multipliers is pinned down by one germ, which
is what makes the locally chosen units of the base agree on overlaps.

## Main results

* `AlgebraicGeometry.bijective_totalQuotientSheaf_map_of_nonempty`: restriction along an
  inclusion of opens with the smaller one nonempty is bijective on `𝒦_Y`.
* `AlgebraicGeometry.injective_totalQuotientSheaf_germ`: hence the germ map at any point of an
  open is injective on `𝒦_Y`.

## Implementation notes

Both statements come from
`AlgebraicGeometry.bijective_totalQuotientSheaf_presheaf_map_of_genericPoints_mem`, whose two
hypotheses hold on an integral scheme and whose conclusion is restriction *from `⊤`*; an
inclusion `V ≤ U` is handled by cancelling the two restrictions from `⊤`.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (Y : Scheme.{u}) [IsIntegral Y]

/-- **Restriction from the whole space to a nonempty open is bijective on `𝒦_Y`.** The only
weakly associated point of an integral scheme is its generic point, and a nonempty open contains
it. -/
theorem bijective_totalQuotientSheaf_map_top {V : Y.Opens} (hV : Nonempty V) :
    Function.Bijective
      (Y.totalQuotientSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom :=
  bijective_totalQuotientSheaf_presheaf_map_of_genericPoints_mem
    (le_of_eq (weaklyAssociatedPointsOfScheme_eq_genericPoints Y))
    (fun U _ => Stacks.Divisors.finite_irreducibleComponents_opens Y U)
    (fun η => by
      have hη : η.1 = genericPoint Y := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using η.2
      rw [hη]
      exact ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV))

/-- **Restriction to a nonempty open is bijective on `𝒦_Y`.** A meromorphic function on an
integral scheme is constant, so nothing is lost by shrinking the open it is defined on. -/
theorem bijective_totalQuotientSheaf_map_of_nonempty {U V : Y.Opens} (h : V ≤ U)
    (hV : Nonempty V) :
    Function.Bijective (Y.totalQuotientSheaf.presheaf.map (homOfLE h).op).hom := by
  obtain ⟨v⟩ := hV
  have hU : Nonempty U := ⟨⟨v.1, h v.2⟩⟩
  have hbV := bijective_totalQuotientSheaf_map_top Y (V := V) ⟨v⟩
  have hbU := bijective_totalQuotientSheaf_map_top Y (V := U) hU
  have hcomp : ∀ x : Y.totalQuotientSheaf.presheaf.obj (op (⊤ : Y.Opens)),
      Y.totalQuotientSheaf.presheaf.map (homOfLE h).op
          (Y.totalQuotientSheaf.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x)
        = Y.totalQuotientSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op x := by
    intro x
    rw [← ConcreteCategory.comp_apply, ← Y.totalQuotientSheaf.presheaf.map_comp,
      show (homOfLE (le_top : U ≤ ⊤)).op ≫ (homOfLE h).op
        = (homOfLE (le_top : V ≤ ⊤)).op from Subsingleton.elim _ _]
  refine ⟨fun p q hpq => ?_, fun z => ?_⟩
  · obtain ⟨p', rfl⟩ := hbU.2 p
    obtain ⟨q', rfl⟩ := hbU.2 q
    exact congrArg _ (hbV.1 ((hcomp p').symm.trans (hpq.trans (hcomp q'))))
  · obtain ⟨z', rfl⟩ := hbV.2 z
    exact ⟨_, hcomp z'⟩

/-- **A meromorphic function on an integral scheme is determined by one germ.** The germ map of
`𝒦_Y` at a point of an open is injective, because every open neighbourhood of that point inside
it is nonempty. -/
theorem injective_totalQuotientSheaf_germ (U : Y.Opens) (y : Y) (hy : y ∈ U) :
    Function.Injective (Y.totalQuotientSheaf.presheaf.germ U y hy).hom := by
  intro p q hpq
  obtain ⟨W, hW, i₁, i₂, he⟩ := Y.totalQuotientSheaf.presheaf.germ_eq y hy hy p q hpq
  rw [show i₁ = homOfLE i₁.le from Subsingleton.elim _ _,
    show i₂ = homOfLE i₁.le from Subsingleton.elim _ _] at he
  exact (bijective_totalQuotientSheaf_map_of_nonempty Y i₁.le ⟨⟨y, hW⟩⟩).1 he

end AlgebraicGeometry

end
