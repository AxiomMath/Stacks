module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separatedness and quasi-separatedness of a finite flat quotient

For a finite flat quotient `Stacks.Groupoids.FiniteFlatQuotient G` of a groupoid scheme over `S` —
a quotient scheme `M` over `S` together with a surjective finite locally free quotient map `U ⟶ M`
whose kernel pair is the given relation — the quotient `M` inherits quasi-separatedness and
separatedness from `U`, both over `S` and absolutely.

## Main results

* `Stacks.Groupoids.FiniteFlatQuotient.isFinite_quotientMap` and
  `Stacks.Groupoids.FiniteFlatQuotient.universallyClosed_quotientMap`: the quotient map of a finite
  flat quotient is finite, hence universally closed.
* `Stacks.Groupoids.FiniteFlatQuotient.quasiSeparated_space_hom`: if `U` is quasi-separated over
  `S`, then so is `M`.
* `Stacks.Groupoids.FiniteFlatQuotient.quasiSeparatedSpace_space`: if `U` is quasi-separated, then
  so is `M`.
* `Stacks.Groupoids.FiniteFlatQuotient.isSeparated_space_hom`: if `U` is separated over `S`, then
  so is `M`.
* `Stacks.Groupoids.FiniteFlatQuotient.isSeparated_space`: if `U` is separated, then so is `M`.

## References

* [Stacks Project, Tag 0BBM](https://stacks.math.columbia.edu/tag/0BBM)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 09MQ](https://stacks.math.columbia.edu/tag/09MQ)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The target of a surjective universally closed morphism from a separated scheme is a separated
scheme. -/
@[sga "1 V 1.6" "more general", sga "3 V 7.4" "special case"]
private theorem isSeparatedScheme_of_surjective_universallyClosed {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [UniversallyClosed f] (hX : X.IsSeparated) : Y.IsSeparated := by
  let g : (Over.mk (terminal.from X) : Over (⊤_ Scheme.{u})) ⟶ Over.mk (terminal.from Y) :=
    Over.homMk f (by subsingleton)
  have : Surjective g.left := ‹Surjective f›
  have : UniversallyClosed g.left := ‹UniversallyClosed f›
  have : IsSeparated (Over.mk (terminal.from X) : Over (⊤_ Scheme.{u})).hom :=
    hX.isSeparated_terminal_from
  exact ⟨isSeparated_of_surjective_universallyClosed g⟩

end AlgebraicGeometry

namespace Stacks.Groupoids.FiniteFlatQuotient

variable {S : Scheme.{u}} {G : GroupoidScheme S}

/-- The quotient map of a finite flat quotient is finite. -/
theorem isFinite_quotientMap (Q : FiniteFlatQuotient G) : IsFinite Q.quotientMap.left :=
  ((_root_.Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    Q.quotientMap.left).mp Q.finiteLocallyFree).1

/-- The quotient map of a finite flat quotient is universally closed, being finite. -/
theorem universallyClosed_quotientMap (Q : FiniteFlatQuotient G) :
    UniversallyClosed Q.quotientMap.left :=
  have := isFinite_quotientMap Q
  inferInstance

private instance (Q : FiniteFlatQuotient G) : Surjective Q.quotientMap.left := Q.surjective

private instance (Q : FiniteFlatQuotient G) : UniversallyClosed Q.quotientMap.left :=
  universallyClosed_quotientMap Q

/-- If the object scheme of the groupoid is quasi-separated over `S`, then so is the quotient
scheme. -/
@[stacks 0BBM "part (1), quasi-separated over the base"]
theorem quasiSeparated_space_hom (Q : FiniteFlatQuotient G)
    (hU : QuasiSeparated G.objects.hom) : QuasiSeparated Q.space.hom :=
  have := hU
  quasiSeparated_of_surjective_universallyClosed Q.quotientMap

/-- If the object scheme of the groupoid is quasi-separated, then so is the quotient scheme. -/
@[stacks 0BBM "part (2), quasi-separated"]
theorem quasiSeparatedSpace_space (Q : FiniteFlatQuotient G)
    (hU : QuasiSeparatedSpace G.objects.left) : QuasiSeparatedSpace Q.space.left :=
  have := hU
  quasiSeparatedSpace_of_surjective_universallyClosed Q.quotientMap.left

/-- If the object scheme of the groupoid is separated over `S`, then so is the quotient scheme. -/
@[stacks 0BBM "part (3), separated over the base", sga "1 V 1.6" "partial"]
theorem isSeparated_space_hom (Q : FiniteFlatQuotient G)
    (hU : IsSeparated G.objects.hom) : IsSeparated Q.space.hom :=
  have := hU
  isSeparated_of_surjective_universallyClosed Q.quotientMap

/-- If the object scheme of the groupoid is separated, then so is the quotient scheme. -/
@[stacks 0BBM "part (4), separated", sga "1 V 1.6" "partial"]
theorem isSeparated_space (Q : FiniteFlatQuotient G)
    (hU : Scheme.IsSeparated G.objects.left) : Scheme.IsSeparated Q.space.left :=
  isSeparatedScheme_of_surjective_universallyClosed Q.quotientMap.left hU

end Stacks.Groupoids.FiniteFlatQuotient

end
