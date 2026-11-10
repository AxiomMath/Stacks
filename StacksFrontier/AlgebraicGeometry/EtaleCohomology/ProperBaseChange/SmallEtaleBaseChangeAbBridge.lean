module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbFinite

/-!
# The two underived étale base change comparisons of a square agree

The library attaches two underived base change comparisons `(f')⁻¹ g_* ⟶ h_* e⁻¹` to a
commutative square of schemes
```
Y --h--> X'
|e        |f'
v         v
T --g--> S
```
of abelian sheaves on the small étale sites: `Stacks.EtaleCohomology.smallEtaleBaseChangeAb`,
whose inverse image is the abstract left adjoint `CategoryTheory.Functor.sheafPullback`, and
`Stacks.EtaleCohomology.etaleAbelianBaseChange`, whose inverse image is a left Kan extension
followed by sheafification. The two are **not** transformations of the same pair of functors —
their sources and targets are built from different inverse images — so neither is the other, and
an identification of one with its base change does not read as an identification of the other
until the two are compared.

This file writes the first as a mate of the comparison of the two composite direct images, the
form in which `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange`
shows that the second being invertible forces the first to be. That is the useful direction:
Stacks 0959 and Stacks 0EYP give the invertibility of `etaleAbelianBaseChange`, through
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isIso_smallEtaleBaseChangeNatTrans`,
whereas the condition `BC(f, n, q₀)` of [Stacks, Tag 0F02] and the derived comparison of
[Stacks, Tag 0F05] are stated through `smallEtaleBaseChangeAb`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_mateEquiv_symm_pushforwardCompIso` —
  `smallEtaleBaseChangeAb` is the mate, along the two inverse-image/direct-image adjunctions of
  the *vertical* morphisms of the square, of the comparison of the two composite direct images,
  with the common composite carried as a named morphism.

## Implementation notes

Both comparisons are, after `Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm` on one side and
`Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso` on the other,
the mate of *one and the same* 2-cell: the comparison of the two composite direct images around
the square. Direct image is restriction along a functor of sites, with no left adjoint and no
sheafification in it, and the two developments spell it with the same term — `Ab` is an
abbreviation for `AddCommGrpCat`, and the coefficient universe `max (u + 1) 0` is `u + 1` — so
the 2-cell is literally shared. What differs is only which left adjoints the two adjunctions use,
and `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_isIso_mateEquiv_symm` says a mate's
invertibility does not depend on that.

The comparison is therefore not a Beck–Chevalley statement and uses no geometry: it holds for an
arbitrary commutative square, with no cartesianness and no hypothesis on the morphisms.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {S T X' Y : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)

/-- **`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is the mate of the comparison of the two
composite direct images around the square**, taken along the two inverse-image/direct-image
adjunctions of the vertical morphisms `f'` and `e`, with the common composite `Y ⟶ S` carried as
a named morphism `P`.

This is its definition with the transport along the commutativity of the square absorbed into the
two named-composite comparisons, which is what
`Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso'_eq` does. -/
public theorem smallEtaleBaseChangeAb_eq_mateEquiv_symm_pushforwardCompIso
    (w : h ≫ f' = e ≫ g) (P : Y ⟶ S) (hPe : P = e ≫ g) (hPh : P = h ≫ f') :
    smallEtaleBaseChangeAb f' g h e w =
      ((mateEquiv (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f')).symm
        (TwoSquare.mk _ _ _ _
          ((smallEtalePushforwardAbCompIso' e g P hPe).hom ≫
            (smallEtalePushforwardAbCompIso' h f' P hPh).inv))) := by
  have hiso : ((smallEtalePushforwardAbCompIso e g).trans
          ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
            (smallEtalePushforwardAbCompIso h f').symm)).hom =
      (smallEtalePushforwardAbCompIso' e g P hPe).hom ≫
        (smallEtalePushforwardAbCompIso' h f' P hPh).inv := by
    rw [smallEtalePushforwardAbCompIso'_eq, smallEtalePushforwardAbCompIso'_eq]
    simp
  refine (Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm _ _ _ _ _).trans ?_
  rw [hiso]

end Stacks.EtaleCohomology

end
