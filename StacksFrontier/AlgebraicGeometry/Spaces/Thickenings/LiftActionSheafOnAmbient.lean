module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianPushforwardComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# The sheaf acting on the lifts, read on the ambient space of the thickening

Let `G ⊂ X'` be a thickening of algebraic spaces over a scheme `S`, write `X` for the subspace,
and let `a : X ⟶ Y` be a morphism over a base `B`.  The sheaf acting on the lifts of `a` is
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})`, which is
`AlgebraicGeometry.Space.liftActionSheaf`; it lives on the small étale site of `X`.  The sheaf
of lifts it acts on lives on the site of `X'`.  This file carries the acting sheaf over to the
site of `X'`, which is what makes the two comparable.

Nothing about the acting sheaf is used: the passage is Equation [Stacks Project, Tag 05ZL] for
sheaves of abelian groups, `AlgebraicGeometry.Space.spacesEtaleAbelianSheafEquiv_of_isThickening`,
together with the comparison equivalence of [Stacks Project, Tag 03G1] between the small étale
and spaces-étale sites, `AlgebraicGeometry.Space.smallEtaleAbelianSheafComparisonEquiv`, and the
forgetful functor from sheaves of modules to sheaves of abelian groups.  So the construction
applies to any sheaf of modules on the subspace, and that is how it is stated; the acting sheaf
of [Stacks Project, Tag 061D] is the instance named at the end.

## Main definitions

* `AlgebraicGeometry.Space.chartAbelianSheafOnAmbient`: a sheaf of modules on the small étale
  site of the subspace of a thickening, read as a sheaf of abelian groups on the small étale
  site of the ambient space.
* `AlgebraicGeometry.Space.abelianSheafOnAmbient`: the same read on the *spaces-étale* site of
  the ambient space.
* `AlgebraicGeometry.Space.liftActionAbelianSheaf`: **the acting sheaf of
  [Stacks Project, Tag 061D] read on the spaces-étale site of the ambient space**, which is the
  shape `AlgebraicGeometry.Space.LiftDerivationAction` takes its acting sheaf `Θ` in.

## Main results

* `AlgebraicGeometry.Space.chartAbelianSheafOnAmbient_obj_obj`: **the sections of the
  chart-level reading over an étale chart `V` of the ambient space are the sections of the given
  sheaf over the base-changed chart `V ×_{X'} X`** — an equality, not a comparison.  For the
  acting sheaf of [Stacks Project, Tag 061D] this says that the sections over `V` are the
  `𝒪`-linear maps `a^*Ω_{Y/B} ⟶ 𝒞_{X/X'}` over `V ×_{X'} X`, which is what the action of
  [Stacks Project, Tag 061C] has to produce.

  It is the abelian reading of
  `AlgebraicGeometry.Space.smallEtaleRingSheafEquiv_inverse_obj_obj`, and holds for the same
  reason: the inverse of a dense-subsite equivalence is restriction along the inclusion of the
  subsite, which is precomposition.

## Implementation notes

The two readings are built in that order, the spaces-étale one from the chart-level one, rather
than both from Equation [Stacks Project, Tag 05ZL] in its spaces-étale form
`AlgebraicGeometry.Space.spacesEtaleAbelianSheafEquiv_of_isThickening`.  Composing that form
with the comparison equivalence of the subspace would compose a quasi-inverse with its own
functor and leave the round trip in the term; the chart-level equivalence is the inner factor of
the spaces-étale one by construction, so this route is the same transport with nothing extra.

**No section formula is claimed for the spaces-étale reading.**  The inverse of the comparison
equivalence is a quasi-inverse supplied by the equivalence instance, not a restriction functor,
so its sections over an object of the spaces-étale site are determined only up to the unit
isomorphism.  The chart-level formula is the one that is an equality, and it is the one a
consumer should go through.

## References

* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL), the identification of
  the two étale topoi.
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1), the comparison of the
  small étale and spaces-étale sites.
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D), the acting sheaf.
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C), the action this serves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {X' : AlgebraicSpaces C S hS} {G : Subfunctor X'.1}

/-- **A sheaf of modules on the subspace of a thickening, read as a sheaf of abelian groups on
the small étale site of the ambient space.**  The two steps are the forgetful functor to sheaves
of abelian groups and Equation [Stacks Project, Tag 05ZL] for abelian sheaves in its chart form,
`AlgebraicGeometry.Space.smallEtaleAbelianSheafEquiv_of_isThickening`. -/
def chartAbelianSheafOnAmbient (hG : IsThickening C S hS X' G)
    (M : Modules.{u, u + 1} C S hS (IsThickening.space C S hS hG).1
      (IsThickening.space C S hS hG).2) :
    Sheaf (SmallEtale.topology C S hS X'.1) AddCommGrpCat.{u + 1} :=
  (smallEtaleAbelianSheafEquiv_of_isThickening C S hS hG).inverse.obj
    ((SheafOfModules.toSheaf _).obj M)

/-- **The sections of the chart-level reading over an étale chart `V` of the ambient space are
the sections of the given sheaf over the base-changed chart `V ×_{X'} X`.**

The inverse of a dense-subsite equivalence is restriction along the inclusion of the subsite,
which is precomposition; so this is an equality and not a comparison.  It is the abelian reading
of `AlgebraicGeometry.Space.smallEtaleRingSheafEquiv_inverse_obj_obj`. -/
theorem chartAbelianSheafOnAmbient_obj_obj (hG : IsThickening C S hS X' G)
    (M : Modules.{u, u + 1} C S hS (IsThickening.space C S hS hG).1
      (IsThickening.space C S hS hG).2) (V : (SmallEtale C S hS X'.1)ᵒᵖ) :
    (chartAbelianSheafOnAmbient C S hS hG M).obj.obj V =
      M.val.presheaf.obj (op ((thickeningChartBaseChange C S hS hG).obj V.unop)) := rfl

/-- **A sheaf of modules on the subspace of a thickening, read as a sheaf of abelian groups on
the spaces-étale site of the ambient space.**  This is
`AlgebraicGeometry.Space.chartAbelianSheafOnAmbient` carried along the comparison equivalence of
[Stacks Project, Tag 03G1] between the small étale and spaces-étale sites of `X'`. -/
def abelianSheafOnAmbient (hG : IsThickening C S hS X' G)
    (M : Modules.{u, u + 1} C S hS (IsThickening.space C S hS hG).1
      (IsThickening.space C S hS hG).2) :
    Sheaf (SpacesEtale.topology C S hS X') AddCommGrpCat.{u + 1} :=
  (smallEtaleAbelianSheafComparisonEquiv C S hS X').inverse.obj
    (chartAbelianSheafOnAmbient C S hS hG M)

variable {Y B : AlgebraicSpaces C S hS}

/-- **The acting sheaf of [Stacks Project, Tag 061D], read on the spaces-étale site of the
ambient space of the thickening.**  This is
`AlgebraicGeometry.Space.liftActionSheaf`, the internal hom
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` on the small étale site of the subspace `X`, carried to
the spaces-étale site of `X'` by `AlgebraicGeometry.Space.abelianSheafOnAmbient`.

It is on the site of `X'` that the sheaf of lifts of [Stacks Project, Tag 061A] lives, so it is
there that the action of [Stacks Project, Tag 061C] has to be read; its underlying presheaf
`(liftActionAbelianSheaf …).obj` is the shape
`AlgebraicGeometry.Space.LiftDerivationAction` takes its acting sheaf `Θ` in. -/
@[stacks 061D "the acting sheaf carried to the spaces-etale site of the ambient space of the \
thickening, which is the site the sheaf of lifts lives on"]
def liftActionAbelianSheaf (hG : IsThickening C S hS X' G) (q : Y ⟶ B)
    (a : IsThickening.space C S hS hG ⟶ Y) :
    Sheaf (SpacesEtale.topology C S hS X') AddCommGrpCat.{u + 1} :=
  abelianSheafOnAmbient C S hS hG (liftActionSheaf C S hS ⟨G, hG.1⟩ q a)

end AlgebraicGeometry.Space

end
