module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibres of the inverse image of a sheaf of sets on the small étale site

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `x` be a geometric
point of `X`.  The fibre at `x` of the inverse image, along the canonical morphism of small
étale topoi of Stacks 03G8, of a sheaf of sets on the small étale site of `Y` is the fibre of
that sheaf at the image geometric point `f ∘ x`:
```
(f⁻¹ G)_x ≅ G_{f ∘ x},
```
naturally in `G`.  This is Stacks 04K2, part (4), at the universe `u` of the structure rings.

## Main definitions

* `AlgebraicGeometry.Space.chartSkyscraperIso`: the small étale skyscraper at a geometric point
  is the restriction along the comparison functor of Stacks 03G1 of the spaces-étale skyscraper
  at the same point.
* `AlgebraicGeometry.Space.spacesBaseChangeSkyscraperIso`: the direct image along base change
  carries the spaces-étale skyscraper at `x` to the one at `f ∘ x`.
* `AlgebraicGeometry.Space.smallEtaleSkyscraperIso`: the direct image along the morphism of
  Stacks 03G8 carries the small étale skyscraper at `x` to the one at `f ∘ x`.
* `AlgebraicGeometry.Space.smallEtaleInverseImageFiberIso`: the fibre comparison
  `(f⁻¹ G)_x ≅ G_{f ∘ x}`.

## Implementation notes

The fibre comparison is the right-adjoint transpose, under `CategoryTheory.conjugateIsoEquiv` of
the composite adjunction, of the skyscraper comparison, so it is the canonical comparison and not
an arbitrary isomorphism of the two functors.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- The small étale skyscraper at a geometric point is the restriction along the comparison
functor of Stacks 03G1 of the spaces-étale skyscraper at the same point. -/
def chartSkyscraperIso :
    (etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor (A := Type u) ≅
      (spacesEtaleSitePoint x).skyscraperSheafFunctor ⋙
        (comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) :=
  Iso.refl _

/-- The direct image of sheaves of sets along base change of algebraic spaces étale over the
target carries the spaces-étale skyscraper at a geometric point `x` of the source to the
spaces-étale skyscraper at the image point.  It is the transpose of
`AlgebraicGeometry.Space.spacesBaseChangeFiberIso`, by uniqueness of right adjoints. -/
def spacesBaseChangeSkyscraperIso :
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    (spacesEtaleSitePoint x).skyscraperSheafFunctor (A := Type u) ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ≅
      (spacesEtaleSitePoint (geometricPointMap f.hom x)).skyscraperSheafFunctor := by
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  set u := (spacesBaseChange B S hS f).functor with hu
  set Px := spacesEtaleSitePoint x with hPx
  set Py := spacesEtaleSitePoint (geometricPointMap f.hom x) with hPy
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal u
      (SpacesEtale.isTerminal_idObj B S hS Y)
      (isTerminal_spacesBaseChange_idObj B S hS f)
  letI : HasFiniteLimits (SpacesEtale B S hS Y) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  letI : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  letI : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  let hcover : CoverPreserving (SpacesEtale.topology B S hS Y)
      (SpacesEtale.topology B S hS X) u := CoverPreserving.of_isContinuous u _ _
  let efib : u ⋙ Px.fiber ≅ Py.fiber := spacesBaseChangeFiberIso B S hS f x
  haveI : InitiallySmall.{u} (u ⋙ Px.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  exact Px.skyscraperSheafFunctorCompSheafPushforwardContinuous u hcover (Type u) ≪≫
    Adjunction.rightAdjointUniq
      ((Px.comap u hcover).skyscraperSheafAdjunction.ofNatIsoLeft
        (Point.sheafFiberIsoOfFiberIso (Px.comap u hcover) Py efib))
      Py.skyscraperSheafAdjunction

/-- The direct image of sheaves of sets along the canonical morphism of small étale topoi of
Stacks 03G8 carries the small étale skyscraper at a geometric point `x` of the source to the
small étale skyscraper at the image point. -/
def smallEtaleSkyscraperIso :
    (etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor (A := Type u) ⋙
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward ≅
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafFunctor := by
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  exact Functor.isoWhiskerRight (chartSkyscraperIso B S hS x) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleRingedToposHom_pushforward B S hS f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (spacesBaseChangeSkyscraperIso B S hS f x) _ ≪≫
    (chartSkyscraperIso B S hS (geometricPointMap f.hom x)).symm

/-- The fibre at a geometric point `x` of `X` of the inverse image along the canonical morphism
of small étale topoi of Stacks 03G8 of a sheaf of sets on the small étale site of `Y` is the
fibre of that sheaf at the image point `f ∘ x`, naturally in the sheaf.

It is the right-adjoint transpose of `AlgebraicGeometry.Space.smallEtaleSkyscraperIso`. -/
@[stacks 04K2 "part (4), for sheaves of sets at the universe of the structure rings"]
def smallEtaleInverseImageFiberIso :
    (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber (A := Type u) ≅
      (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage ⋙
        (etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u) :=
  (conjugateIsoEquiv
      ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.comp
        (etaleSitePoint B S hS X.1 x X.2).skyscraperSheafAdjunction)
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafAdjunction).symm
    (smallEtaleSkyscraperIso B S hS f x)

end AlgebraicGeometry.Space

end

end
