module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageFiberType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The small étale skyscraper comparison of sheaves of sets, on sections

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `x` be a geometric
point of `X`.  This file computes on sections the skyscraper comparisons
`AlgebraicGeometry.Space.spacesBaseChangeSkyscraperIso` and
`AlgebraicGeometry.Space.smallEtaleSkyscraperIso` of sheaves of sets underlying the fibre
comparison of Stacks 04K2, part (4): over an étale chart of `Y` and at a lift of the image point
`f ∘ x`, each is the projection to the lift of `x` that the cartesian square of Stacks 03G2,
part (1) assigns to the lift downstairs.

## Main results

* `AlgebraicGeometry.Space.spacesBaseChangeSkyscraperIso_hom_app_π`: the projections of the
  base-change comparison.
* `AlgebraicGeometry.Space.smallEtaleSkyscraperIso_hom_app_π`: the projections of the small
  étale comparison.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- **The base-change skyscraper comparison of sheaves of sets, on sections.**  Over an
algebraic space `V` étale over `Y` and at a lift `v` of the image point `f ∘ x`, the component
of `AlgebraicGeometry.Space.spacesBaseChangeSkyscraperIso` is the projection to the lift of `x`
into `X ×_Y V` that the cartesian square of Stacks 03G2, part (1) assigns to `v`. -/
theorem spacesBaseChangeSkyscraperIso_hom_app_π (M : Type u) (V : SpacesEtale B S hS Y)
    (v : (spacesEtaleSitePoint (geometricPointMap f.hom x)).fiber.obj V) :
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    ((spacesBaseChangeSkyscraperIso B S hS f x).hom.app M).hom.app (op V) ≫
        Pi.π (fun _ : (spacesEtaleSitePoint (geometricPointMap f.hom x)).fiber.obj V => M) v =
      Pi.π (fun _ : (spacesEtaleSitePoint x).fiber.obj
        ((spacesBaseChange B S hS f).functor.obj V) => M)
        ((spacesBaseChangeFiberIso B S hS f x).inv.app V v) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (spacesBaseChange B S hS f).functor :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal _
      (SpacesEtale.isTerminal_idObj B S hS Y)
      (isTerminal_spacesBaseChange_idObj B S hS f)
  have : HasFiniteLimits (SpacesEtale B S hS Y) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits (spacesBaseChange B S hS f).functor :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  have : RepresentablyFlat (spacesBaseChange B S hS f).functor :=
    flat_of_preservesFiniteLimits _
  let efib : (spacesBaseChange B S hS f).functor ⋙ (spacesEtaleSitePoint x).fiber ≅
      (spacesEtaleSitePoint (geometricPointMap f.hom x)).fiber :=
    spacesBaseChangeFiberIso B S hS f x
  have : InitiallySmall.{u}
      ((spacesBaseChange B S hS f).functor ⋙ (spacesEtaleSitePoint x).fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  exact Point.comapSkyscraperPushforward_hom_app_π (spacesEtaleSitePoint x)
    (spacesEtaleSitePoint (geometricPointMap f.hom x)) (spacesBaseChange B S hS f).functor
    (CoverPreserving.of_isContinuous _ _ _) (spacesBaseChangeFiberIso B S hS f x) M V v

/-- **The small étale skyscraper comparison of sheaves of sets, on sections.**  Over an étale
scheme chart `V` of `Y` and at a lift `q` of the image point, the component of
`AlgebraicGeometry.Space.smallEtaleSkyscraperIso` is the direct-image comparison of Stacks 03G8
followed by the projection to the lift of `x` into `X ×_Y V` that the cartesian square of
Stacks 03G2, part (1) assigns to `q`. -/
theorem smallEtaleSkyscraperIso_hom_app_π (M : Type u) (V : SmallEtale B S hS Y.1)
    (q : (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).fiber.obj V) :
    ((smallEtaleSkyscraperIso B S hS f x).hom.app M).hom.app (op V) ≫
        Pi.π (fun _ : (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).fiber.obj V =>
          M) q =
      ((smallEtaleRingedToposHom_pushforward B S hS f).hom.app
            ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M)).hom.app (op V) ≫
        Pi.π (fun _ : (spacesEtaleSitePoint x).fiber.obj (chartBaseChange B S hS f V) => M)
          ((spacesBaseChangeFiberIso B S hS f x).inv.app
            ((comparisonFunctor B S hS Y).obj V) q) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have hπ := spacesBaseChangeSkyscraperIso_hom_app_π B S hS f x M
    ((comparisonFunctor B S hS Y).obj V) q
  have hβ : (smallEtaleSkyscraperIso B S hS f x).hom.app M =
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app
          ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M) ≫
        ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
          ((spacesBaseChangeSkyscraperIso B S hS f x).hom.app M) := by
    have h0 : (smallEtaleSkyscraperIso B S hS f x).hom.app M =
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
              (𝟙 (((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor
                (A := Type u)).obj M)) ≫
            𝟙 _ ≫
            (smallEtaleRingedToposHom_pushforward B S hS f).hom.app
              ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M) ≫
            𝟙 _ ≫
            ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
                (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
              ((spacesBaseChangeSkyscraperIso B S hS f x).hom.app M) ≫ 𝟙 _ := rfl
    rw [h0, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
      Category.id_comp, Category.comp_id]
    rfl
  rw [hβ, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  exact (Category.assoc _ _ _).trans (congrArg (fun m =>
    ((smallEtaleRingedToposHom_pushforward B S hS f).hom.app
      ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M)).hom.app (op V) ≫ m) hπ)

end AlgebraicGeometry.Space

end

end
