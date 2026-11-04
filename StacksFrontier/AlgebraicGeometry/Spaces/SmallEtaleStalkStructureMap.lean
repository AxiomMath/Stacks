module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependence

/-!
# The germ action of the fibre of the structure map on the small étale site

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `x` be a geometric
point of `X`, with image `f ∘ x`. The fibre at `x` of the inverse-image form of the structure map
of the canonical morphism of small étale ringed topoi of Stacks 03G8, read through the fibre
comparison `AlgebraicGeometry.Space.smallEtaleInverseImageFiberRingIso`, is a homomorphism of the
structure-sheaf fibres `(𝒪_Y)_{f ∘ x} ⟶ (𝒪_X)_x`. This file computes its action on germs, and
shows that, transported to the étale local rings by the comparison of Stacks 05VQ, it is the
canonical homomorphism of étale local rings of Stacks 04NG.

## Main definitions

* `AlgebraicGeometry.Space.stalkStructureMap`: the fibre at `x` of the inverse-image structure
  map, as a homomorphism out of the structure-sheaf fibre at the image point.

## Main results

* `AlgebraicGeometry.Space.stalkStructureMap_toPresheafFiber`: the germ formula — the fibre of
  the structure map carries the germ at a lift of `f ∘ x` of a regular function on an étale
  chart `V` of `Y` to the germ at a compatible lift of `x` of its pullback along any
  commutative diagram of étale scheme charts over `f` with lower chart `V`.
* `AlgebraicGeometry.Space.isEtaleLocalRingMap_stalkStructureMap`: the transported fibre of the
  structure map pulls germs back in every compatible diagram of étale scheme charts, that is,
  it satisfies the germ characterization `AlgebraicGeometry.Space.IsEtaleLocalRingMap` of the
  homomorphism induced by `f`.
* `AlgebraicGeometry.Space.stalkStructureMapAsEtaleLocalRingMap_eq`: the transported fibre is the
  canonical homomorphism of étale local rings of Stacks 04NG.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

universe u

namespace CategoryTheory.Adjunction

variable {C : Type*} {D : Type*} [Category C] [Category D]

/-- The mate, under two adjunctions, of an isomorphism of right adjoints: transposing a map out
of the second left adjoint precomposed with the conjugate isomorphism is transposing it through
the first adjunction and then postcomposing with the isomorphism. -/
theorem mate_homEquiv {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : R₁ ≅ R₂) {A : C} {M : D} (k : L₁.obj A ⟶ M) :
    adj₂.homEquiv A M (((conjugateIsoEquiv adj₁ adj₂).symm β).hom.app A ≫ k) =
      adj₁.homEquiv A M k ≫ β.hom.app M := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    conjugateIsoEquiv_symm_apply_hom, ← unit_conjugateEquiv_symm, Category.assoc,
    ← β.hom.naturality, ← Category.assoc]
  rfl

/-- A criterion for a map out of a composite left adjoint to be the transpose of a given one, in
terms of the conjugate isomorphism of a composite adjunction. -/
theorem conjugate_comp {E : Type*} [Category E] {F : C ⥤ D} {G : D ⥤ C} {P : D ⥤ E} {Q : E ⥤ D}
    {R : C ⥤ E} {T : E ⥤ C} (adjF : F ⊣ G) (adjP : P ⊣ Q) (adjR : R ⊣ T) (β : Q ⋙ G ≅ T)
    {A : C} {B : D} {M : E} (k : A ⟶ G.obj B) (a : P.obj B ⟶ M) (b : R.obj A ⟶ M)
    (h : k ≫ G.map (adjP.homEquiv B M a) ≫ β.hom.app M = adjR.homEquiv A M b) :
    ((conjugateIsoEquiv (adjF.comp adjP) adjR).symm β).hom.app A ≫
        P.map ((adjF.homEquiv A B).symm k) ≫ a = b := by
  apply (adjR.homEquiv A M).injective
  rw [mate_homEquiv, Adjunction.comp_homEquiv]
  show adjF.homEquiv A (Q.obj M)
    (adjP.homEquiv (F.obj A) M (P.map ((adjF.homEquiv A B).symm k) ≫ a)) ≫
      β.hom.app M = adjR.homEquiv A M b
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Category.assoc]
  exact h

end CategoryTheory.Adjunction

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type*} [Category C] {J : GrothendieckTopology C} (Φ : Point.{u} J)
  {A : Type*} [Category A] [Limits.HasProducts.{u} A] [Limits.HasColimitsOfSize.{u, u} A]

omit [Limits.HasColimitsOfSize.{u, u} A] in
/-- Restriction in a skyscraper presheaf is reindexing of the product: it carries the factor
of a lift of the point to the factor of the image of that lift. -/
theorem skyscraperPresheaf_map_π {U V : C} (k : U ⟶ V) (M : A) (w : Φ.fiber.obj U) :
    (Φ.skyscraperPresheaf M).map k.op ≫ Limits.Pi.π (fun _ : Φ.fiber.obj U => M) w =
      Limits.Pi.π (fun _ : Φ.fiber.obj V => M) (Φ.fiber.map k w) :=
  (Limits.Pi.map'_comp_π _ _ w).trans (Category.comp_id _)

/-- The unit of the skyscraper adjunction at a sheaf is germ formation: its component over an
object of the site, followed by the projection to the factor of a lift of the point, is the
germ map at that lift. -/
theorem skyscraperSheafAdjunction_unit_π (F : Sheaf J A) (U : C) (w : Φ.fiber.obj U) :
    (Φ.skyscraperSheafAdjunction.homEquiv F (Φ.sheafFiber.obj F) (𝟙 _)).hom.app (op U) ≫
        Limits.Pi.π (fun _ : Φ.fiber.obj U => Φ.sheafFiber.obj F) w =
      Φ.toPresheafFiber U w F.obj := by
  have h1 : (Φ.skyscraperSheafAdjunction.homEquiv F (Φ.sheafFiber.obj F) (𝟙 _)).hom =
      Φ.skyscraperPresheafHomEquiv (𝟙 (Φ.sheafFiber.obj F)) :=
    skyscraperSheafAdjunction_homEquiv_apply_hom Φ (𝟙 _)
  rw [h1]
  exact (skyscraperPresheafHomEquiv_app_π Φ (𝟙 _) U w).trans (Category.comp_id _)

/-- Transposing a homomorphism into a skyscraper sheaf across the skyscraper adjunction reads
germs off its components: the germ map at a lift of the point, followed by the transpose, is
the component of the homomorphism followed by the projection to the factor of that lift. -/
theorem toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm (F : Sheaf J A) (M : A)
    (c : F ⟶ Φ.skyscraperSheafFunctor.obj M) (U : C) (w : Φ.fiber.obj U) :
    Φ.toPresheafFiber U w F.obj ≫ (Φ.skyscraperSheafAdjunction.homEquiv F M).symm c =
      c.hom.app (op U) ≫ Limits.Pi.π (fun _ : Φ.fiber.obj U => M) w := by
  have h1 : (Φ.skyscraperSheafAdjunction.homEquiv F M).symm c =
      Φ.skyscraperPresheafHomEquiv.symm c.hom :=
    skyscraperSheafAdjunction_homEquiv_symm_apply Φ c
  rw [h1]
  exact toPresheafFiber_skyscraperPresheafHomEquiv_symm Φ c.hom U w

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-! ### The chart correspondence against an arbitrary presentation of the source -/

/-- **The chartwise description of a morphism of sheaves over the correspondence of Stacks
03G8.** Applying a map out of a sheaf on the small étale site of `X` to the value of an `f`-map
of Stacks 03G3 on a diagram of charts is restricting the corresponding map of spaces-étale
sheaves along the diagram. -/
theorem chartCorrespondence_postcomp
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (a : F ⟶ (smallEtaleComparisonRestriction B S hS X).obj H)
    (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶ chartBaseChange B S hS f d.V)
    (hh : HEq (((SpacesEtale.toSpaces B S hS X).map h) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom
      (yoneda.map d.g))
    (s : G.obj.obj (op d.V)) :
    a.hom.app (op d.U) (ξ.app d s) =
      H.obj.map h.op
        ((fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map a ≫
          (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H).hom.app (op d.V) s) := by
  obtain ⟨H₀, i, b, hcomp⟩ :
      ∃ (H₀ : Sheaf (SpacesEtale.topology B S hS X) (Type u))
        (i : F ≅ (smallEtaleComparisonRestriction B S hS X).obj H₀) (b : H₀ ⟶ H),
        i.hom ≫ (smallEtaleComparisonRestriction B S hS X).map b = a := by
    refine ⟨(smallEtaleComparisonRestriction B S hS X).objPreimage F,
      ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm,
      (smallEtaleComparisonRestriction B S hS X).preimage
        (((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫ a), ?_⟩
    rw [(smallEtaleComparisonRestriction B S hS X).map_preimage, Iso.hom_inv_id_assoc]
  have hc := fMapEquivPushforwardHom_ringUniverse_chart B S hS f F G H₀ i ξ d h hh s
  have hleft : a.hom.app (op d.U) (ξ.app d s) =
      b.hom.app (op ((comparisonFunctor B S hS X).obj d.U))
        (i.hom.hom.app (op d.U) (ξ.app d s)) :=
    (congrArg (fun k : F ⟶ (smallEtaleComparisonRestriction B S hS X).obj H =>
      k.hom.app (op d.U) (ξ.app d s)) hcomp).symm
  have hnat := NatTrans.naturality_apply b.hom h.op
    ((fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H₀).hom.app (op d.V) s)
  refine hleft.trans ((congrArg (b.hom.app (op ((comparisonFunctor B S hS X).obj d.U))) hc).trans
    (hnat.trans (congrArg (H.obj.map h.op) ?_)))
  have he : fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H₀ ≫
        (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
          (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map b =
      fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map a ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H := by
    rw [← (smallEtaleRingedToposHom_pushforward B S hS f).hom.naturality b,
      CategoryTheory.Functor.comp_map, ← Category.assoc
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom),
      ← CategoryTheory.Functor.map_comp, hcomp]
  exact congrArg (fun k => k.hom.app (op d.V) s) he

/-- **The chartwise formula for a map out of the target structure sheaf** obtained by pushing a
map out of the source structure sheaf forward along the canonical morphism of small étale
ringed topoi: restricting it along a diagram of charts is pullback of regular functions along
the diagram's morphism of schemes, followed by the original map. -/
theorem structureSheafHom_postcomp_chart
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u})
    (α : (smallEtaleRingedTopos B S hS X).O ⟶
      ((comparisonFunctor B S hS X).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).obj H)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶ chartBaseChange B S hS f d.V)
    (hh : HEq (((SpacesEtale.toSpaces B S hS X).map h) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom
      (yoneda.map d.g))
    (s : ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
      (smallEtaleRingedTopos B S hS Y).O).obj.obj (op d.V)) :
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    H.obj.map h.op
        (((smallEtaleRingedToposHom B S hS f).fSharp ≫
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map α ≫
          (smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app H).hom.app (op d.V) s) =
      α.hom.app (op d.U) (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have hc := chartCorrespondence_postcomp B S hS f
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O)
    ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
    (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS X) H)
    ((smallEtaleRingedTopos B S hS X).forgetRing.map α)
    ((fMapEquivPushforwardHom_ringUniverse B S hS f
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O)
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
          (smallEtaleRingedTopos B S hS Y).O)).symm
      ((smallEtaleRingedTopos B S hS Y).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharp))
    d h hh s
  have hd : ((fMapEquivPushforwardHom_ringUniverse B S hS f
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O)
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
          (smallEtaleRingedTopos B S hS Y).O)).symm
      ((smallEtaleRingedTopos B S hS Y).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharp)).app d s =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s :=
    smallEtaleRingedToposHom_chart B S hS f d s
  have he : fMapEquivPushforwardHom_ringUniverse B S hS f
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O)
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
      ((fMapEquivPushforwardHom_ringUniverse B S hS f
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O)
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
            (smallEtaleRingedTopos B S hS Y).O)).symm
        ((smallEtaleRingedTopos B S hS Y).forgetRing.map
          (smallEtaleRingedToposHom B S hS f).fSharp)) =
      (smallEtaleRingedTopos B S hS Y).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharp :=
    Equiv.apply_symm_apply _ _
  rw [hd, he] at hc
  have h1 : (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map α) =
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
        ((smallEtaleRingedTopos B S hS X).forgetRing.map α) :=
    MorphismOfTopoi.pushforwardRing_map_forget _ α
  have h2 := smallEtaleRingedToposHom_pushforwardRing_forget B S hS f H
  refine Eq.trans (congrArg (fun z => H.obj.map h.op z) ?_) hc.symm
  refine Eq.trans (congrArg (fun k => k.hom.app (op d.V)
      (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map α).hom.app (op d.V)
        ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op d.V) s))) h2) ?_
  exact congrArg (fun w => ((smallEtaleRingedToposHom_pushforward B S hS f).hom.app
      (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS X) H)).hom.app (op d.V) w)
    (congrArg (fun k => k.hom.app (op d.V)
      ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op d.V) s)) h1)

/-! ### The germ action of the fibre of the structure map -/

variable (x : GeometricPoint B S hS X.1)

/-- **The small étale skyscraper comparison on sections.** Over an étale scheme chart `V` of
`Y` and at a lift `q` of the image point, the component of
`AlgebraicGeometry.Space.smallEtaleSkyscraperRingIso` is the direct-image comparison of
Stacks 03G8 followed by the projection to the lift of `x` into `X ×_Y V` that the cartesian
square of Stacks 03G2, part (1) assigns to `q`. -/
theorem smallEtaleSkyscraperRingIso_hom_app_π (M : CommRingCat.{u})
    (V : SmallEtale B S hS Y.1)
    (q : (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).fiber.obj V) :
    ((smallEtaleSkyscraperRingIso B S hS f x).hom.app M).hom.app (op V) ≫
        Pi.π (fun _ : (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).fiber.obj V =>
          M) q =
      ((smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app
            ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M)).hom.app (op V) ≫
        Pi.π (fun _ : (spacesEtaleSitePoint x).fiber.obj (chartBaseChange B S hS f V) => M)
          ((spacesBaseChangeFiberIso B S hS f x).inv.app
            ((comparisonFunctor B S hS Y).obj V) q) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have hπ := spacesBaseChangeSkyscraperRingIso_hom_app_π B S hS f x M
    ((comparisonFunctor B S hS Y).obj V) q
  have hβ : (smallEtaleSkyscraperRingIso B S hS f x).hom.app M =
      (smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app
          ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M) ≫
        ((comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
          ((spacesBaseChangeSkyscraperRingIso B S hS f x).hom.app M) := by
    have h0 : (smallEtaleSkyscraperRingIso B S hS f x).hom.app M =
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
              (𝟙 (((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor
                (A := CommRingCat.{u})).obj M)) ≫
            𝟙 _ ≫
            (smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app
              ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M) ≫
            𝟙 _ ≫
            ((comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
                (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
              ((spacesBaseChangeSkyscraperRingIso B S hS f x).hom.app M) ≫ 𝟙 _ := rfl
    rw [h0, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
      Category.id_comp, Category.comp_id]
    rfl
  rw [hβ, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  exact (Category.assoc _ _ _).trans (congrArg (fun m =>
    ((smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app
      ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj M)).hom.app (op V) ≫ m) hπ)

/-- The structure-sheaf fibre at a geometric point, as an object of `CommRingCat`. -/
abbrev geometricStalkRing : CommRingCat.{u} :=
  ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u})).obj
    (smallEtaleRingedTopos B S hS X).O

/-- The unit of the skyscraper adjunction at the structure sheaf: germ formation at `x`, read
as a homomorphism into the skyscraper with value the structure-sheaf fibre. -/
abbrev stalkSkyscraperUnit :
    (smallEtaleRingedTopos B S hS X).O ⟶
      (etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor.obj
        (geometricStalkRing B S hS x) :=
  ((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafAdjunction (A := CommRingCat.{u})).homEquiv
    (smallEtaleRingedTopos B S hS X).O (geometricStalkRing B S hS x) (𝟙 _)

/-- The spaces-étale skyscraper sheaf at `x` with value the structure-sheaf fibre. -/
abbrev stalkSkyscraperSheaf : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u} :=
  (spacesEtaleSitePoint x).skyscraperSheafFunctor.obj (geometricStalkRing B S hS x)

/-- The homomorphism from `𝒪_Y` to the skyscraper sheaf at `f ∘ x` with value the
structure-sheaf fibre at `x`: the structure map, followed by the direct image of germ formation at
`x` and the skyscraper comparison of Stacks 03G8. -/
abbrev stalkStructureSkyscraperHom :
    (smallEtaleRingedTopos B S hS Y).O ⟶
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafFunctor.obj
        (geometricStalkRing B S hS x) :=
  (smallEtaleRingedToposHom B S hS f).fSharp ≫
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
      (stalkSkyscraperUnit B S hS x) ≫
    (smallEtaleSkyscraperRingIso B S hS f x).hom.app (geometricStalkRing B S hS x)

/-- **The fibre of the structure map at a geometric point.** The fibre at `x` of the
inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of the canonical morphism of small
étale ringed topoi of Stacks 03G8, read as a homomorphism out of the structure-sheaf fibre at
the image point `f ∘ x` by the fibre comparison
`AlgebraicGeometry.Space.smallEtaleInverseImageFiberRingIso`. -/
def stalkStructureMap :
    ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber
        (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O ⟶
      ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O :=
  (smallEtaleInverseImageFiberRingIso B S hS f x).hom.app (smallEtaleRingedTopos B S hS Y).O ≫
    ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u})).map
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage

/-- The fibre of the structure map is the transpose, across the skyscraper adjunction at the
image point, of the direct image of the unit of the skyscraper adjunction at `x` followed by
the skyscraper comparison of Stacks 03G8. -/
theorem stalkStructureMap_eq :
    stalkStructureMap B S hS f x =
      (((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafAdjunction
            (A := CommRingCat.{u})).homEquiv (smallEtaleRingedTopos B S hS Y).O
          (geometricStalkRing B S hS x)).symm
        (stalkStructureSkyscraperHom B S hS f x) := by
  refine Eq.trans (congrArg
    (fun m => (smallEtaleInverseImageFiberRingIso B S hS f x).hom.app
      (smallEtaleRingedTopos B S hS Y).O ≫ m) (Category.comp_id _).symm) ?_
  exact Adjunction.conjugate_comp (smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction
    ((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafAdjunction (A := CommRingCat.{u}))
    ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafAdjunction
      (A := CommRingCat.{u}))
    (smallEtaleSkyscraperRingIso B S hS f x) (smallEtaleRingedToposHom B S hS f).fSharp (𝟙 _) _
    (Equiv.apply_symm_apply _ _).symm

/-- The lift of `x` into the cartesian base change `X ×_Y V` attached to a diagram of étale
scheme charts over `f` and to compatible lifts of `x` and of its image: it is the one the
cartesian square of Stacks 03G2, part (1) assigns to the lift downstairs. -/
theorem spacesBaseChangeFiberIso_inv_app (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (p : GeometricFiber B S hS X.1 x d.U)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) d.V) (hpq : p.1 ≫ d.g = q.1) :
    (spacesBaseChangeFiberIso B S hS f x).inv.app ((comparisonFunctor B S hS Y).obj d.V) q =
      (spacesGeometricFiber x).map (baseChangeArrowOfChartDiagram B S hS f d) p := by
  have hmap : (spacesBaseChangeFiberMap B S hS f x).app
      ((comparisonFunctor B S hS Y).obj d.V)
      ((spacesGeometricFiber x).map (baseChangeArrowOfChartDiagram B S hS f d) p) = q := by
    refine Subtype.ext ?_
    show ((SpacesEtale.toSpaces B S hS X).map (baseChangeArrowOfChartDiagram B S hS f d) ≫
      (spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj d.V)).hom.app (op x.val.siteObject) p.1 = q.1
    rw [yoneda_map_baseChangeArrowOfChartDiagram]
    exact hpq
  conv_lhs => rw [← hmap]
  exact ConcreteCategory.congr_hom ((spacesBaseChangeFiberIso B S hS f x).hom_inv_id_app
    ((comparisonFunctor B S hS Y).obj d.V)) _

/-- **The germ formula for the fibre of the structure map.** Given a commutative diagram of
étale scheme charts over `f` and compatible lifts of `x` and of its image into its two charts,
the fibre at `x` of the inverse-image structure map carries the germ of a regular function on
the lower chart to the germ of its pullback along the diagram's morphism of schemes. -/
theorem stalkStructureMap_toPresheafFiber (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (p : GeometricFiber B S hS X.1 x d.U)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) d.V) (hpq : p.1 ≫ d.g = q.1)
    (s : (structurePresheaf B S hS Y.1).obj (op d.V)) :
    stalkStructureMap B S hS f x
        ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber d.V q
          (smallEtaleRingedTopos B S hS Y).O.obj s) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber d.U p
        (smallEtaleRingedTopos B S hS X).O.obj
        (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have hgerm : (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber d.V q
        (smallEtaleRingedTopos B S hS Y).O.obj ≫ stalkStructureMap B S hS f x =
      (stalkStructureSkyscraperHom B S hS f x).hom.app (op d.V) ≫
        Pi.π (fun _ : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) d.V =>
          geometricStalkRing B S hS x) q := by
    rw [stalkStructureMap_eq]
    exact Point.toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
      (smallEtaleRingedTopos B S hS Y).O (geometricStalkRing B S hS x)
      (stalkStructureSkyscraperHom B S hS f x) d.V q
  refine Eq.trans (ConcreteCategory.congr_hom hgerm s) ?_
  refine Eq.trans (ConcreteCategory.congr_hom
    (smallEtaleSkyscraperRingIso_hom_app_π B S hS f x (geometricStalkRing B S hS x) d.V q)
    (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
        (stalkSkyscraperUnit B S hS x)).hom.app (op d.V)
      ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op d.V) s))) ?_
  rw [spacesBaseChangeFiberIso_inv_app B S hS f x d p q hpq]
  refine Eq.trans (ConcreteCategory.congr_hom (Point.skyscraperPresheaf_map_π
    (spacesEtaleSitePoint x) (baseChangeArrowOfChartDiagram B S hS f d)
    (geometricStalkRing B S hS x) p) _).symm ?_
  refine Eq.trans (congrArg (fun z =>
    Pi.π (fun _ : GeometricFiber B S hS X.1 x d.U => geometricStalkRing B S hS x) p z)
    (structureSheafHom_postcomp_chart B S hS f (stalkSkyscraperSheaf B S hS x)
      (stalkSkyscraperUnit B S hS x) d (baseChangeArrowOfChartDiagram B S hS f d)
      (heq_of_eq (yoneda_map_baseChangeArrowOfChartDiagram B S hS f d)) s)) ?_
  exact ConcreteCategory.congr_hom (Point.skyscraperSheafAdjunction_unit_π
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O d.U p)
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s)

/-- **The germ characterization of the fibre of the structure map.** The fibre at `x` of the
inverse-image structure map of Stacks 03G8, transported to the étale local rings, pulls germs
of regular functions back in every commuting diagram of pointed étale scheme charts over `f`:
it satisfies `AlgebraicGeometry.Space.IsEtaleLocalRingMap`. -/
theorem isEtaleLocalRingMap_stalkStructureMap :
    IsEtaleLocalRingMap f.hom x
      (((pointStalkRingEquiv B S hS X x).toRingHom.comp
          (stalkStructureMap B S hS f x).hom).comp
        (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm.toRingHom) := by
  intro U V g hcomm hpoint
  refine RingHom.ext fun s => ?_
  have hX := pointStalkRingEquiv_germ_neighborhood B S hS X x U
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map g)) s)
  have hY := pointStalkRingEquiv_germ_neighborhood B S hS Y (geometricPointMap f.hom x) V s
  have hg := stalkStructureMap_toPresheafFiber B S hS f x ⟨U.chart, V.chart, g, hcomm⟩
    (⟨U.point, U.point_comp⟩ : GeometricFiber B S hS X.1 x U.chart)
    (⟨V.point, V.point_comp⟩ :
      GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) V.chart) hpoint s
  have hY' : (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm
      (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op V) s) =
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber V.chart
        ⟨V.point, V.point_comp⟩ (smallEtaleRingedTopos B S hS Y).O.obj s := by
    rw [← hY]
    exact (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm_apply_apply _
  refine Eq.trans hX.symm (Eq.trans (congrArg (pointStalkRingEquiv B S hS X x) hg.symm) ?_)
  exact congrArg (fun z => pointStalkRingEquiv B S hS X x ((stalkStructureMap B S hS f x).hom z))
    hY'.symm

/-- **Stacks 04NG for the fibre of the structure map.** The transported fibre of the
inverse-image structure map of Stacks 03G8 is the canonical homomorphism of étale local rings
of Stacks 04NG. -/
theorem stalkStructureMapAsEtaleLocalRingMap_eq :
    (((pointStalkRingEquiv B S hS X x).toRingHom.comp
          (stalkStructureMap B S hS f x).hom).comp
        (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm.toRingHom) =
      etaleLocalRingMap X.2 f.hom x :=
  (existsUnique_etaleLocalRingMap X.2 f.hom x).unique
    (isEtaleLocalRingMap_stalkStructureMap B S hS f x)
    (etaleLocalRingMap_isEtaleLocalRingMap X.2 f.hom x)

end AlgebraicGeometry.Space

end
