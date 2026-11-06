module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointNeighborhoodInclusion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationConeLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The strict henselization as a directed limit of affine étale neighbourhoods

Let `S` be a scheme in a big étale site `B` and let `s` be a geometric point of `S`. The strict
henselization `Spec(𝒪^{sh}_{S,s})` is the limit of the étale neighbourhoods of `s`
(`AlgebraicGeometry.strictHenselizationConeIsLimit`). This file presents that limit over a
*directed set* of *affine* étale neighbourhoods, in the form in which the theorems on limits of
schemes indexed by directed sets (for instance Stacks 09YQ) consume it, and with the limit
projections identified with the canonical morphisms
`AlgebraicGeometry.strictHenselizationNeighborhoodLift` from the strict henselization into the
étale neighbourhoods.

## Main definitions

* `AlgebraicGeometry.affineEtaleNeighborhoodDirectedIndex`: a directed set indexing a cofinal
  family of affine étale neighbourhoods of `s`.
* `AlgebraicGeometry.affineEtaleNeighborhoodDirectedSystem`: the inverse system of these
  neighbourhoods, as étale neighbourhoods of `s` in the sense of the point
  `AlgebraicGeometry.Scheme.pointSmallEtale`.
* `AlgebraicGeometry.etaleNeighborhoodDirectedDiagram`: the underlying inverse system of schemes.
* `AlgebraicGeometry.strictHenselizationAffineDirectedCone`: the cone on that system with vertex
  the strict henselization and legs the canonical morphisms into the neighbourhoods.

## Main results

* `geometricPointToStrictHenselization_comp_strictHenselizationCone_π_app_elements` (in the
  namespace `AlgebraicGeometry`): the legs of the limit cone of the strict henselization carry its
  canonical geometric point to the chosen lifts of `s`.
* `AlgebraicGeometry.strictHenselizationCone_π_app_eq_neighborhoodLift_elements`: the legs of
  that cone are the canonical morphisms into the neighbourhoods.
* `AlgebraicGeometry.strictHenselizationDirectedConeIsLimit`: **the strict henselization is the
  limit of the directed system of affine étale neighbourhoods.**
* `AlgebraicGeometry.exists_etaleNeighborhoodDirectedSystem_hom`: every étale neighbourhood of
  `s` is refined by a member of the directed system.

## Implementation notes

The directed set is obtained from the small cofiltered category of affine neighbourhoods
`AlgebraicGeometry.etaleNeighborhoodAffineIndex` by the theorem that a small filtered category
receives a final functor from a directed set (`CategoryTheory.IsFiltered.exists_directed`); a
limit over a category is a limit over any initial subdiagram.

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-! ### The legs of the limit cone of the strict henselization -/

/-- A morphism from the strict henselization into an affine scheme, composed with the canonical
geometric point of the strict henselization, is determined on global functions by the evaluation
of germs in the residue field of the geometric point. -/
theorem geometricPointToStrictHenselization_comp_eq_of_appTop {W : Scheme.{u}} [IsAffine W]
    (r : strictHenselization B S hS s ⟶ W) (v : s.source ⟶ W)
    (h : ∀ b : Γ(W, ⊤), structureSheafStalkToGeometricField B S hS s
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(etaleLocalRing B S hS s))).hom.hom (r.appTop.hom b)) =
      (v.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of s.residueField)).hom).hom b) :
    geometricPointToStrictHenselization B S hS s ≫ r = v := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of s.residueField)).hom,
    Scheme.Hom.comp_appTop, Category.assoc, geometricPointToStrictHenselization,
    Scheme.ΓSpecIso_naturality]
  ext b
  exact h b

/-- **The legs of the limit cone of the strict henselization carry its canonical geometric point
to the chosen lifts.** For every étale neighbourhood `(V, v)` of `s` inside the big étale site,
the leg of `AlgebraicGeometry.strictHenselizationCone` at `V` composed with the canonical
geometric point of the strict henselization is `v`. -/
theorem geometricPointToStrictHenselization_comp_strictHenselizationCone_π_app_elements
    (V : (geometricPointFiber B S hS s).Elements) :
    geometricPointToStrictHenselization B S hS s ≫
        (strictHenselizationCone B S hS s).π.app V = V.2.1 := by
  obtain ⟨a, ⟨m⟩⟩ := etaleNeighborhoodAffineIndex_weaklyInitial B S hS s V
  rw [← (strictHenselizationCone B S hS s).w m]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (geometricPointToStrictHenselization_comp_strictHenselizationCone_π_app B S hS s a)).trans
      (congrArg Subtype.val m.2))

/-- **The legs of the limit cone of the strict henselization are the canonical morphisms into
the étale neighbourhoods**: the leg at an étale neighbourhood `(V, v)` of `s` inside the big
étale site is the unique morphism `AlgebraicGeometry.strictHenselizationNeighborhoodLift` from
the strict henselization into `V` over `S` carrying the canonical geometric point to `v`. -/
theorem strictHenselizationCone_π_app_eq_neighborhoodLift_elements
    (V : (geometricPointFiber B S hS s).Elements) :
    (strictHenselizationCone B S hS s).π.app V =
      strictHenselizationNeighborhoodLift B S hS s
        ((geometricPointNeighborhoodInclusion B S hS s).obj V).1
        ((geometricPointNeighborhoodInclusion B S hS s).obj V).2 :=
  strictHenselizationNeighborhoodLift_eq B S hS s
    ((geometricPointNeighborhoodInclusion B S hS s).obj V).1
    ((geometricPointNeighborhoodInclusion B S hS s).obj V).2
    ((strictHenselizationCone B S hS s).π.app V)
    (strictHenselizationCone_π_comp_hom_eq B S hS s V)
    (geometricPointToStrictHenselization_comp_strictHenselizationCone_π_app_elements B S hS s V)

/-! ### A directed cofinal family of affine neighbourhoods -/

/-- A directed set indexing a cofinal family of affine étale neighbourhoods of `s`: a directed
set with a final functor to the opposite of the small cofiltered category
`AlgebraicGeometry.etaleNeighborhoodAffineIndex` of affine étale neighbourhoods. -/
def affineEtaleNeighborhoodDirectedIndex : Type u :=
  (IsFiltered.exists_directed (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ).choose

/-- The partial order on the directed set indexing the affine étale neighbourhoods of `s`. -/
instance : PartialOrder (affineEtaleNeighborhoodDirectedIndex B S hS s) :=
  (IsFiltered.exists_directed (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ).choose_spec.choose

/-- The index set of the affine étale neighbourhoods of `s` is directed. -/
instance : IsDirected (affineEtaleNeighborhoodDirectedIndex B S hS s) (· ≤ ·) :=
  (IsFiltered.exists_directed
    (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ).choose_spec.choose_spec.choose

/-- The index set of the affine étale neighbourhoods of `s` is nonempty. -/
instance : Nonempty (affineEtaleNeighborhoodDirectedIndex B S hS s) :=
  (IsFiltered.exists_directed
    (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ).choose_spec.choose_spec.choose_spec.choose

/-- The final functor from the directed set to the opposite of the category of affine
neighbourhoods. -/
def etaleNeighborhoodDirectedIndexFunctor :
    affineEtaleNeighborhoodDirectedIndex B S hS s ⥤ (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ :=
  (IsFiltered.exists_directed
    (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ).choose_spec.choose_spec.choose_spec.choose_spec
    |>.choose

/-- The functor `etaleNeighborhoodDirectedIndexFunctor` is final. -/
instance : (etaleNeighborhoodDirectedIndexFunctor B S hS s).Final :=
  (IsFiltered.exists_directed
    (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ).choose_spec.choose_spec.choose_spec.choose_spec
    |>.choose_spec

/-- The inclusion of the opposite of the directed set into the affine neighbourhoods. It is
initial. -/
abbrev etaleNeighborhoodDirectedAffineInclusion :
    (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ ⥤ etaleNeighborhoodAffineIndex B S hS s :=
  (etaleNeighborhoodDirectedIndexFunctor B S hS s).op ⋙ unopUnop _

/-- The functor `etaleNeighborhoodDirectedAffineInclusion` is initial. -/
instance : (etaleNeighborhoodDirectedAffineInclusion B S hS s).Initial := by
  have := Functor.initial_op_of_final (etaleNeighborhoodDirectedIndexFunctor B S hS s)
  exact Functor.initial_comp _ _

/-- **The directed system of affine étale neighbourhoods of `s`**, as étale neighbourhoods in the
sense of the point `AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site. -/
@[sga "4 VIII 4.5"]
def affineEtaleNeighborhoodDirectedSystem :
    (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ ⥤
      (Scheme.pointSmallEtale s.hom).fiber.Elements :=
  etaleNeighborhoodDirectedAffineInclusion B S hS s ⋙ etaleNeighborhoodAffineInclusion B S hS s ⋙
    geometricPointNeighborhoodInclusion B S hS s

/-- The underlying inverse system of schemes of the directed system of affine étale
neighbourhoods. -/
abbrev etaleNeighborhoodDirectedDiagram :
    (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ ⥤ Scheme.{u} :=
  etaleNeighborhoodDirectedAffineInclusion B S hS s ⋙ etaleNeighborhoodAffineDiagram B S hS s

/-- The étale neighbourhood of the directed system at an index. -/
abbrev etaleNeighborhoodDirectedObj (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    S.Etale :=
  ((affineEtaleNeighborhoodDirectedSystem B S hS s).obj a).1

/-- The chosen lift of `s` to the étale neighbourhood of the directed system at an index. -/
abbrev etaleNeighborhoodDirectedPoint (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    (Scheme.pointSmallEtale s.hom).fiber.obj (etaleNeighborhoodDirectedObj B S hS s a) :=
  ((affineEtaleNeighborhoodDirectedSystem B S hS s).obj a).2

/-- Each scheme of the directed system of affine étale neighbourhoods is affine. -/
instance (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    IsAffine ((etaleNeighborhoodDirectedDiagram B S hS s).obj a) :=
  isAffine_etaleNeighborhoodAffineDiagram_obj B S hS s _

/-- The underlying scheme of each étale neighbourhood of the directed system is affine. -/
instance (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    IsAffine (etaleNeighborhoodDirectedObj B S hS s a).left :=
  isAffine_etaleNeighborhoodAffineDiagram_obj B S hS s _

/-- The transition morphisms of the directed system of affine étale neighbourhoods are affine. -/
instance isAffineHom_etaleNeighborhoodDirectedDiagram_map
    {a b : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ} (m : a ⟶ b) :
    IsAffineHom ((etaleNeighborhoodDirectedDiagram B S hS s).map m) :=
  inferInstance

/-- The underlying scheme of the neighbourhood of the directed system at an index is the value
of the diagram there. -/
theorem etaleNeighborhoodDirectedObj_left (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    (etaleNeighborhoodDirectedObj B S hS s a).left =
      (etaleNeighborhoodDirectedDiagram B S hS s).obj a :=
  rfl

/-- The transition morphisms of the diagram are those of the directed system of
neighbourhoods. -/
theorem etaleNeighborhoodDirectedDiagram_map
    {a b : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ} (m : a ⟶ b) :
    (etaleNeighborhoodDirectedDiagram B S hS s).map m =
      ((affineEtaleNeighborhoodDirectedSystem B S hS s).map m).1.left :=
  rfl

/-- **The strict henselization as a cone on the directed system of affine étale
neighbourhoods**, with legs the canonical morphisms into the neighbourhoods. -/
def strictHenselizationAffineDirectedCone : Cone (etaleNeighborhoodDirectedDiagram B S hS s) where
  pt := strictHenselization B S hS s
  π :=
    { app := fun a => strictHenselizationNeighborhoodLift B S hS s
        (etaleNeighborhoodDirectedObj B S hS s a) (etaleNeighborhoodDirectedPoint B S hS s a)
      naturality := fun a b m => by
        have h := strictHenselizationNeighborhoodLift_comp_left B S hS s
          (etaleNeighborhoodDirectedObj B S hS s a) (etaleNeighborhoodDirectedPoint B S hS s a)
          ((affineEtaleNeighborhoodDirectedSystem B S hS s).map m).1
        rw [((affineEtaleNeighborhoodDirectedSystem B S hS s).map m).2] at h
        exact (Category.id_comp _).trans h.symm }

/-- The vertex of `strictHenselizationAffineDirectedCone` is the strict henselization. -/
@[simp]
theorem strictHenselizationAffineDirectedCone_pt :
    (strictHenselizationAffineDirectedCone B S hS s).pt = strictHenselization B S hS s :=
  rfl

/-- The leg of `strictHenselizationAffineDirectedCone` at an index is the canonical morphism
`strictHenselizationNeighborhoodLift` into the étale neighbourhood at that index. -/
@[simp]
theorem strictHenselizationAffineDirectedCone_π_app
    (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    (strictHenselizationAffineDirectedCone B S hS s).π.app a =
      strictHenselizationNeighborhoodLift B S hS s
        (etaleNeighborhoodDirectedObj B S hS s a) (etaleNeighborhoodDirectedPoint B S hS s a) :=
  rfl

/-- **The strict henselization is the limit of the directed system of affine étale
neighbourhoods.** -/
def strictHenselizationDirectedConeIsLimit :
    IsLimit (strictHenselizationAffineDirectedCone B S hS s) :=
  IsLimit.ofIsoLimit
    ((Functor.Initial.isLimitWhiskerEquiv (etaleNeighborhoodDirectedAffineInclusion B S hS s)
      (strictHenselizationAffineCone B S hS s)).symm
        (strictHenselizationAffineConeIsLimit B S hS s))
    (Cone.ext (Iso.refl (strictHenselization B S hS s)) fun _ =>
      Eq.trans (strictHenselizationCone_π_app_eq_neighborhoodLift_elements B S hS s _)
        (Category.id_comp _).symm :
      Cone.whisker (etaleNeighborhoodDirectedAffineInclusion B S hS s)
          (strictHenselizationAffineCone B S hS s) ≅ strictHenselizationAffineDirectedCone B S hS s)

/-- **Every étale neighbourhood of `s` is refined by a member of the directed system of affine
étale neighbourhoods.** -/
theorem exists_etaleNeighborhoodDirectedSystem_hom
    (U : (Scheme.pointSmallEtale s.hom).fiber.Elements) :
    ∃ a, Nonempty ((affineEtaleNeighborhoodDirectedSystem B S hS s).obj a ⟶ U) := by
  obtain ⟨V, -, ⟨m⟩⟩ := exists_isAffine_geometricPointNeighborhoodInclusion B S hS s U
  obtain ⟨c, ⟨n⟩⟩ := etaleNeighborhoodAffineIndex_weaklyInitial B S hS s V
  obtain ⟨x⟩ : Nonempty (CostructuredArrow (etaleNeighborhoodDirectedAffineInclusion B S hS s) c) :=
    IsConnected.is_nonempty
  exact ⟨x.left, ⟨(geometricPointNeighborhoodInclusion B S hS s).map
    ((etaleNeighborhoodAffineInclusion B S hS s).map x.hom ≫ n) ≫ m⟩⟩

end AlgebraicGeometry
