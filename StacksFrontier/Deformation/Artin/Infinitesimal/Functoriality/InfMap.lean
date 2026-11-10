module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import StacksFrontier.Deformation.Artin.Infinitesimal
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality.TangentMap

/-!
# The infinitesimal automorphisms along a 1-morphism

The map `Inf_x(M) ⟶ Inf_{F x}(M)` induced by a `1`-morphism `F`, built from the comparison
between the trivial deformation of `F x` and the image of the trivial deformation of `x`, its
naturality in `M`, and its `A`-linearity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

namespace Deformation.Artin

/-! ### The infinitesimal automorphisms along a 1-morphism -/

section InfOneMorphism
open Functor
universe u v₁ w₁ v₂ w₂

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v₁} [Category.{w₁} X] {Y : Type v₂} [Category.{w₂} Y]
  (p : X ⥤ BigFppfOver B S hS) (q : Y ⥤ BigFppfOver B S hS)
  (F : X ⥤ Y) (hF : F ⋙ q = p)
  (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)

include hF in
/-- The image under `F` of the retraction of the trivial deformation of `x` lies over the
retraction `Spec A[M] ⟶ Spec A`. -/
public theorem map_trivialRetract_isHomLift (M : SiteModule A B) :
    q.IsHomLift (squareZeroRetraction A B S hS toS hA M)
      (F.map (trivialRetract A B S hS toS hA p x hx hp M)) :=
  lift_map_isHomLift p q F hF (squareZeroRetraction A B S hS toS hA M)
    (underFiber_right_obj p hx (squareZeroArrow A B S hS toS hA M)
      (trivialDeformation A B S hS toS hA p x hx hp M)) hx
    (trivialRetract A B S hS toS hA p x hx hp M)
    (trivialRetract_isHomLift A B S hS toS hA p x hx hp M)

include hF hq in
/-- That image is strongly cartesian, `𝒴` being fibred in groupoids. -/
public theorem map_trivialRetract_isStronglyCartesian (M : SiteModule A B) :
    q.IsStronglyCartesian (squareZeroRetraction A B S hS toS hA M)
      (F.map (trivialRetract A B S hS toS hA p x hx hp M)) := by
  have h := map_trivialRetract_isHomLift A B S hS toS hA p q F hF x hx hp M
  exact hq.isStronglyCartesian_homLift _ _

/-- **The comparison arrow of the two trivial deformations**, with the two properties that
determine it.  The trivial deformation of `F x` and the image under `F` of the trivial
deformation of `x` are both pullbacks of `F x` along the retraction `Spec A[M] ⟶ Spec A`; this
is the arrow from the first to the second supplied by the universal property of the second. -/
public def trivialComparisonData (M : SiteModule A B) :
    { c : (trivialDeformation A B S hS toS hA q (F.obj x)
            (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M).1.right ⟶
          F.obj ((trivialDeformation A B S hS toS hA p x hx hp M).1.right) //
      q.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) c ∧
        c ≫ F.map (trivialRetract A B S hS toS hA p x hx hp M) =
          trivialRetract A B S hS toS hA q (F.obj x)
            (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M } := by
  have h1 := map_trivialRetract_isStronglyCartesian A B S hS toS hA p q F hF x hx hp hq M
  have h2 := trivialRetract_isHomLift A B S hS toS hA q (F.obj x)
    (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M
  have hsplit : squareZeroRetraction A B S hS toS hA M =
      𝟙 (squareZeroOver A B S hS toS M) ≫ squareZeroRetraction A B S hS toS hA M :=
    (Category.id_comp _).symm
  exact ⟨IsStronglyCartesian.map q (squareZeroRetraction A B S hS toS hA M)
      (F.map (trivialRetract A B S hS toS hA p x hx hp M)) hsplit
      (trivialRetract A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M),
    IsStronglyCartesian.map_isHomLift q (squareZeroRetraction A B S hS toS hA M)
      (F.map (trivialRetract A B S hS toS hA p x hx hp M)) hsplit
      (trivialRetract A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M),
    IsStronglyCartesian.fac q (squareZeroRetraction A B S hS toS hA M)
      (F.map (trivialRetract A B S hS toS hA p x hx hp M)) hsplit
      (trivialRetract A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M)⟩

/-- The comparison arrow of the two trivial deformations. -/
public def trivialComparison (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M).1.right ⟶
      F.obj ((trivialDeformation A B S hS toS hA p x hx hp M).1.right) :=
  (trivialComparisonData A B S hS toS hA p q F hF x hx hp hq M).1

public theorem trivialComparison_isHomLift (M : SiteModule A B) :
    q.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
      (trivialComparison A B S hS toS hA p q F hF x hx hp hq M) :=
  (trivialComparisonData A B S hS toS hA p q F hF x hx hp hq M).2.1

public theorem trivialComparison_fac (M : SiteModule A B) :
    trivialComparison A B S hS toS hA p q F hF x hx hp hq M ≫
        F.map (trivialRetract A B S hS toS hA p x hx hp M) =
      trivialRetract A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M :=
  (trivialComparisonData A B S hS toS hA p q F hF x hx hp hq M).2.2

/-- The comparison arrow is compatible with the structure arrows, so it is a morphism of
lifts. -/
public theorem trivialComparison_comp (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA q (F.obj x)
          (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M).1.hom ≫
        trivialComparison A B S hS toS hA p q F hF x hx hp hq M =
      ((squareZeroLiftPost A B S hS toS hA p q F hF x hx M).obj
        (trivialDeformation A B S hS toS hA p x hx hp M)).1.hom := by
  have h1 := map_trivialRetract_isStronglyCartesian A B S hS toS hA p q F hF x hx hp hq M
  have hcm := trivialComparison_isHomLift A B S hS toS hA p q F hF x hx hp hq M
  have hyh := underFiber_isHomLift q (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx)
    (squareZeroArrow A B S hS toS hA M)
    (trivialDeformation A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M)
  have hlhs : q.IsHomLift (squareZeroArrow A B S hS toS hA M)
      ((trivialDeformation A B S hS toS hA q (F.obj x)
          (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M).1.hom ≫
        trivialComparison A B S hS toS hA p q F hF x hx hp hq M) :=
    IsHomLift.comp_lift_id_right' q (squareZeroArrow A B S hS toS hA M) _
      (squareZeroOver A B S hS toS M) _
  have hrhs : q.IsHomLift (squareZeroArrow A B S hS toS hA M)
      (F.map (trivialDeformation A B S hS toS hA p x hx hp M).1.hom) :=
    lift_map_isHomLift p q F hF (squareZeroArrow A B S hS toS hA M) hx
      (underFiber_right_obj p hx (squareZeroArrow A B S hS toS hA M)
        (trivialDeformation A B S hS toS hA p x hx hp M))
      (trivialDeformation A B S hS toS hA p x hx hp M).1.hom
      (underFiber_isHomLift p hx (squareZeroArrow A B S hS toS hA M)
        (trivialDeformation A B S hS toS hA p x hx hp M))
  change (trivialDeformation A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M).1.hom ≫
      trivialComparison A B S hS toS hA p q F hF x hx hp hq M =
    F.map (trivialDeformation A B S hS toS hA p x hx hp M).1.hom
  refine IsStronglyCartesian.ext q (squareZeroRetraction A B S hS toS hA M)
    (F.map (trivialRetract A B S hS toS hA p x hx hp M))
    (squareZeroArrow A B S hS toS hA M) ?_
  rw [Category.assoc, trivialComparison_fac,
    trivialRetract_fac A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M,
    ← F.map_comp, trivialRetract_fac, F.map_id]

/-- The comparison arrow, as a morphism of lifts of `F x` over `A[M]`. -/
public def trivialComparisonHom (M : SiteModule A B) :
    trivialDeformation A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M ⟶
      (squareZeroLiftPost A B S hS toS hA p q F hF x hx M).obj
        (trivialDeformation A B S hS toS hA p x hx hp M) :=
  underFiberHomMk q (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx)
    (squareZeroArrow A B S hS toS hA M)
    (s := trivialDeformation A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M)
    (t := (squareZeroLiftPost A B S hS toS hA p q F hF x hx M).obj
      (trivialDeformation A B S hS toS hA p x hx hp M))
    (trivialComparison A B S hS toS hA p q F hF x hx hp hq M)
    (trivialComparison_isHomLift A B S hS toS hA p q F hF x hx hp hq M)
    (trivialComparison_comp A B S hS toS hA p q F hF x hx hp hq M)

@[simp]
public theorem trivialComparisonHom_right (M : SiteModule A B) :
    (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).1.right =
      trivialComparison A B S hS toS hA p q F hF x hx hp hq M := rfl

/-- **The map on infinitesimal automorphisms induced by a `1`-morphism**: the image under `F`
of an automorphism of the trivial deformation of `x`, restricted along the comparison arrow to
an automorphism of the trivial deformation of `F x`. -/
public def infMapOfOneMorphism (M : SiteModule A B)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    trivialDeformation A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M ⟶
      trivialDeformation A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M :=
  fiberEndRestrict (Under.post q) (underPost_isFiberedInGroupoids q hq (F.obj x))
    (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).1
    (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).2
    ((squareZeroLiftPost A B S hS toS hA p q F hF x hx M).map θ)

/-- The image under `F` of the transition arrow of the trivial deformations lies over the
corresponding arrow of base thickenings. -/
public theorem map_trivialTransitionUnder_isHomLift {M N : SiteModule A B} (f : M ⟶ N) :
    (Under.post q).IsHomLift
      (liftBaseThickeningMap A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) f)
      ((Under.post F).map (trivialTransitionUnder A B S hS toS hA p x hx hp f)) :=
  underPost_map_isHomLift p q F hF hx (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx)
    (squareZeroArrow A B S hS toS hA N) (squareZeroArrow A B S hS toS hA M)
    (squareZeroOverMap A B S hS toS f)
    (by rw [Category.assoc, squareZeroArrow_naturality])
    (trivialDeformation A B S hS toS hA p x hx hp N)
    (trivialDeformation A B S hS toS hA p x hx hp M)
    (trivialTransitionUnder A B S hS toS hA p x hx hp f)
    (trivialTransition_isHomLift A B S hS toS hA p x hx hp f)

/-- The defining square of the map on infinitesimal automorphisms. -/
public theorem infMapOfOneMorphism_fac (M : SiteModule A B)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    (infMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq M θ).1 ≫
        (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).1 =
      (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).1 ≫
        (Under.post F).map θ.1 :=
  fiberEndRestrict_fac (Under.post q) (underPost_isFiberedInGroupoids q hq (F.obj x))
    (a := (squareZeroLiftPost A B S hS toS hA p q F hF x hx M).obj
      (trivialDeformation A B S hS toS hA p x hx hp M))
    (b := trivialDeformation A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq M)
    (g := 𝟙 _)
    (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).1
    (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).2
    ((squareZeroLiftPost A B S hS toS hA p q F hF x hx M).map θ)

/-- The comparison arrows are compatible with the transition arrows, read in `𝒴`. -/
public theorem trivialComparison_naturality {M N : SiteModule A B} (f : M ⟶ N) :
    trivialTransition A B S hS toS hA q (F.obj x)
          (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq f ≫
        trivialComparison A B S hS toS hA p q F hF x hx hp hq M =
      trivialComparison A B S hS toS hA p q F hF x hx hp hq N ≫
        F.map (trivialTransition A B S hS toS hA p x hx hp f) := by
  have h1 := map_trivialRetract_isStronglyCartesian A B S hS toS hA p q F hF x hx hp hq M
  have hcM := trivialComparison_isHomLift A B S hS toS hA p q F hF x hx hp hq M
  have hcN := trivialComparison_isHomLift A B S hS toS hA p q F hF x hx hp hq N
  have hrq := trivialTransition_isHomLift A B S hS toS hA q (F.obj x)
    (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq f
  have hrp : q.IsHomLift (squareZeroOverMap A B S hS toS f)
      (F.map (trivialTransition A B S hS toS hA p x hx hp f)) :=
    lift_map_isHomLift p q F hF (squareZeroOverMap A B S hS toS f)
      (underFiber_right_obj p hx (squareZeroArrow A B S hS toS hA N)
        (trivialDeformation A B S hS toS hA p x hx hp N))
      (underFiber_right_obj p hx (squareZeroArrow A B S hS toS hA M)
        (trivialDeformation A B S hS toS hA p x hx hp M))
      (trivialTransition A B S hS toS hA p x hx hp f)
      (trivialTransition_isHomLift A B S hS toS hA p x hx hp f)
  have hlhs : q.IsHomLift (squareZeroOverMap A B S hS toS f)
      (trivialTransition A B S hS toS hA q (F.obj x)
          (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq f ≫
        trivialComparison A B S hS toS hA p q F hF x hx hp hq M) :=
    IsHomLift.comp_lift_id_right' q (squareZeroOverMap A B S hS toS f) _
      (squareZeroOver A B S hS toS M) _
  have hrhs : q.IsHomLift (squareZeroOverMap A B S hS toS f)
      (trivialComparison A B S hS toS hA p q F hF x hx hp hq N ≫
        F.map (trivialTransition A B S hS toS hA p x hx hp f)) :=
    IsHomLift.comp_lift_id_left' q (squareZeroOver A B S hS toS N) _
      (squareZeroOverMap A B S hS toS f) _
  refine IsStronglyCartesian.ext q (squareZeroRetraction A B S hS toS hA M)
    (F.map (trivialRetract A B S hS toS hA p x hx hp M))
    (squareZeroOverMap A B S hS toS f) ?_
  simp only [Category.assoc]
  rw [trivialComparison_fac A B S hS toS hA p q F hF x hx hp hq M,
    ← F.map_comp, trivialTransition_comp_retract A B S hS toS hA p x hx hp f,
    trivialComparison_fac A B S hS toS hA p q F hF x hx hp hq N,
    trivialTransition_comp_retract A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq f]

/-- The comparison arrows are compatible with the transition arrows, read in the lifts. -/
public theorem trivialComparisonHom_naturality {M N : SiteModule A B} (f : M ⟶ N) :
    (trivialTransitionUnder A B S hS toS hA q (F.obj x)
          (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq f) ≫
        (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).1 =
      (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq N).1 ≫
        (Under.post F).map (trivialTransitionUnder A B S hS toS hA p x hx hp f) :=
  Under.UnderMorphism.ext (trivialComparison_naturality A B S hS toS hA p q F hF x hx hp hq f)

end InfOneMorphism

/-! ### Restriction of endomorphisms of lifts along a 1-morphism -/

section InfLinearity
open Functor
universe u v₁ w₁ v₂ w₂

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v₁} [Category.{w₁} X] {Y : Type v₂} [Category.{w₂} Y]
  (p : X ⥤ BigFppfOver B S hS) (q : Y ⥤ BigFppfOver B S hS)
  (F : X ⥤ Y) (hF : F ⋙ q = p)
  (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)

/-- The image under a `1`-morphism of an arrow of lifts of `x` over the trivial square-zero
extensions, read at the spelling `Deformation.Artin.squareZeroLiftPost` gives to its objects.
The two spellings are definitionally equal; the ascription is what lets the statements below
speak about the fibres of lifts of `F x` while `rewriting` still sees the pattern. -/
public def squareZeroLiftPostArrow {M N : SiteModule A B}
    {s : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x))}
    {t : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj x))}
    (ρ : t.1 ⟶ s.1) :
    ((squareZeroLiftPost A B S hS toS hA p q F hF x hx N).obj t).1 ⟶
      ((squareZeroLiftPost A B S hS toS hA p q F hF x hx M).obj s).1 :=
  (Under.post F).map ρ

@[simp]
public theorem squareZeroLiftPostArrow_eq {M N : SiteModule A B}
    {s : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x))}
    {t : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj x))}
    (ρ : t.1 ⟶ s.1) :
    squareZeroLiftPostArrow A B S hS toS hA p q F hF x hx (M := M) (N := N) ρ =
      (Under.post F).map ρ := rfl

/-- **A `1`-morphism commutes with restriction of endomorphisms of lifts.**  Restricting an
endomorphism of a lift along an arrow of lifts and then applying `F` is the same as applying
`F` and then restricting along the image of that arrow: both sides fill the defining square of
`Deformation.Artin.fiberEndRestrict`, which determines them. -/
public theorem squareZeroLiftPost_map_fiberEndRestrict {M N : SiteModule A B}
    {s : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x))}
    {t : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj x))}
    {gb : (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj x)) ⟶
      Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)}
    (ρ : t.1 ⟶ s.1) (hρ : (Under.post p).IsHomLift gb ρ)
    {gb' : (Under.mk (eqToHom (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) ≫
          squareZeroArrow A B S hS toS hA N) : Under (q.obj (F.obj x))) ⟶
        Under.mk (eqToHom (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) ≫
          squareZeroArrow A B S hS toS hA M)}
    (hρ' : (Under.post q).IsHomLift gb'
      (squareZeroLiftPostArrow A B S hS toS hA p q F hF x hx (M := M) (N := N) ρ))
    (θ : s ⟶ s) :
    (squareZeroLiftPost A B S hS toS hA p q F hF x hx N).map
        (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) ρ hρ θ) =
      fiberEndRestrict (Under.post q) (underPost_isFiberedInGroupoids q hq (F.obj x))
        (squareZeroLiftPostArrow A B S hS toS hA p q F hF x hx (M := M) (N := N) ρ) hρ'
        ((squareZeroLiftPost A B S hS toS hA p q F hF x hx M).map θ) := by
  refine fiberEndRestrict_eq (Under.post q) (underPost_isFiberedInGroupoids q hq (F.obj x))
    (squareZeroLiftPostArrow A B S hS toS hA p q F hF x hx (M := M) (N := N) ρ) hρ'
    ((squareZeroLiftPost A B S hS toS hA p q F hF x hx M).map θ)
    ((squareZeroLiftPost A B S hS toS hA p q F hF x hx N).map
      (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) ρ hρ θ)) ?_
  exact ((Under.post F).map_comp (Fiber.fiberInclusion.map
        (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
          ρ hρ θ)) ρ).symm.trans
    ((congrArg (fun m => (Under.post F).map m)
        (fiberEndRestrict_fac (Under.post p) (underPost_isFiberedInGroupoids p hp x)
          ρ hρ θ)).trans
      ((Under.post F).map_comp ρ (Fiber.fiberInclusion.map θ)))

/-- The image under `F` of the transition arrow of the trivial deformations, at the spelling of
`Deformation.Artin.squareZeroLiftPost`, lies over the corresponding arrow of base
thickenings. -/
public theorem squareZeroLiftPostArrow_trivialTransitionUnder_isHomLift
    {M N : SiteModule A B} (f : M ⟶ N) :
    (Under.post q).IsHomLift
      (liftBaseThickeningMap A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) f)
      (squareZeroLiftPostArrow A B S hS toS hA p q F hF x hx
        (trivialTransitionUnder A B S hS toS hA p x hx hp f)) :=
  map_trivialTransitionUnder_isHomLift A B S hS toS hA p q F hF x hx hp f

/-- **The induced map on infinitesimal automorphisms is natural in the module.**  After
unwinding both transition maps into restrictions of endomorphisms, the two sides are the
restriction of the image of `θ` along the two ways round the square of
`Deformation.Artin.trivialComparisonHom_naturality`. -/
public theorem infMapOfOneMorphism_natural {M N : SiteModule A B} (f : M ⟶ N)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    infMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq N
        ((infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f θ) =
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA q (F.obj x)
          (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq).map f
        (infMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq M θ) := by
  have hρ' := squareZeroLiftPostArrow_trivialTransitionUnder_isHomLift A B S hS toS hA p q F hF
    x hx hp f
  have hσ := trivialTransitionUnder_isHomLift A B S hS toS hA q (F.obj x)
    (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq f
  have h1 := (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq N).2
  have h2 := (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).2
  have hc1 : (Under.post q).IsHomLift (𝟙 _ ≫ liftBaseThickeningMap A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) f)
      ((trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq N).1 ≫
        squareZeroLiftPostArrow A B S hS toS hA p q F hF x hx
          (trivialTransitionUnder A B S hS toS hA p x hx hp f)) := by
    rw [Category.id_comp]
    infer_instance
  have hc2 : (Under.post q).IsHomLift (liftBaseThickeningMap A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) f ≫ 𝟙 _)
      ((trivialTransitionUnder A B S hS toS hA q (F.obj x)
          (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq f) ≫
        (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).1) := by
    rw [Category.comp_id]
    infer_instance
  rw [infAutSetFunctor_map_eq, infAutSetFunctor_map_eq, infMapOfOneMorphism, infMapOfOneMorphism,
    squareZeroLiftPost_map_fiberEndRestrict A B S hS toS hA p q F hF x hx hp hq _ _ hρ',
    ← fiberEndRestrict_comp _ _ _ hρ' _ _ hc1,
    fiberEndRestrict_congr _ _ _ _ hc1 hc2 (trivialComparisonHom_naturality A B S hS toS hA p q F
      hF x hx hp hq f).symm,
    fiberEndRestrict_comp _ _ _ _ _ hσ hc2]

variable (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
  (Inf' : InfinitesimalAutomorphismFunctorData A B S hS toS hA q (F.obj x)
    (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq)

/-- **The map `Inf_x(M) ⟶ Inf_{F x}(M)` induced by a `1`-morphism.**  Stacks 07YA on the
functor of infinitesimal automorphisms: the map on automorphisms of the trivial deformations
read through the two defining bijections.  Nothing is chosen here — the two functors of
infinitesimal automorphisms are *given*, and only their bijections are consumed. -/
public def infFunctorMapOfOneMorphism (M : SiteModule A B) :
    Inf.functor.obj M → Inf'.functor.obj M :=
  fun z => (Inf'.autEquiv M).symm
    (infMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq M (Inf.autEquiv M z))

public theorem autEquiv_infFunctorMapOfOneMorphism (M : SiteModule A B)
    (z : Inf.functor.obj M) :
    Inf'.autEquiv M
        (infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M z) =
      infMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq M (Inf.autEquiv M z) :=
  (Inf'.autEquiv M).apply_symm_apply _

/-- The induced map on the functors of infinitesimal automorphisms is natural in the
module. -/
public theorem infFunctorMapOfOneMorphism_natural {M N : SiteModule A B} (f : M ⟶ N)
    (z : Inf.functor.obj M) :
    infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' N
        (Inf.functor.map f z) =
      Inf'.functor.map f
        (infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M z) := by
  apply (Inf'.autEquiv N).injective
  rw [autEquiv_infFunctorMapOfOneMorphism, Inf.autEquiv_natural, Inf'.autEquiv_natural,
    autEquiv_infFunctorMapOfOneMorphism]
  exact infMapOfOneMorphism_natural A B S hS toS hA p q F hF x hx hp hq f (Inf.autEquiv M z)

/-- **The induced map on infinitesimal automorphisms is `A`-linear.** -/
public theorem isLinearMap_infFunctorMapOfOneMorphism (M : SiteModule A B) :
    IsLinearMap A
      (infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M) :=
  isLinearMap_of_natural_siteModule A B hA Inf.functor Inf'.functor
    (infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf')
    (fun g z => infFunctorMapOfOneMorphism_natural A B S hS toS hA p q F hF x hx hp hq
      Inf Inf' g z) M

/-- The induced map `Inf_x(M) ⟶ Inf_{F x}(M)`, as an `A`-linear map. -/
public def infLinearMapOfOneMorphism (M : SiteModule A B) :
    Inf.functor.obj M →ₗ[A] Inf'.functor.obj M :=
  IsLinearMap.mk' (infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M)
    (isLinearMap_infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M)

@[simp]
public theorem infLinearMapOfOneMorphism_apply (M : SiteModule A B) (z : Inf.functor.obj M) :
    infLinearMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M z =
      infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M z := rfl

end InfLinearity

end Deformation.Artin

end
