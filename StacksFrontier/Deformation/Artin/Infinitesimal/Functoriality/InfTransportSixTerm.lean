module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import StacksFrontier.Deformation.Artin.Infinitesimal
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality.TangentMap
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality.InfMap
public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality.ZeroAndTangentTransport

/-!
# The infinitesimal automorphisms along a vertical isomorphism, and the 2-fibre product

The `A`-linear map on infinitesimal automorphisms induced by a vertical isomorphism, and the
first exactness assertion of the six-term sequence of a `2`-fibre product (Stacks 0DNN).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

namespace Deformation.Artin

/-! ### The infinitesimal automorphisms along a vertical isomorphism -/

section TransportInf
open Functor
universe u v w

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {Y : Type v} [Category.{w} Y] (p : Y ⥤ BigFppfOver B S hS) (y₁ y₂ : Y)
  (hy₁ : p.obj y₁ = algebraOver A B S hS toS hA)
  (hy₂ : p.obj y₂ = algebraOver A B S hS toS hA)
  (ι : y₁ ≅ y₂) (hι : p.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) ι.hom)
  (hp : p.IsFiberedInGroupoids)

include hι in
/-- The inverse of a vertical isomorphism is vertical. -/
public theorem transportIso_inv_isHomLift :
    p.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) ι.inv := by
  have := hι
  infer_instance

/-- **The trivial deformation of `y₂`, read as a lift of `y₁`, is a pullback of `y₁`.**  This
is the arrow down to `y₁` exhibiting it as such: the retraction of the trivial deformation of
`y₂` followed by the inverse of the comparison isomorphism.  It lives entirely in `Y`, which
is what keeps the whole transport free of `Under`-level `eqToHom`. -/
public def transportRetract (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M).1.right ⟶ y₁ :=
  trivialRetract A B S hS toS hA p y₂ hy₂ hp M ≫ ι.inv

include hι in
public theorem transportRetract_isHomLift (M : SiteModule A B) :
    p.IsHomLift (squareZeroRetraction A B S hS toS hA M)
      (transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M) := by
  have := trivialRetract_isHomLift A B S hS toS hA p y₂ hy₂ hp M
  have := transportIso_inv_isHomLift A B S hS toS hA p y₁ y₂ ι hι
  exact IsHomLift.comp_lift_id_right' p (squareZeroRetraction A B S hS toS hA M)
    (trivialRetract A B S hS toS hA p y₂ hy₂ hp M) (algebraOver A B S hS toS hA) ι.inv

include hι in
public theorem transportRetract_isStronglyCartesian (M : SiteModule A B) :
    p.IsStronglyCartesian (squareZeroRetraction A B S hS toS hA M)
      (transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M) := by
  have := transportRetract_isHomLift A B S hS toS hA p y₁ y₂ hy₂ ι hι hp M
  exact hp.isStronglyCartesian_homLift _ _

/-- The structure arrow of the trivial deformation of `y₂` is a section of that arrow, up to
the comparison isomorphism. -/
public theorem trivialDeformation_comp_transportRetract (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M).1.hom ≫
        transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M = ι.inv := by
  rw [transportRetract, ← Category.assoc, trivialRetract_fac, Category.id_comp]

/-- The transported trivial deformation of `y₂` is a lift of `y₁` whose structure arrow is a
section of `Deformation.Artin.transportRetract`. -/
public theorem transportRetract_fac (M : SiteModule A B) :
    ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).obj
          (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M)).1.hom ≫
        transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M = 𝟙 y₁ := by
  show (ι.hom ≫ (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M).1.hom) ≫
    transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M = 𝟙 y₁
  rw [Category.assoc, trivialDeformation_comp_transportRetract, Iso.hom_inv_id]

include hι in
/-- **The comparison arrow of the two trivial deformations across a vertical isomorphism**,
with the two properties that determine it.  The trivial deformation of `y₁` and the transport
of the trivial deformation of `y₂` are both pullbacks of `y₁` along the retraction
`Spec A[M] ⟶ Spec A`; this is the arrow from the first to the second. -/
public def trivialTransportComparisonData (M : SiteModule A B) :
    { c : (trivialDeformation A B S hS toS hA p y₁ hy₁ hp M).1.right ⟶
          (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M).1.right //
      p.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) c ∧
        c ≫ transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M =
          trivialRetract A B S hS toS hA p y₁ hy₁ hp M } := by
  have h1 := transportRetract_isStronglyCartesian A B S hS toS hA p y₁ y₂ hy₂ ι hι hp M
  have h2 := trivialRetract_isHomLift A B S hS toS hA p y₁ hy₁ hp M
  have hsplit : squareZeroRetraction A B S hS toS hA M =
      𝟙 (squareZeroOver A B S hS toS M) ≫ squareZeroRetraction A B S hS toS hA M :=
    (Category.id_comp _).symm
  exact ⟨IsStronglyCartesian.map p (squareZeroRetraction A B S hS toS hA M)
      (transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M) hsplit
      (trivialRetract A B S hS toS hA p y₁ hy₁ hp M),
    IsStronglyCartesian.map_isHomLift p (squareZeroRetraction A B S hS toS hA M)
      (transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M) hsplit
      (trivialRetract A B S hS toS hA p y₁ hy₁ hp M),
    IsStronglyCartesian.fac p (squareZeroRetraction A B S hS toS hA M)
      (transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M) hsplit
      (trivialRetract A B S hS toS hA p y₁ hy₁ hp M)⟩

/-- The comparison arrow of the two trivial deformations across a vertical isomorphism. -/
public def trivialTransportComparison (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA p y₁ hy₁ hp M).1.right ⟶
      (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M).1.right :=
  (trivialTransportComparisonData A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).1

public theorem trivialTransportComparison_isHomLift (M : SiteModule A B) :
    p.IsHomLift (𝟙 (squareZeroOver A B S hS toS M))
      (trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M) :=
  (trivialTransportComparisonData A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).2.1

public theorem trivialTransportComparison_fac (M : SiteModule A B) :
    trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M ≫
        transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M =
      trivialRetract A B S hS toS hA p y₁ hy₁ hp M :=
  (trivialTransportComparisonData A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).2.2

/-- The comparison arrow is compatible with the structure arrows, so it is a morphism of
lifts of `y₁`. -/
public theorem trivialTransportComparison_comp (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA p y₁ hy₁ hp M).1.hom ≫
        trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M =
      ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).obj
        (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M)).1.hom := by
  have h1 := transportRetract_isStronglyCartesian A B S hS toS hA p y₁ y₂ hy₂ ι hι hp M
  have hcm := trivialTransportComparison_isHomLift A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M
  have hy₁h := underFiber_isHomLift p hy₁ (squareZeroArrow A B S hS toS hA M)
    (trivialDeformation A B S hS toS hA p y₁ hy₁ hp M)
  have hy₂h := underFiber_isHomLift p hy₂ (squareZeroArrow A B S hS toS hA M)
    (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M)
  have := hι
  have hlhs : p.IsHomLift (squareZeroArrow A B S hS toS hA M)
      ((trivialDeformation A B S hS toS hA p y₁ hy₁ hp M).1.hom ≫
        trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M) :=
    IsHomLift.comp_lift_id_right' p (squareZeroArrow A B S hS toS hA M) _
      (squareZeroOver A B S hS toS M) _
  have hrhs : p.IsHomLift (squareZeroArrow A B S hS toS hA M)
      (ι.hom ≫ (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M).1.hom) :=
    IsHomLift.comp_lift_id_left' p (algebraOver A B S hS toS hA) ι.hom
      (squareZeroArrow A B S hS toS hA M) _
  show (trivialDeformation A B S hS toS hA p y₁ hy₁ hp M).1.hom ≫
      trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M =
    ι.hom ≫ (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M).1.hom
  refine IsStronglyCartesian.ext p (squareZeroRetraction A B S hS toS hA M)
    (transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M)
    (squareZeroArrow A B S hS toS hA M) ?_
  rw [Category.assoc, trivialTransportComparison_fac, trivialRetract_fac, Category.assoc,
    trivialDeformation_comp_transportRetract, Iso.hom_inv_id]

/-- The comparison arrow, as a morphism of lifts of `y₁` over `A[M]`. -/
public def trivialTransportComparisonHom (M : SiteModule A B) :
    trivialDeformation A B S hS toS hA p y₁ hy₁ hp M ⟶
      (squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).obj
        (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M) :=
  underFiberHomMk p hy₁ (squareZeroArrow A B S hS toS hA M)
    (s := trivialDeformation A B S hS toS hA p y₁ hy₁ hp M)
    (t := (squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).obj
      (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M))
    (trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M)
    (trivialTransportComparison_isHomLift A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M)
    (trivialTransportComparison_comp A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M)

@[simp]
public theorem trivialTransportComparisonHom_right (M : SiteModule A B) :
    (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).1.right =
      trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M := rfl

/-- **The map on infinitesimal automorphisms induced by a vertical isomorphism**: an
automorphism of the trivial deformation of `y₂`, transported to the lifts of `y₁` and then
restricted along the comparison arrow. -/
public def infMapOfTransport (M : SiteModule A B)
    (θ : trivialDeformation A B S hS toS hA p y₂ hy₂ hp M ⟶
      trivialDeformation A B S hS toS hA p y₂ hy₂ hp M) :
    trivialDeformation A B S hS toS hA p y₁ hy₁ hp M ⟶
      trivialDeformation A B S hS toS hA p y₁ hy₁ hp M :=
  fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₁)
    (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).1
    (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).2
    ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).map θ)


/-- The transport of an arrow of lifts, ascribed the type the transport functor gives its
objects.  The two spellings are definitionally equal; the ascription is what lets the
statements below speak about the fibres of lifts of `y₁` without ever rewriting across the
crossing. -/
public def squareZeroLiftTransportArrow {M N : SiteModule A B}
    {s : (Under.post p).Fiber
      (Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj y₂))}
    {t : (Under.post p).Fiber
      (Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj y₂))}
    (ρ : t.1 ⟶ s.1) :
    ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι N).obj t).1 ⟶
      ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).obj s).1 :=
  (Under.map ι.hom).map ρ

@[simp]
public theorem squareZeroLiftTransportArrow_eq {M N : SiteModule A B}
    {s : (Under.post p).Fiber
      (Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj y₂))}
    {t : (Under.post p).Fiber
      (Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj y₂))}
    (ρ : t.1 ⟶ s.1) :
    squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι (M := M) (N := N) ρ =
      (Under.map ι.hom).map ρ := rfl

/-- **Transport commutes with restriction of endomorphisms of lifts.**  Both sides fill the
defining square of `Deformation.Artin.fiberEndRestrict`, which determines them. -/
public theorem squareZeroLiftTransport_map_fiberEndRestrict {M N : SiteModule A B}
    {s : (Under.post p).Fiber
      (Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj y₂))}
    {t : (Under.post p).Fiber
      (Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj y₂))}
    {gb : (Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj y₂)) ⟶
      Under.mk (eqToHom hy₂ ≫ squareZeroArrow A B S hS toS hA M)}
    (ρ : t.1 ⟶ s.1) (hρ : (Under.post p).IsHomLift gb ρ)
    {gb' : (Under.mk (eqToHom hy₁ ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj y₁)) ⟶
        Under.mk (eqToHom hy₁ ≫ squareZeroArrow A B S hS toS hA M)}
    (hρ' : (Under.post p).IsHomLift gb'
      (squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι (M := M) (N := N) ρ))
    (θ : s ⟶ s) :
    (squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι N).map
        (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₂) ρ hρ θ) =
      fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₁)
        (squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι (M := M) (N := N) ρ)
        hρ' ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).map θ) := by
  refine fiberEndRestrict_eq (Under.post p) (underPost_isFiberedInGroupoids p hp y₁)
    (squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι (M := M) (N := N) ρ) hρ'
    ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).map θ)
    ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι N).map
      (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₂) ρ hρ θ)) ?_
  exact ((Under.map ι.hom).map_comp (Fiber.fiberInclusion.map
        (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₂)
          ρ hρ θ)) ρ).symm.trans
    ((congrArg (fun m => (Under.map ι.hom).map m)
        (fiberEndRestrict_fac (Under.post p) (underPost_isFiberedInGroupoids p hp y₂)
          ρ hρ θ)).trans
      ((Under.map ι.hom).map_comp ρ (Fiber.fiberInclusion.map θ)))

/-- The transport of the transition arrow of the trivial deformations lies over the
corresponding arrow of base thickenings of `y₁`. -/
public theorem squareZeroLiftTransportArrow_trivialTransitionUnder_isHomLift
    {M N : SiteModule A B} (f : M ⟶ N) :
    (Under.post p).IsHomLift
      (liftBaseThickeningMap A B S hS toS hA p y₁ hy₁ f)
      (squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι
        (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f)) :=
  underMap_map_isHomLift p hy₁ hy₂ ι.hom hι
    (squareZeroArrow A B S hS toS hA N) (squareZeroArrow A B S hS toS hA M)
    (squareZeroOverMap A B S hS toS f)
    (by rw [Category.assoc, squareZeroArrow_naturality])
    (trivialDeformation A B S hS toS hA p y₂ hy₂ hp N)
    (trivialDeformation A B S hS toS hA p y₂ hy₂ hp M)
    (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f)
    (trivialTransition_isHomLift A B S hS toS hA p y₂ hy₂ hp f)

/-- The comparison arrows are compatible with the transition arrows, read in `Y`. -/
public theorem trivialTransportComparison_naturality {M N : SiteModule A B} (f : M ⟶ N) :
    trivialTransition A B S hS toS hA p y₁ hy₁ hp f ≫
        trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M =
      trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N ≫
        trivialTransition A B S hS toS hA p y₂ hy₂ hp f := by
  have h1 := transportRetract_isStronglyCartesian A B S hS toS hA p y₁ y₂ hy₂ ι hι hp M
  have hcM := trivialTransportComparison_isHomLift A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M
  have hcN := trivialTransportComparison_isHomLift A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N
  have hr₁ := trivialTransition_isHomLift A B S hS toS hA p y₁ hy₁ hp f
  have hr₂ := trivialTransition_isHomLift A B S hS toS hA p y₂ hy₂ hp f
  have hlhs : p.IsHomLift (squareZeroOverMap A B S hS toS f)
      (trivialTransition A B S hS toS hA p y₁ hy₁ hp f ≫
        trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M) :=
    IsHomLift.comp_lift_id_right' p (squareZeroOverMap A B S hS toS f) _
      (squareZeroOver A B S hS toS M) _
  have hrhs : p.IsHomLift (squareZeroOverMap A B S hS toS f)
      (trivialTransportComparison A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N ≫
        trivialTransition A B S hS toS hA p y₂ hy₂ hp f) :=
    IsHomLift.comp_lift_id_left' p (squareZeroOver A B S hS toS N) _
      (squareZeroOverMap A B S hS toS f) _
  refine IsStronglyCartesian.ext p (squareZeroRetraction A B S hS toS hA M)
    (transportRetract A B S hS toS hA p y₁ y₂ hy₂ ι hp M)
    (squareZeroOverMap A B S hS toS f) ?_
  simp only [Category.assoc]
  rw [trivialTransportComparison_fac A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M,
    trivialTransition_comp_retract A B S hS toS hA p y₁ hy₁ hp f, transportRetract,
    ← Category.assoc (trivialTransition A B S hS toS hA p y₂ hy₂ hp f),
    trivialTransition_comp_retract A B S hS toS hA p y₂ hy₂ hp f]
  exact (trivialTransportComparison_fac A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).symm

/-- The comparison arrows are compatible with the transition arrows, read in the lifts. -/
public theorem trivialTransportComparisonHom_naturality {M N : SiteModule A B} (f : M ⟶ N) :
    (trivialTransitionUnder A B S hS toS hA p y₁ hy₁ hp f) ≫
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).1 =
      (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).1 ≫
        (Under.map ι.hom).map (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f) :=
  Under.UnderMorphism.ext
    (trivialTransportComparison_naturality A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp f)

/-- **The map induced on infinitesimal automorphisms by a vertical isomorphism is natural in
the module.** -/
public theorem infMapOfTransport_natural {M N : SiteModule A B} (f : M ⟶ N)
    (θ : trivialDeformation A B S hS toS hA p y₂ hy₂ hp M ⟶
      trivialDeformation A B S hS toS hA p y₂ hy₂ hp M) :
    infMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N
        ((infinitesimalAutomorphismSetFunctor A B S hS toS hA p y₂ hy₂ hp).map f θ) =
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA p y₁ hy₁ hp).map f
        (infMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M θ) := by
  have hρ' : (Under.post p).IsHomLift
      (liftBaseThickeningMap A B S hS toS hA p y₁ hy₁ f)
      (squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι
        (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f)) :=
    squareZeroLiftTransportArrow_trivialTransitionUnder_isHomLift A B S hS toS hA p y₁ y₂
      hy₁ hy₂ ι hι hp f
  have hσ := trivialTransitionUnder_isHomLift A B S hS toS hA p y₁ hy₁ hp f
  have h1 : (Under.post p).IsHomLift
      (𝟙 (Under.mk (eqToHom hy₁ ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj y₁)) ≫
        liftBaseThickeningMap A B S hS toS hA p y₁ hy₁ f)
      ((trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).1 ≫
        squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι
          (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f)) := by
    rw [Category.id_comp]
    have := (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).2
    have := hρ'
    infer_instance
  have h2 : (Under.post p).IsHomLift
      (liftBaseThickeningMap A B S hS toS hA p y₁ hy₁ f ≫
        𝟙 (Under.mk (eqToHom hy₁ ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj y₁)))
      ((trivialTransitionUnder A B S hS toS hA p y₁ hy₁ hp f) ≫
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).1) := by
    rw [Category.comp_id]
    have := hσ
    have := (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).2
    infer_instance
  have hnat : (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).1 ≫
        squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι
          (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f) =
      (trivialTransitionUnder A B S hS toS hA p y₁ hy₁ hp f) ≫
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).1 := by
    symm
    apply trivialTransportComparisonHom_naturality
  have hstep : (infinitesimalAutomorphismSetFunctor A B S hS toS hA p y₂ hy₂ hp).map f θ =
      fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₂)
        (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f)
        (trivialTransitionUnder_isHomLift A B S hS toS hA p y₂ hy₂ hp f) θ := by
    apply infAutSetFunctor_map_eq
  have hstepq : (infinitesimalAutomorphismSetFunctor A B S hS toS hA p y₁ hy₁ hp).map f
        (infMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M θ) =
      fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₁)
        (trivialTransitionUnder A B S hS toS hA p y₁ hy₁ hp f) hσ
        (infMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M θ) := by
    apply infAutSetFunctor_map_eq
  have hL : infMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N
        (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₂)
          (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f)
          (trivialTransitionUnder_isHomLift A B S hS toS hA p y₂ hy₂ hp f) θ) =
      fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₁)
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).1
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).2
        (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp y₁)
          (squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι
            (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f)) hρ'
          ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).map θ)) :=
    congrArg (fun z => fiberEndRestrict (Under.post p)
        (underPost_isFiberedInGroupoids p hp y₁)
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).1
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).2 z)
      (squareZeroLiftTransport_map_fiberEndRestrict A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp
        (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f)
        (trivialTransitionUnder_isHomLift A B S hS toS hA p y₂ hy₂ hp f) hρ' θ)
  refine Eq.trans (congrArg
    (fun z => infMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N z) hstep) ?_
  refine hL.trans (Eq.trans ?_ hstepq.symm)
  exact (fiberEndRestrict_comp (Under.post p) (underPost_isFiberedInGroupoids p hp y₁)
        (squareZeroLiftTransportArrow A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι
          (trivialTransitionUnder A B S hS toS hA p y₂ hy₂ hp f)) hρ'
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).1
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp N).2 h1
        ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).map θ)).symm.trans
    ((fiberEndRestrict_congr (Under.post p) (underPost_isFiberedInGroupoids p hp y₁)
        _ _ h1 h2 hnat
        ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).map θ)).trans
      (fiberEndRestrict_comp (Under.post p) (underPost_isFiberedInGroupoids p hp y₁)
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).1
        (trivialTransportComparisonHom A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M).2
        (trivialTransitionUnder A B S hS toS hA p y₁ hy₁ hp f) hσ h2
        ((squareZeroLiftTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι M).map θ)))

variable (Inf₂ : InfinitesimalAutomorphismFunctorData A B S hS toS hA p y₂ hy₂ hp)
  (Inf₁ : InfinitesimalAutomorphismFunctorData A B S hS toS hA p y₁ hy₁ hp)

/-- **The map `Inf_{y₂}(M) ⟶ Inf_{y₁}(M)` induced by a vertical isomorphism `y₁ ≅ y₂`**, read
through the two defining bijections. -/
public def infFunctorMapOfTransport (M : SiteModule A B) :
    Inf₂.functor.obj M → Inf₁.functor.obj M :=
  fun z => (Inf₁.autEquiv M).symm
    (infMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M (Inf₂.autEquiv M z))

public theorem autEquiv_infFunctorMapOfTransport (M : SiteModule A B) (z : Inf₂.functor.obj M) :
    Inf₁.autEquiv M
        (infFunctorMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp Inf₂ Inf₁ M z) =
      infMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp M (Inf₂.autEquiv M z) :=
  (Inf₁.autEquiv M).apply_symm_apply _

/-- The induced map is natural in the module. -/
public theorem infFunctorMapOfTransport_natural {M N : SiteModule A B} (f : M ⟶ N)
    (z : Inf₂.functor.obj M) :
    infFunctorMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp Inf₂ Inf₁ N
        (Inf₂.functor.map f z) =
      Inf₁.functor.map f
        (infFunctorMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp Inf₂ Inf₁ M z) := by
  apply (Inf₁.autEquiv N).injective
  rw [autEquiv_infFunctorMapOfTransport, Inf₂.autEquiv_natural, Inf₁.autEquiv_natural,
    autEquiv_infFunctorMapOfTransport]
  exact infMapOfTransport_natural A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp f (Inf₂.autEquiv M z)

/-- **The map induced on infinitesimal automorphisms by a vertical isomorphism is
`A`-linear.** -/
public theorem isLinearMap_infFunctorMapOfTransport (M : SiteModule A B) :
    IsLinearMap A
      (infFunctorMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp Inf₂ Inf₁ M) :=
  isLinearMap_of_natural_siteModule A B hA Inf₂.functor Inf₁.functor
    (infFunctorMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp Inf₂ Inf₁)
    (fun g z => infFunctorMapOfTransport_natural A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp
      Inf₂ Inf₁ g z) M

/-- The map `Inf_{y₂}(M) ⟶ Inf_{y₁}(M)` induced by a vertical isomorphism, as an `A`-linear
map. -/
public def infLinearMapOfTransport (M : SiteModule A B) :
    Inf₂.functor.obj M →ₗ[A] Inf₁.functor.obj M :=
  IsLinearMap.mk' (infFunctorMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp Inf₂ Inf₁ M)
    (isLinearMap_infFunctorMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp Inf₂ Inf₁ M)

@[simp]
public theorem infLinearMapOfTransport_apply (M : SiteModule A B) (z : Inf₂.functor.obj M) :
    infLinearMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp Inf₂ Inf₁ M z =
      infFunctorMapOfTransport A B S hS toS hA p y₁ y₂ hy₁ hy₂ ι hι hp Inf₂ Inf₁ M z := rfl

end TransportInf

/-! ### The six-term sequence of a 2-fibre product -/

section TwoFibreSixTerm
open Functor CategoryTheory.TwoFibreProductOver
universe u v₁ w₁ v₂ w₂ v₃ w₃

/-- **The four assertions of Stacks 0DNN that are carried rather than proved here**: exactness
of the six-term sequence of the `2`-fibre product at `Inf_x(M) ⊕ Inf_z(M)`, at `Inf_y(M)`, at
`T_w(M)` and at `T_x(M) ⊕ T_z(M)`, for a given pair of comparison maps out of the `𝒵`-side and
a given boundary map.  Isolating them as one `Prop` is what lets the theorem below state the
whole sequence while naming exactly which part of it is hypothesis. -/
public def TwoFibreSixTermTail (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (toS : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A)))
    {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒵 : Type v₂} [Category.{w₂} 𝒵]
    {𝒴 : Type v₃} [Category.{w₃} 𝒴]
    (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒵 : 𝒵 ⥤ BigFppfOver B S hS)
    (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (P : 𝒳 ⥤ 𝒴) (Q : 𝒵 ⥤ 𝒴)
    (hP : P ⋙ p𝒴 = p𝒳) (hQ : Q ⋙ p𝒴 = p𝒵)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (w : TwoFibreProductOver p𝒳 p𝒵 p𝒴 P Q)
    (hw : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).obj w = algebraOver A B S hS toS hA)
    (InfW : InfinitesimalAutomorphismFunctorData A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ))
    (InfX : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒳 w.x (w.hx.trans hw) h𝒳)
    (InfZ : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒵 w.y (w.hy.trans hw) h𝒵)
    (InfY : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒴 (P.obj w.x)
      (oneMorphism_obj_eq A B S hS toS hA p𝒳 p𝒴 P hP w.x (w.hx.trans hw)) h𝒴)
    (TW : TangentFunctorData A B S hS toS hA (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w
      hw)
    (TX : TangentFunctorData A B S hS toS hA p𝒳 w.x (w.hx.trans hw))
    (TZ : TangentFunctorData A B S hS toS hA p𝒵 w.y (w.hy.trans hw))
    (TY : TangentFunctorData A B S hS toS hA p𝒴 (P.obj w.x) (oneMorphism_obj_eq A B S hS toS hA p𝒳
      p𝒴 P hP w.x (w.hx.trans hw)))
    (M : SiteModule A B)
    (infZY : InfZ.functor.obj M →ₗ[A] InfY.functor.obj M)
    (tanZY : TZ.functor.obj M →ₗ[A] TY.functor.obj M)
    (delta : InfY.functor.obj M →ₗ[A] TW.functor.obj M) : Prop :=
  Function.Exact (LinearMap.prod
        (infLinearMapOfOneMorphism A B S hS toS hA
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴
              P Q) TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳
              p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳
            InfW InfX M)
        (infLinearMapOfOneMorphism A B S hS toS hA
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴
              P Q) TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳
              p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵
            InfW InfZ M)) (LinearMap.coprod
        (infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x (w.hx.trans hw) h𝒳 h𝒴
          InfX InfY M)
        (-infZY)) ∧
    Function.Exact (LinearMap.coprod
        (infLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x (w.hx.trans hw) h𝒳 h𝒴
          InfX InfY M)
        (-infZY)) delta ∧
    Function.Exact delta (LinearMap.prod
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P
            Q) TwoFibreProductOver.fst_comp_eq w hw
          TW TX h𝒳 M)
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P
            Q) TwoFibreProductOver.snd_comp_eq w hw
          TW TZ h𝒵 M)) ∧
    Function.Exact (LinearMap.prod
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 P
            Q) TwoFibreProductOver.fst_comp_eq w hw
          TW TX h𝒳 M)
        (tangentLinearMapOfOneMorphism A B S hS toS hA
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 P
            Q) TwoFibreProductOver.snd_comp_eq w hw
          TW TZ h𝒵 M)) (LinearMap.coprod
        (tangentLinearMapOfOneMorphism A B S hS toS hA p𝒳 p𝒴 P hP w.x (w.hx.trans hw)
          TX TY h𝒴 M)
        (-tanZY))

/-- Two infinitesimal automorphisms with the same image under a `1`-morphism have the same
image under the functor on lifts, the comparison with the trivial deformation being invertible
because the lifts form a category fibred in groupoids. -/
private theorem map_squareZeroLiftPost_eq_of_infFunctorMapOfOneMorphism_eq
    (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {X : Type v₁} [Category.{w₁} X] {Y : Type v₂} [Category.{w₂} Y]
    (p : X ⥤ BigFppfOver B S hS) (q : Y ⥤ BigFppfOver B S hS) (F : X ⥤ Y) (hF : F ⋙ q = p)
    (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
    (Inf' : InfinitesimalAutomorphismFunctorData A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) hq)
    (M : SiteModule A B) (z z' : Inf.functor.obj M)
    (h : infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M z =
      infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M z') :
    (squareZeroLiftPost A B S hS toS hA p q F hF x hx M).map (Inf.autEquiv M z) =
      (squareZeroLiftPost A B S hS toS hA p q F hF x hx M).map (Inf.autEquiv M z') := by
  have e := (autEquiv_infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq
      Inf Inf' M z).symm.trans ((congrArg (fun u => Inf'.autEquiv M u) h).trans
    (autEquiv_infFunctorMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq Inf Inf' M z'))
  have := (underPost_isFiberedInGroupoids q hq (F.obj x)).fiber_isGroupoid
  have : IsIso (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M) :=
    IsGroupoid.all_isIso _
  exact fiberEndRestrict_injective_of_isIso (Under.post q)
    (underPost_isFiberedInGroupoids q hq (F.obj x))
    (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).1
    (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M).2
    (Functor.map_isIso Functor.Fiber.fiberInclusion
      (trivialComparisonHom A B S hS toS hA p q F hF x hx hp hq M)) e

/-- **Exactness of the six-term sequence of Stacks 0DNN at `Inf_w(M)`**: an infinitesimal
automorphism of the trivial deformation of `w` is determined by its two components.  Each
component is read off through the comparison of the trivial deformation of the component with
the image of the trivial deformation of `w`, and that comparison is invertible because the
lifts form a category fibred in groupoids; a morphism of the `2`-fibre product is determined
by its two components. -/
@[stacks 0DNN "exactness of the six-term sequence at Inf_w(M), i.e. injectivity of \
  Inf_w(M) → Inf_x(M) ⊕ Inf_z(M), which is what exactness of 0 → Inf_w(M) → ⋯ says (see \
  exact_zero_iff_injective). Also constructed in this module, and used to state that map, are \
  the four functoriality maps of Remark 07YA out of the 2-fibre product and out of 𝒳 \
  (infLinearMapOfOneMorphism, tangentLinearMapOfOneMorphism) and the zeros of Inf_x(M) and \
  T_x(M) (autEquiv_zero, liftEquiv_zero). The sequence with all five of its maps and the \
  exactness at all five of its places is Deformation.Artin.twoFibre_sixTermExact in \
  StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreInfExact."]
public theorem injective_twoFibreInfProj (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (toS : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A)))
    {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒵 : Type v₂} [Category.{w₂} 𝒵]
    {𝒴 : Type v₃} [Category.{w₃} 𝒴]
    (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒵 : 𝒵 ⥤ BigFppfOver B S hS)
    (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (P : 𝒳 ⥤ 𝒴) (Q : 𝒵 ⥤ 𝒴)
    (hP : P ⋙ p𝒴 = p𝒳) (hQ : Q ⋙ p𝒴 = p𝒵)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (w : TwoFibreProductOver p𝒳 p𝒵 p𝒴 P Q)
    (hw : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q).obj w = algebraOver A B S hS toS hA)
    (InfW : InfinitesimalAutomorphismFunctorData A B S hS toS hA
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) w hw
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ))
    (InfX : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒳 w.x (w.hx.trans hw) h𝒳)
    (InfZ : InfinitesimalAutomorphismFunctorData A B S hS toS hA p𝒵 w.y (w.hy.trans hw) h𝒵)
    (M : SiteModule A B) :
    Function.Injective (LinearMap.prod
        (infLinearMapOfOneMorphism A B S hS toS hA
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒳 (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴
              P Q) TwoFibreProductOver.fst_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳
              p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒳
            InfW InfX M)
        (infLinearMapOfOneMorphism A B S hS toS hA
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 P Q) p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴
              P Q) TwoFibreProductOver.snd_comp_eq w hw (TwoFibreProductOver.isFiberedInGroupoids p𝒳
              p𝒵 p𝒴 P Q h𝒳 h𝒵 h𝒴 hP hQ) h𝒵
            InfW InfZ M)) := by
  intro z z' h
  apply (InfW.autEquiv M).injective
  refine Functor.Fiber.hom_ext (Under.UnderMorphism.ext
    (TwoFibreProductOver.Hom.ext' ?_ ?_))
  · exact congrArg (fun m => m.1.right) (map_squareZeroLiftPost_eq_of_infFunctorMapOfOneMorphism_eq
      A B S hS toS hA _ _ (fst p𝒳 p𝒵 p𝒴 P Q) _ _ _ _ _ InfW InfX M z z'
      (congrArg Prod.fst h))
  · exact congrArg (fun m => m.1.right) (map_squareZeroLiftPost_eq_of_infFunctorMapOfOneMorphism_eq
      A B S hS toS hA _ _ (snd p𝒳 p𝒵 p𝒴 P Q) _ _ _ _ _ InfW InfZ M z z'
      (congrArg Prod.snd h))

end TwoFibreSixTerm

end Deformation.Artin

end
