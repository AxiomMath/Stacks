module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.IsoOfAlgebraIso
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDeformationSectionAlgebra
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.OnePointHom
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.Deformation.Artin.Infinitesimal.TrivialLift
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebraTangentRecord
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear
public import StacksFrontier.Deformation.Smooth.Pi
public import StacksFrontier.Deformation.TangentSpace.FiniteDimensional

/-!
# The tangent space of the stack of polarized schemes at a point over a field

Let `k` be a field and `x₀ = (X ⟶ Spec k, ℒ)` an object of `𝒫olarized` over `Spec k`. Following
the proof of [Stacks, Tag 0D4S], a lift of `x₀` over `Spec k[V]` gives the graded deformation
`Q = k[V] ⊕ ⨁_{d ≥ d₀} H^0(X', ℒ'^{⊗ d})` of the graded `k`-algebra
`P = k ⊕ ⨁_{d ≥ d₀} H^0(X, ℒ^{⊗ d})`, an object of the deformation category of Stacks 0D3L. Taking
classes gives a map from `T_{x₀}(V)` (Stacks 07Y9) to the tangent functor of that deformation
category, natural in `V`, hence linear. Its kernel is trivial: a lift whose graded deformation is
trivial is isomorphic, as a polarized family over `Spec k[V]`, to the trivial deformation (Stacks
0D4F), so it is the trivial lift. Since the target is finite dimensional at `V = k` (Stacks 0DVZ),
so is `T_{x₀}(k)`.

## Main definitions

* `AlgebraicGeometry.PolarizedDeformation.gradedCategory`: the deformation category of `P`.
* `AlgebraicGeometry.PolarizedDeformation.liftClassMap`: the class of the graded deformation of a
  lift.

## Main results

* `AlgebraicGeometry.PolarizedDeformation.liftClassMap_natural`: the class map is natural in `V`.
* `AlgebraicGeometry.PolarizedDeformation.exists_hom_of_classOf_eq`: two lifts with isomorphic
  graded deformations are isomorphic.
* `AlgebraicGeometry.PolarizedDeformation.finiteDimensional_tangentFunctor_obj`: **Stacks 0D4S
  (2)** for the tangent space.

## References

* [Stacks Project, Tag 0D4S](https://stacks.math.columbia.edu/tag/0D4S)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

open CategoryTheory AlgebraicGeometry

universe u

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.BasedCategory.ofFunctor

@[expose] public noncomputable section

namespace AlgebraicGeometry.PolarizedDeformation

open PolarizedFamily Deformation Deformation.Artin
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  (hT : Limits.IsTerminal (B.obj hS))
  {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  (x₀ : PolarizedFamily B)
  (hx : (polarizedSliceProjection B hS hT).obj x₀ = algebraOver k B S hS toS hk)

/-- The deformation category of the special fibre algebra, as a based category over `𝒞_k`. -/
abbrev gradedCategory : BasedCategory (ArtinianLocalAlgCat.{u, u, u} k k) :=
  BasedCategory.ofFunctor (gradedProjection B hS hT toS hk x₀ hx)

/-- The graded deformations of the special fibre algebra form a deformation category. -/
theorem isDeformationCategory_gradedProjection :
    IsDeformationCategory (gradedProjection B hS hT toS hk x₀ hx) := by
  let := AdmissibleDeformation.sectionRingAlgebraOver (deformation₀ B hS hT toS hk x₀ hx)
    (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
  let := AdmissibleDeformation.sectionGradedAlgebra (deformation₀ B hS hT toS hk x₀ hx)
    (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
  have : ∀ d, Module.Finite k (AdmissibleDeformation.sectionGrading
      (deformation₀ B hS hT toS hk x₀ hx) (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)) d) :=
    (specialFiberAlgebra B hS hT toS hk x₀ hx).finite
  exact Deformation.Examples.ProjectiveGradedAlgebra.isDeformationCategory_deformationCategory
    (Λ := k) _ (AdmissibleDeformation.sectionGrading (deformation₀ B hS hT toS hk x₀ hx)
      (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)))

variable {V W : FGModuleCat.{u} k}

/-- The morphism of graded deformations attached to a morphism of lifts. -/
def liftObjectHom (f : V ⟶ W) (yV : LiftFiber B hS hT toS hk x₀ hx V)
    (yW : LiftFiber B hS hT toS hk x₀ hx W) (φ : yW.1.right ⟶ yV.1.right)
    (hφ : (polarizedSliceProjection B hS hT).map φ =
      eqToHom (liftRightEq B hS hT toS hk x₀ hx W yW) ≫
        squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f) ≫
          eqToHom (liftRightEq B hS hT toS hk x₀ hx V yV).symm)
    (hcomm : yW.1.hom ≫ φ = yV.1.hom) :
    (liftObject B hS hT toS hk x₀ hx V yV).1 ⟶ (liftObject B hS hT toS hk x₀ hx W yW).1 :=
  Over.homMk (liftAlgebraHom B hS hT toS hk x₀ hx f yV yW φ hφ hcomm)
    (liftAlgebraHom_comp_toSpecialFiber B hS hT toS hk x₀ hx f yV yW φ hφ hcomm)

/-- The morphism of graded deformations attached to a morphism of lifts lies over
`k[V] ⟶ k[W]`. -/
theorem isHomLift_liftObjectHom (f : V ⟶ W) (yV : LiftFiber B hS hT toS hk x₀ hx V)
    (yW : LiftFiber B hS hT toS hk x₀ hx W) (φ : yW.1.right ⟶ yV.1.right)
    (hφ : (polarizedSliceProjection B hS hT).map φ =
      eqToHom (liftRightEq B hS hT toS hk x₀ hx W yW) ≫
        squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f) ≫
          eqToHom (liftRightEq B hS hT toS hk x₀ hx V yV).symm)
    (hcomm : yW.1.hom ≫ φ = yV.1.hom) :
    (gradedProjection B hS hT toS hk x₀ hx).IsHomLift
      ((artinianSquareZeroExtensionFunctor k k).map f)
      (liftObjectHom B hS hT toS hk x₀ hx f yV yW φ hφ hcomm) :=
  Functor.IsHomLift.map (p := gradedProjection B hS hT toS hk x₀ hx)
    (liftObjectHom B hS hT toS hk x₀ hx f yV yW φ hφ hcomm)

/-- The classes of the graded deformations of two lifts related by a morphism over
`k[V] ⟶ k[W]` correspond under the pushforward. -/
theorem map_classOf_liftObject (f : V ⟶ W) (yV : LiftFiber B hS hT toS hk x₀ hx V)
    (yW : LiftFiber B hS hT toS hk x₀ hx W) (φ : yW.1.right ⟶ yV.1.right)
    (hφ : (polarizedSliceProjection B hS hT).map φ =
      eqToHom (liftRightEq B hS hT toS hk x₀ hx W yW) ≫
        squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f) ≫
          eqToHom (liftRightEq B hS hT toS hk x₀ hx V yV).symm)
    (hcomm : yW.1.hom ≫ φ = yV.1.hom) :
    (isomorphismClasses (gradedCategory B hS hT toS hk x₀ hx)
        (isDeformationCategory_gradedProjection B hS hT toS hk x₀ hx).predeformation.cofibered).map
        ((artinianSquareZeroExtensionFunctor k k).map f)
        (classOf _ _ (liftObject B hS hT toS hk x₀ hx V yV)) =
      classOf _ _ (liftObject B hS hT toS hk x₀ hx W yW) := by
  have : (gradedCategory B hS hT toS hk x₀ hx).p.IsHomLift
      ((artinianSquareZeroExtensionFunctor k k).map f)
      (liftObjectHom B hS hT toS hk x₀ hx f yV yW φ hφ hcomm) :=
    isHomLift_liftObjectHom B hS hT toS hk x₀ hx f yV yW φ hφ hcomm
  exact map_classOf _ _ _ _ _ (liftObjectHom B hS hT toS hk x₀ hx f yV yW φ hφ hcomm)

/-- A fibre morphism of lifts lies over the identity of `Spec k[V]`. -/
theorem map_right_eq_of_fiberHom (y y' : LiftFiber B hS hT toS hk x₀ hx V) (e : y ⟶ y') :
    (polarizedSliceProjection B hS hT).map e.1.right =
      eqToHom (liftRightEq B hS hT toS hk x₀ hx V y) ≫
        squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map (𝟙 V)) ≫
          eqToHom (liftRightEq B hS hT toS hk x₀ hx V y').symm := by
  have := e.2
  have h1 := IsHomLift.fac' (Under.post (polarizedSliceProjection B hS hT))
    (𝟙 (Under.mk (eqToHom hx ≫ squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V))))
    e.1
  have h2 := congrArg (fun φ => φ.right) h1
  simp only [Under.comp_right, Under.eqToHom_right, Under.post_map, Category.id_comp,
    Under.homMk_right] at h2
  rw [h2, CategoryTheory.Functor.map_id, squareZeroOverMap_id, Category.id_comp, eqToHom_trans]

/-- **The class of the graded deformation of a lift**, as a map from the isomorphism classes of
lifts of `x₀` over `k[V]` to the isomorphism classes of graded deformations of the special fibre
algebra over `k[V]`. -/
def liftClassMap (V : FGModuleCat.{u} k) :
    squareZeroLiftClasses k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
        ((fgSiteModule B hk).obj V) →
      (isomorphismClasses (gradedCategory B hS hT toS hk x₀ hx)
        (isDeformationCategory_gradedProjection B hS hT toS hk x₀ hx).predeformation.cofibered).obj
        ((artinianSquareZeroExtensionFunctor k k).obj V) :=
  Quotient.lift (fun y => classOf _ _ (liftObject B hS hT toS hk x₀ hx V y)) (by
    rintro y y' ⟨e⟩
    have h := map_classOf_liftObject B hS hT toS hk x₀ hx (𝟙 V) y' y e.hom.1.right
      (map_right_eq_of_fiberHom B hS hT toS hk x₀ hx y y' e.hom) (Under.w e.hom.1)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
    exact h.symm)

/-- The class map sends the class of a lift to the class of its graded deformation. -/
theorem liftClassMap_mk (y : LiftFiber B hS hT toS hk x₀ hx V) :
    liftClassMap B hS hT toS hk x₀ hx V (Quotient.mk _ y) =
      classOf _ _ (liftObject B hS hT toS hk x₀ hx V y) := rfl

/-- **The class map is natural** with respect to pullback of lifts along module maps. -/
theorem liftClassMap_natural (f : V ⟶ W)
    (a : squareZeroLiftClasses k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
        ((fgSiteModule B hk).obj V))
    (b : squareZeroLiftClasses k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
        ((fgSiteModule B hk).obj W))
    (hab : IsPullbackOfSquareZeroLift k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
      ((fgSiteModule B hk).map f) a b) :
    (isomorphismClasses (gradedCategory B hS hT toS hk x₀ hx)
        (isDeformationCategory_gradedProjection B hS hT toS hk x₀ hx).predeformation.cofibered).map
        ((artinianSquareZeroExtensionFunctor k k).map f) (liftClassMap B hS hT toS hk x₀ hx V a) =
      liftClassMap B hS hT toS hk x₀ hx W b := by
  obtain ⟨a', b', rfl, rfl, φ, hφ, hcomm⟩ := hab
  have := hφ
  have hfac := IsHomLift.fac' (polarizedSliceProjection B hS hT)
    (squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f)) φ
  exact map_classOf_liftObject B hS hT toS hk x₀ hx f a' b' φ hfac hcomm

/-- The special fibre algebra is of finite type over `k` (conclusion (3) of Stacks 0D4F). -/
theorem finiteType_specialFiberAlgebra :
    letI := AdmissibleDeformation.sectionRingAlgebraOver (deformation₀ B hS hT toS hk x₀ hx)
      (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
    Algebra.FiniteType k ((deformation₀ B hS hT toS hk x₀ hx).sectionAlgebra.sectionRing ⊤) := by
  have : IsAffine (deformation₀ B hS hT toS hk x₀ hx).S' :=
    isAffine_of_baseEq (baseEq₀ B hS hT toS hk x₀ hx)
  have hfp :=
    (toDeformationDatum x₀ (compactSpace₀ B hS hT toS hk x₀ hx)).degreeBoundData.finitePresentation
      (deformation₀ B hS hT toS hk x₀ hx) ⊤ (isAffineOpen_top _)
  have h := (RingHom.FiniteType.of_finitePresentation hfp).comp
    (RingHom.FiniteType.of_surjective _
      (bijective_ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)).2)
  let := Stacks.SymGraded.AffinePieces.sectionRingAlgebra
    (deformation₀ B hS hT toS hk x₀ hx).sectionAlgebra ⊤
  show RingHom.FiniteType ((algebraMap Γ((deformation₀ B hS hT toS hk x₀ hx).S', ⊤)
    ((deformation₀ B hS hT toS hk x₀ hx).sectionAlgebra.sectionRing ⊤)).comp
      (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)))
  have heq : (algebraMap Γ((deformation₀ B hS hT toS hk x₀ hx).S', ⊤)
      ((deformation₀ B hS hT toS hk x₀ hx).sectionAlgebra.sectionRing ⊤)) =
      (deformation₀ B hS hT toS hk x₀ hx).sectionAlgebra.strHom ⊤ :=
    RingHom.ext fun r => Stacks.SymGraded.AffinePieces.algebraMap_sectionRingAlgebra _ _ r
  rwa [heq]

omit [Field k] in
/-- Restriction of global functions along the identification of two bases with one spectrum. -/
theorem appTop_eqToHom_ringOfBaseEq {X₁ X₂ : Scheme.{u}} {R : CommRingCat.{u}} (h₁ : X₁ = Spec R)
    (h₂ : X₂ = Spec R) (s : R) :
    (eqToHom (h₁.trans h₂.symm)).appTop (ringOfBaseEq h₂ s) = ringOfBaseEq h₁ s := by
  subst h₁
  have h₂' := h₂.symm
  subst h₂'
  rfl

/-- The scalar action of `k[V]` on the graded algebra of a lift is multiplication by the image
of the scalar in the global functions. -/
theorem smul_liftAlgebra_eq (y : LiftFiber B hS hT toS hk x₀ hx V)
    (s : (liftAlgebra B hS hT toS hk x₀ hx V y).base)
    (z : (liftDef B hS hT toS hk x₀ hx V y).sectionAlgebra.sectionRing ⊤) :
    s • (show (liftAlgebra B hS hT toS hk x₀ hx V y).carrier from z) =
      (liftDef B hS hT toS hk x₀ hx V y).sectionAlgebra.strHom ⊤
        (ringOfBaseEq (liftBaseEq B hS hT toS hk x₀ hx V y) s) * z := by
  let := Stacks.SymGraded.AffinePieces.sectionRingAlgebra
    (liftDef B hS hT toS hk x₀ hx V y).sectionAlgebra ⊤
  rw [Algebra.smul_def]
  exact congrArg (· * z) (Stacks.SymGraded.AffinePieces.algebraMap_sectionRingAlgebra _ _ _)

/-- **Two lifts with isomorphic graded deformations are isomorphic polarized families over the
identity of `Spec k[V]`**: the graded isomorphism of global section algebras comes from an
isomorphism of the sheaf-level algebras over the one-point base, hence (Stacks 0D4F) from an
isomorphism of the deformations. -/
theorem exists_hom_of_classOf_eq (y y₀ : LiftFiber B hS hT toS hk x₀ hx V)
    (h : classOf (gradedCategory B hS hT toS hk x₀ hx)
        (isDeformationCategory_gradedProjection B hS hT toS hk x₀ hx).predeformation.cofibered
        (liftObject B hS hT toS hk x₀ hx V y) =
      classOf _ _ (liftObject B hS hT toS hk x₀ hx V y₀)) :
    ∃ Φ : y.1.right ⟶ y₀.1.right, (polarizedSliceProjection B hS hT).map Φ =
      eqToHom ((liftRightEq B hS hT toS hk x₀ hx V y).trans
        (liftRightEq B hS hT toS hk x₀ hx V y₀).symm) := by
  obtain ⟨e⟩ := (classOf_eq_iff_nonempty_iso _ _ _).mp h
  let D := liftDef B hS hT toS hk x₀ hx V y
  let D₀ := liftDef B hS hT toS hk x₀ hx V y₀
  let P := toDeformationDatum x₀ (compactSpace₀ B hS hT toS hk x₀ hx)
  have hg : D.S' = D₀.S' :=
    (liftBaseEq B hS hT toS hk x₀ hx V y).trans (liftBaseEq B hS hT toS hk x₀ hx V y₀).symm
  let α : (D₀.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).sectionRing ⊤ →+*
      (D.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).sectionRing ⊤ :=
    e.inv.1.left.map
  have hbase : e.inv.1.left.base = 𝟙 _ := by
    have := e.inv.2
    have h' := IsHomLift.fac' (gradedCategory B hS hT toS hk x₀ hx).p
      (𝟙 ((artinianSquareZeroExtensionFunctor k k).obj V)) e.inv.1
    exact h'.trans (by rw [Category.id_comp, eqToHom_trans]; rfl)
  have h1 : ∀ z, e.hom.1.left.map (α z) = z := fun z =>
    DFunLike.congr_fun (congrArg (fun f => f.1.left.map) e.inv_hom_id) z
  have h2 : ∀ z, α (e.hom.1.left.map z) = z := fun z =>
    DFunLike.congr_fun (congrArg (fun f => f.1.left.map) e.hom_inv_id) z
  have hα : Function.Bijective α :=
    ⟨fun a b hab => by rw [← h1 a, ← h1 b, hab], fun z => ⟨_, h2 z⟩⟩
  have hgr : ∀ (n : ℕ)
      (z : (D₀.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).sectionRing ⊤),
      z ∈ (D₀.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).grading ⊤ n →
        α z ∈ (D.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).grading ⊤ n :=
    fun n z hz => e.inv.1.left.map_mem n z hz
  have hsl : ∀ (r : Γ(D₀.S', ⊤))
      (z : (D₀.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).sectionRing ⊤),
      α ((D₀.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).strHom ⊤ r * z) =
        (D.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).strHom ⊤
          ((eqToHom hg).appTop r) * α z := by
    intro r z
    obtain ⟨s, rfl⟩ := (bijective_ringOfBaseEq (liftBaseEq B hS hT toS hk x₀ hx V y₀)).2 r
    have hs := e.inv.1.left.map_smul s z
    have hb1 : e.inv.1.left.base.hom s = s := congrArg (fun f => f.hom s) hbase
    have e₀ := (smul_liftAlgebra_eq B hS hT toS hk x₀ hx y₀ s z).symm
    have e₁ := smul_liftAlgebra_eq B hS hT toS hk x₀ hx y s (α z)
    refine (congrArg α e₀).trans (hs.trans ?_)
    refine (congrArg (fun r : (liftAlgebra B hS hT toS hk x₀ hx V y).base =>
      r • (show (liftAlgebra B hS hT toS hk x₀ hx V y).carrier from α z)) hb1).trans (e₁.trans ?_)
    exact congrArg
      (fun r => (D.truncatedSectionAlgebra P.degreeBound P.degreeBound_pos).strHom ⊤ r * α z)
      (appTop_eqToHom_ringOfBaseEq (liftBaseEq B hS hT toS hk x₀ hx V y)
        (liftBaseEq B hS hT toS hk x₀ hx V y₀) s).symm
  obtain ⟨γ, hγ, -⟩ :=
    Stacks.AlgebraicGeometry.RelativeProjBridge.exists_sheafGradedAlgebraHom_isIso_of_sectionRing
      (eqToHom hg) (opens_eq_bot_or_top_of_baseEq (liftBaseEq B hS hT toS hk x₀ hx V y₀)) α hα hgr
      hsl
  have hb : y.1.right.base = y₀.1.right.base :=
    congrArg Over.left ((liftRightEq B hS hT toS hk x₀ hx V y).trans
      (liftRightEq B hS hT toS hk x₀ hx V y₀).symm)
  let Φ : y.1.right ⟶ y₀.1.right :=
    { baseMap := eqToHom hb
      totalMap := (AdmissibleDeformation.totalIsoOfAlgebraIso D D₀ (eqToIso hg) γ hγ).hom
      cartesian := by
        rw [eqToHom_map]
        exact AdmissibleDeformation.isPullback_totalIsoOfAlgebraIso D D₀ (eqToIso hg) γ hγ
      lineBundleIso := AdmissibleDeformation.polarizationIsoOfAlgebraIso D D₀ (eqToIso hg) γ hγ }
  refine ⟨Φ, ?_⟩
  apply Over.OverMorphism.ext
  show (((polarizedProjection B).sliceAtTerminal hT).map Φ).left = _
  rw [Functor.sliceAtTerminal_map_left, Over.eqToHom_left]
  rfl

/-- **The tangent space `T_{x₀}(k)` is finite dimensional as soon as the class map has trivial
kernel at `k`.** Linearity of the class map comes from its naturality (Stacks 06I7), and the
target is finite dimensional by Stacks 0DVZ. -/
theorem finiteDimensional_of_liftClassMap_eq_zero
    (T : TangentFunctorData k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx)
    (hker : ∀ a : T.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k)),
      liftClassMap B hS hT toS hk x₀ hx (FGModuleCat.of k k) (T.liftEquiv _ a) =
        liftClassMap B hS hT toS hk x₀ hx (FGModuleCat.of k k) (T.liftEquiv _ 0) → a = 0) :
    FiniteDimensional k (T.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k))) := by
  let hD := isDeformationCategory_gradedProjection B hS hT toS hk x₀ hx
  let 𝓖 := gradedCategory B hS hT toS hk x₀ hx
  let LF := associatedTangentSpaceModuleStructureUnlifted 𝓖 hD.predeformation
    (schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory _ hD)
  let U := associatedTangentSpaceSetFunctor 𝓖 hD.predeformation.cofibered
  let eF (V : FGModuleCat.{u} k) : (LF.functor ⋙ forget (ModuleCat k)).obj V = U.obj V :=
    congrArg (fun H => H.obj V) LF.forget_comp
  have : (fgSiteModule B hk).Additive := ⟨rfl⟩
  have : (fgSiteModule B hk).Linear k := ⟨by intros; rfl⟩
  let F := fgSiteModule B hk ⋙ T.functor
  let t : ∀ V : FGModuleCat.{u} k, F.obj V → LF.functor.obj V := fun V a =>
    cast (eF V).symm (liftClassMap B hS hT toS hk x₀ hx V (T.liftEquiv _ a))
  have ht : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W) (a : F.obj V),
      t W ((F.map f) a) = (LF.functor.map f) (t V a) := by
    intro V W f a
    apply cast_inj_of_eq (eF W)
    rw [moduleFunctor_map_cast k LF.functor U LF.forget_comp f (t V a)]
    simp only [t, cast_cast, cast_eq]
    exact (liftClassMap_natural B hS hT toS hk x₀ hx f _ _
      (T.liftEquiv_natural ((fgSiteModule B hk).map f) a)).symm
  have hlin := isLinearMap_of_natural_on_fgModules k F LF.functor t ht
  have hfin : FiniteDimensional k (LF.functor.obj (FGModuleCat.of k k)) := by
    let := AdmissibleDeformation.sectionRingAlgebraOver (deformation₀ B hS hT toS hk x₀ hx)
      (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
    let := AdmissibleDeformation.sectionGradedAlgebra (deformation₀ B hS hT toS hk x₀ hx)
      (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
    have : ∀ d, Module.Finite k (AdmissibleDeformation.sectionGrading
        (deformation₀ B hS hT toS hk x₀ hx) (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)) d) :=
      (specialFiberAlgebra B hS hT toS hk x₀ hx).finite
    have := finiteType_specialFiberAlgebra B hS hT toS hk x₀ hx
    exact (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hD).mp
      (Deformation.Examples.ProjectiveGradedAlgebra.finiteDimensional_tangentSpace (Λ := k) _
        (AdmissibleDeformation.sectionGrading (deformation₀ B hS hT toS hk x₀ hx)
          (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))))
  have hinj' : Function.Injective (t (FGModuleCat.of k k)) := by
    intro a b hab
    have h0 : t (FGModuleCat.of k k) (a - b) = t (FGModuleCat.of k k) 0 := by
      rw [hlin.map_sub, hlin.map_zero]
      exact sub_eq_zero.mpr hab
    exact sub_eq_zero.mp (hker (a - b) (cast_inj_of_eq (eF (FGModuleCat.of k k)).symm h0))
  exact FiniteDimensional.of_injective (IsLinearMap.mk' _ hlin) hinj'

/-- **Stacks 0D4S (2), tangent space.** For a field `k` and a polarized proper scheme `x₀` over
`Spec k`, the value `T_{x₀}(k)` of the tangent functor of Stacks 07Y9 is finite dimensional. The
statement holds for every tangent functor datum. -/
theorem finiteDimensional_tangentFunctor_obj
    (T : TangentFunctorData k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx) :
    FiniteDimensional k (T.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k))) := by
  have hp : (polarizedSliceProjection B hS hT).IsFiberedInGroupoids :=
    polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT
  refine finiteDimensional_of_liftClassMap_eq_zero B hS hT toS hk x₀ hx T fun a ha => ?_
  obtain ⟨y, hy⟩ := Quotient.exists_rep (T.liftEquiv _ a)
  rw [liftEquiv_zero k B S hS toS hk _ x₀ hx hp T, ← hy] at ha
  obtain ⟨Φ, hΦ⟩ := exists_hom_of_classOf_eq B hS hT toS hk x₀ hx y _ ha
  exact eq_zero_of_hom_trivialDeformation k B S hS toS hk _ x₀ hx hp T a y hy.symm Φ hΦ

end AlgebraicGeometry.PolarizedDeformation

end
