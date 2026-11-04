module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.AffineSectionAlgebra
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreserving
public import StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison
public import StacksFrontier.Deformation.Examples.Geometric.Base
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebrasRimSchlessinger

/-!
# Deformations of a polarized scheme over a field as graded algebras

Let `x₀ = (X ⟶ Spec k, ℒ)` be an object of the stack `𝒫olarized` of polarized proper schemes over
`Spec k`, presented over the big fppf site of a terminal base (`polarizedSliceProjection`). The
proof of [Stacks, Tag 0D4S] attaches to `x₀` the graded `k`-algebra
`P = k ⊕ ⨁_{d ≥ d₀} H^0(X, ℒ^{⊗ d})` and to a lift `x₀ ⟶ x'` of `x₀` over `Spec k[V]` the graded
`k[V]`-algebra `Q = k[V] ⊕ ⨁_{d ≥ d₀} H^0(X', ℒ'^{⊗ d})` together with its reduction `Q ⟶ P`, an
object of the deformation category of `P` of Stacks 0D3L. This file builds these objects and the
morphisms between them attached to morphisms of lifts.

## Main definitions

* `AlgebraicGeometry.PolarizedFamily.toDeformationDatum`, `liftDeformation`, `liftHom`: polarized
  families and morphisms under `x₀` read as the data of [Stacks, Tag 0D4F].
* `AlgebraicGeometry.PolarizedDeformation.specialFiberAlgebra`: the graded algebra `P`.
* `AlgebraicGeometry.PolarizedDeformation.liftAlgebra`, `toSpecialFiber`, `liftObject`: the graded
  algebra `Q` of a lift over `k[V]`, its reduction, and the resulting object of the deformation
  category of `P`.
* `AlgebraicGeometry.PolarizedDeformation.liftAlgebraHom`: the morphism attached to a morphism of
  lifts over `k[V] ⟶ k[W]`.

## Main results

* `AlgebraicGeometry.PolarizedDeformation.specialFiberAlgebra_eq`: `P` is the special fibre object
  of Stacks 0D3L.
* `AlgebraicGeometry.PolarizedDeformation.liftAlgebraHom_comp_toSpecialFiber`.

## References

* [Stacks Project, Tag 0D4S](https://stacks.math.columbia.edu/tag/0D4S)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily (AdmissibleDeformation)

universe u

@[expose] public noncomputable section

namespace AlgebraicGeometry.PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- A polarized family over a quasi-compact base, read as the datum `(f : X ⟶ S, ℒ)` of
[Stacks, Tag 0D4F]. -/
def toDeformationDatum (x : PolarizedFamily B) (hx : CompactSpace (B.inclusion.obj x.base)) :
    Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.{u} where
  X := x.total
  S := B.inclusion.obj x.base
  f := x.toBase
  L := x.lineBundle
  isProper := x.proper
  flat := x.flat
  finitePresentation := x.finitePresentation
  invertible := x.invertible
  isRelativelyAmple := x.relativelyAmple
  compactSpace := hx

/-- A morphism `x ⟶ y` of polarized families over a thickening of bases, read as an admissible
deformation of `x` in the sense of [Stacks, Tag 0D4F]. -/
def liftDeformation {x y : PolarizedFamily B} (hx : CompactSpace (B.inclusion.obj x.base))
    (a : x ⟶ y) (ha : Stacks.Thickenings.IsThickening (B.inclusion.map a.baseMap)) :
    (toDeformationDatum x hx).AdmissibleDeformation where
  S' := B.inclusion.obj y.base
  X' := y.total
  i := B.inclusion.map a.baseMap
  i' := a.totalMap
  f' := y.toBase
  isThickening := ha
  isPullback := a.cartesian
  isProper := y.proper
  flat := y.flat
  finitePresentation := y.finitePresentation
  L' := y.lineBundle
  invertible := y.invertible
  polarization := a.lineBundleIso.symm

/-- A morphism of polarized families under `x`, read as a morphism of admissible deformations. -/
def liftHom {x y y' : PolarizedFamily B} (hx : CompactSpace (B.inclusion.obj x.base))
    {a : x ⟶ y} {a' : x ⟶ y'} (ha : Stacks.Thickenings.IsThickening (B.inclusion.map a.baseMap))
    (ha' : Stacks.Thickenings.IsThickening (B.inclusion.map a'.baseMap)) (ψ : y ⟶ y')
    (h : a ≫ ψ = a') :
    AdmissibleDeformation.Hom (liftDeformation hx a ha) (liftDeformation hx a' ha') where
  base := B.inclusion.map ψ.baseMap
  total := ψ.totalMap
  isPullback := ψ.cartesian
  base_comm := by
    change B.inclusion.map a.baseMap ≫ B.inclusion.map ψ.baseMap = B.inclusion.map a'.baseMap
    rw [← Functor.map_comp, ← h]
    rfl
  total_comm := by
    change a.totalMap ≫ ψ.totalMap = a'.totalMap
    rw [← h]
    rfl
  polarization := ψ.lineBundleIso

/-- `liftHom` sends composites to composites. -/
theorem liftHom_comp {x y y' y'' : PolarizedFamily B} (hx : CompactSpace (B.inclusion.obj x.base))
    {a : x ⟶ y} {a' : x ⟶ y'} {a'' : x ⟶ y''}
    (ha : Stacks.Thickenings.IsThickening (B.inclusion.map a.baseMap))
    (ha' : Stacks.Thickenings.IsThickening (B.inclusion.map a'.baseMap))
    (ha'' : Stacks.Thickenings.IsThickening (B.inclusion.map a''.baseMap)) (ψ : y ⟶ y')
    (χ : y' ⟶ y'') (h : a ≫ ψ = a') (h' : a' ≫ χ = a'') :
    liftHom hx ha ha'' (ψ ≫ χ) (by rw [← h', ← h, Category.assoc]) =
      (liftHom hx ha ha' ψ h).comp (liftHom hx ha' ha'' χ h') := rfl

end AlgebraicGeometry.PolarizedFamily

end

@[expose] public noncomputable section

namespace AlgebraicGeometry.PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- `liftHom` only depends on the morphism. -/
theorem liftHom_congr {x y y' : PolarizedFamily B} (hx : CompactSpace (B.inclusion.obj x.base))
    {a : x ⟶ y} {a' : x ⟶ y'} (ha : Stacks.Thickenings.IsThickening (B.inclusion.map a.baseMap))
    (ha' : Stacks.Thickenings.IsThickening (B.inclusion.map a'.baseMap)) {ψ ψ' : y ⟶ y'}
    (hψ : ψ = ψ') (h : a ≫ ψ = a') (h' : a ≫ ψ' = a') :
    liftHom hx ha ha' ψ h = liftHom hx ha ha' ψ' h' := by
  subst hψ
  rfl

/-- The global functions of a scheme identified with `Spec R`, as a ring homomorphism out of
`R`. -/
def ringOfBaseEq {X : Scheme.{u}} {R : CommRingCat.{u}} (h : X = Spec R) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ (eqToHom h).appTop).hom

/-- The identification of global functions is bijective. -/
theorem bijective_ringOfBaseEq {X : Scheme.{u}} {R : CommRingCat.{u}} (h : X = Spec R) :
    Function.Bijective (ringOfBaseEq h) := by
  subst h
  have e : (Scheme.ΓSpecIso R).inv ≫ (eqToHom (rfl : Spec R = Spec R)).appTop =
      (Scheme.ΓSpecIso R).inv := by
    rw [eqToHom_refl, Scheme.Hom.id_appTop, Category.comp_id]
  rw [ringOfBaseEq, e]
  exact (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.bijective

/-- A morphism of schemes identified with `Spec` of a ring map acts on global functions by that
ring map. -/
theorem appLE_ringOfBaseEq {X Y : Scheme.{u}} {R R' : CommRingCat.{u}} (hX : X = Spec R)
    (hY : Y = Spec R') (f : X ⟶ Y) (b : R' ⟶ R)
    (hf : f ≫ eqToHom hY = eqToHom hX ≫ Spec.map b) (r : R') :
    f.appLE ⊤ ⊤ le_rfl (ringOfBaseEq hY r) = ringOfBaseEq hX (b r) := by
  subst hX hY
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hf
  subst hf
  simp only [ringOfBaseEq, eqToHom_refl, Category.comp_id, Scheme.Hom.id_appTop]
  have hn := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality b)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hn
  refine Eq.trans ?_ hn.symm
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso R').inv.hom r))
    (Scheme.Hom.appLE_preimage_self (Spec.map b) ⊤)

/-- The spectrum of an Artinian local ring has only the opens `⊥` and `⊤`. -/
theorem opens_eq_bot_or_top_of_baseEq {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]
    [IsArtinianRing R] (h : X = Spec R) (U : X.Opens) : U = ⊥ ∨ U = ⊤ := by
  subst h
  have : Subsingleton (Spec R) := by
    refine ⟨fun (p q : PrimeSpectrum R) => ?_⟩
    have hp : p.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p.asIdeal
    have hq : q.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime q.asIdeal
    exact PrimeSpectrum.ext ((IsLocalRing.eq_maximalIdeal hp).trans
      (IsLocalRing.eq_maximalIdeal hq).symm)
  by_cases hU : (U : Set (Spec R)).Nonempty
  · right
    obtain ⟨x, hx⟩ := hU
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact (Subsingleton.elim x y) ▸ hx
  · left
    ext y
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hy => hU ⟨y, hy⟩

/-- A scheme identified with the spectrum of an Artinian local ring has a single point. -/
theorem subsingleton_of_baseEq {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]
    [IsArtinianRing R] (h : X = Spec R) : Subsingleton X := by
  subst h
  refine ⟨fun (p q : PrimeSpectrum R) => ?_⟩
  have hp : p.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p.asIdeal
  have hq : q.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime q.asIdeal
  exact PrimeSpectrum.ext ((IsLocalRing.eq_maximalIdeal hp).trans
    (IsLocalRing.eq_maximalIdeal hq).symm)

/-- The closed point of a scheme identified with the spectrum of a local ring. -/
def pointOfBaseEq {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R] (h : X = Spec R) : X :=
  (eqToHom h.symm).base (IsLocalRing.closedPoint R)

/-- On a scheme with only the opens `⊥` and `⊤`, every open containing a point is everything. -/
theorem eq_top_of_mem_of_bot_or_top {X : Scheme.{u}} (hX : ∀ U : X.Opens, U = ⊥ ∨ U = ⊤)
    (s : X) (U : X.Opens) (hs : s ∈ U) : U = ⊤ := by
  rcases hX U with rfl | rfl
  · exact absurd hs (by simp)
  · rfl

/-- A scheme identified with a spectrum is affine. -/
theorem isAffine_of_baseEq {X : Scheme.{u}} {R : CommRingCat.{u}} (h : X = Spec R) :
    IsAffine X := by
  subst h
  infer_instance

end AlgebraicGeometry.PolarizedFamily


/- The goals below mention fibres of structure functors and the induced functor on under
categories, built from definitions that the `implicit` transparency level does not unfold. -/
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion CategoryTheory.Under.post

namespace AlgebraicGeometry.PolarizedDeformation

open PolarizedFamily Deformation Deformation.Artin
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  (hT : Limits.IsTerminal (B.obj hS))
  {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  (x₀ : PolarizedFamily B)
  (hx : (polarizedSliceProjection B hS hT).obj x₀ = algebraOver k B S hS toS hk)

include hx in
/-- The base of the polarized family over the field, identified with `Spec k`. -/
theorem baseEq₀ : B.inclusion.obj x₀.base = Spec (.of k) :=
  congrArg (fun V => B.inclusion.obj V.left) hx

include hx in
/-- The base of the polarized family over the field is quasi-compact. -/
theorem compactSpace₀ : CompactSpace (B.inclusion.obj x₀.base) := by
  rw [baseEq₀ B hS hT toS hk x₀ hx]
  infer_instance

/-- The identity of the polarized family over the field is a thickening of its base. -/
theorem isThickening_id_baseMap :
    Stacks.Thickenings.IsThickening (B.inclusion.map (𝟙 x₀ : x₀ ⟶ x₀).baseMap) := by
  show Stacks.Thickenings.IsThickening (𝟙 (B.inclusion.obj x₀.base))
  exact ⟨inferInstance, Function.surjective_id⟩

/-- The polarized family over the field as its own (trivial) admissible deformation. -/
def deformation₀ :
    (toDeformationDatum x₀ (compactSpace₀ B hS hT toS hk x₀ hx)).AdmissibleDeformation :=
  liftDeformation (compactSpace₀ B hS hT toS hk x₀ hx) (𝟙 x₀) (isThickening_id_baseMap B x₀)

/-- **The graded algebra `P = k ⊕ ⨁_{d ≥ d₀} H^0(X, ℒ^{⊗ d})` of the polarized family over the
field**, as the special fibre of the category of Stacks 0D3L. -/
def specialFiberAlgebra : Deformation.Examples.ProjectiveGradedAlgebra.{u, u, u, u} k k :=
  (deformation₀ B hS hT toS hk x₀ hx).toProjectiveGradedAlgebra
    (Deformation.Examples.residueFieldBase k k) (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
    (bijective_ringOfBaseEq _) (pointOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
    (eq_top_of_mem_of_bot_or_top (opens_eq_bot_or_top_of_baseEq (baseEq₀ B hS hT toS hk x₀ hx)) _)

variable (V : FGModuleCat.{u} k)

/-- The fibre of lifts of the polarized family over the field along `Spec k ⟶ Spec k[V]`. -/
abbrev LiftFiber :=
  (Under.post (polarizedSliceProjection B hS hT)).Fiber
    (Under.mk (eqToHom hx ≫ squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)))

/-- The base of a lift, identified with `Spec k[V]`. -/
theorem liftBaseEq (y : LiftFiber B hS hT toS hk x₀ hx V) :
    B.inclusion.obj y.1.right.base = Spec (squareZeroRing k ((fgSiteModule B hk).obj V).obj) :=
  congrArg (fun W => B.inclusion.obj W.left) (congrArg Under.right y.2)

/-- The base map of a lift is the closed immersion `Spec k ⟶ Spec k[V]`. -/
theorem liftBaseMap_eq (y : LiftFiber B hS hT toS hk x₀ hx V) :
    B.inclusion.map y.1.hom.baseMap ≫ eqToHom (liftBaseEq B hS hT toS hk x₀ hx V y) =
      eqToHom (baseEq₀ B hS hT toS hk x₀ hx) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k
          ((fgSiteModule B hk).obj V).obj).toRingHom) := by
  have hw := Under.w (eqToHom y.2)
  rw [Under.eqToHom_right] at hw
  change (polarizedSliceProjection B hS hT).map y.1.hom ≫ eqToHom _ =
    eqToHom hx ≫ squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V) at hw
  have e1 : ∀ {W₁ W₂ : BigFppfOver B S hS} (h : W₁ = W₂),
      B.inclusion.map (eqToHom h).left =
        eqToHom (congrArg (fun W => B.inclusion.obj W.left) h) := by
    rintro W₁ W₂ rfl
    rfl
  have hl := congrArg (fun φ => B.inclusion.map φ.left) hw
  simp only [Over.comp_left, Functor.map_comp] at hl
  rwa [e1, e1] at hl

/-- The base map of a lift is a thickening. -/
theorem isThickening_liftBaseMap (y : LiftFiber B hS hT toS hk x₀ hx V) :
    Stacks.Thickenings.IsThickening (B.inclusion.map y.1.hom.baseMap) := by
  have h := liftBaseMap_eq B hS hT toS hk x₀ hx V y
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom k k ((fgSiteModule B hk).obj V).obj) :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
      (eqToHom (liftBaseEq B hS hT toS hk x₀ hx V y)), h]
    exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance
      (IsClosedImmersion.spec_of_surjective _ hsurj)
  · have : IsLocalRing (squareZeroRing k ((fgSiteModule B hk).obj V).obj) :=
      inferInstanceAs (IsLocalRing ((artinianSquareZeroExtensionFunctor k k).obj V))
    have : IsArtinianRing (squareZeroRing k ((fgSiteModule B hk).obj V).obj) :=
      inferInstanceAs (IsArtinianRing ((artinianSquareZeroExtensionFunctor k k).obj V))
    have := subsingleton_of_baseEq (liftBaseEq B hS hT toS hk x₀ hx V y)
    intro t
    exact ⟨(eqToHom (baseEq₀ B hS hT toS hk x₀ hx).symm).base (IsLocalRing.closedPoint k),
      Subsingleton.elim _ _⟩

/-- A lift, as an admissible deformation of the polarized family over the field. -/
abbrev liftDef (y : LiftFiber B hS hT toS hk x₀ hx V) :
    (toDeformationDatum x₀ (compactSpace₀ B hS hT toS hk x₀ hx)).AdmissibleDeformation :=
  liftDeformation (compactSpace₀ B hS hT toS hk x₀ hx) y.1.hom
    (isThickening_liftBaseMap B hS hT toS hk x₀ hx V y)

/-- The trivial square-zero extension `k[V]` is local. -/
instance (V : FGModuleCat.{u} k) :
    IsLocalRing (squareZeroRing k ((fgSiteModule B hk).obj V).obj) :=
  inferInstanceAs (IsLocalRing ((artinianSquareZeroExtensionFunctor k k).obj V))

/-- The trivial square-zero extension `k[V]` is Artinian. -/
instance (V : FGModuleCat.{u} k) :
    IsArtinianRing (squareZeroRing k ((fgSiteModule B hk).obj V).obj) :=
  inferInstanceAs (IsArtinianRing ((artinianSquareZeroExtensionFunctor k k).obj V))

/-- **The graded algebra of global sections of a lift over `k[V]`**, as an object of the category
of Stacks 0D3L over `k[V]`. -/
def liftAlgebra (y : LiftFiber B hS hT toS hk x₀ hx V) :
    Deformation.Examples.ProjectiveGradedAlgebra.{u, u, u, u} k k :=
  (liftDef B hS hT toS hk x₀ hx V y).toProjectiveGradedAlgebra
    ((artinianSquareZeroExtensionFunctor k k).obj V)
    (ringOfBaseEq (liftBaseEq B hS hT toS hk x₀ hx V y)) (bijective_ringOfBaseEq _)
    (pointOfBaseEq (liftBaseEq B hS hT toS hk x₀ hx V y))
    (eq_top_of_mem_of_bot_or_top
      (opens_eq_bot_or_top_of_baseEq (liftBaseEq B hS hT toS hk x₀ hx V y)) _)

/-- The map to the residue field of `k[V]` in `𝒞_k` is the first projection. -/
theorem terminal_from_hom_apply (r : (artinianSquareZeroExtensionFunctor k k).obj V) :
    ((Deformation.Examples.isTerminal_residueFieldBase (Λ := k) (k := k)).from
      ((artinianSquareZeroExtensionFunctor k k).obj V)).hom r = r.fst := by
  have h := ((Deformation.Examples.isTerminal_residueFieldBase (Λ := k) (k := k)).from
      ((artinianSquareZeroExtensionFunctor k k).obj V)).residue_comm r
  rwa [Deformation.Examples.residueFieldBase_residueEquiv_residue] at h

/-- The lift, as a morphism of admissible deformations out of the trivial one. -/
def liftHom₀ (y : LiftFiber B hS hT toS hk x₀ hx V) :
    AdmissibleDeformation.Hom (deformation₀ B hS hT toS hk x₀ hx)
      (liftDef B hS hT toS hk x₀ hx V y) :=
  liftHom (compactSpace₀ B hS hT toS hk x₀ hx) (isThickening_id_baseMap B x₀)
    (isThickening_liftBaseMap B hS hT toS hk x₀ hx V y) y.1.hom (Category.id_comp _)

/-- **The reduction of the graded algebra of a lift to the special fibre**, as a morphism of the
category of Stacks 0D3L over `k[V] ⟶ k`. -/
def toSpecialFiber (y : LiftFiber B hS hT toS hk x₀ hx V) :
    liftAlgebra B hS hT toS hk x₀ hx V y ⟶ specialFiberAlgebra B hS hT toS hk x₀ hx :=
  haveI : IsAffine (deformation₀ B hS hT toS hk x₀ hx).S' :=
    isAffine_of_baseEq (baseEq₀ B hS hT toS hk x₀ hx)
  haveI : IsAffine (liftDef B hS hT toS hk x₀ hx V y).S' :=
    isAffine_of_baseEq (liftBaseEq B hS hT toS hk x₀ hx V y)
  AdmissibleDeformation.toProjectiveGradedAlgebraHom (liftHom₀ B hS hT toS hk x₀ hx V y) _ _ _ _ _ _
    ((Deformation.Examples.isTerminal_residueFieldBase (Λ := k) (k := k)).from
      ((artinianSquareZeroExtensionFunctor k k).obj V))
    (fun r => (appLE_ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)
        (liftBaseEq B hS hT toS hk x₀ hx V y) _ _ (liftBaseMap_eq B hS hT toS hk x₀ hx V y)
          r).trans
      (congrArg (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)) (terminal_from_hom_apply V r).symm))

/-- The special fibre algebra is the special fibre object of Stacks 0D3L of its own graded
algebra. -/
theorem specialFiberAlgebra_eq :
    letI := AdmissibleDeformation.sectionRingAlgebraOver (deformation₀ B hS hT toS hk x₀ hx)
      (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
    letI := AdmissibleDeformation.sectionGradedAlgebra (deformation₀ B hS hT toS hk x₀ hx)
      (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
    haveI : ∀ d, Module.Finite k (AdmissibleDeformation.sectionGrading
        (deformation₀ B hS hT toS hk x₀ hx) (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)) d) :=
      (specialFiberAlgebra B hS hT toS hk x₀ hx).finite
    specialFiberAlgebra B hS hT toS hk x₀ hx =
      Deformation.Examples.ProjectiveGradedAlgebra.specialFiber (Λ := k)
        ((deformation₀ B hS hT toS hk x₀ hx).sectionAlgebra.sectionRing ⊤)
        (AdmissibleDeformation.sectionGrading (deformation₀ B hS hT toS hk x₀ hx)
          (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))) := rfl

omit hx in
/-- A morphism of polarized families lying over a morphism of the big fppf site over `S`: its base
map, read in schemes. -/
theorem baseMap_eq_of_map_eq {y₁ y₂ : PolarizedFamily B} (f : y₁ ⟶ y₂)
    {W₁ W₂ : AlgebraicGeometry.BigFppfOver B S hS} (g : W₁ ⟶ W₂)
    (h₁ : (polarizedSliceProjection B hS hT).obj y₁ = W₁)
    (h₂ : (polarizedSliceProjection B hS hT).obj y₂ = W₂)
    (hf : (polarizedSliceProjection B hS hT).map f = eqToHom h₁ ≫ g ≫ eqToHom h₂.symm) :
    B.inclusion.map f.baseMap ≫ eqToHom (congrArg (fun W => B.inclusion.obj W.left) h₂) =
      eqToHom (congrArg (fun W => B.inclusion.obj W.left) h₁) ≫ B.inclusion.map g.left := by
  subst h₁ h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf ⊢
  exact congrArg (fun φ => B.inclusion.map φ.left) hf

/-- The fibrewise category of graded deformations of the special fibre algebra. -/
abbrev gradedProjection :
    Over (specialFiberAlgebra B hS hT toS hk x₀ hx) ⥤ ArtinianLocalAlgCat.{u, u, u} k k :=
  objectsOverFunctor Deformation.Examples.ProjectiveGradedAlgebra.projection
    (specialFiberAlgebra B hS hT toS hk x₀ hx)

/-- The lift, as an object of the deformation category of the special fibre algebra. -/
def liftObject (y : LiftFiber B hS hT toS hk x₀ hx V) :
    (gradedProjection B hS hT toS hk x₀ hx).Fiber
      ((artinianSquareZeroExtensionFunctor k k).obj V) :=
  ⟨Over.mk (toSpecialFiber B hS hT toS hk x₀ hx V y), rfl⟩

/-- The base of a lift lies over `Spec k[V]`. -/
theorem liftRightEq (y : LiftFiber B hS hT toS hk x₀ hx V) :
    (polarizedSliceProjection B hS hT).obj y.1.right =
      squareZeroOver k B S hS toS ((fgSiteModule B hk).obj V) :=
  congrArg Under.right y.2

variable {V} {W : FGModuleCat.{u} k}

/-- **The morphism of graded algebras attached to a morphism of lifts over `k[V] ⟶ k[W]`.** -/
def liftAlgebraHom (f : V ⟶ W) (yV : LiftFiber B hS hT toS hk x₀ hx V)
    (yW : LiftFiber B hS hT toS hk x₀ hx W) (φ : yW.1.right ⟶ yV.1.right)
    (hφ : (polarizedSliceProjection B hS hT).map φ =
      eqToHom (liftRightEq B hS hT toS hk x₀ hx W yW) ≫
        squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f) ≫
          eqToHom (liftRightEq B hS hT toS hk x₀ hx V yV).symm)
    (hcomm : yW.1.hom ≫ φ = yV.1.hom) :
    liftAlgebra B hS hT toS hk x₀ hx V yV ⟶ liftAlgebra B hS hT toS hk x₀ hx W yW :=
  haveI : IsAffine (liftDef B hS hT toS hk x₀ hx V yV).S' :=
    isAffine_of_baseEq (liftBaseEq B hS hT toS hk x₀ hx V yV)
  haveI : IsAffine (liftDef B hS hT toS hk x₀ hx W yW).S' :=
    isAffine_of_baseEq (liftBaseEq B hS hT toS hk x₀ hx W yW)
  AdmissibleDeformation.toProjectiveGradedAlgebraHom
    (liftHom (compactSpace₀ B hS hT toS hk x₀ hx)
      (isThickening_liftBaseMap B hS hT toS hk x₀ hx W yW)
      (isThickening_liftBaseMap B hS hT toS hk x₀ hx V yV) φ hcomm) _ _ _ _ _ _
    ((artinianSquareZeroExtensionFunctor k k).map f)
    (fun r => by
      have hb := baseMap_eq_of_map_eq B hS hT φ
        (squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f))
        (liftRightEq B hS hT toS hk x₀ hx W yW) (liftRightEq B hS hT toS hk x₀ hx V yV) hφ
      exact appLE_ringOfBaseEq (liftBaseEq B hS hT toS hk x₀ hx W yW)
        (liftBaseEq B hS hT toS hk x₀ hx V yV) (B.inclusion.map φ.baseMap)
        (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom) hb r)

/-- **The morphism of graded algebras of a morphism of lifts is compatible with the reductions to
the special fibre.** -/
theorem liftAlgebraHom_comp_toSpecialFiber (f : V ⟶ W) (yV : LiftFiber B hS hT toS hk x₀ hx V)
    (yW : LiftFiber B hS hT toS hk x₀ hx W) (φ : yW.1.right ⟶ yV.1.right)
    (hφ : (polarizedSliceProjection B hS hT).map φ =
      eqToHom (liftRightEq B hS hT toS hk x₀ hx W yW) ≫
        squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f) ≫
          eqToHom (liftRightEq B hS hT toS hk x₀ hx V yV).symm)
    (hcomm : yW.1.hom ≫ φ = yV.1.hom) :
    liftAlgebraHom B hS hT toS hk x₀ hx f yV yW φ hφ hcomm ≫
        toSpecialFiber B hS hT toS hk x₀ hx W yW = toSpecialFiber B hS hT toS hk x₀ hx V yV := by
  apply Deformation.Examples.ProjectiveGradedAlgebra.Hom.ext
  · exact (Deformation.Examples.isTerminal_residueFieldBase (Λ := k) (k := k)).hom_ext _ _
  · show (AdmissibleDeformation.sectionRingHom (liftHom₀ B hS hT toS hk x₀ hx W yW)).comp
        (AdmissibleDeformation.sectionRingHom (liftHom (compactSpace₀ B hS hT toS hk x₀ hx)
          (isThickening_liftBaseMap B hS hT toS hk x₀ hx W yW)
          (isThickening_liftBaseMap B hS hT toS hk x₀ hx V yV) φ hcomm)) =
      AdmissibleDeformation.sectionRingHom (liftHom₀ B hS hT toS hk x₀ hx V yV)
    rw [← AdmissibleDeformation.sectionRingHom_comp]
    exact congrArg AdmissibleDeformation.sectionRingHom
      (liftHom_congr _ _ _ hcomm (by rw [Category.id_comp, hcomm]) (Category.id_comp _))

end AlgebraicGeometry.PolarizedDeformation

end
