module

public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.SecondOrderDescent
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# Algebraization of a versal formal object: the base pinned to the local ring of `S`

The last part of `StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation`.

## Main results

* `Deformation.Artin.exists_finiteType_versal_approximation` — **Stacks 07XH**.
* `Deformation.Artin.isVersalAt_iff_isVersal_stalkBase` and
  `Deformation.Artin.exists_approximation_isVersalAt_iff_isVersal` — the versality comparison
  of Stacks 0CXK with its deformation base pinned to the local ring of `S`, which is the only
  value of that ring the comparison admits.
* `Deformation.Artin.formalBaseStalkAlgebra` and
  `Deformation.Artin.specMap_formalBaseStalkAlgebra` — the algebra structure of a complete
  local base over the local ring of `S` at the image of its closed point, and the
  factorization of its structure morphism through the spectrum of that local ring.

## Implementation notes

The algebra structure over the local ring of `S` is a *named* instance binder in
`Deformation.Artin.isVersalAt_iff_isVersal_stalkBase` and is passed to
`Deformation.Artin.FormalObject.IsVersal` by name rather than left to instance search. The
`CommRing` argument of that predicate precedes its `Algebra` argument, so the search for
`Algebra 𝒪_{S,s} ξ.base.R` runs while the former is still unassigned and does not see the
binder, even though the two types print identically.

## References

* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.fiberInclusion
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

namespace Deformation.Artin

open Deformation.Artin.Approximation

universe u v w

/-- Transporting the property of lying over a morphism of the base along an equality of
base morphisms. -/
private theorem isHomLift_of_eq {C E : Type*} [Category C] [Category E] (p : E ⥤ C)
    {R T : C} {a b : E} {f g : R ⟶ T} (h : f = g) (φ : a ⟶ b)
    (hφ : p.IsHomLift g φ) : p.IsHomLift f φ := by
  cases h
  exact hφ

/-- A morphism that is heterogeneously equal to `b` equals `b` up to an `eqToHom`. -/
private theorem eq_comp_eqToHom_symm_of_heq {C : Type*} [Category C] {X P Q : C} (a : X ⟶ P)
    (b : X ⟶ Q) (h : P = Q) (hab : HEq a b) : a = b ≫ eqToHom h.symm := by
  cases h
  simpa using eq_of_heq hab

/-- An equality of complete bases respects their structure morphisms. -/
private theorem eqToHom_formalBase_toS {S : Scheme.{u}}
    {A A' : Deformation.Artin.FormalBase S} (h : A = A') :
    eqToHom (congrArg (fun b : Deformation.Artin.FormalBase S => Spec (.of b.R)) h) ≫ A'.toS =
      A.toS := by
  cases h
  simp

/-- The spectrum of a composite of ring isomorphisms is the reversed composite of the spectra. -/
private theorem specMap_ofHom_ringEquiv_trans {R T W : Type u} [CommRing R] [CommRing T]
    [CommRing W] (e : R ≃+* T) (e' : T ≃+* W) :
    Spec.map (CommRingCat.ofHom (e.trans e').toRingHom) =
      Spec.map (CommRingCat.ofHom e'.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-! ### Pinning the deformation base of the approximation to the local ring of `S` -/

/-- The chosen complete local base of a complete local object and the base of its
approximation are presentations of one and the same formal base, so a presentation of the
completed local ring by the former is a presentation of it by the latter.

The three conclusions are the `e`, `hrbase` and `hbase` arguments of
`Deformation.Artin.isVersalAt_iff_isVersal` (**Stacks 0CXK**), which are stated at
`ξ.base`, obtained from the `e`, `hrbase` and `hbase` conclusions of
`Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint`, which are stated at
`Deformation.Artin.chosenBase`; the fourth records that the closed point of the base lies
over the deformation base point of `u₀`. -/
public theorem exists_approximationBase_presentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (U : Over S) (x : F)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (u₀ : U.left) [IsLocallyNoetherian U.left]
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    (r : xR.obj.1 ⟶ x)
    (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+*
      (Deformation.Artin.chosenBase B S hS p xR.obj).R)
    (hrbase : ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
          p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀)
    (hbase : (Deformation.Artin.chosenBase B S hS p xR.obj).toS =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀ ≫ U.hom) :
    ∃ e' : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* ξ.base.R,
      HEq ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
          p.map r).left.hom ≫ eqToHom (congrArg Over.left hx))
        (Spec.map (CommRingCat.ofHom e'.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀) ∧
      ξ.base.toS = (Spec.map (CommRingCat.ofHom e'.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀) ≫ U.hom ∧
      ξ.base.toS (IsLocalRing.closedPoint ξ.base.R) =
        Deformation.Artin.basePoint U u₀ := by
  obtain ⟨ec, hec⟩ := exists_formalBase_transport
    (Deformation.Artin.approximation_base_eq B S hS p hp xR ξ hξ)
  have hsplit := specMap_ofHom_ringEquiv_trans e ec
  have hbase' : ξ.base.toS = (Spec.map (CommRingCat.ofHom (e.trans ec).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (U.left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
      U.left.fromSpecStalk u₀) ≫ U.hom := by
    rw [← eqToHom_formalBase_toS
      (Deformation.Artin.approximation_base_eq B S hS p hp xR ξ hξ), hbase, hsplit, hec]
    simp only [Category.assoc]
  refine ⟨e.trans ec, ?_, hbase', ?_⟩
  · refine heq_of_formalBase_eq_comp
      (Deformation.Artin.approximation_base_eq B S hS p hp xR ξ hξ).symm _ _ ?_
    rw [hrbase, hsplit, hec]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  · rw [hbase']
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (fun z => U.hom z)
        (Deformation.Artin.completionPresentation_closedPoint U.left u₀ (e.trans ec))).trans
        (basePoint_eq_hom_apply U u₀).symm)

/-- **The local ring of `S` acting on a complete local base.** A complete local base over `S`
whose closed point lies over `s` is an algebra over the local ring of `S` at `s`, by the
factorization `Deformation.Artin.exists_stalk_algebra_of_formalBase` of its structure
morphism through `Spec 𝒪_{S,s}`.

This is the instance `Deformation.Artin.isVersalAt_iff_isVersal` (**Stacks 0CXK**) asks for
when its ring `Λ` is pinned to the local ring of `S`, which is the only value of `Λ` that
comparison admits; `Deformation.Artin.specMap_formalBaseStalkAlgebra` is the accompanying
factorization of the structure morphism. -/
@[instance_reducible]
public def formalBaseStalkAlgebra {S : Scheme.{u}}
    (A : Deformation.Artin.FormalBase S) (s : S)
    (hs : A.toS (IsLocalRing.closedPoint A.R) = s) :
    Algebra (S.presheaf.stalk s : Type u) A.R :=
  (Classical.choose (exists_stalk_algebra_of_formalBase A s hs)).toAlgebra

/-- The structure morphism of a complete local base factors through `Spec 𝒪_{S,s}` by
`Deformation.Artin.formalBaseStalkAlgebra`. -/
public theorem specMap_formalBaseStalkAlgebra {S : Scheme.{u}}
    (A : Deformation.Artin.FormalBase S) (s : S)
    (hs : A.toS (IsLocalRing.closedPoint A.R) = s) :
    letI := formalBaseStalkAlgebra A s hs
    Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s : Type u) A.R)) ≫
        S.fromSpecStalk s = A.toS :=
  Classical.choose_spec (exists_stalk_algebra_of_formalBase A s hs)

/-- **Versality at a finite type point, with the deformation base pinned to the local ring of
`S`.** Let `xR` be a complete local restriction of `x` at `u₀` presented by a ring isomorphism
`e` of the completed local ring onto the chosen complete local base, as
`Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint` produces one, and let `ξ`
be its approximation. Then `x` is versal at `u₀` exactly when `ξ` is versal over the local
ring of `S` at the image of `u₀`.

This is `Deformation.Artin.isVersalAt_iff_isVersal` (**Stacks 0CXK**) with its ring `Λ`
instantiated at the only value it admits. That comparison takes `Λ`, a morphism
`iΛ : Spec Λ ⟶ S` and the two identifications `CommRingCat.of Λ = 𝒪_{S,s}` and
`HEq iΛ (S.fromSpecStalk s)`; both hold by reflexivity once `Λ` is the local ring itself and
`iΛ` is the canonical morphism out of its spectrum, so neither appears here. What is left is
the algebra structure of `ξ.base.R` over that local ring, which is an instance argument, and
the factorization `hΛ` of the structure morphism of `ξ.base` through it, which is a
hypothesis; both are produced from the geometry by
`Deformation.Artin.exists_approximation_isVersalAt_iff_isVersal`.

The remaining difference from `Deformation.Artin.isVersalAt_iff_isVersal` is bookkeeping.
That comparison states `e`, `hrbase` and `hbase` at `ξ.base`, whereas the construction of
`xR` states them at `Deformation.Artin.chosenBase`; the two formal bases are equal, so the
presentations transport, and `hrbase` becomes an equality rather than a heterogeneous one.

The algebra structure is a *named* instance binder and is passed by name: the search for
`Algebra 𝒪_{S,s} ξ.base.R` runs while the `CommRing` argument of
`Deformation.Artin.FormalObject.IsVersal` is still unassigned, so it does not find the
binder. -/
public theorem isVersalAt_iff_isVersal_stalkBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (U : Over S) (x : F)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (u₀ : U.left)
    [IsLocallyNoetherian S] [LocallyOfFiniteType U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    (r : xR.obj.1 ⟶ x)
    (hr : p.IsCartesian (p.map r) r)
    (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+*
      (Deformation.Artin.chosenBase B S hS p xR.obj).R)
    (hrbase : ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
          p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀)
    (hbase : (Deformation.Artin.chosenBase B S hS p xR.obj).toS =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀ ≫ U.hom)
    [algΛ : Algebra (S.presheaf.stalk (Deformation.Artin.basePoint U u₀) : Type u) ξ.base.R]
    (hΛ : Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk (Deformation.Artin.basePoint U u₀) : Type u)
          ξ.base.R)) ≫ S.fromSpecStalk (Deformation.Artin.basePoint U u₀) = ξ.base.toS) :
    Deformation.Artin.IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx ↔
      @Deformation.Artin.FormalObject.IsVersal B S hS F _ p hp ξ
        (S.presheaf.stalk (Deformation.Artin.basePoint U u₀) : Type u) _ algΛ
        (S.fromSpecStalk (Deformation.Artin.basePoint U u₀)) hΛ := by
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  obtain ⟨e', hrbase', hbase', -⟩ := exists_approximationBase_presentation B S hS p hp U x hx
    u₀ xR ξ hξ r e hrbase hbase
  exact @Deformation.Artin.isVersalAt_iff_isVersal B S hS F _ p hp U x hx u₀ _ _ hu₀ xR ξ hξ e'
    (Spec.map (CommRingCat.ofHom e'.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (U.left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
      U.left.fromSpecStalk u₀) rfl hbase' r hr hrbase'
    (S.presheaf.stalk (Deformation.Artin.basePoint U u₀) : Type u) _ algΛ rfl
    (S.fromSpecStalk (Deformation.Artin.basePoint U u₀)) HEq.rfl hΛ

/-- **The base-pinned form of Stacks 0CXK at a finite type point.** Let `x` be an object over
a scheme `U` of finite type over `S` and let `u₀` be a finite type point of `U` whose
completed local ring is small enough to lie in the site. Then `x` restricts to a complete
local object `xR` at `u₀` whose approximation has its complete local base pinned over the
local ring of `S` at the image of `u₀`, and `x` is versal at `u₀` exactly when that
approximation is versal over that local ring.

Every argument of `Deformation.Artin.isVersalAt_iff_isVersal` (**Stacks 0CXK**) is supplied
here: the complete local object and the Cartesian arrow to `x` by
`Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint`, the presentation of the
completed local ring by the base of the approximation by transport along the equality of the
two formal bases, the ring `Λ` and the morphism `iΛ` by the local ring of `S` and the
canonical morphism out of its spectrum, the algebra structure by
`Deformation.Artin.formalBaseStalkAlgebra` and its factorization by
`Deformation.Artin.specMap_formalBaseStalkAlgebra`.

The right-hand side is versality of a formal object in the sense of **Stacks 0CXJ**, which
by `Deformation.Artin.FormalObject.isVersal_iff` is versality of the associated formal object
of a predeformation category — the form the criterion of **Stacks 06IU** is stated in. -/
public theorem exists_approximation_isVersalAt_iff_isVersal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (U : Over S) (x : F)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (u₀ : U.left)
    [IsLocallyNoetherian S] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hC : B.Contains
      (Spec (.of (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)))) :
    ∃ (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
      (r : xR.obj.1 ⟶ x)
      (hs : ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR).base.toS
          (IsLocalRing.closedPoint
            ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR).base.R) =
        Deformation.Artin.basePoint U u₀),
      p.IsCartesian (p.map r) r ∧
      (Deformation.Artin.IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx ↔
        @Deformation.Artin.FormalObject.IsVersal B S hS F _ p hp
          ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
          (S.presheaf.stalk (Deformation.Artin.basePoint U u₀) : Type u) _
          (formalBaseStalkAlgebra
            ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR).base
            (Deformation.Artin.basePoint U u₀) hs)
          (S.fromSpecStalk (Deformation.Artin.basePoint U u₀))
          (specMap_formalBaseStalkAlgebra
            ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR).base
            (Deformation.Artin.basePoint U u₀) hs)) := by
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  obtain ⟨xR, r, e, hr, hrbase, hbase⟩ :=
    exists_completeLocalObject_of_isFiniteTypePoint B S hS p hp U x hx u₀ hu₀ hC
  obtain ⟨-, -, -, hs⟩ := exists_approximationBase_presentation B S hS p hp U x hx u₀ xR
    ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR) rfl r e hrbase hbase
  refine ⟨xR, r, hs, hr, ?_⟩
  exact @isVersalAt_iff_isVersal_stalkBase B S hS F _ p hp U x hx u₀ _ _ hu₀ xR
    ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR) rfl r hr e hrbase hbase
    (formalBaseStalkAlgebra
      ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR).base
      (Deformation.Artin.basePoint U u₀) hs)
    (specMap_formalBaseStalkAlgebra
      ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR).base
      (Deformation.Artin.basePoint U u₀) hs)

private theorem exists_finiteType_versal_approximation_aux
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (ξ : Deformation.Artin.FormalObject B S hS 𝒳.val.p)
    (heffective : Deformation.Artin.FormalObject.IsEffective B S hS 𝒳.val.p
      𝒳.property ξ)
    (s : S) (hs : ξ.base.toS (closedPoint ξ.base.R) = s)
    (hG : IsGRing (S.presheaf.stalk s))
    (hlimit : AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (baseFiberedCategory B S hS)
      (structureMorphism B S hS 𝒳))
    [Algebra (S.presheaf.stalk s : Type u) ξ.base.R]
    (iΛ : Spec (.of (S.presheaf.stalk s : Type u)) ⟶ S)
    (hiΛ : iΛ = S.fromSpecStalk s)
    (hΛ : Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk s : Type u) ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hversal : Deformation.Artin.FormalObject.IsVersal B S hS 𝒳.val.p 𝒳.property
      ξ (S.presheaf.stalk s : Type u) iΛ hΛ) :
    ∃ (U : Over S) (u₀ : U.left)
      (V : AlgebraicGeometry.BigFppfOver B S hS)
      (_ : (Over.post B.inclusion).obj V = U)
      (x : 𝒳.val.p.Fiber V)
      (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x.1 = U),
      LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom ∧
      AlgebraicGeometry.IsFiniteTypePoint u₀ ∧
      (letI : CommRing ξ.base.R := ξ.base.commRing
       letI : IsLocalRing ξ.base.R := ξ.base.localRing
       Nonempty (U.left.residueField u₀ ≃+* ResidueField ξ.base.R)) ∧
      Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x.1 hx ∧
      ∃ (xR : Deformation.Artin.CompleteLocalObjects B S hS 𝒳.val.p)
        (e : ξ ≅ (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p
          𝒳.property).obj xR)
        (r : xR.obj.1 ⟶ x.1)
        (eR : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+*
          (Deformation.Artin.chosenBase B S hS 𝒳.val.p xR.obj).R),
        𝒳.val.p.IsCartesian (𝒳.val.p.map r) r ∧
        ((eqToHom (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xR.obj).symm ≫
            𝒳.val.p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) =
          (Spec.map (CommRingCat.ofHom
            eR.toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap (U.left.presheaf.stalk u₀)
                (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
            U.left.fromSpecStalk u₀) := by
  classical
  -- The deformation base is the local ring of `S` at `s`, so `iΛ` is the canonical map
  -- from its spectrum; in particular it is a monomorphism, which is what identifies maps
  -- to that spectrum below.
  have hmonoiΛ : Mono iΛ := by
    rw [hiΛ]
    infer_instance
  let : CommRing ξ.base.R := ξ.base.commRing
  let : IsLocalRing ξ.base.R := ξ.base.localRing
  let : Field (ResidueField ξ.base.R) := ResidueField.field ξ.base.R
  let : Algebra (S.presheaf.stalk s) (ResidueField ξ.base.R) :=
    ResidueField.algebra ξ.base.R
  change (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p
    𝒳.property).essImage ξ at heffective
  rcases heffective with ⟨xR, hformal⟩
  obtain ⟨formalIso⟩ := hformal
  let formalEquiv : ξ ≅
      (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p 𝒳.property).obj xR :=
    formalIso.symm
  rcases (Deformation.Artin.approximationFunctorData B S hS 𝒳.val.p
      𝒳.property).2 with ⟨rY, hbase, hcartY, htransitionY, hnaturalY, hrY⟩
  let Rbase := Deformation.Artin.chosenBase B S hS 𝒳.val.p xR.obj
  have hcontains : B.Contains (Spec (.of Rbase.R)) :=
    Deformation.Artin.chosenContains B S hS 𝒳.val.p xR.obj
  have hresFinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (maximalIdeal Rbase.R ^ (0 + 1)))) ≫ Rbase.toS) :=
    Rbase.residueLocallyFiniteType
  have hresQC : QuasiCompact
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (maximalIdeal Rbase.R ^ (0 + 1)))) ≫ Rbase.toS) :=
    Rbase.residueQuasiCompact
  obtain ⟨hfR, hqR⟩ := locallyFiniteType_and_quasiCompact_quotient_pow_one
    (maximalIdeal Rbase.R) Rbase.toS hresFinite hresQC
  have hsR : Rbase.toS (closedPoint Rbase.R) = s := by
    set Yobj := (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p
      𝒳.property).obj xR with hYobj
    have h := congrArg (fun f : Spec (.of ξ.base.R) ⟶ S =>
      f (closedPoint ξ.base.R))
      (Deformation.Artin.FormalObject.Hom.baseMap_spec formalEquiv.hom).1
    let eBase := formalBaseMapIso (B := B) (S := S) (hS := hS)
      (p := 𝒳.val.p) (X := ξ) (Y := Yobj) formalEquiv
    have hclosed : formalEquiv.hom.baseMap (closedPoint ξ.base.R) =
        closedPoint Yobj.base.R := specIso_closedPoint eBase
    have hcomp := Scheme.Hom.comp_apply
      (Deformation.Artin.FormalObject.Hom.baseMap formalEquiv.hom) Yobj.base.toS
      (closedPoint ξ.base.R)
    have step : Yobj.base.toS (closedPoint Yobj.base.R) = s :=
      (congrArg (fun z => Yobj.base.toS z) hclosed.symm).trans
        (hcomp.symm.trans (h.trans hs))
    exact formalBase_toS_closedPoint_congr (hbase xR) step
  have hxR : 𝒳.val.p.obj xR.obj.1 =
      siteObject B S hS hcontains Rbase.toS := by
    simpa [siteObject, Deformation.Artin.baseOver, Rbase] using
      Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xR.obj
  let xInput : 𝒳.val.p.Fiber (siteObject B S hS hcontains Rbase.toS) :=
    ⟨xR.obj.1, hxR⟩
  let : IsNoetherianRing Rbase.R := Rbase.noetherian
  let : IsAdicComplete (maximalIdeal Rbase.R) Rbase.R := Rbase.complete
  have happrox := exists_finiteType_approximation B S hS 𝒳 Rbase.R hcontains
    Rbase.toS hfR hqR s hsR hG hlimit xInput 2 (by omega)
  rcases happrox with
    ⟨A, hcommA, mA, hmA, fA, hA, hRN, hAN, xA, hfiniteA, hquasiA, hrest⟩
  rcases hrest with
    ⟨φ, hφ, iR, iA, eBase, xRN, xAN, r, a, e, hiR, hiA, heBase,
      hcartR, hcartA, hLift, hIso, gr, hgr, hgr0⟩
  let Y := (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p 𝒳.property).obj xR
  have hrR : 𝒳.val.p.IsHomLift iR r := by
    let := hcartR
    infer_instance
  obtain ⟨eYRN, heYRN, heYRNbase⟩ := formal_restriction_iso 𝒳.property Y
    Rbase (hbase xR) hcontains 1 hRN xR.obj.1 hxR (rY xR 1) (hrY xR 1)
    xRN iR hiR r hrR
  let := hIso
  let eξAN : ξ.level 1 ≅ xAN.1 :=
    ((Deformation.Artin.FormalObject.evaluation 1).mapIso formalEquiv) ≪≫ eYRN ≪≫ asIso e
  let V := siteObject B S hS hA fA
  let U : Over S := (Over.post B.inclusion).obj V
  let u₀ : U.left := ⟨mA, hmA.isPrime⟩
  have hbasePoint : Deformation.Artin.basePoint U u₀ = s :=
    (basePoint_specOver A S fA u₀).trans
      ((point_eq_of_second_order_comparison Rbase.R A mA hmA S
        Rbase.toS fA φ hφ).trans hsR)
  have hΛpoint : CommRingCat.of (S.presheaf.stalk s : Type u) =
      S.presheaf.stalk (Deformation.Artin.basePoint U u₀) := by
    rw [hbasePoint]
    rfl
  have hiΛpoint : HEq iΛ
      (S.fromSpecStalk (Deformation.Artin.basePoint U u₀)) := by
    rw [hbasePoint]
    exact heq_of_eq hiΛ
  have huclosed : IsClosed ({u₀} : Set U.left) := by
    show IsClosed ({⟨mA, hmA.isPrime⟩} : Set (PrimeSpectrum A))
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmA
  have hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀ :=
    finiteTypePoint_of_isClosed u₀ huclosed
  let : CommRing A := hcommA
  let : mA.IsMaximal := hmA
  let : LocallyOfFiniteType U.hom := hfiniteA
  have : IsLocallyNoetherian U.left :=
    LocallyOfFiniteType.isLocallyNoetherian U.hom
  let L := U.left.presheaf.stalk u₀
  let C := AlgebraicGeometry.Scheme.completedLocalRing U.left u₀
  let : Algebra A L := by
    show Algebra A ((Spec (.of A)).presheaf.stalk u₀)
    exact StructureSheaf.stalkAlgebra A u₀
  have : IsLocalization.AtPrime L mA :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of A)
      (⟨mA, hmA.isPrime⟩ : PrimeSpectrum A)
  have hL : B.Contains (Spec (.of L)) :=
    Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit mA.primeCompl L hA
  have hC : B.Contains (Spec (.of C)) :=
    contains_spec_adicCompletion B hL (maximalIdeal L)
  let e₂ : (Rbase.R ⧸ maximalIdeal Rbase.R ^ 2) ≃+*
      (C ⧸ maximalIdeal C ^ 2) :=
    φ.trans (completedLocalizationQuotientEquiv mA L 2).symm
  let g : Spec (.of C) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap L C)) ≫ U.left.fromSpecStalk u₀
  let : QuasiCompact U.hom := hquasiA
  let Cbase := completedFormalBase U u₀ hu₀
  have hCn (n : ℕ) : B.Contains (Cbase.truncation n) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit C (C ⧸ maximalIdeal C ^ (n + 1)) hC
  have hgCbase : g ≫ U.hom = Cbase.toS := Category.assoc _ _ _
  let VC := siteObject B S hS hC Cbase.toS
  let iC : VC ⟶ V := Over.homMk
    (ObjectProperty.homMk (X := B.obj hC) (Y := B.obj hA) g) (by
      apply ObjectProperty.hom_ext
      exact hgCbase)
  obtain ⟨xC, rC, hrC⟩ := 𝒳.property.exists_lift iC xA.1 xA.2
  have hcartC : 𝒳.val.p.IsCartesian (𝒳.val.p.map rC) rC := by
    let := stronglyCartesian_of_fibered 𝒳.property rC
    infer_instance
  have hrCinst : 𝒳.val.p.IsHomLift iC rC := hrC
  have hxC : 𝒳.val.p.obj xC = Deformation.Artin.baseOver B S hS Cbase hC :=
   domain_eq_of_isHomLift 𝒳.val.p iC rC hrC
  -- The first infinitesimal neighbourhood of the completion at `u₀`, inside the site.
  let iCN : siteObject B S hS (hCn 1) (Cbase.truncationToS 1) ⟶ VC :=
    Over.homMk (ObjectProperty.homMk
      (AlgebraicGeometry.adicThickeningι C (maximalIdeal C) 1)) (by rfl)
  let eAC := completedLocalizationQuotientEquiv mA L 2
  have heAC : Spec.map (CommRingCat.ofHom eAC.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ 2))) =
      AlgebraicGeometry.adicThickeningι C (maximalIdeal C) 1 ≫ g := by
    dsimp only [g]
    have hstalk : U.left.fromSpecStalk u₀ =
        Spec.map (CommRingCat.ofHom (algebraMap A L)) :=
      AlgebraicGeometry.Spec.fromSpecStalk_eq' (.of A) u₀
    rw [hstalk]
    exact completedLocalizationQuotientEquiv_spec mA L 2
  let eSpecCQ : Spec (.of (C ⧸ maximalIdeal C ^ 2)) ≅ Spec (.of (A ⧸ mA ^ 2)) :=
    Scheme.Spec.mapIso eAC.toCommRingCatIso.symm.op
  have hCbaseT : Cbase.truncationToS 1 =
      AlgebraicGeometry.adicThickeningι C (maximalIdeal C) 1 ≫ g ≫ U.hom :=
    completedFormalBase_truncationToS U u₀ hu₀ 1
  have hCQw : eSpecCQ.hom ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ 2))) ≫ fA) =
      Cbase.truncationToS 1 := by
    rw [hCbaseT]
    exact comp_assoc_eq_comp_assoc _ _ _ _ heAC U.hom
  let eCQ : siteObject B S hS (hCn 1) (Cbase.truncationToS 1) ≅
      siteObject B S hS hAN
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ 2))) ≫ fA) :=
    siteObjectIsoOfSpecIso (hCn 1) hAN (Cbase.truncationToS 1)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ 2))) ≫ fA) eSpecCQ hCQw
  have hiCA : iCN ≫ iC = eCQ.hom ≫ iA := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show AlgebraicGeometry.adicThickeningι C (maximalIdeal C) 1 ≫ g =
      Spec.map (CommRingCat.ofHom eAC.symm.toRingHom) ≫ iA.left.hom
    rw [show iA.left.hom = Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (mA ^ 2))) from hiA]
    exact heAC.symm
  have haA : 𝒳.val.p.IsHomLift iA a := by
    let := hcartA
    infer_instance
  have hlength (n : ℕ) :
      Module.length (Rbase.R ⧸ maximalIdeal Rbase.R ^ n)
        (Rbase.R ⧸ maximalIdeal Rbase.R ^ n) =
      Module.length (C ⧸ maximalIdeal C ^ n) (C ⧸ maximalIdeal C ^ n) :=
    length_quotient_pow_eq_length_completedLocalization
      (maximalIdeal Rbase.R) mA L gr hgr n
  let xCF : Deformation.Artin.CompleteLocalObjectsFull B S hS 𝒳.val.p :=
    ⟨xC, ⟨Cbase, hC, hxC⟩⟩
  let xCR : Deformation.Artin.CompleteLocalObjects B S hS 𝒳.val.p := ⟨xCF⟩
  obtain ⟨er, her⟩ := exists_chosenBase_ringEquiv 𝒳.val.p xCF Cbase hC hxC
  have hrC' : 𝒳.val.p.map rC = eqToHom hxC ≫ iC ≫ eqToHom xA.2.symm :=
    map_eq_of_isHomLift 𝒳.val.p iC rC hrC hxC xA.2
  have hnorm : (eqToHom (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xCF).symm ≫
      𝒳.val.p.map rC ≫ eqToHom xA.2).left.hom =
        Spec.map (CommRingCat.ofHom er.toRingHom) ≫ g := by
    rw [her, hrC']
    exact left_hom_normalize _ _ iC _ _
  have hxA : (𝒳.val.p ⋙ Over.post B.inclusion).obj xA.1 = U :=
    congrArg ((Over.post B.inclusion).obj) xA.2
  have heqMap : (eqToHom xA.2).left.hom = eqToHom (congrArg Over.left hxA) := by
    show (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (eqToHom xA.2) = _
    simp
  have hrbase : ((eqToHom (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xCR.obj).symm ≫
      𝒳.val.p.map rC).left.hom ≫ eqToHom (congrArg Over.left hxA)) =
      Spec.map (CommRingCat.ofHom er.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L C)) ≫ U.left.fromSpecStalk u₀ := by
    have hsplit : ((eqToHom
          (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xCR.obj).symm ≫
          𝒳.val.p.map rC).left.hom ≫ (eqToHom xA.2).left.hom) =
        (eqToHom (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xCR.obj).symm ≫
          𝒳.val.p.map rC ≫ eqToHom xA.2).left.hom :=
      left_hom_assoc _ _ _
    refine Eq.trans ?_ (hsplit.trans hnorm)
    exact congrArg (fun z => (eqToHom
      (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xCR.obj).symm ≫
      𝒳.val.p.map rC).left.hom ≫ z) heqMap.symm
  -- The local ring of `S` at `s` acts canonically on the completed local ring at `u₀`.
  have hsC : Cbase.toS (IsLocalRing.closedPoint C) = s :=
    (completedFormalBase_closedPoint U u₀ hu₀).trans
      ((basePoint_eq_hom_apply U u₀).symm.trans hbasePoint)
  -- The approximation of `xC`, and the identification of its chosen complete base with
  -- the completion of the local ring at `u₀`.
  let Yp := (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p 𝒳.property).obj xCR
  obtain ⟨ecast, hecast⟩ := exists_formalBase_transport (hbase xCR)
  let eCY : Cbase.R ≃+* Yp.base.R := er.trans ecast
  have heCY := specMap_ofHom_ringEquiv_trans er ecast
  have heCY' : Spec.map (CommRingCat.ofHom eCY.toRingHom) =
      eqToHom (congrArg (fun b : Deformation.Artin.FormalBase S => Spec (.of b.R))
          (hbase xCR)) ≫
        Spec.map (CommRingCat.ofHom er.toRingHom) :=
    heCY.trans
      (congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom er.toRingHom)) hecast)
  have herToS : Spec.map (CommRingCat.ofHom er.toRingHom) ≫ Cbase.toS =
      (Deformation.Artin.chosenBase B S hS 𝒳.val.p xCF).toS := by
    have hw := Over.w (eqToHom
      (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xCF).symm ≫ eqToHom hxC)
    have hw' := congrArg (fun t => t.hom) hw
    rw [her]
    exact hw'
  have hYpToS : Spec.map (CommRingCat.ofHom eCY.toRingHom) ≫ Cbase.toS =
      Yp.base.toS := by
    rw [heCY', Category.assoc, herToS]
    exact eqToHom_formalBase_toS (hbase xCR)
  have hsYp : Yp.base.toS (IsLocalRing.closedPoint Yp.base.R) = s := by
    have : IsLocalHom (eCY.toRingHom : Cbase.R →+* Yp.base.R) :=
      IsLocalHom.of_surjective _ eCY.surjective
    have h1 : (Spec.map (CommRingCat.ofHom (eCY.toRingHom : Cbase.R →+* Yp.base.R)))
        (IsLocalRing.closedPoint Yp.base.R) = IsLocalRing.closedPoint Cbase.R :=
      AlgebraicGeometry.Spec_closedPoint
    refine (congrArg (fun f : Spec (.of Yp.base.R) ⟶ S =>
      f (IsLocalRing.closedPoint Yp.base.R)) hYpToS).symm.trans ?_
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (fun z => Cbase.toS z) h1).trans hsC)
  obtain ⟨aΛY, hΛYspec⟩ := exists_stalk_algebra_of_formalBase Yp.base s hsYp
  let algΛY : Algebra (S.presheaf.stalk s : Type u) Yp.base.R := aΛY.toAlgebra
  let : Algebra (S.presheaf.stalk s : Type u) (ResidueField Yp.base.R) :=
    ResidueField.algebra Yp.base.R
  have hΛY : Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s : Type u) Yp.base.R)) ≫ iΛ = Yp.base.toS := by
    rw [hiΛ]
    exact hΛYspec
  -- Level one of the approximation is the second-order comparison object.
  let iY1 : Deformation.Artin.truncationOver B S hS Yp.base Yp.contains 1 ⟶
      Deformation.Artin.baseOver B S hS Cbase hC :=
    eqToHom (Yp.level_eq 1).symm ≫ 𝒳.val.p.map (rY xCR 1) ≫ eqToHom hxC
  have hiY1lift : 𝒳.val.p.IsHomLift iY1 (rY xCR 1) :=
    IsHomLift.of_fac 𝒳.val.p iY1 (rY xCR 1) (Yp.level_eq 1) hxC rfl
  have hiY1hom : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iY1 =
      AlgebraicGeometry.adicThickeningι Yp.base.R (maximalIdeal Yp.base.R) 1 ≫
        Spec.map (CommRingCat.ofHom eCY.toRingHom) := by
    have hsplit : iY1 = (eqToHom (Yp.level_eq 1).symm ≫ 𝒳.val.p.map (rY xCR 1) ≫
          eqToHom (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xCR.obj)) ≫
        (eqToHom (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xCR.obj).symm ≫
          eqToHom hxC) := by
      dsimp only [iY1]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hsplit, Functor.map_comp, hrY xCR 1, heCY', her, Category.assoc]
    rfl
  let γ₁ : Yp.base.truncation 1 ⟶ Cbase.truncation 1 :=
    Spec.map (CommRingCat.ofHom (quotientPowRingEquivOfRingEquiv eCY 2).toRingHom)
  have : IsIso γ₁ := by
    show IsIso (Spec.map (quotientPowRingEquivOfRingEquiv eCY 2).toCommRingCatIso.hom)
    infer_instance
  have hι₁ : γ₁ ≫ AlgebraicGeometry.adicThickeningι Cbase.R (maximalIdeal Cbase.R) 1 =
      AlgebraicGeometry.adicThickeningι Yp.base.R (maximalIdeal Yp.base.R) 1 ≫
        Spec.map (CommRingCat.ofHom eCY.toRingHom) :=
    (adicThickeningι_comp_specMap eCY 1).symm
  have hcomm₁ : γ₁ ≫ Cbase.truncationToS 1 = Yp.base.truncationToS 1 := by
    show γ₁ ≫ AlgebraicGeometry.adicThickeningι Cbase.R (maximalIdeal Cbase.R) 1 ≫ Cbase.toS =
      AlgebraicGeometry.adicThickeningι Yp.base.R (maximalIdeal Yp.base.R) 1 ≫ Yp.base.toS
    rw [← Category.assoc, hι₁, Category.assoc, hYpToS]
  let g₁ : Deformation.Artin.truncationOver B S hS Yp.base Yp.contains 1 ≅
      siteObject B S hS (hCn 1) (Cbase.truncationToS 1) :=
    Over.isoMk (ObjectProperty.isoMk _ (asIso γ₁)) (by
      apply ObjectProperty.hom_ext
      exact hcomm₁)
  have hg₁ : iY1 = g₁.hom ≫ iCN := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iY1 =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (g₁.hom ≫ iCN)
    rw [hiY1hom, Functor.map_comp]
    exact hι₁.symm
  have hG : iY1 ≫ iC = (g₁ ≪≫ eCQ).hom ≫ iA :=
    (congrArg (fun t => t ≫ iC) hg₁).trans
      ((Category.assoc g₁.hom iCN iC).trans
        ((congrArg (fun z => g₁.hom ≫ z) hiCA).trans
          (Category.assoc g₁.hom eCQ.hom iA).symm))
  obtain ⟨eYpAN, -, -⟩ := restriction_iso_of_baseIso 𝒳.property
    (g₁ ≪≫ eCQ) iA (iY1 ≫ iC) hG a (rY xCR 1 ≫ rC) haA
    (isHomLift_comp_of_isHomLift 𝒳.val.p iY1 iC (rY xCR 1) rC hiY1lift hrC)
  let eξYp₁ : ξ.level 1 ≅ Yp.level 1 := eξAN ≪≫ eYpAN.symm
  -- The realizations of `ξ` and of the approximation in their predeformation categories.
  let hx₀ξ := Deformation.Artin.FormalObject.basePoint ξ
    (S.presheaf.stalk s : Type u) iΛ hΛ
  let Cξ := Deformation.Artin.predeformationCategory iΛ
    (𝒳.val.p ⋙ Over.post B.inclusion) (ξ.level 0) hx₀ξ
  let : Category Cξ.carrier := Cξ.category
  let ηξ := Deformation.Artin.FormalObject.predeformationFormalObject ξ
    (S.presheaf.stalk s : Type u) iΛ hΛ
  obtain ⟨hηξbase, hηξpoint, hηξarrow, hηξtrans⟩ :
      ηξ.base = ξ.completeLocalBase (S.presheaf.stalk s : Type u) ∧
      (∀ n, (Cξ.objects (ηξ.level n)).point = ξ.level n) ∧
      (∀ n, HEq (Cξ.objects (ηξ.level n)).arrow
        (Deformation.Artin.FormalObject.closedPointArrow ξ n)) ∧
      (∀ n, HEq (Cξ.morphisms (ηξ.level (n + 1)) (ηξ.level n)
        (ηξ.transition n)).arrow (ξ.transition n)) :=
    ⟨rfl, fun _ => rfl, fun _ => HEq.rfl, fun _ => HEq.rfl⟩
  have hversalξ : Deformation.IsVersal
      (Deformation.Artin.predeformationCategory_isPredeformationCategory
        B hS iΛ 𝒳.val.p (ξ.level 0) hx₀ξ 𝒳.property).cofibered ηξ := hversal
  let hx₁Y := Deformation.Artin.FormalObject.basePoint Yp
    (S.presheaf.stalk s : Type u) iΛ hΛY
  let CY := Deformation.Artin.predeformationCategory iΛ
    (𝒳.val.p ⋙ Over.post B.inclusion) (Yp.level 0) hx₁Y
  let : Category CY.carrier := CY.category
  let ηY := Deformation.Artin.FormalObject.predeformationFormalObject Yp
    (S.presheaf.stalk s : Type u) iΛ hΛY
  obtain ⟨hηYbase, hηYpoint, hηYarrow, hηYtrans⟩ :
      ηY.base = Yp.completeLocalBase (S.presheaf.stalk s : Type u) ∧
      (∀ n, (CY.objects (ηY.level n)).point = Yp.level n) ∧
      (∀ n, HEq (CY.objects (ηY.level n)).arrow
        (Deformation.Artin.FormalObject.closedPointArrow Yp n)) ∧
      (∀ n, HEq (CY.morphisms (ηY.level (n + 1)) (ηY.level n)
        (ηY.transition n)).arrow (Yp.transition n)) :=
    ⟨rfl, fun _ => rfl, fun _ => HEq.rfl, fun _ => HEq.rfl⟩
  have hpY := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    B hS iΛ 𝒳.val.p (Yp.level 0) hx₁Y 𝒳.property).cofibered
  -- The level-one isomorphism descends to the closed fibres, and its base map is the
  -- spectrum of an isomorphism of residue fields over the deformation base.
  obtain ⟨γ₀, β₀, ρ, hβ₀map, hρlift, hρiso, hρfac⟩ :=
    exists_level_zero_iso_of_level_one_iso 𝒳.property ξ Yp eξYp₁
  have : IsIso ρ := hρiso
  obtain ⟨ε, hε⟩ := exists_algEquiv_of_fieldPoint_iso iΛ hx₀ξ hx₁Y ρ
  -- Transport the realization of the approximation into the category of `ξ`.
  let Φ := changeFormalObjects ε iΛ (𝒳.val.p ⋙ Over.post B.inclusion)
    (ξ.level 0) (Yp.level 0) hx₀ξ hx₁Y ρ hε Cξ CY
  let θ := Φ.obj ηY
  have hθobj : ∀ n, Cξ.objects (θ.level n) =
      changeDeformationObject ε iΛ (𝒳.val.p ⋙ Over.post B.inclusion) (ξ.level 0)
        (Yp.level 0) hx₀ξ hx₁Y ρ hε (CY.objects (ηY.level n)) := fun n =>
    changePredeformation_objects ε iΛ (𝒳.val.p ⋙ Over.post B.inclusion) (ξ.level 0)
      (Yp.level 0) hx₀ξ hx₁Y ρ hε Cξ CY (ηY.level n)
  have hθpoint : ∀ n, (Cξ.objects (θ.level n)).point = Yp.level n := fun n =>
    (changeFormalObject_objects_point ε iΛ (𝒳.val.p ⋙ Over.post B.inclusion)
      (ξ.level 0) (Yp.level 0) hx₀ξ hx₁Y ρ hε Cξ CY ηY n).trans (hηYpoint n)
  have hθtrans : ∀ n, HEq (Cξ.morphisms (θ.level (n + 1)) (θ.level n)
      (θ.transition n)).arrow (Yp.transition n) := fun n =>
    (changeFormalObject_morphisms_arrow ε iΛ (𝒳.val.p ⋙ Over.post B.inclusion)
      (ξ.level 0) (Yp.level 0) hx₀ξ hx₁Y ρ hε Cξ CY ηY n).trans (hηYtrans n)
  have hpξ := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    B hS iΛ 𝒳.val.p (ξ.level 0) hx₀ξ 𝒳.property).cofibered
  obtain ⟨θn, qθ, gθ, hqθ, hgθ, hqgθ⟩ := exists_formal_reduction_tower hpξ θ
  -- The adic quotients of the two complete bases have equal length.
  let eξR : ξ.base.R ≃+* Rbase.R :=
    (formalBaseRingEquiv formalEquiv).trans
      (RingEquiv.cast (R := fun b : Deformation.Artin.FormalBase S => b.R) (hbase xR))
  have hlen : ∀ n, Module.length (Deformation.AdicTruncation.obj ηξ.base n)
        (Deformation.AdicTruncation.obj ηξ.base n) =
      Module.length (Deformation.AdicTruncation.obj θ.base n)
        (Deformation.AdicTruncation.obj θ.base n) := by
    intro n
    rw [hηξbase, changeFormalObjects_obj_base ε iΛ
      (𝒳.val.p ⋙ Over.post B.inclusion) (ξ.level 0) (Yp.level 0) hx₀ξ hx₁Y ρ hε
      Cξ CY ηY, hηYbase]
    exact (Module.length_eq_of_ringEquiv
      (quotientPowRingEquivOfRingEquiv eξR (n + 1))).trans
      ((hlength (n + 1)).trans
        (Module.length_eq_of_ringEquiv (quotientPowRingEquivOfRingEquiv eCY (n + 1))))
  -- The level-one isomorphism, read as an isomorphism of deformations of `ξ.level 0`.
  have hd := eq_comp_eqToHom_symm_of_heq _ _ (hηξpoint 1) (hηξarrow 1)
  have hd' : (Cξ.objects (θ.level 1)).arrow =
      (ρ ≫ Deformation.Artin.FormalObject.closedPointArrow Yp 1) ≫ eqToHom (hθpoint 1).symm :=
    eq_comp_eqToHom_symm_of_heq _ _ (hθpoint 1) ((deformationObject_arrow_heq (hθobj 1)).trans
      (heq_comp_of_heq (hηYpoint 1) (hηYarrow 1) ρ))
  have hkey : ρ ≫ Deformation.Artin.FormalObject.closedPointArrow Yp 1 ≫ eξYp₁.inv =
      Deformation.Artin.FormalObject.closedPointArrow ξ 1 := by
    simp only [Deformation.Artin.FormalObject.closedPointArrow, Category.id_comp]
    rw [← Category.assoc, hρfac, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let arrθξ : (Cξ.objects (θ.level 1)).point ⟶ (Cξ.objects (ηξ.level 1)).point :=
    eqToHom (hθpoint 1) ≫ eξYp₁.inv ≫ eqToHom (hηξpoint 1).symm
  let arrξθ : (Cξ.objects (ηξ.level 1)).point ⟶ (Cξ.objects (θ.level 1)).point :=
    eqToHom (hηξpoint 1) ≫ eξYp₁.hom ≫ eqToHom (hθpoint 1).symm
  have harr : arrθξ ≫ arrξθ = 𝟙 _ := by
    simp [arrθξ, arrξθ]
  have harr' : arrξθ ≫ arrθξ = 𝟙 _ := by
    simp [arrθξ, arrξθ]
  have htriθξ : (Cξ.objects (θ.level 1)).arrow ≫ arrθξ =
      (Cξ.objects (ηξ.level 1)).arrow :=
    ((congrArg (fun t => t ≫ arrθξ) hd').trans (by
        simp only [arrθξ, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp])).trans
      ((congrArg (fun t => t ≫ eqToHom (hηξpoint 1).symm) hkey).trans hd.symm)
  have htriξθ : (Cξ.objects (ηξ.level 1)).arrow ≫ arrξθ =
      (Cξ.objects (θ.level 1)).arrow :=
    (congrArg (fun t => t ≫ arrξθ) htriθξ).symm.trans
      (((Category.assoc _ _ _).trans
        (congrArg (fun t => (Cξ.objects (θ.level 1)).arrow ≫ t) harr)).trans
        (Category.comp_id _))
  let m₁ := deformationMorphismOfArrow iΛ (Cξ.objects (ηξ.level 1))
    (Cξ.objects (θ.level 1)) arrθξ htriθξ
  let m₂ := deformationMorphismOfArrow iΛ (Cξ.objects (θ.level 1))
    (Cξ.objects (ηξ.level 1)) arrξθ htriξθ
  let b₁ : ηξ.level 1 ⟶ θ.level 1 := (Cξ.morphisms _ _).symm m₁
  let b₂ : θ.level 1 ⟶ ηξ.level 1 := (Cξ.morphisms _ _).symm m₂
  have hb₁₂ : b₁ ≫ b₂ = 𝟙 (ηξ.level 1) := by
    apply (Cξ.morphisms _ _).injective
    refine deformationMorphism_ext_of_arrow iΛ _ _ ?_
    refine (Cξ.reversed_composition b₁ b₂).trans ?_
    refine Eq.trans ?_ (Cξ.reversed_identity (ηξ.level 1)).symm
    simp only [b₁, b₂, Equiv.apply_symm_apply, m₁, m₂,
      deformationMorphismOfArrow_arrow]
    exact harr'
  have hb₂₁ : b₂ ≫ b₁ = 𝟙 (θ.level 1) := by
    apply (Cξ.morphisms _ _).injective
    refine deformationMorphism_ext_of_arrow iΛ _ _ ?_
    refine (Cξ.reversed_composition b₂ b₁).trans ?_
    refine Eq.trans ?_ (Cξ.reversed_identity (θ.level 1)).symm
    simp only [b₁, b₂, Equiv.apply_symm_apply, m₁, m₂,
      deformationMorphismOfArrow_arrow]
    exact harr
  have : IsIso b₁ := ⟨b₂, hb₁₂, hb₂₁⟩
  let w : Deformation.AdicTruncation.obj ηξ.base 1 ⟶
      Deformation.AdicTruncation.obj θ.base 1 :=
    eqToHom (ηξ.level_eq 1).symm ≫ Cξ.projection.map b₁ ≫ eqToHom (θ.level_eq 1)
  have : IsIso w := by
    dsimp only [w]
    infer_instance
  have hwlift : Cξ.projection.IsHomLift w b₁ :=
    IsHomLift.of_fac Cξ.projection w b₁ (ηξ.level_eq 1) (θ.level_eq 1) rfl
  let := hqθ 1
  have hbase1 : (θn 1).base =
      Deformation.artinianToComplete.obj (Deformation.AdicTruncation.obj θ.base 1) :=
    IsHomLift.codomain_eq Deformation.FormalObject.projection
      (formalBaseQuotient θ.base 1) (qθ 1)
  have hqθbase : (qθ 1).base ≫ eqToHom hbase1 = formalBaseQuotient θ.base 1 :=
    ((IsHomLift.commSq Deformation.FormalObject.projection
      (formalBaseQuotient θ.base 1) (qθ 1)).w).trans (Category.id_comp _)
  let a' : ηξ.base ⟶ (θn 1).base :=
    formalBaseQuotient ηξ.base 1 ≫
      (Deformation.artinianToComplete.map w ≫ eqToHom hbase1.symm)
  have : IsIso (Deformation.artinianToComplete.map w ≫ eqToHom hbase1.symm) :=
    inferInstance
  have ha' : Function.Surjective a'.hom :=
    surjective_formalBaseQuotient_comp 1
      (Deformation.artinianToComplete.map w ≫ eqToHom hbase1.symm)
  let a₁ : ηξ.level 1 ⟶ (θn 1).level 1 := b₁ ≫ (qθ 1).app 1
  have hmapa : Deformation.AdicTruncation.map a' 1 =
      w ≫ (Deformation.AdicTruncation.functor 1).map (qθ 1).base := by
    have hqb : (qθ 1).base = formalBaseQuotient θ.base 1 ≫ eqToHom hbase1.symm := by
      refine Eq.trans ?_ (congrArg (fun t => t ≫ eqToHom hbase1.symm) hqθbase)
      simp
    refine Eq.trans ?_ (congrArg
      (fun t => w ≫ (Deformation.AdicTruncation.functor 1).map t) hqb.symm)
    exact adicTruncation_map_formalBaseQuotient_comp_eqToHom ηξ.base θ.base w
      hbase1.symm
  have ha₁ : Cξ.projection.IsHomLift (Deformation.AdicTruncation.map a' 1) a₁ :=
    isHomLift_of_eq Cξ.projection hmapa a₁
      (isHomLift_comp_of_isHomLift Cξ.projection w
        ((Deformation.AdicTruncation.functor 1).map (qθ 1).base) b₁ ((qθ 1).app 1)
        hwlift ((qθ 1).app_lift 1))
  have hab := exists_formal_iso_of_second_level_of_length_eq hpξ ηξ θ hversalξ
    θn qθ gθ hqθ hgθ hqgθ a' ha' a₁ ha₁ hlen
  have hξYp : Nonempty (ξ ≅ Yp) :=
    formalObjectIsoOfRealizations Cξ ξ Yp ηξ θ hηξpoint hθpoint hηξtrans hθtrans
      hab.1.some
  have : Epi ρ := inferInstance
  have hversalY : Deformation.IsVersal hpY ηY :=
    isVersal_of_changeFormalObjects ε iΛ (𝒳.val.p ⋙ Over.post B.inclusion)
      (ξ.level 0) (Yp.level 0) hx₀ξ hx₁Y ρ hε Cξ CY hpY hpξ ηY θ rfl hab.2
  let gU : Spec (CommRingCat.of Yp.base.R) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom eCY.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L C)) ≫ U.left.fromSpecStalk u₀
  have hbaseU : Yp.base.toS = gU ≫ U.hom :=
    hYpToS.symm.trans (comp_assoc3 (Spec.map (CommRingCat.ofHom eCY.toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap L C))) (U.left.fromSpecStalk u₀) U.hom)
  have hrbaseU : HEq ((eqToHom
      (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xCR.obj).symm ≫
      𝒳.val.p.map rC).left.hom ≫ eqToHom (congrArg Over.left hxA)) gU := by
    refine heq_of_formalBase_eq_comp (hbase xCR).symm _ gU ?_
    exact hrbase.trans (comp_eq_eqToHom_comp _ _ _ _ _ heCY')
  have hversalAt : Deformation.Artin.IsVersalAt U
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ xA.1 hxA :=
    isVersalAt_of_formalObject_isVersal B S hS 𝒳.val.p 𝒳.property U xA.1 hxA u₀ hu₀
      xCR Yp rfl eCY gU rfl hbaseU rC hcartC hrbaseU
      (S.presheaf.stalk s : Type u) hΛpoint iΛ hiΛpoint hΛY hversalY
  have hformalIso : ξ ≅ (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p
      𝒳.property).obj xCR := hξYp.some
  refine ⟨U, u₀, V, rfl, xA, hxA, ?_, ?_, hu₀, ?_, hversalAt,
    ⟨xCR, hformalIso, rC, er, hcartC, hrbase⟩⟩
  · show LocallyOfFiniteType fA
    exact hfiniteA
  · show QuasiCompact fA
    exact hquasiA
  · let : CommRing A := hcommA
    let : mA.IsMaximal := hmA
    show Nonempty (U.left.residueField u₀ ≃+* ResidueField ξ.base.R)
    have eU : U.left.residueField u₀ ≃+* mA.ResidueField := by
      show (Spec (.of A)).residueField u₀ ≃+* mA.ResidueField
      simpa [u₀] using
        (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).commRingCatIsoToRingEquiv
    let eAquot : A ⧸ mA ≃+* mA.ResidueField :=
      RingEquiv.ofBijective (algebraMap (A ⧸ mA) mA.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField mA)
    let eSquare := residueFieldEquivOfSquareQuotientEquiv mA hmA φ
    let eLocal : ResidueField ξ.base.R ≃+* ResidueField Rbase.R :=
      IsLocalRing.ResidueField.mapEquiv eξR
    exact ⟨(eU.trans eAquot.symm).trans (eSquare.symm.trans eLocal.symm)⟩


/-- An effective versal formal object over a locally Noetherian base whose local ring at the
image point is a G-ring is the system of infinitesimal restrictions of an object over a
finite-type neighbourhood, versal at a finite type point with the same residue field. -/
@[stacks 07XH "the whole statement, unconditionally: Stacks 07QZ — Artin approximation \
over a G-ring — is proved in this library, so the Stacks 07XB that this uses is \
itself unconditional"]
public theorem exists_finiteType_versal_approximation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (ξ : Deformation.Artin.FormalObject B S hS 𝒳.val.p)
    (heffective : Deformation.Artin.FormalObject.IsEffective B S hS 𝒳.val.p
      𝒳.property ξ)
    (s : S) (hs : ξ.base.toS (closedPoint ξ.base.R) = s)
    (hG : IsGRing (S.presheaf.stalk s))
    (hlimit : AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (baseFiberedCategory B S hS)
      (structureMorphism B S hS 𝒳))
    [Algebra (S.presheaf.stalk s : Type u) ξ.base.R]
    (iΛ : Spec (.of (S.presheaf.stalk s : Type u)) ⟶ S)
    (hiΛ : iΛ = S.fromSpecStalk s)
    (hΛ : Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk s : Type u) ξ.base.R)) ≫ iΛ = ξ.base.toS)
    (hversal : Deformation.Artin.FormalObject.IsVersal B S hS 𝒳.val.p 𝒳.property
      ξ (S.presheaf.stalk s : Type u) iΛ hΛ) :
    ∃ (U : Over S) (u₀ : U.left)
      (V : AlgebraicGeometry.BigFppfOver B S hS)
      (_ : (Over.post B.inclusion).obj V = U)
      (x : 𝒳.val.p.Fiber V)
      (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x.1 = U),
      LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom ∧
      AlgebraicGeometry.IsFiniteTypePoint u₀ ∧
      (letI : CommRing ξ.base.R := ξ.base.commRing
       letI : IsLocalRing ξ.base.R := ξ.base.localRing
       Nonempty (U.left.residueField u₀ ≃+* ResidueField ξ.base.R)) ∧
      Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x.1 hx ∧
      ∃ (xR : Deformation.Artin.CompleteLocalObjects B S hS 𝒳.val.p)
        (e : ξ ≅ (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p
          𝒳.property).obj xR)
        (r : xR.obj.1 ⟶ x.1)
        (eR : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+*
          (Deformation.Artin.chosenBase B S hS 𝒳.val.p xR.obj).R),
        𝒳.val.p.IsCartesian (𝒳.val.p.map r) r ∧
        ((eqToHom (Deformation.Artin.chosenBase_eq B S hS 𝒳.val.p xR.obj).symm ≫
            𝒳.val.p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) =
          (Spec.map (CommRingCat.ofHom
            eR.toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap (U.left.presheaf.stalk u₀)
                (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
            U.left.fromSpecStalk u₀) :=
  exists_finiteType_versal_approximation_aux B S hS 𝒳 ξ heffective s hs hG hlimit
    iΛ hiΛ hΛ hversal

end Deformation.Artin

end
