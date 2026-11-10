module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange

/-!
# The stalk rings of a cartesian square of algebraic spaces

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --h---> Y
```

be a cartesian square of algebraic spaces over a scheme `S` and let `x̄'` be a geometric point of
`X'`.  `AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat` says that the étale local ring
`𝒪_{X', x̄'}` is flat over `𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}` through a ring map restricting to
the canonical maps of Stacks 04NG, the four étale local rings being taken at the images of `x̄'`.
Those étale local rings live one universe above the schemes; the stalks of the structure sheaves
at the points of the small étale sites, which the sheaves of modules have their stalks over, live
in the universe of the schemes and are identified with them by
`AlgebraicGeometry.Space.pointStalkRingEquiv`, compatibly with the structure maps by
`AlgebraicGeometry.Space.stalkStructureMapAsEtaleLocalRingMap_eq`.

This file transports the statement to the stalk rings at the universe of the schemes.

## Main results

* `AlgebraicGeometry.Space.cartesian_stalkRing_tensor_flat`: the stalk of the structure sheaf of
  `X'` at `x̄'` is flat over the tensor product of the stalks of `X` and `Y'` over the stalk of
  `Y`, through a ring map restricting to the two stalk structure maps.

## References

* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The stalk of the structure sheaf of an algebraic space at the point of its small étale site
determined by a geometric point. -/
abbrev structureStalkRing (Z : AlgebraicSpaces B S hS) (z : GeometricPoint B S hS Z.1) :
    CommRingCat.{u} :=
  Stacks.ringFiber (etaleSitePoint B S hS Z.1 z Z.2) (smallEtaleRingedTopos B S hS Z).O.obj

section TensorTransport

variable {R A B' R₁ A₁ B₁ : Type*} [CommRing R] [CommRing A] [CommRing B'] [CommRing R₁]
  [CommRing A₁] [CommRing B₁]

/-- Inverting the ring isomorphisms in a commuting square of ring maps gives a commuting square. -/
private theorem comp_symm_eq_of_comp_eq (e : A ≃+* A₁) (eR : R ≃+* R₁) (u : R →+* A)
    (u₁ : R₁ →+* A₁) (h : e.toRingHom.comp u = u₁.comp eR.toRingHom) :
    e.symm.toRingHom.comp u₁ = u.comp eR.symm.toRingHom := by
  ext r
  have := congrArg (fun k : R →+* A₁ => k (eR.symm r)) h
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] at this ⊢
  rw [← this, RingEquiv.symm_apply_apply]

/-- **A tensor product of commutative algebras is carried to the tensor product of isomorphic
algebras.**  Given ring isomorphisms `R ≃ R₁`, `A ≃ A₁`, `B' ≃ B₁` compatible with the structure
maps, the induced ring map `A ⊗_R B' ⟶ A₁ ⊗_{R₁} B₁` is bijective. -/
theorem bijective_tensorProductMap_of_ringEquiv (φ : R →+* A) (ψ : R →+* B') (φ₁ : R₁ →+* A₁)
    (ψ₁ : R₁ →+* B₁) (eR : R ≃+* R₁) (eA : A ≃+* A₁) (eB : B' ≃+* B₁)
    (hφ : eA.toRingHom.comp φ = φ₁.comp eR.toRingHom)
    (hψ : eB.toRingHom.comp ψ = ψ₁.comp eR.toRingHom) :
    letI := φ.toAlgebra
    letI := ψ.toAlgebra
    letI := φ₁.toAlgebra
    letI := ψ₁.toAlgebra
    ∃ θ : A ⊗[R] B' →+* A₁ ⊗[R₁] B₁,
      θ.comp Algebra.TensorProduct.includeLeftRingHom =
          Algebra.TensorProduct.includeLeftRingHom.comp eA.toRingHom ∧
        θ.comp Algebra.TensorProduct.includeRight.toRingHom =
          Algebra.TensorProduct.includeRight.toRingHom.comp eB.toRingHom ∧
        Function.Bijective θ := by
  let := φ.toAlgebra
  let := ψ.toAlgebra
  let := φ₁.toAlgebra
  let := ψ₁.toAlgebra
  -- the target as an `R`-algebra through `eR`
  let : Algebra R (A₁ ⊗[R₁] B₁) := ((algebraMap R₁ (A₁ ⊗[R₁] B₁)).comp eR.toRingHom).toAlgebra
  let fA : A →ₐ[R] A₁ ⊗[R₁] B₁ :=
    { toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp eA.toRingHom
      commutes' := fun r => by
        change Algebra.TensorProduct.includeLeftRingHom (eA (φ r)) =
          algebraMap R₁ (A₁ ⊗[R₁] B₁) (eR r)
        have : eA (φ r) = φ₁ (eR r) := congrArg (fun k : R →+* A₁ => k r) hφ
        rw [this]
        exact (Algebra.TensorProduct.includeLeft (R := R₁) (S := R₁) (A := A₁)
          (B := B₁)).commutes (eR r) }
  let fB : B' →ₐ[R] A₁ ⊗[R₁] B₁ :=
    { toRingHom := Algebra.TensorProduct.includeRight.toRingHom.comp eB.toRingHom
      commutes' := fun r => by
        change Algebra.TensorProduct.includeRight (eB (ψ r)) =
          algebraMap R₁ (A₁ ⊗[R₁] B₁) (eR r)
        have : eB (ψ r) = ψ₁ (eR r) := congrArg (fun k : R →+* B₁ => k r) hψ
        rw [this]
        exact Algebra.TensorProduct.includeRight.commutes (eR r) }
  let θ := Algebra.TensorProduct.lift fA fB (fun _ _ => Commute.all _ _)
  -- the inverse, through `eR.symm`
  let : Algebra R₁ (A ⊗[R] B') := ((algebraMap R (A ⊗[R] B')).comp eR.symm.toRingHom).toAlgebra
  have hφ' := comp_symm_eq_of_comp_eq eA eR φ φ₁ hφ
  have hψ' := comp_symm_eq_of_comp_eq eB eR ψ ψ₁ hψ
  let gA : A₁ →ₐ[R₁] A ⊗[R] B' :=
    { toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp eA.symm.toRingHom
      commutes' := fun r => by
        change Algebra.TensorProduct.includeLeftRingHom (eA.symm (φ₁ r)) =
          algebraMap R (A ⊗[R] B') (eR.symm r)
        have : eA.symm (φ₁ r) = φ (eR.symm r) := congrArg (fun k : R₁ →+* A => k r) hφ'
        rw [this]
        exact (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A)
          (B := B')).commutes (eR.symm r) }
  let gB : B₁ →ₐ[R₁] A ⊗[R] B' :=
    { toRingHom := Algebra.TensorProduct.includeRight.toRingHom.comp eB.symm.toRingHom
      commutes' := fun r => by
        change Algebra.TensorProduct.includeRight (eB.symm (ψ₁ r)) =
          algebraMap R (A ⊗[R] B') (eR.symm r)
        have : eB.symm (ψ₁ r) = ψ (eR.symm r) := congrArg (fun k : R₁ →+* B' => k r) hψ'
        rw [this]
        exact Algebra.TensorProduct.includeRight.commutes (eR.symm r) }
  let κ := Algebra.TensorProduct.lift gA gB (fun _ _ => Commute.all _ _)
  refine ⟨θ.toRingHom, ?_, ?_, ?_⟩
  · ext a
    simp [θ, fA]
  · ext b
    simp [θ, fB]
  · have h₁ : ∀ t, κ (θ t) = t := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul a b => simp [θ, κ, fA, fB, gA, gB, Algebra.TensorProduct.tmul_mul_tmul]
      | add s t hs ht => simp only [map_add, hs, ht]
    have h₂ : ∀ t, θ (κ t) = t := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul a b => simp [θ, κ, fA, fB, gA, gB, Algebra.TensorProduct.tmul_mul_tmul]
      | add s t hs ht => simp only [map_add, hs, ht]
    exact ⟨Function.LeftInverse.injective h₁, Function.RightInverse.surjective h₂⟩

end TensorTransport

/-- The identification of stalk rings with étale local rings commutes with the transport along an
equality of geometric points. -/
theorem pointStalkRingEquiv_eqToHom_apply (Z : AlgebraicSpaces B S hS)
    {z₁ z₂ : GeometricPoint B S hS Z.1} (e : z₁ = z₂) (a : structureStalkRing B S hS Z z₁) :
    pointStalkRingEquiv B S hS Z z₂ ((eqToHom (congrArg (structureStalkRing B S hS Z) e)).hom a) =
      (eqToHom (congrArg (etaleLocalRing B S hS Z.1) e)).hom
        (pointStalkRingEquiv B S hS Z z₁ a) := by
  subst e
  rfl

/-- `AlgebraicGeometry.Space.pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap`, at an
element. -/
theorem pointStalkRingEquiv_smallEtaleStalkPullbackRingMap_apply {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (z : GeometricPoint B S hS Z.1)
    (a : structureStalkRing B S hS W (geometricPointMap k.hom z)) :
    pointStalkRingEquiv B S hS Z z (smallEtaleStalkPullbackRingMap B S hS k z a) =
      etaleLocalRingMap Z.2 k.hom z (pointStalkRingEquiv B S hS W (geometricPointMap k.hom z) a) :=
  DFunLike.congr_fun (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS k z) a

/-- The two images in the base of a geometric point of the upper-left corner of a commutative
square of algebraic spaces agree. -/
theorem geometricPointMap_comm {X' X Y' Y : AlgebraicSpaces B S hS}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y' ⟶ Y} (w : g' ≫ f = f' ≫ h)
    (x' : GeometricPoint B S hS X'.1) :
    geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap h.hom (geometricPointMap f'.hom x') :=
  congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') w

/-- **The stalk ring of the upper-left corner of a cartesian square of algebraic spaces is flat
over the tensor product of the two adjacent stalk rings over the stalk ring of the base**, through
a ring map restricting to the two homomorphisms of stalk rings of Stacks 05V5.  This is
`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat` read on the stalks of the structure
sheaves at the points of the small étale sites. -/
theorem cartesian_stalkRing_tensor_flat {X' X Y' Y : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (h : Y' ⟶ Y) (hpb : IsPullback g' f' f h)
    (x' : GeometricPoint B S hS X'.1) :
    letI : Algebra
        (structureStalkRing B S hS Y (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        (structureStalkRing B S hS X (geometricPointMap g'.hom x')) :=
      (smallEtaleStalkPullbackRingMap B S hS f (geometricPointMap g'.hom x')).toAlgebra
    letI : Algebra
        (structureStalkRing B S hS Y (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        (structureStalkRing B S hS Y' (geometricPointMap f'.hom x')) :=
      ((smallEtaleStalkPullbackRingMap B S hS h (geometricPointMap f'.hom x')).comp
        (eqToHom (congrArg (structureStalkRing B S hS Y)
          (geometricPointMap_comm B S hS hpb.w x'))).hom).toAlgebra
    ∃ φ : TensorProduct (structureStalkRing B S hS Y
          (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        (structureStalkRing B S hS X (geometricPointMap g'.hom x'))
        (structureStalkRing B S hS Y' (geometricPointMap f'.hom x')) →+*
        structureStalkRing B S hS X' x',
      φ.comp Algebra.TensorProduct.includeLeftRingHom =
          smallEtaleStalkPullbackRingMap B S hS g' x' ∧
        φ.comp Algebra.TensorProduct.includeRight.toRingHom =
          smallEtaleStalkPullbackRingMap B S hS f' x' ∧ φ.Flat := by
  have hy := geometricPointMap_comm B S hS hpb.w x'
  obtain ⟨φe, hl, hr, hflat⟩ := cartesian_etaleStalk_tensor_flat B S hS g' f' f h hpb x'
  let eR := pointStalkRingEquiv B S hS Y (geometricPointMap f.hom (geometricPointMap g'.hom x'))
  let eA := pointStalkRingEquiv B S hS X (geometricPointMap g'.hom x')
  let eB := pointStalkRingEquiv B S hS Y' (geometricPointMap f'.hom x')
  let eC := pointStalkRingEquiv B S hS X' x'
  have hφ : eA.toRingHom.comp (smallEtaleStalkPullbackRingMap B S hS f
        (geometricPointMap g'.hom x')) =
      (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).comp eR.toRingHom :=
    pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS f _
  have hψ : eB.toRingHom.comp ((smallEtaleStalkPullbackRingMap B S hS h
        (geometricPointMap f'.hom x')).comp
        (eqToHom (congrArg (structureStalkRing B S hS Y) hy)).hom) =
      ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) hy) ≫
        CommRingCat.ofHom (etaleLocalRingMap Y'.2 h.hom (geometricPointMap f'.hom x'))).hom).comp
          eR.toRingHom := by
    ext a
    change eB (smallEtaleStalkPullbackRingMap B S hS h _
        ((eqToHom (congrArg (structureStalkRing B S hS Y) hy)).hom a)) =
      etaleLocalRingMap Y'.2 h.hom _
        ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) hy)).hom (eR a))
    rw [pointStalkRingEquiv_smallEtaleStalkPullbackRingMap_apply,
      pointStalkRingEquiv_eqToHom_apply B S hS Y hy]
  obtain ⟨θ, hθl, hθr, hθ⟩ := bijective_tensorProductMap_of_ringEquiv _ _ _ _ eR eA eB hφ hψ
  refine ⟨eC.symm.toRingHom.comp (φe.comp θ), ?_, ?_, ?_⟩
  · ext a
    have h₁ := DFunLike.congr_fun hθl a
    have h₂ := DFunLike.congr_fun hl (eA a)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h₁ h₂ ⊢
    rw [h₁, h₂, ← pointStalkRingEquiv_smallEtaleStalkPullbackRingMap_apply,
      RingEquiv.symm_apply_apply]
  · ext a
    have h₁ := DFunLike.congr_fun hθr a
    have h₂ := DFunLike.congr_fun hr (eB a)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] at h₁ h₂ ⊢
    rw [h₁, h₂, ← pointStalkRingEquiv_smallEtaleStalkPullbackRingMap_apply,
      RingEquiv.symm_apply_apply]
  · exact ((RingHom.Flat.of_bijective hθ).comp hflat).comp
      (RingHom.Flat.of_bijective eC.symm.bijective)

end AlgebraicGeometry.Space

end
