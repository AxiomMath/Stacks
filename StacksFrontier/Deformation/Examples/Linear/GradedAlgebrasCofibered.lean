module

public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebras

/-!
# Graded algebras are cofibered in groupoids over the base category

The projection sending a graded algebra, finite projective in each degree, over an object of
`𝒞_Λ` to that object is cofibered in groupoids. The pushforward of `(A, P)` along `A → B` is
`(B, P ⊗_A B)` with the base-changed grading; and given `(A, P) → (B, Q)`, `(A, P) → (C, R)`
and `B → C` over `A`, the filling morphism `Q → R` is the algebra map out of `Q ≅ P ⊗_A B`
determined by `P → R` and `B → C`, which respects the gradings because it does so on the
generators `b ⊗ p`.

## Main definitions

* `Deformation.Examples.ProjectiveGradedAlgebra.morphismPushoutEquiv`: the identification of
  the target of a base-change morphism with the pushout of its source.

## Main results

* `Deformation.Examples.ProjectiveGradedAlgebra.morphismPushoutEquiv_tmul`: that
  identification sends `s ⊗ x` to `s • f x`.
* `Deformation.Examples.ProjectiveGradedAlgebra.gradedHom_proj_apply`: a base-change morphism
  commutes with the projections onto graded pieces.
* `Deformation.Examples.ProjectiveGradedAlgebra.pushout_symm_mem_baseChange`: a homogeneous
  element of the target corresponds, under that identification, to an element of the base
  change of the matching graded piece of the source.
* `Deformation.Examples.ProjectiveGradedAlgebra.projection_isCofiberedInGroupoids`: the
  base-algebra projection is cofibered in groupoids.

## Implementation notes

The carrier universe is required to contain the universe of the base algebras, as extension of
scalars needs.

## References

* [Stacks Project, Tag 0D3L](https://stacks.math.columbia.edu/tag/0D3L)
-/

@[expose] public section

open CategoryTheory TensorProduct

namespace Deformation.Examples.ProjectiveGradedAlgebra

universe u v w m

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The projection of a graded algebra onto its `d`-th graded piece, as a linear map. -/
private noncomputable def pieceProj
    (X : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k) (d : ℕ) :
    X.carrier →ₗ[↑X.base] X.grading d :=
  (DFinsupp.lapply d).comp (DirectSum.decomposeAlgEquiv X.grading).toLinearMap

/-- The projection onto a graded piece is a retraction of the inclusion. -/
private theorem pieceProj_comp_subtype
    (X : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k) (d : ℕ) :
    (pieceProj X d).comp (X.grading d).subtype = LinearMap.id := by
  ext x
  simp [pieceProj, DirectSum.decomposeAlgEquiv]

/-- Extension of scalars commutes with taking a graded piece: the `d`-th piece of the
base-changed algebra is the base change of the `d`-th piece. -/
private noncomputable def baseChangePieceEquiv
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k)
    [Algebra (↑X.base) (↑A)] [IsScalarTower (↑X.base) (↑A) (↑A)] (d : ℕ) :
    TensorProduct (↑X.base) (↑A) (X.grading d) ≃ₗ[↑A]
      (X.grading d).baseChange (↑A) := by
  let p := X.grading d
  have hcomp : (LinearMap.baseChange (↑A) (pieceProj X d)).comp
      (LinearMap.baseChange (↑A) p.subtype) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, pieceProj_comp_subtype, LinearMap.baseChange_id]
  have hi : Function.Injective (LinearMap.baseChange (↑A) p.subtype) := 
    Function.LeftInverse.injective (g := LinearMap.baseChange (↑A) (pieceProj X d))
      (LinearMap.congr_fun hcomp)
  exact LinearEquiv.ofBijective (p.toBaseChange (↑A))
    ⟨fun x y hxy ↦ hi (congrArg Subtype.val hxy), Submodule.toBaseChange_surjective (↑A) p⟩

/-- Each base-changed graded piece is finite over the new base algebra. -/
private theorem baseChangePieceFinite
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k)
    [Algebra (↑X.base) (↑A)] (d : ℕ) :
    Module.Finite (↑A) ((X.grading d).baseChange (↑A)) := by
  let : CommRing (↑A) := A.commRing
  let : CommRing (↑X.base) := X.base.commRing
  let : Module.Finite (↑A) (TensorProduct (↑X.base) (↑A) (X.grading d)) := inferInstance
  let map : TensorProduct (↑X.base) (↑A) (X.grading d) →ₗ[↑A]
      (X.grading d).baseChange (↑A) := (X.grading d).toBaseChange (↑A)
  exact Module.Finite.of_surjective (σ := RingHom.id (↑A)) map
    (Submodule.toBaseChange_surjective (↑A) (X.grading d))

/-- Each base-changed graded piece is projective over the new base algebra. -/
private theorem baseChangePieceProjective
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k)
    [Algebra (↑X.base) (↑A)] [IsScalarTower (↑X.base) (↑A) (↑A)] (d : ℕ) :
    Module.Projective (↑A) ((X.grading d).baseChange (↑A)) :=
  Module.Projective.of_equiv' (baseChangePieceEquiv X d)

/-- The pushforward of a graded algebra along a morphism of base algebras: extension of scalars
with the base-changed grading. -/
private noncomputable def baseChangeObject
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k) (f : X.base ⟶ A) :
    ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k := by
  letI : Algebra (↑X.base) (↑A) := f.hom.toAlgebra
  letI : IsScalarTower (↑X.base) (↑A)
      (TensorProduct (↑X.base) (↑A) X.carrier) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine {
    base := A
    carrier := TensorProduct (↑X.base) (↑A) X.carrier
    grading := fun d ↦ (X.grading d).baseChange (↑A)
    commRing := inferInstance
    algebra := inferInstance
    graded := inferInstance
    finite := ?_
    projective := ?_ }
  · intro d
    exact baseChangePieceFinite X d
  · intro d
    exact baseChangePieceProjective X d

/-- The canonical morphism from a graded algebra to its pushforward. -/
private noncomputable def baseChangeMorphism
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k) (f : X.base ⟶ A) :
    ProjectiveGradedAlgebra.Hom X (baseChangeObject X f) := by
  let Y := baseChangeObject X f
  letI : Algebra (↑X.base) (↑A) := f.hom.toAlgebra
  letI : CommRing Y.carrier := Y.commRing
  letI : Algebra (↑A) Y.carrier := Y.algebra
  letI : Algebra (↑X.base) Y.carrier :=
    ((algebraMap (↑A) Y.carrier).comp f.hom.toRingHom).toAlgebra
  letI : IsScalarTower (↑X.base) (↑A) Y.carrier :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      simp only [Algebra.smul_def]
      congr 1
  let i : X.carrier →ₐ[↑X.base] TensorProduct (↑X.base) (↑A) X.carrier :=
    Algebra.TensorProduct.includeRight
      (R := (↑X.base)) (A := (↑A)) (B := X.carrier)
  refine {
    base := f
    map := by
      change X.carrier →+* TensorProduct (↑X.base) (↑A) X.carrier
      exact i.toRingHom
    map_smul := ?_
    map_mem := ?_
    isBaseChange := ?_ }
  · intro r x
    change (1 : A) ⊗ₜ[↑X.base] (r • x) =
      f.hom r • ((1 : A) ⊗ₜ[↑X.base] x)
    rw [TensorProduct.tmul_smul]
    simp only [Algebra.smul_def]
    congr 1
  · intro d x hx
    change (1 : ↑A) ⊗ₜ[↑X.base] x ∈ (X.grading d).baseChange (↑A)
    simpa [i, Algebra.TensorProduct.includeRight] using
      (Submodule.tmul_mem_baseChange_of_mem (1 : ↑A) hx)
  · exact TensorProduct.isBaseChange (↑X.base) X.carrier (↑A)

/-- A morphism of graded algebras sends the image of a scalar of the source base to the image of
its base morphism. -/
private theorem map_algebraMap_eq
    {X Y : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (f : ProjectiveGradedAlgebra.Hom X Y) (r : X.base) :
    f.map (algebraMap (↑X.base) X.carrier r) =
      algebraMap (↑Y.base) Y.carrier (f.base.hom r) := by
  simpa [Algebra.smul_def] using f.map_smul r (1 : X.carrier)

/-- A base-change morphism of graded algebras exhibits its target as the pushout of its source
along the morphism of base algebras. -/
public noncomputable def morphismPushoutEquiv
    {X Y : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (f : ProjectiveGradedAlgebra.Hom X Y) :
    letI : Algebra (↑X.base) (↑Y.base) := f.base.hom.toAlgebra
    TensorProduct (↑X.base) (↑Y.base) X.carrier ≃ₐ[↑Y.base] Y.carrier := by
  letI : CommRing (↑X.base) := X.base.commRing
  letI : CommRing (↑Y.base) := Y.base.commRing
  letI : CommRing X.carrier := X.commRing
  letI : CommRing Y.carrier := Y.commRing
  letI : Algebra (↑X.base) (↑Y.base) := f.base.hom.toAlgebra
  letI : Algebra (↑X.base) Y.carrier :=
    ((algebraMap (↑Y.base) Y.carrier).comp f.base.hom.toRingHom).toAlgebra
  letI : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let alg : X.carrier →ₐ[↑X.base] Y.carrier := {
    toRingHom := f.map
    commutes' := fun r ↦ by
      have h := f.map_smul r (1 : X.carrier)
      calc
        f.map (algebraMap (↑X.base) X.carrier r) =
            algebraMap (↑Y.base) Y.carrier (f.base.hom r) := by
          simpa [Algebra.smul_def] using h
        _ = algebraMap (↑X.base) Y.carrier r := rfl }
  letI : Algebra X.carrier Y.carrier := alg.toRingHom.toAlgebra
  letI : IsScalarTower (↑X.base) X.carrier Y.carrier :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (alg.commutes r).symm
  have hbc : IsBaseChange (↑Y.base)
      (IsScalarTower.toAlgHom (↑X.base) X.carrier Y.carrier).toLinearMap := f.isBaseChange
  letI : Algebra.IsPushout (↑X.base) (↑Y.base) X.carrier Y.carrier := ⟨hbc⟩
  exact Algebra.IsPushout.equiv (↑X.base) (↑Y.base) X.carrier Y.carrier

/-- The pushout identification sends `s ⊗ x` to `s • f x`. -/
public theorem morphismPushoutEquiv_tmul
    {X Y : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (g : ProjectiveGradedAlgebra.Hom X Y) (s : Y.base) (x : X.carrier) :
    letI : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
    morphismPushoutEquiv g (s ⊗ₜ[↑X.base] x) = s • g.map x := by
  let : CommRing (↑X.base) := X.base.commRing
  let : CommRing (↑Y.base) := Y.base.commRing
  let : CommRing X.carrier := X.commRing
  let : CommRing Y.carrier := Y.commRing
  let : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
  let : Algebra (↑X.base) Y.carrier :=
    ((algebraMap (↑Y.base) Y.carrier).comp g.base.hom.toRingHom).toAlgebra
  let : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let alg : X.carrier →ₐ[↑X.base] Y.carrier := {
    toRingHom := g.map
    commutes' := fun r ↦ map_algebraMap_eq g r }
  let : Algebra X.carrier Y.carrier := alg.toRingHom.toAlgebra
  let : IsScalarTower (↑X.base) X.carrier Y.carrier :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (alg.commutes r).symm
  let hbc : IsBaseChange (↑Y.base) alg.toLinearMap := g.isBaseChange
  let : Algebra.IsPushout (↑X.base) (↑Y.base) X.carrier Y.carrier := ⟨hbc⟩
  change Algebra.IsPushout.equiv (↑X.base) (↑Y.base) X.carrier Y.carrier
      (s ⊗ₜ[↑X.base] x) = _
  rw [Algebra.IsPushout.equiv_tmul, show algebraMap X.carrier Y.carrier = g.map from rfl]
  simp [Algebra.smul_def]

/-- A base-change morphism of graded algebras commutes with the projections onto graded
pieces. -/
public theorem gradedHom_proj_apply
    {X Y : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (f : ProjectiveGradedAlgebra.Hom X Y) (d : ℕ) (x : X.carrier) :
    GradedAlgebra.proj Y.grading d (f.map x) =
      f.map (GradedAlgebra.proj X.grading d x) := by
  let dx := DirectSum.decomposeAlgEquiv X.grading x
  have hdx : (DirectSum.decomposeAlgEquiv X.grading).symm dx = x := by
    simp [dx]
  rw [← hdx]
  induction dx using DirectSum.induction_on with
  | zero => simp [GradedAlgebra.proj_apply]
  | add a b ha hb =>
      simp only [map_add, ha, hb]
  | of i a =>
      have hmem : ((a : X.grading i) : X.carrier) ∈ X.grading i := a.property
      have hmapmem := f.map_mem i _ hmem
      simp only [DirectSum.decomposeAlgEquiv_symm_apply, DirectSum.decompose_symm_of]
      by_cases hid : i = d
      · subst d
        simp only [GradedAlgebra.proj_apply,
          DirectSum.decompose_of_mem_same _ hmem,
          DirectSum.decompose_of_mem_same _ hmapmem]
      · simp only [GradedAlgebra.proj_apply,
          DirectSum.decompose_of_mem_ne _ hmapmem hid,
          DirectSum.decompose_of_mem_ne _ hmem hid, map_zero]

/-- Under the pushout identification, a homogeneous element of the target corresponds to an
element of the base change of the corresponding graded piece of the source. -/
public theorem pushout_symm_mem_baseChange
    {X Y : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (g : ProjectiveGradedAlgebra.Hom X Y) (d : ℕ) :
    letI : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
    ∀ y : Y.carrier, y ∈ Y.grading d →
      (morphismPushoutEquiv g).symm y ∈ (X.grading d).baseChange (↑Y.base) := by
  let : CommRing (↑X.base) := X.base.commRing
  let : CommRing (↑Y.base) := Y.base.commRing
  let : CommRing X.carrier := X.commRing
  let : CommRing Y.carrier := Y.commRing
  let : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
  intro y hy
  let e := morphismPushoutEquiv g
  let pX := GradedAlgebra.proj X.grading d
  let pY := GradedAlgebra.proj Y.grading d
  have hproj : pY.comp e.toLinearMap = e.toLinearMap.comp (pX.baseChange (↑Y.base)) := by
    ext s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a x =>
        calc
          pY (e (a ⊗ₜ[↑X.base] x)) = a • pY (g.map x) := by
            rw [morphismPushoutEquiv_tmul, map_smul]
          _ = a • g.map (pX x) := by rw [gradedHom_proj_apply]
          _ = e (a ⊗ₜ[↑X.base] pX x) := by rw [morphismPushoutEquiv_tmul]
  have hpY : pY y = y := by
    simp [pY, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ hy]
  let q := e.symm y
  have hfix : pX.baseChange (↑Y.base) q = q := by
    apply e.injective
    calc
      e (pX.baseChange (↑Y.base) q) = pY (e q) := (LinearMap.congr_fun hproj q).symm
      _ = y := by rw [e.apply_symm_apply, hpY]
      _ = e q := (e.apply_symm_apply y).symm
  let pr := pieceProj X d
  have hp : (pX.baseChange (↑Y.base)) =
      ((X.grading d).subtype.baseChange (↑Y.base)).comp (pr.baseChange (↑Y.base)) := by
    change ((X.grading d).subtype.comp pr).baseChange (↑Y.base) = _
    rw [LinearMap.baseChange_comp]
  rw [Submodule.baseChange]
  refine ⟨pr.baseChange (↑Y.base) q, ?_⟩
  calc
    (X.grading d).subtype.baseChange (↑Y.base) (pr.baseChange (↑Y.base) q) =
        pX.baseChange (↑Y.base) q := by rw [hp]; rfl
    _ = q := hfix

/-- A morphism of graded algebras out of `Y` is determined by its base morphism together with
its restriction along a base-change morphism `X ⟶ Y`, because `Y` is generated over `Y.base`
by the image of `X`. -/
private lemma hom_ext_of_restrict
    {X Y Z : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (g : X ⟶ Y) (c d : Y ⟶ Z) (hbase : c.base = d.base)
    (hmap : ∀ x : X.carrier, c.map (g.map x) = d.map (g.map x)) : c = d := by
  let : CommRing (↑X.base) := X.base.commRing
  let : CommRing (↑Y.base) := Y.base.commRing
  let : CommRing (↑Z.base) := Z.base.commRing
  let : CommRing X.carrier := X.commRing
  let : CommRing Y.carrier := Y.commRing
  let : CommRing Z.carrier := Z.commRing
  let : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
  let : Algebra (↑Y.base) (↑Z.base) := c.base.hom.toAlgebra
  let : Algebra (↑X.base) (↑Z.base) := (c.base.hom.comp g.base.hom).toAlgebra
  let : IsScalarTower (↑X.base) (↑Y.base) (↑Z.base) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (↑X.base) Y.carrier :=
    ((algebraMap (↑Y.base) Y.carrier).comp g.base.hom.toRingHom).toAlgebra
  let : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (↑Y.base) Z.carrier :=
    ((algebraMap (↑Z.base) Z.carrier).comp c.base.hom.toRingHom).toAlgebra
  let : IsScalarTower (↑Y.base) (↑Z.base) Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (↑X.base) Z.carrier :=
    ((algebraMap (↑Z.base) Z.carrier).comp
      (c.base.hom.comp g.base.hom).toRingHom).toAlgebra
  let : IsScalarTower (↑X.base) (↑Y.base) Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let gAlg : X.carrier →ₐ[↑X.base] Y.carrier := {
    toRingHom := g.map
    commutes' := fun r ↦ map_algebraMap_eq g r }
  have hgBC : IsBaseChange (↑Y.base) gAlg.toLinearMap := g.isBaseChange
  let cAlg : Y.carrier →ₐ[↑Y.base] Z.carrier := {
    toRingHom := c.map
    commutes' := fun r ↦ map_algebraMap_eq c r }
  let dAlg : Y.carrier →ₐ[↑Y.base] Z.carrier := {
    toRingHom := d.map
    commutes' := fun r ↦ (map_algebraMap_eq d r).trans (by rw [← hbase]; rfl) }
  have hlinear :
      (cAlg.toLinearMap.restrictScalars (↑X.base)).comp gAlg.toLinearMap =
      (dAlg.toLinearMap.restrictScalars (↑X.base)).comp gAlg.toLinearMap := by
    ext x
    exact hmap x
  have hlin := hgBC.algHom_ext' cAlg.toLinearMap dAlg.toLinearMap hlinear
  exact ProjectiveGradedAlgebra.Hom.ext hbase
    (RingHom.ext fun a ↦ congrArg (fun F : Y.carrier →ₗ[↑Y.base] Z.carrier => F a) hlin)

/-- Given morphisms `g : X ⟶ Y` and `q : X ⟶ Z` of graded algebras and a morphism `b` of the
base algebras of `Y` and `Z` with `g.base ≫ b = q.base`, there is a morphism `Y ⟶ Z` over `b`
through which `q` factors: the algebra map out of `Y ≅ X.carrier ⊗_{X.base} Y.base` given by
`q` and `b`. -/
private lemma exists_fill
    {X Y Z : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (g : X ⟶ Y) (q : X ⟶ Z) (b : Y.base ⟶ Z.base) (hb : g.base ≫ b = q.base) :
    ∃ c : Y ⟶ Z, c.base = b ∧ g ≫ c = q := by
  let : CommRing (↑X.base) := X.base.commRing
  let : CommRing (↑Y.base) := Y.base.commRing
  let : CommRing (↑Z.base) := Z.base.commRing
  let : CommRing X.carrier := X.commRing
  let : CommRing Y.carrier := Y.commRing
  let : CommRing Z.carrier := Z.commRing
  let : Algebra (↑X.base) (↑Y.base) := g.base.hom.toAlgebra
  let : Algebra (↑Y.base) (↑Z.base) := b.hom.toAlgebra
  let : Algebra (↑X.base) (↑Z.base) := q.base.hom.toAlgebra
  have hbRing : b.hom.toRingHom.comp g.base.hom.toRingHom = q.base.hom.toRingHom := by
    have hbHom : (g.base ≫ b).hom.toRingHom = q.base.hom.toRingHom :=
      @congrArg (X.base ⟶ Z.base)
        (↑X.base →+* ↑Z.base) (g.base ≫ b) q.base
        (fun j => j.hom.toRingHom) hb
    ext a
    exact congrArg (fun H : ↑X.base →+* ↑Z.base => H a) hbHom
  let : IsScalarTower (↑X.base) (↑Y.base) (↑Z.base) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change q.base.hom r = b.hom (g.base.hom r)
      exact (congrArg (fun H : ↑X.base →+* ↑Z.base => H r) hbRing).symm
  let : Algebra (↑X.base) Y.carrier :=
    ((algebraMap (↑Y.base) Y.carrier).comp g.base.hom.toRingHom).toAlgebra
  let : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (↑X.base) Z.carrier :=
    ((algebraMap (↑Z.base) Z.carrier).comp q.base.hom.toRingHom).toAlgebra
  let : IsScalarTower (↑X.base) (↑Z.base) Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (↑Y.base) Z.carrier :=
    ((algebraMap (↑Z.base) Z.carrier).comp b.hom.toRingHom).toAlgebra
  let : IsScalarTower (↑Y.base) (↑Z.base) Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower (↑X.base) (↑Y.base) Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap (↑Z.base) Z.carrier (q.base.hom r) =
        algebraMap (↑Z.base) Z.carrier (b.hom (g.base.hom r))
      exact congrArg (algebraMap (↑Z.base) Z.carrier)
        ((congrArg (fun H : ↑X.base →+* ↑Z.base => H r) hbRing).symm)
  let qAlg : X.carrier →ₐ[↑X.base] Z.carrier := {
    toRingHom := q.map
    commutes' := fun r ↦ map_algebraMap_eq q r }
  let : Algebra X.carrier Z.carrier := qAlg.toRingHom.toAlgebra
  let : IsScalarTower (↑X.base) X.carrier Z.carrier :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (qAlg.commutes r).symm
  have hqBC : IsBaseChange (↑Z.base) qAlg.toLinearMap := q.isBaseChange
  let gAlg : X.carrier →ₐ[↑X.base] Y.carrier := {
    toRingHom := g.map
    commutes' := fun r ↦ map_algebraMap_eq g r }
  have hgBC : IsBaseChange (↑Y.base) gAlg.toLinearMap := g.isBaseChange
  let e := morphismPushoutEquiv g
  let lift : TensorProduct (↑X.base) (↑Y.base) X.carrier →ₐ[↑Y.base] Z.carrier :=
    Algebra.TensorProduct.lift (Algebra.ofId (↑Y.base) Z.carrier) qAlg
      (fun _ _ ↦ Commute.all _ _)
  let cAlg : Y.carrier →ₐ[↑Y.base] Z.carrier := lift.comp e.symm
  have he_gen (a : X.carrier) : e (1 ⊗ₜ[↑X.base] a) = g.map a := by
    rw [morphismPushoutEquiv_tmul]
    simp
  have hinv_gen (a : X.carrier) : e.symm (g.map a) = 1 ⊗ₜ[↑X.base] a := by
    apply e.injective
    rw [e.apply_symm_apply, he_gen]
  have hcComp : (cAlg.toLinearMap.restrictScalars (↑X.base)).comp gAlg.toLinearMap =
      qAlg.toLinearMap := by
    ext a
    change lift (e.symm (g.map a)) = q.map a
    rw [hinv_gen]
    simp [lift, Algebra.TensorProduct.lift_tmul, qAlg]
  have hcBC : IsBaseChange (↑Z.base) cAlg.toLinearMap := by
    apply (IsBaseChange.comp_iff hgBC (h := cAlg.toLinearMap)).1
    rw [hcComp]
    exact hqBC
  have hlift_mem (d : ℕ) (t : TensorProduct (↑X.base) (↑Y.base) (X.grading d)) :
      lift ((X.grading d).subtype.baseChange (↑Y.base) t) ∈ Z.grading d := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t t' ht ht' => simpa [map_add] using (Z.grading d).add_mem ht ht'
    | tmul s a =>
        have hs : algebraMap (↑Y.base) Z.carrier s =
            algebraMap (↑Z.base) Z.carrier (b.hom s) := rfl
        have hqa : qAlg a = q.map a := rfl
        simpa [lift, Algebra.TensorProduct.lift_tmul, hs, hqa, Algebra.smul_def] using
          (Z.grading d).smul_mem (b.hom s) (q.map_mem d a a.property)
  have hcMap : cAlg.toRingHom.comp gAlg.toRingHom = q.map := by
    ext a
    exact congrArg (fun l : X.carrier →ₗ[↑X.base] Z.carrier => l a) hcComp
  refine ⟨{
    base := b
    map := cAlg.toRingHom
    map_smul := ?_
    map_mem := ?_
    isBaseChange := ?_ }, rfl, ?_⟩
  · intro s a
    calc
      cAlg.toRingHom (s • a) = s • cAlg.toRingHom a :=
        cAlg.toLinearMap.map_smul s a
      _ = b.hom s • cAlg.toRingHom a := by
        rw [Algebra.smul_def, Algebra.smul_def, show algebraMap (↑Y.base) Z.carrier s =
          algebraMap (↑Z.base) Z.carrier (b.hom s) from rfl]
  · intro d a ha
    have hpre := pushout_symm_mem_baseChange g d a ha
    rw [Submodule.baseChange] at hpre
    obtain ⟨t, ht⟩ := hpre
    change lift (e.symm a) ∈ Z.grading d
    rw [← ht]
    exact hlift_mem d t
  · exact hcBC
  · exact ProjectiveGradedAlgebra.Hom.ext hb hcMap

/-- Given morphisms `g : X ⟶ Y` and `q : X ⟶ Z` of graded algebras and a morphism `b` of the
base algebras of `Y` and `Z` with `g.base ≫ b = q.base`, there is a unique morphism `Y ⟶ Z`
over `b` through which `q` factors. -/
private lemma hom_fillIn
    {X Y Z : ProjectiveGradedAlgebra.{u, v, w, max v m} Λ k}
    (g : X ⟶ Y) (q : X ⟶ Z) (b : Y.base ⟶ Z.base) (hb : g.base ≫ b = q.base) :
    ∃! c : Y ⟶ Z, c.base = b ∧ g ≫ c = q := by
  obtain ⟨c, hcb, hcq⟩ := exists_fill g q b hb
  exact ⟨c, ⟨hcb, hcq⟩, fun d hd ↦ hom_ext_of_restrict g d c (hd.1.trans hcb.symm) fun x ↦
    congrArg (fun h : X ⟶ Z ↦ h.map x) (hd.2.trans hcq.symm)⟩

/-- The base-algebra projection of the category of graded algebras, finite projective in each
degree, is cofibered in groupoids. -/
@[stacks 0D3L]
public theorem projection_isCofiberedInGroupoids :
    IsCofiberedInGroupoids
      (ProjectiveGradedAlgebra.projection.{u, v, w, max v m} (Λ := Λ) (k := k)) := by
  change
    (ProjectiveGradedAlgebra.projection.{u, v, w, max v m}
      (Λ := Λ) (k := k)).op.IsFiberedInGroupoids
  refine { exists_lift := ?_, unique_lift := ?_ }
  · intro V U f X hX
    subst U
    let X₀ := X.unop
    let f₀ : X₀.base ⟶ V.unop := by
      simpa [ProjectiveGradedAlgebra.projection] using f.unop
    let Y := baseChangeObject X₀ f₀
    let mor := baseChangeMorphism X₀ f₀
    refine ⟨Opposite.op Y, Opposite.op mor, ?_⟩
    apply IsHomLift.of_fac' (p := ProjectiveGradedAlgebra.projection.op) f
      (Opposite.op mor) rfl rfl
    apply congrArg Opposite.op
    change mor.base = f₀
    rfl
  · intro x y z φ ψ f h
    let g : ProjectiveGradedAlgebra.Hom x.unop y.unop := φ.unop
    let q : ProjectiveGradedAlgebra.Hom x.unop z.unop := ψ.unop
    let b : y.unop.base ⟶ z.unop.base := f.unop
    have hb : g.base ≫ b = q.base := by
      have hh := congrArg Quiver.Hom.unop h
      simpa [g, q, b, ProjectiveGradedAlgebra.projection] using hh
    obtain ⟨c, ⟨hcb, hcq⟩, huniq⟩ := hom_fillIn g q b hb
    refine ⟨Opposite.op c, ?_, ?_⟩
    · constructor
      · apply Opposite.unop_injective
        change c.base = b
        exact hcb
      · apply Opposite.unop_injective
        exact hcq
    · intro χ hχ
      apply Opposite.unop_injective
      refine huniq χ.unop ⟨?_, ?_⟩
      · have hbase := congrArg Quiver.Hom.unop hχ.1
        simpa [b, ProjectiveGradedAlgebra.projection] using hbase
      · exact congrArg Quiver.Hom.unop hχ.2

end Deformation.Examples.ProjectiveGradedAlgebra
