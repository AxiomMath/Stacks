module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FinitePushforwardModuleStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusEmbeddingOrbit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint

/-!
# The lifts of the geometric point at a point through a finite morphism

Let `f : X ⟶ Y` be a morphism of a big étale site and `y` a point of `Y`, with geometric point
`ȳ : Spec κ(y)‾ ⟶ Y`. A lift of `ȳ` through `f` is the same datum as a point `x` of `X` over `y`
together with a `κ(y)`-embedding `κ(x) → κ(y)‾`. Composing a lift with the geometric Frobenius
of `ȳ` (for `κ(y)` finite) composes the embedding with the Frobenius automorphism of `κ(y)‾`.

## Main definitions

* `Stacks.Frobenius.fiberResidueAlgebra`: `κ(x)` as an algebra over `κ(y)`, for `f(x) = y`.
* `Stacks.Frobenius.liftOfEmbedding`: the lift attached to an embedding.

## Main results

* `Stacks.Frobenius.liftOfEmbedding_injective`, `Stacks.Frobenius.exists_liftOfEmbedding`: the
  lifts are exactly the `liftOfEmbedding`s, once each.
* `Stacks.Frobenius.frobeniusPointHom_comp_liftOfEmbedding`: the Frobenius acts on the
  embeddings by composition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Frobenius

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)

/-- `κ(x)` as an algebra over `κ(y)`, for a point `x` of `X` with `f(x) = y`. -/
public abbrev fiberResidueAlgebra (x : {x : X // f x = y}) :
    Algebra (Y.residueField y) (X.residueField x.1) :=
  ((Y.residueFieldCongr x.2.symm).hom ≫ f.residueFieldMap x.1).hom.toAlgebra

/-- The lifts through `f` of the geometric point `ȳ = geometricPointAt Y y`. -/
public abbrev PointLifts :=
  {g : (geometricPointAt Y y).source ⟶ X // g ≫ f = (geometricPointAt Y y).hom}

/-- The `κ(y)`-embeddings `κ(x) → κ(y)‾`, for a point `x` over `y`. -/
public abbrev FiberEmbeddings (x : {x : X // f x = y}) : Type u :=
  letI := fiberResidueAlgebra f y x
  X.residueField x.1 →ₐ[Y.residueField y] AlgebraicClosure (Y.residueField y)

/-- The lift of `ȳ` attached to a `κ(y)`-embedding `κ(x) → κ(y)‾`. -/
public def liftOfEmbedding (x : {x : X // f x = y}) (ι : FiberEmbeddings f y x) :
    PointLifts f y :=
  letI := fiberResidueAlgebra f y x
  ⟨Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ X.fromSpecResidueField x.1, by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.residueFieldCongr_fromSpecResidueField x.2.symm, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    change _ = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y
    congr 2
    ext z
    exact ι.commutes z⟩

/-- The lift attached to an embedding is the morphism attached by `Scheme.SpecToEquivOfField` to
the point and the embedding. -/
public theorem liftOfEmbedding_eq (x : {x : X // f x = y}) (ι : FiberEmbeddings f y x) :
    (liftOfEmbedding f y x ι).1 = (Scheme.SpecToEquivOfField _ X).symm
      ⟨x.1, letI := fiberResidueAlgebra f y x; CommRingCat.ofHom ι.toRingHom⟩ :=
  rfl

/-- The lift attached to an embedding passes through the point. -/
public theorem liftOfEmbedding_apply (x : {x : X // f x = y}) (ι : FiberEmbeddings f y x)
    (s : (geometricPointAt Y y).source) : (liftOfEmbedding f y x ι).1 s = x.1 := by
  show (X.fromSpecResidueField x.1) _ = x.1
  exact Scheme.fromSpecResidueField_apply _ _

/-- Distinct embeddings give distinct lifts. -/
public theorem liftOfEmbedding_injective (x : {x : X // f x = y}) :
    Function.Injective (liftOfEmbedding f y x) := by
  let := fiberResidueAlgebra f y x
  intro ι ι' h
  have h1 := congrArg (Scheme.SpecToEquivOfField _ X)
    ((liftOfEmbedding_eq f y x ι).symm.trans ((congrArg Subtype.val h).trans
      (liftOfEmbedding_eq f y x ι')))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
  ext z
  exact congrArg (fun g => g.hom z) (eq_of_heq (Sigma.mk.inj h1).2)

/-- **Every lift is attached to an embedding.** -/
public theorem exists_liftOfEmbedding (ℓ : PointLifts f y) :
    ∃ (x : {x : X // f x = y}) (ι : FiberEmbeddings f y x), liftOfEmbedding f y x ι = ℓ := by
  set e := Scheme.SpecToEquivOfField _ X ℓ.1 with he
  have hℓ : ℓ.1 = Spec.map e.2 ≫ X.fromSpecResidueField e.1 :=
    ((Scheme.SpecToEquivOfField _ X).symm_apply_apply ℓ.1).symm
  have hcomp : Scheme.SpecToEquivOfField _ Y (ℓ.1 ≫ f) =
      Scheme.SpecToEquivOfField _ Y (geometricPointAt Y y).hom := congrArg _ ℓ.2
  have h1 : ℓ.1 ≫ f =
      (Scheme.SpecToEquivOfField _ Y).symm ⟨f e.1, f.residueFieldMap e.1 ≫ e.2⟩ := by
    rw [hℓ, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc]
    rfl
  have h2 : (geometricPointAt Y y).hom = (Scheme.SpecToEquivOfField _ Y).symm
      ⟨y, CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))⟩ :=
    rfl
  rw [h1, h2, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Scheme.SpecToEquivOfField_eq_iff] at hcomp
  obtain ⟨hp, hφ⟩ := hcomp
  let x : {x : X // f x = y} := ⟨e.1, hp⟩
  let := fiberResidueAlgebra f y x
  let ι : FiberEmbeddings f y x :=
    { toRingHom := e.2.hom
      commutes' := fun z => by
        have hz := congrArg (fun g => g.hom ((Y.residueFieldCongr hp).inv z)) hφ
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hz
        show e.2.hom (f.residueFieldMap e.1 ((Y.residueFieldCongr hp.symm).hom z)) = _
        exact hz.trans (congrArg
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))
          (Iso.inv_hom_id_apply (Y.residueFieldCongr hp) z)) }
  exact ⟨x, ι, Subtype.ext hℓ.symm⟩

/-- An automorphism of `κ(y)‾` over `κ(y)` acts on the embeddings by composition. -/
public def FiberEmbeddings.comp (x : {x : X // f x = y})
    (τ : AlgebraicClosure (Y.residueField y) ≃ₐ[Y.residueField y]
      AlgebraicClosure (Y.residueField y)) (ι : FiberEmbeddings f y x) :
    FiberEmbeddings f y x :=
  letI := fiberResidueAlgebra f y x
  (τ : _ →ₐ[Y.residueField y] _).comp ι

/-- Precomposing a lift with `Spec` of an automorphism `τ` of `κ(y)‾` is the lift attached to
`τ ∘ ι`. -/
private theorem spec_comp_liftOfEmbedding (x : {x : X // f x = y})
    (τ : AlgebraicClosure (Y.residueField y) ≃ₐ[Y.residueField y]
      AlgebraicClosure (Y.residueField y)) (ι : FiberEmbeddings f y x) :
    Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫ (liftOfEmbedding f y x ι).1 =
      (liftOfEmbedding f y x (FiberEmbeddings.comp f y x τ ι)).1 := by
  let := fiberResidueAlgebra f y x
  show Spec.map _ ≫ Spec.map _ ≫ X.fromSpecResidueField x.1 =
    Spec.map _ ≫ X.fromSpecResidueField x.1
  rw [← Spec.map_comp_assoc]
  rfl

/-- **The geometric Frobenius acts on lifts through the embeddings**: composing the lift attached
to `ι` with the geometric Frobenius of `ȳ` gives the lift attached to `σ ∘ ι`. -/
public theorem frobeniusPointHom_comp_liftOfEmbedding [Finite (Y.residueField y)]
    (x : {x : X // f x = y}) (ι : FiberEmbeddings f y x) :
    (frobeniusPointHom Y y).hom ≫ (liftOfEmbedding f y x ι).1 =
      (liftOfEmbedding f y x
        (FiberEmbeddings.comp f y x (residueGeometricFrobenius Y y) ι)).1 := by
  rw [frobeniusPointHom_hom]
  exact spec_comp_liftOfEmbedding f y x _ ι

/-- The automorphism `τ` of `κ(y)‾` acts on lifts through the embeddings. -/
public theorem galoisPointHom_comp_liftOfEmbedding (x : {x : X // f x = y})
    (τ : AlgebraicClosure (Y.residueField y) ≃ₐ[Y.residueField y]
      AlgebraicClosure (Y.residueField y)) (ι : FiberEmbeddings f y x) :
    (galoisPointHom (AlgebraicClosure (Y.residueField y)) τ (Y.fromSpecResidueField y)).hom ≫
        (liftOfEmbedding f y x ι).1 =
      (liftOfEmbedding f y x (FiberEmbeddings.comp f y x τ ι)).1 := by
  rw [galoisPointHom_hom]
  exact spec_comp_liftOfEmbedding f y x τ ι

end Stacks.Frobenius

namespace AlgebraicGeometry

open Stacks.Frobenius

variable {k : Type u} [Field k] {S : Scheme.{u}} (K : Type u) [Field K] [IsAlgClosed K]
  [Algebra k K] (s : Spec (.of k) ⟶ S)

/-- Morphisms of geometric points are determined by their underlying morphisms of schemes. -/
public theorem GeometricPoint.Hom.ext_of_hom {s t : GeometricPoint S}
    {a b : GeometricPoint.Hom s t} (h : a.hom = b.hom) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- The morphisms of geometric points attached to automorphisms compose as the automorphisms. -/
public theorem galoisPointHom_comp (σ τ : K ≃ₐ[k] K) :
    (galoisPointHom K σ s).comp (galoisPointHom K τ s) = galoisPointHom K (σ * τ) s := by
  refine GeometricPoint.Hom.ext_of_hom ?_
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

end AlgebraicGeometry

end
