module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Examples.Geometric.Base

/-!
# Deformations of a commutative algebra

A flat algebra over an object of `𝒞_Λ` is an Artinian local `Λ`-algebra `A` with residue field
`k`, together with a flat `A`-algebra. A morphism of such objects is a morphism `A ⟶ B` of
`𝒞_Λ` and an `A`-algebra map of the flat algebras exhibiting the second as the base change of
the first; "base change" is expressed as the square of underlying commutative rings being a
pushout, which is what makes composition the pasting of two pushout squares. Forgetting the
flat algebra gives a functor to `𝒞_Λ`, and that functor is cofibered in groupoids, the
cocartesian lift of `A ⟶ B` being base change along it.

The *deformation category* of a `k`-algebra `P` is the category of objects over the flat
algebra `(k, P)`, where `k` is the residue field regarded as an object of `𝒞_Λ`.

## Main definitions

* `Deformation.Examples.FlatAlgebraCategory`: a flat algebra over an object of `𝒞_Λ`.
* `Deformation.Examples.FlatAlgebraCategory.Hom`: a base-change morphism of flat algebras.
* `Deformation.Examples.FlatAlgebraCategory.instCategory`: the category structure on them.
* `Deformation.Examples.FlatAlgebraCategory.projection`: the functor to `𝒞_Λ`.
* `Deformation.Examples.residueFieldAlgebra`: the flat algebra `(k, P)`.
* `Deformation.Examples.ringDeformationCategory`: the deformation category of a `k`-algebra.

## Main results

* `Deformation.Examples.ker_algebraMap_eq_map_ker_of_pushout`: in a pushout square of
  commutative algebras whose base map is surjective, the kernel of the map out of the second
  algebra is the ideal extended from the kernel of the base map.
* `Deformation.Examples.flatAlgebraCategory_projection_isCofiberedInGroupoids`: the projection
  to `𝒞_Λ` is cofibered in groupoids.

## Implementation notes

An `f`-linear algebra map inducing an isomorphism after base change is expressed by the pushout
condition on the square of underlying commutative rings. The commutative-ring pushout category
uses one ambient universe for `k`, the Artinian bases and their flat algebras; the universe of
`Λ` remains independent. The deformation category is an abbreviation for a slice category, so
clients use the existing API of `CategoryTheory.Over` directly.

## References

* [Stacks Project, Tag 0DY1](https://stacks.math.columbia.edu/tag/0DY1)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace Deformation.Examples

open scoped TensorProduct in
/-- In a pushout, the kernel of the map from the second algebra is the extension
of the kernel of a surjective map on the base. -/
theorem ker_algebraMap_eq_map_ker_of_pushout
    (R S T Q : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing Q]
    [Algebra R S] [Algebra R T] [Algebra S Q] [Algebra T Q] [Algebra R Q]
    [IsScalarTower R S Q] [IsScalarTower R T Q] [Algebra.IsPushout R S T Q]
    (hT : Function.Surjective (algebraMap R T)) :
    RingHom.ker (algebraMap S Q) =
      (RingHom.ker (algebraMap R T)).map (algebraMap R S) := by
  let e : S ⊗[R] T ≃ₐ[S] Q := Algebra.IsPushout.equiv R S T Q
  have h1 : algebraMap S Q = e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := S) (B := T)).toRingHom := by
    ext s
    simp [e]
  rw [h1, RingHom.ker_comp_of_injective _ e.toRingEquiv.injective]
  let g : R →ₐ[R] T := Algebra.ofId R T
  have h2 : (Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := S) (B := T)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom.comp
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := R) (A := S) (B := R)).toRingHom := by
    ext s
    simp [g]
  have h3 : RingHom.ker
      (Algebra.TensorProduct.map (AlgHom.id R S) g).toRingHom =
      (RingHom.ker (algebraMap R T)).map
        (Algebra.TensorProduct.includeRight
          (R := R) (A := S) (B := R)).toRingHom := by
    exact Algebra.TensorProduct.lTensor_ker (A := S) g hT
  rw [h2, ← RingHom.comap_ker, h3]
  let r : S ⊗[R] R ≃ₐ[R] S := Algebra.TensorProduct.rid R R S
  have h4 : (Algebra.TensorProduct.includeLeft
      (R := R) (S := R) (A := S) (B := R)).toRingHom =
      (r.toRingEquiv.symm : S →+* S ⊗[R] R) := by
    ext s
    apply r.toRingEquiv.injective
    simp [r]
  have h5 : algebraMap R S = (r.toRingEquiv : S ⊗[R] R →+* S).comp
      (Algebra.TensorProduct.includeRight
        (R := R) (A := S) (B := R)).toRingHom := by
    ext x
    simp [r, Algebra.smul_def]
  rw [h4, h5, ← Ideal.map_map, Ideal.comap_coe, Ideal.map_coe, Ideal.comap_symm]

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A flat algebra over an object of `𝒞_Λ`. -/
structure FlatAlgebraCategory (Λ : Type u) (k : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] where
  /-- The Artinian local `Λ`-algebra the flat algebra lives over. -/
  base : ArtinianLocalAlgCat.{u, w, w} Λ k
  /-- The underlying type of the flat algebra. -/
  fiber : Type w
  [commRing : CommRing fiber]
  [algebra : Algebra base fiber]
  [flat : Module.Flat base fiber]

namespace FlatAlgebraCategory

attribute [instance] commRing algebra flat

/-- The structural ring map from the Artinian base to the flat algebra. -/
abbrev structureMap (X : FlatAlgebraCategory.{u, w} Λ k) :
    CommRingCat.of X.base ⟶ CommRingCat.of X.fiber :=
  CommRingCat.ofHom (algebraMap X.base X.fiber)

/-- The underlying map of commutative rings of a morphism of `𝒞_Λ`. -/
abbrev baseMap {X Y : FlatAlgebraCategory.{u, w} Λ k}
    (f : X.base ⟶ Y.base) : CommRingCat.of X.base ⟶ CommRingCat.of Y.base :=
  CommRingCat.ofHom f.hom.toRingHom

/-- A base-change morphism of flat algebras, lying over a morphism of Artinian bases. -/
@[ext]
structure Hom (X Y : FlatAlgebraCategory.{u, w} Λ k) where
  /-- The morphism of Artinian bases. -/
  base : X.base ⟶ Y.base
  /-- The map of the flat algebras. -/
  map : CommRingCat.of X.fiber ⟶ CommRingCat.of Y.fiber
  /-- The square of underlying commutative rings is a pushout. -/
  cartesian : IsPushout (structureMap X) (baseMap base) map (structureMap Y)

/-- Flat algebras over objects of `𝒞_Λ` and their base-change morphisms form a category. -/
instance instCategory : Category (FlatAlgebraCategory.{u, w} Λ k) where
  Hom := Hom
  id X :=
    { base := 𝟙 X.base
      map := 𝟙 (CommRingCat.of X.fiber)
      cartesian := by simpa [baseMap] using
        (IsPushout.of_id_snd : IsPushout (structureMap X) (𝟙 _) (𝟙 _) (structureMap X)) }
  comp f g :=
    { base := f.base ≫ g.base
      map := f.map ≫ g.map
      cartesian := by
        convert f.cartesian.paste_vert g.cartesian using 1; ext; rfl }
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp
  assoc := by intros; ext <;> simp

/-- Forget the flat algebra and retain its Artinian base. -/
@[implicit_reducible]
def projection : FlatAlgebraCategory.{u, w} Λ k ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k where
  obj X := X.base
  map f := f.base

end FlatAlgebraCategory

/-- The flat algebra `(k, P)` over the residue field, regarded as an object of `𝒞_Λ`. -/
noncomputable def residueFieldAlgebra (P : Type w) [CommRing P] [Algebra k P] :
    FlatAlgebraCategory.{u, w} Λ k where
  base := residueFieldBase Λ k
  fiber := P
  algebra := inferInstance
  flat := inferInstance

/-- The category of deformations of the `k`-algebra `P`: flat algebras over Artinian local
bases equipped with a base-change map to `(k, P)`. -/
@[stacks 0DY1 "ring_deformation_category"]
abbrev ringDeformationCategory (P : Type w) [CommRing P] [Algebra k P] :=
  Over (residueFieldAlgebra (Λ := Λ) (k := k) P)

open scoped TensorProduct in
/-- Base change makes the projection from flat algebras to their Artinian bases cofibered in
groupoids. -/
@[stacks 0DY1 "flat_algebra_category_cofibered"]
theorem flatAlgebraCategory_projection_isCofiberedInGroupoids
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    IsCofiberedInGroupoids (FlatAlgebraCategory.projection (Λ := Λ) (k := k)) := by
  classical
  let _ : Category (FlatAlgebraCategory.{u, w} Λ k) := FlatAlgebraCategory.instCategory
  let p := FlatAlgebraCategory.projection (Λ := Λ) (k := k)
  show p.op.IsFiberedInGroupoids
  constructor
  · intro V U f x hx
    cases hx; cases V
    rename_i V0
    let X := x.unop
    let R := X.base
    let S := V0
    let g : R ⟶ S := f.unop
    let : Algebra R S := g.hom.toRingHom.toAlgebra
    let Y : FlatAlgebraCategory.{u, w} Λ k :=
      { base := S, fiber := S ⊗[R] X.fiber, flat := inferInstance }
    let m : FlatAlgebraCategory.Hom X Y :=
      { base := g, map := CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom),
        cartesian := (CommRingCat.isPushout_tensorProduct R S X.fiber).flip }
    refine ⟨Opposite.op Y, Opposite.op m, ?_⟩
    simpa [p, Y, S, m, g, FlatAlgebraCategory.projection] using
      (Functor.IsHomLift.map (p := p.op) (Opposite.op m))
  · intro x y z φ ψ f h
    let X := x.unop
    let Y := y.unop
    let Z := z.unop
    let phi0 : FlatAlgebraCategory.Hom X Y := φ.unop
    let psi0 : FlatAlgebraCategory.Hom X Z := ψ.unop
    let g : Y.base ⟶ Z.base := f.unop
    have hcomp : phi0.base ≫ g = psi0.base := by
      simpa [p, FlatAlgebraCategory.projection, phi0, psi0] using
        congrArg (fun q : p.op.obj z ⟶ p.op.obj x => q.unop) h
    have hbcomp : FlatAlgebraCategory.baseMap (phi0.base ≫ g) =
        FlatAlgebraCategory.baseMap phi0.base ≫ FlatAlgebraCategory.baseMap g := by
      ext a; rfl
    have hdesc : FlatAlgebraCategory.structureMap X ≫ psi0.map =
        FlatAlgebraCategory.baseMap phi0.base ≫ (FlatAlgebraCategory.baseMap g ≫
          FlatAlgebraCategory.structureMap Z) := by
      rw [psi0.cartesian.w, ← hcomp, hbcomp, Category.assoc]
    let d : CommRingCat.of Y.fiber ⟶ CommRingCat.of Z.fiber :=
      phi0.cartesian.desc _ _ hdesc
    have hmap : phi0.map ≫ d = psi0.map := phi0.cartesian.inl_desc _ _ hdesc
    have houter : IsPushout (FlatAlgebraCategory.structureMap X)
        (FlatAlgebraCategory.baseMap phi0.base ≫ FlatAlgebraCategory.baseMap g)
        (phi0.map ≫ d) (FlatAlgebraCategory.structureMap Z) := by
      rw [← hbcomp, hcomp, hmap]; exact psi0.cartesian
    let chi0 : FlatAlgebraCategory.Hom Y Z :=
      { base := g
        map := d
        cartesian := houter.of_top (phi0.cartesian.inr_desc _ _ hdesc) phi0.cartesian }
    have hchi : (FlatAlgebraCategory.instCategory (Λ := Λ) (k := k)).comp phi0 chi0 = psi0 := by
      refine FlatAlgebraCategory.Hom.ext hcomp ?_
      show phi0.map ≫ chi0.map = psi0.map
      simpa [chi0] using hmap
    refine ⟨Opposite.op chi0, ?_, ?_⟩
    · constructor
      · show Opposite.op (p.map chi0) = f; rfl
      · exact congrArg Opposite.op hchi
    · intro χ hχ
      have hb : (χ.unop).base = g := by
        simpa [p, FlatAlgebraCategory.projection] using
          congrArg (fun q : p.op.obj z ⟶ p.op.obj y => q.unop) hχ.1
      apply Opposite.unop_injective
      apply FlatAlgebraCategory.Hom.ext
      · exact hb
      · apply phi0.cartesian.hom_ext
        · have hm0 := congrArg (fun q : FlatAlgebraCategory.Hom X Z => q.map)
            (congrArg Quiver.Hom.unop hχ.2)
          change phi0.map ≫ χ.unop.map = psi0.map at hm0
          show phi0.map ≫ χ.unop.map = phi0.map ≫ chi0.map
          exact hm0.trans (by simpa [chi0] using hmap.symm)
        · show FlatAlgebraCategory.structureMap Y ≫ χ.unop.map =
            FlatAlgebraCategory.structureMap Y ≫ chi0.map
          rw [χ.unop.cartesian.w, chi0.cartesian.w, hb]

/-! ### The category of flat algebras

The ambient category of flat algebras over varying Artinian bases, its morphisms, its category
structure, its projection to `𝒞_Λ` and the object `(k, P)` of Stacks 0DY1. -/

add_to_stacks 0DY1 "flat_algebra_category" FlatAlgebraCategory
add_to_stacks 0DY1 "flat_algebra_category" FlatAlgebraCategory.Hom
add_to_stacks 0DY1 "flat_algebra_category" FlatAlgebraCategory.instCategory
add_to_stacks 0DY1 "flat_algebra_category" FlatAlgebraCategory.projection
add_to_stacks 0DY1 "flat_algebra_category" residueFieldAlgebra

end Deformation.Examples
