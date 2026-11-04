module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Coproduct
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.RingTheory.Smooth.Reduced

/-!
# The spectrum of a finite étale algebra as a smooth projective scheme

Let `k` be a field and `A` a finite étale `k`-algebra, that is, a finite product of finite
separable field extensions of `k` (Tag 03PC). Then `Spec(A)` is smooth over `k`, because `A` is
étale, and H-projective over `k`, because the structure morphism is finite over an affine base
(Tag 0B3I). This file
makes `Spec(A)` an object of the category of smooth projective schemes over `k`, functorially in
`A`, and shows conversely that every smooth projective scheme of dimension zero over `k` is of
this form: it is the spectrum of its ring of global sections, which is a finite étale
`k`-algebra.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.spec`: the smooth projective `k`-scheme
  `Spec(A)` of a finite étale `k`-algebra `A`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.specMap`: the morphism `Spec(B) ⟶ Spec(A)` of a
  `k`-algebra map `A → B`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.specFunctor`: the functor
  `(finite étale k-algebras)ᵒᵖ ⥤ (smooth projective k-schemes)`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.globalSections`: the `k`-algebra `Γ(X, 𝒪_X)`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isoSpecOfDimensionZero`: for `X` of dimension
  zero, the isomorphism `X ≅ Spec(Γ(X, 𝒪_X))` of smooth projective `k`-schemes.

## References

* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable (k : Type u) [Field k]

section Spec

variable (A : Type u) [CommRing A] [Algebra k A]

/-- The structure morphism `Spec(A) ⟶ Spec(k)` of a `k`-algebra. -/
abbrev specStructure : Spec (.of A) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

/-- The structure morphism `Spec(A) ⟶ Spec(k)` of a module-finite `k`-algebra is finite. -/
theorem isFinite_specStructure [Module.Finite k A] : IsFinite (specStructure k A) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The structure morphism `Spec(A) ⟶ Spec(k)` of an étale `k`-algebra is étale. -/
theorem etale_specStructure [Algebra.Etale k A] : Etale (specStructure k A) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)

variable [Module.Finite k A] [Algebra.Etale k A]

/-- **The spectrum of a finite étale `k`-algebra is a smooth projective `k`-scheme**: smooth since
the algebra is étale, H-projective since the structure morphism is finite over the affine scheme
`Spec(k)` (Tag 0B3I). -/
abbrev spec : (SmoothProjectiveScheme k).FullSubcategory :=
  haveI := isFinite_specStructure k A
  haveI := etale_specStructure k A
  ⟨Over.mk (specStructure k A), (inferInstance : Smooth (specStructure k A)),
    (Stacks.QuasiProjectiveCompactification.isProjectiveMorphism_of_isHProjective
      (Stacks.FiniteMorphismProjective.isHProjective_of_isFinite_of_isAffine
        (specStructure k A))).isProjective⟩

/-- The underlying scheme of `spec k A` is `Spec(A)`. -/
@[simp]
theorem spec_obj_left : (spec k A).obj.left = Spec (.of A) := rfl

/-- The structure morphism of `spec k A` is `Spec(A) ⟶ Spec(k)`. -/
@[simp]
theorem spec_obj_hom : (spec k A).obj.hom = specStructure k A := rfl

/-- The structure morphism of `spec k A` is finite. -/
instance : IsFinite (spec k A).obj.hom := isFinite_specStructure k A

/-- The structure morphism of `spec k A` is étale. -/
instance : Etale (spec k A).obj.hom := etale_specStructure k A

variable {k A} {B C : Type u} [CommRing B] [Algebra k B] [Module.Finite k B] [Algebra.Etale k B]
  [CommRing C] [Algebra k C] [Module.Finite k C] [Algebra.Etale k C]

/-- The morphism `Spec(B) ⟶ Spec(A)` of smooth projective `k`-schemes induced by a `k`-algebra
map `φ : A → B`. -/
def specMap (φ : A →ₐ[k] B) : spec k B ⟶ spec k A :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact φ.commutes a))

/-- The morphism of schemes underlying `specMap φ` is `Spec.map φ`. -/
@[simp]
theorem specMap_hom_left (φ : A →ₐ[k] B) :
    (specMap φ).hom.left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

/-- `specMap` sends the identity of `A` to the identity of `spec k A`. -/
@[simp]
theorem specMap_id : specMap (AlgHom.id k A) = 𝟙 (spec k A) :=
  hom_ext_left (Spec.map_id _)

/-- `specMap` sends a composite `ψ ∘ φ` to `specMap ψ ≫ specMap φ`. -/
@[simp]
theorem specMap_comp (φ : A →ₐ[k] B) (ψ : B →ₐ[k] C) :
    specMap (ψ.comp φ) = specMap ψ ≫ specMap φ :=
  hom_ext_left (by
    show Spec.map (CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom ψ.toRingHom) = _
    rw [Spec.map_comp]
    rfl)

end Spec

/-- The functor `Spec` from finite étale `k`-algebras to smooth projective `k`-schemes. -/
def specFunctor : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤
    (SmoothProjectiveScheme k).FullSubcategory where
  obj A := spec k A.unop
  map φ := specMap φ.unop.hom.hom
  map_id _ := specMap_id
  map_comp φ ψ := specMap_comp ψ.unop.hom.hom φ.unop.hom.hom

/-! ### Smooth projective schemes of dimension zero -/

/-- A finite smooth algebra over a field is étale: after the faithfully flat base change to an
algebraic closure it is reduced and Artinian, hence a finite product of copies of the algebraic
closure, which is étale; and étaleness descends. -/
theorem etale_of_finite_of_smooth (A : Type u) [CommRing A] [Algebra k A] [Module.Finite k A]
    [Algebra.Smooth k A] : Algebra.Etale k A := by
  let K := AlgebraicClosure k
  have : IsReduced (K ⊗[k] A) := Algebra.isReduced_of_smooth K _
  have : IsArtinianRing (K ⊗[k] A) := IsArtinianRing.of_finite K (K ⊗[k] A)
  let eField (m : MaximalSpectrum (K ⊗[k] A)) : K ≃ₐ[K] ((K ⊗[k] A) ⧸ m.asIdeal) :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom K K _)
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))
  let e : (K ⊗[k] A) ≃ₐ[K] (MaximalSpectrum (K ⊗[k] A) → K) :=
    ((IsArtinianRing.equivPi (K ⊗[k] A)).restrictScalars K).trans
      (AlgEquiv.piCongrRight fun m => (eField m).symm)
  have : Algebra.Etale K (K ⊗[k] A) := Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat K

section DimensionZero

variable {k} (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- The ring `Γ(X, 𝒪_X)` of global sections of a smooth projective `k`-scheme. -/
abbrev globalSections : Type u := Γ(X.obj.left, ⊤)

/-- `Γ(X, 𝒪_X)` is a `k`-algebra through the structure morphism. -/
instance algebraGlobalSections : Algebra k (globalSections X) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.obj.hom.appTop).hom.toAlgebra

/-- The `k`-algebra structure on the global sections `Γ(Spec(A), 𝒪)` of `spec k A`. -/
instance algebraGlobalSectionsSpec (A : Type u) [CommRing A] [Algebra k A] [Module.Finite k A]
    [Algebra.Etale k A] : Algebra k (globalSections (spec k A)) :=
  algebraGlobalSections (spec k A)

/-- The algebra map `k → Γ(X, 𝒪_X)` is the map on global sections of the structure morphism,
precomposed with `k ≅ Γ(Spec(k), 𝒪)`. -/
theorem algebraMap_globalSections :
    algebraMap k (globalSections X) = ((Scheme.ΓSpecIso (.of k)).inv ≫ X.obj.hom.appTop).hom :=
  rfl

variable {X} (hX : topologicalKrullDim X.obj.left = 0)

include hX

/-- The structure morphism of a smooth projective `k`-scheme of dimension zero is finite
(Tag 06LH). -/
theorem isFinite_of_dimension_zero : IsFinite X.obj.hom :=
  AlgebraicGeometry.isFinite_of_finiteType_of_dimension_zero k X.obj.hom hX

/-- A smooth projective `k`-scheme of dimension zero is affine (Tag 06LH). -/
theorem isAffine_of_dimension_zero : IsAffine X.obj.left := by
  have := isFinite_of_dimension_zero hX
  exact isAffine_of_isAffineHom X.obj.hom

/-- `Γ(X, 𝒪_X)` is a finite `k`-algebra when `X` has dimension zero. -/
theorem finite_globalSections : Module.Finite k (globalSections X) := by
  have := isFinite_of_dimension_zero hX
  refine RingHom.finite_algebraMap.mp ?_
  rw [algebraMap_globalSections]
  exact RingHom.Finite.comp X.obj.hom.finite_appTop
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.finite

/-- `Γ(X, 𝒪_X)` is a smooth `k`-algebra when `X` has dimension zero. -/
theorem smooth_globalSections : Algebra.Smooth k (globalSections X) := by
  have := isAffine_of_dimension_zero hX
  have hmap : X.obj.hom.appTop.hom.Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp inferInstance
  refine RingHom.smooth_algebraMap.mp ?_
  rw [algebraMap_globalSections]
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.bijective) hmap

/-- `Γ(X, 𝒪_X)` is an étale `k`-algebra when `X` has dimension zero. -/
theorem etale_globalSections : Algebra.Etale k (globalSections X) :=
  have := finite_globalSections hX
  have := smooth_globalSections hX
  etale_of_finite_of_smooth k (globalSections X)

/-- The isomorphism of schemes `X ≅ Spec(Γ(X, 𝒪_X))` for `X` of dimension zero. -/
def isoSpecLeftOfDimensionZero : X.obj.left ≅ Spec (.of (globalSections X)) :=
  haveI : IsAffine X.obj.left := isAffine_of_dimension_zero hX
  X.obj.left.isoSpec

/-- `X ≅ Spec(Γ(X, 𝒪_X))` is an isomorphism over `Spec(k)`. -/
@[reassoc (attr := simp)]
theorem isoSpecLeftOfDimensionZero_hom_specStructure :
    (isoSpecLeftOfDimensionZero hX).hom ≫ specStructure k (globalSections X) = X.obj.hom := by
  show X.obj.left.toSpecΓ ≫ Spec.map
    ((Scheme.ΓSpecIso (.of k)).inv ≫ X.obj.hom.appTop) = X.obj.hom
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc X.obj.hom,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The structure morphism of `Spec(Γ(X, 𝒪_X))` is the inverse of `X ≅ Spec(Γ(X, 𝒪_X))` followed
by the structure morphism of `X`. -/
@[reassoc (attr := simp)]
theorem isoSpecLeftOfDimensionZero_inv_hom :
    specStructure k (globalSections X) = (isoSpecLeftOfDimensionZero hX).inv ≫ X.obj.hom := by
  rw [Iso.eq_inv_comp, isoSpecLeftOfDimensionZero_hom_specStructure]

/-- **A smooth projective `k`-scheme of dimension zero is the spectrum of its finite étale
`k`-algebra of global sections** (Tags 06LH and 03PC). -/
def isoSpecOfDimensionZero :
    haveI := finite_globalSections hX
    haveI := etale_globalSections hX
    X ≅ spec k (globalSections X) :=
  haveI := finite_globalSections hX
  haveI := etale_globalSections hX
  (SmoothProjectiveScheme k).isoMk (Over.isoMk (isoSpecLeftOfDimensionZero hX)
    (isoSpecLeftOfDimensionZero_hom_specStructure hX))

/-- The morphism of schemes underlying the hom of `isoSpecOfDimensionZero hX` is that of
`isoSpecLeftOfDimensionZero hX`. -/
@[simp]
theorem isoSpecOfDimensionZero_hom_hom_left :
    haveI := finite_globalSections hX
    haveI := etale_globalSections hX
    (isoSpecOfDimensionZero hX).hom.hom.left = (isoSpecLeftOfDimensionZero hX).hom := rfl

/-- The morphism of schemes underlying the inverse of `isoSpecOfDimensionZero hX` is that of
`isoSpecLeftOfDimensionZero hX`. -/
@[simp]
theorem isoSpecOfDimensionZero_inv_hom_left :
    haveI := finite_globalSections hX
    haveI := etale_globalSections hX
    (isoSpecOfDimensionZero hX).inv.hom.left = (isoSpecLeftOfDimensionZero hX).inv := rfl

end DimensionZero

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
