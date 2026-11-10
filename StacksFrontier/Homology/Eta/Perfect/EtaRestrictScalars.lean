module

public import StacksFrontier.Homology.Eta.Perfect.BoundedComplexExtendScalars
public import StacksFrontier.Homology.Eta.Perfect.GoodBaseChangeFlat

/-!
# The décalage transported along an isomorphism of coefficient rings

Let `A → B` be a map of commutative rings which is *bijective* — the situation of a ring
isomorphism, written as an algebra structure so that the base-change vocabulary of
`StacksFrontier.Homology.Eta.Perfect.GoodBaseChange` applies — let `f ∈ A` with image
`g = algebraMap A B f`, and let `K` be a cochain complex of `A`-modules.  Then

`η_g (B ⊗_A K)`, read as a complex of `A`-modules by restriction of scalars, is `η_f K`.

This is the transport of the Berthelot--Ogus décalage along an isomorphism of coefficient
rings.  It is what lets a statement about `η_f` over one ring be read over an isomorphic ring:
the comparison of décalages on an affine scheme is proved over the ring of global functions
`Γ(Spec A, ⊤)`, while the complex and the equation of the divisor of an affine chart of
Situation 0F8S live over `A` itself.

## Main definitions

* `Stacks.Eta.RestrictScalars.tensorEquiv`: `B ⊗_A P ≅ P` as `A`-modules, for `A → B`
  bijective.
* `Stacks.Eta.RestrictScalars.baseChangeComplexRestrictIso`: `B ⊗_A K`, read back over `A`, is
  `K`.
* `Stacks.Eta.RestrictScalars.etaObjectRestrictIso`: **the transport of the décalage**,
  `η_g (B ⊗_A K)` read over `A` is `η_f K`.

## Implementation notes

The two inputs are `Stacks.Eta.GoodBaseChange.isIso_etaBaseChangeMap_of_flat` — Tag 0GSR as an
isomorphism of complexes, applicable because a bijective algebra map makes `B` a flat
`A`-module, being `A` itself up to an `A`-linear equivalence — and the identification
`B ⊗_A P ≅ P`, which is `TensorProduct.lid` composed with the `A`-linear equivalence `B ≅ A`.

Restriction of scalars equips the carrier of a `B`-module with the `A`-action
`a • x = algebraMap A B a • x` (`Module.compHom`), which is not the ambient `A`-action on a
tensor product even though `algebraMap_smul` says the two agree.  The `A`-linear maps below are
therefore written out, with `map_smul'` discharged by `algebraMap_smul`, rather than obtained
from `LinearEquiv.toModuleIso`.

## References

* [Stacks Project, Tag 0GSR](https://stacks.math.columbia.edu/tag/0GSR)
-/

@[expose] public noncomputable section

open CategoryTheory EtaPow Stacks.Eta.GoodBaseChange

open scoped TensorProduct

universe u

namespace Stacks.Eta.RestrictScalars

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (hbij : Function.Bijective (algebraMap A B))

/-- A bijective structure map identifies `B` with `A` as an `A`-module. -/
def selfEquiv : B ≃ₗ[A] A :=
  (LinearEquiv.ofBijective (Algebra.linearMap A B) hbij).symm

/-- The structure map sends `selfEquiv hbij b` back to `b`. -/
@[simp]
theorem algebraMap_selfEquiv (b : B) : algebraMap A B (selfEquiv hbij b) = b :=
  (LinearEquiv.ofBijective (Algebra.linearMap A B) hbij).apply_symm_apply b

include hbij in
/-- `B` is a flat `A`-module when the structure map is bijective: it is `A` itself up to an
`A`-linear equivalence. -/
theorem flat_of_bijective : Module.Flat A B :=
  Module.Flat.of_linearEquiv (selfEquiv hbij)

/-- **`B ⊗_A P ≅ P` for a bijective structure map**, as `A`-modules: identify `B` with `A` and
then cancel the tensor factor. -/
def tensorEquiv (P : Type u) [AddCommGroup P] [Module A P] : (B ⊗[A] P) ≃ₗ[A] P :=
  (TensorProduct.congr (selfEquiv hbij) (LinearEquiv.refl A P)).trans (TensorProduct.lid A P)

/-- The identification `B ⊗_A P ≅ P` sends `b ⊗ p` to `selfEquiv hbij b • p`. -/
@[simp]
theorem tensorEquiv_tmul (P : Type u) [AddCommGroup P] [Module A P] (b : B) (p : P) :
    tensorEquiv hbij P (b ⊗ₜ[A] p) = selfEquiv hbij b • p := by
  simp [tensorEquiv]

/-- The identification `B ⊗_A P ≅ P` turns multiplication by the image of `a ∈ A` into
multiplication by `a`.  This is the `map_smul` field of the morphism out of the restriction of
scalars below, where the `A`-action is `a • x = algebraMap A B a • x` by definition. -/
theorem tensorEquiv_algebraMap_smul (P : Type u) [AddCommGroup P] [Module A P] (a : A)
    (x : B ⊗[A] P) :
    tensorEquiv hbij P (algebraMap A B a • x) = a • tensorEquiv hbij P x := by
  rw [algebraMap_smul, map_smul]

/-- `B ⊗_A P`, read as an `A`-module by restriction of scalars along the bijective structure
map, is `P`. -/
def tensorRestrictHom (P : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (B ⊗[A] (P : Type u))) ⟶ P :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (B ⊗[A] (P : Type u))))
    { toFun := fun x => tensorEquiv hbij (P : Type u) x
      map_add' := fun x y => map_add (tensorEquiv hbij (P : Type u)) x y
      map_smul' := fun a x => tensorEquiv_algebraMap_smul hbij (P : Type u) a x }

/-- The morphism `tensorRestrictHom hbij P` acts on elements as `tensorEquiv hbij P`. -/
@[simp]
theorem tensorRestrictHom_apply (P : ModuleCat.{u} A) (x : B ⊗[A] (P : Type u)) :
    (tensorRestrictHom hbij P).hom x = tensorEquiv hbij (P : Type u) x :=
  rfl

/-- The morphism `tensorRestrictHom hbij P` is an isomorphism. -/
theorem isIso_tensorRestrictHom (P : ModuleCat.{u} A) : IsIso (tensorRestrictHom hbij P) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (tensorEquiv hbij (P : Type u)).bijective

/-- `B ⊗_A P`, read as an `A`-module by restriction of scalars along the bijective structure
map, is isomorphic to `P`. -/
def tensorRestrictIso (P : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (B ⊗[A] (P : Type u))) ≅ P :=
  @asIso _ _ _ _ _ (isIso_tensorRestrictHom hbij P)

/-- **The base change of a complex along a bijective structure map, read back over `A`, is the
complex itself.** -/
def baseChangeComplexRestrictIso (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (baseChangeComplex (B := B) K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => tensorRestrictIso hbij (K.X i))
    fun i j _ => by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      change (K.d i j).hom (tensorEquiv hbij (K.X i : Type u) x) =
        tensorEquiv hbij (K.X j : Type u) (LinearMap.baseChange B (K.d i j).hom x)
      induction x using TensorProduct.inductionOn with
      | tmul b p => simp
      | add x y hx hy => simp only [map_add, hx, hy]

/-- **The décalage transported along an isomorphism of coefficient rings.**  Let `A → B` be a
bijective map of commutative rings, let `f ∈ A` with image `g = algebraMap A B f`, and let `K`
be a cochain complex of `A`-modules.  Then the décalage `η_g (B ⊗_A K)` of the base-changed
complex, read as a complex of `A`-modules by restriction of scalars, is the décalage `η_f K`.

The comparison `B ⊗_A (η_f K) ⟶ η_g (B ⊗_A K)` is an isomorphism by Tag 0GSR
(`Stacks.Eta.GoodBaseChange.isIso_etaBaseChangeMap_of_flat`), a bijective structure map being
flat, and `B ⊗_A (η_f K)` read back over `A` is `η_f K` by
`Stacks.Eta.RestrictScalars.baseChangeComplexRestrictIso`. -/
def etaObjectRestrictIso (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (EtaComplex.etaObject (algebraMap A B f) (baseChangeComplex (B := B) K)) ≅
      EtaComplex.etaObject f K :=
  ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso
      (@asIso _ _ _ _ _ (@isIso_etaBaseChangeMap_of_flat A B _ _ _ f
        (flat_of_bijective hbij) K)).symm ≪≫
    baseChangeComplexRestrictIso hbij (EtaComplex.etaObject f K)

/-- The base change of the cochain complex of a bounded complex of finite free modules given in
chosen bases is the cochain complex of the base-changed bounded complex: the canonical
identification of `B ⊗_A (ι → A)` with `ι → B` intertwines multiplication by a matrix with
multiplication by the matrix of images.

This is `BoundedComplex.extendScalarsIso` at the ambient algebra structure, in the spelling
`Stacks.Eta.GoodBaseChange.baseChangeComplex` of base change that the décalage comparison uses
rather than `ModuleCat.extendScalars`. -/
def baseChangeComplexToCochainIso (C : BoundedComplex A) :
    baseChangeComplex (B := B) C.toCochainComplex ≅
      (C.baseChange (algebraMap A B)).toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.piScalarRight A B B (Fin (C.rank i))).toModuleIso)
    fun i j hij => by
      obtain rfl : i + 1 = j := hij
      simp only [baseChangeComplex_d, BoundedComplex.toCochainComplex_d,
        LinearEquiv.toModuleIso_hom]
      exact ModuleCat.hom_ext (piScalarRight_mulVec (C.d i)).symm

/-- **A bounded complex of finite free modules base-changed along a bijective structure map,
read back over `A`, is the complex itself.** -/
def boundedComplexRestrictIso (C : BoundedComplex A) :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (C.baseChange (algebraMap A B)).toCochainComplex ≅
      C.toCochainComplex :=
  ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (baseChangeComplexToCochainIso C).symm ≪≫
    baseChangeComplexRestrictIso hbij C.toCochainComplex

/-- **The décalage of a bounded complex of finite free modules, transported along an
isomorphism of coefficient rings.**  Let `A → B` be a bijective map of commutative rings, let
`f ∈ A` with image `g = algebraMap A B f`, and let `M^•` be a bounded complex of finite free
`A`-modules in chosen bases.  Then the décalage `η_g (M^• ⊗_A B)` of the base-changed complex,
read as a complex of `A`-modules by restriction of scalars, is the décalage `η_f M^•`. -/
def etaObjectBoundedComplexRestrictIso (f : A) (C : BoundedComplex A) :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (EtaComplex.etaObject (algebraMap A B f)
          (C.baseChange (algebraMap A B)).toCochainComplex) ≅
      EtaComplex.etaObject f C.toCochainComplex :=
  ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso
      (EtaComplex.etaObjectIso (algebraMap A B f)
        (baseChangeComplexToCochainIso C).symm) ≪≫
    etaObjectRestrictIso hbij f C.toCochainComplex

end Stacks.Eta.RestrictScalars

end
