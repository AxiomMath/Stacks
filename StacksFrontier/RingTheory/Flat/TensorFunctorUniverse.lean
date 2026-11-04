module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksFrontier.RingTheory.Flat.LinearFunctorFlatComparison

/-!
# Tensoring across universes, and the flat comparison for a functor raising the universe

Let `A` be a commutative ring and let `Φ : ModuleCat.{uA} A ⥤ ModuleCat.{max uA w} A` be an
additive `A`-linear functor which preserves filtered colimits.  There is a canonical map

`Φ(A) ⊗_A M ⟶ Φ(M)`,

natural in `M`, sending `x ⊗ m` to `Φ(a ↦ a • m)(x)`, and it is an isomorphism whenever `M` is
**flat** over `A`.

This is the content of `StacksFrontier.RingTheory.Flat.LinearFunctorFlatComparison` with the
restriction to a single module universe removed.  That file uses Mathlib's monoidal structure on
`ModuleCat.{u} A`, which exists only when the module universe is the universe of `A`; the
application in **Stacks 073K, part (2)** has `A : Type u` but a target one universe up, because
the cohomology of a sheaf whose sections lie in `Type u` lands in `Type (u + 1)`.

## Main definitions

* `Stacks.FlatDevissage.tensorLeftFunctor`: tensoring on the left with a fixed `A`-module `P` in
  `Type w`, as a functor `ModuleCat.{v} A ⥤ ModuleCat.{max v w} A`.
* `Stacks.FlatDevissage.internalHomFunctor`: the internal hom `N ↦ (P →ₗ[A] N)` of `A`-modules in
  a single universe.
* `Stacks.FlatDevissage.tensorLeftAdjunction`: tensoring with `P` is left adjoint to the internal
  hom out of `P`, when the module universe is the universe of `P`.
* `Stacks.FlatDevissage.tensorComparisonUniv`: **the canonical map** `Φ(A) ⊗_A - ⟶ Φ`.

## Main results

* `Stacks.FlatDevissage.tensorComparisonUnivApp_tmul`: the defining formula
  `x ⊗ m ↦ Φ(spanHom m)(x)`, which pins the map down.
* `Stacks.FlatDevissage.tensorComparisonUniv_app_unit`: at `M = A` the map is the right unitor,
  hence invertible.
* `Stacks.FlatDevissage.isIso_tensorComparisonUniv_app_of_flat`: **the comparison is invertible
  at every flat module.**
* `Stacks.FlatDevissage.isIso_tensorComparisonUniv_app_of_flat_succ`: the same, specialised to a
  target one universe above the ring, which is the shape Stacks 073K part (2) uses.

## Implementation notes

The only delicate point is that `tensorLeftFunctor` preserves colimits, which the dévissage of
`Stacks.FlatDevissage.isIso_app_of_flat` needs: there is no adjoint to tensoring in this
generality, since for `M` in `Type v` and `N` in `Type (max v w)` the module `P →ₗ[A] N` lies in
`Type (max v w)` and cannot be an object of the source category.  Instead the functor is
factored as a universe lift followed by tensoring inside the single universe `max v w`
(`Stacks.FlatDevissage.tensorLeftFunctorUliftIso`): the second factor is a left adjoint
(`Stacks.FlatDevissage.tensorLeftAdjunction`), and the first preserves colimits because colimits
in `ModuleCat` are reflected by the forgetful functor to abelian groups, where
`AddCommGrpCat.uliftFunctor` is already known to preserve colimits of arbitrary size.

At the free module of rank one the comparison is built from `TensorProduct.rid` rather than from
a monoidal unitor, again because `ModuleCat.{max uA w} A` carries no monoidal structure.

The target of the functor `Φ` is written `ModuleCat.{max uA w} A`, so a functor whose target is
stated in another form, such as `ModuleCat.{uA + 1} A`, has to be fed explicit universe
arguments: Lean cannot solve `max uA ?w = uA + 1` for `?w`.

As in `StacksFrontier.RingTheory.Flat.LinearFunctorFlatComparison`, `A`-linearity of `Φ` — and not
merely additivity — is what makes the formula `x ⊗ m ↦ Φ(spanHom m)(x)` well defined on the
tensor product, through `spanHom (a • m) = a • spanHom m`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

namespace Stacks.FlatDevissage

universe uA w v j j'

variable {A : Type uA} [CommRing A]

/-- **Tensoring on the left with a fixed module, across universes.**  For `P` an `A`-module in
`Type w` this is the functor `M ↦ P ⊗[A] M` from `A`-modules in `Type v` to `A`-modules in
`Type (max v w)`, which is where the tensor product lives. -/
def tensorLeftFunctor (P : ModuleCat.{w} A) : ModuleCat.{v} A ⥤ ModuleCat.{max v w} A where
  obj M := ModuleCat.of A (P ⊗[A] M)
  map u := ModuleCat.ofHom (LinearMap.lTensor P u.hom)
  map_id M := by
    refine ModuleCat.hom_ext (TensorProduct.ext' fun x m ↦ ?_)
    simp
  map_comp u u' := by
    refine ModuleCat.hom_ext (TensorProduct.ext' fun x m ↦ ?_)
    simp

/-- The functor `tensorLeftFunctor P` sends `u : M ⟶ N` to the map `x ⊗ m ↦ x ⊗ u m`. -/
@[simp]
theorem tensorLeftFunctor_map_tmul (P : ModuleCat.{w} A) {M N : ModuleCat.{v} A} (u : M ⟶ N)
    (x : P) (m : M) :
    ((tensorLeftFunctor P).map u).hom (x ⊗ₜ[A] m) = x ⊗ₜ[A] u.hom m :=
  rfl

/-- Tensoring on the left is an additive functor. -/
instance tensorLeftFunctor_additive (P : ModuleCat.{w} A) :
    (tensorLeftFunctor.{uA, w, v} P).Additive where
  map_add {_ _ u u'} := ModuleCat.hom_ext (LinearMap.lTensor_add P u.hom u'.hom)

/-- Tensoring on the left is an `A`-linear functor. -/
instance tensorLeftFunctor_linear (P : ModuleCat.{w} A) :
    Functor.Linear A (tensorLeftFunctor.{uA, w, v} P) where
  map_smul {_ _ u a} := ModuleCat.hom_ext (LinearMap.lTensor_smul P a u.hom)

/-- **The internal hom of `A`-modules in a single universe.**  If `P` and `N` are `A`-modules in
`Type v` then so is `P →ₗ[A] N`; this is the functor `N ↦ (P →ₗ[A] N)`, which is right adjoint to
tensoring with `P`. -/
def internalHomFunctor (P : ModuleCat.{v} A) : ModuleCat.{v} A ⥤ ModuleCat.{v} A where
  obj N := ModuleCat.of A (P →ₗ[A] N)
  map u := ModuleCat.ofHom
    { toFun := fun f ↦ u.hom ∘ₗ f
      map_add' := fun f g ↦ by ext x; simp
      map_smul' := fun a f ↦ by ext x; simp }
  map_id N := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)
  map_comp u u' := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- **Tensoring with `P` is left adjoint to the internal hom out of `P`**, when the module
universe is the universe of `P`.  The hom equivalence is the universal property of the tensor
product, `TensorProduct.lift` and `TensorProduct.curry`. -/
def tensorLeftAdjunction (P : ModuleCat.{v} A) :
    tensorLeftFunctor.{uA, v, v} P ⊣ internalHomFunctor P :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦
        { toFun := fun f ↦ ModuleCat.ofHom (TensorProduct.curry f.hom).flip
          invFun := fun g ↦ ModuleCat.ofHom (TensorProduct.lift g.hom.flip)
          left_inv := fun _ ↦ ModuleCat.hom_ext (TensorProduct.ext' fun _ _ ↦ rfl)
          right_inv := fun _ ↦
            ModuleCat.hom_ext (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl) }
      homEquiv_naturality_left_symm := fun _ _ ↦
        ModuleCat.hom_ext (TensorProduct.ext' fun _ _ ↦ rfl)
      homEquiv_naturality_right := fun _ _ ↦
        ModuleCat.hom_ext (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl) }

/-- **Tensoring with a module in the ambient module universe preserves all colimits**, being a
left adjoint. -/
theorem preservesColimitsOfSize_tensorLeftFunctor_self (P : ModuleCat.{v} A) :
    PreservesColimitsOfSize.{j, j'} (tensorLeftFunctor.{uA, v, v} P) :=
  (tensorLeftAdjunction P).leftAdjoint_preservesColimits

/-- **The universe-lift functor on `ModuleCat` preserves colimits of size `v`.**  Colimits in
`ModuleCat` are reflected by the forgetful functor to abelian groups, and the universe lift of
abelian groups preserves colimits of arbitrary size. -/
theorem preservesColimitsOfSize_moduleCat_uliftFunctor :
    PreservesColimitsOfSize.{v, v} (ModuleCat.uliftFunctor.{w, v} A) where
  preservesColimitsOfShape {J _} := by
    have : PreservesColimitsOfShape J
        (ModuleCat.uliftFunctor.{w, v} A ⋙ forget₂ (ModuleCat.{max v w} A) AddCommGrpCat) := by
      show PreservesColimitsOfShape J
        (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{w, v})
      infer_instance
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (forget₂ _ AddCommGrpCat)

/-- **Tensoring across universes is a universe lift followed by tensoring inside one universe.** -/
def tensorLeftFunctorUliftIso (P : ModuleCat.{w} A) :
    tensorLeftFunctor.{uA, w, v} P ≅
      ModuleCat.uliftFunctor.{w, v} A ⋙
        tensorLeftFunctor.{uA, max v w, max v w} (ModuleCat.of A (ULift.{v, w} P)) :=
  NatIso.ofComponents
    (fun _ ↦ (TensorProduct.congr ULift.moduleEquiv.symm ULift.moduleEquiv.symm).toModuleIso)
    fun _ ↦ ModuleCat.hom_ext (TensorProduct.ext' fun _ _ ↦ rfl)

/-- **Tensoring on the left with a fixed module preserves all colimits of size `v`**, where `v` is
the module universe of its source.  In particular, it preserves filtered colimits of that size. -/
instance preservesColimitsOfSize_tensorLeftFunctor (P : ModuleCat.{w} A) :
    PreservesColimitsOfSize.{v, v} (tensorLeftFunctor.{uA, w, v} P) := by
  have : PreservesColimitsOfSize.{v, v} (ModuleCat.uliftFunctor.{w, v} A) :=
    preservesColimitsOfSize_moduleCat_uliftFunctor
  have : PreservesColimitsOfSize.{v, v}
      (tensorLeftFunctor.{uA, max v w, max v w} (ModuleCat.of A (ULift.{v, w} P))) :=
    preservesColimitsOfSize_tensorLeftFunctor_self _
  exact preservesColimits_of_natIso (tensorLeftFunctorUliftIso P).symm

variable (Φ : ModuleCat.{uA} A ⥤ ModuleCat.{max uA w} A) [Φ.Additive] [Functor.Linear A Φ]

/-- The `A`-linear map `M →ₗ[A] (Φ(A) →ₗ[A] Φ(M))` sending `m` to `Φ(spanHom m)`.  Additivity and
homogeneity in `m` come from `Stacks.FlatDevissage.spanHom_add` and
`Stacks.FlatDevissage.spanHom_smul` together with the `A`-linearity of `Φ`. -/
def tensorComparisonUnivMap (M : ModuleCat.{uA} A) :
    M →ₗ[A] (Φ.obj (unitModule A) →ₗ[A] Φ.obj M) where
  toFun m := (Φ.map (spanHom m)).hom
  map_add' m n := by rw [spanHom_add, Φ.map_add, ModuleCat.hom_add]
  map_smul' a m := by rw [spanHom_smul, Φ.map_smul, ModuleCat.hom_smul, RingHom.id_apply]

/-- **The canonical map `Φ(A) ⊗_A M ⟶ Φ(M)` across universes**, the component of
`Stacks.FlatDevissage.tensorComparisonUniv` at `M`.  It sends `x ⊗ m` to `Φ(spanHom m)(x)`. -/
def tensorComparisonUnivApp (M : ModuleCat.{uA} A) :
    (tensorLeftFunctor (Φ.obj (unitModule A))).obj M ⟶ Φ.obj M :=
  ModuleCat.ofHom (TensorProduct.lift (tensorComparisonUnivMap Φ M).flip)

/-- The map `tensorComparisonUnivApp Φ M` sends `x ⊗ m` to `Φ(spanHom m)(x)`. -/
@[simp]
theorem tensorComparisonUnivApp_tmul (M : ModuleCat.{uA} A) (x : Φ.obj (unitModule A)) (m : M) :
    (tensorComparisonUnivApp Φ M).hom (x ⊗ₜ[A] m) = (Φ.map (spanHom m)).hom x :=
  rfl

/-- **The canonical map `Φ(A) ⊗_A - ⟶ Φ` across universes**, as a natural transformation out of
`Stacks.FlatDevissage.tensorLeftFunctor`.  Naturality is the identity
`spanHom m ≫ u = spanHom (u m)`. -/
def tensorComparisonUniv : tensorLeftFunctor (Φ.obj (unitModule A)) ⟶ Φ where
  app := tensorComparisonUnivApp Φ
  naturality M N u := by
    refine ModuleCat.hom_ext (TensorProduct.ext' fun x m ↦ ?_)
    change (Φ.map (spanHom (u.hom m))).hom x = (Φ.map u).hom ((Φ.map (spanHom m)).hom x)
    rw [← spanHom_comp, Φ.map_comp]
    rfl

/-- The component of `tensorComparisonUniv Φ` at `M` is `tensorComparisonUnivApp Φ M`. -/
@[simp]
theorem tensorComparisonUniv_app (M : ModuleCat.{uA} A) :
    (tensorComparisonUniv Φ).app M = tensorComparisonUnivApp Φ M :=
  rfl

/-- **The right unitor `Φ(A) ⊗_A A ≅ Φ(A)`**, read in `ModuleCat`.  The monoidal unitor is not
available here, because `ModuleCat.{max uA w} A` carries no monoidal structure unless the module
universe agrees with the universe of `A`; the underlying linear equivalence
`TensorProduct.rid` is used instead. -/
def tensorComparisonUnivUnitIso :
    (tensorLeftFunctor (Φ.obj (unitModule A))).obj (unitModule A) ≅ Φ.obj (unitModule A) :=
  (TensorProduct.rid A (Φ.obj (unitModule A))).toModuleIso

/-- **At the free module of rank one the comparison is the right unitor.**  Indeed
`spanHom a = a • 𝟙`, and an `A`-linear functor sends that to `a • 𝟙`, so the formula
`x ⊗ a ↦ Φ(spanHom a)(x)` reads `x ⊗ a ↦ a • x`. -/
theorem tensorComparisonUniv_app_unit :
    (tensorComparisonUniv Φ).app (unitModule A) = (tensorComparisonUnivUnitIso Φ).hom := by
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x a ↦ ?_)
  show (Φ.map (spanHom (M := unitModule A) a)).hom x
      = TensorProduct.rid A (Φ.obj (unitModule A)) (x ⊗ₜ[A] a)
  rw [spanHom_unit, Φ.map_smul, Φ.map_id, TensorProduct.rid_tmul]
  simp

/-- The comparison is invertible at the free module of rank one. -/
instance isIso_tensorComparisonUniv_app_unit :
    IsIso ((tensorComparisonUniv Φ).app (unitModule A)) := by
  rw [tensorComparisonUniv_app_unit]
  infer_instance

/-- **The canonical map `Φ(A) ⊗_A M ⟶ Φ(M)` is invertible for every flat `M`**, for a functor
`Φ` whose target module universe need not be the universe of `A`.

This is the dévissage of `Stacks.FlatDevissage.isIso_app_of_flat'`: both functors are additive
and preserve filtered colimits of size `uA` — `tensorLeftFunctor` by the instance above — and the
comparison is invertible at the free module of rank one. -/
theorem isIso_tensorComparisonUniv_app_of_flat
    [PreservesFilteredColimitsOfSize.{uA, uA} Φ] (M : ModuleCat.{uA} A) [Module.Flat A M] :
    IsIso ((tensorComparisonUniv Φ).app M) :=
  isIso_app_of_flat' (tensorComparisonUniv Φ) (isIso_tensorComparisonUniv_app_unit Φ) M

/-- **The same, for a flat module given as a type.** -/
theorem isIso_tensorComparisonUniv_app_of_flat'
    [PreservesFilteredColimitsOfSize.{uA, uA} Φ] (M : Type uA) [AddCommGroup M] [Module A M]
    [Module.Flat A M] : IsIso ((tensorComparisonUniv Φ).app (ModuleCat.of A M)) :=
  isIso_tensorComparisonUniv_app_of_flat Φ (ModuleCat.of A M)

/-- **The comparison is invertible at every flat module, for a functor landing one universe up.**

This is the shape in which **Stacks 073K, part (2)** uses the comparison: the ring lies in
`Type uA`, and the cohomology of a sheaf of modules whose sections lie in `Type uA` lies in
`Type (uA + 1)`.  The universe arguments have to be supplied explicitly, here and at any other
use of `Stacks.FlatDevissage.tensorComparisonUniv` whose target universe is not literally of the
form `max uA w`, because Lean cannot solve the constraint `max uA ?w = uA + 1` for `?w`. -/
theorem isIso_tensorComparisonUniv_app_of_flat_succ
    (Ψ : ModuleCat.{uA} A ⥤ ModuleCat.{uA + 1} A) [Ψ.Additive] [Functor.Linear A Ψ]
    [PreservesFilteredColimitsOfSize.{uA, uA} Ψ] (M : ModuleCat.{uA} A) [Module.Flat A M] :
    IsIso ((tensorComparisonUniv.{uA, uA + 1} Ψ).app M) :=
  isIso_tensorComparisonUniv_app_of_flat.{uA, uA + 1} Ψ M

end Stacks.FlatDevissage

end
