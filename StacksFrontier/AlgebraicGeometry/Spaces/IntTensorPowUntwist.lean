module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionIntTensorPowers

/-!
# Untwisting by an invertible module on the small étale site of an algebraic space

Let `X` be an algebraic space and `L` an invertible `𝒪_X`-module on its small étale site, with
integer tensor powers `L^{⊗ k} = AlgebraicGeometry.Space.intTensorPowModule`.  This file supplies
the two facts about tensoring by `L^{⊗ -n}` that the conclusion of Stacks 0GUT consumes — an
epimorphism out of `⨁ f^*ℰ_i ⊗ L^{⊗ -n_i}` — and which were available for neither tensor product
on `AlgebraicGeometry.Space.Modules`:

* **untwisting**: `(ℱ ⊗ L^{⊗ n}) ⊗ L^{⊗ -n} ≅ ℱ`, so that a map `f^*ℰ ⟶ ℱ ⊗ L^{⊗ n}` tensored by
  `L^{⊗ -n}` is a map `f^*ℰ ⊗ L^{⊗ -n} ⟶ ℱ`;
* **`- ⊗ L^{⊗ n}` preserves and reflects epimorphisms**, so that joint surjectivity of the
  untwisted maps and joint surjectivity of the twisted ones are the same statement.  Reflection is
  the direction the source's argument actually runs in, and it is no weaker than preservation
  here: both come from tensoring by `L^{⊗ n}` being an *equivalence*.

Everything is stated at the module universe `u` of the schemes.  That is forced:
`AlgebraicGeometry.SheafOfModules.tensorPow`, and with it `intTensorPowModule`, lives at the
universe where the monoidal structure on presheaves of modules lives, which for the small étale
site of an algebraic space over `Scheme.{u}` is `u`.

## Main results

In the `Stacks.SheafOfModules.Tensor.sheafTensor` spelling, which needs no monoidal instance:

* `AlgebraicGeometry.Space.sheafTensorIntTensorPowPairingIso`: the pairing
  `L^{⊗ a} ⊗ L^{⊗ b} ≅ 𝒪_X` for `a + b = 0`.
* `AlgebraicGeometry.Space.sheafTensorIntTensorPowUntwistIso`: **untwisting**,
  `(ℱ ⊗ L^{⊗ n}) ⊗ L^{⊗ -n} ≅ ℱ`.
* `AlgebraicGeometry.Space.isEquivalence_sheafTensorFlipObj_intTensorPowModule`,
  `AlgebraicGeometry.Space.preservesEpimorphisms_sheafTensorFlipObj_intTensorPowModule` and
  `AlgebraicGeometry.Space.reflectsEpimorphisms_sheafTensorFlipObj_intTensorPowModule`:
  **`- ⊗ L^{⊗ n}` is an equivalence, and so preserves and reflects epimorphisms.**
* `AlgebraicGeometry.Space.epi_sheafTensor_map_app_intTensorPowModule_iff`: the two together, as
  `Epi (f ⊗ 𝟙) ↔ Epi f`.

In the `AlgebraicGeometry.Space.modulesMonoidalCategory` spelling, which is the one
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_tensorObj` is stated for:

* `AlgebraicGeometry.Space.tensorObjIntTensorPowUntwistIso`: untwisting.
* `AlgebraicGeometry.Space.hasInverseIntTensorPowModule`: `L^{⊗ n}` has a two-sided tensor
  inverse, namely `L^{⊗ -n}`, so it is invertible in the sense of Stacks 0FFN for *this* tensor
  product.
* `AlgebraicGeometry.Space.isEquivalence_tensorRight_intTensorPowModule`,
  `AlgebraicGeometry.Space.preservesEpimorphisms_tensorRight_intTensorPowModule`,
  `AlgebraicGeometry.Space.reflectsEpimorphisms_tensorRight_intTensorPowModule` and
  `AlgebraicGeometry.Space.epi_whiskerRight_intTensorPowModule_iff`: the same three facts and the
  same `Epi` criterion for `CategoryTheory.MonoidalCategory.tensorRight`.

## Implementation notes

**No hypothesis beyond invertibility of `L`.**  Every statement below takes exactly
`AlgebraicGeometry.Space.IsInvertibleModule X L` — the hypothesis under which `L^{⊗ k}` is defined
at all — and nothing else: no quasi-coherence, no finiteness, no relative ampleness.  In
particular the untwisting isomorphism holds for an arbitrary `𝒪_X`-module `ℱ`, and the epimorphism
statements for arbitrary source and target.

**The three tensor products, and the bridge between them.**  `Modules` carries two monoidal
structures that are distinct terms, `AlgebraicGeometry.Space.modulesMonoidalCategory` and the
`Stacks.SheafInternalHom.monoidalCategory` that `AlgebraicGeometry.SheafOfModules.tensorPow` is
defined by, and in addition the bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` with no
monoidal structure at all.  The public bridges are
`AlgebraicGeometry.Space.modulesTensorObjIso` and `AlgebraicGeometry.SheafOfModules.tensorIso`,
each identifying one of the monoidal tensor products with `sheafTensor`; no further bridge is
proved here, and none is needed, because the only ingredient taken from the third structure is
`AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf`, which is already stated in the
`sheafTensor` spelling, as is `AlgebraicGeometry.SheafOfModules.tensorPowZeroIso`.  Both spellings
of every result are given, since the chart transport of Stacks 0GUT
(`AlgebraicGeometry.Space.chartRestrictionSchemeModuleTensorIntTensorPowIso`) is written in the
`sheafTensor` one while `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_tensorObj` is written
in the `modulesMonoidalCategory` one, and a consumer of Stacks 0GUT needs both at once.

**Why the epimorphism statements are about an equivalence rather than about a right adjoint.**
Tensoring by a *flat* module preserves epimorphisms and nothing more; it is invertibility of
`L^{⊗ n}` that also gives reflection, and reflection is what the source uses.  For the
`sheafTensor` spelling the equivalence is the existing instance
`Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible` applied to
`AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow`; for the `modulesMonoidalCategory`
spelling it is `CategoryTheory.MonoidalCategory.HasInverse.tensorRightEquivalence` applied to the
pairing isomorphisms below, since invertibility for one of the two monoidal structures is not
invertibility for the other without a comparison of the tensor products, which is what the
pairing supplies.  Preservation and reflection are then Mathlib's: an equivalence is a left
adjoint, and it is faithful.

**No tag is claimed.**  Stacks 0GUT is not proved here, and these are inputs to one step of its
proof; Stacks 01CU, which the tensor powers and their addition law realise, is registered in
`StacksFrontier.AlgebraicGeometry.TensorPowers.Basic`.

## References

* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  (L : Modules.{u, u} B S hS X.1 X.2) [IsInvertibleModule X L]

section Pairing

attribute [local instance] modulesMonoidalCategory

/-- **The pairing of two tensor powers of opposite exponents**, `L^{⊗ a} ⊗ L^{⊗ b} ≅ 𝒪_X` when
`a + b = 0`, with the tensor product of `AlgebraicGeometry.Space.modulesMonoidalCategory`.  This
is the addition law of Stacks 01CU read through
`AlgebraicGeometry.Space.modulesTensorObjIso`, followed by the identification of the zeroth power
with the structure sheaf and of the structure sheaf with the tensor unit, which
`AlgebraicGeometry.Space.modulesTensorUnit_eq` gives on the nose. -/
def tensorObjIntTensorPowPairingIso (a b : ℤ) (hab : a + b = 0) :
    intTensorPowModule B S hS X L a ⊗ intTensorPowModule B S hS X L b ≅
      𝟙_ (Modules.{u, u} B S hS X.1 X.2) :=
  modulesTensorObjIso B S hS X.1 X.2 (intTensorPowModule B S hS X L a)
      (intTensorPowModule B S hS X L b) ≪≫
    AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L a b ≪≫
    eqToIso (congrArg (intTensorPowModule B S hS X L) hab) ≪≫
    AlgebraicGeometry.SheafOfModules.tensorPowZeroIso (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L ≪≫
    eqToIso (modulesTensorUnit_eq B S hS X.1 X.2).symm

/-- **The pairing of two tensor powers of opposite exponents**, in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling: `L^{⊗ a} ⊗ L^{⊗ b} ≅ 𝒪_X` when `a + b = 0`.
This is the addition law of Stacks 01CU,
`AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf`, followed by
`AlgebraicGeometry.SheafOfModules.tensorPowZeroIso`. -/
def sheafTensorIntTensorPowPairingIso (a b : ℤ) (hab : a + b = 0) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS X.1 X.2)).obj (intTensorPowModule B S hS X L a)).obj
        (intTensorPowModule B S hS X L b) ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L a b ≪≫
    eqToIso (congrArg (intTensorPowModule B S hS X L) hab) ≪≫
    AlgebraicGeometry.SheafOfModules.tensorPowZeroIso (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L

/-- **`L^{⊗ n}` has a two-sided tensor inverse for the tensor product of
`AlgebraicGeometry.Space.modulesMonoidalCategory`**, namely `L^{⊗ -n}`: the two pairings
`AlgebraicGeometry.Space.tensorObjIntTensorPowPairingIso` in the exponents `(n, -n)` and
`(-n, n)`.  This is invertibility in the sense of Stacks 0FFN for *that* tensor product, which
invertibility of `L` — a statement about the tensor product of Stacks 01CS — does not give
directly. -/
def hasInverseIntTensorPowModule (n : ℤ) :
    MonoidalCategory.HasInverse (intTensorPowModule B S hS X L n) where
  inv := intTensorPowModule B S hS X L (-n)
  isoLeft := tensorObjIntTensorPowPairingIso B S hS X L n (-n) (by ring)
  isoRight := tensorObjIntTensorPowPairingIso B S hS X L (-n) n (by ring)

/-- **Untwisting**, with the tensor product of
`AlgebraicGeometry.Space.modulesMonoidalCategory`: `(ℱ ⊗ L^{⊗ n}) ⊗ L^{⊗ -n} ≅ ℱ` for an
arbitrary `𝒪_X`-module `ℱ`.  The associator moves the two powers together, the pairing
`AlgebraicGeometry.Space.tensorObjIntTensorPowPairingIso` turns them into the tensor unit, and
the right unitor removes it. -/
def tensorObjIntTensorPowUntwistIso (F : Modules.{u, u} B S hS X.1 X.2) (n : ℤ) :
    (F ⊗ intTensorPowModule B S hS X L n) ⊗ intTensorPowModule B S hS X L (-n) ≅ F :=
  α_ F (intTensorPowModule B S hS X L n) (intTensorPowModule B S hS X L (-n)) ≪≫
    whiskerLeftIso F (tensorObjIntTensorPowPairingIso B S hS X L n (-n) (by ring)) ≪≫ ρ_ F

/-- **Untwisting**, in the `Stacks.SheafOfModules.Tensor.sheafTensor` spelling:
`(ℱ ⊗ L^{⊗ n}) ⊗ L^{⊗ -n} ≅ ℱ` for an arbitrary `𝒪_X`-module `ℱ`.  This is
`AlgebraicGeometry.Space.tensorObjIntTensorPowUntwistIso` with both nestings read through the
bridge `AlgebraicGeometry.Space.modulesTensorObjIso`. -/
def sheafTensorIntTensorPowUntwistIso (F : Modules.{u, u} B S hS X.1 X.2) (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS X.1 X.2)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).obj F).obj
          (intTensorPowModule B S hS X L n))).obj
        (intTensorPowModule B S hS X L (-n)) ≅ F :=
  (modulesTensorObjIso B S hS X.1 X.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS X.1 X.2)).obj F).obj (intTensorPowModule B S hS X L n))
      (intTensorPowModule B S hS X L (-n))).symm ≪≫
    whiskerRightIso
      (modulesTensorObjIso B S hS X.1 X.2 F (intTensorPowModule B S hS X L n)).symm
      (intTensorPowModule B S hS X L (-n)) ≪≫
    tensorObjIntTensorPowUntwistIso B S hS X L F n

end Pairing

section Epi

/-- **Tensoring on the right by `L^{⊗ n}` is an equivalence**, in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling.  Every integer tensor power of an invertible
module is invertible (`AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow`, Stacks 01CT (1)
and (2)), and tensoring on the right by an invertible sheaf of modules is an equivalence. -/
instance isEquivalence_sheafTensorFlipObj_intTensorPowModule (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X.1 X.2)).flip.obj
        (intTensorPowModule B S hS X L n)).IsEquivalence :=
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) (intTensorPowModule B S hS X L n) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L n
  Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2)
    (intTensorPowModule B S hS X L n)

/-- **`- ⊗ L^{⊗ n}` preserves epimorphisms**, in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling: it is an equivalence, hence a left
adjoint. -/
instance preservesEpimorphisms_sheafTensorFlipObj_intTensorPowModule (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X.1 X.2)).flip.obj
        (intTensorPowModule B S hS X L n)).PreservesEpimorphisms :=
  inferInstance

/-- **`- ⊗ L^{⊗ n}` reflects epimorphisms**, in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling: it is an equivalence, hence faithful.  This
is the direction the proof of Stacks 0GUT runs in — joint surjectivity of the untwisted maps is
read off from joint surjectivity of the twisted ones — and it is not available from flatness of
`L^{⊗ n}` alone. -/
instance reflectsEpimorphisms_sheafTensorFlipObj_intTensorPowModule (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X.1 X.2)).flip.obj
        (intTensorPowModule B S hS X L n)).ReflectsEpimorphisms :=
  Functor.reflectsEpimorphisms_of_faithful _

/-- **A morphism is an epimorphism exactly when its twist by `L^{⊗ n}` is**, in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling.  Both directions of
`CategoryTheory.Functor.epi_map_iff_epi` for an equivalence. -/
theorem epi_sheafTensor_map_app_intTensorPowModule_iff (n : ℤ)
    {F G : Modules.{u, u} B S hS X.1 X.2} (f : F ⟶ G) :
    Epi (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS X.1 X.2)).map f).app (intTensorPowModule B S hS X L n)) ↔
      Epi f :=
  Functor.epi_map_iff_epi
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X.1 X.2)).flip.obj (intTensorPowModule B S hS X L n)) f

section Monoidal

attribute [local instance] modulesMonoidalCategory

/-- **Tensoring on the right by `L^{⊗ n}` is an equivalence**, for the tensor product of
`AlgebraicGeometry.Space.modulesMonoidalCategory`.  This is (3) ⇒ (2) of Stacks 0FFM applied to
the two-sided tensor inverse `AlgebraicGeometry.Space.hasInverseIntTensorPowModule`. -/
instance isEquivalence_tensorRight_intTensorPowModule (n : ℤ) :
    (tensorRight (intTensorPowModule B S hS X L n)).IsEquivalence :=
  CategoryTheory.Equivalence.isEquivalence_functor
    (hasInverseIntTensorPowModule B S hS X L n).tensorRightEquivalence

/-- **`- ⊗ L^{⊗ n}` preserves epimorphisms**, for the tensor product of
`AlgebraicGeometry.Space.modulesMonoidalCategory`: it is an equivalence, hence a left
adjoint. -/
instance preservesEpimorphisms_tensorRight_intTensorPowModule (n : ℤ) :
    (tensorRight (intTensorPowModule B S hS X L n)).PreservesEpimorphisms :=
  inferInstance

/-- **`- ⊗ L^{⊗ n}` reflects epimorphisms**, for the tensor product of
`AlgebraicGeometry.Space.modulesMonoidalCategory`: it is an equivalence, hence faithful. -/
instance reflectsEpimorphisms_tensorRight_intTensorPowModule (n : ℤ) :
    (tensorRight (intTensorPowModule B S hS X L n)).ReflectsEpimorphisms :=
  Functor.reflectsEpimorphisms_of_faithful _

/-- **A morphism is an epimorphism exactly when its twist by `L^{⊗ n}` is**, for the tensor
product of `AlgebraicGeometry.Space.modulesMonoidalCategory`. -/
theorem epi_whiskerRight_intTensorPowModule_iff (n : ℤ)
    {F G : Modules.{u, u} B S hS X.1 X.2} (f : F ⟶ G) :
    Epi (f ▷ intTensorPowModule B S hS X L n) ↔ Epi f :=
  Functor.epi_map_iff_epi (tensorRight (intTensorPowModule B S hS X L n)) f

end Monoidal

end Epi

end AlgebraicGeometry.Space

end
