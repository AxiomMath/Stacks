module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoproductRight
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShiftedSumIsProduct
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyDirectSums
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-!
# Tensoring with a free module, and the acyclicity of the twists this produces

A free `𝒪_X`-module on an index type `κ` *is* the coproduct of `κ` copies of the structure
sheaf, so tensoring an `𝒪_X`-module `ℱ` with it produces the coproduct of `κ` copies of `ℱ`:

`(⊕_{κ} 𝒪_X) ⊗_{𝒪_X} ℱ ≅ ⊕_{κ} ℱ`.

That is `Stacks.SheafOfModules.Strict.coproductUnitTensorIso` read at the scheme spelling
`Stacks.RelativeVeryAmple.tensorModules` of the tensor product sheaf of [Stacks, Tag 01CA]; the
two spellings are the same construction on the nose, so no comparison map intervenes and the
index type need not be finite.

The consequence recorded here is a step of the dévissage proving acyclicity of high twists: for
`κ` finite, the higher cohomology of a twist of `(⊕_{κ} 𝒪_X) ⊗ ℱ` vanishes as soon as that of the
corresponding twist of `ℱ` does. A single degree bound for `ℱ` therefore serves every finite free
tensor of `ℱ` at once, and no new estimate is made.

## Main results

* `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.freeTensorModulesIso`: the displayed
  isomorphism `(⊕_{κ} 𝒪_X) ⊗ ℱ ≅ ⊕_{κ} ℱ`, for an arbitrary index type `κ`.
* `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.tensorModulesFreeIso`: the same with the two
  tensor factors interchanged, `ℱ ⊗ (⊕_{κ} 𝒪_X) ≅ ⊕_{κ} ℱ`.
* `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.freeTensorModulesAssocIso`: a twist of a free
  tensor is the coproduct of the twists, `((⊕_{κ} 𝒪_X) ⊗ 𝒜) ⊗ ℬ ≅ ⊕_{κ} (𝒜 ⊗ ℬ)`.
* `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isZero_obj_sigma_of_isZero`: an additive functor
  carries a finite coproduct of objects it kills to a zero object.
* `Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isZero_Hgroup_tensorModules_free`: **uniform
  acyclicity of the twists of a finite free tensor.** For `κ` finite,
  `H ᵖ(X, ((⊕_{κ} 𝒪_X) ⊗ ℱ) ⊗ L ^⊗ d) = 0` whenever `H ᵖ(X, ℱ ⊗ L ^⊗ d) = 0`.

## Implementation notes

**The monoidal structure is ascribed by hand.** The associator used below is that of
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product is
`Stacks.RelativeVeryAmple.tensorModules` definitionally. It is introduced with an explicit type
ascription at `AlgebraicGeometry.Scheme.Modules` rather than as a global instance, because that
is a definition which instance search does not unfold; for the same reason the free module is
written `show X.Modules from SheafOfModules.free κ`, so that the associator is elaborated in the
category the ascription names. The braiding is not taken from the same structure but from
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`, the natural isomorphism between the tensor
bifunctor and its flip: its value on a pair of modules is already an isomorphism of the tensor
product sheaves, with no monoidal instance to supply.

**Why the cohomological step only needs additivity.** Cohomology over an arbitrary open commutes
with *finite* direct sums for the cheap reason that it is additive
(`Stacks.Cohomology.DirectSum.additive_Hfunctor`), and an additive functor preserves finite
biproducts, hence finite coproducts. The much stronger
`Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor`, which handles arbitrary
direct sums, is deliberately not used: it carries the quasi-compactness and quasi-separatedness
hypotheses of [Stacks, Tag 01FF], while `X` here is an arbitrary scheme. This is why the
acyclicity statement is restricted to a finite index type although the isomorphisms above are
not.

**Two instances are named rather than searched for.**
`CategoryTheory.Limits.PreservesFiniteBiproducts` quantifies over index types in `Type 0` only,
so the preservation statement is obtained for `Fin n` and transported along an equivalence
`ι ≃ Fin n`. And the coproducts of sheaves of modules are supplied by
`Stacks.SheafOfModules.FlatCoproduct.hasColimitsOfShape_discrete`, for the reason given at that
declaration: with a `Finite` hypothesis in scope the search for them exhausts the heartbeat
limit.

No Stacks attribute is attached: these are steps of a dévissage rather than the content of a tag.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.RelativeVeryAmple (tensorModules)

universe u

namespace Stacks.AlgebraicGeometry.AmpleTwistAcyclicity

/-- **An additive functor carries a finite coproduct of objects it kills to a zero object.**

An additive functor preserves finite biproducts, hence coproducts indexed by a finite type, so
the image of the coproduct is the coproduct of the images; and a coproduct of zero objects is
zero. The preservation statement is available only for index types in `Type 0`, so it is proved
for `Fin n` and transported along an equivalence `ι ≃ Fin n`. -/
theorem isZero_obj_sigma_of_isZero {C : Type*} [Category C] [Preadditive C] {ι : Type*}
    [Finite ι] [HasColimitsOfShape (Discrete ι) C] {D : Type*} [Category D] [Preadditive D]
    [HasFiniteCoproducts D] (G : C ⥤ D) [G.Additive] (A : ι → C)
    (h : ∀ i, IsZero (G.obj (A i))) : IsZero (G.obj (∐ A)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  have : PreservesFiniteBiproducts G := Functor.preservesFiniteBiproductsOfAdditive G
  have : PreservesColimitsOfShape (Discrete (Fin n)) G :=
    preservesCoproductsOfShape_of_preservesBiproductsOfShape G
  have : PreservesColimitsOfShape (Discrete ι) G :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence e).symm G
  refine (Stacks.ShiftedSum.isZero_coproduct (fun i => G.obj (A i)) h).of_iso ?_
  exact preservesColimitIso G (Discrete.functor A) ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete A G)

variable (X : Scheme.{u})

/-- **Tensoring a module with a free module gives a coproduct of copies of it**,
`(⊕_{κ} 𝒪_X) ⊗_{𝒪_X} ℱ ≅ ⊕_{κ} ℱ`.

`SheafOfModules.free κ` *is* the coproduct of `κ` copies of `𝒪_X`, and
`Stacks.SheafOfModules.Strict.coproductUnitTensorIso` is exactly this statement for that
coproduct: tensoring in the right variable commutes with colimits, and `𝒪_X` is a unit for the
tensor product sheaf. The index type is arbitrary. -/
def freeTensorModulesIso (F : X.Modules) (κ : Type u) :
    tensorModules X (SheafOfModules.free κ) F ≅ ∐ fun _ : κ => F :=
  Stacks.SheafOfModules.Strict.coproductUnitTensorIso X.sheaf F κ

/-- **The same with the two tensor factors interchanged**,
`ℱ ⊗_{𝒪_X} (⊕_{κ} 𝒪_X) ≅ ⊕_{κ} ℱ`.

The tensor bifunctor of sheaves of modules is isomorphic to its own flip, by
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`; the component of that isomorphism at the
pair `(ℱ, ⊕_{κ} 𝒪_X)` exchanges the two factors. -/
def tensorModulesFreeIso (F : X.Modules) (κ : Type u) :
    tensorModules X F (SheafOfModules.free κ) ≅ ∐ fun _ : κ => F :=
  (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.sheaf).app F).app
    (SheafOfModules.free κ)).trans (freeTensorModulesIso X F κ)

/-- **A twist of a free tensor is the coproduct of the twists**,
`((⊕_{κ} 𝒪_X) ⊗ 𝒜) ⊗ ℬ ≅ ⊕_{κ} (𝒜 ⊗ ℬ)`.

The associator moves `ℬ` inside the free factor and `freeTensorModulesIso` is then applied to
`𝒜 ⊗ ℬ`, so no colimit-preservation statement for the functor `- ⊗ ℬ` is needed. -/
def freeTensorModulesAssocIso (A B : X.Modules) (κ : Type u) :
    tensorModules X (tensorModules X (SheafOfModules.free κ) A) B ≅
      ∐ fun _ : κ => tensorModules X A B :=
  letI : MonoidalCategory X.Modules :=
    (Stacks.SheafOfModules.Strict.monoidalCategory (X.sheaf).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf)).property)
  (α_ (show X.Modules from SheafOfModules.free κ) A B).trans
    (freeTensorModulesIso X (tensorModules X A B) κ)

/-- **Uniform acyclicity of the twists of a finite free tensor.** Let `L` be an invertible
`𝒪_X`-module, let `p` be a degree, `d` an exponent and `κ` a finite index type. If the `p`-th
cohomology of the twist `ℱ ⊗ L ^⊗ d` vanishes, then so does that of the twist
`((⊕_{κ} 𝒪_X) ⊗ ℱ) ⊗ L ^⊗ d`.

By `freeTensorModulesAssocIso` the second twist is the coproduct of `κ` copies of the first, and
`H ᵖ(X, -)` is additive, so `isZero_obj_sigma_of_isZero` applies; the vanishing is then
transported along the isomorphism by `CategoryTheory.Limits.IsZero.of_iso`. Nothing about the
twist is used beyond that isomorphism, and no bound on `d` is produced or consumed. -/
theorem isZero_Hgroup_tensorModules_free (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (κ : Type u) [Finite κ] (p : ℕ) (d : ℤ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ p
      (tensorModules X F (Stacks.Ample.tensorPowModule X L d)))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p
      (tensorModules X (tensorModules X (SheafOfModules.free κ) F)
        (Stacks.Ample.tensorPowModule X L d))) := by
  have := Stacks.Cohomology.DirectSum.additive_Hfunctor X.ringCatSheaf ⊤ p
  have := Stacks.SheafOfModules.FlatCoproduct.hasColimitsOfShape_discrete X.ringCatSheaf κ
  refine (isZero_obj_sigma_of_isZero (Hfunctor X.ringCatSheaf ⊤ p)
    (fun _ : κ => tensorModules X F (Stacks.Ample.tensorPowModule X L d))
    fun _ => h).of_iso ?_
  exact (Hfunctor X.ringCatSheaf ⊤ p).mapIso
    (freeTensorModulesAssocIso X F (Stacks.Ample.tensorPowModule X L d) κ)

end Stacks.AlgebraicGeometry.AmpleTwistAcyclicity

end
