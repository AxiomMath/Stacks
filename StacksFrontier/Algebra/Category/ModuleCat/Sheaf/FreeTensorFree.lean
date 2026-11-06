module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# The tensor product of two free sheaves of modules

Let `O♯` be a sheaf of commutative rings on a site `(C, J)`. The free sheaf of `O♯`-modules on a
type `I` is by definition the coproduct of `I` copies of the structure sheaf, and the tensor
product of sheaves of modules preserves coproducts in each variable, so

`O♯^{(I)} ⊗ O♯^{(K)} ≅ O♯^{(I × K)}`.

This file proves that, and the two consequences the free-presentation statements of Stacks
Section 17.21 consume: the first term `M₂ ⊗ Sym^k(M₁)` (respectively `M₂ ⊗ ⋀^k(M₁)`) of the
three-term sequence of Tag 01CJ is free of finite rank as soon as `M₂` and `M₁` are.

## Main definitions

* `Stacks.SheafOfModules.freeTensorFreeIso`: **the tensor product of two free sheaves of modules
  is free on the product of the two index types.**
* `Stacks.SheafOfModules.tensorIsoFree`: the same for two sheaves of modules merely
  *isomorphic* to free ones.

## Main results

* `Stacks.SheafOfModules.tensorSheafBifunctor_obj`: the two spellings of the tensor product of
  sheaves of modules on a site — the bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` and its
  flip with the right factor fixed — agree on objects, by `rfl`.
* `Stacks.SheafOfModules.exists_finite_nonempty_tensor_iso_free`: the consumer form of
  `tensorIsoFree`, with the index type existentially quantified and its finiteness recorded.
* `Stacks.SheafOfModules.exists_finite_nonempty_iso_free_tensor_symmetricPower` and
  `exists_finite_nonempty_iso_free_tensor_exteriorPower`: **`M₂ ⊗ Sym^k(M₁)` and
  `M₂ ⊗ ⋀^k(M₁)` are free of finite rank** when `M₂` and `M₁` are isomorphic to finite free
  sheaves of modules. These are the first terms of the two sequences of Tag 01CJ, in the
  spelling `SheafOfModules.GradedAlgebra.presentationShortComplex_X₁` gives them.

## Implementation notes

**Two spellings of the tensor product, crossed once.** The flip
`(Stacks.SheafOfModules.Tensor.sheafTensor O♯).flip.obj F` is the endofunctor `A ↦ (A ⊗ F)^#`
over the base written `Stacks.commRingSheafToRingSheaf O♯`, and it is the one carrying the
coproduct-preservation instance `Stacks.preservesColimitsOfSize_sheafTensorRight`.
`Stacks.SheafOfModules.Tensor.sheafTensor` is the bifunctor over the base written
`CategoryTheory.Sheaf.toRingCat J O♯`, and it is the one every statement about the sequences of
Tag 01CJ uses. The two bases are definitionally equal and the two functors agree on objects by
`rfl` (`tensorSheafBifunctor_obj`). Every *statement* below is written in the bifunctor
spelling, and the crossing happens only inside the proofs, where defeq is checked once by `:=`
rather than by a rewrite. Writing `freeTensorFreeIso` the other way round and converting
afterwards exhausts the heartbeat budget: the conversion is then between two `Iso`s, whose `hom`
fields are functor applications, instead of between two objects.

**The functor argument of `PreservesCoproduct.iso` is named.** Left implicit it is a
metavariable that the ascribed bifunctor type cannot solve, and the application fails with a
type mismatch mentioning the unsolved functor. This is the "name the implicits" discipline that
the one-line `whnf` timeouts in this development all come down to.

**Finiteness is carried as a hypothesis of the conclusion, not of the statement**, in
`exists_finite_nonempty_tensor_iso_free`: the isomorphism exists for arbitrary index types and
only its finiteness needs `[Finite I]` and `[Finite K]`, so the general statement is the useful
one and the finite consumers below instantiate it.

**Nothing here is specialized to a ringed space**, and nothing is narrowed: the site universes
`u`, `v` are independent of the module universe `w`, which is the universe of the ring as well,
forced for `Stacks.SheafOfModules.Tensor.sheafTensor` exactly as it is in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`.

**No `@[stacks]` attribute.** The free-presentation assertions of Section 17.21 are Tag 01CJ
together with Tag 01CK(6); the sequences themselves are carried by
`SheafOfModules.SymPresentation.symmetricPresentation_exact` and
`SheafOfModules.ExtPresentation.exteriorPresentation_exact`, and the freeness of the powers by
`Stacks.SheafOfModules.symmetricPowerFreeIso` and `exteriorPowerFreeIso`. This file supplies
the one term of those sequences that neither covers, and asserts nothing a tag states that is
not already proved in those files.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The bifunctorial tensor product of sheaves of modules and its flip with the right factor
fixed agree on objects. The two live over the two spellings
`CategoryTheory.Sheaf.toRingCat J O♯` and `Stacks.commRingSheafToRingSheaf O♯` of the same sheaf
of rings; this is the single place that crossing is recorded. -/
theorem tensorSheafBifunctor_obj
    (A B : _root_.SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A).obj B =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).flip.obj B)).obj A := rfl

/-- **The tensor product of two free sheaves of modules is free on the product of the two
index types.** -/
noncomputable def freeTensorFreeIso (I K : Type w) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (_root_.SheafOfModules.free (R :=
        CategoryTheory.Sheaf.toRingCat J Osharp) I)).obj (_root_.SheafOfModules.free (R :=
        CategoryTheory.Sheaf.toRingCat J Osharp) K) ≅
      _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) (I × K) :=
  haveI : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  haveI : HasColimitsOfShape (Discrete I)
      (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :=
    _root_.SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _
  haveI : ∀ X : Type w, HasColimitsOfShape (Discrete X)
      (PresheafOfModules.{w} (Stacks.commRingSheafToRingSheaf Osharp).obj) :=
    fun _ => PresheafOfModules.hasColimitsOfShape _ _
  haveI : HasColimitsOfShape (Discrete I)
      (_root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf Osharp)) :=
    _root_.SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _
  haveI := Stacks.preservesColimitsOfSize_sheafTensorRight.{v, u, w, w} Osharp
    (_root_.SheafOfModules.free (R := Stacks.commRingSheafToRingSheaf Osharp) K)
  PreservesCoproduct.iso
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).flip.obj
        (_root_.SheafOfModules.free (R := Stacks.commRingSheafToRingSheaf Osharp) K))
      (fun _ : I => _root_.SheafOfModules.unit (Stacks.commRingSheafToRingSheaf Osharp)) ≪≫
    Sigma.mapIso (fun _ : I => Stacks.TensorCoherence.tensorSheafUnitIso
      (_root_.SheafOfModules.free (R := Stacks.commRingSheafToRingSheaf Osharp) K)) ≪≫
    _root_.SheafOfModules.freeSigmaIso (fun _ : I => K) ≪≫
    (_root_.SheafOfModules.freeFunctor).mapIso (Equiv.sigmaEquivProd I K).toIso

/-- **The tensor product of two sheaves of modules isomorphic to free ones is free**, on the
product of the two index types. -/
noncomputable def tensorIsoFree
    {A B : _root_.SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)} {I K : Type w}
    (eA : A ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) I)
    (eB : B ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) K) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A).obj B ≅
      _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) (I × K) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).mapIso eA).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).mapIso eB) ≪≫ freeTensorFreeIso J I
          K

/-- The consumer form of `Stacks.SheafOfModules.tensorIsoFree`: the tensor product of two
sheaves of modules isomorphic to free ones is free on some index type, finite when both index
types are. -/
theorem exists_finite_nonempty_tensor_iso_free
    {A B : _root_.SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)} {I K : Type w}
    (eA : A ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) I)
    (eB : B ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) K) :
    ∃ D : Type w, (Finite I → Finite K → Finite D) ∧
      Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A).obj B ≅
        _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) D) :=
  ⟨I × K, fun _ _ => inferInstance, ⟨tensorIsoFree J eA eB⟩⟩

variable {F : _root_.SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)}

/-- Tensoring with a sheaf isomorphic to a finite free one preserves being free of finite rank. -/
private theorem exists_finite_nonempty_tensor_iso_free_of_finite
    {M₂ X : _root_.SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)} {I₂ : Type w}
    [Finite I₂]
    (e₂ : M₂ ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) I₂)
    (h : ∃ K : Type w, Finite K ∧
      Nonempty (X ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) K)) :
    ∃ D : Type w, Finite D ∧
      Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M₂).obj X ≅
        _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) D) := by
  obtain ⟨K, _, ⟨eK⟩⟩ := h
  exact ⟨I₂ × K, inferInstance, ⟨tensorIsoFree J e₂ eK⟩⟩

/-- **The first term `M₂ ⊗ Sym^k(M₁)` of the sequence of Tag 01CJ is free of finite rank** when
`M₂` and `M₁` are isomorphic to finite free sheaves of modules. The object is spelled as
`SheafOfModules.GradedAlgebra.presentationShortComplex_X₁` gives it. -/
theorem exists_finite_nonempty_iso_free_tensor_symmetricPower (k : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F)
    {M₂ : _root_.SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)}
    (I₂ I₁ : Type w) [Finite I₂] [Finite I₁]
    (e₂ : M₂ ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) I₂)
    (e₁ : F ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) I₁) :
    ∃ D : Type w, Finite D ∧
      Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M₂).obj (A.symmetric.piece (k
          : ℤ)) ≅
        _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) D) := by
  exact exists_finite_nonempty_tensor_iso_free_of_finite J e₂
    (exists_finite_nonempty_iso_free_symmetricPower J k A I₁ e₁)

/-- **The first term `M₂ ⊗ ⋀^k(M₁)` of the exterior sequence of Tag 01CJ is free of finite
rank** when `M₂` and `M₁` are isomorphic to finite free sheaves of modules. -/
theorem exists_finite_nonempty_iso_free_tensor_exteriorPower (k : ℕ)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F)
    {M₂ : _root_.SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)}
    (I₂ I₁ : Type w) [Finite I₂] [Finite I₁]
    (e₂ : M₂ ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) I₂)
    (e₁ : F ≅ _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) I₁) :
    ∃ D : Type w, Finite D ∧
      Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M₂).obj (A.exterior.piece (k
          : ℤ)) ≅
        _root_.SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat J Osharp) D) := by
  exact exists_finite_nonempty_tensor_iso_free_of_finite J e₂
    (exists_finite_nonempty_iso_free_exteriorPower J k A I₁ e₁)

end Stacks.SheafOfModules

end
