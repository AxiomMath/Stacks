module

public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invertible quotients of a sheaf of modules, and their base change

Let `X` be a scheme and `E` a sheaf of `𝒪_X`-modules. An *invertible quotient* of `E` is a
surjection `q : E ⟶ L` onto an invertible `𝒪_X`-module. Tag 0B3V identifies these, up to
isomorphism of the target, with the sections of the projective bundle `𝐏(E) → X`, and
identifies the conormal sheaf of such a section with `ker(q) ⊗ L^{⊗ -1}`.

This file carries the module-theoretic half of that tag: the vocabulary of invertible
quotients, the characterization of a negative first tensor power by a trivializing pairing,
and the two base-change comparisons `ker(q)` and `L^{⊗ -1}` are required to satisfy.

## Main definitions

* `Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne`: a sheaf of modules `M` whose tensor
  product with an invertible `L` is the structure sheaf *is* the negative first tensor power
  `L^{⊗ -1}`, canonically. This is the uniqueness of inverses for the tensor product, read off
  the autoequivalence that defines the powers.
* `Stacks.Divisors.InvertibleQuotient`: a surjection from `E` onto an invertible module sheaf,
  with `Stacks.Divisors.InvertibleQuotient.IsEquivalent`,
  `Stacks.Divisors.invertibleQuotientSetoid` and `Stacks.Divisors.InvertibleQuotientClass`
  recording when two of them are to be identified.
* `Stacks.Divisors.quotientKernelBaseChangeMap`: the canonical comparison from the pullback of
  `ker q` to the kernel of the pulled-back quotient. It exists with no hypothesis.
* `Stacks.Divisors.quotientKernelBaseChangeIso`: the comparison identifying the pullback of
  `ker q` with the kernel of the pulled-back quotient, pinned down by its map into the ambient
  module, and `Stacks.Divisors.quotientKernelBaseChangeIsoOfMono` the same under the weaker
  hypothesis that the canonical comparison is a monomorphism.
* `Stacks.Divisors.inverseQuotientBaseChangeIso`: the comparison identifying the pullback of
  `L^{⊗ -1}` with the negative first tensor power of the pulled-back quotient line.

## Main results

* `Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne_hom_tensor`: the identification above
  is the one that carries the canonical trivialization of `L^{⊗ -1} ⊗ L` back to the given
  pairing, so it is normalized and not merely some isomorphism.
* `Stacks.preservesLimit_parallelPair_zero_of_isSplitEpi`: an additive functor preserves the
  kernel of a split epimorphism, and
  `Stacks.Divisors.preservesLimit_parallelPair_zero_pullback_of_isSplitEpi` for the pullback of
  sheaves of modules. This is the formal half of the left exactness used below: the kernel
  sequence of an invertible quotient splits locally, and this is what a splitting buys.
* `Stacks.epi_kernelComparison`: the kernel comparison of a functor preserving finite colimits,
  at an epimorphism, is itself an epimorphism — with no further hypothesis. Hence
  `Stacks.preservesLimit_parallelPair_zero_of_mono_kernelComparison`: for an epimorphism, left
  exactness on its kernel sequence is exactly injectivity of the comparison.
* `Stacks.Divisors.epi_quotientKernelBaseChangeMap`: consequently the canonical comparison
  `g^*(ker q) ⟶ ker q'` is an epimorphism unconditionally, and
  `Stacks.Divisors.eq_quotientKernelBaseChangeMap` says it is the only morphism satisfying the
  normalization Tag 0B3V asks for. Half of that tag's base-change clause for the quotient
  kernel is therefore established here with no added hypothesis.
* `Stacks.Divisors.mono_quotientKernelBaseChangeMap_iff`: the other half, injectivity of the
  comparison, is equivalent to pullback carrying the single monomorphism `ker q ⟶ E` to a
  monomorphism. That is the whole of what remains.

## Implementation notes

The negative first tensor power is, by `Stacks.SheafOfModules.Invertible.tensorPower`, the
image of the structure sheaf under the quasi-inverse of the autoequivalence `· ⊗ L`. So a
module `M` with `M ⊗ L ≅ 𝒪` is identified with it by transporting that isomorphism through the
quasi-inverse and cancelling with the unit of the equivalence; no local structure of `L` and no
coherence of the tensor product is used.

**Both base-change comparisons are stated with an extra hypothesis, and are therefore left
untagged.** Each of the two hypotheses is a result owned by another part of the development,
and neither is on `main`:

* `quotientKernelBaseChangeIso` assumes `PreservesLimit (parallelPair q 0)` for the pullback
  functor, that is, that pullback of sheaves of modules is left exact on the short exact
  sequence `0 → ker q → E → L → 0`. This is true because `L` is invertible, hence flat. The
  comparison itself needs none of that: it exists as `quotientKernelBaseChangeMap`, it is the
  only morphism with the required normalization, and it is an epimorphism. By
  `mono_quotientKernelBaseChangeMap_iff` the hypothesis may be replaced by the single
  statement that pullback carries `ker q ⟶ E` to a monomorphism, which is what
  `quotientKernelBaseChangeIsoOfMono` assumes. Where the quotient happens to be a split
  epimorphism even that is discharged, by
  `preservesLimit_parallelPair_zero_pullback_of_isSplitEpi`.

  The general case is not reachable from what is on `main`. The argument is the split case
  applied on a cover trivializing `L` — which Tag 0B8M now supplies, `L` being invertible
  hence finite locally free of rank one — and then glued. The gluing has no foothold:
  `SheafOfModules.pullback` is defined in Mathlib as `(pushforward φ).leftAdjoint`, and
  `PresheafOfModules.pullback` likewise as a left adjoint obtained from adjoints at each object, so
  neither has a description of its sections, of its restriction to an open, or of its stalks.
  Tag 0B8M is therefore no longer the obstruction; the objectwise description of the pullback
  of sheaves of modules is.
* `inverseQuotientBaseChangeIso` assumes a trivializing pairing
  `g^*(L^{⊗ -1}) ⊗ g^*L ≅ 𝒪_{X'}`. This is the monoidality of the pullback of sheaves of
  modules, Tag 01CD, at the one pair `(L^{⊗ -1}, L)`.

  **That hypothesis is now discharged**, in
  `StacksFrontier/AlgebraicGeometry/InvertibleQuotient/BaseChange.lean`: Tag 01CD is proved
  unconditionally as `Stacks.RingedSpace.isIso_comparison`, so
  `Stacks.Divisors.inverseQuotientBaseChangePairing` builds the pairing and
  `Stacks.Divisors.inverseQuotientBaseChange` is the inverse-line comparison with no
  hypothesis beyond `Q'.L ≅ g^* Q.L`. This clause of Tag 0B3V's base change is therefore
  complete; the hypothesis-taking form is kept here because it also records the
  normalization — the identification is the one determined by the pairing, by
  `isoTensorPowerNegOne_hom_tensor`, and tensoring the conclusion with `g^*L` and composing
  with the canonical trivialization of `Q'.L^{⊗ -1} ⊗ Q'.L` returns the pairing.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry
-- NOTE: inside `namespace Stacks.SheafOfModules.Invertible` the bare name `IsInvertible`
-- resolves to the ENCLOSING namespace's `Stacks.SheafOfModules.IsInvertible` as soon as that
-- constant is in scope, silently overriding this `open` with no ambiguity error — so adding an
-- import could change what those declarations are about. The four uses in that namespace are
-- therefore written out in full. Do not shorten them.
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

namespace Stacks

/-- An additive functor preserves the kernel of a split epimorphism. A section `s` of `q`
splits off `ker q` as the image of the idempotent `𝟙 - q ≫ s`, and the retraction so obtained
is carried along by additivity, so the kernel comparison is invertible.

This is the formal half of the left exactness of pullback on the kernel sequence of an
invertible quotient: that sequence is split *locally*, and the splitting is what the formal
argument consumes. -/
theorem preservesLimit_parallelPair_zero_of_isSplitEpi
    {A : Type*} [Category A] [Preadditive A] {B : Type*} [Category B] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {Z Y : A} (q : Z ⟶ Y) [IsSplitEpi q]
    [HasKernel q] [HasKernel (F.map q)] :
    PreservesLimit (parallelPair q 0) F := by
  have hs : section_ q ≫ q = 𝟙 Y := IsSplitEpi.id q
  have hr0 : (𝟙 Z - q ≫ section_ q) ≫ q = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hs, Category.comp_id, sub_self]
  set r : Z ⟶ kernel q := kernel.lift q (𝟙 Z - q ≫ section_ q) hr0 with hr
  have hri : r ≫ kernel.ι q = 𝟙 Z - q ≫ section_ q := by rw [hr, kernel.lift_ι]
  have hir : kernel.ι q ≫ r = 𝟙 (kernel q) := by
    rw [← cancel_mono (kernel.ι q), Category.assoc, hri, Category.id_comp,
      Preadditive.comp_sub, Category.comp_id, ← Category.assoc, kernel.condition,
      Limits.zero_comp, sub_zero]
  have : IsIso (kernelComparison q F) := by
    refine ⟨kernel.ι (F.map q) ≫ F.map r, ?_, ?_⟩
    · rw [kernelComparison_comp_ι_assoc, ← F.map_comp, hir, F.map_id]
    · rw [← cancel_mono (kernel.ι (F.map q)), Category.assoc, Category.assoc,
        kernelComparison_comp_ι, ← F.map_comp, hri, Category.id_comp,
        F.map_sub, F.map_id, Preadditive.comp_sub, Category.comp_id, F.map_comp,
        ← Category.assoc, kernel.condition, Limits.zero_comp, sub_zero]
  exact PreservesKernel.of_iso_comparison F q

/-- **The kernel comparison of a right exact functor at an epimorphism is an epimorphism.**
If `q` is an epimorphism then it is the cokernel of its own kernel, so a functor preserving
finite colimits carries the kernel sequence `K → Z → Y` to a sequence which is still exact at
the middle term, and exactness there says precisely that the induced map `F K ⟶ ker (F q)` is
surjective.

Only injectivity of the comparison — the vanishing of the first derived functor — can fail.
This is the formal half of the left exactness of a pullback functor on the kernel sequence of
a surjection, available with no hypothesis on the quotient. -/
theorem epi_kernelComparison {A : Type*} [Category A] [Abelian A]
    {B : Type*} [Category B] [Abelian B] (F : A ⥤ B) [F.PreservesZeroMorphisms]
    [PreservesFiniteColimits F] {Z Y : A} (q : Z ⟶ Y) [Epi q] :
    Epi (kernelComparison q F) :=
  ((ShortComplex.exact_kernel q).map_of_epi_of_preservesCokernel F
    inferInstance inferInstance).epi_kernelLift

/-- A right exact functor preserves the kernel of an epimorphism as soon as the kernel
comparison is a monomorphism: the comparison is epi by `Stacks.epi_kernelComparison`, hence
invertible in a balanced category, and a functor whose kernel comparison is invertible
preserves that kernel. So for an epimorphism, left exactness on its kernel sequence is exactly
injectivity of the comparison. -/
theorem preservesLimit_parallelPair_zero_of_mono_kernelComparison
    {A : Type*} [Category A] [Abelian A] {B : Type*} [Category B] [Abelian B]
    (F : A ⥤ B) [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] {Z Y : A} (q : Z ⟶ Y)
    [Epi q] (_hmono : Mono (kernelComparison q F)) :
    PreservesLimit (parallelPair q 0) F :=
  have := epi_kernelComparison F q
  have : IsIso (kernelComparison q F) := isIso_of_mono_of_epi _
  PreservesKernel.of_iso_comparison F q

end Stacks

namespace Stacks.SheafOfModules.Invertible

attribute [local implicit_reducible] TensorSheafification.structureSheaf
  TensorSheafification.sheafify Tensor.sheafTensor

attribute [local irreducible] PresheafOfModules.sheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- A sheaf of modules whose tensor product with an invertible `L` is the structure sheaf is
canonically the negative first tensor power of `L`: transport the trivialization through the
quasi-inverse of the autoequivalence `· ⊗ L` and cancel with the unit of the equivalence. -/
@[ega "II 8.14.12" "partial"]
noncomputable def isoTensorPowerNegOne
    (L M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
    (h : ((Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj L ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    M ≅ tensorPower O hO L (-1) :=
  let e := ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence
  e.unitIso.app M ≪≫ e.inverse.mapIso h

/-- The successor comparison in degree `-1` is the counit of the tensor autoequivalence. -/
theorem powSuccIso_neg_one {A : Type u} [Category.{v} A] (e : A ≌ A) (M : A) :
    powSuccIso e (-1) M = e.counitIso.app M := rfl

/-- The tensor-power successor comparison in degree `-1` is the counit of the tensor
autoequivalence at the structure sheaf. -/
theorem tensorPowerSuccIso_neg_one
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    tensorPowerSuccIso O hO L (-1) =
      ((Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
          L).asEquivalence.counitIso.app
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO)) := rfl

/-- Reindexing a tensor power from `-1 + 1` to `0` is the identity. -/
theorem tensorPowerReindex_neg_one_add_one
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    tensorPowerReindex O hO L (show (-1 : ℤ) + 1 = 0 by omega) = Iso.refl _ := rfl

/-- The composite of the unit of an equivalence at `M` with the image under the quasi-inverse
of an isomorphism `e.functor.obj M ≅ N`, carried back through `e.functor` and the counit at
`N`, is that isomorphism. This is the triangle identity, in the shape in which
`isoTensorPowerNegOne` consumes it. -/
theorem functor_map_inverseMapIso_comp_counit {A : Type*} [Category A] {B : Type*} [Category B]
    (e : A ≌ B) {M : A} {N : B} (k : e.functor.obj M ≅ N) :
    e.functor.map (e.unitIso.app M ≪≫ e.inverse.mapIso k).hom ≫ e.counitIso.hom.app N =
      k.hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [e.counit_naturality k.hom]
  simp

/-- The identification of `M` with `L^{⊗ -1}` is normalized by the trivializing pairing:
tensoring it with `L` carries the canonical trivialization of `L^{⊗ -1} ⊗ L` supplied by
`tensorPowerSuccIso` back to the given pairing. So the identification is not an arbitrary
isomorphism of the two sheaves. -/
theorem isoTensorPowerNegOne_hom_tensor
    (L M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
    (h : ((Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj L ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).map
        (isoTensorPowerNegOne O hO L M h).hom ≫
        (tensorPowerSuccIso O hO L (-1)).hom = h.hom :=
  functor_map_inverseMapIso_comp_counit
    ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence h

end Stacks.SheafOfModules.Invertible

namespace Stacks.Divisors

open Stacks.SheafOfModules.Invertible

/-- A surjection from `E` onto an invertible module sheaf. -/
structure InvertibleQuotient (X : Scheme.{u}) (E : X.Modules) where
  /-- The invertible quotient module. -/
  L : X.Modules
  /-- It is invertible. -/
  invertible : IsInvertible X.presheaf X.ringCatSheaf.2 L
  /-- The quotient map. -/
  q : E ⟶ L
  /-- The quotient map is surjective. -/
  epi : Epi q

/-- Isomorphism of quotient targets commuting with the quotient maps. -/
def InvertibleQuotient.IsEquivalent {X : Scheme.{u}} {E : X.Modules}
    (Q R : InvertibleQuotient X E) : Prop :=
  ∃ α : Q.L ≅ R.L, Q.q ≫ α.hom = R.q

/-- Quotients are identified when their targets are isomorphic over `E`. -/
def invertibleQuotientSetoid (X : Scheme.{u}) (E : X.Modules) :
    Setoid (InvertibleQuotient X E) where
  r := InvertibleQuotient.IsEquivalent
  iseqv := ⟨
    (by intro Q; exact ⟨Iso.refl _, by simp⟩),
    (by intro Q R h; obtain ⟨α, hα⟩ := h
        exact ⟨α.symm, by simp [← hα]⟩),
    (by intro Q R S h₁ h₂
        obtain ⟨α, hα⟩ := h₁
        obtain ⟨β, hβ⟩ := h₂
        exact ⟨α ≪≫ β, by rw [Iso.trans_hom, ← Category.assoc, hα, hβ]⟩)⟩

/-- Isomorphism classes of invertible quotients of `E`. -/
abbrev InvertibleQuotientClass (X : Scheme.{u}) (E : X.Modules) :=
  Quotient (invertibleQuotientSetoid X E)

/-- Pullback of sheaves of modules along a morphism of schemes preserves the kernel of a split
surjection, the pullback functor being additive. -/
theorem preservesLimit_parallelPair_zero_pullback_of_isSplitEpi
    {X X' : Scheme.{u}} (g : X' ⟶ X) {E L : X.Modules} (q : E ⟶ L) [IsSplitEpi q] :
    PreservesLimit (parallelPair q 0) (Scheme.Modules.pullback g) :=
  Stacks.preservesLimit_parallelPair_zero_of_isSplitEpi _ q

/-- Pullback of a quotient kernel is canonically the kernel of the pulled-back quotient. The
comparison is pinned down by its map into the ambient module.

The hypothesis `PreservesLimit (parallelPair Q.q 0)` says that pullback is left exact on the
short exact sequence `0 → ker Q.q → E → Q.L → 0`, which holds because `Q.L` is invertible,
hence flat. -/
noncomputable def quotientKernelBaseChangeIso
    {X X' : Scheme.{u}} (g : X' ⟶ X)
    (E : X.Modules) (E' : X'.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q)
    [PreservesLimit (parallelPair Q.q 0) (Scheme.Modules.pullback g)] :
    { e : (Scheme.Modules.pullback g).obj (kernel Q.q) ≅ kernel Q'.q //
      e.hom ≫ kernel.ι Q'.q =
        (Scheme.Modules.pullback g).map (kernel.ι Q.q) ≫ hE.inv } := by
  have hq' : Q'.q = hE.hom ≫ ((Scheme.Modules.pullback g).map Q.q ≫ hL.inv) := by
    rw [← Category.assoc, ← hq]; simp
  refine ⟨PreservesKernel.iso (Scheme.Modules.pullback g) Q.q ≪≫
    (kernelCompMono ((Scheme.Modules.pullback g).map Q.q) hL.inv).symm ≪≫
    (kernelIsIsoComp hE.hom ((Scheme.Modules.pullback g).map Q.q ≫ hL.inv)).symm ≪≫
    (kernelIsoOfEq hq').symm, ?_⟩
  simp

section KernelBaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) (E' : X'.Modules)
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
  (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
  (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q)

include hE hL hq

/-- The compatibility of the two quotients, read with the comparisons on the other side. -/
theorem quotientBaseChange_comm :
    hE.inv ≫ Q'.q = (Scheme.Modules.pullback g).map Q.q ≫ hL.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, hq, Iso.inv_hom_id_assoc]

/-- The pullback of the inclusion of `ker Q.q`, read into `E'`, lands in `ker Q'.q`. -/
theorem quotientKernelBaseChange_zero :
    ((Scheme.Modules.pullback g).map (kernel.ι Q.q) ≫ hE.inv) ≫ Q'.q = 0 := by
  rw [Category.assoc, quotientBaseChange_comm g E E' hE Q Q' hL hq, ← Category.assoc,
    ← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]

/-- The canonical comparison from the pullback of the kernel of a quotient to the kernel of the
pulled-back quotient. It exists with no hypothesis at all: the pullback of the inclusion of
`ker Q.q`, read into `E'` along `hE`, is killed by `Q'.q`, so it factors through `ker Q'.q`.

This is the map whose invertibility Tag 0B3V's base-change clause asserts;
`Stacks.Divisors.eq_quotientKernelBaseChangeMap` says that it is the only candidate, and
`Stacks.Divisors.epi_quotientKernelBaseChangeMap` that it is always surjective. -/
noncomputable def quotientKernelBaseChangeMap :
    (Scheme.Modules.pullback g).obj (kernel Q.q) ⟶ kernel Q'.q :=
  kernel.lift _ _ (quotientKernelBaseChange_zero g E E' hE Q Q' hL hq)

@[reassoc (attr := simp)]
theorem quotientKernelBaseChangeMap_comp_kernel_ι :
    quotientKernelBaseChangeMap g E E' hE Q Q' hL hq ≫ kernel.ι Q'.q =
      (Scheme.Modules.pullback g).map (kernel.ι Q.q) ≫ hE.inv :=
  kernel.lift_ι _ _ _

/-- The canonical comparison is the unique morphism compatible with the two inclusions into the
ambient modules, `kernel.ι Q'.q` being a monomorphism. So the normalization asked for by Tag
0B3V determines the comparison, and any morphism satisfying it is this one. -/
theorem eq_quotientKernelBaseChangeMap
    (e : (Scheme.Modules.pullback g).obj (kernel Q.q) ⟶ kernel Q'.q)
    (he : e ≫ kernel.ι Q'.q =
      (Scheme.Modules.pullback g).map (kernel.ι Q.q) ≫ hE.inv) :
    e = quotientKernelBaseChangeMap g E E' hE Q Q' hL hq := by
  rw [← cancel_mono (kernel.ι Q'.q), he, quotientKernelBaseChangeMap_comp_kernel_ι]

/-- **The canonical kernel comparison is an epimorphism, with no hypothesis.** Pullback of
sheaves of modules is a left adjoint, hence preserves finite colimits, and `Q.q` is an
epimorphism, so the kernel sequence of `Q.q` stays exact at its middle term after pullback;
that is exactly surjectivity of the comparison.

Half of Tag 0B3V's base-change clause for the quotient kernel is therefore unconditional. What
remains is injectivity, i.e. the vanishing of the first derived functor of pullback on `Q.L`,
and `Stacks.Divisors.quotientKernelBaseChangeIsoOfMono` shows that it is all that remains. -/
theorem epi_quotientKernelBaseChangeMap :
    Epi (quotientKernelBaseChangeMap g E E' hE Q Q' hL hq) := by
  have := Q.epi
  have hS := (ShortComplex.exact_kernel Q.q).map_of_epi_of_preservesCokernel
    (Scheme.Modules.pullback g) inferInstance inferInstance
  have hS' : (ShortComplex.mk
      ((Scheme.Modules.pullback g).map (kernel.ι Q.q) ≫ hE.inv) Q'.q
      (quotientKernelBaseChange_zero g E E' hE Q Q' hL hq)).Exact := by
    refine ShortComplex.exact_of_iso ?_ hS
    exact ShortComplex.isoMk (Iso.refl _) hE.symm hL.symm (by simp)
      (by simpa using quotientBaseChange_comm g E E' hE Q Q' hL hq)
  exact hS'.epi_kernelLift

/-- **Injectivity of the comparison is injectivity of the pulled-back kernel inclusion.** The
comparison composed with `kernel.ι Q'.q` is the pullback of `kernel.ι Q.q` read into `E'`, and
`kernel.ι Q'.q` is a monomorphism, so each of the two is a monomorphism exactly when the other
is.

This puts the one missing half of Tag 0B3V's base-change clause for the quotient kernel in its
sharpest form: all that is needed is that pullback of sheaves of modules carries the inclusion
`ker Q.q ⟶ E` to a monomorphism — nothing about the comparison, the second quotient, or the
three comparison isomorphisms. -/
theorem mono_quotientKernelBaseChangeMap_iff :
    Mono (quotientKernelBaseChangeMap g E E' hE Q Q' hL hq) ↔
      Mono ((Scheme.Modules.pullback g).map (kernel.ι Q.q)) := by
  constructor
  · intro _
    have h : (Scheme.Modules.pullback g).map (kernel.ι Q.q) =
        quotientKernelBaseChangeMap g E E' hE Q Q' hL hq ≫ kernel.ι Q'.q ≫ hE.hom := by
      rw [← Category.assoc, quotientKernelBaseChangeMap_comp_kernel_ι, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    rw [h]
    infer_instance
  · intro _
    have h : Mono (quotientKernelBaseChangeMap g E E' hE Q Q' hL hq ≫ kernel.ι Q'.q) := by
      rw [quotientKernelBaseChangeMap_comp_kernel_ι]
      infer_instance
    exact mono_of_mono _ (kernel.ι Q'.q)

/-- The canonical comparison is invertible as soon as it is a monomorphism: it is always an
epimorphism, and sheaves of modules form a balanced category. -/
theorem isIso_quotientKernelBaseChangeMap_of_mono
    (hmono : Mono (quotientKernelBaseChangeMap g E E' hE Q Q' hL hq)) :
    IsIso (quotientKernelBaseChangeMap g E E' hE Q Q' hL hq) :=
  have := epi_quotientKernelBaseChangeMap g E E' hE Q Q' hL hq
  isIso_of_mono_of_epi _

/-- Tag 0B3V's comparison of the quotient kernel with the kernel of the pulled-back quotient,
assuming only that the canonical comparison is a monomorphism. This is weaker than the
left exactness hypothesis of `Stacks.Divisors.quotientKernelBaseChangeIso`, and it is the
whole of what is missing: by `Stacks.Divisors.epi_quotientKernelBaseChangeMap` the comparison
is already surjective. Left untagged, the hypothesis being an addition to the tag. -/
noncomputable def quotientKernelBaseChangeIsoOfMono
    (hmono : Mono (quotientKernelBaseChangeMap g E E' hE Q Q' hL hq)) :
    { e : (Scheme.Modules.pullback g).obj (kernel Q.q) ≅ kernel Q'.q //
      e.hom ≫ kernel.ι Q'.q =
        (Scheme.Modules.pullback g).map (kernel.ι Q.q) ≫ hE.inv } :=
  have := isIso_quotientKernelBaseChangeMap_of_mono g E E' hE Q Q' hL hq hmono
  ⟨asIso (quotientKernelBaseChangeMap g E E' hE Q Q' hL hq), by simp⟩

/-- The left exact comparison of `Stacks.Divisors.quotientKernelBaseChangeIso` is the canonical
one: it satisfies the normalization, and the normalization determines the morphism. -/
theorem quotientKernelBaseChangeIso_hom
    [PreservesLimit (parallelPair Q.q 0) (Scheme.Modules.pullback g)] :
    (quotientKernelBaseChangeIso g E E' hE Q Q' hL hq).1.hom =
      quotientKernelBaseChangeMap g E E' hE Q Q' hL hq :=
  eq_quotientKernelBaseChangeMap g E E' hE Q Q' hL hq _
    (quotientKernelBaseChangeIso g E E' hE Q Q' hL hq).2

end KernelBaseChange

/-- The inverse-line comparison induced by an isomorphism of quotient line bundles.

The hypothesis `hpair` is the monoidality of the pullback of sheaves of modules at the pair
`(Q.L^{⊗ -1}, Q.L)` — Tag 01CD — combined with the triviality of the pullback of the structure
sheaf. -/
noncomputable def inverseQuotientBaseChangeIso
    {X X' : Scheme.{u}} (g : X' ⟶ X)
    (E : X.Modules) (E' : X'.Modules)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hpair : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X'.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X'.presheaf
        (forget₂ CommRingCat RingCat) X'.ringCatSheaf.2⟩).obj ((Scheme.Modules.pullback g).obj
          (letI := Q.invertible
           tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)))).obj
             ((Scheme.Modules.pullback g).obj Q.L) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf X'.presheaf
        X'.ringCatSheaf.2)) :
    (Scheme.Modules.pullback g).obj
      (letI := Q.invertible
       tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) ≅
      (letI := Q'.invertible
       tensorPower X'.presheaf X'.ringCatSheaf.2 Q'.L (-1)) :=
  letI := Q.invertible
  letI := Q'.invertible
  isoTensorPowerNegOne X'.presheaf X'.ringCatSheaf.2 Q'.L _
    (tensorProductIso X'.presheaf X'.ringCatSheaf.2 (Iso.refl _) hL ≪≫ hpair)

end Stacks.Divisors
