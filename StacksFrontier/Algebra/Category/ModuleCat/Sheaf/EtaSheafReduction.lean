module

public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafBockstein

import StacksCore.Tactic.StacksAttribute

/-!
# The décalage of an invertible ideal, reduced modulo that ideal

Let `(X, O_X)` be a ringed space, `ι : I ⟶ O_X` an invertible ideal subsheaf, and `F` a cochain
complex of `I`-torsion-free `O_X`-modules.  This file builds the comparison between the
reduction `η_I F ⊗ O_X/I` of the Berthelot–Ogus décalage and the complex whose degree-`n` term
is the `n`-th cohomology sheaf of `F ⊗ I^n/I^{n+1}`.

## Main definitions

* `modIdeal`: the reduction `M/IM` of an `O_X`-module modulo the ideal, as the cokernel of
  multiplication by `I`, and `modIdealMap` its functoriality.
* `etaModIdealComplex`: the reduction `η_I F ⊗ O_X/I` of the décalage, as a complex.  This is
  the left-hand side of Tag 0GT9 at the level of complexes.
* `gradedComplex`: the complex `F ⊗ I^n/I^{n+1}`, with degree-`k` term the cokernel of the
  ideal-power inclusion `I^{⊗ (n+1)} ⊗ F^k ⟶ I^{⊗ n} ⊗ F^k`.
* `etaToGradedCycles` and `etaToGradedHomology`: the comparison
  `(η_I F)^n ⟶ Z^n(F ⊗ I^n/I^{n+1}) ⟶ H^n(F ⊗ I^n/I^{n+1})`, the first projection of the fibre
  product defining `(η_I F)^n` read as a cocycle and then as a cocycle class.
* `reductionComparison`: the induced map `(η_I F)^n/I (η_I F)^n ⟶ H^n(F ⊗ I^n/I^{n+1})`, the
  degreewise comparison of Tag 0GT9.

## Main results

* `etaToGraded_comp_d`: the first projection of `(η_I F)^n` is a cocycle of
  `F ⊗ I^n/I^{n+1}`, because the defining fibre-product square says its differential lands in
  the next ideal power.
* `idealPowerIncl_comp_etaToGraded`: multiplication by the ideal kills that cocycle class, so
  the comparison descends to the reduction `(η_I F)^n/I (η_I F)^n`.
* `mono_idealPowerIncl_etaTerm`: multiplication by `I` is injective on `(η_I F)^n`, so the
  décalage is again termwise `I`-torsion-free.  This is what lets `η_I F ⊗ O_X/I` be computed
  by the ordinary tensor product.
* `epi_etaToGradedCycles`, `epi_etaToGradedHomology` and `epi_reductionComparison`: the
  comparison is surjective in every degree.  The degree-`n` cocycles of `F ⊗ I^n/I^{n+1}` are
  exactly the classes of sections of the décalage, because the fibre product defining
  `(η_I F)^n` is the preimage of the next ideal power under the twisted differential.

## Implementation notes

The reduction `M ⊗ O_X/I` is spelled as the cokernel of `idealPowerIncl X I ι 0 M`,
multiplication by the ideal; at `M = O_X` that cokernel is `Bockstein.powerQuotient X I ι 0`,
the object the derived statement of Tag 0GT9 tensors with, and `modIdeal_unit` records that
the two agree.

The comparison is the map the source writes down: a local section `s` of `(η_I F)^n` is
`f^n s'` for a local generator `f` of the ideal, and is sent to the class of `f^n s'` in
`H^n(F ⊗ I^n/I^{n+1})`.  Categorically this is the first projection of the fibre product
defining `(η_I F)^n`, pushed into the successive quotient; `etaToGraded_comp_d` is the
source's observation that the differential kills it, and `idealPowerIncl_comp_etaToGraded` is
the source's observation that a section of `I (η_I F)^n` lies in `I^{⊗ (n+1)} ⊗ F^n`.  No
choice is made anywhere: `reductionComparison` is a `cokernel.desc`, pinned by
`cokernel_π_reductionComparison`.

Naturality of the ideal-power inclusion and the factorization of `idealPowerIncl X I ι n M`
through `idealPowerIncl X I ι 0 (I^{⊗ n} ⊗ M)` are reproved here from the public tensor-power
calculus: `EtaSheaf.lean` has the first privately and the second only inside the proof of
`idealPowerIncl_mono`, and `EtaSheafQuasiIso.lean` already reproves the first for the same
reason.  As there, the steps that `rw` cannot match — the two spellings of the structure sheaf
of rings agree only at `default` transparency — are supplied as chains of ground equations,
and `Mono` hypotheses are passed to `monoComp'` and `monoOfComp` explicitly because instance
search does not see a context hypothesis stated in the other spelling.

### Relation to Tag 0GT9

Tag 0GT9 is a canonical isomorphism `Lη_I M ⊗^L O_X/I ≅ H^•(M/I)` in `D(O_X)`.  The degreewise
comparison built here, together with its surjectivity, is the first step of the source's proof.
`EtaSheafBocksteinChain.lean` assembles it into the morphism of complexes
`Reduction.reductionComparisonChainMap`, using the chain-level Bockstein differential of the
short exact sequence `0 → F ⊗ I^{n+1}/I^{n+2} → F ⊗ I^n/I^{n+2} → F ⊗ I^n/I^{n+1} → 0`;
`EtaSheafReductionDerivedIso.lean` takes its image `Reduction.reductionComparisonQ` in
`D(O_X)`; and `EtaSheafReductionDerivedIsoRegular.lean` proves that arrow invertible in
Situation 0GT4.  The inputs here are `Mono ι`, invertibility of `I` (condition (2) of Tag 0GT3)
and termwise `I`-torsion-freeness of `F`, which is what `Eta.etaObj` itself requires.

`Bockstein.bocksteinTermIsoHomology` of `EtaSheafPowerQuotientResolution.lean` computes the term
`H^n(M ⊗^L I^n/I^{n+1})` of the Bockstein complex of Tag 0GT8 at `M = F` as the degree-`n`
homology of `Tot(F ⊗ [I^{n+1} ⟶ I^n])`, through the K-flat resolution `[I^{n+1} ⟶ I^n]` of
`I^n/I^{n+1}`.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 0GT8](https://stacks.math.columbia.edu/tag/0GT8)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 0F7T](https://stacks.math.columbia.edu/tag/0F7T)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.SheafOfModules.Invertible ( tensorRightFunctor_isEquivalence
  tensorPowerEquivalence powSuccIso powSuccIso_natural
  tensorProductRightUnitor)

universe u v w

namespace Stacks.IdealTorsion.Reduction

open Stacks.IdealTorsion.Eta

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ### Monomorphisms, with every argument explicit

The two spellings of the structure sheaf of rings agree only at `default` transparency, so a
`Mono` hypothesis in the context is invisible to instance search once a rewrite has put the
goal in the other spelling.  These three wrappers take the hypotheses as explicit arguments.
-/

private lemma monoIsoHom {A : Type*} [Category A] {Y Z : A} (α : Y ≅ Z) : Mono α.hom :=
  inferInstance

private lemma monoComp' {A : Type*} [Category A] {Y Z W : A} (f : Y ⟶ Z) (g : Z ⟶ W)
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) := by
  have := hf
  have := hg
  exact mono_comp f g

private lemma monoOfComp {A : Type*} [Category A] {Y Z W : A} (f : Y ⟶ Z) (g : Z ⟶ W)
    (h : Mono (f ≫ g)) : Mono f := by
  have := h
  exact mono_of_mono f g

/-! ### The tensor-power calculus reproved from its public interface -/





/-- The ideal-power inclusion in degree `n` is multiplication by the ideal on the `n`-th
twist, read through the comparison of successive tensor powers. -/
private lemma inclEq
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (n : ℤ) :
    idealPowerIncl X I ι n M =
      (powSuccIso (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Oₓ).property I)) n M).inv ≫
        idealPowerIncl X I ι 0 (idealPowerTerm X I n M) := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I
  have : T.IsEquivalence := tensorRightFunctor_isEquivalence X.sheaf.obj (Oₓ).property I
  let P := idealPowerTerm X I n M
  let c : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).obj P).obj I ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).obj P).obj 𝒪 :=
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)))).map
      (X := (P, I)) (Y := (P, 𝒪)) (𝟙 P, ι)
  let r : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).obj P).obj 𝒪 ⟶
        P :=
    (tensorProductRightUnitor X.sheaf.obj (Oₓ).property P).hom
  show (powSuccIso T.asEquivalence n M).inv ≫ c ≫ r =
    (powSuccIso T.asEquivalence n M).inv ≫ (𝟙 _ ≫ c ≫ r)
  rw [Category.id_comp]

/-! ### The successive quotient `F ⊗ I^n/I^{n+1}` as a complex -/

/-- The degree-`k` term of `F ⊗ I^n/I^{n+1}`: the quotient of `I^{⊗ n} ⊗ F^k` by the image of
the next ideal power. -/
public noncomputable abbrev gradedTerm
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) : SheafOfModules.{u} Oₓ :=
  cokernel (idealPowerIncl X I ι n (F.X k))

/-- The differential of `F ⊗ I^n/I^{n+1}`, induced by the `n`-th twist of the differential of
`F`. -/
public noncomputable def gradedD
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    gradedTerm X I ι F n k ⟶ gradedTerm X I ι F n (k + 1) :=
  cokernel.desc (idealPowerIncl X I ι n (F.X k))
    (idealPowerMap X I n (F.d k (k + 1)) ≫
      cokernel.π (idealPowerIncl X I ι n (F.X (k + 1))))
    (by
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun g => g ≫
        cokernel.π (idealPowerIncl X I ι n (F.X (k + 1))))
        (idealPowerIncl_natural X I ι n (F.d k (k + 1)))) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (idealPowerMap X I (n + 1) (F.d k (k + 1)) ≫ ·)
        (cokernel.condition (idealPowerIncl X I ι n (F.X (k + 1))))) ?_
      exact comp_zero)

@[simp] public theorem cokernel_π_gradedD
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    cokernel.π (idealPowerIncl X I ι n (F.X k)) ≫ gradedD X I ι F n k =
      idealPowerMap X I n (F.d k (k + 1)) ≫
        cokernel.π (idealPowerIncl X I ι n (F.X (k + 1))) :=
  cokernel.π_desc _ _ _

public theorem gradedD_comp_gradedD
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    gradedD X I ι F n k ≫ gradedD X I ι F n (k + 1) = 0 := by
  refine (cancel_epi (cokernel.π (idealPowerIncl X I ι n (F.X k)))).1 ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ gradedD X I ι F n (k + 1))
    (cokernel_π_gradedD X I ι F n k)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (idealPowerMap X I n (F.d k (k + 1)) ≫ ·)
    (cokernel_π_gradedD X I ι F n (k + 1))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫
      cokernel.π (idealPowerIncl X I ι n (F.X (k + 1 + 1))))
    (idealPowerMap_comp X I n (F.d k (k + 1)) (F.d (k + 1) (k + 1 + 1))).symm) ?_
  refine Eq.trans (congrArg (fun g => idealPowerMap X I n g ≫
      cokernel.π (idealPowerIncl X I ι n (F.X (k + 1 + 1))))
    (F.d_comp_d k (k + 1) (k + 1 + 1))) ?_
  refine Eq.trans (congrArg (fun g => g ≫
      cokernel.π (idealPowerIncl X I ι n (F.X (k + 1 + 1))))
    (idealPowerMap_zero X I n (F.X k) (F.X (k + 1 + 1)))) ?_
  exact (zero_comp).trans (comp_zero (f := cokernel.π
    (idealPowerIncl X I ι n (F.X k)))).symm

/-- The complex `F ⊗ I^n/I^{n+1}`, whose degree-`n` cohomology sheaf is the degree-`n` term of
the Bockstein complex of Tag 0GT8. -/
public noncomputable def gradedComplex
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    CochainComplex (SheafOfModules.{u} Oₓ) ℤ :=
  CochainComplex.of (gradedTerm X I ι F n) (gradedD X I ι F n) (gradedD_comp_gradedD X I ι F n)

@[simp] public theorem gradedComplex_X
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    (gradedComplex X I ι F n).X k = gradedTerm X I ι F n k := rfl

public theorem gradedComplex_d
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    (gradedComplex X I ι F n).d k (k + 1) = gradedD X I ι F n k := by
  simp only [gradedComplex, CochainComplex.of_d]

/-! ### The reduction of a module modulo the ideal -/

/-- The reduction `M/IM` of an `O_X`-module modulo the ideal: the cokernel of multiplication
by `I`.  At `M = O_X` this is `Bockstein.powerQuotient X I ι 0`, the sheaf `O_X/I`. -/
@[sga "2 IX 2.2" "more general"]
public noncomputable abbrev modIdeal
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) : SheafOfModules.{u} Oₓ :=
  cokernel (idealPowerIncl X I ι 0 M)

/-! ### The comparison -/

/-- The first projection of the fibre product defining `(η_I F)^n`, read in the degree-`n` term
of `F ⊗ I^n/I^{n+1}`. -/
public noncomputable abbrev etaToGraded
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaTerm X I ι F n ⟶ gradedTerm X I ι F n n :=
  pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
      (idealPowerIncl X I ι n (F.X (n + 1))) ≫
    cokernel.π (idealPowerIncl X I ι n (F.X n))

/-- **The first projection of `(η_I F)^n` is a cocycle of `F ⊗ I^n/I^{n+1}`.**  The defining
fibre-product square says its differential lands in `I^{⊗ (n+1)} ⊗ F^{n+1}`, which is exactly
what is divided out in degree `n + 1`. -/
public theorem etaToGraded_comp_d
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaToGraded X I ι F n ≫ gradedD X I ι F n n = 0 := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
      (idealPowerIncl X I ι n (F.X (n + 1))) ≫ ·)
    (cokernel_π_gradedD X I ι F n n)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫
      cokernel.π (idealPowerIncl X I ι n (F.X (n + 1))))
    (pullback.condition (f := idealPowerMap X I n (F.d n (n + 1)))
      (g := idealPowerIncl X I ι n (F.X (n + 1))))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (pullback.snd (idealPowerMap X I n (F.d n (n + 1)))
      (idealPowerIncl X I ι n (F.X (n + 1))) ≫ ·)
    (cokernel.condition (idealPowerIncl X I ι n (F.X (n + 1))))) ?_
  exact comp_zero

/-- The comparison `(η_I F)^n ⟶ Z^n(F ⊗ I^n/I^{n+1})`: the first projection of the fibre
product defining `(η_I F)^n`, read as a cocycle of `F ⊗ I^n/I^{n+1}`. -/
public noncomputable def etaToGradedCycles
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaTerm X I ι F n ⟶ (gradedComplex X I ι F n).cycles n :=
  (gradedComplex X I ι F n).liftCycles (i := n) (etaToGraded X I ι F n) (n + 1)
    (by simp) (by
      refine Eq.trans (congrArg (etaToGraded X I ι F n ≫ ·)
        (gradedComplex_d X I ι F n n)) ?_
      exact etaToGraded_comp_d X I ι F n)

@[simp] public theorem etaToGradedCycles_i
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaToGradedCycles X I ι F n ≫ (gradedComplex X I ι F n).iCycles n =
      etaToGraded X I ι F n :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The comparison `(η_I F)^n ⟶ H^n(F ⊗ I^n/I^{n+1})`: the cocycle class of the first
projection of the fibre product defining `(η_I F)^n`.  This is the map the source writes as
`s = f^n s' ↦ [f^n s']`. -/
public noncomputable def etaToGradedHomology
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaTerm X I ι F n ⟶ (gradedComplex X I ι F n).homology n :=
  etaToGradedCycles X I ι F n ≫ (gradedComplex X I ι F n).homologyπ n

public theorem etaToGradedCycles_comp_homologyπ
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaToGradedCycles X I ι F n ≫ (gradedComplex X I ι F n).homologyπ n =
      etaToGradedHomology X I ι F n := rfl

/-- The zeroth twist is the identity on morphisms. -/
private lemma pmIdZero (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {M N : SheafOfModules.{u} Oₓ} (f : M ⟶ N) : idealPowerMap X I 0 f = f := rfl

/-- Multiplication by the ideal on a subobject, read in the ambient module: naturality turns it
into a composite of two monomorphisms. -/
private lemma inclZeroNat
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {M N : SheafOfModules.{u} Oₓ} (p : M ⟶ N) :
    idealPowerIncl X I ι 0 M ≫ p =
      idealPowerMap X I (0 + 1) p ≫ idealPowerIncl X I ι 0 N := by
  have h := idealPowerIncl_natural X I ι 0 p
  rw [pmIdZero] at h
  exact h

/-- Multiplication by the ideal on the `n`-th twist is the `n`-th ideal-power inclusion, read
through the comparison of successive tensor powers. -/
private lemma inclZeroPow_eq
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (n : ℤ) :
    idealPowerIncl X I ι 0 (idealPowerTerm X I n M) =
      (powSuccIso (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Oₓ).property I)) n M).hom ≫
        idealPowerIncl X I ι n M := by
  have _he : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj
        I).IsEquivalence :=
    tensorRightFunctor_isEquivalence X.sheaf.obj (Oₓ).property I
  rw [inclEq X I ι M n]
  exact (Iso.hom_inv_id_assoc _ _).symm

/-- Multiplication by the ideal on the `n`-th twist lands in the image of the `(n+1)`-st ideal
power, so it dies in the successive quotient. -/
private lemma inclZeroPow_comp_cokernelπ
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (n : ℤ) :
    idealPowerIncl X I ι 0 (idealPowerTerm X I n M) ≫
        cokernel.π (idealPowerIncl X I ι n M) = 0 := by
  have _he : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj
        I).IsEquivalence :=
    tensorRightFunctor_isEquivalence X.sheaf.obj (Oₓ).property I
  rw [inclZeroPow_eq X I ι M n]
  exact (Category.assoc _ _ _).trans ((congrArg _ (cokernel.condition _)).trans comp_zero)

/-- **Multiplication by the ideal kills the comparison.**  A section of `I (η_I F)^n` lies in
`I^{⊗ (n+1)} ⊗ F^n`, which is what is divided out in the degree-`n` term of
`F ⊗ I^n/I^{n+1}`. -/
public theorem idealPowerIncl_comp_etaToGraded
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    idealPowerIncl X I ι 0 (etaTerm X I ι F n) ≫ etaToGraded X I ι F n = 0 := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (inclZeroNat X I ι _)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg _ (inclZeroPow_comp_cokernelπ X I ι _ n)).trans
    comp_zero)

/-- **The comparison of Tag 0GT9 at the level of complexes, in degree `n`:** the reduction
`(η_I F)^n/I (η_I F)^n` maps to the `n`-th cohomology sheaf of `F ⊗ I^n/I^{n+1}` by sending a
section of the décalage to its cocycle class.

This is the canonical comparison of the tag, in degree `n` and at the level of complexes.  Here
it is shown surjective (`epi_reductionComparison`); the tag's assertion that the induced arrow
of `D(O_X)` is invertible is proved in Situation 0GT4 in
`EtaSheafReductionDerivedIsoRegular.lean`, as
`isIso_reductionComparisonQ_of_isLocallyGeneratedByRegular`. -/
public noncomputable def reductionComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    modIdeal X I ι (etaTerm X I ι F n) ⟶ (gradedComplex X I ι F n).homology n :=
  cokernel.desc (idealPowerIncl X I ι 0 (etaTerm X I ι F n)) (etaToGradedHomology X I ι F n)
    (by
      refine Eq.trans (congrArg (idealPowerIncl X I ι 0 (etaTerm X I ι F n) ≫ ·)
        (etaToGradedCycles_comp_homologyπ X I ι F n).symm) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun g => g ≫ (gradedComplex X I ι F n).homologyπ n) ?_)
        zero_comp
      refine (cancel_mono ((gradedComplex X I ι F n).iCycles n)).1 ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (idealPowerIncl X I ι 0 (etaTerm X I ι F n) ≫ ·)
        (etaToGradedCycles_i X I ι F n)) ?_
      exact (idealPowerIncl_comp_etaToGraded X I ι F n).trans zero_comp.symm)

@[simp] public theorem cokernel_π_reductionComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n)) ≫
        reductionComparison X I ι F n = etaToGradedHomology X I ι F n :=
  cokernel.π_desc _ _ _

/-! ### The décalage is again termwise torsion-free -/

/-- Multiplication by the ideal is injective on a subobject of a module on which it is
injective. -/
private lemma monoInclZero_of_mono
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {M N : SheafOfModules.{u} Oₓ} (p : M ⟶ N) (hp : Mono p)
    (hN : Mono (idealPowerIncl X I ι 0 N)) :
    Mono (idealPowerIncl X I ι 0 M) := by
  have hT : Mono (idealPowerMap X I (0 + 1) p) :=
    @Functor.PreservesMonomorphisms.preserves _ _ _ _
      (tensorPowerEquivalence X.sheaf.obj (Oₓ).property I (0 + 1)).functor
      (Functor.preservesMonomorphisms_of_adjunction
        (tensorPowerEquivalence X.sheaf.obj (Oₓ).property I (0 + 1)).symm.toAdjunction) M N p hp
  have hcomp : Mono (idealPowerIncl X I ι 0 M ≫ p) := by
    rw [inclZeroNat X I ι p]
    exact monoComp' _ _ hT hN
  exact monoOfComp (idealPowerIncl X I ι 0 M) p hcomp

/-- Multiplication by the ideal on the `n`-th twist is the `n`-th ideal-power inclusion read
through the comparison of successive tensor powers, hence a monomorphism whenever that
inclusion is one. -/
private lemma monoInclZeroPow
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (n : ℤ) (hM : Mono (idealPowerIncl X I ι n M)) :
    Mono (idealPowerIncl X I ι 0 (idealPowerTerm X I n M)) := by
  have _he : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj
        I).IsEquivalence :=
    tensorRightFunctor_isEquivalence X.sheaf.obj (Oₓ).property I
  rw [inclZeroPow_eq X I ι M n]
  exact monoComp' _ _ (monoIsoHom _) hM

/-- **Multiplication by the ideal is injective on the terms of the décalage.**  The degree-`n`
term is a subobject of `I^{⊗ n} ⊗ F^n`, on which multiplication by the ideal is injective
because `F^n` is `I`-torsion-free.  This is what lets `η_I F ⊗ O_X/I` be computed by the
ordinary tensor product. -/
public theorem mono_idealPowerIncl_etaTerm
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    Mono (idealPowerIncl X I ι 0 (etaTerm X I ι F n)) := by
  have _hm1 : Mono (idealPowerIncl X I ι n (F.X (n + 1))) :=
    idealPowerIncl_mono X I ι (F.X (n + 1)) (hF (n + 1)) n
  refine monoInclZero_of_mono X I ι
    (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
      (idealPowerIncl X I ι n (F.X (n + 1)))) inferInstance ?_
  exact monoInclZeroPow X I ι (F.X n) n (idealPowerIncl_mono X I ι (F.X n) (hF n) n)

/-! ### The reduced décalage as a complex -/

/-- At the structure sheaf the reduction is `O_X/I`, the sheaf the derived statement of Tag
0GT9 tensors with. -/
public theorem modIdeal_unit
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I] :
    modIdeal X I ι 𝒪 = Stacks.IdealTorsion.Bockstein.powerQuotient X I ι 0 := rfl

/-- The reduction of a morphism modulo the ideal. -/
public noncomputable def modIdealMap
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {M N : SheafOfModules.{u} Oₓ} (f : M ⟶ N) :
    modIdeal X I ι M ⟶ modIdeal X I ι N :=
  cokernel.desc (idealPowerIncl X I ι 0 M) (f ≫ cokernel.π (idealPowerIncl X I ι 0 N))
    (by
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun g => g ≫ cokernel.π (idealPowerIncl X I ι 0 N))
        (inclZeroNat X I ι f)) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (idealPowerMap X I (0 + 1) f ≫ ·)
        (cokernel.condition (idealPowerIncl X I ι 0 N))) ?_
      exact comp_zero)

@[simp] public theorem cokernel_π_modIdealMap
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {M N : SheafOfModules.{u} Oₓ} (f : M ⟶ N) :
    cokernel.π (idealPowerIncl X I ι 0 M) ≫ modIdealMap X I ι f =
      f ≫ cokernel.π (idealPowerIncl X I ι 0 N) :=
  cokernel.π_desc _ _ _

public theorem modIdealMap_comp
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {M N P : SheafOfModules.{u} Oₓ} (f : M ⟶ N) (g : N ⟶ P) :
    modIdealMap X I ι (f ≫ g) = modIdealMap X I ι f ≫ modIdealMap X I ι g := by
  refine (cancel_epi (cokernel.π (idealPowerIncl X I ι 0 M))).1 ?_
  refine Eq.trans (cokernel_π_modIdealMap X I ι (f ≫ g)) ?_
  refine Eq.trans (Category.assoc f g (cokernel.π (idealPowerIncl X I ι 0 P))) ?_
  refine Eq.trans (congrArg (f ≫ ·) (cokernel_π_modIdealMap X I ι g).symm) ?_
  refine Eq.trans (Category.assoc f (cokernel.π (idealPowerIncl X I ι 0 N))
    (modIdealMap X I ι g)).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ modIdealMap X I ι g)
    (cokernel_π_modIdealMap X I ι f).symm) ?_
  exact Category.assoc _ _ _

public theorem modIdealMap_zero
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M N : SheafOfModules.{u} Oₓ) :
    modIdealMap X I ι (0 : M ⟶ N) = 0 := by
  refine (cancel_epi (cokernel.π (idealPowerIncl X I ι 0 M))).1 ?_
  refine Eq.trans (cokernel_π_modIdealMap X I ι (0 : M ⟶ N)) ?_
  exact zero_comp.trans comp_zero.symm

/-- **The reduction `η_I F ⊗ O_X/I` of the décalage, as a complex.**  Its degree-`n` term is
`(η_I F)^n/I (η_I F)^n` and its differential is the reduction of the differential of the
décalage.  This is the left-hand side of Tag 0GT9 at the level of complexes. -/
public noncomputable def etaModIdealComplex
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) :
    CochainComplex (SheafOfModules.{u} Oₓ) ℤ :=
  CochainComplex.of (fun n => modIdeal X I ι (etaTerm X I ι F n))
    (fun n => modIdealMap X I ι ((etaObj X I ι F hF).d n (n + 1)))
    (fun n => by
      refine Eq.trans (modIdealMap_comp X I ι ((etaObj X I ι F hF).d n (n + 1))
        ((etaObj X I ι F hF).d (n + 1) (n + 1 + 1))).symm ?_
      refine Eq.trans (congrArg (modIdealMap X I ι)
        ((etaObj X I ι F hF).d_comp_d n (n + 1) (n + 1 + 1))) ?_
      exact modIdealMap_zero X I ι _ _)

@[simp] public theorem etaModIdealComplex_X
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) (n : ℤ) :
    (etaModIdealComplex X I ι F hF).X n = modIdeal X I ι (etaTerm X I ι F n) := rfl

public theorem etaModIdealComplex_d
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) (n : ℤ) :
    (etaModIdealComplex X I ι F hF).d n (n + 1) =
      modIdealMap X I ι ((etaObj X I ι F hF).d n (n + 1)) := by
  simp only [etaModIdealComplex, CochainComplex.of_d]
  rfl

/-! ### The comparison is surjective

The cocycles of `F ⊗ I^n/I^{n+1}` in degree `n` are exactly the image of the décalage: the
fibre product defining `(η_I F)^n` is the preimage of the next ideal power under the twisted
differential, and the degree-`n` cocycle condition in the successive quotient says precisely
that the twisted differential lands in that ideal power.  So the comparison is surjective
already on cocycles, hence on cohomology.  The word "preimage" is available in an abelian
category on pseudoelements, which is where the argument is run.  Pseudoelements are written
out as `Abelian.Pseudoelement` and applied with `pseudoApply` rather than through the two
coercions, which do not survive the two spellings of the structure sheaf of rings.
-/

open CategoryTheory.Abelian.Pseudoelement (pseudoApply pseudo_pullback
  pseudo_surjective_of_epi pseudo_exact_of_exact pseudo_injective_of_mono
  epi_of_pseudo_surjective)

/-- In an abelian category the fibre product `a⁻¹(K')` of `a : A₀ ⟶ B` along a monomorphism
`k : K' ⟶ B` surjects onto the kernel of the map `A₀/K ⟶ B/K'` induced by `a`: a pseudoelement
of `A₀/K` that the induced map kills lifts to `A₀`, the lift's image under `a` lies in `K'`,
and the two together are a pseudoelement of the fibre product. -/
private lemma exists_pullback_pseudoelement
    {A : Type w} [Category.{v} A] [Abelian A]
    {A₀ B K K' : A} (a : A₀ ⟶ B) (j : K ⟶ A₀) (k : K' ⟶ B) (hk : Mono k)
    (dbar : cokernel j ⟶ cokernel k)
    (hd : cokernel.π j ≫ dbar = a ≫ cokernel.π k)
    (w : Abelian.Pseudoelement (cokernel j))
    (hw : pseudoApply dbar w = 0) :
    ∃ p : Abelian.Pseudoelement (pullback a k),
      pseudoApply (pullback.fst a k ≫ cokernel.π j) p = w := by
  have _hk := hk
  obtain ⟨x, hx⟩ := pseudo_surjective_of_epi (cokernel.π j) w
  have h1 : pseudoApply (cokernel.π j ≫ dbar) x = pseudoApply (a ≫ cokernel.π k) x := by
    rw [hd]
  rw [Abelian.Pseudoelement.comp_apply, Abelian.Pseudoelement.comp_apply, hx, hw] at h1
  obtain ⟨y, hy⟩ := pseudo_exact_of_exact (ShortComplex.cokernelSequence_exact k)
    (pseudoApply a x) h1.symm
  obtain ⟨p, hp, -⟩ := pseudo_pullback (f := a) (g := k) (p := x) (q := y) hy.symm
  refine ⟨p, ?_⟩
  rw [Abelian.Pseudoelement.comp_apply, hp]
  exact hx

/-- **The comparison is surjective onto the cocycles.**  Every degree-`n` cocycle of
`F ⊗ I^n/I^{n+1}` is the class of a section of the décalage: a section of `I^{⊗ n} ⊗ F^n`
whose twisted differential dies in `F ⊗ I^n/I^{n+1}` has that differential in
`I^{⊗ (n+1)} ⊗ F^{n+1}`, which is the defining condition of the fibre product. -/
public theorem epi_etaToGradedCycles
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    Epi (etaToGradedCycles X I ι F n) := by
  have hk : Mono (idealPowerIncl X I ι n (F.X (n + 1))) :=
    idealPowerIncl_mono X I ι (F.X (n + 1)) (hF (n + 1)) n
  refine epi_of_pseudo_surjective _ ?_
  intro c
  have h0 : (gradedComplex X I ι F n).iCycles n ≫ gradedD X I ι F n n = 0 := by
    refine Eq.trans (congrArg ((gradedComplex X I ι F n).iCycles n ≫ ·)
      (gradedComplex_d X I ι F n n).symm) ?_
    exact HomologicalComplex.iCycles_d _ _ _
  have hw : pseudoApply (gradedD X I ι F n n)
      (pseudoApply ((gradedComplex X I ι F n).iCycles n) c) = 0 := by
    refine Eq.trans (Abelian.Pseudoelement.comp_apply
      ((gradedComplex X I ι F n).iCycles n) (gradedD X I ι F n n) c).symm ?_
    refine Eq.trans (congrArg (fun g => pseudoApply g c) h0) ?_
    exact Abelian.Pseudoelement.zero_apply _ c
  obtain ⟨p, hp⟩ := exists_pullback_pseudoelement
    (idealPowerMap X I n (F.d n (n + 1))) (idealPowerIncl X I ι n (F.X n))
    (idealPowerIncl X I ι n (F.X (n + 1))) hk (gradedD X I ι F n n)
    (cokernel_π_gradedD X I ι F n n)
    (pseudoApply ((gradedComplex X I ι F n).iCycles n) c) hw
  refine ⟨p, pseudo_injective_of_mono ((gradedComplex X I ι F n).iCycles n) ?_⟩
  have hgoal : pseudoApply
      (etaToGradedCycles X I ι F n ≫ (gradedComplex X I ι F n).iCycles n) p =
      pseudoApply ((gradedComplex X I ι F n).iCycles n) c := by
    rw [etaToGradedCycles_i]
    exact hp
  rw [Abelian.Pseudoelement.comp_apply] at hgoal
  exact hgoal

/-- **The comparison is surjective on cohomology**, because the projection from the cocycles to
the cohomology sheaf is. -/
public theorem epi_etaToGradedHomology
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    Epi (etaToGradedHomology X I ι F n) := by
  have _h := epi_etaToGradedCycles X I ι F hF n
  rw [← etaToGradedCycles_comp_homologyπ X I ι F n]
  exact epi_comp _ _

/-- **The comparison of Tag 0GT9 is surjective in every degree.**  This is the half of the
tag's isomorphism that holds degreewise: the reduction `(η_I F)^n/I (η_I F)^n` surjects onto
`H^n(F ⊗ I^n/I^{n+1})`.  No declaration of this development asserts it is degreewise mono, which
is why the tag is reached through the acyclicity of the kernel complex
(`quasiIso_reductionComparisonChainMap_iff_acyclic_kernel`) rather than degreewise. -/
public theorem epi_reductionComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    Epi (reductionComparison X I ι F n) := by
  have _h : Epi (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n)) ≫
      reductionComparison X I ι F n) := by
    rw [cokernel_π_reductionComparison X I ι F n]
    exact epi_etaToGradedHomology X I ι F hF n
  exact epi_of_epi (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n))) _


end Stacks.IdealTorsion.Reduction

end
