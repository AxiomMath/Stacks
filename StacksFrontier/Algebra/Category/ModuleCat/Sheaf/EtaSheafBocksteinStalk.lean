module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafReductionStalkModel
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi

import StacksCore.Tactic.StacksAttribute

/-!
# The Bockstein half of Tag 0GT9's stalkwise model identification

Let `(X, O_X)` be a ringed space, `ι : I ⟶ O_X` an invertible ideal subsheaf, and `F` a cochain
complex of `I`-torsion-free `O_X`-modules.  `EtaSheafReductionStalkModel.lean` reduces what
Tag 0GT9 still owes to `Reduction.HasStalkBocksteinComparison`: at every point, an isomorphism
`β` of the stalk of the chain-level Bockstein complex `H^•(F/I)` with the algebraic Bockstein
complex `EtaPow.Bockstein.bocksteinComplex` of `F_x/f`, carrying the stalk of the comparison of
Tag 0GT9 to the algebraic comparison of Tag 0F7T.

This file builds the *objects and the degreewise components* of that `β`.  Nothing on the
Bockstein side existed before it: there was no stalk comparison for `Eta.idealPowerTerm` at a
general twist, none for `gradedComplex`, and none for `bocksteinChainComplex`.

## Main results

* `preservesHomology_stalkModuleFunctor`: **the module-valued stalk functor is exact.**  The
  finite-colimits half is `preservesFiniteColimits_stalkModuleFunctor` and the finite-limits half
  is available by synthesis, so the four-way equivalence `CategoryTheory.Functor.exact_tfae`
  turns the two of them into preservation of homology.
* `stalkHomologyIso`: the stalk of the cohomology sheaf of a complex is the cohomology of the
  stalk complex, in every degree.
* `gradedStalkIso`: **the stalk of `F ⊗ I^n/I^{n+1}` is the algebraic successive quotient
  `F_x ⊗ f^n O_{X,x}/f^{n+1} O_{X,x}`**, as complexes of `O_{X,x}`-modules.
* `bocksteinChainStalkTermIso`: **the degree-`n` component of `β`** — the stalk of
  `H^n(F ⊗ I^n/I^{n+1})` is the degree-`n` term of the algebraic Bockstein complex.

## Implementation notes

### How the graded comparison is built

The two sides are the same quotient of the same module, presented twice.  On the sheaf side
`gradedTerm X I ι F n k` is the cokernel of `Eta.idealPowerIncl`, and the stalk functor preserves
that cokernel; `idealPowerStalkEquiv` then identifies the ambient module, the stalk of
`I^{⊗ n} ⊗ F^k`, with `F^k_x` itself, by dividing by `f^n` — it is the normalized comparison
`Eta.idealPowerStalkComparison`, which is injective with image `f^n F^k_x`, followed by the
inverse of multiplication by `f^n` on the stalk (`EtaPow.fpowEquiv`).  Under it the submodule
divided out, the image of the stalk of `idealPowerIncl`, becomes the `f`-multiples, because the
stalk of the ideal-power inclusion is multiplication by `f`
(`idealPowerStalkEquiv_idealPowerIncl`).  On the algebraic side the same quotient is presented by
`EtaComplex.ModNonzerodivisor.powerReductionMap`, surjective with kernel the `f`-multiples.

The three facts this needs about the normalized comparison — that it is injective, that it is
natural in the module, and that a generator of the stalk ideal is regular on the stalk of an
`I`-torsion-free module — are public in `EtaSheaf.lean`
(`Eta.idealPowerStalkComparison_map_injective`, `Eta.idealPowerStalkComparison_map_natural`,
`Eta.isSMulRegular_stalk_of_generatesStalkIdeal`), and the three about the algebraic quotient in
`StacksFrontier/Homology/Eta/Reduction.lean` (`EtaComplex.ModNonzerodivisor.powerReductionMap` with
its surjectivity and its kernel).  They live there rather than here for the reason recorded in
`EtaSheafReductionStalkModel.lean`: outside the module that defines them the two spellings of the
ambient module are not interchangeable, the colimit cocone of the sheafification not being
exposed.

### Why the differential square is five declarations

As in `EtaSheafReductionStalkModel.lean`: `maxHeartbeats` is per declaration, and each step of
the square spends most of a budget on one `isDefEq` between the two spellings of the stalk of a
complex.  The associativity shuffle is `comp_comp_congr` of that file, stated with every object
and morphism a variable for the same reason.

### What `β` still owes

`bocksteinChainStalkTermIso` is `β`'s component in degree `n`.  One square remains: the square
with the comparison, degreewise:

```
∀ n : ℤ,
  (stalkModuleFunctor X x).map (reductionComparison X I ι F n) ≫
      (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom =
    (etaModIdealStalkIso X I ι F hF x f hgen).hom.f n ≫
      (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
        (stalkComplex X x F) hreg).f n
```

Since the stalk of `cokernel.π` is an epimorphism (`epi_map_cokernel_π`) and
`cokernel_π_reductionComparison` computes the left-hand side on it, that square is equivalent to

```
∀ n : ℤ,
  (stalkModuleFunctor X x).map (etaToGradedHomology X I ι F n) ≫
      (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom =
    (etaStalkIso X I ι F hF x f hgen).hom.f n ≫
      ((EtaComplex.quotientMap f (stalkComplex X x F)).f n ≫
        (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
          (stalkComplex X x F) hreg).f n)
```

— the source's "on stalks this construction matches the maps built in More on Algebra, Lemma
15.97.6", read on the cocycle class of the first projection of `(η_I F)^n`.  Both sides send a
stalk section to the class of the algebraic reduction of its first projection divided by `f^n`;
proving it needs the compatibility of `stalkHomologyIso` with `homologyπ` and the elementwise
description of `Eta.etaStalkIso` against `EtaComplex.coefficient`.

That square is the whole of what `β` owes: it is `Reduction.HasStalkBocksteinSquare` of
`EtaSheafBocksteinSquare.lean`, and
`Reduction.hasStalkBocksteinComparison_of_hasStalkBocksteinSquare` builds `β` from it.  No
*second* residual square — that the components commute with the differentials — is needed, and in
particular neither the `gradedComplex₂` analogue of `gradedStalkIso` nor the compatibility of an
exact functor with `ShortComplex.ShortExact.δ` (which Mathlib does not have) is used.  The stalk of the comparison of Tag 0GT9 is a degreewise
epimorphism (`Reduction.epi_stalk_reductionComparison`), and the comparison, `etaModIdealStalkIso`
and Tag 0F7T's algebraic comparison are all morphisms of complexes; cancelling that epimorphism
derives the differential square from the comparison square in degrees `n` and `n + 1`
(`Reduction.comm_of_epi_of_squares`).  So the chain-level Bockstein operator never has to be
computed at a stalk, and neither the `gradedComplex₂` comparison nor the missing `δ` lemma is on
the critical path.

Nothing here carries `@[stacks 0GT9]`: everything below is a step of the *proof* of the tag.
The tag's own conclusion is proved in Situation 0GT4 in
`EtaSheafReductionDerivedIsoRegular.lean`, as
`Reduction.isIso_reductionComparisonQ_of_isLocallyGeneratedByRegular` and
`Reduction.reductionComparisonQIsoOfRegular`, and the square proved below is what that file
feeds to `Reduction.hasStalkBocksteinSquare_of_isLocallyGeneratedByRegular`.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 0GT8](https://stacks.math.columbia.edu/tag/0GT8)
* [Stacks Project, Tag 0F7T](https://stacks.math.columbia.edu/tag/0F7T)
* [Stacks Project, Tag 0GSQ](https://stacks.math.columbia.edu/tag/0GSQ)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk grpStalk)

universe u

namespace Stacks.IdealTorsion.Reduction

open Stacks.IdealTorsion.Eta

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ### The stalk functor is exact -/

/-- The stalk functor over `O_{X,x}` is additive: it is the additive stalk functor followed by
restriction of scalars.  Stated as a theorem and supplied explicitly, like
`stalkModuleFunctor_preservesZeroMorphisms`, because the category in the middle of the
composite carries two spellings of the same `RingCat` stalk. -/
public theorem additive_stalkModuleFunctor (x : X) : (stalkModuleFunctor X x).Additive :=
  ⟨fun {Y Z} f g => by
    show (ModuleCat.restrictScalars (SemilinearStalk.commStalkIso X.presheaf x).inv.hom).map
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x).map (f + g)) =
      (ModuleCat.restrictScalars (SemilinearStalk.commStalkIso X.presheaf x).inv.hom).map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x).map f) +
        (ModuleCat.restrictScalars (SemilinearStalk.commStalkIso X.presheaf x).inv.hom).map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x).map g)
    rw [Functor.map_add]
    rfl⟩

/-- The stalk functor over `O_{X,x}` is additive. -/
private alias stalkModuleFunctor_additive := additive_stalkModuleFunctor

/-- **The module-valued stalk functor is exact.**  Preserving finite limits and finite colimits
is one of the four equivalent forms of exactness for an additive functor between abelian
categories (`CategoryTheory.Functor.exact_tfae`); preserving homology is another, and it is the
form in which the stalk of a cohomology sheaf is computed. -/
public theorem preservesHomology_stalkModuleFunctor (x : X) :
    @Functor.PreservesHomology _ _ _ _ _ _ (stalkModuleFunctor X x)
      (stalkModuleFunctor_preservesZeroMorphisms X x) :=
  have := stalkModuleFunctor_preservesZeroMorphisms X x
  have := stalkModuleFunctor_additive X x
  have : ∀ {Y Z : SheafOfModules.{u} Oₓ} (g : Y ⟶ Z),
      PreservesLimit (parallelPair g 0) (stalkModuleFunctor X x) := fun g =>
    have : PreservesLimit
        (parallelPair g 0 ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x)
        (ModuleCat.restrictScalars (SemilinearStalk.commStalkIso X.presheaf x).inv.hom) :=
      ModuleCat.preservesLimit_restrictScalars _ _
    comp_preservesLimit (AlgebraicGeometry.SheafOfModules.stalkFunctor Oₓ x)
      (ModuleCat.restrictScalars (SemilinearStalk.commStalkIso X.presheaf x).inv.hom)
  ((Functor.exact_tfae (stalkModuleFunctor X x)).out 4 3).mp
    (And.intro (Functor.preservesFiniteLimits_of_preservesKernels (stalkModuleFunctor X x))
      (preservesFiniteColimits_stalkModuleFunctor X x))

/-- **The stalk of a cohomology sheaf is the cohomology of the stalk complex.**  The stalk
functor is exact, so it carries the homology of the short complex `K^{n-1} → K^n → K^{n+1}` to
the homology of its image. -/
@[no_expose]
public noncomputable def stalkHomologyIso (x : X)
    (K : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    ((stalkComplexFunctor X x).obj K).homology n ≅
      (stalkModuleFunctor X x).obj (K.homology n) :=
  letI := stalkModuleFunctor_preservesZeroMorphisms X x
  letI := preservesHomology_stalkModuleFunctor X x
  (K.sc n).mapHomologyIso (stalkModuleFunctor X x)

/-! ### Dividing by the generator: the stalk of an ideal power is the stalk itself -/

/-- **At a stalk, the `n`-th ideal power of an `I`-torsion-free module is the module itself**:
division by `f^n`.  The normalized comparison `Eta.idealPowerStalkComparison` is injective with
image the submodule `f^n M_x` of `(M_x)_f`, and so is multiplication by `f^n` on `M_x` itself
(`EtaPow.fpowEquiv`); the composite of the first with the inverse of the second is the
identification. -/
private noncomputable def idealPowerStalkEquiv
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (hM : IsIdealTorsionFree X ι M)
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (stalkModuleFunctor X x).obj (idealPowerTerm X I n M) ≃ₗ[ringStalk X x]
      (stalkModuleFunctor X x).obj M :=
  (LinearEquiv.ofInjective _
      (idealPowerStalkComparison_map_injective X I ι M hM x f hf n)).trans
    ((LinearEquiv.ofEq _ _ ((idealPowerStalkComparison X I ι M x f hf).range n)).trans
      (EtaPow.fpowEquiv f
        (isSMulRegular_stalk_of_generatesStalkIdeal X I ι M hM x f hf) n).symm)

/-- `idealPowerStalkEquiv` as a morphism of `ModuleCat`, so that the two spellings of the
stalk do not have to be re-elaborated at every use. -/
private noncomputable def idealPowerStalkMap
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (hM : IsIdealTorsionFree X ι M)
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    (stalkModuleFunctor X x).obj (idealPowerTerm X I n M) ⟶
      (stalkModuleFunctor X x).obj M :=
  ModuleCat.ofHom
    (X := (stalkModuleFunctor X x).obj (idealPowerTerm X I n M))
    (Y := (stalkModuleFunctor X x).obj M)
    (idealPowerStalkEquiv X I ι M hM x f hf n).toLinearMap

/-- The identification is characterised by `f^n ·` (division by `f^n`) `=` the normalized
comparison. -/
private lemma fpowMap_idealPowerStalkEquiv
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (hM : IsIdealTorsionFree X ι M)
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ)
    (z : (stalkModuleFunctor X x).obj (idealPowerTerm X I n M)) :
    EtaPow.fpowMap f ((stalkModuleFunctor X x).obj M) n
        (idealPowerStalkEquiv X I ι M hM x f hf n z) =
      (idealPowerStalkComparison X I ι M x f hf).map n z := by
  have hreg := isSMulRegular_stalk_of_generatesStalkIdeal X I ι M hM x f hf
  show (EtaPow.fpowEquiv f hreg n ((EtaPow.fpowEquiv f hreg n).symm _) :
    EtaPow.Loc f ((stalkModuleFunctor X x).obj M)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- **The stalk of the ideal-power inclusion is multiplication by the generator**, read through
the identification: this is what makes the successive quotient `M_x/f M_x` rather than zero. -/
private lemma idealPowerStalkEquiv_idealPowerIncl
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (hM : IsIdealTorsionFree X ι M)
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ)
    (z : (stalkModuleFunctor X x).obj (idealPowerTerm X I (n + 1) M)) :
    idealPowerStalkEquiv X I ι M hM x f hf n
        ((stalkModuleFunctor X x).map (idealPowerIncl X I ι n M) z) =
      f • idealPowerStalkEquiv X I ι M hM x f hf (n + 1) z := by
  apply EtaPow.fpowMap_injective f
    (isSMulRegular_stalk_of_generatesStalkIdeal X I ι M hM x f hf) n
  rw [fpowMap_idealPowerStalkEquiv, ← EtaPow.fpowMap_succ,
    fpowMap_idealPowerStalkEquiv]
  exact ConcreteCategory.congr_hom
    ((idealPowerStalkComparison X I ι M x f hf).succ n) z

/-- **The image of the stalk of the ideal-power inclusion is the submodule of `f`-multiples**,
read through the identification of the ambient module with the stalk. -/
private lemma map_range_idealPowerIncl
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (hM : IsIdealTorsionFree X ι M)
    (x : X) (f : ringStalk X x) (hf : GeneratesStalkIdeal X ι x f) (n : ℤ) :
    Submodule.map
        (idealPowerStalkEquiv X I ι M hM x f hf n : _ →ₗ[ringStalk X x] _)
        (LinearMap.range
          ((stalkModuleFunctor X x).map (idealPowerIncl X I ι n M)).hom) =
      LinearMap.range
        (EtaComplex.scalarMap f ((stalkModuleFunctor X x).obj M)) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨w, ⟨z, rfl⟩, rfl⟩
    exact ⟨idealPowerStalkEquiv X I ι M hM x f hf (n + 1) z,
      (idealPowerStalkEquiv_idealPowerIncl X I ι M hM x f hf n z).symm⟩
  · rintro y ⟨w, rfl⟩
    refine ⟨(stalkModuleFunctor X x).map (idealPowerIncl X I ι n M)
      ((idealPowerStalkEquiv X I ι M hM x f hf (n + 1)).symm w), ⟨_, rfl⟩, ?_⟩
    have h := idealPowerStalkEquiv_idealPowerIncl X I ι M hM x f hf n
      ((idealPowerStalkEquiv X I ι M hM x f hf (n + 1)).symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h

/-! ### The algebraic successive quotient as a quotient of the stalk complex -/

open Stacks.EtaComplex.FractionalPowerBockstein (successivePowerQuotientShortComplex)

/-- The kernel of the algebraic reduction into the `n`-th successive quotient is the submodule
of `f`-multiples, in the spelling `EtaComplex.scalarMap` in which the sheaf side presents it. -/
private lemma ker_powerReductionMap
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (x : X) (f : ringStalk X x) (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n k : ℤ) :
    LinearMap.ker
        ((Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
          (stalkComplex X x F) n).f k).hom =
      LinearMap.range (EtaComplex.scalarMap f ((stalkComplex X x F).X k)) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨y, hy⟩ := (Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap_eq_zero_iff
      f hf (stalkComplex X x F) hreg n k z).mp hz
    exact ⟨y, hy⟩
  · rintro z ⟨y, rfl⟩
    exact (Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap_eq_zero_iff
      f hf (stalkComplex X x F) hreg n k _).mpr ⟨y, rfl⟩

/-- **The degree-`k` term of the algebraic successive quotient `M ⊗ f^n A/f^{n+1} A` is
`M^k/f M^k`**, by the reduction map of `Homology/Eta/Reduction.lean`. -/
private noncomputable def powerQuotStalkIso
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (x : X) (f : ringStalk X x) (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n k : ℤ) :
    ModuleCat.of (ringStalk X x)
        (((stalkComplex X x F).X k) ⧸
          LinearMap.range (EtaComplex.scalarMap f ((stalkComplex X x F).X k))) ≅
      (successivePowerQuotientShortComplex (stalkComplex X x F) f n).X₃.X k :=
  ((Submodule.quotEquivOfEq _ _
      (ker_powerReductionMap X F x f hf hreg n k).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      (Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap_surjective f hf
        (stalkComplex X x F) hreg n k))).toModuleIso

/-! ### The degreewise graded stalk comparison -/

/-- **The degree-`k` term of the stalk of `F ⊗ I^n/I^{n+1}` is the degree-`k` term of the
algebraic successive quotient.**  The stalk functor preserves the defining cokernel, the ambient
module is identified with `F^k_x` by dividing by `f^n`, and the subobject divided out is the
`f`-multiples on both sides. -/
@[no_expose]
private noncomputable def gradedTermStalkIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n k : ℤ) :
    (stalkModuleFunctor X x).obj (gradedTerm X I ι F n k) ≅
      (successivePowerQuotientShortComplex (stalkComplex X x F) f n).X₃.X k :=
  letI := preservesFiniteColimits_stalkModuleFunctor X x
  PreservesCokernel.iso (stalkModuleFunctor X x)
      (idealPowerIncl X I ι n (F.X k)) ≪≫
    ModuleCat.cokernelIsoRangeQuotient _ ≪≫
      (Submodule.Quotient.equiv _ _
          (idealPowerStalkEquiv X I ι (F.X k) (hF k) x f hgen n)
          (map_range_idealPowerIncl X I ι (F.X k) (hF k) x f hgen n)).toModuleIso ≪≫
        powerQuotStalkIso X F x f hf hreg n k

/-- **The projection onto the successive quotient is carried to the algebraic reduction map.**
This is the characterisation of `gradedTermStalkIso` that the differentials are checked
against. -/
private lemma map_cokernel_π_comp_gradedTermStalkIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n k : ℤ) :
    (stalkModuleFunctor X x).map (cokernel.π (idealPowerIncl X I ι n (F.X k))) ≫
        (gradedTermStalkIso X I ι F hF x f hgen hf hreg n k).hom =
      idealPowerStalkMap X I ι (F.X k) (hF k) x f hgen n ≫
        (Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
          (stalkComplex X x F) n).f k := by
  let := preservesFiniteColimits_stalkModuleFunctor X x
  have h3 : ModuleCat.ofHom (LinearMap.range ((stalkModuleFunctor X x).map
          (idealPowerIncl X I ι n (F.X k))).hom).mkQ ≫
        ((Submodule.Quotient.equiv _ _
            (idealPowerStalkEquiv X I ι (F.X k) (hF k) x f hgen n)
            (map_range_idealPowerIncl X I ι (F.X k) (hF k) x f hgen n)).toModuleIso ≪≫
          powerQuotStalkIso X F x f hf hreg n k).hom =
      idealPowerStalkMap X I ι (F.X k) (hF k) x f hgen n ≫
        (Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
          (stalkComplex X x F) n).f k := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun z => rfl
  refine Eq.trans ?_ h3
  rw [← ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom
      ((stalkModuleFunctor X x).map (idealPowerIncl X I ι n (F.X k))),
    ← PreservesCokernel.π_iso_hom (stalkModuleFunctor X x)
      (idealPowerIncl X I ι n (F.X k))]
  simp only [Category.assoc]
  rfl

/-! ### The differential square, one step per declaration -/

/-- Localizing a map commutes with multiplication by `f^n`, with every module a variable. -/
private lemma fLoc_fpowMap {R : Type u} [CommRing R] {P Q : Type u}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : R) (d : P →ₗ[R] Q) (n : ℤ) (w : P) :
    EtaPow.fLoc f d (EtaPow.fpowMap f P n w) = EtaPow.fpowMap f Q n (d w) := by
  simp only [EtaPow.fpowMap_apply, EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc]

/-- **Division by `f^n` is compatible with the differentials**: the stalk of the `n`-th twist of
`d` becomes `d` at the stalk.  This is the naturality of the normalized comparison
(`Eta.idealPowerStalkComparison_map_natural`) after dividing by `f^n` on both sides. -/
private lemma idealPowerStalkMap_comm
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f) (n k : ℤ) :
    (stalkModuleFunctor X x).map (idealPowerMap X I n (F.d k (k + 1))) ≫
        idealPowerStalkMap X I ι (F.X (k + 1)) (hF (k + 1)) x f hgen n =
      idealPowerStalkMap X I ι (F.X k) (hF k) x f hgen n ≫
        (stalkComplex X x F).d k (k + 1) := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun z => ?_
  apply EtaPow.fpowMap_injective f
    (isSMulRegular_stalk_of_generatesStalkIdeal X I ι (F.X (k + 1)) (hF (k + 1)) x f hgen) n
  show EtaPow.fpowMap f ((stalkModuleFunctor X x).obj (F.X (k + 1))) n
      (idealPowerStalkEquiv X I ι (F.X (k + 1)) (hF (k + 1)) x f hgen n
        ((stalkModuleFunctor X x).map (idealPowerMap X I n (F.d k (k + 1))) z)) =
    EtaPow.fpowMap f ((stalkModuleFunctor X x).obj (F.X (k + 1))) n
      ((stalkModuleFunctor X x).map (F.d k (k + 1))
        (idealPowerStalkEquiv X I ι (F.X k) (hF k) x f hgen n z))
  rw [fpowMap_idealPowerStalkEquiv, ← fLoc_fpowMap, fpowMap_idealPowerStalkEquiv]
  exact (idealPowerStalkComparison_map_natural X I ι (F.d k (k + 1)) x f hgen n z).symm

/-- The projection onto the successive quotient is a map of complexes, at the spelling in which
the differential is read on the complex `F ⊗ I^n/I^{n+1}` rather than on `Eta.gradedD`. -/
private lemma cokernel_π_comp_gradedComplex_d
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    cokernel.π (idealPowerIncl X I ι n (F.X k)) ≫
        (gradedComplex X I ι F n).d k (k + 1) =
      idealPowerMap X I n (F.d k (k + 1)) ≫
        cokernel.π (idealPowerIncl X I ι n (F.X (k + 1))) := by
  rw [gradedComplex_d X I ι F n k]
  exact cokernel_π_gradedD X I ι F n k

/-- A functor carries an equation `f ≫ g = h` to the equation of the images. -/
private lemma map_comp_eq_of_comp_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B T : C} {f : A ⟶ B} {g : B ⟶ T} {h : A ⟶ T} (e : f ≫ g = h) :
    G.map f ≫ G.map g = G.map h := by
  rw [← G.map_comp, e]

/-- The previous square, at a stalk. -/
private lemma map_cokernel_π_comp_stalk_gradedD
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (x : X) (n k : ℤ) :
    (stalkModuleFunctor X x).map (cokernel.π (idealPowerIncl X I ι n (F.X k))) ≫
        ((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).d k (k + 1) =
      (stalkModuleFunctor X x).map (idealPowerMap X I n (F.d k (k + 1))) ≫
        (stalkModuleFunctor X x).map
          (cokernel.π (idealPowerIncl X I ι n (F.X (k + 1)))) := by
  refine Eq.trans ((stalkModuleFunctor X x).map_comp _ _).symm ?_
  refine Eq.trans (congrArg (fun g => (stalkModuleFunctor X x).map g)
    (cokernel_π_comp_gradedComplex_d X I ι F n k)) ?_
  exact (stalkModuleFunctor X x).map_comp _ _

/-- Step one of the differential square: pass the projection through the degreewise
comparison. -/
private lemma gradedTermStalkIso_comm_step₁
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n k : ℤ) :
    (stalkModuleFunctor X x).map (cokernel.π (idealPowerIncl X I ι n (F.X k))) ≫
        ((gradedTermStalkIso X I ι F hF x f hgen hf hreg n k).hom ≫
          (successivePowerQuotientShortComplex (stalkComplex X x F) f n).X₃.d k (k + 1)) =
      idealPowerStalkMap X I ι (F.X k) (hF k) x f hgen n ≫
        ((Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
            (stalkComplex X x F) n).f k ≫
          (successivePowerQuotientShortComplex (stalkComplex X x F) f n).X₃.d k (k + 1)) :=
  comp_comp_congr
    (map_cokernel_π_comp_gradedTermStalkIso X I ι F hF x f hgen hf hreg n k)
    ((successivePowerQuotientShortComplex (stalkComplex X x F) f n).X₃.d k (k + 1))

/-- Step two: the algebraic reduction map is a map of complexes, and division by `f^n` commutes
with the differentials. -/
private lemma gradedTermStalkIso_comm_step₂
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n k : ℤ) :
    idealPowerStalkMap X I ι (F.X k) (hF k) x f hgen n ≫
        ((Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
            (stalkComplex X x F) n).f k ≫
          (successivePowerQuotientShortComplex (stalkComplex X x F) f n).X₃.d k (k + 1)) =
      (stalkModuleFunctor X x).map (idealPowerMap X I n (F.d k (k + 1))) ≫
        (idealPowerStalkMap X I ι (F.X (k + 1)) (hF (k + 1)) x f hgen n ≫
          (Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
            (stalkComplex X x F) n).f (k + 1)) :=
  (congrArg (idealPowerStalkMap X I ι (F.X k) (hF k) x f hgen n ≫ ·)
      ((Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
        (stalkComplex X x F) n).comm k (k + 1))).trans
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun g => g ≫ (Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
          (stalkComplex X x F) n).f (k + 1))
        (idealPowerStalkMap_comm X I ι F hF x f hgen n k).symm)).trans
      (Category.assoc _ _ _))

/-- Step three: pass back through the degreewise comparison in degree `k + 1`. -/
private lemma gradedTermStalkIso_comm_step₃
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n k : ℤ) :
    (stalkModuleFunctor X x).map (idealPowerMap X I n (F.d k (k + 1))) ≫
        (idealPowerStalkMap X I ι (F.X (k + 1)) (hF (k + 1)) x f hgen n ≫
          (Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
            (stalkComplex X x F) n).f (k + 1)) =
      (stalkModuleFunctor X x).map (cokernel.π (idealPowerIncl X I ι n (F.X k))) ≫
        (((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).d k (k + 1) ≫
          (gradedTermStalkIso X I ι F hF x f hgen hf hreg n (k + 1)).hom) :=
  (congrArg ((stalkModuleFunctor X x).map (idealPowerMap X I n (F.d k (k + 1))) ≫ ·)
      (map_cokernel_π_comp_gradedTermStalkIso X I ι F hF x f hgen hf hreg n (k + 1)).symm).trans
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun g => g ≫ (gradedTermStalkIso X I ι F hF x f hgen hf hreg n (k + 1)).hom)
        (map_cokernel_π_comp_stalk_gradedD X I ι F x n k).symm)).trans
      (Category.assoc _ _ _))

/-- The degreewise graded comparisons commute with the differentials: both sides agree after the
projection from the stalk of the ideal power, which is an epimorphism. -/
private lemma gradedTermStalkIso_comm
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n k : ℤ) :
    (gradedTermStalkIso X I ι F hF x f hgen hf hreg n k).hom ≫
        (successivePowerQuotientShortComplex (stalkComplex X x F) f n).X₃.d k (k + 1) =
      ((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).d k (k + 1) ≫
        (gradedTermStalkIso X I ι F hF x f hgen hf hreg n (k + 1)).hom := by
  have := epi_map_cokernel_π X I ι (F.X k) x n
  refine (cancel_epi ((stalkModuleFunctor X x).map
    (cokernel.π (idealPowerIncl X I ι n (F.X k))))).1 ?_
  exact (gradedTermStalkIso_comm_step₁ X I ι F hF x f hgen hf hreg n k).trans
    ((gradedTermStalkIso_comm_step₂ X I ι F hF x f hgen hf hreg n k).trans
      (gradedTermStalkIso_comm_step₃ X I ι F hF x f hgen hf hreg n k))

/-- **The stalk of the graded complex `F ⊗ I^n/I^{n+1}` is the algebraic successive quotient
`F_x ⊗ f^n O_{X,x}/f^{n+1} O_{X,x}`.** -/
@[no_expose]
public noncomputable def gradedStalkIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n : ℤ) :
    (stalkComplexFunctor X x).obj (gradedComplex X I ι F n) ≅
      (successivePowerQuotientShortComplex (stalkComplex X x F) f n).X₃ :=
  HomologicalComplex.Hom.isoOfComponents
    (gradedTermStalkIso X I ι F hF x f hgen hf hreg n)
    (fun k l h => by
      subst h
      exact gradedTermStalkIso_comm X I ι F hF x f hgen hf hreg n k)

/-! ### The components of the Bockstein model isomorphism -/

/-- **The degree-`n` component of the Bockstein model isomorphism `β` owed by Tag 0GT9.**  The
stalk of the cohomology sheaf `H^n(F ⊗ I^n/I^{n+1})` is the degree-`n` term of the algebraic
Bockstein complex of `F_x/f`: the stalk functor commutes with taking cohomology
(`stalkHomologyIso`), and the two complexes whose cohomology is taken are identified by
`gradedStalkIso`.

What remains of `β` is that these components commute with the two differentials, and the square
with the comparison; both are written out in the note at the head of this file. -/
@[no_expose]
public noncomputable def bocksteinChainStalkTermIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n : ℤ) :
    ((stalkComplexFunctor X x).obj (bocksteinChainComplex X I ι F hF)).X n ≅
      (EtaPow.Bockstein.bocksteinComplex f hf (stalkComplex X x F) hreg).X n :=
  (stalkHomologyIso X x (gradedComplex X I ι F n) n).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} (ringStalk X x))
      (ComplexShape.up ℤ) n).mapIso
        (gradedStalkIso X I ι F hF x f hgen hf hreg n)

/-! ### The comparison square: the source's last sentence

The two sides of the square are maps of modules over the stalk ring, and the comparison is read
on elements.  The five helpers that open this section turn an equation of morphisms into the
corresponding equation of applications with every object and morphism a *variable*, so that each
use performs one `isDefEq` between the two spellings of the stalk of a complex rather than a
dozen keyed matches inside it.
-/

/-- An equation of composites, read on an element. -/
private lemma apply_comp_eq {R : Type u} [Ring R] {M N P : ModuleCat.{u} R}
    {a : M ⟶ N} {b : N ⟶ P} {c : M ⟶ P} (h : a ≫ b = c) (z : M) : b (a z) = c z := by
  rw [← ModuleCat.comp_apply, h]

/-- An equation of a morphism with a composite, read on an element. -/
private lemma apply_eq_comp_apply {R : Type u} [Ring R] {M N P : ModuleCat.{u} R}
    {a : M ⟶ N} {b : N ⟶ P} {c : M ⟶ P} (h : c = a ≫ b) (z : M) : c z = b (a z) := by
  rw [h, ModuleCat.comp_apply]

/-- A commuting square, read on an element. -/
private lemma apply_comp_comp {R : Type u} [Ring R] {M N P Q : ModuleCat.{u} R}
    {a : M ⟶ N} {b : N ⟶ Q} {c : M ⟶ P} {d : P ⟶ Q} (h : a ≫ b = c ≫ d) (z : M) :
    b (a z) = d (c z) := by
  rw [← ModuleCat.comp_apply, h, ModuleCat.comp_apply]

/-- A commuting square whose right-hand side is a three-fold composite, read on an element. -/
private lemma apply_comp_comp₂ {R : Type u} [Ring R] {M N P Q T : ModuleCat.{u} R}
    {a : M ⟶ N} {b : N ⟶ T} {c : M ⟶ P} {d : P ⟶ Q} {e : Q ⟶ T}
    (h : a ≫ b = c ≫ d ≫ e) (z : M) : b (a z) = e (d (c z)) := by
  rw [← ModuleCat.comp_apply, h, ModuleCat.comp_apply, ModuleCat.comp_apply]

/-- **The stalk functor's homology comparison, read on a cohomology class.**  Let `u` be a cycle
of `K` at a stalk and `w` a cycle of the stalk complex whose inclusion into the degree-`n` term
is the stalk of the inclusion of `u`.  Then `stalkHomologyIso` carries the stalk of the class of
`u` to the class of `w`.

This is `CategoryTheory.ShortComplex.π_comp_mapHomologyIso_inv`, with the cycles comparison
eliminated by the monomorphy of `iCycles`, so that nothing downstream has to name
`CategoryTheory.ShortComplex.mapCyclesIso`. -/
private lemma stalkHomologyIso_inv_map_homologyπ (x : X)
    (K : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ)
    (u : (stalkModuleFunctor X x).obj (K.cycles n))
    (w : ((stalkComplexFunctor X x).obj K).cycles n)
    (hw : ((stalkComplexFunctor X x).obj K).iCycles n w =
      (stalkModuleFunctor X x).map (K.iCycles n) u) :
    (stalkHomologyIso X x K n).inv ((stalkModuleFunctor X x).map (K.homologyπ n) u) =
      ((stalkComplexFunctor X x).obj K).homologyπ n w := by
  let := stalkModuleFunctor_preservesZeroMorphisms X x
  let := preservesHomology_stalkModuleFunctor X x
  have hcy := apply_comp_eq
    (ShortComplex.mapCyclesIso_inv_comp_iCycles (K.sc n) (stalkModuleFunctor X x)) u
  have hpi := apply_comp_comp
    (ShortComplex.π_comp_mapHomologyIso_inv (K.sc n) (stalkModuleFunctor X x)) u
  have hmono : Function.Injective
      (((stalkComplexFunctor X x).obj K).iCycles n).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hw' : w = ((K.sc n).mapCyclesIso (stalkModuleFunctor X x)).inv u :=
    hmono (hw.trans hcy.symm)
  rw [hw']
  exact hpi

/-- The degree-`k` component of the graded stalk comparison is the degreewise one. -/
private lemma gradedStalkIso_hom_f
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n k : ℤ) :
    (gradedStalkIso X I ι F hF x f hgen hf hreg n).hom.f k =
      (gradedTermStalkIso X I ι F hF x f hgen hf hreg n k).hom := rfl

/-- The degree-`n` component of the Bockstein model comparison, unfolded: the stalk-homology
comparison inverted, followed by the cohomology of the graded stalk comparison. -/
private lemma bocksteinChainStalkTermIso_hom_eq
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n : ℤ) :
    (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom =
      (stalkHomologyIso X x (gradedComplex X I ι F n) n).inv ≫
        HomologicalComplex.homologyMap
          (gradedStalkIso X I ι F hF x f hgen hf hreg n).hom n := rfl

/-- **The coefficient `s'` of the source.**  Dividing the first projection of the décalage by
`f^n` and multiplying back by `f^n` returns Tag 0GT6's comparison read inside the localization:
this is the source's `s = f^n s'`.  It is `etaStalkIso_hom` together with the characterisation of
division by `f^n` by the normalized comparison `Eta.idealPowerStalkComparison`. -/
private lemma fpowMap_idealPowerStalkMap_etaStalkIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f) (n : ℤ)
    (z : (stalkModuleFunctor X x).obj (etaTerm X I ι F n))
    (y : EtaComplex.term f (stalkComplex X x F) n)
    (hy : (etaStalkIso X I ι F hF x f hgen).hom.f n z = y) :
    EtaPow.fpowMap f ((stalkComplex X x F).X n) n
        (idealPowerStalkMap X I ι (F.X n) (hF n) x f hgen n
          ((stalkModuleFunctor X x).map
            (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
              (idealPowerIncl X I ι n (F.X (n + 1)))) z)) =
      (y : EtaPow.Loc f ((stalkComplex X x F).X n)) := by
  have h1 := fpowMap_idealPowerStalkEquiv X I ι (F.X n) (hF n) x f hgen n
    ((stalkModuleFunctor X x).map
      (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1)))) z)
  have h2 := apply_comp_comp (etaStalkIso_hom X I ι F hF x f hgen n) z
  rw [hy] at h2
  exact h1.trans h2.symm

/-- **The first projection of the décalage, divided by `f^n` and reduced.**  The comparison
`etaToGraded` followed by the degreewise graded stalk comparison is division by `f^n` followed by
the algebraic reduction into the `n`-th successive quotient — the source's "the class of
`f^n s'`", read before passing to cohomology. -/
private lemma map_etaToGraded_comp_gradedTermStalkIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n : ℤ) :
    (stalkModuleFunctor X x).map (etaToGraded X I ι F n) ≫
        (gradedTermStalkIso X I ι F hF x f hgen hf hreg n n).hom =
      (stalkModuleFunctor X x).map
          (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
            (idealPowerIncl X I ι n (F.X (n + 1)))) ≫
        (idealPowerStalkMap X I ι (F.X n) (hF n) x f hgen n ≫
          (Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap f hf
            (stalkComplex X x F) n).f n) := by
  refine Eq.trans (congrArg
    (fun g => g ≫ (gradedTermStalkIso X I ι F hF x f hgen hf hreg n n).hom)
    ((stalkModuleFunctor X x).map_comp
      (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1))))
      (cokernel.π (idealPowerIncl X I ι n (F.X n))))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg
    ((stalkModuleFunctor X x).map
      (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1)))) ≫ ·)
    (map_cokernel_π_comp_gradedTermStalkIso X I ι F hF x f hgen hf hreg n n)

/-- The first projection of the décalage, read in the degree-`n` term of `F ⊗ I^n/I^{n+1}`, is a
cocycle at a stalk: it is one before taking stalks (`etaToGraded_comp_d`). -/
private lemma map_etaToGraded_comp_d
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (x : X) (n : ℤ) :
    (stalkModuleFunctor X x).map (etaToGraded X I ι F n) ≫
      ((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).d n (n + 1) = 0 := by
  have h0 : etaToGraded X I ι F n ≫ (gradedComplex X I ι F n).d n (n + 1) = 0 :=
    (congrArg (etaToGraded X I ι F n ≫ ·) (gradedComplex_d X I ι F n n)).trans
      (etaToGraded_comp_d X I ι F n)
  exact (map_comp_eq_of_comp_eq _ h0).trans
    ((stalkModuleFunctor_preservesZeroMorphisms X x).map_zero _ _)

/-- **The comparison square on the cocycle class of the first projection.**  This is the square
of `map_reductionComparison_comp_bocksteinChainStalkTermIso` read before the reduction modulo the
ideal, where the comparison of Tag 0GT9 is `etaToGradedHomology`
(`cokernel_π_reductionComparison`).

It is its own declaration because `maxHeartbeats` is per declaration: this is where the source's
`s = f^n s'` is carried out and the two cocycle classes are compared, and the two reductions of
the square to it are cheap by comparison. -/
private lemma map_etaToGradedHomology_comp_bocksteinChainStalkTermIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n : ℤ) :
    (stalkModuleFunctor X x).map (etaToGradedHomology X I ι F n) ≫
        (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom =
      (etaStalkIso X I ι F hF x f hgen).hom.f n ≫
        ((EtaComplex.quotientMap f (stalkComplex X x F)).f n ≫
          (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
            (stalkComplex X x F) hreg).f n) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  show (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom
      ((stalkModuleFunctor X x).map (etaToGradedHomology X I ι F n) z) =
    (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
        (stalkComplex X x F) hreg).f n
      ((EtaComplex.quotientMap f (stalkComplex X x F)).f n
        ((etaStalkIso X I ι F hF x f hgen).hom.f n z))
  -- the source's `s = f^n s'`
  obtain ⟨y, hy⟩ : ∃ y : EtaComplex.term f (stalkComplex X x F) n,
      (etaStalkIso X I ι F hF x f hgen).hom.f n z = y := ⟨_, rfl⟩
  obtain ⟨hz, hclass⟩ :=
    Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein_mk f hf
      (stalkComplex X x F) hreg n y
      (idealPowerStalkMap X I ι (F.X n) (hF n) x f hgen n
        ((stalkModuleFunctor X x).map
          (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
            (idealPowerIncl X I ι n (F.X (n + 1)))) z))
      (fpowMap_idealPowerStalkMap_etaStalkIso X I ι F hF x f hgen n z y hy).symm
  have hq : (EtaComplex.quotientMap f (stalkComplex X x F)).f n
        ((etaStalkIso X I ι F hF x f hgen).hom.f n z) = Submodule.Quotient.mk y :=
    (congrArg (fun t : EtaComplex.term f (stalkComplex X x F) n =>
        (EtaComplex.quotientMap f (stalkComplex X x F)).f n t) hy).trans
      (EtaComplex.quotientMap_f_apply f (stalkComplex X x F) n y)
  -- the cocycle of the stalk complex which represents the left-hand side
  have hlift : ((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).liftCycles
        ((stalkModuleFunctor X x).map (etaToGraded X I ι F n)) (n + 1) (by simp)
        (map_etaToGraded_comp_d X I ι F x n) ≫
      ((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).iCycles n =
      (stalkModuleFunctor X x).map (etaToGraded X I ι F n) :=
    HomologicalComplex.liftCycles_i _ _ _ _ _
  have hfacCyc : (stalkModuleFunctor X x).map (etaToGradedCycles X I ι F n) ≫
      (stalkModuleFunctor X x).map ((gradedComplex X I ι F n).iCycles n) =
      (stalkModuleFunctor X x).map (etaToGraded X I ι F n) :=
    map_comp_eq_of_comp_eq _ (etaToGradedCycles_i X I ι F n)
  have hclassL := stalkHomologyIso_inv_map_homologyπ X x (gradedComplex X I ι F n) n
    ((stalkModuleFunctor X x).map (etaToGradedCycles X I ι F n) z)
    (((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).liftCycles
      ((stalkModuleFunctor X x).map (etaToGraded X I ι F n)) (n + 1) (by simp)
      (map_etaToGraded_comp_d X I ι F x n) z)
    ((apply_comp_eq hlift z).trans (apply_comp_eq hfacCyc z).symm)
  have hfac : (stalkModuleFunctor X x).map (etaToGradedCycles X I ι F n) ≫
      (stalkModuleFunctor X x).map ((gradedComplex X I ι F n).homologyπ n) =
      (stalkModuleFunctor X x).map (etaToGradedHomology X I ι F n) :=
    map_comp_eq_of_comp_eq _ (etaToGradedCycles_comp_homologyπ X I ι F n)
  have hnat : ((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).homologyπ n ≫
      HomologicalComplex.homologyMap
        (gradedStalkIso X I ι F hF x f hgen hf hreg n).hom n =
      HomologicalComplex.cyclesMap
          (gradedStalkIso X I ι F hF x f hgen hf hreg n).hom n ≫
        (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex
          (stalkComplex X x F) f n).X₃.homologyπ n :=
    HomologicalComplex.homologyπ_naturality _ _
  have hcycmap : HomologicalComplex.cyclesMap
        (gradedStalkIso X I ι F hF x f hgen hf hreg n).hom n ≫
      (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex
        (stalkComplex X x F) f n).X₃.iCycles n =
      ((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).iCycles n ≫
        (gradedStalkIso X I ι F hF x f hgen hf hreg n).hom.f n :=
    HomologicalComplex.cyclesMap_i _ _
  -- the two cocycles agree, hence so do their classes
  have hcycles : HomologicalComplex.cyclesMap
        (gradedStalkIso X I ι F hF x f hgen hf hreg n).hom n
        (((stalkComplexFunctor X x).obj (gradedComplex X I ι F n)).liftCycles
          ((stalkModuleFunctor X x).map (etaToGraded X I ι F n)) (n + 1) (by simp)
          (map_etaToGraded_comp_d X I ι F x n) z) =
      (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex
          (stalkComplex X x F) f n).X₃.cyclesMk
        (Stacks.EtaComplex.ModNonzerodivisor.bocksteinRepresentative (stalkComplex X x F) f n
          (idealPowerStalkMap X I ι (F.X n) (hF n) x f hgen n
            ((stalkModuleFunctor X x).map
              (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
                (idealPowerIncl X I ι n (F.X (n + 1)))) z))) (n + 1) (by simp) hz := by
    apply (ModuleCat.mono_iff_injective
      ((Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex
        (stalkComplex X x F) f n).X₃.iCycles n)).mp inferInstance
    refine Eq.trans (apply_comp_comp hcycmap _) ?_
    refine Eq.trans ?_
      ((Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex
        (stalkComplex X x F) f n).X₃.i_cyclesMk _ (n + 1) (by simp) hz).symm
    refine Eq.trans (congrArg
      (fun t => (gradedStalkIso X I ι F hF x f hgen hf hreg n).hom.f n t)
      (apply_comp_eq hlift z)) ?_
    refine Eq.trans (apply_comp_comp₂
      (map_etaToGraded_comp_gradedTermStalkIso X I ι F hF x f hgen hf hreg n) z) ?_
    exact Stacks.EtaComplex.ModNonzerodivisor.powerReductionMap_representative f hf
      (stalkComplex X x F) n _
  -- assemble
  refine Eq.trans ?_ ((congrArg
    (fun t => (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
      (stalkComplex X x F) hreg).f n t) hq).trans hclass).symm
  refine Eq.trans (congrArg
    (fun t => (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom t)
    (apply_comp_eq hfac z).symm) ?_
  refine Eq.trans (apply_eq_comp_apply
    (bocksteinChainStalkTermIso_hom_eq X I ι F hF x f hgen hf hreg n) _) ?_
  refine Eq.trans (congrArg
    (fun t => HomologicalComplex.homologyMap
      (gradedStalkIso X I ι F hF x f hgen hf hreg n).hom n t) hclassL) ?_
  refine Eq.trans (apply_comp_comp hnat _) ?_
  exact congrArg
    (fun t => (Stacks.EtaComplex.FractionalPowerBockstein.successivePowerQuotientShortComplex
      (stalkComplex X x F) f n).X₃.homologyπ n t) hcycles

/-- **The degreewise comparison square of Tag 0GT9's last step, proved.**  At every point, in
every degree, the stalk of the comparison of Tag 0GT9 followed by the Bockstein model comparison
`bocksteinChainStalkTermIso` agrees with Tag 0GT6's comparison of the reduced décalages
(`etaModIdealStalkIso`) followed by the algebraic comparison of Tag 0F7T.

This is the source's last sentence — "the construction given in the previous paragraph agrees on
stalks with the maps constructed in More on Algebra, Lemma 15.97.6" — and it is proved here, not
assumed.  Nothing is hypothesised beyond the data `HasStalkBocksteinSquare` already carries: a
generator `f` of the stalk ideal which is a nonzerodivisor of `O_{X,x}` and is regular on every
term of the stalk complex.

The proof is the source's own.  Both sides are computed after the stalkwise epimorphism
`epi_map_cokernel_π`, where the left-hand side becomes the cocycle class of the first projection
of `(η_I F)^n` (`cokernel_π_reductionComparison`) and the right-hand side the class of the
algebraic reduction of its coefficient (`map_cokernel_π_comp_etaModIdealStalkIso_hom_f` and
`etaQuotientToBockstein_mk`).  Writing `s = f^n s'` as the source does — which is
`fpowMap_idealPowerStalkMap_etaStalkIso`, i.e. Tag 0GT6's `etaStalkIso_hom` — the two agree
because `map_etaToGraded_comp_gradedTermStalkIso` sends `s` to the algebraic reduction of `s'`
and `powerReductionMap_representative` identifies that reduction with the pure tensor `s' ⊗ f^n`
which Tag 0F7T's comparison names.  The passage from cocycles to classes is
`stalkHomologyIso_inv_map_homologyπ`. -/
public theorem map_reductionComparison_comp_bocksteinChainStalkTermIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ j : ℤ, IsIdealTorsionFree X ι (F.X j))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ j : ℤ, IsSMulRegular ((stalkComplex X x F).X j) f) (n : ℤ) :
    (stalkModuleFunctor X x).map (reductionComparison X I ι F n) ≫
        (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom =
      (etaModIdealStalkIso X I ι F hF x f hgen).hom.f n ≫
        (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
          (stalkComplex X x F) hreg).f n := by
  have := epi_map_cokernel_π X I ι (etaTerm X I ι F n) x 0
  refine (cancel_epi ((stalkModuleFunctor X x).map
    (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n))))).1 ?_
  have hL : (stalkModuleFunctor X x).map
        (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n))) ≫
      ((stalkModuleFunctor X x).map (reductionComparison X I ι F n) ≫
        (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom) =
      (stalkModuleFunctor X x).map (etaToGradedHomology X I ι F n) ≫
        (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom := by
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (map_comp_eq_of_comp_eq _ (cokernel_π_reductionComparison X I ι F n)))
  have hR := comp_comp_congr
    (map_cokernel_π_comp_etaModIdealStalkIso_hom_f X I ι F hF x f hgen n)
    ((Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
      (stalkComplex X x F) hreg).f n)
  exact hL.trans
    ((map_etaToGradedHomology_comp_bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg
      n).trans hR.symm)

end Stacks.IdealTorsion.Reduction

end
