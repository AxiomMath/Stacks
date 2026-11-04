module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafReduction

import StacksCore.Tactic.StacksAttribute

/-!
# The chain-level Bockstein complex, and the comparison of Tag 0GT9 as a map of complexes

Let `(X, O_X)` be a ringed space, `ι : I ⟶ O_X` an invertible ideal subsheaf, and `F` a cochain
complex of `I`-torsion-free `O_X`-modules.  `EtaSheafReduction.lean` builds the degreewise
comparison

`(η_I F)^n/I (η_I F)^n ⟶ H^n(F ⊗ I^n/I^{n+1})`

of Tag 0GT9 and proves it surjective.  This file supplies the differential on the right-hand
side and upgrades the comparison to a morphism of complexes.

The differential is the Bockstein operator: the connecting map of the short exact sequence of
complexes

`0 → F ⊗ I^{n+1}/I^{n+2} → F ⊗ I^n/I^{n+2} → F ⊗ I^n/I^{n+1} → 0`,

whose degreewise form is `Bockstein.quotientShortComplex` of the two ideal-power inclusions
`I^{⊗ (n+2)} ⊗ F^k ⟶ I^{⊗ (n+1)} ⊗ F^k ⟶ I^{⊗ n} ⊗ F^k`.

## Main definitions

* `gradedComplex₂`: the middle complex `F ⊗ I^n/I^{n+2}`, with degree-`k` term the cokernel of
  the composite of two ideal-power inclusions.
* `gradedShortComplex`: the displayed short exact sequence of complexes.
* `bocksteinChainOperator`: the chain-level Bockstein map
  `H^n(F ⊗ I^n/I^{n+1}) ⟶ H^{n+1}(F ⊗ I^{n+1}/I^{n+2})`, the connecting map of that sequence.
* `bocksteinChainComplex`: the complex `H^•(F/I)` at the level of complexes — degree-`n` term
  `H^n(F ⊗ I^n/I^{n+1})`, differential the Bockstein operator.  This is the chain-level form of
  the right-hand side of Tag 0GT9.
* `reductionComparisonChainMap`: **the comparison of Tag 0GT9 as a morphism of complexes**
  `η_I F ⊗ O_X/I ⟶ H^•(F/I)`.

## Main results

* `gradedShortComplex_shortExact`: the displayed sequence of complexes is short exact, because
  it is degreewise the successive-quotient sequence of two monomorphisms.
* `etaToGradedHomology_comp_bocksteinChainOperator`: **the source's compatibility of the
  comparison with the differentials.**  The Bockstein operator sends the cocycle class of the
  first projection of `(η_I F)^n` to the cocycle class of its second projection, and the second
  projection is what the differential of the décalage reads as the first projection in degree
  `n + 1`.  This is the source's parenthetical "essentially because `β` sends the class of
  `f^i s'` to the class of `f^{i+1} t`".
* `bocksteinChainOperator_comp_bocksteinChainOperator`: the Bockstein operator squares to zero.
  It is deduced from the previous item rather than proved directly: the comparison is a
  surjection intertwining the Bockstein with the differential of the décalage, which squares to
  zero.
* `epi_reductionComparisonChainMap`: the comparison of complexes is an epimorphism.

## Implementation notes

The Bockstein operator is `ShortComplex.ShortExact.δ` of the short exact sequence of complexes,
exactly as the module-level `EtaPow.Bockstein.bocksteinOperator` of
`StacksFrontier/Homology/Eta/Reduction.lean` is; the sheaf-level `Bockstein.bocksteinOperator` of
`EtaSheafBockstein.lean` is a different map, the connecting map of a triangle in `D(O_X)` built
from the *derived* tensor product, and identifying the two is not done here — see the note on
what Tag 0GT9 still owes at the end of this section.

The compatibility with differentials is proved from `ShortComplex.ShortExact.δ_eq`, which
computes the connecting map at a chosen lift.  The three choices are the ones the source makes:
the cocycle is the first projection of the fibre product defining `(η_I F)^n`, its lift to
`F ⊗ I^n/I^{n+2}` is the same section read one quotient up, and the differential of that lift
lands in `F ⊗ I^{n+1}/I^{n+2}` by the defining condition of the fibre product, where it is the
second projection.  `Eta.etaObj_d_fst` then says that this second projection is the first
projection of `d(s)`, which is what makes the square commute.

`Bockstein.quotientShortComplex_shortExact` takes its two monomorphism hypotheses as instances;
they are `Eta.idealPowerIncl_mono` applied to the termwise torsion-freeness of `F`.

### What Tag 0GT9 still owes after this file

Tag 0GT9 asserts that `Lη_I M ⊗^L O_X/I ⟶ H^•(M/I)` is an isomorphism in `D(O_X)`.  This file
makes the comparison a morphism of complexes and left three things.  The first of them is now
proved — see the bullet below — so what is still owed after this file is the second and the
third, both of which are the same spelling bridge.

* that it is a quasi-isomorphism.  **This is no longer owed in Situation 0GT4**: it is degreewise
  epi (`epi_reductionComparison`), and no declaration of this development asserts it is
  degreewise mono, so the route taken is that its kernel
  complex is acyclic; that equivalence is proved in `EtaSheafReductionQuasiIso.lean` as
  `quasiIso_reductionComparisonChainMap_iff_acyclic_kernel`, and the resulting obligation
  `(reductionComparisonKernel X I ι F hF).Acyclic` is discharged in
  `EtaSheafReductionDerivedIsoRegular.lean` by
  `acyclic_reductionComparisonKernel_of_isLocallyGeneratedByRegular`, giving
  `quasiIso_reductionComparisonChainMap_of_isLocallyGeneratedByRegular` and the tag's isomorphism
  in `D(O_X)`.  The computation below is the shape of that proof, and is kept for the reader.
  Degreewise that kernel is an
  extension of the boundaries of `F ⊗ I^n/I^{n+1}` by those of `F ⊗ I^{n+1}/I^{n+2}`, and the
  differential carries the sub isomorphically onto the quotient; the module-level form of this
  computation is the proof of
  `EtaComplex.ModNonzerodivisor.etaTensorMod_to_bockstein_quasiIso` (Tag 0F7T), which runs it
  through the acyclic boundary subcomplex of Tag 0F7S;
* the identification of `bocksteinChainComplex` with `Bockstein.bocksteinComplex`, the
  right-hand side of the tag as `EtaSheafBockstein.lean` states it.  The K-flat resolution
  `[I^{n+1} → I^n]` of `I^n/I^{n+1}` this was waiting on is
  `Bockstein.kFlat_powerQuotientResolution` of `EtaSheafPowerQuotientResolution.lean`, and with
  it `Bockstein.bocksteinTermIsoHomology` identifies the two complexes' **terms**:
  `Bockstein.bocksteinTerm X I ι (Q F) n` is the degree-`n` homology of
  `Tot(F ⊗ [I^{n+1} → I^n])`.  Two things remain.  The **differentials** are not identified:
  `Bockstein.bocksteinOperator` is `DerivedCategory.HomologySequence.δ` of a `mapTriangle` of the
  derived tensor product, `bocksteinChainOperator` is `ShortComplex.ShortExact.δ` of
  `gradedShortComplex`, and neither Mathlib nor this development has a lemma relating a
  functor-pushed triangle's `δ` to a chain-level short exact sequence's `δ`.  And the terms are
  matched against `Tot(F ⊗ [I^{n+1} → I^n])` rather than against `gradedTerm`, which additionally
  needs the right-exactness of `F^k ⊗ -` and the `sheafTensor`-versus-`Invertible` bridge;
* the identification of `etaModIdealComplex` with `Lη_I M ⊗^L O_X/I`, which needs the same
  bridge.  The descent from a termwise torsion-free representative to an arbitrary object of
  `D(O_X)` is no longer owed: it is
  `Reduction.exists_isIso_reductionComparisonQ_of_isLocallyGeneratedByRegular` in
  `EtaSheafReductionDerivedIsoRegular.lean`, which produces the representative from Situation
  0GT4's own hypothesis instead of assuming it.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 0GT8](https://stacks.math.columbia.edu/tag/0GT8)
* [Stacks Project, Tag 0F7T](https://stacks.math.columbia.edu/tag/0F7T)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.IdealTorsion.Reduction

open Stacks.IdealTorsion.Eta
open Stacks.IdealTorsion.Bockstein (quotientIncl quotientProj quotientShortComplex)

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-- The successive-quotient inclusion read on the first quotient. -/
private theorem π_quotientIncl {A : Type w} [Category.{v} A] [Abelian A]
    {A₁ A₂ A₃ : A} (a : A₃ ⟶ A₂) (b : A₂ ⟶ A₁) :
    cokernel.π a ≫ quotientIncl a b = b ≫ cokernel.π (a ≫ b) :=
  cokernel.π_desc _ _ _

/-- The successive-quotient projection read on the middle quotient. -/
private theorem π_quotientProj {A : Type w} [Category.{v} A] [Abelian A]
    {A₁ A₂ A₃ : A} (a : A₃ ⟶ A₂) (b : A₂ ⟶ A₁) :
    cokernel.π (a ≫ b) ≫ quotientProj a b = cokernel.π b :=
  cokernel.π_desc _ _ _

/-! ### The complex `F ⊗ I^n/I^{n+2}` -/

/-- The inclusion of the `(n+2)`-nd ideal power in the `n`-th, as the composite of two
successive ideal-power inclusions. -/
public noncomputable abbrev idealPowerIncl₂
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    idealPowerTerm X I (n + 1 + 1) M ⟶ idealPowerTerm X I n M :=
  idealPowerIncl X I ι (n + 1) M ≫ idealPowerIncl X I ι n M

/-- Multiplication by the square of the ideal is natural in the module. -/
public theorem idealPowerIncl₂_natural
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (n : ℤ) {M N : SheafOfModules.{u} Oₓ} (f : M ⟶ N) :
    idealPowerIncl₂ X I ι n M ≫ idealPowerMap X I n f =
      idealPowerMap X I (n + 1 + 1) f ≫ idealPowerIncl₂ X I ι n N :=
  (Category.assoc _ _ _).trans
    ((congrArg (idealPowerIncl X I ι (n + 1) M ≫ ·) (idealPowerIncl_natural X I ι n f)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ idealPowerIncl X I ι n N)
            (idealPowerIncl_natural X I ι (n + 1) f)).trans
          (Category.assoc _ _ _))))

/-- The degree-`k` term of `F ⊗ I^n/I^{n+2}`: the quotient of `I^{⊗ n} ⊗ F^k` by the image of
the ideal power two steps up. -/
public noncomputable abbrev gradedTerm₂
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) : SheafOfModules.{u} Oₓ :=
  cokernel (idealPowerIncl₂ X I ι n (F.X k))

/-- The differential of `F ⊗ I^n/I^{n+2}`, induced by the `n`-th twist of the differential of
`F`. -/
public noncomputable def gradedD₂
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    gradedTerm₂ X I ι F n k ⟶ gradedTerm₂ X I ι F n (k + 1) :=
  cokernel.desc (idealPowerIncl₂ X I ι n (F.X k))
    (idealPowerMap X I n (F.d k (k + 1)) ≫
      cokernel.π (idealPowerIncl₂ X I ι n (F.X (k + 1))))
    (by
      rw [← Category.assoc, idealPowerIncl₂_natural, Category.assoc,
        cokernel.condition, comp_zero])

@[simp] public theorem cokernel_π_gradedD₂
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    cokernel.π (idealPowerIncl₂ X I ι n (F.X k)) ≫ gradedD₂ X I ι F n k =
      idealPowerMap X I n (F.d k (k + 1)) ≫
        cokernel.π (idealPowerIncl₂ X I ι n (F.X (k + 1))) :=
  cokernel.π_desc _ _ _

public theorem gradedD₂_comp_gradedD₂
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    gradedD₂ X I ι F n k ≫ gradedD₂ X I ι F n (k + 1) = 0 := by
  refine (cancel_epi (cokernel.π (idealPowerIncl₂ X I ι n (F.X k)))).1 ?_
  rw [comp_zero, ← Category.assoc, cokernel_π_gradedD₂, Category.assoc,
    cokernel_π_gradedD₂, ← Category.assoc, ← idealPowerMap_comp, F.d_comp_d,
    idealPowerMap_zero, zero_comp]

/-- The complex `F ⊗ I^n/I^{n+2}`, the middle term of the short exact sequence whose connecting
map is the Bockstein operator. -/
public noncomputable def gradedComplex₂
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    CochainComplex (SheafOfModules.{u} Oₓ) ℤ :=
  CochainComplex.of (gradedTerm₂ X I ι F n) (gradedD₂ X I ι F n)
    (gradedD₂_comp_gradedD₂ X I ι F n)

@[simp] public theorem gradedComplex₂_X
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    (gradedComplex₂ X I ι F n).X k = gradedTerm₂ X I ι F n k := rfl

public theorem gradedComplex₂_d
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    (gradedComplex₂ X I ι F n).d k (k + 1) = gradedD₂ X I ι F n k := by
  simp only [gradedComplex₂, CochainComplex.of_d]

/-! ### The short exact sequence of complexes -/

/-- The successive-quotient inclusion commutes with the differentials, stated at the spelling
in which both sides are maps between cokernels rather than between terms of a complex. -/
private theorem gradedIncl_comm
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    quotientIncl (idealPowerIncl X I ι (n + 1) (F.X k)) (idealPowerIncl X I ι n (F.X k)) ≫
        gradedD₂ X I ι F n k =
      gradedD X I ι F (n + 1) k ≫
        quotientIncl (idealPowerIncl X I ι (n + 1) (F.X (k + 1)))
          (idealPowerIncl X I ι n (F.X (k + 1))) := by
  refine (cancel_epi (cokernel.π (idealPowerIncl X I ι (n + 1) (F.X k)))).1 ?_
  conv_lhs => rw [← Category.assoc, π_quotientIncl, Category.assoc, cokernel_π_gradedD₂,
    ← Category.assoc, idealPowerIncl_natural, Category.assoc]
  conv_rhs => rw [← Category.assoc, cokernel_π_gradedD, Category.assoc, π_quotientIncl]

/-- The inclusion `F ⊗ I^{n+1}/I^{n+2} ⟶ F ⊗ I^n/I^{n+2}`, degreewise the successive-quotient
inclusion of two ideal-power inclusions. -/
public noncomputable def gradedIncl
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    gradedComplex X I ι F (n + 1) ⟶ gradedComplex₂ X I ι F n where
  f k := quotientIncl (idealPowerIncl X I ι (n + 1) (F.X k)) (idealPowerIncl X I ι n (F.X k))
  comm' i j h := by
    subst h
    refine Eq.trans (congrArg (quotientIncl (idealPowerIncl X I ι (n + 1) (F.X i))
      (idealPowerIncl X I ι n (F.X i)) ≫ ·) (gradedComplex₂_d X I ι F n i)) ?_
    refine Eq.trans (gradedIncl_comm X I ι F n i) ?_
    exact congrArg (fun g => g ≫ quotientIncl (idealPowerIncl X I ι (n + 1) (F.X (i + 1)))
      (idealPowerIncl X I ι n (F.X (i + 1)))) (gradedComplex_d X I ι F (n + 1) i).symm

/-- The successive-quotient projection commutes with the differentials, stated at the spelling
in which both sides are maps between cokernels rather than between terms of a complex. -/
private theorem gradedProj_comm
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n k : ℤ) :
    quotientProj (idealPowerIncl X I ι (n + 1) (F.X k)) (idealPowerIncl X I ι n (F.X k)) ≫
        gradedD X I ι F n k =
      gradedD₂ X I ι F n k ≫
        quotientProj (idealPowerIncl X I ι (n + 1) (F.X (k + 1)))
          (idealPowerIncl X I ι n (F.X (k + 1))) := by
  refine (cancel_epi (cokernel.π (idealPowerIncl₂ X I ι n (F.X k)))).1 ?_
  conv_lhs => rw [← Category.assoc, π_quotientProj, cokernel_π_gradedD]
  conv_rhs => rw [← Category.assoc, cokernel_π_gradedD₂, Category.assoc, π_quotientProj]

/-- The projection `F ⊗ I^n/I^{n+2} ⟶ F ⊗ I^n/I^{n+1}`, degreewise the successive-quotient
projection of two ideal-power inclusions. -/
public noncomputable def gradedProj
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    gradedComplex₂ X I ι F n ⟶ gradedComplex X I ι F n where
  f k := quotientProj (idealPowerIncl X I ι (n + 1) (F.X k)) (idealPowerIncl X I ι n (F.X k))
  comm' i j h := by
    subst h
    refine Eq.trans (congrArg (quotientProj (idealPowerIncl X I ι (n + 1) (F.X i))
      (idealPowerIncl X I ι n (F.X i)) ≫ ·) (gradedComplex_d X I ι F n i)) ?_
    refine Eq.trans (gradedProj_comm X I ι F n i) ?_
    exact congrArg (fun g => g ≫ quotientProj (idealPowerIncl X I ι (n + 1) (F.X (i + 1)))
      (idealPowerIncl X I ι n (F.X (i + 1)))) (gradedComplex₂_d X I ι F n i).symm

/-- **The short exact sequence of complexes whose connecting map is the Bockstein operator:**
`0 → F ⊗ I^{n+1}/I^{n+2} → F ⊗ I^n/I^{n+2} → F ⊗ I^n/I^{n+1} → 0`. -/
public noncomputable def gradedShortComplex
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    ShortComplex (CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :=
  ShortComplex.mk (gradedIncl X I ι F n) (gradedProj X I ι F n)
    (HomologicalComplex.hom_ext _ _ (fun k =>
      (quotientShortComplex (idealPowerIncl X I ι (n + 1) (F.X k))
        (idealPowerIncl X I ι n (F.X k))).zero))

/-- **The sequence of successive quotients is short exact**, because it is degreewise the
successive-quotient sequence of two monomorphisms, which are monomorphisms because the terms of
`F` are `I`-torsion-free. -/
public theorem gradedShortComplex_shortExact
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    (gradedShortComplex X I ι F n).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun k => ?_)
  have := idealPowerIncl_mono X I ι (F.X k) (hF k) (n + 1)
  have := idealPowerIncl_mono X I ι (F.X k) (hF k) n
  exact Stacks.IdealTorsion.Bockstein.quotientShortComplex_shortExact _ _

/-! ### The chain-level Bockstein operator -/

/-- **The chain-level Bockstein operator**
`H^n(F ⊗ I^n/I^{n+1}) ⟶ H^{n+1}(F ⊗ I^{n+1}/I^{n+2})`: the connecting map of the short exact
sequence of complexes `0 → F ⊗ I^{n+1}/I^{n+2} → F ⊗ I^n/I^{n+2} → F ⊗ I^n/I^{n+1} → 0`. -/
public noncomputable def bocksteinChainOperator
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    (gradedComplex X I ι F n).homology n ⟶
      (gradedComplex X I ι F (n + 1)).homology (n + 1) :=
  (gradedShortComplex_shortExact X I ι F hF n).δ n (n + 1) rfl

/-- **The comparison of Tag 0GT9 intertwines the differential of the décalage with the
Bockstein operator.**  The connecting map sends the cocycle class of the first projection of
`(η_I F)^n` to the class of its second projection, and `Eta.etaObj_d_fst` says that this second
projection is the first projection of the differential of the décalage.  This is the source's
"essentially because `β` sends the class of `f^i s'` to the class of `f^{i+1} t`". -/
public theorem etaToGradedHomology_comp_bocksteinChainOperator
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    etaToGradedHomology X I ι F n ≫ bocksteinChainOperator X I ι F hF n =
      (etaObj X I ι F hF).d n (n + 1) ≫ etaToGradedHomology X I ι F (n + 1) := by
  have hx₃ : etaToGraded X I ι F n ≫ (gradedComplex X I ι F n).d n (n + 1) = 0 :=
    (congrArg (etaToGraded X I ι F n ≫ ·) (gradedComplex_d X I ι F n n)).trans
      (etaToGraded_comp_d X I ι F n)
  have hx₂ : (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1))) ≫
      cokernel.π (idealPowerIncl₂ X I ι n (F.X n))) ≫
        quotientProj (idealPowerIncl X I ι (n + 1) (F.X n))
          (idealPowerIncl X I ι n (F.X n)) = etaToGraded X I ι F n :=
    (Category.assoc _ _ _).trans
      (congrArg (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1))) ≫ ·)
        (π_quotientProj (idealPowerIncl X I ι (n + 1) (F.X n))
          (idealPowerIncl X I ι n (F.X n))))
  have hx₁ : (pullback.snd (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1))) ≫
      cokernel.π (idealPowerIncl X I ι (n + 1) (F.X (n + 1)))) ≫
        quotientIncl (idealPowerIncl X I ι (n + 1) (F.X (n + 1)))
          (idealPowerIncl X I ι n (F.X (n + 1))) =
      (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1))) ≫
      cokernel.π (idealPowerIncl₂ X I ι n (F.X n))) ≫
        gradedD₂ X I ι F n n := by
    conv_lhs => rw [Category.assoc, π_quotientIncl, ← Category.assoc]
    conv_rhs => rw [Category.assoc, cokernel_π_gradedD₂, ← Category.assoc,
      pullback.condition]
  have hδ := (gradedShortComplex_shortExact X I ι F hF n).δ_eq n (n + 1) rfl
    (etaToGraded X I ι F n) hx₃
    (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
      (idealPowerIncl X I ι n (F.X (n + 1))) ≫
      cokernel.π (idealPowerIncl₂ X I ι n (F.X n))) hx₂
    (pullback.snd (idealPowerMap X I n (F.d n (n + 1)))
      (idealPowerIncl X I ι n (F.X (n + 1))) ≫
      cokernel.π (idealPowerIncl X I ι (n + 1) (F.X (n + 1))))
    (hx₁.trans (congrArg (_ ≫ ·) (gradedComplex₂_d X I ι F n n).symm))
    (n + 1 + 1) ((ComplexShape.up ℤ).next_eq' rfl)
  -- `Eta.etaObj_d_fst`: the chosen lift is what the differential of the décalage reads as the
  -- first projection in degree `n + 1`.
  have hfst : (etaObj X I ι F hF).d n (n + 1) ≫ etaToGraded X I ι F (n + 1) =
      pullback.snd (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1))) ≫
        cokernel.π (idealPowerIncl X I ι (n + 1) (F.X (n + 1))) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun g => g ≫ cokernel.π (idealPowerIncl X I ι (n + 1) (F.X (n + 1))))
        (Eta.etaObj_d_fst X I ι F hF n))
  -- The left-hand side of `hδ` is the comparison followed by the Bockstein operator.
  refine Eq.trans (Eq.trans (Category.assoc _ _ _) hδ) ?_
  -- The right-hand side is the differential of the décalage followed by the comparison, the
  -- two lifts to the cocycles agreeing by `hfst`.
  refine Eq.trans (congrArg
    (fun g => g ≫ (gradedComplex X I ι F (n + 1)).homologyπ (n + 1)) ?_)
    (Category.assoc _ _ _)
  refine (cancel_mono ((gradedComplex X I ι F (n + 1)).iCycles (n + 1))).1 ?_
  refine Eq.trans (HomologicalComplex.liftCycles_i _ _ _ _ _) ?_
  exact hfst.symm.trans ((congrArg ((etaObj X I ι F hF).d n (n + 1) ≫ ·)
    (etaToGradedCycles_i X I ι F (n + 1)).symm).trans (Category.assoc _ _ _).symm)

/-- **The Bockstein operator squares to zero.**  The comparison of Tag 0GT9 is a surjection
intertwining it with the differential of the décalage, which squares to zero. -/
public theorem bocksteinChainOperator_comp_bocksteinChainOperator
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    bocksteinChainOperator X I ι F hF n ≫ bocksteinChainOperator X I ι F hF (n + 1) = 0 := by
  have _h := epi_etaToGradedHomology X I ι F hF n
  refine (cancel_epi (etaToGradedHomology X I ι F n)).1 ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ bocksteinChainOperator X I ι F hF (n + 1))
    (etaToGradedHomology_comp_bocksteinChainOperator X I ι F hF n)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg ((etaObj X I ι F hF).d n (n + 1) ≫ ·)
    (etaToGradedHomology_comp_bocksteinChainOperator X I ι F hF (n + 1))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ etaToGradedHomology X I ι F (n + 1 + 1))
    ((etaObj X I ι F hF).d_comp_d n (n + 1) (n + 1 + 1))) ?_
  exact zero_comp.trans comp_zero.symm

/-- **The chain-level form of the complex `H^•(F/I)` of Tag 0GT8**, the right-hand side of
Tag 0GT9: degree-`n` term the `n`-th cohomology sheaf of `F ⊗ I^n/I^{n+1}`, differential the
Bockstein operator. -/
public noncomputable def bocksteinChainComplex
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    CochainComplex (SheafOfModules.{u} Oₓ) ℤ :=
  CochainComplex.of (fun n => (gradedComplex X I ι F n).homology n)
    (bocksteinChainOperator X I ι F hF)
    (bocksteinChainOperator_comp_bocksteinChainOperator X I ι F hF)

@[simp] public theorem bocksteinChainComplex_X
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    (bocksteinChainComplex X I ι F hF).X n = (gradedComplex X I ι F n).homology n := rfl

public theorem bocksteinChainComplex_d
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    (bocksteinChainComplex X I ι F hF).d n (n + 1) =
      bocksteinChainOperator X I ι F hF n := by
  simp only [bocksteinChainComplex, CochainComplex.of_d]

/-! ### The comparison of Tag 0GT9 as a morphism of complexes -/

/-- The commuting square of the comparison, stated for an arbitrary morphism `e` of the
décalage terms in place of the differential of the décalage.  The differential's source and
target are spelled as terms of the complex `η_I F` rather than as `Eta.etaTerm`, which the
rewrites below cannot see through; taking it as a variable at the spelling the cokernel
calculus presents removes the seam. -/
private theorem reductionComparison_comp_of
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ)
    (e : etaTerm X I ι F n ⟶ etaTerm X I ι F (n + 1))
    (he : e ≫ etaToGradedHomology X I ι F (n + 1) =
      etaToGradedHomology X I ι F n ≫ bocksteinChainOperator X I ι F hF n) :
    reductionComparison X I ι F n ≫ bocksteinChainOperator X I ι F hF n =
      modIdealMap X I ι e ≫ reductionComparison X I ι F (n + 1) := by
  refine (cancel_epi (cokernel.π (idealPowerIncl X I ι 0 (etaTerm X I ι F n)))).1 ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ bocksteinChainOperator X I ι F hF n)
    (cokernel_π_reductionComparison X I ι F n)) ?_
  refine Eq.trans he.symm ?_
  refine Eq.trans (congrArg (e ≫ ·)
    (cokernel_π_reductionComparison X I ι F (n + 1)).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun g => g ≫ reductionComparison X I ι F (n + 1))
    (cokernel_π_modIdealMap X I ι e).symm) ?_
  exact Category.assoc _ _ _

/-- **The comparison of Tag 0GT9 as a morphism of complexes:** the reduction
`η_I F ⊗ O_X/I` of the décalage maps to the chain-level Bockstein complex `H^•(F/I)`, degree by
degree by `reductionComparison`.  The squares commute because the Bockstein operator reads the
differential of the décalage on cocycle classes
(`etaToGradedHomology_comp_bocksteinChainOperator`).

This is the canonical comparison of the tag at the level of complexes.  Degreewise it is epi
(`epi_reductionComparison`) and not mono, so the tag's assertion is not visible degree by degree;
that this map is nonetheless a quasi-isomorphism is proved, in Situation 0GT4, as
`quasiIso_reductionComparisonChainMap_of_isLocallyGeneratedByRegular` in
`EtaSheafReductionDerivedIsoRegular.lean`, and with it the tag's isomorphism in `D(O_X)`
(`reductionComparisonQIsoOfRegular` in the same file). -/
public noncomputable def reductionComparisonChainMap
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    etaModIdealComplex X I ι F hF ⟶ bocksteinChainComplex X I ι F hF where
  f n := reductionComparison X I ι F n
  comm' i j h := by
    subst h
    refine Eq.trans (congrArg (reductionComparison X I ι F i ≫ ·)
      (bocksteinChainComplex_d X I ι F hF i)) ?_
    refine Eq.trans (reductionComparison_comp_of X I ι F hF i
      ((etaObj X I ι F hF).d i (i + 1))
      (etaToGradedHomology_comp_bocksteinChainOperator X I ι F hF i).symm) ?_
    exact congrArg (fun g => g ≫ reductionComparison X I ι F (i + 1))
      (etaModIdealComplex_d X I ι F hF i).symm

@[simp] public theorem reductionComparisonChainMap_f
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (n : ℤ) :
    (reductionComparisonChainMap X I ι F hF).f n = reductionComparison X I ι F n := rfl

/-- **The comparison of complexes of Tag 0GT9 is an epimorphism**, because it is degreewise
one (`epi_reductionComparison`). -/
public theorem epi_reductionComparisonChainMap
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) :
    Epi (reductionComparisonChainMap X I ι F hF) :=
  HomologicalComplex.epi_of_epi_f _ (fun n => epi_reductionComparison X I ι F hF n)

end Stacks.IdealTorsion.Reduction

end
