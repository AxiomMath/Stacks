module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafBocksteinChain
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafIdealPowerTensorLeft
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPowerQuotientResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.DerivedTensorSingleTriangleDelta

/-!
# The successive-power sequence tensored with a complex

Let `X` be a ringed space, `ι : I ⟶ O_X` an invertible ideal subsheaf and `P` a cochain complex of
`O_X`-modules.  The total tensor complex `Tot(P ⊗ A[0])` of `P` with a sheaf `A` placed in degree
`0` is the termwise complex `p ↦ P^p ⊗ A`.  For `A = I^n/I^{n+1}` the term `P^p ⊗ I^n/I^{n+1}` is
the cokernel of `I^{n+1} ⊗ P^p ⟶ I^n ⊗ P^p`, so `Tot(P ⊗ (I^n/I^{n+1})[0])` is the complex
`Reduction.gradedComplex X I ι P n` of the chain-level form of Tag 0GT9, and the successive-power
sequence `I^{n+1}/I^{n+2} → I^n/I^{n+2} → I^n/I^{n+1}` tensored with `P` is the short complex
`Reduction.gradedShortComplex X I ι P n` whose connecting map is the chain-level Bockstein
operator.

## Main definitions

* `Stacks.IdealTorsion.ReductionDerived.totalPowerQuotientIso`:
  `Tot(P ⊗ (I^n/I^{n+1})[0]) ≅ gradedComplex X I ι P n`.
* `Stacks.IdealTorsion.ReductionDerived.totalPowerQuotientTwoIso`:
  `Tot(P ⊗ (I^n/I^{n+2})[0]) ≅ gradedComplex₂ X I ι P n`.
* `Stacks.IdealTorsion.ReductionDerived.totalPowerQuotientShortComplexIso`: the isomorphism of
  short complexes of cochain complexes from the successive-power sequence tensored with `P` to
  `gradedShortComplex X I ι P n`.

## References

* [Stacks Project, Tag 0GT8](https://stacks.math.columbia.edu/tag/0GT8)
* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.IdealTorsion.Eta (idealPowerTerm idealPowerIncl idealPowerMap)

universe u

namespace Stacks.IdealTorsion.ReductionDerived

open Stacks.IdealTorsion.Bockstein Stacks.IdealTorsion.Reduction

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
local notation "𝒪" => SheafOfModules.unit Oₓ

/-- **The termwise complex `P ⊗ I^n/I^{n+1}` is `gradedComplex X I ι P n`**: in degree `k`, the
cokernel identification `powerQuotientTensorIso` at `P^k`. -/
public noncomputable def rowPowerQuotientIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    CochainComplex.KFlatBifunctor.rowComplex
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) P
        (powerQuotient X I ι n) ≅
      gradedComplex X I ι P n :=
  HomologicalComplex.Hom.isoOfComponents (fun k => powerQuotientTensorIso X I ι (P.X k) n)
    (by
      rintro k _ rfl
      refine Eq.trans ?_ (powerQuotientTensorIso_natural X I ι (P.d k (k + 1)) n).symm
      congr 1
      refine (gradedComplex_d X I ι P n k).trans ?_
      exact (cancel_epi (cokernel.π _)).1 ((cokernel_π_gradedD X I ι P n k).trans
        (cokernel.π_desc _ _ _).symm))

/-- **The termwise complex `P ⊗ I^n/I^{n+2}` is `gradedComplex₂ X I ι P n`.** -/
public noncomputable def rowPowerQuotientTwoIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    CochainComplex.KFlatBifunctor.rowComplex
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) P
        (cokernel (idealPowerIncl X I ι (n + 1) 𝒪 ≫ idealPowerIncl X I ι n 𝒪)) ≅
      gradedComplex₂ X I ι P n :=
  HomologicalComplex.Hom.isoOfComponents (fun k => powerQuotientTwoTensorIso X I ι (P.X k) n)
    (by
      rintro k _ rfl
      refine Eq.trans ?_ (powerQuotientTwoTensorIso_natural X I ι (P.d k (k + 1)) n).symm
      congr 1
      refine (gradedComplex₂_d X I ι P n k).trans ?_
      exact (cancel_epi (cokernel.π _)).1 ((cokernel_π_gradedD₂ X I ι P n k).trans
        (cokernel.π_desc _ _ _).symm))

/-! ### Short complexes tensored with a complex -/



/-- A short complex of `O_X`-modules tensored termwise with a complex `G`: the short complex
of the termwise complexes `G ⊗ S.X₁ → G ⊗ S.X₂ → G ⊗ S.X₃`. -/
public noncomputable abbrev rowShortComplex (G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (S : ShortComplex (SheafOfModules.{u} Oₓ)) :
    ShortComplex (CochainComplex (SheafOfModules.{u} Oₓ) ℤ) :=
  ShortComplex.mk
    (CochainComplex.KFlatBifunctor.rowComplexMapRight
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G S.f)
    (CochainComplex.KFlatBifunctor.rowComplexMapRight
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G S.g)
    (HomologicalComplex.hom_ext _ _ (fun k => by
      change ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj (G.X k)).map
          S.f ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj
            (G.X k)).map S.g = 0
      rw [← Functor.map_comp, S.zero, Functor.map_zero]))

/-- **`Tot(G ⊗ S[0])` is the termwise short complex `G ⊗ S`**, by `totalSingleIso` in each of
the three places. -/
public noncomputable def totalSingleShortComplexIso
    (G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (S : ShortComplex (SheafOfModules.{u} Oₓ)) :
    (S.map (HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0)).map
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj G) ≅ rowShortComplex X G S :=
  ShortComplex.isoMk
    (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G S.X₁)
    (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G S.X₂)
    (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G S.X₃)
    (CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right _ G S.f).symm
    (CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right _ G S.g).symm

/-- `totalSingleShortComplexIso`, with the source written through the composite functor
`(-)[0] ⋙ Tot(G ⊗ -)`. -/
public noncomputable def totalSingleShortComplexIsoComp
    (G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (S : ShortComplex (SheafOfModules.{u} Oₓ)) :
    S.map (HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0 ⋙
        (Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj G) ≅ rowShortComplex X G S :=
  ShortComplex.isoMk
    (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G S.X₁)
    (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G S.X₂)
    (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf) G S.X₃)
    (CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right _ G S.f).symm
    (CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right _ G S.g).symm

/-- **The consecutive ideal-power sequence tensored on the left by `N` is the cokernel sequence
of `I^{n+1} ⊗ N ⟶ I^n ⊗ N`.** -/
public noncomputable def tensorPowerInclSequenceIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (powerInclSequence X I ι n).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N) ≅
      ShortComplex.cokernelSequence (idealPowerIncl X I ι n N) :=
  ShortComplex.isoMk (idealPowerTensorLeftIso X I N (n + 1)) (idealPowerTensorLeftIso X I N n)
    (powerQuotientTensorIso X I ι N n) (idealPowerTensorLeftIso_incl X I ι N n).symm
    (powerQuotientTensorIso_π X I ι N n).symm

/-- **The consecutive ideal-power sequence stays short exact after tensoring with a module `N`
on which `I^{n+1} ⊗ N ⟶ I^n ⊗ N` is injective**, e.g. an `I`-torsion-free one. -/
public theorem tensorPowerInclSequence_shortExact (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (N : SheafOfModules.{u} Oₓ) (n : ℤ) (hN : Mono (idealPowerIncl X I ι n N)) :
    ((powerInclSequence X I ι n).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj N)).ShortExact :=
  have : Mono (ShortComplex.cokernelSequence (idealPowerIncl X I ι n N)).f := hN
  ShortComplex.shortExact_of_iso (tensorPowerInclSequenceIso X I ι N n).symm
    (ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) inferInstance
      inferInstance)

/-- **`Tot(G ⊗ (0 → I^{n+1} → I^n → I^n/I^{n+1} → 0)[0])` is short exact** for a complex `G` on
whose terms `I^{n+1} ⊗ - ⟶ I^n ⊗ -` is injective (e.g. a complex of `I`-torsion-free modules): it
is degreewise the consecutive ideal-power sequence tensored with a term of `G`. -/
public theorem totalPowerInclSequence_shortExact (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ)
    (hG : ∀ k : ℤ, Mono (idealPowerIncl X I ι n (G.X k))) :
    ((powerInclSequenceSingle X I ι n).map
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj G)).ShortExact :=
  ShortComplex.shortExact_of_iso (totalSingleShortComplexIso X G _).symm
    (HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun k =>
      tensorPowerInclSequence_shortExact X I ι (G.X k) n (hG k)))

/-- **The successive-power sequence tensored termwise with `P` is `gradedShortComplex`.** -/
public noncomputable def rowPowerQuotientShortComplexIso (I : SheafOfModules.{u} Oₓ)
    (ι : I ⟶ 𝒪) [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    rowShortComplex X P (powerQuotientShortComplex X I ι n) ≅ gradedShortComplex X I ι P n :=
  ShortComplex.isoMk (rowPowerQuotientIso X I ι P (n + 1)) (rowPowerQuotientTwoIso X I ι P n)
    (rowPowerQuotientIso X I ι P n)
    (HomologicalComplex.hom_ext _ _ (fun k =>
      (powerQuotientShortComplexTensorIso X I ι (P.X k) n).hom.comm₁₂))
    (HomologicalComplex.hom_ext _ _ (fun k =>
      (powerQuotientShortComplexTensorIso X I ι (P.X k) n).hom.comm₂₃))

/-- **`Tot(P ⊗ (I^{n+1}/I^{n+2} → I^n/I^{n+2} → I^n/I^{n+1})[0])` is
`gradedShortComplex X I ι P n`**, the short exact sequence of complexes whose connecting map is
the chain-level Bockstein operator. -/
public noncomputable def totalPowerQuotientShortComplexIso (I : SheafOfModules.{u} Oₓ)
    (ι : I ⟶ 𝒪) [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    (powerQuotientShortComplex X I ι n).map
        (HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0 ⋙
          (Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P) ≅
      gradedShortComplex X I ι P n :=
  totalSingleShortComplexIsoComp X P _ ≪≫ rowPowerQuotientShortComplexIso X I ι P n

/-- **`Tot(P ⊗ (successive-power sequence)[0])` is short exact** for a complex `P` of
`I`-torsion-free modules, being isomorphic to `gradedShortComplex X I ι P n`. -/
public theorem totalPowerQuotientShortComplex_shortExact (I : SheafOfModules.{u} Oₓ)
    (ι : I ⟶ 𝒪) [Mono ι] [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (P : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hP : ∀ k : ℤ, IsIdealTorsionFree X ι (P.X k)) (n : ℤ) :
    ((powerQuotientShortComplex X I ι n).map
        (HomologicalComplex.single (SheafOfModules.{u} Oₓ) (ComplexShape.up ℤ) 0 ⋙
          (Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P)).ShortExact :=
  ShortComplex.shortExact_of_iso (totalPowerQuotientShortComplexIso X I ι P n).symm
    (gradedShortComplex_shortExact X I ι P hP n)

end Stacks.IdealTorsion.ReductionDerived

end
