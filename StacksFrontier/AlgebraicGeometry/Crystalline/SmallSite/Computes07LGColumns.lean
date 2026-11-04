module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialPair
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Computes07LGEdgesExterior

/-!
# The reduction of [Stacks, Tag 07LG] to the connections and the rows

`...SmallSite.computes07LG_of_edges_of_isGradedExterior` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Computes07LGEdgesExterior.lean` reduces
[Stacks, Proposition 60.21.3, Tag 07LG] to seven inputs: the double complex `K`, the acyclicity
`hcolumns` of its columns off zero, the row target and comparison `rowTarget` and
`rowComparison`, their quasi-isomorphy `hrows`, and the two edge identifications `hrow0` and
`hcolumn0`.

Three of those seven are **theorems** once `K` is the double complex of the cosimplicial module
`M(•)` of a general crystal, and this module plugs them in:

* `K` itself is `...SmallSite.wholeSpaceDoubleComplex`, built in
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/WholeSpaceCosimplicialPair.lean` out of
  the module `M(b) = lim_e Γ((X, T(b)_e, δ(b)), ℱ)` of [Stacks, Proposition 60.20.1, Tag 07JN]
  and a completed connection in each cosimplicial degree;
* `hcolumns` is `...SmallSite.isZero_homology_wholeSpaceDoubleComplex_X`, which is
  [Stacks, Lemma 60.19.3, Tag 07LF];
* `hcolumn0` is `...SmallSite.wholeSpaceDoubleComplexColumnZeroHomologyIso`.

What is left is the cosimplicial family of connections — the three fields `nabla`,
`nabla_tensorMap`, `isSquareZero` of `Crystalline.CosimplicialCompletedPair` — and the row half
`rowTarget`, `rowComparison`, `hrows`, `hrow0`, which is [Stacks, Lemma 60.20.2, Tag 07LD] read
in each cosimplicial degree together with the identification of the row `b = 0`.

## Main result

* `...SmallSite.computes07LG_of_connections_of_rows` — the reduction of [Stacks, Tag 07LG] to
  the per-degree connections and the row data.

## Implementation notes

No tag attribute is placed here: [Stacks, Tag 07LG] itself is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`. This module serves an earlier reduction of it
with named hypotheses, and discharges the column half of the double complex hypotheses, for a
general quasi-coherent crystal.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.20.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

universe u uI

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial

namespace Crystalline

open DividedPowers

namespace GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
  (Dr : DividedPowerRing.{u}) (g : A →+* Dr) (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module (Dr : Type u) (Om i)] [Module (Dr : Type u)ᵐᵒᵖ (Om 1)]
  [IsCentralScalar (Dr : Type u) (Om 1)] (der : DividedPowerDerivation A Dr g (Om 1)) (p : ℕ)
  {ι : Type uI} [Fintype ι] (dx : ι → Om 1)
  (wedge : ∀ i, Om i →ₗ[(Dr : Type u)] Om 1 →ₗ[(Dr : Type u)] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1))
  (hleib : CompletedDeRham.IsGradedLeibniz Dr Om wedge deRham
    (derivationFun A Dr g (Om 1) der))
  [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  (R : Reduction07JG S A Dr g (Om 1) der p dx hp)
  (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
    F.IsQuasicoherentOnSite → IsSheafCrystal F)

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from the per-degree connections and the rows.**

The double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of the source's proof is built here out
of the cosimplicial module `M(•)` of [Stacks, Proposition 60.20.1, Tag 07JN] and the three
carried connection fields, and the two hypotheses of
`...SmallSite.computes07LG_of_edges_of_isGradedExterior` that concern its columns are supplied:
the acyclicity of the columns `a > 0` and the identification of the column `a = 0`.

The remaining inputs are the connections themselves and the row half of the source's argument.

Nothing is weakened: the conclusion is `...SmallSite.Computes07LG` at the constructed
square-zero family `...SmallSite.squareZero07JG`, as in the reduction this one calls. -/
public theorem computes07LG_of_connections_of_rows
    (hext : CompletedDeRham.IsGradedExterior (Dr : Type u) Om wedge deRham)
    (hdx : ∀ j, deRham 1 (dx j) = 0)
    (nabla : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (b : ℕ), CompletedConnection S.p ((wholeSpaceDPAlgebra hp).completedRing S.p b)
        ((wholeSpaceDPAlgebra hp).forms S.p 1 b) ((wholeSpaceDPAlgebra hp).differential S.p b)
        ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier b))
    (hnabla : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      {m n : SimplexCategory} (φ : m ⟶ n)
      (x : (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier m.len),
      nabla F hF n.len
          ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).map φ x) =
        (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).tensorMap φ 1
          (nabla F hF m.len x))
    (hsqz : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (b : ℕ),
      CompletedDeRham.IsSquareZero S.p ((wholeSpaceDPAlgebra hp).completedRing S.p b)
        (fun a => (wholeSpaceDPAlgebra hp).forms S.p a b) ((wholeSpaceDPAlgebra hp).wedge S.p b)
        ((wholeSpaceDPAlgebra hp).deRham S.p b)
        ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier b)
        (nabla F hF b) ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p b))
    (rowTarget : ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      CochainComplex AddCommGrpCat.{u} ℕ)
    (rowComparison : ∀ (F : SheafOfModules.{u} (structureSheaf S))
      (hF : F.IsQuasicoherentOnSite),
      wholeSpaceDoubleComplex hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF) ⟶
        AlgebraicTopology.constantCosimplicialCochainComplex.obj (rowTarget F hF))
    (hrows : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (b : ℤ), QuasiIso ((StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map (rowComparison F hF))).f b))
    (hrow0 : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (j : ℕ), Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
          ((crystalDeRhamComplex S A Dr g Om der p dx wedge deRham hleib R h07IT F hF
            (squareZero07JG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hext hdx
              F hF)).homology j) ≅
        AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
          (((cosimplicialDoubleComplexFunctor.obj
            (wholeSpaceDoubleComplex hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
              (hnabla F hF) (hsqz F hF))).flip.X 0).homology (j : ℤ)))) :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT
      (squareZero07JG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hext hdx) :=
  computes07LG_of_edges_of_isGradedExterior S A Dr g Om der p dx wedge deRham hleib hp R h07IT
    hext hdx
    (fun F hF ↦ wholeSpaceDoubleComplex hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
      (hnabla F hF) (hsqz F hF))
    (fun F hF n hn j ↦ isZero_homology_wholeSpaceDoubleComplex_X hp
      (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF) (hnabla F hF) (hsqz F hF) n hn j)
    rowTarget rowComparison hrows hrow0
    (fun F hF _ j ↦ ⟨wholeSpaceDoubleComplexColumnZeroHomologyIso hp
      (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF) (hnabla F hF) (hsqz F hF) j⟩)

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
