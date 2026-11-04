module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRowQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Computes07LGColumns

/-!
# [Stacks, Tag 07LG] from the completed de Rham rows

This file reduces [Stacks, Proposition 60.21.3, Tag 07LG] to the per-degree connections, a
degreewise homotopy equivalence of the completed de Rham complex `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` of
each cosimplicial degree `b` with one comparison complex, and an identification in cohomology of
`M ⊗^∧_D Ω^*_D` with the completed de Rham complex `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` of degree zero.
These row hypotheses are in the shape in which [Stacks, Lemma 60.20.2, Tag 07LD] produces its
conclusion.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.computes07LG_of_connections_of_deRhamRows`:
  `...SmallSite.Computes07LG` from the per-degree connections, a degreewise homotopy
  equivalence of each row with one comparison complex, and the degree-zero identification.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.20.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
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

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from the per-degree connections and the completed
de Rham form of the rows.**

The row hypotheses are the ones [Stacks, Lemma 60.20.2, Tag 07LD] produces: a comparison complex
given as a graded family `N` with a square-zero family of additive differentials `dL`, a morphism
`rho` of the double complex into its constant cosimplicial object, and in each cosimplicial
degree `b` a degreewise homotopy equivalence of `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` with `N` — the maps
`iotaDeg`, `piDeg`, the homotopy `hDeg`, the two chain-map identities `hiota` and `hpi`, the
retraction `hretract`, the two homotopy identities `h0` and `hsucc`, and the section property
`hsec` of `rho` against `iotaDeg`.

`hrow0` is the bare identification of `M ⊗^∧_D Ω^*_D` with the completed de Rham complex
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` of the cosimplicial degree zero, in cohomology. -/
public theorem computes07LG_of_connections_of_deRhamRows
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
    (N : ∀ (F : SheafOfModules.{u} (structureSheaf S)), F.IsQuasicoherentOnSite → ℕ → Type u)
    [instN : ∀ F hF i, AddCommGroup (N F hF i)]
    (dL : ∀ F hF i, N F hF i →+ N F hF (i + 1))
    (hdL : ∀ F hF (i : ℕ) (x : N F hF i), dL F hF (i + 1) (dL F hF i x) = 0)
    (rho : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      wholeSpaceDoubleComplex hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF) ⟶
        AlgebraicTopology.constantCosimplicialCochainComplex.obj
          (deRhamComparisonTarget (N F hF) (dL F hF) (hdL F hF)))
    (iotaDeg : ∀ F hF (b i : ℕ), N F hF i →+
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
        (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj i b)
    (piDeg : ∀ F hF (b i : ℕ),
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
        (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj i b →+ N F hF i)
    (hDeg : ∀ F hF (b i : ℕ),
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj (i + 1) b →+
        (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj i b)
    (hiota : ∀ F hF (b i : ℕ) (x : N F hF i),
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).degreeDifferential b i (iotaDeg F hF b i x) =
        iotaDeg F hF b (i + 1) (dL F hF i x))
    (hpi : ∀ F hF (b i : ℕ) (y :
        (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj i b),
      dL F hF i (piDeg F hF b i y) = piDeg F hF b (i + 1)
        ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).degreeDifferential b i y))
    (hretract : ∀ F hF (b i : ℕ) (x : N F hF i), piDeg F hF b i (iotaDeg F hF b i x) = x)
    (h0 : ∀ F hF (b : ℕ) (x :
        (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj 0 b),
      hDeg F hF b 0
          ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
            (hnabla F hF) (hsqz F hF)).degreeDifferential b 0 x) +
        iotaDeg F hF b 0 (piDeg F hF b 0 x) = x)
    (hsucc : ∀ F hF (b i : ℕ) (x :
        (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj (i + 1) b),
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
            (hnabla F hF) (hsqz F hF)).degreeDifferential b i (hDeg F hF b i x) +
          hDeg F hF b (i + 1)
            ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
              (hnabla F hF) (hsqz F hF)).degreeDifferential b (i + 1) x) +
          iotaDeg F hF b (i + 1) (piDeg F hF b (i + 1) x) = x)
    (hsec : ∀ F hF (b i : ℕ) (x : N F hF i),
      ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).rowDeRhamComparison (rho F hF) b).f i
        (iotaDeg F hF b i x) = x)
    (hrow0 : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (j : ℕ), Nonempty
        ((crystalDeRhamComplex S A Dr g Om der p dx wedge deRham hleib R h07IT F hF
            (squareZero07JG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hext hdx
              F hF)).homology j ≅
          ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
            (hnabla F hF) (hsqz F hF)).degreeDeRhamComplex 0).homology j)) :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT
      (squareZero07JG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hext hdx) :=
  computes07LG_of_connections_of_rows S A Dr g Om der p dx wedge deRham hleib hp R h07IT
    hext hdx nabla hnabla hsqz
    (fun F hF ↦ deRhamComparisonTarget (N F hF) (dL F hF) (hdL F hF)) rho
    (fun F hF b ↦ CosimplicialCompletedPair.quasiIso_flipMap_of_deRhamAddHomHomotopyEquiv
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
        (hnabla F hF) (hsqz F hF))
      (N F hF) (dL F hF) (hdL F hF) (rho F hF) (iotaDeg F hF) (piDeg F hF) (hDeg F hF)
      (hiota F hF) (hpi F hF) (hretract F hF) (h0 F hF) (hsucc F hF) (hsec F hF) b)
    (fun F hF j ↦ ⟨AddCommGrpCat.uliftFunctor.{u + 1, u}.mapIso
      ((hrow0 F hF j).some.trans
        ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).rowZeroHomologyIso j).symm)⟩)

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
