module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeRowQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamCohomology07LG

/-!
# [Stacks, Proposition 60.21.3, Tag 07LG]: the de Rham complex of a crystal computes its
crystalline cohomology

In the situation of [Stacks, Proposition 60.20.1, Tag 07JN] — `X = Spec(C)` over `S = Spec(A)`,
both affine, with `p` nilpotent on `X` — let `ℱ` be a crystal in quasi-coherent
`𝒪_{X/S}`-modules on `Cris(X/S)` and `(M, ∇)` the module with connection over `D` corresponding to
it ([Stacks, Lemma 60.17.3, Tag 07JG], `...SmallSite.crystalPairFunctor`).  Then the complex
`M ⊗^∧_D Ω^*_D` (`...SmallSite.crystalPairDeRhamComplex`) computes `RΓ(Cris(X/S), ℱ)`: its
cohomology in every degree `j` is `H^j(Cris(X/S), ℱ)`.

## The proof, following the source

The double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of the cosimplicial pair of the crystal
(`...SmallSite.crystalCosimplicialPair`: the module `M(b) = lim_e Γ(T(b)_e, ℱ)` of the
cosimplicial envelope `D(•)`, with the base change of `∇` along the coprojection `σ_b`, which makes
sense because `ℱ` is a crystal) has acyclic columns `a > 0` ([Stacks, Lemma 60.19.3, Tag 07LF]) and
column zero `M(•)`, which computes `RΓ(Cris(X/S), ℱ)` by [Stacks, Tag 07JN]; and its rows are
quasi-isomorphic to the row zero `M ⊗^∧_D Ω^*_D` along the coprojections, by
[Stacks, Lemma 60.21.2, Tag 07LD] and [Stacks, Lemma 60.17.5, Tag 07L2]
(`Crystalline.quasiIso_baseChangePair_rowFromZeroHom`).  The two degenerations of the double
complex are assembled in `...SmallSite.crystalPairDeRhamCohomologyIsoOfQuasiIso`.

## Main results

* `...SmallSite.quasiIso_crystalCosimplicialPair_rowFromZeroHom` — the rows of the double complex
  of the crystal are quasi-isomorphic to the row zero.
* `...SmallSite.crystalPairDeRhamCohomologyIso` — `H^j(M ⊗^∧_D Ω^*_D) ≅ H^j(Cris(X/S), ℱ)`.
* `...SmallSite.crystalPairDeRhamComplex_computesCohomology` — **[Stacks, Tag 07LG].**

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Simplicial

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp] (Fc : QuasiCoherentCrystal S)

/-- **The rows of the double complex of a crystal are quasi-isomorphic to the row zero**: every
coprojection `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` of the cosimplicial pair
of the crystal is a quasi-isomorphism, by `Crystalline.quasiIso_baseChangePair_rowFromZeroHom`. -/
theorem quasiIso_crystalCosimplicialPair_rowFromZeroHom (b : ℕ) :
    QuasiIso ((crystalCosimplicialPair hp Fc).rowFromZeroHom b) :=
  quasiIso_baseChangePair_rowFromZeroHom (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpaceCosimplicialModule hp Fc) (crystalCoprojectionBeta hp Fc)
    (crystalCoprojectionBeta_of_tmul hp Fc) (crystalPairFormsConnection hp Fc)
    (crystalPairFormsConnection_horizontal_delta hp Fc)
    (hasIntegrableConnection_crystalPairFormsConnection hp Fc) b

/-- **The cohomology of `M ⊗^∧_D Ω^*_D` is the crystalline cohomology of the crystal**:
`H^j(M ⊗^∧_D Ω^*_D) ≅ H^j(Cris(X/S), ℱ)` for every `j`, the complex being lifted to the universe
in which crystalline cohomology is defined. -/
def crystalPairDeRhamCohomologyIso (j : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj ((crystalPairDeRhamComplex hp Fc).homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj) :=
  crystalPairDeRhamCohomologyIsoOfQuasiIso hp Fc
    (quasiIso_crystalCosimplicialPair_rowFromZeroHom hp Fc) j

/-- **[Stacks, Proposition 60.21.3, Tag 07LG]**: in the situation of
[Stacks, Proposition 60.20.1, Tag 07JN] (`X` and `S` affine, `p` nilpotent on `X`, and `D` the
completed envelope of any surjective polynomial presentation `A[x_i : i ∈ ι] → C`, supplied as the
instance `...SmallSite.WholeSpacePresentation S hp`, by default the tautological one), let `ℱ` be a
crystal in quasi-coherent `𝒪_{X/S}`-modules and `(M, ∇)` the module with connection over `D`
corresponding to it under [Stacks, Lemma 60.17.3, Tag 07JG] (`...SmallSite.crystalPairFunctor`).
Then the complex `M ⊗^∧_D Ω^*_D` (`...SmallSite.crystalPairDeRhamComplex`) computes
`RΓ(Cris(X/S), ℱ)`: for every `j`, `H^j(M ⊗^∧_D Ω^*_D) ≅ H^j(Cris(X/S), ℱ)`
(`...SmallSite.crystalPairDeRhamCohomologyIso`). -/
@[stacks 07LG "for any surjective polynomial presentation g : A[x_i : i ∈ ι] → C, supplied as \
the WholeSpacePresentation instance (the default instance is the tautological one): the \
complex M ⊗^∧_D Ω*_D of the pair (M, ∇) of a crystal in quasi-coherent \
modules computes RΓ(Cris(X/S), F): its cohomology in every degree j is H^j(Cris(X/S), F)"]
theorem crystalPairDeRhamComplex_computesCohomology :
    ∀ j : ℕ, Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        ((crystalPairDeRhamComplex hp Fc).homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj)) :=
  fun j => ⟨crystalPairDeRhamCohomologyIso hp Fc j⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
