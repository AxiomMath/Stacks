module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalCosimplicialPair
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceRowZeroCohomology

/-!
# The complex `M ⊗^∧_D Ω^*_D` of a crystal and its comparison with crystalline cohomology

For a crystal `ℱ` in quasi-coherent modules on the small crystalline site of an affine situation,
with `(M, ∇)` its pair under the functor of [Stacks, Lemma 60.17.3, Tag 07JG]
(`...SmallSite.crystalPairFunctor`), this module builds the complex `M ⊗^∧_D Ω^*_D` of
[Stacks, Proposition 60.21.3, Tag 07LG] — `...SmallSite.crystalPairDeRhamComplex` — and compares
its cohomology with `H^j(Cris(X/S), ℱ)` given that every coprojection
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} → M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` of the cosimplicial pair of the crystal
is a quasi-isomorphism (`...SmallSite.crystalPairDeRhamCohomologyIsoOfQuasiIso`).

## Main definitions

* `...SmallSite.crystalPairDeRhamComplex` — `M ⊗^∧_D Ω^*_D`.
* `...SmallSite.crystalPairDeRhamCohomologyIsoOfQuasiIso` — `H^j(M ⊗^∧_D Ω^*_D) ≅
  H^j(Cris(X/S), ℱ)` from the quasi-isomorphisms of the rows.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp] (Fc : QuasiCoherentCrystal S)

/-- **The complex `M ⊗^∧_D Ω^*_D` of [Stacks, Proposition 60.21.3, Tag 07LG]** for the pair
`(M, ∇) = ...SmallSite.crystalPairFunctor hp`.obj ℱ of [Stacks, Lemma 60.17.3, Tag 07JG]: its
module is `M = lim_e Γ(T_e, ℱ) = ...SmallSite.wholeSpaceSections hp ℱ ⦋0⦌`, the carrier of the
pair, its ring is the completed envelope `D = D̂(0)`, its forms are the completed divided power
forms `Ω̂^*_D` of [Stacks, Tag 07J9], and its connection is the connection
`...SmallSite.pairConnection` of the pair read in `Ω̂¹_D` through
`...SmallSite.crystalPairFormsEquiv` (`...SmallSite.crystalPairFormsConnection`). -/
def crystalPairDeRhamComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  CompletedDeRham.complex S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
    (fun a => (wholeSpaceDPAlgebra hp).forms S.p a 0) ((wholeSpaceDPAlgebra hp).wedge S.p 0)
    ((wholeSpaceDPAlgebra hp).deRham S.p 0) (wholeSpaceSections hp Fc ⦋0⦌)
    (crystalPairFormsConnection hp Fc) ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p 0)
    (isSquareZero_crystalPairFormsConnection hp Fc)

/-- The module of the complex is the module of the pair of [Stacks, Tag 07JG]. -/
alias crystalPair_carrier := crystalPairFunctor_obj_carrier

/-- The term of degree `a` of `M ⊗^∧_D Ω^*_D` is `M ⊗̂_D Ω̂^a_D`. -/
theorem crystalPairDeRhamComplex_X (a : ℕ) :
    (crystalPairDeRhamComplex hp Fc).X a =
      AddCommGrpCat.of (CompletedTensor S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
        ((wholeSpaceDPAlgebra hp).forms S.p a 0) (wholeSpaceSections hp Fc ⦋0⦌)) := rfl

/-- The differential of `M ⊗^∧_D Ω^*_D` is the de Rham differential of the connection. -/
theorem crystalPairDeRhamComplex_d (a : ℕ) :
    (crystalPairDeRhamComplex hp Fc).d a (a + 1) =
      AddCommGrpCat.ofHom (CompletedDeRham.differential S.p
        ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
        (fun a => (wholeSpaceDPAlgebra hp).forms S.p a 0) ((wholeSpaceDPAlgebra hp).wedge S.p 0)
        ((wholeSpaceDPAlgebra hp).deRham S.p 0) (wholeSpaceSections hp Fc ⦋0⦌)
        (crystalPairFormsConnection hp Fc) ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p 0) a) :=
  CompletedDeRham.complex_d _ _ _ _ _ _ _ _ _ a

/-- The cosimplicial pair of the crystal is the whole-space cosimplicial pair of its
connections. -/
theorem crystalCosimplicialPair_eq :
    crystalCosimplicialPair hp Fc =
      wholeSpaceCosimplicialPair hp Fc (crystalCosimplicialPair hp Fc).nabla
        (crystalCosimplicialPair hp Fc).nabla_tensorMap
        (crystalCosimplicialPair hp Fc).isSquareZero := rfl

/-- The degree zero connection of the cosimplicial pair of a crystal is the connection of the
pair: the base change along the identity
(`Crystalline.CosimplicialCompletedModule.baseChangeConnection_zero`). -/
theorem crystalCosimplicialPair_nabla_zero :
    (crystalCosimplicialPair hp Fc).nabla 0 = crystalPairFormsConnection hp Fc :=
  CompletedConnection.ext fun y ↦
    (wholeSpaceCosimplicialModule hp Fc).baseChangeConnection_zero
      (crystalPairFormsConnection hp Fc) (crystalCoprojectionBeta hp Fc)
      (crystalCoprojectionBeta_of_tmul hp Fc) y

/-- Completed de Rham complexes of equal connections are equal. -/
theorem _root_.Crystalline.CompletedDeRham.complex_congr_nabla {p : ℕ} {D : Type*} [CommRing D]
    {Om : ℕ → Type*} [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
    {wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1)} {deRham : ∀ i, Om i →+ Om (i + 1)}
    {dmap : D → Om 1} {M : Type*} [AddCommGroup M] [Module D M]
    {nabla nabla' : CompletedConnection p D (Om 1) dmap M}
    {hleib : CompletedDeRham.IsGradedLeibniz D Om wedge deRham dmap}
    (hsq : CompletedDeRham.IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsq' : CompletedDeRham.IsSquareZero p D Om wedge deRham M nabla' hleib) (h : nabla = nabla') :
    CompletedDeRham.complex p D Om wedge deRham M nabla hleib hsq =
      CompletedDeRham.complex p D Om wedge deRham M nabla' hleib hsq' := by
  subst h
  rfl

/-- **The row of degree zero of the cosimplicial pair of a crystal is `M ⊗^∧_D Ω^*_D`.** -/
theorem crystalCosimplicialPair_degreeDeRhamComplex_zero :
    (crystalCosimplicialPair hp Fc).degreeDeRhamComplex 0 = crystalPairDeRhamComplex hp Fc :=
  CompletedDeRham.complex_congr_nabla _ _ (crystalCosimplicialPair_nabla_zero hp Fc)

/-- **The comparison of [Stacks, Proposition 60.21.3, Tag 07LG] from the rows**: if every
coprojection `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} → M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` of the cosimplicial pair of
the crystal is a quasi-isomorphism, then `H^j(M ⊗^∧_D Ω^*_D) ≅ H^j(Cris(X/S), ℱ)` for every `j`:
the two degenerations of the double complex, the identification of its column zero with
`M(0) → M(1) → ⋯`, and [Stacks, Proposition 60.20.1, Tag 07JN]
(`...SmallSite.wholeSpaceRowZeroCohomologyIsoOfQuasiIso`). -/
def crystalPairDeRhamCohomologyIsoOfQuasiIso
    (hq : ∀ b, QuasiIso ((crystalCosimplicialPair hp Fc).rowFromZeroHom b)) (j : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj ((crystalPairDeRhamComplex hp Fc).homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj) :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.mapIso
      (HomologicalComplex.homologyMapIso
        (eqToIso (crystalCosimplicialPair_degreeDeRhamComplex_zero hp Fc)).symm j) ≪≫
    wholeSpaceRowZeroCohomologyIsoOfQuasiIso hp Fc (crystalCosimplicialPair hp Fc).nabla
      (crystalCosimplicialPair hp Fc).nabla_tensorMap (crystalCosimplicialPair hp Fc).isSquareZero
      hq j

end Crystalline.GlobalCrystallineSituation.SmallSite

end
