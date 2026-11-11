module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamLevelComparison07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamLevelHypotheses
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelZeroDeRhamComparison07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenAugmentationQuasiIso

/-!
# The Čech rows of the de Rham complex of a crystal, and the restriction to `T(0)`

Let `(p, (S, I, γ), X)` be a global crystalline situation with `X` and `S` affine and `p`
nilpotent on `S` (hence on `X`), `T(n)_e` the system `...SmallSite.wholeSpaceSystem` of
[Stacks, Proposition 60.20.1, Tag 07JN] (for its default presentation) and `F` a crystal in
quasi-coherent `𝒪_{X/S}`-modules, with de Rham complex `K^• = F ⊗ Ω^•_{X/S}`
(`(...SmallSite.crystalDeRhamSheafData hF).natComplex`) and cosimplicial pair `(M(•), ∇_•)`
(`...SmallSite.crystalCosimplicialPair`).

This module proves, unconditionally:

* `wholeSpaceCechRowDeRhamIso` — **the row `b` of the Čech complex of `K^•`,
  `lim_e (F ⊗ Ω^•_{X/S})(T(b)_e)`, is `M(b) ⊗^∧_{D(b)} Ω^•_{D(b)}`** (after the universe lift),
  and these identifications carry the Čech coprojections to the coprojections of the pair
  (`cosimplicialRowCoprojection_comp_wholeSpaceCechRowDeRhamIso`);
* `wholeSpaceCechRowZeroDeRhamIso` — the case `b = 0`:
  `lim_e (F ⊗ Ω^•_{X/S})(T(0)_e) ≅ M ⊗^∧_D Ω^•_D` (`...SmallSite.crystalPairDeRhamComplex`);
* `quasiIso_cosimplicialRowCoprojection_crystalDeRhamSheafData` — **every coprojection
  `lim_e K^•(T(0)_e) ⟶ lim_e K^•(T(b)_e)` is a quasi-isomorphism**, transported from
  `...SmallSite.quasiIso_crystalCosimplicialPair_rowFromZeroHom` ([Stacks, Tag 07LD]);
* `quasiIso_openAugmentationNat_crystalDeRhamSheafData` — for a quasi-isomorphism
  `φ : K^• ⟶ J^•` onto a complex of injective abelian sheaves, **the restriction
  `Γ(X, u_{X/S, *}J^•) ⟶ lim_e J^•(T(0)_e)` is a quasi-isomorphism**, and so is
  `lim_e K^•(T(0)_e) ⟶ lim_e J^•(T(0)_e)`: the hypothesis of
  `...SmallSite.quasiIso_openAugmentationNat_of_quasiIso` is discharged.

The proof reads every limit at the stable level `e = ...SmallSite.wholeSpaceStableLevel hA`
past which the tower `T(b)_•` is constant (this is where `p` nilpotent on `S` is used), and there
compares the explicit sections complex with `M(b) ⊗^∧ Ω^•` by
`...SmallSite.stableLevelReduce`; the connection is matched in degree zero by
`...SmallSite.reduceTensor_crystalPairConnModule_nabla` and in degree `b` by base change.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hA : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

/-- **The degree-zero compatibility of the connections at the stable level**, from
`...SmallSite.reduceTensor_crystalPairConnModule_nabla`. -/
theorem stableLevelBridge : StableLevelBridge hA hp hF := fun m ↦
  reduceTensor_crystalPairConnModule_nabla hp hA (quasiCoherentCrystalOf hF)
    (e := wholeSpaceStableLevel hA) m

/-- **The row `b` of the Čech complex of the de Rham complex of a crystal is the completed de Rham
complex of the degree `b` of its cosimplicial pair**:
`lim_e (F ⊗ Ω^•_{X/S})(T(b)_e) ≅ M(b) ⊗^∧_{D(b)} Ω^•_{D(b)}`, lifted to the universe of the
sheaves. -/
def wholeSpaceCechRowDeRhamIso (b : ℕ) :
    cosimplicialRowComplex ((cechCosimplicialComplex (wholeSpaceSystem S hp)).obj
        (crystalDeRhamSheafData hF).natComplex) b ≅
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).obj
        ((crystalCosimplicialPair hp (quasiCoherentCrystalOf hF)).degreeDeRhamComplex b) :=
  crystalDeRhamCechRowIso (stableLevelBridge hA hp hF) b

/-- **The identifications of the Čech rows carry the coprojections to the coprojections of the
cosimplicial pair.** -/
theorem cosimplicialRowCoprojection_comp_wholeSpaceCechRowDeRhamIso (b : ℕ) :
    cosimplicialRowCoprojection _ b ≫ (wholeSpaceCechRowDeRhamIso hA hp hF b).hom =
      (wholeSpaceCechRowDeRhamIso hA hp hF 0).hom ≫
        (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).map
          ((crystalCosimplicialPair hp (quasiCoherentCrystalOf hF)).rowFromZeroHom b) :=
  cosimplicialRowCoprojection_comp_crystalDeRhamCechRowIso (stableLevelBridge hA hp hF) b

/-- **The Čech row zero of the de Rham complex of a crystal is `M ⊗^∧_D Ω^•_D`**:
`lim_e (F ⊗ Ω^•_{X/S})(T(0)_e) ≅ M ⊗^∧_D Ω^•_D`, lifted to the universe of the sheaves. -/
def wholeSpaceCechRowZeroDeRhamIso :
    cosimplicialRowComplex ((cechCosimplicialComplex (wholeSpaceSystem S hp)).obj
        (crystalDeRhamSheafData hF).natComplex) 0 ≅
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).obj
        (crystalPairDeRhamComplex hp (quasiCoherentCrystalOf hF)) :=
  wholeSpaceCechRowDeRhamIso hA hp hF 0 ≪≫
    (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).mapIso
      (eqToIso (crystalCosimplicialPair_degreeDeRhamComplex_zero hp _))

include hA in
/-- **The coprojections of the Čech rows of the de Rham complex of a crystal are
quasi-isomorphisms**: `lim_e K^•(T(0)_e) ⟶ lim_e K^•(T(b)_e)` for every `b`, for the system of
[Stacks, Tag 07JN]. -/
theorem quasiIso_cosimplicialRowCoprojection_crystalDeRhamSheafData (b : ℕ) :
    QuasiIso (cosimplicialRowCoprojection ((cechCosimplicialComplex (wholeSpaceSystem S hp)).obj
      (crystalDeRhamSheafData hF).natComplex) b) :=
  quasiIso_cosimplicialRowCoprojection_of_rowIso _ _
    (crystalDeRhamCechRowIso (stableLevelBridge hA hp hF))
    (cosimplicialRowCoprojection_comp_crystalDeRhamCechRowIso (stableLevelBridge hA hp hF))
    (quasiIso_crystalCosimplicialPair_rowFromZeroHom hp _) b

include hA in
/-- **The restriction `Γ(X, u_{X/S, *}J^•) ⟶ lim_e J^•(T(0)_e)` is a quasi-isomorphism** for an
injective resolution `φ : F ⊗ Ω^•_{X/S} ⟶ J^•` of the de Rham complex of a crystal, and so is
the map `lim_e (F ⊗ Ω^•_{X/S})(T(0)_e) ⟶ lim_e J^•(T(0)_e)` induced by `φ`. -/
theorem quasiIso_openAugmentationNat_crystalDeRhamSheafData
    {J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ}
    (φ : (crystalDeRhamSheafData hF).natComplex ⟶ J) [QuasiIso φ] [∀ a, Injective (J.X a)] :
    QuasiIso (openAugmentationNat (isOpenProCovering_wholeSpaceSystem hp) J) ∧
      QuasiIso (cosimplicialRowMap ((cechCosimplicialComplex (wholeSpaceSystem S hp)).map φ) 0) :=
  quasiIso_openAugmentationNat_of_quasiIso (isOpenProCovering_wholeSpaceSystem hp)
    (hasAffineMonoLevels_wholeSpaceSystem hp) φ
    (vanishingOnLevels07Q9_crystalDeRhamSheafData hp hF)
    (hasSurjectiveLevelTransitions_crystalDeRhamSheafData hp hF)
    (quasiIso_cosimplicialRowCoprojection_crystalDeRhamSheafData hA hp hF)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
