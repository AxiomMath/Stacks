module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.ClopenLift.Reduction
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Reduction
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic

/-!
# The cohomological hypothesis of Stacks Tag 0B5P, consumed at the ideal sheaf of a morphism

The hypothesis of [Stacks, Tag 0B5P] quantifies over quasi-coherent ideal sheaves of `𝒪_X`, read
as quasi-coherent subobjects of `𝒪_X` in `X.Modules`
(`Stacks.AmpleCohomologicalCriterion.HasEventuallyVanishingH1`). This file spends it at the ideal
sheaf of a quasi-compact morphism `i : Y ⟶ X`, which is the only instance the proof of the tag
uses, and records what remains.

Given the hypothesis and `i`, some positive tensor power `L^{⊗ n}` makes

  `Γ(X, 𝒪_X ⊗ L^{⊗ n}) ⟶ Γ(X, i_* 𝒪_Y ⊗ L^{⊗ n})`

an epimorphism, where `I_i = ker(𝒪_X ⟶ i_* 𝒪_Y)`. Every step is in the library:
`Stacks.AmpleCohomologicalCriterion.kerSubobject` is the ideal sheaf as a subobject and
`Stacks.AmpleCohomologicalCriterion.isQuasicoherent_kerSubobject` is its quasi-coherence, so the
hypothesis applies;
`Stacks.AmpleCohomologicalCriterion.shortExact_map_subobjectShortComplex` tensors the sequence
`0 → I_i → 𝒪_X → 𝒪_X/I_i → 0` by the invertible module `L^{⊗ n}` and stays short exact; and
`Stacks.AmpleCohomologicalCriterion.epi_evaluation_map_g` turns the vanishing `H¹` into
surjectivity on global sections.

Combined with `Stacks.Tag0B5PClopenLift.isAmple_of_forall_surjective`, Tag 0B5P is reduced to a
single implication, isolated here as
`Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence`.

## Main definitions

* `Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence X`: **the residue of the tag left by
  this file.** For a morphism `i : Y ⟶ X` and an invertible `𝒪_X`-module `P`, surjectivity of
  `Γ(X, 𝒪_X ⊗ P) ⟶ Γ(X, i_* 𝒪_Y ⊗ P)` implies surjectivity of the restriction
  `Γ(X, P) ⟶ Γ(Y, i^* P)`.

## Main results

* `Stacks.Tag0B5PClopenLift.exists_epi_evaluation_map_pushforwardUnit`: **the hypothesis of
  [Stacks, Tag 0B5P], consumed at the ideal sheaf of a quasi-compact morphism.**
* `Stacks.Tag0B5PClopenLift.isAmple_of_hasEventuallyVanishingH1`: **[Stacks, Tag 0B5P] modulo
  `ProjectionFormulaConsequence`.**

## Why `ProjectionFormulaConsequence` is not proved here, and what it is

It is the projection formula, [Stacks, Tag 0FZE] (equivalently [Stacks, Tag 01E8]), in the only
form the tag needs: the isomorphism `i_* 𝒪_Y ⊗ P ≅ i_*(i^* P)` for the affine morphism `i` and
the invertible module `P`, together with the identification of `𝒪_X ⊗ P ⟶ (𝒪_X/I_i) ⊗ P` with
the unit `P ⟶ i_*(i^* P)` under it and the unitor `𝒪_X ⊗ P ≅ P`. Granting the formula, the
implication is the two-square diagram chase that the source performs in one line.

The residue is discharged downstream rather than here.
`Stacks.ProjectionFormula.projectionFormulaConsequence`, in
`StacksFrontier/AlgebraicGeometry/ProjectionFormulaInvertible/AmpleCriterion.lean`, proves
`ProjectionFormulaConsequence X` for every scheme `X` with no hypothesis, from the projection
formula morphism being invertible whenever its second argument is invertible, and
`Stacks.ProjectionFormula.isAmple_of_hasEventuallyVanishingH1` is then [Stacks, Tag 0B5P] with
exactly the tag's hypotheses. That file is not imported here: it imports this one.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.AlgebraicGeometry.ClosedImmersionTFAE
  (epi_unitToPushforwardObjUnit_of_isClosedImmersion)

open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.Tag0B5PClopenLift

variable {X : Scheme.{u}}

/-- The closed immersion `avoidι U hx` is quasi-compact. -/
instance quasiCompact_avoidι (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X)) :
    QuasiCompact (avoidι U hx) :=
  inferInstanceAs (QuasiCompact
    (Scheme.IdealSheafData.vanishingIdeal (avoidClosed U hx)).subschemeι)

/-! ### The short exact sequence of the ideal sheaf -/

/-- **The short exact sequence of the ideal sheaf of a closed immersion**,
`0 → I_i → 𝒪_X → i_* 𝒪_Y → 0`, with `I_i` presented as the kernel of `𝒪_X ⟶ i_* 𝒪_Y`. -/
noncomputable abbrev idealShortComplex {Y : Scheme.{u}} (i : Y ⟶ X) :
    ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
  ShortComplex.mk (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))
    (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) (kernel.condition _)

/-- `Stacks.Tag0B5PClopenLift.idealShortComplex` is short exact: the left map is the kernel
inclusion, and the right map is an epimorphism because `i` is a closed immersion
(`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion`).
-/
theorem shortExact_idealShortComplex {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] :
    (idealShortComplex i).ShortExact :=
  { exact := ShortComplex.exact_kernel _
    epi_g := epi_unitToPushforwardObjUnit_of_isClosedImmersion i }

/-! ### The hypothesis of Stacks Tag 0B5P, consumed -/

/-- **The hypothesis of [Stacks, Tag 0B5P], consumed at the ideal sheaf of a closed immersion.**
If every quasi-coherent ideal sheaf of `𝒪_X` has vanishing `H¹` after some positive twist, then
for every closed immersion `i : Y ⟶ X` some positive tensor power `L^{⊗ n}` makes

  `Γ(X, 𝒪_X ⊗ L^{⊗ n}) ⟶ Γ(X, i_* 𝒪_Y ⊗ L^{⊗ n})`

an epimorphism.

The ideal sheaf is quasi-coherent by [Stacks, Tag 01R8], so the hypothesis applies to it; the
sequence stays short exact after tensoring by the invertible module `L^{⊗ n}`; and the vanishing
`H¹` becomes surjectivity on global sections. -/
theorem exists_epi_evaluation_map_pushforwardUnit (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (h : Stacks.AmpleCohomologicalCriterion.HasEventuallyVanishingH1 X L)
    {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] :
    ∃ n : ℕ, 1 ≤ n ∧
      Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
            (Stacks.Ample.tensorPowModule X L (n : ℤ))).map
          (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))) := by
  obtain ⟨n, hn, hzero⟩ :=
    h (Stacks.AmpleCohomologicalCriterion.kerSubobject i)
      (Stacks.AmpleCohomologicalCriterion.isQuasicoherent_kerSubobject i)
  let twist : X.Modules ⥤ X.Modules :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
      (Stacks.Ample.tensorPowModule X L (n : ℤ))
  have exactSequence :=
    Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight X
      (Stacks.Ample.tensorPowModule X L (n : ℤ)) (shortExact_idealShortComplex i)
  have vanishing : IsZero
      (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 1).obj
        (twist.obj (idealShortComplex i).X₁)) :=
    IsZero.of_iso hzero
      (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 1).mapIso
        (twist.mapIso (Stacks.AmpleCohomologicalCriterion.underlyingKerSubobjectIso i).symm))
  have surjective : Epi
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        (twist.map (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))) :=
    Stacks.AmpleCohomologicalCriterion.epi_evaluation_map_g X ⊤ exactSequence vanishing
  exact ⟨n, hn, surjective⟩

/-! ### The remaining obligation -/

/-- **The projection formula, in the only form [Stacks, Tag 0B5P] consumes it.** For a morphism
`i : Y ⟶ X` and an invertible `𝒪_X`-module `P`, surjectivity of

  `Γ(X, 𝒪_X ⊗ P) ⟶ Γ(X, i_* 𝒪_Y ⊗ P)`

implies surjectivity of the restriction of global sections `Γ(X, P) ⟶ Γ(Y, i^* P)`, that is, of
the evaluation at `⊤` of the unit of `i^* ⊣ i_*`.

Granting [Stacks, Tag 0FZE] -- the isomorphism `i_* 𝒪_Y ⊗ P ≅ i_*(i^* P)` for an affine morphism
`i`, with its naturality against the unit -- this is a two-square diagram chase: the formula
identifies the target, the unitor `𝒪_X ⊗ P ≅ P` identifies the source, and the canonical map
`𝒪_X ⟶ i_* 𝒪_Y` is carried to the unit. The projection formula itself is not available in this
repository; see the module documentation.

**This is a hypothesis, not a result.** It is stated here only so that the single statement this
directory owes has a name and a type, and so that a future proof of Tag 0FZE closes Tag 0B5P by
discharging it. -/
abbrev ProjectionFormulaConsequence (X : Scheme.{u}) : Prop :=
  ∀ {Y : Scheme.{u}} (i : Y ⟶ X) (P : X.Modules) [Stacks.Ample.IsInvertibleModule X P],
    Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj P).map
          (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))) →
      Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app P))

/-- **[Stacks, Tag 0B5P] modulo the projection formula.** On a quasi-compact scheme, an
invertible `𝒪_X`-module whose positive twists eventually kill the first cohomology of every
quasi-coherent ideal sheaf is ample, provided
`Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence`.

Everything else in the proof of the tag is discharged: the reduction to closed points is
`Stacks.AmpleCohomologicalCriterion.isAmple_of_closed_points`, the cohomological hypothesis is
spent by `Stacks.Tag0B5PClopenLift.exists_epi_evaluation_map_pushforwardUnit`, the section on the
auxiliary closed subscheme is
`Stacks.Tag0B5PClopenLift.exists_nonvanishingLocus_eq_singleton`, its nonvanishing locus is
transported by [Stacks, Tag 0H78] and its affineness follows from [Stacks, Tag 01PV]. -/
theorem isAmple_of_hasEventuallyVanishingH1 (X : Scheme.{u}) [CompactSpace X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hpf : ProjectionFormulaConsequence X)
    (h : Stacks.AmpleCohomologicalCriterion.HasEventuallyVanishingH1 X L) :
    Stacks.Ample.IsAmple X L := by
  refine isAmple_of_forall_surjective X L fun x hx U hU hxU => ?_
  obtain ⟨n, hn, hg⟩ := exists_epi_evaluation_map_pushforwardUnit X L h (avoidι U hx)
  exact ⟨n, hn, surjective_pullbackGlobalSection_of_epi (avoidι U hx) _
    (hpf (avoidι U hx) (Stacks.Ample.tensorPowModule X L (n : ℤ)) hg)⟩

end Stacks.Tag0B5PClopenLift

end
