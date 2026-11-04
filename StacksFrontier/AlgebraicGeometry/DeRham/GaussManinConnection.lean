module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceConcrete
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaStepSquare
import StacksCore.Tactic.StacksAttribute

/-!
# The Gauss–Manin connection

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated, smooth morphism of schemes over `S`, with
`g : Y ⟶ S` the structure morphism of the target, and suppose that the de Rham cohomology
sheaves `ℋ^q_dR(X/Y) = H^q(Rf_*Ω^•_{X/Y})` are flat `𝒪_Y`-modules. The remark
[Stacks, Tag 0FMN] says that the spectral sequence of [Stacks, Tag 0FMM] then has first page

`E_1^{p, q} = Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`,

that `d_1^{0, q} : ℋ^q_dR(X/Y) ⟶ Ω^1_{Y/S} ⊗ ℋ^q_dR(X/Y)` is an integrable connection `∇`, the
**Gauss–Manin connection**, and that the complex `(Ω^•_{Y/S} ⊗ ℋ^q_dR(X/Y), d_1^{•, q})` is the de
Rham complex of `∇`.

## Main definitions

* `Stacks.DeRhamSmooth.gaussManinConnection`: the Gauss–Manin connection on `ℋ^q_dR(X/Y)`, the
  connection of the Katz–Oda family `d_1^{•, q}`.
* `Stacks.DeRhamSmooth.gaussManinTwistedDifferential`: its de Rham complex
  `ℋ^q_dR(X/Y) ⊗ Ω^•_{Y/S}`, with differentials `d_1^{•, q}`.

## Main results

* `Stacks.DeRhamSmooth.deRhamSmoothSpectralSequence_gaussManin`: **[Stacks, Tag 0FMN]**.

## Implementation notes

The spectral sequence is `Stacks.DeRhamSmooth.deRhamSmoothSpectralSequence`, the one of 0FMM; the
identification of its first page is `deRhamSmoothFirstPageFlatIso`, and its first differential,
read on `Ω^p_{Y/S} ⊗ ℋ^q_dR(X/Y)`, is `deRhamFirstPageFlatDifferential`. Its Katz–Oda Leibniz
rule `d_1(ω ⊗ s) = dω ⊗ s + (-1)^p ω ∧ d_1(1 ⊗ s)` is
`isKatzOdaLeibniz_deRhamFirstPageFlatDifferential`, proved, not assumed; the connection and its
de Rham complex are the ones `AlgebraicGeometry.Scheme.Hom.katzOdaConnection` and
`katzOdaTwistedDifferential` attach to a Katz–Oda family, and integrability is `d_1 ∘ d_1 = 0`.

The remark also says that `ℋ^q_dR(X/Y)` is finite locally free when `f` is in addition proper
and `S` lives over `ℚ`. The source defers that to a future reference ("insert future reference
here") and gives no argument, so that sentence is not part of the statement formalized here.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Hom Stacks.DeRhamDirectImage

universe u

attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackTensorCoherence.braidedCategory

namespace Stacks.DeRhamSmooth

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  [Smooth f]
  (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
    (deRhamCohomologySheaf f q))

/-- **The Gauss–Manin connection** on `ℋ^q_dR(X/Y)`, for flat de Rham cohomology sheaves: the
map `d_1^{0, q} : ℋ^q_dR(X/Y) ⟶ Ω^1_{Y/S} ⊗ ℋ^q_dR(X/Y)` of the spectral sequence of
[Stacks, Tag 0FMM], read on `ℋ^q_dR(X/Y) ⊗ Ω^1_{Y/S}`; it is a connection by the Katz–Oda rule
`isKatzOdaLeibniz_deRhamFirstPageFlatDifferential`. -/
def gaussManinConnection (q : ℤ) : ModuleConnection g (deRhamCohomologySheaf f q) :=
  katzOdaConnection (isKatzOdaLeibniz_deRhamFirstPageFlatDifferential f g hflat q)

/-- **The de Rham complex of the Gauss–Manin connection**, `ℋ^q_dR(X/Y) ⊗ Ω^•_{Y/S}`, whose
differential in degree `p` is `d_1^{p, q}` read on `ℋ^q_dR(X/Y) ⊗ Ω^p_{Y/S}`. -/
def gaussManinTwistedDifferential (q : ℤ) :
    TwistedDeRhamDifferential (gaussManinConnection f g hflat q) :=
  katzOdaTwistedDifferential (isKatzOdaLeibniz_deRhamFirstPageFlatDifferential f g hflat q)

/-- **Stacks Project, Tag 0FMN.** Let `f : X ⟶ Y` be a quasi-compact, quasi-separated, smooth
morphism of schemes over `S`, with `g : Y ⟶ S` the structure morphism of the target, and suppose
the de Rham cohomology sheaves `ℋ^q_dR(X/Y)` are flat `𝒪_Y`-modules. Then the spectral sequence
`E` of [Stacks, Tag 0FMM] (bounded, abutting to `R^{p + q}f_*Ω^•_{X/S}`) has
`E_1^{p, q} = Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)` (`deRhamSmoothFirstPageFlatIso`), and for every `q`:

1. its differentials are maps `d_1^{p, q} : Ω^p_{Y/S} ⊗ ℋ^q ⟶ Ω^{p + 1}_{Y/S} ⊗ ℋ^q`, namely
   `deRhamFirstPageFlatDifferential`, and they satisfy the Katz–Oda Leibniz rule
   `d_1(ω ⊗ s) = dω ⊗ s + (-1)^p ω ∧ d_1(1 ⊗ s)`;
2. `d_1^{0, q} : ℋ^q ⟶ Ω^1_{Y/S} ⊗ ℋ^q` is the integrable connection `∇` of
   `gaussManinConnection` (the **Gauss–Manin connection**), read through
   `Ω^1_{Y/S} ⊗ ℋ^q ≅ ℋ^q ⊗ Ω_{Y/S}`;
3. the complex `ℋ^q ⟶ Ω^1_{Y/S} ⊗ ℋ^q ⟶ Ω^2_{Y/S} ⊗ ℋ^q ⟶ ⋯` with differentials `d_1^{•, q}` is
   the de Rham complex of `∇` (`gaussManinTwistedDifferential`, a complex), its differential in
   degree `p` being `d_1^{p, q}` read through `Ω^p_{Y/S} ⊗ ℋ^q ≅ ℋ^q ⊗ Ω^p_{Y/S}`.

The sentence of the remark on finite local freeness for proper `f` over `ℚ` is deferred by the
source to a future reference and is not included. -/
@[stacks 0FMN "the first page Ω^p_{Y/S} ⊗ ℋ^q_dR(X/Y) for flat ℋ^q_dR, d_1^{0,q} the integrable \
Gauss–Manin connection and d_1^{•,q} its de Rham complex; the finite local freeness for proper f \
over ℚ is deferred by the source and omitted"]
theorem deRhamSmoothSpectralSequence_gaussManin (q : ℤ) :
    _root_.IsBounded (deRhamSmoothSpectralSequence f g) ∧
      SpectralSequence.AbutsTo (deRhamSmoothSpectralSequence f g)
        (fun n => deRhamHigherDirectImage f g n) ∧
      (∀ p : ℤ, Nonempty (((deRhamSmoothSpectralSequence f g).page 1).X (p, q) ≅
        deRhamFirstPageFlat f g p q)) ∧
      (∀ p : ℤ, ((deRhamSmoothSpectralSequence f g).page 1).d (p, q) (p + 1, q) =
        (deRhamSmoothFirstPageFlatIso f g hflat p q).hom ≫
          deRhamFirstPageFlatDifferential f g hflat p q ≫
            (deRhamSmoothFirstPageFlatIso f g hflat (p + 1) q).inv) ∧
      IsKatzOdaLeibniz g (deRhamCohomologySheaf f q)
        (fun p => deRhamFirstPageFlatDifferential f g hflat p q) ∧
      (∀ (U : (Y.Opens)ᵒᵖ) (s : (deRhamCohomologySheaf f q).val.obj U),
        (gaussManinConnection f g hflat q).d U s =
          (formsTensorConnectionIso g (deRhamCohomologySheaf f q)).hom.val.app U
            ((deRhamFirstPageFlatDifferential f g hflat 0 q).val.app U
              (formsTensorUnitTmul g (deRhamCohomologySheaf f q) U s))) ∧
      (gaussManinConnection f g hflat q).IsIntegrable (gaussManinTwistedDifferential f g hflat q) ∧
      (gaussManinTwistedDifferential f g hflat q).IsComplex ∧
      ∀ p : ℕ, (gaussManinTwistedDifferential f g hflat q).d p =
        (_root_.pushforward (toInverseImageBase g)).map
            (β_ (modulesOnRing (deRhamCohomologySheaf f q)) (formsOnRing g p)).hom ≫
          deRhamFirstPageFlatDifferential f g hflat p q ≫
          (_root_.pushforward (toInverseImageBase g)).map
            ((formsTensorSuccIso g (deRhamCohomologySheaf f q) p).hom ≫
              (β_ (formsOnRing g ((p + 1 : ℕ) : ℤ))
                (modulesOnRing (deRhamCohomologySheaf f q))).hom) :=
  ⟨deRhamSmoothSpectralSequence_isBounded f g, deRhamSmoothSpectralSequence_abutsTo f g,
    fun p => ⟨deRhamSmoothFirstPageFlatIso f g hflat p q⟩,
    fun p => deRhamSmoothSpectralSequence_d_flat f g hflat p q,
    isKatzOdaLeibniz_deRhamFirstPageFlatDifferential f g hflat q,
    katzOdaConnection_d _,
    isIntegrable_katzOdaConnection _
      (fun p => deRhamFirstPageFlatDifferential_comp f g hflat p q),
    katzOdaTwistedDifferential_isComplex _
      (fun p => deRhamFirstPageFlatDifferential_comp f g hflat p q),
    katzOdaTwistedDifferential_d _⟩

end Stacks.DeRhamSmooth

end
