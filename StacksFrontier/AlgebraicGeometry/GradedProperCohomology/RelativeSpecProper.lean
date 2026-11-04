module

public import StacksFrontier.AlgebraicGeometry.AlgebraExtensionSection.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedPullbackComap
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.SpecAlgebraSheafSections
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.SpecReesRelativeSpec
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion
public import StacksFrontier.AlgebraicGeometry.RelativeSpecClosedImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange

/-!
# A relative spectrum proper over an affine scheme, and the engine of Tag 0897 applied to it

Let `g : Z ⟶ Y` be a **proper** morphism of schemes with `Y` affine, let `𝒜` be a quasi-coherent
sheaf of commutative `𝒪_Y`-algebras, let `q : S ⟶ Y` be an affine morphism with `𝒜 ≅ q_* 𝒪_S`,
and let `𝒞` be a quasi-coherent sheaf of commutative `𝒪_Z`-algebras receiving a **locally
surjective** morphism `ψ : (algebraPullback g).obj 𝒜 ⟶ 𝒞`. Then the relative spectrum
`Spec_Z(𝒞)` carries a proper morphism to `S`.

The chain is the one the Rees case already ran, for `𝒜 = ⨁_{n ≥ 0} Ĩⁿ` and `S = Spec(reesAlgebra
I)`, in `StacksFrontier/AlgebraicGeometry/FormalFunctions/SpecReesRelativeSpec.lean`: an affine
morphism exhibits its source as the relative spectrum of its pushed-forward structure sheaf
([Stacks, Tag 01S8],
`AlgebraicGeometry.relativeSpecOverIsoOfAlgebraIso`), so `S ×_Y Z` is `Spec_Z(g^* 𝒜)` by
[Stacks, Tag 01LX] part (2) (`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`); a
locally surjective morphism of quasi-coherent algebra sheaves has a closed immersion of relative
spectra (`Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom`); the
first projection of `S ×_Y Z` is proper, being a base change of `g`; and a closed immersion
followed by a proper morphism is proper
(`Stacks.Cohomology.FormalFunctions.isProper_comp_pullbackFst_of_isClosedImmersion`).

**Nothing in that chain is about the Rees algebra**, and this file is it with no graded algebra
mentioned at all.

## Main definitions

* `Stacks.RelativeSpecProper.baseChangeRelativeSpecIso`: **`S ×_Y Z ≅ Spec_Z(g^* 𝒜)`.**
* `Stacks.RelativeSpecProper.relativeSpecToPullback`: the morphism `Spec_Z(𝒞) ⟶ S ×_Y Z` attached
  to `ψ`.

## Main results

* `Stacks.RelativeSpecProper.isClosedImmersion_relativeSpecToPullback`: it is a closed immersion.
* `Stacks.RelativeSpecProper.isProper_relativeSpecToPullback_comp_pullbackFst`: **`Spec_Z(𝒞) ⟶ S`
  is proper.**
* `Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedPullbackSpec`:
  **part (2) of [Stacks, Tag 0897] with the base change *and* the properness of `f'`
  discharged** — the uniform vanishing
  `Hᵖ(Z, Mₙ ⊗ ℒ ^⊗ d) = 0` for one `d₀` and all `p > 0`, `d ≥ d₀`, `n`, for a graded module over
  the degreewise pullback `g^* 𝓐` of a graded algebra sheaf on the affine base, with no
  hypothesis left about a morphism to a spectrum.
* `Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedAlgebraSections`:
  the same over `Spec k`, with the affine morphism and the identification of `𝒜` with a
  pushed-forward structure sheaf replaced by their arithmetic content — a Noetherian
  `k`-algebra `R` and a ring isomorphism of `R` with the global sections of `⨁ₙ 𝓐ₙ` compatible
  with the structure maps. This is the form the fibre of [Stacks, Tag 0D2N] uses, with
  `k = κ(y)` and `R = Gr_𝔪(A)`.

## What this leaves, for [Stacks, Tag 0D2M]

The capstones' remaining hypotheses are the graded module's own (finite type, quasi-coherent
pieces, vanishing in negative degrees, quasi-coherent coproduct), local Noetherianness of the
relative spectrum — reducible to that of `Z` and finite type of `𝓐`'s ungraded realization by
`Stacks.GradedProperCohomology.isLocallyNoetherian_relativeSpecOver` — and ampleness of `π^* ℒ`
upstairs, which [Stacks, Tag 0892] part (2)
(`Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`) supplies from ampleness of `ℒ` on
`Z` because `π` is affine. At the fibre of [Stacks, Tag 0D2N] that `Z` is `X_y`, where ampleness
of `ℒ_y` is the hypothesis of the tag, and `𝓐` is the associated graded `⨁ₙ 𝔪ⁿ/𝔪ⁿ⁺¹` of the
maximal ideal of the local base, a finitely generated graded `κ(y)`-algebra.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01W4](https://stacks.math.columbia.edu/tag/01W4)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.FiniteTypeDominating
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.RelativeSpecProper

variable {Z Y S : Scheme.{u}} (g : Z ⟶ Y) (q : S ⟶ Y) [IsAffineHom q]
  (𝒜 : AlgebraSheaf Y) [AlgebraSheaf.IsQuasicoherent 𝒜]
  (e : pushforwardAlgebra q ≅ 𝒜)
  (𝒞 : AlgebraSheaf Z) [AlgebraSheaf.IsQuasicoherent 𝒞]

/-- **`S ×_Y Z ≅ Spec_Z(g^* 𝒜)`**, the relative spectrum over `Z` of the algebra pullback. `S` is
the relative spectrum of `𝒜` over `Y`, `q` being affine with `q_* 𝒪_S ≅ 𝒜` ([Stacks, Tag 01S8]),
and then this is [Stacks, Tag 01LX] part (2). -/
def baseChangeRelativeSpecIso :
    (Over.pullback g).obj (Over.mk q) ≅
      Over.mk (relativeSpecToBase ((algebraPullback g).obj 𝒜)) :=
  ((Over.pullback g).mapIso (relativeSpecOverIsoOfAlgebraIso q 𝒜 e)).trans
    (relativeSpecBaseChangeIso g 𝒜)

/-- The morphism `Spec_Z(𝒞) ⟶ S ×_Y Z` attached to a morphism of algebra sheaves
`ψ : g^* 𝒜 ⟶ 𝒞`: the relative spectrum of `ψ`, followed by the identification of
`Spec_Z(g^* 𝒜)` with the base change. -/
def relativeSpecToPullback (ψ : (algebraPullback g).obj 𝒜 ⟶ 𝒞) :
    (relativeSpecOver 𝒞).left ⟶ pullback q g :=
  (relativeSpecMapOfAlgebraHom ((algebraPullback g).obj 𝒜) 𝒞 ψ).left ≫
    (baseChangeRelativeSpecIso g q 𝒜 e).inv.left

/-- **A locally surjective `ψ : g^* 𝒜 ⟶ 𝒞` exhibits `Spec_Z(𝒞)` as a closed subscheme of the base
change `S ×_Y Z`.** The relative spectrum of a locally surjective morphism of quasi-coherent
algebra sheaves is a closed immersion
(`Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom`), and the
remaining factor is an isomorphism. -/
theorem isClosedImmersion_relativeSpecToPullback (ψ : (algebraPullback g).obj 𝒜 ⟶ 𝒞)
    (hψ : CategoryTheory.Sheaf.IsLocallySurjective ψ.right) :
    AlgebraicGeometry.IsClosedImmersion (relativeSpecToPullback g q 𝒜 e 𝒞 ψ) :=
  have hci := Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom
    ((algebraPullback g).obj 𝒜) 𝒞 ψ hψ
  have _hiso : IsIso (baseChangeRelativeSpecIso g q 𝒜 e).inv.left :=
    show IsIso ((Over.forget Z).map (baseChangeRelativeSpecIso g q 𝒜 e).inv) from inferInstance
  @AlgebraicGeometry.IsClosedImmersion.comp _ _ _ _ _ hci inferInstance

/-- **`Spec_Z(𝒞) ⟶ S` is proper**, for a proper `g : Z ⟶ Y` and a locally surjective
`ψ : g^* 𝒜 ⟶ 𝒞`. The first projection of `S ×_Y Z` is proper as a base change of `g`
([Stacks, Tag 01W4]) and a closed immersion followed by a proper morphism is proper. -/
theorem isProper_relativeSpecToPullback_comp_pullbackFst (hg : AlgebraicGeometry.IsProper g)
    (ψ : (algebraPullback g).obj 𝒜 ⟶ 𝒞)
    (hψ : CategoryTheory.Sheaf.IsLocallySurjective ψ.right) :
    AlgebraicGeometry.IsProper
      (relativeSpecToPullback g q 𝒜 e 𝒞 ψ ≫ pullback.fst q g) :=
  Stacks.Cohomology.FormalFunctions.isProper_comp_pullbackFst_of_isClosedImmersion q hg _
    (isClosedImmersion_relativeSpecToPullback g q 𝒜 e 𝒞 ψ hψ)

end Stacks.RelativeSpecProper

namespace Stacks.GradedProperCohomology

open Stacks.Conormal (gradedPullback gradedPullback_mul_comm)

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  (𝓐 : _root_.SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (a : (𝓐.piece i).val.obj W)
    (b : (𝓐.piece j).val.obj W), HEq ((𝓐.mul i j).app W a b) ((𝓐.mul j i).app W b a))

/-- The ungraded realization of the degreewise pullback `g^* 𝓐`, as a sheaf of commutative
`𝒪_Z`-algebras: the `𝓑` that the fibre-side instance of [Stacks, Tag 0897] is run with. A
`reducible` abbreviation, so that it unifies on sight with the `gradedAlgebraSheaf` appearing in
the hypotheses of `Stacks.GradedProperCohomology.isLocallyNoetherian_relativeSpecOver` and of the
uniform vanishing. -/
abbrev pullbackGradedAlgebraSheaf : AlgebraSheaf Z :=
  gradedAlgebraSheaf Z (gradedPullback g 𝓐) (gradedPullback_mul_comm g 𝓐 hA)

/-- **The morphism `f' : Spec_Z(⨁ₙ g^*𝓐ₙ) ⟶ S` of [Stacks, Tag 0897]'s base change**, for a
graded algebra sheaf `𝓐` on the affine `Y` whose ungraded realization is the pushed-forward
structure sheaf of an affine `q : S ⟶ Y`. It is the closed immersion into `S ×_Y Z` coming from
the comparison of the two pullbacks of `𝓐`, followed by the first projection. -/
def gradedPullbackToSpec {S : Scheme.{u}} (q : S ⟶ Y) [IsAffineHom q]
    [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf Y 𝓐 hA)]
    (e : pushforwardAlgebra q ≅ gradedAlgebraSheaf Y 𝓐 hA) [IsAffine Y]
    [AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g 𝓐 hA)] :
    (relativeSpecOver (pullbackGradedAlgebraSheaf g 𝓐 hA)).left ⟶ S :=
  Stacks.RelativeSpecProper.relativeSpecToPullback g q (gradedAlgebraSheaf Y 𝓐 hA) e
      (pullbackGradedAlgebraSheaf g 𝓐 hA)
      (Stacks.GradedComap.pullbackHom g 𝓐 (gradedPullback g 𝓐)
        (Stacks.GradedComap.unitPieceComparison g 𝓐) hA (gradedPullback_mul_comm g 𝓐 hA)) ≫
    pullback.fst q g

/-- **`f'` is proper**, for a proper `g`: the comparison of the two pullbacks of `𝓐` is locally
surjective (`Stacks.GradedComap.isLocallySurjective_unitPullbackHom`), so `f'` is a closed
immersion followed by a base change of `g`. -/
theorem isProper_gradedPullbackToSpec {S : Scheme.{u}} (q : S ⟶ Y) [IsAffineHom q]
    [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf Y 𝓐 hA)]
    (e : pushforwardAlgebra q ≅ gradedAlgebraSheaf Y 𝓐 hA) [IsAffine Y]
    [AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g 𝓐 hA)]
    (hg : AlgebraicGeometry.IsProper g) (hqc : ∀ n : ℤ, (𝓐.piece n).IsQuasicoherent) :
    AlgebraicGeometry.IsProper (gradedPullbackToSpec g 𝓐 hA q e) :=
  Stacks.RelativeSpecProper.isProper_relativeSpecToPullback_comp_pullbackFst g q
    (gradedAlgebraSheaf Y 𝓐 hA) e (pullbackGradedAlgebraSheaf g 𝓐 hA) hg _
    (Stacks.GradedComap.isLocallySurjective_unitPullbackHom g 𝓐 hA hqc)

/-- **[Stacks, Tag 0897] part (2) with the base change *and* the properness of `f'` discharged.**

Let `g : Z ⟶ Y` be proper with `Y` affine, let `𝓐` be a sheaf of graded `𝒪_Y`-algebras with
commutative homogeneous multiplication, quasi-coherent pieces and quasi-coherent ungraded
realization, and suppose that realization is the pushed-forward structure sheaf of
`Spec R ⟶ Y` for a Noetherian ring `R` — which over an affine `Y` is no condition but a naming of
`R`. Let `M` be a graded module of finite type over the degreewise pullback `g^* 𝓐`, with
quasi-coherent pieces vanishing in negative degrees, and write
`π : X' = Spec_Z(⨁ₙ g^*𝓐ₙ) ⟶ Z`. If `X'` is locally Noetherian and `π^* ℒ` is ample on it for an
invertible `𝒪_Z`-module `ℒ`, then one integer `d₀` makes

`Hᵖ(Z, Mₙ ⊗ ℒ ^⊗ d) = 0` for every `p > 0`, every `d ≥ d₀` and every `n`.

Compared with `Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedModule`
the proper morphism `f' : X' ⟶ Spec R` is no longer a hypothesis: it is
`Stacks.GradedProperCohomology.gradedPullbackToSpec`, proper by
`isProper_gradedPullbackToSpec`. -/
theorem exists_isZero_Hgroup_tensorPowTwist_of_gradedPullbackSpec [IsAffine Y]
    [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf Y 𝓐 hA)]
    (hqc : ∀ n : ℤ, (𝓐.piece n).IsQuasicoherent) (hg : AlgebraicGeometry.IsProper g)
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (q : Spec (CommRingCat.of R) ⟶ Y) [IsAffineHom q]
    (e : pushforwardAlgebra q ≅ gradedAlgebraSheaf Y 𝓐 hA)
    [(gradedPullback g 𝓐).IsCommutative]
    [AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g 𝓐 hA)]
    [IsLocallyNoetherian (relativeSpecOver (pullbackGradedAlgebraSheaf g 𝓐 hA)).left]
    (M : _root_.SheafOfModules.GradedModule.{u, u, u} (gradedPullback g 𝓐))
    (hB : ((_root_.SheafOfModules.restrictScalars
      (gradedPullback g 𝓐).ungradedStructureMap).obj
        (_root_.SheafOfModules.unit (gradedPullback g 𝓐).ungradedSheaf)).IsQuasicoherent)
    (hcop : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) (hft : M.IsFiniteType)
    (L : Z.Modules) [IsInvertibleModule Z L]
    (hL : IsAmple (relativeSpecOver (pullbackGradedAlgebraSheaf g 𝓐 hA)).left
      (pullbackModule (relativeSpecOver (pullbackGradedAlgebraSheaf g 𝓐 hA)).hom L)) :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p → ∀ n : ℕ,
      IsZero (Hgroup Z.ringCatSheaf ⊤ p
        (tensorModules Z (M.piece (n : ℤ)) (tensorPowModule Z L (d : ℤ)))) :=
  have := isProper_gradedPullbackToSpec g 𝓐 hA q e hg hqc
  exists_isZero_Hgroup_tensorPowTwist_of_gradedModule (gradedPullback g 𝓐)
    (gradedPullback_mul_comm g 𝓐 hA) M hB hcop hneg hft
    (gradedPullbackToSpec g 𝓐 hA q e) L hL

/-- **[Stacks, Tag 0897] part (2) with every geometric hypothesis of the base change
discharged, over `Spec` of a ring.**

Same as `Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedPullbackSpec`
with the affine morphism `q` and the identification `e` replaced by their arithmetic content: a
Noetherian `k`-algebra `R` and a ring isomorphism `ρ` of `R` with the global sections of the
ungraded realization of `𝓐`, compatible with the structure maps. The morphism is
`Spec(R) ⟶ Spec(k)` and the identification is
`Stacks.RelativeSpec.AlgebraSheaf.specAlgebraSheafIsoOfSectionsRingEquiv`.

At the fibre `X_y` of [Stacks, Tag 0D2N] this is the form to use: `k = κ(y)`,
`R = Gr_𝔪(A) = ⨁ₙ 𝔪ⁿ/𝔪ⁿ⁺¹`, `𝓐` the associated graded of `𝔪` as a graded algebra sheaf on
`Spec κ(y)`, and `ρ` the identification of `Gr_𝔪(A)` with its global sections. -/
theorem exists_isZero_Hgroup_tensorPowTwist_of_gradedAlgebraSections {Z : Scheme.{u}}
    {k : Type u} [CommRing k] (g' : Z ⟶ Spec (CommRingCat.of k))
    (𝓐' : _root_.SheafOfModules.GradedAlgebra.{u, u} (Spec (CommRingCat.of k)).ringCatSheaf)
    (hA' : ∀ (i j : ℤ) (W : (Opens ↥(Spec (CommRingCat.of k)))ᵒᵖ)
      (a : (𝓐'.piece i).val.obj W) (b : (𝓐'.piece j).val.obj W),
      HEq ((𝓐'.mul i j).app W a b) ((𝓐'.mul j i).app W b a))
    [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf (Spec (CommRingCat.of k)) 𝓐' hA')]
    (hqc : ∀ n : ℤ, (𝓐'.piece n).IsQuasicoherent) (hg : AlgebraicGeometry.IsProper g')
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Algebra k R]
    (ρ : R ≃+* ↥((gradedAlgebraSheaf (Spec (CommRingCat.of k)) 𝓐' hA').sections ⊤))
    (hρ : ∀ r : k, ρ (algebraMap k R r) =
      (gradedAlgebraSheaf (Spec (CommRingCat.of k)) 𝓐' hA').unitTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv r))
    [(gradedPullback g' 𝓐').IsCommutative]
    [AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g' 𝓐' hA')]
    [IsLocallyNoetherian (relativeSpecOver (pullbackGradedAlgebraSheaf g' 𝓐' hA')).left]
    (M : _root_.SheafOfModules.GradedModule.{u, u, u} (gradedPullback g' 𝓐'))
    (hB : ((_root_.SheafOfModules.restrictScalars
      (gradedPullback g' 𝓐').ungradedStructureMap).obj
        (_root_.SheafOfModules.unit (gradedPullback g' 𝓐').ungradedSheaf)).IsQuasicoherent)
    (hcop : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) (hft : M.IsFiniteType)
    (L : Z.Modules) [IsInvertibleModule Z L]
    (hL : IsAmple (relativeSpecOver (pullbackGradedAlgebraSheaf g' 𝓐' hA')).left
      (pullbackModule (relativeSpecOver (pullbackGradedAlgebraSheaf g' 𝓐' hA')).hom L)) :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p → ∀ n : ℕ,
      IsZero (Hgroup Z.ringCatSheaf ⊤ p
        (tensorModules Z (M.piece (n : ℤ)) (tensorPowModule Z L (d : ℤ)))) :=
  exists_isZero_Hgroup_tensorPowTwist_of_gradedPullbackSpec g' 𝓐' hA' hqc hg
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (AlgebraSheaf.specAlgebraSheafIsoOfSectionsRingEquiv
      (gradedAlgebraSheaf (Spec (CommRingCat.of k)) 𝓐' hA') R ρ hρ).symm
    M hB hcop hneg hft L hL

end Stacks.GradedProperCohomology

end
