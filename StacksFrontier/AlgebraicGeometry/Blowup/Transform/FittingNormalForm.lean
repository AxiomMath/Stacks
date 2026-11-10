module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.Blowup.PerfectPullback
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingKernel
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.TwoTermResolution
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback

/-!
# Normal form of a module of constant rank on a dense open after blowing up its Fitting ideal

Let `ℱ` be a perfect `𝒪_X`-module of Tor dimension at most one on a scheme `X` which is finite
locally free of constant rank `r` on a scheme-theoretically dense open `U ⊆ X`. Blowing up the
`r`-th Fitting ideal of `ℱ` produces a `U`-admissible blowup `b : X' ⟶ X` together with a
canonical short exact sequence

`0 ⟶ 𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 0`

in which `𝒬` is the strict transform of `ℱ`, finite locally free of rank `r`, and `𝒦` is finitely
presented, perfect, of Tor dimension at most one, and vanishes over `U`. This is Stacks tag 0EST.

The blowup is taken in the spelling of tag 0ESN, namely as the base change
`Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase I)` of the blowup along the identity of
`X`, with structure morphism the first projection; that is the scheme the strict transform of a
module lives on.

## Main results

* `AlgebraicGeometry.isAdmissibleBlowup_fittingBlowUpFst`: the structure morphism of the Fitting
  blowup, in the base-change spelling, is a `U`-admissible blowup.
* `AlgebraicGeometry.shortExact_strictTransformKernel`: the kernel inclusion and the canonical
  surjection onto the strict transform form a short exact sequence.
* `AlgebraicGeometry.isPerfect_strictTransformKernel` and
  `AlgebraicGeometry.hasTorAmplitude_strictTransformKernel`: the kernel is a perfect
  `𝒪_{X'}`-module of Tor dimension at most one, under the hypotheses tag 0EST makes on `ℱ`. This
  is the part of tag 0EST that is not already tag 0ESN (1)–(3).
* `AlgebraicGeometry.isPerfect_modulePullback_pullbackFst_blowUpToBase` and
  `AlgebraicGeometry.hasTorAmplitude_modulePullback_pullbackFst_blowUpToBase`: tag 0ESS for
  `b^*ℱ`, moved along the isomorphism of the base change with the blowup, for an arbitrary ideal
  sheaf and at the hypotheses tag 0ESS makes.
* `AlgebraicGeometry.isFinitePresentation_of_isPerfect_single`: a perfect module is of finite
  presentation, so tag 0ESN applies to `ℱ`.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_shortExact_strictTransform`: **tag 0EST**, the
  above packaged in its existential shape.

Part (4) of tag 0ESN assumes less than tag 0EST does: it asks only that `ℱ` be finitely
presented, and it is about the blowup of the Fitting ideal specifically. Nothing in this file
states it at those hypotheses; the four declarations that do are in
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/FittingPerfectTransform.lean`, proved from the
globalized resolution of tag 0F7M rather than from tag 0ESS. Two of them,
`AlgebraicGeometry.isPerfect_strictTransformKernel_of_isFinitePresentation` and
`AlgebraicGeometry.hasTorAmplitude_strictTransformKernel_of_isFinitePresentation`, generalize the
two about the kernel proved here.

The first section proves, for a morphism of ringed spaces whose module pullback preserves
homology, that the comparison `Lf^*K ⟶ f^*K` of tag 06YJ is invertible at every complex, hence
that perfectness and Tor amplitude of a module in degree `0` pass to the ordinary pullback. Those
statements are about an arbitrary such morphism, not about a blowup; they are here because the
only consumer is the transport below.

## Implementation notes

**The two spellings of the blowup.** Tag 0ESN is formalized in the base-change spelling: the
structure morphism of the blowup there is `CategoryTheory.Limits.pullback.fst (𝟙 X) (blowUpToBase
I)`, whereas tag 0ESS (`AlgebraicGeometry.isPerfect_modulePullback_blowUpToBase`) and
`AlgebraicGeometry.isAdmissibleBlowup_fittingIdeal` are about `AlgebraicGeometry.blowUpToBase I`
itself. The two differ by precomposition with `CategoryTheory.Limits.pullback.snd (𝟙 X)
(blowUpToBase I)`, which is an isomorphism because the other leg is an identity
(`CategoryTheory.Limits.pullback_snd_iso_of_left_iso`). For admissibility that costs nothing:
`Stacks.Blowup.IsAdmissibleBlowup.comp_iso` records that the predicate of tag 080K, which
exposes its isomorphism with the blowup, is insensitive to precomposition with an isomorphism.
For perfectness and Tor amplitude it costs the first section, because the two predicates are
stated of a derived object and have to be carried along a derived pullback.

**Why the comparison morphism is invertible for an exact pullback.** The pullback along an
isomorphism is an equivalence
(`Stacks.Cohomology.modulePullbackIso_isEquivalence`), hence exact, hence
preserves homology. For any such morphism, resolve a complex by a K-flat one
(`Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution`); the comparison is invertible
on a K-flat complex by tag 06YJ, and the resolution stays a quasi-isomorphism after pullback
precisely because pullback preserves homology, so
`AlgebraicGeometry.derivedPullbackComparison_isIso_of_quasiIso` transfers invertibility.

**Perfectness of the kernel.** The short exact sequence gives a distinguished triangle
`𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 𝒦[1]` (`CategoryTheory.ShortComplex.ShortExact.singleTriangle`); `b^*ℱ` is
perfect by the transport above and `𝒬` is perfect because it is finite locally free
(`AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree`), so tag 08CR for the first
vertex applies.

**Tor dimension of the kernel.** The same triangle, with `b^*ℱ` of Tor amplitude in `[-1, 0]`
and `𝒬` flat, puts `𝒦` in Tor amplitude `[-1, 1]` by tag 08CJ (3). The degree `1` is removed by
right t-exactness of the derived tensor product: a module in degree `0` tensored with a module in
degree `0` lies in `D^{≤ 0}` (`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct`).

## References

* [Stacks Project, Tag 0EST](https://stacks.math.columbia.edu/tag/0EST)
* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
* [Stacks Project, Tag 0ESS](https://stacks.math.columbia.edu/tag/0ESS)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Blowup

/-- Being a `U`-admissible blowup is insensitive to precomposition with an isomorphism: the
predicate of tag 080K exposes an isomorphism of the source with the blowup of the centre, and the
two isomorphisms compose. -/
theorem IsAdmissibleBlowup.comp_iso {X X' X'' : AlgebraicGeometry.Scheme.{u}} {U : X.Opens}
    {f : X' ⟶ X} (h : IsAdmissibleBlowup U f) (e : X'' ≅ X') :
    IsAdmissibleBlowup U (e.hom ≫ f) := by
  obtain ⟨I, hfp, hdisj, e', he⟩ := h
  exact ⟨I, hfp, hdisj, e ≪≫ e', by rw [Iso.trans_hom, Category.assoc, he]⟩

end Stacks.Blowup

namespace AlgebraicGeometry

/-! ### Perfectness and Tor amplitude along a morphism whose module pullback is exact -/

/-- **Stacks Project, Tag 06YJ, for an exact pullback.** If the module pullback along a morphism
of ringed spaces preserves homology, the comparison `Lf^*K ⟶ f^*K` is invertible at every
complex: resolve the complex by a K-flat one, where the comparison is invertible, and observe
that the resolution stays a quasi-isomorphism after pullback. -/
theorem isIso_derivedPullbackComparison_of_preservesHomology
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) [(modulePullback f).PreservesHomology]
    (L : CochainComplex (OXMod.{u, u} Y) ℤ) :
    IsIso.{u + 1, u + 1} ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) := by
  obtain ⟨K, q, hK, -, hq, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y L
  have := hq
  exact derivedPullbackComparison_isIso_of_quasiIso f q hq
    (HomologicalComplex.quasiIso_map_of_preservesHomology _ _)
    (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f K hK)

/-- The derived pullback of a module placed in degree `0` along a morphism whose module pullback
preserves homology is the ordinary pullback, again in degree `0`. -/
def derivedPullbackSingleIsoOfPreservesHomology
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) [(modulePullback f).PreservesHomology]
    (M : OXMod.{u, u} Y) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj M) ≅
      (DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj ((modulePullback f).obj M) := by
  let G := modulePullback f
  let K : CochainComplex (OXMod.{u, u} Y) ℤ :=
    (CochainComplex.singleFunctor (OXMod.{u, u} Y) 0).obj M
  let eX : (DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj M ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (OXMod.{u, u} Y) (ComplexShape.up ℤ)).obj K) :=
    (DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} Y) 0).app M ≪≫
      ((DerivedCategory.quotientCompQhIso (OXMod.{u, u} Y)).app K).symm
  let eOrd := DerivedCategory.Qh.mapIso
      ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso (OXMod.{u, u} X)).app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapCochainComplexSingleFunctor G 0).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} X) 0).app (G.obj M)).symm
  exact (derivedPullback f).mapIso eX ≪≫
    @asIso _ _ _ _ _ (isIso_derivedPullbackComparison_of_preservesHomology f K) ≪≫ eOrd

/-- The ordinary pullback of a perfect module along a morphism whose module pullback preserves
homology is perfect: the derived pullback of a perfect object is perfect by tag 09UA, and here
the derived pullback is the ordinary one. -/
theorem isPerfect_modulePullback_of_preservesHomology
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) [(modulePullback f).PreservesHomology]
    (M : OXMod.{u, u} Y)
    (h : IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj M)) :
    IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj ((modulePullback f).obj M)) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback f _ h
  exact ⟨E, hE, ⟨eE ≪≫ derivedPullbackSingleIsoOfPreservesHomology f M⟩⟩

/-- The ordinary pullback of a module of Tor amplitude in `[a, b]` along a morphism whose module
pullback preserves homology again has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitude_modulePullback_of_preservesHomology
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) [(modulePullback f).PreservesHomology]
    (M : OXMod.{u, u} Y) (a b : ℤ)
    (h : HasTorAmplitude Y ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj M) a b) :
    HasTorAmplitude X
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj ((modulePullback f).obj M)) a b := by
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1}
    (Pullback.hasTorAmplitude_derivedPullback f _ a b h)
    (derivedPullbackSingleIsoOfPreservesHomology f M).symm

/-- Perfectness of a module placed in degree `0` depends only on its isomorphism class. -/
theorem isPerfect_single_of_iso {X : RingedSpace.{u, u}} {M N : OXMod.{u, u} X} (e : M ≅ N)
    (h : IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M)) :
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj N) := by
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).mapIso e) h

/-- Tor amplitude of a module placed in degree `0` depends only on its isomorphism class. -/
theorem hasTorAmplitude_single_of_iso {X : RingedSpace.{u, u}} {M N : OXMod.{u, u} X} (e : M ≅ N)
    (a b : ℤ)
    (h : HasTorAmplitude X ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M) a b) :
    HasTorAmplitude X ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj N) a b := by
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} h
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).mapIso e).symm

/-- **A module in degree `0` has no Tor in positive degrees.** For an `𝒪_X`-module `M` and any
`𝒪_X`-module `P`, the derived tensor product `M[0] ⊗^L P[0]` lies in `D^{≤ 0}`, by right
t-exactness of the derived tensor product; so any Tor-amplitude interval of `M[0]` may have its
upper end lowered to `0`. -/
theorem hasTorAmplitude_single_upper_zero {X : RingedSpace.{u, u}} (M : OXMod.{u, u} X)
    (a b : ℤ)
    (h : HasTorAmplitude X ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M) a b) :
    HasTorAmplitude X ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M) a 0 := by
  intro P i hi
  by_cases hia : i < a
  · exact h P i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega)
  · have hi0 : 0 + 0 < i := by simp only [Set.mem_Icc, not_and_or, not_le] at hi; omega
    have hM : ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M).IsLE 0 := inferInstance
    have hP : ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj P).IsLE 0 := inferInstance
    have hle := @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct _ _ _ X.sheaf
      _ _ _ _ _ _ (derTensor X)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj P) 0 0 hM hP
    exact (DerivedCategory.isLE_iff _ (0 + 0)).1 hle i hi0

/-- **A perfect module is of finite presentation.** An `𝒪_X`-module on a scheme which is perfect
when placed in degree `0` is of finite presentation: a perfect object is pseudo-coherent, in
particular `(-1)`-pseudo-coherent, and a module in degree `0` is `(-1)`-pseudo-coherent exactly
when it is of finite presentation (Stacks 09V9 (2)). -/
theorem isFinitePresentation_of_isPerfect_single {X : Scheme.{u}} (F : X.Modules)
    (hperfect : IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F)) :
    F.IsFinitePresentation := by
  obtain ⟨E, hE, he⟩ := hperfect
  exact RingedSpace.isFinitePresentation_of_isPseudoCoherentFrom_singleFunctor_zero_neg_one F
    ⟨E, RingedSpace.IsPerfectComplex.isPseudoCoherentComplex hE (-1), he⟩

/-- **The kernel of a surjection onto a finite locally free module keeps Tor dimension at most
one.** For a short exact sequence `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒬 ⟶ 0` of `𝒪_Y`-modules with `ℬ` of Tor
dimension at most one and `𝒬` finite locally free, `𝒜` has Tor dimension at most one.

The triangle `𝒜[0] ⟶ ℬ[0] ⟶ 𝒬[0] ⟶ 𝒜[1]` and tag 08CJ (3) put `𝒜[0]` in Tor amplitude
`[-1, 1]`, `𝒬` being flat; `AlgebraicGeometry.hasTorAmplitude_single_upper_zero` removes the
degree `1`. -/
theorem hasTorAmplitude_X₁_of_shortExact_isFiniteLocallyFree {Y : Scheme.{u}}
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (h₂ : HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₂) (-1) 0)
    (h₃ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) S.X₃) :
    HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₁) (-1) 0 := by
  have hB : HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₂) (-2 + 1) (0 + 1) :=
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} h₂
      (show (-2 : ℤ) + 1 ≤ -1 by omega) (show (0 : ℤ) ≤ 0 + 1 by omega)
  have hQ : HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₃) (-2) 0 :=
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree Y S.X₃ h₃)
      (show (-2 : ℤ) ≤ 0 by omega) le_rfl
  have hA : HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₁) (-2 + 1) (0 + 1) :=
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₁.{u, u + 1}
      hS.singleTriangle hS.singleTriangle_distinguished (-2) 0 hB hQ
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
    (hasTorAmplitude_single_upper_zero (X := Y.toRingedSpace) S.X₁ _ _ hA)
    (show (-1 : ℤ) ≤ -2 + 1 by omega) le_rfl

/-! ### The blowup in the base-change spelling -/

section Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The second projection of the base change of the blowup along the identity of `X` is an
isomorphism of sheaved spaces: it is an isomorphism of schemes because the other leg is an
identity, and the forgetful functor to sheaved spaces carries isomorphisms to isomorphisms. -/
theorem isIso_toShHom_pullback_snd_blowUpToBase :
    IsIso ((pullback.snd (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom) := by
  have h : IsIso (pullback.snd (𝟙 X) (blowUpToBase I)) := by
    change IsIso (pullback.snd (𝟙 X) (show _ ⟶ X from blowUpToBase I))
    infer_instance
  have := h
  exact inferInstanceAs (IsIso ((Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).map (pullback.snd (𝟙 X) (blowUpToBase I))))

/-- Module pullback along the second projection of the base change of the blowup along the
identity preserves homology: that projection is an isomorphism, so its module pullback is an
equivalence, hence exact. -/
instance preservesHomology_modulePullback_snd_blowUpToBase :
    (modulePullback ((pullback.snd (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom)
      ).PreservesHomology := by
  have := isIso_toShHom_pullback_snd_blowUpToBase I
  have he : (modulePullback
      (asIso ((pullback.snd (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom)).hom).IsEquivalence :=
    Stacks.Cohomology.modulePullbackIso_isEquivalence _
  have := he
  have : PreservesFiniteLimits (modulePullback
      ((pullback.snd (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom)) := inferInstance
  have hc : PreservesColimits (modulePullback
      ((pullback.snd (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom)) :=
    Adjunction.leftAdjoint_preservesColimits (modulePullbackPushforwardAdjunction _)
  have := hc
  have : PreservesFiniteColimits (modulePullback
      ((pullback.snd (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom)) := inferInstance
  exact Functor.preservesHomologyOfExact _

/-- The structure morphism of the base change of the blowup along the identity factors as the
second projection followed by the blowup morphism. -/
theorem toShHom_pullback_fst_blowUpToBase :
    (pullback.fst (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom =
      (pullback.snd (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom ≫
        (blowUpToBase I).toLRSHom.toShHom :=
  congrArg (fun f : _ ⟶ X => f.toLRSHom.toShHom)
    ((Category.comp_id _).symm.trans (pullback.condition ..))

/-- The pullback of a module to the base change of the blowup along the identity, as the pullback
to the blowup followed by the pullback along the second projection. -/
def modulePullbackFstIso (F : OXMod.{u, u} X.toRingedSpace) :
    (modulePullback ((pullback.fst (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom)).obj F ≅
      (modulePullback ((pullback.snd (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom)).obj
        ((modulePullback ((blowUpToBase I).toLRSHom.toShHom)).obj F) :=
  eqToIso (congrArg (fun f => (modulePullback f).obj F)
      (toShHom_pullback_fst_blowUpToBase I)) ≪≫
    ((Stacks.DerivedPullback.Composition.modulePullbackComp
      ((pullback.snd (𝟙 X) (blowUpToBase I)).toLRSHom.toShHom)
      ((blowUpToBase I).toLRSHom.toShHom)).app F).symm

/-- **Perfectness transported from the blowup to its base change along the identity.** The
pullback of a perfect `𝒪_X`-module of Tor dimension at most one to the base change of the blowup
of `I` along the identity of `X` is perfect.

This is tag 0ESS, which is stated on the blowup itself, moved along the isomorphism of the base
change with the blowup; the hypotheses are the ones tag 0ESS makes, on `ℱ` over `X`, and `I` is an
arbitrary ideal sheaf. Part (4) of tag 0ESN is a different statement, about the blowup of the
Fitting ideal and assuming only that `ℱ` is finitely presented; it is carried at those hypotheses
by `AlgebraicGeometry.isPerfect_modulePullback_fittingBlowUpFst` and
`AlgebraicGeometry.isPerfect_strictTransformKernel_of_isFinitePresentation` in
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/FittingPerfectTransform.lean`.

The registration below records that this statement is the base-change spelling used in the
proof of part (4); it is not a claim that it is part (4). -/
@[stacks 0ESN "the pullback is perfect"]
theorem isPerfect_modulePullback_pullbackFst_blowUpToBase (F : OXMod.{u, u} X.toRingedSpace)
    (hperfect : IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F))
    (htor : HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0) :
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase I)).toRingedSpace)
        0).obj
      ((Scheme.Modules.pullback (pullback.fst (𝟙 X) (blowUpToBase I))).obj F)) :=
  isPerfect_single_of_iso (modulePullbackFstIso I F).symm
    (isPerfect_modulePullback_of_preservesHomology _ _
      (isPerfect_modulePullback_blowUpToBase I F hperfect htor))

/-- **Tor amplitude transported from the blowup to its base change along the identity.** The
pullback of an `𝒪_X`-module of Tor dimension at most one to the base change of the blowup of `I`
along the identity of `X` again has Tor dimension at most one.

As above this is the base-change spelling of tag 0ESS, at the hypotheses tag 0ESS makes and for
an arbitrary ideal sheaf `I`, not part (4) of tag 0ESN. The latter is
`AlgebraicGeometry.hasTorAmplitude_modulePullback_fittingBlowUpFst` and
`AlgebraicGeometry.hasTorAmplitude_strictTransformKernel_of_isFinitePresentation` in
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/FittingPerfectTransform.lean`, which assume only
that `ℱ` is finitely presented.

As above, the registration below records the base-change spelling used in the proof of part (4), not
part (4) itself. -/
@[stacks 0ESN "the Tor dimension of the pullback"]
theorem hasTorAmplitude_modulePullback_pullbackFst_blowUpToBase
    (F : OXMod.{u, u} X.toRingedSpace)
    (htor : HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0) :
    HasTorAmplitude
      (Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase I)).toRingedSpace
      ((DerivedCategory.singleFunctor
        (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X)
          (blowUpToBase I)).toRingedSpace) 0).obj
        ((Scheme.Modules.pullback (pullback.fst (𝟙 X) (blowUpToBase I))).obj F)) (-1) 0 :=
  hasTorAmplitude_single_of_iso (modulePullbackFstIso I F).symm (-1) 0
    (hasTorAmplitude_modulePullback_of_preservesHomology _ _ (-1) 0
      (hasTorAmplitude_modulePullback_blowUpToBase I F htor))

end Blowup

/-! ### Stacks 0EST: the blowup, the sequence, and the perfectness of the kernel -/

variable {X : Scheme.{u}} (F : X.Modules) (r : ℕ)

/-- The canonical surjection from the pullback of a module along the Fitting blowup onto its
strict transform, in the base-change spelling of tag 0ESN. Its kernel is
`AlgebraicGeometry.strictTransformKernel`. -/
abbrev strictTransformQuotientMap :
    (Scheme.Modules.pullback
        (pullback.fst (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ))))).obj F ⟶
      Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))
        (exceptionalIdeal (fittingIdeal F (r : ℤ))) F :=
  Stacks.StrictTransform.π (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))
    (exceptionalIdeal (fittingIdeal F (r : ℤ))) F

/-- The sequence `0 ⟶ 𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 0` of tag 0EST: the kernel of the canonical surjection
onto the strict transform, that surjection, and the pullback in between. -/
abbrev strictTransformKernelSequence : ShortComplex
    (Stacks.StrictTransform.baseChange (𝟙 X)
      (blowUpToBase (fittingIdeal F (r : ℤ)))).Modules :=
  ShortComplex.mk (kernel.ι (strictTransformQuotientMap F r))
    (strictTransformQuotientMap F r) (kernel.condition _)

/-- **The Fitting blowup is admissible.** The structure morphism of the blowup of `X` in the
`r`-th Fitting ideal of `ℱ`, written as the base change of that blowup along the identity of `X`,
is a `U`-admissible blowup.

This is `AlgebraicGeometry.isAdmissibleBlowup_fittingIdeal` moved across the isomorphism
`CategoryTheory.Limits.pullback.snd (𝟙 X) (blowUpToBase I)`, which is the isomorphism of the base
change along an identity with the other factor. -/
theorem isAdmissibleBlowup_fittingBlowUpFst [F.IsFinitePresentation] (U : X.Opens)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    Stacks.Blowup.IsAdmissibleBlowup U
      (pullback.fst (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))) := by
  have hfac : pullback.fst (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ))) =
      (asIso (pullback.snd (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ))))).hom ≫
        blowUpToBase (fittingIdeal F (r : ℤ)) :=
    (Category.comp_id _).symm.trans pullback.condition
  rw [hfac]
  exact (isAdmissibleBlowup_fittingIdeal F U r hrank).comp_iso _

/-- **The kernel sequence is short exact.** The kernel inclusion into the pullback
of `ℱ` along the Fitting blowup and the canonical surjection onto the strict transform form a
short exact sequence

`0 ⟶ 𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 0`.

The surjection is a cokernel, hence an epimorphism, and its kernel inclusion is a monomorphism
which is a kernel, which is exactly short exactness. -/
theorem shortExact_strictTransformKernel :
    (strictTransformKernelSequence F r).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := show Mono (kernel.ι (strictTransformQuotientMap F r)) from inferInstance
  epi_g := show Epi (strictTransformQuotientMap F r) from inferInstance

/-- The strict transform of a finitely presented module of constant rank `r` on a dense open is
finite locally free. -/
private theorem isFiniteLocallyFree_strictTransform_sheaf [F.IsFinitePresentation] (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))
        (exceptionalIdeal (fittingIdeal F (r : ℤ))) F) :=
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  have := isFiniteLocallyFreeOfRank_strictTransform_of_dense F U r hU hrank
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r

/-- **The kernel is perfect.** The kernel of the canonical
surjection from `b^*ℱ` onto the strict transform of `ℱ` is a perfect `𝒪_{X'}`-module.

The short exact sequence gives a distinguished triangle `𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 𝒦[1]`; `b^*ℱ` is perfect
by tag 0ESS and `𝒬` is perfect because it is finite locally free of rank `r` by tag 0ESN (2), so
the first vertex is perfect by tag 08CR. -/
theorem isPerfect_strictTransformKernel [F.IsFinitePresentation] (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r)
    (hperfect : IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F))
    (htor : HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0) :
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X)
        (blowUpToBase (fittingIdeal F (r : ℤ)))).toRingedSpace) 0).obj
      (strictTransformKernel F r)) := by
  have := isFiniteLocallyFree_strictTransform_sheaf F r U hU hrank
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished
    (shortExact_strictTransformKernel F r).singleTriangle
    (shortExact_strictTransformKernel F r).singleTriangle_distinguished
    (isPerfect_modulePullback_pullbackFst_blowUpToBase (fittingIdeal F (r : ℤ)) F hperfect htor)
    (isPerfect_singleFunctor_of_isFiniteLocallyFree
      (Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ))))
      (Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))
        (exceptionalIdeal (fittingIdeal F (r : ℤ))) F)
      (isFiniteLocallyFree_of_isFiniteLocallyFreeClass _))

/-- **The kernel has Tor dimension at most one.** The kernel of the canonical surjection from
`b^*ℱ` onto the strict transform of `ℱ`, placed in degree `0`, has Tor amplitude in `[-1, 0]`.

The short exact sequence gives a distinguished triangle `𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 𝒦[1]`. Here `b^*ℱ` has
Tor amplitude in `[-1, 0]` by tag 0ESS and `𝒬` in `[0, 0]`, being finite locally free hence flat,
so tag 08CJ (3) puts `𝒦` in `[-1, 1]`. A module in degree `0` has no Tor in positive degrees
(`AlgebraicGeometry.hasTorAmplitude_single_upper_zero`), which removes degree `1`. -/
theorem hasTorAmplitude_strictTransformKernel [F.IsFinitePresentation] (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r)
    (htor : HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0) :
    HasTorAmplitude (Stacks.StrictTransform.baseChange (𝟙 X)
        (blowUpToBase (fittingIdeal F (r : ℤ)))).toRingedSpace
      ((DerivedCategory.singleFunctor
        (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X)
          (blowUpToBase (fittingIdeal F (r : ℤ)))).toRingedSpace) 0).obj
        (strictTransformKernel F r)) (-1) 0 := by
  have := isFiniteLocallyFree_strictTransform_sheaf F r U hU hrank
  exact hasTorAmplitude_X₁_of_shortExact_isFiniteLocallyFree (strictTransformKernelSequence F r)
    (shortExact_strictTransformKernel F r)
    (hasTorAmplitude_modulePullback_pullbackFst_blowUpToBase (fittingIdeal F (r : ℤ)) F htor)
    (isFiniteLocallyFree_of_isFiniteLocallyFreeClass _)

/-- **Stacks Project, Tag 0EST.** Let `ℱ` be a perfect `𝒪_X`-module of Tor dimension at most
one which is finite locally free of constant rank `r` on a scheme-theoretically dense open `U`.
Then there is a `U`-admissible blowup `b : X' ⟶ X` and a short exact sequence

`0 ⟶ 𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 0`

with `𝒬` finite locally free of rank `r` and `𝒦` finitely presented, perfect, of Tor dimension at
most one, and zero over `U`.

The witnesses are canonical: `X'` is the base change along the identity of `X` of the blowup of
the `r`-th Fitting ideal of `ℱ`, `𝒬` is the strict transform of `ℱ` and `𝒦` is the kernel of the
canonical surjection onto it. The finite presentation of `ℱ`, which the Fitting ideals need, is
not assumed: it follows from perfectness
(`AlgebraicGeometry.isFinitePresentation_of_isPerfect_single`). -/
@[stacks 0EST]
theorem exists_isAdmissibleBlowup_shortExact_strictTransform
    (U : X.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r)
    (hperfect : IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F))
    (htor : HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) (-1) 0) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup U b ∧
      ∃ (K Q : X'.Modules) (i : K ⟶ (Scheme.Modules.pullback b).obj F)
        (p : (Scheme.Modules.pullback b).obj F ⟶ Q) (w : i ≫ p = 0),
        (ShortComplex.mk i p w).ShortExact ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q r ∧
            K.IsFinitePresentation ∧
              IsPerfect.{u, u, u + 1}
                ((DerivedCategory.singleFunctor (OXMod.{u, u} X'.toRingedSpace) 0).obj K) ∧
                HasTorAmplitude X'.toRingedSpace
                  ((DerivedCategory.singleFunctor (OXMod.{u, u} X'.toRingedSpace) 0).obj K)
                  (-1) 0 ∧
                IsZero ((Scheme.Modules.pullback (b ⁻¹ᵁ U).ι).obj K) := by
  have : F.IsFinitePresentation := isFinitePresentation_of_isPerfect_single F hperfect
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  refine ⟨Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ))),
    pullback.fst (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ))),
    isAdmissibleBlowup_fittingBlowUpFst F r U hrank,
    strictTransformKernel F r, _, kernel.ι (strictTransformQuotientMap F r),
    strictTransformQuotientMap F r, kernel.condition _,
    shortExact_strictTransformKernel F r,
    isFiniteLocallyFreeOfRank_strictTransform_of_dense F U r hU hrank,
    strictTransformKernel_isFinitePresentation F U hU r hrank,
    isPerfect_strictTransformKernel F r U hU hrank hperfect htor,
    hasTorAmplitude_strictTransformKernel F r U hU hrank htor,
    strictTransformKernel_restrict_isZero F U r hrank⟩

end AlgebraicGeometry

end
