module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.QuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.ResolvingDatumUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
import StacksCore.Tactic.StacksAttribute

/-!
# A Fourier-Mukai functor and the bounded coherent derived category

Let `S` be a Noetherian scheme, let `X` and `Y` be of finite type over `S` and let
`K ∈ D^b_Coh(𝒪_{X ×_S Y})`. [Stacks, Tag 0FYU] asserts that the Fourier-Mukai functor

`Φ_K : D(𝒪_X) ⟶ D(𝒪_Y)`,  `M ⟼ R pr_{2,*}(L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K)`

of [Stacks, Tag 0FYQ] carries `D^b_Coh(𝒪_X)` into `D^b_Coh(𝒪_Y)` as soon as one of four
alternative conditions holds, and that in each of them the support condition is automatic when
`X ⟶ S` is proper.

This file carries the last of those assertions and the part of the argument that is common to
all four conditions; the whole tag, with each of the four conditions, is
`AlgebraicGeometry.fourierMukai_derivedCategoryBBounded` in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/BoundedCoherentConditions.lean`.

The source proof runs as follows. Write `T = L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K`, so that
`Φ_K(M) = R pr_{2,*} T`. The object `T` is pseudo-coherent, by [Stacks, Tag 09U7] for the
derived pullback and [Stacks, Tag 09J3] for the derived tensor product, hence has coherent
cohomology sheaves by [Stacks, Tag 08E8], `X ×_S Y` being locally Noetherian. The supports of
its cohomology sheaves are proper over `Y`. Granted a bound below on `T`, which is what each of
the four conditions is used to produce, [Stacks, Tag 08E2] applied to
`pr₂ : X ×_S Y ⟶ Y` then puts `R pr_{2,*} T` in `D^b_Coh(𝒪_Y)`.

## Main results

* `AlgebraicGeometry.isProperOver_of_isProper`: over a proper morphism every closed subset of
  the source is proper over the target.
* `AlgebraicGeometry.isProperOver_pullbackSnd_of_isProper`: **[Stacks, Tag 0FYU], the final
  assertion.** When `X ⟶ S` is proper, every closed subset of `X ×_S Y` — in particular the
  support of each `H^i(K)` — is proper over `Y`.
* `AlgebraicGeometry.isCoherent_homology_fourierMukaiTensor`: the cohomology sheaves of
  `L pr_1^* M ⊗^𝐋 K` are coherent, for `M` and `K` in `D^b_Coh`.
* `AlgebraicGeometry.isLE_fourierMukaiPullback` and
  `AlgebraicGeometry.isLE_fourierMukaiTensor`: `L pr_1^*` and `- ⊗^𝐋 K` preserve a bound above.
* `AlgebraicGeometry.derivedCategoryBBounded_fourierMukai_of_isProperOver_supp`:
  **[Stacks, Tag 0FYU], the part of the proof common to the four conditions.** `Φ_K(M)` is in
  `D^b_Coh(𝒪_Y)` once `L pr_1^* M ⊗^𝐋 K` is bounded below and the supports of its cohomology
  sheaves are proper over `Y`.
* `AlgebraicGeometry.derivedCategoryBBounded_fourierMukai_of_isProper`: the same with the
  support hypothesis discharged by the final assertion of the tag, for `X ⟶ S` proper.

## Implementation notes

*The model of the derived categories.* Everything is read at
`CategoryTheory.HasDerivedCategory.standard`, which `AlgebraicGeometry.fourierMukai` and
[Stacks, Tag 08E2] are both stated at; the priority of the local instance selects it over the
locally small model arriving with the imports.

*What the two main statements take as hypotheses, and why.*

The hypothesis `haff` is
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`, the named
`Prop` this library carries for [Stacks, Tag 02O5]. It is what this library's form of
[Stacks, Tag 08E2] takes, and it is passed straight through.

The hypothesis `hGE` is a bound below on `L pr_1^* M ⊗^𝐋 K`. The source reduces all four
conditions of the tag to exactly this — "Hence in each case it suffices to prove that this
tensor product is bounded below" — and each condition is a different way of producing it:
condition (1) assumes finite Tor dimension of `K` over `pr_1^{-1}𝒪_X` outright, conditions (2),
(3) and (4) each derive that finite Tor dimension and then quote condition (1). So `hGE` is the
case distinction of the tag, not its conclusion; the statements below are the content shared by
the four cases, with the case distinction left as a hypothesis.

Everything else the source's argument uses is discharged. The bound above on the tensor product,
which is the other half of what [Stacks, Tag 08E2] consumes, comes from right t-exactness of the
derived pullback (`isLE_fourierMukaiPullback`, proved here from a K-flat strictly bounded above
representative) and right t-exactness of the derived tensor product of [Stacks, Tag 06YU].

*The two spellings of the derived direct image.* `AlgebraicGeometry.fourierMukaiPushforward` is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` and
`AlgebraicGeometry.derivedPushforwardModules`, which [Stacks, Tag 08E2] is stated with, is
`AlgebraicGeometry.RingedSpace.derivedPushforward`; the two are the same total right derived
functor of the same degreewise pushforward, so the conclusion of the tag is read directly
against `Φ_K`.

## References

* [Stacks Project, Tag 0FYU](https://stacks.math.columbia.edu/tag/0FYU)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 09U7](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Tag 09J3](https://stacks.math.columbia.edu/tag/09J3)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0CYN](https://stacks.math.columbia.edu/tag/0CYN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProperSupportCoherent

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Closed subsets of the source of a proper morphism -/

/-- **Every closed subset of the source of a proper morphism is proper over the target.** The
reduced induced closed subscheme on such a subset maps to the source by a closed immersion,
which is proper, and a composition of proper morphisms is proper. -/
theorem isProperOver_of_isProper {Z W : Scheme.{u}} (p : Z ⟶ W) [IsProper p] (T : Closeds Z) :
    IsProperOver p T := by
  show IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p)
  infer_instance

/-! ### The Fourier-Mukai setting -/

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **[Stacks, Tag 0FYU], the final assertion.** If `X ⟶ S` is proper then so is the second
projection `pr₂ : X ×_S Y ⟶ Y`, being its base change, and therefore every closed subset of
`X ×_S Y` is proper over `Y`. In particular the support condition on the cohomology sheaves of
the kernel, which each of the four conditions of the tag makes, holds automatically. -/
theorem isProperOver_pullbackSnd_of_isProper [IsProper f]
    (T : Closeds (Limits.pullback f g : Scheme.{u})) :
    IsProperOver (Limits.pullback.snd f g) T :=
  isProperOver_of_isProper _ T

/-- **The derived pullback along `pr₁` preserves a bound above.** An object of `D^{≤a}(𝒪_X)` is
represented by a K-flat complex whose terms vanish above `a`, by [Stacks, Tag 05T7] and
[Stacks, Tag 06YQ]; on a K-flat complex the derived pullback of [Stacks, Tag 06YJ] is the
degreewise pullback, by [Stacks, Tag 06YS]; and the degreewise pullback of a complex with
vanishing terms above `a` again has vanishing terms above `a`. -/
theorem isLE_fourierMukaiPullback (M : DerivedCategory X.Modules) (a : ℤ) (hM : M.IsLE a) :
    ((fourierMukaiPullback f g).obj M).IsLE a := by
  obtain ⟨F, hF, hFLE, ⟨eF⟩⟩ :=
    @Stacks.DerivedTensor.RingedSite.exists_kFlat_isStrictlyLE_representative _ _ _
      X.toRingedSpace.sheaf _ _ _ _ _ _ M a hM
  have e := Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat
    (Limits.pullback.fst f g).toLRSHom.toShHom F hF
  have hpF : CochainComplex.IsLE (((RingedSpaceModuleAdjunction.modulePullback
      (Limits.pullback.fst f g).toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F) a := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact HomologicalComplex.ExactAt.of_isZero
      (Functor.map_isZero _ (F.isZero_of_isStrictlyLE a i hi))
  have h1 : (DerivedCategory.Q.obj (((RingedSpaceModuleAdjunction.modulePullback
      (Limits.pullback.fst f g).toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F)).IsLE a :=
    (DerivedCategory.isLE_Q_obj_iff _ a).2 hpF
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (e.symm ≪≫ (fourierMukaiPullback f g).mapIso eF) a

/-- **A bound above on `L pr_1^* M` gives one on `L pr_1^* M ⊗^𝐋 K`**, by the right
t-exactness of the derived tensor product of [Stacks, Tag 06YU] in each variable. No finiteness
hypothesis on `S`, `X`, `Y` or `K` is involved. -/
theorem isLE_fourierMukaiTensor (K : DerivedCategory (Limits.pullback f g).Modules)
    (M : DerivedCategory X.Modules) (a b : ℤ)
    (hM : ((fourierMukaiPullback f g).obj M).IsLE a) (hK : K.IsLE b) :
    ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M)).IsLE (a + b) :=
  @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct _ _ _
    (Limits.pullback f g).toRingedSpace.sheaf _ _ _ _ _ _ _
    ((fourierMukaiPullback f g).obj M) K a b hM hK

section FiniteType

variable [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType g] [QuasiCompact g]

/-! ### Coherence of the cohomology of the kernel tensor

`X`, `Y` and `X ×_S Y` are Noetherian throughout: the first two are of finite type over the
Noetherian scheme `S`, and the second projection `X ×_S Y ⟶ Y` is of finite type by base change
from `f`. -/

/-- **The cohomology sheaves of `L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K` are coherent** when those of
`M` and of `K` are and both are bounded above.

This is the first half of the argument of [Stacks, Tag 0FYU], common to its four conditions.
`M` and `K` are pseudo-coherent by [Stacks, Tag 08E8], `L pr_1^* M` is pseudo-coherent by
[Stacks, Tag 09U7], the derived tensor product of two pseudo-coherent objects is pseudo-coherent
by [Stacks, Tag 09J3], and a pseudo-coherent object of `D_QCoh` on a locally Noetherian scheme
has coherent cohomology sheaves, which is [Stacks, Tag 08E8] again. Quasi-coherence of the
cohomology sheaves along the way is [Stacks, Tag 08DW] part (1) for the pullback and
[Stacks, Tag 08DX] part (1) for the tensor product. -/
theorem isCoherent_homology_fourierMukaiTensor
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : DerivedCategoryB.derivedCategoryBMinus
      (fun F : (Limits.pullback f g).Modules => F.IsCoherent) K)
    (M : DerivedCategory X.Modules)
    (hM : DerivedCategoryB.derivedCategoryBMinus (fun F : X.Modules => F.IsCoherent) M)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj
        ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M))).IsCoherent := by
  have hXN : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hYN : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType g
  have hPN : IsNoetherian (Limits.pullback f g) :=
    isNoetherian_of_locallyOfFiniteType (Limits.pullback.snd f g)
  -- Pseudo-coherence and quasi-coherence of the cohomology of the two factors, by Tag 08E8.
  have hfactor : ∀ (Z : Scheme.{u}) [IsNoetherian Z] (N : DerivedCategory Z.Modules),
      DerivedCategoryB.derivedCategoryBMinus (fun F : Z.Modules => F.IsCoherent) N →
        RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace) N ∧
          ∀ j : ℤ, ((DerivedCategory.homologyFunctor Z.Modules j).obj N).IsQuasicoherent :=
    fun Z _ N ⟨hNb, hNc⟩ =>
      ⟨TorFormula.isPseudoCoherent_of_isBoundedAbove_of_isCoherent_homology Z N hNb hNc,
        fun j => have := hNc j; _root_.isQuasicoherent_of_isCoherent _⟩
  obtain ⟨hMpc, hMq⟩ := hfactor X M hM
  obtain ⟨hKpc, hKq⟩ := hfactor _ K hK
  -- Pseudo-coherence of the derived pullback, by Tag 09U7.
  have hApc : RingedSpace.IsPseudoCoherent
      (X := (Limits.pullback f g).toRingedSpace) ((fourierMukaiPullback f g).obj M) := by
    have hfrom : ∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
        (X := (Limits.pullback f g).toRingedSpace)
        ((fourierMukaiPullback f g).obj M) m := fun m =>
      RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
        (Limits.pullback.fst f g).toLRSHom.toShHom M m (hMpc.isPseudoCoherentFrom m)
    obtain ⟨C, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (F := DerivedCategory.Q
        (C := StrictlyPerfect.OXMod.{u, u} (Limits.pullback f g).toRingedSpace))
      ((fourierMukaiPullback f g).obj M)
    exact ⟨C, fun m => RingedSpace.isPseudoCoherentComplexFrom_of_iso _ m (hfrom m) C e, ⟨e⟩⟩
  -- Pseudo-coherence of the derived tensor product, by Tag 09J3.
  have hTpc := RingedSpace.isPseudoCoherent_derivedTensorProduct
    (Limits.pullback f g).toRingedSpace
    (Stacks.Cohomology.TorAmplitude.derTensor (Limits.pullback f g).toRingedSpace)
    ((fourierMukaiPullback f g).obj M) K hApc hKpc
  -- Quasi-coherence of the cohomology sheaves of the derived tensor product.
  have hpullq : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      ((fourierMukaiPullback f g).obj M)).IsQuasicoherent := fun j =>
    Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
      (Limits.pullback.fst f g) M hMq j
  have htensq : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      ((fourierMukaiTensor f g K).obj
        ((fourierMukaiPullback f g).obj M))).IsQuasicoherent := fun j =>
    TorFormula.isQuasicoherent_homology_derivedTensor (Limits.pullback f g)
      ((fourierMukaiPullback f g).obj M) K hpullq hKq j
  -- Coherence, by the other half of Tag 08E8.
  exact isCoherent_homology_of_isPseudoCoherentFrom (Limits.pullback f g) _ i htensq
    (hTpc.isPseudoCoherentFrom i) i le_rfl

/-! ### The Fourier-Mukai functor on the bounded coherent derived categories -/

/-- **[Stacks, Tag 0FYU], the part of the proof common to its four conditions.** Let `S` be a
Noetherian scheme, let `X` and `Y` be of finite type over `S`, let `K` be an object of
`D^b_Coh(𝒪_{X ×_S Y})` and let `M` be an object of `D^b_Coh(𝒪_X)`. Suppose that the supports of
the cohomology sheaves of `T = L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K` are proper over `Y` and that `T`
is bounded below. Then `Φ_K(M)` is an object of `D^b_Coh(𝒪_Y)`.

The cohomology sheaves of `T` are coherent by `isCoherent_homology_fourierMukaiTensor`, and `T`
is bounded above by `isLE_fourierMukaiPullback` and `isLE_fourierMukaiTensor`;
[Stacks, Tag 08E2] applied to the second projection, which is locally of finite type by base
change, then gives the conclusion.

Producing the bound below on `T` is what each of the four conditions of the tag is for; it is
the hypothesis `hGE`. The hypothesis `haff` is this library's named form of
[Stacks, Tag 02O5], which is the hypothesis of its [Stacks, Tag 08E2]. -/
theorem derivedCategoryBBounded_fourierMukai_of_isProperOver_supp
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun F : (Limits.pullback f g).Modules => F.IsCoherent) K)
    (M : DerivedCategory X.Modules)
    (hM : DerivedCategoryB.derivedCategoryBBounded (fun F : X.Modules => F.IsCoherent) M)
    (d : ℤ) (hGE : ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M)).IsGE d)
    (hsupp : ∀ (j : ℤ) (hcl : IsClosed (SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
        ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M))))),
      IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : Y.Modules => N.IsCoherent)
      ((fourierMukai f g K).obj M) := by
  have hYN : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType g
  obtain ⟨⟨hKlo, b, hKhi⟩, hKc⟩ := hK
  obtain ⟨⟨hMlo, c, hMhi⟩, hMc⟩ := hM
  have hKLE : K.IsLE b := (DerivedCategory.isLE_iff K b).2 fun j hj => hKhi j hj
  have hMLE : M.IsLE c := (DerivedCategory.isLE_iff M c).2 fun j hj => hMhi j hj
  have hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M))).IsCoherent := fun j =>
    isCoherent_homology_fourierMukaiTensor f g K ⟨⟨b, hKhi⟩, hKc⟩ M ⟨⟨c, hMhi⟩, hMc⟩ j
  have hLE := isLE_fourierMukaiTensor f g K M c b
    (isLE_fourierMukaiPullback f g M c hMLE) hKLE
  exact derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp (Limits.pullback.snd f g)
    _ hcoh (fun j => hsupp j _) haff d (c + b) hGE hLE

omit [LocallyOfFiniteType f] in
/-- **[Stacks, Tag 0FYU] for a proper `X ⟶ S`, the part of the proof common to its four
conditions.** When `X ⟶ S` is proper the support hypothesis of the tag is automatic, by
`isProperOver_pullbackSnd_of_isProper`, so the only thing the four conditions are still needed
for is the bound below on `L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K`. -/
theorem derivedCategoryBBounded_fourierMukai_of_isProper [IsProper f]
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun F : (Limits.pullback f g).Modules => F.IsCoherent) K)
    (M : DerivedCategory X.Modules)
    (hM : DerivedCategoryB.derivedCategoryBBounded (fun F : X.Modules => F.IsCoherent) M)
    (d : ℤ) (hGE : ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M)).IsGE d)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : Y.Modules => N.IsCoherent)
      ((fourierMukai f g K).obj M) :=
  derivedCategoryBBounded_fourierMukai_of_isProperOver_supp f g K hK M hM d hGE
    (fun _ hcl => isProperOver_pullbackSnd_of_isProper f g ⟨_, hcl⟩) haff

end FiniteType

end AlgebraicGeometry

end
