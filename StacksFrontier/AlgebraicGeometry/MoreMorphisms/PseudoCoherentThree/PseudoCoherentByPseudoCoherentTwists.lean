module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukaiQCoh
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeOpenCoverLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeAbsolute
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRelative09UU
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictFunctorAlongIso
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedTensorProduct
public import StacksFrontier.AlgebraicGeometry.Perfect.BeilinsonCoherentCharacterization
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TwistedFourierMukai
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.RelativeProjectiveBundlePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherence.TwistResolution

/-!
# Relative pseudo-coherence from pseudo-coherent twists of the derived global sections

Let `A` be a ring, let `X` be a scheme separated and of finite presentation over `A` and let
`K ∈ D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent in `D(A)` for every pseudo-coherent
`E` in `D(𝒪_X)`, then `K` is pseudo-coherent relative to `A` ([Stacks, Tag 0CSL]).

## The proof

Relative pseudo-coherence is local on `X`
(`AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_of_forall_exists_opens`), so fix `x ∈ X` and a
derived Chow datum `U, m, V, Z, E` around it ([Stacks, Tag 0CSJ],
`AlgebraicGeometry.exists_derivedChowDatum`), with projections `p : X ×_A ℙᵐ_A ⟶ X` and
`q : X ×_A ℙᵐ_A ⟶ ℙᵐ_A`. Put `L = Rq_*(Lp^*K ⊗^𝐋 E)`.

* For every `i`, `RΓ(ℙᵐ_A, L ⊗^𝐋 𝒪(i)) ≅ RΓ(X, K ⊗^𝐋 Rp_*(E ⊗^𝐋 Lq^*𝒪(i)))`
  ([Stacks, Tag 08EU] twice and the Leray isomorphisms,
  `AlgebraicGeometry.nonempty_derivedGlobalSectionsOver_chowTwist_iso`).
* `E ⊗^𝐋 Lq^*𝒪(i)` is pseudo-coherent ([Stacks, Tag 09J3] and [Stacks, Tag 09U7]), hence so is
  `Rp_*(E ⊗^𝐋 Lq^*𝒪(i))` ([Stacks, Tag 0CSD] for the projective bundle `p`,
  `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_fst_projectiveSpaceOver`), and the
  hypothesis makes the displayed complex pseudo-coherent.
* Hence `L` is pseudo-coherent on `ℙᵐ_A` ([Stacks, Tag 0CSG], (5) ⟹ (1),
  `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.isPseudoCoherent_of_twists`).
* `L|_V ≅ R(U ⟶ V)_*(K|_U)` ([Stacks, Tag 0CSK], `AlgebraicGeometry.chowDatum_fourierMukai`), so
  the latter is pseudo-coherent on the open `V` of `ℙᵐ_A`, which is flat and of finite presentation
  over `A`; as `U ⟶ V` is a closed immersion, [Stacks, Tag 09UU] makes `K|_U` pseudo-coherent
  relative to `A`.

## Implementation notes

The hypothesis is stated with `Stacks.SheafOfModules.derivedTensor`, the derived tensor product
of Stacks 0CSH and Stacks 0GEN, and the geometric steps run with
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the one of Stacks 08EU and 0CSK;
the two agree by `AlgebraicGeometry.RingedSite.derivedTensorObjIso`. Derived categories are the
standard model, as in the definition of relative pseudo-coherence.

## References

* [Stacks Project, Lemma 37.69.4 (Tag 0CSL)](https://stacks.math.columbia.edu/tag/0CSL)
* [Stacks Project, Tag 0CSJ](https://stacks.math.columbia.edu/tag/0CSJ)
* [Stacks Project, Tag 0CSK](https://stacks.math.columbia.edu/tag/0CSK)
* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
* [Stacks Project, Tag 0CSG](https://stacks.math.columbia.edu/tag/0CSG)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 09UU](https://stacks.math.columbia.edu/tag/09UU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

open DerivedChow
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

/-- Projective space over a scheme is locally of finite presentation over it: it is the base
change of the integral model, which is locally of finite type over the Noetherian terminal
scheme. -/
instance locallyOfFinitePresentation_projectiveSpaceOver (m : ℕ) (S : Scheme.{u}) :
    LocallyOfFinitePresentation (projectiveSpaceOver m S ↘ S) := by
  have := locallyOfFiniteType_terminal_from_projectiveSpaceAtUniverse.{u} m
  change LocallyOfFinitePresentation (pullback.fst _ _)
  infer_instance

/-- Along the inclusion of an open subscheme the derived pullback is restriction. -/
def derivedPullbackRestrictIso {X : Scheme.{u}} (U : X.Opens) (K : DerivedCategory X.Modules) :
    (derivedPullback (ofScheme U.ι)).obj K ≅
      (Scheme.Modules.pullback U.ι).mapDerivedCategory.obj K :=
  haveI : PreservesFiniteLimits (modulePullback (ofScheme U.ι)) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pullback U.ι))
  haveI : PreservesFiniteColimits (modulePullback (ofScheme U.ι)) :=
    preservesFiniteColimits_modulePullback _
  (SpecField.derivedPullbackMapDerivedIso (ofScheme U.ι)).app K

/-- Pseudo-coherence of an object of `D(R)` depends only on its isomorphism class. -/
theorem _root_.StacksDraft.PseudoCoherence.IsPseudoCoherent.of_iso {R : Type*} [Ring R]
    {K K' : DerivedCategory (ModuleCat R)} (h : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (e : K ≅ K') : StacksDraft.PseudoCoherence.IsPseudoCoherent K' := by
  obtain ⟨E, hE, ⟨g⟩⟩ := h
  exact ⟨E, hE, ⟨g ≪≫ e⟩⟩

/-- Every twist `𝒪(d)` of projective space, in degree zero, is pseudo-coherent. -/
theorem isPseudoCoherent_singleFunctor_twistOver (m : ℕ) (S : Scheme.{u}) (d : ℤ) :
    RingedSpace.IsPseudoCoherent (X := (projectiveSpaceOver m S).toRingedSpace)
      ((DerivedCategory.singleFunctor (projectiveSpaceOver m S).Modules 0).obj
        (twistOver m S d)) :=
  Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect
    (X := (projectiveSpaceOver m S).toRingedSpace) _
    (Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.isPerfect_singleFunctor_twistOver
      m S d)

section

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- Let `A` be a ring, let `X` be a scheme separated and of finite presentation over `A`, with
structure morphism `f : X ⟶ Spec A`, and let `K ∈ D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗^𝐋 K)` is a
pseudo-coherent object of `D(A)` for every pseudo-coherent object `E` of `D(𝒪_X)`, then `K` is
pseudo-coherent relative to `A`.

"Separated and of finite presentation over `A`" is `IsSeparated f`, `QuasiCompact f` and
`LocallyOfFinitePresentation f` (quasi-separatedness follows from separatedness);
`K ∈ D_QCoh(𝒪_X)` is quasi-coherence of its cohomology sheaves; `RΓ(X, -)` is the `A`-linear
`AlgebraicGeometry.derivedGlobalSectionsOver f`; pseudo-coherence relative to `A` is
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherent f` (Stacks 09UI). -/
@[stacks 0CSL]
theorem isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPseudoCoherent
    (f : X ⟶ Spec (.of A)) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFinitePresentation f] (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hpc : ∀ E : DerivedCategory X.Modules, RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
      StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((derivedGlobalSectionsOver f).obj
          (((Stacks.SheafOfModules.derivedTensor X.sheaf).obj E).obj K))) :
    f.IsPseudoCoherent K := by
  refine Scheme.Hom.isPseudoCoherent_of_forall_exists_opens f K fun x => ?_
  obtain ⟨U, m, V, Z, iZ, z, E, hxU, hiZ, hfpZ, hb, hz, hc, hW, hzV, hE, hEpc, hEsupp⟩ :=
    exists_derivedChowDatum f x
  have := hiZ
  obtain ⟨hι, hιfp, hFM⟩ := chowDatum_fourierMukai f m U V iZ hb hc hW E hE
  have hP2 : ∀ L : DerivedCategory (projectiveSpaceOver m (Spec (.of A))).Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj L).IsQuasicoherent) →
      (∀ d : ℤ, StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((derivedGlobalSectionsOver (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).obj
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            (projectiveSpaceOver m (Spec (.of A))).sheaf).obj L).obj
            ((DerivedCategory.singleFunctor (projectiveSpaceOver m (Spec (.of A))).Modules 0).obj
              (twistOver m (Spec (.of A)) d))))) →
      RingedSpace.IsPseudoCoherent (X := (projectiveSpaceOver m (Spec (.of A))).toRingedSpace) L :=
    fun L hLq hLt => ProjectiveSpacePseudoCoherence.isPseudoCoherent_of_twists m L hLq
      fun d _ => hLt d
  have hCSD : ∀ F : DerivedCategory
      (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).Modules,
      RingedSpace.IsPseudoCoherent (X := (pullback f
        (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).toRingedSpace) F →
      RingedSpace.IsPseudoCoherent (X := X.toRingedSpace)
        ((derivedPushforward (ofScheme (pullback.fst f
          (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))))).obj F) :=
    isPseudoCoherent_derivedPushforward_fst_projectiveSpaceOver m f
  have hEqc := isQuasicoherentDerived_of_isPseudoCoherent.{u, u + 1} _ E hEpc
  have hpK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedPullback (ofScheme (pullback.fst f
        (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))))).obj K)).IsQuasicoherent :=
    fun i => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel _ K hK i
  have hL : RingedSpace.IsPseudoCoherent
      (X := (projectiveSpaceOver m (Spec (.of A))).toRingedSpace)
      ((derivedPushforward (ofScheme (pullback.snd f
          (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))))).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).sheaf).obj
          ((derivedPullback (ofScheme (pullback.fst f
            (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))))).obj K)).obj E)) := by
    have : IsProper (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)) :=
      isProper_projectiveSpaceOver m _
    have : CompactSpace (projectiveSpaceOver m (Spec (.of A))) :=
      QuasiCompact.compactSpace_of_compactSpace
        (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))
    refine hP2 _ (fun i => AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs
      _ _ (TorFormula.isQuasicoherent_homology_derivedTensor _ _ _ hpK hEqc) i) fun d => ?_
    obtain ⟨e⟩ := nonempty_derivedGlobalSectionsOver_chowTwist_iso f m K hK E hEqc d
    have hOpc := isPseudoCoherent_singleFunctor_twistOver m (Spec (.of A)) d
    have hE' := hCSD _ (RingedSpace.isPseudoCoherent_derivedTensorProduct
      (pullback f (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))).toRingedSpace
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) E
      ((derivedPullback (ofScheme (pullback.snd f
        (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))))).obj
        ((DerivedCategory.singleFunctor (projectiveSpaceOver m (Spec (.of A))).Modules 0).obj
          (twistOver m (Spec (.of A)) d))) hEpc
      (Scheme.Hom.isPseudoCoherent_derivedPullback _ _ hOpc))
    refine (hpc _ hE').of_iso ?_
    refine ((derivedGlobalSectionsOver f).mapIso ?_) ≪≫ e.symm
    exact RingedSite.derivedTensorObjIso (Stacks.SheafOfModules.ringedSite X.sheaf) _ K ≪≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).braidingIso
        (Stacks.RingedSpace.toRingedSite X.toRingedSpace) _ K
  obtain ⟨e⟩ := hFM K hK
  have h0 := Scheme.Modules.isPseudoCoherent_derivedPullback _ V _ hL
  have hLV := RingedSpace.IsPseudoCoherent.of_iso (X := V.toScheme.toRingedSpace) h0 e
  have hcomp := chowDatumMorphism_comp_ι_comp _ _ iZ U V f
    (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A)) pullback.condition hb hW
  have := hι
  refine ⟨U, hxU, fun n => ?_⟩
  have h3 := (Scheme.Hom.derivedPushforwardRelative_iff_pseudoCoherentFrom _
    (V.ι ≫ (projectiveSpaceOver m (Spec (.of A)) ↘ Spec (.of A))) _ n).2
      (hLV.isPseudoCoherentFrom n)
  have h1 := (Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforwardRelative _ _ _ n).2 h3
  exact ((Scheme.Hom.isPseudoCoherentFrom_congr_hom hcomp _ n).1 h1).of_iso _
    (derivedPullbackRestrictIso U K ≪≫
      ((Scheme.Modules.mapDerivedCategoryRestrictFunctorIsoPullback U.ι).app K).symm)

end

end AlgebraicGeometry

end
