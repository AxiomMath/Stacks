module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LocallySmallModel
public import StacksFrontier.AlgebraicGeometry.Duality.InternalHom.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidalModelComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonFlat
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomStrengthTensorDual
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentCompactDualizable
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# The right adjoint of a Fourier-Mukai transform at the locally small model

Let `X ⟶ S` and `Y ⟶ S` be morphisms of quasi-compact quasi-separated schemes, `p` and `q` the two
projections of `X ×_S Y`, `K` a pseudo-coherent object of `D_QCoh(𝒪_{X ×_S Y})`, and `a` the right
adjoint of `Rq_* : D_QCoh(𝒪_{X ×_S Y}) ⥤ D_QCoh(𝒪_Y)` ([Stacks, Tag 0A9E]). This file proves the
core of [Stacks, Tag 0FYW] at the locally small model of the derived categories, where `a` is
constructed.

The kernel is `K' = R𝓗om(K, a(𝒪_Y))`, which lies in `D_QCoh` by [Stacks, Tag 0A6H] and
[Stacks, Tag 0A9I] (`Stacks.Duality.dualKernel`); the transform `Φ'` of the statement is,
after the exchange of the factors, `N ↦ Rp_*(Lq^*N ⊗ᴸ K')`
(`Stacks.Duality.fourierMukaiDualLocallySmall`). The canonical map
`Hom_X(M, Φ'(N)) ⟶ Hom_Y(Φ(M), N)` is the source's composite
`Hom(M, Rp_*(Lq^*N ⊗ K')) = Hom(Lp^*M, Lq^*N ⊗ K') ⟶ Hom(Lp^*M, R𝓗om(K, a(N)))
  = Hom(Lp^*M ⊗ K, a(N)) = Hom(Rq_*(Lp^*M ⊗ K), N)`,
the middle arrow being composition with `γ = R𝓗om(K, β) ∘ α`, where
`α : Lq^*N ⊗ R𝓗om(K, a(𝒪_Y)) ⟶ R𝓗om(K, Lq^*N ⊗ a(𝒪_Y))` is the map of [Stacks, Tag 0BYS] (in its
adjunction-theoretic form, the strength of `- ⊗ᴸ K ⊣ R𝓗om(K, -)`) and
`β : Lq^*N ⊗ a(𝒪_Y) ⟶ a(N)` is the map of [Stacks, Tag 0A9S].

`γ` is invertible when `N` is perfect (`α` by [Stacks, Tag 0ATN], `Lq^*N` being perfect,
[Stacks, Tag 09UA]; `β` by [Stacks, Tag 0A9T]) and when `K` is perfect and `X ⟶ S` is proper, flat
and of finite presentation (`α` by [Stacks, Tag 0ATN], `β` by [Stacks, Tag 0E4K] for the base
change `q` of `X ⟶ S`). The composite is then bijective, every other step being a bijection.

## Main definitions

* `Stacks.Duality.InternalHom.tensorRightSheafHomAdjunction`: [Stacks, Tag 08J8] at the locally
  small model, for the monoidal structure
  `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal`.
* `Stacks.Duality.dualKernel`: `R𝓗om(K, a(𝒪_Y))`.
* `Stacks.Duality.dualKernelPairing`: the map `γ`.
* `Stacks.Duality.rightAdjointComparison`: the canonical map.

## Main results

* `Stacks.Duality.rightAdjointComparison_naturality_left`,
  `Stacks.Duality.rightAdjointComparison_naturality_right`: it is natural in `M` and `N`.
* `Stacks.Duality.isIso_dualKernelPairing_of_isPerfect`,
  `Stacks.Duality.isIso_dualKernelPairing_of_isPerfect_of_flat`: the two invertibility criteria.
* `Stacks.Duality.bijective_rightAdjointComparison_of_isIso`.

## References

* [Stacks Project, Tag 0FYW](https://stacks.math.columbia.edu/tag/0FYW)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace Stacks.Duality.InternalHom

variable {X : Scheme.{u}}

/-- **The transported tensor product is the derived tensor product.** `- ⊗ᴸ P` of the standard
model conjugated by the comparison of the two models
(`Stacks.Duality.InternalHom.derivedTensorRight`)
is tensoring with `P` for the monoidal structure
`AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal` of the locally small model: the
comparison is a monoidal functor
(`AlgebraicGeometry.Scheme.Modules.derivedMonoidalModelComparison`). -/
def derivedTensorRightIso (P : DerivedCategory X.Modules) :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    derivedTensorRight P ≅ MonoidalCategory.tensorRight P :=
  letI := Scheme.Modules.standardDerivedMonoidal X
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI := Scheme.Modules.derivedMonoidalModelComparison X
  let E := StacksDraft.DerivedModel.schemeModulesComparison X
  let P₀ := E.inverse.obj P
  let μ : MonoidalCategory.tensorRight P₀ ⋙ E.functor ≅
      E.functor ⋙ MonoidalCategory.tensorRight (E.functor.obj P₀) :=
    NatIso.ofComponents (fun A => (Functor.Monoidal.μIso E.functor A P₀).symm)
      (fun {A A'} φ => by
        dsimp
        rw [Functor.OplaxMonoidal.δ_natural_left])
  Functor.isoWhiskerLeft E.inverse μ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight E.counitIso _ ≪≫ Functor.leftUnitor _ ≪≫
    (tensoringRight _).mapIso (E.counitIso.app P)

/-- **[Stacks, Tag 08J8] at the locally small model, at its monoidal structure**: tensoring with
`P` for `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal` is left adjoint to
`R𝓗om(P, -)`. -/
def tensorRightSheafHomAdjunction (P : DerivedCategory X.Modules) :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    MonoidalCategory.tensorRight P ⊣ derivedSheafHom P :=
  (derivedTensorSheafHomAdjunction P).ofNatIsoLeft (derivedTensorRightIso P)

end Stacks.Duality.InternalHom

namespace Stacks.Duality

/-- **The left dual of a perfect object of `D(𝒪_X)` at the locally small model**, for the monoidal
structure `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal`: the exact pairing of
[Stacks, Tag 0FPC] at the standard model, carried across the monoidal comparison of the two
models. -/
@[instance_reducible]
def exactPairingDerivedDualLocallySmall {X : Scheme.{u}} (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    ExactPairing E (Stacks.SheafOfModules.derivedDual X.sheaf E) :=
  Scheme.Modules.exactPairingOfStandard X E _
    (exactPairingDerivedDualStandard E
      ((AlgebraicGeometry.PerfectApproximation.isPerfect_standard_iff E).2 hE))

/-- In a full subcategory, the morphism with a given underlying morphism is compatible with
precomposition. -/
theorem _root_.CategoryTheory.ObjectProperty.fullyFaithfulι_homEquiv_symm_comp {C : Type*}
    [Category* C] (P : ObjectProperty C) {A B D : P.FullSubcategory} (w : A ⟶ B)
    (z : P.ι.obj B ⟶ P.ι.obj D) :
    P.fullyFaithfulι.homEquiv.symm (P.ι.map w ≫ z) = w ≫ P.fullyFaithfulι.homEquiv.symm z :=
  rfl

section RightAdjoint

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace (pullback f g : Scheme.{u})] [QuasiSeparatedSpace (pullback f g : Scheme.{u})]

/-- The right adjoint `a` of `Rq_* : D_QCoh(𝒪_{X ×_S Y}) ⥤ D_QCoh(𝒪_Y)`, `q` the second
projection ([Stacks, Tag 0A9E]). -/
abbrev secondProjectionTwistedInverseImage :
    quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory (pullback f g) :=
  twistedInverseImage (pullback.snd f g) (isQuasicoherent_homology_derivedPushforward_of_qcqs _)

/-- The adjunction `Rq_* ⊣ a`. -/
abbrev secondProjectionTwistedAdjunction :
    quasiCoherentDerivedPushforward (pullback.snd f g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⊣
      secondProjectionTwistedInverseImage f g :=
  twistedInverseImageAdjunction (pullback.snd f g)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)

/-- `a(𝒪_Y)`. -/
abbrev twistedUnit : quasiCoherentDerivedCategory (pullback f g) :=
  (secondProjectionTwistedInverseImage f g).obj (𝟙_ _)

/-- `a(𝒪_Y)` lies in `D⁺_QCoh` ([Stacks, Tag 0A9I]). -/
theorem twistedUnit_mem_derivedCategoryBPlus :
    DerivedCategoryB.derivedCategoryBPlus (A := (pullback f g).Modules)
      (SheafOfModules.isQuasicoherent (pullback f g).ringCatSheaf) (twistedUnit f g).obj :=
  ⟨isBoundedBelow_twistedInverseImage_obj (pullback.snd f g) (𝟙_ _)
    (KoszulRegular.isBoundedBelow_singleFunctor_obj (SheafOfModules.unit Y.ringCatSheaf)),
    (twistedUnit f g).property⟩

/-- **The kernel `R𝓗om(K, a(𝒪_Y))` on `X ×_S Y`**, at the locally small model, for `K`
pseudo-coherent: it has quasi-coherent cohomology sheaves by [Stacks, Tag 0A6H], `a(𝒪_Y)` being
in `D⁺_QCoh` by [Stacks, Tag 0A9I]. -/
def dualKernel (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj) :
    quasiCoherentDerivedCategory (pullback f g) :=
  ⟨(InternalHom.derivedSheafHom K.obj).obj (twistedUnit f g).obj, fun i =>
    InternalHom.isQuasicoherent_homology_derivedSheafHom_of_isPseudoCoherent K.obj _ hK
      (twistedUnit_mem_derivedCategoryBPlus f g) i⟩

/-- Equation 48.8.0.1 of [Stacks, Tag 0A9S] for the second projection,
`Lq^*N ⊗ᴸ a(𝒪_Y) ⟶ a(N)`, as a morphism of functors of `N`. -/
def twistedComparison :
    quasiCoherentDerivedPullback' (pullback.snd f g) ⋙
        MonoidalCategory.tensorRight (twistedUnit f g) ⟶
      secondProjectionTwistedInverseImage f g :=
  (quasiCoherentDerivedAdjunction (pullback.snd f g)
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).comparisonNatTrans
    (secondProjectionTwistedAdjunction f g) (𝟙_ _) ≫
    Functor.whiskerRight (rightUnitorNatIso _).hom _

/-- **The map `γ`**: `Lq^*N ⊗ᴸ R𝓗om(K, a(𝒪_Y)) ⟶ R𝓗om(K, a(N))`, the map `α` of
[Stacks, Tag 0BYS] (in its adjunction-theoretic form, the strength of `- ⊗ᴸ K ⊣ R𝓗om(K, -)`)
followed by `R𝓗om(K, -)` of the map `β` of [Stacks, Tag 0A9S]. -/
def dualKernelPairing (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    (N : quasiCoherentDerivedCategory Y) :
    (((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N) ⊗ dualKernel f g K hK).obj ⟶
      (InternalHom.derivedSheafHom K.obj).obj
        ((secondProjectionTwistedInverseImage f g).obj N).obj :=
  letI := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  internalHomStrength (InternalHom.tensorRightSheafHomAdjunction K.obj)
      ((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N).obj (twistedUnit f g).obj ≫
    (InternalHom.derivedSheafHom K.obj).map ((twistedComparison f g).app N).hom

/-- **`γ` is natural in `N`.** -/
theorem dualKernelPairing_naturality (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    {N N' : quasiCoherentDerivedCategory Y} (n : N ⟶ N') :
    ((quasiCoherentDerivedPullback' (pullback.snd f g)).map n ▷ dualKernel f g K hK).hom ≫
        dualKernelPairing f g K hK N' =
      dualKernelPairing f g K hK N ≫
        (InternalHom.derivedSheafHom K.obj).map
          ((secondProjectionTwistedInverseImage f g).map n).hom := by
  let := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  have hβ := congrArg InducedCategory.Hom.hom ((twistedComparison f g).naturality n)
  change ((quasiCoherentDerivedPullback' (pullback.snd f g)).map n).hom ▷ (twistedUnit f g).obj ≫
      ((twistedComparison f g).app N').hom =
    ((twistedComparison f g).app N).hom ≫ ((secondProjectionTwistedInverseImage f g).map n).hom
    at hβ
  dsimp only [dualKernelPairing]
  show ((quasiCoherentDerivedPullback' (pullback.snd f g)).map n).hom ▷
      (InternalHom.derivedSheafHom K.obj).obj (twistedUnit f g).obj ≫ _ ≫ _ = _
  rw [← Category.assoc, internalHomStrength_naturality_left, Category.assoc, ← Functor.map_comp,
    hβ, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- `γ` is invertible when the strength `α` and the comparison `β` are. -/
private theorem isIso_dualKernelPairing_of_isIso_of_isIso
    (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    (N : quasiCoherentDerivedCategory Y)
    (h₁ : letI := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
      IsIso (internalHomStrength (InternalHom.tensorRightSheafHomAdjunction K.obj)
        ((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N).obj (twistedUnit f g).obj))
    (h₂ : IsIso ((twistedComparison f g).app N)) :
    IsIso (dualKernelPairing f g K hK N) := by
  have h₃ : IsIso ((twistedComparison f g).app N).hom := by
    show IsIso ((ObjectProperty.ι _).map ((twistedComparison f g).app N))
    infer_instance
  exact IsIso.comp_isIso' h₁ ((InternalHom.derivedSheafHom K.obj).map_isIso _)

/-- **`γ` is invertible on perfect objects**: the map `α` of [Stacks, Tag 0BYS] is invertible
when the tensor factor `Lq^*N` is perfect ([Stacks, Tag 0ATN], [Stacks, Tag 09UA]), and the map
`β` of [Stacks, Tag 0A9S] is invertible on perfect objects ([Stacks, Tag 0A9T]). -/
theorem isIso_dualKernelPairing_of_isPerfect (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    (N : quasiCoherentDerivedCategory Y)
    (hN : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) N.obj) :
    IsIso (dualKernelPairing f g K hK N) := by
  let := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  have : ExactPairing ((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N).obj
      (Stacks.SheafOfModules.derivedDual (pullback f g).sheaf
        ((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N).obj) :=
    exactPairingDerivedDualLocallySmall _
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
        (hX := Scheme.Modules.hasDerivedCategory (pullback f g))
        (hY := Scheme.Modules.hasDerivedCategory Y) (pullback.snd f g).toLRSHom.toShHom N.obj hN)
  have h₁ := isIso_internalHomStrength_of_dual (InternalHom.tensorRightSheafHomAdjunction K.obj)
    ((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N).obj
    (Stacks.SheafOfModules.derivedDual (pullback f g).sheaf
      ((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N).obj) (twistedUnit f g).obj
  let := exactPairingPerfectDual N hN
  have h₂ : IsIso ((twistedComparison f g).app N) := by
    have := (quasiCoherentDerivedAdjunction (pullback.snd f g)
      (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).isIso_comparisonMap_of_exactPairing
      (secondProjectionTwistedAdjunction f g) N (perfectDual N hN) (𝟙_ _)
    dsimp only [twistedComparison, NatTrans.comp_app, Functor.whiskerRight_app,
      Adjunction.comparisonNatTrans]
    infer_instance
  exact isIso_dualKernelPairing_of_isIso_of_isIso f g K hK N h₁ h₂

/-- **`γ` is invertible for a perfect kernel over a proper flat morphism of finite
presentation**: the map `α` of [Stacks, Tag 0BYS] is invertible when the source `K` of the
internal Hom is perfect ([Stacks, Tag 0ATN]), and the map `β` of [Stacks, Tag 0A9S] is invertible
for the second projection, which is proper, flat and of finite presentation as a base change of
`f` ([Stacks, Tag 0E4K]). -/
theorem isIso_dualKernelPairing_of_isPerfect_of_flat [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    (hKp : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (pullback f g).toRingedSpace) K.obj)
    (N : quasiCoherentDerivedCategory Y) :
    IsIso (dualKernelPairing f g K hK N) := by
  let := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  have : ExactPairing K.obj (Stacks.SheafOfModules.derivedDual (pullback f g).sheaf K.obj) :=
    exactPairingDerivedDualLocallySmall K.obj hKp
  have h₁ := isIso_internalHomStrength_of_source_dual (M := K.obj)
    (N := Stacks.SheafOfModules.derivedDual (pullback f g).sheaf K.obj)
    (InternalHom.tensorRightSheafHomAdjunction K.obj)
    ((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N).obj (twistedUnit f g).obj
  have : IsProper (pullback.snd f g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g) ‹IsProper f›
  have : Flat (pullback.snd f g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g) ‹Flat f›
  have : LocallyOfFinitePresentation (pullback.snd f g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g)
      ‹LocallyOfFinitePresentation f›
  have h₂ : IsIso ((twistedComparison f g).app N) := by
    have := isIso_comparisonMap_of_flat (pullback.snd f g) N (𝟙_ _)
    dsimp only [twistedComparison, NatTrans.comp_app, Functor.whiskerRight_app,
      Adjunction.comparisonNatTrans]
    infer_instance
  exact isIso_dualKernelPairing_of_isIso_of_isIso f g K hK N h₁ h₂

/-- The adjunction `Lp^* ⊣ Rp_*` on `D_QCoh` for the first projection `p`. -/
abbrev firstProjectionAdjunction :=
  quasiCoherentDerivedAdjunction (pullback.fst f g) (isQuasicoherent_homology_derivedPullback' _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)

/-- The first half of the comparison: `Hom(M, Rp_*(Lq^*N ⊗ᴸ K')) ≃ Hom(Lp^*M, Lq^*N ⊗ᴸ K')`,
by the adjunction `Lp^* ⊣ Rp_*` ([Stacks, Tag 079W]), read in `D(𝒪_{X ×_S Y})`. -/
def rightAdjointComparisonSource (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    (M : quasiCoherentDerivedCategory X) (N : quasiCoherentDerivedCategory Y) :
    (M ⟶ (fourierMukaiDualLocallySmall f g (dualKernel f g K hK)).obj N) ≃
      (((quasiCoherentDerivedPullback' (pullback.fst f g)).obj M).obj ⟶
        (((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N) ⊗ dualKernel f g K hK).obj) :=
  ((firstProjectionAdjunction f g).homEquiv _ _).symm.trans
    (ObjectProperty.fullyFaithfulι _).homEquiv

/-- The second half of the comparison:
`Hom(Lp^*M, R𝓗om(K, a(N))) ≃ Hom(Lp^*M ⊗ᴸ K, a(N)) ≃ Hom(Rq_*(Lp^*M ⊗ᴸ K), N)`, by the
tensor–internal-Hom adjunction ([Stacks, Tag 08J8]) and the adjunction `Rq_* ⊣ a`
([Stacks, Tag 0A9E]). -/
def rightAdjointComparisonTarget (K : quasiCoherentDerivedCategory (pullback f g))
    (M : quasiCoherentDerivedCategory X) (N : quasiCoherentDerivedCategory Y) :
    (((quasiCoherentDerivedPullback' (pullback.fst f g)).obj M).obj ⟶
        (InternalHom.derivedSheafHom K.obj).obj
          ((secondProjectionTwistedInverseImage f g).obj N).obj) ≃
      ((fourierMukaiLocallySmall f g K).obj M ⟶ N) :=
  letI := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  ((InternalHom.tensorRightSheafHomAdjunction K.obj).homEquiv _ _).symm.trans
    (((ObjectProperty.fullyFaithfulι _).homEquiv
        (X := (MonoidalCategory.tensorRight K).obj
          ((quasiCoherentDerivedPullback' (pullback.fst f g)).obj M))
        (Y := (secondProjectionTwistedInverseImage f g).obj N)).symm.trans
      ((secondProjectionTwistedAdjunction f g).homEquiv _ _).symm)

/-- **The comparison map of [Stacks, Tag 0FYW] at the locally small model**,
`Hom_X(M, Φ'(N)) ⟶ Hom_Y(Φ(M), N)`: the adjunction `Lp^* ⊣ Rp_*`, the map `γ`, the
tensor–internal-Hom adjunction and the adjunction `Rq_* ⊣ a`. -/
def rightAdjointComparison (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    (M : quasiCoherentDerivedCategory X) (N : quasiCoherentDerivedCategory Y)
    (v : M ⟶ (fourierMukaiDualLocallySmall f g (dualKernel f g K hK)).obj N) :
    (fourierMukaiLocallySmall f g K).obj M ⟶ N :=
  rightAdjointComparisonTarget f g K M N
    (rightAdjointComparisonSource f g K hK M N v ≫ dualKernelPairing f g K hK N)

/-- The second half of the comparison is natural in `M`. -/
theorem rightAdjointComparisonTarget_symm_naturality_left
    (K : quasiCoherentDerivedCategory (pullback f g))
    {M M' : quasiCoherentDerivedCategory X} (m : M' ⟶ M) (N : quasiCoherentDerivedCategory Y)
    (t : (fourierMukaiLocallySmall f g K).obj M ⟶ N) :
    (rightAdjointComparisonTarget f g K M' N).symm ((fourierMukaiLocallySmall f g K).map m ≫ t) =
      ((quasiCoherentDerivedPullback' (pullback.fst f g)).map m).hom ≫
        (rightAdjointComparisonTarget f g K M N).symm t := by
  let := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  have hw : (ObjectProperty.ι _).map
      ((MonoidalCategory.tensorRight K).map
        ((quasiCoherentDerivedPullback' (pullback.fst f g)).map m)) =
      (MonoidalCategory.tensorRight K.obj).map
        ((quasiCoherentDerivedPullback' (pullback.fst f g)).map m).hom :=
    whiskerRight_hom_quasiCoherentDerivedCategory (pullback f g) _ K
  dsimp only [rightAdjointComparisonTarget, Equiv.symm_trans_apply, Equiv.symm_symm]
  rw [show (fourierMukaiLocallySmall f g K).map m = (quasiCoherentDerivedPushforward
      (pullback.snd f g) (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
        ((MonoidalCategory.tensorRight K).map
          ((quasiCoherentDerivedPullback' (pullback.fst f g)).map m))
      from rfl, (secondProjectionTwistedAdjunction f g).homEquiv_naturality_left,
    Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_apply, Functor.map_comp,
    hw, Adjunction.homEquiv_naturality_left]

/-- **The comparison map is natural in `M`.** -/
theorem rightAdjointComparison_naturality_left
    (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    {M M' : quasiCoherentDerivedCategory X} (m : M' ⟶ M) (N : quasiCoherentDerivedCategory Y)
    (v : M ⟶ (fourierMukaiDualLocallySmall f g (dualKernel f g K hK)).obj N) :
    rightAdjointComparison f g K hK M' N (m ≫ v) =
      (fourierMukaiLocallySmall f g K).map m ≫ rightAdjointComparison f g K hK M N v := by
  let := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  have h₁ : rightAdjointComparisonSource f g K hK M' N (m ≫ v) =
      ((quasiCoherentDerivedPullback' (pullback.fst f g)).map m).hom ≫
        rightAdjointComparisonSource f g K hK M N v := by
    show (((firstProjectionAdjunction f g).homEquiv _ _).symm (m ≫ v)).hom = _
    rw [Adjunction.homEquiv_naturality_left_symm]
    rfl
  dsimp only [rightAdjointComparison]
  rw [h₁, Category.assoc]
  apply (rightAdjointComparisonTarget f g K M' N).symm.injective
  rw [Equiv.symm_apply_apply, rightAdjointComparisonTarget_symm_naturality_left,
    Equiv.symm_apply_apply]

/-- The second half of the comparison is natural in `N`. -/
theorem rightAdjointComparisonTarget_symm_naturality_right
    (K : quasiCoherentDerivedCategory (pullback f g)) (M : quasiCoherentDerivedCategory X)
    {N N' : quasiCoherentDerivedCategory Y} (n : N ⟶ N')
    (t : (fourierMukaiLocallySmall f g K).obj M ⟶ N) :
    (rightAdjointComparisonTarget f g K M N').symm (t ≫ n) =
      (rightAdjointComparisonTarget f g K M N).symm t ≫
        (InternalHom.derivedSheafHom K.obj).map
          ((secondProjectionTwistedInverseImage f g).map n).hom := by
  let := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  dsimp only [rightAdjointComparisonTarget, Equiv.symm_trans_apply, Equiv.symm_symm]
  rw [(secondProjectionTwistedAdjunction f g).homEquiv_naturality_right,
    Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_apply, Functor.map_comp,
    ObjectProperty.ι_map, Adjunction.homEquiv_naturality_right]
  rfl

/-- **The comparison map is natural in `N`.** -/
theorem rightAdjointComparison_naturality_right
    (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    (M : quasiCoherentDerivedCategory X) {N N' : quasiCoherentDerivedCategory Y} (n : N ⟶ N')
    (v : M ⟶ (fourierMukaiDualLocallySmall f g (dualKernel f g K hK)).obj N) :
    rightAdjointComparison f g K hK M N'
        (v ≫ (fourierMukaiDualLocallySmall f g (dualKernel f g K hK)).map n) =
      rightAdjointComparison f g K hK M N v ≫ n := by
  let := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  have h₁ : rightAdjointComparisonSource f g K hK M N'
        (v ≫ (fourierMukaiDualLocallySmall f g (dualKernel f g K hK)).map n) =
      rightAdjointComparisonSource f g K hK M N v ≫
        ((quasiCoherentDerivedPullback' (pullback.snd f g)).map n ▷ dualKernel f g K hK).hom := by
    show (((firstProjectionAdjunction f g).homEquiv _ _).symm
      (v ≫ (quasiCoherentDerivedPushforward (pullback.fst f g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
          ((MonoidalCategory.tensorRight (dualKernel f g K hK)).map
            ((quasiCoherentDerivedPullback' (pullback.snd f g)).map n)))).hom = _
    rw [Adjunction.homEquiv_naturality_right_symm]
    rfl
  dsimp only [rightAdjointComparison]
  rw [h₁, Category.assoc, dualKernelPairing_naturality, ← Category.assoc]
  apply (rightAdjointComparisonTarget f g K M N').symm.injective
  rw [Equiv.symm_apply_apply, rightAdjointComparisonTarget_symm_naturality_right,
    Equiv.symm_apply_apply]

/-- The comparison map is bijective as soon as `γ` is invertible. -/
theorem bijective_rightAdjointComparison_of_isIso
    (K : quasiCoherentDerivedCategory (pullback f g))
    (hK : RingedSpace.IsPseudoCoherent (X := (pullback f g).toRingedSpace) K.obj)
    (M : quasiCoherentDerivedCategory X) (N : quasiCoherentDerivedCategory Y)
    [IsIso (dualKernelPairing f g K hK N)] :
    Function.Bijective (rightAdjointComparison f g K hK M N) := by
  have hγ : Function.Bijective (fun x :
      ((quasiCoherentDerivedPullback' (pullback.fst f g)).obj M).obj ⟶
      (((quasiCoherentDerivedPullback' (pullback.snd f g)).obj N) ⊗ dualKernel f g K hK).obj =>
        x ≫ dualKernelPairing f g K hK N) :=
    ⟨fun _ _ h => (cancel_mono _).1 h,
      fun z => ⟨z ≫ inv (dualKernelPairing f g K hK N), by simp⟩⟩
  exact (rightAdjointComparisonTarget f g K M N).bijective.comp
    (hγ.comp (rightAdjointComparisonSource f g K hK M N).bijective)

end RightAdjoint

end Stacks.Duality

end
