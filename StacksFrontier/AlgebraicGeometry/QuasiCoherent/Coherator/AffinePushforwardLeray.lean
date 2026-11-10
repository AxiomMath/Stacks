module

public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardBounds
public import StacksFrontier.AlgebraicGeometry.RelativeLeray.Basic
import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison

/-!
# Leray acyclicity for the unbounded derived direct image

Let `f : X ⟶ S` be a morphism of ringed spaces and let `ℱ^•` be a complex of `𝒪_X`-modules each
of which is right acyclic for `f_*`. If `ℱ^•` is *bounded below*, then `f_*ℱ^•` already computes
`Rf_*ℱ^•`: the canonical comparison `f_*ℱ^• ⟶ Rf_*ℱ^•` is an isomorphism of `D(𝒪_S)`. That is
Leray's acyclicity lemma, [Stacks, Tag 015E], for the *unbounded* derived direct image.

For an *affine* morphism of schemes the boundedness may be dropped: a complex of quasi-coherent
`𝒪_X`-modules has `f_*`-acyclic terms by [Stacks, Tag 01XC], and then `f_*ℱ^• ⟶ Rf_*ℱ^•` is an
isomorphism with no boundedness hypothesis at all. That is [Stacks, Tag 0G9N] for an affine
morphism.

The reduction to the bounded below case is the one the source gives. Fix a degree `q` and cut
`ℱ^•` by the stupid truncation `σ_{≥ q-1}ℱ^• ⟶ ℱ^•`, which is an isomorphism in degrees `≥ q-1`
and zero below. The naturality square of the comparison at that map has

* its top edge an isomorphism, by the bounded below case — `σ_{≥ q-1}ℱ^•` is bounded below and its
  terms are terms of `ℱ^•` or zero, hence `f_*`-acyclic;
* its left edge an isomorphism on `H^q`, because `f_*` of a map which is an isomorphism in degrees
  `≥ q-1` is an isomorphism on `H^q`;
* its right edge an isomorphism on `H^q`, because the stupid truncation triangle is degreewise
  split, hence distinguished in `K(𝒪_X)`, and its third vertex `σ_{≤ q-2}ℱ^•` has
  `Rf_*`-image in degrees `≤ q - 2` by [Stacks, Tag 08D5] part (2) for an affine morphism, which
  kills `H^q` and `H^{q-1}` there.

So the bottom edge is an isomorphism on `H^q`, for every `q`, and a morphism of `D(𝒪_S)` which is
an isomorphism on every cohomology sheaf is an isomorphism.

## Main results

* `RingedSpaceModuleAdjunction.hasRightDerivedFunctorPlus_modulePushforward` — direct image of
  modules on a ringed space has a right derived functor on the bounded below homotopy category, so
  that `CategoryTheory.Functor.rightAcyclic` is available for it.
* `AlgebraicGeometry.rightAcyclic_modulePushforward_of_injective` and
  `AlgebraicGeometry.exists_mono_rightAcyclic_modulePushforward` — the `f_*`-acyclic modules form
  a class adapted to `f_*` in the sense of [Stacks, Tag 05T8].
* `AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_plus_of_rightAcyclic` — **Leray's
  acyclicity lemma for the unbounded derived direct image**, for a bounded below complex with
  `f_*`-acyclic terms.
* `AlgebraicGeometry.rightAcyclic_modulePushforward_of_isQuasicoherent` — a quasi-coherent module
  is `f_*`-acyclic when `f` is an affine morphism of schemes, which is [Stacks, Tag 01XC] read
  through the acyclicity criterion.
* `AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_isAffineHom` — **[Stacks, Tag 0G9N] for
  an affine morphism**: a complex of quasi-coherent modules computes its unbounded derived direct
  image along an affine morphism.
* `AlgebraicGeometry.containsZero_rightAcyclic_modulePushforward` — a zero module is acyclic for
  direct image, which is what carries acyclicity to the terms of a stupid truncation.
* `AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_rightAcyclic_of_quasiCompact` —
  **[Stacks, Tag 0G9N] for a quasi-compact quasi-separated morphism with quasi-compact target**,
  the same argument with the cut moved down by the integer of [Stacks, Tag 01XJ].

## Implementation notes

**No `@[stacks 0G9N]` attribute is placed.** Tag 0G9N is stated for a quasi-compact
quasi-separated morphism and an arbitrary complex of quasi-coherent modules with `f_*`-acyclic
terms, with *no hypothesis on the target*. Two cases of it are proved below: the *affine*
morphism, where the acyclicity hypothesis is automatic and the target is unconstrained, and the
quasi-compact quasi-separated morphism with *quasi-compact* target. The step that forces the
extra hypothesis in the second is the vanishing of `H^q` and `H^{q-1}` on
`Rf_*(σ_{≤ q-2-N}ℱ^•)`, which rests on [Stacks, Tag 08D5] part (2): the uniform integer
`N = N(X, Y, f)` of [Stacks, Tag 01XJ] exists only for a quasi-compact target. What is missing
for the tag is therefore the localization of the conclusion on the target — the statement is
local on `Y`, but transporting the unit of the derived direct image along restriction to an open
of `Y` is not available here. Nor is
`@[stacks 015E]` placed on the bounded below case: Leray's acyclicity lemma is already carried by
`CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`, whose conclusion is
about the *bounded below* derived functor, and the statement below is its transfer to the
unbounded one — a different assertion, obtained from the K-injective criterion of
[Stacks, Tag 070K] rather than from that lemma.

**Two instances are declared globally.** That direct image of modules on a ringed space has a
bounded below right derived functor is what makes `CategoryTheory.Functor.rightAcyclic` even
*state*, so it has to be reachable from every consumer of the results below. Left exactness is
needed only in the proofs here, but the same statement appears as a `local instance` in
`StacksFrontier/AlgebraicGeometry/RelativeLeray/Basic.lean` and in
`StacksFrontier/AlgebraicGeometry/RelativeLeray/Leray.lean`, where it is unreachable from outside;
this is the public form of it, and neither declaration can fire except at `modulePushforward`.

**The stupid truncation triangle is built here rather than imported.** `HomologicalComplex`'s
stupid truncations give a short complex `σ_{≥ n+1}K ⟶ K ⟶ σ_{≤ n}K` which is split in every
degree — above the cut the first map is invertible and the third object vanishes, below the cut
the other way round — and `CochainComplex.trianglehOfDegreewiseSplit` turns a degreewise split
short complex into a distinguished triangle of `K(𝒪_X)`. The four declarations assembling that
are `private`: they are a standard construction with no geometry in them, and nothing outside
this file needs them.

**Two transports of the localization.** The unit is a transformation out of the homotopy
category, so its source edge is `Qh` of a homotopy class, while cohomology of a map of complexes
is read through `DerivedCategory.Q`; and `DerivedCategory.Q` is not reducible, so the two are
compared by `DerivedCategory.quotientCompQhIso_hom_naturality` rather than by unfolding. The two
private lemmas doing it are `mapHomotopyCategory_map_quotient_map`, which is an equation of terms
that happen to be identical, and `isIso_homologyFunctor_map_Qh_quotient_map_iff`.

## References

* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit isIso_derivedPushforwardUnit_app_of_isKInjective)

universe u

namespace RingedSpaceModuleAdjunction

/-- **Direct image of modules on a ringed space has a bounded below right derived functor.** Every
functor out of `K⁺(𝒪_X)` does, `𝒪_X`-modules having enough injectives. This is what makes
`CategoryTheory.Functor.rightAcyclic` available for `f_*`. -/
public instance hasRightDerivedFunctorPlus_modulePushforward
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) [HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (structureSheafRing Y))] :
    ((modulePushforward f).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) := by
  have := (HomotopyCategory.Plus.localizerMorphism_derives
    ((modulePushforward f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).hasPointwiseRightDerivedFunctor
  exact Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

end RingedSpaceModuleAdjunction

namespace AlgebraicGeometry

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnboundedHigherDirectImage.isGrothendieckAbelian_moduleSheaves

/-! ### The class of modules acyclic for direct image -/

/-- **An injective module is acyclic for direct image.** The complex `J[0]` has injective terms,
and the structure map of a right derived functor on `K⁺` is invertible at such a complex. -/
public theorem rightAcyclic_modulePushforward_of_injective {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (J : SheafOfModules.{u} (structureSheafRing X)) [Injective J] :
    (modulePushforward f).rightAcyclic J := by
  have hinj : ∀ n : ℤ, Injective
      (((HomotopyCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).obj J).obj.as.X n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · exact Injective.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) J).symm ‹_›
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 J n hn).injective
  dsimp only [Functor.rightAcyclic]
  infer_instance

/-- **Every module is a subobject of one acyclic for direct image**: embed it into an injective.
This is the first hypothesis of [Stacks, Tag 05T8] for the class of `f_*`-acyclic modules. -/
public theorem exists_mono_rightAcyclic_modulePushforward {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    ∃ (Z : SheafOfModules.{u} (structureSheafRing X)) (_ : (modulePushforward f).rightAcyclic Z)
      (j : M ⟶ Z), Mono j :=
  ⟨Injective.under M, rightAcyclic_modulePushforward_of_injective f _, Injective.ι M,
    inferInstance⟩

/-! ### Leray's acyclicity lemma for the unbounded derived direct image -/

/-- **Leray's acyclicity lemma for the unbounded derived direct image.** Let `f : X ⟶ Y` be a
morphism of ringed spaces and let `K` be a *bounded below* complex of `𝒪_X`-modules each of whose
terms is right acyclic for `f_*`. Then the canonical comparison `f_*K ⟶ Rf_*K` is an isomorphism
of `D(𝒪_Y)`.

By the K-injective criterion of [Stacks, Tag 070K] in the form
`Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff`, it suffices that `f_*`
carry one quasi-isomorphism `s : K ⟶ L` into a K-injective complex to a quasi-isomorphism. Take
`L` to be a bounded below complex of injective modules, which is K-injective; then
[Stacks, Tag 05T8] applied to the class of `f_*`-acyclic modules — whose two hypotheses are
`AlgebraicGeometry.exists_mono_rightAcyclic_modulePushforward` and the closure property of
[Stacks, Tag 015D] — says exactly that `f_*s` is a quasi-isomorphism. -/
public theorem isIso_derivedPushforwardUnit_app_of_plus_of_rightAcyclic
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hK : CochainComplex.plus (SheafOfModules.{u} (structureSheafRing X)) K)
    (hac : ∀ n : ℤ, (modulePushforward f).rightAcyclic (K.X n)) :
    IsIso ((derivedPushforwardUnit f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj K)) := by
  obtain ⟨n, hn⟩ := hK
  obtain ⟨L, s, hs, hLinj, hLn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  have hs' := hs
  have hLK : L.IsKInjective := CochainComplex.isKInjective_of_injective L n
  have hres : ∀ C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (h : C ⟶ I),
        I.IsKInjective ∧ QuasiIso h := fun C =>
    ⟨(Stacks.Injectives.kInjectiveResolutionFunctor _).obj C,
      (Stacks.Injectives.kInjectiveResolutionInclusion _).app C, inferInstance, inferInstance⟩
  rw [Stacks.SmallDerivedCategory.isIso_rightDerivedUnit_app_quotient_iff hres _ _ _ s hLK hs]
  refine ((DerivedCategory.isIso_Qh_map_iff _).trans
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).trans
      (HomologicalComplex.mem_quasiIso_iff _))).2 ?_
  exact Functor.RightAcyclicCriterion.map_quasiIso (modulePushforward f)
    ((modulePushforward f).rightAcyclic)
    (exists_mono_rightAcyclic_modulePushforward f)
    (fun S hS h₁ h₂ =>
      (Functor.rightAcyclic_and_shortExact_map_of_shortExact (modulePushforward f) S hS).2.1 h₁ h₂)
    s ⟨n, hn⟩ ⟨n, hLn⟩ hac
    (fun m => have := hLinj m; rightAcyclic_modulePushforward_of_injective f (L.X m))

/-! ### Quasi-coherent modules are acyclic for an affine morphism -/

/-- **A quasi-coherent module is acyclic for direct image along an affine morphism.** Direct image
is left exact, so acyclicity is the vanishing of `R^p f_*` in positive degrees, which is
[Stacks, Tag 01XC]. -/
public theorem rightAcyclic_modulePushforward_of_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hM : M.IsQuasicoherent) :
    (modulePushforward f.toLRSHom.toShHom).rightAcyclic M := by
  refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (modulePushforward f.toLRSHom.toShHom) M).2
    (Stacks.RelativeLeray.preservesFiniteLimits_modulePushforward
      f.toLRSHom.toShHom)).2 fun i hi => ?_
  exact @Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom
    X Y f M ‹_› hM i hi

/-! ### The stupid truncation triangle -/

section StupidTrunc

variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]

/-- The short complex `σ_{≥ n+1}K ⟶ K ⟶ σ_{≤ n}K` of stupid truncations of a cochain complex. -/
private def stupidTruncShortComplex (K : CochainComplex A ℤ) (n : ℤ) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE (n + 1)))
    (K.πStupidTrunc (ComplexShape.embeddingUpIntLE n)) (by
      ext i
      simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
      by_cases hi : ∃ j : ℕ, (ComplexShape.embeddingUpIntGE (n + 1)).f j = i
      · obtain ⟨j, hj⟩ := hi
        refine (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE n) i ?_).eq_of_tgt _ _
        rw [ComplexShape.notMem_range_embeddingUpIntLE_iff, ← hj]
        change n < n + 1 + (j : ℤ)
        omega
      · exact (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (n + 1)) i
          (by simpa using hi)).eq_of_src _ _)

/-- The stupid truncation short complex is split in every degree: above the cut the first map is
invertible and the third object vanishes, below the cut the other way round. -/
private def stupidTruncSplitting (K : CochainComplex A ℤ) (n i : ℤ) :
    ((stupidTruncShortComplex K n).map (HomologicalComplex.eval A _ i)).Splitting := by
  by_cases h : n < i
  · exact ShortComplex.Splitting.ofIsIsoOfIsZero _
      (K.isIso_ιStupidTrunc_f (ComplexShape.embeddingUpIntGE (n + 1))
        (i := (i - (n + 1)).toNat) (by change n + 1 + ((i - (n + 1)).toNat : ℤ) = i; omega))
      (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE n) i
        (by rw [ComplexShape.notMem_range_embeddingUpIntLE_iff]; omega))
  · exact ShortComplex.Splitting.ofIsZeroOfIsIso _
      (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (n + 1)) i
        (by rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]; omega))
      (K.isIso_πStupidTrunc_f (ComplexShape.embeddingUpIntLE n)
        (i := (n - i).toNat) (by change n - ((n - i).toNat : ℤ) = i; omega))

/-- Above the cut the inclusion of a stupid truncation from below is invertible in each degree. -/
private alias isIso_ιStupidTrunc_f := Stacks.DerivedAcyclic.isIso_ιStupidTrunc_f

/-- A stupid truncation from below is bounded below. -/
private alias plus_stupidTruncGE := Stacks.DerivedAcyclic.plus_stupidTruncGE

variable [HasBinaryBiproducts A]

/-- The distinguished triangle `σ_{≥ n+1}K ⟶ K ⟶ σ_{≤ n}K ⟶ (σ_{≥ n+1}K)[1]` of `K(A)`. -/
private def stupidTruncTriangleh (K : CochainComplex A ℤ) (n : ℤ) :
    Triangle (HomotopyCategory A (ComplexShape.up ℤ)) :=
  CochainComplex.trianglehOfDegreewiseSplit
    (stupidTruncShortComplex K n) (stupidTruncSplitting K n)

private lemma stupidTruncTriangleh_distinguished (K : CochainComplex A ℤ) (n : ℤ) :
    stupidTruncTriangleh K n ∈ distTriang (HomotopyCategory A (ComplexShape.up ℤ)) :=
  (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2
    ⟨_, _, ⟨Iso.refl _⟩⟩

end StupidTrunc

/-- The object of the derived category represented by a stupid truncation from above lives in
degrees `≤ a`. -/
private alias isLE_Q_stupidTruncLE := Stacks.DerivedAcyclic.isLE_stupidTruncLE

/-- The terms of a stupid truncation from above satisfy any isomorphism-closed property containing
zero that the terms of the complex satisfy. -/
private lemma prop_stupidTruncLE_X {A : Type*} [Category* A] [Abelian A] (P : ObjectProperty A)
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero] (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, P (K.X n)) (a i : ℤ) :
    P ((K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X i) := by
  by_cases hi : i ≤ a
  · have heq : (ComplexShape.embeddingUpIntLE a).f (a - i).toNat = i := by
      change a - ((a - i).toNat : ℤ) = i
      omega
    exact P.prop_of_iso (K.stupidTruncXIso (ComplexShape.embeddingUpIntLE a) heq).symm (hK i)
  · exact P.prop_of_isZero (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE a) i
      (by rw [ComplexShape.notMem_range_embeddingUpIntLE_iff]; omega))

/-- The terms of a stupid truncation from below satisfy any isomorphism-closed property containing
zero that the terms of the complex satisfy. -/
private lemma prop_stupidTruncGE_X {A : Type*} [Category* A] [Abelian A] (P : ObjectProperty A)
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero] (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, P (K.X n)) (a i : ℤ) :
    P ((K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X i) := by
  by_cases hi : ∃ j : ℕ, (ComplexShape.embeddingUpIntGE a).f j = i
  · obtain ⟨j, hj⟩ := hi
    exact P.prop_of_iso (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE a) hj).symm (hK i)
  · exact P.prop_of_isZero (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE a) i
      (by simpa using hi))

/-- The homology of a complex whose terms satisfy a weak Serre class property satisfies it too. -/
private lemma prop_homology_of_prop_X {A : Type*} [Category* A] [Abelian A] (P : ObjectProperty A)
    [P.IsWeakSerreClass] (K : CochainComplex A ℤ) (hK : ∀ n : ℤ, P (K.X n)) (i : ℤ) :
    P (K.homology i) :=
  P.prop_of_isColimit_cokernelCofork
    (K.homologyIsCokernel ((ComplexShape.up ℤ).prev i) i rfl) (hK _)
    (P.prop_of_isLimit_kernelFork
      (K.cyclesIsKernel i ((ComplexShape.up ℤ).next i) rfl) (hK i) (hK _))

/-- The degree-`q` homology of the image in `D(A)` of a map of cochain complexes is invertible
exactly when the degree-`q` homology of the map itself is. -/
private lemma isIso_homologyFunctor_map_Q_map_iff {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {K L : CochainComplex A ℤ} (h : K ⟶ L) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor A q).map (DerivedCategory.Q.map h)) ↔
      IsIso (HomologicalComplex.homologyMap h q) := by
  have hnat := (DerivedCategory.homologyFunctorFactors A q).hom.naturality h
  dsimp only [Functor.comp_map] at hnat
  rw [← isIso_comp_right_iff _ ((DerivedCategory.homologyFunctorFactors A q).hom.app L),
    hnat, isIso_comp_left_iff]
  rfl

/-- The image of a stupid truncation from below under an additive functor is invertible on `H^q`
above the cut: it is invertible in degrees `≥ a`, so in particular in degrees `q - 1`, `q` and
`q + 1`. -/
private lemma isIso_homologyMap_map_ιStupidTrunc {A B : Type*} [Category* A] [Abelian A]
    [Category* B] [Abelian B] (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) (a q : ℤ)
    (ha : a < q) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a))) q) := by
  let g := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a))
  change IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℤ) q).map g))
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · change Epi (g.f ((ComplexShape.up ℤ).prev q))
    have : IsIso (g.f ((ComplexShape.up ℤ).prev q)) := by
      rw [CochainComplex.prev]
      dsimp only [g, Functor.mapHomologicalComplex_map_f]
      have := isIso_ιStupidTrunc_f K a (q - 1) (by omega)
      infer_instance
    exact IsIso.epi_of_iso _
  · change IsIso (g.f q)
    dsimp only [g, Functor.mapHomologicalComplex_map_f]
    have := isIso_ιStupidTrunc_f K a q (by omega)
    infer_instance
  · change Mono (g.f ((ComplexShape.up ℤ).next q))
    have : IsIso (g.f ((ComplexShape.up ℤ).next q)) := by
      rw [CochainComplex.next]
      dsimp only [g, Functor.mapHomologicalComplex_map_f]
      have := isIso_ιStupidTrunc_f K a (q + 1) (by omega)
      infer_instance
    exact IsIso.mono_of_iso _

/-- The functor induced on homotopy categories by an additive functor, evaluated at the image of
a map of cochain complexes, is the image of the degreewise application of the functor. Both sides
unfold to the same term; the equation is stated so that it can be rewritten with. -/
private lemma mapHomotopyCategory_map_quotient_map {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex A ℤ} (h : K ⟶ L) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map h) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map h) :=
  rfl

/-- The degree-`q` homology of the image in `D(A)` of the homotopy class of a map of cochain
complexes is invertible exactly when the degree-`q` homology of the map itself is. -/
private lemma isIso_homologyFunctor_map_Qh_quotient_map_iff {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {K L : CochainComplex A ℤ} (h : K ⟶ L) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor A q).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map h))) ↔
      IsIso (HomologicalComplex.homologyMap h q) := by
  rw [← isIso_homologyFunctor_map_Q_map_iff h q,
    ← isIso_comp_right_iff _ ((DerivedCategory.homologyFunctor A q).map
      ((DerivedCategory.quotientCompQhIso A).hom.app L)),
    ← Functor.map_comp, DerivedCategory.quotientCompQhIso_hom_naturality,
    Functor.map_comp, isIso_comp_left_iff]

/-! ### Tag 0G9N for an affine morphism -/

/-- The cut argument shared by the two forms of [Stacks, Tag 0G9N]: if the comparison is invertible
at the stupid truncation `σ_{≥ c+1}K`, and `Rf_*` of a complex with quasi-coherent cohomology in
degrees `≤ c` lives in degrees `≤ q - 2`, then it is invertible on `H^q` at `K`. -/
private theorem isIso_homologyFunctor_map_derivedPushforwardUnit_app {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) (q c : ℤ) (hc : c + 1 < q)
    (hTop : IsIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)).obj (K.stupidTrunc (ComplexShape.embeddingUpIntGE (c + 1))))))
    (hLE : ∀ E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)),
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent) →
      E.IsLE c → ((derivedPushforward f.toLRSHom.toShHom).obj E).IsLE (q - 2)) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).map
      ((derivedPushforwardUnit f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)).obj K))) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X.toRingedSpace)
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f.toLRSHom.toShHom).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated
      (modulePushforward f.toLRSHom.toShHom) _ (derivedPushforwardUnit f.toLRSHom.toShHom)
  let PX := SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)
  have hP : PX.ContainsZero := containsZero_isQuasicoherent X
  have hW : PX.IsWeakSerreClass :=
    Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass X
  let α := derivedPushforwardUnit f.toLRSHom.toShHom
  -- The stupid truncation `σ_{≥ c+1}K ⟶ K`, and the cut `σ_{≤ c}K`.
  let ι := K.ιStupidTrunc (ComplexShape.embeddingUpIntGE (c + 1))
  let KGE := K.stupidTrunc (ComplexShape.embeddingUpIntGE (c + 1))
  let KLE := K.stupidTrunc (ComplexShape.embeddingUpIntLE c)
  -- The right edge: the stupid truncation triangle, and the upper bound on the cut.
  have hRight : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).map
      ((DerivedCategory.Qh ⋙ derivedPushforward f.toLRSHom.toShHom).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ι))) := by
    let T := (DerivedCategory.Qh ⋙ derivedPushforward f.toLRSHom.toShHom).mapTriangle.obj
      (stupidTruncTriangleh K c)
    have hT : T ∈ distTriang
        (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :=
      (DerivedCategory.Qh ⋙ derivedPushforward f.toLRSHom.toShHom).map_distinguished _
        (stupidTruncTriangleh_distinguished K c)
    have hcohLE : ∀ j : ℤ, PX ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
        (DerivedCategory.Q.obj KLE)) := fun j =>
      PX.prop_of_iso ((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).app KLE).symm
        (@prop_homology_of_prop_X _ _ _ PX hW KLE
          (@prop_stupidTruncLE_X _ _ _ PX _ hP K hqc c) j)
    have hcut : T.obj₃.IsLE (q - 2) := by
      have := hLE _ hcohLE (isLE_Q_stupidTruncLE K c)
      exact DerivedCategory.TStructure.t.isLE_of_iso
        (((derivedPushforward f.toLRSHom.toShHom).mapIso
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))).app KLE)).symm) (q - 2)
    have hz : IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).obj T.obj₃) :=
      T.obj₃.isZero_of_isLE (q - 2) q (by omega)
    have hz' : IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (q - 1)).obj T.obj₃) :=
      T.obj₃.isZero_of_isLE (q - 2) (q - 1) (by omega)
    have hepi : Epi ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).map T.mor₁) :=
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u}
          (structureSheafRing Y.toRingedSpace)) 0).homologySequence_epi_shift_map_mor₁_iff
        T hT q).2 (hz.eq_of_tgt _ _)
    have hmono : Mono ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).map T.mor₁) :=
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u}
          (structureSheafRing Y.toRingedSpace)) 0).homologySequence_mono_shift_map_mor₁_iff
        T hT (q - 1) q (by omega)).2 (hz'.eq_of_src _ _)
    exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).map T.mor₁)
  -- The left edge: direct image of a map invertible above the cut.
  have hLeft : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory
        f.toLRSHom.toShHom).map
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ)).map ι))) := by
    change IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).map
      (DerivedCategory.Qh.map
        (((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)).map ι))))
    rw [mapHomotopyCategory_map_quotient_map]
    exact (isIso_homologyFunctor_map_Qh_quotient_map_iff
      (((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ι) q).2
      (isIso_homologyMap_map_ιStupidTrunc (modulePushforward f.toLRSHom.toShHom) K
        (c + 1) q (by omega))
  -- Assemble the naturality square.
  have hnat := α.naturality ((HomotopyCategory.quotient
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)).map ι)
  have hcomp : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).map
      (α.app ((HomotopyCategory.quotient
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)).obj KGE) ≫
        (DerivedCategory.Qh ⋙ derivedPushforward f.toLRSHom.toShHom).map
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ)).map ι))) := by
    rw [Functor.map_comp]
    have h₁ : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) q).map
        (α.app ((HomotopyCategory.quotient
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)).obj KGE))) :=
      have := hTop
      inferInstance
    exact IsIso.comp_isIso' h₁ hRight
  rw [← hnat, Functor.map_comp] at hcomp
  have := hLeft
  exact (isIso_comp_left_iff _ _).1 hcomp


/-- **[Stacks, Tag 0G9N] for an affine morphism.** Let `f : X ⟶ Y` be an affine morphism of
schemes and let `K` be a complex of quasi-coherent `𝒪_X`-modules — no boundedness is assumed.
Then `f_*K` represents `Rf_*K` in `D(𝒪_Y)`: the canonical comparison is an isomorphism.

See the module documentation for the shape of the argument. -/
public theorem isIso_derivedPushforwardUnit_app_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    IsIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)).obj K)) := by
  let PX := SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)
  have hP : PX.ContainsZero := containsZero_isQuasicoherent X
  rw [DerivedCategory.isIso_iff]
  intro q
  refine isIso_homologyFunctor_map_derivedPushforwardUnit_app f K hqc q (q - 2) (by omega) ?_
    fun E hE hb => isLE_derivedPushforward_obj_of_isAffineHom f E hE (q - 2) hb
  exact isIso_derivedPushforwardUnit_app_of_plus_of_rightAcyclic f.toLRSHom.toShHom _
    (plus_stupidTruncGE K (q - 2 + 1)) fun n =>
      rightAcyclic_modulePushforward_of_isQuasicoherent f _
        (@prop_stupidTruncGE_X _ _ _ PX _ hP K hqc (q - 2 + 1) n)

/-- **A zero module is acyclic for direct image.** A zero object is injective, and an injective
module is acyclic for direct image by
`AlgebraicGeometry.rightAcyclic_modulePushforward_of_injective`.

Together with `CategoryTheory.Functor.rightAcyclic_isClosedUnderIsomorphisms` this is what carries
acyclicity to the terms of a stupid truncation, which are the terms of the complex above the cut
and zero below it. -/
public theorem containsZero_rightAcyclic_modulePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((modulePushforward f.toLRSHom.toShHom).rightAcyclic).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ :=
      Limits.HasZeroObject.zero (C := SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    have _ : Injective Z := hZ.injective
    exact ⟨Z, hZ, rightAcyclic_modulePushforward_of_injective f.toLRSHom.toShHom Z⟩

/-! ### Tag 0G9N for a quasi-compact quasi-separated morphism -/

/-- **[Stacks, Tag 0G9N] for a quasi-compact quasi-separated morphism with quasi-compact
target.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y`
quasi-compact, and let `K` be a complex of quasi-coherent `𝒪_X`-modules each of which is right
acyclic for `f_*` — no boundedness is assumed. Then `f_*K` represents `Rf_*K` in `D(𝒪_Y)`.

This is the argument of `AlgebraicGeometry.isIso_derivedPushforwardUnit_app_of_isAffineHom` with
the cut moved down by the integer `N = N(X, Y, f)` of [Stacks, Tag 01XJ]. Fix a degree `q` and cut
`K` by the stupid truncation `σ_{≥ q-1-N}K ⟶ K`. The top edge of the naturality square of the
comparison at that map is an isomorphism by the bounded below case, its left edge is an
isomorphism on `H ᵠ` because `f_*` of a map invertible in degrees `≥ q-1-N` is, and its right edge
is an isomorphism on `H ᵠ` because the third vertex `σ_{≤ q-2-N}K` of the degreewise split stupid
truncation triangle has `Rf_*`-image in degrees `≤ q - 2` by
`AlgebraicGeometry.exists_isLE_derivedPushforward_obj`, which is [Stacks, Tag 08D5] part (2).

For an affine morphism the acyclicity hypothesis is automatic, by
`AlgebraicGeometry.rightAcyclic_modulePushforward_of_isQuasicoherent`, and no hypothesis on the
target is needed; that is the statement above. -/
public theorem isIso_derivedPushforwardUnit_app_of_rightAcyclic_of_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent)
    (hac : ∀ n : ℤ, (modulePushforward f.toLRSHom.toShHom).rightAcyclic (K.X n)) :
    IsIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)).obj K)) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj f
  have hPac : ((modulePushforward f.toLRSHom.toShHom).rightAcyclic).ContainsZero :=
    containsZero_rightAcyclic_modulePushforward f
  rw [DerivedCategory.isIso_iff]
  intro q
  refine isIso_homologyFunctor_map_derivedPushforwardUnit_app f K hqc q (q - 2 - N) (by omega) ?_
    fun E hE hb => ?_
  · exact isIso_derivedPushforwardUnit_app_of_plus_of_rightAcyclic f.toLRSHom.toShHom _
      (plus_stupidTruncGE K _) fun n => prop_stupidTruncGE_X _ K hac _ n
  · have := hN E hE _ hb
    rwa [show q - 2 - N + N = q - 2 by omega] at this

end AlgebraicGeometry

end
