module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
public import StacksFrontier.Homology.Tor.Presentation
public import Mathlib.AlgebraicGeometry.ResidueField
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreCriterion

/-!
# Derived fibres of an object of finite Tor dimension over the base, and Stacks 0GEH

Let `f : X ⟶ S` be a morphism of schemes and let `E` be an object of `D(𝒪_X)` of Tor amplitude
in `[a, b]` over `S`, in the stalkwise sense of Stacks 0C0V. Then the cohomology of `E` is
concentrated in `[a, b]`, and so is the cohomology of the derived pullback of `E` along any base
change of `f`. Taking the base change to be `Spec κ(s) ⟶ S` gives the derived fibre
`L(X_s ⟶ X)^*E`, which is therefore bounded below, hence locally bounded below: this is the
second clause of condition (2) of Stacks 0GEH.

Flatness of `f` is what makes the fibre square Tor independent, so that Tor amplitude over the
base transports across it by Stacks 0C0V; the argument needs nothing else of the fibre.

The fibrewise criterion, Stacks 0GEH, follows: let `f : X ⟶ S` be flat and locally of finite
presentation and let `E` be a pseudo-coherent object of `D(𝒪_X)`. Then `E` is `S`-perfect if and
only if `E` is locally bounded below and for every point `s` of `S` the derived fibre
`L(X_s ⟶ X)^*E` of `D(𝒪_{X_s})` is locally bounded below.

## Main results

* `AlgebraicGeometry.torIndependent_of_flat`: a flat morphism is Tor independent from every
  other morphism to the same base.
* `AlgebraicGeometry.isZero_of_forall_modulesStalk`: an `𝒪_X`-module with vanishing stalks over
  the local rings is zero.
* `AlgebraicGeometry.isZero_homology_of_hasTorAmplitudeOver`: Tor amplitude in `[a, b]` over the
  base bounds the cohomology of the object itself to `[a, b]`.
* `AlgebraicGeometry.isLocallyBoundedBelow_derivedPullback_of_isPullback`: the derived pullback
  of such an object along a base change of a flat morphism is locally bounded below.
* `AlgebraicGeometry.isLocallyBoundedBelow_derivedPullback_fibre_of_hasTorAmplitudeOver`: the
  same at the fibre over a point of `S`.
* `AffinePerfectDescent.isPerfectRelativeTo_tildeObj_iff_isLocallyBoundedBelow_and_fibres`:
  Stacks 0GEH for a morphism of affine schemes and a sheafified complex.
* `AlgebraicGeometry.isPerfectRelativeTo_iff_of_isAffine`: Stacks 0GEH for a morphism of affine
  schemes and an arbitrary pseudo-coherent object.
* `AlgebraicGeometry.isPerfectRelativeTo_iff_isLocallyBoundedBelow_and_fibres`: Stacks 0GEH.

## Implementation notes

Tor amplitude over the base is read on the stalk complexes of a representing complex, viewed
over the local rings of `S`; at a point `x` it is the canonical Tor amplitude of
`AlgebraicGeometry.relativeStalkComplex`. Canonical Tor amplitude in `[a, b]` bounds the
cohomology of a complex of modules to `[a, b]`, since Stacks 0654 produces a flat representative
concentrated there; and the stalk functor and restriction of scalars along the germ map of `f`
are both exact and both reflect zero objects, so that bound propagates to the cohomology sheaves
of `E`.

The hypothesis `HasTorAmplitudeOver` is the stalkwise Tor amplitude of Stacks 0C0V in one global
interval. On an affine scheme it is identified with the Tor clause of relative perfectness,
Stacks 0DI0, by
`AffinePerfectDescent.exists_hasTorAmplitudeOver_of_locallyHasFiniteTorDimension`; this gives the
implication (1) ⇒ (2) of Stacks 0GEH on affine schemes. The converse on affine schemes is
`AffinePerfectDescent.isPerfectRelativeTo_of_isLocallyBoundedBelow_and_fibres` (Stacks 0GHJ
through the tilde dictionary).

The general case follows the source: everything is local, so one reduces to affine opens
`U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`. Relative perfectness restricts to and glues from such `U`
(`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_forall_mem`) and does not see the passage
from `S` to `V` (`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_baseOpen_iff`). The fibre of
`U ⟶ V` over `s ∈ V` is an open subscheme of the fibre of `f` over the image of `s` in `S`, and
these opens cover the fibres of `f`. On an affine scheme a pseudo-coherent object has
quasi-coherent cohomology (Stacks 08E5), hence is the derived sheafification of a complex of
modules, and the affine case is transported along `AlgebraicGeometry.Scheme.isoSpec`.

## References

* [Stacks Project, Lemma 36.35.13 (Tag 0GEH)](https://stacks.math.columbia.edu/tag/0GEH)
* [Stacks Project, Lemma 36.19.3 (Tag 0C0V)](https://stacks.math.columbia.edu/tag/0C0V)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 15.66.4 (Tag 0654)](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Lemma 15.85.10 (Tag 0GHJ)](https://stacks.math.columbia.edu/tag/0GHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard SheafOfModules.instAbelian

/-! ### Exact functors, cohomology and zero objects -/


/-- Vanishing of an `𝒪_X`-module is detected on the stalks read over the local rings: a module
all of whose stalks vanish has the zero morphism for an identity, because that is so at every
stalk. -/
public theorem isZero_of_forall_modulesStalk {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M)) :
    IsZero M := by
  refine (IsZero.iff_id_eq_zero M).2 ?_
  have hiso : IsIso (0 : M ⟶ M) := by
    refine isIso_of_forall_modulesStalk 0 fun x => ?_
    rw [Functor.map_zero, ← (IsZero.iff_id_eq_zero _).1 (h x)]
    infer_instance
  have h2 := IsIso.inv_hom_id (0 : M ⟶ M)
  rw [comp_zero] at h2
  exact h2.symm

/-! ### Tor independence from a flat morphism -/

/-- **A flat morphism is Tor independent from every morphism to the same base.** At a pair of
points over a common point of `S` the local ring of `X` is flat over the local ring of `S`, and
the higher Tor modules of a flat module vanish. -/
public theorem torIndependent_of_flat {X S Y : Scheme.{u}} (f : X ⟶ S) [Flat f] (g : Y ⟶ S) :
    TorIndependent f g := by
  intro x y h p hp
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    AlgebraicGeometry.Flat.stalkMap f x
  exact isZero_Tor_succ_of_flat _ _ n

/-! ### Tor amplitude over the base bounds the cohomology -/

/-- **Canonical Tor amplitude in `[a, b]` bounds the cohomology to `[a, b]`.** By Stacks 0654 the
object is represented by a complex of flat modules vanishing outside `[a, b]`, which has no
cohomology there either. -/
private theorem isZero_homology_of_hasTorAmplitudeCanonical {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b i : ℤ)
    (hK : HasTorAmplitudeCanonical R K a b) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
  obtain ⟨L, -, hGE, hLE, ⟨e⟩⟩ :=
    (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K a b).1 hK
  have hLi : IsZero (L.X i) := by
    rcases (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi : i < a ∨ b < i) with
      hlt | hgt
    · exact L.isZero_of_isStrictlyGE a i hlt
    · exact L.isZero_of_isStrictlyLE b i hgt
  exact (ShortComplex.isZero_homology_of_isZero_X₂ (L.sc i) hLi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app L)

/-- The same bound for Tor amplitude read after lifting the ring and the module carriers into
the ambient universe: the lift is exact and faithful, so it reflects the vanishing. -/
private theorem isZero_homology_of_hasTorAmplitudeCanonicalLift {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b i : ℤ)
    (hK : HasTorAmplitudeCanonicalLift.{u, u, u} K a b) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
  have h := isZero_homology_of_hasTorAmplitudeCanonical
    ((moduleLift.{u, u, u} R).mapDerivedCategory.obj K) a b i hK hi
  exact isZero_of_faithful (moduleLift.{u, u, u} R)
    ((isZero_homology_mapDerivedCategory_iff (moduleLift.{u, u, u} R) K i).1 h)

/-- **An object of Tor amplitude in `[a, b]` over the base has its cohomology concentrated in
`[a, b]`.** Tor amplitude over the base is the canonical Tor amplitude of the stalk complexes of
a representing complex, read over the local rings of `S`; that bounds the cohomology of each
stalk complex, and the stalk functor and restriction of scalars along the germ map are exact and
reflect zero objects, so the cohomology sheaves of `E` vanish outside `[a, b]`. -/
public theorem isZero_homology_of_hasTorAmplitudeOver {X S : Scheme.{u}} (f : X ⟶ S)
    (E : DerivedCategory X.Modules) (a b : ℤ) (hE : HasTorAmplitudeOver f E a b)
    (i : ℤ) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj E) := by
  obtain ⟨K, ⟨eK⟩, hK⟩ := hE
  have hQ : IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      (DerivedCategory.Q.obj K)) := by
    refine isZero_of_forall_modulesStalk _ fun x => ?_
    have hz := isZero_homology_of_hasTorAmplitudeCanonicalLift
      (DerivedCategory.Q.obj (relativeStalkComplex f K x)) a b i (hK x) hi
    have hz2 := hz.of_iso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (S.presheaf.stalk (f.base x))) i).mapIso
        (relativeStalkComplexDerivedIso f K x)).symm
    have hz3 := (isZero_homology_mapDerivedCategory_iff
      (ModuleCat.restrictScalars (f.stalkMap x).hom)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) i).1 hz2
    exact (isZero_homology_mapDerivedCategory_iff
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x) (DerivedCategory.Q.obj K) i).1
      (isZero_of_faithful (ModuleCat.restrictScalars (f.stalkMap x).hom) hz3)
  exact hQ.of_iso ((DerivedCategory.homologyFunctor X.Modules i).mapIso eK).symm

/-! ### Derived pullbacks along a base change of a flat morphism -/

/-- **The derived pullback of an object of finite Tor amplitude over the base, along a base
change of a flat morphism, is locally bounded below.** Flatness of `f` makes the square Tor
independent, so Stacks 0C0V carries Tor amplitude in `[a, b]` over `S` to Tor amplitude in
`[a, b]` over `S'`, and that bounds the cohomology of the pullback to `[a, b]`.

The conclusion is in fact uniform in the point: the cohomology of the pullback vanishes below
`a` on all of `X'`. -/
public theorem isLocallyBoundedBelow_derivedPullback_of_isPullback
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) [Flat f]
    (hpb : IsPullback g' f' f g) (E : DerivedCategory X.Modules) (a b : ℤ)
    (hamp : HasTorAmplitudeOver f E a b) :
    RingedSpace.IsLocallyBoundedBelow X'.toRingedSpace
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g'.toLRSHom.toShHom).obj E) := by
  have h := derivedPullback_hasTorAmplitudeOver g' f' f g hpb (torIndependent_of_flat f g) E a b
    hamp
  intro _
  refine ⟨⊤, trivial, a, fun j hj => ?_⟩
  exact Functor.map_isZero _ (isZero_homology_of_hasTorAmplitudeOver f' _ a b h j
    (by simp only [Set.mem_Icc]; omega))

/-- **Derived fibres of an object of finite Tor amplitude over the base.** Let `f : X ⟶ S`
be flat and locally of finite presentation, and let `E` be an object of `D(𝒪_X)` of Tor amplitude
in `[a, b]` over `S`. For every point `s` of `S` the derived pullback of `E` to the fibre
`X_s = X ×_S Spec κ(s)` is locally bounded below.

The fibre square is cartesian and `f` is flat, hence the square is Tor independent, so Stacks
0C0V transports the Tor amplitude to the fibre over `Spec κ(s)`; Tor amplitude over the base
bounds the cohomology of the object, so the derived fibre is even globally bounded below. -/
public theorem isLocallyBoundedBelow_derivedPullback_fibre_of_hasTorAmplitudeOver
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules) (a b : ℤ) (hamp : HasTorAmplitudeOver f E a b) (s : S) :
    RingedSpace.IsLocallyBoundedBelow
      (Limits.pullback f (S.fromSpecResidueField s)).toRingedSpace
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Limits.pullback.fst f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj E) :=
  isLocallyBoundedBelow_derivedPullback_of_isPullback
    (Limits.pullback.fst f (S.fromSpecResidueField s))
    (Limits.pullback.snd f (S.fromSpecResidueField s)) f (S.fromSpecResidueField s)
    (IsPullback.of_hasPullback _ _) E a b hamp

end AlgebraicGeometry

/-! ### Stacks 0GEH -/

open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

namespace AffinePerfectDescent

open AlgebraicGeometry.AffineRelativeTorAmplitude

section Affine

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Stacks 0GEH, the implication (1) ⇒ (2), for a morphism of affine schemes and a sheafified
complex.** Let `R → A` be flat of finite presentation, let `f : Spec A ⟶ Spec R` be the
associated morphism, and let `M^•` be a complex of `A`-modules. If its derived sheafification
`M̃^•` is `Spec R`-perfect in the sense of Stacks 0DI0, then `M̃^•` is locally bounded below and
for every point `s` of `Spec R` the derived fibre `L(X_s ⟶ X)^*M̃^•` is locally bounded below,
where `X_s = Spec A ×_{Spec R} Spec κ(s)`.

The first clause is `AlgebraicGeometry.isLocallyBoundedBelow_of_isPerfectRelativeTo`, which needs
nothing affine. The second is
`AlgebraicGeometry.isLocallyBoundedBelow_derivedPullback_fibre_of_hasTorAmplitudeOver`, whose
hypothesis of stalkwise Tor amplitude over the base is supplied here from the Tor clause of
relative perfectness by `exists_hasTorAmplitudeOver_of_isPerfectRelativeTo`; that passage is
where the affine hypothesis is spent. -/
theorem isLocallyBoundedBelow_and_fibres_of_isPerfectRelativeTo [Module.Flat R A]
    [Algebra.FinitePresentation R A] (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : (specMap R A).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) (tildeObj A M)) :
    RingedSpace.IsLocallyBoundedBelow (Spec (CommRingCat.of A)).toRingedSpace (tildeObj A M) ∧
      ∀ s : Spec (CommRingCat.of R), RingedSpace.IsLocallyBoundedBelow
        (Limits.pullback (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toRingedSpace
        ((derivedPullback (Limits.pullback.fst (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toLRSHom.toShHom).obj
            (tildeObj A M)) := by
  obtain ⟨a, b, hamp⟩ := exists_hasTorAmplitudeOver_of_isPerfectRelativeTo R A M h
  refine ⟨isLocallyBoundedBelow_of_isPerfectRelativeTo (specMap R A) _ (fun _ => rfl) _ h,
    fun s => ?_⟩
  exact isLocallyBoundedBelow_derivedPullback_fibre_of_hasTorAmplitudeOver (specMap R A)
    (tildeObj A M) a b hamp s

/-- **A perfect complex of `A`-modules satisfies condition (2) of Stacks 0GEH.** For `R → A`
flat of finite presentation and `M^•` a complex of `A`-modules representing a perfect object of
`D(A)`, the derived sheafification `M̃^•` is locally bounded below and so is each of its derived
fibres.

A perfect object of `D(A)` is perfect relative to `R` by Stacks 0DHU,
`PseudoCoherence.isRelativelyPerfect_of_isPerfect`, which crosses to `Spec R`-perfectness of
`M̃^•` by the affine dictionary `isPerfectRelativeTo_tildeObj_iff`; the conclusion is then
`isLocallyBoundedBelow_and_fibres_of_isPerfectRelativeTo`.

This is the non-vacuity witness for the hypothesis of that theorem: perfectness of
`DerivedCategory.Q.obj M` assumes nothing about certified derived tensor products, and Stacks
066T, `StacksDraft.Perfect.isPerfect_of_bounded_of_isPerfectModule`, supplies it for every
bounded complex of perfect `A`-modules. -/
theorem isLocallyBoundedBelow_and_fibres_of_isPerfect [Module.Flat R A]
    [Algebra.FinitePresentation R A] (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj M)) :
    RingedSpace.IsLocallyBoundedBelow (Spec (CommRingCat.of A)).toRingedSpace (tildeObj A M) ∧
      ∀ s : Spec (CommRingCat.of R), RingedSpace.IsLocallyBoundedBelow
        (Limits.pullback (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toRingedSpace
        ((derivedPullback (Limits.pullback.fst (specMap R A)
          ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toLRSHom.toShHom).obj
            (tildeObj A M)) :=
  isLocallyBoundedBelow_and_fibres_of_isPerfectRelativeTo R A M
    ((isPerfectRelativeTo_tildeObj_iff R A M).2
      (PseudoCoherence.isRelativelyPerfect_of_isPerfect
        (PseudoCoherence.canonicalDerivedTensoringDatum R).tensor
        (PseudoCoherence.canonicalDerivedTensoringDatum R).comparison
        (PseudoCoherence.canonicalDerivedTensoringDatum R).isLeftDerived
        (DerivedCategory.Q.obj M) hM))

/-- **Stacks 0GEH for a morphism of affine schemes and a sheafified complex.** Let `R → A` be
flat of finite presentation, let `f : Spec A ⟶ Spec R` be the associated morphism of affine
schemes and let `M^•` be a complex of `A`-modules whose derived sheafification `M̃^•` is a
pseudo-coherent object of `D(𝒪_{Spec A})`. Then `M̃^•` is `Spec R`-perfect in the sense of
Stacks 0DI0 if and only if `M̃^•` is locally bounded below and for every point `s` of `Spec R`
the derived fibre `L(X_s ⟶ X)^*M̃^•` of `D(𝒪_{X_s})` is locally bounded below, where
`X_s = Spec A ×_{Spec R} Spec κ(s)`.

The forward implication is `isLocallyBoundedBelow_and_fibres_of_isPerfectRelativeTo` and does
not use pseudo-coherence; the converse is
`isPerfectRelativeTo_of_isLocallyBoundedBelow_and_fibres` and does. -/
theorem isPerfectRelativeTo_tildeObj_iff_isLocallyBoundedBelow_and_fibres [Module.Flat R A]
    [Algebra.FinitePresentation R A] (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hpc : RingedSpace.IsPseudoCoherent (X := (Spec (CommRingCat.of A)).toRingedSpace)
      (tildeObj A M)) :
    (specMap R A).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) (tildeObj A M) ↔
      RingedSpace.IsLocallyBoundedBelow (Spec (CommRingCat.of A)).toRingedSpace (tildeObj A M) ∧
        ∀ s : Spec (CommRingCat.of R), RingedSpace.IsLocallyBoundedBelow
          (Limits.pullback (specMap R A)
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toRingedSpace
          ((derivedPullback (Limits.pullback.fst (specMap R A)
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toLRSHom.toShHom).obj
              (tildeObj A M)) :=
  ⟨isLocallyBoundedBelow_and_fibres_of_isPerfectRelativeTo R A M,
    fun h => isPerfectRelativeTo_of_isLocallyBoundedBelow_and_fibres R A M hpc h.1 h.2⟩

/-- **The structure sheaf of `Spec A` is `Spec R`-perfect, proved through condition (2).** For
`R → A` flat of finite presentation, `𝒪_{Spec A} = Ã` is `Spec R`-perfect.

This is the non-vacuity witness of
`isPerfectRelativeTo_of_isLocallyBoundedBelow_and_fibres`: it assumes nothing, and it reaches
condition (1) by feeding condition (2) — supplied by
`isLocallyBoundedBelow_and_fibres_of_isPerfect` — through that implication, so all three of
its hypotheses are exhibited as simultaneously satisfiable at an instance where the object is
nonzero. Instantiating `R := ULift ℤ` and `A := ℤ[x]` gives a closed statement about `𝔸^1_ℤ`,
whose base has positive dimension and whose fibres are positive-dimensional and nonempty. -/
theorem isPerfectRelativeTo_single_self [Module.Flat R A] [Algebra.FinitePresentation R A] :
    (specMap R A).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      (tildeObj A ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A))) := by
  have hM := isPerfect_Q_single_self A
  have hrp := PseudoCoherence.isRelativelyPerfect_of_isPerfect
    (PseudoCoherence.canonicalDerivedTensoringDatum R).tensor
    (PseudoCoherence.canonicalDerivedTensoringDatum R).comparison
    (PseudoCoherence.canonicalDerivedTensoringDatum R).isLeftDerived _ hM
  obtain ⟨h1, h2⟩ := isLocallyBoundedBelow_and_fibres_of_isPerfect R A _ hM
  exact isPerfectRelativeTo_of_isLocallyBoundedBelow_and_fibres R A _
    ((RingedSpace.isPseudoCoherent_tilde_iff _).2 hrp.1) h1 h2

/-- **The non-vacuity certificate, with every binder closed.** The structure sheaf of the affine
line `𝔸^1_ℤ = Spec ℤ[x]` is `Spec ℤ`-perfect. Every binder of
`isPerfectRelativeTo_of_isLocallyBoundedBelow_and_fibres` — the two rings, the algebra, the
flatness and finite-presentation instances, the complex, and all three hypotheses — is
instantiated here from declarations that assume nothing, at an instance which is not degenerate:
`Spec ℤ` has dimension one, the morphism has relative dimension one, every fibre
`𝔸^1_{κ(p)}` is nonempty, and the object is the nonzero structure sheaf. -/
theorem isPerfectRelativeTo_affineLine_int :
    (specMap (ULift.{u} ℤ) (MvPolynomial (Fin 1) (ULift.{u} ℤ))).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      (tildeObj (MvPolynomial (Fin 1) (ULift.{u} ℤ))
        ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin 1) (ULift.{u} ℤ)))
          0).obj (ModuleCat.of _ (MvPolynomial (Fin 1) (ULift.{u} ℤ))))) :=
  isPerfectRelativeTo_single_self (ULift.{u} ℤ) (MvPolynomial (Fin 1) (ULift.{u} ℤ))

end Affine

end AffinePerfectDescent

/-! ### The general case -/

section Affine

/-- Relative perfectness at the canonical certificate family is invariant under isomorphism. -/
private theorem isPerfectRelativeTo_canonical_iff_of_iso {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] {E E' : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (e : E ≅ E') :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E ↔
      f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E' :=
  ⟨Scheme.Hom.isPerfectRelativeTo_canonical_of_iso f e,
    Scheme.Hom.isPerfectRelativeTo_canonical_of_iso f e.symm⟩

open AffinePerfectDescent AffineRelativeTorAmplitude in
/-- **The fibrewise criterion on the spectrum of a flat finitely presented algebra.** Let `R → A`
be flat of finite presentation and let `E` be a pseudo-coherent object of `D(𝒪_{Spec A})`. Then
`E` is `Spec R`-perfect if and only if `E` is locally bounded below and every derived fibre
`L(X_s ⟶ X)^*E`, `s ∈ Spec R`, is locally bounded below.

`E` has quasi-coherent cohomology (Stacks 08E5), so it is the derived sheafification of a complex
of `A`-modules, where the criterion is
`AffinePerfectDescent.isPerfectRelativeTo_tildeObj_iff_isLocallyBoundedBelow_and_fibres`. -/
theorem isPerfectRelativeTo_specMap_iff (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (E : DerivedCategory (OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := (Spec (CommRingCat.of A)).toRingedSpace) E) :
    (specMap R A).IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        E ↔
      RingedSpace.IsLocallyBoundedBelow (Spec (CommRingCat.of A)).toRingedSpace E ∧
        ∀ s : Spec (CommRingCat.of R), RingedSpace.IsLocallyBoundedBelow
          (pullback (specMap R A) ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toRingedSpace
          ((derivedPullback (pullback.fst (specMap R A)
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toLRSHom.toShHom).obj E) := by
  have hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Spec (CommRingCat.of A)).Modules n).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent (Spec (CommRingCat.of A)) E hE
  obtain ⟨K, ⟨eK⟩⟩ := StandardModel.exists_iso_mapDerivedCategory (CommRingCat.of A) E hqc
  obtain ⟨M, ⟨eM⟩⟩ : (DerivedCategory.Q (C := ModuleCat.{u} A)).essImage K :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) K
  have eE : tildeObj A M ≅ E :=
    ((tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors.app M).symm ≪≫
      (tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso eM ≪≫ eK
  refine (isPerfectRelativeTo_canonical_iff_of_iso _ eE.symm).trans ?_
  have hM := RingedSpace.IsPseudoCoherent.of_iso hE eE.symm
  have key := isPerfectRelativeTo_tildeObj_iff_isLocallyBoundedBelow_and_fibres R A M hM
  refine key.trans (and_congr ?_ (forall_congr' fun s => ?_))
  · exact RingedSpace.isLocallyBoundedBelow_iso_iff eE
  · exact RingedSpace.isLocallyBoundedBelow_iso_iff ((derivedPullback (pullback.fst (specMap R A)
      ((Spec (CommRingCat.of R)).fromSpecResidueField s)).toLRSHom.toShHom).mapIso eE)

/-- **The fibrewise criterion for a morphism isomorphic to the spectrum of a ring map.** Let
`g : U ⟶ V` be flat and locally of finite presentation, isomorphic as an arrow to
`Spec φ : Spec A ⟶ Spec R`, with `U` quasi-compact, and let `K` be a pseudo-coherent object of
`D(𝒪_U)`. Then `K` is `V`-perfect if and only if `K` is locally bounded below and every derived
fibre `L(U_s ⟶ U)^*K`, `s ∈ V`, is locally bounded below. -/
theorem isPerfectRelativeTo_iff_of_arrowIso_spec {U V : Scheme.{u}} [CompactSpace U]
    (g : U ⟶ V) [Flat g] [LocallyOfFinitePresentation g] {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (α : U ≅ Spec A) (β : V ≅ Spec R) (w : g ≫ β.hom = α.hom ≫ Spec.map φ)
    (K : DerivedCategory (OXMod.{u, u} U.toRingedSpace))
    (hK : RingedSpace.IsPseudoCoherent (X := U.toRingedSpace) K) :
    g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K ↔
      RingedSpace.IsLocallyBoundedBelow U.toRingedSpace K ∧
        ∀ s : V, RingedSpace.IsLocallyBoundedBelow
          (pullback g (V.fromSpecResidueField s)).toRingedSpace
          ((derivedPullback (pullback.fst g (V.fromSpecResidueField s)).toLRSHom.toShHom).obj
            K) := by
  let : Algebra R A := φ.hom.toAlgebra
  have hφ : Spec.map φ = α.inv ≫ g ≫ β.hom := by rw [w, Iso.inv_hom_id_assoc]
  have hflat : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have hlfp : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  have : Module.Flat R A := (HasRingHomProperty.Spec_iff (P := @Flat)).1 hflat
  have : Algebra.FinitePresentation R A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 hlfp
  let K' := (derivedPullback (Scheme.forgetToRingedSpace.mapIso α).inv).obj K
  have eK : (derivedPullback (Scheme.forgetToRingedSpace.mapIso α).hom).obj K' ≅ K :=
    (Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso
      (Scheme.forgetToRingedSpace.mapIso α).symm).app K
  have hK' := RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback
    (Scheme.forgetToRingedSpace.mapIso α).inv K hK
  have key := isPerfectRelativeTo_specMap_iff R A K' hK'
  have hperf : g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      K ↔ (AffineRelativeTorAmplitude.specMap R A).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K' := by
    refine (isPerfectRelativeTo_canonical_iff_of_iso g eK.symm).trans ?_
    exact Scheme.Hom.isPerfectRelativeTo_arrowIso_iff g (Spec.map φ)
      (ringedArrowIsoOfIso g (Spec.map φ) α β w) K'
  have hbb : RingedSpace.IsLocallyBoundedBelow U.toRingedSpace K ↔
      RingedSpace.IsLocallyBoundedBelow (Spec A).toRingedSpace K' :=
    (RingedSpace.isLocallyBoundedBelow_iso_iff eK.symm).trans
      (isLocallyBoundedBelow_derivedPullback_iso_iff α K')
  have hfib : ∀ s : V, RingedSpace.IsLocallyBoundedBelow
        (pullback g (V.fromSpecResidueField s)).toRingedSpace
        ((derivedPullback (pullback.fst g (V.fromSpecResidueField s)).toLRSHom.toShHom).obj K) ↔
      RingedSpace.IsLocallyBoundedBelow
        (pullback (Spec.map φ) ((Spec R).fromSpecResidueField (β.hom.base s))).toRingedSpace
        ((derivedPullback (pullback.fst (Spec.map φ)
          ((Spec R).fromSpecResidueField (β.hom.base s))).toLRSHom.toShHom).obj K') := fun s =>
    (RingedSpace.isLocallyBoundedBelow_iso_iff ((derivedPullback
      (pullback.fst g (V.fromSpecResidueField s)).toLRSHom.toShHom).mapIso eK.symm)).trans
      (isLocallyBoundedBelow_fibre_iff_of_arrowIso g (Spec.map φ) α β w K' s)
  refine hperf.trans (key.trans (and_congr hbb.symm ⟨fun h s => (hfib s).2 (h _), fun h p => ?_⟩))
  have hp : β.hom.base (β.inv.base p) = p := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
  exact hp ▸ (hfib _).1 (h _)

/-- **The fibrewise criterion for a morphism of affine schemes.** Let `g : U ⟶ V` be a flat
morphism of affine schemes, locally of finite presentation, and let `K` be a pseudo-coherent
object of `D(𝒪_U)`. Then `K` is `V`-perfect if and only if `K` is locally bounded below and every
derived fibre `L(U_s ⟶ U)^*K`, `s ∈ V`, is locally bounded below. -/
theorem isPerfectRelativeTo_iff_of_isAffine {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (g : U ⟶ V) [Flat g] [LocallyOfFinitePresentation g]
    (K : DerivedCategory (OXMod.{u, u} U.toRingedSpace))
    (hK : RingedSpace.IsPseudoCoherent (X := U.toRingedSpace) K) :
    g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K ↔
      RingedSpace.IsLocallyBoundedBelow U.toRingedSpace K ∧
        ∀ s : V, RingedSpace.IsLocallyBoundedBelow
          (pullback g (V.fromSpecResidueField s)).toRingedSpace
          ((derivedPullback (pullback.fst g (V.fromSpecResidueField s)).toLRSHom.toShHom).obj
            K) :=
  isPerfectRelativeTo_iff_of_arrowIso_spec g g.appTop U.isoSpec V.isoSpec
    (Scheme.Hom.pullbackIsoSpecTensor_aux₁ g) K hK


end Affine

section Criterion

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]

/-- **Stacks 0GEH.** Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite
presentation, and let `E` be a pseudo-coherent object of `D(𝒪_X)`. The following are equivalent:

1. `E` is `S`-perfect (Stacks 0DI0);
2. `E` is locally bounded below and for every point `s ∈ S` the derived fibre `L(X_s ⟶ X)^*E` of
   `D(𝒪_{X_s})` is locally bounded below, where `X_s = X ×_S Spec κ(s)`.

Relative perfectness is read at the canonical certificate family
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`, the genuine
derived tensor product over `f⁻¹𝒪_S`. -/
@[stacks 0GEH]
theorem isPerfectRelativeTo_iff_isLocallyBoundedBelow_and_fibres
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E ↔
      RingedSpace.IsLocallyBoundedBelow X.toRingedSpace E ∧
        ∀ s : S, RingedSpace.IsLocallyBoundedBelow
          (pullback f (S.fromSpecResidueField s)).toRingedSpace
          ((derivedPullback (pullback.fst f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj
            E) := by
  constructor
  · intro h
    refine ⟨isLocallyBoundedBelow_of_isPerfectRelativeTo f _ (fun _ => rfl) E h, fun s₀ => ?_⟩
    refine isLocallyBoundedBelow_of_forall_openImmersion _ fun z => ?_
    obtain ⟨V, U, hV, hU, hxU, hUV⟩ := exists_affineOpens_le f
      ((pullback.fst f (S.fromSpecResidueField s₀)).base z)
    have : IsAffine V := hV
    have : IsAffine U := hU
    have hfz : f.base ((pullback.fst f (S.fromSpecResidueField s₀)).base z) = s₀ := by
      have hz : (pullback.fst f (S.fromSpecResidueField s₀)).base z ∈ f.base ⁻¹' {s₀} := by
        rw [← Scheme.Hom.range_fiberι]
        exact ⟨z, rfl⟩
      exact hz
    have hsV : s₀ ∈ V := hfz ▸ hUV hxU
    have hg := (Scheme.Hom.isPerfectRelativeTo_baseOpen_iff (f.resLE V U hUV) V.ι
      (Scheme.Hom.resLE_comp_ι f hUV) _).1
      (Scheme.Hom.isPerfectRelativeTo_opens_ι f U E h)
    have hgK := ((isPerfectRelativeTo_iff_of_isAffine (f.resLE V U hUV) _
      (Scheme.Hom.isPseudoCoherent_derivedPullback U.ι E hE)).1 hg).2 ⟨s₀, hsV⟩
    exact exists_openImmersion_fibre f (f.resLE V U hUV) U.ι V.ι (Scheme.Hom.resLE_comp_ι f hUV)
      ⟨s₀, hsV⟩ s₀ rfl E z (by rw [Scheme.Opens.range_ι]; exact hxU) hgK
  · rintro ⟨h1, h2⟩
    refine Scheme.Hom.isPerfectRelativeTo_of_forall_mem f E fun x => ?_
    obtain ⟨V, U, hV, hU, hxU, hUV⟩ := exists_affineOpens_le f x
    have : IsAffine V := hV
    have : IsAffine U := hU
    refine ⟨U, hxU, (Scheme.Hom.isPerfectRelativeTo_baseOpen_iff (f.resLE V U hUV) V.ι
      (Scheme.Hom.resLE_comp_ι f hUV) _).2 ?_⟩
    refine (isPerfectRelativeTo_iff_of_isAffine (f.resLE V U hUV) _
      (Scheme.Hom.isPseudoCoherent_derivedPullback U.ι E hE)).2
      ⟨isLocallyBoundedBelow_derivedPullback_of_isOpenImmersion U.ι E h1, fun s => ?_⟩
    exact isLocallyBoundedBelow_fibre_of_openImmersion f (f.resLE V U hUV) U.ι V.ι
      (Scheme.Hom.resLE_comp_ι f hUV) s E (h2 _)


end Criterion

/-- **Condition (2) of Stacks 0GEH for the affine line over `ℤ`.** The structure sheaf of
`𝔸^1_ℤ = Spec ℤ[x]` is locally bounded below, and so is each of its derived fibres over
`Spec ℤ`; this is condition (1),
`AlgebraicGeometry.AffinePerfectDescent.isPerfectRelativeTo_affineLine_int`, read through
`isPerfectRelativeTo_iff_isLocallyBoundedBelow_and_fibres`. -/
theorem isLocallyBoundedBelow_and_fibres_affineLine_int :
    RingedSpace.IsLocallyBoundedBelow
        (Spec (CommRingCat.of (MvPolynomial (Fin 1) (ULift.{u} ℤ)))).toRingedSpace
        (AffinePerfectDescent.tildeObj (MvPolynomial (Fin 1) (ULift.{u} ℤ))
          ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin 1) (ULift.{u} ℤ)))
            0).obj (ModuleCat.of _ (MvPolynomial (Fin 1) (ULift.{u} ℤ))))) ∧
      ∀ s : Spec (CommRingCat.of (ULift.{u} ℤ)), RingedSpace.IsLocallyBoundedBelow
        (pullback (AffineRelativeTorAmplitude.specMap (ULift.{u} ℤ)
          (MvPolynomial (Fin 1) (ULift.{u} ℤ)))
          ((Spec (CommRingCat.of (ULift.{u} ℤ))).fromSpecResidueField s)).toRingedSpace
        ((derivedPullback (pullback.fst (AffineRelativeTorAmplitude.specMap (ULift.{u} ℤ)
          (MvPolynomial (Fin 1) (ULift.{u} ℤ)))
          ((Spec (CommRingCat.of (ULift.{u} ℤ))).fromSpecResidueField s)).toLRSHom.toShHom).obj
          (AffinePerfectDescent.tildeObj (MvPolynomial (Fin 1) (ULift.{u} ℤ))
            ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin 1) (ULift.{u} ℤ)))
              0).obj (ModuleCat.of _ (MvPolynomial (Fin 1) (ULift.{u} ℤ)))))) :=
  (isPerfectRelativeTo_iff_isLocallyBoundedBelow_and_fibres _ _
    AffinePerfectDescent.isPerfectRelativeTo_affineLine_int.1).1
    AffinePerfectDescent.isPerfectRelativeTo_affineLine_int


end AlgebraicGeometry

end
