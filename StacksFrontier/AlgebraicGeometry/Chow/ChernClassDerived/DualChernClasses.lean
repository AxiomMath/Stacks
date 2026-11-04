module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualComplexChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualOfAPresentationComplex
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtComputation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedPullbackOfADual
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace

/-!
# The characteristic classes of the derived dual of a perfect object

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `E` be a perfect object of `D(𝒪_X)` whose Chern classes
are defined in the sense of [Stacks, Tag 0F9E] (1). This file proves [Stacks, Tag 0FAE]: the
characteristic classes of the derived dual `E^∨ = RSheafHom(E, 𝒪_X)` are those of `E` with the
alternating sign,

  `c_p(E^∨) = (-1)^p c_p(E)`,  `P_p(E^∨) = (-1)^p P_p(E)`  in  `A^p(X)`,
  `ch_p(E^∨) = (-1)^p ch_p(E)`  in  `A^p(X) ⊗ 𝐐`.

## Main definitions

* `Stacks.Chow.dualPresentationComplex` — the naive dual `SheafHom^•(𝓔^•, 𝒪_Y)` of a complex of
  `𝒪_Y`-modules, and `Stacks.Chow.dualPresentationComplexXIso`, the identification of its
  degree-`n` term with `(𝓔^{-n})^∨`.
* `Stacks.Chow.EnvelopePresentation.derivedDual` — **the derived dual of an envelope
  presentation**: the same envelope, with the naive dual complex, presents `E^∨`.

## Main results

* `Stacks.Chow.isLocallyBoundedFiniteLocallyFree_dualPresentationComplex` — the naive dual of a
  locally bounded complex of finite locally free modules is again one.
* `Stacks.Chow.hasDefinedChernClasses_derivedDual` — the Chern classes of `E^∨` are defined,
  which is what makes the source's assertion well-typed.
* `Stacks.Chow.perfectChernClass_apply_derivedDual`,
  `Stacks.Chow.perfectPowerSumComponent_derivedDual` and
  `Stacks.Chow.perfectChernCharacterComponent_derivedDual` — the three sign identities of
  [Stacks, Tag 0FAE].

## Implementation notes

### The three steps

The source's first proof reduces to a bounded complex of finite locally free modules and applies
[Stacks, Tag 0FA5]. Here the reduction is carried out presentation by presentation, which is how
[Stacks, Tag 0GUD] defines the classes of a perfect object in the first place: `c(E)` is
characterized by its restriction along the envelope of a presentation
(`Stacks.Chow.res_perfectChernClass`), so a *presentation of `E^∨` on the same envelope whose
complex is a termwise dual of the presenting complex of `E`* turns the sign rules for complexes
of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualComplexChern` into the sign rules
for `E^∨`.

Building that presentation needs exactly three things, and each is proved elsewhere:

* `Lf^*(E^∨) ≅ (Lf^*E)^∨`, which is
  `Stacks.SheafOfModules.derivedPullbackDerivedDualIso`, [Stacks, Tag 0FPC] carried along the
  monoidal derived pullback of [Stacks, Tag 079U]. Its two perfectness hypotheses are discharged
  by `Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree` on the
  presenting complex and by
  `Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect`, [Stacks, Tag 08CM]
  implying [Stacks, Tag 08G5], which turns the ringed-space perfectness the source assumes into
  the ringed-site perfectness those results are stated at.
* `(Q 𝓔^•)^∨ ≅ Q(SheafHom^•(𝓔^•, 𝒪_Y))`, which is
  `Stacks.Chow.derivedDualQIsoOfLocallyBounded`, the locally bounded form of
  [Stacks, Tag 08DM].
* `SheafHom^•(𝓔^•, 𝒪_Y)^n ≅ (𝓔^{-n})^∨`, which is
  `Stacks.Chow.dualPresentationComplexXIso`.

### Why the terms identification needs no boundedness and no monoidal structure

The degree-`n` term of the internal Hom complex of [Stacks, Tag 0A8Z] is the *product*, over
`q : ℤ`, of the sheaves `SheafHom(𝓔^{-q}, 𝓕^{n-q})`, which is
`AlgebraicGeometry.RingedSite.homDegreeIsLimit` and holds with no hypothesis on either complex.
When the target is the structure sheaf in degree zero all factors but `q = n` vanish, and a
product of a family with one nonvanishing member is that member:
`AlgebraicGeometry.RingedSite.homDegreeIsoSingle`. So no bound is needed.

Two other routes were considered and are worse. The coproduct description of [Stacks, Tag 08JH]
— `AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso` — collapses the same way but is
gated on a *global* bound `{i | ¬ IsZero (𝓔^i)}.Finite`, which the complex of an envelope
presentation does not have: on an envelope that is not quasi-compact the bounds genuinely vary
with the point. And the `ihom` spelling of the internal Hom complex,
`Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex_eq`, would need a monoidal closed
structure on the category `AlgebraicGeometry.Scheme.Modules Y` that the Chow complexes live in;
a compiler probe reports `failed to synthesize instance of type class MonoidalCategory
Y.Modules`, and it is not merely unseated — the monoidal structures of the repository are built
on `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf _)`, so seating them here would mean
transporting the whole closed structure across that spelling.

### Local boundedness of the dual complex

The terms are handled by `Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf`
— the dual-at-a-nonconstant-rank clause of [Stacks, Tag 0FA7] — transported along
`dualPresentationComplexXIso`. For the bounds, the window `[lo, hi]` of `𝓔^•` becomes the window
`[-hi, -lo]` of the dual, and the vanishing is moved across by
`Stacks.Chow.isZero_over_dualSheaf`: the internal Hom out of a module vanishing on `U` vanishes
on `U`, because the internal Hom commutes with restriction to the slice
(`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheafOverIso`, [Stacks, Tag 0E8H]) and the
internal Hom out of a zero module is zero
(`AlgebraicGeometry.RingedSite.internalHomSheaf_isZero_of_isZero`).

Local boundedness in the Chow sense is stated with
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`, restriction to the open
*subspace*, while the internal-Hom restriction results are stated with `SheafOfModules.over`,
restriction to the *slice site*. The two directions of that passage are
`Stacks.Chow.isZero_over_of_isZero_restrictModules`, the unit of
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`, and
`Stacks.Chow.isZero_restrictModules_of_isZero_over`, which is free because
`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp` is `Iso.refl`.

### Only termwise isomorphisms of complexes are used

The sign rules of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualComplexChern` ask
only for isomorphisms `𝓕^n ≅ (𝓔^{-n})^∨` and nothing about the differentials, so the signed
transpose differential of the dual complex of [Stacks, Tag 0FPR] never enters, and the identity
`(Q 𝓔^•)^∨ ≅ Q(SheafHom^•(𝓔^•, 𝒪_Y))` is used only in the derived category, where it is what
the presentation's `representation` field asks for.

## References

* [Stacks Project, Tag 0FAE](https://stacks.math.columbia.edu/tag/0FAE)
* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open StrictlyPerfect
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The naive dual of a complex, and its terms -/

section DualComplex

variable {Y : Scheme.{u}}

/-- **The naive dual complex `SheafHom^•(𝓔^•, 𝒪_Y)`** of a complex of `𝒪_Y`-modules: the internal
Hom complex of [Stacks, Tag 0A8Z] into the structure sheaf placed in degree zero. For a locally
bounded complex of finite locally free modules its class in `D(𝒪_Y)` is the derived dual of the
class of `𝓔^•`, which is `Stacks.Chow.derivedDualQIsoOfLocallyBounded`. -/
def dualPresentationComplex (P : CochainComplex Y.Modules ℤ) : CochainComplex Y.Modules ℤ :=
  (AlgebraicGeometry.RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Y.sheaf) P
    (AlgebraicGeometry.RingedSite.structureSheafComplex
      (Stacks.SheafOfModules.ringedSite Y.sheaf))).obj

/-- **`SheafHom^•(𝓔^•, 𝒪_Y)^n ≅ (𝓔^{-n})^∨`.** The degree-`n` term of the naive dual complex is
the dual of the degree-`(-n)` term, with no hypothesis on the complex at all.

The term is the product over `q : ℤ` of the sheaves `SheafHom(𝓔^{-q}, 𝒪[0]^{n-q})`, and
`𝒪[0]^{n-q}` is zero unless `q = n`; `AlgebraicGeometry.RingedSite.homDegreeIsoSingle` is that
collapse, and `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf` is the internal Hom into the
structure sheaf on the nose. -/
def dualPresentationComplexXIso (P : CochainComplex Y.Modules ℤ) (n : ℤ) :
    (dualPresentationComplex P).X n ≅ dualSheaf (P.X (-n)) :=
  AlgebraicGeometry.RingedSite.homDegreeIsoSingle
    (Stacks.SheafOfModules.ringedSite Y.sheaf) P _ n

end DualComplex

/-! ### Vanishing on an open, across the two models of restriction -/

section Vanishing

variable {Y : Scheme.{u}} (M : Y.Modules) (U : Opens (Y : TopCat.{u}))

/-- **A module whose restriction to the open subspace `Y|_U` vanishes has vanishing restriction
to the slice site over `U`.** This is the unit of
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`, read at the module,
as in `Stacks.Chow.isLocallyStrictlyPerfect_of_isLocallyBoundedFiniteLocallyFree`. -/
theorem isZero_over_of_isZero_restrictModules
    (h : IsZero ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules
      Y.toRingedSpace U).obj M)) :
    IsZero (M.over U) :=
  (Functor.map_isZero (AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict
    Y.toRingedSpace U).inverse h).of_iso
      (AlgebraicGeometry.RingedSpace.overEquivRestrictedUnitIso Y.toRingedSpace U M).symm

/-- **The converse**: a module whose restriction to the slice site over `U` vanishes has
vanishing restriction to the open subspace `Y|_U`. No transport is paid — restriction to the
subspace *is* restriction to the slice followed by the identification of the two models, which
is what `AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp` records by being
`Iso.refl`. -/
theorem isZero_restrictModules_of_isZero_over (h : IsZero (M.over U)) :
    IsZero ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules
      Y.toRingedSpace U).obj M) :=
  Functor.map_isZero (AlgebraicGeometry.RingedSpace.overToRestricted Y.toRingedSpace U) h

end Vanishing

section DualVanishing

variable {Y : Scheme.{u}}

/-- **The dual of a module vanishing on `U` vanishes on `U`.** The dual is the internal Hom into
the structure sheaf, the internal Hom commutes with restriction to the slice site over `U`
([Stacks, Tag 0E8H]), and the internal Hom out of a zero module is zero. -/
theorem isZero_over_dualSheaf (M : Y.Modules) (U : Y.Opens) (h : IsZero (M.over U)) :
    IsZero ((dualSheaf M).over U) :=
  (AlgebraicGeometry.RingedSite.internalHomSheaf_isZero_of_isZero
    ((Stacks.SheafOfModules.ringedSite Y.sheaf).over U) h).of_iso
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheafOverIso Y U M)

end DualVanishing

/-! ### The naive dual of a locally bounded complex of finite locally free modules -/

section LocallyBounded

variable {Y : Scheme.{u}} {P : CochainComplex Y.Modules ℤ}

/-- **The naive dual of a locally bounded complex of finite locally free modules is again
one.** The terms are the duals of the terms, which are finite locally free by the
dual-at-a-nonconstant-rank clause of [Stacks, Tag 0FA7]; and the window `[lo, hi]` of `𝓔^•`
around a point becomes the window `[-hi, -lo]` of the dual, the vanishing being carried across by
`Stacks.Chow.isZero_over_dualSheaf`. -/
theorem isLocallyBoundedFiniteLocallyFree_dualPresentationComplex
    (hP : IsLocallyBoundedFiniteLocallyFree (X := Y.toRingedSpace) P) :
    IsLocallyBoundedFiniteLocallyFree (X := Y.toRingedSpace) (dualPresentationComplex P) := by
  refine ⟨fun n => ?_, fun x => ?_⟩
  · exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
      (dualPresentationComplexXIso P n).symm
      (h := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf (P.X (-n))
        (hP.1 (-n)))
  · obtain ⟨U, hxU, lo, hi, hz⟩ := hP.2 x
    refine ⟨U, hxU, -hi, -lo, fun n hn => ?_⟩
    have hwin : -n < lo ∨ hi < -n := by
      rcases hn with h | h
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    refine isZero_restrictModules_of_isZero_over _ U
      ((isZero_over_dualSheaf (P.X (-n)) U
        (isZero_over_of_isZero_restrictModules _ U (hz (-n) hwin))).of_iso ?_)
    exact (SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.SheafOfModules.ringedSite Y.sheaf).O) U).mapIso
        (dualPresentationComplexXIso P n)

/-- **A locally bounded complex of finite locally free modules represents a perfect object for
the ringed site of opens.** The complex is a perfect complex of the ringed space by
`Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree`, and
[Stacks, Tag 08CM] implies [Stacks, Tag 08G5] by
`Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect`. -/
theorem isPerfect_ringedSite_Q_of_isLocallyBoundedFiniteLocallyFree
    (hP : IsLocallyBoundedFiniteLocallyFree (X := Y.toRingedSpace) P) :
    (Stacks.SheafOfModules.ringedSite Y.sheaf).IsPerfect (DerivedCategory.Q.obj P) :=
  Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect Y.toRingedSpace _
    ⟨P, Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree P hP,
      ⟨Iso.refl _⟩⟩

end LocallyBounded

/-! ### The derived dual of an object of `D(𝒪_Y)`, at the Chow spelling -/

section DerivedDualMap

variable {Y : Scheme.{u}}

/-- **The derived dual `E^∨ = RSheafHom(E, 𝒪_Y)` of an object of `D(𝒪_Y)`**, read in the category
`DerivedCategory Y.Modules` that the Chow chapter's objects live in.

The underlying object is `Stacks.SheafOfModules.derivedDual`, stated at
`Stacks.SheafOfModules.StructureSheafModules Y.sheaf`. That is the same type as `Y.Modules`, but
its `Category`, `Abelian` and `HasDerivedCategory` instances are different *terms*, so an
`EnvelopePresentation` of the unwrapped object does not match
`Stacks.Chow.EnvelopePresentation.locallyOfFiniteType_f` and the restriction of its classes along
its own envelope cannot even be stated. Naming the object here is what keeps the Chow statements
on the Chow side of that seam; this is the device of `Stacks.Chow.derivedTwist`. -/
def derivedDual (E : DerivedCategory Y.Modules) : DerivedCategory Y.Modules :=
  Stacks.SheafOfModules.derivedDual Y.sheaf E

/-- **The derived dual of [Stacks, Tag 08DQ] carries an isomorphism to an isomorphism**: it is
the derived internal Hom into the structure sheaf, contravariantly functorial in its source, and
a contravariant functor applied to an isomorphism is an isomorphism. -/
def derivedDualMapIso {L L' : DerivedCategory Y.Modules} (e : L ≅ L') :
    derivedDual L ≅ derivedDual L' :=
  ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).mapIso e.symm.op).app _

end DerivedDualMap

/-! ### The derived dual of an envelope presentation -/

section Presentation

variable {X : Scheme.{u}} {E : DerivedCategory X.Modules}

/-- **The derived dual of an envelope presentation.** If `f : Y ⟶ X` is an envelope with `Lf^*E`
represented by the locally bounded complex `𝓔^•` of finite locally free modules, and `E` is
perfect, then the same envelope has `Lf^*(E^∨)` represented by the naive dual complex
`SheafHom^•(𝓔^•, 𝒪_Y)`.

The representing isomorphism is the composite of the three identities named in this module's
documentation: `Lf^*(E^∨) ≅ (Lf^*E)^∨` of [Stacks, Tag 0FPC], then `(Lf^*E)^∨ ≅ (Q 𝓔^•)^∨` by
functoriality of the dual, then `(Q 𝓔^•)^∨ ≅ Q(SheafHom^•(𝓔^•, 𝒪_Y))` of [Stacks, Tag 08DM]. -/
def EnvelopePresentation.derivedDual (H : EnvelopePresentation E)
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    EnvelopePresentation (Stacks.Chow.derivedDual E) where
  Y := H.Y
  f := H.f
  envelope := H.envelope
  P := dualPresentationComplex H.P
  locallyBounded := isLocallyBoundedFiniteLocallyFree_dualPresentationComplex H.locallyBounded
  representation :=
    ⟨Stacks.SheafOfModules.derivedPullbackDerivedDualIso H.f.toLRSHom.toShHom E
        (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect
          X.toRingedSpace E hE)
        (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect
          H.Y.toRingedSpace _
          ⟨H.P, Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree
            H.P H.locallyBounded, ⟨H.representation.some.symm⟩⟩) ≪≫
      derivedDualMapIso H.representation.some ≪≫
      derivedDualQIsoOfLocallyBounded H.locallyBounded⟩

/-- The dual presentation lives on the same envelope scheme. -/
@[simp]
theorem EnvelopePresentation.derivedDual_Y (H : EnvelopePresentation E)
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    (H.derivedDual hE).Y = H.Y :=
  rfl

/-- The dual presentation uses the same envelope. -/
theorem EnvelopePresentation.derivedDual_f (H : EnvelopePresentation E)
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    (H.derivedDual hE).f = H.f :=
  rfl

/-- The complex of the dual presentation is the naive dual complex. -/
theorem EnvelopePresentation.derivedDual_P (H : EnvelopePresentation E)
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    (H.derivedDual hE).P = dualPresentationComplex H.P :=
  rfl

/-- **The Chern classes of the derived dual of a perfect object are defined** as soon as those of
the object are, [Stacks, Tag 0F9E] (1) for `E^∨`: dualize an envelope presentation of `E`.

This is what makes the assertion of [Stacks, Tag 0FAE] well-typed, the classes `c_p`, `P_p` and
`ch_p` of [Stacks, Tag 0F9E] (2) being defined only under that hypothesis. -/
@[stacks 0FAE "the Chern classes of the derived dual are defined, which is what makes the \
assertion of the lemma well-typed"]
theorem hasDefinedChernClasses_derivedDual
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (h : HasDefinedChernClasses E) :
    HasDefinedChernClasses (Stacks.Chow.derivedDual E) :=
  ⟨h.some.derivedDual hE⟩

end Presentation

/-! ### The three sign identities -/

section Signs

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules}

/-- **The sign rule for the total Chern class of the derived dual**:
`c(E^∨)` is the `(-1)^p`-scaling of `c(E)`.

Both sides restrict, along the envelope of the dual presentation
`Stacks.Chow.EnvelopePresentation.derivedDual` — which is the envelope of the given presentation
of `E` — to the total Chern class of the naive dual complex and to the scaling of the total
Chern class of the presenting complex respectively, and those agree by
`Stacks.Chow.complexChern_of_termwiseDual`. Restriction along an envelope is injective on total
classes, which is `Stacks.Chow.eq_perfectChernClass`. -/
theorem perfectChernClass_derivedDual
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (h : HasDefinedChernClasses E) :
    perfectChernClass C sX (hasDefinedChernClasses_derivedDual hE h) =
      TotalChowClass.signScale (perfectChernClass C sX h) :=
  -- The envelope and the complex of the dual presentation are `H.f` and `SheafHom^•(H.P, 𝒪)`
  -- only up to unfolding the structure instance, so the chain is written out at `H.f` and
  -- matched against the goal by definitional equality rather than rewritten into it.
  (eq_perfectChernClass C sX (hasDefinedChernClasses_derivedDual hE h) (h.some.derivedDual hE)
    ((TotalChowClass.res_signScale h.some.f rfl (perfectChernClass C sX h)).trans
      ((congrArg TotalChowClass.signScale (res_perfectChernClass C sX h h.some)).trans
        (complexChern_of_termwiseDual C (h.some.f ≫ sX) h.some.locallyBounded
          (isLocallyBoundedFiniteLocallyFree_dualPresentationComplex h.some.locallyBounded)
          (dualPresentationComplexXIso h.some.P)).symm))).symm

/-- **`c_p(E^∨) = (-1)^p c_p(E)` in `A^p(X)`**, the first conclusion of [Stacks, Tag 0FAE]. -/
@[stacks 0FAE "the Chern classes: c_p(E-dual) = (-1)^p c_p(E) in A^p(X)"]
theorem perfectChernClass_apply_derivedDual
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (h : HasDefinedChernClasses E) (p : ℕ) :
    perfectChernClass C sX (hasDefinedChernClasses_derivedDual hE h) p =
      ((-1 : ℤ) ^ p) • perfectChernClass C sX h p := by
  rw [perfectChernClass_derivedDual C sX hE h, TotalChowClass.signScale_apply]

/-- **The sign rule for the power-sum classes of the derived dual**: `P_p(E^∨)` is the
`(-1)^p`-scaling of `P_p(E)`.

As for the total Chern class, both sides restrict along the envelope of the dual presentation,
to `P_p` of the naive dual complex and to the scaling of `P_p` of the presenting complex, and
those agree by `Stacks.Chow.complexPowerSum_of_termwiseDual`. -/
theorem perfectPowerSum_derivedDual
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (h : HasDefinedChernClasses E) (p : ℕ) :
    perfectPowerSum C sX (hasDefinedChernClasses_derivedDual hE h) p =
      TotalChowClass.signScale (perfectPowerSum C sX h p) := by
  refine TotalChowClass.res_injective_of_isEnvelope (h.some.derivedDual hE).f
    (h.some.derivedDual hE).envelope rfl ?_
  rw [res_perfectPowerSum C sX (hasDefinedChernClasses_derivedDual hE h)
      (h.some.derivedDual hE) p, TotalChowClass.res_signScale]
  exact (complexPowerSum_of_termwiseDual C (h.some.f ≫ sX) h.some.locallyBounded
      (isLocallyBoundedFiniteLocallyFree_dualPresentationComplex h.some.locallyBounded)
      (dualPresentationComplexXIso h.some.P) p).trans
    (congrArg TotalChowClass.signScale (res_perfectPowerSum C sX h h.some p).symm)

/-- **`P_p(E^∨) = (-1)^p P_p(E)` in `A^p(X)`**, the second conclusion of [Stacks, Tag 0FAE]. -/
@[stacks 0FAE "the power-sum classes: P_p(E-dual) = (-1)^p P_p(E) in A^p(X)"]
theorem perfectPowerSumComponent_derivedDual
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (h : HasDefinedChernClasses E) (p : ℕ) :
    perfectPowerSumComponent C sX (hasDefinedChernClasses_derivedDual hE h) p =
      ((-1 : ℤ) ^ p) • perfectPowerSumComponent C sX h p := by
  show perfectPowerSum C sX (hasDefinedChernClasses_derivedDual hE h) p p =
    ((-1 : ℤ) ^ p) • perfectPowerSum C sX h p p
  rw [perfectPowerSum_derivedDual C sX hE h p, TotalChowClass.signScale_apply]

/-- **`ch_p(E^∨) = (-1)^p ch_p(E)` in `A^p(X) ⊗ 𝐐`**, the third conclusion of
[Stacks, Tag 0FAE]. The Chern character component is `P_p/p!`, so the sign passes through the
tensor factor. -/
@[stacks 0FAE "the Chern character: ch_p(E-dual) = (-1)^p ch_p(E) in A^p(X) tensor Q"]
theorem perfectChernCharacterComponent_derivedDual
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (h : HasDefinedChernClasses E) (p : ℕ) :
    perfectChernCharacterComponent C sX (hasDefinedChernClasses_derivedDual hE h) p =
      ((-1 : ℤ) ^ p) • perfectChernCharacterComponent C sX h p := by
  show ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ]
      perfectPowerSumComponent C sX (hasDefinedChernClasses_derivedDual hE h) p =
    ((-1 : ℤ) ^ p) • (((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] perfectPowerSumComponent C sX h p)
  rw [perfectPowerSumComponent_derivedDual C sX hE h p, TensorProduct.tmul_smul]

/-- **The Chern character sign identity with the rational scalar**, which is how the source
writes it: `ch_p(E^∨) = (-1)^p ch_p(E)` with `(-1)^p` read in `𝐐`. The two readings agree because
`(-1)^p` is an integer and the `𝐐`-action on `A^p(X) ⊗ 𝐐` restricts to the `𝐙`-action. -/
theorem perfectChernCharacterComponent_derivedDual'
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (h : HasDefinedChernClasses E) (p : ℕ) :
    perfectChernCharacterComponent C sX (hasDefinedChernClasses_derivedDual hE h) p =
      ((-1 : ℚ) ^ p) • perfectChernCharacterComponent C sX h p := by
  rw [perfectChernCharacterComponent_derivedDual C sX hE h p,
    show ((-1 : ℚ) ^ p) = ((((-1 : ℤ) ^ p : ℤ) : ℚ)) by push_cast; ring,
    Int.cast_smul_eq_zsmul]

end Signs

end Stacks.Chow

end
