module

public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.GradedDirectImage
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.GeneratedInDegreeOne
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
import StacksCore.Tactic.StacksAttribute

/-!
# Deformations of projective schemes

Let `f : X ⟶ S` be proper, flat and of finite presentation, let `ℒ` be an invertible
`𝒪_X`-module ample relative to `f`, and let `S` be quasi-compact.  [Stacks, Tag 0D4F] produces a
single degree bound `d₀ ≥ 0` which works for *every* cartesian deformation of the family across a
thickening of the base: for every cartesian square

```
X --i'--> X'
|f        |f'
S --i-->  S'
```

with `S ⊂ S'` a thickening, `f'` proper, flat and of finite presentation, and every invertible
`𝒪_{X'}`-module `ℒ'` with `ℒ ≅ (i')^* ℒ'`, the five conclusions of the tag hold with that one
`d₀`, and the construction is functorial in the data.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily`: the hypotheses of the tag on
  the family `(X, S, f, ℒ)` being deformed.
* `Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.AdmissibleDeformation`: one
  cartesian deformation of a polarized family across a thickening of the base, with its lifted
  polarization.
* `PolarizedFamily.AdmissibleDeformation.sectionPiece` in this namespace:
  the degree-`d` piece `𝒜'_d = (f')_* (ℒ')^{⊗ d}`.
* `PolarizedFamily.AdmissibleDeformation.IsTruncatedSectionAlgebra` in this namespace:
  the characterisation of `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d` by its homogeneous pieces.
* The granted inputs `UniformHighTwistVanishing`, `VanishingDescendsAlongThickening`,
  `RelativelyAmpleLiftsAlongThickening`, `TruncatedSectionAlgebraExists`,
  `TruncatedSectionAlgebraFinitePresentation`, `RelativeProjIdentification` and
  `TwistIdentification` in this namespace, each a statement of a tag the source cites and this
  library does not carry; see the implementation notes.

[Stacks, Tag 0D4F] itself is
`Stacks.AlgebraicGeometry.ProjectiveDeformation.exists_uniform_degreeBound_functorial`.

## Implementation notes

**The inputs.**  The cited inputs of the source proof are recorded here as Props, each
quantified over data that the statement of [Stacks, Tag 0D4F] never mentions, so that none of
them contains the uniformity of `d₀`:

* `UniformHighTwistVanishing` is the eventual-vanishing clause of [Stacks, Tag 0B5T] at that
  tag's own hypotheses — `g` proper, `M` ample relative to `g`, base quasi-compact.  The library's
  form of it,
  `RelativeAmpleTwistVanishing.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`,
  assumes in addition that the base is Noetherian, which [Stacks, Tag 0D4F] does not grant, and
  is itself conditional on
  `Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase`.  It speaks of
  one family and no deformation.
* `VanishingDescendsAlongThickening` is the composite of three cited inputs: [Stacks, Tag 0B91]
  (1) makes `Rg'_* ℱ'` a perfect object of `D(𝒪_{T'})` whose formation commutes with arbitrary
  base change, so that `Lj^* Rg'_* ℱ' = Rg_* (j')^* ℱ'`; [Stacks, Tag 0D4E] identifies the latter
  with a finite locally free module in degree `0`; and [Stacks, Tag 0BDK] transports that back up
  along `j`, which is surjective on points.  The perfection half of [Stacks, Tag 0B91] is absent
  outright — see the attribute strings of
  `StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatPushforwardBaseChange.lean` — and the
  universal
  property of [Stacks, Tag 0BDK] is proved only along open immersions, see the docstring of
  `StacksFrontier/AlgebraicGeometry/Perfect/SingleDegreeRankOpen.lean`, whereas a thickening is a
  closed immersion.  The granted statement quantifies over an arbitrary invertible module on the
  deformed total space, an arbitrary invertible module on the original one isomorphic to its
  restriction, and an arbitrary single degree; it knows nothing of ampleness and fixes no bound,
  so the uniformity of `d₀` is not contained in it.
* `TruncatedSectionAlgebraExists` is the assertion of [Stacks, Tag 01VJ] (5) that
  `𝒪_T ⊕ ⨁_{d ≥ d₀} g_* M^{⊗ d}` is a quasi-coherent graded `𝒪_T`-algebra.  The library
  assembles the full algebra `⨁_{d ≥ 0} g_* M^{⊗ d}` (`Stacks.RelativeAmple.directImageAlgebra`)
  but not this truncation of it.
* `TruncatedSectionAlgebraFinitePresentation` is conclusion (3) for a single deformation.  The
  source proves it from [Stacks, Tag 0B5T] (the finite generation clause), the limit descent of
  [Stacks, Tags 01ZR, 0B8W, 081F, 04AI, 09MT] and the algebra chain
  [Stacks, Tags 00IS, 0561, 0519, 0D46, 00F4].  That argument uses neither the thickening nor the
  uniformity of `d₀` — it is affine-local on `S'` and sees only `X' ⟶ S'`, `ℒ'` and the local
  freeness of the pieces, which is exactly what is hypothesised here.  The limit inputs are all
  proved unconditionally; the finite generation clause of [Stacks, Tag 0B5T] is not, being blocked
  on clause (5) of [Stacks, Tag 01YS] — see the docstring of
  `StacksFrontier/AlgebraicGeometry/ProperAmpleCohomology/Basic.lean`.
* `RelativeProjIdentification` is conclusion (4) for a single deformation.  The source obtains it
  from [Stacks, Tags 07ZJ, 01VJ, 01O9, 0C6J]; the library carries [Stacks, Tag 07ZJ]
  (`Stacks.AlgebraicGeometry.RelativeProjMapDomain.isIso_relativeMapHom_of_eventually_isIso`) and
  [Stacks, Tag 0C6J] (`Stacks.RelativeAmple.isIso_relativeAmpleProjHom`, for the morphism
  `r_{L, ψ}` of [Stacks, Tag 01VJ], `Stacks.RelativeAmple.relativeAmpleProjHom`); what is not
  supplied is the comparison of the truncated algebra here with the full algebra
  `Stacks.RelativeAmple.directImageAlgebra` that [Stacks, Tag 07ZJ] would be applied to.
* `TwistIdentification` is conclusion (5) for a single deformation.  No comparison map of that
  shape exists in the library: the graded map `θ` of [Stacks, Tag 01O9] is not constructed, the
  second claim of [Stacks, Tag 01QI] — its absolute analogue — is recorded as absent in
  `StacksFrontier/AlgebraicGeometry/SectionRingProjGoodOpen/Basic.lean`, and the only global
  statement of the degree-one case is for the canonical map out of a symmetric algebra,
  `Stacks.Tag07ZRVeryAmple.twistOneIsoPullback`.

* `RelativelyAmpleLiftsAlongThickening` is [Stacks, Tag 0D2R] in the form the data of this tag
  provides.  The library carries it as
  `Stacks.ThickeningInvertible.isRelativelyAmple_of_isRelativelyAmple_pullback`, conditional on
  `Stacks.ThickeningInvertible.AmpleReflectedByThickening` — the `mp` half of
  [Stacks, Tag 09MW] — and stated for the restriction `(i')^* ℒ'` rather than for a module
  isomorphic to it.

**Which `𝒪(1)`.**  The twist of conclusion (5) is
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist 𝒜' 1`, whose nested-cocycle input is
discharged unconditionally by `Stacks.AlgebraicGeometry.ProjTwistCocycle.isNestedCocycle`.  It is
the same sheaf as `Stacks.Tag07ZRVeryAmple.twistOne 𝒜'`, but the results proved about the latter
need `𝒜'` generated in degree one: the truncated algebra of this tag is generated in degrees
`≥ d₀` and has `𝒜'_1 = 0` as soon as `d₀ > 1`.

**Which `IsFiniteLocallyFree`.**  The repository carries two classes of this name with the same
body.  The one used here is `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of
`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean`, which is the conclusion of
[Stacks, Tag 0D4E] as formalized, read over `AlgebraicGeometry.Scheme.Modules` of the *deformed*
base
`S'`.  The other, `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, appears only inside the proofs
of the side conditions.

**Two short names that already occur elsewhere.**  `PolarizedFamily` is also the name of
`AlgebraicGeometry.PolarizedFamily` in
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedFamilies.lean`, whose base is an object of the big
fppf site `B.Schemes` and which is the input of the Quot-functor development; the one here is over
a plain `AlgebraicGeometry.Scheme` and additionally demands that the base be quasi-compact and the
polarization relatively ample, neither of which that one does.  `sectionPiece` is also the name of
`Stacks.Cohomology.TwistedGradedModule.sectionPiece`, which is a graded piece of a twisted module
on one scheme, not a direct image.  Neither fully qualified name is shared, and nothing here is
stated about either of those objects.

**Which relative `Proj`.**  `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` applied to a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` over `S'`, which is the only
relative `Proj` in the repository carrying a Serre twist.  The other one,
`Stacks.RelativeProj.Situation.relativeProj`, has a twist only conditionally on a
`Stacks.RelativeProj.Situation.TwistTransition`, which is never constructed.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Ample
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.VanishingHigherDirectImages
open Stacks.RelativeAmple
open Stacks.Thickenings

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

attribute [local instance] HasDerivedCategory.standard

/-! ### The data of the tag -/

/-- **A polarized family.**  A proper, flat morphism of finite presentation `f : X ⟶ S` over a
quasi-compact base, together with an invertible `𝒪_X`-module ample relative to `f`.  These are the
hypotheses of [Stacks, Tag 0D4F] on the family being deformed. -/
public structure PolarizedFamily where
  /-- The total space. -/
  X : Scheme.{u}
  /-- The base. -/
  S : Scheme.{u}
  /-- The structure morphism. -/
  f : X ⟶ S
  /-- The polarization. -/
  L : X.Modules
  /-- The structure morphism is proper. -/
  isProper : IsProper f
  /-- The structure morphism is flat. -/
  flat : Flat f
  /-- The structure morphism is of finite presentation. -/
  finitePresentation : _root_.AlgebraicGeometry.FinitePresentation f
  /-- The polarization is invertible. -/
  invertible : IsInvertibleModule X L
  /-- The polarization is ample relative to the structure morphism. -/
  isRelativelyAmple : letI := invertible; IsRelativelyAmple f L
  /-- The base is quasi-compact. -/
  compactSpace : CompactSpace S

namespace PolarizedFamily

attribute [instance] isProper flat invertible compactSpace

/-- **An admissible deformation of a polarized family.**  A cartesian square whose bottom row is a
thickening `S ⊂ S'` of the base, whose right-hand column `f'` is again proper, flat and of finite
presentation, together with an invertible `𝒪_{X'}`-module `ℒ'` restricting to the polarization.
This is the data over which the degree bound of [Stacks, Tag 0D4F] is uniform. -/
public structure AdmissibleDeformation (P : PolarizedFamily.{u}) where
  /-- The deformed base. -/
  S' : Scheme.{u}
  /-- The deformed total space. -/
  X' : Scheme.{u}
  /-- The thickening of the base. -/
  i : P.S ⟶ S'
  /-- The induced immersion of total spaces. -/
  i' : P.X ⟶ X'
  /-- The deformed structure morphism. -/
  f' : X' ⟶ S'
  /-- The bottom row is a thickening. -/
  isThickening : IsThickening i
  /-- The square is cartesian. -/
  isPullback : IsPullback i' P.f f' i
  /-- The deformed structure morphism is proper. -/
  isProper : IsProper f'
  /-- The deformed structure morphism is flat. -/
  flat : Flat f'
  /-- The deformed structure morphism is of finite presentation. -/
  finitePresentation : _root_.AlgebraicGeometry.FinitePresentation f'
  /-- The lifted polarization. -/
  L' : X'.Modules
  /-- The lifted polarization is invertible. -/
  invertible : IsInvertibleModule X' L'
  /-- The lifted polarization restricts to the polarization. -/
  polarization : P.L ≅ (Scheme.Modules.pullback i').obj L'

namespace AdmissibleDeformation

attribute [instance] isProper flat invertible

variable {P : PolarizedFamily.{u}} (D : P.AdmissibleDeformation)

/-- **The degree-`d` piece `𝒜'_d = (f')_* (ℒ')^{⊗ d}` of the section algebra of a
deformation.** -/
public noncomputable def sectionPiece (d : ℕ) : D.S'.Modules :=
  (Scheme.Modules.pushforward D.f').obj (tensorPowModule D.X' D.L' (d : ℤ))

/-- **The truncated section algebra of a deformation, characterised by its homogeneous pieces.**
A quasi-coherent graded `𝒪_{S'}`-algebra `A` is the truncated section algebra of `D` at `d₀` when
its degree-zero piece is the structure sheaf, its degree-`d` piece is `𝒜'_d` for every `d ≥ d₀`,
and every remaining piece vanishes.  This is
`𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d` of [Stacks, Tag 0D4F] (3). -/
public def IsTruncatedSectionAlgebra (d₀ : ℕ) (A : SheafGradedAlgebra D.S') : Prop :=
  Nonempty (A.piece 0 ≅ _root_.SheafOfModules.unit D.S'.ringCatSheaf) ∧
    (∀ d : ℕ, d₀ ≤ d → Nonempty (A.piece (d : ℤ) ≅ D.sectionPiece d)) ∧
      ∀ n : ℤ, n ≠ 0 → n < (d₀ : ℤ) → IsZero (A.piece n)

/-! ### The side conditions of [Stacks, Tag 0D4E] for the tensor powers -/

/-- The tensor powers of the lifted polarization are of finite presentation: they are invertible,
and an invertible module on a scheme is of finite presentation. -/
public theorem isFinitePresentation_tensorPowModule (d : ℕ) :
    (tensorPowModule D.X' D.L' (d : ℤ)).IsFinitePresentation :=
  Stacks.ModuleDescent.isFinitePresentation_of_isInvertible D.X'
    (tensorPowModule D.X' D.L' (d : ℤ))
    (Stacks.Ample.isInvertibleModule_tensorPowModule D.X' D.L' (d : ℤ))

/-- The tensor powers of the lifted polarization are finite locally free: invertibility is finite
local freeness of rank one, by [Stacks, Tag 0B8M]. -/
public theorem isFiniteLocallyFree_tensorPowModule (d : ℕ) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := D.X'.ringCatSheaf) (tensorPowModule D.X' D.L' (d : ℤ)) :=
  haveI := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible D.X'
    (tensorPowModule D.X' D.L' (d : ℤ))
    (Stacks.Ample.isInvertibleModule_tensorPowModule D.X' D.L' (d : ℤ))
  _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (R := D.X'.ringCatSheaf) (tensorPowModule D.X' D.L' (d : ℤ)) 1

/-- The tensor powers of the lifted polarization are flat over the deformed base: they are finite
locally free and `f'` is flat. -/
public theorem isFlatOver_tensorPowModule (d : ℕ) :
    IsFlatOver D.f'.toLRSHom.toShHom (tensorPowModule D.X' D.L' (d : ℤ)) :=
  haveI : (tensorPowModule D.X' D.L' (d : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule D.L' (d : ℤ)
  haveI := D.isFiniteLocallyFree_tensorPowModule d
  _root_.AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree D.f'
    (tensorPowModule D.X' D.L' (d : ℤ))

/-- All of `X'` is proper over `S'`, so the support of every `𝒪_{X'}`-module is proper over `S'`.
This is the hypothesis [Stacks, Tag 0D4E] asks of the support. -/
public theorem exists_isProperOver (F : D.X'.Modules) :
    letI : LocallyOfFinitePresentation D.f' := D.finitePresentation.locallyOfFinitePresentation
    ∃ Z : Closeds D.X', IsProperOver D.f' Z ∧
      _root_.SheafOfModules.supp F ⊆ (Z : Set D.X') := by
  let _ : LocallyOfFinitePresentation D.f' := D.finitePresentation.locallyOfFinitePresentation
  refine ⟨⊤, ?_, fun x _ => trivial⟩
  rw [isProperOver_iff_exists_isProper]
  exact ⟨⊥, Scheme.IdealSheafData.support_bot, inferInstance⟩

end AdmissibleDeformation

end PolarizedFamily

open PolarizedFamily PolarizedFamily.AdmissibleDeformation

/-! ### The granted inputs -/

/-- **The eventual-vanishing clause of [Stacks, Tag 0B5T], at that tag's own hypotheses.**  For a
proper, flat morphism `g : Y ⟶ T` of finite presentation over a quasi-compact base, with `M` an
invertible `𝒪_Y`-module ample relative to `g`, there is a positive degree beyond which every
higher direct image of every tensor power of `M` vanishes.

The library's form of this,
`RelativeAmpleTwistVanishing.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`,
assumes in addition that `T` is Noetherian, which [Stacks, Tag 0D4F] does not grant, and it is
itself conditional on
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase`.

This mentions one family and no deformation; in particular it does not say that the degree can be
chosen uniformly over the deformations of a family, which is the content of
[Stacks, Tag 0D4F]. -/
public def UniformHighTwistVanishing : Prop :=
  ∀ (Y T : Scheme.{u}) (g : Y ⟶ T) (M : Y.Modules) [IsInvertibleModule Y M],
    IsProper g → Flat g → _root_.AlgebraicGeometry.FinitePresentation g → CompactSpace T →
    IsRelativelyAmple g M →
      ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ p : ℤ, 0 < p →
        IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus p).obj
          (tensorPowModule Y M (d : ℤ)))

/-- **Vanishing of the higher direct images of an invertible module descends along a thickening of
the base.**  Let

```
Y --j'--> Y'
|g        |g'
T --j-->  T'
```

be cartesian with `T ⊂ T'` a thickening and `g'` proper, flat and of finite presentation, let `M'`
be an invertible `𝒪_{Y'}`-module, and let `N` be an invertible `𝒪_Y`-module isomorphic to
`(j')^* M'`.  If the higher direct images of `N^{⊗ d}` along `g` vanish, then those of
`(M')^{⊗ d}` along `g'` vanish.

This is the composite of three cited inputs of [Stacks, Tag 0D4F] that the library does not carry.
[Stacks, Tag 0B91] (1) makes `Rg'_* (M')^{⊗ d}` a perfect object of `D(𝒪_{T'})` whose formation
commutes with arbitrary base change, so that `Lj^* Rg'_* (M')^{⊗ d} = Rg_* N^{⊗ d}`;
[Stacks, Tag 0D4E] identifies the latter with a finite locally free module placed in degree `0`;
and [Stacks, Tag 0BDK] transports that conclusion back up along `j`, which is surjective on
points.  The perfection half of [Stacks, Tag 0B91] is absent outright — see the attribute strings
of `StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatPushforwardBaseChange.lean` — and the
universal property of [Stacks, Tag 0BDK] is proved only along open immersions, see the docstring
of `StacksFrontier/AlgebraicGeometry/Perfect/SingleDegreeRankOpen.lean`, whereas a thickening is a
closed immersion.

The statement is quantified over an arbitrary thickening, an arbitrary invertible module and a
single arbitrary degree.  It says nothing about ampleness and fixes no degree bound, so the
uniformity of `d₀` over the deformations of a family — the content of [Stacks, Tag 0D4F] — is not
contained in it. -/
public def VanishingDescendsAlongThickening : Prop :=
  ∀ (Y Y' T T' : Scheme.{u}) (g : Y ⟶ T) (g' : Y' ⟶ T') (j : T ⟶ T') (j' : Y ⟶ Y'),
    IsThickening j → IsPullback j' g g' j →
    IsProper g' → Flat g' → _root_.AlgebraicGeometry.FinitePresentation g' →
    ∀ (M' : Y'.Modules) [IsInvertibleModule Y' M']
      (N : Y.Modules) [IsInvertibleModule Y N],
      Nonempty (N ≅ (Scheme.Modules.pullback j').obj M') → ∀ d : ℕ,
      (∀ p : ℤ, 0 < p → IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus p).obj
          (tensorPowModule Y N (d : ℤ)))) →
      ∀ p : ℤ, 0 < p → IsZero (((Scheme.Modules.pushforward g').rightDerivedPlus p).obj
        (tensorPowModule Y' M' (d : ℤ)))

/-- **[Stacks, Tag 0D2R]: relative ampleness lifts along a thickening of the base.**  In a
cartesian square as above with `T ⊂ T'` a thickening, if `N ≅ (j')^* M'` is ample relative to `g`
then `M'` is ample relative to `g'`.

This is the implication the source uses at the start of its proof: *observe that `ℒ'` is
`f'`-ample, see Lemma 0D2R*.  The library carries it as
`Stacks.ThickeningInvertible.isRelativelyAmple_of_isRelativelyAmple_pullback`, conditional on
`Stacks.ThickeningInvertible.AmpleReflectedByThickening` — the `mp` half of [Stacks, Tag 09MW],
which is genuinely not proved there — and stated for the restriction `(i)^* ℒ'` rather than for a
module isomorphic to it.  It is granted here in the form the tag's data provides, quantified over
an arbitrary thickening and arbitrary invertible modules; it fixes no degree and says nothing
about direct images, so it contains no part of the uniformity. -/
public def RelativelyAmpleLiftsAlongThickening : Prop :=
  ∀ (Y Y' T T' : Scheme.{u}) (g : Y ⟶ T) (g' : Y' ⟶ T') (j : T ⟶ T') (j' : Y ⟶ Y'),
    IsThickening j → IsPullback j' g g' j →
    ∀ (M' : Y'.Modules) [IsInvertibleModule Y' M']
      (N : Y.Modules) [IsInvertibleModule Y N],
      Nonempty (N ≅ (Scheme.Modules.pullback j').obj M') →
      IsRelativelyAmple g N → IsRelativelyAmple g' M'

/-- **The truncated section algebra exists as a quasi-coherent graded algebra.**  This is the
assertion of [Stacks, Tag 01VJ] (5) that `𝒪_{S'} ⊕ ⨁_{d ≥ d₀} (f')_* (ℒ')^{⊗ d}` is a
quasi-coherent graded `𝒪_{S'}`-algebra.

The library carries the homogeneous pieces, `Stacks.RelativeAmple.gradedDirectImage`, but not the
multiplication: the docstring of
`StacksFrontier/AlgebraicGeometry/RelativeAmple/GradedDirectImage.lean` records that the graded
algebra is never assembled, the available product on tensor powers
(`Stacks.SheafOfModules.TensorPower.laurentAlgebra`) being graded by all of `ℤ` with non-vanishing
negative pieces.

This asserts existence of an algebra with prescribed pieces, for one deformation and one
truncation degree; it says nothing about finite presentation, about relative `Proj`, or about a
uniform degree. -/
public def TruncatedSectionAlgebraExists : Prop :=
  ∀ (P : PolarizedFamily.{u}) (D : P.AdmissibleDeformation) (d₀ : ℕ), 0 < d₀ →
    ∃ A : SheafGradedAlgebra D.S', D.IsTruncatedSectionAlgebra d₀ A

/-- **Conclusion (3) of [Stacks, Tag 0D4F] for a single deformation.**  The truncated section
algebra is of finite presentation as a sheaf of `𝒪_{S'}`-algebras — the notion of
[Stacks, Section 01PD] — that is, over every affine open `U` of `S'` the ring map
`Γ(S', U) ⟶ Γ(U, 𝒜')` is of finite presentation.

The source proves this affine-locally on `S'` from [Stacks, Tag 0B5T] (the finite generation
clause), the limit descent of [Stacks, Tags 01ZR, 0B8W, 081F, 04AI, 09MT] and the algebra chain
[Stacks, Tags 00IS, 0561, 0519, 0D46, 00F4].  That argument uses neither the thickening nor the
uniformity of `d₀`: it sees only `X' ⟶ S'`, the relative ampleness of `ℒ'` and the local freeness
of the pieces, which is exactly what is hypothesised here.  The limit inputs are all proved
unconditionally; the finite generation clause of [Stacks, Tag 0B5T] is not, being blocked on
clause (5) of [Stacks, Tag 01YS] — see the docstring of
`StacksFrontier/AlgebraicGeometry/ProperAmpleCohomology/Basic.lean`. -/
public def TruncatedSectionAlgebraFinitePresentation : Prop :=
  ∀ (P : PolarizedFamily.{u}) (D : P.AdmissibleDeformation) (d₀ : ℕ), 0 < d₀ →
    IsRelativelyAmple D.f' D.L' →
    (∀ d : ℕ, d₀ ≤ d →
      _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := D.S'.ringCatSheaf) (D.sectionPiece d)) →
    ∀ A : SheafGradedAlgebra D.S', D.IsTruncatedSectionAlgebra d₀ A →
      ∀ U : D.S'.Opens, IsAffineOpen U → RingHom.FinitePresentation (A.strHom U)

/-- **Conclusion (4) of [Stacks, Tag 0D4F] for a single deformation.**  There is a canonical
isomorphism `r' : X' ⟶ Proj_{S'}(𝒜')` over `S'`.

The source obtains it from [Stacks, Tags 07ZJ, 01VJ, 01O9, 0C6J]: the inclusion of the truncated
algebra into the full graded direct image algebra is an isomorphism in degrees `≥ d₀`, hence
induces an isomorphism of relative `Proj` ([Stacks, Tag 07ZJ]), and `X'` is the relative `Proj` of
the full algebra ([Stacks, Tag 0C6J]).  The library carries [Stacks, Tag 07ZJ] as
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.isIso_relativeMapHom_of_eventually_isIso` and
[Stacks, Tag 0C6J] as `Stacks.RelativeAmple.isIso_relativeAmpleProjHom` (for the full algebra
`Stacks.RelativeAmple.directImageAlgebra` and the morphism
`Stacks.RelativeAmple.relativeAmpleProjHom` of [Stacks, Tag 01VJ]); the comparison of an
arbitrary truncated algebra `A` with the full one is not supplied. -/
public def RelativeProjIdentification : Prop :=
  ∀ (P : PolarizedFamily.{u}) (D : P.AdmissibleDeformation) (d₀ : ℕ), 0 < d₀ →
    IsRelativelyAmple D.f' D.L' →
    ∀ A : SheafGradedAlgebra D.S', D.IsTruncatedSectionAlgebra d₀ A →
      ∃ r : D.X' ⟶ (relativeProj A).scheme,
        IsIso r ∧ r ≫ (relativeProj A).toBase = D.f'

/-- **Conclusion (5) of [Stacks, Tag 0D4F] for a single deformation.**  The canonical isomorphism
`r'` of conclusion (4) pulls `𝒪_{Proj_{S'}(𝒜')}(1)` back to `ℒ'`.

No comparison map of that shape exists in the library: the graded map `θ` of
[Stacks, Tag 01O9] is not constructed, the second claim of [Stacks, Tag 01QI] — its absolute
analogue — is recorded as absent in
`StacksFrontier/AlgebraicGeometry/SectionRingProjGoodOpen/Basic.lean`, and the only global statement
of the degree-one case is for the canonical map out of a symmetric algebra,
`Stacks.Tag07ZRVeryAmple.twistOneIsoPullback`. -/
public def TwistIdentification : Prop :=
  ∀ (P : PolarizedFamily.{u}) (D : P.AdmissibleDeformation) (d₀ : ℕ), 0 < d₀ →
    IsRelativelyAmple D.f' D.L' →
    ∀ A : SheafGradedAlgebra D.S', D.IsTruncatedSectionAlgebra d₀ A →
      ∀ r : D.X' ⟶ (relativeProj A).scheme, IsIso r →
        r ≫ (relativeProj A).toBase = D.f' →
        ∀ hcoc : IsNestedCocycle A 1,
          Nonempty ((Scheme.Modules.pullback r).obj (gluedTwist A 1 hcoc) ≅ D.L')

end Stacks.AlgebraicGeometry.ProjectiveDeformation
