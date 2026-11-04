module

public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 01VK: relative ampleness over an affine base is ampleness

Stacks Tag 01VK says that for `f : X ⟶ S` a morphism of schemes with `S` affine and `L` an
invertible `𝒪_X`-module, `L` is ample relative to `f` if and only if `L` is ample on `X`.

## Main results

* `Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`: **Stacks Tag 01VK.**
* `Stacks.RelativeAmpleAffineBase.isAmple_of_isAmple_modulePullback`: ampleness descends along an
  isomorphism of schemes — if `i^* L` is ample for `i` invertible, then `L` is ample.
* `Stacks.RelativeAmpleAffineBase.isAffineHom_preimage_ι`: over an affine base, the open immersion
  of the preimage of an affine open is an affine morphism.

## The route

The source proves this as a corollary of Stacks Tag 01VJ — relative ampleness may be checked on an
affine open covering of the base — whose own proof goes through relative `Proj` and is not
available here. It is not needed: both implications are elementary once ampleness is known to pull
back along an affine morphism, which `Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`
proves unconditionally.

**Ampleness implies relative ampleness.** Quasi-compactness of `f` over an affine base is
quasi-compactness of `X`, which ampleness provides; an affine scheme is a quasi-separated compact
space, so this is Mathlib's `AlgebraicGeometry.quasiCompact_iff_compactSpace`. For an affine open
`V ⊆ S`, the open immersion
`(f⁻¹V).ι : f⁻¹V ⟶ X` is the base change of `V.ι : V ⟶ S` along `f`
(`AlgebraicGeometry.isPullback_morphismRestrict`), and `V.ι` is an affine morphism because both
`V` and `S` are affine schemes; affine morphisms are stable under base change, so `(f⁻¹V).ι` is
affine and Tag 0B3E applies on the nose. This is where affineness of `S` is used, and it is the
only place: without it `V.ι` need not be affine, and the restriction of an ample module to
`f⁻¹V` need not be ample.

**Relative ampleness implies ampleness.** Taking `V = ⊤`, which is affine because `S` is, the
hypothesis gives ampleness of `L` restricted to `f⁻¹(⊤) = ⊤`, and `⊤ ⟶ X` is an isomorphism. So
all that is owed is that ampleness descends along an isomorphism, which is Tag 0B3E again —
applied to the *inverse* isomorphism, since an isomorphism is an affine morphism — together with
the identification of `(i⁻¹)^* (i^* L)` with `L`. That identification is pseudofunctoriality of the
module pullback, `Stacks.PullbackPseudofunctor.modulePullbackCompIso` and
`modulePullbackIdIso`, and the transport of ampleness across it is
`Stacks.RelativeVeryAmple.isAmple_congr`.

## Two apparent obstructions

Two obstructions might be expected here, and neither applies:

* "`IsAmple` is not known to be isomorphism-invariant — there is no `isAmple_congr`". There is:
  `Stacks.RelativeVeryAmple.isAmple_congr`, in
  `StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPower.lean`. The module documentation
  of `StacksFrontier/AlgebraicGeometry/RelativeAmple/Basic.lean` still records it as unavailable.
* Stacks Tag 0H78 — that the nonvanishing locus of a pulled-back section is the preimage of the
  nonvanishing locus — looks as if it must be carried as the premise `SectionPullbackCompatible` for
  the converse. It is proved, unconditionally and at the generality of a morphism of locally ringed
  spaces, as `Stacks.NonvanishingPullback.preimage_nonvanishingLocus_lrs`; the scheme form
  `Stacks.NonvanishingPullback.sectionPullbackCompatible` is what Tag 0B3E consumes.

Neither direction here needs Stacks Tag 01VJ, Stacks Tag 01Q3, or the premise
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing` that the general case of Tag 0B3E still stands
on.

## Implementation notes

**Which Tag 01PS.** Two declarations in this repository carry the Tag 01PS attribute, with no
comparison between them: `AlgebraicGeometry.Scheme.Modules.IsAmple` in
`StacksFrontier/AlgebraicGeometry/Ample/Defs.lean` and `Stacks.Ample.IsAmple` in
`StacksFrontier/AlgebraicGeometry/AmpleWire/Basic.lean`. Everything here is stated over the latter,
because the library's Tag 01VH, `Stacks.RelativeAmple.IsRelativelyAmple`, is defined over it.

**The isomorphism `(i⁻¹)^* (i^* L) ≅ L` is built on a ringed space.** The module pullback is a
construction on morphisms of ringed spaces, so the composition law `i⁻¹ ≫ i = 𝟙` has to be
transported from schemes; it is, by `congrArg`, since `AlgebraicGeometry.Scheme.Hom.comp_toLRSHom`
and `AlgebraicGeometry.LocallyRingedSpace.comp_toShHom` are both `rfl`.

## References

* [EGA II, Corollary 4.6.6]
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample

universe u

namespace Stacks.RelativeAmpleAffineBase

/-! ### Ampleness descends along an isomorphism of schemes -/

/-- **`b^* (a^* M) ≅ M` whenever `b ≫ a` is the identity**, for morphisms of ringed spaces. This is
pseudofunctoriality of the module pullback,
`Stacks.PullbackPseudofunctor.modulePullbackCompIso`, composed with its unit
`Stacks.PullbackPseudofunctor.modulePullbackIdIso`. -/
def modulePullbackCompIdIso {A B : RingedSpace.{u, u}} (a : A ⟶ B) (b : B ⟶ A)
    (h : b ≫ a = 𝟙 B) (M : SheafOfModules.{u} (structureSheafRing B)) :
    (modulePullback b).obj ((modulePullback a).obj M) ≅ M :=
  ((Stacks.PullbackPseudofunctor.modulePullbackCompIso a b).app M).symm ≪≫
    eqToIso (congrArg (fun m : B ⟶ B => (modulePullback m).obj M) h) ≪≫
      (Stacks.PullbackPseudofunctor.modulePullbackIdIso B).app M

/-- **`(i⁻¹)^* (i^* L) ≅ L` for an isomorphism of schemes `i`.**
`Stacks.RelativeAmpleAffineBase.modulePullbackCompIdIso` on the underlying morphisms of ringed
spaces; the composition law is transported from schemes by `congrArg`. -/
def modulePullbackInvIso {X Y : Scheme.{u}} (i : X ⟶ Y) [IsIso i] (L : Y.Modules) :
    Stacks.AmpleLocallyClosed.pullbackModule (inv i)
        (Stacks.AmpleLocallyClosed.pullbackModule i L) ≅ L :=
  modulePullbackCompIdIso i.toLRSHom.toShHom (inv i).toLRSHom.toShHom
    (congrArg (fun g : Y ⟶ Y => g.toLRSHom.toShHom) (IsIso.inv_hom_id i)) L

/-- **Ampleness descends along an isomorphism of schemes.** If `i : X ⟶ Y` is an isomorphism and
`i^* L` is ample on `X`, then `L` is ample on `Y`.

An isomorphism is an affine morphism, so
`Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom` applied to `i⁻¹` turns ampleness of
`i^* L` into ampleness of `(i⁻¹)^* (i^* L)`, and `Stacks.RelativeVeryAmple.isAmple_congr` moves it
onto `L` along `Stacks.RelativeAmpleAffineBase.modulePullbackInvIso`. -/
theorem isAmple_of_isAmple_modulePullback {X Y : Scheme.{u}} (i : X ⟶ Y) [IsIso i]
    (L : Y.Modules) [IsInvertibleModule Y L]
    (h : IsAmple X (Stacks.AmpleLocallyClosed.pullbackModule i L)) : IsAmple Y L :=
  (Stacks.RelativeVeryAmple.isAmple_congr _ _ (modulePullbackInvIso i L)).mp
    (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom (inv i) _ h)

/-- The open immersion of the top open of a scheme is an isomorphism, by
`AlgebraicGeometry.Scheme.topIso`. Stated rather than registered as an instance, since it concerns
a declaration of Mathlib's. -/
theorem isIso_ι_top (X : Scheme.{u}) : IsIso (⊤ : X.Opens).ι :=
  ⟨X.topIso.inv, X.ι_toIso_inv, X.toIso_inv_ι⟩

/-! ### Preimages of affine opens over an affine base -/

/-- **Over an affine base, the open immersion of the preimage of an affine open is an affine
morphism.** It is the base change of `V.ι : V ⟶ S` along `f`
(`AlgebraicGeometry.isPullback_morphismRestrict`), `V.ι` is affine because `V` and `S` are both
affine schemes, and affine morphisms are stable under base change. -/
@[ega "II 1.6.2" "(iii), special case"]
theorem isAffineHom_preimage_ι {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (V : S.Opens)
    (hV : IsAffineOpen V) : IsAffineHom (f ⁻¹ᵁ V).ι := by
  have : IsAffine V.toScheme := hV
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_morphismRestrict f V) inferInstance

/-! ### Stacks Tag 01VK -/

/-- **Stacks Tag 01VK.** Over an affine base, an invertible `𝒪_X`-module is ample relative to
`f : X ⟶ S` if and only if it is ample on `X`.

Both implications are `Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`, the
unconditional case of Stacks Tag 0B3E for an affine morphism. Forwards, at `V = ⊤`: the hypothesis
gives ampleness of the restriction of `L` to `f⁻¹(⊤) = ⊤`, and
`Stacks.RelativeAmpleAffineBase.isAmple_of_isAmple_modulePullback` descends it along the
isomorphism `⊤ ⟶ X`. Backwards: quasi-compactness of `f` over an affine base is quasi-compactness
of `X`, and on each affine open `V` of `S` the open immersion of `f⁻¹V` is an affine morphism by
`Stacks.RelativeAmpleAffineBase.isAffineHom_preimage_ι`. -/
@[stacks 01VK, ega "II 4.6.6"]
theorem isRelativelyAmple_iff_isAmple {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔ IsAmple X L := by
  constructor
  · intro h
    have := isIso_ι_top X
    exact isAmple_of_isAmple_modulePullback (⊤ : X.Opens).ι L (h.2 ⊤ (isAffineOpen_top S))
  · intro h
    refine ⟨(quasiCompact_iff_compactSpace f).mpr h.1, fun V hV => ?_⟩
    have := isAffineHom_preimage_ι f V hV
    exact Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom (f ⁻¹ᵁ V).ι L h

end Stacks.RelativeAmpleAffineBase

end
