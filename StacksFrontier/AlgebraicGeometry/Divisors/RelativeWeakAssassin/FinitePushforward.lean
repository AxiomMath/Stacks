module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.Pushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.BaseChange

/-!
# The relative weak assassin of a finite direct image

Let `f : X ⟶ S` be a morphism of schemes, let `i : Z ⟶ X` be a finite morphism and let `F` be a
quasi-coherent `𝒪_Z`-module.  The relative weak assassin `WeakAss_{X/S}(i_* F)` is the image
under `i` of `WeakAss_{Z/S}(F)`.

## Main results

* `AlgebraicGeometry.weaklyAssociatedPoints_congr`: isomorphic modules have the same weakly
  associated points.
* `AlgebraicGeometry.pullbackPushforwardFiberIso`: for a base-change square with affine right
  edge, the comparison isomorphism `g^* f_* 𝓕 ≅ f'_* (g')^* 𝓕`.
* `AlgebraicGeometry.relativeWeaklyAssociatedPoints_pushforward_eq_image` computes the relative
  weak assassin of a finite direct image.

## Implementation notes

The structure morphism of the source over the base is the composite `i ≫ f`, so over a point
`s` of the base the fibre of `i ≫ f` is the base change of `i` along the fibre inclusion of
`f`; this is `AlgebraicGeometry.Scheme.Hom.isPullback_fiberMap`.  The restriction of `i_* F` to
the fibre of `f` is then the direct image, along that base change, of the restriction of `F` —
this is affine base change, the second assertion of Stacks Tag 02KG, available here as
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom` — and
Stacks Tag 05EZ computes the weakly associated points of that direct image.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 05EZ](https://stacks.math.columbia.edu/tag/05EZ)
* [Stacks Project, Tag 0CUD](https://stacks.math.columbia.edu/tag/0CUD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Isomorphic sheaves of modules on a scheme have the same weakly associated points. -/
theorem weaklyAssociatedPoints_congr {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    Stacks.Divisors.weaklyAssociatedPoints F = Stacks.Divisors.weaklyAssociatedPoints G :=
  Set.Subset.antisymm
    (weaklyAssociatedPoints_subset_of_mono e.hom)
    (weaklyAssociatedPoints_subset_of_mono e.inv)

/-- **Affine base change**, the second assertion of Stacks Tag 02KG, as an isomorphism: for a
cartesian square of schemes whose right-hand edge `f` is affine and a quasi-coherent module
`𝓕` on its upper-right corner, the canonical morphism `g^* f_* 𝓕 ⟶ f'_* (g')^* 𝓕` is an
isomorphism. -/
noncomputable def pullbackPushforwardFiberIso (d : BaseChangeDiagram.{u}) [IsAffineHom d.f] :
    (Scheme.Modules.pullback d.g).obj ((Scheme.Modules.pushforward d.f).obj d.F) ≅
      (Scheme.Modules.pushforward d.f').obj d.pulledBack :=
  haveI := d.isQuasicoherent
  haveI := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    d.isPullback d.F
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans d.isPullback.w).app d.F)

/-- The weakly associated points of the restriction of a finite direct image to a fibre of the
base. -/
private theorem fiberWeaklyAssociatedPoints_pushforward_eq_image
    {Z X S : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsFinite i]
    (F : Z.Modules) [F.IsQuasicoherent] (s : S) :
    (f.fiberι s) ''
        Stacks.Divisors.weaklyAssociatedPoints
          ((Scheme.Modules.pullback (f.fiberι s)).obj
            ((Scheme.Modules.pushforward i).obj F)) =
      i '' ((i ≫ f).fiberι s ''
        Stacks.Divisors.weaklyAssociatedPoints
          ((Scheme.Modules.pullback ((i ≫ f).fiberι s)).obj F)) := by
  have hpull := (f.isPullback_fiberMap i s).flip
  let d : BaseChangeDiagram := {
    X' := (i ≫ f).fiber s, X := Z, S' := f.fiber s, S := X
    g' := (i ≫ f).fiberι s, f' := f.fiberMap i s, f := i, g := f.fiberι s
    isPullback := hpull, F := F
  }
  let : IsFinite d.f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpull ‹IsFinite i›
  let : IsAffineHom d.f := by change IsAffineHom i; infer_instance
  let : d.F.IsQuasicoherent := by
    change F.IsQuasicoherent
    infer_instance
  let : d.pulledBack.IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback d.g' d.F inferInstance
  rw [weaklyAssociatedPoints_congr (pullbackPushforwardFiberIso d),
    weaklyAssociatedPoints_pushforward_eq_image_of_isFinite d.f' d.pulledBack,
    Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ ↦ ?_
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun g ↦ g x) hpull.w.symm

/-- **Stacks Project, Tag 0CUD.**  The relative weak assassin of a finite direct image is the
image of the relative weak assassin on the source. -/
@[stacks 0CUD]
theorem relativeWeaklyAssociatedPoints_pushforward_eq_image
    {Z X S : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsFinite i]
    (F : Z.Modules) [F.IsQuasicoherent] :
    relativeWeaklyAssociatedPoints f ((Scheme.Modules.pushforward i).obj F) =
      i '' relativeWeaklyAssociatedPoints (i ≫ f) F := by
  unfold relativeWeaklyAssociatedPoints
  rw [Set.image_iUnion]
  exact Set.iUnion_congr fun s ↦
    fiberWeaklyAssociatedPoints_pushforward_eq_image f i F s

end AlgebraicGeometry

end
