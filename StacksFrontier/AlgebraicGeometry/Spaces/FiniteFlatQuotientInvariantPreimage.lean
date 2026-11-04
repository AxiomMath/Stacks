module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientKernelPair
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.OpenSaturation

/-!
# An invariant open is the full preimage of its image under a quotient map

Let `(U, R, s, t, c)` be a groupoid scheme over `S` and let `f : U ⟶ M` be a morphism of
`S`-schemes whose kernel pair is the pair `(t, s)`, that is `R = U ×_M U`. Then the fibres of
`f` on points are exactly the `R`-equivalence classes, so an `R`-invariant subset of `U` is the
preimage under `f` of its image. Consequently, if the image of an invariant open `V` is an open
`W` of `M`, the restriction of `f` over `W` *is* the morphism `V ⟶ W`, and finite local freeness
of `f` can be read off a family of such restrictions covering `M`.

This is the second half of the finite-local-freeness clause of the conclusion of Stacks 07S6:
the first half, that finite local freeness is Zariski local on the target, is the
instance for `Stacks.Morphisms.IsFiniteLocallyFree`, and what the source proof adds is the
identification `f⁻¹(U_i/R_i) = U_i` of the preimages of the members of the covering of the
quotient. **Nothing here is Stacks 07S6 and nothing here carries that tag**: the quotient
scheme `M`, the morphism `f`, the open images `W` and the finite locally free morphisms
`V ⟶ W` are all hypotheses, and producing them is the content of that proposition.

## Main results

* `AlgebraicGeometry.exists_arrow_of_base_eq_of_isPullback`: **the kernel-pair property read on
  points.** Two points of `U` with the same image under `f` are the target and the source of a
  point of `R`.
* `AlgebraicGeometry.preimage_image_eq_of_isInvariantSet`: an `R`-invariant subset of `U` is the
  preimage under `f` of its image.
* `AlgebraicGeometry.preimage_eq_of_isInvariantOpen`: the same for an invariant open whose
  image is open, as an equality of opens of `U`.
* `AlgebraicGeometry.morphismRestrict_mem_of_preimage_eq`: a morphism property holding of a
  morphism `V ⟶ W` over the inclusion of `W` holds of the restriction of `f` over `W`, when `V`
  is the preimage of `W`.
* `AlgebraicGeometry.isFiniteLocallyFree_of_isInvariantOpen_cover`: **the finite-local-freeness
  clause of the conclusion of Stacks 07S6, reduced to the local quotients.** A morphism whose
  kernel pair is the given relation is finite locally free as soon as the images of a family of
  invariant opens are a covering of `M` by opens over which `f` is finite locally free.

## Implementation notes

The kernel-pair hypothesis of every statement here is the conclusion of
`AlgebraicGeometry.isPullback_of_quotientSheaf_isRepresented`, which is why that module is
imported although no declaration of it is named in a proof.

The point-level kernel-pair property is the only place where the geometry of schemes enters:
it needs that the underlying set of a fibre product of schemes surjects onto the fibre product
of the underlying sets, `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`, which is
not formal and is false for general locally ringed spaces. The Cartesian square is transported
from schemes over `S` to schemes by `CategoryTheory.IsPullback.map` along
`CategoryTheory.Over.forget`, and the comparison with the chosen fibre product is
`CategoryTheory.IsPullback.isoPullback`, whose two equations
`CategoryTheory.IsPullback.isoPullback_inv_fst` and `..._inv_snd` are read on the point `z`
produced there. Reading them on points is done by rewriting inside a composite and then
appealing to definitional equality of `(g ≫ h).base z` with `h.base (g.base z)`, not by `simp`,
which normalizes the two sides of those equations to each other and proves nothing.

Only the inclusion of the preimage of the image in the invariant set has content; the reverse
inclusion is `Set.subset_preimage_image`. Invariance is used in exactly the direction it is
stated: the arrow produced from a point of the invariant set and an arbitrary point with the
same image has its source in the set, hence its target there too.

The restriction `f ∣_ W` is identified with the given morphism `V ⟶ W` by cancelling the
inclusion of `W`, which is a monomorphism, against `AlgebraicGeometry.morphismRestrict_ι`. The
equality of opens is eliminated by `subst` before the identification, so no `eqToHom` appears;
the statement is therefore about an arbitrary morphism property and is independent of finite
local freeness.

## References

* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry

/-- **The kernel-pair property read on points.** If the target and source maps of a groupoid
scheme form the kernel pair of a morphism `f : U ⟶ M` of `S`-schemes, then any two points of
`U` with the same image under `f` are the target and the source of a single point of the arrow
scheme.

The underlying set of the fibre product `U ×_M U` surjects onto the fibre product of the
underlying sets, and the Cartesian square identifies the arrow scheme with that fibre
product. -/
theorem exists_arrow_of_base_eq_of_isPullback {S : Scheme.{u}} (G : GroupoidScheme S)
    {M : Over S} (f : G.objects ⟶ M) (hpb : IsPullback G.target G.source f f)
    (x y : G.objects.left) (h : f.left.base x = f.left.base y) :
    ∃ r : G.arrows.left, G.target.left.base r = x ∧ G.source.left.base r = y := by
  have hpb' : IsPullback G.target.left G.source.left f.left f.left := hpb.map (Over.forget S)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  exact ⟨hpb'.isoPullback.inv.base z,
    (congrArg (·.base z) hpb'.isoPullback_inv_fst).trans hz1,
    (congrArg (·.base z) hpb'.isoPullback_inv_snd).trans hz2⟩

/-- **An invariant subset is the preimage of its image.** If the target and source maps of a
groupoid scheme form the kernel pair of a morphism `f : U ⟶ M` of `S`-schemes, then an
`R`-invariant subset of `U` in the sense of Tag 03BC is the preimage under `f` of its
image. -/
theorem preimage_image_eq_of_isInvariantSet {S : Scheme.{u}} (G : GroupoidScheme S)
    {M : Over S} (f : G.objects ⟶ M) (hpb : IsPullback G.target G.source f f)
    {W : Set G.objects.left} (hW : IsInvariantSet G W) :
    f.left.base ⁻¹' (f.left.base '' W) = W := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨r, hr1, hr2⟩ := exists_arrow_of_base_eq_of_isPullback G f hpb x y hxy.symm
  rw [← hr1]
  exact hW r (hr2 ▸ hy)

/-- **An invariant open is the preimage of its image.** If the target and source maps of a
groupoid scheme form the kernel pair of `f : U ⟶ M` and the image of an `R`-invariant open `V`
of `U` is the underlying set of an open `W` of `M`, then `V` is the preimage of `W`. -/
theorem preimage_eq_of_isInvariantOpen {S : Scheme.{u}} (G : GroupoidScheme S)
    {M : Over S} (f : G.objects ⟶ M) (hpb : IsPullback G.target G.source f f)
    {V : G.objects.left.Opens} (hV : IsInvariantOpen G V) {W : M.left.Opens}
    (hW : (W : Set M.left) = f.left.base '' (V : Set G.objects.left)) :
    f.left ⁻¹ᵁ W = V := by
  refine TopologicalSpace.Opens.ext ?_
  rw [show ((f.left ⁻¹ᵁ W : G.objects.left.Opens) : Set G.objects.left) =
    f.left.base ⁻¹' (W : Set M.left) from rfl, hW]
  exact preimage_image_eq_of_isInvariantSet G f hpb hV

/-- A morphism property which holds of a morphism `V ⟶ W` compatible with `f` over the
inclusion of `W` holds of the restriction of `f` over `W`, provided `V` is the preimage of `W`.

The two morphisms are then equal, by cancelling the monomorphism `W.ι` against
`AlgebraicGeometry.morphismRestrict_ι`. -/
theorem morphismRestrict_mem_of_preimage_eq (P : MorphismProperty Scheme.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens) {V : X.Opens} (hV : f ⁻¹ᵁ W = V)
    (g : V.toScheme ⟶ W.toScheme) (hg : g ≫ W.ι = V.ι ≫ f) (hP : P g) : P (f ∣_ W) := by
  subst hV
  have hmono : Mono W.ι := inferInstance
  have hgr : f ∣_ W = g := (cancel_mono W.ι).mp (by rw [morphismRestrict_ι, hg])
  rw [hgr]
  exact hP

/-- **The finite-local-freeness clause of Stacks 07S6, reduced to the local quotients.** Let
`(U, R, s, t, c)` be a groupoid scheme over `S` and `f : U ⟶ M` a morphism of `S`-schemes whose
kernel pair is `(t, s)`. Suppose given a family of `R`-invariant opens `V i` of `U`, opens
`W i` of `M` covering `M` whose underlying sets are the images of the `V i`, and finite locally
free morphisms `g i : V i ⟶ W i` compatible with `f`. Then `f` is finite locally free.

The invariant opens are the preimages of the `W i`, so each `g i` *is* the restriction of `f`
over `W i`, and finite local freeness is Zariski local on the target. -/
theorem isFiniteLocallyFree_of_isInvariantOpen_cover {S : Scheme.{u}} (G : GroupoidScheme S)
    {M : Over S} (f : G.objects ⟶ M) (hpb : IsPullback G.target G.source f f)
    {ι : Type*} (V : ι → G.objects.left.Opens) (hV : ∀ i, IsInvariantOpen G (V i))
    (W : ι → M.left.Opens) (hiSup : iSup W = ⊤)
    (hW : ∀ i, (W i : Set M.left) = f.left.base '' (V i : Set G.objects.left))
    (g : ∀ i, (V i).toScheme ⟶ (W i).toScheme)
    (hg : ∀ i, g i ≫ (W i).ι = (V i).ι ≫ f.left)
    (hflf : ∀ i, IsFiniteLocallyFree (g i)) : IsFiniteLocallyFree f.left :=
  IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFiniteLocallyFree) W hiSup fun i ↦
    morphismRestrict_mem_of_preimage_eq (@IsFiniteLocallyFree) f.left (W i)
      (preimage_eq_of_isInvariantOpen G f hpb (hV i) (hW i)) (g i) (hg i) (hflf i)

end AlgebraicGeometry

end

end
