module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineStandardFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentReduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.SigmaMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending affine morphisms along an fpqc covering of an affine base

Let `S` be an affine scheme, let `{X i ⟶ S}` be an fpqc covering family and let `D` be a descent
datum relative to that family, in the sense of Stacks 023W, each of whose component morphisms
`V i ⟶ X i` is affine. Then `D` is effective in the sense of Stacks 02VU: it is isomorphic to the
canonical descent datum of a scheme over `S`. This is
[Stacks, Tag 0245](https://stacks.math.columbia.edu/tag/0245) over an affine base.

The source's proof has two steps, and both are available in that generality. Affineness of a
morphism is Zariski local on the base and stable under base change, so
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffine` — the fpqc case of Stacks 02W3 over
an affine base — reduces an arbitrary fpqc covering of the affine base to a single surjective flat
morphism of affine schemes. There faithfully flat descent of modules, Stacks 023N, descends the
algebra, which is
`AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_surjective_of_flat`.

## Main results

* `AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isAffineHom`: **Stacks 0245 over an
  affine base.**

## Implementation notes

*Why the base must be affine.* Stacks 0245 is stated for an arbitrary base, and the reduction it
rests on is available only over an affine one: the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentReduction` record that the passage to an
arbitrary base glues the schemes descended over the affine opens of the base along
[Stacks, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH), which needs a coherent choice of
the descended scheme over every affine open, and that this is not available. So the affineness of
`S` is a genuine restriction and the tag is carried in phrase form.

*The universe of the index type.* The index type of the covering family lies in the universe of
the schemes, as throughout the reduction: that is what the refinement step of Stacks 022E and the
pullback functor of Stacks 02VS are stated for.

*Closure under finite disjoint unions.* The reduction asks that `IsAffineHom` be closed under
finite disjoint unions, which is `AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap` once
affineness of a morphism is known to be Zariski local on the base. That locality is not a global
instance in this development, so it is named from the affine-local property of `IsAffineHom`, as
elsewhere in `StacksDraft.AlgebraicGeometry.Descent`.

*Why no detour through ind-quasi-affine morphisms.* An affine morphism is quasi-affine, hence
ind-quasi-affine, so the conclusion is also a special case of
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isIndQuasiAffineHom`, Stacks 0APK over
an affine base. The affine argument is taken directly instead, because it is the one the source
gives for this statement and because Stacks 0APK is proved from it.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace DescentData

/-- **[Stacks, Tag 0245](https://stacks.math.columbia.edu/tag/0245) over an affine base.** Let `S`
be an affine scheme, let `{X i ⟶ S}` be an fpqc covering family and let `D` be a descent datum
relative to it whose structure morphism over each `X i` is affine. Then `D` is effective: it is
isomorphic to the canonical descent datum of a scheme over `S`. -/
@[stacks 0245 "the case of an affine base",
  sga "3 IX 2.3" "partial",
  sga "3 VIII 1.7.2" "(ii), special case",
  sga "3 XXIV 3.11.2" "special case"]
theorem isFamilyEffective_of_forall_isAffineHom {ι : Type u} {S : Scheme.{u}} [IsAffine S]
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f) (hP : ∀ i, IsAffineHom (D.obj i).hom) :
    D.IsFamilyEffective :=
  have : IsZariskiLocalAtTarget (@IsAffineHom.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  isFamilyEffective_of_isAffine (P := @IsAffineHom)
    (fun a ha ↦ IsZariskiLocalAtTarget.sigmaMap a ha)
    (fun a hsurj hflat E hPE ↦
      DescentDatum.isEffective_of_isAffineHom_of_surjective_of_flat (a := a) hsurj hflat E hPE)
    f hf D hP

end DescentData

end AlgebraicGeometry

end
