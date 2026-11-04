module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentative
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmple
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.Separated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfect objects as bounded complexes of finite locally free modules, without a stand-in

In the namespace `Stacks.Perfect.BoundedLocallyFreeComplexes`,
`exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty` states [Stacks, Tag 0F8F] for a
quasi-compact and quasi-separated scheme with the resolution property, and it goes through
[Stacks, Tag 0F8C] to get an affine diagonal.  There are classes of schemes for which the diagonal
is affine for an unrelated reason, and on those the route through Tag 0F8C — and hence through the
converse of [Stacks, Tag 0F8B] — is not needed at all.  This file records those special cases, each
a special case of Tag 0F8F.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_iso_of_isSeparated`:
  the separated case.  A separated scheme has a closed, hence affine, diagonal, so Tag 0F8C is
  not needed at all.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_iso_of_isNoetherian`:
  the Noetherian case, from the Noetherian case of Tag 0F8C
  (`AlgebraicGeometry.isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian`), which is
  where that tag is unconditional.
* `AlgebraicGeometry.hasResolutionProperty_of_isAffine`: an affine scheme has the resolution
  property, its structure sheaf being ample.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_iso_of_isAmple`:
  the case of a scheme carrying an ample invertible module, where both the resolution property
  and separatedness come from the ample module, and
  `Stacks.Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_iso_of_isAffine`
  and `Stacks.Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_iso_spec`:
  the affine case, where every hypothesis on the scheme is discharged.

## Implementation notes

Quasi-separatedness of a separated scheme and affineness of its diagonal are both instances:
`AlgebraicGeometry.Scheme.IsSeparated` asks that `pullback.diagonal (terminal.from X)` be a
closed immersion, and a closed immersion is affine.  So the separated case is
`exists_boundedFiniteLocallyFree_iso_of_affineDiagonal` with no work.

Ampleness is `Stacks.Ample.IsAmple`, which contains quasi-compactness of the scheme; the
resolution property is [Stacks, Tag 0F87] and separatedness is [Stacks, Tag 09MP], the latter
stated for `AlgebraicGeometry.Scheme.Modules.IsAmple` and transported by
`Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple`.

## References

* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
* [Stacks Project, Tag 0F87](https://stacks.math.columbia.edu/tag/0F87)
* [Stacks Project, Tag 09MP](https://stacks.math.columbia.edu/tag/09MP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes

universe u

namespace AlgebraicGeometry

/-- **An affine scheme has the resolution property.**  Its structure sheaf is an ample invertible
module, and a scheme with an ample invertible module has the resolution property by
[Stacks, Tag 0F87]. -/
theorem hasResolutionProperty_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    HasResolutionProperty X :=
  hasResolutionProperty_of_isAmple (Stacks.Ample.unitModule X)
    (Stacks.Ample.isAmple_unitModule_of_isAffine X)

end AlgebraicGeometry

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The separated case of [Stacks, Tag 0F8F].**  On a quasi-compact separated scheme with the
resolution property every perfect object of `D(𝒪_X)` is isomorphic to the image of a bounded
complex of finite locally free `𝒪_X`-modules.

Separatedness makes the diagonal a closed immersion, hence affine, so [Stacks, Tag 0F8C] — and
with it the converse of [Stacks, Tag 0F8B] — is not needed.  The source hypothesis of Tag 0F8F is
quasi-separatedness, which is weaker; this is therefore a special case of that tag and does not
carry its registration. -/
theorem exists_boundedFiniteLocallyFree_iso_of_isSeparated (X : Scheme.{u}) [CompactSpace X]
    [X.IsSeparated] [HasResolutionProperty X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  exists_boundedFiniteLocallyFree_iso_of_affineDiagonal X K hK

/-- **The Noetherian case of [Stacks, Tag 0F8F].**  On a Noetherian scheme with the resolution
property every perfect object of `D(𝒪_X)` is isomorphic to the image of a bounded complex of
finite locally free `𝒪_X`-modules.

A Noetherian scheme is quasi-compact and quasi-separated, and the Noetherian case of
[Stacks, Tag 0F8C] gives the affine diagonal outright: the reduction to the Noetherian case is
the only part of that tag that needs the converse of [Stacks, Tag 0F8B]. -/
theorem exists_boundedFiniteLocallyFree_iso_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X]
    [HasResolutionProperty X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  have _ : QuasiSeparatedSpace X := IsLocallyNoetherian.quasiSeparatedSpace
  have _ := isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian X
  exists_boundedFiniteLocallyFree_iso_of_affineDiagonal X K hK

/-- **[Stacks, Tag 0F8F] for a scheme with an ample invertible module.**  Every perfect object of
`D(𝒪_X)` is then isomorphic to the image of a bounded complex of finite locally free
`𝒪_X`-modules.

Ampleness contains quasi-compactness, gives the resolution property by [Stacks, Tag 0F87] and
separatedness by [Stacks, Tag 09MP], so no hypothesis on the scheme beyond the ample module is
left. -/
@[sga "6 0 3.1" "more general"]
theorem exists_boundedFiniteLocallyFree_iso_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  have _ : CompactSpace X := hL.1
  have _ : HasResolutionProperty X := hasResolutionProperty_of_isAmple L hL
  have _ : X.IsSeparated :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X L hL).isSeparated
  exists_boundedFiniteLocallyFree_iso_of_isSeparated X K hK

/-- **[Stacks, Tag 0F8F] for an affine scheme.**  Every perfect object of `D(𝒪_X)` on an affine
scheme is isomorphic to the image of a bounded complex of finite locally free `𝒪_X`-modules.

The structure sheaf is ample, so every hypothesis on the scheme is discharged. -/
@[sga "6 I 4.8" "special case", sga "6 II 2.2.10" "partial"]
theorem exists_boundedFiniteLocallyFree_iso_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  exists_boundedFiniteLocallyFree_iso_of_isAmple X (Stacks.Ample.unitModule X)
    (Stacks.Ample.isAmple_unitModule_of_isAffine X) K hK

/-- **[Stacks, Tag 0F8F] on the spectrum of a ring.**  Every perfect object of `D(𝒪_{Spec R})` is
isomorphic to the image of a bounded complex of finite locally free `𝒪_{Spec R}`-modules.

Stated for `Spec` of an arbitrary ring, with no hypothesis left on the scheme: this is the
instance at which the hypotheses of Tag 0F8F are exhibited as satisfiable. -/
theorem exists_boundedFiniteLocallyFree_iso_spec (R : CommRingCat.{u})
    (K : DerivedCategory (Spec R).Modules)
    (hK : IsPerfect (X := (Spec R).toRingedSpace) K) :
    ∃ E : CochainComplex (Spec R).Modules ℤ, boundedFiniteLocallyFreeComplex (Spec R) E ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  exists_boundedFiniteLocallyFree_iso_of_isAffine (Spec R) K hK

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
