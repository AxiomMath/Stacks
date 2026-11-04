module

public import StacksFrontier.AlgebraicGeometry.Divisors.AmpleFamilyRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealCoveringResolutionNoetherianImage

/-!
# A quasi-compact regular scheme with affine diagonal has the resolution property

This is [Stacks, Tag 0F8A].  Let `X` be a quasi-compact regular scheme whose diagonal is affine.
Then `X` has the resolution property: every quasi-coherent `𝒪_X`-module of finite type is the
quotient of a finite locally free one.

The source proves this by combining [Stacks, Tag 0GML] — such an `X` carries an ample family of
invertible modules — with [Stacks, Tag 0GMM], the resolution property for a scheme with an ample
family, which in turn rests on the substantial direction of [Stacks, Tag 0F89].  The route taken
here is shorter and needs none of that: the proof of Tag 0GML already produces, around every
point of `X`, a *dense affine open* `U` together with an effective Cartier divisor cutting out its
complement, and the sheaf of ideals of an effective Cartier divisor is by definition invertible,
hence finite locally free.  So the data that the substantial direction of Tag 0F89 asks for is
available directly, and because a quasi-compact regular scheme is Noetherian, the Noetherian case
of that direction — which *is* proved in this development — applies.

## Main definitions

* `Stacks.Divisors.kernelIdealSheafι`: the inclusion `ℐ ⟶ 𝒪_X` of the sheaf of ideals of a closed
  subscheme, read sectionwise through `Stacks.Divisors.kernelIdealSheaf`.

## Main results

* `AlgebraicGeometry.idealSheafDataOfHom_kernelIdealSheafι`: the image of that inclusion is the
  sheaf of ideals one started from.
* `AlgebraicGeometry.isFiniteLocallyFree_kernelIdealSheaf`: **the sheaf of ideals of an effective
  Cartier divisor is finite locally free.**
* `AlgebraicGeometry.hasResolutionProperty_of_isNoetherian_of_isEffectiveCartierDivisor`: **a
  Noetherian scheme which is covered by finitely many affine opens, each the complement of an
  effective Cartier divisor, has the resolution property.**
* `AlgebraicGeometry.IsRegular.hasResolutionProperty` (in
  `StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyAmpleFamilyIdealCovering.lean`):
  **[Stacks, Tag 0F8A]**, with no hypotheses beyond those of the source, deduced from the last
  statement.

## The argument

Regularity enters twice, and only through the ingredients of [Stacks, Tag 0GML].  First,
`AlgebraicGeometry.isRegular_tfae` gives `IsLocallyNoetherian X`, which with quasi-compactness is
`IsNoetherian X`, and it gives regular — hence unique factorization — local rings
(`IsRegularLocalRing.uniqueFactorizationMonoid`).  Second, a regular scheme is normal, so
`AlgebraicGeometry.exists_isAffineOpen_dense_mem_of_isNormal` supplies around each `x` a dense
affine open `U x` containing `x`, and [Stacks, Tag 0EGJ] in the form
`AlgebraicGeometry.exists_effectiveCartierDivisor_compl_affineOpen` turns each of those into an
effective Cartier divisor `D x` with `V(D x) = X \ U x`.  Quasi-compactness cuts the covering
`X = ⋃ x, U x` down to a finite one, and
`hasResolutionProperty_of_isNoetherian_of_isEffectiveCartierDivisor` finishes.

That last step is
`AlgebraicGeometry.hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom`, the
Noetherian case of the substantial direction of [Stacks, Tag 0F89] stated for morphisms out of
finite locally free modules, fed with the ideal sheaf inclusions `ℐ_{D j} ⟶ 𝒪_X`.  Nothing about
the resolution property is reproved here.

## Implementation notes

**Why the sectionwise ideal sheaf.** `Stacks.Divisors.IsEffectiveCartierDivisor` is invertibility
of the *categorical* ideal sheaf `Stacks.ClosedImmersion.idealSheaf`, whose sections are not
immediately an ideal of `Γ(X, V)`.  `Stacks.Divisors.kernelIdealSheaf` is the same sheaf presented
sectionwise, as the kernel of `𝒪_X ⟶ i_* 𝒪_Z`, and `Stacks.Divisors.kernelIdealSheafIso`
identifies the two; the sectionwise presentation is the one for which the image ideal of the
inclusion is computable, because Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app` says that over an affine open that
kernel *is* `I.ideal V`.  Invertibility is transported across the isomorphism at the level of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, where
`Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one` — clause 2
of [Stacks, Tag 0B8M] — makes the transport available.

**Quasi-coherence is an explicit argument.**
`AlgebraicGeometry.idealSheafDataOfHom` takes quasi-coherence of its source as an instance, and
the two spellings of the sheaf of rings indexing the modules (`X.ringCatSheaf` and the ringed-space
`Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing`) are definitionally but not
syntactically equal, so instance search does not bridge them.  Hence
`idealSheafDataOfHom_kernelIdealSheafι` takes the quasi-coherence hypothesis explicitly and the
statement names it with `@`; the conclusion is independent of which proof is supplied, the only
field of `AlgebraicGeometry.Scheme.IdealSheafData` that depends on it being a proof.

## References

* [Stacks Project, Tag 0F8A](https://stacks.math.columbia.edu/tag/0F8A)
* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 0EGJ](https://stacks.math.columbia.edu/tag/0EGJ)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **The inclusion of the sheaf of ideals of a closed subscheme into the structure sheaf**, with
the ideal sheaf presented sectionwise as `Stacks.Divisors.kernelIdealSheaf`: over an open `V` it
is the inclusion of `ker (𝒪_X(V) ⟶ 𝒪_Z(i⁻¹V))` into `𝒪_X(V)`. -/
noncomputable def kernelIdealSheafι (I : X.IdealSheafData) :
    (kernelIdealSheaf I : X.Modules) ⟶
      Stacks.AlgebraicGeometry.IdealPowerColimit.structureModule X :=
  SheafOfModules.kerIota (structureSheafHomOfIdealSheafData I)

end Stacks.Divisors

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.IdealPowerColimit
open Stacks.Divisors (kernelIdealSheaf kernelIdealSheafι)

variable {X : Scheme.{u}}

/-- Over an affine open, the image of the ideal sheaf inclusion is the defining ideal itself.
This is Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app` read as a statement
about the range of a morphism of sheaves of modules. -/
theorem idealOfHom_kernelIdealSheafι (I : X.IdealSheafData) (V : X.affineOpens) :
    idealOfHom (kernelIdealSheaf I : X.Modules) (kernelIdealSheafι I) V.1 = I.ideal V := by
  apply le_antisymm
  · rintro y ⟨z, rfl⟩
    rw [← I.ker_subschemeι_app V]
    exact z.2
  · intro y hy
    rw [← I.ker_subschemeι_app V] at hy
    exact ⟨Stacks.Divisors.mkKernelSection I y hy, rfl⟩

/-- **The image of the ideal sheaf inclusion is the sheaf of ideals one started from.**  Two
quasi-coherent sheaves of ideals agreeing on every affine open are equal, and over an affine open
both sides are `I.ideal V` by `AlgebraicGeometry.idealOfHom_kernelIdealSheafι`. -/
theorem idealSheafDataOfHom_kernelIdealSheafι (I : X.IdealSheafData)
    (hqc : (kernelIdealSheaf I : X.Modules).IsQuasicoherent) :
    @idealSheafDataOfHom X (kernelIdealSheaf I : X.Modules) hqc (kernelIdealSheafι I) = I :=
  Scheme.IdealSheafData.ext (funext fun V => idealOfHom_kernelIdealSheafι I V)

/-- **The sheaf of ideals of an effective Cartier divisor is finite locally free.**  Being an
effective Cartier divisor is invertibility of that sheaf of ideals ([Stacks, Tag 01WR] (2)), and an
invertible module on a scheme is finite locally free of rank one by clause 2 of
[Stacks, Tag 0B8M]. -/
theorem isFiniteLocallyFree_kernelIdealSheaf {I : X.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (kernelIdealSheaf I : X.Modules) := by
  have hinv : Stacks.Ample.IsInvertibleModule X
      (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom) := hI
  have hrank :
      SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf)
        (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom : X.Modules) 1 :=
    (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one X
      (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom)).mp hinv
  have : SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf)
      (kernelIdealSheaf I : X.Modules) 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (Stacks.Divisors.kernelIdealSheafIso I) hrank
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (R := X.ringCatSheaf)
    (kernelIdealSheaf I : X.Modules) 1

/-- The sheaf of ideals of an effective Cartier divisor is quasi-coherent, being finite locally
free. -/
theorem isQuasicoherent_kernelIdealSheaf {I : X.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    (kernelIdealSheaf I : X.Modules).IsQuasicoherent :=
  have := isFiniteLocallyFree_kernelIdealSheaf hI
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree
    (R := X.ringCatSheaf) (kernelIdealSheaf I : X.Modules)

/-- **A Noetherian scheme covered by finitely many affine opens, each the complement of an
effective Cartier divisor, has the resolution property.**

This is the substantial direction of [Stacks, Tag 0F89] in the one case in which this development
has it — the Noetherian one — fed with the data an effective Cartier divisor supplies for free:
its sheaf of ideals is finite locally free, and the image of the inclusion of that sheaf of ideals
into `𝒪_X` is the sheaf of ideals itself, so the vanishing locus is the given complement. -/
theorem hasResolutionProperty_of_isNoetherian_of_isEffectiveCartierDivisor [IsNoetherian X]
    {m : ℕ} (U : Fin m → X.Opens) (D : Fin m → X.IdealSheafData)
    (hU : ∀ j, IsAffineOpen (U j)) (hcov : ⨆ j, U j = ⊤)
    (hD : ∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (D j))
    (hsupp : ∀ j, ((D j).support : Set X) = ((U j : Set X))ᶜ) :
    HasResolutionProperty X := by
  refine hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom U
    (fun j => (kernelIdealSheaf (D j) : X.Modules))
    (fun j => isFiniteLocallyFree_kernelIdealSheaf (hD j))
    (fun j => kernelIdealSheafι (D j))
    (fun j => isQuasicoherent_kernelIdealSheaf (hD j)) hU hcov fun j => ?_
  rw [idealSheafDataOfHom_kernelIdealSheafι (D j) (isQuasicoherent_kernelIdealSheaf (hD j))]
  exact hsupp j

end AlgebraicGeometry

end
