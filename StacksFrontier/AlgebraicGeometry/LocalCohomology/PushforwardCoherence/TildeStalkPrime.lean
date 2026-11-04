module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.RingTheory.Depth.AlgebraMap

/-!
# The stalk of `M̃` at a prime: support and depth

Let `A` be a commutative ring, let `M` be an `A`-module and let `𝔭` be a prime of `A`. The stalk
of `M̃` at `𝔭` is the localization `M_𝔭`, by Mathlib's
`AlgebraicGeometry.tilde.toStalk` and the `IsLocalizedModule` instance it carries. This file
draws the two consequences that read a pointwise condition on `M̃` as a condition on `M`: the
point `𝔭` lies in the support of `M̃` exactly when `M_𝔭` is nontrivial, and the depth of the
stalk of `M̃` at `𝔭` over `𝒪_{Spec A, 𝔭}` is the depth of `M_𝔭` over `A_𝔭`.

These are the terms in which [Stacks, Tag 0BJR] and the affine criteria of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/PushforwardCoherence/` state the
depth--dimension condition, and the stalk side is the one a condition on an arbitrary coherent
module is stated in; the two are only comparable through the identification below.

## Main definitions

* `AlgebraicGeometry.tildeStalkLinearEquiv`: the stalk of `M̃` at `𝔭` is `M_𝔭`, as an
  `A`-linear equivalence.

## Main results

* `AlgebraicGeometry.mem_supp_tilde_iff_nontrivial_localizedModule`: `𝔭 ∈ Supp(M̃)` exactly
  when `M_𝔭 ≠ 0`.
* `AlgebraicGeometry.depth_stalk_tilde_eq_depth_localizedModule`: the depth of the stalk of
  `M̃` at `𝔭` is the depth of `M_𝔭`.
* `AlgebraicGeometry.supportDim_stalk_tilde_eq_supportDim_localizedModule`: the dimension of
  the support of the stalk of `M̃` at `𝔭` is that of `M_𝔭`.

## Implementation notes

**The prime and the point are passed separately.** The carrier of the scheme `Spec A` and the
type `PrimeSpectrum A` are definitionally equal, but not at the transparency instance search
uses: at a point of the scheme the local-ring and stalk-module instances are found and
`𝔭.IsPrime` is not, while at a prime it is the other way round. Both statements below therefore
take a point `x` of `Spec A`, a prime `𝔭` of `A` and the equation identifying them, so that each
side of the conclusion is written at the spelling whose instances exist. A caller holding only a
point supplies the prime as that same point and `rfl`.

The compatibility of the two scalar actions on the stalk of `M̃` — Mathlib's `A`-action and the
`𝒪_{Spec A, 𝔭}`-action of `AlgebraicGeometry.Scheme.Modules.instModuleStalk` — is
definitional: `algebraMap A 𝒪_{Spec A, 𝔭} r • z = r • z` holds by `rfl`, which is what makes
the scalar towers below available with no germ computation. The depth comparison is then the
same three steps as
`AlgebraicGeometry.depth_stalk_eq_depth_localizedModule` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/StalkDepthCriterion.lean`: extend the
`A`-linear equivalence to `A_𝔭`, and compare depths over `A_𝔭` and over the stalk along the
surjective `algebraMap`. That lemma is not used here: it computes the depth of the stalk of a
quasi-coherent module through its sections over an affine open, and at the top open of `Spec A`
those sections are an `Γ(Spec A, ⊤)`-module rather than an `A`-module, so it answers over the
primes of `Γ(Spec A, ⊤)`.

## References

* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- **The stalk of `M̃` at a prime `𝔭` is the localization `M_𝔭`**, as an `A`-linear
equivalence. This is Mathlib's `IsLocalizedModule` instance on `AlgebraicGeometry.tilde.toStalk`
read through `IsLocalizedModule.linearEquiv`. -/
public def tildeStalkLinearEquiv (p : PrimeSpectrum (ToType R)) :
    LocalizedModule p.asIdeal.primeCompl M ≃ₗ[ToType R] ((tilde M).presheaf.stalk p) :=
  IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (tilde.toStalk M p).hom

/-- **A prime lies in the support of `M̃` exactly when the localization of `M` there is
nonzero.** The two modules are isomorphic by `tildeStalkLinearEquiv`, so one is trivial exactly
when the other is. -/
public theorem mem_supp_tilde_iff_nontrivial_localizedModule (x : Spec R)
    (p : PrimeSpectrum (ToType R)) (hp : (p : Spec R) = x) :
    x ∈ SheafOfModules.supp (tilde M) ↔
      Nontrivial (LocalizedModule p.asIdeal.primeCompl M) := by
  subst hp
  refine (SheafOfModules.mem_supp_iff_nontrivial_stalk (tilde M) (p : Spec R)).trans ?_
  exact (Equiv.nontrivial_congr (tildeStalkLinearEquiv M p).toEquiv).symm

private instance (p : PrimeSpectrum (ToType R)) :
    Algebra (ToType R) ((Spec R).presheaf.stalk (p : Spec R)) :=
  StructureSheaf.stalkAlgebra (ToType R) p

private instance (p : PrimeSpectrum (ToType R)) :
    IsLocalization.AtPrime ((Spec R).presheaf.stalk (p : Spec R)) p.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk R p

/-- The identification of `A_𝔭` with the stalk of the structure sheaf at `𝔭`. -/
private def localizationAlgEquivStalk (p : PrimeSpectrum (ToType R)) :
    Localization.AtPrime p.asIdeal ≃ₐ[ToType R] ((Spec R).presheaf.stalk (p : Spec R)) :=
  IsLocalization.algEquiv p.asIdeal.primeCompl _ _

private instance (p : PrimeSpectrum (ToType R)) :
    Algebra (Localization.AtPrime p.asIdeal) ((Spec R).presheaf.stalk (p : Spec R)) :=
  (localizationAlgEquivStalk p).toAlgHom.toAlgebra

private instance (p : PrimeSpectrum (ToType R)) :
    Module ((Spec R).presheaf.stalk (p : Spec R)) ((tilde M).presheaf.stalk (p : Spec R)) :=
  Scheme.Modules.instModuleStalk (tilde M) (p : Spec R)

private instance (p : PrimeSpectrum (ToType R)) :
    Module (Localization.AtPrime p.asIdeal) ((tilde M).presheaf.stalk (p : Spec R)) :=
  Module.compHom _
    (algebraMap (Localization.AtPrime p.asIdeal) ((Spec R).presheaf.stalk (p : Spec R)))

private instance (p : PrimeSpectrum (ToType R)) :
    IsScalarTower (ToType R) (Localization.AtPrime p.asIdeal)
      ((Spec R).presheaf.stalk (p : Spec R)) :=
  IsScalarTower.of_algebraMap_smul fun r t =>
    congrArg (· * t) ((localizationAlgEquivStalk p).commutes r)

private instance (p : PrimeSpectrum (ToType R)) :
    IsScalarTower (ToType R) (Localization.AtPrime p.asIdeal)
      ((tilde M).presheaf.stalk (p : Spec R)) :=
  IsScalarTower.of_algebraMap_smul fun r n =>
    congrArg (· • n) ((localizationAlgEquivStalk p).commutes r)

/-- **The depth of the stalk of `M̃` at a prime `𝔭` is the depth of `M_𝔭`.** The stalk is
`M_𝔭` by `tildeStalkLinearEquiv` and the stalk of the structure sheaf is `A_𝔭` by
`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`, compatibly: the `A`-action on the
stalk of `M̃` is the restriction of the stalk-ring action by `rfl`. -/
public theorem depth_stalk_tilde_eq_depth_localizedModule (x : Spec R)
    (p : PrimeSpectrum (ToType R)) (hp : (p : Spec R) = x) :
    Module.depth ((Spec R).presheaf.stalk x) (maximalIdeal ((Spec R).presheaf.stalk x))
        ((tilde M).presheaf.stalk x) =
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) := by
  let iMod : Module ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) :=
    Scheme.Modules.instModuleStalk (tilde M) x
  let iLocal : IsLocalRing ((Spec R).presheaf.stalk x) := inferInstance
  subst hp
  let : IsScalarTower (ToType R) ((Spec R).presheaf.stalk (p : Spec R))
      ((tilde M).presheaf.stalk (p : Spec R)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower (Localization.AtPrime p.asIdeal)
      ((Spec R).presheaf.stalk (p : Spec R)) ((tilde M).presheaf.stalk (p : Spec R)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hdepthM : Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) =
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        ((tilde M).presheaf.stalk (p : Spec R)) :=
    Module.depth_eq_depth_of_linearEquiv (maximalIdeal (Localization.AtPrime p.asIdeal))
      ((tildeStalkLinearEquiv M p).extendScalarsOfIsLocalization p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal))
  have hmax : Ideal.map
        (algebraMap (Localization.AtPrime p.asIdeal) ((Spec R).presheaf.stalk (p : Spec R)))
        (maximalIdeal (Localization.AtPrime p.asIdeal)) =
      maximalIdeal ((Spec R).presheaf.stalk (p : Spec R)) :=
    IsLocalRing.map_ringEquiv_maximalIdeal (localizationAlgEquivStalk p).toRingEquiv
  have hdepthST := Module.depth_eq_depth_map_algebraMap
    (A := Localization.AtPrime p.asIdeal) (B := (Spec R).presheaf.stalk (p : Spec R))
    (localizationAlgEquivStalk p).surjective (maximalIdeal (Localization.AtPrime p.asIdeal))
    ((tilde M).presheaf.stalk (p : Spec R))
  rw [hmax] at hdepthST
  exact hdepthST.symm.trans hdepthM.symm

/-- **The dimension of the support of the stalk of `M̃` at a prime `𝔭` is that of `M_𝔭`.** The
stalk is `M_𝔭` by `tildeStalkLinearEquiv`, `A_𝔭`-linearly after extending scalars, and the
`A_𝔭`-action on the stalk is the stalk-ring action read through the isomorphism
`A_𝔭 ≅ 𝒪_{Spec A, 𝔭}`, so the identity of the stalk is semilinear over that isomorphism. -/
public theorem supportDim_stalk_tilde_eq_supportDim_localizedModule (x : Spec R)
    (p : PrimeSpectrum (ToType R)) (hp : (p : Spec R) = x) :
    Module.supportDim ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) =
      Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) := by
  let iMod : Module ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) :=
    Scheme.Modules.instModuleStalk (tilde M) x
  subst hp
  let eM := (tildeStalkLinearEquiv M p).extendScalarsOfIsLocalization p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal)
  have hM : Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) =
      Module.supportDim (Localization.AtPrime p.asIdeal)
        ((tilde M).presheaf.stalk (p : Spec R)) :=
    Module.supportDim_eq_of_semilinearEquiv (RingEquiv.refl _) eM.toAddEquiv
      fun a m => eM.map_smul a m
  refine Eq.trans ?_ hM.symm
  exact (Module.supportDim_eq_of_semilinearEquiv (localizationAlgEquivStalk p).toRingEquiv
    (AddEquiv.refl ((tilde M).presheaf.stalk (p : Spec R))) fun _ _ => rfl).symm

end AlgebraicGeometry

end
