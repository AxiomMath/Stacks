module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGammaFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsChartSquare

/-!
# The spectrum of the global functions, over a terminal base

Over a *terminal* base scheme `S` every scheme of the site carries a unique structure morphism
to `S`, so the forgetful functor from the big fppf category over `S` to schemes is fully
faithful. Two consequences are recorded here.

First, the functor of points `AlgebraicGeometry.Space.schemePoints` of a scheme contained in
the site is representable by an object of the site, and the comparison morphism is the
canonical one, `AlgebraicGeometry.Space.schemePointsUnit`.

Second, an *affine* algebraic space over a terminal base is the functor of points of the
spectrum of its ring of global regular functions: the canonical morphism
`AlgebraicGeometry.Space.toSpecGlobalFunctions` of Stacks 05Z1 is an isomorphism. This is
`AlgebraicGeometry.Space.isIso_of_bijective_globalFunctionsMap` applied to it, pullback of
regular functions along it being the canonical identification
`AlgebraicGeometry.Space.specGlobalFunctionsGamma`, which is a ring isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.terminalSiteObject`: a scheme contained in the site, as an object of
  the big fppf category over a terminal base.
* `AlgebraicGeometry.Space.schemePointsIso`: the identification of the functor of points of a
  contained scheme with the presheaf that object represents.
* `AlgebraicGeometry.Space.canonicalGlobalFunctionsModel`: the canonical small model of the ring
  of global functions of an algebraic space, namely
  `AlgebraicGeometry.Space.globalFunctionsModel`, whose spectrum is shown here to be contained
  in the site.
* `AlgebraicGeometry.Space.affineSpaceIsoSchemePoints`: the identification of an affine
  algebraic space with the functor of points of the spectrum of its global functions.

## Main results

* `AlgebraicGeometry.Space.isIso_schemePointsUnit`: over a terminal base the comparison of the
  two functors of points of an object of the site is an isomorphism.
* `AlgebraicGeometry.Space.isAffineSpace_schemePoints`: over a terminal base the functor of
  points of a contained affine scheme is an affine algebraic space.
* `AlgebraicGeometry.Space.contains_spec_globalFunctionsModel`: the spectrum of the canonical
  model of the global functions of an algebraic space satisfies the size cutoff of the site.
* `AlgebraicGeometry.Space.isIso_toSpecGlobalFunctions`: the canonical morphism to the spectrum
  of the global functions is an isomorphism for an affine algebraic space.

## Implementation notes

*Why the terminal base is needed, and only there.* The surjectivity half of
`AlgebraicGeometry.Space.isIso_schemePointsUnit` is the statement that a morphism of the
underlying schemes of two objects of the site is automatically a morphism over `S`, which is
exactly terminality; the injectivity half is faithfulness of the forgetful functor and holds
over any base. `AlgebraicGeometry.Space.isIso_toSpecGlobalFunctions` inherits the hypothesis
from Stacks 05Z1, which needs it to turn a ring homomorphism into a morphism over `S`, and from
`AlgebraicGeometry.Space.specGlobalFunctions`, whose structure morphism is the one terminality
supplies.

*The containment of the spectrum.* It is the one of
`AlgebraicGeometry.Space.nonempty_globalFunctionsModel`, made explicit for the canonical model
rather than for the chosen subring of that proof: restriction of global functions to a
surjective étale chart is injective, and
`AlgebraicGeometry.Scheme.size_Spec_lt_of_injective_sections` — Stacks 000R (9) for a ring
injecting into the sections of an object of `Sch_κ` — bounds the size of the spectrum.

## References

* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two functors of points over a terminal base -/


/-- Over a terminal base the comparison of the two functors of points of an object of the site
is an isomorphism. -/
theorem isIso_schemePointsUnit (hterminal : IsTerminal S) (Z : BigFppfOver B S hS) :
    IsIso (schemePointsUnit B S hS Z) := by
  have : ∀ W : (BigFppfOver B S hS)ᵒᵖ, IsIso ((schemePointsUnit B S hS Z).app W) := by
    intro W
    rw [CategoryTheory.isIso_iff_bijective]
    constructor
    · intro t t' h
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rwa [← schemePointsUnit_app B S hS Z W t, ← schemePointsUnit_app B S hS Z W t']
    · intro v
      refine ⟨BigFppfOver.homOfCompEq B S hS v (hterminal.hom_ext _ _), ?_⟩
      rw [schemePointsUnit_app]
      exact BigFppfOver.toScheme_map_homOfCompEq B S hS v _
  exact NatIso.isIso_of_isIso_app _

/-- The object of the big fppf site over a terminal base attached to a contained scheme. -/
def terminalSiteObject (hterminal : IsTerminal S) {T : Scheme.{u}} (hT : B.Contains T) :
    BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (hterminal.from T) : B.obj hT ⟶ B.obj hS)

/-- The underlying scheme of `terminalSiteObject B S hS hterminal hT` is `T`. -/
theorem toScheme_terminalSiteObject (hterminal : IsTerminal S) {T : Scheme.{u}}
    (hT : B.Contains T) :
    (BigFppfOver.toScheme B S hS).obj (terminalSiteObject B S hS hterminal hT) = T := rfl

/-- Over a terminal base the functor of points of a contained scheme is representable. -/
def schemePointsIso (hterminal : IsTerminal S) {T : Scheme.{u}} (hT : B.Contains T) :
    yoneda.obj (terminalSiteObject B S hS hterminal hT) ≅ schemePoints B S hS T := by
  have hiso := isIso_schemePointsUnit B S hS hterminal (terminalSiteObject B S hS hterminal hT)
  exact @asIso _ _ _ _ _ hiso

/-- Over a terminal base the functor of points of a contained affine scheme is an affine
algebraic space. -/
theorem isAffineSpace_schemePoints (hterminal : IsTerminal S) {T : Scheme.{u}}
    (hT : B.Contains T) [IsAffine T] : IsAffineSpace B S hS (schemePoints B S hS T) :=
  (isAffineSpace_yoneda B S hS (terminalSiteObject B S hS hterminal hT)
    (inferInstanceAs (IsAffine T))).of_iso
      (schemePointsIso B S hS hterminal hT)

/-- The spectrum of the canonical `u`-model of the global functions of an algebraic space is an
object of the site. -/
theorem contains_spec_globalFunctionsModel (X : AlgebraicSpaces B S hS) :
    B.Contains (Spec (CommRingCat.of (globalFunctionsModel B S hS X))) := by
  obtain ⟨U, φ, hsurj, hetale⟩ := X.property.exists_atlas
  let V : SmallEtale B S hS X.obj := ⟨CostructuredArrow.mk φ, hetale⟩
  have hinj : Function.Injective
      ((globalFunctionsChartRestriction B S hS X V).comp
        (globalFunctionsModelEquiv B S hS X).toRingHom) :=
    (injective_globalFunctionsChartRestriction_of_isSurjective B S hS X V
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X.obj X.property U φ).1 hsurj)).comp
      (globalFunctionsModelEquiv B S hS X).injective
  exact Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (p := CommRingCat.ofHom ((globalFunctionsChartRestriction B S hS X V).comp
      (globalFunctionsModelEquiv B S hS X).toRingHom)) hinj U.left.property

/-- The canonical small model of the global functions of an algebraic space. -/
def canonicalGlobalFunctionsModel (X : AlgebraicSpaces B S hS) :
    GlobalFunctionsModel B S hS X.obj where
  ring := CommRingCat.of (globalFunctionsModel B S hS X)
  contains := contains_spec_globalFunctionsModel B S hS X
  equiv := globalFunctionsModelEquiv B S hS X

/-- The spectrum of a small model of the global functions, as an object of the site, is the
object the terminal base attaches to the contained scheme `Spec A`. -/
theorem specGlobalFunctions_eq (hterminal : IsTerminal S) (X : AlgebraicSpaces B S hS)
    (M : GlobalFunctionsModel B S hS X.obj) :
    specGlobalFunctions B S hS X M hterminal =
      terminalSiteObject B S hS hterminal M.contains := rfl

/-- **The canonical morphism to the spectrum of the global functions is an isomorphism for an
affine algebraic space.** -/
theorem isIso_toSpecGlobalFunctions (hterminal : IsTerminal S) (X : AlgebraicSpaces B S hS)
    (M : GlobalFunctionsModel B S hS X.obj) (hX : IsAffineSpace B S hS X.obj) :
    IsIso (toSpecGlobalFunctions B S hS X M hterminal) := by
  have hΓbij : Function.Bijective (specGlobalFunctionsGamma B S hS X M hterminal) :=
    M.equiv.bijective.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso M.ring).hom)
  have hpb := pullbackToGlobalFunctions_eq B S hS X (specGlobalFunctions B S hS X M hterminal)
    (toSpecGlobalFunctions B S hS X M hterminal)
  rw [pullbackToGlobalFunctions_toSpecGlobalFunctions B S hS X M hterminal] at hpb
  set e := reprGlobalFunctionsEquiv B S hS (specGlobalFunctions B S hS X M hterminal)
  have hbij : Function.Bijective
      (globalFunctionsMap B S hS (toSpecGlobalFunctions B S hS X M hterminal)) := by
    have hfun : (globalFunctionsMap B S hS
          (toSpecGlobalFunctions B S hS X M hterminal) : _ → _)
        = (specGlobalFunctionsGamma B S hS X M hterminal : _ → _) ∘ (e : _ → _) := by
      funext y
      refine Eq.trans ?_ (RingHom.congr_fun hpb.symm (e y))
      exact congrArg (fun z => globalFunctionsMap B S hS
        (toSpecGlobalFunctions B S hS X M hterminal) z) (e.symm_apply_apply y).symm
    rw [hfun]
    exact hΓbij.comp e.bijective
  exact isIso_of_bijective_globalFunctionsMap B S hS hX
    (isAffineSpace_yoneda B S hS (specGlobalFunctions B S hS X M hterminal) inferInstance)
    _ hbij

/-- **An affine algebraic space over a terminal base is the functor of points of the spectrum
of its ring of global regular functions.** -/
def affineSpaceIsoSchemePoints (hterminal : IsTerminal S) (X : AlgebraicSpaces B S hS)
    (M : GlobalFunctionsModel B S hS X.obj) (hX : IsAffineSpace B S hS X.obj) :
    X.obj ≅ schemePoints B S hS (Spec M.ring) := by
  have h1 := isIso_toSpecGlobalFunctions B S hS hterminal X M hX
  have h2 := isIso_schemePointsUnit B S hS hterminal (specGlobalFunctions B S hS X M hterminal)
  exact (ObjectProperty.ι _).mapIso (@asIso _ _ _ _ _ h1) ≪≫ (@asIso _ _ _ _ _ h2)

end AlgebraicGeometry.Space

end
