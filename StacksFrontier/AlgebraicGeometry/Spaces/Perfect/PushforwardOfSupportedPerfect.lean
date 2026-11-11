module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects

/-!
# Perfectness of the derived direct image of a supported perfect object

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, set `T = |X| \ |U|`, and let `E` be a perfect object of `D(𝒪_V)` supported on
`j^{-1}T`.  Stacks 08HK says that `Rj_*E` is a perfect object of `D(𝒪_X)`.

The source's proof is two sentences: perfectness is a local condition on `X_étale`, so it
suffices to check it after restricting to `U` and to `V`; on `V` the restriction is `E` itself
by Stacks 08GG, and on `U` it vanishes because `E` vanishes on `V \ j^{-1}T`.  This file carries
out that deduction from its three inputs, taken as hypotheses, and proves the two facts about
perfectness the deduction needs, namely that a zero object of `D(𝒪)` is perfect and that
perfectness transports along an isomorphism, for a ringed site, unconditionally and with all
universes free.  The three inputs are now proved, in `SupportedPushforwardPerfect.lean` and
`PerfectEtaleLocalSliceRestriction.lean`, and Stacks 08HK itself is registered as
`AlgebraicGeometry.Space.isPerfect_rightAdjoint_edsDerivedRestrictEtale_of_cohomologySupportedOn`
and, for the derived direct image `AlgebraicGeometry.derivedModulePushforward`, as
`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_cohomologySupportedOn`.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfectComplex_of_isZero`: a zero complex of `𝒪`-modules on
  a ringed site is a perfect complex.
* `AlgebraicGeometry.RingedSite.isPerfect_of_isZero`: a zero object of `D(𝒪)` is perfect.
* `AlgebraicGeometry.RingedSite.IsPerfect.of_iso`: perfectness transports along an isomorphism
  of `D(𝒪)`.
* `AlgebraicGeometry.Space.isPerfect_derivedPushforward_of_cohomologySupportedOn`: the source's
  deduction of Stacks 08HK from its three inputs, each a hypothesis.

## Implementation notes

*Perfectness, support, and the square.*  Perfectness is
`AlgebraicGeometry.RingedSite.IsPerfect` of Stacks 08G5 on the small étale ringed site
`AlgebraicGeometry.Space.smallEtaleRingedSite` of Stacks 04KH, which is the site the source
means by `D(𝒪_X)`; support is `AlgebraicGeometry.Space.CohomologySupportedOn` of Stacks 08GF;
the square is the structure `AlgebraicGeometry.Space.IsElementaryDistinguishedSquare` of
Stacks 08GM, whose open subspace, étale space and étale morphism are read off by
`AlgebraicGeometry.Space.edsOpen`, `AlgebraicGeometry.Space.edsEtale` and
`AlgebraicGeometry.Space.edsEtaleHom`, and `j^{-1}T` is
`AlgebraicGeometry.Space.edsEtalePreimageComplementPoints`.  No new predicate is introduced.
At the module universe `u` of the structure rings every sheafification and local-bijectivity
hypothesis that `IsPerfect` asks of the site and of its slices is an instance, by
`AlgebraicGeometry.Space.RingedSite`, so none appears as a binder.

*`Rj_*` enters as data.*  Following
`AlgebraicGeometry.Space.isIso_supportedShriekToPushforward` and Stacks 08HA, the derived
direct image is a functor `RpushD` together with an adjunction `(-)|_V ⊣ RpushD`.  A right
adjoint together with its adjunction is unique up to a unique compatible isomorphism, so this
pins both the functor and the counit `(Rj_*E)|_V ⟶ E` that clause (2)(b) of Stacks 08GG is
about; it does not weaken the statement.

*The three inputs, each a named hypothesis.*  Each is stated as an implication *from* the
support hypothesis where it uses it, so that the source's support hypothesis is really consumed.
All three are proved elsewhere in the library:

1. `hlocal` is that perfectness is local on `X_étale` along the covering `{U ⟶ X, j : V ⟶ X}`,
   which is the first sentence of the source's proof; it is
   `AlgebraicGeometry.Space.isPerfect_of_isPerfect_eds`.
2. `h2b` is clause (2)(b) of Stacks 08GG, that the counit `(Rj_*E)|_V ⟶ E` is an isomorphism
   for `E` supported on `j^{-1}T`; it is
   `AlgebraicGeometry.Space.isIso_counit_edsEtale_rightAdjoint_of_cohomologySupportedOn`.
3. `hUzero` is that the restriction of `Rj_*E` to `U` vanishes, which the source gets from
   `E|_{V ∖ j^{-1}T} = 0` and Stacks 08GE; it is
   `AlgebraicGeometry.Space.isZero_edsDerivedRestrictOpen_rightAdjoint_of_cohomologySupportedOn`.

*What is proved here.*  Given the three, the deduction is the source's: `hUzero` and
`isPerfect_of_isZero` make the restriction to `U` perfect, `h2b` and `IsPerfect.of_iso` carry
the perfectness of `E` to the restriction to `V`, and `hlocal` assembles them.  The support
hypothesis is used exactly twice, once in each of the first two steps.

## References

* [Stacks Project, Tag 08HK](https://stacks.math.columbia.edu/tag/08HK)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v w m d

namespace AlgebraicGeometry.RingedSite

/-! ### Zero objects and isomorphisms, for perfectness on a ringed site -/

/-- A zero `𝒪`-module is a direct summand of a finite free `𝒪`-module: take the free module on
no generators and the two zero maps, the retract identity holding because raising a zero module
to the common module universe leaves it zero. -/
private theorem isDirectSummandOfFiniteFreeOfIsZero {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] {F : SheafOfModules.{m} R}
    (hF : IsZero F) : IsDirectSummandOfFiniteFree R F := by
  refine ⟨0, 0, 0, ?_⟩
  exact IsZero.eq_of_src (Functor.map_isZero _ hF) _ _

section Zero

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{m}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- A zero complex of `𝒪`-modules on a ringed site is a perfect complex: over every object of
the site the total sieve is covering, and the restriction of the complex is itself a zero
complex, hence strictly perfect — it has no nonzero term, and a zero module is a direct summand
of a finite free module — so the identity is the required quasi-isomorphism. -/
theorem isPerfectComplex_of_isZero
    {E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : IsZero E) :
    X.IsPerfectComplex E := by
  intro U
  refine ⟨(⊤ : Sieve U).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact X.J.top_mem U
  · intro Z f _
    have hz : IsZero (X.restrictComplex E Z) :=
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          Z).mapHomologicalComplex
        (ComplexShape.up ℤ)).map_isZero hE
    have hX (i : ℤ) : IsZero ((X.restrictComplex E Z).X i) :=
      (HomologicalComplex.eval _ (ComplexShape.up ℤ) i).map_isZero hz
    refine ⟨X.restrictComplex E Z, ⟨Set.finite_empty.subset ?_, fun i => ?_⟩, 𝟙 _,
      inferInstance⟩
    · intro i hi
      exact absurd (hX i) hi
    · exact isDirectSummandOfFiniteFreeOfIsZero ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over
        Z) (hX i)

variable [HasSheafify X.J AddCommGrpCat.{m}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [HasDerivedCategory.{d} (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- A zero object of `D(𝒪)` is perfect: it is represented by the zero complex, which is a
perfect complex. -/
theorem isPerfect_of_isZero
    {K : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsZero K) : X.IsPerfect K :=
  ⟨0, X.isPerfectComplex_of_isZero (isZero_zero _),
    ⟨(DerivedCategory.Q.map_isZero (isZero_zero _)).iso hK⟩⟩

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- Perfectness transports along an isomorphism of `D(𝒪)`: a perfect complex representing the
source represents the target as well. -/
theorem IsPerfect.of_iso
    {K K' : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : X.IsPerfect K) (e : K ≅ K') : X.IsPerfect K' := by
  obtain ⟨E, hE, ⟨i⟩⟩ := hK
  exact ⟨E, hE, ⟨i ≪≫ e⟩⟩

end Zero

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- Restriction of derived objects of `D(𝒪_X)` to the open subspace `U` of an elementary
distinguished square, induced by the exact restriction of modules along the open immersion. -/
abbrev edsDerivedRestrictOpen :
    DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS (edsOpen B S hS hsq).1
        (edsOpen B S hS hsq).2) :=
  (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory

/-- Restriction of derived objects of `D(𝒪_X)` to the étale space `V` of an elementary
distinguished square, induced by the exact restriction of modules along `j`. -/
abbrev edsDerivedRestrictEtale :
    DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) :=
  (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory

variable {RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
    (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
  (adjPush : edsDerivedRestrictEtale B S hS hsq ⊣ RpushD)

/-- **The source's deduction of Stacks 08HK from its three inputs.**  For an elementary
distinguished square `(U ⊆ X, j : V ⟶ X)` with `T = |X| \ |U|`, a right adjoint `RpushD` of
derived restriction to `V`, and a perfect `E` in `D(𝒪_V)` supported on `j^{-1}T`: if
perfectness is local along the square (`hlocal`), the counit `(Rj_*E)|_V ⟶ E` is an isomorphism
(`h2b`, clause (2)(b) of Stacks 08GG) and `(Rj_*E)|_U` vanishes (`hUzero`), then `Rj_*E` is
perfect.  Both `h2b` and `hUzero` are stated as implications from the support hypothesis.

The three inputs are proved, so Stacks 08HK holds outright; it is registered as
`AlgebraicGeometry.Space.isPerfect_rightAdjoint_edsDerivedRestrictEtale_of_cohomologySupportedOn`
and `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_cohomologySupportedOn`. -/
theorem isPerfect_derivedPushforward_of_cohomologySupportedOn
    (E : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hperf : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect E)
    (hE : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) E)
    (h2b : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
        (edsEtalePreimageComplementPoints B S hS hsq) E →
      IsIso (adjPush.counit.app E))
    (hUzero : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
        (edsEtalePreimageComplementPoints B S hS hsq) E →
      IsZero ((edsDerivedRestrictOpen B S hS hsq).obj (RpushD.obj E)))
    (hlocal :
      (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
          (edsOpen B S hS hsq).2).IsPerfect
          ((edsDerivedRestrictOpen B S hS hsq).obj (RpushD.obj E)) →
        (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
            (edsEtale B S hS hsq).2).IsPerfect
            ((edsDerivedRestrictEtale B S hS hsq).obj (RpushD.obj E)) →
          (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect (RpushD.obj E)) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect (RpushD.obj E) := by
  have := h2b hE
  exact hlocal (RingedSite.isPerfect_of_isZero _ (hUzero hE))
    (RingedSite.IsPerfect.of_iso _ hperf (asIso (adjPush.counit.app E)).symm)

end Square

end AlgebraicGeometry.Space

end
