module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of the derived direct image of a supported perfect object

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, set `T = |X| \ |U|`, and let `E` be a perfect object of `D(𝒪_V)` supported on
`j^{-1}T`.  Stacks 08HK says that `Rj_*E` is a perfect object of `D(𝒪_X)`.

The source's proof is two sentences: perfectness is a local condition on `X_étale`, so it
suffices to check it after restricting to `U` and to `V`; on `V` the restriction is `E` itself
by Stacks 08GG, and on `U` it vanishes because `E` vanishes on `V \ j^{-1}T`.  That passage is
what is carried out here, from three named hypotheses standing for the three inputs the library
does not have — see the implementation notes, which say precisely what each one is and why it
is missing.  The two facts about perfectness the passage needs, namely that a zero object of
`D(𝒪)` is perfect and that perfectness transports along an isomorphism, are *not* in the
library for a ringed site; they are proved here, unconditionally and with all universes free.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfectComplex_of_isZero`: a zero complex of `𝒪`-modules on
  a ringed site is a perfect complex.
* `AlgebraicGeometry.RingedSite.isPerfect_of_isZero`: a zero object of `D(𝒪)` is perfect.
* `AlgebraicGeometry.RingedSite.IsPerfect.of_iso`: perfectness transports along an isomorphism
  of `D(𝒪)`.
* `AlgebraicGeometry.Space.isPerfect_derivedPushforward_of_cohomologySupportedOn`:
  **Stacks 08HK**, granted the three inputs described below.

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

*The three missing inputs, each a named hypothesis.*  None of the three is proved anywhere in
the library, and each is stated as an implication *from* the support hypothesis, exactly as
`hvan` and `h2b` are in `SupportedOnComplement.lean`, so that the source's support hypothesis
is really consumed and is not left dangling.

1. `hlocal` is that perfectness is local on `X_étale` along the covering `{U ⟶ X, j : V ⟶ X}`,
   which is the first sentence of the source's proof.  The library's statement of it is
   `AlgebraicGeometry.RingedSite.isPerfect_of_locally`, Stacks 08G5 read through Stacks 08G6
   part (1), and it is **inapplicable here for a universe reason, not for want of a covering**:
   it is stated for a `RingedSite.{u, u, 0}`, whereas
   `AlgebraicGeometry.Space.smallEtaleRingedSite` is a `RingedSite.{u + 1, u, u}`, whose objects
   lie one universe above its morphisms.  The restriction is inherited from Stacks 08FR
   (`Stacks.SheafOfModules.exists_coveringSieve_quasiIso_of_derivedIso`), which turns a derived
   isomorphism into an honest map of complexes and is available only when the objects and the
   morphisms of the site share a universe.  So Stacks 08G6 part (1), and with it every
   local-to-global statement about perfectness, is currently unreachable for an algebraic space,
   and the covering `{U, V}` of `X_étale` would not help.
2. `h2b` is clause (2)(b) of Stacks 08GG, that the counit `(Rj_*E)|_V ⟶ E` is an isomorphism
   for `E` supported on `j^{-1}T`.  `SupportedOnComplement.lean` proves clauses (1)(a), (1)(b)
   and (2)(c) and records in its own notes that clauses (2)(a) and (2)(b) are *not* proved:
   the source obtains them by base changing the square to `V`, where `j` acquires a section,
   and that reduction is not carried by the library.  Clause (2)(c), which *is* proved there,
   takes (2)(b) as a hypothesis too.
3. `hUzero` is that the restriction of `Rj_*E` to `U` vanishes.  The source gets it from
   `E|_{V ∖ j^{-1}T} = 0` and Stacks 08GE.  The first half is the step
   `Hⁱ(E|_Y) = Hⁱ(E)|_Y` together with Stacks 04K5, and `SupportedOnComplement.lean` records
   that it is unavailable because Mathlib proves no commutation of
   `CategoryTheory.Functor.mapDerivedCategory` with the homology functors; that is the same gap
   its hypothesis `hvan` stands for.  Stacks 08GE itself is proved, as
   `AlgebraicGeometry.Space.derivedModulePushforwardEtaleRestrictIso`.

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
    {E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (hE : IsZero E) :
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
theorem isPerfect_of_isZero {K : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsZero K) : X.IsPerfect K :=
  ⟨0, X.isPerfectComplex_of_isZero (isZero_zero _),
    ⟨(DerivedCategory.Q.map_isZero (isZero_zero _)).iso hK⟩⟩

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- Perfectness transports along an isomorphism of `D(𝒪)`: a perfect complex representing the
source represents the target as well. -/
theorem IsPerfect.of_iso {K K' : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
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

/-- **Stacks 08HK.**  Let `S` be a scheme, let `(U ⊆ X, j : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`, and set `T = |X| \ |U|`.  Let `E` be a
perfect object of `D(𝒪_V)` supported on `j^{-1}T`.  Then `Rj_*E` is a perfect object of
`D(𝒪_X)`.

This is the source's own two-sentence proof, granted its three inputs, each of which is a named
hypothesis here because the library does not have it: `hlocal` is that perfectness is local on
`X_étale`, `h2b` is clause (2)(b) of Stacks 08GG, and `hUzero` is the vanishing of the
restriction of `Rj_*E` to `U`.  The implementation notes of this file say exactly what each one
is and why it is missing.  Both `h2b` and `hUzero` are stated as implications from the support
hypothesis, which is where the support hypothesis of the source is used.

The two facts about perfectness the passage needs — that a zero object of `D(𝒪)` is perfect and
that perfectness transports along an isomorphism — are proved in this file for a ringed site,
unconditionally. -/
@[stacks 08HK "Rj_*E is a perfect object of D(O_X) for E perfect on V and supported on
j^{-1}T. CONDITIONAL on three named hypotheses, NONE of which is proved in the library, and
which together are the whole of the source's argument apart from the two perfectness facts
proved in this file. (i) hlocal: perfectness is local on X_etale along {U, V}, the first
sentence of the source's proof. The library's form of it, isPerfect_of_locally (Tag 08G5
through Tag 08G6 part (1)), is stated for a RingedSite.{u, u, 0} and the small etale ringed
site of an algebraic space is a RingedSite.{u + 1, u, u}, so it does not apply; the obstruction
is inherited from Tag 08FR, which needs the objects and the morphisms of the site in one
universe, and is NOT a missing covering. (ii) h2b: clause (2)(b) of Tag 08GG, that the counit
(Rj_*E)|_V to E is an isomorphism for supported E. SupportedOnComplement.lean proves clauses
(1)(a), (1)(b) and (2)(c) and records that (2)(a) and (2)(b) are unproved, the source getting
them by a base change of the square to V that the library does not carry. (iii) hUzero: the
vanishing of (Rj_*E)|_U, which the source gets from E|_{V minus j^{-1}T} = 0 and Tag 08GE; the
first half needs H^i(E|_Y) = H^i(E)|_Y, unavailable because Mathlib proves no commutation of
Functor.mapDerivedCategory with the homology functors, the same gap as the hypothesis hvan
there. Tag 08GE itself is proved. What IS proved: the source's deduction, with h2b and hUzero
taking the support hypothesis as antecedent so that it is genuinely consumed. Rj_* enters as a
right adjoint of derived restriction together with its adjunction, as in Tag 08HA"]
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
