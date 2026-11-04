module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LisseEtaleDerivedQuasicoherentRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07B9 (1)(d): `D_QCoh(𝒪_𝒳)` computed on the lisse-étale site

Let `𝒳` be an algebraic stack and `g` the morphism of ringed topoi of **Stacks 0788** for the
lisse-étale site, with `g^*` restriction to the smooth objects and `Lg_!` its left adjoint
(**Stacks 07AS** (2)).  `LQCoh^fbc(𝒪_𝒳)` is the class with the flat base change property of
**Stacks 0762** read with the pullback of sheaves, and `𝒫_𝒳 = Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`.

As in the source, the argument of (2)(d) applies verbatim on the étale site: by (1)(a) and (1)(b)
`g^*` induces a functor
`c : D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⥤ D_QCoh(𝒪_{𝒳_{lisse,étale}})`,
`g^* Lg_! = id`, and by (1)(c) and (1)(b) the counit `Lg_! g^* E ⟶ E` is inverted by the quotient
functor, so `q ∘ Lg_!` is a quasi-inverse of `c`
(`CategoryTheory.Pretriangulated.quotientEquivalenceOfLeftAdjoint`).  Composing with the
equivalence of **Stacks 07B8** between that quotient and `D_QCoh(𝒪_𝒳)` (the Verdier quotient of
**Stacks 07B6**) gives (1)(d).

Everything here is stated at the standard models of the derived categories, named by `letI` in
the statements, which is where Stacks 07B3 (1) and hence (1)(c) are.  The category
`Mod(𝒳_étale, 𝒪_𝒳)` is read throughout at the spelling `SheafOfModules (lisseAmbientRing ..)` of
the source of `g^*`, which is `AlgebraicGeometry.Stack.etaleModules` up to unfolding.

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.etaleQuotientDerivedQuasicoherentEquivalence`: the
  equivalence `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ≌ D_QCoh(𝒪_{𝒳_{lisse,étale}})`
  with functor induced by `g^*` and inverse `q ∘ Lg_!`.
* `AlgebraicGeometry.Stack.LisseEtale.derivedQuasicoherentEquivalence`: **Stacks 07B9** (1)(d),
  `D_QCoh(𝒪_𝒳) ≌ D_QCoh(𝒪_{𝒳_{lisse,étale}})`.

## References

* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07B8](https://stacks.math.columbia.edu/tag/07B8)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DerivedCategory.KernelColocalization

universe u w

namespace AlgebraicGeometry.Stack.LisseEtale

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  Stacks.hasSheafCompose_forget₂_commRingCat Stacks.essentiallySmall_over

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The quotient of `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` by `D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)` is
`D_QCoh(𝒪_{𝒳_{lisse,étale}})`**: `g^*` induces a functor `c` by Stacks 07B9 (1)(a), (1)(b), and
`q ∘ Lg_!` is a quasi-inverse of it, by `g^* Lg_! = id` (Stacks 07AS (2)), Stacks 07B9 (1)(c) and
(1)(b).  This is the argument of the source for (2)(d), run on the lisse-étale site. -/
def etaleQuotientDerivedQuasicoherentEquivalence :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳))
    quotient (A := SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
        (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳) ≌
      (DerivedCategoryB.derivedCategoryB (lisseQuasicoherentModules B S hS 𝒳)).FullSubcategory :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳))
  letI := HasDerivedCategory.standard (etaleModules B S hS 𝒳)
  haveI : (DerivedCategoryB.derivedCategoryB (A := SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
      (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)).IsTriangulated :=
    DerivedCategoryB.derivedCategoryB_isTriangulated _
      (isWeakSerre_lisseAmbientModules B E h S hS 𝒳)
  haveI : ObjectProperty.IsClosedUnderIsomorphisms
      (DerivedCategoryB.derivedCategoryB (A := SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)) :=
    @DerivedCategoryB.isClosedUnderIsomorphisms_derivedCategoryB _ _ _ _ _
      (isWeakSerre_lisseAmbientModules B E h S hS 𝒳).isClosedUnderIsomorphisms
  haveI := isIso_derivedModuleLowerShriekAdjunction_unit B S hS 𝒳
  Pretriangulated.quotientEquivalenceOfLeftAdjoint (derivedModuleRestriction B S hS 𝒳)
    (derivedModuleLowerShriekAdjunction B S hS 𝒳)
    (DerivedCategoryB.derivedCategoryB (A := SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
      (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳))
    (DerivedCategoryB.derivedCategoryB (lisseQuasicoherentModules B S hS 𝒳))
    (derivedInter (A := SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
      (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
      (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳))
    (fun K hK => derivedCategoryB_derivedModuleRestriction B E h S hS 𝒳 K hK)
    (derivedCategoryB_derivedModuleLowerShriek B E h S hS 𝒳)
    (fun K hK => (isZero_derivedModuleRestriction_iff_derivedParasitic B E h S hS 𝒳 K
      (fun n => (hK n).2)).2 hK)
    (toQuotient (A := SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
      (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
      (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳))
    (fun K hK hK0 => (isZero_derivedModuleRestriction_iff_derivedParasitic B E h S hS 𝒳 K hK).1 hK0)

/-- **Stacks 07B9** (1)(d).  Restriction `g^*` to the lisse-étale site and `Lg_!` define mutually
inverse equivalences between `D_QCoh(𝒪_𝒳)` — the Verdier quotient
`D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of Stacks 07B6 — and
`D_QCoh(𝒪_{𝒳_{lisse,étale}})`, the flat base change property of Stacks 0762 being read with the
pullback of sheaves.

As in the source, `D_QCoh(𝒪_𝒳)` is identified with
`D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)` by Stacks 07B8
(`AlgebraicGeometry.Stack.derivedCategoryQuasicoherentEtaleSheafFlatBaseChangeEquivalence`, induced
by `ε^*`), and on that quotient `g^*` and `q ∘ Lg_!` are mutually inverse
(`AlgebraicGeometry.Stack.LisseEtale.etaleQuotientDerivedQuasicoherentEquivalence`).  Stated at the
standard models of the derived categories, where Stacks 07B3 (1) is. -/
@[stacks 07B9 "part (1)(d): g^* and Lg_! define mutually inverse equivalences between \
D_QCoh(𝒪_𝒳), the Verdier quotient of Stacks 07B6, and D_QCoh(𝒪_{𝒳_lisse,étale}), through the \
equivalence of Stacks 07B8; the inverse is q ∘ ε^* ∘ Lg_! \
(derivedQuasicoherentEquivalenceInverseIso); for LQCoh^fbc with the flat base change property \
of Stacks 0762 read with the pullback of sheaves, at module universe u, at the standard models \
of the derived categories"]
def derivedQuasicoherentEquivalence :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳))
    ParasiticQuotient.quotient B S hS 𝒳
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) ≌
      (DerivedCategoryB.derivedCategoryB (lisseQuasicoherentModules B S hS 𝒳)).FullSubcategory :=
  letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  letI := HasDerivedCategory.standard (etaleModules B S hS 𝒳)
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳))
  (derivedCategoryQuasicoherentEtaleSheafFlatBaseChangeEquivalence B E h S hS 𝒳).symm.trans
    (etaleQuotientDerivedQuasicoherentEquivalence B E h S hS 𝒳)

/-- The inverse of Stacks 07B9 (1)(d) is `Lg_!`: it is `Lg_!` on `D_QCoh(𝒪_{𝒳_{lisse,étale}})`
(landing in `D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` by Stacks 07B9 (1)(c)), followed by `ε^*` and the
quotient functor onto `D_QCoh(𝒪_𝒳)`. -/
def derivedQuasicoherentEquivalenceInverseIso :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (etaleModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳))
    (derivedQuasicoherentEquivalence B E h S hS 𝒳).inverse ≅
      Pretriangulated.leftAdjointOfClass
          (DerivedCategoryB.derivedCategoryB
            (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳))
          (DerivedCategoryB.derivedCategoryB (lisseQuasicoherentModules B S hS 𝒳))
          (derivedCategoryB_derivedModuleLowerShriek B E h S hS 𝒳) ⋙
        epsilonPullbackDerivedSheafFlatBaseChange B E h S hS 𝒳 ⋙
          ParasiticQuotient.toQuotient B S hS 𝒳
            (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) :=
  letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  letI := HasDerivedCategory.standard (etaleModules B S hS 𝒳)
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳))
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (toQuotientCompDerivedCategoryQuasicoherentEtaleSheafFlatBaseChangeEquivalenceIso
      B E h S hS 𝒳)

end AlgebraicGeometry.Stack.LisseEtale
