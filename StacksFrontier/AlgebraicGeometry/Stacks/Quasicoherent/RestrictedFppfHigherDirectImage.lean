module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictedStackHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcFppfHigherDirectImage

/-!
# Stacks 0GQH

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact, quasi-separated 1-morphism of algebraic stacks which is
representable by algebraic spaces, let `ℱ` be in `LQCoh^{fbc}(𝒪_𝒳)`, and let `y : V ⟶ 𝒴` be an
object of `𝒴` over a scheme `V`. Then `U = V ×_𝒴 𝒳` is an algebraic space and, for the base
change `f' : U ⟶ V` of `f`,

```text
(Rⁱf_*ℱ)|_{V_étale} = Rⁱf'_{small,*}(ℱ|_{U_étale}).
```

Here `Rⁱf_*` is the higher direct image of `Mod(𝒪_𝒳)`, the fppf topology,
`AlgebraicGeometry.Stack.fppfModulesHigherDirectImage`.

`Mod(𝒪_𝒳)` is `AlgebraicGeometry.Stack.StackModules`, the sheaves of `𝒪_𝒳`-modules whose modules
of sections lie in the universe `u` of the schemes of the site. That is the source's setting: a
sheaf on `(Sch/S)_{fppf}` is a sheaf of sets, read here as sets of the universe `u` the site is
built in, and `Rⁱf_*` is defined on that category. The membership `ℱ ∈ LQCoh^{fbc}(𝒪_𝒳)` is
accordingly read at that universe.

`AlgebraicGeometry.Space.restrictedHigherDirectImageChartIso` is an earlier form of the identity,
for total derived direct images, which takes the base change isomorphism of Stacks 075H as an
argument; the statement here does not.

The proof is the source's. **Stacks 0771 (4)(a)**,
`AlgebraicGeometry.Stack.nonempty_etaleComparison_fppfModulesHigherDirectImage_iso`, says that
`Rⁱf_*ℱ` may be computed in the étale topology. The étale identity is
`AlgebraicGeometry.Stack.restrictedStackModuleHigherDirectImageIsoOfScheme`, which combines
**Stacks 075H** and **Stacks 075N**. That `U` is an algebraic space is **Stacks 0300**,
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_twoFibreProduct`.

## Main results

* `AlgebraicGeometry.Stack.restrictedFppfModulesHigherDirectImage`: **Stacks 0GQH**.

## References

* [Stacks Project, Tag 0GQH](https://stacks.math.columbia.edu/tag/0GQH)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u t

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GQH.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact (`hqc`), quasi-separated (`hqs`)
1-morphism of algebraic stacks which is representable by algebraic spaces (`hrep`). Let `ℱ` be in
`LQCoh^{fbc}(𝒪_𝒳)` (`hF`), and let `y : V ⟶ 𝒴` be an object of `𝒴` over a scheme `V`. Then:

* the 2-fibre product `U = V ×_𝒴 𝒳` is represented by an algebraic space;
* for every such presentation `eU` of `U` by an algebraic space, with `f' : U ⟶ V` the base
  change of `f` (`AlgebraicGeometry.Stack.baseChangeSpacesHom`), and for every `i`,
  `(Rⁱf_*ℱ)|_{V_étale} ≅ Rⁱf'_{small,*}(ℱ|_{U_étale})`.

Here `Rⁱf_*` is the higher direct image of `Mod(𝒪_𝒳)`, in the fppf topology. `(-)|_{V_étale}` reads
an fppf module on the étale site (`stackModulesEtaleComparison`), pulls it back along `y` and
restricts it to the small étale site of `V` (`π_{V,*}`, Stacks 073M). `(-)|_{U_étale}` does the
same along the projection `U ⟶ 𝒳`. `f'_{small,*}` is the direct image of the small étale sites
of the algebraic spaces `U` and `V`. -/
@[stacks 0GQH "the whole lemma, with Mod(O_X) the sheaves of modules at the universe u of the \
  schemes (the source's setting): for f : X -> Y quasi-compact, quasi-separated and \
  representable by algebraic spaces, F in LQCoh^fbc(O_X) \
  (the flat base change property read on sheaves, Stacks 0762) and an object y : V -> Y over a \
  scheme V, the 2-fibre product U = V x_Y X is an algebraic space, and for every presentation \
  of it and every i, (R^i f_* F)|_{V_etale} = R^i f'_{small,*}(F|_{U_etale}), with R^i f_* the \
  fppf higher direct image of Mod(O_X)"]
theorem restrictedFppfModulesHigherDirectImage {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (F : StackModules B S hS .fppf 𝒳) (hF : lqcohSheafFbcFppfModules.{u, t, u} B E h S hS 𝒳 F)
    {V : BigFppfOver B S hS} (y : schemeStack.{u, t} B S hS V ⟶ 𝒴) :
    (∃ U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS U ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val.p
        (presheafOfCategories (U ⋙ typeToCat)).p)) ∧
    ∀ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
      (eU : StacksRepresentableCFG.EquivalenceOver
        (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val.p
        (presheafOfCategories (U ⋙ typeToCat)).p) (i : ℕ),
      Nonempty ((AlgebraicGeometry.RingedToposHom.pushforwardModules
          (Space.projectionRingedToposHom B S hS (yoneda.obj V)
            (schemeStack.{u, t} B S hS V).val.val.p
            (schemeStack.{u, t} B S hS V).val.isFiberedInGroupoids
            (isAlgebraicSpace_yoneda B S hS V) (schemeStackEquivalenceOver B S hS))).obj
          ((stackModuleInverseImage B S hS .etale y).obj
            ((stackModulesEtaleComparison B S hS 𝒴).obj
              ((fppfModulesHigherDirectImage B S hS f i).obj F))) ≅
        (Space.smallEtaleHigherDirectImage
            (baseChangeSpacesHom B S hS f y (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
              (schemeStackEquivalenceOver B S hS) U hU eU) i).obj
          ((AlgebraicGeometry.RingedToposHom.pushforwardModules
            (Space.projectionRingedToposHom B S hS U
              (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.val.p
              (twoFibreProductSquareAlgebraicStacks B S hS f y).pt.val.isFiberedInGroupoids
              hU eU)).obj
            ((stackModuleInverseImage B S hS .etale
              (twoFibreProductSquareAlgebraicStacks B S hS f y).fst).obj
              ((stackModulesEtaleComparison B S hS 𝒳).obj F)))) := by
  refine ⟨exists_isAlgebraicSpace_equivalenceOver_twoFibreProduct B S hS f y hrep,
    fun U hU eU i => ?_⟩
  obtain ⟨e⟩ := nonempty_etaleComparison_fppfModulesHigherDirectImage_iso B E h S hS f hqc hqs F
    hF i
  exact ⟨(AlgebraicGeometry.RingedToposHom.pushforwardModules
      (Space.projectionRingedToposHom B S hS (yoneda.obj V)
        (schemeStack.{u, t} B S hS V).val.val.p
        (schemeStack.{u, t} B S hS V).val.isFiberedInGroupoids
        (isAlgebraicSpace_yoneda B S hS V) (schemeStackEquivalenceOver B S hS))).mapIso
      ((stackModuleInverseImage B S hS .etale y).mapIso e) ≪≫
    restrictedStackModuleHigherDirectImageIsoOfScheme B S hS f y U hU eU i _⟩

end AlgebraicGeometry.Stack
