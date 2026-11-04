module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardQuasicoherent

/-!
# The cohomology of a derived direct image on the quasi-coherent derived category

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks, and

`Rf_{QCoh,*} : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴)`

the functor that the diagram of **Stacks 07BC** induces on the bounded-below Verdier quotients of
**Stacks 07B6** (`AlgebraicGeometry.Stack.derivedPushforwardQuasicoherentPlus`). This file proves
the final assertion of that proposition: that the higher direct images `Rⁱf_QCoh` of
**Stacks 077A** are `Hⁱ ∘ Rf_{QCoh,*}`, with `Hⁱ` the cohomology functor of **Stacks 07B7**.

`Hⁱ` is the descent through the quotient functor of the composite `Q ∘ Hⁱ` on
`D⁺_{LQCoh^fbc}`, and the assertion is stated as the identification

`Q_𝒳 ⋙ Rf_{QCoh,*} ⋙ Hⁱ ≅ Rf_*^{LQCoh} ⋙ (Q ∘ Hⁱ)`

of functors on `D⁺_{LQCoh^fbc}(𝒪_𝒳)`. The quotient functor `Q_𝒳` is a localization, so this
determines `Rf_{QCoh,*} ⋙ Hⁱ`.

## Main definitions

* `AlgebraicGeometry.Stack.plusCohomologyQuasicoherent`: the functor `Q ∘ Hⁱ` of **Stacks 07B7**
  at the seating of **Stacks 07BC** — take the `i`-th cohomology module of a bounded-below
  complex in `D⁺_{LQCoh^fbc}(𝒪_𝒵)` and apply the coherator of **Stacks 0781** part (2) at
  section universe `u + 1`.
* `AlgebraicGeometry.Stack.plusCohomologyDerivedCategoryQuasicoherent`, with
  `AlgebraicGeometry.Stack.plusCohomologyDerivedCategoryQuasicoherentFac`: its descent
  `Hⁱ : D⁺_QCoh(𝒪_𝒵) ⥤ QCoh(𝒪_𝒵)` through the quotient functor, and the defining identity
  (104.5.1.1) of **Stacks 07B7** that the descent satisfies.

## Main results

* `AlgebraicGeometry.Stack.derivedPushforwardQuasicoherentPlus_comp_plusCohomology`: the final
  assertion of **Stacks 07BC**, for any functor on `D⁺_QCoh(𝒪_𝒴)` satisfying the defining
  identity of `Hⁱ`.
* `AlgebraicGeometry.Stack.derivedPushforwardQuasicoherentPlus_comp_plusCohomologyDerivedCategory`:
  the same for the descent built here.

## Implementation notes

### The seating, and why `Hⁱ` is rebuilt here

The cohomology functor of **Stacks 07B7**,
`AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherent`, is seated at module universe
`u`: its source is the unbounded Verdier quotient
`AlgebraicGeometry.Stack.derivedCategoryQuasicoherent` of `Mod(𝒪_𝒳)` at section universe `u`, and
its target is `FibredSite.quasicoherentModules.{u, u + 1, u, u}`.

`Rf_{QCoh,*}` cannot be moved there. The direct image of **Stacks 06WE** along a 1-morphism of
algebraic stacks is computed by limits indexed by the two sites, whose objects lie in
`Type (u + 1)`, so it produces modules with sections in `u + 1`
(`AlgebraicGeometry.Stack.fppfDerivedPushforwardPlus`). So the two functors the final assertion
composes live at different module universes, and the composite `Hⁱ ∘ Rf_{QCoh,*}` does not
typecheck with that `Hⁱ`.

The coherator of **Stacks 0778**, which that `Hⁱ` applies, is seated at module universe `u`
for the same reason `LQCoh^fbc` is: `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` is
stated at `FibredSite.quasicoherentModules.{u, u + 1, u, u}` and
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u}`. At `u + 1`
the coherator this library has is
`AlgebraicGeometry.FibredSite.moduleCoheratorSucc`, **Stacks 0781** part (2) — the right adjoint
of `QCoh(𝒪_𝒵) ⊆ Mod(𝒪_𝒵)` rather than of `QCoh(𝒪_𝒵) ⊆ LQCoh^fbc(𝒪_𝒵)`. The two agree on
`LQCoh^fbc(𝒪_𝒵)`: both are built as `A ↦ (⊤_ CostructuredArrow i A).left` from one existence
theorem, and **Stacks 077A** is seated at `u + 1` in the same way. So `Q ∘ Hⁱ` is formed here
with that coherator, and its three special-adjoint-functor-theorem inputs from **Stacks 0781**
part (1) — `hclosed`, `hwp`, `hsep` — are the same three hypotheses **Stacks 077A** carries.
This is the seating in which `Rⁱf_QCoh` of **Stacks 077A** itself lives:
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImageQuasicoherent` has exactly
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfQuasicoherentModules` as its target, which is the
target of `Q ∘ Hⁱ` below.

### The one hypothesis of the descent

`AlgebraicGeometry.Stack.plusCohomologyDerivedCategoryQuasicoherent` carries `hinv`, the
statement that `Q ∘ Hⁱ` inverts the class of morphisms the quotient of **Stacks 07B6** inverts.
At module universe `u` that statement is proved, as
`AlgebraicGeometry.Stack.isInvertedBy_cohomologyQuasicoherent`, from two inputs: that `Q ∘ Hⁱ` is
homological, and the kernel computation of **Stacks 0779** identifying the kernel of the
coherator with the parasitic modules. Neither input is available at `u + 1`: the kernel
computation `AlgebraicGeometry.Stack.isZero_flatBaseChangeQuasicoherator_iff_isParasitic` is
stated for the coherator of **Stacks 0778** at module universe `u`. So `hinv` is carried rather
than derived. It is not the conclusion and does not yield it: it mentions no 1-morphism and no
direct image, only the single stack `𝒵`.

The final assertion itself is proved over no such hypothesis. It takes any functor on
`D⁺_QCoh(𝒪_𝒴)` together with the defining identity of `Hⁱ`; the descent is one way to produce
that pair.

### What the assertion does not say

It is not asserted below that the right-hand side, restricted along the degree-zero embedding of
`QCoh(𝒪_𝒳)` into `D⁺_{LQCoh^fbc}(𝒪_𝒳)`, is `Rⁱf_QCoh` of **Stacks 077A** on the nose. That
restriction asks for the comparison between the `i`-th cohomology of the total derived functor
`CategoryTheory.Functor.rightDerivedFunctorPlus` of the direct image and its `i`-th right derived
functor `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`, which is not proved here; the
target of the right-hand side is `Rⁱf_QCoh`'s own category.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B7](https://stacks.math.columbia.edu/tag/07B7)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The cohomology functors at the seating of Stacks 07BC -/

section Cohomology

variable (𝒵 : AlgebraicStacks.{u, w} B S hS)
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)]
  (hclosed : FibredSite.QuasicoherentClosedUnderColimitsSucc B S hS 𝒵.val.val.p
    𝒵.val.isFiberedInGroupoids)
  (hwp : WellPowered.{u + 1} (AlgebraicStacks.fppfQuasicoherentModules B S hS 𝒵)ᵒᵖ)
  (hsep : HasSeparator (AlgebraicStacks.fppfQuasicoherentModules B S hS 𝒵))

/-- **The functor `Q ∘ Hⁱ : D⁺_{LQCoh^fbc}(𝒪_𝒵) ⥤ QCoh(𝒪_𝒵)` of Stacks 07B7**, at the seating of
**Stacks 07BC**: take the `i`-th cohomology module of a bounded-below complex of fppf modules at
section universe `u + 1`, and apply the coherator of **Stacks 0781** part (2) there.
Its target is the category `Rⁱf_QCoh` of **Stacks 077A** takes values in. -/
def plusCohomologyQuasicoherent (i : ℤ) :
    (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒵).FullSubcategory ⥤
      AlgebraicStacks.fppfQuasicoherentModules B S hS 𝒵 :=
  (derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒵).ι ⋙
    DerivedCategory.Plus.ι ⋙
      DerivedCategory.homologyFunctor (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵) i ⋙
        FibredSite.moduleCoheratorSucc B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids
          hclosed hwp hsep

/-- **Stacks 07B7 at the seating of Stacks 07BC: the cohomology functor

`Hⁱ : D⁺_QCoh(𝒪_𝒵) ⥤ QCoh(𝒪_𝒵)`.**

The descent of `Q ∘ Hⁱ` through the quotient functor of **Stacks 07B6**, given that `Q ∘ Hⁱ`
inverts the morphisms that quotient inverts (`hinv`). -/
def plusCohomologyDerivedCategoryQuasicoherent (i : ℤ)
    (hinv : (derivedQuasicoherentWPlus B E h S hS 𝒵).IsInvertedBy
      (plusCohomologyQuasicoherent B E h S hS 𝒵 hclosed hwp hsep i)) :
    derivedCategoryQuasicoherentPlus B E h S hS 𝒵 ⥤
      AlgebraicStacks.fppfQuasicoherentModules B S hS 𝒵 :=
  Localization.lift _ hinv (toDerivedCategoryQuasicoherentPlus B E h S hS 𝒵)

/-- **The defining identity (104.5.1.1) of Stacks 07B7**, at the seating of **Stacks 07BC**:
composed with the quotient functor `D⁺_{LQCoh^fbc}(𝒪_𝒵) ⥤ D⁺_QCoh(𝒪_𝒵)`, the cohomology functor
`Hⁱ` is the functor `Q ∘ Hⁱ` it descends. -/
def plusCohomologyDerivedCategoryQuasicoherentFac (i : ℤ)
    (hinv : (derivedQuasicoherentWPlus B E h S hS 𝒵).IsInvertedBy
      (plusCohomologyQuasicoherent B E h S hS 𝒵 hclosed hwp hsep i)) :
    toDerivedCategoryQuasicoherentPlus B E h S hS 𝒵 ⋙
        plusCohomologyDerivedCategoryQuasicoherent B E h S hS 𝒵 hclosed hwp hsep i hinv ≅
      plusCohomologyQuasicoherent B E h S hS 𝒵 hclosed hwp hsep i :=
  Localization.fac _ _ _

end Cohomology

/-! ### The final assertion of Stacks 07BC -/

section FinalAssertion

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]
  (hclosed : FibredSite.QuasicoherentClosedUnderColimitsSucc B S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids)
  (hwp : WellPowered.{u + 1} (AlgebraicStacks.fppfQuasicoherentModules B S hS 𝒴)ᵒᵖ)
  (hsep : HasSeparator (AlgebraicStacks.fppfQuasicoherentModules B S hS 𝒴))
  (f : 𝒳 ⟶ 𝒴)
  (hf : ∀ K, derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
    derivedLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
      ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K))
  (hdist : DerivedPushforwardMapsDistinguished B S hS f)
  (hpar : ∀ K, derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒳 K →
    derivedParasiticLocallyQuasicoherentFlatBaseChangePlus B E h S hS 𝒴
      ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K))

/-- **Stacks 07BC, the final assertion.** For a quasi-compact and quasi-separated 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks, the cohomology functor `Hⁱ` of **Stacks 07B7** composed with
the induced functor `Rf_{QCoh,*} : D⁺_QCoh(𝒪_𝒳) ⥤ D⁺_QCoh(𝒪_𝒴)` is the higher direct image of
**Stacks 077A**: precomposed with the quotient functor of `𝒳` it is the middle vertical functor
`Rf_*^{LQCoh}` of the diagram of **Stacks 07BC** followed by `Q ∘ Hⁱ`, which is `Q ∘ Rⁱf_*`.

`Hⁱ` is taken here as any functor on `D⁺_QCoh(𝒪_𝒴)` equipped with the defining identity `α`
(104.5.1.1); `AlgebraicGeometry.Stack.plusCohomologyDerivedCategoryQuasicoherent` is one. -/
@[stacks 07BC "the final assertion of the tag: the functors Rⁱf_QCoh of Stacks 077A are \
  Hⁱ ∘ Rf_(QCoh,*), read as the identification of Q_𝒳 ⋙ Rf_(QCoh,*) ⋙ Hⁱ with \
  Rf_*^LQCoh ⋙ (Q ∘ Hⁱ) over the defining identity (104.5.1.1) of Hⁱ, at the module universe \
  u + 1 that the derived direct image of Stacks 06WE on an algebraic stack lives in"]
def derivedPushforwardQuasicoherentPlus_comp_plusCohomology (i : ℤ)
    (H : derivedCategoryQuasicoherentPlus B E h S hS 𝒴 ⥤
      AlgebraicStacks.fppfQuasicoherentModules B S hS 𝒴)
    (α : toDerivedCategoryQuasicoherentPlus B E h S hS 𝒴 ⋙ H ≅
      plusCohomologyQuasicoherent B E h S hS 𝒴 hclosed hwp hsep i) :
    toDerivedCategoryQuasicoherentPlus B E h S hS 𝒳 ⋙
        derivedPushforwardQuasicoherentPlus B E h S hS f hf hdist hpar ⋙ H ≅
      derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange B E h S hS f hf ⋙
        plusCohomologyQuasicoherent B E h S hS 𝒴 hclosed hwp hsep i :=
  eqToIso (congrArg (fun G => G ⋙ H)
      (toDerivedCategoryQuasicoherentPlus_comp_derivedPushforwardQuasicoherentPlus
        B E h S hS f hf hdist hpar)) ≪≫
    Functor.isoWhiskerLeft _ α

/-- **Stacks 07BC, the final assertion**, for the cohomology functor
`AlgebraicGeometry.Stack.plusCohomologyDerivedCategoryQuasicoherent` built here: its defining
identity is `AlgebraicGeometry.Stack.plusCohomologyDerivedCategoryQuasicoherentFac`. -/
@[stacks 07BC "the final assertion of the tag for the cohomology functor Hⁱ built as the descent \
  of Q ∘ Hⁱ through the quotient of Stacks 07B6"]
def derivedPushforwardQuasicoherentPlus_comp_plusCohomologyDerivedCategory (i : ℤ)
    (hinv : (derivedQuasicoherentWPlus B E h S hS 𝒴).IsInvertedBy
      (plusCohomologyQuasicoherent B E h S hS 𝒴 hclosed hwp hsep i)) :
    toDerivedCategoryQuasicoherentPlus B E h S hS 𝒳 ⋙
        derivedPushforwardQuasicoherentPlus B E h S hS f hf hdist hpar ⋙
          plusCohomologyDerivedCategoryQuasicoherent B E h S hS 𝒴 hclosed hwp hsep i hinv ≅
      derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange B E h S hS f hf ⋙
        plusCohomologyQuasicoherent B E h S hS 𝒴 hclosed hwp hsep i :=
  derivedPushforwardQuasicoherentPlus_comp_plusCohomology B E h S hS hclosed hwp hsep f hf hdist
    hpar i _ (plusCohomologyDerivedCategoryQuasicoherentFac B E h S hS 𝒴 hclosed hwp hsep i hinv)

end FinalAssertion

end AlgebraicGeometry.Stack

end
