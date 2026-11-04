module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorParasiticKernel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent

/-!
# Colimits and the quasi-coherent direct image (Stacks 0GQX)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks over a
scheme `S`. **Stacks 077A** builds the quasi-coherent direct image
`f_{QCoh,*} : QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)`, and its higher analogues `R^i f_{QCoh,*}`, as a composite
of three functors: the inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` of **Stacks 0778**, the étale
direct image `f_*` — respectively `R^i f_*` — restricted to `LQCoh^fbc`, and the coherator
`Q : LQCoh^fbc(𝒪_𝒴) ⥤ QCoh(𝒪_𝒴)` of **Stacks 0778**. **Stacks 0GQX** says that `f_{QCoh,*}` and
every `R^i f_{QCoh,*}` commute with direct sums and with filtered colimits.

The source's proof is one sentence: the composite commutes with those colimits because each of
its three factors does. That step is recorded here, for a composite whose middle factor is
carried as data. Since `f_{QCoh,*}` and the functors `R^i f_{QCoh,*}` differ only in which étale
direct image occupies the middle factor, it covers `f_{QCoh,*}` and every `R^i f_{QCoh,*}` at
once. The whole of **Stacks 0GQX**, filtered colimits included, is
`AlgebraicStacks.preservesCoproducts_and_filteredColimits_quasicoherentDirectImages_of_qcqs` in
`QuasicoherentDirectImageFilteredColimits.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.quasicoherentDirectImageOfEtale`: the composite of **Stacks 077A**,
  over the étale direct image on `LQCoh^fbc` as data. It is `f_{QCoh,*}` when that data is `f_*`
  and `R^i f_{QCoh,*}` when it is `R^i f_*`.

## What is proved and what is assumed

Of the three factors, the last is in hand: `Q` commutes with all colimits by **Stacks 0779**
part (3), which is proved as
`AlgebraicGeometry.Stack.preservesColimitsOfSize_flatBaseChangeQuasicoherator` over the chart
data `r` of the construction of **Stacks 0778**. That chart data, and the seven inputs the
coherator of **Stacks 0778** is built over, are reproduced here verbatim and consumed.

The other two factors are assumed, each by a single hypothesis naming a result of the source
which this library does not have.

* The *middle* factor is carried as data `D`, and the hypothesis on it is **Stacks 0GQW**: the
  étale direct image commutes with the colimit. **Stacks 0GQW** is proved, as
  `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf` and
  its étale companion, but it does not discharge the hypothesis. It is the statement for
  *abelian* sheaves along `CategoryTheory.Functor.sheafPushforwardCocontinuous`, not for the
  direct image of *modules* of **Stacks 06WE**; it reads the coefficients at universe
  `max (u + 1) a`, whereas `LQCoh^fbc` pins module sections to the universe `u` of the schemes;
  passing from all modules to the full subcategory `LQCoh^fbc` is the agreement of colimits of
  **Stacks 07AQ** part (2); and that form is itself conditional on the cohomology of the
  2-fibres of `f` commuting with the colimit, which the library's **Stacks 0GQV** does not supply,
  as the module docstring of
  `StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfHigherDirectImages.lean` records.
* The *first* factor, the inclusion `i` of **Stacks 0778**, is assumed to commute with the
  colimit. For colimits indexed in the universe `u` this is the hypothesis `hpres` that the
  coherator of **Stacks 0778** is already built over, and it is the agreement of the colimits of
  `LQCoh^fbc(𝒪_𝒳)` with those of the ambient modules, **Stacks 07AQ** part (2); only part (1) of
  that tag is proved.

Direct image on `LQCoh^fbc` is data rather than a functor built here for two reasons. It is
**Stacks 077A**, which is absent from the library; and it cannot be assembled from what is
available, because the higher direct images of modules on the sites of a stack,
`AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`, produce modules with sections in
`u + 1`, while `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeModules` pins them to
`u` — the universe gap which the docstring of
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_moduleSheafHigherDirectImage` records as a
generalization of **Stacks 03DN**. No `@[stacks 077A]` attribute is recorded below: the
composite *takes* the direct image as data, so an attribute on it would assert nothing.

Quasi-compactness and quasi-separatedness of `f` appear in no statement. The source uses them
only to produce the middle factor, by **Stacks 077A**, and to make it commute with the colimits,
by **Stacks 0GQW**; both of those are hypotheses here, so the two conditions stand behind them.
The library's **Stacks 0GQW** omits them for exactly the same reason.

## Implementation notes

The source of `f` is presented strictly, its structure functor written as the morphism's functor
followed by the structure functor of the target, which is the presentation the direct image along
`f` is stated in; compare `AlgebraicGeometry.Stack.IsLocallyQuasicoherentHigherDirectImage`. The
universes are those of `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator`: the site of a
stack is a `Type (u + 1)` with morphisms in `Type u`, essentially `u`-small, and the module
sections live in `u`.

Direct sums are colimits over a discrete diagram, `CategoryTheory.Discrete`, whose index type may
lie in any universe; the shape of a filtered colimit is an arbitrary category satisfying
`CategoryTheory.IsFiltered`. Both are the shapes the library's **Stacks 0GQW** and **Stacks 0779**
are stated at, so no size restriction is introduced beyond theirs.

## References

* [Stacks Project, Tag 0GQX](https://stacks.math.columbia.edu/tag/0GQX)
* [Stacks Project, Tag 0GQW](https://stacks.math.columbia.edu/tag/0GQW)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe uA vA uJ vJ u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
  [EssentiallySmall.{u} 𝒴.val.val.obj] (f : 𝒳 ⟶ 𝒴)
  (hincX : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom),
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) .etale).obj F).val)
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf))
  (hpres : PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids hinc))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids))
  (hlsD : LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids))

/-- The composite of **Stacks 077A**: the inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` of
**Stacks 0778**, then the étale direct image `D` on `LQCoh^fbc`, then the coherator
`Q : LQCoh^fbc(𝒪_𝒴) ⥤ QCoh(𝒪_𝒴)`. It is `f_{QCoh,*}` for `D = f_*` and `R^i f_{QCoh,*}` for
`D = R^i f_*`. -/
def quasicoherentDirectImageOfEtale
    (D : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids :=
  quasicoherentToFlatBaseChange B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) hincX ⋙
    D ⋙ flatBaseChangeQuasicoherator B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      hinc hclosed hpres hls hlsD hwp hsep

variable {𝒜 : Type uA} [Category.{vA} 𝒜]
  (r : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids ⥤ 𝒜)
  (hrcounit : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒴.val.val.p 𝒴.val.isFiberedInGroupoids,
    IsIso (r.map ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app F)))
  (hreq : (quasicoherentToFlatBaseChange B E h S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids hinc ⋙ r).IsEquivalence)
  (D : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids)

include hinc hrcounit hreq in
/-- The composite of **Stacks 077A** commutes with colimits of a shape `J` as soon as each of its
three factors does: the inclusion by `hpresX`, the étale direct image by `hD`, and the coherator
by **Stacks 0779** part (3) over the chart data `r`. -/
private theorem preservesColimitsOfShape_quasicoherentDirectImageOfEtale
    {J : Type uJ} [Category.{vJ} J]
    (hrcolim : PreservesColimitsOfSize.{vJ, uJ} r)
    (hpresX : PreservesColimitsOfShape J (quasicoherentToFlatBaseChange B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) hincX))
    (hD : PreservesColimitsOfShape J D) :
    PreservesColimitsOfShape J (quasicoherentDirectImageOfEtale B E h S hS f hincX hinc
      hclosed hpres hls hlsD hwp hsep D) := by
  have := hpresX
  have := hD
  have := (preservesColimitsOfSize_flatBaseChangeQuasicoherator B E h S hS 𝒴 hinc hclosed
    hpres hls hlsD hwp hsep r hrcounit hreq hrcolim).preservesColimitsOfShape (J := J)
  exact inferInstanceAs (PreservesColimitsOfShape J (_ ⋙ _ ⋙ _))

end AlgebraicGeometry.Stack

end
