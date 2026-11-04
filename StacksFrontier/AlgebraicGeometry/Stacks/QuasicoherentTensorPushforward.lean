module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePullbackMap
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroCupProductAndCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors

/-!
# The quasi-coherent direct image of the structure sheaf of a 2-fibre product

Let `a : 𝒴 ⟶ 𝒳` and `b : 𝒵 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`, each
representable by schemes, quasi-compact, quasi-separated and flat, let `𝒫 = 𝒴 ×_𝒳 𝒵` and let
`f : 𝒫 ⟶ 𝒳` be the projection.  **Stacks 0GRN** says

`a_{QCoh, *}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh, *}𝒪_𝒵 = f_{QCoh, *}𝒪_𝒫`

in `QCoh(𝒪_𝒳)`, the tensor product being the monoidal product of
`AlgebraicGeometry.FibredSite.monoidalCategoryQuasicoherentModules` and the three direct images
being the functor `f_{QCoh, *}` of **Stacks 077A**, written as the composite `Q ∘ f_* ∘ i`.
As printed, Stacks 0GRN is false
(`AlgebraicGeometry.Stack.AlgebraicStacks.not_forall_nonempty_tensorPushforwardUnits_iso`), and
the invertibility statements here are conditional on the invertibility of `μ` after a functor
reflecting isomorphisms.

The canonical map

`μ : a_{QCoh, *}𝒪_𝒴 ⊗ b_{QCoh, *}𝒪_𝒵 ⟶ f_{QCoh, *}𝒪_𝒫`

is the tensor product of the relative pullback maps of **Stacks 06UM** along the two legs
`𝒫 ⟶ 𝒴` and `𝒫 ⟶ 𝒵`, read in `QCoh(𝒪_𝒳)` through the coherator `Q` of **Stacks 0778**,
followed by the relative cup product of **Remark 0GQR** carried through `Q`.

## Main definitions

* `AlgebraicGeometry.Stack.locallyQuasicoherentStructurePullbackMap`: for a factorization
  `𝒫 ⟶ 𝒲 ⟶ 𝒳` of algebraic stacks, the relative pullback map `w_*𝒪_𝒲 ⟶ f_*𝒪_𝒫` on
  `LQCoh^fbc(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.quasicoherentRelativePullbackMap`: the same map read in
  `QCoh(𝒪_𝒳)` through the coherator `Q` of **Lemma 0778**, i.e.
  `w_{QCoh, *}𝒪_𝒲 ⟶ f_{QCoh, *}𝒪_𝒫`.
* `AlgebraicGeometry.Stack.quasicoherentTensorPushforwardMap`: the canonical map `μ`.

## Main results

* `AlgebraicGeometry.Stack.quasicoherentTensorPushforwardMap_eq_coheratorCupProduct`: `μ` is the
  comparison of **Remark 0GQR** attached to the naive relative cup product precomposed with the
  two relative pullback maps on `LQCoh^fbc(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.map_quasicoherentTensorPushforwardMap_comp_counit`: the diagram of
  **Remark 0GQR** at `μ` commutes.
* `AlgebraicGeometry.Stack.isIso_quasicoherentTensorPushforwardMap` and
  `AlgebraicGeometry.Stack.quasicoherentTensorPushforwardIso`: `μ` is an isomorphism, and hence
  `a_{QCoh, *}𝒪_𝒴 ⊗ b_{QCoh, *}𝒪_𝒵 ≅ f_{QCoh, *}𝒪_𝒫`, provided `μ` becomes invertible under a
  functor reflecting isomorphisms.
* `AlgebraicGeometry.Stack.isIso_quasicoherentTensorPushforwardMap_of_isIso_sheafMap`: `μ` is an
  isomorphism provided its underlying map of sheaves of modules on the fppf site of `𝒳` is.

## Implementation notes

**Direct images.**  Every quasi-coherent direct image is written as the composite of
**Stacks 077A**: the inclusion `i : QCoh(𝒪_𝒫) → LQCoh^fbc(𝒪_𝒫)` of **Lemma 0778**
(`AlgebraicGeometry.Stack.quasicoherentToFlatBaseChange`), the direct image `f_*` on `LQCoh^fbc`
of **Proposition 0771**, and the coherator `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Lemma 0778**
(`AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator`).  So `f_{QCoh, *}𝒪_𝒫` reads
`Q (f_* (i 𝒪_𝒫))`.  The functor `AlgebraicGeometry.Stack.quasicoherentPushforward` lives at
module universe `u + 1`, where neither `AlgebraicGeometry.FibredSite.quasicoherentTensorObj` nor
`AlgebraicGeometry.FibredSite.quasicoherentTensorUnit` exists: the monoidal structure of
Tag 05NA requires the module universe to equal the universe of the coefficient rings.

**The 2-fibre product.**  `𝒫` is the apex of a 2-commutative square `sq` over the cospan
`(a, b)` that is a 2-fibre product in the 2-category of algebraic stacks; the canonical such
square `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` is one by
`AlgebraicGeometry.Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks`
(**Stacks 04T2**).  The projection `f : 𝒫 ⟶ 𝒳` is `sq.fst ≫ a`, 2-isomorphic to `sq.snd ≫ b`
by `sq.iso`.

**Data.**  The direct images `aStar`, `bStar`, `fStar` on `LQCoh^fbc` and the inverse-image
adjunctions on `LQCoh^fbc` are the data of **Proposition 0771**, with `fStar` related to the
other two by `cmpY : prStarY ⋙ aStar ≅ fStar` and `cmpZ : prStarZ ⋙ bStar ≅ fStar`.  The data
`hincX`, `hincY`, `hincZ`, `hincP`, `hclosed`, `hpres`, `hls`, `hlsD`, `hwp`, `hsep` are the
inputs of the coherator of **Lemma 0778**.  The tensor product `TLQ` on `LQCoh^fbc(𝒪_𝒳)` and the
comparison `tcmp` carrying the monoidal product of `QCoh(𝒪_𝒳)` into it are the monoidality half
of **Lemma 0GQM**.  The map `cup` is the naive relative cup product of **Tag 0FPJ** for `f` at
`(𝒪_𝒫, 𝒪_𝒫)`, followed by `f_*` of the unitor `𝒪_𝒫 ⊗ 𝒪_𝒫 ≅ 𝒪_𝒫`: the right vertical arrow of
**Remark 0GQR**.

**Invertibility.**  The étale-local step is the hypothesis `hchart`, that `μ` becomes invertible
under a functor `res` reflecting isomorphisms; in Stacks, `res` is restriction to `U_étale` for a
smooth surjective `U → 𝒳`.  The hypotheses that `a` and `b` are representable, quasi-compact,
quasi-separated and flat appear in the statements but are not used in the proofs.

## References

* [Stacks Project, Tag 0GRN](https://stacks.math.columbia.edu/tag/0GRN)
* [Stacks Project, Tag 06UM](https://stacks.math.columbia.edu/tag/06UM)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 0FPJ](https://stacks.math.columbia.edu/tag/0FPJ)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 0GQR](https://stacks.math.columbia.edu/tag/0GQR)
* [Stacks Project, Tag 0GQH](https://stacks.math.columbia.edu/tag/0GQH)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DegreeZeroCupProduct
open scoped CategoryTheory.Prod

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

section RelativePullback

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (hE : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒲 𝒬 : AlgebraicStacks.{u, w} B S hS}
  [EssentiallySmall.{u} 𝒳.val.val.obj] [EssentiallySmall.{u} 𝒲.val.val.obj]
  [EssentiallySmall.{u} 𝒬.val.val.obj]
  (hincX : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS 𝒳.val.val.p 𝒳.val.property
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒳.val.property
        .etale).obj F).val)
  (hincW : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒲.val.val.p 𝒲.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS 𝒲.val.val.p 𝒲.val.property
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒲.val.val.p 𝒲.val.property
        .etale).obj F).val)
  (hincP : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒬.val.val.p 𝒬.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS 𝒬.val.val.p 𝒬.val.property
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒬.val.val.p 𝒬.val.property
        .etale).obj F).val)
  (wStar : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒲.val.val.p 𝒲.val.property ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒳.val.val.p 𝒳.val.property)
  (fStar : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒬.val.val.p 𝒬.val.property ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒳.val.val.p 𝒳.val.property)
  (pr : 𝒬 ⟶ 𝒲)
  (hlq : ∀ M : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒲.val.val.p 𝒲.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS 𝒬.val.val.p 𝒬.val.property
      ((modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒬.val.val.p 𝒲.val.val.p
        𝒬.val.property 𝒲.val.property (CatFiberedInGroupoids.homFunctor pr.hom)
        pr.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)).obj M.obj).val)
  (prStar : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒬.val.val.p 𝒬.val.property ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒲.val.val.p 𝒲.val.property)
  (adjPr : locallyQuasicoherentFlatBaseChangePullback B E hE S hS
      𝒬.val.val.p 𝒬.val.property 𝒲.val.val.p 𝒲.val.property
      (CatFiberedInGroupoids.homFunctor pr.hom) pr.hom.hom.w hlq ⊣ prStar)
  (cmp : prStar ⋙ wStar ≅ fStar)

/-- **The relative pullback map on `LQCoh^fbc` at the structure sheaf.**  For a factorization
`𝒬 --pr--> 𝒲 --w--> 𝒳` of 1-morphisms of algebraic stacks with direct images `wStar`, `fStar`
on `LQCoh^fbc` identified by `cmp : pr_* ⋙ w_* ≅ f_*`, the relative pullback map at the
structure sheaf of `𝒲`, followed by `f_*` of the identification `pr^*𝒪_𝒲 ≅ 𝒪_𝒬` of
`AlgebraicGeometry.Stack.locallyQuasicoherentStructureSheafPullbackIso`:

`w_*𝒪_𝒲 ⟶ f_*(pr^*𝒪_𝒲) ⟶ f_*𝒪_𝒬`. -/
@[stacks 06UM "the relative pullback map w_*𝒪_𝒲 ⟶ f_*𝒪_𝒬 at the structure sheaf of the middle \
stack of a factorization 𝒬 ⟶ 𝒲 ⟶ 𝒳 of algebraic stacks, on LQCoh^fbc, for direct images \
wStar, fStar and an adjunction adjPr with an identification cmp : prStar ⋙ wStar ≅ fStar"]
def locallyQuasicoherentStructurePullbackMap :
    wStar.obj ((quasicoherentToFlatBaseChange B E hE S hS 𝒲.val.val.p 𝒲.val.property hincW).obj
        (FibredSite.quasicoherentTensorUnit B S hS 𝒲.val.val.p 𝒲.val.property)) ⟶
      fStar.obj ((quasicoherentToFlatBaseChange B E hE S hS
          𝒬.val.val.p 𝒬.val.property hincP).obj
        (FibredSite.quasicoherentTensorUnit B S hS 𝒬.val.val.p 𝒬.val.property)) :=
  (locallyQuasicoherentFlatBaseChangeRelativePullback B E hE S hS
        𝒳.val.val.p 𝒳.val.property 𝒲.val.val.p 𝒲.val.property 𝒬.val.val.p 𝒬.val.property
        (CatFiberedInGroupoids.homFunctor pr.hom) pr.hom.hom.w hlq prStar adjPr
        wStar fStar cmp).app
      ((quasicoherentToFlatBaseChange B E hE S hS 𝒲.val.val.p 𝒲.val.property hincW).obj
        (FibredSite.quasicoherentTensorUnit B S hS 𝒲.val.val.p 𝒲.val.property)) ≫
    fStar.map (locallyQuasicoherentStructureSheafPullbackIso B E hE S hS
      𝒲.val.val.p 𝒲.val.property 𝒬.val.val.p 𝒬.val.property
      (CatFiberedInGroupoids.homFunctor pr.hom) pr.hom.hom.w hincW hincP hlq).hom

variable (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.property .fppf))
  (hpres : PreservesColimitsOfSize.{u, u}
    (quasicoherentToFlatBaseChange B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.property))
  (hlsD : LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
    𝒳.val.val.p 𝒳.val.property))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.property)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.property))

/-- **The relative pullback map in `QCoh(𝒪_𝒳)` at the structure sheaf.**  The coherator `Q` of
**Lemma 0778** applied to
`AlgebraicGeometry.Stack.locallyQuasicoherentStructurePullbackMap`.  Its source and target are
the three-step composite `Q ∘ w_* ∘ i` of **Stacks 077A** at the structure sheaf, so this is a
map

`w_{QCoh, *}𝒪_𝒲 ⟶ f_{QCoh, *}𝒪_𝒬`

in `QCoh(𝒪_𝒳)`. -/
@[stacks 06UM "the relative pullback map w_{QCoh,*}𝒪_𝒲 ⟶ f_{QCoh,*}𝒪_𝒬 in QCoh(𝒪_𝒳), the \
coherator of Lemma 0778 applied to the map on LQCoh^fbc, over the same data of Proposition 0771 \
together with the coherator inputs hincX, hclosed, hpres, hls, hlsD, hwp, hsep of Lemma 0778"]
def quasicoherentRelativePullbackMap :
    (flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed hpres
          hls hlsD hwp hsep).obj
        (wStar.obj ((quasicoherentToFlatBaseChange B E hE S hS 𝒲.val.val.p 𝒲.val.property
          hincW).obj (FibredSite.quasicoherentTensorUnit B S hS 𝒲.val.val.p 𝒲.val.property))) ⟶
      (flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed hpres
          hls hlsD hwp hsep).obj
        (fStar.obj ((quasicoherentToFlatBaseChange B E hE S hS 𝒬.val.val.p 𝒬.val.property
          hincP).obj (FibredSite.quasicoherentTensorUnit B S hS 𝒬.val.val.p 𝒬.val.property))) :=
  (flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed hpres
      hls hlsD hwp hsep).map
    (locallyQuasicoherentStructurePullbackMap B E hE S hS hincW hincP wStar fStar pr hlq
      prStar adjPr cmp)

end RelativePullback

section TensorPushforward

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (hE : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
  [EssentiallySmall.{u} 𝒳.val.val.obj]
  (a : 𝒴 ⟶ 𝒳) (b : 𝒵 ⟶ 𝒳) (sq : Bicategory.TwoCommSq a b)
  (hincX : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS 𝒳.val.val.p 𝒳.val.property
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒳.val.property
        .etale).obj F).val)
  (hincY : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒴.val.val.p 𝒴.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS 𝒴.val.val.p 𝒴.val.property
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p 𝒴.val.property
        .etale).obj F).val)
  (hincZ : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒵.val.val.p 𝒵.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS 𝒵.val.val.p 𝒵.val.property
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒵.val.val.p 𝒵.val.property
        .etale).obj F).val)
  (hincP : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      sq.pt.val.val.p sq.pt.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS sq.pt.val.val.p sq.pt.val.property
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS sq.pt.val.val.p sq.pt.val.property
        .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.property .fppf))
  (hpres : PreservesColimitsOfSize.{u, u}
    (quasicoherentToFlatBaseChange B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.property))
  (hlsD : LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
    𝒳.val.val.p 𝒳.val.property))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.property)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.property))
  (aStar : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒴.val.val.p 𝒴.val.property ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒳.val.val.p 𝒳.val.property)
  (bStar : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒵.val.val.p 𝒵.val.property ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒳.val.val.p 𝒳.val.property)
  (fStar : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      sq.pt.val.val.p sq.pt.val.property ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒳.val.val.p 𝒳.val.property)
  (hlqY : ∀ M : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒴.val.val.p 𝒴.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS sq.pt.val.val.p sq.pt.val.property
      ((modulePullback.{u, u + 1, u, u, u + 1, u} B S hS sq.pt.val.val.p
        𝒴.val.val.p sq.pt.val.property 𝒴.val.property
        (CatFiberedInGroupoids.homFunctor sq.fst.hom) sq.fst.hom.hom.w
        (etaleTopology B) (etaleTopology_le_topology B)).obj M.obj).val)
  (prStarY : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      sq.pt.val.val.p sq.pt.val.property ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒴.val.val.p 𝒴.val.property)
  (adjPrY : (locallyQuasicoherentFlatBaseChangePullback B E hE S hS
      sq.pt.val.val.p sq.pt.val.property 𝒴.val.val.p 𝒴.val.property
      (CatFiberedInGroupoids.homFunctor sq.fst.hom) sq.fst.hom.hom.w hlqY) ⊣ prStarY)
  (cmpY : prStarY ⋙ aStar ≅ fStar)
  (hlqZ : ∀ M : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒵.val.val.p 𝒵.val.property,
    IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS sq.pt.val.val.p sq.pt.val.property
      ((modulePullback.{u, u + 1, u, u, u + 1, u} B S hS sq.pt.val.val.p
        𝒵.val.val.p sq.pt.val.property 𝒵.val.property
        (CatFiberedInGroupoids.homFunctor sq.snd.hom) sq.snd.hom.hom.w
        (etaleTopology B) (etaleTopology_le_topology B)).obj M.obj).val)
  (prStarZ : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      sq.pt.val.val.p sq.pt.val.property ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒵.val.val.p 𝒵.val.property)
  (adjPrZ : (locallyQuasicoherentFlatBaseChangePullback B E hE S hS
      sq.pt.val.val.p sq.pt.val.property 𝒵.val.val.p 𝒵.val.property
      (CatFiberedInGroupoids.homFunctor sq.snd.hom) sq.snd.hom.hom.w hlqZ) ⊣ prStarZ)
  (cmpZ : prStarZ ⋙ bStar ≅ fStar)
  (TLQ : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒳.val.val.p 𝒳.val.property ×
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒳.val.val.p 𝒳.val.property ⥤
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS
      𝒳.val.val.p 𝒳.val.property)
  (tcmp : (Functor.uncurry.obj (FibredSite.quasicoherentTensorBifunctor B S hS
      𝒳.val.val.p 𝒳.val.property)) ⋙
      (quasicoherentToFlatBaseChange B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX) ⟶
    (quasicoherentToFlatBaseChange B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX).prod
        (quasicoherentToFlatBaseChange B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX) ⋙ TLQ)
  (cup : TLQ.obj (fStar.obj ((quasicoherentToFlatBaseChange B E hE S hS sq.pt.val.val.p
      sq.pt.val.property hincP).obj
        (FibredSite.quasicoherentTensorUnit B S hS sq.pt.val.val.p sq.pt.val.property)),
      fStar.obj ((quasicoherentToFlatBaseChange B E hE S hS sq.pt.val.val.p sq.pt.val.property
          hincP).obj
        (FibredSite.quasicoherentTensorUnit B S hS sq.pt.val.val.p sq.pt.val.property))) ⟶
    fStar.obj ((quasicoherentToFlatBaseChange B E hE S hS sq.pt.val.val.p sq.pt.val.property
        hincP).obj
        (FibredSite.quasicoherentTensorUnit B S hS sq.pt.val.val.p sq.pt.val.property)))

/-- **The canonical map `μ`.**  For 1-morphisms `a : 𝒴 ⟶ 𝒳`, `b : 𝒵 ⟶ 𝒳` of
algebraic stacks and a 2-fibre product square `sq` over the cospan `(a, b)` with apex
`𝒫 = 𝒴 ×_𝒳 𝒵` and projection `f = sq.fst ≫ a`, the map

`μ : a_{QCoh, *}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh, *}𝒪_𝒵 ⟶ f_{QCoh, *}𝒪_𝒫`

given by the tensor product of the two relative pullback maps
`AlgebraicGeometry.Stack.quasicoherentRelativePullbackMap` along the legs `sq.fst` and `sq.snd`,
followed by the comparison of **Remark 0GQR** attached to the coherator of
**Lemma 0778** at the relative cup product `cup`. -/
@[stacks 0GRN "THE CANONICAL MAP ONLY, NOT THE ASSERTION. This is \
μ : a_{QCoh,*}𝒪_𝒴 ⊗ b_{QCoh,*}𝒪_𝒵 ⟶ f_{QCoh,*}𝒪_𝒫, built from the two relative pullback maps \
of Stacks 06UM and the comparison of Remark 0GQR. Its INVERTIBILITY, which is what the tag \
asserts, is NOT PROVED here: the étale-local step (the content of Cohomology of Stacks \
Section 103.12, namely Lemma 0GQH plus the scheme-level Künneth of Lemma 0FLQ) does not \
compose with the stack-level QCoh monoidal product without further infrastructure. The \
reduction lemmas below that conclude invertibility from invertibility after a reflecting \
functor are deliberately left UNTAGGED, being instances of \
CategoryTheory.isIso_of_reflects_iso rather than content of this tag"]
def quasicoherentTensorPushforwardMap :
    FibredSite.quasicoherentTensorObj B S hS 𝒳.val.val.p 𝒳.val.property
        ((flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed
            hpres hls hlsD hwp hsep).obj
          (aStar.obj ((quasicoherentToFlatBaseChange B E hE S hS 𝒴.val.val.p 𝒴.val.property
            hincY).obj (FibredSite.quasicoherentTensorUnit B S hS 𝒴.val.val.p 𝒴.val.property))))
        ((flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed
            hpres hls hlsD hwp hsep).obj
          (bStar.obj ((quasicoherentToFlatBaseChange B E hE S hS 𝒵.val.val.p 𝒵.val.property
            hincZ).obj (FibredSite.quasicoherentTensorUnit B S hS 𝒵.val.val.p
              𝒵.val.property)))) ⟶
      (flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed hpres
          hls hlsD hwp hsep).obj
        (fStar.obj ((quasicoherentToFlatBaseChange B E hE S hS sq.pt.val.val.p
          sq.pt.val.property hincP).obj
            (FibredSite.quasicoherentTensorUnit B S hS sq.pt.val.val.p sq.pt.val.property))) :=
  (Functor.uncurry.obj (FibredSite.quasicoherentTensorBifunctor B S hS
      𝒳.val.val.p 𝒳.val.property)).map
      ((quasicoherentRelativePullbackMap B E hE S hS hincX hincY hincP aStar fStar
      sq.fst hlqY prStarY adjPrY cmpY hclosed hpres hls hlsD hwp hsep) ×ₘ
        (quasicoherentRelativePullbackMap B E hE S hS hincX hincZ hincP bStar fStar
      sq.snd hlqZ prStarZ adjPrZ cmpZ hclosed hpres hls hlsD hwp hsep)) ≫
    coheratorCupProduct (flatBaseChangeQuasicoheratorAdjunction B E hE S hS 𝒳.val.val.p
        𝒳.val.property hincX
      hclosed hpres hls hlsD hwp hsep)
      (Functor.uncurry.obj (FibredSite.quasicoherentTensorBifunctor B S hS
      𝒳.val.val.p 𝒳.val.property)) TLQ tcmp cup

/-- **`μ` is the comparison of Remark 0GQR at a single map out of a tensor product.**  Tensoring
the two relative pullback maps and then applying the comparison of the coherator is the same as
applying the comparison to the relative cup product precomposed with those two maps on
`LQCoh^fbc(𝒪_𝒳)`. -/
@[stacks 0GRN "the identification of μ with Q of the relative cup product precomposed with the \
two relative pullback maps on LQCoh^fbc, i.e. that applying the coherator commutes with \
tensoring the two maps of Stacks 06UM in"]
theorem quasicoherentTensorPushforwardMap_eq_coheratorCupProduct :
    (quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY hincZ hincP hclosed hpres hls
        hlsD hwp hsep
        aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ adjPrZ cmpZ
        TLQ tcmp cup) =
      coheratorCupProduct (flatBaseChangeQuasicoheratorAdjunction B E hE S hS 𝒳.val.val.p
          𝒳.val.property hincX
      hclosed hpres hls hlsD hwp hsep)
        (Functor.uncurry.obj (FibredSite.quasicoherentTensorBifunctor B S hS
      𝒳.val.val.p 𝒳.val.property)) TLQ tcmp
        (TLQ.map ((locallyQuasicoherentStructurePullbackMap B E hE S hS hincY hincP aStar fStar
      sq.fst hlqY prStarY adjPrY cmpY) ×ₘ
            (locallyQuasicoherentStructurePullbackMap B E hE S hS hincZ hincP bStar fStar
      sq.snd hlqZ prStarZ adjPrZ cmpZ)) ≫ cup) := by
  have h := coheratorCupProduct_natural (flatBaseChangeQuasicoheratorAdjunction B E hE S hS
      𝒳.val.val.p 𝒳.val.property hincX
      hclosed hpres hls hlsD hwp hsep)
    (Functor.uncurry.obj (FibredSite.quasicoherentTensorBifunctor B S hS
      𝒳.val.val.p 𝒳.val.property)) TLQ tcmp
    (locallyQuasicoherentStructurePullbackMap B E hE S hS hincY hincP aStar fStar
      sq.fst hlqY prStarY adjPrY cmpY)
    (locallyQuasicoherentStructurePullbackMap B E hE S hS hincZ hincP bStar fStar
      sq.snd hlqZ prStarZ adjPrZ cmpZ)
    (TLQ.map ((locallyQuasicoherentStructurePullbackMap B E hE S hS hincY hincP aStar fStar
      sq.fst hlqY prStarY adjPrY cmpY) ×ₘ
      (locallyQuasicoherentStructurePullbackMap B E hE S hS hincZ hincP bStar fStar
      sq.snd hlqZ prStarZ adjPrZ cmpZ)) ≫ cup) cup (𝟙 _) (Category.comp_id _).symm
  rwa [CategoryTheory.Functor.map_id, Category.comp_id] at h

/-- **The diagram of Remark 0GQR commutes at `μ`.**  The inclusion of **Lemma 0778** applied to
`μ`, followed by the counit of the coherator adjunction, is the comparison `tcmp` of
**Lemma 0GQM** followed by the counit in each tensor factor and then by the relative cup product
precomposed with the two relative pullback maps. -/
@[stacks 0GRN "commutativity of the diagram of Remark 0GQR at μ, over the same carried data"]
theorem map_quasicoherentTensorPushforwardMap_comp_counit :
    (quasicoherentToFlatBaseChange B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX).map
          (quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY hincZ hincP hclosed
              hpres hls hlsD hwp hsep
        aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ adjPrZ cmpZ
        TLQ tcmp cup) ≫
        (flatBaseChangeQuasicoheratorAdjunction B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX
      hclosed hpres hls hlsD hwp hsep).counit.app
          (fStar.obj ((quasicoherentToFlatBaseChange B E hE S hS sq.pt.val.val.p sq.pt.val.property
              hincP).obj
        (FibredSite.quasicoherentTensorUnit B S hS sq.pt.val.val.p sq.pt.val.property))) =
      tcmp.app ((flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed
          hpres hls hlsD hwp hsep).obj (aStar.obj
            ((quasicoherentToFlatBaseChange B E hE S hS 𝒴.val.val.p 𝒴.val.property hincY).obj
                (FibredSite.quasicoherentTensorUnit B S hS 𝒴.val.val.p 𝒴.val.property))),
          (flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed hpres
              hls hlsD hwp hsep).obj (bStar.obj
            ((quasicoherentToFlatBaseChange B E hE S hS 𝒵.val.val.p 𝒵.val.property hincZ).obj
                (FibredSite.quasicoherentTensorUnit B S hS 𝒵.val.val.p 𝒵.val.property)))) ≫
        TLQ.map ((flatBaseChangeQuasicoheratorAdjunction B E hE S hS 𝒳.val.val.p 𝒳.val.property
            hincX
      hclosed hpres hls hlsD hwp hsep).counit.app
              (aStar.obj ((quasicoherentToFlatBaseChange B E hE S hS 𝒴.val.val.p 𝒴.val.property
                  hincY).obj
                (FibredSite.quasicoherentTensorUnit B S hS 𝒴.val.val.p 𝒴.val.property))) ×ₘ
            (flatBaseChangeQuasicoheratorAdjunction B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX
      hclosed hpres hls hlsD hwp hsep).counit.app
              (bStar.obj ((quasicoherentToFlatBaseChange B E hE S hS 𝒵.val.val.p 𝒵.val.property
                  hincZ).obj
                (FibredSite.quasicoherentTensorUnit B S hS 𝒵.val.val.p 𝒵.val.property)))) ≫
          (TLQ.map ((locallyQuasicoherentStructurePullbackMap B E hE S hS hincY hincP aStar fStar
      sq.fst hlqY prStarY adjPrY cmpY) ×ₘ
              (locallyQuasicoherentStructurePullbackMap B E hE S hS hincZ hincP bStar fStar
      sq.snd hlqZ prStarZ adjPrZ cmpZ)) ≫ cup) := by
  rw [quasicoherentTensorPushforwardMap_eq_coheratorCupProduct]
  exact map_coheratorCupProduct_comp_counit _ _ _ _ _

/-- **The canonical map `μ` is an isomorphism once it is one after a functor reflecting
isomorphisms.**  Let `a : 𝒴 ⟶ 𝒳` and `b : 𝒵 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`,
each representable by schemes, quasi-compact, quasi-separated and flat, let `sq` exhibit
`𝒫 = 𝒴 ×_𝒳 𝒵` as their 2-fibre product and let `f = sq.fst ≫ a` be the projection.  Then the
canonical map

`μ : a_{QCoh, *}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh, *}𝒪_𝒵 ⟶ f_{QCoh, *}𝒪_𝒫`

is an isomorphism, provided it becomes invertible under a functor `res` reflecting isomorphisms
(the hypothesis `hchart`). -/
theorem isIso_quasicoherentTensorPushforwardMap {𝒟 : Type u₂} [Category.{v₂} 𝒟]
    (res : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒳.val.property ⥤ 𝒟)
    (hres : res.ReflectsIsomorphisms)
    (hchart : IsIso (res.map (quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY
        hincZ hincP hclosed hpres hls hlsD hwp hsep
        aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ adjPrZ cmpZ
        TLQ tcmp cup)))
    (_hrepA : Stacks.RepresentableMorphism.IsRepresentableMorphism
      𝒴.val.val.p 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor a.hom))
    (_hqcA : IsQuasiCompactMorphism B S hS a)
    (_hqsA : IsQuasiSeparated B S hS a.hom)
    (_hflatA : AlgebraicStacks.IsFlat B S hS a)
    (_hrepB : Stacks.RepresentableMorphism.IsRepresentableMorphism
      𝒵.val.val.p 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor b.hom))
    (_hqcB : IsQuasiCompactMorphism B S hS b)
    (_hqsB : IsQuasiSeparated B S hS b.hom)
    (_hflatB : AlgebraicStacks.IsFlat B S hS b)
    (_hsq : Bicategory.IsTwoFibreProduct sq) :
    IsIso (quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY hincZ hincP hclosed
        hpres hls hlsD hwp hsep
        aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ adjPrZ cmpZ
        TLQ tcmp cup) := by
  have := hres
  have := hchart
  exact isIso_of_reflects_iso _ res

/-- The canonical map
`AlgebraicGeometry.Stack.quasicoherentTensorPushforwardMap` read as an isomorphism

`a_{QCoh, *}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh, *}𝒪_𝒵 ≅ f_{QCoh, *}𝒪_𝒫`

in `QCoh(𝒪_𝒳)`, under the hypotheses of
`AlgebraicGeometry.Stack.isIso_quasicoherentTensorPushforwardMap`. -/
def quasicoherentTensorPushforwardIso {𝒟 : Type u₂} [Category.{v₂} 𝒟]
    (res : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p 𝒳.val.property ⥤ 𝒟)
    (hres : res.ReflectsIsomorphisms)
    (hchart : IsIso (res.map (quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY
        hincZ hincP hclosed hpres hls hlsD hwp hsep
        aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ adjPrZ cmpZ
        TLQ tcmp cup)))
    (_hrepA : Stacks.RepresentableMorphism.IsRepresentableMorphism
      𝒴.val.val.p 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor a.hom))
    (_hqcA : IsQuasiCompactMorphism B S hS a)
    (_hqsA : IsQuasiSeparated B S hS a.hom)
    (_hflatA : AlgebraicStacks.IsFlat B S hS a)
    (_hrepB : Stacks.RepresentableMorphism.IsRepresentableMorphism
      𝒵.val.val.p 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor b.hom))
    (_hqcB : IsQuasiCompactMorphism B S hS b)
    (_hqsB : IsQuasiSeparated B S hS b.hom)
    (_hflatB : AlgebraicStacks.IsFlat B S hS b)
    (_hsq : Bicategory.IsTwoFibreProduct sq) :
    FibredSite.quasicoherentTensorObj B S hS 𝒳.val.val.p 𝒳.val.property
        ((flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed
            hpres hls hlsD hwp hsep).obj
          (aStar.obj ((quasicoherentToFlatBaseChange B E hE S hS 𝒴.val.val.p 𝒴.val.property
            hincY).obj (FibredSite.quasicoherentTensorUnit B S hS 𝒴.val.val.p 𝒴.val.property))))
        ((flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed
            hpres hls hlsD hwp hsep).obj
          (bStar.obj ((quasicoherentToFlatBaseChange B E hE S hS 𝒵.val.val.p 𝒵.val.property
            hincZ).obj (FibredSite.quasicoherentTensorUnit B S hS 𝒵.val.val.p
              𝒵.val.property)))) ≅
      (flatBaseChangeQuasicoherator B E hE S hS 𝒳.val.val.p 𝒳.val.property hincX hclosed hpres
          hls hlsD hwp hsep).obj
        (fStar.obj ((quasicoherentToFlatBaseChange B E hE S hS sq.pt.val.val.p
          sq.pt.val.property hincP).obj
            (FibredSite.quasicoherentTensorUnit B S hS sq.pt.val.val.p sq.pt.val.property))) :=
  have := isIso_quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY hincZ hincP
    hclosed hpres hls hlsD hwp hsep aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ
        adjPrZ
    cmpZ TLQ tcmp cup res hres hchart _hrepA _hqcA _hqsA _hflatA _hrepB _hqcB _hqsB _hflatB
    _hsq
  asIso (quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY hincZ hincP hclosed hpres
      hls hlsD hwp hsep
        aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ adjPrZ cmpZ
        TLQ tcmp cup)

/-- **Invertibility of `μ` from the level of sheaves of modules.**  If the map
underlying `μ` in the category of sheaves of modules on the fppf site of `𝒳` is an isomorphism,
then `μ` is one. -/
theorem isIso_quasicoherentTensorPushforwardMap_of_isIso_sheafMap
    (hsheaf : IsIso ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.property .fppf)).ι.map
      (quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY hincZ hincP hclosed hpres
          hls hlsD hwp hsep
        aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ adjPrZ cmpZ
        TLQ tcmp cup)))
    (_hrepA : Stacks.RepresentableMorphism.IsRepresentableMorphism
      𝒴.val.val.p 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor a.hom))
    (_hqcA : IsQuasiCompactMorphism B S hS a)
    (_hqsA : IsQuasiSeparated B S hS a.hom)
    (_hflatA : AlgebraicStacks.IsFlat B S hS a)
    (_hrepB : Stacks.RepresentableMorphism.IsRepresentableMorphism
      𝒵.val.val.p 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor b.hom))
    (_hqcB : IsQuasiCompactMorphism B S hS b)
    (_hqsB : IsQuasiSeparated B S hS b.hom)
    (_hflatB : AlgebraicStacks.IsFlat B S hS b)
    (_hsq : Bicategory.IsTwoFibreProduct sq) :
    IsIso (quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY hincZ hincP hclosed
        hpres hls hlsD hwp hsep
        aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ adjPrZ cmpZ
        TLQ tcmp cup) :=
  isIso_quasicoherentTensorPushforwardMap B E hE S hS a b sq hincX hincY hincZ hincP
    hclosed hpres hls hlsD hwp hsep aStar bStar fStar hlqY prStarY adjPrY cmpY hlqZ prStarZ
        adjPrZ
    cmpZ TLQ tcmp cup (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.property .fppf)).ι
    (ObjectProperty.fullyFaithfulι _).reflectsIsomorphisms hsheaf _hrepA _hqcA _hqsA _hflatA _hrepB
        _hqcB
    _hqsB _hflatB _hsq

end TensorPushforward

section CanonicalFibreProduct

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- The canonical 2-commutative square over a cospan of algebraic stacks, with apex
`𝒴 ×_𝒳 𝒵`, is a 2-fibre product (**Stacks 04T2**), so it satisfies the hypothesis `_hsq` of
`AlgebraicGeometry.Stack.isIso_quasicoherentTensorPushforwardMap`. -/
example (a : 𝒴 ⟶ 𝒳) (b : 𝒵 ⟶ 𝒳) :
    Bicategory.IsTwoFibreProduct (twoFibreProductSquareAlgebraicStacks B S hS a b) :=
  isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a b

end CanonicalFibreProduct

end AlgebraicGeometry.Stack

end
