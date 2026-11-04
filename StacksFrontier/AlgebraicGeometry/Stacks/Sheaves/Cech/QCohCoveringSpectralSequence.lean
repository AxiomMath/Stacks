module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatCoveringSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules

/-!
# The covering pushforward spectral sequence for a quasi-coherent module

Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable `1`-morphisms of algebraic stacks with `f`
representable by algebraic spaces, surjective, flat and locally of finite presentation, and let
`𝓕` be a quasi-coherent module on the fppf site of `𝒳`. The relative Čech nerve of `f` gives a
first-quadrant spectral sequence whose first page is the higher direct image along `g ∘ fₚ` of
the inverse image `fₚ^*𝓕` on the degree `p` term of the nerve, and which abuts to the higher
direct images of `𝓕` along `g`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.pushforwardPageOneIsoQuasicoherent`: the first page
  of the spectral sequence of a flat presentation for a quasi-coherent module
  at `(p, q)` is the degree `q` higher direct image along `g ∘ fₚ` of the inverse image of `𝓕`
  on the degree `p` term of the nerve, taken as a module.

The spectral sequence itself, in the quasi-coherent form of the source, is
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasicoherentCoveringSpectralSequence` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/QuasicoherentCoveringSpectralSequence.lean`.

## Implementation notes

The spectral sequence is the one of Tag 072G part (2)(a), which holds for an arbitrary abelian
sheaf on the fppf site of `𝒳`; what the quasi-coherent case adds is that the input is the
source's own `𝓕 ∈ QCoh(𝒪_𝒳)`, through `AlgebraicGeometry.FibredSite.toSiteModules` and the
abelian sheaf underlying the resulting sheaf of modules, and the reading of the first page. The
inverse image of a sheaf of modules along a `1`-morphism changes neither the underlying abelian
presheaf nor the scalars — it precomposes both with the morphism — so the abelian sheaf
underlying `fₚ^*𝓕` *is* the restriction of the abelian sheaf underlying `𝓕`, which is
`SheafOfModules.toSheaf_obj_restrictAlongContinuous`, and the first page of the spectral
sequence of the underlying abelian sheaf already computes the higher direct image of `fₚ^*𝓕`.
The restriction is taken along `Stacks.RelativeCech.Tuple.projection`, whose continuity is part
of the spectral sequence datum and so is not an extra hypothesis.

The spectral sequence itself, its first page, its first-quadrant vanishing and its abutment are
those recorded by `Stacks.RelativeCech.PushforwardSpectralSequenceData`; no parallel datum is
introduced.

Two features of the source statement are *not* reproduced, and the tag attributes say so.

First, the direct images here are the direct images of abelian sheaves along the morphisms of
sites, not the quasi-coherent direct images `R^q (g ∘ fₚ)_{QCoh,*}` and `R^q g_{QCoh,*}` of the
source, and the spectral sequence is one of abelian sheaves on the fppf site of `𝒴` rather than
one in `QCoh(𝒪_𝒴)`. The quasi-coherent pushforward of Tag 077A *is* available, as
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImageQuasicoherent`; what blocks the
quasi-coherent form of the present tag is not that functor but three other things. A spectral
sequence valued in `QCoh(𝒪_𝒴)` needs `Abelian` on that category at the module universe `u + 1`
of this seating, and no such instance or hypothesis is available; the datum
`Stacks.RelativeCech.PushforwardSpectralSequenceData` is hard-wired to sheaves of abelian
groups with no category parameter to exchange; and carrying pages through the coherator needs
the exactness of Tag 0779. The module-level direct image used here instead is
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImage`, valued in all of `Mod(𝒪_𝒴)`.
Already the module-level form of Tag 072G part (2)(b) is absent — the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/Cech/SmoothCoveringSpectralSequence.lean` record
why, and `AlgebraicGeometry.Stack.AlgebraicStacks.HasFppfCechPresentation` carries it whole as
a hypothesis of Tag 0770 for exactly that reason. The quasi-coherent form of the present tag is a
strengthening of that absent statement, so it is the abelian form that is recorded here, in the
same way that Tag 075H is recorded for abelian sheaves only.

Second, the source assumes `f` quasi-compact and quasi-separated and `g` quasi-compact and
quasi-separated. Neither is used: in the source they are spent on making the quasi-coherent
direct images defined, and the abelian direct images along the morphisms of sites are defined
for any `1`-morphism. Omitting them leaves a statement that implies the source's, so they are
omitted rather than carried as decoration.

That `𝒰` has equalizers, part (3) of Tag 06WY, is carried, exactly as in Tag 072G and Tag 06XJ.

The source states the spectral sequence with first page `E₂^{p,q}`, whereas its own proof
invokes the relative Čech pushforward spectral sequence, which gives that object as `E₁^{p,q}`;
the first differential of the Čech double complex is the Čech differential, so `E₁` is the
correct page and is what is stated here, exactly as for Tag 0784.

## References

* [Stacks Project, Tag 0785](https://stacks.math.columbia.edu/tag/0785)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 072D](https://stacks.math.columbia.edu/tag/072D)
* [Stacks Project, Tag 0784](https://stacks.math.columbia.edu/tag/0784)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Fppf

variable {𝒰 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴)
  (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
  (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
  (hlfp : IsLocallyOfFinitePresentation B S hS f)
  [HasEqualizers 𝒰.val.val.obj]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ P : 𝒳.val.val.objᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a},
    (CatFiberedInGroupoids.homFunctor g.hom).op.HasPointwiseRightKanExtension P]
  [∀ (n : ℕ) (P : (Stacks.RelativeCech.Tuple 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a}),
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) n ⋙
      CatFiberedInGroupoids.homFunctor g.hom).op.HasPointwiseRightKanExtension P]

/-- The sheaf of `𝒪_𝒳`-modules on the fppf site of `𝒳` underlying a quasi-coherent module, the
image of `𝓕 ∈ QCoh(𝒪_𝒳)` under the inclusion of Tag 06WG. -/
abbrev fppfQuasicoherentSiteModule
    (𝓕 : FibredSite.quasicoherentModules.{u, u + 1, u, max (u + 1) a} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    SheafOfModules.{max (u + 1) a} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf) :=
  (FibredSite.toSiteModules.{u, u + 1, u, max (u + 1) a} B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids SiteKind.fppf).obj 𝓕

/-- **Stacks 0785**, the first page. The term of the covering pushforward spectral sequence of a
flat presentation in position `(p, q)` is the degree `q` higher direct image along `g ∘ fₚ` of
the inverse image `fₚ^*𝓕` of the quasi-coherent module `𝓕` on the degree `p` term `𝒰ₚ` of the
relative Čech nerve of `f`, the inverse image being taken as a sheaf of modules. -/
@[stacks 0785 "the reading of the E₁ page as the higher direct image of the inverse image of \
the quasi-coherent module, the inverse image being taken as a sheaf of modules and the higher \
direct image being the abelian one along the morphism of sites"]
def pushforwardPageOneIsoQuasicoherent
    (𝓕 : FibredSite.quasicoherentModules.{u, u + 1, u, max (u + 1) a} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)
    (data : Stacks.RelativeCech.PushforwardSpectralSequenceData B S hS 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) SiteKind.fppf
      (fppfAbelianSheaf B S hS (fppfQuasicoherentSiteModule B S hS 𝓕))) (i j : ℕ) :
    letI := data.continuous i
    letI := data.cocontinuous i
    letI := data.gCocontinuous
    letI := data.enoughInjectives i
    letI : (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) i ⋙
        CatFiberedInGroupoids.homFunctor g.hom).IsCocontinuous
        (BigFppfOver.associatedTopology B S hS
          (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) i ⋙ 𝒳.val.val.p) SiteKind.fppf)
        (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p SiteKind.fppf) :=
      isCocontinuous_comp (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom) i)
        (CatFiberedInGroupoids.homFunctor g.hom)
        (BigFppfOver.associatedTopology B S hS
          (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) i ⋙ 𝒳.val.val.p) SiteKind.fppf)
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
    letI := Stacks.RelativeCech.additive_pushforwardCocontinuous AddCommGrpCat.{max (u + 1) a}
      (BigFppfOver.associatedTopology B S hS
        (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom) i ⋙ 𝒳.val.val.p) SiteKind.fppf)
      (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p SiteKind.fppf)
      (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) i ⋙
        CatFiberedInGroupoids.homFunctor g.hom)
    (data.sequence.page 1).X ((i : ℤ), (j : ℤ)) ≅
      (((Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) i ⋙
          CatFiberedInGroupoids.homFunctor g.hom).sheafPushforwardCocontinuous
            AddCommGrpCat.{max (u + 1) a}
            (BigFppfOver.associatedTopology B S hS
              (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
                (CatFiberedInGroupoids.homFunctor f.hom) i ⋙ 𝒳.val.val.p) SiteKind.fppf)
            (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p SiteKind.fppf)).rightDerived
          j).obj
        ((SheafOfModules.toSheaf _).obj
          ((SheafOfModules.restrictAlongContinuous
            (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
              (CatFiberedInGroupoids.homFunctor f.hom) i)
            (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
              𝒳.val.isFiberedInGroupoids SiteKind.fppf)).obj
            (fppfQuasicoherentSiteModule B S hS 𝓕))) :=
  data.pageOneIso i j

end Fppf

end AlgebraicGeometry.Stack.AlgebraicStacks

end
