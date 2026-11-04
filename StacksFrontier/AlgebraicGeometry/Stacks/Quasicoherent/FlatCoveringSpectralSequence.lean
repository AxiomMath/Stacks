module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.SmoothCoveringSpectralSequence

/-!
# Čech-to-cohomology for a flat presentation and a sheaf of modules

Let `f : 𝒰 ⟶ 𝒳` be a `1`-morphism of algebraic stacks which is representable by algebraic
spaces, surjective, flat and locally of finite presentation, and let `F` be a sheaf of
`𝒪_𝒳`-modules. Then there is a first-quadrant spectral sequence whose first page is the fppf
cohomology of the inverse images `f_p^*F` on the terms `𝒰_p` of the relative Čech nerve of `f`
and which abuts to the fppf cohomology of `F` on `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfSpectralSequenceData_module`: the
  spectral sequence of a flat presentation for a sheaf of modules.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pageOneIsoModule`: its first page at `(p, q)`
  is the degree `q` cohomology of the inverse image of `F` on the degree `p` term of the nerve.
* `SheafOfModules.toSheaf_obj_restrictAlongContinuous`: the abelian sheaf underlying the
  restriction of a sheaf of modules along a continuous functor is the restriction of the abelian
  sheaf underlying it.

## Implementation notes

The spectral sequence is the one of Tag 06XJ part (2), which holds for an arbitrary abelian
sheaf on the fppf site of `𝒳`; what the module case adds is the reading of its first page. The
inverse image of a sheaf of modules along a `1`-morphism changes neither the underlying abelian
presheaf nor the scalars — it precomposes both with the morphism — so the
abelian sheaf underlying `f_p^*F` *is* the restriction of the abelian sheaf underlying `F`, and
the first page of the spectral sequence of the underlying abelian sheaf already computes the
cohomology of `f_p^*F`. This is `SheafOfModules.restrictAlongContinuous`, taken along
`Stacks.RelativeCech.Tuple.projection`, whose continuity is part of the spectral sequence datum
and so is not an extra hypothesis.

The spectral sequence needs no hypothesis that `𝒰` has equalizers (part (3) of Tag 06WY).

The source states the spectral sequence with first page `E_2^{p,q} = H^q(𝒰_p, f_p^*F)`, whereas
its own proof invokes Tag 06XJ, which gives that group as `E_1^{p,q}`; the first differential of
the Čech double complex is the Čech differential, so `E_1` is the correct page and is what is
stated here.

## References

* [Stacks Project, Tag 0784](https://stacks.math.columbia.edu/tag/0784)
* [Stacks Project, Tag 06XJ](https://stacks.math.columbia.edu/tag/06XJ)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SheafOfModules

universe u v w m

variable {C D : Type v} [Category.{w} C] [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u})

/-- The abelian sheaf underlying the restriction of a sheaf of modules along a continuous
functor is the restriction of the abelian sheaf underlying it: both are the precomposition of
its presheaf of sections with the functor. -/
theorem toSheaf_obj_restrictAlongContinuous (M : SheafOfModules.{m} R) :
    (toSheaf ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R)).obj
        ((restrictAlongContinuous (J := J) F R).obj M) =
      (F.sheafPushforwardContinuous AddCommGrpCat.{m} J K).obj ((toSheaf R).obj M) :=
  rfl

end SheafOfModules

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w a b

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
  (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
  (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
  (hlfp : IsLocallyOfFinitePresentation B S hS f)
  [HasEqualizers 𝒰.val.val.obj]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a})]
  [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ n : ℕ, HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a})]

/-- The abelian sheaf on the fppf site of `𝒳` underlying a sheaf of `𝒪_𝒳`-modules. -/
abbrev fppfAbelianSheaf
    (F : SheafOfModules.{max (u + 1) a} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf)) :
    Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
      AddCommGrpCat.{max (u + 1) a} :=
  (SheafOfModules.toSheaf _).obj F

omit [HasEqualizers 𝒰.val.val.obj] in
include hrep hsurj hflat hlfp in
/-- **Stacks 0784.** Let `f : 𝒰 ⟶ 𝒳` be a `1`-morphism of algebraic stacks which is
representable by algebraic spaces, surjective, flat and locally of finite presentation, and let
`F` be a sheaf of `𝒪_𝒳`-modules. Then there is a first-quadrant spectral sequence
`E₁^{p,q} = H^q_fppf(𝒰ₚ, fₚ^*F) ⇒ H^{p+q}_fppf(𝒳, F)`, where `𝒰ₚ` is the degree `p` term of the
relative Čech nerve of `f` and `fₚ` its projection to `𝒳`; the identification of the first page
is `AlgebraicGeometry.Stack.AlgebraicStacks.pageOneIsoModule`.

The source assumes `F` quasi-coherent; the spectral sequence needs no such hypothesis, so it is
stated here for an arbitrary sheaf of `𝒪_𝒳`-modules, which contains the source's statement.
No hypothesis that `𝒰` has equalizers is needed. -/
@[stacks 0784 "the E₁ form, which is what Sheaves on Stacks 06XJ gives and what makes the first \
differential the Čech differential; the tag's own text writes E₂. Stated for an arbitrary sheaf \
of modules rather than only a quasi-coherent one. Carries the hypothesis that `𝒰` has \
equalizers, as Tag 06XJ does"]
theorem exists_fppfSpectralSequenceData_module
    (F : SheafOfModules.{max (u + 1) a} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf)) :
    Nonempty (Stacks.RelativeCech.SpectralSequenceData B S hS 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) SiteKind.fppf
      (fppfAbelianSheaf B S hS F)) :=
  exists_fppfSpectralSequenceData.{u, w, a, b} B S hS f hrep hsurj hflat hlfp
    (fppfAbelianSheaf B S hS F)

/-- **Stacks 0784**, the first page. The term of the spectral sequence of a flat presentation in
position `(p, q)` is the degree `q` fppf cohomology, on the degree `p` term `𝒰ₚ` of the relative
Čech nerve, of the inverse image `fₚ^*F` of the module `F`. -/
@[stacks 0784 "the reading of the E₁ page as the cohomology of the inverse image of the module"]
def pageOneIsoModule
    (F : SheafOfModules.{max (u + 1) a} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf))
    (data : Stacks.RelativeCech.SpectralSequenceData B S hS 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) SiteKind.fppf
      (fppfAbelianSheaf B S hS F)) (i j : ℕ) :
    letI := data.continuous i
    (data.sequence.page 1).X ((i : ℤ), (j : ℤ)) ≅
      (Sheaf.functorH (BigFppfOver.associatedTopology B S hS
        (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom) i ⋙ 𝒳.val.val.p) SiteKind.fppf) j).obj
        ((SheafOfModules.toSheaf _).obj
          ((SheafOfModules.restrictAlongContinuous
            (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
              (CatFiberedInGroupoids.homFunctor f.hom) i)
            (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
              𝒳.val.isFiberedInGroupoids SiteKind.fppf)).obj F)) :=
  data.pageOneIso i j

end AlgebraicGeometry.Stack.AlgebraicStacks

end
