module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatCoveringSpectralSequence

/-!
# The spectral sequence of a flat presentation for a sheaf of modules

Let `f : 𝒰 ⟶ 𝒳` be a `1`-morphism of algebraic stacks which is representable by algebraic
spaces, surjective, flat and locally of finite presentation, and let `F` be a sheaf of
`𝒪_𝒳`-modules. Then there is a first-quadrant spectral sequence
`E₁^{p,q} = H^q(𝒰ₚ, fₚ^*F) ⇒ H^{p+q}(𝒳, F)`, where `𝒰ₚ = 𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰` (`p + 1` factors) is
the degree `p` term of the relative Čech nerve of `f` and `fₚ : 𝒰ₚ ⟶ 𝒳` its projection. This is
Stacks 0784, with no hypothesis beyond those of the source.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfModuleCechSpectralSequence`: Stacks 0784.

## Implementation notes

The source proves the tag as a special case of Sheaves on Stacks, Tag 06XJ, and so does this
file: the spectral sequence is
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfCechSpectralSequence` applied to the abelian
sheaf underlying `F`. The inverse image `fₚ^*F` of a sheaf of modules along the projection of the
Čech nerve precomposes both the sections and the scalars with that projection, so its underlying
abelian sheaf is the inverse image of the abelian sheaf underlying `F`
(`SheafOfModules.toSheaf_obj_restrictAlongContinuous`), and the first page of Tag 06XJ is the
cohomology of `fₚ^*F` on the nose.

Tag 06XJ needs that `𝒰` has equalizers. This is part (3) of Stacks 06WY, proved for every
algebraic stack as the instance `AlgebraicGeometry.Stack.AlgebraicStacks.hasEqualizers`, so it is
not a hypothesis here. The cohomology groups are taken in the universe of the coefficients, where
sheafification and the `Ext` groups defining cohomology exist
(`Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp` and
`Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp`), so the statement carries no instance
hypotheses either.

The source assumes `F` quasi-coherent, but the spectral sequence exists for every sheaf of
`𝒪_𝒳`-modules, so it is stated for an arbitrary one; this contains the source's statement.
The statement of record writes the first page as `E₁`, and the source's proof invokes Tag 06XJ,
which gives the cohomology of `fₚ^*F` as the `E₁` page, the first differential being the Čech
differential; that is the page stated here. (The online text writes `E₂` for the same groups,
which is not what Tag 06XJ produces.)

## References

* [Stacks Project, Tag 0784](https://stacks.math.columbia.edu/tag/0784)
* [Stacks Project, Tag 06XJ](https://stacks.math.columbia.edu/tag/06XJ)
* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w a

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)

/-- Let `f : 𝒰 ⟶ 𝒳` be a `1`-morphism of algebraic stacks which is representable by algebraic
spaces, surjective, flat and locally of finite presentation, and let `F` be a sheaf of
`𝒪_𝒳`-modules (for instance a quasi-coherent one). Then there is a first-quadrant spectral sequence
`E₁^{p,q} = H^q(𝒰ₚ, fₚ^*F) ⇒ H^{p+q}(𝒳, F)`, where `𝒰ₚ = 𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰` (`p + 1` factors) is the
degree `p` term of the relative Čech nerve of `f` and `fₚ : 𝒰ₚ ⟶ 𝒳` its projection.

The spectral sequence, its first-quadrant vanishing and its convergence to the cohomology of `F` on
`𝒳` are the fields of `Stacks.RelativeCech.SpectralSequenceData` for the abelian sheaf underlying
`F`; the condition on that datum identifies its `E₁` term at `(p, q)` with the degree `q`
cohomology of the inverse image `fₚ^*F` of the module `F` on `𝒰ₚ`. -/
@[stacks 0784 "for an arbitrary sheaf of modules, which contains the quasi-coherent case; the \
equalizers of `𝒰` needed by Tag 06XJ are Tag 06WY (3), proved for algebraic stacks"]
theorem exists_fppfModuleCechSpectralSequence
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (F : SheafOfModules.{max (u + 1) a} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids SiteKind.fppf)) :
    ∃ data : Stacks.RelativeCech.SpectralSequenceData B S hS 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) SiteKind.fppf
        ((SheafOfModules.toSheaf _).obj F),
      ∀ p q : ℕ, letI := data.continuous p
        Nonempty ((data.sequence.page 1).X ((p : ℤ), (q : ℤ)) ≅
          (Sheaf.functorH (BigFppfOver.associatedTopology B S hS
            (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
              (CatFiberedInGroupoids.homFunctor f.hom) p ⋙ 𝒳.val.val.p) SiteKind.fppf) q).obj
            ((SheafOfModules.toSheaf _).obj
              ((SheafOfModules.restrictAlongContinuous
                (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
                  (CatFiberedInGroupoids.homFunctor f.hom) p)
                (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
                  𝒳.val.isFiberedInGroupoids SiteKind.fppf)).obj F))) := by
  obtain ⟨data⟩ := exists_fppfCechSpectralSequence.{u, w, a} B S hS f hrep hsurj hflat hlfp
    ((SheafOfModules.toSheaf _).obj F)
  exact ⟨data, fun p q => ⟨data.pageOneIso p q⟩⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
