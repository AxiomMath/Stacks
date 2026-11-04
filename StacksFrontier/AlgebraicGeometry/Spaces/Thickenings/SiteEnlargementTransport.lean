module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementExtension

/-!
# Transport of a square-zero extension to an enlarged big fppf site

Let `B` be a big fppf site, `S` a scheme of `B` and `f : X ⟶ Y` a morphism of algebraic spaces
over `S` for `B`, and let `E` be a square-zero extension of the structure sheaf of `X` as an
algebra over `f⁻¹𝒪_Y` (`AlgebraicGeometry.Space.SquareZeroExtension`). For every big fppf site
`B'` containing `B`, the whole datum transports to `B'`: the algebraic spaces, the morphism, the
small étale site of `X`, the extension with its kernel, surjection and algebra structure, and
the structure sheaves, with comparison isomorphisms identifying each piece on `B` with the
restriction of its counterpart on `B'`. This is the site enlargement with which Stacks 05ZT is
proved without a size hypothesis: the construction of the thickening may produce schemes too
large for `B`, and it is carried out on a site large enough to contain them.

## Main definitions

* `AlgebraicGeometry.Space.SiteTransport`: the transported datum and its comparisons.

## Main results

* `AlgebraicGeometry.Space.nonempty_siteTransport`: the transport exists for every containing
  big fppf site.

## Implementation notes

Every field of `AlgebraicGeometry.Space.SiteTransport` is data or an equation between data; no
field asserts a theorem. The transport is constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementExtension` and the files it
imports: the algebraic spaces through the inverse image of Stacks 03FP
(`AlgebraicGeometry.changeBigSite`), the small étale site through the transport of étale charts,
which is a dense subsite inclusion, and the sheaves through the resulting equivalences of
categories of sheaves.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A square-zero extension transported to an enlarged big fppf site.** For a big fppf site
`B'` containing `B`: algebraic spaces `X'`, `Y'` and a morphism `f'` over `S` for `B'` whose
restrictions are `X`, `Y` and `f`; a functor from the small étale site of `X` to that of `X'`
lying over the inclusion of big fppf sites; a square-zero extension of the structure sheaf of
`X'` as an `f'⁻¹𝒪_{Y'}`-algebra; and comparison isomorphisms identifying the extension sheaf,
its kernel, the structure sheaf of `X` and `f⁻¹𝒪_Y` with the restrictions of their counterparts
along that functor, compatibly with the inclusion of the kernel, with the surjection and with
the algebra structure. -/
structure SiteTransport {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (B' : BigFppfSite.{u})
    (hB : IsContained (τ := .fppf) B B') (hS' : B'.Contains S) where
  /-- The transported source. -/
  X' : AlgebraicSpaces B' S hS'
  /-- The transported target. -/
  Y' : AlgebraicSpaces B' S hS'
  /-- The transported morphism. -/
  f' : X' ⟶ Y'
  /-- The source is the restriction of the transported source. -/
  XIso : X.1 ≅ (inclusionOver hB S hS).op ⋙ X'.1
  /-- The target is the restriction of the transported target. -/
  YIso : Y.1 ≅ (inclusionOver hB S hS).op ⋙ Y'.1
  /-- The morphism is the restriction of the transported morphism. -/
  map_compatibility :
    XIso.hom ≫ ((inclusionOver hB S hS).op.whiskerLeft f'.hom) = f.hom ≫ YIso.hom
  /-- The transport of étale charts. -/
  chartTransport : SmallEtale B S hS X.1 ⥤ SmallEtale B' S hS' X'.1
  /-- The transport of étale charts lies over the inclusion of big fppf sites. -/
  chartCompatibility :
    SmallEtale.toOver B S hS X.1 ⋙ inclusionOver hB S hS ≅
      chartTransport ⋙ SmallEtale.toOver B' S hS' X'.1
  /-- The transported square-zero extension. -/
  extension : SquareZeroExtension B' S hS' f'
  /-- The extension sheaf is the restriction of the transported extension sheaf. -/
  extensionIso : E.A.val ≅ chartTransport.op ⋙ extension.A.val
  /-- The kernel is the restriction of the transported kernel. -/
  kernelIso : E.I.val.presheaf ≅ chartTransport.op ⋙ extension.I.val.presheaf
  /-- The two comparisons are compatible with the inclusions of the kernels. -/
  kernel_compatibility (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : E.I.val.obj U) :
    extensionIso.hom.app U (E.ι U x) =
      extension.ι (chartTransport.op.obj U) (kernelIso.hom.app U x)
  /-- The structure sheaf of `X` is the restriction of the structure sheaf of `X'`. -/
  structureIso :
    (smallEtaleRingedTopos B S hS X).O.val ≅
      chartTransport.op ⋙ (smallEtaleRingedTopos B' S hS' X').O.val
  /-- The comparisons are compatible with the surjections onto the structure sheaves. -/
  quotient_compatibility :
    extensionIso.hom ≫ (chartTransport.op.whiskerLeft extension.π.hom) =
      E.π.hom ≫ structureIso.hom
  /-- The inverse image `f⁻¹𝒪_Y` is the restriction of `f'⁻¹𝒪_{Y'}`. -/
  baseAlgebraIso :
    ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O).val ≅
    chartTransport.op ⋙
      ((smallEtaleRingedToposHom B' S hS' f').toToposHom.inverseImageRing.obj
        (smallEtaleRingedTopos B' S hS' Y').O).val
  /-- The comparisons are compatible with the algebra structures. -/
  baseAlgebra_compatibility :
    baseAlgebraIso.hom ≫ (chartTransport.op.whiskerLeft extension.toBase.hom) =
      E.toBase.hom ≫ extensionIso.hom

open SiteEnlargement in
/-- **Every square-zero extension transports to every big fppf site containing the given one.**
The transported spaces are the inverse images of Stacks 03FP, the functor on small étale sites is
the transport of étale charts, and the transported extension is
`AlgebraicGeometry.SiteEnlargement.transportExtension`; the comparisons are the counits of the
equivalences given by restriction of sheaves along the transport of étale charts and the
identification `AlgebraicGeometry.SiteEnlargement.inverseImageRingComparison` of inverse images of
structure sheaves. -/
def siteTransport {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (B' : BigFppfSite.{u})
    (hB : IsContained (τ := .fppf) B B') (hS' : B'.Contains S) :
    SiteTransport B S hS E B' hB hS' where
  X' := (changeBigSite B B' hB S hS).obj X
  Y' := (changeBigSite B B' hB S hS).obj Y
  f' := (changeBigSite B B' hB S hS).map f
  XIso := changeBigSitePresheafIso B B' hB S hS X
  YIso := changeBigSitePresheafIso B B' hB S hS Y
  map_compatibility := NatTrans.ext (funext fun T =>
    (changeBigSitePresheafIso_naturality B B' hB S hS f T.unop).symm)
  chartTransport := SiteEnlargement.chartTransport B B' hB S hS X
  chartCompatibility := chartTransportToOverIso B B' hB S hS X
  extension := transportExtension hB hS' E
  extensionIso := (sheafToPresheaf _ _).mapIso (transportAIso hB hS' E).symm
  kernelIso := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso
    (transportIIso hB hS' E).symm
  kernel_compatibility U x := by
    refine Eq.trans ?_ (transportInclusionSet_app hB hS' E U.unop _).symm
    exact (congrArg (fun t => (transportAIso hB hS' E).inv.hom.app U (E.ι U t))
      (transportIIso_hom_inv_apply hB hS' E U.unop x)).symm
  structureIso := Iso.refl _
  quotient_compatibility :=
    ((congrArg (fun m => ((transportAIso hB hS' E).inv ≫ m).hom) (map_transportπ hB hS' E)).trans
      ((congrArg (fun m => m.hom) (Iso.inv_hom_id_assoc (transportAIso hB hS' E) E.π)).trans
        (Category.comp_id _).symm))
  baseAlgebraIso := (sheafToPresheaf _ _).mapIso (inverseImageRingComparison hB hS' f)
  baseAlgebra_compatibility :=
    (congrArg (fun m => ((inverseImageRingComparison hB hS' f).hom ≫ m).hom)
      (map_transportToBase hB hS' E)).trans
      (congrArg (fun m => m.hom) (Iso.hom_inv_id_assoc (inverseImageRingComparison hB hS' f)
        (E.toBase ≫ (transportAIso hB hS' E).inv)))

/-- **The transport of a square-zero extension to an enlarged big fppf site exists**, for every big
fppf site containing the given one. -/
theorem nonempty_siteTransport {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (B' : BigFppfSite.{u})
    (hB : IsContained (τ := .fppf) B B') (hS' : B'.Contains S) :
    Nonempty (SiteTransport B S hS E B' hB hS') :=
  ⟨siteTransport B S hS E B' hB hS'⟩

end AlgebraicGeometry.Space

end
