module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtalePullback
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.PullbackOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFibreScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Weak association on the fibre of a morphism of represented algebraic spaces

Let `α : W ⟶ V` be a morphism of the big fppf site of a scheme `S`, let `G` be a quasi-coherent
`𝒪`-module on the algebraic space `h_W` and let `p` be a field-valued point of `h_V`. The fibre
of `h_α` over `p` is represented, by
`AlgebraicGeometry.Space.fibreRepresentedIso`, so weak association of Stacks 0CTX on that fibre
is the Zariski weak association of Stacks 056L on the representing scheme of the fibre, and the
module there is the Zariski inverse image of the represented Zariski restriction of `G` along the
representing morphism of the projection. This file carries that dictionary.

## Main definitions

* `AlgebraicGeometry.Space.fibreRepresentedModuleIso`: the comparison of the two readings of the
  restriction of `G` to the fibre.
* `AlgebraicGeometry.Space.toSchemePullbackIso` and
  `AlgebraicGeometry.Space.toSchemeFibreIso`: the representing scheme of the fibre, identified
  with the fibre product of the representing schemes and — over the residue field of a point `v`
  of the target scheme — with the scheme-theoretic fibre at `v`.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_fibre_iff_zariski`: weak association on the
  fibre is the Zariski weak association of the inverse image on the representing scheme of the
  fibre.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_pullback_fst_iff_pullback` and
  `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_pullback_fst_iff_fiber`: that Zariski
  statement, transported to the fibre product of the representing schemes and to the
  scheme-theoretic fibre.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_schemeSpace_of_isAffine`:
  **Stacks 03GA for a morphism into a represented algebraic space with affine representing
  scheme** — the identity chart is then an affine étale chart through which every morphism into
  the space factors, so no further input is needed.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_fibreRepresentedModule`: the restriction of `G`
  to the fibre is quasi-coherent when the scheme representing `W` is affine.

## Implementation notes

No `@[stacks]` attribute is claimed here. The two weak-association statements are transports of
results in the library — Stacks 0CUU along the identification of the fibre, which is an isomorphism and
hence étale, and the comparison of the weak assassin of a represented algebraic space with the
Zariski weak assassin of the representing scheme — and the quasi-coherence statements are
instances of Stacks 03GA through an affine chart of the target.

## References

* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {W V : BigFppfOver B S hS}

/-- The restriction of a module to the fibre of `h_α` over a field-valued point `p` of `h_V`,
read on the representing scheme of the fibre, is the Zariski inverse image along the
representing morphism of the projection. -/
noncomputable def fibreRepresentedModuleIso (α : W ⟶ V)
    (G : Modules.{u, u} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W))
    (hG : G.IsQuasicoherentOnSite) (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    (Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).map (pullback.fst α p.siteHom))).obj
        (representedZariskiRestriction B S hS W (isAlgebraicSpace_yoneda B S hS W) G) ≅
      representedZariskiRestriction B S hS (pullback α p.siteHom)
        (isAlgebraicSpace_yoneda B S hS _)
        ((modulePullback B S hS (fibreRepresentedIso B S hS α p).hom).obj
          ((modulePullback B S hS
            (fibreAtFieldValuedPointProjection B S hS (schemeSpaceMap α) p)).obj G)) :=
  (representedZariskiRestrictionBaseChangeIso B S hS (pullback.fst α p.siteHom) G hG).trans
    (representedZariskiRestrictionIso B S hS _ (isAlgebraicSpace_yoneda B S hS _)
      ((eqToIso (by rw [fibreRepresentedIso_hom_comp_projection B S hS α p])).trans
        ((modulePullbackCompIso B S hS (fibreRepresentedIso B S hS α p).hom
          (fibreAtFieldValuedPointProjection B S hS (schemeSpaceMap α) p)).app G).symm))

/-- The identification of the fibre is étale, being an isomorphism. -/
theorem isEtale_fibreRepresentedIso_hom (α : W ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    IsEtale B S hS (fibreRepresentedIso B S hS α p).hom.hom := by
  have _ : IsIso ((fibreRepresentedIso B S hS α p).hom.hom) := by
    rw [fibreRepresentedIso_hom_hom]
    exact Iso.isIso_hom _
  exact isEtale_of_isIso B S hS _

/-- **Weak association on the fibre of a morphism of represented algebraic spaces is the
Zariski weak association of the inverse image on the representing scheme of the fibre.** -/
theorem isWeaklyAssociatedPoint_fibre_iff_zariski (α : W ⟶ V)
    (G : Modules.{u, u} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W))
    (hG : G.IsQuasicoherentOnSite) (p : FieldValuedPoint B S hS (yoneda.obj V))
    (hqc : ((modulePullback B S hS (fibreRepresentedIso B S hS α p).hom).obj
      ((modulePullback B S hS
        (fibreAtFieldValuedPointProjection B S hS (schemeSpaceMap α) p)).obj
          G)).IsQuasicoherentOnSite)
    (θ : points B S hS (yoneda.obj (pullback α p.siteHom))) :
    IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS (schemeSpaceMap α) p)
        ((modulePullback B S hS
          (fibreAtFieldValuedPointProjection B S hS (schemeSpaceMap α) p)).obj G)
        (pointsMap B S hS (yoneda.obj (pullback α p.siteHom))
          (fibreRepresentedIso B S hS α p).hom.hom θ) ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback
            ((BigFppfOver.toScheme B S hS).map (pullback.fst α p.siteHom))).obj
          (representedZariskiRestriction B S hS W (isAlgebraicSpace_yoneda B S hS W) G))
        (pointsToScheme B S hS (pullback α p.siteHom) θ) :=
  ((isWeaklyAssociatedPoint_modulePullback_iff B S hS
      (fibreRepresentedIso B S hS α p).hom
      (isEtale_fibreRepresentedIso_hom B S hS α p) _ θ).symm.trans
    ((@isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPoint_zariski B S hS
        (pullback α p.siteHom) (isAlgebraicSpace_yoneda B S hS _)
        ((modulePullback B S hS (fibreRepresentedIso B S hS α p).hom).obj
          ((modulePullback B S hS
            (fibreAtFieldValuedPointProjection B S hS (schemeSpaceMap α) p)).obj G))
        hqc θ).trans
      (isWeaklyAssociatedPoint_iff_of_iso
        (fibreRepresentedModuleIso B S hS α G hG p) _).symm))

/-- The identification of the representing scheme of the fibre over the residue field of a
point `v` with the scheme-theoretic fibre at `v`. -/
noncomputable def toSchemeFibreIso (α : W ⟶ V) (v : (BigFppfOver.toScheme B S hS).obj V) :
    (BigFppfOver.toScheme B S hS).obj
        (pullback α (schemePointRepresentative B S hS V v).siteHom) ≅
      ((BigFppfOver.toScheme B S hS).map α).fiber v :=
  (isPullback_toScheme_fibre_schemePointRepresentative B S hS α v).isoPullback

/-- The identification carries the representing morphism of the projection to the fibre
inclusion. -/
theorem toSchemeFibreIso_hom_comp_fiberι (α : W ⟶ V)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    (BigFppfOver.toScheme B S hS).map
        (pullback.fst α (schemePointRepresentative B S hS V v).siteHom) =
      (toSchemeFibreIso B S hS α v).hom ≫ ((BigFppfOver.toScheme B S hS).map α).fiberι v :=
  ((isPullback_toScheme_fibre_schemePointRepresentative B S hS α v).isoPullback_hom_fst).symm

/-- Zariski weak association of a pullback along `f = e.hom ≫ g`, for an isomorphism `e`, is that
of the pullback along `g` at the image point. -/
private theorem isWeaklyAssociatedPoint_pullback_iff_of_hom_eq_comp {X Y Z : Scheme.{u}}
    (e : X ≅ Y) (f : X ⟶ Z) (g : Y ⟶ Z) (h : f = e.hom ≫ g) (N : Z.Modules) (x : X) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback f).obj N) x ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback g).obj N)
        (e.hom.base x) :=
  (isWeaklyAssociatedPoint_iff_of_iso
    ((eqToIso (congrArg (fun m => (Scheme.Modules.pullback m).obj N) h)).trans
      ((Scheme.Modules.pullbackComp e.hom g).app N).symm) x).trans
    (isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion e.hom _ x)

/-- **Zariski weak association of the inverse image along the projection from the fibre over
the residue field of `v` is Zariski weak association on the scheme-theoretic fibre at `v`.** -/
theorem isWeaklyAssociatedPoint_pullback_fst_iff_fiber (α : W ⟶ V)
    (N : ((BigFppfOver.toScheme B S hS).obj W).Modules)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (θs : (BigFppfOver.toScheme B S hS).obj
      (pullback α (schemePointRepresentative B S hS V v).siteHom)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
          (pullback.fst α (schemePointRepresentative B S hS V v).siteHom))).obj N) θs ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback
          (((BigFppfOver.toScheme B S hS).map α).fiberι v)).obj N)
        ((toSchemeFibreIso B S hS α v).hom.base θs) := by
  exact isWeaklyAssociatedPoint_pullback_iff_of_hom_eq_comp (toSchemeFibreIso B S hS α v) _ _
    (toSchemeFibreIso_hom_comp_fiberι B S hS α v) N θs

/-- **Stacks 03GA for a morphism into a represented algebraic space with affine representing
scheme.** The identity chart of such a space is an affine étale chart through which every
morphism into it factors, so the pullback of a quasi-coherent module is quasi-coherent with no
further hypothesis. -/
theorem isQuasicoherentOnSite_modulePullback_schemeSpace_of_isAffine
    {X : AlgebraicSpaces B S hS} (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (f : X ⟶ schemeSpace W)
    (G : Modules.{u, u} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W))
    (hG : G.IsQuasicoherentOnSite) :
    ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_affineChartFactorization B S hS f
    (selfChart B S hS W) hW f (Category.comp_id f).symm G hG

/-- The restriction of a quasi-coherent module to the fibre of `h_α` over a field-valued point
of the target, read on the representing scheme of the fibre, is quasi-coherent when the
representing scheme of the source is affine. -/
theorem isQuasicoherentOnSite_fibreRepresentedModule (α : W ⟶ V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (G : Modules.{u, u} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W))
    (hG : G.IsQuasicoherentOnSite) (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    ((modulePullback B S hS (fibreRepresentedIso B S hS α p).hom).obj
      ((modulePullback B S hS
        (fibreAtFieldValuedPointProjection B S hS (schemeSpaceMap α) p)).obj
          G)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((modulePullbackCompIso B S hS (fibreRepresentedIso B S hS α p).hom
      (fibreAtFieldValuedPointProjection B S hS (schemeSpaceMap α) p)).app G)).symm
    (isQuasicoherentOnSite_modulePullback_schemeSpace_of_isAffine B S hS hW
      ((fibreRepresentedIso B S hS α p).hom ≫
        fibreAtFieldValuedPointProjection B S hS (schemeSpaceMap α) p) G hG)

/-- The identification of the representing scheme of the fibre over a field-valued point `p`
with the fibre product of the representing schemes. -/
noncomputable def toSchemePullbackIso (α : W ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    (BigFppfOver.toScheme B S hS).obj (pullback α p.siteHom) ≅
      pullback ((BigFppfOver.toScheme B S hS).map α)
        ((BigFppfOver.toScheme B S hS).map p.siteHom) :=
  (isPullback_toScheme_fibre B S hS α p).isoPullback

/-- The identification carries the representing morphism of the projection to the first
projection of the fibre product of schemes. -/
theorem toSchemePullbackIso_hom_comp_fst (α : W ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj V)) :
    (BigFppfOver.toScheme B S hS).map (pullback.fst α p.siteHom) =
      (toSchemePullbackIso B S hS α p).hom ≫
        pullback.fst ((BigFppfOver.toScheme B S hS).map α)
          ((BigFppfOver.toScheme B S hS).map p.siteHom) :=
  ((isPullback_toScheme_fibre B S hS α p).isoPullback_hom_fst).symm

/-- **Zariski weak association of the inverse image along the projection from the fibre over a
field-valued point is Zariski weak association on the fibre product of the representing
schemes.** -/
theorem isWeaklyAssociatedPoint_pullback_fst_iff_pullback (α : W ⟶ V)
    (N : ((BigFppfOver.toScheme B S hS).obj W).Modules)
    (p : FieldValuedPoint B S hS (yoneda.obj V))
    (θs : (BigFppfOver.toScheme B S hS).obj (pullback α p.siteHom)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
          (pullback.fst α p.siteHom))).obj N) θs ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback (pullback.fst ((BigFppfOver.toScheme B S hS).map α)
          ((BigFppfOver.toScheme B S hS).map p.siteHom))).obj N)
        ((toSchemePullbackIso B S hS α p).hom.base θs) := by
  exact isWeaklyAssociatedPoint_pullback_iff_of_hom_eq_comp (toSchemePullbackIso B S hS α p) _ _
    (toSchemePullbackIso_hom_comp_fst B S hS α p) N θs

end AlgebraicGeometry.Space

end
