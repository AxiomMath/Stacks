module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiPullbackFpqcZariskiRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiPullbackSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcEtaleRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections

/-!
# Sections and the fpqc sheaf condition for a sheaf pulled back from a small site

Let `S` be a scheme, let `τ` be the Zariski or the étale topology and let
`π_S : (Sch/S)_τ ⟶ S_τ` be the projection from the big `τ`-topos over `S` to the small
`τ`-topos of `S`. For a sheaf `F` on the small `τ`-site of `S`, the inverse image `π_S⁻¹F` has
two properties: its sections over a scheme `f : X ⟶ S` over `S` are the global sections on the
small `τ`-site of `X` of the small-site pullback `f⁻¹F`, and the presheaf underlying `π_S⁻¹F`
is a sheaf for the fpqc topology.

## Main results

* `AlgebraicGeometry.smallSiteInverseImage_sections_and_isSheaf_fpqc` — **Tag 09XN**, the whole
  statement: both properties, at both values of `τ`.

## Implementation notes

The two values of `τ` are two unrelated site structures in this library, `BigZariskiSite` and
`BigEtaleSite`, so the source's standing `τ ∈ {Zariski, étale}` is rendered as a conjunction of
the two cases rather than as a quantifier. The sections formula is data — a natural isomorphism
of functors in the sheaf, chosen compatibly with restriction along morphisms of schemes over
`S` — so the conjunction is a `PProd` of two subtypes rather than an `And`.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 09XN.** Let `S` be a scheme, let `τ` be the Zariski or the étale topology and let
`π_S : (Sch/S)_τ ⟶ S_τ` be the projection from the big `τ`-topos over `S` to the small
`τ`-topos of `S`. For a sheaf `F` on the small `τ`-site of `S`:

1. the sections of `π_S⁻¹F` over a scheme `f : X ⟶ S` over `S` are the global sections on the
   small `τ`-site of `X` of the small-site pullback `f⁻¹F`, naturally in `F` and compatibly
   with restriction along any morphism of schemes over `S`;
2. the presheaf underlying `π_S⁻¹F` is a sheaf for the fpqc topology on the big `τ`-site
   over `S`.

The first component of the conjunction is the Zariski case, the second the étale case; the two
are the source's two values of `τ`, which are unrelated site structures here. Within each case
the sections formula is `AlgebraicGeometry.zariskiInverseImageSectionsComparison` resp.
`AlgebraicGeometry.etaleInverseImageSectionsComparison` — the family of comparison isomorphisms
together with its compatibility with restriction — and the fpqc sheaf condition is
`AlgebraicGeometry.smallZariskiProjection_inverseImage_isSheaf_fpqc` resp.
`AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc`. -/
@[stacks 09XN]
public noncomputable def smallSiteInverseImage_sections_and_isSheaf_fpqc :
    (∀ (B : BigZariskiSite.{u}) (S : B.Schemes),
        { e : ∀ X : BigZariskiOver B S.obj S.property,
            (smallZariskiProjection B S).inverseImage ⋙
              (sheafSections (BigZariskiOver.topology B S.obj S.property)
                (Type (u + 1))).obj (Opposite.op X) ≅
            (smallZariskiBaseChange B X.hom).sheafPullback
                (Type (u + 1))
                (SmallZariski.topology B S.obj S.property)
                (SmallZariski.topology B X.left.obj X.left.property) ⋙
              Sheaf.Γ (SmallZariski.topology B X.left.obj X.left.property)
                (Type (u + 1)) //
          (∀ {X Y : BigZariskiOver B S.obj S.property} (g : Y ⟶ X)
              (F : Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1))),
              (e X).hom.app F ≫ zariskiPullbackSectionsRestriction B S g F =
                ((smallZariskiProjection B S).inverseImage.obj F).obj.map g.op ≫
                  (e Y).hom.app F) ∧
            ∀ F : Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1)),
              Presheaf.IsSheaf
                ((Scheme.fpqcPrecoverage.comap
                  (BigZariskiOver.toScheme B S.obj S.property)).toGrothendieck)
                ((smallZariskiProjection B S).inverseImage.obj F).obj }) ×'
    ∀ (B : BigEtaleSite.{u}) (S : B.Scheme),
      { e : ∀ X : BigEtaleOver B S.obj S.property,
          (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage ⋙
            (sheafSections (BigEtaleOver.topology B S.obj S.property)
              (Type (u + 1))).obj (Opposite.op X) ≅
          (smallEtaleBaseChange B X.hom).sheafPullback
              (Type (u + 1))
              (SmallEtale.topology B S.obj S.property)
              (SmallEtale.topology B X.left.obj X.left.property) ⋙
            Sheaf.Γ (SmallEtale.topology B X.left.obj X.left.property)
              (Type (u + 1)) //
        (∀ {X Y : BigEtaleOver B S.obj S.property} (g : Y ⟶ X)
            (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))),
            (e X).hom.app F ≫ etalePullbackSectionsRestriction B S g F =
              ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.map
                  g.op ≫
                (e Y).hom.app F) ∧
          ∀ F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)),
            Presheaf.IsSheaf
              ((Scheme.fpqcPrecoverage.comap
                (BigEtaleOver.toScheme B S.obj S.property)).toGrothendieck)
              ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj } :=
  ⟨fun B S =>
      ⟨(zariskiInverseImageSectionsComparison B S).val,
        (zariskiInverseImageSectionsComparison B S).property,
        smallZariskiProjection_inverseImage_isSheaf_fpqc B S⟩,
    fun B S =>
      ⟨(etaleInverseImageSectionsComparison B S).val,
        (etaleInverseImageSectionsComparison B S).property,
        bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc B S.obj S.property⟩⟩

end AlgebraicGeometry

end
