module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.CategoryTheory.Sites.PullbackLocalSections

/-!
# Sections of an inverse image from a small site are locally pulled back

Let `S` be a scheme in a big Zariski or big étale site, let `π_S` be the projection from the
big topos over `S` to the small topos of `S`, and let `F` be a sheaf on the small site. A
section of `π_S⁻¹F` over a scheme `X` over `S` becomes, after restriction along a covering
family of `X` for the big site, the restriction along some `X' ⟶ U` of the image under the
adjunction unit of a section of `F` over an object `U` of the small site.

## Main results

* `AlgebraicGeometry.exists_locally_unit_section_smallZariski`: the statement for the big Zariski
  site.
* `AlgebraicGeometry.exists_locally_unit_section_smallEtale`: the statement for the big étale
  site.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- A section of `π_S⁻¹F` over a scheme over `S` in a big Zariski site is, after restriction
along a covering family for the big site, the restriction of the image under the adjunction unit
of a section of `F` over an open subscheme of `S`. -/
public theorem exists_locally_unit_section_smallZariski
    (B : BigZariskiSite.{u}) (S : B.Schemes)
    (F : Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1)))
    (X : BigZariskiOver B S.obj S.property)
    (s : ((smallZariskiProjection B S).inverseImage.obj F).obj.obj (op X)) :
    ∃ R : Sieve X, R ∈ BigZariskiOver.topology B S.obj S.property X ∧
      ∀ ⦃Y : BigZariskiOver B S.obj S.property⦄ (k : Y ⟶ X), R k →
        ∃ (U : SmallZariski B S.obj S.property)
          (h : Y ⟶ (SmallZariski.inclusion B S.obj S.property).obj U)
          (t : F.obj.obj (op U)),
          ((smallZariskiProjection B S).inverseImage.obj F).obj.map k.op s =
            ((smallZariskiProjection B S).inverseImage.obj F).obj.map h.op
              (Functor.unitSection (SmallZariski.inclusion B S.obj S.property)
                (SmallZariski.topology B S.obj S.property)
                (BigZariskiOver.topology B S.obj S.property)
                (smallZariskiProjection B S).adj F U t) :=
  Functor.exists_locally_unit_section _ _ _ (smallZariskiProjection B S).adj F X s

/-- A section of `π_S⁻¹F` over a scheme over `S` in a big étale site is, after restriction
along a covering family for the big site, the restriction of the image under the adjunction unit
of a section of `F` over an object of the small étale site of `S`. -/
public theorem exists_locally_unit_section_smallEtale
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (X : BigEtaleOver B S hS)
    (s : ((bigEtaleToSmallEtaleMorphism B S hS).inverseImage.obj F).obj.obj (op X)) :
    ∃ R : Sieve X, R ∈ BigEtaleOver.topology B S hS X ∧
      ∀ ⦃Y : BigEtaleOver B S hS⦄ (k : Y ⟶ X), R k →
        ∃ (U : SmallEtale B S hS) (h : Y ⟶ (SmallEtale.inclusion B S hS).obj U)
          (t : F.obj.obj (op U)),
          ((bigEtaleToSmallEtaleMorphism B S hS).inverseImage.obj F).obj.map k.op s =
            ((bigEtaleToSmallEtaleMorphism B S hS).inverseImage.obj F).obj.map h.op
              (Functor.unitSection (SmallEtale.inclusion B S hS)
                (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS)
                (bigEtaleToSmallEtaleMorphism B S hS).adj F U t) :=
  have := (smallEtaleInclusion_isMorphismOfSites B S hS).toIsContinuous
  Functor.exists_locally_unit_section _ _ _ (bigEtaleToSmallEtaleMorphism B S hS).adj F X s

end AlgebraicGeometry

end
