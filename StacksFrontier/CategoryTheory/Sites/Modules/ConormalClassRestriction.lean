module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalClassLocal
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialTensor

/-!
# Restriction of the universal differential of the conormal sequence

The universal differential `1 ⊗ d f`, one of the two distinguished local sections of the
conormal sequence of a presentation `φ : A ⟶ B` of sheaves of commutative rings, is compatible
with the restriction maps.  This is what
lets a statement proved over one object of a covering sieve be compared with the restriction
of a statement over the object covered, which every local argument about the degree `-1`
cohomology of a presentation does.  The companion statement for the conormal class `f mod I²` is
`Stacks.Sites.Conormal.conormalClass_map`.

## Main results

* `Stacks.Sites.Conormal.tensorDifferential_map`: the universal differential of a restriction is
  the restriction of the universal differential.

## Implementation notes

It is the compatibility of the module sheafification unit with restriction
(`Stacks.Sites.Conormal.toAssociatedModule_map`) composed with the corresponding statement on
the sections of the presheaf, `Stacks.Sites.Conormal.tensorPresheaf_map_one_tmul_d`.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of the
  naive cotangent complex from the presentation, whose degree `-1` comparison is local.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sheafification of presheaves of abelian groups on an essentially small site. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On an essentially small site, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom]

/-- The universal differential of a restriction is the restriction of the universal
differential. -/
theorem tensorDifferential_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : A.obj.obj X) :
    tensorDifferential.{v, u, w, z} J R A B a φ Y (A.obj.map f x) =
      (conormalSequence.{v, u, w, z} J R A B a φ).X₂.val.map f
        (tensorDifferential.{v, u, w, z} J R A B a φ X x) := by
  refine Eq.trans (congrArg (toAssociatedModule.{v, u, w, z} J A B φ
    (tensorPresheaf φ.hom a.hom) Y)
    (tensorPresheaf_map_one_tmul_d J B φ.hom a.hom f x).symm) ?_
  exact toAssociatedModule_map.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) f _

end Stacks.Sites.Conormal

end
