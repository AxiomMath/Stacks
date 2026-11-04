module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentEtaleLocalisation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentRestriction

/-!
# The naive cotangent complex of a morphism of algebraic spaces is étale local

Let `S` be a scheme and consider a commutative square
```
U --g--> V
|p       |q
X --f--> Y
```
of algebraic spaces over `S` with `p` and `q` étale. Stacks 0D0W gives a canonical
identification

`NL_{X/Y}|_{U_étale} = NL_{U/V}` in `D(𝒪_U)`,

of the restriction to the small étale site of `U` of the naive cotangent complex of `f`
(Stacks 0D0V) with the naive cotangent complex of `g`. This file proves it, as an isomorphism
of complexes of sheaves of `𝒪_U`-modules and hence in `D(𝒪_U)`.

## Main definitions

* `AlgebraicGeometry.Space.etaleModuleRestriction`: the restriction `𝓕 ↦ 𝓕|_{U_étale}` of
  sheaves of `𝒪_X`-modules along an étale `p : U ⟶ X`.
* `AlgebraicGeometry.Space.etaleRestrictionNaiveBaseRingIso`: the identification
  `(f⁻¹𝒪_Y)|_{U_étale} ≅ g⁻¹𝒪_V` of the base rings.
* `AlgebraicGeometry.Space.naiveCotangentEtaleRestrictionIso`: **Stacks 0D0W** as an isomorphism
  of complexes, `NL_{X/Y}|_{U_étale} ≅ NL_{U/V}`.
* `AlgebraicGeometry.Space.naiveCotangentEtaleRestrictionDerivedIso`: **Stacks 0D0W** in
  `D(𝒪_U)`.

## Main results

* `AlgebraicGeometry.Space.etaleRestrictionNaiveBaseRingIso_fSharp`: the identification of the
  base rings and the identification `𝒪_X|_{U_étale} = 𝒪_U` carry the restriction of the
  structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` to the structure map `g⁻¹𝒪_V ⟶ 𝒪_U`.

## Implementation notes

The restriction `𝓕|_{U_étale}` is restriction along the postcomposition functor
`j : U_étale ⥤ X_étale` of Stacks 03LP, with coefficients read over `𝒪_U` through the
identification `𝒪_X|_{U_étale} = 𝒪_U` of Stacks 03LV,
`AlgebraicGeometry.Space.etaleRestrictionStructureSheafIso`. Restriction along `j` is the
inverse image `p_small⁻¹` of the morphism of small étale topoi, by Stacks 03LQ
(`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` and
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso`), so this is the functor
`p_small⁻¹` of sheaves of modules of the source.

The proof is the source's. Formation of the naive cotangent complex commutes with restriction
along the continuous and cocontinuous functor `j`
(`Stacks.SheafOfModules.restrictionNaiveCotangentComplexIso`, Stacks 08TZ for the morphism of
topoi attached to `j`), so `NL_{X/Y}|_{U_étale}` is the naive cotangent complex of the restricted
structure map `(f⁻¹𝒪_Y)|_{U_étale} ⟶ 𝒪_X|_{U_étale}`. That map is identified with
`g⁻¹𝒪_V ⟶ 𝒪_U` by Stacks 03LV at `p`, and at `q` together with the composition law of
Stacks 03G8 for the square, and the canonical chain map of Stacks 08TX attached to the resulting
square of sheaves of rings is an isomorphism. The structure sheaves have sections in the universe
`u` and the sheaves of modules in the universe `u + 1` of the small étale sites; no universe is
identified with another.

`CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat`, an instance for an arbitrary site at a
coefficient universe containing the universe of its objects, is demoted in this file: tried
first at the universe `u` of the structure rings it poses a universe constraint instance search
cannot solve, instead of failing. The instance it competes with is a `Prop`, so nothing depends
on which one is found.

## References

* [Stacks Project, Tag 0D0W](https://stacks.math.columbia.edu/tag/0D0W)
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V), the naive cotangent
  complex of a morphism of algebraic spaces.
* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ), the inverse image of
  the naive cotangent complex.
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

namespace AlgebraicGeometry.Space

universe t u

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {U V X Y : AlgebraicSpaces B S hS}

/-- **The restriction `𝓕 ↦ 𝓕|_{U_étale}`** of sheaves of `𝒪_X`-modules along an étale morphism
`p : U ⟶ X` of algebraic spaces: restriction along the postcomposition functor
`U_étale ⥤ X_étale` of Stacks 03LP, which is the inverse image `p_small⁻¹` by Stacks 03LQ, with
the coefficients read over `𝒪_U` through `𝒪_X|_{U_étale} = 𝒪_U` (Stacks 03LV). On sections,
`𝓕|_{U_étale}(W) = 𝓕(W ⟶ U ⟶ X)`. -/
noncomputable def etaleModuleRestriction (p : U ⟶ X) (hp : IsEtale B S hS p.hom) :
    _root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).O) ⥤
      _root_.SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS U).O) :=
  Stacks.Sites.Conormal.ringSheafModuleRestriction.{u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)
      (smallEtalePostcomp B S hS p hp) (smallEtaleRingedTopos B S hS X).O ⋙
    _root_.SheafOfModules.restrictScalars.{u + 1}
      (underlyingRingHomOfSite.{u, u + 1, u} (etaleRestrictionStructureSheafIso B S hS p hp).inv)

/-- Restriction to `U_étale` is additive: on sections it is the identity of the abelian
groups of sections over the objects of the form `W ⟶ U ⟶ X`. -/
instance etaleModuleRestriction_additive (p : U ⟶ X) (hp : IsEtale B S hS p.hom) :
    (etaleModuleRestriction B S hS p hp).Additive :=
  inferInstanceAs (Stacks.Sites.Conormal.ringSheafModuleRestriction.{u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)
      (smallEtalePostcomp B S hS p hp) (smallEtaleRingedTopos B S hS X).O ⋙
    _root_.SheafOfModules.restrictScalars.{u + 1}
      (underlyingRingHomOfSite.{u, u + 1, u}
        (etaleRestrictionStructureSheafIso B S hS p hp).inv)).Additive

/-- **The identification of the base rings** `(f⁻¹𝒪_Y)|_{U_étale} ≅ g⁻¹𝒪_V`, for a commuting
square `p ≫ f = g ≫ q` of algebraic spaces with `p` and `q` étale: restriction to `U_étale` is
`p⁻¹` (Stacks 03LQ), and `p⁻¹f⁻¹𝒪_Y ≅ g⁻¹𝒪_V` by the composition law of Stacks 03G8 for the
square and the clause `q⁻¹𝒪_Y = 𝒪_V` of Stacks 03LV,
`AlgebraicGeometry.Space.etaleSquareBaseRingIso`. -/
noncomputable def etaleRestrictionNaiveBaseRingIso {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V}
    {q : V ⟶ Y} (h : p ≫ f = g ≫ q) (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom) :
    ((smallEtalePostcomp B S hS p hp).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)).obj
        ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O) ≅
      (smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS V).O :=
  (inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS U.1)
      (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
      (smallEtaleRingedToposHom B S hS p).toToposHom
      (smallToposMorphismTypeU_inverseImageIso B S hS p hp)
      ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O)).symm ≪≫
    etaleSquareBaseRingIso B S hS h hq

/-- **The structure maps correspond.** The identification of the base rings and the
identification `𝒪_X|_{U_étale} = 𝒪_U` of Stacks 03LV carry the restriction to `U_étale` of the
structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` to the structure map `g⁻¹𝒪_V ⟶ 𝒪_U`. -/
theorem etaleRestrictionNaiveBaseRingIso_fSharp {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V}
    {q : V ⟶ Y} (h : p ≫ f = g ≫ q) (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom) :
    ((smallEtalePostcomp B S hS p hp).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)).map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage ≫
        (etaleRestrictionStructureSheafIso B S hS p hp).hom =
      (etaleRestrictionNaiveBaseRingIso B S hS h hp hq).hom ≫
        (smallEtaleRingedToposHom B S hS g).fSharpInverseImage := by
  have h₁ := inverseImageCommRingRestrictionIso_inv_naturality (SmallEtale.topology B S hS U.1)
    (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
    (smallEtaleRingedToposHom B S hS p).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS p hp)
    (smallEtaleRingedToposHom B S hS f).fSharpInverseImage
  have h₂ := etaleSquareBaseRingIso_fSharpInverseImage B S hS h hq
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

/-- **Stacks 0D0W, as an isomorphism of complexes.** For a commutative square `p ≫ f = g ≫ q` of
algebraic spaces over `S` with `p` and `q` étale, the restriction to the small étale site of
`U` of the naive cotangent complex of `f` is the naive cotangent complex of `g`:

`NL_{X/Y}|_{U_étale} ≅ NL_{U/V}`,

as complexes of sheaves of `𝒪_U`-modules. It is the restriction of scalars along
`𝒪_U ≅ 𝒪_X|_{U_étale}` of `Stacks.SheafOfModules.restrictionNaiveCotangentComplexIso`, which
identifies `NL_{X/Y}|_{U_étale}` with the naive cotangent complex of
`(f⁻¹𝒪_Y)|_{U_étale} ⟶ 𝒪_X|_{U_étale}`, followed by the inverse of the canonical chain map of
Stacks 08TX attached to the square of sheaves of rings of
`AlgebraicGeometry.Space.etaleRestrictionNaiveBaseRingIso_fSharp`. -/
@[stacks 0D0W "the canonical identification NL_{X/Y}|_{U_étale} = NL_{U/V}, as an isomorphism of
complexes of sheaves of O_U-modules, of which the identification in D(O_U) is the image. The
restriction is along the postcomposition functor U_étale ⥤ X_étale, i.e. p_small⁻¹ (Tag 03LQ),
with O_X|_{U_étale} = O_U (Tag 03LV); formation of the naive cotangent complex commutes with it
(Tag 08TZ for that functor), and the square of structure maps is identified through Tags 03LV
and 03G8"]
noncomputable def naiveCotangentEtaleRestrictionIso {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V}
    {q : V ⟶ Y} (h : p ≫ f = g ≫ q) (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom) :
    ((etaleModuleRestriction B S hS p hp).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex B S hS f) ≅
      naiveCotangentComplex B S hS g :=
  ((_root_.SheafOfModules.restrictScalars.{u + 1}
      (underlyingRingHomOfSite.{u, u + 1, u}
        (etaleRestrictionStructureSheafIso B S hS p hp).inv)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso
    (Stacks.SheafOfModules.restrictionNaiveCotangentComplexIso.{u, u + 1, u, u}
      (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)
      (smallEtalePostcomp B S hS p hp) (smallEtaleRingedToposHom B S hS p).toToposHom
      (smallToposMorphismTypeU_inverseImageIso B S hS p hp)
      ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O)
      (smallEtaleRingedTopos B S hS X).O (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) ≪≫
    (Stacks.SheafOfModules.naiveCotangentComplexIsoOfSquare.{u, u + 1, u, u}
      (SmallEtale.topology B S hS U.1)
      ((smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS V).O)
      (smallEtaleRingedTopos B S hS U).O (smallEtaleRingedToposHom B S hS g).fSharpInverseImage
      (((smallEtalePostcomp B S hS p hp).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)).obj
        ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O))
      (((smallEtalePostcomp B S hS p hp).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)).obj
        (smallEtaleRingedTopos B S hS X).O)
      (((smallEtalePostcomp B S hS p hp).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)).map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage)
      (etaleRestrictionNaiveBaseRingIso B S hS h hp hq).symm
      (etaleRestrictionStructureSheafIso B S hS p hp).symm
      (by
        rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc,
          ← etaleRestrictionNaiveBaseRingIso_fSharp B S hS h hp hq, Category.assoc,
          Iso.hom_inv_id, Category.comp_id])).symm

/-- **Stacks 0D0W.** For a commutative square `p ≫ f = g ≫ q` of algebraic spaces over `S` with
`p` and `q` étale, there is a canonical identification

`NL_{X/Y}|_{U_étale} = NL_{U/V}` in `D(𝒪_U)`:

the image in the derived category of sheaves of `𝒪_U`-modules of the isomorphism of complexes
`AlgebraicGeometry.Space.naiveCotangentEtaleRestrictionIso`. -/
@[stacks 0D0W "the canonical identification NL_{X/Y}|_{U_étale} = NL_{U/V} in D(O_U) for a
commutative square of algebraic spaces over S with p and q étale"]
noncomputable def naiveCotangentEtaleRestrictionDerivedIso {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V}
    {q : V ⟶ Y} (h : p ≫ f = g ≫ q) (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom)
    [HasDerivedCategory.{t} (_root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (smallEtaleRingedTopos B S hS U).O))] :
    DerivedCategory.Q.obj
        (((etaleModuleRestriction B S hS p hp).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (naiveCotangentComplex B S hS f)) ≅
      DerivedCategory.Q.obj (naiveCotangentComplex B S hS g) :=
  DerivedCategory.Q.mapIso (naiveCotangentEtaleRestrictionIso B S hS h hp hq)

end AlgebraicGeometry.Space

end
