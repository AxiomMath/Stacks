module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalLeadingIdentityStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleOfImmersionRestrictionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquarePieceMapCompositionLaw

/-!
# Stacks 04CO: the conormal sheaf restricted to an étale scheme chart

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `U` be a scheme of the site and `φ : U ⟶ X` an étale morphism, and let

```
Z_U --p--> Z
|j         |i
U  --φ-->  X
```

be a cartesian square in which `Z_U = U ×_X Z` is a scheme `R` of the site and `j : R ⟶ U` a
morphism of schemes.  [Stacks Project, Tag 04CO] says that `Z_U` is a locally closed subscheme
of `U` and that

`𝒞_{Z/X}|_{Z_U} = 𝒞_{Z_U/U}`

canonically and functorially in `U`, where on the right `𝒞_{Z_U/U}` is the conormal sheaf of the
immersion of **schemes** `Z_U ⟶ U` of Morphisms, Definition [Stacks Project, Tag 01R2]
(`Stacks.Conormal.conormalSheaf`), read as a module on the small étale site of the algebraic
space `Z_U` (its associated module, `AlgebraicGeometry.SmallEtale.associatedModule`, transported
by `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`).

## Main results

* `AlgebraicGeometry.Space.isImmersion_toScheme_of_isPullback`: `Z_U ⟶ U` is an immersion of
  schemes.
* `AlgebraicGeometry.Space.exists_isPullback_representedSpaceMap`: the fibre product `U ×_X Z` is
  represented by a scheme of the site.
* `AlgebraicGeometry.Space.isIso_conormalModuleSchemeEtaleRestriction`: the canonical map
  `𝒞_{Z/X}|_{Z_U} ⟶ 𝒞_{Z_U/U}` is an isomorphism.
* `AlgebraicGeometry.Space.conormalModuleSchemeEtaleRestriction_comp`: functoriality in `U`.
* `AlgebraicGeometry.Space.conormalModuleSchemeEtaleRestriction`: **Stacks 04CO**, all clauses
  in one statement.

The canonical map is the composite
`conormalMapOfImmersions … ≫ (conormalModuleOfImmersionRepresentedIso …).hom` of the canonical
map of [Stacks Project, Tag 04CP] at the cartesian square and the identification of part (1) of
[Stacks Project, Tag 04G2].

## References

* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CategoryTheory

/-- For a functor `M`, if `c' = a ≫ M(c₁) ≫ c₂` and `c₂ ≫ e' = M(e) ≫ t`, then
`c' ≫ e' = a ≫ M(c₁ ≫ e) ≫ t`. -/
theorem comp_eq_comp_map_comp_of {C : Type*} {D : Type*} [Category C] [Category D] (M : C ⥤ D)
    {P Y₁ Y₂ : C} {Q W W' : D} (a : Q ⟶ M.obj P) (c₁ : P ⟶ Y₁) (e : Y₁ ⟶ Y₂)
    (c₂ : M.obj Y₁ ⟶ W) (e' : W ⟶ W') (t : M.obj Y₂ ⟶ W') (c' : Q ⟶ W)
    (hcomp : c' = a ≫ M.map c₁ ≫ c₂) (hnat : c₂ ≫ e' = M.map e ≫ t) :
    c' ≫ e' = a ≫ M.map (c₁ ≫ e) ≫ t := by
  rw [hcomp, Category.assoc, Category.assoc, hnat, Functor.map_comp, Category.assoc]

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS} {R V : BigFppfOver B S hS}

/-- **`Z_U = U ×_X Z` is a locally closed subscheme of `U`.**  In a cartesian square whose lower
left corner is a scheme `U` and whose upper left corner is a scheme `R`, the morphism of schemes
`R ⟶ U` is an immersion when `i` is. -/
theorem isImmersion_toScheme_of_isPullback {i : Z ⟶ X}
    {φ : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ X}
    {j : R ⟶ V}
    {p : (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ⟶ Z}
    (sq : IsPullback p (representedSpaceMap B S hS j) i φ) (hi : IsImmersion B S hS i.hom) :
    AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) j).1
    (isImmersion_of_isPullback B S hS sq hi)

/-- **The fibre product `U ×_X Z` is a scheme.**  The base change of an immersion along a
morphism from a scheme `U` of the site is represented by a scheme of the site. -/
theorem exists_isPullback_representedSpaceMap (i : Z ⟶ X) (hi : IsImmersion B S hS i.hom)
    (φ : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ X) :
    ∃ (R : BigFppfOver B S hS) (j : R ⟶ V)
      (p : (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ⟶ Z),
      IsPullback p (representedSpaceMap B S hS j) i φ :=
  ⟨hi.rep.pullback φ.hom, hi.rep.snd φ.hom, ObjectProperty.homMk (hi.rep.fst φ.hom),
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T))
      (hi.rep.isPullback φ.hom)⟩

section Square

attribute [local irreducible] modulePullback modulePullbackCompIso modulePullbackIdIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso
  squarePullbackCompIso representedSmallEtaleModuleEquivalence

variable {i : Z ⟶ X}
    {φ : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ X}
    {j : R ⟶ V}
    {p : (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ⟶ Z}

/-- **Stacks 04CO, the identification is an isomorphism.**  For `φ` étale the canonical map
`𝒞_{Z/X}|_{Z_U} = p^*𝒞_{Z/X} ⟶ 𝒞_{Z_U/U}` — the canonical map of [Stacks Project, Tag 04CP] of
the square, followed by the identification of part (1) of [Stacks Project, Tag 04G2] of the
conormal module of the represented immersion `Z_U ⟶ U` with the conormal sheaf of the immersion of
schemes of Morphisms, Definition [Stacks Project, Tag 01R2] — is an isomorphism. -/
theorem isIso_conormalModuleSchemeEtaleRestriction
    (sq : IsPullback p (representedSpaceMap B S hS j) i φ) (hi : IsImmersion B S hS i.hom)
    (hφ : IsEtale B S hS φ.hom) :
    haveI := isImmersion_toScheme_of_isPullback B S hS sq hi
    IsIso (conormalMapOfImmersions B S hS (representedSpaceMap B S hS j) i
        p φ
        (isImmersion_representedSpaceMap B S hS j) hi sq.w.symm ≫
      (conormalModuleOfImmersionRepresentedIso B S hS j).hom) :=
  have := isImmersion_toScheme_of_isPullback B S hS sq hi
  have : IsIso (conormalMapOfImmersions B S hS (representedSpaceMap B S hS j) i
        p φ
        (isImmersion_representedSpaceMap B S hS j) hi sq.w.symm) := by
    rw [← conormalModuleOfImmersionEtaleRestrictionIso_hom B S hS p (representedSpaceMap B S hS j)
      i φ sq hi hφ]
    infer_instance
  @IsIso.comp_isIso _ _ _ _ _ _ _ this (Iso.isIso_hom _)

/-- **Stacks 04CO, functoriality in `U`.**  Let `ψ : U' ⟶ U` be a morphism of schemes of the
site over `X`, let `Z_{U'} = U' ×_X Z` be represented by `j' : R' ⟶ V'`, and let `b : R' ⟶ R` be
the induced morphism, with `j' ≫ ψ = b ≫ j` and the square for `U'` the pasting of the square of
`ψ` with the square for `U`.  Then the identification of Stacks 04CO for `U'` is the composition
comparison of [Stacks Project, Tag 03LU], followed by the restriction along `b` of the
identification for `U`, followed by the base change of associated modules and the associated
module of the canonical map of Morphisms, Lemma [Stacks Project, Tag 01R4] of the square of
immersions of schemes `Z_{U'} ⟶ U'`, `Z_U ⟶ U`. -/
theorem conormalModuleSchemeEtaleRestriction_comp
    (sq : IsPullback p (representedSpaceMap B S hS j) i φ) (hi : IsImmersion B S hS i.hom)
    {R' V' : BigFppfOver B S hS} (ψ : V' ⟶ V) (j' : R' ⟶ V') (b : R' ⟶ R)
    (hb : j' ≫ ψ = b ≫ j)
    (sq' : IsPullback (representedSpaceMap B S hS b ≫ p) (representedSpaceMap B S hS j') i
      (representedSpaceMap B S hS ψ ≫ φ)) :
    haveI := isImmersion_toScheme_of_isPullback B S hS sq hi
    haveI := isImmersion_toScheme_of_isPullback B S hS sq' hi
    conormalMapOfImmersions B S hS (representedSpaceMap B S hS j') i
        (representedSpaceMap B S hS b ≫ p) (representedSpaceMap B S hS ψ ≫ φ)
        (isImmersion_representedSpaceMap B S hS j') hi sq'.w.symm ≫
      (conormalModuleOfImmersionRepresentedIso B S hS j').hom =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS b) p).inv.app
          (immersionConormalModule B S hS i hi) ≫
        (modulePullback B S hS (representedSpaceMap B S hS b)).map
          (conormalMapOfImmersions B S hS (representedSpaceMap B S hS j) i
        p φ
        (isImmersion_representedSpaceMap B S hS j) hi sq.w.symm ≫
            (conormalModuleOfImmersionRepresentedIso B S hS j).hom) ≫
        (representedAssociatedModulePullbackIso B S hS b
            (relativelyRepresentable_yoneda_map B S hS b)
            (Stacks.Conormal.conormalSheaf ((BigFppfOver.toScheme B S hS).map j))).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R').functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj R') R'.left.property).map
            (Stacks.Immersion.immersionConormalSheafMap
              ((BigFppfOver.toScheme B S hS).map j')
              ((BigFppfOver.toScheme B S hS).map j)
              ((BigFppfOver.toScheme B S hS).map b)
              ((BigFppfOver.toScheme B S hS).map ψ)
              (toShHom_square_of_comp_eq B S hS j' j b ψ hb))) :=
  haveI := isImmersion_toScheme_of_isPullback B S hS sq hi
  haveI := isImmersion_toScheme_of_isPullback B S hS sq' hi
  Stacks.CategoryTheory.comp_eq_comp_map_comp_of
    (modulePullback B S hS (representedSpaceMap B S hS b)) _ _ _ _ _ _ _
    (conormalMapOfImmersions_comp B S hS (representedSpaceMap B S hS j')
      (representedSpaceMap B S hS j) i (representedSpaceMap B S hS b)
      (representedSpaceMap B S hS ψ) p φ (isImmersion_representedSpaceMap B S hS j')
      (isImmersion_representedSpaceMap B S hS j) hi
      (representedSpaceMap_square_of_comp_eq B S hS j' j b ψ hb) sq.w.symm sq'.w.symm)
    (conormalModuleOfImmersionRepresentedIso_naturality B S hS j' j b ψ hb)

end Square

/-- **Stacks 04CO.**  Let `i : Z ⟶ X` be an immersion of algebraic spaces over `S`, let `U` be a
scheme of the site and `φ : U ⟶ X` étale.  Then

* the fibre product `Z_U = U ×_X Z` is a scheme `R` of the site, and for every presentation of
  it by a cartesian square with `j : R ⟶ U` and `p : Z_U ⟶ Z`:
* `j` is an immersion of schemes, so `Z_U` is a locally closed subscheme of `U`;
* the canonical map `𝒞_{Z/X}|_{Z_U} = p^*𝒞_{Z/X} ⟶ 𝒞_{Z_U/U}` — the canonical map of
  [Stacks Project, Tag 04CP] of the square followed by part (1) of [Stacks Project, Tag 04G2],
  whose target is the conormal sheaf `Stacks.Conormal.conormalSheaf` of the immersion of schemes
  `j` of Morphisms, Definition [Stacks Project, Tag 01R2] read on the small étale site — is an
  isomorphism;
* this identification is functorial in `U`: for a morphism `ψ : U' ⟶ U` of schemes over `X`
  with induced `b : Z_{U'} ⟶ Z_U`, the identification for `U'` is the restriction along `b` of
  the identification for `U` followed by the canonical map of Morphisms, Lemma
  [Stacks Project, Tag 01R4] of the schemes. -/
@[stacks 04CO]
theorem conormalModuleSchemeEtaleRestriction (i : Z ⟶ X) (hi : IsImmersion B S hS i.hom)
    (φ : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (hφ : IsEtale B S hS φ.hom) :
    (∃ (R : BigFppfOver B S hS) (j : R ⟶ V)
      (p : (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ⟶ Z),
      IsPullback p (representedSpaceMap B S hS j) i φ) ∧
    ∀ {R : BigFppfOver B S hS} (j : R ⟶ V)
      (p : (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ⟶ Z)
      (sq : IsPullback p (representedSpaceMap B S hS j) i φ),
      AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      (haveI := isImmersion_toScheme_of_isPullback B S hS sq hi
      IsIso (conormalMapOfImmersions B S hS (representedSpaceMap B S hS j) i
        p φ
        (isImmersion_representedSpaceMap B S hS j) hi sq.w.symm ≫
        (conormalModuleOfImmersionRepresentedIso B S hS j).hom)) ∧
      ∀ {R' V' : BigFppfOver B S hS} (ψ : V' ⟶ V) (j' : R' ⟶ V') (b : R' ⟶ R)
        (hb : j' ≫ ψ = b ≫ j)
        (sq' : IsPullback (representedSpaceMap B S hS b ≫ p) (representedSpaceMap B S hS j') i
          (representedSpaceMap B S hS ψ ≫ φ)),
        haveI := isImmersion_toScheme_of_isPullback B S hS sq hi
        haveI := isImmersion_toScheme_of_isPullback B S hS sq' hi
        conormalMapOfImmersions B S hS (representedSpaceMap B S hS j') i
            (representedSpaceMap B S hS b ≫ p) (representedSpaceMap B S hS ψ ≫ φ)
            (isImmersion_representedSpaceMap B S hS j') hi sq'.w.symm ≫
          (conormalModuleOfImmersionRepresentedIso B S hS j').hom =
          (modulePullbackCompIso B S hS (representedSpaceMap B S hS b) p).inv.app
              (immersionConormalModule B S hS i hi) ≫
            (modulePullback B S hS (representedSpaceMap B S hS b)).map
              (conormalMapOfImmersions B S hS (representedSpaceMap B S hS j) i
            p φ
            (isImmersion_representedSpaceMap B S hS j) hi sq.w.symm ≫
                (conormalModuleOfImmersionRepresentedIso B S hS j).hom) ≫
            (representedAssociatedModulePullbackIso B S hS b
                (relativelyRepresentable_yoneda_map B S hS b)
                (Stacks.Conormal.conormalSheaf ((BigFppfOver.toScheme B S hS).map j))).hom ≫
            (representedSmallEtaleModuleEquivalence B S hS R').functor.map
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj R') R'.left.property).map
                (Stacks.Immersion.immersionConormalSheafMap
                  ((BigFppfOver.toScheme B S hS).map j')
                  ((BigFppfOver.toScheme B S hS).map j)
                  ((BigFppfOver.toScheme B S hS).map b)
                  ((BigFppfOver.toScheme B S hS).map ψ)
                  (toShHom_square_of_comp_eq B S hS j' j b ψ hb))) :=
  ⟨exists_isPullback_representedSpaceMap B S hS i hi φ, fun _ _ sq =>
    ⟨isImmersion_toScheme_of_isPullback B S hS sq hi,
      isIso_conormalModuleSchemeEtaleRestriction B S hS sq hi hφ,
      fun ψ j' b hb sq' => conormalModuleSchemeEtaleRestriction_comp B S hS sq hi ψ j' b hb sq'⟩⟩

end AlgebraicGeometry.Space

end
