module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Transport
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 03FD as a named isomorphism

`ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying` states Stacks 03FD as an existence:
*there is* a comparison between the cohomology of a sheaf of modules and the cohomology of its
underlying abelian sheaf. A choice carries no information beyond the normalization it was chosen
with, and for the comparisons over the objects of the site the existence form quantifies
`∀ U, ∃ eU`, so the comparisons for two different objects are chosen independently and no
relation between them can be recovered. This file replaces the existence statement by a named
isomorphism.

## Main definitions and results

* `ModuleSheafCohomology.comparisonIso`: for an exact functor `F` and a left exact functor `G`
  corepresented by `X`, with `F ⋙ G` corepresented by `Y` and with `Ext`-acyclicity of `F` on
  injectives against `X`, the comparison `(F ⋙ G).rightDerived n ≅ F ⋙ G.rightDerived n`, in
  *every* degree and as a `def`. It is the degreewise component of an isomorphism of
  `δ`-functors, `comparisonDeltaIso`.
* `ModuleSheafCohomology.comparisonIso_zero`: the degree-zero normalization. It holds by
  construction: the `δ`-functor isomorphism is the one extending the canonical degree-zero
  isomorphism `degreeZeroIso`.
* `ModuleSheafCohomology.comparisonIso_hom_eq`: the characterization. The comparison is the
  *unique* morphism of `δ`-functors whose degree-zero component is the canonical one; in
  particular it is determined in every degree by its value in degree zero.
* `ModuleSheafCohomology.rightDerivedCoyonedaSuccIso_app` together with
  `ModuleSheafCohomology.extCyclesMap_apply`: the characterization on injective resolutions. In
  positive degree the comparison is built from the identification of `Ext X Z (n + 1)` with the
  degree `n + 1` cohomology of `Hom(I, X)` for the chosen injective resolution `I` of `Z`, under
  which the class of a cocycle `f` is `I.extMk f`.
* `ModuleSheafCohomology.globalSectionsComparisonIso`,
  `ModuleSheafCohomology.sectionsComparisonIso`: the two instances of Stacks 03FD, for global
  sections and for sections over an object `U` of the site, with their degree-zero
  normalizations. `exists_moduleSheafCohomologyIsoUnderlying` recovers the existence statement
  from them, so that the two forms cannot drift apart.
* `ModuleSheafCohomology.comparisonIso_naturality`: the comparison is natural in the
  corepresentation data. This is the general form of a compatibility with restriction; what it
  still needs to become one is discussed in the last section of this docstring.

## Implementation notes

The construction is the `δ`-functor argument of
`StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison`, reassembled so
that nothing is chosen. The two sides of the comparison are made `δ`-functors by transporting
the `δ`-functor `extDeltaFunctor` on `Ext` along `extFunctorObjIsoRightDerived`, the degreewise
identification of `Ext` out of a corepresenting object with the right-derived functors of the
corepresented functor; both transports are universal, so Stacks 010U produces a unique
isomorphism of `δ`-functors extending any isomorphism in degree zero, and the canonical
degree-zero isomorphism is taken. This differs from the existence version in two ways: the
degrees are not treated by separate constructions, and the comparison in positive degree is no
longer only known to exist.

What this does **not** provide is naturality in the object `U` of the site — but it does provide
naturality in the corepresentation data, which is everything about it that is not specific to the
site. See the last section of this docstring.

## Naturality

Compatibility with restriction says, for `f : U ⟶ V`, that the comparisons for `U` and for `V`
commute with the maps `NatTrans.rightDerived` induces on cohomology from restriction of sections.
Both maps to be compared are morphisms of `δ`-functors out of the universal `δ`-functor of the
`V` side, so Stacks 010S reduces the claim to degree zero, where both comparisons are the
canonical `degreeZeroIso`. That argument is carried out in full generality here, in
`comparisonIso_naturality`: for any `ρ : G' ⟶ G`, `x : X ⟶ X'`, `y : Y ⟶ Y'` whose
corepresentations match up, the comparison commutes with `NatTrans.rightDerived ρ` in every
degree. Its inputs are

* `extFunctorObjIsoRightDerived_naturality` — the identification of `Ext` with right-derived
  functors is natural in the corepresenting object. In positive degree this is
  `rightDerivedCoyonedaSuccIso_naturality`, read on the chosen injective resolution through
  `extLeftHomologyMapDataFst`; in degree zero it is `extZeroIsoCoyoneda_naturality` together
  with `toRightDerivedZero_naturality_functor`, which is naturality of
  `Functor.toRightDerivedZero` in the *functor* (Mathlib has it only in the object);
* `extDeltaFunctorPrecomp` — precomposition on `Ext` is a morphism of `δ`-functors, which is
  `Ext.comp_assoc`;
* `selfDerivedDeltaFunctorRestriction` and `derivedDeltaFunctorRestriction` — the two halves
  that package the above as morphisms of the transported `δ`-functors;
* `degreeZeroIso_naturality` — the degree-zero case.

What is still missing, and all that is missing, is the *site-level* instantiation: for `f : U ⟶ V`
one must produce the three maps and the two compatibilities that `comparisonIso_naturality`
consumes, namely that `evaluationRepresentation` is natural in `U` against restriction of
sections, and that `tensorSheafHomIso` is natural in the abelian presheaf `P`. The second needs
`tensorSheafHomIso` to stop being `no_expose`; the extension-of-scalars adjunction data of
`ModuleCohomologyComparison` it unfolds to is already public, so there is no visibility cascade
left to open. It is bookkeeping about that adjunction, not homological algebra.

In particular the two clauses of Stacks 01F1 this file was built for are not blocked on anything
deeper: not on a missing long exact sequence for `Functor.rightDerived`, and not on any choice.

## References

* [Stacks: Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks: Tag 010U](https://stacks.math.columbia.edu/tag/010U)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits CategoryTheory.Abelian

namespace ModuleSheafCohomology

/-! ### `Functor.toRightDerivedZero` is natural in the functor

Mathlib's `InjectiveResolution.toRightDerivedZero'_naturality` moves the object; these two move
the functor. They are what identifies `NatTrans.rightDerived` in degree zero with the
transformation it was derived from, and so are the degree-zero input to the naturality of the
comparison in the corepresenting object. -/

section RightDerivedZero

universe v u u'

variable {A : Type u} [Category.{v} A] [Abelian A] {D : Type u'} [Category.{v} D] [Abelian D]

/-- The canonical map from an object to the cycles of the image of an injective resolution is
natural in the functor: for `ρ : H ⟶ H'`, applying `ρ` and then the map for `H'` is the map for
`H` followed by `ρ` on cycles. Both sides are cocycles, so this is
`InjectiveResolution.toRightDerivedZero'_comp_iCycles` on each side followed by naturality of
`ρ` at `I.ι.f 0`. -/
lemma toRightDerivedZero'_naturality_functor {Z : A} (I : InjectiveResolution Z)
    {H H' : A ⥤ D} [H.Additive] [H'.Additive] (ρ : H ⟶ H') :
    ρ.app Z ≫ I.toRightDerivedZero' H' =
      I.toRightDerivedZero' H ≫ HomologicalComplex.cyclesMap
        ((NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℕ)).app I.cocomplex) 0 := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ 0)]
  simp only [Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles,
    HomologicalComplex.cyclesMap_i,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
  exact (ρ.naturality (I.ι.f 0)).symm

variable [HasInjectiveResolutions A]

/-- **`Functor.toRightDerivedZero` is natural in the functor.** For `ρ : H ⟶ H'` of additive
functors, `ρ` followed by the canonical map `H' ⟶ H'.rightDerived 0` is the canonical map
`H ⟶ H.rightDerived 0` followed by `NatTrans.rightDerived ρ 0`.

Both sides are read on the chosen injective resolution, by
`InjectiveResolution.toRightDerivedZero_eq` and `InjectiveResolution.rightDerived_app_eq`, after
which the content is `toRightDerivedZero'_naturality_functor` on cycles and
`HomologicalComplex.homologyπ_naturality` for the passage from cycles to homology. The
reassociations are written as terms: `InjectiveResolution.isoRightDerivedObj` presents the
homology as `(HomologicalComplex.homologyFunctor _ _ 0).obj K` while
`CochainComplex.isoHomologyπ₀` presents it as `K.homology 0`, and `Category.assoc` does not fire
across that junction. -/
lemma toRightDerivedZero_naturality_functor {H H' : A ⥤ D} [H.Additive] [H'.Additive]
    (ρ : H ⟶ H') :
    ρ ≫ H'.toRightDerivedZero = H.toRightDerivedZero ≫ NatTrans.rightDerived ρ 0 := by
  refine NatTrans.ext (funext fun Z => ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app,
    InjectiveResolution.toRightDerivedZero_eq (injectiveResolution Z) H',
    InjectiveResolution.toRightDerivedZero_eq (injectiveResolution Z) H,
    InjectiveResolution.rightDerived_app_eq ρ (injectiveResolution Z) 0]
  set r := ρ.app Z
  set t := (injectiveResolution Z).toRightDerivedZero' H
  set t' := (injectiveResolution Z).toRightDerivedZero' H'
  set ψ := (NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℕ)).app
    (injectiveResolution Z).cocomplex
  set π := (CochainComplex.isoHomologyπ₀ ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution Z).cocomplex)).hom
  set π' := (CochainComplex.isoHomologyπ₀ ((H'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution Z).cocomplex)).hom
  set a := (injectiveResolution Z).isoRightDerivedObj H 0
  set b := (injectiveResolution Z).isoRightDerivedObj H' 0
  set m := (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) 0).map ψ
  have f1 : r ≫ t' = t ≫ HomologicalComplex.cyclesMap ψ 0 :=
    toRightDerivedZero'_naturality_functor (injectiveResolution Z) ρ
  have f2 : HomologicalComplex.cyclesMap ψ 0 ≫ π' = π ≫ m :=
    (HomologicalComplex.homologyπ_naturality ψ 0).symm
  have hrhs : (t ≫ π ≫ a.inv) ≫ a.hom ≫ m ≫ b.inv = t ≫ π ≫ m ≫ b.inv :=
    (Category.assoc t (π ≫ a.inv) (a.hom ≫ m ≫ b.inv)).trans
      (congrArg (fun k => t ≫ k)
        ((Category.assoc π a.inv (a.hom ≫ m ≫ b.inv)).trans
          (congrArg (fun k => π ≫ k) (Iso.inv_hom_id_assoc a (m ≫ b.inv)))))
  have hlhs : r ≫ t' ≫ π' ≫ b.inv = t ≫ π ≫ m ≫ b.inv :=
    (Category.assoc r t' (π' ≫ b.inv)).symm.trans
      ((congrArg (fun k => k ≫ π' ≫ b.inv) f1).trans
        ((Category.assoc t (HomologicalComplex.cyclesMap ψ 0) (π' ≫ b.inv)).trans
          (congrArg (fun k => t ≫ k)
            ((Category.assoc (HomologicalComplex.cyclesMap ψ 0) π' b.inv).symm.trans
              ((congrArg (fun k => k ≫ b.inv) f2).trans
                (Category.assoc π m b.inv))))))
  exact hlhs.trans hrhs.symm

end RightDerivedZero

/-! ### `Ext` out of a corepresenting object computes right-derived functors -/

section Corepresented

universe v u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]

/-- **`Ext` out of a corepresenting object computes right-derived functors.** For an additive,
left exact `G : A ⥤ Ab` corepresented by `X`, the `Ext`-functors out of `X` are the right-derived
functors of `G`, in every degree. In degree zero this is the corepresentation composed with left
exactness of `G`; in positive degree it is `rightDerivedCoyonedaSuccIso`, the identification of
`Ext` in the second variable with the right-derived functors of `preadditiveCoyoneda`,
transported along the corepresentation by `rightDerivedIso`.

This is the constructive content of `nonempty_extFunctorObj_iso_rightDerived`. The two degree
ranges are built by different constructions and no compatibility between them is claimed; what
normalizes the comparisons assembled from this is the degree-zero component of the `δ`-functor
isomorphism, not this definition. -/
def extFunctorObjIsoRightDerived (G : A ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G]
    (X : A) (α : G ≅ preadditiveCoyoneda.obj (op X)) :
    ∀ n : ℕ, extFunctorObj X n ≅ G.rightDerived n
  | 0 => extZeroIsoCoyoneda X ≪≫ α.symm ≪≫ G.rightDerivedZeroIsoSelf.symm
  | n + 1 => (rightDerivedCoyonedaSuccIso X n).symm ≪≫ rightDerivedIso α.symm (n + 1)

/-- In degree zero, `extFunctorObjIsoRightDerived` is the corepresentation followed by the
inverse of the degree-zero normalization of the right-derived functors. -/
lemma extFunctorObjIsoRightDerived_zero (G : A ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G]
    (X : A) (α : G ≅ preadditiveCoyoneda.obj (op X)) :
    extFunctorObjIsoRightDerived G X α 0 =
      extZeroIsoCoyoneda X ≪≫ α.symm ≪≫ G.rightDerivedZeroIsoSelf.symm :=
  rfl

/-- In positive degree, `extFunctorObjIsoRightDerived` is `rightDerivedCoyonedaSuccIso`
transported along the corepresentation. -/
lemma extFunctorObjIsoRightDerived_succ (G : A ⥤ Ab.{v}) [G.Additive]
    [PreservesFiniteLimits G] (X : A) (α : G ≅ preadditiveCoyoneda.obj (op X)) (n : ℕ) :
    extFunctorObjIsoRightDerived G X α (n + 1) =
      (rightDerivedCoyonedaSuccIso X n).symm ≪≫ rightDerivedIso α.symm (n + 1) :=
  rfl

/-! ### Naturality in the corepresenting object

The comparison of `Ext` with right-derived functors is natural in the corepresenting object.
This is the input a compatibility with restriction needs, and the two lemmas below are its
positive-degree and degree-zero halves. -/

omit [HasInjectiveResolutions A] in
/-- Precomposition with `x : X ⟶ X'`, as a natural transformation of `Ext`-functors out of `X'`
and out of `X`. This is `extFunctor` applied to `x.op`, with its type spelled through
`extFunctorObj`; the two agree only after unfolding `extFunctor`, which is enough to stop `rw`
and `simp` from firing across the difference. -/
def extPrecomp {X X' : A} (x : X ⟶ X') (n : ℕ) : extFunctorObj X' n ⟶ extFunctorObj X n :=
  (extFunctor n).map x.op

omit [HasInjectiveResolutions A] in
/-- The map of Hom short complexes induced by precomposition with `x : X ⟶ X'`: the first-variable
counterpart of `homShortComplexMap`, which moves the injective resolution instead. -/
abbrev homShortComplexMapFst {Z : A} (I : InjectiveResolution Z) {X X' : A} (x : X ⟶ X')
    (n : ℕ) : homShortComplex I X' n ⟶ homShortComplex I X n :=
  (HomologicalComplex.shortComplexFunctor' Ab.{v} (ComplexShape.up ℕ) n (n + 1) (n + 2)).map
    ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map x.op)
      (ComplexShape.up ℕ)).app I.cocomplex)

omit [HasInjectiveResolutions A] in
/-- **`extLeftHomologyData` is natural in the first `Ext` variable.** Precomposition with
`x : X ⟶ X'` carries a cocycle `t` of `Hom(I, X')` to the cocycle `x ≫ t` of `Hom(I, X)` and the
class `I.extMk t` to `Ext.mk₀ x` composed with it, which is `mk₀_comp_extMk`. The first-variable
counterpart of `extLeftHomologyMapData`. -/
def extLeftHomologyMapDataFst {Z : A} (I : InjectiveResolution Z) {X X' : A} (x : X ⟶ X')
    (n : ℕ) :
    ShortComplex.LeftHomologyMapData (homShortComplexMapFst I x n)
      (extLeftHomologyData I X' n) (extLeftHomologyData I X n) where
  φK := AddCommGrpCat.ofHom
    { toFun t := ⟨x ≫ (t.val : X' ⟶ I.cocomplex.X (n + 1)), by
        have ht : (t.val : X' ⟶ I.cocomplex.X (n + 1)) ≫
            I.cocomplex.d (n + 1) (n + 2) = 0 := t.property
        exact (Category.assoc x (t.val : X' ⟶ I.cocomplex.X (n + 1))
            (I.cocomplex.d (n + 1) (n + 2))).trans
          ((congrArg (fun k => x ≫ k) ht).trans comp_zero)⟩
      map_zero' := Subtype.ext comp_zero
      map_add' t t' := Subtype.ext (Preadditive.comp_add X X' (I.cocomplex.X (n + 1)) x
        (t.val : X' ⟶ I.cocomplex.X (n + 1)) (t'.val : X' ⟶ I.cocomplex.X (n + 1))) }
  φH := (extPrecomp x (n + 1)).app Z
  commi := by ext t; rfl
  commf' := by
    ext u
    exact Subtype.ext (Category.assoc x (u : X' ⟶ I.cocomplex.X n)
      (I.cocomplex.d n (n + 1))).symm
  commπ := by
    ext t
    exact I.mk₀_comp_extMk t.val (n + 2) rfl t.property x

omit [HasInjectiveResolutions A] in
/-- **`extZeroIsoCoyoneda` is natural in `X`.** The degree-zero half of the naturality of
`extFunctorObjIsoRightDerived` in the corepresenting object: the identification of `Ext X Z 0`
with `X ⟶ Z` turns precomposition on `Ext` into precomposition on morphisms. -/
lemma extZeroIsoCoyoneda_naturality {X X' : A} (x : X ⟶ X') :
    extPrecomp x 0 ≫ (extZeroIsoCoyoneda X).hom =
      (extZeroIsoCoyoneda X').hom ≫ preadditiveCoyoneda.map x.op := by
  ext Z a
  change Ext.addEquiv₀ ((Ext.mk₀ x).comp a (zero_add 0)) = x ≫ Ext.addEquiv₀ a
  apply Ext.addEquiv₀.symm.injective
  simp only [AddEquiv.symm_apply_apply, Ext.addEquiv₀_symm_apply, ← Ext.mk₀_comp_mk₀]
  exact congrArg (fun k => (Ext.mk₀ x).comp k (zero_add 0))
    (Ext.mk₀_addEquiv₀_apply a).symm

/-- `rightDerivedCoyonedaSuccIso` on the chosen injective resolution, in the form of its
component morphism rather than its component isomorphism. See
`rightDerivedCoyonedaSuccIso_app`. -/
lemma rightDerivedCoyonedaSuccIso_hom_app (X Z : A) (n : ℕ)
    (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    (rightDerivedCoyonedaSuccIso X n).hom.app Z =
      ((injectiveResolution Z).isoRightDerivedObj
          (preadditiveCoyoneda.obj (op X)) (n + 1)).hom ≫
        (HomologicalComplex.homologyFunctorIso' Ab.{v} (ComplexShape.up ℕ) n (n + 1) (n + 2)
          hi hk).hom.app _ ≫
        (extLeftHomologyData (injectiveResolution Z) X n).homologyIso.hom :=
  rfl

/-- **`rightDerivedCoyonedaSuccIso` is natural in `X`.** The positive-degree half of the
naturality of `extFunctorObjIsoRightDerived` in the corepresenting object: precomposition with
`x : X ⟶ X'` on `Ext` corresponds, under the identification of `Ext` with the right-derived
functors of `preadditiveCoyoneda`, to `NatTrans.rightDerived` of precomposition with `x` on
`Hom(X', -)`.

Both sides are read on the chosen injective resolution, where the right-derived functor is
`InjectiveResolution.rightDerived_app_eq`, the passage to the short complex in degrees
`n, n + 1, n + 2` is naturality of `HomologicalComplex.homologyFunctorIso'`, and the
identification with `Ext` is `extLeftHomologyMapDataFst`. The reassociations are written as
terms: `InjectiveResolution.isoRightDerivedObj` presents the homology as
`(HomologicalComplex.homologyFunctor _ _ p).obj K` while `ShortComplex.homologyMap` presents it
as `K.homology p`, and `Category.assoc` does not fire across that junction. -/
lemma rightDerivedCoyonedaSuccIso_naturality {X X' : A} (x : X ⟶ X') (n : ℕ) :
    NatTrans.rightDerived (preadditiveCoyoneda.map x.op) (n + 1) ≫
        (rightDerivedCoyonedaSuccIso X n).hom =
      (rightDerivedCoyonedaSuccIso X' n).hom ≫ extPrecomp x (n + 1) := by
  have hi : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  have hk : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by simp
  refine NatTrans.ext (funext fun Z => ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app,
    rightDerivedCoyonedaSuccIso_hom_app X Z n hi hk,
    rightDerivedCoyonedaSuccIso_hom_app X' Z n hi hk,
    InjectiveResolution.rightDerived_app_eq (preadditiveCoyoneda.map x.op)
      (injectiveResolution Z) (n + 1)]
  set q := (injectiveResolution Z).isoRightDerivedObj
    (preadditiveCoyoneda.obj (op X)) (n + 1) 
  set p := ((injectiveResolution Z).isoRightDerivedObj
    (preadditiveCoyoneda.obj (op X')) (n + 1)).hom 
  set m := (HomologicalComplex.homologyFunctor Ab.{v} (ComplexShape.up ℕ) (n + 1)).map
    ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map x.op)
      (ComplexShape.up ℕ)).app (injectiveResolution Z).cocomplex) 
  set u := (HomologicalComplex.homologyFunctorIso' Ab.{v} (ComplexShape.up ℕ) n (n + 1) (n + 2)
    hi hk).hom.app (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution Z).cocomplex) 
  set u' := (HomologicalComplex.homologyFunctorIso' Ab.{v} (ComplexShape.up ℕ) n (n + 1) (n + 2)
    hi hk).hom.app (((preadditiveCoyoneda.obj (op X')).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution Z).cocomplex) 
  set v := (extLeftHomologyData (injectiveResolution Z) X n).homologyIso.hom 
  set v' := (extLeftHomologyData (injectiveResolution Z) X' n).homologyIso.hom 
  set e := (extPrecomp x (n + 1)).app Z 
  have key : m ≫ u = u' ≫ ShortComplex.homologyMap
      (homShortComplexMapFst (injectiveResolution Z) x n) :=
    (HomologicalComplex.homologyFunctorIso' Ab.{v} (ComplexShape.up ℕ) n (n + 1) (n + 2)
      hi hk).hom.naturality _
  have hcomm : ShortComplex.homologyMap
      (homShortComplexMapFst (injectiveResolution Z) x n) ≫ v = v' ≫ e :=
    (extLeftHomologyMapDataFst (injectiveResolution Z) x n).homologyMap_comm
  have hrd : (p ≫ m ≫ q.inv) ≫ q.hom = p ≫ m := by
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmain : m ≫ u ≫ v = u' ≫ v' ≫ e :=
    (Category.assoc m u v).symm.trans
      ((congrArg (fun k => k ≫ v) key).trans
        ((Category.assoc u' _ v).trans (congrArg (fun k => u' ≫ k) hcomm)))
  exact (Category.assoc (p ≫ m ≫ q.inv) q.hom (u ≫ v)).symm.trans
    ((congrArg (fun k => k ≫ u ≫ v) hrd).trans
      ((Category.assoc p m (u ≫ v)).trans
        ((congrArg (fun k => p ≫ k) hmain).trans
          ((Category.assoc p (u' ≫ v') e).trans
            (congrArg (fun k => p ≫ k) (Category.assoc u' v' e))).symm)))

/-- If `ρ` intertwines `α.hom` and `α'.hom` with `c`, then `c` intertwines `α.inv` and
`α'.inv` with `ρ`. -/
private lemma comp_inv_eq_inv_comp_of_comp_hom_eq {C : Type*} [Category C] {G G' P P' : C}
    {ρ : G' ⟶ G} {c : P' ⟶ P} {α : G ≅ P} {α' : G' ≅ P'} (h : ρ ≫ α.hom = α'.hom ≫ c) :
    c ≫ α.inv = α'.inv ≫ ρ := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- **The comparison of `Ext` with right-derived functors is natural in the corepresenting
object.** Let `G` and `G'` be corepresented by `X` and `X'`, let `ρ : G' ⟶ G`, let `x : X ⟶ X'`,
and suppose the corepresentations identify `ρ` with precomposition by `x`. Then
`extFunctorObjIsoRightDerived` carries precomposition by `x` on `Ext` to
`NatTrans.rightDerived ρ`, in every degree.

In degree zero this is `extZeroIsoCoyoneda_naturality` together with
`toRightDerivedZero_naturality_functor`; in positive degree it is
`rightDerivedCoyonedaSuccIso_naturality` together with functoriality of
`NatTrans.rightDerived`. -/
lemma extFunctorObjIsoRightDerived_naturality
    {G G' : A ⥤ Ab.{v}} [G.Additive] [G'.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteLimits G'] {X X' : A} (x : X ⟶ X')
    (α : G ≅ preadditiveCoyoneda.obj (op X)) (α' : G' ≅ preadditiveCoyoneda.obj (op X'))
    (ρ : G' ⟶ G) (hρ : ρ ≫ α.hom = α'.hom ≫ preadditiveCoyoneda.map x.op) (n : ℕ) :
    extPrecomp x n ≫ (extFunctorObjIsoRightDerived G X α n).hom =
      (extFunctorObjIsoRightDerived G' X' α' n).hom ≫ NatTrans.rightDerived ρ n := by
  have hα := comp_inv_eq_inv_comp_of_comp_hom_eq hρ
  cases n with
  | zero =>
      simp only [extFunctorObjIsoRightDerived_zero, Iso.trans_hom, Iso.symm_hom,
        Functor.rightDerivedZeroIsoSelf_inv, Category.assoc]
      rw [← Category.assoc, extZeroIsoCoyoneda_naturality, Category.assoc,
        ← Category.assoc (preadditiveCoyoneda.map x.op) α.inv G.toRightDerivedZero, hα,
        Category.assoc, toRightDerivedZero_naturality_functor ρ]
  | succ n =>
      rw [extFunctorObjIsoRightDerived_succ, extFunctorObjIsoRightDerived_succ]
      change extPrecomp x (n + 1) ≫ (rightDerivedCoyonedaSuccIso X n).inv ≫
            NatTrans.rightDerived α.inv (n + 1) =
          ((rightDerivedCoyonedaSuccIso X' n).inv ≫ NatTrans.rightDerived α'.inv (n + 1)) ≫
            NatTrans.rightDerived ρ (n + 1)
      have hinv := comp_inv_eq_inv_comp_of_comp_hom_eq
        (rightDerivedCoyonedaSuccIso_naturality x n)
      rw [← Category.assoc, hinv, Category.assoc, Category.assoc,
        ← NatTrans.rightDerived_comp, ← NatTrans.rightDerived_comp, hα]

/-! ### The characterization on injective resolutions -/

/-- **`rightDerivedCoyonedaSuccIso` on the chosen injective resolution.** At an object `Z`, the
identification of the degree `n + 1` right-derived functor of `Hom(X, -)` with `Ext X Z (n + 1)`
is: compute the right-derived functor on the chosen injective resolution `I` of `Z`
(`InjectiveResolution.isoRightDerivedObj`), read its degree `n + 1` cohomology as the homology
of the short complex of `Hom(I, X)` in degrees `n, n + 1, n + 2`
(`HomologicalComplex.homologyFunctorIso'`), and identify that homology with `Ext` by
`extLeftHomologyData`. This holds by definition and is recorded so that consumers need not
unfold the definition. -/
lemma rightDerivedCoyonedaSuccIso_app (X Z : A) (n : ℕ)
    (hi : (ComplexShape.up ℕ).prev (n + 1) = n)
    (hk : (ComplexShape.up ℕ).next (n + 1) = n + 2) :
    (rightDerivedCoyonedaSuccIso X n).app Z =
      (injectiveResolution Z).isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) (n + 1) ≪≫
        (HomologicalComplex.homologyFunctorIso' Ab.{v} (ComplexShape.up ℕ) n (n + 1) (n + 2)
          hi hk).app _ ≪≫
        (extLeftHomologyData (injectiveResolution Z) X n).homologyIso :=
  rfl

omit [HasInjectiveResolutions A] in
/-- **The homology data identifying `Ext` with cocycles.** The projection of
`extLeftHomologyData` to its homology object is `extCyclesMap`: a cocycle
`f : I.cocomplex.X (n + 1) ⟶ X` of the Hom-complex of an injective resolution `I` of `Y` is sent
to the class `I.extMk f`. -/
lemma extLeftHomologyData_π {Y : A} (I : InjectiveResolution Y) (X : A) (n : ℕ) :
    (extLeftHomologyData I X n).π = AddCommGrpCat.ofHom (extCyclesMap I X n) :=
  rfl

omit [HasInjectiveResolutions A] in
/-- `extCyclesMap` sends a cocycle to the `Ext` class it represents. -/
lemma extCyclesMap_apply {Y : A} (I : InjectiveResolution Y) (X : A) (n : ℕ)
    (f : (homShortComplex I X n).g.hom.ker) :
    extCyclesMap I X n f = I.extMk f.val (n + 2) rfl f.property :=
  rfl

end Corepresented

/-! ### Precomposition as a morphism of `δ`-functors -/

section DeltaPrecomp

universe v u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
  {B : Type u'} [Category.{v} B] [Abelian B]

/-- **Precomposition on `Ext` is a morphism of `δ`-functors.** The connecting morphism of
`extDeltaFunctor` is postcomposition with the `Ext`-class of a short exact sequence, and
`extPrecomp` is precomposition, so the compatibility is associativity of `Ext`-composition. -/
def extDeltaFunctorPrecomp (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {X X' : A} (x : X ⟶ X') :
    extDeltaFunctor F X' ⟶ extDeltaFunctor F X where
  app n := Functor.whiskerLeft F (extPrecomp x n)
  comm {S} hS n := by
    have := hS.mono_f
    have := hS.epi_g
    ext e
    change ((Ext.mk₀ x).comp e (zero_add n)).comp (hS.map_of_exact F).extClass rfl =
      (Ext.mk₀ x).comp (e.comp (hS.map_of_exact F).extClass rfl) (zero_add (n + 1))
    exact Ext.comp_assoc (Ext.mk₀ x) e (hS.map_of_exact F).extClass (zero_add n) rfl
      (by lia)

end DeltaPrecomp

/-! ### The comparison as an isomorphism of `δ`-functors -/

section Comparison

universe v u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]
  {B : Type u'} [Category.{v} B] [Abelian B] [HasExt.{v} B] [HasInjectiveResolutions B]
  [EnoughInjectives B]

/-- The `δ`-functor on the right-derived functors of a corepresented functor on `B` itself,
obtained by transporting the `δ`-functor structure of `Ext` along
`extFunctorObjIsoRightDerived`. Its component functors are literally the `H.rightDerived n`. -/
@[ega "0 12.1.1" "more general"]
def selfDerivedDeltaFunctor (H : B ⥤ Ab.{v}) [H.Additive] [PreservesFiniteLimits H] (Y : B)
    (γ : H ≅ preadditiveCoyoneda.obj (op Y)) : DeltaFunctor B Ab.{v} :=
  (extDeltaFunctor (𝟭 B) Y).ofIso (fun n => H.rightDerived n)
    (fun n => extFunctorObjIsoRightDerived H Y γ n)

/-- The transported `δ`-functor is universal: `Ext` out of anything vanishes in positive degree
against an injective object. -/
@[ega "0 12.1.1" "more general"]
lemma selfDerivedDeltaFunctor_isUniversal (H : B ⥤ Ab.{v}) [H.Additive]
    [PreservesFiniteLimits H] (Y : B) (γ : H ≅ preadditiveCoyoneda.obj (op Y)) :
    (selfDerivedDeltaFunctor H Y γ).IsUniversal :=
  have : (extDeltaFunctor (𝟭 B) Y).IsUniversal :=
    extDeltaFunctor_isUniversal (𝟭 B) Y (by
      intro I _ n e
      change Ext.{v} Y I (n + 1) at e
      exact Ext.eq_zero_of_injective e)
  DeltaFunctor.ofIso_isUniversal _ _ _

/-- The `δ`-functor on `F ⋙ G.rightDerived n` for an exact `F` and a corepresented `G`, obtained
by transporting the `δ`-functor structure of `Ext` in the second variable precomposed with `F`
along `extFunctorObjIsoRightDerived`. Its component functors are literally the
`F ⋙ G.rightDerived n`. -/
@[sga "4 V 2.1.1" "more general"]
def derivedDeltaFunctor (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : A ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G] (X : A)
    (α : G ≅ preadditiveCoyoneda.obj (op X)) : DeltaFunctor B Ab.{v} :=
  (extDeltaFunctor F X).ofIso (fun n => F ⋙ G.rightDerived n)
    (fun n => Functor.isoWhiskerLeft F (extFunctorObjIsoRightDerived G X α n))

omit [HasExt.{v} B] [HasInjectiveResolutions B] in
/-- The transported `δ`-functor is universal exactly when the underlying `Ext`-`δ`-functor is,
which is the acyclicity hypothesis: `Ext X (F.obj I) (n + 1)` vanishes for injective `I`. -/
lemma derivedDeltaFunctor_isUniversal (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : A ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G] (X : A)
    (α : G ≅ preadditiveCoyoneda.obj (op X))
    (h : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext.{v} X (F.obj I) (n + 1)), e = 0) :
    (derivedDeltaFunctor F G X α).IsUniversal :=
  have : (extDeltaFunctor F X).IsUniversal := extDeltaFunctor_isUniversal F X h
  DeltaFunctor.ofIso_isUniversal _ _ _

variable (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : A ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G]

/-- **The canonical degree-zero comparison.** Both `(F ⋙ G).rightDerived 0` and
`F ⋙ G.rightDerived 0` are canonically `F ⋙ G`, by left exactness; this is the resulting
isomorphism between them. No hypothesis beyond left exactness is used, and nothing is chosen. -/
def degreeZeroIso : (F ⋙ G).rightDerived 0 ≅ F ⋙ G.rightDerived 0 :=
  (F ⋙ G).rightDerivedZeroIsoSelf ≪≫ Functor.isoWhiskerLeft F G.rightDerivedZeroIsoSelf.symm

omit [HasExt.{v} A] [HasExt.{v} B] [EnoughInjectives B] [PreservesFiniteColimits F] in
/-- The degree-zero comparison intertwines the two canonical maps to the zeroth right-derived
functors. -/
@[reassoc]
lemma toRightDerivedZero_comp_degreeZeroIso :
    (F ⋙ G).toRightDerivedZero ≫ (degreeZeroIso F G).hom =
      Functor.whiskerLeft F G.toRightDerivedZero := by
  simp [degreeZeroIso]

variable (X : A) (α : G ≅ preadditiveCoyoneda.obj (op X)) (Y : B)
  (β : preadditiveCoyoneda.obj (op Y) ≅ F ⋙ preadditiveCoyoneda.obj (op X))
  (h : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext.{v} X (F.obj I) (n + 1)), e = 0)

/-- The corepresentation of `F ⋙ G` by `Y` obtained from the corepresentation `α` of `G` by `X`
and the identification `β` of maps out of `Y` with maps out of `X` after `F`. -/
def compCorepresentation : F ⋙ G ≅ preadditiveCoyoneda.obj (op Y) :=
  Functor.isoWhiskerLeft F α ≪≫ β.symm

/-- **The comparison of Stacks 03FD as an isomorphism of `δ`-functors.** Deriving `F ⋙ G` and
deriving `G` after `F` are both universal `δ`-functors — the first because `Ext` is, the second
because of the acyclicity hypothesis `h` — so by Stacks 010U there is a unique isomorphism of
`δ`-functors between them extending the canonical degree-zero isomorphism `degreeZeroIso`.
This is it. -/
def comparisonDeltaIso :
    selfDerivedDeltaFunctor (F ⋙ G) Y (compCorepresentation F G X α Y β) ≅
      derivedDeltaFunctor F G X α :=
  haveI := selfDerivedDeltaFunctor_isUniversal (F ⋙ G) Y (compCorepresentation F G X α Y β)
  haveI := derivedDeltaFunctor_isUniversal F G X α h
  DeltaFunctor.IsUniversal.isoOfIso (degreeZeroIso F G)

/-- **Stacks 03FD, constructively.** For an exact functor `F` and a left exact functor `G`
corepresented by `X`, such that `Ext X (F.obj I) (n + 1)` vanishes on injectives `I`, deriving
the composite `F ⋙ G` agrees with applying `F` and deriving `G`, in every degree. This is a
named isomorphism, not a choice: it is the degreewise component of `comparisonDeltaIso`. -/
def comparisonIso (n : ℕ) : (F ⋙ G).rightDerived n ≅ F ⋙ G.rightDerived n where
  hom := (comparisonDeltaIso F G X α Y β h).hom.app n
  inv := (comparisonDeltaIso F G X α Y β h).inv.app n
  hom_inv_id := congrArg (fun η => η.app n) (comparisonDeltaIso F G X α Y β h).hom_inv_id
  inv_hom_id := congrArg (fun η => η.app n) (comparisonDeltaIso F G X α Y β h).inv_hom_id

/-- The degree-zero component of the `δ`-functor isomorphism is the canonical degree-zero
isomorphism it was built to extend. -/
@[simp]
lemma comparisonDeltaIso_hom_app_zero :
    (comparisonDeltaIso F G X α Y β h).hom.app 0 = (degreeZeroIso F G).hom :=
  have := selfDerivedDeltaFunctor_isUniversal (F ⋙ G) Y (compCorepresentation F G X α Y β)
  have := derivedDeltaFunctor_isUniversal F G X α h
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero
    (F := selfDerivedDeltaFunctor (F ⋙ G) Y (compCorepresentation F G X α Y β))
    (G := derivedDeltaFunctor F G X α) (degreeZeroIso F G)

/-- In degree zero the comparison is the canonical isomorphism `degreeZeroIso`. -/
@[simp]
lemma comparisonIso_zero : comparisonIso F G X α Y β h 0 = degreeZeroIso F G :=
  Iso.ext (comparisonDeltaIso_hom_app_zero F G X α Y β h)

/-- **The degree-zero normalization of Stacks 03FD.** The comparison intertwines the two
canonical maps to the zeroth right-derived functors. This is the same equation that
`moduleSheafCohomologyIsoUnderlying` asserts of its chosen comparison, and here it holds by
construction. -/
@[reassoc]
lemma toRightDerivedZero_comp_comparisonIso :
    (F ⋙ G).toRightDerivedZero ≫ (comparisonIso F G X α Y β h 0).hom =
      Functor.whiskerLeft F G.toRightDerivedZero := by
  rw [comparisonIso_zero]
  exact toRightDerivedZero_comp_degreeZeroIso F G

/-- **The characterization of the comparison.** Any morphism of `δ`-functors from the derived
`δ`-functor of `F ⋙ G` to that of `G` after `F` whose degree-zero component is the canonical
isomorphism *is* the comparison, in every degree. Universality of the source (Stacks 010S) makes
the degree-zero component determine everything. -/
lemma comparisonIso_hom_eq
    (η : selfDerivedDeltaFunctor (F ⋙ G) Y (compCorepresentation F G X α Y β) ⟶
      derivedDeltaFunctor F G X α)
    (h₀ : η.app 0 = (degreeZeroIso F G).hom) (n : ℕ) :
    η.app n = (comparisonIso F G X α Y β h n).hom := by
  have := selfDerivedDeltaFunctor_isUniversal (F ⋙ G) Y (compCorepresentation F G X α Y β)
  have := derivedDeltaFunctor_isUniversal F G X α h
  have : η = (comparisonDeltaIso F G X α Y β h).hom := by
    refine DeltaFunctor.IsUniversal.hom_ext_zero _ ?_
    rw [h₀, comparisonDeltaIso_hom_app_zero]
  rw [this]
  rfl

/-- Any two isomorphisms of `δ`-functors between the two sides agree as soon as they agree in
degree zero (Stacks 010U), so the comparison is determined by its degree-zero component. -/
lemma comparisonDeltaIso_eq
    (η : selfDerivedDeltaFunctor (F ⋙ G) Y (compCorepresentation F G X α Y β) ≅
      derivedDeltaFunctor F G X α)
    (h₀ : η.hom.app 0 = (degreeZeroIso F G).hom) :
    η = comparisonDeltaIso F G X α Y β h := by
  have := selfDerivedDeltaFunctor_isUniversal (F ⋙ G) Y (compCorepresentation F G X α Y β)
  have := derivedDeltaFunctor_isUniversal F G X α h
  refine DeltaFunctor.IsUniversal.iso_ext ?_
  rw [h₀, comparisonDeltaIso_hom_app_zero]

end Comparison

/-! ### Naturality of the comparison in the corepresentation data -/

section Naturality

universe v u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]
  {B : Type u'} [Category.{v} B] [Abelian B] [HasExt.{v} B] [HasInjectiveResolutions B]
  [EnoughInjectives B]

/-- The connecting morphism of the `δ`-functor `Ext Y (-)`, with its type spelled without the
identity functor in the way `extDeltaFunctor` leaves it. Only the spelling differs; stating it
this way is what lets `Category.assoc` fire in the proofs below. -/
def extDelta (Y : B) {S : ShortComplex B} (hS : S.ShortExact) (n : ℕ) :
    (extFunctorObj Y n).obj S.X₃ ⟶ (extFunctorObj Y (n + 1)).obj S.X₁ :=
  (extDeltaFunctor (𝟭 B) Y).δ hS n

omit [EnoughInjectives B] in
/-- The connecting morphism of `selfDerivedDeltaFunctor` is the one of `Ext` conjugated by
`extFunctorObjIsoRightDerived`. -/
lemma selfDerivedDeltaFunctor_δ {H : B ⥤ Ab.{v}} [H.Additive] [PreservesFiniteLimits H]
    {Y : B} (γ : H ≅ preadditiveCoyoneda.obj (op Y)) {S : ShortComplex B} (hS : S.ShortExact)
    (n : ℕ) :
    (selfDerivedDeltaFunctor H Y γ).δ hS n =
      (extFunctorObjIsoRightDerived H Y γ n).inv.app S.X₃ ≫ extDelta Y hS n ≫
        (extFunctorObjIsoRightDerived H Y γ (n + 1)).hom.app S.X₁ := by
  rfl

/-- **Restriction is a morphism of `δ`-functors, on the derived functors of a corepresented
functor on `B`.** Given `σ : H' ⟶ H` and `y : Y ⟶ Y'` identified by the corepresentations, the
family `NatTrans.rightDerived σ` commutes with the connecting morphisms. The connecting
morphisms are conjugates of the ones on `Ext` (`selfDerivedDeltaFunctor_δ`), so this is
`extFunctorObjIsoRightDerived_naturality` together with `extDeltaFunctorPrecomp`. -/
def selfDerivedDeltaFunctorRestriction
    {H H' : B ⥤ Ab.{v}} [H.Additive] [H'.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteLimits H'] (σ : H' ⟶ H) {Y Y' : B} (y : Y ⟶ Y')
    (γ : H ≅ preadditiveCoyoneda.obj (op Y)) (γ' : H' ≅ preadditiveCoyoneda.obj (op Y'))
    (hσ : σ ≫ γ.hom = γ'.hom ≫ preadditiveCoyoneda.map y.op) :
    selfDerivedDeltaFunctor H' Y' γ' ⟶ selfDerivedDeltaFunctor H Y γ where
  app n := NatTrans.rightDerived σ n
  comm {S} hS n := by
    have N : ∀ m : ℕ, extPrecomp y m ≫ (extFunctorObjIsoRightDerived H Y γ m).hom =
        (extFunctorObjIsoRightDerived H' Y' γ' m).hom ≫ NatTrans.rightDerived σ m :=
      fun m => extFunctorObjIsoRightDerived_naturality y γ γ' σ hσ m
    have Ninv : ∀ m : ℕ, NatTrans.rightDerived σ m ≫
        (extFunctorObjIsoRightDerived H Y γ m).inv =
        (extFunctorObjIsoRightDerived H' Y' γ' m).inv ≫ extPrecomp y m := by
      intro m
      rw [← cancel_mono (extFunctorObjIsoRightDerived H Y γ m).hom, Category.assoc,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, N m, Iso.inv_hom_id_assoc]
    have h1 : (NatTrans.rightDerived σ n).app S.X₃ ≫
        (extFunctorObjIsoRightDerived H Y γ n).inv.app S.X₃ =
        (extFunctorObjIsoRightDerived H' Y' γ' n).inv.app S.X₃ ≫ (extPrecomp y n).app S.X₃ :=
      NatTrans.congr_app (Ninv n) S.X₃
    have h2 : (extPrecomp y (n + 1)).app S.X₁ ≫
        (extFunctorObjIsoRightDerived H Y γ (n + 1)).hom.app S.X₁ =
        (extFunctorObjIsoRightDerived H' Y' γ' (n + 1)).hom.app S.X₁ ≫
          (NatTrans.rightDerived σ (n + 1)).app S.X₁ :=
      NatTrans.congr_app (N (n + 1)) S.X₁
    have P : (extPrecomp y n).app S.X₃ ≫ extDelta Y hS n =
        extDelta Y' hS n ≫ (extPrecomp y (n + 1)).app S.X₁ :=
      (extDeltaFunctorPrecomp (𝟭 B) y).comm hS n
    change (NatTrans.rightDerived σ n).app S.X₃ ≫ (selfDerivedDeltaFunctor H Y γ).δ hS n =
      (selfDerivedDeltaFunctor H' Y' γ').δ hS n ≫ (NatTrans.rightDerived σ (n + 1)).app S.X₁
    rw [selfDerivedDeltaFunctor_δ, selfDerivedDeltaFunctor_δ]
    set rn := (NatTrans.rightDerived σ n).app S.X₃
    set rn1 := (NatTrans.rightDerived σ (n + 1)).app S.X₁
    set iH := (extFunctorObjIsoRightDerived H Y γ n).inv.app S.X₃
    set iH' := (extFunctorObjIsoRightDerived H' Y' γ' n).inv.app S.X₃
    set hH := (extFunctorObjIsoRightDerived H Y γ (n + 1)).hom.app S.X₁
    set hH' := (extFunctorObjIsoRightDerived H' Y' γ' (n + 1)).hom.app S.X₁
    set en := (extPrecomp y n).app S.X₃
    set en1 := (extPrecomp y (n + 1)).app S.X₁
    set dY := extDelta Y hS n
    set dY' := extDelta Y' hS n
    exact (Category.assoc rn iH (dY ≫ hH)).symm.trans
      ((congrArg (fun k => k ≫ dY ≫ hH) h1).trans
        ((Category.assoc iH' en (dY ≫ hH)).trans
          (congrArg (fun k => iH' ≫ k)
            ((Category.assoc en dY hH).symm.trans
              ((congrArg (fun k => k ≫ hH) P).trans
                ((Category.assoc dY' en1 hH).trans
                  (congrArg (fun k => dY' ≫ k) h2)))))))

/-- The connecting morphism of the `δ`-functor `Ext X (F -)`, with its type spelled without the
functor composition. As for `extDelta`, only the spelling differs. -/
def extDeltaComp (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (X : A) {S : ShortComplex B} (hS : S.ShortExact) (n : ℕ) :
    (extFunctorObj X n).obj (F.obj S.X₃) ⟶ (extFunctorObj X (n + 1)).obj (F.obj S.X₁) :=
  (extDeltaFunctor F X).δ hS n

omit [HasExt.{v} B] [HasInjectiveResolutions B] [EnoughInjectives B] in
/-- The connecting morphism of `derivedDeltaFunctor` is the one of `Ext` conjugated by
`extFunctorObjIsoRightDerived`, whiskered by `F`. -/
lemma derivedDeltaFunctor_δ (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : A ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G]
    (X : A) (α : G ≅ preadditiveCoyoneda.obj (op X)) {S : ShortComplex B} (hS : S.ShortExact)
    (n : ℕ) :
    (derivedDeltaFunctor F G X α).δ hS n =
      (extFunctorObjIsoRightDerived G X α n).inv.app (F.obj S.X₃) ≫ extDeltaComp F X hS n ≫
        (extFunctorObjIsoRightDerived G X α (n + 1)).hom.app (F.obj S.X₁) :=
  rfl

/-- **Restriction is a morphism of `δ`-functors, on `F` followed by the derived functors of a
corepresented functor on `A`.** The counterpart of `selfDerivedDeltaFunctorRestriction` for the
other side of the comparison, proved the same way. -/
def derivedDeltaFunctorRestriction (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {G G' : A ⥤ Ab.{v}} [G.Additive] [G'.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteLimits G'] (ρ : G' ⟶ G) {X X' : A} (x : X ⟶ X')
    (α : G ≅ preadditiveCoyoneda.obj (op X)) (α' : G' ≅ preadditiveCoyoneda.obj (op X'))
    (hα : ρ ≫ α.hom = α'.hom ≫ preadditiveCoyoneda.map x.op) :
    derivedDeltaFunctor F G' X' α' ⟶ derivedDeltaFunctor F G X α where
  app n := Functor.whiskerLeft F (NatTrans.rightDerived ρ n)
  comm {S} hS n := by
    have N : ∀ m : ℕ, extPrecomp x m ≫ (extFunctorObjIsoRightDerived G X α m).hom =
        (extFunctorObjIsoRightDerived G' X' α' m).hom ≫ NatTrans.rightDerived ρ m :=
      fun m => extFunctorObjIsoRightDerived_naturality x α α' ρ hα m
    have Ninv : ∀ m : ℕ, NatTrans.rightDerived ρ m ≫
        (extFunctorObjIsoRightDerived G X α m).inv =
        (extFunctorObjIsoRightDerived G' X' α' m).inv ≫ extPrecomp x m := by
      intro m
      rw [← cancel_mono (extFunctorObjIsoRightDerived G X α m).hom, Category.assoc,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, N m, Iso.inv_hom_id_assoc]
    have h1 : (NatTrans.rightDerived ρ n).app (F.obj S.X₃) ≫
        (extFunctorObjIsoRightDerived G X α n).inv.app (F.obj S.X₃) =
        (extFunctorObjIsoRightDerived G' X' α' n).inv.app (F.obj S.X₃) ≫
          (extPrecomp x n).app (F.obj S.X₃) :=
      NatTrans.congr_app (Ninv n) (F.obj S.X₃)
    have h2 : (extPrecomp x (n + 1)).app (F.obj S.X₁) ≫
        (extFunctorObjIsoRightDerived G X α (n + 1)).hom.app (F.obj S.X₁) =
        (extFunctorObjIsoRightDerived G' X' α' (n + 1)).hom.app (F.obj S.X₁) ≫
          (NatTrans.rightDerived ρ (n + 1)).app (F.obj S.X₁) :=
      NatTrans.congr_app (N (n + 1)) (F.obj S.X₁)
    have P : (extPrecomp x n).app (F.obj S.X₃) ≫ extDeltaComp F X hS n =
        extDeltaComp F X' hS n ≫ (extPrecomp x (n + 1)).app (F.obj S.X₁) :=
      (extDeltaFunctorPrecomp F x).comm hS n
    change (NatTrans.rightDerived ρ n).app (F.obj S.X₃) ≫ (derivedDeltaFunctor F G X α).δ hS n =
      (derivedDeltaFunctor F G' X' α').δ hS n ≫
        (NatTrans.rightDerived ρ (n + 1)).app (F.obj S.X₁)
    rw [derivedDeltaFunctor_δ, derivedDeltaFunctor_δ]
    set rn := (NatTrans.rightDerived ρ n).app (F.obj S.X₃)
    set rn1 := (NatTrans.rightDerived ρ (n + 1)).app (F.obj S.X₁)
    set iH := (extFunctorObjIsoRightDerived G X α n).inv.app (F.obj S.X₃)
    set iH' := (extFunctorObjIsoRightDerived G' X' α' n).inv.app (F.obj S.X₃)
    set hH := (extFunctorObjIsoRightDerived G X α (n + 1)).hom.app (F.obj S.X₁)
    set hH' := (extFunctorObjIsoRightDerived G' X' α' (n + 1)).hom.app (F.obj S.X₁)
    set en := (extPrecomp x n).app (F.obj S.X₃)
    set en1 := (extPrecomp x (n + 1)).app (F.obj S.X₁)
    set dX := extDeltaComp F X hS n
    set dX' := extDeltaComp F X' hS n
    exact (Category.assoc rn iH (dX ≫ hH)).symm.trans
      ((congrArg (fun k => k ≫ dX ≫ hH) h1).trans
        ((Category.assoc iH' en (dX ≫ hH)).trans
          (congrArg (fun k => iH' ≫ k)
            ((Category.assoc en dX hH).symm.trans
              ((congrArg (fun k => k ≫ hH) P).trans
                ((Category.assoc dX' en1 hH).trans
                  (congrArg (fun k => dX' ≫ k) h2)))))))

omit [HasExt.{v} A] [HasExt.{v} B] [EnoughInjectives B] in
/-- **The canonical degree-zero comparison is natural in the functor.** This is
`toRightDerivedZero_naturality_functor`, used once for `Functor.whiskerLeft F ρ` on the
composite and once for `ρ` on the second factor. -/
lemma degreeZeroIso_naturality (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F]
    {G G' : A ⥤ Ab.{v}} [G.Additive] [G'.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteLimits G'] (ρ : G' ⟶ G) :
    NatTrans.rightDerived (Functor.whiskerLeft F ρ) 0 ≫ (degreeZeroIso F G).hom =
      (degreeZeroIso F G').hom ≫ Functor.whiskerLeft F (NatTrans.rightDerived ρ 0) := by
  have hτ := toRightDerivedZero_naturality_functor (Functor.whiskerLeft F ρ)
  have hA : NatTrans.rightDerived (Functor.whiskerLeft F ρ) 0 ≫
      (F ⋙ G).rightDerivedZeroIsoSelf.hom =
      (F ⋙ G').rightDerivedZeroIsoSelf.hom ≫ Functor.whiskerLeft F ρ := by
    rw [← cancel_epi (F ⋙ G').toRightDerivedZero, ← Category.assoc, ← hτ]
    simp
  have hB : Functor.whiskerLeft F G'.toRightDerivedZero ≫
      Functor.whiskerLeft F (NatTrans.rightDerived ρ 0) =
      Functor.whiskerLeft F ρ ≫ Functor.whiskerLeft F G.toRightDerivedZero := by
    rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp,
      ← toRightDerivedZero_naturality_functor ρ]
  simp only [degreeZeroIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.rightDerivedZeroIsoSelf_inv, Category.assoc]
  rw [← Category.assoc, hA, Category.assoc, hB]

/-- **The comparison of Stacks 03FD is natural in the corepresentation data.** Let `ρ : G' ⟶ G`
be a transformation of corepresented functors, identified by the corepresentations with
precomposition along `x : X ⟶ X'`, and let `y : Y ⟶ Y'` identify the corepresentations of the
composites with `F`. Then the comparisons for `(G, X, Y)` and for `(G', X', Y')` commute, in
every degree, with the maps `NatTrans.rightDerived` induces from `ρ`.

Both composites are morphisms of `δ`-functors out of the universal `δ`-functor of the
`(G', X', Y')` side — `selfDerivedDeltaFunctorRestriction` and
`derivedDeltaFunctorRestriction` supply the two restriction halves — so by Stacks 010S it is
enough that they agree in degree zero, where both comparisons are the canonical `degreeZeroIso`
and the statement is `degreeZeroIso_naturality`. -/
theorem comparisonIso_naturality
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {G G' : A ⥤ Ab.{v}} [G.Additive] [G'.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteLimits G'] (ρ : G' ⟶ G) {X X' : A} (x : X ⟶ X')
    (α : G ≅ preadditiveCoyoneda.obj (op X)) (α' : G' ≅ preadditiveCoyoneda.obj (op X'))
    {Y Y' : B} (y : Y ⟶ Y')
    (β : preadditiveCoyoneda.obj (op Y) ≅ F ⋙ preadditiveCoyoneda.obj (op X))
    (β' : preadditiveCoyoneda.obj (op Y') ≅ F ⋙ preadditiveCoyoneda.obj (op X'))
    (h : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext.{v} X (F.obj I) (n + 1)), e = 0)
    (h' : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext.{v} X' (F.obj I) (n + 1)), e = 0)
    (hα : ρ ≫ α.hom = α'.hom ≫ preadditiveCoyoneda.map x.op)
    (hβ : Functor.whiskerLeft F ρ ≫ (compCorepresentation F G X α Y β).hom =
      (compCorepresentation F G' X' α' Y' β').hom ≫ preadditiveCoyoneda.map y.op)
    (n : ℕ) :
    NatTrans.rightDerived (Functor.whiskerLeft F ρ) n ≫
        (comparisonIso F G X α Y β h n).hom =
      (comparisonIso F G' X' α' Y' β' h' n).hom ≫
        Functor.whiskerLeft F (NatTrans.rightDerived ρ n) := by
  have hUniv := selfDerivedDeltaFunctor_isUniversal (F ⋙ G') Y'
    (compCorepresentation F G' X' α' Y' β')
  have key : selfDerivedDeltaFunctorRestriction (Functor.whiskerLeft F ρ) y
        (compCorepresentation F G X α Y β) (compCorepresentation F G' X' α' Y' β') hβ ≫
      (comparisonDeltaIso F G X α Y β h).hom =
      (comparisonDeltaIso F G' X' α' Y' β' h').hom ≫
        derivedDeltaFunctorRestriction F ρ x α α' hα := by
    refine DeltaFunctor.IsUniversal.hom_ext_zero _ ?_
    change NatTrans.rightDerived (Functor.whiskerLeft F ρ) 0 ≫
      (comparisonDeltaIso F G X α Y β h).hom.app 0 =
      (comparisonDeltaIso F G' X' α' Y' β' h').hom.app 0 ≫
        Functor.whiskerLeft F (NatTrans.rightDerived ρ 0)
    rw [comparisonDeltaIso_hom_app_zero, comparisonDeltaIso_hom_app_zero]
    exact degreeZeroIso_naturality F ρ
  exact congrArg (fun η => η.app n) key

end Naturality

/-! ### The two instances of Stacks 03FD -/

section Site

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})

/-- Global sections of abelian sheaves form an additive functor. -/
local instance : (Sheaf.Γ J Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Taking sections over `U` is an additive functor on abelian sheaves. -/
local instance (U : C) : ((sheafSections J Ab.{u}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- Taking sections over `U` preserves finite limits of abelian sheaves. -/
local instance (U : C) :
    PreservesFiniteLimits ((sheafSections J Ab.{u}).obj (op U)) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J Ab.{u}).symm

attribute [local instance] toSheaf_preservesFiniteColimits

/-- **Stacks 03FD for global sections, as a named isomorphism.** Deriving the global sections of
a sheaf of modules and then forgetting agrees, in every degree, with forgetting to an abelian
sheaf and deriving global sections there. Global sections of abelian sheaves are corepresented by
the constant sheaf on `ℤ` (`globalSectionsRepresentation`), which is sectionwise torsion free, so
the acyclicity hypothesis is `ext_eq_zero_of_isTorsionFree`. -/
def globalSectionsComparisonIso (n : ℕ) :
    (SheafOfModules.toSheaf.{u} R ⋙ Sheaf.Γ J Ab.{u}).rightDerived n ≅
      SheafOfModules.toSheaf.{u} R ⋙ (Sheaf.Γ J Ab.{u}).rightDerived n :=
  comparisonIso (SheafOfModules.toSheaf.{u} R) (Sheaf.Γ J Ab.{u}) _
    (globalSectionsRepresentation J)
    ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
      (tensorPresheaf R.obj ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))))
    (tensorSheafHomIso J R ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))))
    (fun I _ index extension =>
      ext_eq_zero_of_isTorsionFree J R I _
        (isTorsionFree_sheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
          (fun _ => by
            change Module.IsTorsionFree ℤ (ULift.{u} ℤ)
            exact Module.Flat.isTorsionFree)) index extension)
    n

/-- The degree-zero normalization of `globalSectionsComparisonIso`. -/
lemma toRightDerivedZero_comp_globalSectionsComparisonIso :
    (SheafOfModules.toSheaf.{u} R ⋙ Sheaf.Γ J Ab.{u}).toRightDerivedZero ≫
        (globalSectionsComparisonIso J R 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf.{u} R) (Sheaf.Γ J Ab.{u}).toRightDerivedZero :=
  toRightDerivedZero_comp_comparisonIso _ _ _ _ _ _ _

/-- **Stacks 03FD for sections over an object of the site, as a named isomorphism.** Deriving
sections over `U` of a sheaf of modules and then forgetting agrees, in every degree, with
forgetting to an abelian sheaf and deriving sections over `U` there. Sections over `U` of abelian
sheaves are corepresented by the sheafification of the free abelian presheaf on `yoneda.obj U`
(`evaluationRepresentation`), and the acyclicity hypothesis is
`ext_eq_zero_of_injective_toSheaf`.

Unlike `moduleSheafCohomologyIsoUnderlying`, which quantifies `∀ U, ∃ eU`, this is one named
isomorphism depending on `U`; that is what makes a compatibility with restriction a meaningful
statement at all. -/
def sectionsComparisonIso (U : C) (n : ℕ) :
    (SheafOfModules.toSheaf.{u} R ⋙ (sheafSections J Ab.{u}).obj (op U)).rightDerived n ≅
      SheafOfModules.toSheaf.{u} R ⋙ ((sheafSections J Ab.{u}).obj (op U)).rightDerived n :=
  comparisonIso (SheafOfModules.toSheaf.{u} R) ((sheafSections J Ab.{u}).obj (op U)) _
    (evaluationRepresentation J U)
    ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
      (tensorPresheaf R.obj (yoneda.obj U ⋙ AddCommGrpCat.free)))
    (tensorSheafHomIso J R (yoneda.obj U ⋙ AddCommGrpCat.free))
    (fun I _ index extension => ext_eq_zero_of_injective_toSheaf J R I U index extension) n

/-- The degree-zero normalization of `sectionsComparisonIso`. -/
lemma toRightDerivedZero_comp_sectionsComparisonIso (U : C) :
    (SheafOfModules.toSheaf.{u} R ⋙ (sheafSections J Ab.{u}).obj (op U)).toRightDerivedZero ≫
        (sectionsComparisonIso J R U 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf.{u} R)
        ((sheafSections J Ab.{u}).obj (op U)).toRightDerivedZero :=
  toRightDerivedZero_comp_comparisonIso _ _ _ _ _ _ _

/-- **Stacks 03FD**, in the existence form of `moduleSheafCohomologyIsoUnderlying`, recovered
from the two named isomorphisms. Nothing uses this form; it is recorded so that the existence
statement and the construction cannot drift apart. -/
theorem exists_moduleSheafCohomologyIsoUnderlying :
    ∃ eSite : ∀ i : ℕ,
        (SheafOfModules.toSheaf.{u} R ⋙ Sheaf.Γ J Ab.{u}).rightDerived i ≅
          SheafOfModules.toSheaf.{u} R ⋙ (Sheaf.Γ J Ab.{u}).rightDerived i,
      (SheafOfModules.toSheaf.{u} R ⋙ Sheaf.Γ J Ab.{u}).toRightDerivedZero ≫
          (eSite 0).hom =
        Functor.whiskerLeft (SheafOfModules.toSheaf.{u} R)
          (Sheaf.Γ J Ab.{u}).toRightDerivedZero ∧
      ∀ U : C,
        ∃ eU : ∀ i : ℕ,
            (SheafOfModules.toSheaf.{u} R ⋙
                (sheafSections J Ab.{u}).obj (op U)).rightDerived i ≅
              SheafOfModules.toSheaf.{u} R ⋙
                ((sheafSections J Ab.{u}).obj (op U)).rightDerived i,
          (SheafOfModules.toSheaf.{u} R ⋙
                (sheafSections J Ab.{u}).obj (op U)).toRightDerivedZero ≫
              (eU 0).hom =
            Functor.whiskerLeft (SheafOfModules.toSheaf.{u} R)
              ((sheafSections J Ab.{u}).obj (op U)).toRightDerivedZero :=
  ⟨globalSectionsComparisonIso J R, toRightDerivedZero_comp_globalSectionsComparisonIso J R,
    fun U => ⟨sectionsComparisonIso J R U,
      toRightDerivedZero_comp_sectionsComparisonIso J R U⟩⟩

end Site

end ModuleSheafCohomology

end
