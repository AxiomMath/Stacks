module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The derived form of Tag 08PT is independent of the point resolution

Let `C` be a small category with the chaotic topology, let `B` be a ring, and let `ℱ` be a
diagram of `B`-modules on `Cᵒᵖ`. For every point resolution `U_•` of `C` —
`Stacks.ChaoticSite.IsPointResolution` — the module
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolution`
produces an isomorphism

`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)`

(`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`), one point resolution at a
time. This file shows that the family of these isomorphisms is **natural in the point
resolution**: a morphism `v : U_• ⟶ V_•` of cosimplicial objects of `C` induces a map
`ℱ(V_•) ⟶ ℱ(U_•)` of extended Moore complexes — evaluation of `ℱ` is contravariant — and the
triangle

`Q(ℱ(V_•)) ⟶ Q(ℱ(U_•)) ⟶ Lπ_!(ℱ)`,

whose second arrow is the isomorphism at `U_•` and whose composite is asserted to be the
isomorphism at `V_•`, commutes. Equivalently: the isomorphism does not depend on the chosen point
resolution, compatibly with maps between point resolutions. This is the totalized form of the
canonical map of [Stacks, Tag 08Q6]: the content of that tag is that the comparison of a section
with derived lower shriek is canonical, and here the "section" is the whole extended Moore complex
of a cosimplicial object rather than a single object of the site.

## Why it is cheap

The isomorphism `mooreCochainQIsoDerivedColimitOfResolution` takes the projective resolution
`ε : P^• ⟶ ℱ[0]` of the coefficient diagram as a *parameter*, and only its first two factors
mention `U_•` at all: the two filtrations of the double complex `mooreBicomplex U P`. The last two
factors — the computation of `Lπ_!` on the K-projective complex `P^•` and the comparison
`Lπ_!(P^•) ≅ Lπ_!(ℱ)` — are the same term for every point resolution. So the whole statement
reduces to two chain-level squares for the double complex map `Z_V ⟶ Z_U` induced by `v`, and the
column square is the only one carrying content: **both column augmentations land in the same
`(colim P^•)[0]`**, and the triangle they form is the relation
`ℱ(v_0) ≫ ι_{U_0} = ι_{V_0}` between colimit injections — `CategoryTheory.Limits.colimit.w`. No
homology is computed.

Because `mooreCochainQIsoDerivedColimit` builds its resolution from the coefficient diagram `ℱ`
alone, the same chosen resolution serves every point resolution, and the naturality statement for
it is the statement for a fixed resolution.

## Main definitions

* `Stacks.ChaoticSite.ModuleValued.mooreSimpMap`: the map of Moore complexes
  `ℱ(V_•) ⟶ ℱ(U_•)` induced by a morphism `v : U_• ⟶ V_•` of cosimplicial objects, natural
  in `ℱ`.
* `Stacks.ChaoticSite.ModuleValued.mooreCochainMap`: the same map on extended Moore complexes,
  read as cochain complexes over `ℤ`.

## Main results

* `Stacks.ChaoticSite.ModuleValued.mooreCochainMap_comp_augmentation`: **the augmentations to
  `(colim ℱ)[0]` agree**, which is the one piece of content.
* `Stacks.ChaoticSite.ModuleValued.mooreBicomplexMap_comp_columnMap` and
  `Stacks.ChaoticSite.ModuleValued.mooreBicomplexMap_comp_rowMap`: the two chain-level squares
  for the double complexes.
* `Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoTotal_naturality` and
  `Stacks.ChaoticSite.ModuleValued.totalQIsoColimOfResolution_naturality`: naturality of the
  two filtrations.
* `Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimitOfResolution_naturality` and
  `Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit_naturality`: **the derived form
  of [Stacks, Tag 08PT] is natural in the point resolution.**

## Implementation notes

The naturality is in the point resolution only; it is still not naturality in the coefficient
diagram `ℱ`, which the construction cannot give — see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolution`. What
is proved here is what a consumer comparing two resolutions of the same object needs, for instance
the comparison of two presentations of an algebra in [Stacks, Tag 08PU].

`HomologicalComplex.singleMapHomologicalComplex_hom_naturality` is a general statement about
Mathlib's comparison `single ⋙ F.mapHomologicalComplex ≅ F ⋙ single`, namely that it is natural
in the functor `F`. Mathlib records that comparison as a natural isomorphism in the *object* only,
so the statement in the functor variable is proved here; it is needed because the first filtration
of the double complex is set up through that comparison.

## References

* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology StacksDraft.TotalComplexQuasiIso

/-! ### Naturality of the comparison `single ⋙ F.mapHomologicalComplex ≅ F ⋙ single` -/

namespace HomologicalComplex

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [Preadditive W₁] [Preadditive W₂]
  [HasZeroObject W₁] [HasZeroObject W₂] {ι : Type*} [DecidableEq ι]

/-- **Mathlib's comparison `single ⋙ F.mapHomologicalComplex ≅ F ⋙ single` is natural in the
functor `F`.** For a natural transformation `τ : F ⟶ G` of functors preserving zero morphisms,
the square relating the two comparisons commutes: in the degree `j` it is the naturality of `τ`
at the identification of the degree-`j` term of `(single X)` with `X`, and in every other degree
both composites leave a zero object. -/
lemma singleMapHomologicalComplex_hom_naturality (c : ComplexShape ι) (j : ι)
    {F G : W₁ ⥤ W₂} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G) (X : W₁) :
    (NatTrans.mapHomologicalComplex τ c).app ((single W₁ c j).obj X) ≫
        (singleMapHomologicalComplex G c j).hom.app X =
      (singleMapHomologicalComplex F c j).hom.app X ≫ (single W₂ c j).map (τ.app X) := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  by_cases hi : i = j
  · subst hi
    have hτ : τ.app (((single W₁ c i).obj X).X i) ≫ G.map (singleObjXSelf c i X).hom =
        F.map (singleObjXSelf c i X).hom ≫ τ.app X :=
      (τ.naturality (singleObjXSelf c i X).hom).symm
    rw [comp_f, comp_f, singleMapHomologicalComplex_hom_app_self,
      singleMapHomologicalComplex_hom_app_self, single_map_f_self]
    change τ.app (((single W₁ c i).obj X).X i) ≫ _ = _
    rw [← Category.assoc, hτ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · exact (Functor.map_isZero F (isZero_single_obj_X c j X i hi)).eq_of_src _ _

end HomologicalComplex

namespace Stacks.ChaoticSite.ModuleValued

/-! ### Naturality of the total complex of a double complex concentrated in the column zero -/

section TotalSingleColumnZero

variable {A : Type*} [Category* A] [Abelian A]

/-- **The identification of a cochain complex with the total complex of the double complex
concentrated in its column zero is natural.** This is
`StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit_naturality` at `a = 0`, where the shift
by `-0` is removed by `CategoryTheory.shiftFunctorZero`. -/
lemma totalSingleColumnZeroIso_hom_naturality {W W' : CochainComplex A ℤ} (g : W ⟶ W')
    [(singleColumn W 0).HasTotal (ComplexShape.up ℤ)]
    [(singleColumn W' 0).HasTotal (ComplexShape.up ℤ)] :
    g ≫ (totalSingleColumnZeroIso W').hom =
      (totalSingleColumnZeroIso W).hom ≫
        HomologicalComplex₂.total.map ((HomologicalComplex.single (CochainComplex A ℤ)
          (ComplexShape.up ℤ) 0).map g) (ComplexShape.up ℤ) := by
  have hshift : ((CategoryTheory.shiftFunctorZero (CochainComplex A ℤ) ℤ).app W).inv ≫
      (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-0 : ℤ)).map g =
        g ≫ ((CategoryTheory.shiftFunctorZero (CochainComplex A ℤ) ℤ).app W').inv :=
    ((CategoryTheory.shiftFunctorZero (CochainComplex A ℤ) ℤ).inv.naturality g).symm
  have hunit := totalSingleColumnUnit_naturality g (0 : ℤ)
  dsimp only [totalSingleColumnZeroIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [Category.assoc, ← hunit]
  simp only [← Category.assoc, hshift]

end TotalSingleColumnZero

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B] {U V : CosimplicialObject C}

/-! ### The map of Moore complexes induced by a morphism of cosimplicial objects -/

/-- **The map of Moore complexes induced by a morphism `v : U_• ⟶ V_•` of cosimplicial objects
of the site**, `ℱ(V_•) ⟶ ℱ(U_•)`, natural in the diagram `ℱ` of `B`-modules: the evaluation of
`ℱ` is contravariant, so the map goes from the resolution `V_•` to the resolution `U_•`. -/
def mooreSimpMap (v : U ⟶ V) :
    moduleCosimplicialMooreComplex (B := B) V ⟶ moduleCosimplicialMooreComplex (B := B) U :=
  Functor.whiskerRight
    ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (ModuleCat.{u} B)).map (NatTrans.op v))
    (alternatingFaceMapComplex (ModuleCat.{u} B))

/-- **The map of extended Moore complexes induced by a morphism of cosimplicial objects**, read
as a map of cochain complexes over `ℤ`: the reindexing of
`Stacks.ChaoticSite.ModuleValued.mooreSimpMap` along `ComplexShape.embeddingUpIntLE 0`. -/
def mooreCochainMap (v : U ⟶ V) :
    mooreCochainComplex (B := B) V ⟶ mooreCochainComplex (B := B) U :=
  Functor.whiskerRight (mooreSimpMap v)
    ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{u} B))

/-- The degree-zero component of `Stacks.ChaoticSite.ModuleValued.mooreSimpMap` is the
restriction of sections along `v_0 : U_0 ⟶ V_0`. -/
lemma mooreSimpMap_app_f_zero (v : U ⟶ V) (F : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    ((mooreSimpMap (B := B) v).app F).f 0 = F.map (v.app (SimplexCategory.mk 0)).op :=
  rfl

/-- The degree-zero component of `Stacks.ChaoticSite.ModuleValued.mooreCochainMap`, through the
identification of the degree-zero term of the extended Moore complex with `ℱ(U_0)`. -/
lemma mooreCochainMap_app_f_zero (v : U ⟶ V) (F : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    ((mooreCochainMap (B := B) v).app F).f 0 =
      (GeneralValued.mooreCochainXZeroIso V F).hom ≫ ((mooreSimpMap v).app F).f 0 ≫
        (GeneralValued.mooreCochainXZeroIso U F).inv :=
  HomologicalComplex.extendMap_f _ _ (by simp)

/-- **The augmentations to `(colim ℱ)[0]` of the extended Moore complexes of two point
resolutions agree**, compatibly with a morphism `v : U_• ⟶ V_•` between them. This is the one
piece of content in the naturality of the derived comparison: in degree zero the statement is the
relation `ℱ(v_0) ≫ ι_{U_0} = ι_{V_0}` between the colimit injections of `colim ℱ`, and in every
other degree the target is a zero object. -/
lemma mooreCochainMap_comp_augmentation (v : U ⟶ V) :
    mooreCochainMap (B := B) v ≫ mooreCochainAugmentation U = mooreCochainAugmentation V := by
  refine NatTrans.ext (funext fun F => HomologicalComplex.hom_ext _ _ (fun q => ?_))
  by_cases hq : q = 0
  · subst hq
    rw [NatTrans.comp_app, HomologicalComplex.comp_f, mooreCochainMap_app_f_zero,
      GeneralValued.mooreCochainAugmentation_f_zero,
      GeneralValued.mooreCochainAugmentation_f_zero, GeneralValued.mooreCochainAug₀,
      GeneralValued.mooreCochainAug₀, mooreSimpMap_app_f_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (F.map (v.app (SimplexCategory.mk 0)).op),
      colimit.w F (v.app (SimplexCategory.mk 0)).op]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (colim.obj F) q hq).eq_of_tgt _ _

/-! ### The two chain-level squares for the double complexes -/

variable (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ)

/-- **The map of double complexes induced by a morphism of cosimplicial objects**,
`mooreBicomplex V P ⟶ mooreBicomplex U P`: the map of extended Moore complexes applied in each
first degree. -/
abbrev mooreBicomplexMap (v : U ⟶ V) :
    mooreBicomplex V P ⟶ mooreBicomplex U P :=
  (NatTrans.mapHomologicalComplex (mooreCochainMap v) (ComplexShape.up ℤ)).app P

/-- **The columnwise augmentations of the two double complexes land in the same `(colim P^•)[0]`,
compatibly with a morphism of cosimplicial objects.** This is
`Stacks.ChaoticSite.ModuleValued.mooreCochainMap_comp_augmentation` applied in each first
degree. -/
lemma mooreBicomplexMap_comp_columnMap (v : U ⟶ V) :
    mooreBicomplexMap P v ≫ mooreBicomplexColumnMap U P = mooreBicomplexColumnMap V P := by
  rw [mooreBicomplexMap, mooreBicomplexColumnMap, mooreBicomplexColumnMap, ← NatTrans.comp_app,
    ← NatTrans.mapHomologicalComplex_comp, mooreCochainMap_comp_augmentation]

variable (F : Cᵒᵖ ⥤ ModuleCat.{u} B)

/-- **The rowwise augmentations of the two double complexes are compatible with a morphism of
cosimplicial objects**: this is the naturality of
`Stacks.ChaoticSite.ModuleValued.mooreCochainMap`, read on complexes, at the resolution
`ε : P^• ⟶ ℱ[0]`. -/
lemma mooreBicomplexMap_comp_rowMap (v : U ⟶ V)
    (ε : P ⟶ (HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F) :
    mooreBicomplexMap P v ≫ mooreBicomplexRowMap U P F ε =
      mooreBicomplexRowMap V P F ε ≫
        mooreBicomplexMap
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F) v :=
  (NatTrans.mapHomologicalComplex_naturality (mooreCochainMap v) ε).symm

/-- **The first factor of the comparison — the identification of the extended Moore complex with
the total complex of the double complex of a resolution — is compatible with a morphism of
cosimplicial objects.** The two ingredients are the naturality of the identification of a complex
with the total complex of its column-zero double complex, and the naturality of Mathlib's
comparison `single ⋙ F.mapHomologicalComplex ≅ F ⋙ single` in the functor `F`. -/
lemma mooreCochainMap_comp_totalSingleColumn (v : U ⟶ V) :
    (mooreCochainMap v).app F ≫
        (totalSingleColumnZeroIso ((mooreCochainComplex U).obj F)).hom ≫
        HomologicalComplex₂.total.map
          ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
            (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ) =
      (totalSingleColumnZeroIso ((mooreCochainComplex V).obj F)).hom ≫
        HomologicalComplex₂.total.map
          ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex V)
            (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map (mooreBicomplexMap
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F) v)
          (ComplexShape.up ℤ) := by
  have hsingle : ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex V)
        (ComplexShape.up ℤ) 0).app F).inv ≫
      mooreBicomplexMap
        ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F) v =
    (HomologicalComplex.single (CochainComplex (ModuleCat.{u} B) ℤ) (ComplexShape.up ℤ) 0).map
        ((mooreCochainMap v).app F) ≫
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
        (ComplexShape.up ℤ) 0).app F).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    simpa only [Iso.app_hom, mooreBicomplexMap] using
      HomologicalComplex.singleMapHomologicalComplex_hom_naturality (ComplexShape.up ℤ) 0
        (mooreCochainMap v) F
  rw [← Category.assoc, totalSingleColumnZeroIso_hom_naturality ((mooreCochainMap v).app F)]
  simp only [Category.assoc, ← HomologicalComplex₂.total.map_comp, hsingle]

/-! ### Naturality of the derived comparison -/

/-- An equation `f ≫ g = k` of maps of double complexes persists after `Q ∘ Tot`. -/
private lemma Q_map_total_map_comp_eq
    {X Y Z : HomologicalComplex₂ (ModuleCat.{u} B) (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (h : f ≫ g = k) :
    DerivedCategory.Q.map (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (HomologicalComplex₂.total.map g (ComplexShape.up ℤ)) =
      DerivedCategory.Q.map (HomologicalComplex₂.total.map k (ComplexShape.up ℤ)) := by
  subst h
  simp only [HomologicalComplex₂.total.map_comp, Functor.map_comp]

/-- **Naturality in the point resolution of the comparison through the second filtration** of the
double complex. -/
lemma mooreCochainQIsoTotal_naturality (v : U ⟶ V) [P.IsStrictlyLE 0]
    (ε : P ⟶ (HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)
    [QuasiIso ε] :
    DerivedCategory.Q.map ((mooreCochainMap v).app F) ≫
        (mooreCochainQIsoTotal U F P ε).hom =
      (mooreCochainQIsoTotal V F P ε).hom ≫
        DerivedCategory.Q.map (HomologicalComplex₂.total.map (mooreBicomplexMap P v)
          (ComplexShape.up ℤ)) := by
  have _hV : QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexRowMap V P F ε)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexRowTotalMap V P F ε
  have _hU : QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexRowMap U P F ε)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexRowTotalMap U P F ε
  have hrow := Q_map_total_map_comp_eq (mooreBicomplexMap_comp_rowMap P F v ε)
  simp only [HomologicalComplex₂.total.map_comp, Functor.map_comp] at hrow
  have hcol := congrArg DerivedCategory.Q.map (mooreCochainMap_comp_totalSingleColumn F v)
  simp only [Functor.map_comp] at hcol
  refine (cancel_mono (DerivedCategory.Q.map (HomologicalComplex₂.total.map
    (mooreBicomplexRowMap U P F ε) (ComplexShape.up ℤ)))).mp ?_
  dsimp only [mooreCochainQIsoTotal, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    Functor.mapIso_hom]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, hrow,
    IsIso.inv_hom_id_assoc]
  exact hcol

/-- **Naturality in the point resolution of the comparison through the first filtration** of the
double complex: the target `colim P^•` is the same for both point resolutions, and the
compatibility is the columnwise triangle
`Stacks.ChaoticSite.ModuleValued.mooreBicomplexMap_comp_columnMap`. -/
lemma totalQIsoColimOfResolution_naturality (v : U ⟶ V) (hU : IsPointResolution U)
    (hV : IsPointResolution V) [P.IsStrictlyLE 0] [∀ n, Projective (P.X n)] :
    DerivedCategory.Q.map (HomologicalComplex₂.total.map (mooreBicomplexMap P v)
          (ComplexShape.up ℤ)) ≫
        (totalQIsoColimOfResolution U hU P).hom =
      (totalQIsoColimOfResolution V hV P).hom := by
  have hcolumn := Q_map_total_map_comp_eq (mooreBicomplexMap_comp_columnMap P v)
  have _h1 : QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexColumnTotalMap U P hU
  have _h2 : QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexColumnMap V P)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexColumnTotalMap V P hV
  have _h3 : IsIso (totalSingleRowZeroUnit
      (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) := isIso_totalSingleRowZeroUnit _
  dsimp only [totalQIsoColimOfResolution, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Functor.mapIso_inv]
  rw [← Category.assoc, hcolumn]

/-- **The derived form of [Stacks, Tag 08PT] at module coefficients is natural in the point
resolution.** Let `C` be a small category with the chaotic topology, `B` a ring, `ℱ` a diagram of
`B`-modules on `Cᵒᵖ`, and `ε : P^• ⟶ ℱ[0]` a bounded above resolution of `ℱ` by projective
diagrams. Let `U_•` and `V_•` be point resolutions of `C` and let `v : U_• ⟶ V_•` be a morphism of
cosimplicial objects. Then the triangle

`Q(ℱ(V_•)) ⟶ Q(ℱ(U_•)) ⟶ Lπ_!(ℱ)`

commutes: the comparison of `Stacks.ChaoticSite.ModuleValued`
`.mooreCochainQIsoDerivedColimitOfResolution` at `U_•`, precomposed with the map of extended
Moore complexes induced by `v`, is the comparison at `V_•`.

The last two factors of the comparison — the computation of `Lπ_!` on the K-projective complex
`P^•` and the comparison `Lπ_!(P^•) ≅ Lπ_!(ℱ)` — do not mention the point resolution, so the
statement is the two filtrations of the double complex:
`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoTotal_naturality` and
`Stacks.ChaoticSite.ModuleValued.totalQIsoColimOfResolution_naturality`. -/
theorem mooreCochainQIsoDerivedColimitOfResolution_naturality (v : U ⟶ V)
    (hU : IsPointResolution U) (hV : IsPointResolution V) [P.IsStrictlyLE 0]
    [∀ n, Projective (P.X n)]
    (ε : P ⟶ (HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)
    [QuasiIso ε] :
    DerivedCategory.Q.map ((mooreCochainMap v).app F) ≫
        (mooreCochainQIsoDerivedColimitOfResolution U F hU P ε).hom =
      (mooreCochainQIsoDerivedColimitOfResolution V F hV P ε).hom := by
  have _hKP : P.IsKProjective := CochainComplex.isKProjective_of_projective P 0
  dsimp only [mooreCochainQIsoDerivedColimitOfResolution, Iso.trans_hom]
  rw [← Category.assoc (DerivedCategory.Q.map ((mooreCochainMap v).app F)),
    mooreCochainQIsoTotal_naturality P F v ε, Category.assoc,
    ← Category.assoc (DerivedCategory.Q.map (HomologicalComplex₂.total.map
      (mooreBicomplexMap P v) (ComplexShape.up ℤ))),
    totalQIsoColimOfResolution_naturality P v hU hV]

/-- **The derived form of [Stacks, Tag 08PT] at module coefficients is independent of the point
resolution**, compatibly with morphisms of point resolutions. For a morphism `v : U_• ⟶ V_•` of
cosimplicial objects of `C`, both point resolutions, and a diagram `ℱ` of `B`-modules on `Cᵒᵖ`,
the triangle

`Q(ℱ(V_•)) ⟶ Q(ℱ(U_•)) ⟶ Lπ_!(ℱ)`

commutes, the second arrow being
`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit` at `U_•` and the composite being
the same isomorphism at `V_•`. This is the totalized form of the canonical map of
[Stacks, Tag 08Q6]: the comparison of the extended Moore complex of a point resolution with
derived lower shriek does not depend on the point resolution.

The projective resolution of `ℱ` chosen by
`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit` is built from `ℱ` alone, so one
and the same resolution serves both point resolutions and the statement is
`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimitOfResolution_naturality`. -/
@[stacks 08PT "the derived form at module coefficients is natural in the point resolution: a \
  morphism of cosimplicial objects between two point resolutions carries the comparison at one \
  to the comparison at the other. Still not asserted natural in the coefficient module"]
theorem mooreCochainQIsoDerivedColimit_naturality (v : U ⟶ V) (hU : IsPointResolution U)
    (hV : IsPointResolution V) (F : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    DerivedCategory.Q.map ((mooreCochainMap v).app F) ≫
        (mooreCochainQIsoDerivedColimit U F hU).hom =
      (mooreCochainQIsoDerivedColimit V F hV).hom := by
  let R := (ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)
    inferInstance).choose
  have : ∀ n, Projective (R.complex.X n) := R.projective
  have : CochainComplex.IsStrictlyLE R.complex 0 := R.boundedAbove
  have : QuasiIso R.α := R.quasiIso
  exact mooreCochainQIsoDerivedColimitOfResolution_naturality R.complex F v hU hV R.α

end Stacks.ChaoticSite.ModuleValued

end
