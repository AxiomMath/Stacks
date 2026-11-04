module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import StacksFrontier.Homology.HomComplex.RHom
import StacksCore.Tactic.StacksAttribute

/-!
# Derived functors of the inclusion of abelian sheaves into presheaves

Let `(C, J)` be a small site. The inclusion `sheafToPresheaf J AddCommGrpCat` of abelian
sheaves into abelian presheaves is left exact: this is Mathlib's instance saying that it
preserves finite limits, and it is recorded here as the first half of [Stacks, Tag 03AY].

Its higher right derived functors are the cohomology presheaves. The objectwise half of that
statement is proved here: for an abelian sheaf `G` and `p : ℕ` there is an isomorphism
`((sheafToPresheaf J AddCommGrpCat).rightDerived p).obj G ≅ G.cohomologyPresheaf p`,
obtained by computing the right derived functor on the chosen injective resolution of `G`
(`InjectiveResolution.isoRightDerivedObj`) and then identifying the homology presheaves of the
resulting section complex with the cohomology presheaves. The latter identification is the
bridge `Stacks.Cohomology.Locality.extEquivSectionHomology` of Section 21.7, which already carries
  its
naturality in the object of the site.

The remaining naturality in the sheaf `G` needs the same bridge to be natural in `G`, and this
file supplies the pieces of that argument which do not refer to a morphism of resolutions:
`homComplexPostcomp` and `homologyAddEquiv_postcomp` describe the covariant functoriality of a
Hom complex and its effect on cohomology classes, and the `_naturality` lemmas below record that
each of the four comparison isomorphisms making up
  `Stacks.Cohomology.Locality.extEquivSectionHomology` is
natural in its complex.

## Main definitions

* `homComplexPostcomp`: postcomposition with `g : L ⟶ L'` as a morphism of Hom complexes
  `Hom^•(K, L) ⟶ Hom^•(K, L')`.
* `Stacks.Cohomology.cohomologyPresheafIsoResolution`: the homology presheaves of the section
  complex of an injective resolution of `G` are the cohomology presheaves of `G`.
* `Stacks.Cohomology.rightDerivedObjIsoCohomologyPresheaf`: the value at `G` of the `p`-th right
  derived functor of `sheafToPresheaf` is `G.cohomologyPresheaf p`.

## Main results

* `homologyAddEquiv_postcomp`: `CochainComplex.HomComplex.homologyAddEquiv` turns the map induced
  on homology by `homComplexPostcomp K g` into `cohomologyClassPostcomp K g n`.
* `Stacks.Cohomology.extAddEquivCohomologyClass_naturality_coeff`: composing an `Ext` class with
  `Abelian.Ext.mk₀ f` corresponds to `cohomologyClassPostcomp` along a lift of `f` to injective
  resolutions.
* `Stacks.Cohomology.homComplexSingleIsoCoyoneda_naturality`,
  `Stacks.Cohomology.auxIso_naturality_complex`,
  `Stacks.Cohomology.mapExtendIso_naturality_complex`,
  `Stacks.Cohomology.mapExtendHomologyIso_naturality_complex`,
  `Stacks.Cohomology.homComplexHomologyEquivSectionHomology_naturality_coeff`: naturality in the
  complex of the four comparison isomorphisms of Section 21.7.

## Implementation notes

`homComplexPostcomp` and `homologyAddEquiv_postcomp` are stated in the root namespace, next to
the `cocyclePostcompAddMonoidHom` and `cohomologyClassPostcomp` of
`StacksFrontier.Homology.HomComplex.RHom` that they are about.

`cohomologyPresheafIsoResolution` states its source as
`(HomologicalComplex.homologyFunctor _ _ p).obj (Stacks.Cohomology.Locality.sectionComplex G I)`
  rather than
`(Stacks.Cohomology.Locality.sectionComplex G I).homology p`. The two are definitionally equal, but
  only the
first form is the literal target of `InjectiveResolution.isoRightDerivedObj`, so only it lets the
two isomorphisms be composed without a reducibility override.

## References

* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/-- Postcomposition with `g : L ⟶ L'`, as a morphism of Hom complexes
`Hom^•(K, L) ⟶ Hom^•(K, L')`. Degreewise it is `cocyclePostcompAddMonoidHom`, and on homology it
induces `cohomologyClassPostcomp`. -/
noncomputable def homComplexPostcomp {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) {L L' : CochainComplex A ℤ} (g : L ⟶ L') :
    CochainComplex.HomComplex K L ⟶ CochainComplex.HomComplex K L' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦ z.comp (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero n)
      map_zero' := by cat_disch
      map_add' := by cat_disch }
  comm' i j hij := by
    subst j
    ext z
    exact CochainComplex.HomComplex.δ_comp_ofHom z g (i + 1)

/-- The identification `Hⁿ(Hom^•(K, L)) ≃+ CohomologyClass K L n` of
`CochainComplex.HomComplex.homologyAddEquiv` turns the map induced on homology by
`homComplexPostcomp K g` into `cohomologyClassPostcomp K g n`. -/
theorem homologyAddEquiv_postcomp {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) {L L' : CochainComplex A ℤ} (g : L ⟶ L') (n : ℤ)
    (η : (K.HomComplex L).homology n) :
    cohomologyClassPostcomp K g n (CochainComplex.HomComplex.homologyAddEquiv K L n η) =
      CochainComplex.HomComplex.homologyAddEquiv K L' n
        ((HomologicalComplex.homologyMap (homComplexPostcomp K g) n) η) := by
  have key (M : CochainComplex A ℤ) (w : (K.HomComplex M).cycles n) :
      CochainComplex.HomComplex.homologyAddEquiv K M n ((K.HomComplex M).homologyπ n w) =
        CochainComplex.HomComplex.CohomologyClass.mk
          ((CochainComplex.HomComplex.leftHomologyData K M n).cyclesIso.hom w) :=
    ConcreteCategory.congr_hom
      (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom
        ((K.HomComplex M).sc n) (CochainComplex.HomComplex.leftHomologyData K M n)) w
  have hπ : Function.Surjective (ConcreteCategory.hom ((K.HomComplex L).homologyπ n)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hπ η
  let a : CochainComplex.HomComplex.Cocycle K L n :=
    (CochainComplex.HomComplex.leftHomologyData K L n).cyclesIso.hom z
  have hmap :
      (CochainComplex.HomComplex.leftHomologyData K L' n).cyclesIso.hom
          ((HomologicalComplex.cyclesMap (homComplexPostcomp K g) n) z) =
        a.postcomp g := by
    apply Subtype.ext
    have h1 := ConcreteCategory.congr_hom
      (CochainComplex.HomComplex.leftHomologyData K L' n).cyclesIso_hom_comp_i
      ((HomologicalComplex.cyclesMap (homComplexPostcomp K g) n) z)
    have h2 := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (homComplexPostcomp K g) n) z
    have h3 := ConcreteCategory.congr_hom
      (CochainComplex.HomComplex.leftHomologyData K L n).cyclesIso_hom_comp_i z
    simp only [ConcreteCategory.comp_apply] at h1 h2 h3
    refine h1.trans ?_
    refine h2.trans ?_
    show ((HomologicalComplex.iCycles (K.HomComplex L) n) z).comp _ (add_zero n) =
      a.1.comp _ (add_zero n)
    congr 1
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (homComplexPostcomp K g) n) z
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat, key L z, key L', hmap]
  exact cohomologyClassPostcomp_mk K g n a

namespace Stacks.Cohomology

add_to_stacks 03AY "left exact"
  CategoryTheory.Sheaf.instPreservesFiniteLimitsFunctorOppositeSheafToPresheafOfHasFiniteLimits
add_to_sga "3 IV 4.4.1" "(i)"
  CategoryTheory.Sheaf.instPreservesFiniteLimitsFunctorOppositeSheafToPresheafOfHasFiniteLimits
add_to_sga "4 II 4.1" "special case"
  CategoryTheory.Sheaf.instPreservesFiniteLimitsFunctorOppositeSheafToPresheafOfHasFiniteLimits

section Resolution

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Compatibility of `InjectiveResolution.extAddEquivCohomologyClass` with composition with
`Abelian.Ext.mk₀ f`: postcomposing an `Ext` class with `f` corresponds, on cohomology classes of
the Hom complex, to `cohomologyClassPostcomp` along a lift `φ` of `f` to the resolutions. -/
theorem extAddEquivCohomologyClass_naturality_coeff
    [HasExt.{v} A] {G H : A} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f)
    (p : ℕ) (X : A) (ξ : Abelian.Ext X G p) :
    I'.extAddEquivCohomologyClass (ξ.comp (Abelian.Ext.mk₀ f) (add_zero p)) =
      cohomologyClassPostcomp ((CochainComplex.singleFunctor _ 0).obj X) φ.hom' p
        (I.extAddEquivCohomologyClass ξ) := by
  obtain ⟨z, hz, hξ⟩ := I.extMk_surjective ξ (p + 1) rfl
  rw [← hξ, I.extMk_comp_mk₀ z (p + 1) rfl hz φ]
  simp only [InjectiveResolution.extAddEquivCohomologyClass_apply,
    InjectiveResolution.extEquivCohomologyClass_extMk, cohomologyClassPostcomp_mk]
  simp only [← CochainComplex.HomComplex.Cocycle.fromSingleMk_postcomp]
  have hmap : (z ≫ φ.hom.f p) ≫ (I'.cochainComplexXIso (p : ℤ) p (by simp)).inv =
      (z ≫ (I.cochainComplexXIso (p : ℤ) p (by simp)).inv) ≫ φ.hom'.f (p : ℤ) := by
    simp [φ.hom'_f p p rfl]
  congr 1
  ext : 1
  exact (CochainComplex.HomComplex.Cochain.fromSingleEquiv
    (by ring : (0 : ℤ) + (p : ℤ) = (p : ℤ))).injective (by simpa using hmap)

/-- `Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda` is natural in its cochain complex: it
  intertwines
`homComplexPostcomp` with the degreewise action of `Hom(X, -)`. -/
theorem homComplexSingleIsoCoyoneda_naturality (X : A)
    {K L : CochainComplex A ℤ} (g : K ⟶ L) :
    homComplexPostcomp ((CochainComplex.singleFunctor A 0).obj X) g ≫
      (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda X L).hom =
    (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda X K).hom ≫
      ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g := by
  ext n α
  obtain ⟨z, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective α n (by ring)
  simp only [Functor.mapHomologicalComplex_obj_X, HomologicalComplex.comp_f,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Functor.mapHomologicalComplex_map_f]
  show (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by ring : (0 : ℤ) + n = n))
      ((CochainComplex.HomComplex.Cochain.fromSingleMk z (by ring : (0 : ℤ) + n = n)).comp
        (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero n)) =
    (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by ring : (0 : ℤ) + n = n))
      (CochainComplex.HomComplex.Cochain.fromSingleMk z (by ring : (0 : ℤ) + n = n)) ≫ g.f n
  rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp]
  simp

end Resolution

section Extend

variable {A B : Type u} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]

/-- `Stacks.Cohomology.Locality.auxIso` is natural in its complex: the degreewise comparison
  between `F`
applied to an `Option`-indexed extension and the extension of `F` applied to the complex commutes
with the maps induced by `g : K ⟶ L`. -/
theorem auxIso_naturality_complex (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex A ℕ} (g : K ⟶ L) (i : Option ℕ) :
    F.map (HomologicalComplex.extend.mapX g i) ≫ (Stacks.Cohomology.Locality.auxIso F L i).hom =
    (Stacks.Cohomology.Locality.auxIso F K i).hom ≫
      HomologicalComplex.extend.mapX
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) i := by
  cases i with
  | none =>
      exact (HomologicalComplex.extend.isZero_X
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) rfl).eq_of_tgt _ _
  | some a =>
      dsimp only [HomologicalComplex.extend.mapX, HomologicalComplex.extend.X,
        Stacks.Cohomology.Locality.auxIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        HomologicalComplex.extend.XIso, Functor.mapHomologicalComplex_obj_X,
        Functor.mapHomologicalComplex_map_f]
      generalize_proofs
      simp

/-- `Stacks.Cohomology.Locality.mapExtendIso` is natural in its complex. -/
theorem mapExtendIso_naturality_complex (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex A ℕ} (g : K ⟶ L) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)) ≫
      (Stacks.Cohomology.Locality.mapExtendIso F L).hom =
    (Stacks.Cohomology.Locality.mapExtendIso F K).hom ≫
      HomologicalComplex.extendMap
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)
        ComplexShape.embeddingUpNat := by
  ext i'
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [Stacks.Cohomology.Locality.mapExtendIso, Functor.mapHomologicalComplex_map_f]
  exact auxIso_naturality_complex F g (ComplexShape.embeddingUpNat.r i')

/-- `Stacks.Cohomology.Locality.mapExtendHomologyIso` is natural in its complex. -/
theorem mapExtendHomologyIso_naturality_complex (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex A ℕ} (g : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)) (n : ℤ) ≫
      (Stacks.Cohomology.Locality.mapExtendHomologyIso F L n).hom =
    (Stacks.Cohomology.Locality.mapExtendHomologyIso F K n).hom ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) n := by
  have hj : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl
  have key : ∀ X : CochainComplex A ℕ,
      (Stacks.Cohomology.Locality.mapExtendHomologyIso F X n).hom =
        HomologicalComplex.homologyMap (Stacks.Cohomology.Locality.mapExtendIso F X).hom (n : ℤ) ≫
          (HomologicalComplex.extendHomologyIso
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj X)
            ComplexShape.embeddingUpNat hj).hom := fun _ => rfl
  rw [key L, key K]
  have h : HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)) (n : ℤ) ≫
      HomologicalComplex.homologyMap (Stacks.Cohomology.Locality.mapExtendIso F L).hom (n : ℤ) =
      HomologicalComplex.homologyMap (Stacks.Cohomology.Locality.mapExtendIso F K).hom (n : ℤ) ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)
          ComplexShape.embeddingUpNat) (n : ℤ) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      mapExtendIso_naturality_complex F g]
  rw [← Category.assoc, h, Category.assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality, Category.assoc]

end Extend

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]

attribute [local instance 10000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- The homology presheaves of the section complex of an injective resolution `I` of an abelian
sheaf `G` are the cohomology presheaves of `G`. -/
noncomputable def cohomologyPresheafIsoResolution
    (G : Sheaf J AddCommGrpCat.{u}) (I : InjectiveResolution G) (p : ℕ) :
    (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℕ) p).obj
        (Stacks.Cohomology.Locality.sectionComplex G I) ≅ G.cohomologyPresheaf p := by
  refine (NatIso.ofComponents (fun ⟨U⟩ ↦
    (Stacks.Cohomology.Locality.extEquivSectionHomology G I p U).toAddCommGrpIso) ?_).symm
  rintro ⟨U⟩ ⟨V⟩ f
  ext ξ
  exact Stacks.Cohomology.Locality.extEquivSectionHomology_naturality G I p f.unop ξ

/-- **Stacks 03AY, objectwise.** The value at an abelian sheaf `G` of the `p`-th right derived
functor of the inclusion of abelian sheaves into abelian presheaves is the `p`-th cohomology
presheaf of `G`. -/
@[sga "4 IV 4.8" "for an abelian sheaf G", sga "4 V 2.4.2" "special case"]
noncomputable def rightDerivedObjIsoCohomologyPresheaf
    (G : Sheaf J AddCommGrpCat.{u}) (p : ℕ) :
    ((sheafToPresheaf J (AddCommGrpCat.{u})).rightDerived p).obj G ≅
      G.cohomologyPresheaf p :=
  let I := injectiveResolution G
  I.isoRightDerivedObj (sheafToPresheaf J (AddCommGrpCat.{u})) p ≪≫
    cohomologyPresheafIsoResolution J G I p

/-- `Stacks.Cohomology.Locality.homComplexHomologyEquivSectionHomology` is natural in the sheaf: it
intertwines the map induced on Hom-complex homology by a lift `φ` of `f : G ⟶ H` with the map
induced on the homology of the section complexes, evaluated at `U`. -/
theorem homComplexHomologyEquivSectionHomology_naturality_coeff
    {G H : Sheaf J AddCommGrpCat.{u}} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f)
    (p : ℕ) (U : C) (η : (Stacks.Cohomology.Locality.homComplex G I U).homology p) :
    Stacks.Cohomology.Locality.homComplexHomologyEquivSectionHomology H I' p U
        ((HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (Opposite.op
            (Stacks.Cohomology.Locality.freeYonedaSheaf (J := J) U))).mapHomologicalComplex
              (ComplexShape.up ℕ)).map φ.hom) p) η) =
      ((HomologicalComplex.homologyMap
        (((sheafToPresheaf J AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ.hom) p).app (Opposite.op U))
        (Stacks.Cohomology.Locality.homComplexHomologyEquivSectionHomology G I p U η) := by
  let S := sheafToPresheaf J AddCommGrpCat
  let e := Stacks.Cohomology.Locality.eFun (J := J) U
  let E := (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)
  have hn := (NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).hom.naturality φ.hom
  have hn' := congrArg
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).map) hn
  simp only [HomologicalComplex.homologyFunctor_map] at hn'
  simp only [HomologicalComplex.homologyMap_comp] at hn'
  have hm' :
      (HomologicalComplex.homologyMap
        (((S ⋙ E).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) p) ≫
        (ShortComplex.mapHomologyIso ((Stacks.Cohomology.Locality.sectionComplex H I').sc p) E).hom
          =
      (ShortComplex.mapHomologyIso ((Stacks.Cohomology.Locality.sectionComplex G I).sc p) E).hom ≫
        ((HomologicalComplex.homologyMap
          ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) p).app (Opposite.op U)) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u})
        (ComplexShape.up ℕ) p).map ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)) E
  exact (congrArg
      (fun x ↦ (ConcreteCategory.hom
        (ShortComplex.mapHomologyIso ((Stacks.Cohomology.Locality.sectionComplex H I').sc p) E).hom)
          x)
      (ConcreteCategory.congr_hom hn' η)).trans
    (ConcreteCategory.congr_hom hm'
      ((ConcreteCategory.hom (HomologicalComplex.homologyMap
        ((NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).hom.app I.cocomplex) p)) η))

end Stacks.Cohomology
