module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.CanonicalDerivedLowerShriekMapOnResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.ConstantRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.LowerShriekAsAColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExplicitChainMapOnHomology
public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Sites.Continuous

/-!
# Stacks 08PH: the canonical maps of Remark 08PD on the homology of a category

Let `f : C' ⥤ C` be a functor between small categories. Give both categories their chaotic
topologies and the one-object category `*` the ring `B`; the unique functors to `*` and `f` make
this an instance of Situation 08PA (`Stacks.ChaoticSite.functorSituation`), with morphisms of
topoi `π : Sh(C) ⟶ Sh(*)`, `π' : Sh(C') ⟶ Sh(*)` and `g : Sh(C') ⟶ Sh(C)`. For `F` in `Ab(C)`,
`F'` in `Ab(C')` and `t : F' ⟶ g⁻¹F`, Remark 08PD gives a canonical map `Lπ'_!F' ⟶ Lπ_!F`. Stacks
08PH asserts that, on `H_n(C', F') = L_nπ'_!F'` and `H_n(C, F) = L_nπ_!F`, this map comes from the
chain map `K_•(F') ⟶ K_•(F)` of simplicial replacements. This file proves it.

## The argument

`H_n(C, F)` is `L_n colim F`, computed by the colimit of a projective resolution `P_•` of `F`.
On the chaotic site sheaves are presheaves, and `π_!` read on sections over the point is
`colim` (`Stacks.ChaoticSite.colimitLowerShriekIso`); so `L_nπ_!F`, read on sections over the point,
is the homology of `colim P_•` (`Stacks.ChaoticSite.totalHomologyIso`). The canonical map of
Remark 08PD is computed on the resolutions by
`Stacks.Sites.FibredCategory.MorphismSituation.canonicalDerivedLowerShriekMap_comp_eq`, for the lift
of `t` to the resolutions (`Stacks.ChaoticSite.sheafLift`). In degree zero the resulting map of
complexes is `colim` of the lift followed by the comparison of colimits along `f`
(`Stacks.ChaoticSite.colimitLowerShriekComplexIso_hom_resolutionLowerShriekMap`), which is the
chain map defining `Stacks.CategoryHomology.categoryHomologyMap`
(`Stacks.CategoryHomology.homologyMapAux_eq_resolutionHomologyIso`). Stacks 08PH's comparison
with `K_•` is then `Stacks.CategoryHomology.replacementChainMap_homologyMap`.

## Main definitions

* `Stacks.ChaoticSite.totalHomologyIso`, `Stacks.ChaoticSite.sourceHomologyIso`: the
  identifications `H_n(C, F) = L_nπ_!F` and `H_n(C', F') = L_nπ'_!F'`, read on sections over the
  point.

## Main results

* `Stacks.ChaoticSite.map_homologyFunctor_map_canonicalDerivedLowerShriekMap'`: under these
  identifications `H^{-n}` of the canonical map of Remark 08PD is
  `Stacks.CategoryHomology.categoryHomologyMap`.
* `Stacks.ChaoticSite.map_homologyFunctor_map_canonicalDerivedLowerShriekMap'_eq_homologyMap`:
  **Stacks 08PH**, the same map is induced by the chain map `K_•(F') ⟶ K_•(F)`.

## References

* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
* [Stacks Project, Tag 08PD](https://stacks.math.columbia.edu/tag/08PD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryHomology

universe w v u u' w'

open HomologicalComplex Stacks.Homology.DerivedLeftAdjointComp

section CochainResolutions

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C']
  [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' w})]
  [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w})]

/-- The homology of a small category, read on the cochain complex indexed by `ℤ` of the chosen
projective resolution: `H_n(C, F)` is the homology in degree `-n` of the colimit of that
complex. -/
def resolutionHomologyIso {D : Type v} [SmallCategory D]
    [HasColimitsOfShape Dᵒᵖ AddCommGrpCat.{w'}]
    [EnoughProjectives (Dᵒᵖ ⥤ AddCommGrpCat.{w'})]
    (F : Dᵒᵖ ⥤ AddCommGrpCat.{w'}) (n : ℕ) :
    ((colim : (Dᵒᵖ ⥤ AddCommGrpCat.{w'}) ⥤ _).leftDerived n).obj F ≅
      (((colim : (Dᵒᵖ ⥤ AddCommGrpCat.{w'}) ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (ProjectiveResolution.of F).cochainComplex).homology (-(n : ℤ)) :=
  (ProjectiveResolution.of F).isoLeftDerivedObj colim n ≪≫
    ((((colim : (Dᵒᵖ ⥤ AddCommGrpCat.{w'}) ⥤ _).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (ProjectiveResolution.of F).complex).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)).symm ≪≫
    homologyMapIso (mapHomologicalComplexExtendIso colim (ProjectiveResolution.of F).complex
      ComplexShape.embeddingDownNat) (-(n : ℤ))

omit [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' w})]
  [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w})] in
/-- Extending along `ℕ ⊆ ℤ` commutes with the comparison `colim_{C'ᵒᵖ} ∘ f⁻¹ ⟶ colim_{Cᵒᵖ}`. -/
theorem extendMap_colimitRestrictionPreComplex (f : C' ⥤ C)
    {X' : ChainComplex (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ℕ}
    {X : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ℕ}
    (ψ : X' ⟶ ((presheafRestriction.{u, u', w} f).mapHomologicalComplex _).obj X) :
    extendMap (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ⥤ _).mapHomologicalComplex _).map ψ ≫
        colimitRestrictionPreComplex.{u, u', w} f X) ComplexShape.embeddingDownNat =
      (mapHomologicalComplexExtendIso colim X' ComplexShape.embeddingDownNat).hom ≫
        ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ⥤ _).mapHomologicalComplex _).map
          (extendMap ψ ComplexShape.embeddingDownNat ≫
            (mapHomologicalComplexExtendIso (presheafRestriction.{u, u', w} f) X
              ComplexShape.embeddingDownNat).hom) ≫
        (NatTrans.mapHomologicalComplex (colimitRestrictionPre.{u, u', w} f)
          (ComplexShape.up ℤ)).app (X.extend ComplexShape.embeddingDownNat) ≫
        (mapHomologicalComplexExtendIso colim X ComplexShape.embeddingDownNat).inv := by
  rw [← Category.assoc, ← Category.assoc, Iso.eq_comp_inv]
  refine HomologicalComplex.hom_ext _ _ fun i' => ?_
  by_cases h : ∃ a, ComplexShape.embeddingDownNat.f a = i'
  · obtain ⟨a, rfl⟩ := h
    simp only [comp_f, extendMap_f _ _ rfl, mapHomologicalComplexExtendIso_hom_f _ _ _ rfl,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
      colimitRestrictionPre_app, Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc, Functor.map_comp, Category.assoc]
    congr 1
    exact (colimit.pre_map (extendXIso X ComplexShape.embeddingDownNat _).inv f.op)
  · simp only [not_exists] at h
    exact (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ⥤ _).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj X').isZero_extend_X ComplexShape.embeddingDownNat i' h
      |>.eq_of_src _ _

omit [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' w})]
  [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w})] in
/-- The homology of `colim(ψ)` followed by the comparison of colimits, read on the extensions of
the two complexes to `ℤ`. -/
theorem homologyMap_colimitRestrictionPreComplex_eq_extend (f : C' ⥤ C)
    {X' : ChainComplex (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ℕ}
    {X : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ℕ}
    (ψ : X' ⟶ ((presheafRestriction.{u, u', w} f).mapHomologicalComplex _).obj X) (n : ℕ) :
    homologyMap (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ⥤ _).mapHomologicalComplex _).map ψ ≫
        colimitRestrictionPreComplex.{u, u', w} f X) n =
      (((colim.mapHomologicalComplex (ComplexShape.down ℕ)).obj X').extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).inv ≫
        homologyMap (mapHomologicalComplexExtendIso colim X' ComplexShape.embeddingDownNat).hom
          (-(n : ℤ)) ≫
        homologyMap (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (extendMap ψ ComplexShape.embeddingDownNat ≫
              (mapHomologicalComplexExtendIso (presheafRestriction.{u, u', w} f) X
                ComplexShape.embeddingDownNat).hom) ≫
          (NatTrans.mapHomologicalComplex (colimitRestrictionPre.{u, u', w} f)
            (ComplexShape.up ℤ)).app (X.extend ComplexShape.embeddingDownNat)) (-(n : ℤ)) ≫
        homologyMap (mapHomologicalComplexExtendIso colim X ComplexShape.embeddingDownNat).inv
          (-(n : ℤ)) ≫
        (((colim.mapHomologicalComplex (ComplexShape.down ℕ)).obj X).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom := by
  have hext : ((mapHomologicalComplexExtendIso colim X' ComplexShape.embeddingDownNat).hom ≫
      (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (extendMap ψ ComplexShape.embeddingDownNat ≫
              (mapHomologicalComplexExtendIso (presheafRestriction.{u, u', w} f) X
                ComplexShape.embeddingDownNat).hom) ≫
          (NatTrans.mapHomologicalComplex (colimitRestrictionPre.{u, u', w} f)
            (ComplexShape.up ℤ)).app (X.extend ComplexShape.embeddingDownNat))) ≫
        (mapHomologicalComplexExtendIso colim X ComplexShape.embeddingDownNat).inv =
      extendMap (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ⥤ _).mapHomologicalComplex _).map ψ ≫
        colimitRestrictionPreComplex.{u, u', w} f X) ComplexShape.embeddingDownNat := by
    rw [extendMap_colimitRestrictionPreComplex.{w} f ψ]
    simp only [Category.assoc]
  rw [← homologyMap_comp_assoc, ← homologyMap_comp_assoc, hext, extendHomologyIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- **The canonical map on homology, read on the cochain complexes of the resolutions.** -/
theorem homologyMapAux_eq_resolutionHomologyIso (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' w}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}}
    (t : F' ⟶ f.op ⋙ F) (n : ℕ)
    (ψ : (ProjectiveResolution.of F').complex ⟶
      ((presheafRestriction.{u, u', w} f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (ProjectiveResolution.of F).complex)
    (hψ : ψ ≫ (presheafRestriction.{u, u', w} f).mapAugmentation (ProjectiveResolution.of F).π =
      (ProjectiveResolution.of F').π ≫ (ChainComplex.single₀ _).map t) :
    homologyMapAux.{u, u', w} f t n =
      (resolutionHomologyIso F' n).hom ≫
        homologyMap (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' w}) ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (extendLift (presheafRestriction.{u, u', w} f)
              (ProjectiveResolution.of F') (ProjectiveResolution.of F) ψ) ≫
          (NatTrans.mapHomologicalComplex (colimitRestrictionPre.{u, u', w} f)
            (ComplexShape.up ℤ)).app (ProjectiveResolution.of F).cochainComplex) (-(n : ℤ)) ≫
        (resolutionHomologyIso F n).inv := by
  rw [homologyMapAux_eq f t n ψ hψ]
  change _ ≫ homologyMap _ n ≫ _ = _
  rw [homologyMap_colimitRestrictionPreComplex_eq_extend.{w} f ψ n]
  simp only [resolutionHomologyIso, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rfl

end CochainResolutions

/-- `Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso` is natural in the
complex. -/
theorem mapHomologicalComplexHomologyIso_hom_naturality {C₁ C₂ : Type*} [Category* C₁]
    [Category* C₂] [Abelian C₁] [Abelian C₂] (F : C₁ ⥤ C₂) [F.Additive] [F.PreservesHomology]
    {K L : CochainComplex C₁ ℤ} (φ : K ⟶ L) (q : ℤ) :
    homologyMap ((F.mapHomologicalComplex _).map φ) q ≫
        (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso F L q).hom =
      (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso F K q).hom ≫
        F.map (homologyMap φ q) :=
  ShortComplex.mapHomologyIso_hom_naturality ((shortComplexFunctor C₁ _ q).map φ) F

end Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe w v u u'

section SheavesOfEqTrivial

variable {D : Type*} [Category* D] {J : GrothendieckTopology D}
  (hJ : J = GrothendieckTopology.trivial D) (A : Type*) [Category* A]

include hJ in
/-- Every presheaf is a sheaf for a topology which is the chaotic one. -/
theorem isSheaf_of_eq_trivial (P : Dᵒᵖ ⥤ A) : Presheaf.IsSheaf J P := by
  subst hJ
  rw [GrothendieckTopology.trivial_eq_bot]
  exact Presheaf.isSheaf_bot P

/-- Sheaves for a topology which is the chaotic one are presheaves. -/
def sheafEquivOfEqTrivial : Sheaf J A ≌ (Dᵒᵖ ⥤ A) where
  functor := sheafToPresheaf J A
  inverse :=
    { obj := fun P => ⟨P, isSheaf_of_eq_trivial hJ A P⟩
      map := fun f => ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Reading a presheaf as a sheaf is additive. -/
instance [Preadditive A] : (sheafEquivOfEqTrivial hJ A).inverse.Additive where
  map_add := rfl

/-- The functor of `sheafEquivOfEqTrivial` is the underlying presheaf. -/
@[simp]
lemma sheafEquivOfEqTrivial_functor :
    (sheafEquivOfEqTrivial hJ A).functor = sheafToPresheaf J A :=
  rfl

/-- The presheaf underlying a presheaf read as a sheaf is the presheaf. -/
@[simp]
lemma sheafEquivOfEqTrivial_inverse_obj_obj (P : Dᵒᵖ ⥤ A) :
    ((sheafEquivOfEqTrivial hJ A).inverse.obj P).obj = P :=
  rfl

/-- The map of presheaves underlying a map read between sheaves is the map. -/
@[simp]
lemma sheafEquivOfEqTrivial_inverse_map_hom {P Q : Dᵒᵖ ⥤ A} (g : P ⟶ Q) :
    ((sheafEquivOfEqTrivial hJ A).inverse.map g).hom = g :=
  rfl

/-- The unit of `sheafEquivOfEqTrivial` is the identity on underlying presheaves. -/
@[simp]
lemma sheafEquivOfEqTrivial_unit_app_hom (X : Sheaf J A) :
    ((sheafEquivOfEqTrivial hJ A).unit.app X).hom = 𝟙 X.obj :=
  rfl

end SheavesOfEqTrivial

section LowerShriekToThePoint

variable {D : Type*} [Category* D] {J : GrothendieckTopology D}
  (hJ : J = GrothendieckTopology.trivial D) (A : Type*) [Category* A] [HasColimitsOfShape Dᵒᵖ A]
  {K : GrothendieckTopology (Discrete PUnit.{v + 1})}
  (hK : K = GrothendieckTopology.trivial (Discrete PUnit.{v + 1}))

/-- Sheaves on the chaotic one-object site are objects of the coefficient category, through their
sections over the unique object. -/
abbrev pointSheafEquiv :
    Sheaf K A ≌ A :=
  (sheafEquivOfEqTrivial hK A).trans
    (pointConstEquiv.{v} A).symm

/-- The constant sheaf on the point of a map has that map as its components. -/
@[simp]
lemma pointSheafEquiv_inverse_map_hom_app {M N : A} (g : M ⟶ N)
    (x : (Discrete PUnit.{v + 1})ᵒᵖ) : ((pointSheafEquiv.{v} A hK).inverse.map g).hom.app x = g :=
  rfl

/-- The unit of `pointSheafEquiv` is the identity on sections. -/
@[simp]
lemma pointSheafEquiv_unit_app_hom_app
    (Y : Sheaf (K) A)
    (x : (Discrete PUnit.{v + 1})ᵒᵖ) :
    ((pointSheafEquiv.{v} A hK).unit.app Y).hom.app x = 𝟙 _ := by
  obtain ⟨⟨⟨⟩⟩⟩ := x
  simp [pointSheafEquiv, Equivalence.unit, pointConstEquiv, pointConstIso, sheafEquivOfEqTrivial]

variable (q : D ⥤ Discrete PUnit.{v + 1})
  [hq : q.IsContinuous J (K)]

/-- Restricting the sheaf of a constant object along the unique functor to the point is the
constant presheaf. -/
def constRestrictionIso :
    Functor.const Dᵒᵖ ⋙ (sheafEquivOfEqTrivial hJ A).inverse ≅
      (pointSheafEquiv.{v} A hK).inverse ⋙
        q.sheafPushforwardContinuous A J (K) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

omit [HasColimitsOfShape Dᵒᵖ A] in
/-- The components of `constRestrictionIso` are identities. -/
@[simp]
lemma constRestrictionIso_hom_app_hom (M : A) :
    ((constRestrictionIso hJ A hK q).hom.app M).hom = 𝟙 _ :=
  rfl

variable {L : Sheaf J A ⥤ Sheaf (K) A}
  (adj : L ⊣ q.sheafPushforwardContinuous A J (K))

/-- **Lower shriek to the chaotic point is the colimit**, read on sections over the point: the
colimit of the underlying presheaf is the sections of `π_!` over the unique object. -/
def colimitLowerShriekIso :
    (sheafEquivOfEqTrivial hJ A).functor ⋙ colim ≅ L ⋙ (pointSheafEquiv.{v} A hK).functor :=
  Adjunction.leftAdjointUniq
    (((sheafEquivOfEqTrivial hJ A).toAdjunction.comp colimConstAdj).ofNatIsoRight
      (constRestrictionIso hJ A hK q))
    (adj.comp (pointSheafEquiv.{v} A hK).toAdjunction)

/-- The coprojections of the colimit are the unit of `π_! ⊣ π⁻¹`. -/
theorem ι_colimitLowerShriekIso_hom (X : Sheaf J A) (c : Dᵒᵖ) :
    colimit.ι X.obj c ≫ (colimitLowerShriekIso hJ A hK q adj).hom.app X =
      (adj.unit.app X).hom.app c := by
  have hu : (((sheafEquivOfEqTrivial hJ A).toAdjunction.comp colimConstAdj).ofNatIsoRight
      (constRestrictionIso hJ A hK q)).unit.app X =
      ((sheafEquivOfEqTrivial hJ A).toAdjunction.comp colimConstAdj).unit.app X ≫
        (constRestrictionIso hJ A hK q).hom.app _ := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((sheafEquivOfEqTrivial hJ A).toAdjunction.comp colimConstAdj).ofNatIsoRight
      (constRestrictionIso hJ A hK q))
    (adj.comp (pointSheafEquiv.{v} A hK).toAdjunction) X
  rw [hu, Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  have h' := congrArg (fun g => g.hom.app c) h
  simp only [Functor.id_obj, Functor.comp_obj, sheafEquivOfEqTrivial_functor,
    ObjectProperty.ι_obj, colim_obj, Equivalence.toAdjunction_unit, Category.assoc,
    Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
    sheafEquivOfEqTrivial_inverse_obj_obj, sheafEquivOfEqTrivial_unit_app_hom,
    sheafEquivOfEqTrivial_inverse_map_hom, constRestrictionIso_hom_app_hom, Category.id_comp,
    NatTrans.comp_app, Functor.const_obj_obj, Functor.sheafPushforwardContinuous_map_hom_app,
    pointSheafEquiv_unit_app_hom_app] at h'
  have hid : ∀ {P Q : Dᵒᵖ ⥤ A} (g : P ⟶ Q) (x : Dᵒᵖ), (𝟙 P ≫ g).app x = g.app x :=
    fun g x => congrArg (fun k => NatTrans.app k x) (Category.id_comp g)
  exact ((congrArg (_ ≫ ·) (hid _ c)).symm.trans h').trans (Category.comp_id _)

variable [Preadditive A] [Preadditive (Sheaf J A)] [Preadditive (Sheaf K A)]
  [hL : L.PreservesZeroMorphisms]
  [(colim : (Dᵒᵖ ⥤ A) ⥤ A).PreservesZeroMorphisms]
  [(pointSheafEquiv.{v} A hK).functor.PreservesZeroMorphisms]

/-- `colimitLowerShriekIso` applied degreewise to a cochain complex of sheaves. -/
def colimitLowerShriekComplexIso (K : CochainComplex (Sheaf J A) ℤ) :
    ((colim : (Dᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((sheafEquivOfEqTrivial hJ A).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((pointSheafEquiv.{v} A hK).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (colimitLowerShriekIso hJ A hK q adj).app (K.X i))
    (fun _ _ _ => ((colimitLowerShriekIso hJ A hK q adj).hom.naturality _).symm)

end LowerShriekToThePoint

section DegreeZero

variable {D : Type*} [Category* D] {J : GrothendieckTopology D}
  (hJ : J = GrothendieckTopology.trivial D) {D' : Type*} [Category* D']
  {J' : GrothendieckTopology D'} (hJ' : J' = GrothendieckTopology.trivial D')
  (A : Type*) [Category* A] [HasColimitsOfShape Dᵒᵖ A] [HasColimitsOfShape D'ᵒᵖ A]
  {K : GrothendieckTopology (Discrete PUnit.{v + 1})}
  (hK : K = GrothendieckTopology.trivial (Discrete PUnit.{v + 1}))
  (q : D ⥤ Discrete PUnit.{v + 1}) (f : D' ⥤ D)
  [hq : q.IsContinuous J K] [hq' : (f ⋙ q).IsContinuous J' K]
  [hf : f.IsContinuous J' J]
  {L : Sheaf J A ⥤ Sheaf (K) A}
  (adj : L ⊣ q.sheafPushforwardContinuous A J (K))
  {L' : Sheaf J' A ⥤ Sheaf (K) A}
  (adj' : L' ⊣ (f ⋙ q).sheafPushforwardContinuous A J'
    (K))
  {G : Sheaf J' A ⥤ Sheaf J A} (adjG : G ⊣ f.sheafPushforwardContinuous A J' J)
  (e : q.sheafPushforwardContinuous A J (K) ⋙
      f.sheafPushforwardContinuous A J' J ≅
    (f ⋙ q).sheafPushforwardContinuous A J' (K))

omit [HasColimitsOfShape Dᵒᵖ A] [HasColimitsOfShape D'ᵒᵖ A] in
/-- The comparison of restrictions along `f ⋙ q` attached to a proof of `f ⋙ q = f ⋙ q` is the
identity on sections. -/
theorem sheafPushforwardContinuousComp'_eqToIso_hom_app_hom (h : f ⋙ q = f ⋙ q) (Y : Sheaf K A) :
    ((Functor.sheafPushforwardContinuousComp' (eqToIso h) A J' J K).hom.app Y).hom = 𝟙 _ := by
  ext c
  simp
  rfl

include hJ hJ' hK in
/-- **The canonical map in degree zero is `colim(φ)` followed by the comparison of colimits.**
For `φ : F' ⟶ g⁻¹F`, the map `π'_!F' ⟶ π_!g_!F' ⟶ π_!F` attached to the adjoint of `φ`, read on
sections over the point, is the map of colimits
`colim_{D'ᵒᵖ} F' ⟶ colim_{D'ᵒᵖ} f⁻¹F ⟶ colim_{Dᵒᵖ} F`. -/
theorem colimitLowerShriekIso_hom_app_comp
    (he : ∀ Y, (e.hom.app Y).hom = 𝟙 _)
    (X' : Sheaf J' A) (X : Sheaf J A) (φ : X' ⟶ (f.sheafPushforwardContinuous A J' J).obj X) :
    (colimitLowerShriekIso hJ' A hK (f ⋙ q) adj').hom.app X' ≫
        (pointSheafEquiv.{v} A hK).functor.map
          ((Adjunction.leftAdjointCompIso adjG adj adj' e).inv.app X' ≫
            L.map (G.map φ ≫ adjG.counit.app X)) =
      colim.map (φ.hom : X'.obj ⟶ f.op ⋙ X.obj) ≫ colimit.pre X.obj f.op ≫
        (colimitLowerShriekIso hJ A hK q adj).hom.app X := by
  apply colimit.hom_ext
  intro c
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (ι_colimitLowerShriekIso_hom hJ' A hK (f ⋙ q) adj' X' c))).trans ?_
  refine Eq.trans ?_ ((colimit.ι_map_assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (colimit.ι_pre_assoc _ _ _ _)).trans (congrArg (_ ≫ ·)
      (ι_colimitLowerShriekIso_hom hJ A hK q adj X _)))).symm
  have key := congrArg (fun g => g.hom.app c)
    (Adjunction.homEquiv_leftAdjointCompIso_inv_app_comp adjG adj adj' e
      ((adjG.homEquiv _ _).symm φ))
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at key
  simp [he] at key
  have key' := key.trans (congrArg (fun g => φ.hom.app c ≫ NatTrans.app g c)
    (Category.comp_id _))
  simp only [Functor.map_comp]
  exact key'

end DegreeZero


section Situation

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
  (B : CommRingCat.{max w u u'})

/-- `π_! = colim` on sections over the point, for the target of the situation attached to `f`. -/
abbrev totalColimitLowerShriekIso :=
  colimitLowerShriekIso (functorSituation_totalTopology.{w} C C' f B) AddCommGrpCat.{max w u u'}
    (K := (functorSituation.{w} C C' f B).base.J) rfl (functorSituation.{w} C C' f B).p
    (hq := (functorSituation.{w} C C' f B).pContinuous)
    (functorSituation.{w} C C' f B).totalAbelianLowerShriekAdjunction

/-- The source projection `p' = f ⋙ p` is continuous. -/
instance comp_p_isContinuous : ((functorSituation.{w} C C' f B).u ⋙ (functorSituation.{w} C C' f
    B).p).IsContinuous
    (functorSituation.{w} C C' f B).sourceTopology (functorSituation.{w} C C' f B).base.J :=
  (functorSituation.{w} C C' f B).p'Continuous

/-- The adjunction `π'_! ⊣ (π')⁻¹` of the source, with `p' = f ⋙ p` written out. -/
abbrev sourceAdjunction :
    (functorSituation.{w} C C' f B).sourceAbelianLowerShriek ⊣
      ((functorSituation.{w} C C' f B).u ⋙ (functorSituation.{w} C C' f
          B).p).sheafPushforwardContinuous AddCommGrpCat.{max w u u'}
        (functorSituation.{w} C C' f B).sourceTopology (functorSituation.{w} C C' f B).base.J :=
  (functorSituation.{w} C C' f B).sourceAbelianLowerShriekAdjunction

/-- The factorization `(π')⁻¹ = g⁻¹ ∘ π⁻¹`, with `p' = f ⋙ p` written out. -/
abbrev inverseImageCompIso :
    (functorSituation.{w} C C' f B).totalAbelianInverseImage ⋙
        (functorSituation.{w} C C' f B).abelianInverseImage ≅
      ((functorSituation.{w} C C' f B).u ⋙ (functorSituation.{w} C C' f
          B).p).sheafPushforwardContinuous AddCommGrpCat.{max w u u'}
        (functorSituation.{w} C C' f B).sourceTopology (functorSituation.{w} C C' f B).base.J :=
  (functorSituation.{w} C C' f B).abelianInverseImageCompIso

/-- `π'_! = colim` on sections over the point, for the source of the situation attached to `f`. -/
abbrev sourceColimitLowerShriekIso :=
  colimitLowerShriekIso (functorSituation_sourceTopology.{w} C C' f B) AddCommGrpCat.{max w u u'}
    (K := (functorSituation.{w} C C' f B).base.J) rfl ((functorSituation.{w} C C' f B).u ⋙
        (functorSituation.{w} C C' f B).p)
    (hq := (functorSituation.{w} C C' f B).p'Continuous) (sourceAdjunction f B)

/-- `colimitLowerShriekIso_hom_app_comp` for the situation attached to a functor: the canonical
map in degree zero, on sections over the point, is the map of colimits. -/
theorem sourceColimitLowerShriekIso_hom_app_comp
    (X' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'})
    (X : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'})
    (φ : X' ⟶ (functorSituation.{w} C C' f B).abelianInverseImage.obj X) :
    (sourceColimitLowerShriekIso f B).hom.app X' ≫
        (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
          (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.map
          ((Adjunction.leftAdjointCompIso (functorSituation.{w} C C' f
              B).abelianLowerShriekAdjunction
              (functorSituation.{w} C C' f B).totalAbelianLowerShriekAdjunction
              (sourceAdjunction f B) (inverseImageCompIso f B)).inv.app X' ≫
            (functorSituation.{w} C C' f B).totalAbelianLowerShriek.map
              ((functorSituation.{w} C C' f B).abelianLowerShriek.map φ ≫
                (functorSituation.{w} C C' f B).abelianLowerShriekAdjunction.counit.app X)) =
      colim.map (φ.hom : X'.obj ⟶ (functorSituation.{w} C C' f B).u.op ⋙ X.obj) ≫
        colimit.pre X.obj (functorSituation.{w} C C' f B).u.op ≫
        (totalColimitLowerShriekIso f B).hom.app X := by
  have h := colimitLowerShriekIso_hom_app_comp (functorSituation_totalTopology.{w} C C' f B)
    (functorSituation_sourceTopology.{w} C C' f B) AddCommGrpCat.{max w u u'}
    (K := (functorSituation.{w} C C' f B).base.J) rfl (functorSituation.{w} C C' f B).p
    (functorSituation.{w} C C' f B).u (hq := (functorSituation.{w} C C' f B).pContinuous)
    (hq' := (functorSituation.{w} C C' f B).p'Continuous)
    (hf := (functorSituation.{w} C C' f B).uContinuous)
    (functorSituation.{w} C C' f B).totalAbelianLowerShriekAdjunction
    (sourceAdjunction f B) (functorSituation.{w} C C' f B).abelianLowerShriekAdjunction
    (inverseImageCompIso f B) (sheafPushforwardContinuousComp'_eqToIso_hom_app_hom
      AddCommGrpCat.{max w u u'} _ _ (hq := (functorSituation.{w} C C' f B).pContinuous)
      (hq' := comp_p_isContinuous f B) (hf := (functorSituation.{w} C C' f B).uContinuous)
      (functorSituation.{w} C C' f B).isFibredOneMorphism.comp_eq) X' X φ
  exact h

end Situation

section PresheafLift

open HomologicalComplex Stacks.Homology.DerivedLeftAdjointComp Stacks.CategoryHomology

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
  (B : CommRingCat.{max w u u'})

/-- Abelian presheaves on the target have enough projectives. -/
instance totalEnoughProjectives : EnoughProjectives
    ((functorSituation.{w} C C' f B).totalᵒᵖ ⥤ AddCommGrpCat.{max w u u'}) :=
  presheafEnoughProjectives.{u, max u' w} (functorSituation.{w} C C' f B).total

/-- Abelian presheaves on the source have enough projectives. -/
instance sourceEnoughProjectives : EnoughProjectives
    ((functorSituation.{w} C C' f B).sourceᵒᵖ ⥤ AddCommGrpCat.{max w u u'}) :=
  presheafEnoughProjectives.{u', max u w} (functorSituation.{w} C C' f B).source

/-- The lift of `t : F' ⟶ g⁻¹F` to the chosen projective resolutions, on presheaves. -/
abbrev presheafLift
    {F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}}
    {F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}}
    (t : F' ⟶ (functorSituation.{w} C C' f B).abelianInverseImage.obj F) :
    (ProjectiveResolution.of F'.obj).complex ⟶
      ((presheafRestriction.{u, u', w} (functorSituation.{w} C C' f B).u).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (ProjectiveResolution.of F.obj).complex :=
  have : PreservesFiniteLimits (presheafRestriction.{u, u', w} (functorSituation.{w} C C' f B).u) :=
    inferInstance
  have : PreservesFiniteColimits
    (presheafRestriction.{u, u', w} (functorSituation.{w} C C' f B).u) := inferInstance
  have : (presheafRestriction.{u, u', w} (functorSituation.{w} C C' f B).u).PreservesHomology :=
    inferInstance
  have := (ProjectiveResolution.of F.obj).quasiIso
  have := Functor.quasiIso_mapAugmentation
    (presheafRestriction.{u, u', w} (functorSituation.{w} C C' f B).u)
    (ProjectiveResolution.of F.obj).π
  ProjectiveResolution.lift' (Z := (presheafRestriction.{u, u', w}
      (functorSituation.{w} C C' f B).u).obj F.obj) t.hom (ProjectiveResolution.of F'.obj)
    ((presheafRestriction.{u, u', w} (functorSituation.{w} C C' f B).u).mapAugmentation
      (ProjectiveResolution.of F.obj).π)

end PresheafLift

section Resolutions

open HomologicalComplex Stacks.Homology.DerivedLeftAdjointComp Stacks.CategoryHomology

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
  (B : CommRingCat.{max w u u'})

/-- Abelian sheaves on the target of the situation are abelian presheaves. -/
abbrev totalSheafEquiv :=
  sheafEquivOfEqTrivial (functorSituation_totalTopology.{w} C C' f B) AddCommGrpCat.{max w u u'}

/-- Abelian sheaves on the source of the situation are abelian presheaves. -/
abbrev sourceSheafEquiv :=
  sheafEquivOfEqTrivial (functorSituation_sourceTopology.{w} C C' f B) AddCommGrpCat.{max w u u'}

/-- Reading presheaves on the target as sheaves is additive. -/
instance totalSheafEquiv_inverse_additive : (totalSheafEquiv f B).inverse.Additive where
  map_add := rfl

/-- Reading presheaves on the source as sheaves is additive. -/
instance sourceSheafEquiv_inverse_additive : (sourceSheafEquiv f B).inverse.Additive where
  map_add := rfl

/-- The cochain complex of the chosen projective resolution of the underlying presheaf of `F`,
read as a complex of sheaves on the target. -/
abbrev totalResolution
    (F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}) :
    CochainComplex (Sheaf (functorSituation.{w} C C' f B).totalTopology
      AddCommGrpCat.{max w u u'}) ℤ :=
  ((totalSheafEquiv f B).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (ProjectiveResolution.of F.obj).cochainComplex

/-- The cochain complex of the chosen projective resolution of the underlying presheaf of `F'`,
read as a complex of sheaves on the source. -/
abbrev sourceResolution
    (F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}) :
    CochainComplex (Sheaf (functorSituation.{w} C C' f B).sourceTopology
      AddCommGrpCat.{max w u u'}) ℤ :=
  ((sourceSheafEquiv f B).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (ProjectiveResolution.of F'.obj).cochainComplex

/-- The resolution of a sheaf on the target is K-projective. -/
instance (F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}) :
    (totalResolution f B F).IsKProjective := by
  have : (totalResolution f B F).IsStrictlyLE 0 :=
      ⟨fun n hn => (totalSheafEquiv f B).inverse.map_isZero
    (CochainComplex.isZero_of_isStrictlyLE _ 0 n (by
      by_contra h
      exact hn (-n).toNat (by simp at hn ⊢; omega)))⟩
  have : ∀ n, Projective ((totalResolution f B F).X n) := fun n =>
    (totalSheafEquiv f B).symm.toAdjunction.map_projective _ inferInstance
  exact CochainComplex.isKProjective_of_projective _ 0

/-- The resolution of a sheaf on the source is K-projective. -/
instance (F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}) :
    (sourceResolution f B F').IsKProjective := by
  have : (sourceResolution f B F').IsStrictlyLE 0 := ⟨fun n hn =>
    (sourceSheafEquiv f B).inverse.map_isZero
    (CochainComplex.isZero_of_isStrictlyLE _ 0 n (by
      by_contra h
      exact hn (-n).toNat (by simp at hn ⊢; omega)))⟩
  have : ∀ n, Projective ((sourceResolution f B F').X n) := fun n =>
    (sourceSheafEquiv f B).symm.toAdjunction.map_projective _ inferInstance
  exact CochainComplex.isKProjective_of_projective _ 0

/-- The augmentation of `totalResolution`. -/
def totalAugmentation
    (F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}) :
    totalResolution f B F ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F :=
  ((totalSheafEquiv f B).inverse.mapHomologicalComplex _).map (ProjectiveResolution.of F.obj).π' ≫
    (HomologicalComplex.singleMapHomologicalComplex (totalSheafEquiv f B).inverse _ 0).hom.app F.obj

/-- The augmentation of `sourceResolution`. -/
def sourceAugmentation
    (F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}) :
    sourceResolution f B F' ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F' :=
  ((sourceSheafEquiv f B).inverse.mapHomologicalComplex _).map
      (ProjectiveResolution.of F'.obj).π' ≫
    (HomologicalComplex.singleMapHomologicalComplex (sourceSheafEquiv f B).inverse _ 0).hom.app
      F'.obj

/-- The augmentation of the resolution of a sheaf on the target is a quasi-isomorphism. -/
instance (F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}) :
    QuasiIso (totalAugmentation f B F) := by
  have : (totalSheafEquiv f B).inverse.PreservesHomology := inferInstance
  have : QuasiIso (ProjectiveResolution.of F.obj).π' := inferInstance
  have : IsIso ((HomologicalComplex.singleMapHomologicalComplex (totalSheafEquiv f B).inverse
      (ComplexShape.up ℤ) 0).hom.app F.obj) :=
    ((HomologicalComplex.singleMapHomologicalComplex (totalSheafEquiv f B).inverse
      (ComplexShape.up ℤ) 0).app F.obj).isIso_hom
  have : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (totalSheafEquiv f B).inverse
      (ComplexShape.up ℤ) 0).hom.app F.obj) := quasiIso_of_isIso _
  have hq0 := this
  have : QuasiIso (((totalSheafEquiv f B).inverse.mapHomologicalComplex
    (ComplexShape.up ℤ)).map (ProjectiveResolution.of F.obj).π') :=
    quasiIso_map_of_preservesHomology _ _
  exact (quasiIso_iff_comp_right _ _ (hφ' := hq0)).2 this

/-- The augmentation of the resolution of a sheaf on the source is a quasi-isomorphism. -/
instance (F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}) :
    QuasiIso (sourceAugmentation f B F') := by
  have : (sourceSheafEquiv f B).inverse.PreservesHomology := inferInstance
  have : QuasiIso (ProjectiveResolution.of F'.obj).π' := inferInstance
  have : IsIso ((HomologicalComplex.singleMapHomologicalComplex (sourceSheafEquiv f B).inverse
      (ComplexShape.up ℤ) 0).hom.app F'.obj) :=
    ((HomologicalComplex.singleMapHomologicalComplex (sourceSheafEquiv f B).inverse
      (ComplexShape.up ℤ) 0).app F'.obj).isIso_hom
  have : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (sourceSheafEquiv f B).inverse
      (ComplexShape.up ℤ) 0).hom.app F'.obj) := quasiIso_of_isIso _
  have hq0 := this
  have : QuasiIso (((sourceSheafEquiv f B).inverse.mapHomologicalComplex
    (ComplexShape.up ℤ)).map (ProjectiveResolution.of F'.obj).π') :=
    quasiIso_map_of_preservesHomology _ _
  exact (quasiIso_iff_comp_right _ _ (hφ' := hq0)).2 this

/-- The lift of `t : F' ⟶ g⁻¹F` to the resolutions, as a map of complexes of sheaves. -/
def sheafLift
    {F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}}
    {F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}}
    (t : F' ⟶ (functorSituation.{w} C C' f B).abelianInverseImage.obj F) :
    sourceResolution f B F' ⟶
      ((functorSituation.{w} C C' f B).abelianInverseImage.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (totalResolution f B F) :=
  ((sourceSheafEquiv f B).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (extendLift (presheafRestriction.{u, u', w} (functorSituation.{w} C C' f B).u)
      (ProjectiveResolution.of F'.obj) (ProjectiveResolution.of F.obj) (presheafLift f B t))

/-- `sheafLift` lifts `t` through the augmentations of the two resolutions. -/
theorem liftCondition_sheafLift
    {F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}}
    {F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}}
    (t : F' ⟶ (functorSituation.{w} C C' f B).abelianInverseImage.obj F) :
    LiftCondition (functorSituation.{w} C C' f B).abelianInverseImage t
      (sourceAugmentation f B F') (totalAugmentation f B F) (sheafLift f B t) := by
  have h := liftCondition_extendLift
    (presheafRestriction.{u, u', w} (functorSituation.{w} C C' f B).u)
    (F := F.obj) (F' := F'.obj) t.hom
    (ProjectiveResolution.of F'.obj) (ProjectiveResolution.of F.obj) (presheafLift f B t)
    (ProjectiveResolution.lift'_commutes _ _ _)
  unfold LiftCondition at h ⊢
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi0 : i = 0
  · subst hi0
    apply Sheaf.hom_ext
    exact congrArg (fun g => HomologicalComplex.Hom.f g 0) h
  · exact ((functorSituation.{w} C C' f B).abelianInverseImage.map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i hi0)).eq_of_tgt _ _

/-- `π'_!` preserves zero morphisms. -/
instance sourceAbelianLowerShriek_preservesZeroMorphisms :
    (functorSituation.{w} C C' f B).sourceAbelianLowerShriek.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- `π_!` preserves zero morphisms. -/
instance totalAbelianLowerShriek_preservesZeroMorphisms :
    (functorSituation.{w} C C' f B).totalAbelianLowerShriek.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The degreewise map `π'_!(K') ⟶ π_!(K)` attached to the lift, for the situation. -/
abbrev resolutionLowerShriekMap
    {F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}}
    {F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}}
    (t : F' ⟶ (functorSituation.{w} C C' f B).abelianInverseImage.obj F) :=
  resolutionMap (functorSituation.{w} C C' f B).abelianLowerShriekAdjunction
    (functorSituation.{w} C C' f B).totalAbelianLowerShriekAdjunction
    (functorSituation.{w} C C' f B).sourceAbelianLowerShriekAdjunction
    (functorSituation.{w} C C' f B).abelianInverseImageCompIso (sheafLift f B t)

/-- **The canonical map in degree zero, degreewise on the resolutions.** -/
theorem colimitLowerShriekComplexIso_hom_resolutionLowerShriekMap
    {F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}}
    {F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}}
    (t : F' ⟶ (functorSituation.{w} C C' f B).abelianInverseImage.obj F) :
    (colimitLowerShriekComplexIso (functorSituation_sourceTopology.{w} C C' f B)
        AddCommGrpCat.{max w u u'} (K := (functorSituation.{w} C C' f B).base.J) rfl
        ((functorSituation.{w} C C' f B).u ⋙ (functorSituation.{w} C C' f B).p)
        (hq := (functorSituation.{w} C C' f B).p'Continuous) (sourceAdjunction f B)
        (hL := @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
          (sourceAdjunction f B).isLeftAdjoint) (sourceResolution f B F')).hom ≫
      ((pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
          (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).map (resolutionLowerShriekMap f B t) =
    ((colim : ((functorSituation.{w} C C' f B).sourceᵒᵖ ⥤ AddCommGrpCat.{max w u u'}) ⥤
        _).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (((sourceSheafEquiv f B).functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (sheafLift f B t)) ≫
      (NatTrans.mapHomologicalComplex
        (colimitRestrictionPre.{u, u', w} (functorSituation.{w} C C' f B).u)
          (ComplexShape.up ℤ)).app
          (((totalSheafEquiv f B).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (totalResolution f B F)) ≫
      (colimitLowerShriekComplexIso (functorSituation_totalTopology.{w} C C' f B)
        AddCommGrpCat.{max w u u'} (K := (functorSituation.{w} C C' f B).base.J) rfl
        (functorSituation.{w} C C' f B).p (hq := (functorSituation.{w} C C' f B).pContinuous)
        (functorSituation.{w} C C' f B).totalAbelianLowerShriekAdjunction
        (hL := @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
          (functorSituation.{w} C C' f B).totalAbelianLowerShriekAdjunction.isLeftAdjoint)
              (totalResolution f B F)).hom := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  exact sourceColimitLowerShriekIso_hom_app_comp f B _ _ ((sheafLift f B t).f i)

/-- Abelian sheaves on the point of the situation can be sheafified. -/
instance baseHasSheafify : HasSheafify (functorSituation.{w} C C' f B).base.J
    AddCommGrpCat.{max w u u'} :=
  (functorSituation.{w} C C' f B).hasSheafifyBaseTopology.{max u u', u, u', max u u', u, u', w}

/-- Abelian sheaves on the point of the situation form an abelian category. -/
instance baseAbelian : Abelian (Sheaf (functorSituation.{w} C C' f B).base.J
    AddCommGrpCat.{max w u u'}) :=
  sheafIsAbelian

/-- Sections over the point are additive. -/
instance pointSheafEquiv_functor_additive :
    @Functor.Additive _ _ _ _ (Abelian.toPreadditive (self := baseAbelian f B)) _
      (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
      (K := (functorSituation.{w} C C' f B).base.J) rfl).functor where
  map_add := rfl

/-- Sections over the point preserve finite limits. -/
instance pointSheafEquiv_functor_preservesFiniteLimits :
    PreservesFiniteLimits (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
      (K := (functorSituation.{w} C C' f B).base.J) rfl).functor := by
  have := (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
      (K := (functorSituation.{w} C C' f B).base.J)
          rfl).symm.toAdjunction.rightAdjoint_preservesLimits.{0, 0}
  infer_instance

/-- Sections over the point preserve finite colimits. -/
instance pointSheafEquiv_functor_preservesFiniteColimits :
    PreservesFiniteColimits (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
      (K := (functorSituation.{w} C C' f B).base.J) rfl).functor := by
  have := (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
      (K := (functorSituation.{w} C C' f B).base.J)
          rfl).toAdjunction.leftAdjoint_preservesColimits.{0, 0}
  infer_instance

variable
  [HasDerivedCategory (Sheaf (functorSituation.{w} C C' f B).base.J AddCommGrpCat.{max w u u'})]

/-- The sections over the point of `H^{-n}` of a complex of abelian sheaves on the point, read on
the complex of sections. -/
def pointHomologyIso (L : CochainComplex (Sheaf (functorSituation.{w} C C' f B).base.J
      AddCommGrpCat.{max w u u'}) ℤ) (n : ℤ) :
    (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.obj
        ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
            AddCommGrpCat.{max w u u'}) n).obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (Sheaf (functorSituation.{w} C C' f
              B).base.J AddCommGrpCat.{max w u u'}) (ComplexShape.up ℤ)).obj L))) ≅
      (((pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).homology n :=
  (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
      (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.mapIso
      ((DerivedCategory.homologyFunctorFactorsh (Sheaf (functorSituation.{w} C C' f B).base.J
          AddCommGrpCat.{max w u u'}) n).app
          ((HomotopyCategory.quotient (Sheaf (functorSituation.{w} C C' f B).base.J
              AddCommGrpCat.{max w u u'}) (ComplexShape.up ℤ)).obj L) ≪≫
        (HomotopyCategory.homologyFunctorFactors (Sheaf (functorSituation.{w} C C' f B).base.J
            AddCommGrpCat.{max w u u'}) (ComplexShape.up ℤ) n).app L) ≪≫
    (@Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso _ _ _ _
      (Abelian.toPreadditive (self := baseAbelian f B)) _ _ _
      (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor
      (pointSheafEquiv_functor_additive f B)
      (@Functor.preservesHomologyOfExact _ _ _ _ _ _ _
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (pointSheafEquiv_functor_additive f B))
        (pointSheafEquiv_functor_preservesFiniteLimits f B)
        (pointSheafEquiv_functor_preservesFiniteColimits f B))
      L n inferInstance inferInstance).symm

/-- Transport of a commutative square along a functor and two isomorphisms. -/
private lemma comp_mapIso_trans_symm_hom {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (E : 𝒞 ⥤ 𝒟)
    {P P' Q Q' : 𝒞} {R R' : 𝒟} (x : P ⟶ P') (y : Q ⟶ Q') (z : R ⟶ R') (α : P ≅ Q) (α' : P' ≅ Q')
    (β : R ≅ E.obj Q) (β' : R' ≅ E.obj Q') (h₁ : x ≫ α'.hom = α.hom ≫ y)
    (h₂ : z ≫ β'.hom = β.hom ≫ E.map y) :
    E.map x ≫ (E.mapIso α' ≪≫ β'.symm).hom = (E.mapIso α ≪≫ β.symm).hom ≫ z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Functor.map_comp_assoc, h₁, Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, h₂, Iso.inv_hom_id_assoc]

/-- `pointHomologyIso` is natural in the complex. -/
theorem pointHomologyIso_hom_naturality {L L' : CochainComplex
    (Sheaf (functorSituation.{w} C C' f B).base.J AddCommGrpCat.{max w u u'}) ℤ} (g : L ⟶ L')
    (n : ℤ) :
    (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.map
        ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
            AddCommGrpCat.{max w u u'}) n).map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient (Sheaf (functorSituation.{w} C C' f
              B).base.J AddCommGrpCat.{max w u u'}) (ComplexShape.up ℤ)).map g))) ≫
      (pointHomologyIso f B L' n).hom =
    (pointHomologyIso f B L n).hom ≫
      homologyMap (((pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) n := by
  have n1 := (DerivedCategory.homologyFunctorFactorsh (Sheaf (functorSituation.{w} C C' f B).base.J
      AddCommGrpCat.{max w u u'}) n).hom.naturality
    ((HomotopyCategory.quotient (Sheaf (functorSituation.{w} C C' f B).base.J AddCommGrpCat.{max w
        u u'}) (ComplexShape.up ℤ)).map g)
  have n2 := (HomotopyCategory.homologyFunctorFactors (Sheaf (functorSituation.{w} C C' f B).base.J
      AddCommGrpCat.{max w u u'}) (ComplexShape.up ℤ) n).hom.naturality g
  simp only [Functor.comp_map] at n1 n2
  have hX := ((reassoc_of% n1) ((HomotopyCategory.homologyFunctorFactors (Sheaf
      (functorSituation.{w} C C' f B).base.J AddCommGrpCat.{max w u u'})
    (ComplexShape.up ℤ) n).hom.app L')).trans (congrArg (_ ≫ ·) n2)
  have h3 := @mapHomologicalComplexHomologyIso_hom_naturality _ _ _ _ (baseAbelian f B) _
      (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'} (K :=
      (functorSituation.{w} C C' f B).base.J) rfl).functor
    (pointSheafEquiv_functor_additive f B)
      (@Functor.preservesHomologyOfExact _ _ _ _ _ _ _
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (pointSheafEquiv_functor_additive f B))
        (pointSheafEquiv_functor_preservesFiniteLimits f B)
        (pointSheafEquiv_functor_preservesFiniteColimits f B)) L L' g n
  exact comp_mapIso_trans_symm_hom _ _ _ _ _ _ _ _ hX h3

end Resolutions

section Bridge

open HomologicalComplex Stacks.Homology.DerivedLeftAdjointComp Stacks.CategoryHomology

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
  (B : CommRingCat.{max w u u'})

/-- Transport of a map along isomorphisms, in three steps. -/
private lemma eq_trans_trans_hom_comp_inv {𝒞 : Type*} [Category* 𝒞] {a b a₁ b₁ c₁ c₂ d₁ d₂ : 𝒞}
    (u : a ⟶ b) (p' : a ≅ a₁) (p : b ≅ b₁) (v : a₁ ⟶ b₁) (h₁ : u ≫ p.hom = p'.hom ≫ v)
    (j' : a₁ ≅ c₁) (j : b₁ ≅ c₂) (w : c₁ ⟶ c₂) (hv : v = j'.hom ≫ w ≫ j.inv)
    (r' : c₁ ≅ d₁) (r : c₂ ≅ d₂) (m : d₁ ⟶ d₂) (hm : m = r'.inv ≫ w ≫ r.hom) :
    u = (p' ≪≫ j' ≪≫ r').hom ≫ m ≫ (p ≪≫ j ≪≫ r).inv := by
  rw [(Iso.eq_comp_inv p).2 h₁, hv, hm]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- A map of complexes which is a map `M` up to isomorphisms of complexes has the homology of
`M` up to the induced isomorphisms. -/
private lemma homologyMap_eq_of_iso_comp {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] {ι : Type*}
    {c : ComplexShape ι} {X₁ X₂ Y₁ Y₂ : HomologicalComplex 𝒜 c} (g : X₁ ⟶ X₂) (i₁ : Y₁ ≅ X₁)
    (i₂ : Y₂ ≅ X₂) (M : Y₁ ⟶ Y₂) (h : i₁.hom ≫ g = M ≫ i₂.hom) (q : ι) :
    homologyMap g q =
      (homologyMapIso i₁.symm q).hom ≫ homologyMap M q ≫ (homologyMapIso i₂.symm q).inv := by
  rw [(Iso.eq_inv_comp i₁).2 h]
  simp [homologyMap_comp]

/-- A map between isomorphic objects, transported along a second pair of isomorphisms. -/
private lemma hom_comp_comp_inv_eq_trans {𝒞 : Type*} [Category* 𝒞] {a b c d e g : 𝒞}
    (Φ' : a ≅ b) (m : b ⟶ c) (Φ : d ≅ c) (R' : b ≅ e) (R : c ≅ g) (k : e ⟶ g)
    (h : k = R'.inv ≫ m ≫ R.hom) :
    Φ'.hom ≫ m ≫ Φ.inv = (Φ' ≪≫ R').hom ≫ k ≫ (Φ ≪≫ R).inv := by
  subst h
  simp

/-- A map in a derived category, recovered from a commutative square with isomorphisms. -/
private lemma map_map_eq_of_comp_eq {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ]
    (H : 𝒞 ⥤ 𝒟) (E : 𝒟 ⥤ ℰ) {A' B' A B Y' Y : 𝒞} {Z' Z : ℰ} (x' : A' ⟶ B') (_ : IsIso x')
    (c : B' ⟶ B) (a' : A' ⟶ Y') (_ : IsIso a') (r : Y' ⟶ Y) (a : A ⟶ Y) (_ : IsIso a)
    (x : A ⟶ B) (_ : IsIso x) (hc : x' ≫ c = a' ≫ r ≫ inv a ≫ x) (Ξ' : E.obj (H.obj Y') ≅ Z')
    (Ξ : E.obj (H.obj Y) ≅ Z) (m : Z' ⟶ Z) (hk : E.map (H.map r) = Ξ'.hom ≫ m ≫ Ξ.inv) :
    E.map (H.map c) = (E.mapIso (H.mapIso ((asIso x').symm ≪≫ asIso a')) ≪≫ Ξ').hom ≫ m ≫
      (E.mapIso (H.mapIso ((asIso x).symm ≪≫ asIso a)) ≪≫ Ξ).inv := by
  rw [(IsIso.eq_inv_comp x').2 hc]
  simp only [Functor.map_comp, hk, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv, Category.assoc]

/-- The augmentation of the resolution of a sheaf on the target is invertible in the derived
category. -/
instance isIso_Qh_map_singleQuot_totalAugmentation
    [HasDerivedCategory (Sheaf (functorSituation.{w} C C' f B).totalTopology
      AddCommGrpCat.{max w u u'})]
    (F : Sheaf (functorSituation.{w} C C' f
    B).totalTopology AddCommGrpCat.{max w u u'}) :
    IsIso (DerivedCategory.Qh.map (singleQuot (totalAugmentation f B F))) :=
  Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (show QuasiIso _ from inferInstance))

/-- The augmentation of the resolution of a sheaf on the source is invertible in the derived
category. -/
instance isIso_Qh_map_singleQuot_sourceAugmentation
    [HasDerivedCategory (Sheaf (functorSituation.{w} C C' f B).sourceTopology
      AddCommGrpCat.{max w u u'})]
    (F' : Sheaf (functorSituation.{w} C C' f
    B).sourceTopology AddCommGrpCat.{max w u u'}) :
    IsIso (DerivedCategory.Qh.map (singleQuot (sourceAugmentation f B F'))) :=
  Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (show QuasiIso _ from inferInstance))

section Generic

variable
  [HasDerivedCategory (Sheaf (functorSituation.{w} C C' f B).base.J AddCommGrpCat.{max w u u'})]

/-- The sections over the point of `H^{-n}` of `π_!` applied degreewise to the resolution of `F`
are the homology `H_n(C, F)`. -/
def totalResolutionHomologyIso (F : Sheaf (functorSituation.{w} C C' f B).totalTopology
    AddCommGrpCat.{max w u u'}) (n : ℕ) :
    (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.obj
      ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
          AddCommGrpCat.{max w u u'}) (-(n : ℤ))).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (Sheaf (functorSituation.{w} C C' f
            B).base.J AddCommGrpCat.{max w u u'}) (ComplexShape.up ℤ)).obj
          (((functorSituation.{w} C C' f B).totalAbelianLowerShriek.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (totalResolution f B F))))) ≅
      categoryHomology.{u, max u' w} F.obj n :=
  pointHomologyIso f B _ (-(n : ℤ)) ≪≫
    homologyMapIso (colimitLowerShriekComplexIso (functorSituation_totalTopology.{w} C C' f B)
        AddCommGrpCat.{max w u u'} (K := (functorSituation.{w} C C' f B).base.J) rfl
        (functorSituation.{w} C C' f B).p (hq := (functorSituation.{w} C C' f B).pContinuous)
        (functorSituation.{w} C C' f B).totalAbelianLowerShriekAdjunction
        (hL := @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
          (functorSituation.{w} C C' f B).totalAbelianLowerShriekAdjunction.isLeftAdjoint)
        (totalResolution f B F)).symm (-(n : ℤ)) ≪≫
    (resolutionHomologyIso F.obj n).symm

/-- The sections over the point of `H^{-n}` of `π'_!` applied degreewise to the resolution of
`F'` are the homology `H_n(C', F')`. -/
def sourceResolutionHomologyIso (F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology
    AddCommGrpCat.{max w u u'}) (n : ℕ) :
    (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.obj
      ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
          AddCommGrpCat.{max w u u'}) (-(n : ℤ))).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (Sheaf (functorSituation.{w} C C' f
            B).base.J AddCommGrpCat.{max w u u'}) (ComplexShape.up ℤ)).obj
          (((functorSituation.{w} C C' f B).sourceAbelianLowerShriek.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (sourceResolution f B F'))))) ≅
      categoryHomology.{u', max u w} F'.obj n :=
  pointHomologyIso f B _ (-(n : ℤ)) ≪≫
    homologyMapIso (colimitLowerShriekComplexIso (functorSituation_sourceTopology.{w} C C' f B)
        AddCommGrpCat.{max w u u'} (K := (functorSituation.{w} C C' f B).base.J) rfl
        ((functorSituation.{w} C C' f B).u ⋙ (functorSituation.{w} C C' f B).p) (hq :=
            (functorSituation.{w} C C' f B).p'Continuous) (sourceAdjunction f B)
        (hL := @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
          (sourceAdjunction f B).isLeftAdjoint)
        (sourceResolution f B F')).symm (-(n : ℤ)) ≪≫
    (resolutionHomologyIso F'.obj n).symm

/-- The map `π'_!(K') ⟶ π_!(K)` on the resolutions induces the canonical map of homology. -/
theorem map_homologyFunctor_map_resolutionLowerShriekMap
    {F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}} {F' :
        Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'}}
    (t : F' ⟶ (functorSituation.{w} C C' f B).abelianInverseImage.obj F) (n : ℕ) :
    (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.map
            ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
        AddCommGrpCat.{max w u u'}) (-(n : ℤ))).map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (Sheaf (functorSituation.{w} C C' f B).base.J AddCommGrpCat.{max
          w u u'}) (ComplexShape.up ℤ)).map (resolutionLowerShriekMap f B t)))) =
      (sourceResolutionHomologyIso f B F' n).hom ≫
        categoryHomologyMap.{u, u', w} f (t.hom : F'.obj ⟶ f.op ⋙ F.obj) n ≫
        (totalResolutionHomologyIso f B F n).inv :=
  eq_trans_trans_hom_comp_inv _ _ _ _
    (pointHomologyIso_hom_naturality f B (resolutionLowerShriekMap f B t) (-(n : ℤ))) _ _ _
    (homologyMap_eq_of_iso_comp _ _ _ _
      (colimitLowerShriekComplexIso_hom_resolutionLowerShriekMap f B t) _) _ _ _
    (homologyMapAux_eq_resolutionHomologyIso.{w} (functorSituation.{w} C C' f B).u t.hom n
        (presheafLift f B t)
      (ProjectiveResolution.lift'_commutes _ _ _))

end Generic

attribute [local instance] HasDerivedCategory.standard

/-- **`H_n(C, F) = L_nπ_!F`**: the sections over the point of `H^{-n}(Lπ_!F)` are the homology
of `C` with coefficients in the underlying presheaf of `F`. -/
def totalHomologyIso (F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w
    u u'}) (n : ℕ) :
    (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.obj
            ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
        AddCommGrpCat.{max w u u'}) (-(n : ℤ))).obj ((functorSituation.{w} C C' f
            B).derivedTotalAbelianLowerShriek.obj
      ((DerivedCategory.singleFunctor (Sheaf (functorSituation.{w} C C' f B).totalTopology
          AddCommGrpCat.{max w u u'}) 0).obj F))) ≅
      categoryHomology.{u, max u' w} F.obj n :=
  (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.mapIso
            ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
        AddCommGrpCat.{max w u u'}) (-(n : ℤ))).mapIso
    ((asIso ((functorSituation.{w} C C' f B).derivedTotalAbelianLowerShriek.map
      (DerivedCategory.Qh.map (singleQuot (totalAugmentation f B F)) ≫
        (DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app F))).symm ≪≫
      @asIso _ _ _ _ ((Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w u
          u', u, u, max u u',
        max u u'} (functorSituation.{w} C C' f B).totalTopology
        (functorSituation.{w} C C' f B).base.J (functorSituation.{w} C C' f B).p).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (totalResolution f B F))) ((functorSituation.{w} C C' f B).isIso_totalComparison_app _))) ≪≫
    totalResolutionHomologyIso f B F n

/-- **`H_n(C', F') = L_nπ'_!F'`**: the sections over the point of `H^{-n}(Lπ'_!F')` are the
homology of `C'` with coefficients in the underlying presheaf of `F'`. -/
def sourceHomologyIso (F' : Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max
    w u u'}) (n : ℕ) :
    (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.obj
            ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
        AddCommGrpCat.{max w u u'}) (-(n : ℤ))).obj ((functorSituation.{w} C C' f
            B).derivedSourceAbelianLowerShriek.obj
      ((DerivedCategory.singleFunctor (Sheaf (functorSituation.{w} C C' f B).sourceTopology
          AddCommGrpCat.{max w u u'}) 0).obj F'))) ≅
      categoryHomology.{u', max u w} F'.obj n :=
  (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.mapIso
            ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
        AddCommGrpCat.{max w u u'}) (-(n : ℤ))).mapIso
    ((asIso ((functorSituation.{w} C C' f B).derivedSourceAbelianLowerShriek.map
      (DerivedCategory.Qh.map (singleQuot (sourceAugmentation f B F')) ≫
        (DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app F'))).symm ≪≫
      @asIso _ _ _ _ ((Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w u
          u', u', u', max u u',
        max u u'} (functorSituation.{w} C C' f B).sourceTopology
        (functorSituation.{w} C C' f B).base.J (functorSituation.{w} C C' f B).p').app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (sourceResolution f B F'))) ((functorSituation.{w} C C' f B).isIso_sourceComparison_app
            _))) ≪≫
    sourceResolutionHomologyIso f B F' n

/-- **Stacks 08PH, the canonical maps on homology come from Remark 08PD.** Let `f : C' ⥤ C` be a
functor between small categories, give both categories their chaotic topologies and view them,
with `f`, as the situation of Stacks 08PA over the point (`functorSituation`). Let `F` be an
abelian presheaf on `C`, `F'` an abelian presheaf on `C'` and `t : F' ⟶ f⁻¹F`. Under the
identifications `H_n(C, F) = L_nπ_!F` and `H_n(C', F') = L_nπ'_!F'` (`totalHomologyIso` and
`sourceHomologyIso`: `H^{-n}` of the derived lower shriek to the point, read through the sections
over the point), the map `H^{-n}` of the canonical map `Lπ'_!F' ⟶ Lπ_!F` of Remark 08PD is the
canonical map `H_n(C', F') ⟶ H_n(C, F)` built from the chain map `K(F') ⟶ K(F)` on projective
resolutions (`categoryHomologyMap`). -/
@[stacks 08PH "the maps of Remark 08PD are the canonical maps on homology"]
theorem map_homologyFunctor_map_canonicalDerivedLowerShriekMap'
    (F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}) (F' :
        Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'})
    (t : F' ⟶ (functorSituation.{w} C C' f B).abelianInverseImage.obj F) (n : ℕ) :
    (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.map
            ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
        AddCommGrpCat.{max w u u'}) (-(n : ℤ))).map ((functorSituation.{w} C C' f
            B).canonicalDerivedLowerShriekMap' F F' t)) =
      (sourceHomologyIso f B F' n).hom ≫
        categoryHomologyMap.{u, u', w} f (t.hom : F'.obj ⟶ f.op ⋙ F.obj) n ≫
        (totalHomologyIso f B F n).inv := by
  exact map_map_eq_of_comp_eq _ _ _ inferInstance _ _
    ((functorSituation.{w} C C' f B).isIso_sourceComparison_app (sourceResolution f B F')) _ _
    ((functorSituation.{w} C C' f B).isIso_totalComparison_app (totalResolution f B F)) _
    inferInstance
    ((functorSituation.{w} C C' f B).canonicalDerivedLowerShriekMap_comp_eq
      (Stacks.Sites.FibredCategory.MorphismSituation.abelianLowerShriekAcyclic
          (functorSituation.{w} C C' f B))
      (Stacks.Sites.FibredCategory.MorphismSituation.totalSituation (functorSituation.{w} C C' f
          B)).abelianLowerShriekAcyclic
      (Stacks.Sites.FibredCategory.MorphismSituation.sourceSituation (functorSituation.{w} C C' f
          B)).abelianLowerShriekAcyclic
      F F' t (sourceAugmentation f B F') (totalAugmentation f B F) (sheafLift f B t)
      (liftCondition_sheafLift f B t) ((functorSituation.{w} C C' f B).isIso_totalComparison_app
          _)) _ _ _
    (map_homologyFunctor_map_resolutionLowerShriekMap f B t n)

/-- **Stacks 08PH: the maps of Remark 08PD come from the chain map `K_•(F') ⟶ K_•(F)`.** Let
`f : C' ⥤ C` be a functor between small categories with their chaotic topologies, viewed with the
point and a ring `B` as the situation of Stacks 08PA (`functorSituation`). Let `F` be an abelian
sheaf on `C`, `F'` one on `C'` and `t : F' ⟶ g⁻¹F`. Identify `H_n(C, F) = L_nπ_!F` and
`H_n(C', F') = L_nπ'_!F'` (`totalHomologyIso`, `sourceHomologyIso`) and compute homology by the
simplicial replacements of Stacks 08PG (`categoryHomologyReplacementIso`). Then `H^{-n}` of the
canonical map `Lπ'_!F' ⟶ Lπ_!F` of Remark 08PD is the map induced on homology by the chain map
`K_•(F') ⟶ K_•(F)`, `(U'_n → … → U'_0, s') ↦ (f(U'_n) → … → f(U'_0), t(s'))`
(`replacementChainMap`). -/
@[stacks 08PH "the maps of Remark 08PD come from the displayed chain map K(F') → K(F)"]
theorem map_homologyFunctor_map_canonicalDerivedLowerShriekMap'_eq_homologyMap
    (F : Sheaf (functorSituation.{w} C C' f B).totalTopology AddCommGrpCat.{max w u u'}) (F' :
        Sheaf (functorSituation.{w} C C' f B).sourceTopology AddCommGrpCat.{max w u u'})
    (t : F' ⟶ (functorSituation.{w} C C' f B).abelianInverseImage.obj F) (n : ℕ) :
    (pointSheafEquiv.{max u u'} AddCommGrpCat.{max w u u'}
        (K := (functorSituation.{w} C C' f B).base.J) rfl).functor.map
            ((DerivedCategory.homologyFunctor (Sheaf (functorSituation.{w} C C' f B).base.J
        AddCommGrpCat.{max w u u'}) (-(n : ℤ))).map ((functorSituation.{w} C C' f
            B).canonicalDerivedLowerShriekMap' F F' t)) =
      (sourceHomologyIso f B F' n ≪≫ categoryHomologyReplacementIso.{u', max u w} F'.obj n).hom ≫
        HomologicalComplex.homologyMap
          (replacementChainMap.{u, u', w} f (t.hom : F'.obj ⟶ f.op ⋙ F.obj)) n ≫
        (totalHomologyIso f B F n ≪≫ categoryHomologyReplacementIso.{u, max u' w} F.obj n).inv := by
  have h := (Iso.eq_inv_comp _).2 (replacementChainMap_homologyMap.{u, u', w} f
    (t.hom : F'.obj ⟶ f.op ⋙ F.obj) n)
  exact (map_homologyFunctor_map_canonicalDerivedLowerShriekMap' f B F F' t n).trans
    (hom_comp_comp_inv_eq_trans _ _ _ _ _ _ h)

end Bridge

end Stacks.ChaoticSite

end
