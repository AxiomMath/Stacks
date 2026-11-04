module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeIsoModel
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenComplexModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens

/-!
# Naturality of the restriction of the derived internal Hom to opens of a scheme

The comparisons `Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso` (along an isomorphism of
schemes), `Stacks.SheafOfModules.derivedSheafHomSchemeOpenIso` (from the slice site to the open
subscheme) and `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso` ([Stacks, Tag 08DL]
for an open subscheme) are natural in the contravariant variable.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso_natural_left`
* `Stacks.SheafOfModules.derivedSheafHomSchemeOpenIso_natural_left`
* `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso_natural_left`

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The transport of the derived internal Hom along an isomorphism of schemes is natural in the
first variable. -/
theorem derivedSheafHomSchemeIsoIso_natural_left {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g]
    {K K' : DerivedCategory (StructureSheafModules B.sheaf)}
    (L : DerivedCategory (StructureSheafModules B.sheaf)) (k : K' ⟶ K) :
    (Scheme.Modules.restrictFunctor g).mapDerivedCategory.map
        (((RingedSite.derivedSheafHomBifunctor (ringedSite B.sheaf)).map k.op).app L) ≫
      (derivedSheafHomSchemeIsoIso g K' L).hom =
    (derivedSheafHomSchemeIsoIso g K L).hom ≫
      ((RingedSite.derivedSheafHomBifunctor (ringedSite A.sheaf)).map
        ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.map k).op).app
          ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj L) :=
  RingedSite.siteEquivDerivedSheafHomIsoOfIso_natural_left
    (X := ringedSite B.sheaf) (Y := ringedSite A.sheaf)
    (schemeIsoOpensEquivalence g) (schemeIsoPhi g) (hφ := isIso_schemeIsoPhi g)
    (hlim := RingedSite.pushforward_preservesFiniteLimitsOfIso
      (schemeIsoOpensEquivalence g) (schemeIsoPhi g))
    (hcolim := RingedSite.pushforward_preservesFiniteColimitsOfIso
      (schemeIsoOpensEquivalence g) (schemeIsoPhi g)) L k

/-- The transport of the derived internal Hom from the slice site over `U` to the open
subscheme `U` is natural in the first variable. -/
theorem derivedSheafHomSchemeOpenIso_natural_left {S : Scheme.{u}} (U : S.Opens)
    {K K' : DerivedCategory (_root_.SheafOfModules.{u} (S.ringCatSheaf.over U))}
    (L : DerivedCategory (_root_.SheafOfModules.{u} (S.ringCatSheaf.over U))) (k : K' ⟶ K) :
    ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.map
        (((RingedSite.derivedSheafHomBifunctor ((ringedSite S.sheaf).over U)).map k.op).app L) ≫
      (derivedSheafHomSchemeOpenIso U K' L).hom =
    (derivedSheafHomSchemeOpenIso U K L).hom ≫
      ((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).map
        (((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.map k).op).app
          (((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.obj L) :=
  RingedSite.siteEquivDerivedSheafHomIsoOfIso_natural_left
    (X := (ringedSite S.sheaf).over U) (Y := ringedSite U.toScheme.sheaf)
    U.overEquivalence.symm (schemeOpenPhi U) (hφ := isIso_schemeOpenPhi U)
    (hlim := inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.overEquiv U).functor))
    (hcolim := inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.overEquiv U).functor))
    L k

/-- Composing commutative squares along a composite of four morphisms. -/
private theorem comp_four_of_squares {C : Type*} [Category C] {P P' Q₁ Q₁' Q₂ Q₂' Q₃ Q₃' R R' : C}
    {r : P ⟶ P'} {a : P ⟶ Q₁} {a' : P' ⟶ Q₁'} {m₁ : Q₁ ⟶ Q₁'} {b : Q₁ ⟶ Q₂} {b' : Q₁' ⟶ Q₂'}
    {m₂ : Q₂ ⟶ Q₂'} {c : Q₂ ⟶ Q₃} {c' : Q₂' ⟶ Q₃'} {d : Q₃ ⟶ R} {d' : Q₃' ⟶ R'} {s : R ⟶ R'}
    (h₁ : r ≫ a' = a ≫ m₁) (h₂ : m₁ ≫ b' = b ≫ m₂) (h₃ : m₂ ≫ c' ≫ d' = c ≫ d ≫ s) :
    r ≫ a' ≫ b' ≫ c' ≫ d' = (a ≫ b ≫ c ≫ d) ≫ s := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

/-- A square in the contravariant variable of a bifunctor, followed by a map in the covariant
variable. -/
private theorem bifunctor_square {C D E : Type*} [Category C] [Category D] [Category E]
    (H : Cᵒᵖ ⥤ D ⥤ E) {P P' Q Q' : C} {m : P' ⟶ P} {e : Q ⟶ P} {e' : Q' ⟶ P'} {q : Q' ⟶ Q}
    (h : e' ≫ m = q ≫ e) {X₀ Y₀ : D} (t : X₀ ⟶ Y₀) :
    (H.map m.op).app X₀ ≫ (H.map e'.op).app X₀ ≫ (H.obj (op Q')).map t =
      (H.map e.op).app X₀ ≫ (H.obj (op Q)).map t ≫ (H.map q.op).app Y₀ := by
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, ← op_comp, h, op_comp, Functor.map_comp,
    NatTrans.comp_app, Category.assoc, NatTrans.naturality]

section Restriction

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {S : Scheme.{u}} (U : S.Opens)
  [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology S).over U) AddCommGrpCat.{u}]
  [PreservesFiniteLimits (_root_.SheafOfModules.overFunctor.{u} S.ringCatSheaf U)]
  [PreservesFiniteColimits (_root_.SheafOfModules.overFunctor.{u} S.ringCatSheaf U)]

/-- **[Stacks, Tag 08DL] for an open subscheme is natural in the first variable.** -/
theorem derivedSheafHomSchemeRestrictionIso_natural_left
    {K K' : DerivedCategory (StructureSheafModules S.sheaf)}
    (L : DerivedCategory (StructureSheafModules S.sheaf)) (k : K' ⟶ K) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map
        (((RingedSite.derivedSheafHomBifunctor (ringedSite S.sheaf)).map k.op).app L) ≫
      (derivedSheafHomSchemeRestrictionIso U K' L).hom =
    (derivedSheafHomSchemeRestrictionIso U K L).hom ≫
      ((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).map
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map k).op).app
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj L) := by
  have h1 := derivedSheafHomSchemeRestriction_natural_left U (L := L) k
  have h2 := derivedSheafHomSchemeOpenIso_natural_left U ((derivedRestrict S.sheaf U).obj L)
    ((derivedRestrict S.sheaf U).map k)
  have h3 : ((derivedOverFunctorEquiv U).app K').inv ≫
      ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.map
        ((derivedRestrict S.sheaf U).map k) =
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map k ≫
        ((derivedOverFunctorEquiv U).app K).inv :=
    ((derivedOverFunctorEquiv U).inv.naturality k).symm
  exact comp_four_of_squares h1 h2 (bifunctor_square _ h3 _)

end Restriction

/-! ### Restriction along an open immersion -/

section OpenImmersion

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]

/-- Restriction along an open immersion `j` is restriction to the open `j(X)` followed by
restriction along the isomorphism `X ≅ j(X)`, on derived categories. -/
def derivedRestrictFactorIso :
    (Scheme.Modules.restrictFunctor j).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor j.opensRange.ι).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor j.isoOpensRange.hom).mapDerivedCategory :=
  Stacks.DerivedGlueing.mapDerivedCategoryCongr
      (Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoOpensRange_hom_ι j).symm ≪≫
        Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι) ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCompIso _ _).symm

/-- [Stacks, Tag 08DL] for an open subscheme, as an isomorphism of functors of the first
variable. -/
def derivedSheafHomSchemeRestrictionNatIso {S : Scheme.{u}} (U : S.Opens)
    (L : DerivedCategory (StructureSheafModules S.sheaf)) :
    (RingedSite.derivedSheafHomBifunctor (ringedSite S.sheaf)).flip.obj L ⋙
        (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.op ⋙
        (RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).flip.obj
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj L) :=
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := S.ringCatSheaf) U
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := S.ringCatSheaf) U
  NatIso.ofComponents (fun K => derivedSheafHomSchemeRestrictionIso U K.unop L)
    (fun k => derivedSheafHomSchemeRestrictionIso_natural_left U L k.unop)

/-- The transport of the derived internal Hom along an isomorphism of schemes, as an isomorphism
of functors of the first variable. -/
def derivedSheafHomSchemeIsoNatIso {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g]
    (L : DerivedCategory (StructureSheafModules B.sheaf)) :
    (RingedSite.derivedSheafHomBifunctor (ringedSite B.sheaf)).flip.obj L ⋙
        (Scheme.Modules.restrictFunctor g).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor g).mapDerivedCategory.op ⋙
        (RingedSite.derivedSheafHomBifunctor (ringedSite A.sheaf)).flip.obj
          ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj L) :=
  NatIso.ofComponents (fun K => derivedSheafHomSchemeIsoIso g K.unop L)
    (fun k => derivedSheafHomSchemeIsoIso_natural_left g L k.unop)

/-- A natural isomorphism `H(-, L) ⋙ F ≅ F.op ⋙ H'(-, F L)` carried along an isomorphism of
functors `F ≅ F'`. -/
def sheafHomNatIsoCongr {C D : Type*} [Category C] [Category D] (H : Cᵒᵖ ⥤ C ⥤ C)
    (H' : Dᵒᵖ ⥤ D ⥤ D) {F F' : C ⥤ D} (e : F ≅ F') (L : C)
    (i : H.flip.obj L ⋙ F ≅ F.op ⋙ H'.flip.obj (F.obj L)) :
    H.flip.obj L ⋙ F' ≅ F'.op ⋙ H'.flip.obj (F'.obj L) :=
  Functor.isoWhiskerLeft _ e.symm ≪≫ i ≪≫ Functor.isoWhiskerRight (NatIso.op e.symm) _ ≪≫
    Functor.isoWhiskerLeft _ (H'.flip.mapIso (e.app L))

/-- A natural isomorphism `H(-, L) ⋙ F ≅ F.op ⋙ H'(-, F L)` for a composite `F = F₁ ⋙ F₂`. -/
def sheafHomNatIsoComp {C D E : Type*} [Category C] [Category D] [Category E]
    (H : Cᵒᵖ ⥤ C ⥤ C) (H' : Dᵒᵖ ⥤ D ⥤ D) (H'' : Eᵒᵖ ⥤ E ⥤ E) (F₁ : C ⥤ D) (F₂ : D ⥤ E)
    (L : C) (i₁ : H.flip.obj L ⋙ F₁ ≅ F₁.op ⋙ H'.flip.obj (F₁.obj L))
    (i₂ : H'.flip.obj (F₁.obj L) ⋙ F₂ ≅ F₂.op ⋙ H''.flip.obj (F₂.obj (F₁.obj L))) :
    H.flip.obj L ⋙ (F₁ ⋙ F₂) ≅ (F₁ ⋙ F₂).op ⋙ H''.flip.obj ((F₁ ⋙ F₂).obj L) :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight i₁ F₂ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F₁.op i₂ ≪≫ (Functor.associator _ _ _).symm

/-- **The derived internal Hom commutes with restriction along an open immersion**
([Stacks, Tag 08DL]), as an isomorphism of functors of the first variable:
`R𝓗om_{𝒪_Z}(K, L)|_X ≅ R𝓗om_{𝒪_X}(K|_X, L|_X)`, naturally in `K`. -/
def derivedSheafHomOpenImmersionIso (L : DerivedCategory (StructureSheafModules Z.sheaf)) :
    (RingedSite.derivedSheafHomBifunctor (ringedSite Z.sheaf)).flip.obj L ⋙
        (Scheme.Modules.restrictFunctor j).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.op ⋙
        (RingedSite.derivedSheafHomBifunctor (ringedSite X.sheaf)).flip.obj
          ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj L) :=
  sheafHomNatIsoCongr _ _ (derivedRestrictFactorIso j).symm L
    (sheafHomNatIsoComp _ _ _ _ _ L (derivedSheafHomSchemeRestrictionNatIso j.opensRange L)
      (derivedSheafHomSchemeIsoNatIso j.isoOpensRange.hom _))

end OpenImmersion

end Stacks.SheafOfModules

end
