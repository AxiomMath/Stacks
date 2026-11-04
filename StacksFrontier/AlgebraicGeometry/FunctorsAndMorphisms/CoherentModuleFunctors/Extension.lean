module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Presentable.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimitSections
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
public import StacksFrontier.CategoryTheory.KanExtension.Extend
public import StacksFrontier.Topology.Sheaves.Limits.SpectralCovers
public import StacksFrontier.Topology.Sheaves.Modules.Coherent

/-!
# Extending a functor from the coherent to the quasi-coherent modules

Let `X` and `Y` be schemes with `X` Noetherian. A functor `Coh(𝒪_X) ⥤ Coh(𝒪_Y)` extends to a
functor `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` which commutes with filtered colimits, and that extension is
unique up to a unique natural isomorphism compatible with the chosen identification on the
coherent modules. The extension is the left Kan extension along the inclusion
`Coh(𝒪_X) ⥤ QCoh(𝒪_X)`, which is a dense family of finitely presentable objects because `X` is
Noetherian.

## Main definitions

* `AlgebraicGeometry.CoherentModuleFunctors.coherentToQuasicoherent` is the inclusion
  `Coh(𝒪_X) ⥤ QCoh(𝒪_X)`.
* `AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension` packages such an extension
  together with its identification on the coherent modules.

## Main results

* `AlgebraicGeometry.CoherentModuleFunctors.isFinitelyPresentable_of_isCoherent`: on a Noetherian
  scheme a coherent module is a finitely presentable object of `QCoh(𝒪_X)`.
* `AlgebraicGeometry.CoherentModuleFunctors.coherentProperty_ind`: on a Noetherian scheme every
  quasi-coherent module is a filtered colimit of coherent ones.
* `AlgebraicGeometry.CoherentModuleFunctors.filteredColimitExtension` constructs the extension.
* `AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension.existsUnique_iso` is the
  uniqueness statement.

## Implementation notes

Coherence is read both as the category `Coh(𝒪_X)` of coherent `𝒪_X`-modules and as the property
`coherentProperty` of objects of `QCoh(𝒪_X)`; the two presentations are compared by an
equivalence of categories, which is how the general Kan extension theorem over a property of
objects is applied. The restriction condition is recorded
as a natural isomorphism after the two inclusions of the coherent modules, and uniqueness is
relative to that specified identification. Only `X` has to be Noetherian, so the statement is
recorded in that stronger form. Both module categories live over the scheme universe, and
preservation is stated explicitly for filtered diagrams in that universe.

## References

* [Stacks Project, Tag 0FZL](https://stacks.math.columbia.edu/tag/0FZL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SheafOfModules (CoherentModules)

universe u

namespace AlgebraicGeometry.CoherentModuleFunctors

/-! ### The inclusion of the coherent modules -/

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` of the coherent `𝒪_X`-modules into the quasi-coherent
ones, available because a coherent module is quasi-coherent. -/
def coherentToQuasicoherent (X : Scheme.{u}) :
    CoherentModules X.ringCatSheaf ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.ιOfLE fun M hM =>
    have : M.IsCoherent := hM
    isQuasicoherent_of_isCoherent M

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` is full. -/
instance full_coherentToQuasicoherent (X : Scheme.{u}) :
    (coherentToQuasicoherent X).Full :=
  ObjectProperty.full_ιOfLE _

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` is faithful. -/
instance faithful_coherentToQuasicoherent (X : Scheme.{u}) :
    (coherentToQuasicoherent X).Faithful :=
  ObjectProperty.faithful_ιOfLE _

/-- Coherence, read as a property of objects of the category `QCoh(𝒪_X)` of quasi-coherent
`𝒪_X`-modules. -/
abbrev coherentProperty (X : Scheme.{u}) :
    ObjectProperty (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  fun M => M.obj.IsCoherent

/-! ### Finite presentability of the coherent modules -/

/-- An object of a full subcategory whose inclusion commutes with filtered colimits is finitely
presentable as soon as the underlying object is. -/
private lemma isFinitelyPresentable_fullSubcategory {C : Type (u + 1)} [Category.{u} C]
    {P : ObjectProperty C} [PreservesFilteredColimitsOfSize.{u, u} P.ι]
    (M : P.FullSubcategory) (hM : IsFinitelyPresentable.{u} M.obj) :
    IsFinitelyPresentable.{u} M := by
  have hbase :=
    (isFinitelyPresentable_iff_preservesFilteredColimitsOfSize (X := M.obj)).mp hM
  have hiso : coyoneda.obj (op M) ≅ P.ι ⋙ coyoneda.obj (op M.obj) :=
    NatIso.ofComponents
      (fun N => Equiv.toIso (by
        show (M ⟶ N) ≃ (M.obj ⟶ N.obj)
        exact P.fullyFaithfulι.homEquiv (X := M) (Y := N)))
      (by intros; ext h; rfl)
  refine isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr ⟨fun J _ _ => ?_⟩
  have : PreservesColimitsOfShape J P.ι :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  have : PreservesColimitsOfShape J (coyoneda.obj (op M.obj)) :=
    hbase.preserves_filtered_colimits J
  exact preservesColimitsOfShape_of_natIso hiso.symm

/-- The inclusion of the quasi-coherent `𝒪_X`-modules into all `𝒪_X`-modules commutes with
filtered colimits, being a left adjoint. -/
lemma preservesFilteredColimitsOfSize_quasicoherentι (X : Scheme.{u}) :
    PreservesFilteredColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι := by
  have := quasicoherentInclusion_isLeftAdjoint X
  exact ⟨fun J _ _ => inferInstance⟩

/-- On a Noetherian scheme every open has a cofinal system of finite open coverings with
quasi-compact pairwise intersections. -/
private lemma hasFiniteCompactCofinalCovers_top (X : Scheme.{u}) [IsNoetherian X] :
    DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := (X : TopCat.{u})) ⊤ :=
  hasFiniteCompactCofinalCovers_of_isCompact ⊤
    (inferInstance : IsNoetherian X).toCompactSpace.isCompact_univ

/-- On a Noetherian scheme a coherent `𝒪_X`-module is a finitely presentable object of all
`𝒪_X`-modules: it is of finite presentation, and morphisms out of a module of finite
presentation commute with filtered colimits. -/
lemma isFinitelyPresentable_of_isCoherent_obj (X : Scheme.{u}) [IsNoetherian X]
    (M : SheafOfModules.{u} X.ringCatSheaf) (hM : M.IsCoherent) :
    IsFinitelyPresentable.{u} M := by
  have : M.IsFinitePresentation := isFinitePresentation_of_isCoherent M
  refine isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr ⟨fun J _ _ => ?_⟩
  exact Stacks.SheafOfModules.preservesColimitsOfShape_coyoneda_of_isFinitePresentation
    X.sheaf M J (hasFiniteCompactCofinalCovers_top X)

/-- **On a Noetherian scheme a coherent module is a finitely presentable object of
`QCoh(𝒪_X)`.** -/
lemma isFinitelyPresentable_of_isCoherent (X : Scheme.{u}) [IsNoetherian X]
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hM : M.obj.IsCoherent) : IsFinitelyPresentable.{u} M :=
  have := preservesFilteredColimitsOfSize_quasicoherentι X
  isFinitelyPresentable_fullSubcategory M (isFinitelyPresentable_of_isCoherent_obj X M.obj hM)

/-! ### The two presentations of the coherent modules -/

/-- The coherent objects of `QCoh(𝒪_X)` are the coherent `𝒪_X`-modules: both sides are the
coherent `𝒪_X`-modules with all `𝒪_X`-module morphisms between them. -/
def coherentSubcategoryEquivalence (X : Scheme.{u}) :
    (coherentProperty X).FullSubcategory ≌
      CoherentModules X.ringCatSheaf where
  functor :=
    { obj := fun M => ⟨M.obj.obj, M.property⟩
      map := fun f => ObjectProperty.homMk f.hom.hom }
  inverse :=
    { obj := fun M => ⟨(coherentToQuasicoherent X).obj M, M.property⟩
      map := fun f => ObjectProperty.homMk ((coherentToQuasicoherent X).map f) }
  unitIso := NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (Iso.refl M.obj))
    (fun _ => ObjectProperty.hom_ext _ rfl)
  counitIso := NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (Iso.refl M.obj))
    (fun _ => ObjectProperty.hom_ext _ rfl)
  functor_unitIso_comp := fun _ => ObjectProperty.hom_ext _ rfl

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` is the inclusion of the coherent objects of
`QCoh(𝒪_X)` read through `coherentSubcategoryEquivalence`. -/
def coherentSubcategoryInclusionIso (X : Scheme.{u}) :
    coherentToQuasicoherent X ≅
      (coherentSubcategoryEquivalence X).inverse ⋙ (coherentProperty X).ι :=
  NatIso.ofComponents
    (fun M => (SheafOfModules.isQuasicoherent X.ringCatSheaf).isoMk
      (Iso.refl ((coherentToQuasicoherent X).obj M).obj))
    (fun _ => ObjectProperty.hom_ext _ rfl)

/-- The inclusion of the coherent objects of `QCoh(𝒪_X)` is the inclusion
`Coh(𝒪_X) ⥤ QCoh(𝒪_X)` read through `coherentSubcategoryEquivalence`. -/
def coherentSubcategoryForwardIso (X : Scheme.{u}) :
    (coherentSubcategoryEquivalence X).functor ⋙ coherentToQuasicoherent X ≅
      (coherentProperty X).ι :=
  NatIso.ofComponents
    (fun M => (SheafOfModules.isQuasicoherent X.ringCatSheaf).isoMk
      (Iso.refl (((coherentSubcategoryEquivalence X).functor ⋙
        coherentToQuasicoherent X).obj M).obj))
    (fun _ => ObjectProperty.hom_ext _ rfl)

/-- On a locally Noetherian scheme the coherent objects of `QCoh(𝒪_X)` form an essentially small
category: a coherent module is of finite type, and the modules of finite type on a ringed space
have only a set of isomorphism classes. -/
lemma essentiallySmall_coherentProperty (X : Scheme.{u}) [IsLocallyNoetherian X] :
    EssentiallySmall.{u} (coherentProperty X).FullSubcategory := by
  have hft : ObjectProperty.EssentiallySmall.{u}
      (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsFiniteType) :=
    Stacks.SheafOfModules.essentiallySmall_isFiniteType
      X.toLocallyRingedSpace.toRingedSpace
  have hle : (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent) ≤
      fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsFiniteType := by
    intro M hM
    have h := ((Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae X M).out 1 2).mp hM
    exact h.2
  have hcoh : ObjectProperty.EssentiallySmall.{u}
      (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent) :=
    ObjectProperty.EssentiallySmall.of_le hle
  have hCoh : EssentiallySmall.{u} (CoherentModules X.ringCatSheaf) := by
    show EssentiallySmall.{u}
      (ObjectProperty.FullSubcategory
        (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent))
    infer_instance
  exact (essentiallySmall_congr (coherentSubcategoryEquivalence X)).2 hCoh

/-! ### Quasi-coherent modules as filtered colimits of coherent modules -/

/-- **On a Noetherian scheme every quasi-coherent module is a filtered colimit of coherent
modules**: it is the filtered colimit of its quasi-coherent submodules of finite type, and on a
Noetherian scheme those are coherent. -/
lemma coherentProperty_ind (X : Scheme.{u}) [IsNoetherian X]
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (coherentProperty X).ind.{u} M := by
  let M₀ : X.Modules := M.obj
  let Jbig := FiniteTypeQuasicoherentSubobject M₀
  have : Small.{u} Jbig :=
    small_of_injective (f := fun j : Jbig => j.obj)
      (fun _ _ h => ObjectProperty.FullSubcategory.ext h)
  have : IsFiltered Jbig := finiteTypeQuasicoherentSubobject_isFiltered M₀
  have : EssentiallySmall.{u} Jbig := essentiallySmall_of_small_of_locallySmall Jbig
  let e := equivSmallModel Jbig
  let J := SmallModel Jbig
  have : IsFiltered J := IsFiltered.of_equivalence e
  let D₀ := e.inverse ⋙ finiteTypeQuasicoherentSubobjectFunctor M₀
  let c₀ := (finiteTypeQuasicoherentSubobjectCocone M₀).whisker e.inverse
  have hc₀ : IsColimit c₀ :=
    (Functor.Final.isColimitWhiskerEquiv e.inverse _).symm
      (isColimit_finiteTypeQuasicoherentSubobjectCocone M₀)
  let D : J ⥤ (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).lift D₀
      fun j => (e.inverse.obj j).property.1
  have hcoh (j : J) : (D.obj j).obj.IsCoherent :=
    ((Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae X (D₀.obj j)).out 2 1).mp
      (e.inverse.obj j).property
  let c : Cocone D :=
    { pt := M
      ι :=
        { app := fun j => ObjectProperty.homMk (c₀.ι.app j)
          naturality := fun _ _ f => ObjectProperty.hom_ext _ (c₀.ι.naturality f) } }
  have hc : IsColimit c := by
    have : CreatesColimitsOfShape J (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
      createsColimitsOfShapeFullSubcategoryInclusion J _
    exact isColimitOfReflects (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι <|
      IsColimit.ofIsoColimit hc₀ (Cocone.ext (Iso.refl _) (fun _ => rfl))
  exact ⟨J, inferInstance, inferInstance, ⟨D, c.ι, hc⟩, hcoh⟩

/-! ### The extension -/

/-- A filtered-colimit-preserving extension to the quasi-coherent modules of a functor between
categories of coherent modules. -/
structure FilteredColimitExtension (X Y : Scheme.{u})
    (F : CoherentModules X.ringCatSheaf ⥤
      CoherentModules Y.ringCatSheaf) where
  /-- The extended functor on quasi-coherent modules. -/
  functor : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory
  /-- The extended functor commutes with filtered colimits. -/
  preservesFilteredColimits : PreservesFilteredColimitsOfSize.{u, u} functor
  /-- The restriction of the extended functor to the coherent modules agrees with the original
  functor. -/
  iso : coherentToQuasicoherent X ⋙ functor ≅ F ⋙ coherentToQuasicoherent Y

/-- The functor underlying an extension preserves filtered colimits. -/
instance FilteredColimitExtension.instPreservesFilteredColimitsOfSize {X Y : Scheme.{u}}
    {F : CoherentModules X.ringCatSheaf ⥤
      CoherentModules Y.ringCatSheaf}
    (E : FilteredColimitExtension X Y F) :
    PreservesFilteredColimitsOfSize.{u, u} E.functor :=
  E.preservesFilteredColimits

section Uniqueness

variable {X Y : Scheme.{u}}
  {F : CoherentModules X.ringCatSheaf ⥤
    CoherentModules Y.ringCatSheaf}

/-- The restriction of an extension to the coherent objects of `QCoh(𝒪_X)`, identified with the
original functor through `coherentSubcategoryEquivalence`. -/
private def restrictionIso (E : FilteredColimitExtension X Y F) :
    (coherentProperty X).ι ⋙ E.functor ≅
      (coherentSubcategoryEquivalence X).functor ⋙ (F ⋙ coherentToQuasicoherent Y) :=
  Functor.isoWhiskerRight (coherentSubcategoryForwardIso X).symm E.functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (coherentSubcategoryEquivalence X).functor E.iso

/-- The comparison of two restrictions at a coherent object of `QCoh(𝒪_X)` is the comparison of
the two extensions at the corresponding coherent module, conjugated by the inclusions. -/
private lemma restrictionIso_trans_symm_hom_app (E₁ E₂ : FilteredColimitExtension X Y F)
    (A : (coherentProperty X).FullSubcategory) :
    ((restrictionIso E₁).trans (restrictionIso E₂).symm).hom.app A =
      E₁.functor.map ((coherentSubcategoryForwardIso X).app A).inv ≫
        (E₁.iso.trans E₂.iso.symm).hom.app
          ((coherentSubcategoryEquivalence X).functor.obj A) ≫
        E₂.functor.map ((coherentSubcategoryForwardIso X).app A).hom := by
  simp [restrictionIso, Functor.isoWhiskerRight, Functor.isoWhiskerLeft, Category.assoc]

/-- Two natural transformations of functors which agree at an object agree at every isomorphic
object, as soon as the prescribed values are compatible with the isomorphism. -/
private lemma natTrans_app_eq_of_iso {C D : Type*} [Category C] [Category D]
    {G₁ G₂ : C ⥤ D} (n : G₁ ⟶ G₂) {P Q : C} (k : P ≅ Q)
    {γP : G₁.obj P ⟶ G₂.obj P} {γQ : G₁.obj Q ⟶ G₂.obj Q}
    (hP : n.app P = γP) (hk : G₁.map k.hom ≫ γQ = γP ≫ G₂.map k.hom) :
    n.app Q = γQ := by
  refine (cancel_epi (G₁.map k.hom)).1 ?_
  rw [n.naturality k.hom, hP, hk]

/-- The identification of a coherent module, included into `QCoh(𝒪_X)`, with the corresponding
coherent object of `QCoh(𝒪_X)`. -/
private def coherentCounitIso (X : Scheme.{u}) (M : CoherentModules X.ringCatSheaf) :
    (coherentProperty X).ι.obj ((coherentSubcategoryEquivalence X).inverse.obj M) ≅
      (coherentToQuasicoherent X).obj M :=
  ((coherentSubcategoryForwardIso X).app
      ((coherentSubcategoryEquivalence X).inverse.obj M)).symm ≪≫
    (coherentToQuasicoherent X).mapIso
      ((coherentSubcategoryEquivalence X).counitIso.app M)

/-- Conjugating a morphism by an isomorphism and then composing with its inverse recovers the
original morphism. -/
private lemma conjugate_hom_comp {C D : Type*} [Category C] [Category D] {G₁ G₂ : C ⥤ D}
    {T P : C} (q : T ≅ P) {βT : G₁.obj T ⟶ G₂.obj T} {γP : G₁.obj P ⟶ G₂.obj P}
    (hγ : γP = G₁.map q.inv ≫ βT ≫ G₂.map q.hom) :
    G₁.map q.hom ≫ γP = βT ≫ G₂.map q.hom := by
  rw [hγ, ← Category.assoc, ← Functor.map_comp, q.hom_inv_id, G₁.map_id, Category.id_comp]

/-- A morphism conjugated by an isomorphism stays compatible with a naturality square after
composing the isomorphism with a further morphism. -/
private lemma conjugate_comp {C D : Type*} [Category C] [Category D] {G₁ G₂ : C ⥤ D}
    {T P Q : C} (q : T ≅ P) (cm : T ⟶ Q)
    {βT : G₁.obj T ⟶ G₂.obj T} {βQ : G₁.obj Q ⟶ G₂.obj Q}
    (hβ : G₁.map cm ≫ βQ = βT ≫ G₂.map cm)
    {γP : G₁.obj P ⟶ G₂.obj P} (hγ : γP = G₁.map q.inv ≫ βT ≫ G₂.map q.hom) :
    G₁.map (q.inv ≫ cm) ≫ βQ = γP ≫ G₂.map (q.inv ≫ cm) := by
  rw [hγ, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (G₂.map q.hom), ← Functor.map_comp, q.hom_inv_id, G₂.map_id,
    Category.id_comp, hβ]

/-- Compatibility with the identifications on the coherent modules follows from compatibility
with the identifications on the coherent objects of `QCoh(𝒪_X)`. -/
private theorem whiskerLeft_coherentToQuasicoherent_of_whiskerLeft_ι
    (E₁ E₂ : FilteredColimitExtension X Y F) (e : E₁.functor ≅ E₂.functor)
    (he : Functor.whiskerLeft (coherentProperty X).ι e.hom =
      ((restrictionIso E₁).trans (restrictionIso E₂).symm).hom) :
    Functor.whiskerLeft (coherentToQuasicoherent X) e.hom =
      (E₁.iso.trans E₂.iso.symm).hom :=
  NatTrans.ext <| funext fun M =>
    natTrans_app_eq_of_iso e.hom (coherentCounitIso X M)
      (congrArg (fun τ => τ.app ((coherentSubcategoryEquivalence X).inverse.obj M)) he)
      (conjugate_comp
        ((coherentSubcategoryForwardIso X).app
          ((coherentSubcategoryEquivalence X).inverse.obj M))
        ((coherentToQuasicoherent X).map
          ((coherentSubcategoryEquivalence X).counitIso.app M).hom)
        ((E₁.iso.trans E₂.iso.symm).hom.naturality
          ((coherentSubcategoryEquivalence X).counitIso.app M).hom)
        (restrictionIso_trans_symm_hom_app E₁ E₂
          ((coherentSubcategoryEquivalence X).inverse.obj M)))

/-- Compatibility with the identifications on the coherent objects of `QCoh(𝒪_X)` follows from
compatibility with the identifications on the coherent modules. -/
private theorem whiskerLeft_ι_of_whiskerLeft_coherentToQuasicoherent
    (E₁ E₂ : FilteredColimitExtension X Y F) (e : E₁.functor ≅ E₂.functor)
    (he : Functor.whiskerLeft (coherentToQuasicoherent X) e.hom =
      (E₁.iso.trans E₂.iso.symm).hom) :
    Functor.whiskerLeft (coherentProperty X).ι e.hom =
      ((restrictionIso E₁).trans (restrictionIso E₂).symm).hom :=
  NatTrans.ext <| funext fun A =>
    natTrans_app_eq_of_iso e.hom ((coherentSubcategoryForwardIso X).app A)
      (congrArg (fun τ => τ.app ((coherentSubcategoryEquivalence X).functor.obj A)) he)
      (conjugate_hom_comp _ (restrictionIso_trans_symm_hom_app E₁ E₂ A))

end Uniqueness

/-- **Stacks Project, Tag 0FZL.** A functor from the coherent modules on a Noetherian scheme to
the coherent modules on a scheme extends to a functor on quasi-coherent modules which commutes
with filtered colimits. -/
@[stacks 0FZL "extension"]
noncomputable def filteredColimitExtension (X Y : Scheme.{u}) [IsNoetherian X]
    (F : CoherentModules X.ringCatSheaf ⥤
      CoherentModules Y.ringCatSheaf) :
    FilteredColimitExtension X Y F := by
  have : EssentiallySmall.{u} (coherentProperty X).FullSubcategory :=
    essentiallySmall_coherentProperty X
  have hcompact : coherentProperty X ≤
      ObjectProperty.isFinitelyPresentable.{u}
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    fun M hM => isFinitelyPresentable_of_isCoherent X M hM
  have hExt := ObjectProperty.exists_extension_of_preservesFilteredColimits
    (coherentProperty X) hcompact (coherentProperty_ind X)
    ((coherentSubcategoryEquivalence X).functor ⋙ (F ⋙ coherentToQuasicoherent Y))
  exact ⟨Classical.choose hExt, (Classical.choose_spec hExt).1,
    Functor.isoWhiskerRight (coherentSubcategoryInclusionIso X) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (coherentSubcategoryEquivalence X).inverse
        (Classical.choice (Classical.choose_spec hExt).2) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (coherentSubcategoryEquivalence X).counitIso
        (F ⋙ coherentToQuasicoherent Y) ≪≫
      Functor.leftUnitor _⟩

/-- **Stacks Project, Tag 0FZL.** Two filtered-colimit-preserving extensions are related by a
unique natural isomorphism compatible with their specified identifications on the coherent
modules. -/
@[stacks 0FZL "extension"]
theorem FilteredColimitExtension.existsUnique_iso {X Y : Scheme.{u}} [IsNoetherian X]
    {F : CoherentModules X.ringCatSheaf ⥤
      CoherentModules Y.ringCatSheaf}
    (E₁ E₂ : FilteredColimitExtension X Y F) :
    ∃! e : E₁.functor ≅ E₂.functor,
      Functor.whiskerLeft (coherentToQuasicoherent X) e.hom =
        (E₁.iso.trans E₂.iso.symm).hom := by
  have : EssentiallySmall.{u} (coherentProperty X).FullSubcategory :=
    essentiallySmall_coherentProperty X
  have hcompact : coherentProperty X ≤
      ObjectProperty.isFinitelyPresentable.{u}
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    fun M hM => isFinitelyPresentable_of_isCoherent X M hM
  obtain ⟨e, he, hu⟩ :=
    ObjectProperty.existsUnique_iso_of_preservesFilteredColimits
      (coherentProperty X) hcompact (coherentProperty_ind X)
      E₁.functor E₂.functor (restrictionIso E₁) (restrictionIso E₂)
  exact ⟨e, whiskerLeft_coherentToQuasicoherent_of_whiskerLeft_ι E₁ E₂ e he, fun e' he' =>
    hu e' (whiskerLeft_ι_of_whiskerLeft_coherentToQuasicoherent E₁ E₂ e' he')⟩

end AlgebraicGeometry.CoherentModuleFunctors
