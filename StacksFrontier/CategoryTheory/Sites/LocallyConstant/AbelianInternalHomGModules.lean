module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.GModuleInternalHom

/-!
# The internal Hom of finite locally constant abelian sheaves and of finite `G`-modules

Let `(C, J)` be a site, `G` a topological group and `e` an equivalence of the finite locally
constant sheaves of sets on `C` with the finite continuous `G`-sets. Through the transport of
commutative group objects
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence` `e` attaches a
finite discrete `G`-module `E 𝒢` to every finite locally constant abelian sheaf `𝒢`. This file
proves that if the internal Hom `ℋom(𝒢, ℱ)` of two such sheaves is again finite locally constant,
then `E ℋom(𝒢, ℱ) ≅ Hom_ℤ(E 𝒢, E ℱ)`, the latter with the conjugation action.

The argument is Yoneda's, carried out on the underlying sets, where `e` acts. For a finite
locally constant sheaf of sets `T`, a morphism `T ⟶ ℋom(𝒢, ℱ)` is a pairing `T × 𝒢 ⟶ ℱ` additive in
`𝒢` (`Stacks.ConstantSheaf.internalHomPresheafPairingEquiv`); additivity in `𝒢` is
multiplicativity in the second variable for the commutative group objects underlying `𝒢` and `ℱ`
(`CategoryTheory.IsMulRight`), which `e` preserves because it preserves products
(`CategoryTheory.Functor.FullyFaithful.mulRightEquiv`); and on the side of `G`-sets such pairings
are the morphisms into `Hom_ℤ(E 𝒢, E ℱ)` (`CategoryTheory.ContinuousGAddCommGrp.homPairingEquiv`).

## Main definitions

* `Stacks.ConstantSheaf.setCommGrp`: the commutative group object among finite locally constant
  sheaves of sets underlying a finite locally constant abelian sheaf.
* `Stacks.ConstantSheaf.mulRightPairingEquiv`: pairings multiplicative in the second variable for
  these group objects are pairings of presheaves additive in the second variable.
* `Stacks.ConstantSheaf.internalHomTransportIso`: `E ℋom(𝒢, ℱ) ≅ Hom_ℤ(E 𝒢, E ℱ)` when
  `ℋom(𝒢, ℱ)` is finite locally constant.

## Main results

* `Stacks.ConstantSheaf.internalHomTransportIso_naturality`: the isomorphism
  `internalHomTransportIso` is natural in `𝒢`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
  MonObj

open scoped CategoryTheory.Obj

universe v u u' w

attribute [local instance] cartesianMonoidalContinuousGSet braidedContinuousGSet
  cartesianMonoidalSheafType braidedSheafType discreteForget₂Type discreteForget₂AddCommGrpCat
  CategoryTheory.braidedContinuousGSetIsFinite CategoryTheory.braidedι_continuousGSetIsFinite
  Stacks.ConstantSheaf.braidedFiniteLocallyConstantSetSheaf
  Stacks.ConstantSheaf.braidedι_finiteLocallyConstantSetSheaf

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]

/-- The inclusion of sheaves of sets into presheaves of sets is braided for the cartesian monoidal
structures. -/
local instance : (sheafToPresheaf J (Type (max u v))).Braided := .ofChosenFiniteProducts _

/-- **The commutative group object of finite locally constant sheaves of sets underlying a finite
locally constant abelian sheaf**: the internal group of the abelian sheaf, read inside the full
subcategory. -/
abbrev setCommGrp (𝒢 : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory) :
    CommGrp (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory :=
  (isFiniteLocallyConstantSetSheaf.{v, u, u} J).commGrpEquivalence.inverse.obj
    (((Sites.AbelianSheaf.equivalence J).congrFullSubcategory
      (commGrpProp_inverseImage_internalSheaf J)).functor.obj 𝒢)

/-- **The multiplication of `setCommGrp`, read on presheaves, is the sectionwise addition** of
the abelian sheaf. -/
lemma mul_sheafToPresheaf_ι_setCommGrp
    (𝒢 : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory) :
    MonObj.mul (X := (sheafToPresheaf J (Type (max u v))).obj
        ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.obj (setCommGrp J 𝒢).X)) =
      (Sites.AbelianSheaf.presheafGrpObj 𝒢.obj.obj).mul := by
  let P := isFiniteLocallyConstantSetSheaf.{v, u, u} J
  let A : P.FullSubcategory := (setCommGrp J 𝒢).X
  let S := sheafToPresheaf J (Type (max u v))
  let R : CommGrp (Sheaf J (Type (max u v))) := Sites.AbelianSheaf.internalSheafObj J 𝒢.obj
  let m₁ : P.ι.obj A ⊗ P.ι.obj A ⟶ P.ι.obj A := @MonObj.mul _ _ _ R.X R.grp.toMonObj
  show Functor.LaxMonoidal.μ S (P.ι.obj A) (P.ι.obj A) ≫
      S.map (Functor.LaxMonoidal.μ P.ι A A ≫
          P.ι.map (P.fullyFaithfulι.preimage (X := A ⊗ A) (Y := A)
            (Functor.OplaxMonoidal.δ P.ι A A ≫ m₁))) = _
  rw [Functor.FullyFaithful.map_preimage, Functor.Monoidal.μ_δ_assoc]
  let m₂ : S.obj (P.ι.obj A) ⊗ S.obj (P.ι.obj A) ⟶ S.obj (P.ι.obj A) :=
    (Sites.AbelianSheaf.presheafGrpObj 𝒢.obj.obj).mul
  show Functor.LaxMonoidal.μ S (P.ι.obj A) (P.ι.obj A) ≫
      S.map ((fullyFaithfulSheafToPresheaf J (Type (max u v))).preimage
          (X := P.ι.obj A ⊗ P.ι.obj A) (Y := P.ι.obj A)
          (Functor.OplaxMonoidal.δ S (P.ι.obj A) (P.ι.obj A) ≫ m₂)) = m₂
  rw [Functor.FullyFaithful.map_preimage, Functor.Monoidal.μ_δ_assoc]

/-- **Pairings multiplicative in the second variable for the group objects of the transport are
pairings of presheaves additive in the second variable.** -/
noncomputable def mulRightPairingEquiv
    (T : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory)
    (𝒢 ℱ : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory) :
    {β : T ⊗ (setCommGrp J 𝒢).X ⟶ (setCommGrp J ℱ).X // IsMulRight β} ≃
      {β' : T.obj.obj ⊗ (𝒢.obj.obj ⋙ forget AddCommGrpCat) ⟶ ℱ.obj.obj ⋙ forget AddCommGrpCat //
        IsAddRightPairing _ _ _ β'} :=
  (((isFiniteLocallyConstantSetSheaf.{v, u, u} J).fullyFaithfulι.mulRightEquiv T _ _).trans
    ((fullyFaithfulSheafToPresheaf J (Type (max u v))).mulRightEquiv _ _ _)).trans
    (Equiv.subtypeEquivRight fun β' ↦
      ((isMulRight_congr _ (Sites.AbelianSheaf.presheafGrpObj 𝒢.obj.obj).toMonObj _
        (Sites.AbelianSheaf.presheafGrpObj ℱ.obj.obj).toMonObj
        (mul_sheafToPresheaf_ι_setCommGrp J 𝒢) (mul_sheafToPresheaf_ι_setCommGrp J ℱ) β').trans
        (isMulRight_iff_isAddRightPairing _ _ _ β')))

/-- The pairing of presheaves attached by `mulRightPairingEquiv` to `β` is the image of `β` under
the inclusion and `sheafToPresheaf`, precomposed with their lax monoidal structure maps. -/
lemma mulRightPairingEquiv_apply
    (T : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory)
    (𝒢 ℱ : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory)
    (β : {β : T ⊗ (setCommGrp J 𝒢).X ⟶ (setCommGrp J ℱ).X // IsMulRight β}) :
    (mulRightPairingEquiv J T 𝒢 ℱ β).1 =
      Functor.LaxMonoidal.μ (sheafToPresheaf J (Type (max u v))) _ _ ≫
        (sheafToPresheaf J (Type (max u v))).map
          (Functor.LaxMonoidal.μ (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι _ _ ≫
            (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.map β.1) :=
  rfl

/-- The transport `β ↦ μ ≫ F'.map (μ ≫ F.map β)` along two fully faithful monoidal functors is
natural in the first variable. -/
private theorem mulRightEquiv_comp_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [CartesianMonoidalCategory E]
    {F : C ⥤ D} {F' : D ⥤ E} [F.Monoidal] [F'.Monoidal] (hF : F.FullyFaithful)
    (hF' : F'.FullyFaithful) {T' T A B : C} [MonObj A] [MonObj B] (h : T' ⟶ T)
    (β : {β : T ⊗ A ⟶ B // IsMulRight β}) :
    (hF'.mulRightEquiv _ _ _ (hF.mulRightEquiv T' A B ⟨h ▷ _ ≫ β.1, β.2.whiskerRight_comp h⟩)).1 =
      F'.map (F.map h) ▷ _ ≫ (hF'.mulRightEquiv _ _ _ (hF.mulRightEquiv T A B β)).1 := by
  rw [show hF.mulRightEquiv T' A B ⟨h ▷ _ ≫ β.1, β.2.whiskerRight_comp h⟩ =
    ⟨F.map h ▷ _ ≫ (hF.mulRightEquiv T A B β).1,
      (hF.mulRightEquiv T A B β).2.whiskerRight_comp _⟩ from
    Subtype.ext (hF.mulRightEquiv_comp h β)]
  exact hF'.mulRightEquiv_comp _ _

/-- The bijection `mulRightPairingEquiv` is natural in the sheaf of sets. -/
lemma mulRightPairingEquiv_comp
    {T' T : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory} (h : T' ⟶ T)
    (𝒢 ℱ : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory)
    (β : {β : T ⊗ (setCommGrp J 𝒢).X ⟶ (setCommGrp J ℱ).X // IsMulRight β}) :
    (mulRightPairingEquiv J T' 𝒢 ℱ ⟨h ▷ _ ≫ β.1, β.2.whiskerRight_comp h⟩).1 =
      h.hom.hom ▷ (𝒢.obj.obj ⋙ forget AddCommGrpCat) ≫ (mulRightPairingEquiv J T 𝒢 ℱ β).1 := by
  exact mulRightEquiv_comp_comp (isFiniteLocallyConstantSetSheaf.{v, u, u} J).fullyFaithfulι
    (fullyFaithfulSheafToPresheaf J (Type (max u v))) h β

/-- For a pairing whose first factor is itself a group object of the transport, multiplicativity in
the first variable is additivity in the first variable of the corresponding pairing of presheaves.
-/
lemma isMulLeft_iff_mulRightPairingEquiv
    (𝒢 ℱ 𝒦 : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory)
    (β : {β : (setCommGrp J 𝒦).X ⊗ (setCommGrp J 𝒢).X ⟶ (setCommGrp J ℱ).X // IsMulRight β}) :
    IsMulLeft β.1 ↔ ∀ (X : Cᵒᵖ) (t t' : 𝒦.obj.obj.obj X) (g : 𝒢.obj.obj.obj X),
      (mulRightPairingEquiv J (setCommGrp J 𝒦).X 𝒢 ℱ β).1.app X (t + t', g) =
        (mulRightPairingEquiv J (setCommGrp J 𝒦).X 𝒢 ℱ β).1.app X (t, g) +
          (mulRightPairingEquiv J (setCommGrp J 𝒦).X 𝒢 ℱ β).1.app X (t', g) := by
  let P := isFiniteLocallyConstantSetSheaf.{v, u, u} J
  rw [← Functor.isMulLeft_μ_comp_map_iff_of_faithful P.ι β.1,
    ← Functor.isMulLeft_μ_comp_map_iff_of_faithful (sheafToPresheaf J (Type (max u v)))]
  exact (isMulLeft_congr _ (Sites.AbelianSheaf.presheafGrpObj 𝒦.obj.obj).toMonObj _
    (Sites.AbelianSheaf.presheafGrpObj ℱ.obj.obj).toMonObj
    (mul_sheafToPresheaf_ι_setCommGrp J 𝒦) (mul_sheafToPresheaf_ι_setCommGrp J ℱ) _).trans
    (isMulLeft_functorToTypes_iff _)

section GSet

variable (G : Type u') [Group G] [TopologicalSpace G]

/-- The functor `gsetPresheaf` from continuous `G`-sets to presheaves of sets on the one-object
category of `G` is braided for the cartesian monoidal structures. -/
local instance : (gsetPresheaf.{u', w} (G := G)).Braided := .ofChosenFiniteProducts _

/-- **The multiplication of a commutative group object of finite continuous `G`-sets, read on the
one-object category of `G`, is the addition of the corresponding discrete `G`-module.** -/
lemma mul_gsetPresheaf_ι_eq
    (B : CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory) :
    letI : MonObj ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B.X) :=
      Functor.monObjObj B.X
    letI : (gsetPresheaf.{u', w} (G := G)).LaxMonoidal :=
      (Functor.Braided.ofChosenFiniteProducts _).toMonoidal.toLaxMonoidal
    letI : MonObj ((gsetPresheaf (G := G)).obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B.X)) :=
      Functor.monObjObj _
    MonObj.mul (X := (gsetPresheaf (G := G)).obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B.X)) =
      (Sites.AbelianSheaf.presheafGrpObj ((gmodulePresheaf (G := G)).obj (externalGModule.obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj B)))).mul := by
  ext x ⟨a, b⟩
  rfl

/-- `mul_gsetPresheaf_ι_eq` for any monoidal structures on the two functors (they are unique). -/
lemma mul_gsetPresheaf_ι_eq_of_monoidal
    (B : CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory)
    (iι : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.Monoidal)
    (ig : (gsetPresheaf.{u', w} (G := G)).Monoidal) :
    @MonObj.mul _ _ _ ((gsetPresheaf (G := G)).obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B.X))
      (@Functor.monObjObj _ _ _ _ _ _ (gsetPresheaf (G := G)) ig.toLaxMonoidal _
        (@Functor.monObjObj _ _ _ _ _ _ (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι
          iι.toLaxMonoidal B.X B.grp.toMonObj)) =
      (Sites.AbelianSheaf.presheafGrpObj ((gmodulePresheaf (G := G)).obj (externalGModule.obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj B)))).mul := by
  obtain rfl : iι = (Functor.Braided.ofChosenFiniteProducts _).toMonoidal := Subsingleton.elim _ _
  obtain rfl : ig = (Functor.Braided.ofChosenFiniteProducts _).toMonoidal := Subsingleton.elim _ _
  ext x ⟨a, b⟩
  rfl

/-- The functor to sets underlying the discrete `G`-module read off a commutative group object of
finite continuous `G`-sets is the `G`-set itself. -/
lemma gmodulePresheaf_externalGModule_forget
    (B : CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory) :
    (gmodulePresheaf (G := G)).obj (externalGModule.obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj B)) ⋙
        forget AddCommGrpCat =
      (gsetPresheaf (G := G)).obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B.X) :=
  rfl

/-- Multiplicativity in the second variable on the one-object category of `G`, for the group
structures read off commutative group objects of finite continuous `G`-sets (and any monoidal
structures on the two functors involved), is additivity in the second variable for the
corresponding discrete `G`-modules. -/
lemma isMulRight_gsetPresheaf_iff_isAddRightPairing
    (S : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory)
    (B₁ B₂ : CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory)
    (iι : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.Monoidal)
    (ig : (gsetPresheaf.{u', w} (G := G)).Monoidal)
    (β : (gsetPresheaf (G := G)).obj S.obj ⊗ (gsetPresheaf (G := G)).obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B₁.X) ⟶
      (gsetPresheaf (G := G)).obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B₂.X)) :
    @IsMulRight _ _ _ _ _ _
      (@Functor.monObjObj _ _ _ _ _ _ (gsetPresheaf (G := G)) ig.toLaxMonoidal _
        (@Functor.monObjObj _ _ _ _ _ _ (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι
          iι.toLaxMonoidal B₁.X B₁.grp.toMonObj))
      (@Functor.monObjObj _ _ _ _ _ _ (gsetPresheaf (G := G)) ig.toLaxMonoidal _
        (@Functor.monObjObj _ _ _ _ _ _ (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι
          iι.toLaxMonoidal B₂.X B₂.grp.toMonObj)) β ↔
      IsAddRightPairing ((gsetPresheaf (G := G)).obj S.obj)
        ((gmodulePresheaf (G := G)).obj (externalGModule.obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj B₁)))
        ((gmodulePresheaf (G := G)).obj (externalGModule.obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj B₂))) β := by
  obtain rfl : iι = (Functor.Braided.ofChosenFiniteProducts _).toMonoidal := Subsingleton.elim _ _
  obtain rfl : ig = (Functor.Braided.ofChosenFiniteProducts _).toMonoidal := Subsingleton.elim _ _
  rw [isMulRight_functorToTypes_iff]
  rfl

variable {G}

/-- Multiplicativity in the first variable on the one-object category of `G`, read in terms of
the corresponding discrete `G`-modules, for any monoidal structures on the functors involved. -/
lemma isMulLeft_gsetPresheaf_iff
    (B₀ B₁ B₂ : CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory)
    (iι : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.Monoidal)
    (ig : (gsetPresheaf.{u', w} (G := G)).Monoidal)
    (β : (gsetPresheaf (G := G)).obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B₀.X) ⊗
      (gsetPresheaf (G := G)).obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B₁.X) ⟶
      (gsetPresheaf (G := G)).obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B₂.X)) :
    @IsMulLeft _ _ _ _ _ _
      (@Functor.monObjObj _ _ _ _ _ _ (gsetPresheaf (G := G)) ig.toLaxMonoidal _
        (@Functor.monObjObj _ _ _ _ _ _ (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι
          iι.toLaxMonoidal B₀.X B₀.grp.toMonObj))
      (@Functor.monObjObj _ _ _ _ _ _ (gsetPresheaf (G := G)) ig.toLaxMonoidal _
        (@Functor.monObjObj _ _ _ _ _ _ (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι
          iι.toLaxMonoidal B₂.X B₂.grp.toMonObj)) β ↔
      ∀ (t t' : (externalGModule.obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj B₀)).obj.obj.V)
        (m : (externalGModule.obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj B₁)).obj.obj.V),
        (show (externalGModule.obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj
            B₂)).obj.obj.V from
          β.app (SingleObj.star G) (t + t', m)) =
          (show (externalGModule.obj
            ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj
              B₂)).obj.obj.V from
            β.app (SingleObj.star G) (t, m)) +
          (show (externalGModule.obj
            ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj
              B₂)).obj.obj.V from
            β.app (SingleObj.star G) (t', m)) := by
  obtain rfl : iι = (Functor.Braided.ofChosenFiniteProducts _).toMonoidal := Subsingleton.elim _ _
  obtain rfl : ig = (Functor.Braided.ofChosenFiniteProducts _).toMonoidal := Subsingleton.elim _ _
  rw [isMulLeft_functorToTypes_iff]
  exact ⟨fun h t t' m ↦ h _ t t' m, fun h x t t' m ↦ h t t' m⟩

/-- The monoidal structure on `gsetPresheaf` given by its preservation of finite products. -/
abbrev gsetPresheafMonoidal : (gsetPresheaf.{u', w} (G := G)).Monoidal :=
  (Functor.Braided.ofChosenFiniteProducts _).toMonoidal

/-- The monoidal structure on the inclusion of finite continuous `G`-sets given by its
preservation of finite products. -/
abbrev ιContinuousGSetIsFiniteMonoidal :
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.Monoidal :=
  (Functor.Braided.ofChosenFiniteProducts _).toMonoidal

/-- The monoid structure on a commutative group object of finite `G`-sets, read on the
one-object category of `G`. -/
abbrev gsetPresheafMonObj
    (B : CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory) :
    MonObj ((gsetPresheaf (G := G)).obj
      ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B.X)) :=
  @Functor.monObjObj _ _ _ _ _ _ (gsetPresheaf (G := G))
    (gsetPresheafMonoidal (G := G)).toLaxMonoidal _
    (@Functor.monObjObj _ _ _ _ _ _ (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι
      (ιContinuousGSetIsFiniteMonoidal (G := G)).toLaxMonoidal B.X B.grp.toMonObj)

/-- Pairings of finite continuous `G`-sets multiplicative in the second variable are, along the
inclusion and the reading on the one-object category of `G`, pairings of presheaves on that
category multiplicative in the second variable. -/
noncomputable def mulRightGSetPushEquiv
    (S : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory)
    (B₁ B₂ : CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory) :
    {β : S ⊗ B₁.X ⟶ B₂.X // IsMulRight β} ≃
      {β' : (gsetPresheaf (G := G)).obj S.obj ⊗ (gsetPresheaf (G := G)).obj
            ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B₁.X) ⟶
          (gsetPresheaf (G := G)).obj
            ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B₂.X) //
        @IsMulRight _ _ _ _ _ _ (gsetPresheafMonObj (G := G) B₁) (gsetPresheafMonObj (G := G) B₂)
          β'} :=
  letI := gsetPresheafMonoidal (G := G)
  letI := ιContinuousGSetIsFiniteMonoidal (G := G)
  (@Functor.FullyFaithful.mulRightEquiv _ _ _ _ _ _
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι
    (ιContinuousGSetIsFiniteMonoidal (G := G))
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).fullyFaithfulι S B₁.X B₂.X
    B₁.grp.toMonObj B₂.grp.toMonObj).trans
    (@Functor.FullyFaithful.mulRightEquiv _ _ _ _ _ _ (gsetPresheaf (G := G))
      (gsetPresheafMonoidal (G := G)) gsetPresheafFullyFaithful
      ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj S)
      ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B₁.X)
      ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.obj B₂.X)
      (@Functor.monObjObj _ _ _ _ _ _ (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι
        (ιContinuousGSetIsFiniteMonoidal (G := G)).toLaxMonoidal B₁.X B₁.grp.toMonObj)
      (@Functor.monObjObj _ _ _ _ _ _ (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι
        (ιContinuousGSetIsFiniteMonoidal (G := G)).toLaxMonoidal B₂.X B₂.grp.toMonObj))

/-- **Pairings of finite continuous `G`-sets multiplicative in the second variable are pairings
additive in the second variable of the corresponding discrete `G`-modules.** -/
noncomputable def mulRightGPairingEquiv
    (S : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory)
    (B₁ B₂ : CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory) :
    {β : S ⊗ B₁.X ⟶ B₂.X // IsMulRight β} ≃
      {β' : (gsetPresheaf (G := G)).obj S.obj ⊗ ((gmodulePresheaf (G := G)).obj (externalGModule.obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj B₁)) ⋙
            forget AddCommGrpCat) ⟶
        (gmodulePresheaf (G := G)).obj (externalGModule.obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.mapCommGrp.obj B₂)) ⋙
          forget AddCommGrpCat //
        IsAddRightPairing _ _ _ β'} :=
  (mulRightGSetPushEquiv S B₁ B₂).trans (Equiv.subtypeEquivRight fun β' ↦
    isMulRight_gsetPresheaf_iff_isAddRightPairing G S B₁ B₂
      (ιContinuousGSetIsFiniteMonoidal (G := G)) (gsetPresheafMonoidal (G := G)) β')

/-- The bijection `mulRightGPairingEquiv` is natural in the `G`-set. -/
lemma mulRightGPairingEquiv_comp
    {S' S : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory}
    (h : S' ⟶ S)
    (B₁ B₂ : CommGrp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory)
    (β : {β : S ⊗ B₁.X ⟶ B₂.X // IsMulRight β}) :
    (mulRightGPairingEquiv S' B₁ B₂ ⟨h ▷ _ ≫ β.1, β.2.whiskerRight_comp h⟩).1 =
      (gsetPresheaf (G := G)).map h.hom ▷ _ ≫ (mulRightGPairingEquiv S B₁ B₂ β).1 := by
  exact mulRightEquiv_comp_comp (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).fullyFaithfulι
    gsetPresheafFullyFaithful h β

variable (e : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory ≌
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory)

/-- **The discrete `G`-module of the transport, unfolded**: it is read off the image under `e` of
the commutative group object `setCommGrp`. -/
lemma finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_functor_obj
    (𝒢 : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory) :
    letI : e.functor.Braided := .ofChosenFiniteProducts _
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj 𝒢).obj =
      externalGModule.obj
        ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι.mapCommGrp.obj
          (e.functor.mapCommGrp.obj (setCommGrp J 𝒢))) :=
  rfl

end GSet

section Yoneda

variable {G : Type u'} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (e : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory ≌
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory)
  (𝒢 ℱ : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory)
  (hℋ : isFiniteLocallyConstantAbelianSheaf.{v, u, u} J (internalHomSheaf J 𝒢.obj ℱ.obj))

/-- `ℋom(𝒢, ℱ)`, as a finite locally constant abelian sheaf. -/
abbrev internalHomFiniteLocallyConstant :
    (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory :=
  ⟨internalHomSheaf J 𝒢.obj ℱ.obj, hℋ⟩

/-- `Hom_ℤ(E 𝒢, E ℱ)` with the conjugation action, as a finite discrete `G`-module. -/
abbrev homTransport : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory :=
  ContinuousGAddCommGrp.homIsFinite
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj 𝒢)
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj ℱ)

/-- **The Yoneda bijection**: for a finite locally constant sheaf of sets `T`, morphisms
`T ⟶ ℋom(𝒢, ℱ)` correspond to morphisms `T ⟶ e⁻¹ Hom_ℤ(E 𝒢, E ℱ)`, through pairings additive in
the second variable on both sides. -/
noncomputable def internalHomYonedaEquiv
    (T : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory) :
    (T ⟶ (forgetFiniteLocallyConstantAbelianSheaf J).obj
        (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ)) ≃
      (T ⟶ e.inverse.obj ((ContinuousGAddCommGrp.forgetActionIsFinite G).obj
        (homTransport J e 𝒢 ℱ))) :=
  letI : e.functor.Braided := .ofChosenFiniteProducts _
  haveI : Finite ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      𝒢).obj.obj.obj.V :=
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj 𝒢).property
  ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).fullyFaithfulι.homEquiv).trans <|
  ((fullyFaithfulSheafToPresheaf J (Type (max u v))).homEquiv).trans <|
  (internalHomPresheafPairingEquiv T.obj.obj 𝒢.obj.obj ℱ.obj.obj).trans <|
  (mulRightPairingEquiv J T 𝒢 ℱ).symm.trans <|
  (e.fullyFaithfulFunctor.mulRightEquiv T (setCommGrp J 𝒢).X (setCommGrp J ℱ).X).trans <|
  (mulRightGPairingEquiv (e.functor.obj T) (e.functor.mapCommGrp.obj (setCommGrp J 𝒢))
    (e.functor.mapCommGrp.obj (setCommGrp J ℱ))).trans <|
  (ContinuousGAddCommGrp.homPairingEquiv
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj 𝒢).obj
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj ℱ).obj
    (e.functor.obj T).obj).symm.trans <|
  ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).fullyFaithfulι.homEquiv
      (X := e.functor.obj T)
      (Y := (ContinuousGAddCommGrp.forgetActionIsFinite G).obj (homTransport J e 𝒢 ℱ))).symm.trans
    (e.toAdjunction.homEquiv T
      ((ContinuousGAddCommGrp.forgetActionIsFinite G).obj (homTransport J e 𝒢 ℱ)))

omit [IsTopologicalGroup G] in
/-- Naturality of a family of bijections passes to the inverse bijections. -/
lemma _root_.Equiv.symm_apply_eq_of_naturality {α α' β β' : Sort*} (e : α ≃ β) (e' : α' ≃ β')
    (f : α → α') (g : β → β') (h : ∀ a, e' (f a) = g (e a)) (b : β) :
    e'.symm (g b) = f (e.symm b) := by
  rw [← e.apply_symm_apply b, ← h, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- **The Yoneda bijection is natural in the finite locally constant sheaf of sets.** -/
lemma internalHomYonedaEquiv_comp
    {T' T : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory} (h : T' ⟶ T)
    (φ : T ⟶ (forgetFiniteLocallyConstantAbelianSheaf J).obj
      (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ)) :
    internalHomYonedaEquiv J e 𝒢 ℱ hℋ T' (h ≫ φ) = h ≫ internalHomYonedaEquiv J e 𝒢 ℱ hℋ T φ := by
  let : e.functor.Braided := .ofChosenFiniteProducts _
  have : Finite ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      𝒢).obj.obj.obj.V :=
    ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj 𝒢).property
  let P := isFiniteLocallyConstantSetSheaf.{v, u, u} J
  let Q := AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G
  let EE := finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e
  have s₁ : internalHomPresheafPairingEquiv T'.obj.obj 𝒢.obj.obj ℱ.obj.obj
      ((fullyFaithfulSheafToPresheaf J (Type (max u v))).homEquiv
        (P.fullyFaithfulι.homEquiv (h ≫ φ))) =
      ⟨h.hom.hom ▷ _ ≫ (internalHomPresheafPairingEquiv T.obj.obj 𝒢.obj.obj ℱ.obj.obj
        ((fullyFaithfulSheafToPresheaf J (Type (max u v))).homEquiv
          (P.fullyFaithfulι.homEquiv φ))).1,
        IsAddRightPairing.whiskerRight_comp _ _ _ h.hom.hom
          (internalHomPresheafPairingEquiv T.obj.obj 𝒢.obj.obj ℱ.obj.obj
            ((fullyFaithfulSheafToPresheaf J (Type (max u v))).homEquiv
              (P.fullyFaithfulι.homEquiv φ))).2⟩ :=
    Subtype.ext rfl
  have s₂ := Equiv.symm_apply_eq_of_naturality (mulRightPairingEquiv J T 𝒢 ℱ)
    (mulRightPairingEquiv J T' 𝒢 ℱ) (fun β ↦ ⟨h ▷ _ ≫ β.1, β.2.whiskerRight_comp h⟩)
    (fun β' ↦ ⟨h.hom.hom ▷ _ ≫ β'.1, IsAddRightPairing.whiskerRight_comp _ _ _ h.hom.hom β'.2⟩)
    (fun β ↦ Subtype.ext (mulRightPairingEquiv_comp J h 𝒢 ℱ β))
  have s₃ : ∀ β : {β : T ⊗ (setCommGrp J 𝒢).X ⟶ (setCommGrp J ℱ).X // IsMulRight β},
      e.fullyFaithfulFunctor.mulRightEquiv T' _ _ ⟨h ▷ _ ≫ β.1, β.2.whiskerRight_comp h⟩ =
        ⟨e.functor.map h ▷ _ ≫ (e.fullyFaithfulFunctor.mulRightEquiv T _ _ β).1,
          (e.fullyFaithfulFunctor.mulRightEquiv T _ _ β).2.whiskerRight_comp _⟩ :=
    fun β ↦ Subtype.ext (e.fullyFaithfulFunctor.mulRightEquiv_comp h β)
  have s₄ : ∀ β : {β : e.functor.obj T ⊗ (e.functor.mapCommGrp.obj (setCommGrp J 𝒢)).X ⟶
      (e.functor.mapCommGrp.obj (setCommGrp J ℱ)).X // IsMulRight β},
      mulRightGPairingEquiv (e.functor.obj T') (e.functor.mapCommGrp.obj (setCommGrp J 𝒢))
          (e.functor.mapCommGrp.obj (setCommGrp J ℱ))
          ⟨e.functor.map h ▷ _ ≫ β.1, β.2.whiskerRight_comp _⟩ =
        ⟨(gsetPresheaf (G := G)).map (e.functor.map h).hom ▷ _ ≫
            (mulRightGPairingEquiv (e.functor.obj T) (e.functor.mapCommGrp.obj (setCommGrp J 𝒢))
              (e.functor.mapCommGrp.obj (setCommGrp J ℱ)) β).1,
          IsAddRightPairing.whiskerRight_comp _ _ _ _
            (mulRightGPairingEquiv (e.functor.obj T) (e.functor.mapCommGrp.obj (setCommGrp J 𝒢))
              (e.functor.mapCommGrp.obj (setCommGrp J ℱ)) β).2⟩ :=
    fun β ↦ Subtype.ext (mulRightGPairingEquiv_comp (e.functor.map h)
      (e.functor.mapCommGrp.obj (setCommGrp J 𝒢)) (e.functor.mapCommGrp.obj (setCommGrp J ℱ)) β)
  have s₅ := Equiv.symm_apply_eq_of_naturality
    (ContinuousGAddCommGrp.homPairingEquiv (EE.functor.obj 𝒢).obj (EE.functor.obj ℱ).obj
      (e.functor.obj T).obj)
    (ContinuousGAddCommGrp.homPairingEquiv (EE.functor.obj 𝒢).obj (EE.functor.obj ℱ).obj
      (e.functor.obj T').obj)
    (fun f ↦ (e.functor.map h).hom ≫ f)
    (fun β' ↦ ⟨(gsetPresheaf (G := G)).map (e.functor.map h).hom ▷ _ ≫ β'.1,
      IsAddRightPairing.whiskerRight_comp _ _ _ _ β'.2⟩)
    (fun f ↦ Subtype.ext (ContinuousGAddCommGrp.pairingOfGSetHom_comp _ (e.functor.map h).hom f))
  let Z := (ContinuousGAddCommGrp.forgetActionIsFinite G).obj (homTransport J e 𝒢 ℱ)
  let B₁ := e.functor.mapCommGrp.obj (setCommGrp J 𝒢)
  let B₂ := e.functor.mapCommGrp.obj (setCommGrp J ℱ)
  let tail₅ : ∀ T : P.FullSubcategory, (Q.ι.obj (e.functor.obj T) ⟶ Q.ι.obj Z) →
      (T ⟶ e.inverse.obj Z) :=
    fun T f ↦ e.toAdjunction.homEquiv T Z (Q.fullyFaithfulι.preimage f)
  have n₅ : ∀ f : Q.ι.obj (e.functor.obj T) ⟶ Q.ι.obj Z,
      tail₅ T' (Q.ι.map (e.functor.map h) ≫ f) = h ≫ tail₅ T f := fun f ↦ by
    show e.toAdjunction.homEquiv T' Z
        (Q.fullyFaithfulι.preimage (Q.ι.map (e.functor.map h) ≫ f)) =
      h ≫ e.toAdjunction.homEquiv T Z (Q.fullyFaithfulι.preimage f)
    rw [← e.toAdjunction.homEquiv_naturality_left]
    congr 1
  let tail₄ : ∀ T : P.FullSubcategory,
      {β : (gsetPresheaf (G := G)).obj (e.functor.obj T).obj ⊗
          ((gmodulePresheaf (G := G)).obj (EE.functor.obj 𝒢).obj ⋙ forget AddCommGrpCat) ⟶
        (gmodulePresheaf (G := G)).obj (EE.functor.obj ℱ).obj ⋙ forget AddCommGrpCat //
          IsAddRightPairing _ _ _ β} → (T ⟶ e.inverse.obj Z) :=
    fun T q ↦ tail₅ T ((ContinuousGAddCommGrp.homPairingEquiv (EE.functor.obj 𝒢).obj
      (EE.functor.obj ℱ).obj (e.functor.obj T).obj).symm q)
  have n₄ : ∀ q, tail₄ T' ⟨(gsetPresheaf (G := G)).map (e.functor.map h).hom ▷ _ ≫ q.1,
      IsAddRightPairing.whiskerRight_comp _ _ _ _ q.2⟩ = h ≫ tail₄ T q := fun q ↦
    (congrArg (tail₅ T') (s₅ q)).trans (n₅ _)
  let tail₃ : ∀ T : P.FullSubcategory,
      {β : e.functor.obj T ⊗ B₁.X ⟶ B₂.X // IsMulRight β} → (T ⟶ e.inverse.obj Z) :=
    fun T β ↦ tail₄ T (mulRightGPairingEquiv (e.functor.obj T) B₁ B₂ β)
  have n₃ : ∀ β, tail₃ T' ⟨e.functor.map h ▷ _ ≫ β.1, β.2.whiskerRight_comp _⟩ =
      h ≫ tail₃ T β := fun β ↦
    (congrArg (tail₄ T') (s₄ β)).trans (n₄ _)
  let tail₂ : ∀ T : P.FullSubcategory,
      {β : T ⊗ (setCommGrp J 𝒢).X ⟶ (setCommGrp J ℱ).X // IsMulRight β} →
        (T ⟶ e.inverse.obj Z) :=
    fun T β ↦ tail₃ T (e.fullyFaithfulFunctor.mulRightEquiv T _ _ β)
  have n₂ : ∀ β, tail₂ T' ⟨h ▷ _ ≫ β.1, β.2.whiskerRight_comp h⟩ = h ≫ tail₂ T β := fun β ↦
    (congrArg (tail₃ T') (s₃ β)).trans (n₃ _)
  let tail₁ : ∀ T : P.FullSubcategory,
      {β' : T.obj.obj ⊗ (𝒢.obj.obj ⋙ forget AddCommGrpCat) ⟶ ℱ.obj.obj ⋙ forget AddCommGrpCat //
        IsAddRightPairing _ _ _ β'} → (T ⟶ e.inverse.obj Z) :=
    fun T p ↦ tail₂ T ((mulRightPairingEquiv J T 𝒢 ℱ).symm p)
  have n₁ : ∀ p, tail₁ T' ⟨h.hom.hom ▷ _ ≫ p.1,
      IsAddRightPairing.whiskerRight_comp _ _ _ h.hom.hom p.2⟩ = h ≫ tail₁ T p := fun p ↦
    (congrArg (tail₂ T') (s₂ p)).trans (n₂ _)
  exact (congrArg (tail₁ T') s₁).trans (n₁ _)

/-- **`ℋom(𝒢, ℱ)` is `e⁻¹ Hom_ℤ(E 𝒢, E ℱ)` on underlying sheaves of sets.** -/
noncomputable def internalHomForgetIso :
    (forgetFiniteLocallyConstantAbelianSheaf J).obj (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ) ≅
      e.inverse.obj ((ContinuousGAddCommGrp.forgetActionIsFinite G).obj (homTransport J e 𝒢 ℱ)) :=
  Yoneda.ext _ _ (fun {T} φ ↦ internalHomYonedaEquiv J e 𝒢 ℱ hℋ T φ)
    (fun {T} ψ ↦ (internalHomYonedaEquiv J e 𝒢 ℱ hℋ T).symm ψ)
    (fun {_} φ ↦ Equiv.symm_apply_apply _ φ) (fun {_} ψ ↦ Equiv.apply_symm_apply _ ψ)
    (fun f g ↦ internalHomYonedaEquiv_comp J e 𝒢 ℱ hℋ f g)

/-- **`E ℋom(𝒢, ℱ)` and `Hom_ℤ(E 𝒢, E ℱ)` have isomorphic underlying finite `G`-sets.** -/
noncomputable def internalHomForgetActionIso :
    (ContinuousGAddCommGrp.forgetActionIsFinite G).obj
        ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
          (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ)) ≅
      (ContinuousGAddCommGrp.forgetActionIsFinite G).obj (homTransport J e 𝒢 ℱ) :=
  e.functor.mapIso (internalHomForgetIso J e 𝒢 ℱ hℋ) ≪≫ e.counitIso.app _

/-- The evaluation pairing `ℋom(𝒢, ℱ) × 𝒢 ⟶ ℱ`, read on the side of finite `G`-sets: the image
under the Yoneda bijection of the identity of `ℋom(𝒢, ℱ)`, as a pairing
`E ℋom(𝒢, ℱ) × E 𝒢 ⟶ E ℱ`. -/
noncomputable def internalHomEvalTransport :
    (gsetPresheaf (G := G)).obj (e.functor.obj ((forgetFiniteLocallyConstantAbelianSheaf J).obj
        (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ))).obj ⊗
      ((gmodulePresheaf (G := G)).obj
        ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj 𝒢).obj ⋙
        forget AddCommGrpCat) ⟶
      (gmodulePresheaf (G := G)).obj
        ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj ℱ).obj ⋙
        forget AddCommGrpCat :=
  letI : e.functor.Braided := .ofChosenFiniteProducts _
  (mulRightGPairingEquiv _ (e.functor.mapCommGrp.obj (setCommGrp J 𝒢))
    (e.functor.mapCommGrp.obj (setCommGrp J ℱ))
    (e.fullyFaithfulFunctor.mulRightEquiv _ (setCommGrp J 𝒢).X (setCommGrp J ℱ).X
      ((mulRightPairingEquiv J _ 𝒢 ℱ).symm
        (internalHomPresheafPairingEquiv _ 𝒢.obj.obj ℱ.obj.obj
          ((fullyFaithfulSheafToPresheaf J (Type (max u v))).homEquiv
            ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).fullyFaithfulι.homEquiv
              (𝟙 ((forgetFiniteLocallyConstantAbelianSheaf J).obj
                (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ))))))))).1

/-- **The isomorphism `E ℋom(𝒢, ℱ) ≅ Hom_ℤ(E 𝒢, E ℱ)` on elements**: `x` is sent to
`m ↦ ev(x, m)`, the transported evaluation pairing. -/
lemma internalHomForgetActionIso_hom_apply
    (x : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ)).obj.obj.obj.V)
    (m : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      𝒢).obj.obj.obj.V) :
    ContinuousGAddCommGrp.homOfElem
        ((internalHomForgetActionIso J e 𝒢 ℱ hℋ).hom.hom.hom.hom x) m =
      (internalHomEvalTransport J e 𝒢 ℱ hℋ).app (SingleObj.star G) (x, m) := by
  let : e.functor.Braided := .ofChosenFiniteProducts _
  let EE := finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e
  let T₀ := (forgetFiniteLocallyConstantAbelianSheaf J).obj
    (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ)
  let Z := (ContinuousGAddCommGrp.forgetActionIsFinite G).obj (homTransport J e 𝒢 ℱ)
  let q' := mulRightGPairingEquiv _ (e.functor.mapCommGrp.obj (setCommGrp J 𝒢))
    (e.functor.mapCommGrp.obj (setCommGrp J ℱ))
    (e.fullyFaithfulFunctor.mulRightEquiv T₀ (setCommGrp J 𝒢).X (setCommGrp J ℱ).X
      ((mulRightPairingEquiv J T₀ 𝒢 ℱ).symm
        (internalHomPresheafPairingEquiv _ 𝒢.obj.obj ℱ.obj.obj
          ((fullyFaithfulSheafToPresheaf J (Type (max u v))).homEquiv
            ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).fullyFaithfulι.homEquiv (𝟙 T₀))))))
  let f' : e.functor.obj T₀ ⟶ Z :=
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).fullyFaithfulι.preimage
      ((ContinuousGAddCommGrp.homPairingEquiv (EE.functor.obj 𝒢).obj (EE.functor.obj ℱ).obj
        (e.functor.obj T₀).obj).symm q')
  have hθ : (internalHomForgetActionIso J e 𝒢 ℱ hℋ).hom = f' := by
    show e.functor.map (e.toAdjunction.homEquiv T₀ Z f') ≫ e.toAdjunction.counit.app Z = f'
    exact (e.toAdjunction.homEquiv_counit (g := e.toAdjunction.homEquiv T₀ Z f')).symm.trans
      (Equiv.symm_apply_apply _ f')
  exact congrArg (fun φ : e.functor.obj T₀ ⟶ Z ↦
    ContinuousGAddCommGrp.homOfElem (φ.hom.hom.hom.hom x) m) hθ

omit [IsTopologicalGroup G] in
/-- **The transported evaluation pairing is additive in its first variable.** -/
lemma internalHomEvalTransport_add_left
    (t t' : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ)).obj.obj.obj.V)
    (m : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      𝒢).obj.obj.obj.V) :
    (show ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
        ℱ).obj.obj.obj.V from
      (internalHomEvalTransport J e 𝒢 ℱ hℋ).app (SingleObj.star G) (t + t', m)) =
      (show ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
          ℱ).obj.obj.obj.V from
        (internalHomEvalTransport J e 𝒢 ℱ hℋ).app (SingleObj.star G) (t, m)) +
      (show ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
          ℱ).obj.obj.obj.V from
        (internalHomEvalTransport J e 𝒢 ℱ hℋ).app (SingleObj.star G) (t', m)) := by
  let : e.functor.Braided := .ofChosenFiniteProducts _
  let ℋ := internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ
  let p₀ := internalHomPresheafPairingEquiv _ 𝒢.obj.obj ℱ.obj.obj
    ((fullyFaithfulSheafToPresheaf J (Type (max u v))).homEquiv
      ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).fullyFaithfulι.homEquiv
        (𝟙 ((forgetFiniteLocallyConstantAbelianSheaf J).obj ℋ))))
  let βD : {β : (setCommGrp J ℋ).X ⊗ (setCommGrp J 𝒢).X ⟶ (setCommGrp J ℱ).X // IsMulRight β} :=
    (mulRightPairingEquiv J _ 𝒢 ℱ).symm p₀
  have h₀ : IsMulLeft βD.1 := by
    rw [isMulLeft_iff_mulRightPairingEquiv J 𝒢 ℱ ℋ βD]
    intro X a a' g
    rw [show mulRightPairingEquiv J (setCommGrp J ℋ).X 𝒢 ℱ βD = p₀ from
      Equiv.apply_symm_apply _ _]
    rfl
  have h₁ : IsMulLeft (e.fullyFaithfulFunctor.mulRightEquiv _ (setCommGrp J 𝒢).X
      (setCommGrp J ℱ).X βD).1 :=
    (Functor.isMulLeft_μ_comp_map_iff_of_faithful e.functor βD.1).mpr h₀
  let βC := e.fullyFaithfulFunctor.mulRightEquiv _ (setCommGrp J 𝒢).X (setCommGrp J ℱ).X βD
  have h₂ := (@Functor.isMulLeft_μ_comp_map_iff_of_faithful _ _ _ _ _ _
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι
    (ιContinuousGSetIsFiniteMonoidal (G := G))
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).fullyFaithfulι.faithful _ _ _
    (e.functor.mapCommGrp.obj (setCommGrp J ℋ)).grp.toMonObj
    (e.functor.mapCommGrp.obj (setCommGrp J ℱ)).grp.toMonObj βC.1).mpr h₁
  have h₃ := (@Functor.isMulLeft_μ_comp_map_iff_of_faithful _ _ _ _ _ _ (gsetPresheaf (G := G))
    (gsetPresheafMonoidal (G := G)) gsetPresheafFullyFaithful.faithful _ _ _ _ _ _).mpr h₂
  exact (isMulLeft_gsetPresheaf_iff (e.functor.mapCommGrp.obj (setCommGrp J ℋ))
    (e.functor.mapCommGrp.obj (setCommGrp J 𝒢)) (e.functor.mapCommGrp.obj (setCommGrp J ℱ))
    (ιContinuousGSetIsFiniteMonoidal (G := G)) (gsetPresheafMonoidal (G := G)) _).mp h₃ t t' m

/-- **`E ℋom(𝒢, ℱ) ≅ Hom_ℤ(E 𝒢, E ℱ)`.** If the internal Hom of two finite locally constant abelian
sheaves is finite locally constant, the finite discrete `G`-module the transport attaches to it is
`Hom_ℤ(E 𝒢, E ℱ)` with the conjugation action. Under the isomorphism a section of `ℋom(𝒢, ℱ)` is
sent to the map `m ↦ ev(x, m)` given by evaluation
(`Stacks.ConstantSheaf.internalHomTransportIso_hom_apply`). -/
noncomputable def internalHomTransportIso :
    (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
        (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ) ≅ homTransport J e 𝒢 ℱ :=
  ContinuousGAddCommGrp.isoOfForgetActionIsFiniteIso (internalHomForgetActionIso J e 𝒢 ℱ hℋ)
    (fun x y ↦ AddMonoidHom.ext fun m ↦
      ((internalHomForgetActionIso_hom_apply J e 𝒢 ℱ hℋ (x + y) m).trans
        (internalHomEvalTransport_add_left J e 𝒢 ℱ hℋ x y m)).trans
        (congrArg₂ (· + ·) (internalHomForgetActionIso_hom_apply J e 𝒢 ℱ hℋ x m).symm
          (internalHomForgetActionIso_hom_apply J e 𝒢 ℱ hℋ y m).symm))

/-- The isomorphism `internalHomTransportIso` on elements: evaluation. -/
lemma internalHomTransportIso_hom_apply
    (x : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ)).obj.obj.obj.V)
    (m : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      𝒢).obj.obj.obj.V) :
    ContinuousGAddCommGrp.homOfElem
        ((internalHomTransportIso J e 𝒢 ℱ hℋ).hom.hom.hom.hom.hom x) m =
      (internalHomEvalTransport J e 𝒢 ℱ hℋ).app (SingleObj.star G) (x, m) :=
  internalHomForgetActionIso_hom_apply J e 𝒢 ℱ hℋ x m

section Naturality

variable {𝒢} {𝒢' : (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory}
  (hℋ' : isFiniteLocallyConstantAbelianSheaf.{v, u, u} J (internalHomSheaf J 𝒢'.obj ℱ.obj))
  (w : 𝒢' ⟶ 𝒢)

/-- `ℋom(w, ℱ) : ℋom(𝒢, ℱ) ⟶ ℋom(𝒢', ℱ)`, precomposition with `w`, among the finite locally
constant abelian sheaves. -/
def internalHomFiniteLocallyConstantMap :
    internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ ⟶ internalHomFiniteLocallyConstant J 𝒢' ℱ hℋ' :=
  ObjectProperty.homMk ((internalHomFunctor J ℱ.obj).map w.hom.op)

omit [IsTopologicalGroup G] in
/-- **The transported evaluation pairing is dinatural**: `ev'(ℋom(w)(x), m') = ev(x, w(m'))`. -/
lemma internalHomEvalTransport_naturality
    (t : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      (internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ)).obj.obj.obj.V)
    (m : ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj
      𝒢').obj.obj.obj.V) :
    (internalHomEvalTransport J e 𝒢' ℱ hℋ').app (SingleObj.star G)
        (((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.map
          (internalHomFiniteLocallyConstantMap J ℱ hℋ hℋ' w)).hom.hom.hom.hom.hom t, m) =
      (internalHomEvalTransport J e 𝒢 ℱ hℋ).app (SingleObj.star G)
        (t, ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.map
          w).hom.hom.hom.hom.hom m) := by
  let : e.functor.Braided := .ofChosenFiniteProducts _
  let P := isFiniteLocallyConstantSetSheaf.{v, u, u} J
  let S := sheafToPresheaf J (Type (max u v))
  let U := forgetFiniteLocallyConstantAbelianSheaf J
  let ℋ := internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ
  let ℋ' := internalHomFiniteLocallyConstant J 𝒢' ℱ hℋ'
  let T₀ := U.obj ℋ
  let T₀' := U.obj ℋ'
  let h : T₀ ⟶ T₀' := U.map (internalHomFiniteLocallyConstantMap J ℱ hℋ hℋ' w)
  let k : (setCommGrp J 𝒢').X ⟶ (setCommGrp J 𝒢).X := U.map w
  let p₀ := internalHomPresheafPairingEquiv T₀.obj.obj 𝒢.obj.obj ℱ.obj.obj
    ((fullyFaithfulSheafToPresheaf J (Type (max u v))).homEquiv (P.fullyFaithfulι.homEquiv (𝟙 T₀)))
  let p₀' := internalHomPresheafPairingEquiv T₀'.obj.obj 𝒢'.obj.obj ℱ.obj.obj
    ((fullyFaithfulSheafToPresheaf J (Type (max u v))).homEquiv
      (P.fullyFaithfulι.homEquiv (𝟙 T₀')))
  let evD := ((mulRightPairingEquiv J T₀ 𝒢 ℱ).symm p₀).1
  let evD' := ((mulRightPairingEquiv J T₀' 𝒢' ℱ).symm p₀').1
  let Φ : ∀ {T A : P.FullSubcategory}, (T ⊗ A ⟶ (setCommGrp J ℱ).X) →
      (S.obj (P.ι.obj T) ⊗ S.obj (P.ι.obj A) ⟶ S.obj (P.ι.obj (setCommGrp J ℱ).X)) :=
    fun β ↦ Functor.LaxMonoidal.μ S _ _ ≫ S.map (Functor.LaxMonoidal.μ P.ι _ _ ≫ P.ι.map β)
  have hΦ : ∀ {T A : P.FullSubcategory} (β₁ β₂ : T ⊗ A ⟶ (setCommGrp J ℱ).X),
      Φ β₁ = Φ β₂ → β₁ = β₂ := fun β₁ β₂ hβ ↦ by
    have h₁ := (cancel_epi _).mp hβ
    have h₂ := (fullyFaithfulSheafToPresheaf J (Type (max u v))).map_injective h₁
    exact P.fullyFaithfulι.map_injective ((cancel_epi _).mp h₂)
  have hev : Φ evD = p₀.1 :=
    (mulRightPairingEquiv_apply J T₀ 𝒢 ℱ ((mulRightPairingEquiv J T₀ 𝒢 ℱ).symm p₀)).symm.trans
      (congrArg Subtype.val (Equiv.apply_symm_apply (mulRightPairingEquiv J T₀ 𝒢 ℱ) p₀))
  have hev' : Φ evD' = p₀'.1 :=
    (mulRightPairingEquiv_apply J T₀' 𝒢' ℱ ((mulRightPairingEquiv J T₀' 𝒢' ℱ).symm p₀')).symm.trans
      (congrArg Subtype.val (Equiv.apply_symm_apply (mulRightPairingEquiv J T₀' 𝒢' ℱ) p₀'))
  have hD : h ▷ _ ≫ evD' = T₀ ◁ k ≫ evD := by
    apply hΦ
    show Functor.LaxMonoidal.μ S _ _ ≫ S.map (Functor.LaxMonoidal.μ P.ι _ _ ≫ P.ι.map _) =
      Functor.LaxMonoidal.μ S _ _ ≫ S.map (Functor.LaxMonoidal.μ P.ι _ _ ≫ P.ι.map _)
    rw [Functor.μ_comp_map_whiskerRight_comp, Functor.μ_comp_map_whiskerRight_comp,
      Functor.μ_comp_map_whiskerLeft_comp, Functor.μ_comp_map_whiskerLeft_comp]
    refine (congrArg (fun φ ↦ S.map (P.ι.map h) ▷ _ ≫ φ) hev').trans
      (Eq.trans ?_ (congrArg (fun φ ↦ _ ◁ S.map (P.ι.map k) ≫ φ) hev).symm)
    ext X ⟨α, g⟩
    rfl
  let Tr : ∀ {T A : P.FullSubcategory}, (T ⊗ A ⟶ (setCommGrp J ℱ).X) →
      ((gsetPresheaf (G := G)).obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι.obj (e.functor.obj T)) ⊗
        (gsetPresheaf (G := G)).obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι.obj (e.functor.obj A)) ⟶
        (gsetPresheaf (G := G)).obj
          ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι.obj
            (e.functor.obj (setCommGrp J ℱ).X))) :=
    fun β ↦ @Functor.LaxMonoidal.μ _ _ _ _ _ _ (gsetPresheaf (G := G))
        (gsetPresheafMonoidal (G := G)).toLaxMonoidal _ _ ≫
      (gsetPresheaf (G := G)).map (@Functor.LaxMonoidal.μ _ _ _ _ _ _
          (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι
          (ιContinuousGSetIsFiniteMonoidal (G := G)).toLaxMonoidal _ _ ≫
        (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι.map
          (Functor.LaxMonoidal.μ e.functor _ _ ≫ e.functor.map β))
  have hT : Tr (h ▷ _ ≫ evD') = (gsetPresheaf (G := G)).map
      ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι.map (e.functor.map h)) ▷ _ ≫
      Tr evD' := by
    show _ ≫ _ = _
    rw [Functor.μ_comp_map_whiskerRight_comp e.functor,
      @Functor.μ_comp_map_whiskerRight_comp _ _ _ _ _ _
        (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι
        (ιContinuousGSetIsFiniteMonoidal (G := G)),
      @Functor.μ_comp_map_whiskerRight_comp _ _ _ _ _ _ (gsetPresheaf (G := G))
        (gsetPresheafMonoidal (G := G))]
  have hA : Tr (T₀ ◁ k ≫ evD) = _ ◁ (gsetPresheaf (G := G)).map
      ((AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι.map (e.functor.map k)) ≫
      Tr evD := by
    show _ ≫ _ = _
    rw [Functor.μ_comp_map_whiskerLeft_comp e.functor,
      @Functor.μ_comp_map_whiskerLeft_comp _ _ _ _ _ _
        (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).ι
        (ιContinuousGSetIsFiniteMonoidal (G := G)),
      @Functor.μ_comp_map_whiskerLeft_comp _ _ _ _ _ _ (gsetPresheaf (G := G))
        (gsetPresheafMonoidal (G := G))]
  exact congrArg (fun φ ↦ φ.app (SingleObj.star G) (t, m))
    ((hT.symm.trans (congrArg Tr hD)).trans hA)

/-- **`E ℋom(𝒢, ℱ) ≅ Hom_ℤ(E 𝒢, E ℱ)` is natural in `𝒢`.** -/
theorem internalHomTransportIso_naturality :
    (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.map
        (internalHomFiniteLocallyConstantMap J ℱ hℋ hℋ' w) ≫
        (internalHomTransportIso J e 𝒢' ℱ hℋ').hom =
      (internalHomTransportIso J e 𝒢 ℱ hℋ).hom ≫
        ContinuousGAddCommGrp.homIsFiniteMap
          ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.map w)
          (𝟙 _) := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun t ↦ AddMonoidHom.ext fun m ↦ ?_)
  exact ((internalHomTransportIso_hom_apply J e 𝒢' ℱ hℋ' _ m).trans
    (internalHomEvalTransport_naturality J e ℱ hℋ hℋ' w t m)).trans
    (internalHomTransportIso_hom_apply J e 𝒢 ℱ hℋ t _).symm

section Congr

variable {M M' N : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory}

/-- **`ℋom(𝒢, ℱ) ≅ E⁻¹ Hom_ℤ(M, N)`** for `E 𝒢 ≅ M` and `E ℱ ≅ N`: the isomorphism
`internalHomTransportIso` transported along the two given isomorphisms and the unit of `E`. -/
def internalHomTransportCongrIso
    (a : (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj 𝒢 ≅ M)
    (b : (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj ℱ ≅ N) :
    internalHomFiniteLocallyConstant J 𝒢 ℱ hℋ ≅
      (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj
        (ContinuousGAddCommGrp.homIsFinite M N) :=
  (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).unitIso.app _ ≪≫
    (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.mapIso
      (internalHomTransportIso J e 𝒢 ℱ hℋ ≪≫ ContinuousGAddCommGrp.homIsFiniteCongr a b)

/-- **`internalHomTransportCongrIso` is natural in the first variable.** -/
theorem internalHomTransportCongrIso_naturality
    (a : (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj 𝒢 ≅ M)
    (a' : (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj 𝒢' ≅ M')
    (b : (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.obj ℱ ≅ N)
    (v : M' ⟶ M)
    (hv : (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor.map w ≫ a.hom =
      a'.hom ≫ v) :
    internalHomFiniteLocallyConstantMap J ℱ hℋ hℋ' w ≫
        (internalHomTransportCongrIso J e ℱ hℋ' a' b).hom =
      (internalHomTransportCongrIso J e ℱ hℋ a b).hom ≫
        (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.map
          (ContinuousGAddCommGrp.homIsFiniteMap v (𝟙 N)) := by
  let E := finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e
  have h₁ := CommSq.mk (E.unitIso.hom.naturality (internalHomFiniteLocallyConstantMap J ℱ hℋ hℋ' w))
  have h₂ := CommSq.mk (internalHomTransportIso_naturality J e ℱ hℋ hℋ' w)
  have h₃ := CommSq.mk (ContinuousGAddCommGrp.homIsFiniteMap_comp_homIsFiniteCongr a a' b _ v hv)
  exact (h₁.vert_comp ((h₂.vert_comp h₃).map E.inverse)).w

end Congr

end Naturality

end Yoneda

end Stacks.ConstantSheaf

end
