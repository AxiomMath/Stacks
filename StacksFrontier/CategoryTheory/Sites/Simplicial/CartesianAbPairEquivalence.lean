module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianAbPair
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPairEquivalence

/-!
# Cartesian sheaves of abelian groups on a simplicial site are pairs with a cocycle isomorphism

Let `S` be a simplicial-site situation. This file proves the half of Stacks 0D7I concerning sheaves
of abelian groups: the category of cartesian sheaves of abelian groups on the total site is
equivalent to the category of pairs `(ℱ, α)` of
`CategoryTheory.SimplicialSiteSituation.CartesianAbPair`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.cartesianAbSheafEquivCartesianAbPair`: **Stacks 0D7I**
  for sheaves of abelian groups.

## References

* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.Functor
open scoped Simplicial

universe u

namespace CategoryTheory

/-! ### Lifting a commutative group structure through a jointly faithful family -/

section GroupLifting

open scoped CategoryTheory.Obj

universe v v' u₀ u' w

variable {C : Type u₀} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {ι : Type w} {D : ι → Type u'} [∀ i, Category.{v'} (D i)]
  [∀ i, CartesianMonoidalCategory (D i)] [∀ i, BraidedCategory (D i)]

/-- An object of a cartesian monoidal category carries a commutative group structure as soon as
candidate unit, multiplication and inverse maps are given whose images under a jointly faithful
family of braided functors are the operations of commutative group structures downstairs. -/
def liftCommGrp (R : ∀ i, C ⥤ D i) [∀ i, (R i).Braided]
    (hinj : ∀ {X Y : C} (f g : X ⟶ Y), (∀ i, (R i).map f = (R i).map g) → f = g)
    (X : C) [∀ i, GrpObj ((R i).obj X)] [∀ i, IsCommMonObj ((R i).obj X)]
    (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X) (inv : X ⟶ X)
    (ho : ∀ i, (R i).map one = OplaxMonoidal.η (R i) ≫ MonObj.one)
    (hm : ∀ i, (R i).map mul = OplaxMonoidal.δ (R i) X X ≫ MonObj.mul)
    (hi : ∀ i, (R i).map inv = GrpObj.inv) : CommGrp C := by
  letI : GrpObj X :=
    { one := one
      mul := mul
      inv := inv
      one_mul := hinj _ _ (fun i => by
        simp [ho, hm, ← OplaxMonoidal.δ_natural_left_assoc])
      mul_one := hinj _ _ (fun i => by
        simp [ho, hm, ← OplaxMonoidal.δ_natural_right_assoc])
      mul_assoc := hinj _ _ (fun i => by
        simp [hm, ← OplaxMonoidal.δ_natural_left_assoc,
          ← OplaxMonoidal.δ_natural_right_assoc])
      left_inv := hinj _ _ (fun i => by
        simp [ho, hm, hi, OplaxMonoidal.η_of_cartesianMonoidalCategory])
      right_inv := hinj _ _ (fun i => by
        simp [ho, hm, hi, OplaxMonoidal.η_of_cartesianMonoidalCategory]) }
  exact
    { X := X
      comm :=
        { mul_comm := hinj _ _ (fun i => by
            change (R i).map ((β_ X X).hom ≫ mul) = (R i).map mul
            simp [hm, IsCommMonObj.mul_comm]) } }

omit [BraidedCategory C] [∀ i, BraidedCategory (D i)] in
/-- A morphism whose images under a jointly faithful family of monoidal functors are morphisms of
monoid objects is a morphism of monoid objects. -/
theorem isMonHom_of_components (R : ∀ i, C ⥤ D i) [∀ i, (R i).Monoidal]
    (hinj : ∀ {X Y : C} (f g : X ⟶ Y), (∀ i, (R i).map f = (R i).map g) → f = g)
    {X Y : C} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) [∀ i, IsMonHom ((R i).map f)] :
    IsMonHom f where
  one_hom := hinj _ _ (fun i => by
    apply (cancel_epi (LaxMonoidal.ε (R i))).mp
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc, Functor.obj.η_def] using
      IsMonHom.one_hom ((R i).map f))
  mul_hom := hinj _ _ (fun i => by
    apply (cancel_epi (LaxMonoidal.μ (R i) X X)).mp
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc, Functor.obj.μ_def,
      ← LaxMonoidal.μ_natural_assoc] using IsMonHom.mul_hom ((R i).map f))

/-- A commutative group object transported along an isomorphism of its underlying object. -/
def transportCommGrp (G : CommGrp C) {X : C} (e : G.X ≅ X) : CommGrp C := by
  letI : GrpObj X := GrpObj.ofIso e
  refine { X := X, comm := ⟨?_⟩ }
  change (β_ X X).hom ≫ ((e.inv ⊗ₘ e.inv) ≫ MonObj.mul ≫ e.hom) =
    (e.inv ⊗ₘ e.inv) ≫ MonObj.mul ≫ e.hom
  rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]

/-- The transport of a commutative group object along an isomorphism is isomorphic to it. -/
def transportCommGrpIso (G : CommGrp C) {X : C} (e : G.X ≅ X) : G ≅ transportCommGrp G e := by
  refine CommGrp.mkIso e ?_ ?_
  · change MonObj.one ≫ e.hom = MonObj.one ≫ e.hom
    rfl
  · change MonObj.mul ≫ e.hom =
      (e.hom ⊗ₘ e.hom) ≫ (e.inv ⊗ₘ e.inv) ≫ MonObj.mul ≫ e.hom
    simp [← Category.assoc]

end GroupLifting

section Transition

open scoped CategoryTheory.Obj

universe v v' u₀ u'

variable {B : Type u₀} [Category.{v} B] [CartesianMonoidalCategory B]
  {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
  {E : Type u'} [Category.{v'} E] [CartesianMonoidalCategory E]
  (F : B ⥤ D') (G : B ⥤ E) (I : D' ⥤ E)
  [F.Monoidal] [G.Monoidal] [I.Monoidal]
  (t : F ⋙ I ⟶ G) (X : B) [GrpObj (F.obj X)] [GrpObj (G.obj X)]
  [IsMonHom (show I.obj (F.obj X) ⟶ G.obj X from t.app X)]

/-- A natural transformation of monoidal functors whose component at an object is a morphism of
monoid objects carries the transported unit of the source to the unit of the target. -/
theorem component_one_compatible :
    t.app (𝟙_ B) ≫ OplaxMonoidal.η G ≫ MonObj.one =
      I.map (OplaxMonoidal.η F ≫ MonObj.one) ≫ t.app X := by
  apply (cancel_epi (LaxMonoidal.ε (F ⋙ I))).mp
  simp only [← Category.assoc, NatTrans.IsMonoidal.unit]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp,
    LaxMonoidal.comp_ε, ← CategoryTheory.Functor.map_comp_assoc, Monoidal.ε_η,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Functor.obj.η_def, Category.assoc] using
    (IsMonHom.one_hom (show I.obj (F.obj X) ⟶ G.obj X from t.app X)).symm

/-- A natural transformation of monoidal functors whose component at an object is a morphism of
monoid objects carries the transported multiplication of the source to the multiplication of the
target. -/
theorem component_mul_compatible :
    t.app (X ⊗ X) ≫ OplaxMonoidal.δ G X X ≫ MonObj.mul =
      I.map (OplaxMonoidal.δ F X X ≫ MonObj.mul) ≫ t.app X := by
  apply (cancel_epi (LaxMonoidal.μ (F ⋙ I) X X)).mp
  simp only [← Category.assoc, NatTrans.IsMonoidal.tensor]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp,
    LaxMonoidal.comp_μ, ← CategoryTheory.Functor.map_comp_assoc, Monoidal.μ_δ,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Functor.obj.μ_def, Category.assoc] using
    (IsMonHom.mul_hom (show I.obj (F.obj X) ⟶ G.obj X from t.app X)).symm

end Transition

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-! ### Assembling a morphism of total-site sheaves from its restrictions -/

/-- A family of morphisms between the restrictions of two sheaves on the total site, compatible
with the *inverse-image* transitions, comes from a morphism of the sheaves themselves. -/
noncomputable def totalHomOfFibreFamily {F G : Sheaf S.totalTopology (Type u)}
    (β : ∀ n, (S.restrict n).obj F ⟶ (S.restrict n).obj G)
    (hβ : ∀ (m n : SimplexCategory) (φ : m ⟶ n),
      (S.transitionMorphism φ).inverseImage.map (β m) ≫ (S.fiberTransition φ).app G =
        (S.fiberTransition φ).app F ≫ β n) : F ⟶ G :=
  S.totalHomOfFamily β (fun φ => by
    rw [← fiberTransition_adj, ← fiberTransition_adj]
    exact Adjunction.homEquiv_naturality_left_square _ _ _ _ _ (hβ _ _ φ))

/-- The morphism assembled from a compatible family restricts to that family. -/
theorem restrict_map_totalHomOfFibreFamily {F G : Sheaf S.totalTopology (Type u)}
    (β : ∀ n, (S.restrict n).obj F ⟶ (S.restrict n).obj G)
    (hβ : ∀ (m n : SimplexCategory) (φ : m ⟶ n),
      (S.transitionMorphism φ).inverseImage.map (β m) ≫ (S.fiberTransition φ).app G =
        (S.fiberTransition φ).app F ≫ β n) (n : SimplexCategory) :
    (S.restrict n).map (S.totalHomOfFibreFamily β hβ) = β n :=
  S.restrict_map_totalHomOfFamily _ _ n

/-- The restrictions to the simplicial degrees are jointly faithful. -/
theorem restrict_jointly_injective {F G : Sheaf S.totalTopology (Type u)} (f g : F ⟶ G)
    (h : ∀ n, (S.restrict n).map f = (S.restrict n).map g) : f = g :=
  S.total_hom_ext h

/-! ### The cartesian monoidal structures used below -/

section Internal

open scoped CategoryTheory.Obj

attribute [local instance] CategoryTheory.sheafTypeCartesian

attribute [local instance] CategoryTheory.SimplicialSiteSituation.totalBraided

alias abPairTotalBraided := CategoryTheory.SimplicialSiteSituation.totalBraided

attribute [local instance] CategoryTheory.componentCartesian

attribute [local instance] CategoryTheory.componentBraided

alias abPairComponentBraided := CategoryTheory.componentBraided

attribute [local instance] CategoryTheory.SimplicialSiteSituation.restrictBraided

alias abPairRestrictBraided := CategoryTheory.SimplicialSiteSituation.restrictBraided

attribute [local instance] CategoryTheory.SimplicialSiteSituation.transitionBraided

alias abPairInverseImageBraided := CategoryTheory.SimplicialSiteSituation.transitionBraided

/-! ### Cartesian sheaves of abelian groups as cartesian commutative group objects -/

/-- The category of cartesian sheaves of abelian groups on the total site of a simplicial-site
situation. -/
abbrev CartesianAbSheaf (S : SimplicialSiteSituation.{u}) :=
  ObjectProperty.FullSubcategory (IsCartesianAbSheaf S)

/-- The category of commutative group objects in the sheaves of sets on the total site whose
underlying sheaf of sets is cartesian. -/
abbrev CartesianGrpSheaf :=
  ObjectProperty.FullSubcategory
    (fun G : CommGrp (Sheaf S.totalTopology (Type u)) => IsCartesianSheaf S G.X)

/-- Internalizing the group structure of a cartesian sheaf of abelian groups. -/
noncomputable def cartesianAbInternal : CartesianAbSheaf S ⥤ CartesianGrpSheaf S where
  obj F := ⟨(AbelianSheaf.internalSheaf S.totalTopology).obj F.obj, F.property⟩
  map f := ObjectProperty.homMk ((AbelianSheaf.internalSheaf S.totalTopology).map f.hom)
  map_id F := ObjectProperty.hom_ext _ ((AbelianSheaf.internalSheaf S.totalTopology).map_id F.obj)
  map_comp f g :=
    ObjectProperty.hom_ext _ ((AbelianSheaf.internalSheaf S.totalTopology).map_comp f.hom g.hom)

/-- Internalizing the group structure is faithful. -/
instance cartesianAbInternal_faithful : (S.cartesianAbInternal).Faithful where
  map_injective {F G} f g h := by
    apply ObjectProperty.hom_ext
    apply (sheafCompose S.totalTopology (forget Ab.{u})).map_injective
    exact congrArg (fun a => a.hom.hom.hom.hom) h

/-- Internalizing the group structure is full. -/
instance cartesianAbInternal_full : (S.cartesianAbInternal).Full where
  map_surjective {F G} f := by
    refine ⟨ObjectProperty.homMk
      (((AbelianSheaf.internalExternalIso S.totalTopology).app F.obj).inv ≫
        (AbelianSheaf.externalSheaf S.totalTopology).map f.hom ≫
          ((AbelianSheaf.internalExternalIso S.totalTopology).app G.obj).hom), ?_⟩
    apply ObjectProperty.hom_ext
    apply CommGrp.hom_ext
    change 𝟙 _ ≫ f.hom.hom.hom.hom ≫ 𝟙 _ = _
    simp

/-- Internalizing the group structure is essentially surjective. -/
instance cartesianAbInternal_essSurj : (S.cartesianAbInternal).EssSurj where
  mem_essImage G :=
    ⟨⟨(AbelianSheaf.externalSheaf S.totalTopology).obj G.obj, G.property⟩,
      ⟨ObjectProperty.isoMk _ ((AbelianSheaf.externalInternalIso S.totalTopology).app G.obj)⟩⟩

/-- Internalizing the group structure is an equivalence. -/
instance cartesianAbInternal_isEquivalence : (S.cartesianAbInternal).IsEquivalence := {}

/-! ### The abelian pair of a cartesian commutative group object -/

/-- The abelian inverse image of the abelian sheaf attached to a commutative group object is the
abelian sheaf attached to its geometric inverse image. -/
noncomputable def abelianInverseExternalIso {m n : SimplexCategory} (φ : m ⟶ n)
    (G : CommGrp (Sheaf (S.componentTopology m) (Type u))) :
    (abelianTransition S φ).obj
        ((AbelianSheaf.externalSheaf (S.componentTopology m)).obj G) ≅
      (AbelianSheaf.externalSheaf (S.componentTopology n)).obj
        ((S.transitionMorphism φ).inverseImage.mapCommGrp.obj G) :=
  (AbelianSheaf.externalSheaf (S.componentTopology n)).mapIso
    ((S.transitionMorphism φ).inverseImage.mapCommGrp.mapIso
      ((AbelianSheaf.externalInternalIso (S.componentTopology m)).app G))

/-- The canonical transition of a commutative group object in sheaves of sets on the total site,
read on commutative group objects. -/
noncomputable def commGrpFiberTransition (G : CommGrp (Sheaf S.totalTopology (Type u)))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.mapCommGrp.obj
        ((S.restrict m).mapCommGrp.obj G) ⟶ (S.restrict n).mapCommGrp.obj G :=
  (Functor.mapCommGrpCompIso (F := S.restrict.{u, u} m)
      (G := (S.transitionMorphism φ).inverseImage)).inv.app G ≫
    (Functor.mapCommGrpNatTrans (S.fiberTransition φ)).app G

/-- The canonical transition of a commutative group object, read on abelian sheaves. -/
noncomputable def groupAbelianTransition (G : CommGrp (Sheaf S.totalTopology (Type u)))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianTransition S φ).obj
        ((AbelianSheaf.externalSheaf (S.componentTopology m)).obj
          ((S.restrict m).mapCommGrp.obj G)) ⟶
      (AbelianSheaf.externalSheaf (S.componentTopology n)).obj
        ((S.restrict n).mapCommGrp.obj G) :=
  (S.abelianInverseExternalIso φ ((S.restrict m).mapCommGrp.obj G)).hom ≫
    (AbelianSheaf.externalSheaf (S.componentTopology n)).map (S.commGrpFiberTransition G φ)

/-- Forgetting the abelian group structure of the abelian sheaf attached to a morphism of
commutative group objects gives back the morphism of sheaves of sets. -/
theorem abelianForget_map_externalSheaf_map {n : SimplexCategory}
    {X Y : CommGrp (Sheaf (S.componentTopology n) (Type u))} (f : X ⟶ Y) :
    (S.abelianForget n).map ((AbelianSheaf.externalSheaf (S.componentTopology n)).map f) =
      f.hom.hom.hom := rfl

/-- On underlying sheaves of sets the identification of the abelian inverse image with the abelian
sheaf of the geometric inverse image is the geometric inverse image of an identity. -/
theorem abelianForget_map_abelianInverseExternalIso_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (G : CommGrp (Sheaf (S.componentTopology m) (Type u))) :
    (S.abelianForget n).map (S.abelianInverseExternalIso φ G).hom =
      (S.transitionMorphism φ).inverseImage.map (𝟙 G.X) := rfl

/-- The underlying map of sheaves of sets of the transition read on commutative group objects is
the canonical transition of Stacks 09WF. -/
theorem commGrpFiberTransition_hom (G : CommGrp (Sheaf S.totalTopology (Type u)))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.commGrpFiberTransition G φ).hom.hom.hom = (S.fiberTransition φ).app G.X := by
  change 𝟙 _ ≫ (S.fiberTransition φ).app G.X = _
  rw [Category.id_comp]

/-- On underlying sheaves of sets the abelian transition of a commutative group object is the
canonical transition of Stacks 09WF, preceded by the inverse image of an identity. -/
theorem abelianForget_map_groupAbelianTransition'
    (G : CommGrp (Sheaf S.totalTopology (Type u))) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.abelianForget n).map (S.groupAbelianTransition G φ) =
      (S.transitionMorphism φ).inverseImage.map (𝟙 ((S.restrict m).obj G.X)) ≫
        𝟙 ((S.transitionMorphism φ).inverseImage.obj ((S.restrict m).obj G.X)) ≫
        (S.fiberTransition φ).app G.X := rfl

/-- On underlying sheaves of sets the abelian transition of a commutative group object is the
canonical transition of Stacks 09WF. -/
theorem abelianForget_map_groupAbelianTransition
    (G : CommGrp (Sheaf S.totalTopology (Type u))) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.abelianForget n).map (S.groupAbelianTransition G φ) =
      (S.fiberTransition φ).app G.X :=
  (S.abelianForget_map_groupAbelianTransition' G φ).trans (by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp])

/-- For a cartesian commutative group object the abelian transitions are invertible. -/
theorem groupAbelianTransition_isIso (G : CartesianGrpSheaf S) {m n : SimplexCategory}
    (φ : m ⟶ n) : IsIso (S.groupAbelianTransition G.obj φ) := by
  let : IsIso ((S.abelianForget n).map (S.groupAbelianTransition G.obj φ)) := by
    rw [S.abelianForget_map_groupAbelianTransition]
    exact G.property φ
  exact isIso_of_reflects_iso _ (S.abelianForget n)

/-- For a cartesian commutative group object, the comparison isomorphism between the two abelian
inverse images of its degree-zero restriction to degree one. -/
noncomputable def groupSheafComparisonIso (G : CartesianGrpSheaf S) :
    (abelianTransition S (SimplexCategory.δ (1 : Fin 2))).obj
        ((AbelianSheaf.externalSheaf (S.componentTopology ⦋0⦌)).obj
          ((S.restrict ⦋0⦌).mapCommGrp.obj G.obj)) ≅
      (abelianTransition S (SimplexCategory.δ (0 : Fin 2))).obj
        ((AbelianSheaf.externalSheaf (S.componentTopology ⦋0⦌)).obj
          ((S.restrict ⦋0⦌).mapCommGrp.obj G.obj)) := by
  have := S.groupAbelianTransition_isIso G (SimplexCategory.δ (1 : Fin 2))
  have := S.groupAbelianTransition_isIso G (SimplexCategory.δ (0 : Fin 2))
  exact asIso (S.groupAbelianTransition G.obj (SimplexCategory.δ (1 : Fin 2))) ≪≫
    (asIso (S.groupAbelianTransition G.obj (SimplexCategory.δ (0 : Fin 2)))).symm

/-- On underlying sheaves of sets the comparison isomorphism of a cartesian commutative group
object is the comparison isomorphism of the underlying cartesian sheaf of sets. -/
theorem abelianForget_map_groupSheafComparisonIso (G : CartesianGrpSheaf S) :
    (S.abelianForget ⦋1⦌).map (S.groupSheafComparisonIso G).hom =
      (S.cartesianIso ⟨G.obj.X, G.property⟩).hom := by
  let := S.groupAbelianTransition_isIso G (SimplexCategory.δ (0 : Fin 2))
  let : IsIso ((S.fiberTransition (SimplexCategory.δ (0 : Fin 2))).app G.obj.X) :=
    G.property (SimplexCategory.δ (0 : Fin 2))
  simp only [groupSheafComparisonIso, cartesianIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv,
    S.abelianForget_map_groupAbelianTransition]
  rfl

/-- The abelian pair attached to a cartesian commutative group object in sheaves of sets. -/
noncomputable def groupSheafToPair (G : CartesianGrpSheaf S) : CartesianAbPair S where
  sheaf := (AbelianSheaf.externalSheaf (S.componentTopology ⦋0⦌)).obj
    ((S.restrict ⦋0⦌).mapCommGrp.obj G.obj)
  iso := S.groupSheafComparisonIso G
  cocycle := by
    apply (S.abelianForget ⦋2⦌).map_injective
    simp only [CategoryTheory.Functor.map_comp, abelianGlueLeft, abelianGlueMiddle,
      abelianGlueRight, S.abelianForget_map_abelianGlueOfEq_hom,
      S.abelianForget_map_abelianGlueOfEq_inv, S.abelianForget_map_abelianTransition_map,
      S.abelianForget_map_groupSheafComparisonIso]
    exact S.cartesianIso_cocycle ⟨G.obj.X, G.property⟩

/-- The degree-zero sheaf of the abelian pair attached to a cartesian commutative group object,
read on underlying sheaves of sets. -/
theorem abelianForget_map_externalSheaf_mapCommGrp_map
    {G H : CommGrp (Sheaf S.totalTopology (Type u))} (f : G ⟶ H) :
    (S.abelianForget ⦋0⦌).map ((AbelianSheaf.externalSheaf (S.componentTopology ⦋0⦌)).map
        ((S.restrict ⦋0⦌).mapCommGrp.map f)) = (S.restrict ⦋0⦌).map f.hom.hom.hom := rfl

/-- The functor from cartesian commutative group objects in sheaves of sets on the total site to
abelian pairs. -/
noncomputable def groupSheafToPairFunctor : CartesianGrpSheaf S ⥤ CartesianAbPair S where
  obj := S.groupSheafToPair
  map {G H} f :=
    { map := (AbelianSheaf.externalSheaf (S.componentTopology ⦋0⦌)).map
        ((S.restrict ⦋0⦌).mapCommGrp.map f.hom)
      comm := by
        apply (S.abelianForget ⦋1⦌).map_injective
        simp only [CategoryTheory.Functor.map_comp, S.abelianForget_map_abelianTransition_map,
          S.abelianForget_map_externalSheaf_mapCommGrp_map, groupSheafToPair,
          S.abelianForget_map_groupSheafComparisonIso]
        exact S.cartesianIso_naturality
          (ObjectProperty.homMk f.hom.hom.hom.hom :
            (⟨G.obj.X, G.property⟩ : CartesianSheaf S) ⟶ ⟨H.obj.X, H.property⟩) }
  map_id G := CartesianAbPair.hom_ext S (((S.restrict ⦋0⦌).mapCommGrp ⋙
    AbelianSheaf.externalSheaf (S.componentTopology ⦋0⦌)).map_id G.obj)
  map_comp f g := CartesianAbPair.hom_ext S (((S.restrict ⦋0⦌).mapCommGrp ⋙
    AbelianSheaf.externalSheaf (S.componentTopology ⦋0⦌)).map_comp f.hom g.hom)

/-- A morphism between the abelian sheaves attached to two commutative group objects, read as a
morphism of commutative group objects. -/
noncomputable def externalHomInternal (n : SimplexCategory)
    {G H : CommGrp (Sheaf (S.componentTopology n) (Type u))}
    (f : (AbelianSheaf.externalSheaf (S.componentTopology n)).obj G ⟶
      (AbelianSheaf.externalSheaf (S.componentTopology n)).obj H) : G ⟶ H :=
  ((AbelianSheaf.externalInternalIso (S.componentTopology n)).app G).inv ≫
    (AbelianSheaf.internalSheaf (S.componentTopology n)).map f ≫
    ((AbelianSheaf.externalInternalIso (S.componentTopology n)).app H).hom

/-- Reading a morphism of abelian sheaves as a morphism of commutative group objects does not
change the underlying map of sheaves of sets. -/
theorem externalHomInternal_hom (n : SimplexCategory)
    {G H : CommGrp (Sheaf (S.componentTopology n) (Type u))}
    (f : (AbelianSheaf.externalSheaf (S.componentTopology n)).obj G ⟶
      (AbelianSheaf.externalSheaf (S.componentTopology n)).obj H) :
    (S.externalHomInternal n f).hom.hom.hom = (S.abelianForget n).map f := by
  change 𝟙 _ ≫ (S.abelianForget n).map f ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- The degree-zero commutative group object of a cartesian commutative group object. -/
noncomputable abbrev groupZero (G : CartesianGrpSheaf S) :
    CommGrp (Sheaf (S.componentTopology ⦋0⦌) (Type u)) :=
  (S.restrict ⦋0⦌).mapCommGrp.obj G.obj

/-- A morphism of abelian pairs of cartesian commutative group objects, read as a morphism of their
degree-zero commutative group objects. -/
noncomputable def groupPairHomInternal {G H : CartesianGrpSheaf S}
    (a : S.groupSheafToPair G ⟶ S.groupSheafToPair H) : S.groupZero G ⟶ S.groupZero H :=
  S.externalHomInternal ⦋0⦌ (G := S.groupZero G) (H := S.groupZero H) a.map

/-- The underlying map of sheaves of sets of a morphism of abelian pairs. -/
theorem groupPairHomInternal_hom {G H : CartesianGrpSheaf S}
    (a : S.groupSheafToPair G ⟶ S.groupSheafToPair H) :
    (S.groupPairHomInternal a).hom.hom.hom = (S.abelianForget ⦋0⦌).map a.map :=
  S.externalHomInternal_hom ⦋0⦌ (G := S.groupZero G) (H := S.groupZero H) a.map

/-- Forgetting the group structure of a morphism of the abelian pairs of two cartesian commutative
group objects gives a morphism of the pairs of their underlying cartesian sheaves of sets. -/
noncomputable def groupPairHomUnderlying {G H : CartesianGrpSheaf S}
    (a : S.groupSheafToPair G ⟶ S.groupSheafToPair H) :
    S.pairOfCartesianSheaf ⟨G.obj.X, G.property⟩ ⟶
      S.pairOfCartesianSheaf ⟨H.obj.X, H.property⟩ where
  map := (S.groupPairHomInternal a).hom.hom.hom
  comm := by
    have h := congrArg (S.abelianForget ⦋1⦌).map a.comm
    simp only [CategoryTheory.Functor.map_comp, S.abelianForget_map_abelianTransition_map,
      groupSheafToPair, S.abelianForget_map_groupSheafComparisonIso] at h
    rwa [S.groupPairHomInternal_hom]

/-- The functor to abelian pairs is faithful. -/
instance groupSheafToPairFunctor_faithful : S.groupSheafToPairFunctor.Faithful where
  map_injective {G H} f g h := by
    apply ObjectProperty.hom_ext
    apply CommGrp.hom_ext
    have he : (ObjectProperty.homMk f.hom.hom.hom.hom :
        (⟨G.obj.X, G.property⟩ : CartesianSheaf S) ⟶ ⟨H.obj.X, H.property⟩) =
        ObjectProperty.homMk g.hom.hom.hom.hom := by
      apply S.cartesianPairFunctor.map_injective
      apply CartesianPair.hom_ext S
      exact congrArg (fun a => (S.abelianForget ⦋0⦌).map (CartesianAbPair.Hom.map a)) h
    exact congrArg (fun a => a.hom) he

/-! ### Fullness of the functor to abelian pairs -/

/-- The morphism of cartesian sheaves of sets attached to a morphism of their pairs. -/
noncomputable def cartesianHomOfPair {F G : CartesianSheaf S}
    (a : S.pairOfCartesianSheaf F ⟶ S.pairOfCartesianSheaf G) : F.obj ⟶ G.obj :=
  S.totalHomOfFibreFamily
    (fun n => S.cartesianHomAlong (F := F) (G := G) a.map
      (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len)))
    (fun _ _ φ => S.cartesianHomAlong_naturality a.map a.comm φ)

/-- The morphism of cartesian sheaves attached to a morphism of pairs restricts, in degree `n`, to
the candidate morphism along the last vertex. -/
theorem restrict_map_cartesianHomOfPair {F G : CartesianSheaf S}
    (a : S.pairOfCartesianSheaf F ⟶ S.pairOfCartesianSheaf G) (n : SimplexCategory) :
    (S.restrict n).map (S.cartesianHomOfPair a) =
      S.cartesianHomAlong (F := F) (G := G) a.map
        (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len)) :=
  S.restrict_map_totalHomOfFibreFamily _
    (fun _ _ φ => S.cartesianHomAlong_naturality a.map a.comm φ) n

/-- The underlying map of sheaves of sets of a composite of morphisms of commutative group
objects. -/
theorem commGrp_comp_hom {m : SimplexCategory}
    {X Y Z : CommGrp (Sheaf (S.componentTopology m) (Type u))} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.hom.hom = f.hom.hom.hom ≫ g.hom.hom.hom := rfl

/-- The geometric inverse image of a morphism of commutative group objects acts on the underlying
sheaves of sets as the geometric inverse image. -/
theorem mapCommGrp_map_hom {m n : SimplexCategory} (φ : m ⟶ n)
    {X Y : CommGrp (Sheaf (S.componentTopology m) (Type u))} (f : X ⟶ Y) :
    ((S.transitionMorphism φ).inverseImage.mapCommGrp.map f).hom.hom.hom =
      (S.transitionMorphism φ).inverseImage.map f.hom.hom.hom := rfl

/-- For a cartesian commutative group object the canonical transition along a vertex is an
isomorphism of commutative group objects. -/
noncomputable def commGrpFiberTransitionIso (G : CartesianGrpSheaf S) {n : SimplexCategory}
    (ψ : ⦋0⦌ ⟶ n) :
    (S.transitionMorphism ψ).inverseImage.mapCommGrp.obj (S.groupZero G) ≅
      ((S.restrict.{u, u} n).mapCommGrp).obj G.obj := by
  have h := (S.commGrpFiberTransition G.obj ψ).hom.hom.isMonHom_hom
  rw [S.commGrpFiberTransition_hom] at h
  exact CommGrp.mkIso (@asIso _ _ _ _ ((S.fiberTransition ψ).app G.obj.X) (G.property ψ))
    h.one_hom h.mul_hom

/-- The underlying map of sheaves of sets of the transition isomorphism. -/
theorem commGrpFiberTransitionIso_hom_hom (G : CartesianGrpSheaf S) {n : SimplexCategory}
    (ψ : ⦋0⦌ ⟶ n) :
    (S.commGrpFiberTransitionIso G ψ).hom.hom.hom.hom =
      (S.fiberTransition ψ).app G.obj.X := rfl

/-- The underlying map of sheaves of sets of the inverse of the transition isomorphism. -/
theorem commGrpFiberTransitionIso_inv_hom (G : CartesianGrpSheaf S) {n : SimplexCategory}
    (ψ : ⦋0⦌ ⟶ n) :
    (S.commGrpFiberTransitionIso G ψ).inv.hom.hom.hom =
      @inv _ _ _ _ ((S.fiberTransition ψ).app G.obj.X) (G.property ψ) := rfl

/-- The candidate morphism along a vertex, read on commutative group objects. -/
noncomputable def commGrpHomAlong {G H : CartesianGrpSheaf S} (b : S.groupZero G ⟶ S.groupZero H)
    {n : SimplexCategory} (ψ : ⦋0⦌ ⟶ n) :
    ((S.restrict.{u, u} n).mapCommGrp).obj G.obj ⟶
      ((S.restrict.{u, u} n).mapCommGrp).obj H.obj :=
  (S.commGrpFiberTransitionIso G ψ).inv ≫
    (S.transitionMorphism ψ).inverseImage.mapCommGrp.map b ≫
    (S.commGrpFiberTransitionIso H ψ).hom

/-- The underlying map of sheaves of sets of the candidate morphism along a vertex, read on
commutative group objects, is the candidate morphism along that vertex. -/
theorem commGrpHomAlong_hom {G H : CartesianGrpSheaf S} (b : S.groupZero G ⟶ S.groupZero H)
    {n : SimplexCategory} (ψ : ⦋0⦌ ⟶ n) :
    (S.commGrpHomAlong b ψ).hom.hom.hom =
      S.cartesianHomAlong (F := ⟨G.obj.X, G.property⟩) (G := ⟨H.obj.X, H.property⟩)
        b.hom.hom.hom ψ := by
  rw [commGrpHomAlong, S.commGrp_comp_hom, S.commGrp_comp_hom,
    S.commGrpFiberTransitionIso_inv_hom, S.commGrpFiberTransitionIso_hom_hom,
    S.mapCommGrp_map_hom]
  rfl

/-- The candidate morphism along a vertex attached to a morphism of the degree-zero commutative
group objects is a morphism of commutative group objects. -/
theorem cartesianHomAlong_isMonHom {G H : CartesianGrpSheaf S}
    (b : S.groupZero G ⟶ S.groupZero H) {n : SimplexCategory} (ψ : ⦋0⦌ ⟶ n) :
    IsMonHom (S.cartesianHomAlong (F := ⟨G.obj.X, G.property⟩) (G := ⟨H.obj.X, H.property⟩)
      b.hom.hom.hom ψ) := by
  rw [← S.commGrpHomAlong_hom b ψ]
  exact (S.commGrpHomAlong b ψ).hom.hom.isMonHom_hom

/-- The morphism of sheaves of sets attached to a morphism of abelian pairs is a morphism of
commutative group objects in each simplicial degree, hence a morphism of commutative group objects
on the total site. -/
theorem cartesianHomOfPair_isMonHom {G H : CartesianGrpSheaf S}
    (a : S.groupSheafToPair G ⟶ S.groupSheafToPair H) :
    IsMonHom (S.cartesianHomOfPair (S.groupPairHomUnderlying a)) := by
  suffices hc : ∀ n, IsMonHom ((S.restrict n).map
      (S.cartesianHomOfPair (S.groupPairHomUnderlying a))) by
    let := hc
    exact isMonHom_of_components S.restrict.{u, u} S.restrict_jointly_injective _
  intro n
  rw [S.restrict_map_cartesianHomOfPair]
  exact S.cartesianHomAlong_isMonHom (S.groupPairHomInternal a) _

/-- The functor to abelian pairs is full. -/
instance groupSheafToPairFunctor_full : S.groupSheafToPairFunctor.Full where
  map_surjective {G H} a := by
    let := S.cartesianHomOfPair_isMonHom a
    refine ⟨ObjectProperty.homMk (InducedCategory.homMk
      (Grp.homMk (S.cartesianHomOfPair (S.groupPairHomUnderlying a)))), ?_⟩
    apply CartesianAbPair.hom_ext S
    apply (S.abelianForget ⦋0⦌).map_injective
    change (S.restrict ⦋0⦌).map (S.cartesianHomOfPair (S.groupPairHomUnderlying a)) = _
    rw [S.restrict_map_cartesianHomOfPair,
      show SimplexCategory.const (SimplexCategory.mk 0) ⦋0⦌ (Fin.last ⦋0⦌.len) = 𝟙 ⦋0⦌ by
        apply SimplexCategory.Hom.ext_zero_left
        rfl]
    exact S.cartesianHomAlong_id (S.groupPairHomUnderlying a).map

/-! ### Essential surjectivity: the abelian sheaf descended from an abelian pair -/

/-- The underlying map of sheaves of sets of the inverse of the abelian compositor at a
factorization is the inverse of the compositor at that factorization. -/
theorem abelianForget_map_abelianPasteIsoOfEq_inv {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (θ : l ⟶ n) (h : ψ ≫ φ = θ) (F : Sheaf (S.componentTopology l) Ab.{u}) :
    (S.abelianForget n).map (S.abelianPasteIsoOfEq ψ φ θ h F).inv =
      (S.pasteIsoOfEq ψ φ θ h ((S.abelianForget l).obj F)).inv :=
  (S.abelianForget n).map_inv_of_map_hom (S.abelianPasteIsoOfEq ψ φ θ h F)
    (S.pasteIsoOfEq ψ φ θ h ((S.abelianForget l).obj F))
    (S.abelianForget_map_abelianPasteIsoOfEq_hom ψ φ θ h F)

/-- The sheaf of abelian groups in degree `n` of the system attached to an abelian pair: the
abelian inverse image of its degree-zero sheaf along the last vertex of `⦋n⦌`. -/
noncomputable def abelianPairSheaf (A : CartesianAbPair S) (n : SimplexCategory) :
    Sheaf (S.componentTopology n) Ab.{u} :=
  (abelianTransition S
    (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))).obj A.sheaf

/-- The abelian transport of the comparison isomorphism along an edge of a simplex. -/
noncomputable def abelianTransportAlongIso (A : CartesianAbPair S) {n : SimplexCategory}
    (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n) (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    (abelianTransition S v).obj A.sheaf ≅ (abelianTransition S w).obj A.sheaf :=
  (S.abelianPasteIsoOfEq _ φ v h₁ A.sheaf).symm ≪≫
    (abelianTransition S φ).mapIso A.iso ≪≫ S.abelianPasteIsoOfEq _ φ w h₀ A.sheaf

/-- The abelian transport along the edge of `⦋n⦌` joining two vertices `i ≤ j`. -/
noncomputable def abelianEdgeTransportIso (A : CartesianAbPair S) {n : ℕ} (i j : Fin (n + 1))
    (h : i ≤ j) :
    (abelianTransition S
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)).obj A.sheaf ≅
      (abelianTransition S
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j)).obj A.sheaf :=
  S.abelianTransportAlongIso A (SimplexCategory.mkOfLe i j h) _ _
    (SimplexCategory.delta_one_comp_mkOfLe n i j h)
    (SimplexCategory.delta_zero_comp_mkOfLe n i j h)

/-- The abelian identification of the inverse image of the degree-zero sheaf along a vertex of
`⦋m⦌`, pulled back along a simplex map, with its inverse image along the image vertex. -/
noncomputable def abelianVertexPaste {m n : SimplexCategory} (φ : m ⟶ n)
    (i : Fin (m.len + 1)) (F : Sheaf (S.componentTopology ⦋0⦌) Ab.{u}) :
    (abelianTransition S φ).obj ((abelianTransition S
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m.len) i)).obj F) ≅
      (abelianTransition S (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk n.len) (φ.toOrderHom i))).obj F :=
  S.abelianPasteIsoOfEq _ φ _ (SimplexCategory.vertexMap_comp φ i) F

/-- The transition in the abelian system attached to an abelian pair. -/
noncomputable def abelianPairTransition (A : CartesianAbPair S) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (abelianTransition S φ).obj (S.abelianPairSheaf A m) ⟶ S.abelianPairSheaf A n :=
  (S.abelianVertexPaste φ (Fin.last m.len) A.sheaf).hom ≫
    (S.abelianEdgeTransportIso A (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len)
      (Fin.le_last _)).hom

/-- On underlying sheaves of sets the abelian transport along an edge is the transport along that
edge for the underlying pair. -/
theorem abelianForget_map_abelianTransportAlongIso_hom (A : CartesianAbPair S)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    (S.abelianForget n).map (S.abelianTransportAlongIso A φ v w h₁ h₀).hom =
      S.transportAlong (S.abelianPairUnderlying A).sheaf (S.abelianPairUnderlying A).iso
        φ v w h₁ h₀ := by
  change (S.abelianForget n).map ((S.abelianPasteIsoOfEq _ φ v h₁ A.sheaf).inv ≫
    ((abelianTransition S φ).map A.iso.hom ≫
      (S.abelianPasteIsoOfEq _ φ w h₀ A.sheaf).hom)) = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    S.abelianForget_map_abelianPasteIsoOfEq_inv, S.abelianForget_map_abelianPasteIsoOfEq_hom,
    S.abelianForget_map_abelianTransition_map]
  rfl

/-- On underlying sheaves of sets the abelian transport along an edge of `⦋n⦌` is the transport
along that edge for the underlying pair. -/
theorem abelianForget_map_abelianEdgeTransportIso_hom (A : CartesianAbPair S) {n : ℕ}
    (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.abelianForget (SimplexCategory.mk n)).map (S.abelianEdgeTransportIso A i j h).hom =
      S.edgeTransport (S.abelianPairUnderlying A).sheaf (S.abelianPairUnderlying A).iso i j h :=
  S.abelianForget_map_abelianTransportAlongIso_hom A _ _ _ _ _

/-- On underlying sheaves of sets the abelian vertex identification is the vertex identification of
the underlying pair. -/
theorem abelianForget_map_abelianVertexPaste_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (i : Fin (m.len + 1)) (F : Sheaf (S.componentTopology ⦋0⦌) Ab.{u}) :
    (S.abelianForget n).map (S.abelianVertexPaste φ i F).hom =
      (S.vertexPaste φ i ((S.abelianForget ⦋0⦌).obj F)).hom :=
  S.abelianForget_map_abelianPasteIsoOfEq_hom _ φ _ _ F

/-- On underlying sheaves of sets the abelian transition of the system attached to an abelian pair
is the transition of the system attached to the underlying pair. -/
theorem abelianForget_map_abelianPairTransition (A : CartesianAbPair S)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.abelianForget n).map (S.abelianPairTransition A φ) =
      S.pairTransition (S.abelianPairUnderlying A) φ := by
  change (S.abelianForget n).map ((S.abelianVertexPaste φ (Fin.last m.len) A.sheaf).hom ≫
    (S.abelianEdgeTransportIso A (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len)
      (Fin.le_last _)).hom) = _
  rw [CategoryTheory.Functor.map_comp, S.abelianForget_map_abelianVertexPaste_hom,
    S.abelianForget_map_abelianEdgeTransportIso_hom]
  rfl

/-- The internal commutative group in degree `n` of the system attached to an abelian pair. -/
noncomputable def pairComponentGroup (A : CartesianAbPair S) (n : SimplexCategory) :
    CommGrp (Sheaf (S.componentTopology n) (Type u)) :=
  (AbelianSheaf.internalSheaf (S.componentTopology n)).obj (S.abelianPairSheaf A n)

/-- The counit of the identification of abelian sheaves with commutative group objects is the
identity on underlying sheaves of sets. -/
theorem externalInternalIso_inv_hom {n : SimplexCategory}
    (Y : CommGrp (Sheaf (S.componentTopology n) (Type u))) :
    ((AbelianSheaf.externalInternalIso (S.componentTopology n)).app Y).inv.hom.hom.hom =
      𝟙 Y.X := rfl

/-- Internalizing a morphism of abelian sheaves does not change the underlying map of sheaves of
sets. -/
theorem internalSheaf_map_hom {n : SimplexCategory}
    {X Y : Sheaf (S.componentTopology n) Ab.{u}} (f : X ⟶ Y) :
    ((AbelianSheaf.internalSheaf (S.componentTopology n)).map f).hom.hom.hom =
      (S.abelianForget n).map f := rfl

/-- The transition of the system of internal commutative groups attached to an abelian pair. -/
noncomputable def pairComponentGroupTransition (A : CartesianAbPair S) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.mapCommGrp.obj (S.pairComponentGroup A m) ⟶
      S.pairComponentGroup A n :=
  ((AbelianSheaf.externalInternalIso (S.componentTopology n)).app
      ((S.transitionMorphism φ).inverseImage.mapCommGrp.obj (S.pairComponentGroup A m))).inv ≫
    (AbelianSheaf.internalSheaf (S.componentTopology n)).map (S.abelianPairTransition A φ)

/-- On underlying sheaves of sets the transition of the system of internal commutative groups
attached to an abelian pair is the transition of the underlying pair. -/
theorem pairComponentGroupTransition_hom (A : CartesianAbPair S) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (S.pairComponentGroupTransition A φ).hom.hom.hom =
      S.pairTransition (S.abelianPairUnderlying A) φ := by
  change ((AbelianSheaf.externalInternalIso (S.componentTopology n)).app
        ((S.transitionMorphism φ).inverseImage.mapCommGrp.obj
          (S.pairComponentGroup A m))).inv.hom.hom.hom ≫
      ((AbelianSheaf.internalSheaf (S.componentTopology n)).map
        (S.abelianPairTransition A φ)).hom.hom.hom = _
  rw [S.externalInternalIso_inv_hom, S.internalSheaf_map_hom,
    S.abelianForget_map_abelianPairTransition]
  exact Category.id_comp _

/-- The internal commutative group of the degree-`n` restriction of the sheaf of sets descended
from the pair underlying an abelian pair. -/
noncomputable def pairRestrictionGroup (A : CartesianAbPair S) (n : SimplexCategory) :
    CommGrp (Sheaf (S.componentTopology n) (Type u)) :=
  transportCommGrp (S.pairComponentGroup A n)
    (S.pairRestrictIso (S.abelianPairUnderlying A) n).symm

/-- The transported commutative group is the one attached to the pair. -/
noncomputable def pairRestrictionGroupIso (A : CartesianAbPair S) (n : SimplexCategory) :
    S.pairRestrictionGroup A n ≅ S.pairComponentGroup A n :=
  (transportCommGrpIso (S.pairComponentGroup A n)
    (S.pairRestrictIso (S.abelianPairUnderlying A) n).symm).symm

/-- The underlying map of sheaves of sets of the identification of the two commutative group
structures. -/
theorem pairRestrictionGroupIso_hom_hom (A : CartesianAbPair S) (n : SimplexCategory) :
    (S.pairRestrictionGroupIso A n).hom.hom.hom.hom =
      (S.pairRestrictIso (S.abelianPairUnderlying A) n).hom := rfl

/-- The underlying map of sheaves of sets of the inverse of that identification. -/
theorem pairRestrictionGroupIso_inv_hom (A : CartesianAbPair S) (n : SimplexCategory) :
    (S.pairRestrictionGroupIso A n).inv.hom.hom.hom =
      (S.pairRestrictIso (S.abelianPairUnderlying A) n).inv := rfl

/-- The transition of the system of commutative groups on the restrictions of the descended sheaf
of sets. -/
noncomputable def pairRestrictionGroupTransition (A : CartesianAbPair S)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.mapCommGrp.obj (S.pairRestrictionGroup A m) ⟶
      S.pairRestrictionGroup A n :=
  (S.transitionMorphism φ).inverseImage.mapCommGrp.map (S.pairRestrictionGroupIso A m).hom ≫
    S.pairComponentGroupTransition A φ ≫ (S.pairRestrictionGroupIso A n).inv

/-- On underlying sheaves of sets that transition is the canonical transition of the descended
sheaf of sets. -/
theorem pairRestrictionGroupTransition_hom (A : CartesianAbPair S) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (S.pairRestrictionGroupTransition A φ).hom.hom.hom =
      (S.fiberTransition φ).app (S.pairTotalSheaf (S.abelianPairUnderlying A)) := by
  change ((S.transitionMorphism φ).inverseImage.mapCommGrp.map
        (S.pairRestrictionGroupIso A m).hom).hom.hom.hom ≫
      (S.pairComponentGroupTransition A φ).hom.hom.hom ≫
      (S.pairRestrictionGroupIso A n).inv.hom.hom.hom = _
  rw [S.mapCommGrp_map_hom, S.pairRestrictionGroupIso_hom_hom,
    S.pairComponentGroupTransition_hom, S.pairRestrictionGroupIso_inv_hom,
    S.fiberTransition_pairTotalSheaf]
  rfl

/-! ### Lifting the group structures to the total site -/

section TotalGroup

variable (F : Sheaf S.totalTopology (Type u))
  [∀ n, GrpObj ((S.restrict.{u, u} n).obj F)]
  [∀ n, IsCommMonObj ((S.restrict.{u, u} n).obj F)]
  (ht : ∀ (m n : SimplexCategory) (φ : m ⟶ n),
    IsMonHom (show (S.transitionMorphism φ).inverseImage.obj ((S.restrict.{u, u} m).obj F) ⟶
      (S.restrict.{u, u} n).obj F from (S.fiberTransition φ).app F))

omit [∀ n, IsCommMonObj ((S.restrict.{u, u} n).obj F)] in
include ht in
/-- The units of the degreewise group structures are compatible with the transitions. -/
theorem totalOne_compat {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.map
          (OplaxMonoidal.η (S.restrict.{u, u} m) ≫
            MonObj.one (X := (S.restrict.{u, u} m).obj F)) ≫
        (S.fiberTransition φ).app F =
      (S.fiberTransition φ).app (𝟙_ (Sheaf S.totalTopology (Type u))) ≫
        (OplaxMonoidal.η (S.restrict.{u, u} n) ≫
          MonObj.one (X := (S.restrict.{u, u} n).obj F)) := by
  let := ht m n φ
  exact (component_one_compatible (S.restrict.{u, u} m) (S.restrict.{u, u} n)
    (S.transitionMorphism φ).inverseImage (S.fiberTransition φ) F).symm

omit [∀ n, IsCommMonObj ((S.restrict.{u, u} n).obj F)] in
include ht in
/-- The multiplications of the degreewise group structures are compatible with the transitions. -/
theorem totalMul_compat {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.map
          (OplaxMonoidal.δ (S.restrict.{u, u} m) F F ≫
            MonObj.mul (X := (S.restrict.{u, u} m).obj F)) ≫
        (S.fiberTransition φ).app F =
      (S.fiberTransition φ).app (F ⊗ F) ≫
        (OplaxMonoidal.δ (S.restrict.{u, u} n) F F ≫
          MonObj.mul (X := (S.restrict.{u, u} n).obj F)) := by
  let := ht m n φ
  exact (component_mul_compatible (S.restrict.{u, u} m) (S.restrict.{u, u} n)
    (S.transitionMorphism φ).inverseImage (S.fiberTransition φ) F).symm

omit [∀ n, IsCommMonObj ((S.restrict.{u, u} n).obj F)] in
include ht in
/-- The inverses of the degreewise group structures are compatible with the transitions. -/
theorem totalNeg_compat {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.map
          (GrpObj.inv (X := (S.restrict.{u, u} m).obj F)) ≫ (S.fiberTransition φ).app F =
      (S.fiberTransition φ).app F ≫ GrpObj.inv (X := (S.restrict.{u, u} n).obj F) := by
  let := ht m n φ
  exact GrpObj.inv_hom (show (S.transitionMorphism φ).inverseImage.obj
    ((S.restrict.{u, u} m).obj F) ⟶ (S.restrict.{u, u} n).obj F from
      (S.fiberTransition φ).app F)

/-- The unit of the commutative group structure assembled from the degreewise ones. -/
noncomputable def totalOne : 𝟙_ (Sheaf S.totalTopology (Type u)) ⟶ F :=
  S.totalHomOfFibreFamily
    (fun n => OplaxMonoidal.η (S.restrict.{u, u} n) ≫
      MonObj.one (X := (S.restrict.{u, u} n).obj F))
    (fun _ _ φ => S.totalOne_compat F ht φ)

/-- The multiplication of the commutative group structure assembled from the degreewise ones. -/
noncomputable def totalMul : F ⊗ F ⟶ F :=
  S.totalHomOfFibreFamily
    (fun n => OplaxMonoidal.δ (S.restrict.{u, u} n) F F ≫
      MonObj.mul (X := (S.restrict.{u, u} n).obj F))
    (fun _ _ φ => S.totalMul_compat F ht φ)

/-- The inverse of the commutative group structure assembled from the degreewise ones. -/
noncomputable def totalNeg : F ⟶ F :=
  S.totalHomOfFibreFamily
    (fun n => GrpObj.inv (X := (S.restrict.{u, u} n).obj F))
    (fun _ _ φ => S.totalNeg_compat F ht φ)

omit [∀ n, IsCommMonObj ((S.restrict.{u, u} n).obj F)] in
/-- The restriction of the assembled unit is the degreewise unit. -/
theorem restrict_map_totalOne (n : SimplexCategory) :
    (S.restrict.{u, u} n).map (S.totalOne F ht) =
      OplaxMonoidal.η (S.restrict.{u, u} n) ≫ MonObj.one :=
  S.restrict_map_totalHomOfFibreFamily _ _ n

omit [∀ n, IsCommMonObj ((S.restrict.{u, u} n).obj F)] in
/-- The restriction of the assembled multiplication is the degreewise multiplication. -/
theorem restrict_map_totalMul (n : SimplexCategory) :
    (S.restrict.{u, u} n).map (S.totalMul F ht) =
      OplaxMonoidal.δ (S.restrict.{u, u} n) F F ≫ MonObj.mul :=
  S.restrict_map_totalHomOfFibreFamily _ _ n

omit [∀ n, IsCommMonObj ((S.restrict.{u, u} n).obj F)] in
/-- The restriction of the assembled inverse is the degreewise inverse. -/
theorem restrict_map_totalNeg (n : SimplexCategory) :
    (S.restrict.{u, u} n).map (S.totalNeg F ht) = GrpObj.inv :=
  S.restrict_map_totalHomOfFibreFamily _ _ n

/-- A sheaf of sets on the total site whose restrictions carry commutative group structures
compatible with the canonical transitions is a commutative group object. -/
noncomputable def totalSheafCommGrp : CommGrp (Sheaf S.totalTopology (Type u)) :=
  liftCommGrp S.restrict.{u, u} S.restrict_jointly_injective F
    (S.totalOne F ht) (S.totalMul F ht) (S.totalNeg F ht)
    (S.restrict_map_totalOne F ht) (S.restrict_map_totalMul F ht)
    (S.restrict_map_totalNeg F ht)

/-- The restriction in degree `n` of the commutative group object built from the restrictions is
the commutative group structure that degree was given. -/
noncomputable def totalSheafCommGrpRestrictionIso (n : SimplexCategory) :
    (S.restrict.{u, u} n).mapCommGrp.obj (S.totalSheafCommGrp F ht) ≅
      (⟨(S.restrict.{u, u} n).obj F⟩ : CommGrp (Sheaf (S.componentTopology n) (Type u))) := by
  refine CommGrp.mkIso (Iso.refl _) ?_ ?_
  · change (LaxMonoidal.ε (S.restrict.{u, u} n) ≫
        (S.restrict.{u, u} n).map (S.totalOne F ht)) ≫ 𝟙 _ = _
    rw [S.restrict_map_totalOne]
    simp
  · change (LaxMonoidal.μ (S.restrict.{u, u} n) F F ≫
        (S.restrict.{u, u} n).map (S.totalMul F ht)) ≫ 𝟙 _ = _
    rw [S.restrict_map_totalMul, Category.comp_id, ← Category.assoc, Monoidal.μ_δ,
      Category.id_comp]
    exact ((MonoidalCategory.id_tensorHom_id _ _ =≫ MonObj.mul).trans
      (Category.id_comp _)).symm

end TotalGroup

/-- The degreewise group structure on the restrictions of the sheaf of sets descended from the pair
underlying an abelian pair. -/
noncomputable instance pairTotalGrpObj (A : CartesianAbPair S) (n : SimplexCategory) :
    GrpObj ((S.restrict.{u, u} n).obj (S.pairTotalSheaf (S.abelianPairUnderlying A))) :=
  (S.pairRestrictionGroup A n).grp

/-- That group structure is commutative. -/
noncomputable instance pairTotalIsCommMonObj (A : CartesianAbPair S) (n : SimplexCategory) :
    IsCommMonObj ((S.restrict.{u, u} n).obj (S.pairTotalSheaf (S.abelianPairUnderlying A))) :=
  (S.pairRestrictionGroup A n).comm

/-- The canonical transitions of the descended sheaf of sets are morphisms of commutative group
objects for those group structures. -/
theorem pairTotalGroup_isMonHom (A : CartesianAbPair S) (m n : SimplexCategory) (φ : m ⟶ n) :
    IsMonHom (show (S.transitionMorphism φ).inverseImage.obj ((S.restrict.{u, u} m).obj
        (S.pairTotalSheaf (S.abelianPairUnderlying A))) ⟶
      (S.restrict.{u, u} n).obj (S.pairTotalSheaf (S.abelianPairUnderlying A)) from
        (S.fiberTransition φ).app (S.pairTotalSheaf (S.abelianPairUnderlying A))) := by
  rw [← S.pairRestrictionGroupTransition_hom A φ]
  exact (S.pairRestrictionGroupTransition A φ).hom.hom.isMonHom_hom

/-- **Stacks 0D7I.** The cartesian commutative group object descended from an abelian pair. -/
noncomputable def pairTotalGroup (A : CartesianAbPair S) : CartesianGrpSheaf S :=
  ⟨S.totalSheafCommGrp (S.pairTotalSheaf (S.abelianPairUnderlying A)) (S.pairTotalGroup_isMonHom A),
    S.pairTotalSheaf_isCartesian (S.abelianPairUnderlying A)⟩

/-- The restriction in degree `n` of the commutative group object descended from an abelian pair is
the component of the system of commutative groups. -/
noncomputable def pairTotalGroupRestrictionIso (A : CartesianAbPair S) (n : SimplexCategory) :
    (S.restrict.{u, u} n).mapCommGrp.obj (S.pairTotalGroup A).obj ≅
      S.pairComponentGroup A n :=
  S.totalSheafCommGrpRestrictionIso (S.pairTotalSheaf (S.abelianPairUnderlying A))
      (S.pairTotalGroup_isMonHom A) n ≪≫ S.pairRestrictionGroupIso A n

/-- The underlying map of sheaves of sets of that identification is the identification of the
degree-`n` restriction of the descended sheaf of sets. -/
theorem pairTotalGroupRestrictionIso_hom (A : CartesianAbPair S) (n : SimplexCategory) :
    (S.pairTotalGroupRestrictionIso A n).hom.hom.hom.hom =
      (S.pairRestrictIso (S.abelianPairUnderlying A) n).hom := by
  change 𝟙 _ ≫ (S.pairRestrictIso (S.abelianPairUnderlying A) n).hom = _
  exact Category.id_comp _

/-- The component in degree zero of the abelian system attached to an abelian pair is its
degree-zero sheaf. -/
noncomputable def abelianPairZeroIso (A : CartesianAbPair S) :
    S.abelianPairSheaf A ⦋0⦌ ≅ A.sheaf :=
  eqToIso (congrArg (fun k => (abelianTransition S k).obj A.sheaf)
      SimplexCategory.vertexMap_zero_zero) ≪≫ (abelianIdIso S ⦋0⦌).app A.sheaf

/-- On underlying sheaves of sets that identification is the degree-zero identification of the
underlying pair. -/
theorem abelianForget_map_abelianPairZeroIso (A : CartesianAbPair S) :
    (S.abelianForget ⦋0⦌).map (S.abelianPairZeroIso A).hom =
      (S.pairZeroIso (S.abelianPairUnderlying A)).hom := by
  change (S.abelianForget ⦋0⦌).map (eqToHom (congrArg
      (fun k => (abelianTransition S k).obj A.sheaf)
      SimplexCategory.vertexMap_zero_zero) ≫ (abelianIdIso S ⦋0⦌).hom.app A.sheaf) = _
  rw [CategoryTheory.Functor.map_comp, eqToHom_map, S.forget_map_abelianIdIso_app]
  rfl

/-- **Stacks 0D7I.** The degree-zero sheaf of the abelian pair of the commutative group object
descended from an abelian pair is the degree-zero sheaf of that pair. -/
noncomputable def pairTotalGroupZeroIso (A : CartesianAbPair S) :
    (S.groupSheafToPairFunctor.obj (S.pairTotalGroup A)).sheaf ≅ A.sheaf :=
  (AbelianSheaf.externalSheaf (S.componentTopology ⦋0⦌)).mapIso
      (S.pairTotalGroupRestrictionIso A ⦋0⦌) ≪≫
    (AbelianSheaf.internalExternalIso (S.componentTopology ⦋0⦌)).app
      (S.abelianPairSheaf A ⦋0⦌) ≪≫ S.abelianPairZeroIso A

/-- On underlying sheaves of sets that identification is the degree-zero identification of the
descended sheaf of sets. -/
theorem abelianForget_map_pairTotalGroupZeroIso (A : CartesianAbPair S) :
    (S.abelianForget ⦋0⦌).map (S.pairTotalGroupZeroIso A).hom =
      (S.pairTotalZeroIso (S.abelianPairUnderlying A)).hom := by
  change (S.pairTotalGroupRestrictionIso A ⦋0⦌).hom.hom.hom.hom ≫
      𝟙 ((S.abelianForget ⦋0⦌).obj (S.abelianPairSheaf A ⦋0⦌)) ≫
      (S.abelianForget ⦋0⦌).map (S.abelianPairZeroIso A).hom = _
  rw [S.pairTotalGroupRestrictionIso_hom, S.abelianForget_map_abelianPairZeroIso]
  exact _ ≫= Category.id_comp _

/-- The degree-zero identification of the sheaf descended from a pair of sheaves of sets carries
the comparison isomorphism of the pair to the comparison isomorphism of the descended sheaf. -/
theorem pairTotalZeroIso_comm (A : CartesianPair S) :
    (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map
          (S.pairTotalZeroIso A).hom ≫ A.iso.hom =
      (S.cartesianIso (S.pairCartesianSheaf A)).hom ≫
        (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map
          (S.pairTotalZeroIso A).hom :=
  have hc : (S.cartesianIso (S.pairCartesianSheaf A)).hom ≫
        (S.fiberTransition (SimplexCategory.δ (0 : Fin 2))).app (S.pairTotalSheaf A) =
      (S.fiberTransition (SimplexCategory.δ (1 : Fin 2))).app (S.pairTotalSheaf A) :=
    S.cartesianIso_hom_comp (S.pairCartesianSheaf A)
  (((S.fiberTransition_pairTotalSheaf_face_one A).symm.trans (hc =≫ _).symm).trans
      (Category.assoc _ _ _)).trans
    (_ ≫= S.fiberTransition_pairTotalSheaf_face_zero A)

/-- On underlying sheaves of sets the comparison isomorphism of the abelian pair attached to a
cartesian commutative group object is the comparison isomorphism of the underlying cartesian sheaf
of sets. -/
theorem abelianForget_map_groupSheafToPairFunctor_obj_iso (G : CartesianGrpSheaf S) :
    (S.abelianForget ⦋1⦌).map (S.groupSheafToPairFunctor.obj G).iso.hom =
      (S.cartesianIso ⟨G.obj.X, G.property⟩).hom :=
  S.abelianForget_map_groupSheafComparisonIso G

/-- **Stacks 0D7I.** Every abelian pair is the abelian pair of a cartesian commutative group object
in sheaves of sets on the total site. -/
instance groupSheafToPairFunctor_essSurj : S.groupSheafToPairFunctor.EssSurj where
  mem_essImage A := by
    refine ⟨S.pairTotalGroup A, ⟨CartesianAbPair.isoMk S (S.pairTotalGroupZeroIso A) ?_⟩⟩
    apply (S.abelianForget ⦋1⦌).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      S.abelianForget_map_abelianTransition_map, S.abelianForget_map_abelianTransition_map,
      S.abelianForget_map_pairTotalGroupZeroIso,
      S.abelianForget_map_groupSheafToPairFunctor_obj_iso]
    exact S.pairTotalZeroIso_comm (S.abelianPairUnderlying A)

/-- The functor from cartesian commutative group objects to abelian pairs is an equivalence. -/
instance groupSheafToPairFunctor_isEquivalence :
    S.groupSheafToPairFunctor.IsEquivalence := {}

/-! ### The equivalence -/

/-- **Stacks 0D7I.** The functor from cartesian sheaves of abelian groups on the total site of a
simplicial-site situation to abelian pairs: internalize the group structure, restrict to degree
zero and compare the two canonical transitions to degree one. -/
noncomputable def cartesianAbPairFunctor : CartesianAbSheaf S ⥤ CartesianAbPair S :=
  S.cartesianAbInternal ⋙ S.groupSheafToPairFunctor

/-- The functor from cartesian sheaves of abelian groups to abelian pairs is an equivalence. -/
instance cartesianAbPairFunctor_isEquivalence :
    S.cartesianAbPairFunctor.IsEquivalence :=
  inferInstanceAs (S.cartesianAbInternal ⋙ S.groupSheafToPairFunctor).IsEquivalence

/-- The degree-zero sheaf of the abelian pair attached to a cartesian sheaf of abelian groups has,
as underlying sheaf of sets, the degree-zero restriction of the underlying sheaf of sets. -/
theorem abelianForget_obj_cartesianAbPairFunctor_obj_sheaf (F : CartesianAbSheaf S) :
    (S.abelianForget ⦋0⦌).obj (S.cartesianAbPairFunctor.obj F).sheaf =
      (S.restrict ⦋0⦌).obj
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj F.obj) := rfl

/-- The comparison isomorphism of the abelian pair attached to a cartesian sheaf of abelian groups
is, on underlying sheaves of sets, the comparison of the two canonical transitions of Stacks
09WF. -/
theorem abelianForget_map_cartesianAbPairFunctor_obj_iso (F : CartesianAbSheaf S) :
    (S.abelianForget ⦋1⦌).map (S.cartesianAbPairFunctor.obj F).iso.hom =
      (S.cartesianIso ⟨(sheafCompose S.totalTopology (forget Ab.{u})).obj F.obj,
        F.property⟩).hom :=
  S.abelianForget_map_groupSheafComparisonIso _

/-- **Stacks 0D7I.** The category of cartesian sheaves of abelian groups on the total site of a
simplicial-site situation is equivalent to the category of pairs `(ℱ, α)` consisting of a sheaf of
abelian groups `ℱ` on the degree-zero component and an isomorphism
`α : (f_{δ¹₁})⁻¹ℱ ≅ (f_{δ¹₀})⁻¹ℱ` of sheaves of abelian groups on the degree-one component
satisfying the cocycle condition `(f_{δ²₁})⁻¹α = (f_{δ²₀})⁻¹α ∘ (f_{δ²₂})⁻¹α` on the degree-two
component. -/
@[stacks 0D7I "sheaves of abelian groups"]
noncomputable def cartesianAbSheafEquivCartesianAbPair :
    CartesianAbSheaf S ≌ CartesianAbPair S :=
  S.cartesianAbPairFunctor.asEquivalence

end Internal

end SimplicialSiteSituation

end CategoryTheory

end
