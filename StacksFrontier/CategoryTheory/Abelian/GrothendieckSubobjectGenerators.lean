module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-!
# A set of generators of a Grothendieck abelian category, read on subobjects

Let `C` be a Grothendieck abelian category.  There is a family `F : T → C` indexed by a type of
the universe of the category, such that every object `X` of `C` is the directed colimit of those
of its subobjects that are isomorphic to a member of the family.

The family is the family of quotients of finite coproducts of copies of a separator `G`: its
index is the set of pairs `(n, K)` of a natural number and a subobject `K` of `G^n`, which is a
set because `C` is well-powered.  A subobject of `X` isomorphic to a quotient of `G^n` is the image
of a morphism `G^n ⟶ X`, and conversely.  The images of the morphisms out of finite coproducts of
copies of `G` form a directed system, since the image of the sum of two such morphisms contains
both images, and their supremum is `X`, since `G` is a separator.  The colimit of a directed
system of subobjects is their supremum in a Grothendieck abelian category,
`CategoryTheory.IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`.

## Main definitions

* `CategoryTheory.IsGrothendieckAbelian.isoFamilySubobjects`: the subobjects of `X` isomorphic
  to a member of a family, and
  `CategoryTheory.IsGrothendieckAbelian.isoFamilySubobjectsCocone` the cocone of their
  inclusions, with vertex `X`.

## Main results

* `CategoryTheory.IsGrothendieckAbelian.exists_family_isFiltered_isColimit`: in a Grothendieck
  abelian category there is a family of objects indexed by a small type such that every object
  is the directed colimit of its subobjects isomorphic to a member of the family.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C]

/-- The subobjects of `X` which are isomorphic to a member of the family `F`. -/
def isoFamilySubobjects {T : Type w} (F : T → C) (X : C) : ObjectProperty (Subobject X) :=
  fun N => ∃ t : T, Nonempty ((N : C) ≅ F t)

/-- The cocone with vertex `X` of the inclusions of the subobjects of `X` isomorphic to a member
of the family `F`. -/
def isoFamilySubobjectsCocone {T : Type w} (F : T → C) (X : C) :
    Cocone ((isoFamilySubobjects F X).ι ⋙ Subobject.underlying) :=
  Cocone.mk X
    { app := fun N => N.obj.arrow
      naturality := fun {_ _} f => by simp [Subobject.underlying_arrow f.hom] }

section Abelian

variable [Abelian C]

/-- The finite coproduct of `n` copies of an object. -/
abbrev finPow (G : C) (n : ℕ) : C := ∐ fun _ : Fin n => G

/-- The image of the morphism `G^n ⟶ X` given by `n` morphisms `G ⟶ X`. -/
abbrev imageOfFamily {G X : C} {n : ℕ} (f : Fin n → (G ⟶ X)) : Subobject X :=
  imageSubobject (Sigma.desc f)

/-- The image of a morphism `G^n ⟶ X` is a quotient of `G^n`: it is isomorphic to the cokernel
of the inclusion of the kernel. -/
def imageSubobjectIsoCokernel {A X : C} (g : A ⟶ X) :
    (imageSubobject g : C) ≅ cokernel (Subobject.mk (kernel.ι g)).arrow :=
  imageSubobjectIso g ≪≫ (Abelian.coimageIsoImage' g).symm ≪≫
    (cokernelIsoOfEq (Subobject.underlyingIso_arrow (kernel.ι g)).symm ≪≫
      cokernelEpiComp (Subobject.underlyingIso (kernel.ι g)).inv (Subobject.mk (kernel.ι g)).arrow)

/-- A subobject `N` of `X` with an epimorphism `p : A ⟶ N` is the image of `p ≫ N.arrow`. -/
theorem imageSubobject_comp_arrow_of_epi {A X : C} (N : Subobject X) (p : A ⟶ (N : C)) [Epi p] :
    imageSubobject (p ≫ N.arrow) = N := by
  change Subobject.mk (image.ι (p ≫ N.arrow)) = N
  conv_rhs => rw [← Subobject.mk_arrow N]
  have := strongEpi_of_epi p
  exact (Subobject.mk_eq_mk_of_comm _ _ (image.isoStrongEpiMono p N.arrow rfl)
    (image.isoStrongEpiMono_hom_comp_ι p N.arrow rfl)).symm

/-- The image of the morphism `G^n ⟶ X` given by a family of morphisms is contained in a
subobject through which every member of the family factors. -/
theorem imageOfFamily_le {G X : C} {n : ℕ} (f : Fin n → (G ⟶ X)) (Z : Subobject X)
    (h : ∀ i, Z.Factors (f i)) : imageOfFamily f ≤ Z :=
  imageSubobject_le (Sigma.desc f) (Sigma.desc fun i => Z.factorThru (f i) (h i))
    (Sigma.hom_ext _ _ fun i => by simp)

/-- Every member of a family of morphisms factors through the image of the morphism they give
out of `G^n`. -/
theorem factors_imageOfFamily {G X : C} {n : ℕ} (f : Fin n → (G ⟶ X)) (i : Fin n) :
    (imageOfFamily f).Factors (f i) := by
  have h : f i = (Sigma.ι _ i ≫ factorThruImageSubobject (Sigma.desc f)) ≫
      (imageSubobject (Sigma.desc f)).arrow := by
    rw [Category.assoc, imageSubobject_arrow_comp, Sigma.ι_desc]
  rw [h]
  exact Subobject.factors_comp_arrow _

variable (G : C) [LocallySmall.{w} C] [WellPowered.{w} C]

/-- The index of the quotients of finite coproducts of copies of `G`: pairs of a natural number
`n` and a subobject of `G^n`. -/
abbrev QuotientIndex : Type w :=
  Σ n : ℕ, Shrink.{w} (Subobject (finPow G n))

/-- The quotient of `G^n` by a subobject. -/
def quotientFamily (t : QuotientIndex G) : C :=
  cokernel ((equivShrink (Subobject (finPow G t.1))).symm t.2).arrow

variable {G}

/-- The member of `quotientFamily G` at the index `(n, K)` is the cokernel of `K`. -/
def quotientFamilyIso (n : ℕ) (K : Subobject (finPow G n)) :
    quotientFamily G ⟨n, equivShrink (Subobject (finPow G n)) K⟩ ≅ cokernel K.arrow :=
  eqToIso (congrArg (fun K' : Subobject (finPow G n) => cokernel K'.arrow)
    (Equiv.symm_apply_apply
      (equivShrink (Subobject (finPow G n)) : _ ≃ Shrink.{w} (Subobject (finPow G n))) K))

/-- The image of a morphism `G^n ⟶ X` is isomorphic to a member of `quotientFamily G`. -/
theorem isoFamilySubobjects_imageOfFamily {X : C} {n : ℕ} (f : Fin n → (G ⟶ X)) :
    isoFamilySubobjects (quotientFamily G) X (imageOfFamily f) := by
  refine ⟨⟨n, equivShrink _ (Subobject.mk (kernel.ι (Sigma.desc f)))⟩, ⟨?_⟩⟩
  exact imageSubobjectIsoCokernel (Sigma.desc f) ≪≫
    (quotientFamilyIso n _).symm

/-- A subobject of `X` isomorphic to a member of `quotientFamily G` is the image of a morphism
`G^n ⟶ X`. -/
theorem exists_eq_imageOfFamily {X : C} {N : Subobject X}
    (hN : isoFamilySubobjects (quotientFamily G) X N) :
    ∃ (n : ℕ) (f : Fin n → (G ⟶ X)), N = imageOfFamily f := by
  obtain ⟨t, ⟨e⟩⟩ := hN
  obtain ⟨n, k⟩ := t
  obtain ⟨K, rfl⟩ := (equivShrink (Subobject (finPow G n))).surjective k
  let p : finPow G n ⟶ (N : C) := cokernel.π K.arrow ≫
    (quotientFamilyIso n K).inv ≫ e.inv
  have : Epi p := by
    simp only [p]
    infer_instance
  refine ⟨n, fun i => Sigma.ι (fun _ : Fin n => G) i ≫ p ≫ N.arrow, ?_⟩
  have hd : Sigma.desc (fun i => Sigma.ι (fun _ : Fin n => G) i ≫ p ≫ N.arrow) = p ≫ N.arrow :=
    (Sigma.hom_ext _ _ fun i => by simp)
  simp only [imageOfFamily, hd]
  exact (imageSubobject_comp_arrow_of_epi N p).symm

omit [LocallySmall.{w} C] [WellPowered.{w} C] in
/-- Two images of morphisms out of finite coproducts of copies of `G` are contained in a third. -/
theorem exists_imageOfFamily_le {X : C} {n₁ n₂ : ℕ} (f₁ : Fin n₁ → (G ⟶ X))
    (f₂ : Fin n₂ → (G ⟶ X)) :
    imageOfFamily f₁ ≤ imageOfFamily (Fin.append f₁ f₂) ∧
      imageOfFamily f₂ ≤ imageOfFamily (Fin.append f₁ f₂) := by
  constructor
  · refine imageOfFamily_le f₁ _ fun i => ?_
    have := factors_imageOfFamily (Fin.append f₁ f₂) (Fin.castAdd n₂ i)
    rwa [Fin.append_left] at this
  · refine imageOfFamily_le f₂ _ fun i => ?_
    have := factors_imageOfFamily (Fin.append f₁ f₂) (Fin.natAdd n₁ i)
    rwa [Fin.append_right] at this

/-- The subobjects of `X` isomorphic to a member of `quotientFamily G` form a filtered
category. -/
theorem isFiltered_isoFamilySubobjects (X : C) :
    IsFiltered (isoFamilySubobjects (quotientFamily G) X).FullSubcategory := by
  have hne : Nonempty (isoFamilySubobjects (quotientFamily G) X).FullSubcategory :=
    ⟨⟨_, isoFamilySubobjects_imageOfFamily (n := 0) (G := G) (X := X) fun i => Fin.elim0 i⟩⟩
  have : IsFilteredOrEmpty (isoFamilySubobjects (quotientFamily G) X).FullSubcategory :=
    { cocone_objs := fun N₁ N₂ => by
        obtain ⟨n₁, f₁, h₁⟩ := exists_eq_imageOfFamily N₁.property
        obtain ⟨n₂, f₂, h₂⟩ := exists_eq_imageOfFamily N₂.property
        obtain ⟨l₁, l₂⟩ := exists_imageOfFamily_le f₁ f₂
        exact ⟨⟨_, isoFamilySubobjects_imageOfFamily (Fin.append f₁ f₂)⟩,
          ObjectProperty.homMk (homOfLE (h₁ ▸ l₁)), ObjectProperty.homMk (homOfLE (h₂ ▸ l₂)),
          trivial⟩
      cocone_maps := fun _ Y _ _ => ⟨Y, 𝟙 Y, by ext; exact Subsingleton.elim _ _⟩ }
  exact { toIsFilteredOrEmpty := this, nonempty := hne }

end Abelian

section Grothendieck

variable [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- A small model of the subobjects of `X` satisfying a property. -/
abbrev SmallSubobjects (X : C) (P : ObjectProperty (Subobject X)) : Type w :=
  Shrink.{w} {N : Subobject X // P N}

/-- The order on the small model of the subobjects satisfying a property. -/
instance (X : C) (P : ObjectProperty (Subobject X)) : Preorder (SmallSubobjects X P) :=
  Preorder.lift fun j => ((equivShrink _).symm j).1

/-- The subobject of `X` attached to an element of the small model. -/
abbrev SmallSubobjects.sub {X : C} {P : ObjectProperty (Subobject X)}
    (j : SmallSubobjects X P) : Subobject X :=
  ((equivShrink _).symm j).1

/-- The comparison functor from the small model to the full subcategory. -/
def smallSubobjectsFunctor (X : C) (P : ObjectProperty (Subobject X)) :
    SmallSubobjects X P ⥤ P.FullSubcategory where
  obj j := ⟨j.sub, ((equivShrink _).symm j).2⟩
  map {j j'} f := ObjectProperty.homMk (homOfLE (show j.sub ≤ j'.sub from (leOfHom f : j ≤ j')))

/-- The subobject attached to the image of an element in the small model is that element. -/
theorem SmallSubobjects.sub_equivShrink {X : C} {P : ObjectProperty (Subobject X)}
    (N : {N : Subobject X // P N}) : SmallSubobjects.sub (P := P) (equivShrink _ N) = N.1 := by
  simp only [SmallSubobjects.sub, Equiv.symm_apply_apply]

instance (X : C) (P : ObjectProperty (Subobject X)) : (smallSubobjectsFunctor X P).Full where
  map_surjective {j j'} f := ⟨homOfLE (show j.sub ≤ j'.sub from leOfHom f.hom), by
    ext; exact Subsingleton.elim _ _⟩

instance (X : C) (P : ObjectProperty (Subobject X)) : (smallSubobjectsFunctor X P).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance (X : C) (P : ObjectProperty (Subobject X)) : (smallSubobjectsFunctor X P).EssSurj where
  mem_essImage N := ⟨equivShrink _ ⟨N.obj, N.property⟩, ⟨
    { hom := ObjectProperty.homMk (homOfLE (le_of_eq (SmallSubobjects.sub_equivShrink
        (P := P) ⟨N.obj, N.property⟩)))
      inv := ObjectProperty.homMk (homOfLE (le_of_eq (SmallSubobjects.sub_equivShrink
        (P := P) ⟨N.obj, N.property⟩).symm))
      hom_inv_id := by ext; exact Subsingleton.elim _ _
      inv_hom_id := by ext; exact Subsingleton.elim _ _ }⟩⟩

instance (X : C) (P : ObjectProperty (Subobject X)) :
    (smallSubobjectsFunctor X P).IsEquivalence where

/-- The supremum of the subobjects of `X` isomorphic to a member of `quotientFamily G` is `X`,
for a separator `G`. -/
theorem iSup_isoFamilySubobjects_eq_top {G : C} (hG : IsSeparator G) (X : C) :
    ⨆ N : (isoFamilySubobjects (quotientFamily G) X).FullSubcategory, N.obj = ⊤ := by
  set S := ⨆ N : (isoFamilySubobjects (quotientFamily G) X).FullSubcategory, N.obj
  have hπ : cokernel.π S.arrow = 0 := by
    refine hG.def _ _ fun h => ?_
    let N : (isoFamilySubobjects (quotientFamily G) X).FullSubcategory :=
      ⟨_, isoFamilySubobjects_imageOfFamily (fun _ : Fin 1 => h)⟩
    have hf : S.Factors h :=
      Subobject.factors_of_le h (le_iSup (fun N => N.obj) N)
        (factors_imageOfFamily (fun _ : Fin 1 => h) 0)
    rw [Limits.comp_zero, ← Subobject.factorThru_arrow S h hf, Category.assoc,
      cokernel.condition, Limits.comp_zero]
  have : Epi S.arrow := Preadditive.epi_of_cokernel_zero hπ
  have : IsIso S.arrow := isIso_of_mono_of_epi _
  exact (Subobject.isIso_arrow_iff_eq_top S).1 inferInstance

/-- **A filtered family of subobjects with supremum `X` has colimit `X`.**  In a Grothendieck
abelian category, if the subobjects of `X` satisfying `P` form a filtered category and their
supremum is `X`, the cocone of their inclusions is a colimit cocone. -/
theorem isColimit_of_iSup_eq_top {X : C} (P : ObjectProperty (Subobject X))
    [IsFiltered P.FullSubcategory] (hP : ⨆ N : P.FullSubcategory, N.obj = ⊤)
    (c : Cocone (P.ι ⋙ Subobject.underlying)) (hc : c.pt = X)
    (hι : ∀ N, c.ι.app N ≫ eqToHom hc = N.obj.arrow) :
    Nonempty (IsColimit c) := by
  let e := smallSubobjectsFunctor X P
  have : IsFiltered (SmallSubobjects X P) := IsFiltered.of_equivalence e.asEquivalence.symm
  let F' : SmallSubobjects X P ⥤ MonoOver X := e ⋙ P.ι ⋙ Subobject.representative
  let c' : Cocone (F' ⋙ MonoOver.forget X) :=
    { pt := Over.mk (𝟙 X)
      ι := { app := fun j => Over.homMk (F'.obj j).obj.hom
             naturality := fun _ _ _ => Over.mkIdTerminal.hom_ext _ _ } }
  have : Mono c'.pt.hom := inferInstanceAs (Mono (𝟙 X))
  have hsup : Subobject.mk c'.pt.hom = ⨆ j, Subobject.mk (F'.obj j).obj.hom := by
    have h1 : ∀ j, Subobject.mk (F'.obj j).obj.hom = (e.obj j).obj := fun j =>
      Subobject.mk_arrow (e.obj j).obj
    simp only [h1]
    refine (Subobject.mk_eq_top_of_isIso (𝟙 X)).trans ?_
    rw [← hP]
    apply le_antisymm
    · exact iSup_le fun N => (le_of_eq (SmallSubobjects.sub_equivShrink (P := P)
        ⟨N.obj, N.property⟩).symm).trans (le_iSup (fun j => (e.obj j).obj) _)
    · exact iSup_le fun j => le_iSup (fun N : P.FullSubcategory => N.obj) (e.obj j)
  have hc' := isColimitMapCoconeOfSubobjectMkEqISup F' c' hsup
  have hw : IsColimit (c.whisker e) := by
    refine IsColimit.ofIsoColimit hc' (Cocone.ext (eqToIso hc.symm) fun j => ?_)
    rw [← cancel_mono (eqToHom hc)]
    simp only [eqToIso.hom, eqToHom_trans, eqToHom_refl, Category.comp_id, Category.assoc]
    exact (hι (e.obj j)).symm
  exact ⟨(Functor.Final.isColimitWhiskerEquiv e c) hw⟩

/-- **In a Grothendieck abelian category there is a set of objects such that every object is
the directed colimit of those of its subobjects isomorphic to one of them.** -/
theorem exists_family_isFiltered_isColimit :
    ∃ (T : Type w) (F : T → C), ∀ X : C,
      IsFiltered (isoFamilySubobjects F X).FullSubcategory ∧
        Nonempty (IsColimit (isoFamilySubobjectsCocone F X)) := by
  refine ⟨QuotientIndex (separator C), quotientFamily (separator C), fun X => ?_⟩
  have := isFiltered_isoFamilySubobjects (G := separator C) X
  exact ⟨this, isColimit_of_iSup_eq_top _
    (iSup_isoFamilySubobjects_eq_top (isSeparator_separator C) X) _ rfl fun N => by simp
      [isoFamilySubobjectsCocone]⟩

end Grothendieck

end CategoryTheory.IsGrothendieckAbelian

end
