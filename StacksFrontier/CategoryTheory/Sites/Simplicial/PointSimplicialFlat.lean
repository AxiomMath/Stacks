module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.PointSimplicialModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensorComparisonWeak
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.FlatMapIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi

/-!
# Flatness on the point

On the site of the point with the trivial topology, a morphism of sheaves of commutative rings is
flat as soon as its ring map of sections at the point is flat: the point is a conservative point
of its own site, and the fibre of a sheaf at it is its value at the point.

## Main results

* `CategoryTheory.PointSimplicialSite.isFlatMap_of_flat_app`: flatness on the point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.PointSimplicialSite

noncomputable section

variable (J : GrothendieckTopology Pt.{u}) (hJ : J = ⊥)

/-- The fibre functor of the point of the site of the point. -/
abbrev ptFiber : Pt.{u} ⥤ Type u := (Functor.const Pt.{u}).obj PUnit.{u + 1}

/-- The element of the fibre functor. -/
abbrev ptElement : ptFiber.{u}.Elements := ptFiber.elementsMk pt PUnit.unit

/-- Any two morphisms between elements of the fibre functor are equal. -/
instance subsingleton_elements_hom (X Y : ptFiber.{u}.Elements) : Subsingleton (X ⟶ Y) :=
  ⟨fun _ _ => Functor.Elements.hom_ext ((subsingleton_hom.{u} _ _).elim _ _)⟩

/-- A morphism between any two elements. -/
def elementsHom (X Y : ptFiber.{u}.Elements) : X ⟶ Y := ⟨homOf _ _, rfl⟩

/-- The element is initial. -/
def elementsInitial : IsInitial ptElement.{u} :=
  IsInitial.ofUniqueHom (fun Y => elementsHom _ Y) (fun _ _ => Subsingleton.elim _ _)

/-- The element is terminal. -/
def elementsTerminal : IsTerminal ptElement.{u} :=
  IsTerminal.ofUniqueHom (fun Y => elementsHom Y _) (fun _ _ => Subsingleton.elim _ _)

/-- The category of elements of the fibre functor is cofiltered. -/
instance : IsCofiltered ptFiber.{u}.Elements :=
  IsCofiltered.of_isInitial _ elementsInitial.{u}

/-- The category of elements of the fibre functor is initially small. -/
instance : InitiallySmall.{u} ptFiber.{u}.Elements :=
  initiallySmall_of_essentiallySmall _

/-- Colimits indexed by the opposite of the category of elements of the fibre functor. -/
instance hasColimitsOfShape_ptFiber_elements_op {A : Type*} [Category A]
    [HasColimitsOfSize.{u, u} A] : HasColimitsOfShape ptFiber.{u}.Elementsᵒᵖ A :=
  hasColimitsOfShape_of_finallySmall _ _

/-- Colimits of diagrams indexed by the opposite of the category of elements of the fibre
functor. -/
instance (priority := high) hasColimit_ptFiber_elements_op {A : Type*} [Category A]
    [HasColimitsOfSize.{u, u} A] (F : ptFiber.{u}.Elementsᵒᵖ ⥤ A) : HasColimit F :=
  HasColimitsOfShape.has_colimit F

include hJ in
/-- The point of the site of the point. -/
def point : J.Point.{u} where
  fiber := ptFiber.{u}
  jointly_surjective {X} R hR x := by
    subst hJ
    rw [GrothendieckTopology.bot_covering] at hR
    subst hR
    exact ⟨X, 𝟙 X, trivial, x, rfl⟩

/-- The element is terminal in the opposite category, which indexes the fibre colimit. -/
def elementsOpTerminal : IsTerminal (op ptElement.{u}) := elementsInitial.{u}.op

variable {J}

/-- The colimit injection of the element into the fibre of a presheaf is an isomorphism. -/
theorem isIso_ι_fiber {A : Type*} [Category A] [HasColimitsOfSize.{u, u} A]
    (F : Pt.{u}ᵒᵖ ⥤ A) :
    IsIso (colimit.ι ((CategoryOfElements.π ptFiber.{u}).op ⋙ F) (op ptElement)) :=
  isIso_ι_of_isTerminal elementsOpTerminal _

/-- The colimit injection of the element into the fibre is natural in the presheaf. -/
theorem ι_presheafFiber_map {A : Type*} [Category A] [HasColimitsOfSize.{u, u} A]
    {F G : Pt.{u}ᵒᵖ ⥤ A} (f : F ⟶ G) :
    colimit.ι ((CategoryOfElements.π ptFiber.{u}).op ⋙ F) (op ptElement) ≫
        (point J hJ).presheafFiber.map f =
      f.app (op pt) ≫ colimit.ι ((CategoryOfElements.π ptFiber.{u}).op ⋙ G) (op ptElement) :=
  colimit.ι_map _ _

/-- The point of the site of the point is conservative. -/
theorem isConservativeFamilyOfPoints :
    (ObjectProperty.ofObj (fun _ : PUnit.{1} => point J hJ)).IsConservativeFamilyOfPoints := by
  refine ⟨⟨fun {F G} f hf => ?_⟩⟩
  have h : IsIso ((point J hJ).presheafFiber.map f.hom) := hf ⟨point J hJ, ⟨PUnit.unit⟩⟩
  have hc := @IsIso.comp_isIso _ _ _ _ _ _ _ (isIso_ι_fiber F.obj) h
  rw [ι_presheafFiber_map hJ f.hom] at hc
  have happ := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (isIso_ι_fiber G.obj) hc
  have : ∀ X : Pt.{u}ᵒᵖ, IsIso (f.hom.app X) := fun _ => happ
  have : IsIso f.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf J (Type u)).map f) := this
  exact isIso_of_reflects_iso f (sheafToPresheaf J (Type u))

include hJ in
/-- **Flatness on the point.** A morphism of sheaves of commutative rings on the point with the
trivial topology is flat if its ring map of sections at the point is flat. -/
theorem isFlatMap_of_flat_app {O O' : Sheaf J CommRingCat.{u}} (g : O ⟶ O')
    (hg : (g.hom.app (op pt)).hom.Flat) :
    AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{u, u, u} g := by
  refine (AlgebraicGeometry.SheafOfModules.isFlatMapULift_iff_isFlatMap.{u} g).2 ?_
  change Stacks.SheafOfModules.IsFlat (Stacks.ringMapAsModule.{u, u, u} g)
  rw [Stacks.isFlat_iff_forall_isFlatModuleStalk_of_weakSheafify (fun _ : PUnit.{1} => point J hJ)
    (isConservativeFamilyOfPoints hJ)]
  intro i
  refine (Stacks.isFlatModuleStalk_ringMapAsModule_iff.{u, u, u} (point J hJ) g).2 ?_
  have h1 := isIso_ι_fiber O.obj
  have h2 := isIso_ι_fiber O'.obj
  have hsq := ι_presheafFiber_map hJ g.hom
  have e : (point J hJ).presheafFiber.map g.hom =
      @inv _ _ _ _ (colimit.ι ((CategoryOfElements.π ptFiber.{u}).op ⋙ O.obj) (op ptElement)) h1 ≫
        g.hom.app (op pt) ≫
          colimit.ι ((CategoryOfElements.π ptFiber.{u}).op ⋙ O'.obj) (op ptElement) :=
    (@IsIso.eq_inv_comp _ _ _ _ _ _ h1 _ _).2 hsq
  rw [e]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective ?_) (RingHom.Flat.comp hg
    (RingHom.Flat.of_bijective ?_))
  · exact (ConcreteCategory.bijective_of_isIso
      (@inv _ _ _ _ (colimit.ι ((CategoryOfElements.π ptFiber.{u}).op ⋙ O.obj) (op ptElement)) h1))
  · exact @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ h2

omit hJ in
/-- The unit of the adjunction of the identity morphism of sites is invertible. -/
theorem isIso_unit_id [(𝟭 Pt.{u}).IsContinuous J J] (F : Sheaf J (Type u)) :
    IsIso (((𝟭 Pt.{u}).sheafAdjunctionContinuous (Type u) J J).unit.app F) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((𝟭 Pt.{u}).sheafAdjunctionContinuous (Type u) J J) Adjunction.id F
  have h' : IsIso (((𝟭 Pt.{u}).sheafAdjunctionContinuous (Type u) J J).unit.app F ≫
      ((𝟭 Pt.{u}).sheafPushforwardContinuous (Type u) J J).map
        ((((𝟭 Pt.{u}).sheafAdjunctionContinuous (Type u) J J).leftAdjointUniq
          Adjunction.id).hom.app F)) := by
    rw [h]; exact inferInstanceAs (IsIso (𝟙 _))
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance h'

end

end CategoryTheory.PointSimplicialSite

end
