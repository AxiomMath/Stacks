module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf

/-!
# Functoriality of presheaves of modules on fibred categories

A morphism of categories fibred in groupoids over the big fppf site induces
inverse-image and direct-image functors on presheaves of modules over their
structure sheaves.

## Main definitions

* `AlgebraicGeometry.Stack.compatibleSections`: for a functor `L : C ⥤ D`, a functor
  `F : C ⥤ AddCommGrpCat` and `y : D`, the group of compatible families of sections of `F`
  indexed by the maps `y ⟶ L.obj x`.
* `AlgebraicGeometry.Stack.sectionsAdjunction`: precomposition with `L` is left adjoint to
  `AlgebraicGeometry.Stack.sectionsFunctor`, the functor of compatible families.
* `AlgebraicGeometry.Stack.moduleSectionsFunctor`: the direct image of presheaves of modules
  along a functor, given by compatible families of sections.
* `AlgebraicGeometry.Stack.moduleSectionsAdjunction`: restriction of modules
  `PresheafOfModules.pushforward₀` is left adjoint to `moduleSectionsFunctor`.
* `AlgebraicGeometry.Stack.ModuleFunctoriality`: the inverse- and direct-image functors of
  presheaves of modules, their underlying functors on abelian presheaves, and their adjunction.
* `AlgebraicGeometry.Stack.moduleFunctoriality`: the inverse- and direct-image functors induced by
  a morphism of categories fibred in groupoids.

## Implementation notes

The inverse image is Mathlib's `PresheafOfModules.pushforward₀`, followed by transport of scalars
along the equality of structure presheaves. The structure sheaves are taken on the fppf sites;
their underlying ring presheaves do not depend on the selected topology.

In `AlgebraicGeometry.Stack.sectionsModule` the scalar action produced by `M.map_smul` is
`(f.op ⋙ R).map a`, which is `R.map (f.op.map a)` definitionally but not syntactically, so that
step states the instance explicitly.

## References

* [Stacks Project, Tag 06WD](https://stacks.math.columbia.edu/tag/06WD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m v' w'

namespace AlgebraicGeometry.Stack

section CompatibleSections

variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  (L : C ⥤ D)

/-- The subgroup of compatible families of sections: for `y : D`, the families
`s x g ∈ F.obj x`, indexed by `x : C` and `g : y ⟶ L.obj x`, with
`F.map a (s x g) = s x' (g ≫ L.map a)` for every `a : x ⟶ x'`. -/
def compatibleSections (F : C ⥤ AddCommGrpCat.{m}) (y : D) :
    AddSubgroup (∀ x : C, (y ⟶ L.obj x) → F.obj x) where
  carrier := {s | ∀ (x x' : C) (a : x ⟶ x') (g : y ⟶ L.obj x),
    F.map a (s x g) = s x' (g ≫ L.map a)}
  zero_mem' := by intro x x' a g; exact map_zero (F.map a).hom
  add_mem' := by
    intro s t hs ht x x' a g
    exact (map_add (F.map a).hom _ _).trans (congrArg₂ (· + ·) (hs x x' a g) (ht x x' a g))
  neg_mem' := by
    intro s hs x x' a g
    exact (map_neg (F.map a).hom _).trans (congrArg Neg.neg (hs x x' a g))

/-- The functor `D ⥤ AddCommGrpCat` sending `y` to the group `compatibleSections L F y` of
compatible families, acting on maps by precomposition. -/
def sectionsPresheaf (F : C ⥤ AddCommGrpCat.{max v w m v' w'}) :
    D ⥤ AddCommGrpCat.{max v w m v' w'} where
  obj y := AddCommGrpCat.of (compatibleSections.{v, w, max v w m v' w'} L F y)
  map {y z} a := AddCommGrpCat.ofHom {
    toFun := fun s => ⟨fun x g => s.val x (a ≫ g), by
      intro x x' b g
      simpa only [Category.assoc] using s.property x x' b (a ≫ g)⟩
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  map_id y := by ext s x g; exact congrArg (s.val x) (Category.id_comp g)
  map_comp a b := by ext s x g; exact congrArg (s.val x) (Category.assoc a b g)

/-- The functor of compatible families, `F ↦ sectionsPresheaf L F`. -/
def sectionsFunctor : (C ⥤ AddCommGrpCat.{max v w m v' w'}) ⥤
    (D ⥤ AddCommGrpCat.{max v w m v' w'}) where
  obj F := sectionsPresheaf.{v, w, m} L F
  map {F G} α := {
    app y := AddCommGrpCat.ofHom {
      toFun := fun s => ⟨fun x g => α.app x (s.val x g), by
        intro x x' a g
        change G.map a (α.app x (s.val x g)) = α.app x' (s.val x' (g ≫ L.map a))
        rw [← NatTrans.naturality_apply α a, s.property x x' a g]⟩
      map_zero' := by apply Subtype.ext; funext x g; exact map_zero (α.app x).hom
      map_add' := by intro s t; apply Subtype.ext; funext x g; exact map_add (α.app x).hom _ _ }
    naturality := by intro y z a; ext s; rfl }
  map_id F := by ext y s; rfl
  map_comp α β := by ext y s; rfl

/-- The morphism `G ⟶ sectionsPresheaf L F` corresponding to a morphism `α : L ⋙ G ⟶ F`,
sending a section `s` to the family `g ↦ α (G.map g s)`. -/
def sectionsLift {F : C ⥤ AddCommGrpCat.{max v w m v' w'}}
    {G : D ⥤ AddCommGrpCat.{max v w m v' w'}} (α : L ⋙ G ⟶ F) :
    G ⟶ sectionsPresheaf.{v, w, m} L F where
  app y := AddCommGrpCat.ofHom {
    toFun := fun s => ⟨fun x g => α.app x (G.map g s), by
      intro x x' a g
      rw [← NatTrans.naturality_apply α a]
      change α.app x' (G.map (L.map a) (G.map g s)) =
        α.app x' (G.map (g ≫ L.map a) s)
      rw [G.map_comp]; rfl⟩
    map_zero' := by apply Subtype.ext; funext x g; simp
    map_add' := by intro s t; apply Subtype.ext; funext x g; simp }
  naturality := by
    intro y z a
    ext s
    apply Subtype.ext; funext x g
    change α.app x (G.map g (G.map a s)) = α.app x (G.map (a ≫ g) s)
    rw [G.map_comp]; rfl

/-- The morphism `L ⋙ G ⟶ F` corresponding to a morphism `G ⟶ sectionsPresheaf L F`, evaluating
each family at the identity. -/
def sectionsDesc {F : C ⥤ AddCommGrpCat.{max v w m v' w'}}
    {G : D ⥤ AddCommGrpCat.{max v w m v' w'}} (β : G ⟶ sectionsPresheaf.{v, w, m} L F) :
    L ⋙ G ⟶ F where
  app x := AddCommGrpCat.ofHom {
    toFun := fun s => (β.app (L.obj x) s).val x (𝟙 _)
    map_zero' := by rw [map_zero]; rfl
    map_add' := by intro s t; rw [map_add]; rfl }
  naturality := by
    intro x x' a
    ext s
    have h := congrArg (fun t => t.val x' (𝟙 _)) (NatTrans.naturality_apply β (L.map a) s)
    change (β.app (L.obj x') (G.map (L.map a) s)).val x' (𝟙 _) =
      F.map a ((β.app (L.obj x) s).val x (𝟙 _))
    rw [h, (β.app (L.obj x) s).property x x' a (𝟙 _)]
    change (β.app (L.obj x) s).val x' (L.map a ≫ 𝟙 _) =
      (β.app (L.obj x) s).val x' (𝟙 _ ≫ L.map a)
    simp only [Category.id_comp, Category.comp_id]

/-- Morphisms `L ⋙ G ⟶ F` correspond to morphisms `G ⟶ sectionsPresheaf L F`. -/
def sectionsHomEquiv (G : D ⥤ AddCommGrpCat.{max v w m v' w'})
    (F : C ⥤ AddCommGrpCat.{max v w m v' w'}) :
    (L ⋙ G ⟶ F) ≃ (G ⟶ sectionsPresheaf.{v, w, m} L F) where
  toFun := sectionsLift.{v, w, m} L
  invFun := sectionsDesc.{v, w, m} L
  left_inv α := by
    ext x s
    change α.app x (G.map (𝟙 _) s) = α.app x s
    rw [G.map_id]; rfl
  right_inv β := by
    ext y s
    apply Subtype.ext; funext x g
    change (β.app (L.obj x) (G.map g s)).val x (𝟙 _) = (β.app y s).val x g
    rw [NatTrans.naturality_apply β g]
    exact congrArg ((β.app y s).val x) (Category.comp_id g)

/-- Precomposition with `L` is left adjoint to the functor of compatible families. -/
def sectionsAdjunction :
    (Functor.whiskeringLeft C D AddCommGrpCat.{max v w m v' w'}).obj L ⊣
      sectionsFunctor.{v, w, m} L :=
  Adjunction.mkOfHomEquiv {
    homEquiv := sectionsHomEquiv.{v, w, m} L
    homEquiv_naturality_left_symm := by intro G G' F α β; ext x s; rfl
    homEquiv_naturality_right := by intro G F F' α β; ext y s; rfl }

end CompatibleSections
section ModuleSections

variable {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
  (f : X ⥤ Y) (R : Yᵒᵖ ⥤ RingCat.{u})

/-- The module structure of the sections over `x` of a presheaf of `f.op ⋙ R`-modules, over the
ring `R.obj (f.op.obj x)`. -/
@[instance_reducible]
def restrictedSectionModule (M : PresheafOfModules.{m} (f.op ⋙ R)) (x : Xᵒᵖ) :
    Module (R.obj (f.op.obj x)) (M.presheaf.obj x) := (M.obj x).isModule

attribute [local instance] restrictedSectionModule

/-- The `R.obj y`-module structure on the compatible families of sections of a presheaf of
`f.op ⋙ R`-modules, `r • s = (g ↦ R.map g r • s x g)`. -/
@[instance_reducible]
noncomputable def sectionsModule (M : PresheafOfModules.{m} (f.op ⋙ R)) (y : Yᵒᵖ) :
    Module (R.obj y) (compatibleSections.{v, w, m} f.op M.presheaf y) where
  smul r s := ⟨fun x g => R.map g r • s.val x g, by
    intro x x' a g
    change M.map a (R.map g r • s.val x g) =
      R.map (g ≫ f.op.map a) r • s.val x' (g ≫ f.op.map a)
    have hms : M.map a (R.map g r • s.val x g) =
        R.map (f.op.map a) (R.map g r) • M.presheaf.map a (s.val x g) :=
      M.map_smul a (R.map g r) (s.val x g)
    rw [hms, s.property x x' a g, R.map_comp]
    rfl⟩
  one_smul s := by
    apply Subtype.ext; funext x g
    change R.map g 1 • s.val x g = _
    rw [(R.map g).hom.map_one, one_smul]
  mul_smul r t s := by
    apply Subtype.ext; funext x g
    change R.map g (r * t) • s.val x g = R.map g r • (R.map g t • s.val x g)
    rw [map_mul, mul_smul]
  smul_zero r := by apply Subtype.ext; funext x g; exact smul_zero _
  smul_add r s t := by apply Subtype.ext; funext x g; exact smul_add _ _ _
  add_smul r t s := by
    apply Subtype.ext; funext x g
    change R.map g (r + t) • s.val x g = R.map g r • s.val x g + R.map g t • s.val x g
    rw [map_add, add_smul]
  zero_smul s := by
    apply Subtype.ext; funext x g
    change R.map g 0 • s.val x g = _
    rw [(R.map g).hom.map_zero, zero_smul]
    rfl

attribute [local instance] sectionsModule

/-- The presheaf of `R`-modules of compatible families of sections of a presheaf of
`f.op ⋙ R`-modules. -/
noncomputable def moduleSectionsObj (M : PresheafOfModules.{max u v w m v' w'} (f.op ⋙ R)) :
    PresheafOfModules.{max u v w m v' w'} R where
  obj y := ModuleCat.of (R.obj y) (compatibleSections.{v, w, max u v w m v' w'} f.op M.presheaf y)
  map {y z} a := ModuleCat.ofHom
    (X := ModuleCat.of (R.obj y) (compatibleSections.{v, w, max u v w m v' w'} f.op M.presheaf y))
    (Y := (ModuleCat.restrictScalars (R.map a).hom).obj
      (ModuleCat.of (R.obj z) (compatibleSections.{v, w, max u v w m v' w'} f.op M.presheaf z))) {
    toFun := (sectionsPresheaf.{v, w, max u m} f.op M.presheaf).map a
    map_add' := ((sectionsPresheaf.{v, w, max u m} f.op M.presheaf).map a).hom.map_add
    map_smul' := by
      intro r s
      apply Subtype.ext; funext x g
      change R.map (a ≫ g) r • s.val x (a ≫ g) =
        R.map g (R.map a r) • s.val x (a ≫ g)
      rw [R.map_comp]; rfl }
  map_id y := by
    ext s
    apply Subtype.ext; funext x g
    exact congrArg (s.val x) (Category.id_comp g)
  map_comp a b := by
    ext s
    apply Subtype.ext; funext x g
    exact congrArg (s.val x) (Category.assoc a b g)

/-- The direct image of presheaves of modules along `f`, sending `M` to the presheaf of
`R`-modules of compatible families of its sections. -/
noncomputable def moduleSectionsFunctor :
    PresheafOfModules.{max u v w m v' w'} (f.op ⋙ R) ⥤ PresheafOfModules.{max u v w m v' w'} R where
  obj := moduleSectionsObj.{u, v, w, m} f R
  map {M N} α := {
    app y := ModuleCat.ofHom {
      __ := (((sectionsFunctor.{v, w, max u m} f.op).map
        ((PresheafOfModules.toPresheaf _).map α)).app y).hom
      map_smul' := by
        intro r s
        apply Subtype.ext; funext x g
        exact (α.app x).hom.map_smul (R.map g r) (s.val x g) }
    naturality := by intro y z a; ext s; rfl }
  map_id M := by ext y s; rfl
  map_comp α β := by ext y s; rfl

/-- The morphism `N ⟶ moduleSectionsObj f R M` corresponding to a morphism from the restriction
of `N` along `f` to `M`. -/
noncomputable def moduleSectionsLift {M : PresheafOfModules.{max u v w m v' w'} (f.op ⋙ R)}
    {N : PresheafOfModules.{max u v w m v' w'} R}
    (α : (PresheafOfModules.pushforward₀ f R).obj N ⟶ M) :
    N ⟶ moduleSectionsObj.{u, v, w, m} f R M where
  app y := ModuleCat.ofHom {
    toFun := (sectionsLift.{v, w, max u m} f.op (F := M.presheaf) (G := N.presheaf)
      ((PresheafOfModules.toPresheaf _).map α)).app y
    map_add' := ((sectionsLift.{v, w, max u m} f.op (F := M.presheaf) (G := N.presheaf)
      ((PresheafOfModules.toPresheaf _).map α)).app y).hom.map_add
    map_smul' := by
      intro r s
      apply Subtype.ext; funext x g
      change α.app x (N.map g (r • s)) = R.map g r • α.app x (N.map g s)
      rw [N.map_smul]
      exact (α.app x).hom.map_smul _ _ }
  naturality := by
    intro y z a
    ext s
    apply Subtype.ext; funext x g
    change α.app x (N.map g (N.map a s)) = α.app x (N.map (a ≫ g) s)
    rw [N.map_comp_apply]

/-- The morphism from the restriction of `N` along `f` to `M` corresponding to a morphism
`N ⟶ moduleSectionsObj f R M`, evaluating each family at the identity. -/
noncomputable def moduleSectionsDesc {M : PresheafOfModules.{max u v w m v' w'} (f.op ⋙ R)}
    {N : PresheafOfModules.{max u v w m v' w'} R} (β : N ⟶ moduleSectionsObj.{u, v, w, m} f R M) :
    (PresheafOfModules.pushforward₀ f R).obj N ⟶ M where
  app x := ModuleCat.ofHom {
    __ := ((sectionsDesc.{v, w, max u m} f.op ((PresheafOfModules.toPresheaf _).map β)).app x).hom
    map_smul' := by
      intro r s
      change (β.app (f.op.obj x) (r • s)).val x (𝟙 _) =
        r • (β.app (f.op.obj x) s).val x (𝟙 _)
      rw [(β.app (f.op.obj x)).hom.map_smul]
      change R.map (𝟙 _) r • (β.app (f.op.obj x) s).val x (𝟙 _) = _
      rw [R.map_id]; rfl }
  naturality := by
    intro x x' a
    ext s
    exact NatTrans.naturality_apply
      (sectionsDesc.{v, w, max u m} f.op ((PresheafOfModules.toPresheaf _).map β)) a s

/-- Morphisms from the restriction of `N` along `f` to `M` correspond to morphisms
`N ⟶ moduleSectionsObj f R M`. -/
noncomputable def moduleSectionsHomEquiv (N : PresheafOfModules.{max u v w m v' w'} R)
    (M : PresheafOfModules.{max u v w m v' w'} (f.op ⋙ R)) :
    ((PresheafOfModules.pushforward₀ f R).obj N ⟶ M) ≃
      (N ⟶ moduleSectionsObj.{u, v, w, m} f R M) where
  toFun := moduleSectionsLift.{u, v, w, m} f R
  invFun := moduleSectionsDesc.{u, v, w, m} f R
  left_inv α := by
    ext x s
    change α.app x (N.map (𝟙 _) s) = α.app x s
    rw [N.map_id]; rfl
  right_inv β := by
    ext y s
    apply Subtype.ext; funext x g
    change (β.app (f.op.obj x) (N.map g s)).val x (𝟙 _) = (β.app y s).val x g
    rw [PresheafOfModules.naturality_apply β g]
    exact congrArg ((β.app y s).val x) (Category.comp_id g)

/-- Restriction of presheaves of modules along `f` is left adjoint to the direct image
`moduleSectionsFunctor f R`. -/
noncomputable def moduleSectionsAdjunction :
    PresheafOfModules.pushforward₀ f R ⊣ moduleSectionsFunctor.{u, v, w, m} f R :=
  Adjunction.mkOfHomEquiv {
    homEquiv := moduleSectionsHomEquiv.{u, v, w, m} f R
    homEquiv_naturality_left_symm := by intro N N' M α β; ext x s; rfl
    homEquiv_naturality_right := by intro N M M' α β; ext y s; rfl }

end ModuleSections
section Transport

variable {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
  (f : X ⥤ Y) (R : Yᵒᵖ ⥤ RingCat.{u})

/-- For an equality `T = f.op ⋙ R` of presheaves of rings: a functor from presheaves of
`T`-modules to presheaves of `R`-modules, an isomorphism of its underlying abelian presheaves with
the right Kan extension along `f.op`, and an adjunction with restriction of modules along `f`
followed by transport of scalars. -/
noncomputable def moduleDirectImageData
    (T : Xᵒᵖ ⥤ RingCat.{u}) (h : T = f.op ⋙ R) :
    Σ P : PresheafOfModules.{max u v w m v' w'} T ⥤ PresheafOfModules.{max u v w m v' w'} R,
      (P ⋙ PresheafOfModules.toPresheaf R ≅ PresheafOfModules.toPresheaf T ⋙ f.op.ran) ×
      (PresheafOfModules.pushforward₀ f R ⋙
        PresheafOfModules.restrictScalars (eqToHom h) ⊣ P) := by
  subst T
  exact ⟨moduleSectionsFunctor.{u, v, w, m} f R,
    Functor.isoWhiskerLeft (PresheafOfModules.toPresheaf (f.op ⋙ R))
      ((sectionsAdjunction.{v, w, max u m} f.op).rightAdjointUniq
        (f.op.ranAdjunction AddCommGrpCat.{max u v w m v' w'})),
    moduleSectionsAdjunction.{u, v, w, m} f R⟩

end Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
  (pX : X ⥤ BigFppfOver B S hS)
  (pY : Y ⥤ BigFppfOver B S hS)
  (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
  (f : X ⥤ Y)

/-- The inverse- and direct-image functors of presheaves of modules along a
morphism of categories fibred in groupoids over the big fppf site. -/
structure ModuleFunctoriality where
  /-- The structure presheaf on the source is the restriction of the one on the target. -/
  structurePresheaf_eq :
    (ringStructureSheafCore B S hS pX hpX B.topology le_rfl).obj =
      f.op ⋙ (ringStructureSheafCore B S hS pY hpY B.topology le_rfl).obj
  /-- Inverse image of presheaves of modules. -/
  pullback :
    PresheafOfModules.{max u v w m v' w'}
        (ringStructureSheafCore B S hS pY hpY B.topology le_rfl).obj ⥤
      PresheafOfModules.{max u v w m v' w'}
        (ringStructureSheafCore B S hS pX hpX B.topology le_rfl).obj
  /-- Inverse image is the objectwise restriction of modules. -/
  pullback_iso : pullback ≅
    PresheafOfModules.pushforward₀ f
        (ringStructureSheafCore B S hS pY hpY B.topology le_rfl).obj ⋙
      PresheafOfModules.restrictScalars (eqToHom structurePresheaf_eq)
  /-- Direct image of presheaves of modules. -/
  pushforward :
    PresheafOfModules.{max u v w m v' w'}
        (ringStructureSheafCore B S hS pX hpX B.topology le_rfl).obj ⥤
      PresheafOfModules.{max u v w m v' w'}
        (ringStructureSheafCore B S hS pY hpY B.topology le_rfl).obj
  /-- On underlying abelian presheaves, direct image is right Kan extension. -/
  pushforward_iso :
    pushforward ⋙
        PresheafOfModules.toPresheaf
          (ringStructureSheafCore B S hS pY hpY B.topology le_rfl).obj ≅
      PresheafOfModules.toPresheaf
          (ringStructureSheafCore B S hS pX hpX B.topology le_rfl).obj ⋙
        f.op.ran
  /-- The two functors form the canonical adjoint pair. -/
  adjunction : pullback ⊣ pushforward

/-- The two functors on presheaves of modules induced by a morphism of
categories fibred in groupoids over the big fppf site. -/
@[stacks 06WD]
noncomputable def moduleFunctoriality (hf : f ⋙ pY = pX) :
    ModuleFunctoriality.{u, v, w, m, v', w'} B S hS pX pY hpX hpY f := by
  have hO :
      (ringStructureSheafCore B S hS pX hpX B.topology le_rfl).obj =
        f.op ⋙ (ringStructureSheafCore B S hS pY hpY B.topology le_rfl).obj := by
    rw [ringStructureSheafCore_obj, ringStructureSheafCore_obj, ← hf]
    rfl
  let d := moduleDirectImageData.{u, v, w, m} f
    (ringStructureSheafCore B S hS pY hpY B.topology le_rfl).obj
    (ringStructureSheafCore B S hS pX hpX B.topology le_rfl).obj hO
  exact
    { structurePresheaf_eq := hO
      pullback := PresheafOfModules.pushforward₀ f
          (ringStructureSheafCore B S hS pY hpY B.topology le_rfl).obj ⋙
        PresheafOfModules.restrictScalars (eqToHom hO)
      pullback_iso := Iso.refl _
      pushforward := d.1
      pushforward_iso := d.2.1
      adjunction := d.2.2 }

end AlgebraicGeometry.Stack
