module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# Shrinking the hom types of a category of costructured arrows

Let `G : 𝒜 ⥤ ℰ` be a functor between locally small categories and let `d` be an object of `ℰ`.
Replacing both categories by their hom-shrunk models `CategoryTheory.ShrinkHoms` turns `G` into
`ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ`, and this file identifies the categories of
costructured arrows to `d` on the two sides:

`CostructuredArrow G d` is equivalent to
`CostructuredArrow (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ) (ShrinkHoms.toShrinkHoms d)`

and the equivalence lies, in both directions, *strictly* over any category `C` over which `𝒜`
lies: the comparison is the identity on the underlying objects, and the hom types are only
transported along `equivShrink`.

That strictness is the point. A moduli description of the fibres of a 1-morphism of categories
fibred in groupoids is proved at the categories in which the moduli problem lives, whose hom
types need not be small; the 2-category of algebraic stacks of Stacks 03YP is formed at the hom
universe of the site, so a comparison 1-morphism into a 2-fibre product computed there has to be
written between the hom-shrunk models, and a 1-morphism of categories over the site must commute
with the structure functors on the nose.

## Main definitions

* `StacksRepresentableCFG.costructuredArrowShrinkHomsFunctor` and
  `StacksRepresentableCFG.costructuredArrowUnshrinkHomsFunctor`: the two comparison functors.
* `StacksRepresentableCFG.costructuredArrowShrinkHomsHom` and
  `StacksRepresentableCFG.costructuredArrowShrinkHomsInv`: the same, as 1-morphisms over `C`.
* `StacksRepresentableCFG.costructuredArrowShrinkHoms`: the equivalence over `C`.

## Main results

* `CategoryTheory.ShrinkHoms.inverse_map_functor_map` and
  `CategoryTheory.ShrinkHoms.functor_map_inverse_map`: the two round trips on hom types are the
  identity.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.ShrinkHoms

universe w v u

variable (C : Type u) [Category.{v} C] [LocallySmall.{w} C]

/-- Shrinking a morphism and undoing the shrinking returns the morphism. -/
@[simp]
theorem inverse_map_functor_map {X Y : C} (f : X ⟶ Y) :
    (inverse C).map ((functor C).map f) = f :=
  (equivShrink (X ⟶ Y)).symm_apply_apply f

/-- Undoing the shrinking of a morphism of the hom-shrunk model and shrinking again returns the
morphism. -/
@[simp]
theorem functor_map_inverse_map {X Y : ShrinkHoms.{u} C} (f : X ⟶ Y) :
    (functor C).map ((inverse C).map f) = f :=
  (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).apply_symm_apply f

end CategoryTheory.ShrinkHoms

namespace StacksRepresentableCFG

universe w w' v₀ u₀ v₁ u₁ v₂ u₂

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {ℰ : Type u₂} [Category.{v₂} ℰ]
  [LocallySmall.{w} 𝒜] [LocallySmall.{w'} ℰ] (G : 𝒜 ⥤ ℰ) (d : ℰ)

/-- The triangle of a morphism of costructured arrows survives shrinking the hom types. -/
theorem costructuredArrow_w_shrinkHoms {c c' : CostructuredArrow G d} (m : c ⟶ c') :
    (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ).map ((ShrinkHoms.functor 𝒜).map m.left) ≫
        (ShrinkHoms.functor ℰ).map c'.hom = (ShrinkHoms.functor ℰ).map c.hom := by
  rw [Functor.comp_map, Functor.comp_map, ShrinkHoms.inverse_map_functor_map]
  exact ((ShrinkHoms.functor ℰ).map_comp _ _).symm.trans (congrArg _ (CostructuredArrow.w m))

/-- The triangle of a morphism of costructured arrows of the hom-shrunk models survives undoing
the shrinking. -/
theorem costructuredArrow_w_unshrinkHoms
    {c c' : CostructuredArrow (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ)
      (ShrinkHoms.toShrinkHoms d)} (m : c ⟶ c') :
    G.map ((ShrinkHoms.inverse 𝒜).map m.left) ≫ (ShrinkHoms.inverse ℰ).map c'.hom =
      (ShrinkHoms.inverse ℰ).map c.hom := by
  have := congrArg (ShrinkHoms.inverse ℰ).map (CostructuredArrow.w m)
  rwa [Functor.map_comp, Functor.comp_map, Functor.comp_map,
    ShrinkHoms.inverse_map_functor_map] at this

/-- **The costructured arrows to `d` read between the hom-shrunk models**: an arrow `G x ⟶ d` goes
to its shrinking. The functor is the identity on the underlying objects. -/
def costructuredArrowShrinkHomsFunctor :
    CostructuredArrow G d ⥤
      CostructuredArrow (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ)
        (ShrinkHoms.toShrinkHoms d) where
  obj c := CostructuredArrow.mk (Y := ShrinkHoms.toShrinkHoms c.left)
    ((ShrinkHoms.functor ℰ).map c.hom)
  map {_ _} m := CostructuredArrow.homMk ((ShrinkHoms.functor 𝒜).map m.left)
    (costructuredArrow_w_shrinkHoms G d m)
  map_id x := CostructuredArrow.hom_ext _ _ ((ShrinkHoms.functor 𝒜).map_id x.left)
  map_comp m m' :=
    CostructuredArrow.hom_ext _ _ ((ShrinkHoms.functor 𝒜).map_comp m.left m'.left)

/-- **The costructured arrows of the hom-shrunk models read back**: an arrow of the hom-shrunk
model goes to the morphism it shrinks. -/
def costructuredArrowUnshrinkHomsFunctor :
    CostructuredArrow (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ)
        (ShrinkHoms.toShrinkHoms d) ⥤
      CostructuredArrow G d where
  obj c := CostructuredArrow.mk (Y := (ShrinkHoms.inverse 𝒜).obj c.left)
    ((ShrinkHoms.inverse ℰ).map c.hom)
  map {_ _} m := CostructuredArrow.homMk ((ShrinkHoms.inverse 𝒜).map m.left)
    (costructuredArrow_w_unshrinkHoms G d m)
  map_id x := CostructuredArrow.hom_ext _ _ ((ShrinkHoms.inverse 𝒜).map_id x.left)
  map_comp m m' :=
    CostructuredArrow.hom_ext _ _ ((ShrinkHoms.inverse 𝒜).map_comp m.left m'.left)

/-- The underlying morphism of the image of `m` under `costructuredArrowShrinkHomsFunctor` is the
shrinking of `m.left`. -/
@[simp]
theorem costructuredArrowShrinkHomsFunctor_map_left {c c' : CostructuredArrow G d} (m : c ⟶ c') :
    ((costructuredArrowShrinkHomsFunctor G d).map m).left = (ShrinkHoms.functor 𝒜).map m.left :=
  rfl

/-- The structure arrow of the image of `c` under `costructuredArrowShrinkHomsFunctor` is the
shrinking of `c.hom`. -/
@[simp]
theorem costructuredArrowShrinkHomsFunctor_obj_hom (c : CostructuredArrow G d) :
    ((costructuredArrowShrinkHomsFunctor G d).obj c).hom = (ShrinkHoms.functor ℰ).map c.hom :=
  rfl

/-- The underlying morphism of the image of `m` under `costructuredArrowUnshrinkHomsFunctor` is
the morphism that `m.left` shrinks. -/
@[simp]
theorem costructuredArrowUnshrinkHomsFunctor_map_left
    {c c' : CostructuredArrow (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ)
      (ShrinkHoms.toShrinkHoms d)} (m : c ⟶ c') :
    ((costructuredArrowUnshrinkHomsFunctor G d).map m).left =
      (ShrinkHoms.inverse 𝒜).map m.left :=
  rfl

/-- The structure arrow of the image of `c` under `costructuredArrowUnshrinkHomsFunctor` is the
morphism that `c.hom` shrinks. -/
@[simp]
theorem costructuredArrowUnshrinkHomsFunctor_obj_hom
    (c : CostructuredArrow (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ)
      (ShrinkHoms.toShrinkHoms d)) :
    ((costructuredArrowUnshrinkHomsFunctor G d).obj c).hom = (ShrinkHoms.inverse ℰ).map c.hom :=
  rfl

variable {C : Type u₀} [Category.{v₀} C] (p : 𝒜 ⥤ C)

/-- **The forward comparison 1-morphism over `C`.** -/
def costructuredArrowShrinkHomsHom :
    MorphismOver (CostructuredArrow.proj G d ⋙ p)
      (CostructuredArrow.proj (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ)
          (ShrinkHoms.toShrinkHoms d) ⋙ ShrinkHoms.inverse 𝒜 ⋙ p) where
  functor := costructuredArrowShrinkHomsFunctor G d
  w := CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ m => by
    change p.map ((ShrinkHoms.inverse 𝒜).map ((ShrinkHoms.functor 𝒜).map m.left)) = _
    rw [ShrinkHoms.inverse_map_functor_map]
    exact (Category.comp_id _).symm.trans (Category.id_comp _).symm)

/-- **The backward comparison 1-morphism over `C`.** -/
def costructuredArrowShrinkHomsInv :
    MorphismOver
      (CostructuredArrow.proj (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ)
          (ShrinkHoms.toShrinkHoms d) ⋙ ShrinkHoms.inverse 𝒜 ⋙ p)
      (CostructuredArrow.proj G d ⋙ p) where
  functor := costructuredArrowUnshrinkHomsFunctor G d
  w := rfl

/-- The underlying functor of `costructuredArrowShrinkHomsHom` is
`costructuredArrowShrinkHomsFunctor`. -/
@[simp]
theorem costructuredArrowShrinkHomsHom_functor :
    (costructuredArrowShrinkHomsHom G d p).functor = costructuredArrowShrinkHomsFunctor G d :=
  rfl

/-- The underlying functor of `costructuredArrowShrinkHomsInv` is
`costructuredArrowUnshrinkHomsFunctor`. -/
@[simp]
theorem costructuredArrowShrinkHomsInv_functor :
    (costructuredArrowShrinkHomsInv G d p).functor = costructuredArrowUnshrinkHomsFunctor G d :=
  rfl

/-- **Shrinking the hom types of a category of costructured arrows gives an equivalent category
over `C`.** Both 1-morphisms are strictly over `C`, and the unit and counit are the identity on
the underlying objects, hence vertical. -/
def costructuredArrowShrinkHoms :
    StacksRepresentableCFG.EquivalenceOver (CostructuredArrow.proj G d ⋙ p)
      (CostructuredArrow.proj (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ)
          (ShrinkHoms.toShrinkHoms d) ⋙ ShrinkHoms.inverse 𝒜 ⋙ p) where
  hom := costructuredArrowShrinkHomsHom G d p
  inv := costructuredArrowShrinkHomsInv G d p
  unitIso := NatIso.ofComponents
    (fun c => CostructuredArrow.isoMk (Iso.refl c.left) (by
      change G.map (𝟙 c.left) ≫ (ShrinkHoms.inverse ℰ).map ((ShrinkHoms.functor ℰ).map c.hom) =
        c.hom
      exact ((congrArg (fun k : G.obj c.left ⟶ G.obj c.left =>
            k ≫ (ShrinkHoms.inverse ℰ).map ((ShrinkHoms.functor ℰ).map c.hom))
          (G.map_id c.left)).trans (Category.id_comp _)).trans
        (ShrinkHoms.inverse_map_functor_map ℰ c.hom)))
    (fun {c c'} m => CostructuredArrow.hom_ext _ _ (by
      change m.left ≫ 𝟙 c'.left =
        𝟙 c.left ≫ (ShrinkHoms.inverse 𝒜).map ((ShrinkHoms.functor 𝒜).map m.left)
      exact (Category.comp_id m.left).trans ((Category.id_comp m.left).symm.trans
        (congrArg (fun k : c.left ⟶ c'.left => 𝟙 c.left ≫ k)
          (ShrinkHoms.inverse_map_functor_map 𝒜 m.left).symm))))
  counitIso := NatIso.ofComponents
    (fun c => CostructuredArrow.isoMk (Iso.refl c.left) (by
      change (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ).map (𝟙 c.left) ≫ c.hom =
        (ShrinkHoms.functor ℰ).map ((ShrinkHoms.inverse ℰ).map c.hom)
      exact ((congrArg (fun k : (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ).obj c.left ⟶
              (ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ).obj c.left => k ≫ c.hom)
            ((ShrinkHoms.inverse 𝒜 ⋙ G ⋙ ShrinkHoms.functor ℰ).map_id c.left)).trans
          (Category.id_comp c.hom)).trans
        (ShrinkHoms.functor_map_inverse_map ℰ c.hom).symm))
    (fun {c c'} m => CostructuredArrow.hom_ext _ _ (by
      change (ShrinkHoms.functor 𝒜).map ((ShrinkHoms.inverse 𝒜).map m.left) ≫ 𝟙 c'.left =
        𝟙 c.left ≫ m.left
      exact (congrArg (fun k : c.left ⟶ c'.left => k ≫ 𝟙 c'.left)
          (ShrinkHoms.functor_map_inverse_map 𝒜 m.left)).trans
        ((Category.comp_id m.left).trans (Category.id_comp m.left).symm)))
  unit_over := by
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    intro x
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    change p.map (𝟙 x.left) = _
    exact (p.map_id x.left).trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm)
  counit_over := by
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    intro x
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    change p.map ((ShrinkHoms.inverse 𝒜).map (𝟙 x.left)) = _
    exact ((congrArg p.map ((ShrinkHoms.inverse 𝒜).map_id x.left)).trans
      (p.map_id _)).trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm)

end StacksRepresentableCFG

end
