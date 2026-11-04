module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.CategoryTheory.Adjunction.MatePaste

/-!
# Direct images around a commutative square of a big étale site

For a commutative square `c ≫ f = f' ≫ b` of a big étale site, the two composite direct images
`f_* c_*` and `b_* f'_*` of sheaves on the small étale sites agree, through the direct image
along the common composite; this is the 2-cell whose mate along the inverse-image/direct-image
adjunctions of `c` and `b` is the base change map `b⁻¹ f_* ⟶ f'_* c⁻¹`. For two such squares on
top of each other, these 2-cells paste vertically to the 2-cell of the outer rectangle, through
the comparison of the direct image along a composite with the composite of the direct images.

## Main definitions

* `AlgebraicGeometry.smallEtalePushforwardSquare`: the 2-cell `c_* ⋙ f_* ⟶ f'_* ⋙ b_*` of a
  commutative square, for an arbitrary coefficient category.
* `AlgebraicGeometry.smallEtalePushforwardBaseChange`: its mate, the base change map
  `b⁻¹ f_* ⟶ f'_* c⁻¹`.

## Main results

* `AlgebraicGeometry.smallEtalePushforwardSquare_app_hom_app`: the 2-cell on sections.
* `AlgebraicGeometry.smallEtaleBaseChange_paste`: the pasting identity on the small étale site,
  deduced from `CategoryTheory.Over.pullback_paste`, its form for iterated pullbacks in slices.
* `AlgebraicGeometry.smallEtalePushforwardSquare_paste`: the vertical pasting identity.
* `AlgebraicGeometry.smallEtalePushforwardBaseChange_paste`: the horizontal pasting of the base
  change maps (Sites, Remark 0F6X).

## Implementation notes

Every functor in sight is the direct image along a functor of small étale sites, and every
2-cell is induced by a natural isomorphism of those functors, so the pasting identity is, on
sections, the equality of two morphisms of the small étale site of `X'` into a threefold
iterated fibre product. Such a morphism is determined by its composite with the three first
projections, `CategoryTheory.Over.pullback_hom_ext₃`, and each canonical comparison
carries the first projections to one another.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 0F6X](https://stacks.math.columbia.edu/tag/0F6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ u

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] [HasPullbacks C]

/-- A morphism of slices into a threefold iterated pullback is determined by its composite with
the three first projections. -/
theorem pullback_hom_ext₃ {W X Y Z : C} (x : W ⟶ X) (y : X ⟶ Y) (z : Y ⟶ Z)
    (U : Over Z) {V : Over W}
    (φ ψ : V ⟶ (Over.pullback x).obj ((Over.pullback y).obj ((Over.pullback z).obj U)))
    (h : φ.left ≫ pullback.fst _ x ≫ pullback.fst _ y ≫ pullback.fst U.hom z =
      ψ.left ≫ pullback.fst _ x ≫ pullback.fst _ y ≫ pullback.fst U.hom z) :
    φ = ψ := by
  have hs : φ.left ≫ pullback.snd _ x = ψ.left ≫ pullback.snd _ x :=
    (Over.w φ).trans (Over.w ψ).symm
  have hs₂ : φ.left ≫ pullback.fst _ x ≫ pullback.snd _ y =
      ψ.left ≫ pullback.fst _ x ≫ pullback.snd _ y := by
    simp only [Over.pullback_obj_left, Over.pullback_obj_hom] at hs ⊢
    rw [pullback.condition, reassoc_of% hs]
  have hs₃ : φ.left ≫ pullback.fst _ x ≫ pullback.fst _ y ≫ pullback.snd U.hom z =
      ψ.left ≫ pullback.fst _ x ≫ pullback.fst _ y ≫ pullback.snd U.hom z := by
    simp only [Over.pullback_obj_left, Over.pullback_obj_hom] at hs₂ ⊢
    rw [pullback.condition]
    simpa only [Category.assoc] using congrArg (· ≫ y) hs₂
  ext1
  refine pullback.hom_ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_) hs
  · simpa only [Category.assoc] using h
  · simpa only [Category.assoc] using hs₃
  · simpa only [Category.assoc] using hs₂

/-- A morphism of slices into a twofold iterated pullback is determined by its composite with
the two first projections. -/
theorem pullback_hom_ext₂ {X Y Z : C} (x : X ⟶ Y) (y : Y ⟶ Z) (U : Over Z) {V : Over X}
    (φ ψ : V ⟶ (Over.pullback x).obj ((Over.pullback y).obj U))
    (h : φ.left ≫ pullback.fst _ x ≫ pullback.fst U.hom y =
      ψ.left ≫ pullback.fst _ x ≫ pullback.fst U.hom y) :
    φ = ψ := by
  have hs : φ.left ≫ pullback.snd _ x = ψ.left ≫ pullback.snd _ x :=
    (Over.w φ).trans (Over.w ψ).symm
  have hs₂ : φ.left ≫ pullback.fst _ x ≫ pullback.snd U.hom y =
      ψ.left ≫ pullback.fst _ x ≫ pullback.snd U.hom y := by
    simp only [Over.pullback_obj_left, Over.pullback_obj_hom] at hs ⊢
    rw [pullback.condition, reassoc_of% hs]
  ext1
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) hs
  · simpa only [Category.assoc] using h
  · simpa only [Category.assoc] using hs₂

@[reassoc]
private lemma pullbackComp_hom_fst_fst {X Y Z : C} (x : X ⟶ Y) (y : Y ⟶ Z) (V : Over Z) :
    ((Over.pullbackComp x y).hom.app V).left ≫ pullback.fst ((Over.pullback y).obj V).hom x ≫
        pullback.fst V.hom y = pullback.fst V.hom (x ≫ y) :=
  Over.pullbackComp_hom_app_left_fst_fst x y V

@[reassoc]
private lemma pullbackComp_inv_fst {X Y Z : C} (x : X ⟶ Y) (y : Y ⟶ Z) (V : Over Z) :
    ((Over.pullbackComp x y).inv.app V).left ≫ pullback.fst V.hom (x ≫ y) =
      pullback.fst ((Over.pullback y).obj V).hom x ≫ pullback.fst V.hom y :=
  Over.pullbackComp_inv_app_left_fst x y V

@[reassoc]
private lemma pullback_eqToHom_fst {X Y : C} {x x' : X ⟶ Y} (e : x = x')
    {E : Over.pullback x = Over.pullback x'} (V : Over Y) :
    ((eqToHom E).app V).left ≫ pullback.fst V.hom x' = pullback.fst V.hom x := by
  subst e
  simp

/-- The vertical pasting identity for the comparisons of iterated pullbacks in slices: for two
commutative squares on top of each other, the two composites of canonical comparisons from
`(f' ≫ g')^* a^* U` to `c^* f^* g^* U` agree. -/
theorem pullback_paste {X Y Z X' Y' Z' : C} (c : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (b : Y' ⟶ Y) (g' : Y' ⟶ Z') (g : Y ⟶ Z) (a : Z' ⟶ Z) (h₁ : c ≫ f = f' ≫ b)
    (h₂ : b ≫ g = g' ≫ a) (h : c ≫ f ≫ g = (f' ≫ g') ≫ a) (U : Over Z) :
    (Over.pullbackComp f' g').hom.app ((Over.pullback a).obj U) ≫
        (Over.pullback f').map ((Over.pullbackComp g' a).inv.app U) ≫
        (Over.pullback f').map
          ((eqToHom (congrArg (fun k : Y' ⟶ Z => Over.pullback k) h₂.symm)).app U) ≫
        (Over.pullback f').map ((Over.pullbackComp b g).hom.app U) ≫
        (Over.pullbackComp f' b).inv.app ((Over.pullback g).obj U) ≫
        (eqToHom (congrArg (fun k : X' ⟶ Y => Over.pullback k) h₁.symm)).app
          ((Over.pullback g).obj U) ≫
        (Over.pullbackComp c f).hom.app ((Over.pullback g).obj U) =
      (Over.pullbackComp (f' ≫ g') a).inv.app U ≫
        (eqToHom (congrArg (fun k : X' ⟶ Z => Over.pullback k) h.symm)).app U ≫
        (Over.pullbackComp c (f ≫ g)).hom.app U ≫
        (Over.pullback c).map ((Over.pullbackComp f g).hom.app U) := by
  apply pullback_hom_ext₃ c f g U
  dsimp only [Functor.comp_obj]
  simp only [Over.comp_left, Category.assoc, pullbackComp_hom_fst_fst_assoc,
    pullbackComp_hom_fst_fst, pullbackComp_inv_fst_assoc, pullbackComp_inv_fst,
    Over.pullback_map_left, pullback.lift_fst_assoc, pullback_eqToHom_fst_assoc h₁.symm,
    pullback_eqToHom_fst h₂.symm, pullback_eqToHom_fst h.symm]

/-- The comparison of the two iterated pullbacks around a commutative square, through the
pullback along the common composite, is compatible with the projections. -/
theorem pullback_square_left_fst {X Y X' Y' : C} (c : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (b : Y' ⟶ Y) (h : c ≫ f = f' ≫ b) (U : Over Y) :
    ((Over.pullbackComp f' b).inv.app U ≫
        (eqToHom (congrArg (fun k : X' ⟶ Y => Over.pullback k) h.symm)).app U ≫
        (Over.pullbackComp c f).hom.app U).left ≫ pullback.fst _ c ≫ pullback.fst U.hom f =
      pullback.fst _ f' ≫ pullback.fst U.hom b := by
  simp only [Over.comp_left, Category.assoc, pullbackComp_hom_fst_fst, pullbackComp_inv_fst,
    pullback_eqToHom_fst h.symm]

end CategoryTheory.Over

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section Projections

variable {X Y Z : B.Scheme} (x : X ⟶ Y) (y : Y ⟶ Z)

private lemma inclusion_map_compIso_inv (V : SmallEtale B Z.obj Z.property) :
    (SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_compIso B X Y Z x y).val.inv.app V) =
      (Over.pullbackComp x y).hom.app V.obj := by
  let := hasPullbacks_bigEtaleSite B
  let := preservesPullbacks_bigEtaleSiteInclusion B
  apply (cancel_mono ((Over.pullbackComp x y).inv.app V.obj)).1
  calc
    _ = (SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_compIso B X Y Z x y).val.inv.app V) ≫
          (SmallEtale.inclusion B X.obj X.property).map
            ((smallEtaleBaseChange_compIso B X Y Z x y).val.hom.app V) :=
        congrArg
          (fun q => (SmallEtale.inclusion B X.obj X.property).map
            ((smallEtaleBaseChange_compIso B X Y Z x y).val.inv.app V) ≫ q)
          (smallEtaleBaseChange_compIso_app B X Y Z x y V).symm
    _ = (SmallEtale.inclusion B X.obj X.property).map
          (((smallEtaleBaseChange_compIso B X Y Z x y).val.inv.app V) ≫
            (smallEtaleBaseChange_compIso B X Y Z x y).val.hom.app V) := by
        rw [← Functor.map_comp]
    _ = _ := by simp

private lemma inclusion_map_compIso_hom (V : SmallEtale B Z.obj Z.property) :
    (SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_compIso B X Y Z x y).val.hom.app V) =
      (Over.pullbackComp x y).inv.app V.obj :=
  smallEtaleBaseChange_compIso_app B X Y Z x y V

private lemma inclusion_map_eqToHom {x x' : X ⟶ Y} (e : x = x')
    (V : SmallEtale B Y.obj Y.property) :
    (SmallEtale.inclusion B X.obj X.property).map
        ((eqToHom (congrArg (smallEtaleBaseChange B) e)).app V) =
      (eqToHom (congrArg (fun k : X ⟶ Y => Over.pullback k) e)).app V.obj := by
  subst e
  simp

private lemma inclusion_map_smallEtaleBaseChange_map {V V' : SmallEtale B Y.obj Y.property}
    (k : V ⟶ V') :
    (SmallEtale.inclusion B X.obj X.property).map ((smallEtaleBaseChange B x).map k) =
      (Over.pullback x).map ((SmallEtale.inclusion B Y.obj Y.property).map k) := rfl

/-- The comparison `c^* f^* U ⟵ f'^* b^* U` of the two iterated base changes around a commutative
square, through the base change along the common composite, is the unique morphism of the small
étale site compatible with the projections to `U`. -/
theorem smallEtaleBaseChange_square_eq {X' X Y' Y : B.Scheme} (c : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (b : Y' ⟶ Y) (h : c ≫ f = f' ≫ b) (U : SmallEtale B Y.obj Y.property)
    (φ : (smallEtaleBaseChange B f').obj ((smallEtaleBaseChange B b).obj U) ⟶
      (smallEtaleBaseChange B c).obj ((smallEtaleBaseChange B f).obj U))
    (hφ : φ.hom.left ≫ pullback.fst _ c ≫ pullback.fst U.obj.hom f =
      pullback.fst _ f' ≫ pullback.fst U.obj.hom b) :
    φ = (smallEtaleBaseChange_compIso B X' Y' Y f' b).val.hom.app U ≫
      (eqToHom (congrArg (smallEtaleBaseChange B) h.symm)).app U ≫
      (smallEtaleBaseChange_compIso B X' X Y c f).val.inv.app U := by
  apply (SmallEtale.inclusion B X'.obj X'.property).map_injective
  rw [Functor.map_comp, Functor.map_comp, inclusion_map_compIso_hom,
    inclusion_map_eqToHom (e := h.symm), inclusion_map_compIso_inv]
  exact Over.pullback_hom_ext₂ c f U.obj _ _
    (hφ.trans (Over.pullback_square_left_fst c f' f b h U.obj).symm)

end Projections

section Square

variable (A : Type u₁) [Category.{v₁} A]

/-- The 2-cell `c_* ⋙ f_* ⟶ f'_* ⋙ b_*` of a commutative square `c ≫ f = f' ≫ b` of a big
étale site: both composites are identified with the direct image along the common composite
(Stacks 021J). Its mate along the inverse-image/direct-image adjunctions of `c` and `b` is the
base change map `b⁻¹ f_* ⟶ f'_* c⁻¹`. -/
def smallEtalePushforwardSquare {X' X Y' Y : B.Scheme} (c : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (b : Y' ⟶ Y) (h : c ≫ f = f' ≫ b) :
    TwoSquare (B.smallPushforward c A) (B.smallPushforward f' A) (B.smallPushforward f A)
      (B.smallPushforward b A) :=
  letI := Functor.isContinuous_comp (smallEtaleBaseChange B f) (smallEtaleBaseChange B c)
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)
  letI := Functor.isContinuous_comp (smallEtaleBaseChange B b) (smallEtaleBaseChange B f')
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B Y'.obj Y'.property)
    (SmallEtale.topology B X'.obj X'.property)
  TwoSquare.mk _ _ _ _ <|
    (Functor.sheafPushforwardContinuousIso
      ((smallEtaleBaseChange_compIso B X' X Y c f).val ≪≫
        eqToIso (congrArg (smallEtaleBaseChange B) h) ≪≫
        (smallEtaleBaseChange_compIso B X' Y' Y f' b).val.symm) A
      (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X'.obj X'.property)).hom

/-- The direct-image 2-cell of a commutative square, on sections: restriction along the
comparison of the two iterated base changes through the base change along the common
composite. -/
theorem smallEtalePushforwardSquare_app_hom_app {X' X Y' Y : B.Scheme} (c : X' ⟶ X)
    (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y) (h : c ≫ f = f' ≫ b)
    (G : Sheaf (SmallEtale.topology B X'.obj X'.property) A)
    (U : (SmallEtale B Y.obj Y.property)ᵒᵖ) :
    ((smallEtalePushforwardSquare B A c f' f b h).app G).hom.app U =
      G.obj.map ((smallEtaleBaseChange_compIso B X' Y' Y f' b).val.hom.app U.unop ≫
        (eqToHom (congrArg (smallEtaleBaseChange B) h.symm)).app U.unop ≫
        (smallEtaleBaseChange_compIso B X' X Y c f).val.inv.app U.unop).op := by
  simp [smallEtalePushforwardSquare]
  rfl

/-- The comparison of direct images along a composite, on sections. -/
theorem smallEtaleSheafPushforwardCompIso_hom_app_sections {X Y Z : B.Scheme} (x : X ⟶ Y)
    (y : Y ⟶ Z) (G : Sheaf (SmallEtale.topology B X.obj X.property) A)
    (U : (SmallEtale B Z.obj Z.property)ᵒᵖ) :
    ((smallEtaleSheafPushforwardCompIso B X Y Z x y A).hom.app G).hom.app U =
      G.obj.map ((smallEtaleBaseChange_compIso B X Y Z x y).val.inv.app U.unop).op := by
  simp [smallEtaleSheafPushforwardCompIso]
  rfl

variable {X Y Z X' Y' Z' : B.Scheme} (c : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
  (g' : Y' ⟶ Z') (g : Y ⟶ Z) (a : Z' ⟶ Z)

/-- The vertical pasting of the direct-image 2-cells, on the small étale site of `X'`: the
two composites of the canonical comparisons of iterated base changes of an étale `Z`-scheme
`U` agree. -/
theorem smallEtaleBaseChange_paste (h₁ : c ≫ f = f' ≫ b) (h₂ : b ≫ g = g' ≫ a)
    (h : c ≫ f ≫ g = (f' ≫ g') ≫ a) (U : SmallEtale B Z.obj Z.property) :
    (smallEtaleBaseChange_compIso B X' Y' Z' f' g').val.inv.app
          ((smallEtaleBaseChange B a).obj U) ≫
        (smallEtaleBaseChange B f').map
          ((smallEtaleBaseChange_compIso B Y' Z' Z g' a).val.hom.app U) ≫
        (smallEtaleBaseChange B f').map
          ((eqToHom (congrArg (smallEtaleBaseChange B) h₂.symm)).app U) ≫
        (smallEtaleBaseChange B f').map
          ((smallEtaleBaseChange_compIso B Y' Y Z b g).val.inv.app U) ≫
        (smallEtaleBaseChange_compIso B X' Y' Y f' b).val.hom.app
          ((smallEtaleBaseChange B g).obj U) ≫
        (eqToHom (congrArg (smallEtaleBaseChange B) h₁.symm)).app
          ((smallEtaleBaseChange B g).obj U) ≫
        (smallEtaleBaseChange_compIso B X' X Y c f).val.inv.app
          ((smallEtaleBaseChange B g).obj U) =
      (smallEtaleBaseChange_compIso B X' Z' Z (f' ≫ g') a).val.hom.app U ≫
        (eqToHom (congrArg (smallEtaleBaseChange B) h.symm)).app U ≫
        (smallEtaleBaseChange_compIso B X' X Z c (f ≫ g)).val.inv.app U ≫
        (smallEtaleBaseChange B c).map
          ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app U) := by
  apply (SmallEtale.inclusion B X'.obj X'.property).map_injective
  simp only [Functor.map_comp, inclusion_map_compIso_inv, inclusion_map_compIso_hom,
    inclusion_map_smallEtaleBaseChange_map, inclusion_map_eqToHom (e := h.symm),
    inclusion_map_eqToHom (e := h₁.symm), inclusion_map_eqToHom (e := h₂.symm)]
  exact Over.pullback_paste c f' f b g' g a h₁ h₂ h U.obj

/-- **Vertical pasting of the direct-image 2-cells.** For two commutative squares on top of
each other, the 2-cell of the outer rectangle is the vertical paste of the 2-cells of the two
squares, through the comparisons `f_* ⋙ g_* ≅ (f ≫ g)_*` and `f'_* ⋙ g'_* ≅ (f' ≫ g')_*`. -/
theorem smallEtalePushforwardSquare_paste (h₁ : c ≫ f = f' ≫ b) (h₂ : b ≫ g = g' ≫ a)
    (h : c ≫ f ≫ g = (f' ≫ g') ≫ a)
    (G : Sheaf (SmallEtale.topology B X'.obj X'.property) A) :
    (B.smallPushforward g A).map ((smallEtalePushforwardSquare B A c f' f b h₁).app G) ≫
        (smallEtalePushforwardSquare B A b g' g a h₂).app ((B.smallPushforward f' A).obj G) ≫
        (B.smallPushforward a A).map
          ((smallEtaleSheafPushforwardCompIso B X' Y' Z' f' g' A).hom.app G) =
      (smallEtaleSheafPushforwardCompIso B X Y Z f g A).hom.app
          ((B.smallPushforward c A).obj G) ≫
        (smallEtalePushforwardSquare B A c (f' ≫ g') (f ≫ g) a h).app G := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have key := congrArg (fun m => G.obj.map m.op)
    (smallEtaleBaseChange_paste B c f' f b g' g a h₁ h₂ h U.unop)
  simp only [op_comp, Functor.map_comp, Category.assoc] at key
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    smallEtalePushforwardSquare_app_hom_app, Functor.sheafPushforwardContinuous_map_hom_app,
    smallEtaleSheafPushforwardCompIso_hom_app_sections,
    Functor.sheafPushforwardContinuous_obj_obj_map, op_comp, Functor.map_comp, Category.assoc,
    Quiver.Hom.unop_op, unop_comp]
  refine Eq.trans ?_ key
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _)))))))

section BaseChange

/-- The base change map `b⁻¹ f_* ⟶ f'_* c⁻¹` of a commutative square `c ≫ f = f' ≫ b` of a big
étale site, for sheaves with values in a category `A`: the mate, along the
inverse-image/direct-image adjunctions of `c` and `b`, of the identification
`AlgebraicGeometry.smallEtalePushforwardSquare` of the two composite direct images. For
`A = Type (u + 1)` it is `AlgebraicGeometry.smallEtaleBaseChangeNatTrans`. -/
def smallEtalePushforwardBaseChange {X' X Y' Y : B.Scheme} (c : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (b : Y' ⟶ Y) (h : c ≫ f = f' ≫ b) [(B.smallPushforward c A).IsRightAdjoint]
    [(B.smallPushforward b A).IsRightAdjoint] :
    TwoSquare (B.smallPushforward f A) (B.smallInverseImage c A) (B.smallInverseImage b A)
      (B.smallPushforward f' A) :=
  (mateEquiv (B.smallPullbackAdjunction c A) (B.smallPullbackAdjunction b A)).symm
    (smallEtalePushforwardSquare B A c f' f b h)

/-- **Pasting of base change maps** (Sites, Remark 0F6X, for small étale sites). For two
commutative squares on top of each other, the base change map of the outer rectangle is the
horizontal paste of the base change maps of the two squares, through the comparisons
`f_* ⋙ g_* ≅ (f ≫ g)_*` and `f'_* ⋙ g'_* ≅ (f' ≫ g')_*`. -/
theorem smallEtalePushforwardBaseChange_paste (h₁ : c ≫ f = f' ≫ b) (h₂ : b ≫ g = g' ≫ a)
    (h : c ≫ f ≫ g = (f' ≫ g') ≫ a) [(B.smallPushforward c A).IsRightAdjoint]
    [(B.smallPushforward b A).IsRightAdjoint] [(B.smallPushforward a A).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) A) :
    (B.smallInverseImage a A).map
        ((smallEtaleSheafPushforwardCompIso B X Y Z f g A).hom.app F) ≫
        (smallEtalePushforwardBaseChange B A c (f' ≫ g') (f ≫ g) a h).app F =
      (smallEtalePushforwardBaseChange B A b g' g a h₂).app ((B.smallPushforward f A).obj F) ≫
        (B.smallPushforward g' A).map
          ((smallEtalePushforwardBaseChange B A c f' f b h₁).app F) ≫
        (smallEtaleSheafPushforwardCompIso B X' Y' Z' f' g' A).hom.app
          ((B.smallInverseImage c A).obj F) :=
  mateEquiv_symm_paste_app (B.smallPullbackAdjunction c A) (B.smallPullbackAdjunction b A)
    (B.smallPullbackAdjunction a A) (smallEtaleSheafPushforwardCompIso B X Y Z f g A)
    (smallEtaleSheafPushforwardCompIso B X' Y' Z' f' g' A)
    (smallEtalePushforwardSquare B A c f' f b h₁) (smallEtalePushforwardSquare B A b g' g a h₂)
    (smallEtalePushforwardSquare B A c (f' ≫ g') (f ≫ g) a h)
    (smallEtalePushforwardSquare_paste B A c f' f b g' g a h₁ h₂ h) F

end BaseChange

end Square

end AlgebraicGeometry
