module

public import StacksFrontier.CategoryTheory.Sites.InverseImageTensor

/-!
# Naturality of the inverse image/tensor comparison for sheaves of modules

`Stacks.InverseImageTensor.sheafPullbackTensorIso` compares the inverse image of a tensor
product of sheaves of `Λ`-modules along a continuous functor of sites with the tensor product of
the inverse images. This file proves that comparison natural in each variable separately, in the
two shapes `CategoryTheory.Functor.mapBifunctorTotalIso` consumes as its hypotheses `hε₁` and
`hε₂` — that is, for `F := curriedTensor (Sheaf J (ModuleCat Λ))`,
`F' := curriedTensor (Sheaf J' (ModuleCat Λ))`, `Φ = Φ₁ = Φ₂ := G.sheafPullback (ModuleCat Λ) J J'`
and `ε := sheafPullbackTensorIso`. With them, inverse image commutes with the *total tensor
complex* of two complexes of sheaves of `Λ`-modules.

## Main results

* `Stacks.InverseImageTensor.lanDelta_natural_left` and
  `Stacks.InverseImageTensor.lanDelta_natural_right` — the comparison
  `Stacks.InverseImageTensor.lanDelta` between the left Kan extension of a tensor product and the
  tensor product of the left Kan extensions is natural in each variable.
* `Stacks.InverseImageTensor.sheafPullbackTensorIso_naturality_left` and
  `Stacks.InverseImageTensor.sheafPullbackTensorIso_naturality_right` — **the two naturality
  squares of the inverse image/tensor comparison of sheaves.**

## Implementation notes

Naturality of `lanDelta` was the only missing link, and it is a uniqueness-of-lifts argument
rather than a diagram chase: both sides are morphisms out of `K.lan.obj (P ⊗ Q)`, which is a left
Kan extension, so `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension` reduces the claim to
agreement after the unit, where `Stacks.InverseImageTensor.lanUnit_app_comp_lanDelta_app` and
naturality of `K.lanUnit` identify both sides with a tensor product of units.

The remaining five factors of the six-fold composite defining `sheafPullbackTensorIso` are
natural for standard reasons: naturality of the counit of `sheafificationAdjunction`,
`CategoryTheory.Functor.LaxMonoidal.μ_natural_left` and `_right` together with
`CategoryTheory.Functor.OplaxMonoidal.δ_natural_left` and `_right` for `presheafToSheaf`, and
naturality of `Stacks.InverseImageTensor.sheafifyCompPullbackIso`, which is an isomorphism of
functors. No monoidal structure on `G.sheafPullback` is constructed: a `Functor.Monoidal`
instance would additionally owe the unit comparison and the associativity coherence, and then an
identification of its tensorator with `sheafPullbackTensorIso`.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v v' u u' w

namespace Stacks.InverseImageTensor

section Lan

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (K : C ⥤ D)
  (Λ : Type w) [CommRing Λ]
  [∀ X : D, HasColimitsOfShape (CostructuredArrow K X) (ModuleCat.{w} Λ)]

/-- Naturality of the unit of the left Kan extension, componentwise. -/
private theorem lanUnit_app_comp_lan_map_app {X Y : C ⥤ ModuleCat.{w} Λ} (u : X ⟶ Y) (c : C) :
    (K.lanUnit.app X).app c ≫ (K.lan.map u).app (K.obj c)
      = u.app c ≫ (K.lanUnit.app Y).app c :=
  (NatTrans.congr_app (K.lanUnit.naturality u) c).symm

/-- Naturality of `Stacks.InverseImageTensor.lanDelta` in the first variable. Both sides are
morphisms out of `K.lan.obj (P ⊗ Q)`, a left Kan extension, so they agree as soon as they agree
after the unit, where both are the tensor product of units precomposed with `f`. -/
@[reassoc]
public theorem lanDelta_natural_left {P P' : C ⥤ ModuleCat.{w} Λ} (f : P ⟶ P')
    (Q : C ⥤ ModuleCat.{w} Λ) :
    K.lan.map (f ▷ Q) ≫ lanDelta K Λ P' Q
      = lanDelta K Λ P Q ≫ K.lan.map f ▷ K.lan.obj Q := by
  refine Functor.hom_ext_of_isLeftKanExtension _ (K.lanUnit.app (P ⊗ Q)) _ _
    (NatTrans.ext (funext fun c => ?_))
  have hL : (K.lanUnit.app (P ⊗ Q)).app c ≫ (K.lan.map (f ▷ Q)).app (K.obj c) ≫
      (lanDelta K Λ P' Q).app (K.obj c)
      = (f.app c ≫ (K.lanUnit.app P').app c) ⊗ₘ (K.lanUnit.app Q).app c := by
    rw [← Category.assoc, lanUnit_app_comp_lan_map_app K Λ (f ▷ Q) c, Category.assoc,
      lanUnit_app_comp_lanDelta_app]
    exact MonoidalCategory.whiskerRight_comp_tensorHom _ _ _
  have hR : (K.lanUnit.app (P ⊗ Q)).app c ≫ (lanDelta K Λ P Q).app (K.obj c) ≫
      (K.lan.map f ▷ K.lan.obj Q).app (K.obj c)
      = ((K.lanUnit.app P).app c ≫ (K.lan.map f).app (K.obj c)) ⊗ₘ (K.lanUnit.app Q).app c := by
    rw [← Category.assoc, lanUnit_app_comp_lanDelta_app]
    exact MonoidalCategory.tensorHom_comp_whiskerRight _ _ _
  exact hL.trans (Eq.trans (by rw [lanUnit_app_comp_lan_map_app K Λ f c]) hR.symm)

/-- Naturality of `Stacks.InverseImageTensor.lanDelta` in the second variable. -/
@[reassoc]
public theorem lanDelta_natural_right (P : C ⥤ ModuleCat.{w} Λ) {Q Q' : C ⥤ ModuleCat.{w} Λ}
    (g : Q ⟶ Q') :
    K.lan.map (P ◁ g) ≫ lanDelta K Λ P Q'
      = lanDelta K Λ P Q ≫ K.lan.obj P ◁ K.lan.map g := by
  refine Functor.hom_ext_of_isLeftKanExtension _ (K.lanUnit.app (P ⊗ Q)) _ _
    (NatTrans.ext (funext fun c => ?_))
  have hL : (K.lanUnit.app (P ⊗ Q)).app c ≫ (K.lan.map (P ◁ g)).app (K.obj c) ≫
      (lanDelta K Λ P Q').app (K.obj c)
      = (K.lanUnit.app P).app c ⊗ₘ (g.app c ≫ (K.lanUnit.app Q').app c) := by
    rw [← Category.assoc, lanUnit_app_comp_lan_map_app K Λ (P ◁ g) c, Category.assoc,
      lanUnit_app_comp_lanDelta_app]
    exact MonoidalCategory.whiskerLeft_comp_tensorHom _ _ _
  have hR : (K.lanUnit.app (P ⊗ Q)).app c ≫ (lanDelta K Λ P Q).app (K.obj c) ≫
      (K.lan.obj P ◁ K.lan.map g).app (K.obj c)
      = (K.lanUnit.app P).app c ⊗ₘ ((K.lanUnit.app Q).app c ≫ (K.lan.map g).app (K.obj c)) := by
    rw [← Category.assoc, lanUnit_app_comp_lanDelta_app]
    exact MonoidalCategory.tensorHom_comp_whiskerLeft _ _ _
  exact hL.trans (Eq.trans (by rw [lanUnit_app_comp_lan_map_app K Λ g c]) hR.symm)

end Lan

/-- Naturality of the counit of the sheafification adjunction. -/
private theorem map_map_comp_counit_app {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{w} Λ)] {a a' : Sheaf J (ModuleCat.{w} Λ)} (f : a ⟶ a') :
    (presheafToSheaf J (ModuleCat.{w} Λ)).map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f) ≫
        (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a'
      = (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a ≫ f :=
  (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.naturality f

/-- A morphism of sheaves composed with the inverse of the counit of the target is the inverse of
the counit of the source composed with the sheafification of the underlying presheaf morphism. -/
private theorem comp_inv_counit_app {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{w} Λ)] {a a' : Sheaf J (ModuleCat.{w} Λ)} (f : a ⟶ a') :
    f ≫ inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a')
      = inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a) ≫
        (presheafToSheaf J (ModuleCat.{w} Λ)).map
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f) := by
  rw [IsIso.comp_inv_eq, Category.assoc, map_map_comp_counit_app J Λ f,
    IsIso.inv_hom_id_assoc]

section Sheaf

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) (Λ : Type w) [CommRing Λ]
  (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
  [G.IsContinuous J J']
  [HasWeakSheafify J (ModuleCat.{w} Λ)] [HasWeakSheafify J' (ModuleCat.{w} Λ)]
  [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) (ModuleCat.{w} Λ)]
  [(G.sheafPushforwardContinuous (ModuleCat.{w} Λ) J J').IsRightAdjoint]
  [(J.W (A := ModuleCat.{w} Λ)).IsMonoidal] [(J'.W (A := ModuleCat.{w} Λ)).IsMonoidal]
  [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G.op X)]

private instance (F : Cᵒᵖ ⥤ ModuleCat.{w} Λ) : G.op.HasLeftKanExtension F :=
  Functor.HasLeftKanExtension.mk _ (Functor.pointwiseLeftKanExtensionUnit G.op F)

public theorem sheafPullbackTensorIso_naturality_left {a a' : Sheaf J (ModuleCat.{w} Λ)}
    (f : a ⟶ a') (b : Sheaf J (ModuleCat.{w} Λ)) :
    (G.sheafPullback (ModuleCat.{w} Λ) J J').map
          (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map f).app b) ≫
        (sheafPullbackTensorIso G Λ J J' a' b).hom
      = (sheafPullbackTensorIso G Λ J J' a b).hom ≫
        ((curriedTensor (Sheaf J' (ModuleCat.{w} Λ))).map
            ((G.sheafPullback (ModuleCat.{w} Λ) J J').map f)).app
          ((G.sheafPullback (ModuleCat.{w} Λ) J J').obj b) := by
  simp only [sheafPullbackTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorIso_hom, tensorIso_inv, asIso_hom, asIso_inv, curriedTensor_map_app,
    Iso.app_hom, Iso.app_inv, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
    Category.assoc]
  have key1 : (f ▷ b) ≫
        (inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a') ⊗ₘ
            inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app b)) ≫
          Functor.LaxMonoidal.μ (presheafToSheaf J (ModuleCat.{w} Λ))
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a')
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)
      = ((inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a) ⊗ₘ
            inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app b)) ≫
          Functor.LaxMonoidal.μ (presheafToSheaf J (ModuleCat.{w} Λ))
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
        (presheafToSheaf J (ModuleCat.{w} Λ)).map
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f ▷
            (sheafToPresheaf J (ModuleCat.{w} Λ)).obj b) := by
    rw [← Category.assoc, MonoidalCategory.whiskerRight_comp_tensorHom, comp_inv_counit_app J Λ f,
      ← MonoidalCategory.tensorHom_comp_whiskerRight, Category.assoc]
    simp only [Functor.comp_obj]
    rw [Functor.LaxMonoidal.μ_natural_left, Category.assoc]
  have h1 : (G.sheafPullback (ModuleCat.{w} Λ) J J').map
        ((presheafToSheaf J (ModuleCat.{w} Λ)).map
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f ▷
            (sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
      (sheafifyCompPullbackIso G Λ J J').hom.app
        ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a' ⊗
          (sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)
      = (sheafifyCompPullbackIso G Λ J J').hom.app
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a ⊗
              (sheafToPresheaf J (ModuleCat.{w} Λ)).obj b) ≫
        (presheafToSheaf J' (ModuleCat.{w} Λ)).map
          (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f ▷
            (sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) :=
    (sheafifyCompPullbackIso G Λ J J').hom.naturality _
  have h2 : (presheafToSheaf J' (ModuleCat.{w} Λ)).map
        (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f ▷
          (sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
      (presheafToSheaf J' (ModuleCat.{w} Λ)).map
        (lanDelta G.op Λ ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a')
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b))
      = (presheafToSheaf J' (ModuleCat.{w} Λ)).map
            (lanDelta G.op Λ ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)
              ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
        (presheafToSheaf J' (ModuleCat.{w} Λ)).map
          (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f) ▷
            G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, lanDelta_natural_left]
  have h3 : (presheafToSheaf J' (ModuleCat.{w} Λ)).map
        (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f) ▷
          G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
      Functor.OplaxMonoidal.δ (presheafToSheaf J' (ModuleCat.{w} Λ))
        (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a'))
        (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b))
      = Functor.OplaxMonoidal.δ (presheafToSheaf J' (ModuleCat.{w} Λ))
            (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a))
            (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
        (presheafToSheaf J' (ModuleCat.{w} Λ)).map
            (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f)) ▷
          (presheafToSheaf J' (ModuleCat.{w} Λ)).obj
            (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) :=
    (Functor.OplaxMonoidal.δ_natural_left (presheafToSheaf J' (ModuleCat.{w} Λ)) _ _).symm
  have hSinv : (presheafToSheaf J' (ModuleCat.{w} Λ)).map
        (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f)) ≫
      (sheafifyCompPullbackIso G Λ J J').inv.app
        ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a')
      = (sheafifyCompPullbackIso G Λ J J').inv.app
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a) ≫
        (G.sheafPullback (ModuleCat.{w} Λ) J J').map
          ((presheafToSheaf J (ModuleCat.{w} Λ)).map
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f)) :=
    (sheafifyCompPullbackIso G Λ J J').inv.naturality _
  have h4 : ((presheafToSheaf J' (ModuleCat.{w} Λ)).map
          (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f)) ▷
        (presheafToSheaf J' (ModuleCat.{w} Λ)).obj
          (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b))) ≫
      ((sheafifyCompPullbackIso G Λ J J').inv.app
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a') ⊗ₘ
        (sheafifyCompPullbackIso G Λ J J').inv.app
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b))
      = ((sheafifyCompPullbackIso G Λ J J').inv.app
              ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a) ⊗ₘ
          (sheafifyCompPullbackIso G Λ J J').inv.app
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
        ((G.sheafPullback (ModuleCat.{w} Λ) J J').map
            ((presheafToSheaf J (ModuleCat.{w} Λ)).map
              ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f)) ▷
          (G.sheafPullback (ModuleCat.{w} Λ) J J').obj
            ((presheafToSheaf J (ModuleCat.{w} Λ)).obj
              ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b))) := by
    rw [MonoidalCategory.whiskerRight_comp_tensorHom, hSinv]
    exact (MonoidalCategory.tensorHom_comp_whiskerRight _ _ _).symm
  have h5 : ((G.sheafPullback (ModuleCat.{w} Λ) J J').map
          ((presheafToSheaf J (ModuleCat.{w} Λ)).map
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).map f)) ▷
        (G.sheafPullback (ModuleCat.{w} Λ) J J').obj
          ((presheafToSheaf J (ModuleCat.{w} Λ)).obj
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b))) ≫
      ((G.sheafPullback (ModuleCat.{w} Λ) J J').map
            ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a') ⊗ₘ
        (G.sheafPullback (ModuleCat.{w} Λ) J J').map
          ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app b))
      = ((G.sheafPullback (ModuleCat.{w} Λ) J J').map
              ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a) ⊗ₘ
          (G.sheafPullback (ModuleCat.{w} Λ) J J').map
            ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app b)) ≫
        ((G.sheafPullback (ModuleCat.{w} Λ) J J').map f ▷
          (G.sheafPullback (ModuleCat.{w} Λ) J J').obj b) := by
    rw [MonoidalCategory.whiskerRight_comp_tensorHom, ← Functor.map_comp,
      map_map_comp_counit_app J Λ f,
      Functor.map_comp]
    exact (MonoidalCategory.tensorHom_comp_whiskerRight _ _ _).symm
  rw [← Functor.map_comp_assoc, key1, Functor.map_comp, Category.assoc,
    reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, reassoc_of% h4, h5]

public theorem sheafPullbackTensorIso_naturality_right (a : Sheaf J (ModuleCat.{w} Λ))
    {b b' : Sheaf J (ModuleCat.{w} Λ)} (g : b ⟶ b') :
    (G.sheafPullback (ModuleCat.{w} Λ) J J').map
          (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).obj a).map g) ≫
        (sheafPullbackTensorIso G Λ J J' a b').hom
      = (sheafPullbackTensorIso G Λ J J' a b).hom ≫
        ((curriedTensor (Sheaf J' (ModuleCat.{w} Λ))).obj
            ((G.sheafPullback (ModuleCat.{w} Λ) J J').obj a)).map
          ((G.sheafPullback (ModuleCat.{w} Λ) J J').map g) := by
  simp only [sheafPullbackTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorIso_hom, tensorIso_inv, asIso_hom, asIso_inv, curriedTensor_obj_map,
    Iso.app_hom, Iso.app_inv, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
    Category.assoc]
  have key1 : (a ◁ g) ≫
        (inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a) ⊗ₘ
            inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app b')) ≫
          Functor.LaxMonoidal.μ (presheafToSheaf J (ModuleCat.{w} Λ))
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b')
      = ((inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a) ⊗ₘ
            inv ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app b)) ≫
          Functor.LaxMonoidal.μ (presheafToSheaf J (ModuleCat.{w} Λ))
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
        (presheafToSheaf J (ModuleCat.{w} Λ)).map
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a ◁
            (sheafToPresheaf J (ModuleCat.{w} Λ)).map g) := by
    rw [← Category.assoc, MonoidalCategory.whiskerLeft_comp_tensorHom, comp_inv_counit_app J Λ g,
      ← MonoidalCategory.tensorHom_comp_whiskerLeft, Category.assoc]
    simp only [Functor.comp_obj]
    rw [Functor.LaxMonoidal.μ_natural_right, Category.assoc]
  have h1 : (G.sheafPullback (ModuleCat.{w} Λ) J J').map
        ((presheafToSheaf J (ModuleCat.{w} Λ)).map
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a ◁
            (sheafToPresheaf J (ModuleCat.{w} Λ)).map g)) ≫
      (sheafifyCompPullbackIso G Λ J J').hom.app
        ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a ⊗
          (sheafToPresheaf J (ModuleCat.{w} Λ)).obj b')
      = (sheafifyCompPullbackIso G Λ J J').hom.app
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a ⊗
              (sheafToPresheaf J (ModuleCat.{w} Λ)).obj b) ≫
        (presheafToSheaf J' (ModuleCat.{w} Λ)).map
          (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a ◁
            (sheafToPresheaf J (ModuleCat.{w} Λ)).map g)) :=
    (sheafifyCompPullbackIso G Λ J J').hom.naturality _
  have h2 : (presheafToSheaf J' (ModuleCat.{w} Λ)).map
        (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a ◁
          (sheafToPresheaf J (ModuleCat.{w} Λ)).map g)) ≫
      (presheafToSheaf J' (ModuleCat.{w} Λ)).map
        (lanDelta G.op Λ ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b'))
      = (presheafToSheaf J' (ModuleCat.{w} Λ)).map
            (lanDelta G.op Λ ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)
              ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
        (presheafToSheaf J' (ModuleCat.{w} Λ)).map
          (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a) ◁
            G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map g)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, lanDelta_natural_right]
  have h3 : (presheafToSheaf J' (ModuleCat.{w} Λ)).map
        (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a) ◁
          G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map g)) ≫
      Functor.OplaxMonoidal.δ (presheafToSheaf J' (ModuleCat.{w} Λ))
        (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a))
        (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b'))
      = Functor.OplaxMonoidal.δ (presheafToSheaf J' (ModuleCat.{w} Λ))
            (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a))
            (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
        (presheafToSheaf J' (ModuleCat.{w} Λ)).obj
            (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)) ◁
          (presheafToSheaf J' (ModuleCat.{w} Λ)).map
            (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map g)) :=
    (Functor.OplaxMonoidal.δ_natural_right (presheafToSheaf J' (ModuleCat.{w} Λ)) _ _).symm
  have hSinv : (presheafToSheaf J' (ModuleCat.{w} Λ)).map
        (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map g)) ≫
      (sheafifyCompPullbackIso G Λ J J').inv.app
        ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b')
      = (sheafifyCompPullbackIso G Λ J J').inv.app
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b) ≫
        (G.sheafPullback (ModuleCat.{w} Λ) J J').map
          ((presheafToSheaf J (ModuleCat.{w} Λ)).map
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).map g)) :=
    (sheafifyCompPullbackIso G Λ J J').inv.naturality _
  have h4 : ((presheafToSheaf J' (ModuleCat.{w} Λ)).obj
          (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)) ◁
        (presheafToSheaf J' (ModuleCat.{w} Λ)).map
          (G.op.lan.map ((sheafToPresheaf J (ModuleCat.{w} Λ)).map g))) ≫
      ((sheafifyCompPullbackIso G Λ J J').inv.app
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a) ⊗ₘ
        (sheafifyCompPullbackIso G Λ J J').inv.app
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b'))
      = ((sheafifyCompPullbackIso G Λ J J').inv.app
              ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a) ⊗ₘ
          (sheafifyCompPullbackIso G Λ J J').inv.app
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj b)) ≫
        ((G.sheafPullback (ModuleCat.{w} Λ) J J').obj
            ((presheafToSheaf J (ModuleCat.{w} Λ)).obj
              ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)) ◁
          (G.sheafPullback (ModuleCat.{w} Λ) J J').map
            ((presheafToSheaf J (ModuleCat.{w} Λ)).map
              ((sheafToPresheaf J (ModuleCat.{w} Λ)).map g))) := by
    rw [MonoidalCategory.whiskerLeft_comp_tensorHom, hSinv]
    exact (MonoidalCategory.tensorHom_comp_whiskerLeft _ _ _).symm
  have h5 : ((G.sheafPullback (ModuleCat.{w} Λ) J J').obj
          ((presheafToSheaf J (ModuleCat.{w} Λ)).obj
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj a)) ◁
        (G.sheafPullback (ModuleCat.{w} Λ) J J').map
          ((presheafToSheaf J (ModuleCat.{w} Λ)).map
            ((sheafToPresheaf J (ModuleCat.{w} Λ)).map g))) ≫
      ((G.sheafPullback (ModuleCat.{w} Λ) J J').map
            ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a) ⊗ₘ
        (G.sheafPullback (ModuleCat.{w} Λ) J J').map
          ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app b'))
      = ((G.sheafPullback (ModuleCat.{w} Λ) J J').map
              ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app a) ⊗ₘ
          (G.sheafPullback (ModuleCat.{w} Λ) J J').map
            ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app b)) ≫
        ((G.sheafPullback (ModuleCat.{w} Λ) J J').obj a ◁
          (G.sheafPullback (ModuleCat.{w} Λ) J J').map g) := by
    rw [MonoidalCategory.whiskerLeft_comp_tensorHom, ← Functor.map_comp,
      map_map_comp_counit_app J Λ g,
      Functor.map_comp]
    exact (MonoidalCategory.tensorHom_comp_whiskerLeft _ _ _).symm
  rw [← Functor.map_comp_assoc, key1, Functor.map_comp, Category.assoc,
    reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, reassoc_of% h4, h5]

end Sheaf

end Stacks.InverseImageTensor

end
