module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardSectionTransportCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso

/-!
# The functor of trivialisations of a module on a scheme

Let `U` be a scheme of the big fppf site of `S` and `N` a module on the small étale site of the
algebraic space `U`.  Over a scheme `h : V ⟶ U` over `U` the *trivialisations* of `N` are the
isomorphisms `𝒪_V ≅ h^*N`, and pulling them back along morphisms of schemes over `U` makes them a
presheaf on `Sch/U`.  For `N` invertible this is the functor whose representability is the
geometric content of Stacks 0D2A: it is `Isom(𝒪_T, σ_T^*L)` of the proof of that lemma.

## Main definitions

* `AlgebraicGeometry.Space.trivializationPullback`: the inverse image `𝒪_W ≅ q^*𝒪_V ≅ q^*a^*N ≅
  b^*N` of a trivialisation `𝒪_V ≅ a^*N` along `q : W ⟶ V` with `q ≫ a = b`.
* `AlgebraicGeometry.Space.trivializationsPresheaf`: the presheaf of trivialisations on the
  schemes over `U`.

## Main results

* `AlgebraicGeometry.Space.trivializationPullback_id` and
  `AlgebraicGeometry.Space.trivializationPullback_comp`: the inverse image of trivialisations is
  functorial, by the coherences of Stacks 03LU and of the identification `q^*𝒪 ≅ 𝒪`.

## References

* [Stacks Project, Tag 0D2A](https://stacks.math.columbia.edu/tag/0D2A)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Pullback

variable {V W X Z : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS Z.1 Z.2)

/-- The inverse image of a trivialisation. -/
def trivializationPullback {a : V ⟶ Z} {b : W ⟶ Z} (q : W ⟶ V) (h : q ≫ a = b)
    (α : structureModule V ≅ (modulePullback B S hS a).obj N) :
    structureModule W ≅ (modulePullback B S hS b).obj N :=
  structureModulePullbackIso q ≪≫ (modulePullback B S hS q).mapIso α ≪≫
    ((modulePullbackTriangle B S hS h).app N).symm

/-- The underlying homomorphism of the inverse image of a trivialisation. -/
theorem trivializationPullback_hom {a : V ⟶ Z} {b : W ⟶ Z} (q : W ⟶ V) (h : q ≫ a = b)
    (α : structureModule V ≅ (modulePullback B S hS a).obj N) :
    (trivializationPullback N q h α).hom = (structureModulePullbackIso q).hom ≫
      (modulePullback B S hS q).map α.hom ≫ (modulePullbackTriangle B S hS h).inv.app N :=
  rfl

/-- The comparison of Stacks 03LU for a composite with an identity, at a module. -/
theorem modulePullbackTriangle_id_app_symm {a : V ⟶ Z} (h : 𝟙 V ≫ a = a) :
    ((modulePullbackTriangle B S hS h).app N).symm =
      ((modulePushforwardCoherence B S hS).modulePullbackIdIso V).app
        ((modulePullback B S hS a).obj N) := by
  rw [(modulePushforwardCoherence B S hS).modulePullbackTriangle_id]
  ext1
  simp

/-- The inverse image of a trivialisation along an identity is the trivialisation. -/
theorem trivializationPullback_id {a : V ⟶ Z} (h : 𝟙 V ≫ a = a)
    (α : structureModule V ≅ (modulePullback B S hS a).obj N) :
    trivializationPullback N (𝟙 V) h α = α := by
  rw [trivializationPullback,
    (modulePushforwardCoherence B S hS).structureModulePullbackIso_id,
    modulePullbackTriangle_id_app_symm]
  ext1
  exact Functor.iso_id_conj _ α.hom

/-- The comparison of Stacks 03LU for a triple composite, at a module. -/
theorem modulePullbackTriangle_app_symm_comp {a : V ⟶ Z} {b : W ⟶ Z} {c : X ⟶ Z} (q : W ⟶ V)
    (r : X ⟶ W) (h1 : q ≫ a = b) (h2 : r ≫ b = c) (h3 : (r ≫ q) ≫ a = c) :
    ((modulePullbackTriangle B S hS h3).app N).symm =
      (modulePullbackTriangle B S hS (rfl : r ≫ q = r ≫ q)).app
          ((modulePullback B S hS a).obj N) ≪≫
        (modulePullback B S hS r).mapIso ((modulePullbackTriangle B S hS h1).app N).symm ≪≫
        ((modulePullbackTriangle B S hS h2).app N).symm := by
  have key := congrArg (fun e ↦ e.app N)
    ((modulePushforwardCoherence B S hS).modulePullbackTriangle_comp
      (f := r) (g := q) (p := a) rfl h1 h2 h3)
  have key' : (modulePullbackTriangle B S hS h3).app N ≪≫
      (modulePullbackTriangle B S hS (rfl : r ≫ q = r ≫ q)).app
        ((modulePullback B S hS a).obj N) =
      (modulePullbackTriangle B S hS h2).app N ≪≫
        (modulePullback B S hS r).mapIso ((modulePullbackTriangle B S hS h1).app N) := by
    ext1
    have k2 := congrArg Iso.hom key
    simpa only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id, Functor.mapIso_hom] using k2
  calc ((modulePullbackTriangle B S hS h3).app N).symm
      = (modulePullbackTriangle B S hS (rfl : r ≫ q = r ≫ q)).app
            ((modulePullback B S hS a).obj N) ≪≫
          ((modulePullbackTriangle B S hS h3).app N ≪≫
            (modulePullbackTriangle B S hS (rfl : r ≫ q = r ≫ q)).app
              ((modulePullback B S hS a).obj N)).symm := by
        rw [Iso.trans_symm, ← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
    _ = _ := by
        rw [key', Iso.trans_symm, Functor.mapIso_symm]

/-- The inverse image of a trivialisation along a composite is the inverse image along the two
factors in turn. -/
theorem trivializationPullback_comp {a : V ⟶ Z} {b : W ⟶ Z} {c : X ⟶ Z} (q : W ⟶ V)
    (r : X ⟶ W) (h1 : q ≫ a = b) (h2 : r ≫ b = c) (h3 : (r ≫ q) ≫ a = c)
    (α : structureModule V ≅ (modulePullback B S hS a).obj N) :
    trivializationPullback N (r ≫ q) h3 α =
      trivializationPullback N r h2 (trivializationPullback N q h1 α) := by
  ext1
  rw [trivializationPullback_hom, trivializationPullback_hom, trivializationPullback_hom]
  exact Functor.transport_comp_iso _ _ _ _
    (ModulePushforwardCoherence.structureModulePullbackIso_symm_of_comp r q rfl) _ _ _
    (modulePullbackTriangle_app_symm_comp N q r h1 h2 h3) α.hom

/-- The inverse image of a trivialisation depends on the morphism, not on its presentation. -/
theorem trivializationPullback_congr {a : V ⟶ Z} {b : W ⟶ Z} {q q' : W ⟶ V} (hq : q = q')
    (h : q ≫ a = b) (h' : q' ≫ a = b)
    (α : structureModule V ≅ (modulePullback B S hS a).obj N) :
    trivializationPullback N q h α = trivializationPullback N q' h' α := by
  subst hq
  rfl

end Pullback

section Presheaf

variable (U : BigFppfOver B S hS)
  (N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
    ((schemeSpaceFunctor B S hS).obj U).2)

/-- **The functor of trivialisations of a module on a scheme.**  Over a scheme `h : V ⟶ U`
over `U` its value is the set of trivialisations `𝒪_V ≅ h^*N`, and restriction is the inverse
image of trivialisations. -/
def trivializationsPresheaf : (Over U)ᵒᵖ ⥤ Type (u + 1) where
  obj V := structureModule ((schemeSpaceFunctor B S hS).obj V.unop.left) ≅
    (modulePullback B S hS ((schemeSpaceFunctor B S hS).map V.unop.hom)).obj N
  map {V₁ V₂} g := TypeCat.ofHom fun α ↦
    trivializationPullback N ((schemeSpaceFunctor B S hS).map g.unop.left)
      (by rw [← Functor.map_comp, Over.w g.unop]) α
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro α
    exact (trivializationPullback_congr N (by simp) _ (by simp) α).trans
      (trivializationPullback_id N _ α)
  map_comp {V₁ V₂ V₃} f g := by
    apply ConcreteCategory.hom_ext
    intro α
    exact (trivializationPullback_congr N (by simp) _ (by simp [← Functor.map_comp]) α).trans
      (trivializationPullback_comp N _ _ _ _ _ α)

/-- Restriction in the presheaf of trivialisations is the inverse image of trivialisations. -/
theorem trivializationsPresheaf_map_apply {V₁ V₂ : (Over U)ᵒᵖ} (g : V₁ ⟶ V₂)
    (α : (trivializationsPresheaf U N).obj V₁) :
    (trivializationsPresheaf U N).map g α =
      trivializationPullback N ((schemeSpaceFunctor B S hS).map g.unop.left)
        (by rw [← CategoryTheory.Functor.map_comp, Over.w g.unop]) α := by
  dsimp only [trivializationsPresheaf]
  exact TypeCat.ofHom_apply _ α

end Presheaf

end AlgebraicGeometry.Space
