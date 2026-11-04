module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# A right adjoint to a functor into a categorical pullback

Let `F : A' ⥤ B` and `G : C ⥤ B` be functors and let `S` be a categorical commutative square
over them with cone point `A`: functors `S.fst : A ⥤ A'` and `S.snd : A ⥤ C` together with an
isomorphism `S.fst ⋙ F ≅ S.snd ⋙ G`. It defines a functor `A ⥤ F ⊡ G` into the categorical
pullback. If `S.fst`, `S.snd` and `G` are left adjoints, with right adjoints `R₁`, `R₂` and `R`,
and `A` has pullbacks, this functor has a right adjoint: it sends a triple
`(x', y, φ : F x' ≅ G y)` to the fibre product of `R₁ x' ⟶ R₂ R G y ⟵ R₂ y`, where the second
map is `R₂` of the unit of `G ⊣ R`, and the first is adjoint to
`S.snd (R₁ x') ⋙ G ≅ F (S.fst (R₁ x')) ⟶ F x' ≅ G y`, built from the counit of
`S.fst ⊣ R₁` and `φ`.

This is the construction of a quasi-inverse in [Stacks, Tag 0GF4], where `S` is the inverse
image to a proper modification and to its centre, and `F`, `G` are the inverse images to the
exceptional locus.

## Main definitions

All names are in the namespace `CategoryTheory.Limits.CategoricalPullback`.

* `gluingObj`: the fibre product above.
* `gluingHomEquiv`: maps out of the image of an object of `A` into a triple are maps into the
  fibre product.
* `gluingAdjunction`: the adjunction.
* `gluingUnit`: its unit, the pair of units of `S.fst ⊣ R₁` and `S.snd ⊣ R₂`.

## Main results

* `gluingAdjunction_counit_app_fst` and `gluingAdjunction_counit_app_snd`: the components of the
  counit are the counits of `S.fst ⊣ R₁` and `S.snd ⊣ R₂` after the two projections.
* `gluingAdjunction_unit_app_fst` and `gluingAdjunction_unit_app_snd`: the unit is the pair of
  units of `S.fst ⊣ R₁` and `S.snd ⊣ R₂`.
* `isIso_map_pullbackSnd_gluingObj`: if `S.snd` preserves the fibre product, the base change map
  `R₁ ⋙ S.snd ⟶ F ⋙ R` (the mate of `S.iso⁻¹`) is invertible at `x'` and the counit of
  `S.snd ⊣ R₂` is invertible at `R G y`, then `S.snd` carries the second projection out of the
  fibre product to an isomorphism.
* `isEquivalence_toFunctorToCategoricalPullback_of_isIso`: the functor `A ⥤ F ⊡ G` is an
  equivalence as soon as the unit (`gluingUnit`) and the two components of the counit of
  `gluingAdjunction` are invertible.

## References

* [Stacks Project, Tag 0GF4](https://stacks.math.columbia.edu/tag/0GF4)
* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Limits.CategoricalPullback

variable {A : Type*} {A' : Type*} {B : Type*} {C : Type*}
  [Category* A] [Category* A'] [Category* B] [Category* C]
  {F : A' ⥤ B} {G : C ⥤ B} (S : CatCommSqOver F G A)
  {R₁ : A' ⥤ A} {R₂ : C ⥤ A} {R : B ⥤ C}
  (adj₁ : S.fst ⊣ R₁) (adj₂ : S.snd ⊣ R₂) (adj : G ⊣ R)

/-- For a triple `x = (x', y, φ)` of `F ⊡ G`, the map `R₁ x' ⟶ R₂ R G y` adjoint to
`G (S.snd (R₁ x')) ≅ F (S.fst (R₁ x')) ⟶ F x' ≅ G y`. -/
def gluingFst (x : F ⊡ G) : R₁.obj x.fst ⟶ R₂.obj (R.obj (G.obj x.snd)) :=
  adj₂.homEquiv _ _ (adj.homEquiv _ _
    (S.iso.inv.app (R₁.obj x.fst) ≫ F.map (adj₁.counit.app x.fst) ≫ x.iso.hom))

variable (R₂) in
/-- For a triple `x = (x', y, φ)` of `F ⊡ G`, the map `R₂ y ⟶ R₂ R G y` given by the unit of
`G ⊣ R`. -/
def gluingSnd (x : F ⊡ G) : R₂.obj x.snd ⟶ R₂.obj (R.obj (G.obj x.snd)) :=
  R₂.map (adj.unit.app x.snd)

variable [HasPullbacks A]

/-- The value at a triple `x = (x', y, φ)` of the right adjoint of the functor `A ⥤ F ⊡ G`
defined by `S`: the fibre product of `R₁ x' ⟶ R₂ R G y ⟵ R₂ y`. -/
abbrev gluingObj (x : F ⊡ G) : A :=
  pullback (gluingFst S adj₁ adj₂ adj x) (gluingSnd R₂ adj x)

/-- Two maps into `R₁ x'` and `R₂ y` agree in `R₂ R G y` exactly when their adjoints form a
morphism of `F ⊡ G`. -/
theorem gluing_condition_iff {a : A} (x : F ⊡ G) (p : a ⟶ R₁.obj x.fst)
    (q : a ⟶ R₂.obj x.snd) :
    p ≫ gluingFst S adj₁ adj₂ adj x = q ≫ gluingSnd R₂ adj x ↔
      F.map ((adj₁.homEquiv _ _).symm p) ≫ x.iso.hom =
        S.iso.hom.app a ≫ G.map ((adj₂.homEquiv _ _).symm q) := by
  have hp : p ≫ gluingFst S adj₁ adj₂ adj x = adj₂.homEquiv _ _ (adj.homEquiv _ _
      (S.iso.inv.app a ≫ F.map ((adj₁.homEquiv _ _).symm p) ≫ x.iso.hom)) := by
    rw [gluingFst, ← adj₂.homEquiv_naturality_left, ← adj.homEquiv_naturality_left,
      ← Functor.comp_map S.snd G, S.iso.inv.naturality_assoc, Functor.comp_map, ← F.map_comp_assoc,
      Adjunction.homEquiv_counit]
  have hq : q ≫ gluingSnd R₂ adj x = adj₂.homEquiv _ _ (adj.homEquiv _ _
      (G.map ((adj₂.homEquiv _ _).symm q))) := by
    have h : adj.homEquiv _ _ (G.map ((adj₂.homEquiv _ _).symm q)) =
        (adj₂.homEquiv _ _).symm q ≫ adj.unit.app _ := by
      simp [Adjunction.homEquiv_unit]
    rw [h, adj₂.homEquiv_naturality_right, Equiv.apply_symm_apply, gluingSnd]
  rw [hp, hq, (adj₂.homEquiv _ _).injective.eq_iff, (adj.homEquiv _ _).injective.eq_iff,
    ← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom]

/-- `gluing_condition_iff` read on the adjoints: a pair of maps `S.fst a ⟶ x'` and `S.snd a ⟶ y`
is a morphism of `F ⊡ G` exactly when its two adjoints agree in `R₂ R G y`. -/
theorem gluing_condition_iff' {a : A} (x : F ⊡ G) (u : S.fst.obj a ⟶ x.fst)
    (v : S.snd.obj a ⟶ x.snd) :
    adj₁.homEquiv _ _ u ≫ gluingFst S adj₁ adj₂ adj x =
        adj₂.homEquiv _ _ v ≫ gluingSnd R₂ adj x ↔
      F.map u ≫ x.iso.hom = S.iso.hom.app a ≫ G.map v := by
  rw [gluing_condition_iff, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Maps out of the image of `a` in `F ⊡ G` into a triple `x` are maps from `a` into
`gluingObj S adj₁ adj₂ adj x`. -/
def gluingHomEquiv (a : A) (x : F ⊡ G) :
    (((CatCommSqOver.toFunctorToCategoricalPullback F G A).obj S).obj a ⟶ x) ≃
      (a ⟶ gluingObj S adj₁ adj₂ adj x) where
  toFun φ := pullback.lift (adj₁.homEquiv _ _ φ.fst) (adj₂.homEquiv _ _ φ.snd)
    ((gluing_condition_iff' S adj₁ adj₂ adj x φ.fst φ.snd).2 φ.w)
  invFun ψ :=
    { fst := (adj₁.homEquiv _ _).symm (ψ ≫ pullback.fst _ _)
      snd := (adj₂.homEquiv _ _).symm (ψ ≫ pullback.snd _ _)
      w := (gluing_condition_iff S adj₁ adj₂ adj x _ _).1 (by
        rw [Category.assoc, Category.assoc, pullback.condition]) }
  left_inv φ := by
    refine CategoricalPullback.hom_ext ?_ ?_
    · dsimp only
      rw [pullback.lift_fst]
      exact (adj₁.homEquiv _ _).symm_apply_apply φ.fst
    · dsimp only
      rw [pullback.lift_snd]
      exact (adj₂.homEquiv _ _).symm_apply_apply φ.snd
  right_inv ψ := by
    refine pullback.hom_ext ?_ ?_
    · dsimp only
      rw [pullback.lift_fst]
      exact (adj₁.homEquiv _ _).apply_symm_apply _
    · dsimp only
      rw [pullback.lift_snd]
      exact (adj₂.homEquiv _ _).apply_symm_apply _

/-- `gluingHomEquiv` is natural in the object of `A`. -/
theorem gluingHomEquiv_naturality (a' a : A) (x : F ⊡ G) (f : a' ⟶ a)
    (g : ((CatCommSqOver.toFunctorToCategoricalPullback F G A).obj S).obj a ⟶ x) :
    gluingHomEquiv S adj₁ adj₂ adj a' x
        (((CatCommSqOver.toFunctorToCategoricalPullback F G A).obj S).map f ≫ g) =
      f ≫ gluingHomEquiv S adj₁ adj₂ adj a x g := by
  refine pullback.hom_ext ?_ ?_ <;> dsimp only [gluingHomEquiv, Equiv.coe_fn_mk] <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] <;>
    exact Adjunction.homEquiv_naturality_left _ _ _

/-- The functor `A ⥤ F ⊡ G` defined by a categorical commutative square whose legs are left
adjoints is a left adjoint, when `G` is one too and `A` has pullbacks. -/
def gluingAdjunction :
    (CatCommSqOver.toFunctorToCategoricalPullback F G A).obj S ⊣
      Adjunction.rightAdjointOfEquiv (gluingHomEquiv S adj₁ adj₂ adj)
        (gluingHomEquiv_naturality S adj₁ adj₂ adj) :=
  Adjunction.adjunctionOfEquivRight _ _

/-- The right adjoint of `gluingAdjunction` sends a triple `x` to `gluingObj S adj₁ adj₂ adj x`. -/
@[simp]
theorem gluingAdjunction_rightAdjoint_obj (x : F ⊡ G) :
    (Adjunction.rightAdjointOfEquiv (gluingHomEquiv S adj₁ adj₂ adj)
      (gluingHomEquiv_naturality S adj₁ adj₂ adj)).obj x = gluingObj S adj₁ adj₂ adj x :=
  rfl

/-- The first component of the counit is the counit of `S.fst ⊣ R₁` after the first
projection. -/
theorem gluingAdjunction_counit_app_fst (x : F ⊡ G) :
    ((gluingAdjunction S adj₁ adj₂ adj).counit.app x).fst =
      S.fst.map (pullback.fst _ _) ≫ adj₁.counit.app x.fst := by
  simp [gluingAdjunction, gluingHomEquiv, Adjunction.homEquiv_counit]
  rfl

/-- The second component of the counit is the counit of `S.snd ⊣ R₂` after the second
projection. -/
theorem gluingAdjunction_counit_app_snd (x : F ⊡ G) :
    ((gluingAdjunction S adj₁ adj₂ adj).counit.app x).snd =
      S.snd.map (pullback.snd _ _) ≫ adj₂.counit.app x.snd := by
  simp [gluingAdjunction, gluingHomEquiv, Adjunction.homEquiv_counit]
  rfl

/-- The unit followed by the first projection is the unit of `S.fst ⊣ R₁`. -/
theorem gluingAdjunction_unit_app_fst (a : A) :
    (gluingAdjunction S adj₁ adj₂ adj).unit.app a ≫ pullback.fst _ _ = adj₁.unit.app a := by
  simp only [gluingAdjunction, Adjunction.adjunctionOfEquivRight_unit_app, gluingHomEquiv,
    Equiv.coe_fn_mk]
  rw [pullback.lift_fst]
  exact adj₁.homEquiv_id a

/-- The unit followed by the second projection is the unit of `S.snd ⊣ R₂`. -/
theorem gluingAdjunction_unit_app_snd (a : A) :
    (gluingAdjunction S adj₁ adj₂ adj).unit.app a ≫ pullback.snd _ _ = adj₂.unit.app a := by
  simp only [gluingAdjunction, Adjunction.adjunctionOfEquivRight_unit_app, gluingHomEquiv,
    Equiv.coe_fn_mk]
  rw [pullback.lift_snd]
  exact adj₂.homEquiv_id a

/-- `S.snd` of the first map of the fibre product, followed by the counit of `S.snd ⊣ R₂`, is the
base change map `R₁ ⋙ S.snd ⟶ F ⋙ R` (the mate of `S.iso⁻¹`) followed by `R` of the structure
isomorphism of the triple. -/
theorem map_gluingFst_comp_counit (x : F ⊡ G) :
    S.snd.map (gluingFst S adj₁ adj₂ adj x) ≫ adj₂.counit.app _ =
      (mateEquiv adj₁ adj (TwoSquare.mk _ _ _ _ S.iso.inv)).natTrans.app x.fst ≫
        R.map x.iso.hom := by
  have h : S.snd.map (gluingFst S adj₁ adj₂ adj x) ≫ adj₂.counit.app _ =
      (adj₂.homEquiv _ _).symm (gluingFst S adj₁ adj₂ adj x) :=
    (adj₂.homEquiv_counit _ _ _).symm
  rw [h, gluingFst, Equiv.symm_apply_apply, ← Category.assoc, adj.homEquiv_naturality_right]
  refine congrArg (· ≫ R.map x.iso.hom) ?_
  simp [mateEquiv, Adjunction.homEquiv_unit]

/-- If `S.snd` preserves the fibre product `gluingObj`, the base change map `R₁ ⋙ S.snd ⟶ F ⋙ R`
is invertible at `x.fst` and the counit of `S.snd ⊣ R₂` is invertible at `R G x.snd`, then
`S.snd` carries the second projection out of `gluingObj` to an isomorphism. -/
theorem isIso_map_pullbackSnd_gluingObj (x : F ⊡ G)
    [PreservesLimit (cospan (gluingFst S adj₁ adj₂ adj x) (gluingSnd R₂ adj x)) S.snd]
    [IsIso ((mateEquiv adj₁ adj (TwoSquare.mk _ _ _ _ S.iso.inv)).natTrans.app x.fst)]
    [IsIso (adj₂.counit.app (R.obj (G.obj x.snd)))] :
    IsIso (S.snd.map (pullback.snd (gluingFst S adj₁ adj₂ adj x) (gluingSnd R₂ adj x))) := by
  have : IsIso (S.snd.map (gluingFst S adj₁ adj₂ adj x)) := by
    have h := map_gluingFst_comp_counit S adj₁ adj₂ adj x
    have : IsIso (S.snd.map (gluingFst S adj₁ adj₂ adj x) ≫ adj₂.counit.app _) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _ (adj₂.counit.app _)
  have := hasPullback_of_preservesPullback S.snd (gluingFst S adj₁ adj₂ adj x)
    (gluingSnd R₂ adj x)
  rw [← PreservesPullback.iso_hom_snd]
  infer_instance

/-- The gluing condition read on the components of the counit: `F` of the first component,
followed by the structure isomorphism of `x`, is the structure isomorphism of the image of the
fibre product followed by `G` of the second component. -/
theorem gluing_counit_w (x : F ⊡ G) :
    F.map (S.fst.map (pullback.fst (gluingFst S adj₁ adj₂ adj x) (gluingSnd R₂ adj x)) ≫
        adj₁.counit.app x.fst) ≫ x.iso.hom =
      S.iso.hom.app (gluingObj S adj₁ adj₂ adj x) ≫
        G.map (S.snd.map (pullback.snd (gluingFst S adj₁ adj₂ adj x) (gluingSnd R₂ adj x)) ≫
          adj₂.counit.app x.snd) := by
  have h := (gluing_condition_iff S adj₁ adj₂ adj x (pullback.fst _ _) (pullback.snd _ _)).1
    pullback.condition
  simpa only [Adjunction.homEquiv_counit] using h

/-- The counit of `gluingAdjunction` is invertible at `x` exactly when its two components, the
counits of `S.fst ⊣ R₁` and `S.snd ⊣ R₂` after the two projections, are. -/
theorem isIso_gluingAdjunction_counit_app_iff (x : F ⊡ G) :
    IsIso ((gluingAdjunction S adj₁ adj₂ adj).counit.app x) ↔
      IsIso (S.fst.map (pullback.fst (gluingFst S adj₁ adj₂ adj x) (gluingSnd R₂ adj x)) ≫
          adj₁.counit.app x.fst) ∧
        IsIso (S.snd.map (pullback.snd (gluingFst S adj₁ adj₂ adj x) (gluingSnd R₂ adj x)) ≫
          adj₂.counit.app x.snd) := by
  rw [CategoricalPullback.isIso_iff, gluingAdjunction_counit_app_fst,
    gluingAdjunction_counit_app_snd]
  exact Iff.rfl

/-- The unit of `gluingAdjunction` at `a`: the map into the fibre product given by the units of
`S.fst ⊣ R₁` and `S.snd ⊣ R₂`. -/
def gluingUnit (a : A) :
    a ⟶ gluingObj S adj₁ adj₂ adj
      (((CatCommSqOver.toFunctorToCategoricalPullback F G A).obj S).obj a) :=
  (gluingAdjunction S adj₁ adj₂ adj).unit.app a

/-- The first component of `gluingUnit` is the unit of `S.fst ⊣ R₁`. -/
@[reassoc (attr := simp)]
theorem gluingUnit_fst (a : A) :
    gluingUnit S adj₁ adj₂ adj a ≫ pullback.fst _ _ = adj₁.unit.app a :=
  gluingAdjunction_unit_app_fst S adj₁ adj₂ adj a

/-- The second component of `gluingUnit` is the unit of `S.snd ⊣ R₂`. -/
@[reassoc (attr := simp)]
theorem gluingUnit_snd (a : A) :
    gluingUnit S adj₁ adj₂ adj a ≫ pullback.snd _ _ = adj₂.unit.app a :=
  gluingAdjunction_unit_app_snd S adj₁ adj₂ adj a

/-- **Gluing along a categorical pullback.** If the unit of `gluingAdjunction`, computed by
`gluingUnit`, and the two components of its counit are invertible, the functor `A ⥤ F ⊡ G`
defined by `S` is an equivalence of categories. -/
theorem isEquivalence_toFunctorToCategoricalPullback_of_isIso
    (hunit : ∀ a, IsIso (gluingUnit S adj₁ adj₂ adj a))
    (hfst : ∀ x : F ⊡ G,
      IsIso (S.fst.map (pullback.fst (gluingFst S adj₁ adj₂ adj x) (gluingSnd R₂ adj x)) ≫
        adj₁.counit.app x.fst))
    (hsnd : ∀ x : F ⊡ G,
      IsIso (S.snd.map (pullback.snd (gluingFst S adj₁ adj₂ adj x) (gluingSnd R₂ adj x)) ≫
        adj₂.counit.app x.snd)) :
    ((CatCommSqOver.toFunctorToCategoricalPullback F G A).obj S).IsEquivalence := by
  have : ∀ a, IsIso ((gluingAdjunction S adj₁ adj₂ adj).unit.app a) := hunit
  have : ∀ x, IsIso ((gluingAdjunction S adj₁ adj₂ adj).counit.app x) := fun x ↦
    (isIso_gluingAdjunction_counit_app_iff S adj₁ adj₂ adj x).2 ⟨hfst x, hsnd x⟩
  exact (gluingAdjunction S adj₁ adj₂ adj).toEquivalence.isEquivalence_functor

end CategoryTheory.Limits.CategoricalPullback
