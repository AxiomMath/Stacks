module

public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Fibres
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids

/-!
# The presheaf on `𝒞/U` of isomorphism classes of pairs `(x, φ : f^* y ⟶ F(x))`

Let `𝒞` be a category, let `𝒳` and `𝒴` be categories fibred in groupoids over `𝒞`, let
`F : 𝒳 ⥤ 𝒴` be a 1-morphism over `𝒞`, fix a choice of pullbacks `c` for `𝒴`, an object `U` of `𝒞`
and an object `y` of the fibre `𝒴_U`. The criterion of Stacks 02Y9 for `F` to be representable
quantifies over the presheaf on the slice `𝒞/U`

`(f : V ⟶ U) ↦ {(x, φ) | x an object of 𝒳_V, φ : f^* y ⟶ F(x) a morphism of 𝒴_V}/≅`,

whose transition maps use the chosen pullbacks of `𝒴`. This file constructs that presheaf as a
functor `(𝒞/U)ᵒᵖ ⥤ Type _`, the presheaf of isomorphism classes of the fibres of the first
projection `π₁ : (𝒞/U) ×_𝒴 𝒳 ⥤ 𝒞/U`, and proves that every element is the class of a pair, the
criterion for two pairs to have the same class, and the formula computing a restriction map.

## Main definitions

* `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor`: the 1-morphism `𝒞/U ⥤ 𝒴` over `𝒞` given
  by `(f : V ⟶ U) ↦ f^* y`, for a choice of pullbacks and an object `y` of `𝒴_U`.
* `CategoryTheory.PairIsoClass.projection`: the first projection `(𝒞/U) ×_𝒴 𝒳 ⥤ 𝒞/U` of the
  2-fibre product taken along `sliceFunctor`, whose fibre over `f` is the category of pairs.
* `CategoryTheory.PairIsoClass.presheaf`: the presheaf of the criterion.
* `CategoryTheory.PairIsoClass.mk`: the isomorphism class of a pair `(x, φ)`.

## Main results

* `CategoryTheory.PairIsoClass.objEquiv`: the objects of the fibre of `projection` over `f` are the
  pairs `(x, φ)`.
* `CategoryTheory.PairIsoClass.mk_surjective`: every element of the presheaf at `f` is the class of
  a pair.
* `CategoryTheory.PairIsoClass.mk_eq_mk_iff`: two pairs have the same class exactly when there is
  an isomorphism `x ≅ x'` in the fibre `𝒳_V` carrying `φ` to `φ'`.
* `CategoryTheory.PairIsoClass.presheaf_map_mk`: the restriction of the class of `(x, φ)` along
  `h : f' ⟶ f` is the class of any pair `(x', φ')` admitting a morphism `χ : x' ⟶ x` over `h.left`
  compatible with the comparison map `(f')^* y ⟶ f^* y` of the chosen pullbacks.
* `CategoryTheory.PairIsoClass.exists_pair_of_hom`: such a pair `(x', φ')` and such a `χ` always
  exist.
-/

@[expose] public section

-- The fibre of a functor, the projections of the 2-fibre product and `sliceFunctor` are plain
-- `def`s, so goals mentioning an object of a fibre, its underlying object of the 2-fibre product,
-- or the value `f^* y` of `sliceFunctor` are not type-correct at `implicit` transparency.
set_option backward.isDefEq.respectTransparency false

open Opposite

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

namespace Functor.ChoiceOfPullbacks

attribute [local implicit_reducible] Functor.Fiber

variable {p𝒴 : 𝒴 ⥤ 𝒞} (c : p𝒴.ChoiceOfPullbacks) {U : 𝒞} (y : p𝒴.Fiber U)

/-- The 1-morphism `𝒞/U ⥤ 𝒴` over `𝒞` attached by a choice of pullbacks to an object `y` of the
fibre `𝒴_U`, namely `(f : V ⟶ U) ↦ f^* y` on objects. A morphism `h : f' ⟶ f` of `𝒞/U` is sent to
the unique morphism `(f')^* y ⟶ f^* y` lying over `h.left` through which the chosen cartesian lift
`(f')^* y ⟶ y` factors, which exists because the chosen lift `f^* y ⟶ y` is strongly cartesian and
`f'.hom = h.left ≫ f.hom`.

Under the 2-Yoneda lemma of Stacks 004B this is the 1-morphism corresponding to `y`. -/
noncomputable def sliceFunctor : Over U ⥤ 𝒴 where
  obj f := (c.obj f.hom y).1
  map {f' f} h :=
    IsStronglyCartesian.map p𝒴 f.hom (c.map f.hom y)
      (show f'.hom = h.left ≫ f.hom from (Over.w h).symm) (c.map f'.hom y)
  map_id f := by
    simp only [Over.id_left]
    exact IsStronglyCartesian.map_self p𝒴 f.hom (c.map f.hom y)
  map_comp {f'' f' f} h' h :=
    (IsStronglyCartesian.map_comp_map p𝒴 f.hom (c.map f.hom y)
      (show f'.hom = h.left ≫ f.hom from (Over.w h).symm)
      (show f''.hom = h'.left ≫ f'.hom from (Over.w h').symm)
      (c.map f'.hom y) (c.map f''.hom y)).symm

/-- The value of `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` at an object `f : V ⟶ U`
of `𝒞/U` is the chosen pullback `f^* y`. -/
@[simp]
lemma sliceFunctor_obj (f : Over U) : (c.sliceFunctor y).obj f = (c.obj f.hom y).1 := rfl

/-- The image of a morphism of `𝒞/U` under
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` lies over its underlying morphism of
`𝒞`. -/
instance sliceFunctor_map_isHomLift {f' f : Over U} (h : f' ⟶ f) :
    p𝒴.IsHomLift h.left ((c.sliceFunctor y).map h) :=
  IsStronglyCartesian.map_isHomLift p𝒴 f.hom (c.map f.hom y)
    (show f'.hom = h.left ≫ f.hom from (Over.w h).symm) (c.map f'.hom y)

/-- The defining factorisation of the transition map of
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor`: it is compatible with the chosen
cartesian lifts. -/
@[reassoc (attr := simp)]
lemma sliceFunctor_map_fac {f' f : Over U} (h : f' ⟶ f) :
    (c.sliceFunctor y).map h ≫ c.map f.hom y = c.map f'.hom y :=
  IsStronglyCartesian.fac p𝒴 f.hom (c.map f.hom y)
    (show f'.hom = h.left ≫ f.hom from (Over.w h).symm) (c.map f'.hom y)

/-- That factorisation determines the transition map of
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor`. -/
lemma sliceFunctor_map_uniq {f' f : Over U} (h : f' ⟶ f)
    (ψ : (c.obj f'.hom y).1 ⟶ (c.obj f.hom y).1) (hψ : p𝒴.IsHomLift h.left ψ)
    (hfac : ψ ≫ c.map f.hom y = c.map f'.hom y) : ψ = (c.sliceFunctor y).map h :=
  have := hψ
  IsStronglyCartesian.map_uniq p𝒴 f.hom (c.map f.hom y)
    (show f'.hom = h.left ≫ f.hom from (Over.w h).symm) (c.map f'.hom y) ψ hfac

/-- `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` commutes strictly with the projections
to `𝒞`, i.e. it is a 1-morphism over `𝒞`. -/
lemma sliceFunctor_comp : c.sliceFunctor y ⋙ p𝒴 = Over.forget U := by
  refine CategoryTheory.Functor.ext (fun f => (c.obj f.hom y).2) ?_
  intro f' f h
  change p𝒴.map ((c.sliceFunctor y).map h) = _
  rw [IsHomLift.fac' p𝒴 h.left ((c.sliceFunctor y).map h)]
  rfl

/-- For Mathlib's canonical choice of pullbacks,
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` is the functor
`CategoryTheory.Functor.FiberedMor.OfFiberObj.pullbackFunctor` of the 2-Yoneda lemma for fibred
categories. -/
lemma sliceFunctor_chosenPullbacks (p : 𝒴 ⥤ 𝒞) [p.IsFibered] {U : 𝒞} (y : p.Fiber U) :
    (chosenPullbacks p).sliceFunctor y = FiberedMor.OfFiberObj.pullbackFunctor p U y.2 := rfl

end Functor.ChoiceOfPullbacks

namespace PairIsoClass

open _root_.CategoryTheory.Functor _root_.CategoryTheory.Functor.ChoiceOfPullbacks
  _root_.CategoryTheory.TwoFibreProductOver

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  TwoFibreProductOver.fst Functor.ChoiceOfPullbacks.sliceFunctor

/-- The first projection `π₁ : (𝒞/U) ×_𝒴 𝒳 ⥤ 𝒞/U` of the 2-fibre product of the slice `𝒞/U` and
`𝒳` over `𝒴`, taken along the 1-morphism `(f : V ⟶ U) ↦ f^* y` of
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor`.

By Stacks 02Y5 its fibre over `f : V ⟶ U` is the category of pairs `(x, φ)` with `x` an object of
`𝒳_V` and `φ : f^* y ⟶ F(x)` a morphism of `𝒴_V`, and by Stacks 02Y6 it is a category fibred in
groupoids over `𝒞/U`. -/
noncomputable abbrev projection (p𝒳 : 𝒳 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) {p𝒴 : 𝒴 ⥤ 𝒞}
    (c : p𝒴.ChoiceOfPullbacks) {U : 𝒞} (y : p𝒴.Fiber U) :
    TwoFibreProductOver (Over.forget U) p𝒳 p𝒴 (c.sliceFunctor y) F ⥤ Over U :=
  TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 (c.sliceFunctor y) F

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} (F : 𝒳 ⥤ 𝒴) (c : p𝒴.ChoiceOfPullbacks) {U : 𝒞}
  (y : p𝒴.Fiber U) (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
  (hF : F ⋙ p𝒴 = p𝒳)

include h𝒳 h𝒴 hF in
/-- **Stacks 02Y6** for the 2-fibre product taken along `f ↦ f^* y`: the projection to `𝒞/U` is a
category fibred in groupoids. -/
lemma isFiberedInGroupoids : (projection p𝒳 F c y).IsFiberedInGroupoids :=
  TwoFibreProductOver.fst_isFiberedInGroupoids U p𝒳 p𝒴 F (c.sliceFunctor y) h𝒳 h𝒴 hF
    (c.sliceFunctor_comp y)

include h𝒳 h𝒴 hF in
/-- The projection to `𝒞/U` is a fibred category. -/
lemma isFibered : (projection p𝒳 F c y).IsFibered :=
  (isFiberedInGroupoids F c y h𝒳 h𝒴 hF).isFibered

include h𝒳 h𝒴 hF in
/-- The presheaf on the slice `𝒞/U` of Stacks 02Y9 (2):

`(f : V ⟶ U) ↦ {(x, φ) | x an object of 𝒳_V, φ : f^* y ⟶ F(x) a morphism of 𝒴_V}/≅`.

It is the presheaf of isomorphism classes of the fibres of
`CategoryTheory.PairIsoClass.projection`, whose fibre over `f` is by Stacks 02Y5 the category of
those pairs. A restriction map along `h : f' ⟶ f` sends the class of `(x, φ)` to the class of a
pullback of `x` along `h`, compared with the transition map `(f')^* y ⟶ f^* y` of the chosen
pullbacks. -/
noncomputable def presheaf : (Over U)ᵒᵖ ⥤ Type (max u₁ v₁ u₂ v₃) :=
  have := isFibered F c y h𝒳 h𝒴 hF
  (projection p𝒳 F c y).isoClassPresheaf

/-- **Stacks 02Y5 (1)**: the objects of the fibre of
`CategoryTheory.PairIsoClass.projection` over `f : V ⟶ U` are the pairs `(x, φ)` consisting of an
object `x` of `𝒳_V` and a morphism `φ : f^* y ⟶ F(x)` of `𝒴_V`. -/
noncomputable def objEquiv (f : Over U) :
    (projection p𝒳 F c y).Fiber f ≃
      Σ x : p𝒳.Fiber f.left, {φ : (c.obj f.hom y).1 ⟶ F.obj x.1 // p𝒴.IsHomLift (𝟙 f.left) φ} :=
  TwoFibreProductOver.FstFiber.objEquiv h𝒴

section

variable {f : Over U} (x : p𝒳.Fiber f.left) (φ : (c.obj f.hom y).1 ⟶ F.obj x.1)
  (hφ : p𝒴.IsHomLift (𝟙 f.left) φ)

/-- The `𝒞/U`-component of the object of the fibre attached to a pair is `f`. -/
lemma objEquiv_symm_x : ((objEquiv F c y h𝒴 f).symm ⟨x, φ, hφ⟩).1.x = f := rfl

/-- The `𝒳`-component of the object of the fibre attached to a pair is `x`. -/
lemma objEquiv_symm_y : ((objEquiv F c y h𝒴 f).symm ⟨x, φ, hφ⟩).1.y = x.1 := rfl

/-- The comparison isomorphism of the object of the fibre attached to a pair is `φ`. -/
lemma objEquiv_symm_iso_hom : ((objEquiv F c y h𝒴 f).symm ⟨x, φ, hφ⟩).1.iso.hom = φ := rfl

/-- The comparison isomorphism `φ` of Stacks 02Y5, for the object of the fibre attached to a pair
`(x, φ)`, is `φ` itself. -/
@[simp]
lemma phiIso_objEquiv_symm :
    (FstFiber.phiIso ((objEquiv F c y h𝒴 f).symm ⟨x, φ, hφ⟩)).hom = φ := by
  have h : (FstFiber.phiIso ((objEquiv F c y h𝒴 f).symm ⟨x, φ, hφ⟩)).hom
      = 𝟙 ((c.obj f.hom y).1) ≫ φ := rfl
  rw [h, Category.id_comp]

/-- The isomorphism class of the pair `(x, φ)`, an element of the presheaf of Stacks 02Y9 (2) at
`f : V ⟶ U`. -/
noncomputable def mk : (presheaf F c y h𝒳 h𝒴 hF).obj (op f) :=
  isoClassMk (projection p𝒳 F c y) ((objEquiv F c y h𝒴 f).symm ⟨x, φ, hφ⟩)

end

/-- Every element of the presheaf of Stacks 02Y9 (2) at `f : V ⟶ U` is the class of a pair. -/
lemma mk_surjective {f : Over U} (t : (presheaf F c y h𝒳 h𝒴 hF).obj (op f)) :
    ∃ (x : p𝒳.Fiber f.left) (φ : (c.obj f.hom y).1 ⟶ F.obj x.1)
      (hφ : p𝒴.IsHomLift (𝟙 f.left) φ), mk F c y h𝒳 h𝒴 hF x φ hφ = t := by
  obtain ⟨A, hA⟩ := isoClassMk_surjective (p := projection p𝒳 F c y) (U := f) t
  refine ⟨(objEquiv F c y h𝒴 f A).1, (objEquiv F c y h𝒴 f A).2.1,
    (objEquiv F c y h𝒴 f A).2.2, ?_⟩
  rw [← hA]
  exact congrArg (isoClassMk (projection p𝒳 F c y))
    (Equiv.symm_apply_apply (objEquiv F c y h𝒴 f) A)

/-- Two pairs over `f : V ⟶ U` have the same isomorphism class exactly when there is an
isomorphism `ψ : x ≅ x'` in the fibre `𝒳_V` with `F(ψ) ∘ φ = φ'`. -/
lemma mk_eq_mk_iff {f : Over U} (x x' : p𝒳.Fiber f.left)
    (φ : (c.obj f.hom y).1 ⟶ F.obj x.1) (hφ : p𝒴.IsHomLift (𝟙 f.left) φ)
    (φ' : (c.obj f.hom y).1 ⟶ F.obj x'.1) (hφ' : p𝒴.IsHomLift (𝟙 f.left) φ') :
    mk F c y h𝒳 h𝒴 hF x φ hφ = mk F c y h𝒳 h𝒴 hF x' φ' hφ' ↔
      ∃ ψ : x ≅ x', φ ≫ F.map (Fiber.fiberInclusion.map ψ.hom) = φ' := by
  have key : ∀ {P Q : (projection p𝒳 F c y).Fiber f} (u : P ⟶ Q) (v : Q ⟶ P),
      (FstFiber.homEquiv P Q u).1 ≫ (FstFiber.homEquiv Q P v).1 = 𝟙 P.1.y → u ≫ v = 𝟙 P := by
    intro P Q u v h
    refine (FstFiber.homEquiv P P).injective (Subtype.ext ?_)
    rw [FstFiber.homEquiv_comp, h, FstFiber.homEquiv_id]
  constructor
  · intro hEq
    obtain ⟨ι⟩ := exists_iso_of_isoClassMk_eq hEq
    have := (FstFiber.homEquiv _ _ ι.hom).2.1
    have := (FstFiber.homEquiv _ _ ι.inv).2.1
    have hcomp := congrArg Subtype.val (congrArg (FstFiber.homEquiv _ _) ι.hom_inv_id)
    have hcomp' := congrArg Subtype.val (congrArg (FstFiber.homEquiv _ _) ι.inv_hom_id)
    rw [FstFiber.homEquiv_comp, FstFiber.homEquiv_id] at hcomp hcomp'
    refine ⟨⟨Fiber.homMk p𝒳 f.left (FstFiber.homEquiv _ _ ι.hom).1,
      Fiber.homMk p𝒳 f.left (FstFiber.homEquiv _ _ ι.inv).1,
      Fiber.hom_ext hcomp, Fiber.hom_ext hcomp'⟩, ?_⟩
    simpa using (Iso.eq_inv_comp _).mp (FstFiber.homEquiv _ _ ι.hom).2.2
  · rintro ⟨ψ, hψ⟩
    have e1 : Fiber.fiberInclusion.map ψ.hom ≫ Fiber.fiberInclusion.map ψ.inv = 𝟙 x.1 :=
      congrArg Subtype.val ψ.hom_inv_id
    have e2 : Fiber.fiberInclusion.map ψ.inv ≫ Fiber.fiberInclusion.map ψ.hom = 𝟙 x'.1 :=
      congrArg Subtype.val ψ.inv_hom_id
    have hψ' : φ' ≫ F.map (Fiber.fiberInclusion.map ψ.inv) = φ := by
      rw [← hψ, Category.assoc, ← F.map_comp, e1, F.map_id, Category.comp_id]
    have hw : ∀ {x x' : p𝒳.Fiber f.left} {φ : (c.obj f.hom y).1 ⟶ F.obj x.1}
        {φ' : (c.obj f.hom y).1 ⟶ F.obj x'.1} (hφ : p𝒴.IsHomLift (𝟙 f.left) φ)
        (hφ' : p𝒴.IsHomLift (𝟙 f.left) φ') (g : x.1 ⟶ x'.1), φ ≫ F.map g = φ' →
        F.map g = (FstFiber.phiIso ((objEquiv F c y h𝒴 f).symm ⟨x, φ, hφ⟩)).inv
          ≫ (FstFiber.phiIso ((objEquiv F c y h𝒴 f).symm ⟨x', φ', hφ'⟩)).hom :=
      fun _ _ _ h => (Iso.eq_inv_comp _).mpr (by simpa using h)
    refine isoClassMk_eq_of_iso ⟨(FstFiber.homEquiv _ _).symm ⟨_, ψ.hom.2, hw hφ hφ' _ hψ⟩,
      (FstFiber.homEquiv _ _).symm ⟨_, ψ.inv.2, hw hφ' hφ _ hψ'⟩, key _ _ ?_, key _ _ ?_⟩ <;>
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exacts [e1, e2]

/-- The restriction along `h : f' ⟶ f` of the class of a pair `(x, φ)` is the class of any pair
`(x', φ')` over `f'` admitting a morphism `χ : x' ⟶ x` of `𝒳` over `h.left` which makes the square
with sides `(f')^* y ⟶ f^* y ⟶ F(x)` and `(f')^* y ⟶ F(x') ⟶ F(x)` commute, the map
`(f')^* y ⟶ f^* y` being the transition map of the chosen pullbacks. -/
lemma presheaf_map_mk {f' f : Over U} (h : f' ⟶ f) (x : p𝒳.Fiber f.left)
    (φ : (c.obj f.hom y).1 ⟶ F.obj x.1) (hφ : p𝒴.IsHomLift (𝟙 f.left) φ)
    (x' : p𝒳.Fiber f'.left) (φ' : (c.obj f'.hom y).1 ⟶ F.obj x'.1)
    (hφ' : p𝒴.IsHomLift (𝟙 f'.left) φ') (χ : x'.1 ⟶ x.1) (hχ : p𝒳.IsHomLift h.left χ)
    (hsq : (c.sliceFunctor y).map h ≫ φ = φ' ≫ F.map χ) :
    (presheaf F c y h𝒳 h𝒴 hF).map h.op (mk F c y h𝒳 h𝒴 hF x φ hφ)
      = mk F c y h𝒳 h𝒴 hF x' φ' hφ' := by
  have hfib := isFiberedInGroupoids F c y h𝒳 h𝒴 hF
  have := hfib.isFibered
  have := hχ
  let u : ((objEquiv F c y h𝒴 f').symm ⟨x', φ', hφ'⟩).1 ⟶
      ((objEquiv F c y h𝒴 f).symm ⟨x, φ, hφ⟩).1 :=
    TwoFibreProductOver.Hom.mk' h χ (by rw [IsHomLift.fac' p𝒳 h.left χ]; simp) hsq
  have hu : (projection p𝒳 F c y).IsHomLift h u :=
    IsHomLift.of_fac' (projection p𝒳 F c y) h u rfl rfl (by simp [u])
  have : (projection p𝒳 F c y).IsStronglyCartesian h u := hfib.isStronglyCartesian_homLift h u
  exact (isoClassMk_eq_pullbackFiber_of_isCartesian h _ _ u hu inferInstance).symm

include h𝒳 h𝒴 hF in
/-- Given a pair `(x, φ)` over `f` and `h : f' ⟶ f`, there are a pair `(x', φ')` over `f'` and a
morphism `χ : x' ⟶ x` of `𝒳` over `h.left` such that the composite `(f')^* y ⟶ f^* y ⟶ F(x)`
equals `(f')^* y ⟶ F(x') ⟶ F(x)`. -/
lemma exists_pair_of_hom {f' f : Over U} (h : f' ⟶ f) (x : p𝒳.Fiber f.left)
    (φ : (c.obj f.hom y).1 ⟶ F.obj x.1) (hφ : p𝒴.IsHomLift (𝟙 f.left) φ) :
    ∃ (x' : p𝒳.Fiber f'.left) (φ' : (c.obj f'.hom y).1 ⟶ F.obj x'.1)
      (_ : p𝒴.IsHomLift (𝟙 f'.left) φ') (χ : x'.1 ⟶ x.1) (_ : p𝒳.IsHomLift h.left χ),
      (c.sliceFunctor y).map h ≫ φ = φ' ≫ F.map χ := by
  obtain ⟨x'₀, χ, hχ⟩ := h𝒳.exists_lift h.left x.1 x.2
  have := hχ
  have hFχ : p𝒴.IsHomLift h.left (F.map χ) := Functor.isHomLift_map_of_comp_eq hF h.left χ
  have : p𝒴.IsStronglyCartesian h.left (F.map χ) := h𝒴.isStronglyCartesian_homLift h.left (F.map χ)
  have := hφ
  have hcomp : p𝒴.IsHomLift h.left ((c.sliceFunctor y).map h ≫ φ) :=
    IsHomLift.comp_lift_id_right p𝒴 h.left ((c.sliceFunctor y).map h) φ
  refine ⟨⟨x'₀, IsHomLift.domain_eq p𝒳 h.left χ⟩,
    IsStronglyCartesian.map p𝒴 h.left (F.map χ) (Category.id_comp h.left).symm
      ((c.sliceFunctor y).map h ≫ φ), ?_, χ, hχ, ?_⟩
  · exact IsStronglyCartesian.map_isHomLift p𝒴 h.left (F.map χ) (Category.id_comp h.left).symm
      ((c.sliceFunctor y).map h ≫ φ)
  · exact (IsStronglyCartesian.fac p𝒴 h.left (F.map χ) (Category.id_comp h.left).symm
      ((c.sliceFunctor y).map h ≫ φ)).symm

end PairIsoClass

end CategoryTheory
