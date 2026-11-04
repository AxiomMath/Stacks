module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardFiber

/-!
# The morphism presheaves of a pushforward of a fibred category

Let `u : 𝒞 ⥤ 𝒟` be a continuous functor of sites and `p : 𝒮 ⥤ 𝒟` a fibred category. This file
proves condition (2) of Stacks 026F for the pushforward `u^p𝒮 ⥤ 𝒞`: the presheaves `Mor(x, y)` of
Stacks 02ZB on `𝒞/U` are sheaves.

Since the fibre of `u^p𝒮` over `U` is the fibre of `p` over `u U`, compatibly with pullbacks, the
presheaf `Mor(x, y)` on `𝒞/U` is the restriction along `𝒞/U ⥤ 𝒟/u(U)` of the presheaf
`Mor(x, y)` on `𝒟/u(U)`, and the restriction functor is continuous.

## Main results

* `CategoryTheory.StrictPullback.isContinuous_overPost`, the localisation `𝒞/U ⥤ 𝒟/u(U)` of a
  continuous functor of sites is continuous;
* `CategoryTheory.StrictPullback.pullbackFiberFibIso`, the comparison between the chosen pullbacks
  of `u^p𝒮` and those of `p`, and
  `CategoryTheory.StrictPullback.morPresheafFibIso`, the resulting identification of `Mor(x, y)` on
  `𝒞/U` with the restriction of `Mor(x, y)` on `𝒟/u(U)`;
* `CategoryTheory.StrictPullback.isMorSheaf_structureFunctor`, condition (2) of Stacks 026F for
  the pushforward.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]

namespace StrictPullback

/-- A continuous functor of sites in the sense of Stacks 00WU — one that is continuous and
commutes with the fibre products appearing in coverings — induces a continuous functor of the
localised sites `𝒞/U ⥤ 𝒟/u(U)`. -/
lemma isContinuous_overPost (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟)
    (u : 𝒞 ⥤ 𝒟) [u.IsContinuous J K] [HasPullbacks 𝒞] [PreservesLimitsOfShape WalkingCospan u]
    (U : 𝒞) : (Over.post (X := U) u).IsContinuous (J.over U) (K.over (u.obj U)) :=
  have : u.PreservesOneHypercovers.{max u₁ v₁} J K :=
    Functor.PreservesOneHypercovers.of_coverPreserving (CoverPreserving.of_isContinuous u J K)
  inferInstance

section Fibre

variable {u : 𝒞 ⥤ 𝒟} {p : 𝒮 ⥤ 𝒟}

/-- The `𝒞`-component of a morphism of `u^p𝒮` between two objects over `V` and lying over `𝟙 V`
is forced: it is the comparison `eqToHom` between the two identifications with `V`. -/
lemma base_eq_eqToHom {V : 𝒞} {X Y : StrictPullback u p} (hX : X.base = V) (hY : Y.base = V)
    (f : X ⟶ Y) (hf : (structureFunctor u p).IsHomLift (𝟙 V) f) :
    f.base = eqToHom hX ≫ eqToHom hY.symm := by
  subst hY
  have := hf
  have h : f.base = eqToHom hX ≫ 𝟙 Y.base ≫ eqToHom (rfl : Y.base = Y.base).symm :=
    IsHomLift.fac' (structureFunctor u p) (𝟙 Y.base) f
  simpa using h

/-- A morphism of the fibre of `p` over `u V`, read as a morphism of `u^p𝒮` between two objects
lying over `V`. Its `𝒞`-component is forced to be the comparison `eqToHom`, by
`StrictPullback.base_eq_eqToHom`. -/
def fiberHomMk {V : 𝒞} {X Y : StrictPullback u p} (hX : X.base = V) (hY : Y.base = V)
    (β : X.fib ⟶ Y.fib) (hβ : p.IsHomLift (𝟙 (u.obj V)) β) : X ⟶ Y :=
  ⟨eqToHom hX ≫ eqToHom hY.symm, β, by
    subst hY
    have := hβ
    rw [IsHomLift.fac' p (𝟙 (u.obj Y.base)) β]
    simp [Category.id_comp, eqToHom_map, eqToHom_refl, Category.comp_id, eqToHom_trans]⟩

/-- The `𝒞`-component of `StrictPullback.fiberHomMk` is the comparison `eqToHom` between the two
identifications of the bases with `V`. -/
@[simp] lemma fiberHomMk_base {V : 𝒞} {X Y : StrictPullback u p} (hX : X.base = V) (hY : Y.base = V)
    (β : X.fib ⟶ Y.fib) (hβ : p.IsHomLift (𝟙 (u.obj V)) β) :
    (fiberHomMk hX hY β hβ).base = eqToHom hX ≫ eqToHom hY.symm := rfl

/-- The `𝒮`-component of `StrictPullback.fiberHomMk hX hY β hβ` is `β`. -/
@[simp] lemma fiberHomMk_fib {V : 𝒞} {X Y : StrictPullback u p} (hX : X.base = V) (hY : Y.base = V)
    (β : X.fib ⟶ Y.fib) (hβ : p.IsHomLift (𝟙 (u.obj V)) β) :
    (fiberHomMk hX hY β hβ).fib = β := rfl

/-- `StrictPullback.fiberHomMk` lands in the fibre of `u^p𝒮` over `V`. -/
lemma isHomLift_fiberHomMk {V : 𝒞} {X Y : StrictPullback u p} (hX : X.base = V) (hY : Y.base = V)
    (β : X.fib ⟶ Y.fib) (hβ : p.IsHomLift (𝟙 (u.obj V)) β) :
    (structureFunctor u p).IsHomLift (𝟙 V) (fiberHomMk hX hY β hβ) :=
  IsHomLift.of_fac' _ _ _ hX hY (by simp)

/-- A composite of morphisms lying over `f₁` and `f₂` lies over any `f` equal to `f₁ ≫ f₂`. -/
private lemma isHomLift_comp_of_eq {R S T : 𝒟} {f : R ⟶ T} {f₁ : R ⟶ S} {f₂ : S ⟶ T}
    (e : f₁ ≫ f₂ = f) {a b c : 𝒮} {α : a ⟶ b} {β : b ⟶ c} (h₁ : p.IsHomLift f₁ α)
    (h₂ : p.IsHomLift f₂ β) : p.IsHomLift f (α ≫ β) := by
  subst e
  infer_instance

end Fibre

/-! ### Comparison of the chosen pullbacks

The fibre of `u^p𝒮` over `V` is the fibre of `p` over `u V`, but the chosen pullback of `x` along
`g : V ⟶ U` taken in `u^p𝒮` and the chosen pullback of the `𝒮`-component of `x` along `u g` taken
in `𝒮` are two independent choices. They are canonically isomorphic, since the `𝒮`-component of the
first is again a cartesian lift of `u g`; that comparison is what transports the presheaf
`Mor(x, y)` of `u^p𝒮` to the presheaf `Mor(x, y)` of `p`. -/

section MorPresheaf

-- The domain and codomain of the chosen cartesian lifts compared below are stated through
-- `Functor.pullbackFiber` and `StrictPullback.fiberFib`, so the instance arguments of
-- `IsHomLift` and `IsCartesian` are only found after unfolding those.
set_option backward.isDefEq.respectTransparency false

variable {u : 𝒞 ⥤ 𝒟} {p : 𝒮 ⥤ 𝒟} [p.IsFibered]

/-- The comparison isomorphism between the `𝒮`-component of the chosen `u^p𝒮`-pullback of `x`
along `g` and the chosen `p`-pullback of the `𝒮`-component of `x` along `u g`. This is
`CategoryTheory.StrictPullback.fiberFibPullbackIso` read in `𝒮` and in the direction the transport
of the morphism presheaf below uses, and it is the analogue, for the identification of `(u^p𝒮)_V`
with `𝒮_{u V}`, of `CategoryTheory.Functor.pullbackFiberιIso`. -/
noncomputable def pullbackFiberFibIso {U : 𝒞} (x : (structureFunctor u p).Fiber U) {V : 𝒞}
    (g : V ⟶ U) :
    (Functor.pullbackFiber (structureFunctor u p) x g).1.fib ≅
      (Functor.pullbackFiber p (fiberFib x) (u.map g)).1 :=
  (Functor.Fiber.fiberInclusion.mapIso (fiberFibPullbackIso x g)).symm

/-- `StrictPullback.pullbackFiberFibIso` is an isomorphism of the fibre of `p` over `u V`. -/
lemma isHomLift_pullbackFiberFibIso_hom {U : 𝒞} (x : (structureFunctor u p).Fiber U) {V : 𝒞}
    (g : V ⟶ U) : p.IsHomLift (𝟙 (u.obj V)) (pullbackFiberFibIso x g).hom :=
  (fiberFibPullbackIso x g).inv.2

/-- The inverse of `StrictPullback.pullbackFiberFibIso` also lies in the fibre over `u V`. -/
lemma isHomLift_pullbackFiberFibIso_inv {U : 𝒞} (x : (structureFunctor u p).Fiber U) {V : 𝒞}
    (g : V ⟶ U) : p.IsHomLift (𝟙 (u.obj V)) (pullbackFiberFibIso x g).inv :=
  (fiberFibPullbackIso x g).hom.2

/-- `StrictPullback.pullbackFiberFibIso` is compatible with the two chosen cartesian lifts it
compares. -/
@[reassoc]
lemma pullbackFiberFibIso_hom_fac {U : 𝒞} (x : (structureFunctor u p).Fiber U) {V : 𝒞}
    (g : V ⟶ U) :
    (pullbackFiberFibIso x g).hom ≫ Functor.IsPreFibered.pullbackMap (fiberFib x).2 (u.map g) =
      (Functor.IsPreFibered.pullbackMap x.2 g).fib :=
  fiberFibPullbackIso_inv_fac x g

/-- `CategoryTheory.Functor.pullbackFiberMap_fac` for the chosen `p`-pullbacks along the images
under `u` of the morphisms of `𝒞/U`, stated with those images spelled out. -/
lemma pullbackFiberMap_post_fac {U : 𝒞} (x' : p.Fiber (u.obj U)) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    Functor.pullbackFiberMap p x' ((Over.post u).map h) ≫
        Functor.IsPreFibered.pullbackMap x'.2 (u.map g₂.hom) =
      Functor.IsPreFibered.pullbackMap x'.2 (u.map g₁.hom) :=
  Functor.pullbackFiberMap_fac p x' ((Over.post u).map h)

/-- Conjugating by the comparison isomorphisms turns the restriction map of the chosen
`u^p𝒮`-pullbacks of `x` into the restriction map of the chosen `p`-pullbacks of its `𝒮`-component.
This is the naturality of `StrictPullback.pullbackFiberFibIso`. -/
lemma pullbackFiberMap_fib_pullbackFiberFibIso_hom {U : 𝒞} (x : (structureFunctor u p).Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    (Functor.pullbackFiberMap (structureFunctor u p) x h).fib ≫
        (pullbackFiberFibIso x g₂.hom).hom =
      (pullbackFiberFibIso x g₁.hom).hom ≫
        Functor.pullbackFiberMap p (fiberFib x) ((Over.post u).map h) := by
  have hl : p.IsHomLift (u.map h.left) _ := isHomLift_comp_of_eq (Category.comp_id _)
    (isHomLift_fib_of_isHomLift h.left _
      (Functor.pullbackFiberMap_isHomLift (structureFunctor u p) x h))
    (isHomLift_pullbackFiberFibIso_hom x g₂.hom)
  have hr : p.IsHomLift (u.map h.left) _ := isHomLift_comp_of_eq (Category.id_comp _)
    (isHomLift_pullbackFiberFibIso_hom x g₁.hom)
    (Functor.pullbackFiberMap_isHomLift p (fiberFib x) ((Over.post u).map h))
  refine Functor.IsStronglyCartesian.ext p (u.map g₂.hom)
    (Functor.IsPreFibered.pullbackMap (fiberFib x).2 (u.map g₂.hom)) (u.map h.left) ?_
  rw [Category.assoc, Category.assoc, pullbackFiberFibIso_hom_fac, pullbackFiberMap_post_fac,
    pullbackFiberFibIso_hom_fac, ← comp_fib, Functor.pullbackFiberMap_fac]

/-- `StrictPullback.pullbackFiberMap_fib_pullbackFiberFibIso_hom` with the comparison isomorphisms
inverted. -/
@[reassoc]
lemma pullbackFiberFibIso_inv_pullbackFiberMap_fib {U : 𝒞} (x : (structureFunctor u p).Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    (pullbackFiberFibIso x g₁.hom).inv ≫
        (Functor.pullbackFiberMap (structureFunctor u p) x h).fib =
      Functor.pullbackFiberMap p (fiberFib x) ((Over.post u).map h) ≫
        (pullbackFiberFibIso x g₂.hom).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← pullbackFiberMap_fib_pullbackFiberFibIso_hom x h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The identification of the fibre of `u^p𝒮` over `V` with the fibre of `p` over `u V`,
conjugated by the comparison isomorphisms, identifies the sections over `g` of the presheaf
`Mor(x, y)` of `u^p𝒮` with the sections over `u g` of the presheaf `Mor(x, y)` of `p`. This is the
analogue of `CategoryTheory.Functor.morSectionιEquiv`. -/
noncomputable def morSectionFibEquiv {U : 𝒞} (x y : (structureFunctor u p).Fiber U) (g : Over U) :
    (Functor.pullbackFiber (structureFunctor u p) x g.hom ⟶
        Functor.pullbackFiber (structureFunctor u p) y g.hom) ≃
      (Functor.pullbackFiber p (fiberFib x) (u.map g.hom) ⟶
        Functor.pullbackFiber p (fiberFib y) (u.map g.hom)) where
  toFun m := ⟨(pullbackFiberFibIso x g.hom).inv ≫
      (Functor.Fiber.fiberInclusion.map m).fib ≫ (pullbackFiberFibIso y g.hom).hom,
    Functor.isHomLift_id_comp p _ _ (isHomLift_pullbackFiberFibIso_inv x g.hom)
      (Functor.isHomLift_id_comp p _ _ (isHomLift_id_fib _ m.2)
        (isHomLift_pullbackFiberFibIso_hom y g.hom))⟩
  invFun n := ⟨fiberHomMk (Functor.pullbackFiber (structureFunctor u p) x g.hom).2
      (Functor.pullbackFiber (structureFunctor u p) y g.hom).2
      ((pullbackFiberFibIso x g.hom).hom ≫ Functor.Fiber.fiberInclusion.map n ≫
        (pullbackFiberFibIso y g.hom).inv)
      (Functor.isHomLift_id_comp p _ _ (isHomLift_pullbackFiberFibIso_hom x g.hom)
        (Functor.isHomLift_id_comp p _ _ n.2 (isHomLift_pullbackFiberFibIso_inv y g.hom))),
    isHomLift_fiberHomMk _ _ _ _⟩
  left_inv m := by
    apply Functor.Fiber.hom_ext
    refine Hom.ext ((base_eq_eqToHom
      (Functor.pullbackFiber (structureFunctor u p) x g.hom).2
      (Functor.pullbackFiber (structureFunctor u p) y g.hom).2 _ m.2).symm) ?_
    simp [Functor.Fiber.fiberInclusion]
  right_inv n := by
    apply Functor.Fiber.hom_ext
    simp [Functor.Fiber.fiberInclusion]

/-- The presheaf `Mor(x, y)` on `𝒞/U` of the pushforward `u^p𝒮` is the presheaf `Mor(x, y)` on
`𝒟/u(U)` of `p` restricted along `Over.post u : 𝒞/U ⥤ 𝒟/u(U)`, up to the universe lift forced by
the fact that a morphism of `u^p𝒮` is a pair. This is the analogue of
`CategoryTheory.Functor.morPresheafιIso`. -/
noncomputable def morPresheafFibIso {U : 𝒞} (x y : (structureFunctor u p).Fiber U) :
    Functor.morPresheaf (structureFunctor u p) x y ≅
      (Over.post (X := U) u).op ⋙
        Functor.morPresheaf p (fiberFib x) (fiberFib y) ⋙ uliftFunctor.{v₁} :=
  NatIso.ofComponents
    (fun g => Equiv.toIso ((morSectionFibEquiv x y g.unop).trans Equiv.ulift.symm)) <| by
      rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
      ext m
      change ULift.up (morSectionFibEquiv x y g₁
            (Functor.morRestrict (structureFunctor u p) x y h m)) =
        ULift.up (Functor.morRestrict p (fiberFib x) (fiberFib y) ((Over.post (X := U) u).map h)
          (morSectionFibEquiv x y g₂ m))
      congr 1
      refine Functor.morRestrict_uniq p (fiberFib x) (fiberFib y) ((Over.post (X := U) u).map h)
        (morSectionFibEquiv x y g₂ m) _ ?_
      change ((pullbackFiberFibIso x g₁.hom).inv ≫
            (Functor.Fiber.fiberInclusion.map
              (Functor.morRestrict (structureFunctor u p) x y h m)).fib ≫
            (pullbackFiberFibIso y g₁.hom).hom) ≫
          Functor.IsPreFibered.pullbackMap (fiberFib y).2 (u.map g₁.hom) =
        Functor.pullbackFiberMap p (fiberFib x) ((Over.post (X := U) u).map h) ≫
          ((pullbackFiberFibIso x g₂.hom).inv ≫
            (Functor.Fiber.fiberInclusion.map m).fib ≫
            (pullbackFiberFibIso y g₂.hom).hom) ≫
          Functor.IsPreFibered.pullbackMap (fiberFib y).2 (u.map g₂.hom)
      simp only [Category.assoc]
      rw [pullbackFiberFibIso_hom_fac, ← comp_fib, Functor.morRestrict_fac, comp_fib, comp_fib,
        ← pullbackFiberFibIso_hom_fac y g₂.hom,
        pullbackFiberFibIso_inv_pullbackFiberMap_fib_assoc]

end MorPresheaf

/-- **Stacks 026F (2)** for the pushforward: the presheaf `Mor(x, y)` on `𝒞/U` of the pushforward
of a stack along a continuous functor of sites is a sheaf. -/
theorem isMorSheaf_structureFunctor (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟)
    (u : 𝒞 ⥤ 𝒟) [u.IsContinuous J K] [HasPullbacks 𝒞] [PreservesLimitsOfShape WalkingCospan u]
    (p : 𝒮 ⥤ 𝒟) [p.IsFibered]
    (hp : ∀ (Y : 𝒟) (a b : p.Fiber Y), Functor.IsMorSheaf p K Y a b)
    (U : 𝒞) (x y : (structureFunctor u p).Fiber U) :
    Functor.IsMorSheaf (structureFunctor u p) J U x y := by
  have := isContinuous_overPost J K u U
  have h0 : Presieve.IsSheaf (K.over (u.obj U)) (Functor.morPresheaf p (fiberFib x) (fiberFib y)) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (hp (u.obj U) (fiberFib x) (fiberFib y))
  have h1 : Presheaf.IsSheaf (K.over (u.obj U))
      (Functor.morPresheaf p (fiberFib x) (fiberFib y) ⋙ uliftFunctor.{v₁}) :=
    (isSheaf_iff_isSheaf_of_type _ _).2 (Presieve.isSheaf_comp_uliftFunctor _ h0)
  exact (Presheaf.isSheaf_of_iso_iff (morPresheafFibIso x y)).2
    ((Over.post (X := U) u).op_comp_isSheaf_of_isSheaf (J.over U) (K.over (u.obj U)) _ h1)

end StrictPullback

end CategoryTheory
