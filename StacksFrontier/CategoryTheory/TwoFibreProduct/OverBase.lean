module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# The (2,1)-category of categories over `𝒞` has 2-fibre products (Stacks 0040)

In the 2-category `Cat/𝒞` of categories over a fixed base `𝒞` (Definition 003Y) an object is a
functor `p𝒳 : 𝒳 ⥤ 𝒞`, a 1-morphism `(𝒳, p𝒳) ⟶ (𝒮, p𝒮)` is a functor `F : 𝒳 ⥤ 𝒮` with
`F ⋙ p𝒮 = p𝒳`, and a 2-morphism is a natural transformation each of whose components is
*vertical*, i.e. lies over an identity of `𝒞`; verticality is spelled `p𝒮.IsHomLift (𝟙 U) _`.

The 2-fibre product itself is `CategoryTheory.TwoFibreProductOver`: its objects are the quadruples
`(U, x, y, φ)` of Stacks 0040, with `x` and `y` over `U` and `φ : F x ≅ G y` vertical over `U`, and
its morphisms are the pairs `(a, b)` lying over one common morphism of `𝒞` and making the
comparison square commute. Its cone — the two forgetful functors `fst`, `snd`, both strictly over
`𝒞`, and the vertical 2-cell `psiIso` filling the square — is proved with the construction.

This file adds the universal property, over `𝒞` throughout. A test cone consists of a category
`(W, pW)` over `𝒞`, 1-morphisms `H`, `K` over `𝒞` and an isomorphism `t : H ⋙ F ≅ K ⋙ G` *of
1-morphisms over `𝒞`*, i.e. one with vertical components; `lift` is the mediating 1-morphism
`w ↦ (pW w, H w, K w, t w)`, `lift_comp_structureFunctor` says it is a 1-morphism over `𝒞`,
`liftCompFst` and `liftCompSnd` are the comparison 2-isomorphisms and are vertical, and
`lift_whiskerRight_psi` is the compatibility of the factorisation with `t`. Uniqueness is
`liftIso` — any other factorisation is 2-isomorphic over `𝒞` to `lift` — together with
`natTrans_ext`, which says a 2-morphism into the 2-fibre product is determined by its two
projections.

Nothing here reduces to the absolute 2-fibre product of plain categories, Mathlib's
`Limits.CategoricalPullback` (Stacks 003R): Stacks 0H2D exhibits a cospan for which the absolute
and the relative construction are inequivalent, the difference being exactly that the comparison
isomorphism is arbitrary in the first and vertical in the second.
-/

/-! # Stacks 0040: 2-fibre products of categories over a base

For a cospan `F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮` of categories over `𝒞`, the categorical pullback
`𝒳 ×_𝒮 𝒴` is a 2-fibre product in the (2,1)-category of categories over `𝒞`: any test datum
`(W, X : W ⥤ 𝒳, Y : W ⥤ 𝒴, t : X ⋙ F ≅ Y ⋙ G)` factors through it via a mediating functor,
and more strongly `(W ⥤ 𝒳 ×_𝒮 𝒴) ≌ CatCommSqOver F G W`, whose full faithfulness supplies the
uniqueness of the mediating 2-morphisms omitted by the bare existence statement.
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/- The `implicit` transparency level of Lean 4.34 unfolds neither the projections of the 2-fibre
product nor `Functor.Fiber.mk`, so the vertical `eqToHom` bookkeeping below does not reduce. -/
attribute [local implicit_reducible] fst snd structureFunctor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

/-! ### The comparison isomorphism lives in a fibre category -/

/-- For `F` a 1-morphism of categories over `𝒞`, the object `F x` of `𝒮` lies over `U` whenever
`x` lies over `U`. -/
theorem obj_over_base_x (hF : F ⋙ p𝒮 = p𝒳) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    p𝒮.obj (F.obj P.x) = P.base :=
  (Functor.congr_obj hF P.x).trans P.hx

/-- For `G` a 1-morphism of categories over `𝒞`, the object `G y` of `𝒮` lies over `U` whenever
`y` lies over `U`. -/
theorem obj_over_base_y (hG : G ⋙ p𝒮 = p𝒴) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    p𝒮.obj (G.obj P.y) = P.base :=
  (Functor.congr_obj hG P.y).trans P.hy

/-- Clause (1) of Stacks 0040: the comparison isomorphism `φ` of an object `(U, x, y, φ)` is an
isomorphism `F x ≅ G y` *in the fibre category* `𝒮_U`. Both `F x` and `G y` lie over `U` because
`F` and `G` are 1-morphisms over `𝒞`, and `φ` is vertical by construction. -/
@[stacks 0040]
def fibreIso (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    Functor.Fiber.mk (obj_over_base_x p𝒳 p𝒴 p𝒮 F G hF P) ≅
      Functor.Fiber.mk (obj_over_base_y p𝒳 p𝒴 p𝒮 F G hG P) where
  hom := haveI := P.vertical; Functor.Fiber.homMk p𝒮 P.base P.iso.hom
  inv := haveI := P.vertical; Functor.Fiber.homMk p𝒮 P.base P.iso.inv
  hom_inv_id := by have := P.vertical; ext; simp
  inv_hom_id := by have := P.vertical; ext; simp

/-! ### The mediating 1-morphism -/

variable {W : Type u₅} [Category.{v₅} W] (pW : W ⥤ 𝒞) (H : W ⥤ 𝒳) (K : W ⥤ 𝒴)
  (hH : H ⋙ p𝒳 = pW) (hK : K ⋙ p𝒴 = pW) (t : H ⋙ F ≅ K ⋙ G)
  (ht : ∀ w, p𝒮.IsHomLift (𝟙 (pW.obj w)) (t.hom.app w))

/-- The mediating 1-morphism `γ : W ⥤ 𝒳 ×_𝒮 𝒴` of Stacks 0040, sending `w` to the quadruple
`(pW w, H w, K w, t w)`. That `H` and `K` are 1-morphisms over `𝒞` is what makes the two components
of `γ h` lie over the common base morphism `pW h`, and the comparison square is the naturality
of `t`. -/
@[simps, stacks 0040]
def lift : W ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G where
  obj w :=
    { base := pW.obj w
      x := H.obj w
      y := K.obj w
      hx := Functor.congr_obj hH w
      hy := Functor.congr_obj hK w
      iso := t.app w
      vertical := ht w }
  map {w w'} h :=
    { hbase := pW.map h
      a := H.map h
      b := K.map h
      ha := IsHomLift.of_fac' p𝒳 (pW.map h) (H.map h) (Functor.congr_obj hH w)
        (Functor.congr_obj hH w') (Functor.congr_hom hH h)
      hb := IsHomLift.of_fac' p𝒴 (pW.map h) (K.map h) (Functor.congr_obj hK w)
        (Functor.congr_obj hK w') (Functor.congr_hom hK h)
      w := t.hom.naturality h }
  map_id _ := by apply Hom.ext' <;> simp
  map_comp _ _ := by apply Hom.ext' <;> simp

/-! ### Full faithfulness of the mediating 1-morphism -/

/-- **The mediating 1-morphism is faithful as soon as `K` is.** Its `𝒴`-component is `K` itself. -/
instance faithful_lift [K.Faithful] :
    (lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).Faithful where
  map_injective {_w _w'} {h h'} e :=
    have hb : ((lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).map h).b
        = ((lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).map h').b := congrArg Hom.b e
    K.map_injective hb

/-- **The mediating 1-morphism is full as soon as `K` is full and faithful and `F` is faithful.**
A morphism `Φ` of the 2-fibre product between two objects in the image has a `𝒴`-component which
is `K` of some `h`, by fullness of `K`; and then `Φ`'s own compatibility square and the naturality
of `t` at `h` make `F` agree on `Φ`'s `𝒳`-component and on `H h` after composing with the
isomorphism `t` at the target, so faithfulness of `F` identifies them. -/
instance full_lift [K.Full] [K.Faithful] [F.Faithful] :
    (lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).Full where
  map_surjective {w w'} Φ := by
    obtain ⟨h, hh⟩ := Functor.Full.map_surjective (F := K) Φ.b
    refine ⟨h, Hom.ext' ?_ ?_⟩
    · have hn := t.hom.naturality h
      simp only [Functor.comp_map] at hn
      rw [hh] at hn
      have hw := Φ.w
      simp only [lift_obj_iso, Iso.app_hom] at hw
      have key : F.map (H.map h) ≫ t.hom.app w' = F.map Φ.a ≫ t.hom.app w' := hn.trans hw.symm
      exact F.map_injective ((Iso.cancel_iso_hom_right _ _ (t.app w')).mp key)
    · exact hh

attribute [local implicit_reducible] lift

/-- The mediating 1-morphism is a 1-morphism of categories over `𝒞`: it sends `w` to an object
lying over `pW w`, and a morphism to one lying over `pW h`. -/
@[stacks 0040]
theorem lift_comp_structureFunctor :
    lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht ⋙ structureFunctor p𝒳 p𝒴 p𝒮 F G = pW :=
  Functor.ext (fun _ => rfl) (fun _ _ _ => by simp)

/-- The first comparison 2-isomorphism `γ ⋙ fst ≅ H`. The mediating 1-morphism is the one
constructed in the source, so this is the identity. -/
def liftCompFst : lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht ⋙ fst p𝒳 p𝒴 p𝒮 F G ≅ H :=
  Iso.refl _

/-- The second comparison 2-isomorphism `γ ⋙ snd ≅ K`. -/
def liftCompSnd : lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht ⋙ snd p𝒳 p𝒴 p𝒮 F G ≅ K :=
  Iso.refl _

attribute [local implicit_reducible] liftCompFst liftCompSnd

/-- The first comparison isomorphism is a 2-morphism over `𝒞`: its components are vertical. -/
@[stacks 0040]
theorem liftCompFst_hom_app_isHomLift (w : W) :
    p𝒳.IsHomLift (𝟙 (pW.obj w)) ((liftCompFst p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).hom.app w) :=
  IsHomLift.id (Functor.congr_obj hH w)

/-- The second comparison isomorphism is a 2-morphism over `𝒞`: its components are vertical. -/
@[stacks 0040]
theorem liftCompSnd_hom_app_isHomLift (w : W) :
    p𝒴.IsHomLift (𝟙 (pW.obj w)) ((liftCompSnd p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).hom.app w) :=
  IsHomLift.id (Functor.congr_obj hK w)

/-- The factorisation is compatible with the given isomorphism `t`: whiskering the 2-cell `ψ` into
`γ` and correcting by the two comparison isomorphisms recovers `t`. This is the commuting square of
2-morphisms which makes `γ` a factorisation of the test cone `(H, K, t)`, rather than merely a
1-morphism with the right two projections. -/
@[stacks 0040]
theorem lift_whiskerRight_psi :
    Functor.whiskerRight (liftCompFst p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).hom F ≫ t.hom =
      Functor.whiskerLeft (lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht) (psiIso p𝒳 p𝒴 p𝒮 F G).hom ≫
        Functor.whiskerRight (liftCompSnd p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).hom G := by
  ext w
  simp [liftCompFst, liftCompSnd]

/-! ### Uniqueness of the mediating 1-morphism -/

/-- A morphism of the 2-fibre product whose two components are isomorphisms is an isomorphism. -/
theorem isIso_of_isIso_components {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (φ : P ⟶ Q)
    (h₁ : IsIso φ.a) (h₂ : IsIso φ.b) : IsIso φ := by
  have := h₁
  have := h₂
  have := φ.ha
  have := φ.hb
  have hx' : φ.hbase = eqToHom P.hx.symm ≫ p𝒳.map φ.a ≫ eqToHom Q.hx := φ.hbase_eq
  have hy' : φ.hbase = eqToHom P.hy.symm ≫ p𝒴.map φ.b ≫ eqToHom Q.hy :=
    IsHomLift.fac p𝒴 φ.hbase φ.b
  refine ⟨⟨Hom.mk' (inv φ.a) (inv φ.b) ?_ ?_, ?_, ?_⟩⟩
  · simpa using IsIso.inv_eq_inv.mpr (hy'.symm.trans hx')
  · simp only [Functor.map_inv]
    rw [IsIso.inv_comp_eq, ← Category.assoc, φ.w, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  · apply Hom.ext' <;> simp
  · apply Hom.ext' <;> simp

/-- Two 2-morphisms into the 2-fibre product that agree after projecting to `𝒳` and to `𝒴` are
equal, so the mediating 2-morphism supplied by `liftIso` is the only one. -/
@[stacks 0040]
theorem natTrans_ext {γ δ : W ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {α β : γ ⟶ δ}
    (h₁ : Functor.whiskerRight α (fst p𝒳 p𝒴 p𝒮 F G) =
      Functor.whiskerRight β (fst p𝒳 p𝒴 p𝒮 F G))
    (h₂ : Functor.whiskerRight α (snd p𝒳 p𝒴 p𝒮 F G) =
      Functor.whiskerRight β (snd p𝒳 p𝒴 p𝒮 F G)) : α = β := by
  ext w
  refine Hom.ext' ?_ ?_
  · simpa using NatTrans.congr_app h₁ w
  · simpa using NatTrans.congr_app h₂ w

variable {p𝒳 p𝒴 p𝒮 F G pW H K t}

/-- Any other factorisation of the test cone `(H, K, t)` through the 2-fibre product is
2-isomorphic over `𝒞` to the mediating 1-morphism `lift`. Together with `natTrans_ext` this is the
uniqueness half of the 2-universal property: the factorisation is unique up to a unique
2-isomorphism over `𝒞`. -/
@[stacks 0040]
noncomputable def liftIso (γ : W ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G)
    (a : γ ⋙ fst p𝒳 p𝒴 p𝒮 F G ≅ H) (b : γ ⋙ snd p𝒳 p𝒴 p𝒮 F G ≅ K)
    (ha : ∀ w, p𝒳.IsHomLift (𝟙 (pW.obj w)) (a.hom.app w))
    (hb : ∀ w, p𝒴.IsHomLift (𝟙 (pW.obj w)) (b.hom.app w))
    (hab : Functor.whiskerRight a.hom F ≫ t.hom =
      Functor.whiskerLeft γ (psiIso p𝒳 p𝒴 p𝒮 F G).hom ≫ Functor.whiskerRight b.hom G)
    (hH : H ⋙ p𝒳 = pW) (hK : K ⋙ p𝒴 = pW)
    (ht : ∀ w, p𝒮.IsHomLift (𝟙 (pW.obj w)) (t.hom.app w)) :
    γ ≅ lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht := by
  refine NatIso.ofComponents (fun w => ?_) (fun {w w'} h => ?_)
  · refine @asIso _ _ _ _ (Hom.mk' (a.hom.app w) (b.hom.app w) ?_ ?_) ?_
    · have := ha w
      have := hb w
      rw [IsHomLift.fac' p𝒳 (𝟙 (pW.obj w)) (a.hom.app w),
        IsHomLift.fac' p𝒴 (𝟙 (pW.obj w)) (b.hom.app w)]
      simp
    · simpa using NatTrans.congr_app hab w
    · exact isIso_of_isIso_components p𝒳 p𝒴 p𝒮 F G _
        (by simp only [Hom.mk'_a]; infer_instance) (by simp only [Hom.mk'_b]; infer_instance)
  · apply Hom.ext'
    · simpa using a.hom.naturality h
    · simpa using b.hom.naturality h

end CategoryTheory.TwoFibreProductOver
