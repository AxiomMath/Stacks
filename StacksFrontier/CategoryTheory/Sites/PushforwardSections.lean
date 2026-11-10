module

public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.Sites.GlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# Computing a pushforward of presheaves along a morphism of fibred categories

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred over `𝒞`, with `p𝒴 : 𝒴 ⥤ 𝒞` fibred in
groupoids, and let `ℱ` be a presheaf of types on `𝒳`. Stacks 06W6 computes the value at an object
`y` of the fibre `𝒴_V` of the pushforward `f_* ℱ`, i.e. of the right Kan extension of `ℱ` along
`f.op`: it is the set of global sections of the restriction of `ℱ` to the two-fibre product
`(𝒞/V) ×_𝒞 𝒳`, taken over a choice of pullbacks for `p𝒴`.

The computation goes through an equivalence of index categories. The right Kan extension at `op y`
is a limit over `CostructuredArrow f y`, and the two-fibre product maps to that index category by
sending a pair to its comparison arrow `P.y ⟶ y`. Groupoidness of the fibres of `p𝒴` is what makes
that functor an equivalence: a lift of an identity between two objects of a fibre is invertible, so
the arrow produced by the universal property of a chosen cartesian lift is an isomorphism.

## Main definitions

* `CategoryTheory.Functor.CartesianSliceDatum`, the data a choice of pullbacks attaches to an
  object `Y` of `𝒴`: a 1-morphism `𝒞/p𝒴(Y) ⥤ 𝒴` together with a cone to `Y` of strongly cartesian
  lifts. `CategoryTheory.Functor.ChoiceOfPullbacks.sliceDatum` is the datum of a choice of
  pullbacks.
* `CategoryTheory.Presheaf.pushforwardSectionsEquiv`, Stacks 06W6: the identification of the
  pushforward at `y` with the global sections of the restricted presheaf.

## Main results

* `CategoryTheory.Presheaf.pushforwardSectionsEquiv_apply`, the componentwise description of the
  identification by the counit of the right Kan extension;
* `CategoryTheory.Presheaf.pushforwardSectionsEquiv_naturality`, its naturality in the presheaf.

## Implementation notes

`CategoryTheory.Functor.Fiber` is a plain `def` for a subtype, and
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` unfolds through it, so every goal
mentioning `c.sliceFunctor y` fails to be type-correct at `implicit` transparency and `rw`/`simp`
silently refuse it. The whole development below is therefore phrased over a variable
`CategoryTheory.Functor.CartesianSliceDatum`, whose projections are opaque to `whnf`; the three
results of Stacks 06W6 are obtained from it by substituting the fibre equation of `y` and taking
the datum of the choice of pullbacks.
-/

@[expose] public section

open CategoryTheory Opposite

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- The data attached to an object `Y` of `𝒴` by a choice of pullbacks for `p𝒴 : 𝒴 ⥤ 𝒞`:
a 1-morphism `𝒞/p𝒴(Y) ⥤ 𝒴` over `𝒞` together with a cone to `Y` whose components are strongly
cartesian lifts of the structure morphisms of the slice. -/
structure CartesianSliceDatum (p𝒴 : 𝒴 ⥤ 𝒞) (Y : 𝒴) where
  /-- The 1-morphism `𝒞/p𝒴(Y) ⥤ 𝒴`. -/
  sliceMor : Over (p𝒴.obj Y) ⥤ 𝒴
  /-- The cone from `sliceMor` to `Y`. -/
  cone : ∀ W : Over (p𝒴.obj Y), sliceMor.obj W ⟶ Y
  /-- The cone is natural. -/
  cone_naturality : ∀ {W W' : Over (p𝒴.obj Y)} (h : W ⟶ W'),
    sliceMor.map h ≫ cone W' = cone W
  /-- Each component of the cone is a strongly cartesian lift of the structure morphism. -/
  cone_isStronglyCartesian : ∀ W : Over (p𝒴.obj Y), p𝒴.IsStronglyCartesian W.hom (cone W)
  /-- `sliceMor` is a 1-morphism over `𝒞`. -/
  sliceMor_map_isHomLift : ∀ {W W' : Over (p𝒴.obj Y)} (h : W ⟶ W'),
    p𝒴.IsHomLift h.left (sliceMor.map h)

namespace ChoiceOfPullbacks

variable {p𝒴 : 𝒴 ⥤ 𝒞}

/-- The cartesian slice datum of an object `Y` of `𝒴` determined by a choice of pullbacks: its
1-morphism is `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` at the tautological element
of the fibre over `p𝒴(Y)`, and its cone is the family of chosen cartesian lifts. -/
noncomputable def sliceDatum (c : p𝒴.ChoiceOfPullbacks) (Y : 𝒴) :
    p𝒴.CartesianSliceDatum Y where
  sliceMor := c.sliceFunctor (Fiber.mk (rfl : p𝒴.obj Y = p𝒴.obj Y))
  cone W := c.map W.hom (Fiber.mk (rfl : p𝒴.obj Y = p𝒴.obj Y))
  cone_naturality h := c.sliceFunctor_map_fac _ h
  cone_isStronglyCartesian W := c.isStronglyCartesian W.hom _
  sliceMor_map_isHomLift h := c.sliceFunctor_map_isHomLift _ h

/-- The 1-morphism of `sliceDatum c Y` is the slice functor of `c` at `Y`. -/
@[simp]
lemma sliceDatum_sliceMor (c : p𝒴.ChoiceOfPullbacks) (Y : 𝒴) :
    (c.sliceDatum Y).sliceMor = c.sliceFunctor (Fiber.mk (rfl : p𝒴.obj Y = p𝒴.obj Y)) := rfl

/-- The component of the cone of `sliceDatum c Y` at `W` is the chosen pullback along `W.hom`. -/
@[simp]
lemma sliceDatum_cone (c : p𝒴.ChoiceOfPullbacks) (Y : 𝒴) (W : Over (p𝒴.obj Y)) :
    (c.sliceDatum Y).cone W = c.map W.hom (Fiber.mk (rfl : p𝒴.obj Y = p𝒴.obj Y)) := rfl

end ChoiceOfPullbacks

end CategoryTheory.Functor

namespace CategoryTheory.Presheaf

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- The comparison arrow of an object of the two-fibre product is natural: a morphism of the
two-fibre product commutes with the arrows to `Y`. -/
lemma pushforwardIndexFunctor_w
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y)
    {P Q : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f}
    (φ : P ⟶ Q) :
    f.map φ.b ≫ (Q.iso.inv ≫ D.cone Q.x) = P.iso.inv ≫ D.cone P.x := by
  have h : f.map φ.b ≫ Q.iso.inv = P.iso.inv ≫ D.sliceMor.map φ.a := by
    calc
      f.map φ.b ≫ Q.iso.inv = P.iso.inv ≫ (P.iso.hom ≫ f.map φ.b) ≫ Q.iso.inv := by simp
      _ = P.iso.inv ≫ (D.sliceMor.map φ.a ≫ Q.iso.hom) ≫ Q.iso.inv := by rw [← φ.w]
      _ = P.iso.inv ≫ D.sliceMor.map φ.a := by simp [Category.assoc]
  calc
    f.map φ.b ≫ (Q.iso.inv ≫ D.cone Q.x) =
        (f.map φ.b ≫ Q.iso.inv) ≫ D.cone Q.x := by simp [Category.assoc]
    _ = (P.iso.inv ≫ D.sliceMor.map φ.a) ≫ D.cone Q.x := by rw [h]
    _ = P.iso.inv ≫ D.cone P.x := by rw [Category.assoc, D.cone_naturality]

/-- The functor from the two-fibre product to the index category of the right Kan extension:
an object is sent to its comparison arrow `P.y ⟶ Y`. -/
noncomputable def pushforwardIndexFunctor
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y) :
    TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f ⥤
      CostructuredArrow f Y where
  obj P := CostructuredArrow.mk (P.iso.inv ≫ D.cone P.x)
  map {P Q} φ := CostructuredArrow.homMk φ.b (pushforwardIndexFunctor_w p𝒳 p𝒴 f D φ)
  map_id P := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp φ ψ := by
    apply CostructuredArrow.hom_ext
    rfl

/-- The object of the two-fibre product attached to an arrow `Z.left ⟶ Y` of the index category:
its slice component is the structure morphism of `Z`, and the comparison isomorphism comes from
the universal property of the chosen cartesian lift together with groupoidness of the fibres. -/
noncomputable def pushforwardIndexInverseObj
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (Z : CostructuredArrow f Y) :
    TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f := by
  let W₀ : Over (p𝒴.obj Y) := Over.mk (p𝒴.map Z.hom)
  letI : p𝒴.IsStronglyCartesian W₀.hom (D.cone W₀) := D.cone_isStronglyCartesian W₀
  let β : f.obj Z.left ⟶ D.sliceMor.obj W₀ :=
    Functor.IsStronglyCartesian.map p𝒴 W₀.hom (D.cone W₀)
      (g := 𝟙 (p𝒴.obj (f.obj Z.left))) (f' := p𝒴.map Z.hom) (by simp [W₀]) Z.hom
  have hβ : p𝒴.IsHomLift (𝟙 (p𝒴.obj (f.obj Z.left))) β :=
    Functor.IsStronglyCartesian.map_isHomLift p𝒴 W₀.hom (D.cone W₀)
      (g := 𝟙 (p𝒴.obj (f.obj Z.left))) (f' := p𝒴.map Z.hom) (by simp [W₀]) Z.hom
  letI : IsIso β := Functor.isIso_of_fiber_isGroupoid (h𝒴.fiber_isGroupoid _) β hβ
  refine ⟨p𝒴.obj (f.obj Z.left), W₀, Z.left, rfl, ?_, (asIso β).symm, ?_⟩
  · simpa using (congrArg (fun g : 𝒳 ⥤ 𝒞 => g.obj Z.left) hf).symm
  · have : p𝒴.IsHomLift (𝟙 (p𝒴.obj (f.obj Z.left))) (asIso β).hom := by simpa using hβ
    exact IsHomLift.lift_id_inv p𝒴 _ (asIso β)


/-- The comparison isomorphism of an object of the two-fibre product composed with the cone is
the arrow the index functor produces. -/
lemma pushforwardIndexCone_isHomLift
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y)
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    p𝒴.IsHomLift P.x.hom (P.iso.inv ≫ D.cone P.x) := by
  have hver : p𝒴.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have hinv : p𝒴.IsHomLift (𝟙 P.base) P.iso.inv := IsHomLift.lift_id_inv p𝒴 P.base P.iso
  have hsc : p𝒴.IsStronglyCartesian P.x.hom (D.cone P.x) := D.cone_isStronglyCartesian P.x
  exact IsHomLift.comp_lift_id_left' p𝒴 P.base P.iso.inv P.x.hom (D.cone P.x)

/-- A candidate pair of components for a morphism of the two-fibre product satisfies the
comparison square as soon as it is compatible with the cone. -/
lemma pushforwardIndexSliceMor_map_comp_iso_hom
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y)
    {P Q : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f}
    (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (hb : p𝒴.IsHomLift a.left (f.map b))
    (hcone : P.iso.inv ≫ D.cone P.x = f.map b ≫ Q.iso.inv ≫ D.cone Q.x) :
    D.sliceMor.map a ≫ Q.iso.hom = P.iso.hom ≫ f.map b := by
  have hPver : p𝒴.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have hQver : p𝒴.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
  have hPinv : p𝒴.IsHomLift (𝟙 P.base) P.iso.inv := IsHomLift.lift_id_inv p𝒴 P.base P.iso
  have hQinv : p𝒴.IsHomLift (𝟙 Q.base) Q.iso.inv := IsHomLift.lift_id_inv p𝒴 Q.base Q.iso
  have hAmap : p𝒴.IsHomLift a.left (D.sliceMor.map a) := D.sliceMor_map_isHomLift a
  have hsc : p𝒴.IsStronglyCartesian Q.x.hom (D.cone Q.x) := D.cone_isStronglyCartesian Q.x
  have hphi : p𝒴.IsHomLift P.x.hom (P.iso.inv ≫ D.cone P.x) :=
    pushforwardIndexCone_isHomLift p𝒳 p𝒴 f D P
  have hLeft : p𝒴.IsHomLift a.left (P.iso.inv ≫ D.sliceMor.map a) :=
    IsHomLift.comp_lift_id_left' p𝒴 P.base P.iso.inv a.left (D.sliceMor.map a)
  have hRight : p𝒴.IsHomLift a.left (f.map b ≫ Q.iso.inv) :=
    IsHomLift.comp_lift_id_right' p𝒴 a.left (f.map b) Q.base Q.iso.inv
  have hf' : P.x.hom = a.left ≫ Q.x.hom := (Over.w a).symm
  have h1 : (P.iso.inv ≫ D.sliceMor.map a) ≫ D.cone Q.x = P.iso.inv ≫ D.cone P.x := by
    rw [Category.assoc, D.cone_naturality]
  have h2 : (f.map b ≫ Q.iso.inv) ≫ D.cone Q.x = P.iso.inv ≫ D.cone P.x := by
    rw [Category.assoc, ← hcone]
  have e₁ := Functor.IsStronglyCartesian.map_uniq p𝒴 Q.x.hom (D.cone Q.x) hf'
    (P.iso.inv ≫ D.cone P.x) (P.iso.inv ≫ D.sliceMor.map a) h1
  have e₂ := Functor.IsStronglyCartesian.map_uniq p𝒴 Q.x.hom (D.cone Q.x) hf'
    (P.iso.inv ≫ D.cone P.x) (f.map b ≫ Q.iso.inv) h2
  have h₁ : P.iso.inv ≫ D.sliceMor.map a = f.map b ≫ Q.iso.inv := e₁.trans e₂.symm
  calc
    D.sliceMor.map a ≫ Q.iso.hom =
        P.iso.hom ≫ (P.iso.inv ≫ D.sliceMor.map a) ≫ Q.iso.hom := by simp
    _ = P.iso.hom ≫ (f.map b ≫ Q.iso.inv) ≫ Q.iso.hom := by rw [h₁]
    _ = P.iso.hom ≫ f.map b := by simp [Category.assoc]

section Inverse

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
  {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y)
  (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)

/-- The slice component of `pushforwardIndexInverseObj` is the structure morphism of `Z`. -/
@[simp]
lemma pushforwardIndexInverseObj_x (Z : CostructuredArrow f Y) :
    (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z).x = Over.mk (p𝒴.map Z.hom) := rfl

/-- The `𝒳`-component of `pushforwardIndexInverseObj` is the source of `Z`. -/
@[simp]
lemma pushforwardIndexInverseObj_y (Z : CostructuredArrow f Y) :
    (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z).y = Z.left := rfl

/-- The base of `pushforwardIndexInverseObj`. -/
@[simp]
lemma pushforwardIndexInverseObj_base (Z : CostructuredArrow f Y) :
    (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z).base = p𝒴.obj (f.obj Z.left) := rfl

/-- The comparison arrow of `pushforwardIndexInverseObj` recovers the structure morphism of `Z`. -/
lemma pushforwardIndexInverseObj_iso_inv_comp_cone (Z : CostructuredArrow f Y) :
    (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z).iso.inv ≫
      D.cone (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z).x = Z.hom := by
  dsimp [pushforwardIndexInverseObj]
  simp

/-- The slice component of the morphism of two-fibre products attached by
`pushforwardIndexInverseObj` to a morphism `g : Z ⟶ Z'` of the index category. -/
noncomputable def pushforwardIndexInverseMapX {Z Z' : CostructuredArrow f Y} (g : Z ⟶ Z') :
    (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z).x ⟶
      (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z').x :=
  Over.homMk (p𝒴.map (f.map g.left)) (by
    dsimp [pushforwardIndexInverseObj]
    rw [← Functor.map_comp]
    simp)

/-- The underlying morphism of `pushforwardIndexInverseMapX` is `p𝒴.map (f.map g.left)`. -/
@[simp]
lemma pushforwardIndexInverseMapX_left {Z Z' : CostructuredArrow f Y} (g : Z ⟶ Z') :
    (pushforwardIndexInverseMapX p𝒳 p𝒴 f D h𝒴 hf g).left = p𝒴.map (f.map g.left) := rfl

/-- `pushforwardIndexInverseMapX` sends identities to identities. -/
@[simp]
lemma pushforwardIndexInverseMapX_id (Z : CostructuredArrow f Y) :
    pushforwardIndexInverseMapX p𝒳 p𝒴 f D h𝒴 hf (𝟙 Z) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp

/-- `pushforwardIndexInverseMapX` sends composites to composites. -/
@[simp]
lemma pushforwardIndexInverseMapX_comp {Z Z' Z'' : CostructuredArrow f Y}
    (g : Z ⟶ Z') (h : Z' ⟶ Z'') :
    pushforwardIndexInverseMapX p𝒳 p𝒴 f D h𝒴 hf (g ≫ h) =
      pushforwardIndexInverseMapX p𝒳 p𝒴 f D h𝒴 hf g ≫
        pushforwardIndexInverseMapX p𝒳 p𝒴 f D h𝒴 hf h := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  simp [Functor.map_comp]

/-- The base compatibility of the two components. -/
lemma pushforwardIndexInverseMap_base {Z Z' : CostructuredArrow f Y} (g : Z ⟶ Z') :
    eqToHom (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z).hy.symm ≫
        p𝒳.map g.left ≫ eqToHom (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z').hy =
      𝟙 (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z).base ≫
        p𝒴.map (f.map g.left) ≫
          𝟙 (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z').base := by
  simpa using (Functor.IsFiberedInGroupoids.Factorization.map_eq_of_comp_eq
    p𝒳 p𝒴 f hf g.left).symm

/-- The morphism of the two-fibre product attached to a morphism of the index category. -/
noncomputable def pushforwardIndexInverseMap {Z Z' : CostructuredArrow f Y} (g : Z ⟶ Z') :
    pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z ⟶
      pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z' :=
  TwoFibreProductOver.Hom.mk' (pushforwardIndexInverseMapX p𝒳 p𝒴 f D h𝒴 hf g) g.left
    (pushforwardIndexInverseMap_base p𝒳 p𝒴 f D h𝒴 hf g)
    (pushforwardIndexSliceMor_map_comp_iso_hom p𝒳 p𝒴 f D
      (P := pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z)
      (Q := pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z')
      (pushforwardIndexInverseMapX p𝒳 p𝒴 f D h𝒴 hf g) g.left
      (by
        rw [pushforwardIndexInverseMapX_left]
        exact IsHomLift.map p𝒴 (f.map g.left))
      (by
        rw [pushforwardIndexInverseObj_iso_inv_comp_cone,
          pushforwardIndexInverseObj_iso_inv_comp_cone]
        exact (CostructuredArrow.w g).symm))

/-- The slice component of `pushforwardIndexInverseMap` is `pushforwardIndexInverseMapX`. -/
@[simp]
lemma pushforwardIndexInverseMap_a {Z Z' : CostructuredArrow f Y} (g : Z ⟶ Z') :
    (pushforwardIndexInverseMap p𝒳 p𝒴 f D h𝒴 hf g).a =
      pushforwardIndexInverseMapX p𝒳 p𝒴 f D h𝒴 hf g := rfl

/-- The `𝒳`-component of `pushforwardIndexInverseMap` is `g.left`. -/
@[simp]
lemma pushforwardIndexInverseMap_b {Z Z' : CostructuredArrow f Y} (g : Z ⟶ Z') :
    (pushforwardIndexInverseMap p𝒳 p𝒴 f D h𝒴 hf g).b = g.left := rfl

/-- The inverse functor: the index category of the right Kan extension maps back into the
two-fibre product. -/
noncomputable def pushforwardIndexInverse :
    CostructuredArrow f Y ⥤
      TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f where
  obj Z := pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf Z
  map g := pushforwardIndexInverseMap p𝒳 p𝒴 f D h𝒴 hf g
  map_id Z := by
    apply TwoFibreProductOver.Hom.ext' <;> simp
  map_comp g h := by
    apply TwoFibreProductOver.Hom.ext' <;> simp

end Inverse

section Unit

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
  {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y)
  (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)

/-- The source of the arrow `pushforwardIndexFunctor` attaches to `P` is `P.y`. -/
@[simp]
lemma pushforwardIndexFunctor_obj_left
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj P).left = P.y := rfl

/-- The arrow `pushforwardIndexFunctor` attaches to `P` is `P.iso.inv ≫ D.cone P.x`. -/
@[simp]
lemma pushforwardIndexFunctor_obj_hom
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj P).hom = P.iso.inv ≫ D.cone P.x := rfl

/-- The round trip through the index category does not move the `𝒳`-component. -/
lemma pushforwardIndexInverseObj_index_y
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf
      ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj P)).y = P.y := rfl

/-- The projection to `𝒳` is natural for the inverse functor. -/
lemma pushforwardIndexInverse_snd_naturality_inv
    {Z Z' : CostructuredArrow f Y} (g : Z ⟶ Z') :
    eqToHom (pushforwardIndexInverseObj_y p𝒳 p𝒴 f D h𝒴 hf Z).symm ≫
        (TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f).map
          ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).map g) =
      (CostructuredArrow.proj f Y).map g ≫
        eqToHom (pushforwardIndexInverseObj_y p𝒳 p𝒴 f D h𝒴 hf Z').symm := by
  simp only [pushforwardIndexInverse, CostructuredArrow.proj, TwoFibreProductOver.snd,
    pushforwardIndexInverseMap_b]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

include hf in
/-- The source of the comparison arrow of an object of the two-fibre product lies over the
slice component. -/
lemma pushforwardIndexUnit_left
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    p𝒴.obj (f.obj P.y) = P.x.left := by
  simpa using (congrFun (congrArg (fun G : 𝒳 ⥤ 𝒞 => G.obj) hf) P.y).trans (P.hy.trans P.hx.symm)

/-- The comparison arrow of an object of the two-fibre product lies over the structure
morphism of its slice component. -/
lemma pushforwardIndexUnit_hα
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    eqToHom (pushforwardIndexUnit_left p𝒳 p𝒴 f D hf P) ≫ P.x.hom =
      p𝒴.map (P.iso.inv ≫ D.cone P.x) := by
  have := pushforwardIndexCone_isHomLift p𝒳 p𝒴 f D P
  rw [IsHomLift.fac' p𝒴 P.x.hom (P.iso.inv ≫ D.cone P.x)]
  simp

/-- The slice component of the unit of the index equivalence. -/
noncomputable def pushforwardIndexUnitIso
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf
      ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj P)).x ≅ P.x :=
  Over.isoMk (eqToIso (pushforwardIndexUnit_left p𝒳 p𝒴 f D hf P))
    (pushforwardIndexUnit_hα p𝒳 p𝒴 f D hf P)

/-- The underlying morphism of `pushforwardIndexUnitIso` is an `eqToHom`. -/
@[simp]
lemma pushforwardIndexUnitIso_hom_left
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    (pushforwardIndexUnitIso p𝒳 p𝒴 f D h𝒴 hf P).hom.left =
      eqToHom (pushforwardIndexUnit_left p𝒳 p𝒴 f D hf P) := rfl

/-- The unit of the index equivalence at an object of the two-fibre product. -/
noncomputable def pushforwardIndexUnitHom
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf
      ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj P) ⟶ P :=
  TwoFibreProductOver.Hom.mk' (pushforwardIndexUnitIso p𝒳 p𝒴 f D h𝒴 hf P).hom
    (eqToHom (pushforwardIndexInverseObj_index_y p𝒳 p𝒴 f D h𝒴 hf P))
    (by
      have key : ∀ {X₁ X₂ X₃ X₄ Y₂ Y₃ : 𝒞} (k₁ : X₁ = X₂) (k₂ : X₂ = X₃) (k₃ : X₃ = X₄)
          (l₁ : X₁ = Y₂) (l₂ : Y₂ = Y₃) (l₃ : Y₃ = X₄),
          eqToHom k₁ ≫ eqToHom k₂ ≫ eqToHom k₃ =
            eqToHom l₁ ≫ eqToHom l₂ ≫ eqToHom l₃ := by
        intros
        simp
      simp only [eqToHom_map, Over.forget_map, pushforwardIndexUnitIso_hom_left]
      exact key _ _ _ _ _ _)
    (pushforwardIndexSliceMor_map_comp_iso_hom p𝒳 p𝒴 f D
      (P := pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf
        ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj P))
      (Q := P)
      (pushforwardIndexUnitIso p𝒳 p𝒴 f D h𝒴 hf P).hom
      (eqToHom (pushforwardIndexInverseObj_index_y p𝒳 p𝒴 f D h𝒴 hf P))
      (by
        refine IsHomLift.of_fac' p𝒴 _ _ rfl
          (pushforwardIndexUnit_left p𝒳 p𝒴 f D hf P) ?_
        rw [eqToHom_map, eqToHom_map]
        simp)
      (by
        rw [pushforwardIndexInverseObj_iso_inv_comp_cone, eqToHom_map]
        exact (Category.id_comp _).symm))

/-- The `𝒳`-component of `pushforwardIndexUnitHom` is an `eqToHom`. -/
@[simp]
lemma pushforwardIndexUnitHom_b
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    (pushforwardIndexUnitHom p𝒳 p𝒴 f D h𝒴 hf P).b =
      eqToHom (pushforwardIndexInverseObj_index_y p𝒳 p𝒴 f D h𝒴 hf P) := rfl

/-- The projection to `𝒳` sends the unit to the canonical identification. -/
lemma pushforwardIndexUnitHom_snd
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    (TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f).map
      (pushforwardIndexUnitHom p𝒳 p𝒴 f D h𝒴 hf P) =
        eqToHom (pushforwardIndexInverseObj_index_y p𝒳 p𝒴 f D h𝒴 hf P) := by
  rw [TwoFibreProductOver.snd_map]
  exact pushforwardIndexUnitHom_b p𝒳 p𝒴 f D h𝒴 hf P

/-- The other round trip is the identity on the nose. -/
lemma pushforwardIndexFunctor_inverse_obj_eq (Z : CostructuredArrow f Y) :
    (pushforwardIndexFunctor p𝒳 p𝒴 f D).obj
      ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).obj Z) = Z := by
  refine CostructuredArrow.obj_ext
    ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj
      ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).obj Z)) Z rfl ?_
  exact ((congrArg (fun m => m ≫ Z.hom) (f.map_id _)).trans (Category.id_comp _)).trans
    (pushforwardIndexInverseObj_iso_inv_comp_cone p𝒳 p𝒴 f D h𝒴 hf Z).symm

end Unit

/-- The sections of `ℱ` over the index category `CostructuredArrow f Y` are in bijection with
the sections of the restriction of `ℱ` to the two-fibre product. -/
noncomputable def pushforwardIndexSectionsEquiv
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) (ℱ : 𝒳ᵒᵖ ⥤ Type w) :
    ((CostructuredArrow.proj f Y).op ⋙ ℱ).sections ≃
      ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴
        D.sliceMor f).op ⋙ ℱ).sections where
  toFun s := ⟨fun P => s.val ((pushforwardIndexFunctor p𝒳 p𝒴 f D).op.obj P), by
    intro P Q g
    change ℱ.map ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴
      D.sliceMor f).map g.unop).op _ = _
    exact s.property ((pushforwardIndexFunctor p𝒳 p𝒴 f D).op.map g)⟩
  invFun s := ⟨fun Z => by
    change ℱ.obj (op Z.unop.left)
    have v : ℱ.obj (op
        ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).obj Z.unop).y) := by
      simpa [Functor.comp_obj, TwoFibreProductOver.snd] using
        s.val ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.obj Z)
    exact ℱ.map (eqToHom (congrArg Opposite.op
      (pushforwardIndexInverseObj_y p𝒳 p𝒴 f D h𝒴 hf Z.unop))) v, by
    intro P Q g
    let hP := pushforwardIndexInverseObj_y p𝒳 p𝒴 f D h𝒴 hf P.unop
    let hQ := pushforwardIndexInverseObj_y p𝒳 p𝒴 f D h𝒴 hf Q.unop
    let aP := eqToHom (congrArg Opposite.op hP)
    let aQ := eqToHom (congrArg Opposite.op hQ)
    have hsq := pushforwardIndexInverse_snd_naturality_inv
      p𝒳 p𝒴 f D h𝒴 hf g.unop
    have hsq' : ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴
          D.sliceMor f).op.map
            ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.map g)) ≫ aQ =
        aP ≫ (CostructuredArrow.proj f Y).op.map g := by
      change ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴
        D.sliceMor f).map
          ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).map g.unop)).op ≫ aQ =
        aP ≫ ((CostructuredArrow.proj f Y).map g.unop).op
      apply Quiver.Hom.unop_inj
      simp only [aP, aQ]
      exact hsq
    have hcompat := s.property ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.map g)
    calc
      ℱ.map ((CostructuredArrow.proj f Y).op.map g)
          (ℱ.map aP (s.val ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.obj P))) =
          ℱ.map (aP ≫ (CostructuredArrow.proj f Y).op.map g)
            (s.val ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.obj P)) :=
          (Functor.map_comp_apply ℱ _ _ _).symm
      _ = ℱ.map (((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴
              D.sliceMor f).op.map
                ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.map g)) ≫ aQ)
            (s.val ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.obj P)) := by
        rw [hsq']
        rfl
      _ = ℱ.map aQ
            (ℱ.map ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴
              D.sliceMor f).op.map
              ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.map g))
              (s.val ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.obj P))) :=
        Functor.map_comp_apply ℱ _ _ _
      _ = ℱ.map aQ (s.val ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).op.obj Q)) := by
        simpa [Functor.comp_map] using congrArg (fun z => ℱ.map aQ z) hcompat
      _ = _ := rfl⟩
  left_inv s := by
    apply Functor.sections_ext_iff.mpr
    intro Z
    have cancel : ∀ {A B : 𝒳ᵒᵖ} (e₁ : A ⟶ B) (e₂ : B ⟶ A), e₁ ≫ e₂ = 𝟙 A →
        ∀ x : ℱ.obj A, ℱ.map e₂ (ℱ.map e₁ x) = x := by
      intro A B e₁ e₂ he x
      rw [← Functor.map_comp_apply, he]
      simp
    have keyop : ∀ {A B : 𝒳} (k : A = B) (k' : (op A : 𝒳ᵒᵖ) = op B),
        (eqToHom k).op ≫ eqToHom k' = 𝟙 (op B) := by
      intro A B k k'
      subst k
      simp
    have hobj := pushforwardIndexFunctor_inverse_obj_eq p𝒳 p𝒴 f D h𝒴 hf Z.unop
    have hleft : ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).obj Z.unop).y = Z.unop.left :=
      pushforwardIndexInverseObj_y p𝒳 p𝒴 f D h𝒴 hf Z.unop
    have he : (CostructuredArrow.proj f Y).map (eqToHom hobj) = eqToHom hleft :=
      CostructuredArrow.eqToHom_left hobj
    have hcompat := s.property (eqToHom hobj).op
    have hcanc : ((CostructuredArrow.proj f Y).map (eqToHom hobj)).op ≫
        eqToHom (congrArg Opposite.op hleft) = 𝟙 (op Z.unop.left) := by
      rw [he]
      exact keyop _ _
    change ℱ.map (eqToHom (congrArg Opposite.op hleft))
      (s.val (op ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj
        ((pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).obj Z.unop)))) = s.val Z
    rw [← hcompat]
    exact cancel _ _ hcanc (s.val Z)
  right_inv s := by
    apply Functor.sections_ext_iff.mpr
    intro P
    have cancel : ∀ {A B : 𝒳ᵒᵖ} (e₁ : A ⟶ B) (e₂ : B ⟶ A), e₁ ≫ e₂ = 𝟙 A →
        ∀ x : ℱ.obj A, ℱ.map e₂ (ℱ.map e₁ x) = x := by
      intro A B e₁ e₂ he x
      rw [← Functor.map_comp_apply, he]
      simp
    have keyop : ∀ {A B : 𝒳} (k : A = B) (k' : (op A : 𝒳ᵒᵖ) = op B),
        (eqToHom k).op ≫ eqToHom k' = 𝟙 (op B) := by
      intro A B k k'
      subst k
      simp
    have h := pushforwardIndexInverseObj_index_y p𝒳 p𝒴 f D h𝒴 hf P.unop
    have hcompat := s.property (pushforwardIndexUnitHom p𝒳 p𝒴 f D h𝒴 hf P.unop).op
    have hmap := pushforwardIndexUnitHom_snd p𝒳 p𝒴 f D h𝒴 hf P.unop
    have hcanc : ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f).map
          (pushforwardIndexUnitHom p𝒳 p𝒴 f D h𝒴 hf P.unop)).op ≫
        eqToHom (congrArg Opposite.op h) = 𝟙 (op P.unop.y) := by
      rw [hmap]
      exact keyop _ _
    change ℱ.map (eqToHom (congrArg Opposite.op h))
      (s.val (op (pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf
        ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj P.unop)))) = s.val P
    rw [← hcompat]
    exact cancel _ _ hcanc (s.val P)

/-- The sections of `ℱ` over `StructuredArrow (op Y) f.op` are in bijection with those over
`CostructuredArrow f Y`, via the equivalence `costructuredArrowOpEquivalence f Y`. -/
noncomputable def pushforwardCostrSectionsEquiv
    (f : 𝒳 ⥤ 𝒴) (Y : 𝒴) (ℱ : 𝒳ᵒᵖ ⥤ Type w) :
    ((StructuredArrow.proj (op Y) f.op ⋙ ℱ).sections) ≃
      ((CostructuredArrow.proj f Y).op ⋙ ℱ).sections :=
  Equiv.ofBijective
    (Functor.sectionsPrecomp (CategoryTheory.costructuredArrowOpEquivalence f Y).functor)
    (Functor.bijective_sectionsPrecomp
      (CategoryTheory.costructuredArrowOpEquivalence f Y).functor
      (StructuredArrow.proj (op Y) f.op ⋙ ℱ))

/-- The identification of global sections with compatible families of sections is natural in
the presheaf. -/
lemma globalSectionsEquivSections_naturality
    {C : Type u₁} [Category.{v₁} C] {F G : Cᵒᵖ ⥤ Type w}
    (η : F ⟶ G) (s : Presheaf.globalSections F) :
    Presheaf.globalSectionsEquivSections G (s ≫ η) =
      (Functor.sectionsFunctor Cᵒᵖ).map η
        (Presheaf.globalSectionsEquivSections F s) := by
  apply Subtype.ext
  funext j
  rfl

/-! ### The pushforward formula -/

/-- The pushforward formula for a presheaf along a functor into a category fibred
in groupoids.
The projection from the two-fibre product to `𝒳` pulls the presheaf back by
restriction; its global sections compute the right Kan extension at `y`. -/
noncomputable def pushforwardSectionsEquivAux
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    [∀ (G : 𝒳ᵒᵖ ⥤ Type w), f.op.HasPointwiseRightKanExtension G] :
    (f.op.ran.obj ℱ).obj (op Y) ≃
      Presheaf.globalSections
        ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f).op ⋙ ℱ) :=
  (f.op.ranObjObjIsoLimit ℱ (op Y)).toEquiv.trans
    ((Limits.Types.limitEquivSections _).trans
      ((pushforwardCostrSectionsEquiv f Y ℱ).trans
        ((pushforwardIndexSectionsEquiv p𝒳 p𝒴 f D h𝒴 hf ℱ).trans
          (Presheaf.globalSectionsEquivSections
            ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴
              D.sliceMor f).op ⋙ ℱ)).symm)))

/-- At a pair in the two-fibre product, the section corresponding to a pushforward
section is obtained by restricting along the comparison arrow to `Y` and then
applying the counit of the right Kan extension. -/
lemma pushforwardSectionsEquivAux_apply
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    [∀ (G : 𝒳ᵒᵖ ⥤ Type w), f.op.HasPointwiseRightKanExtension G]
    (s : (f.op.ran.obj ℱ).obj (op Y))
    (P : TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f) :
    ((Presheaf.globalSectionsEquivSections
        ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f).op ⋙ ℱ))
      (pushforwardSectionsEquivAux p𝒳 p𝒴 f h𝒴 hf D ℱ s)).1 (op P) =
      (f.op.ranCounit.app ℱ).app (op P.y)
        ((f.op.ran.obj ℱ).map (P.iso.inv ≫ D.cone P.x).op s) := by
  have hπ := Functor.ranObjObjIsoLimit_hom_π f.op ℱ (op Y)
    (StructuredArrow.mk (Y := op P.y)
      ((pushforwardIndexFunctor p𝒳 p𝒴 f D).obj P).hom.op)
  have hval := congrArg
    (fun g : (f.op.ran.obj ℱ).obj (op Y) ⟶ ℱ.obj (op P.y) => g s) hπ
  simp only [Functor.comp_obj, Functor.op_obj, Functor.whiskeringLeft_obj_obj,
    Functor.id_obj, op_comp, Functor.map_comp, comp_apply]
  convert hval using 1
  simp only [pushforwardIndexFunctor, CostructuredArrow.mk,
    CostructuredArrow.left, CostructuredArrow.hom, StructuredArrow.mk,
    StructuredArrow.right, StructuredArrow.hom, TwoFibreProductOver.snd,
    op_comp, Functor.map_comp, CategoryTheory.comp_apply]
  simp
  rfl

/-- The pushforward identification commutes with maps of presheaves. -/
lemma pushforwardSectionsEquivAux_naturality
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y) (ℱ 𝒢 : 𝒳ᵒᵖ ⥤ Type w)
    [∀ (G : 𝒳ᵒᵖ ⥤ Type w), f.op.HasPointwiseRightKanExtension G]
    (η : ℱ ⟶ 𝒢) (s : (f.op.ran.obj ℱ).obj (op Y)) :
    pushforwardSectionsEquivAux p𝒳 p𝒴 f h𝒴 hf D 𝒢
        (((f.op.ran.map η).app (op Y)) s) =
      (pushforwardSectionsEquivAux p𝒳 p𝒴 f h𝒴 hf D ℱ s) ≫
        Functor.whiskerLeft
          (TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f).op η := by
  apply (Presheaf.globalSectionsEquivSections
    ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f).op ⋙ 𝒢)).injective
  apply Functor.sections_ext_iff.mpr
  intro P
  rw [pushforwardSectionsEquivAux_apply (P := P.unop), globalSectionsEquivSections_naturality]
  change (f.op.ranCounit.app 𝒢).app (op P.unop.y)
      ((f.op.ran.obj 𝒢).map
        (P.unop.iso.inv ≫ D.cone P.unop.x).op
        (((f.op.ran.map η).app (op Y)) s)) =
    ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴
      D.sliceMor f).op.whiskerLeft η).app P
      ((Presheaf.globalSectionsEquivSections
        ((TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f).op ⋙ ℱ)
        (pushforwardSectionsEquivAux p𝒳 p𝒴 f h𝒴 hf D ℱ s)).1 P)
  rw [pushforwardSectionsEquivAux_apply]
  have hRanVal :
      (f.op.ran.obj 𝒢).map (P.unop.iso.inv ≫ D.cone P.unop.x).op
          ((f.op.ran.map η).app (op Y) s) =
        (f.op.ran.map η).app (op (f.obj P.unop.y))
          ((f.op.ran.obj ℱ).map (P.unop.iso.inv ≫ D.cone P.unop.x).op s) := by
    simpa only [CategoryTheory.comp_apply] using (congrArg (fun g => g s)
      ((f.op.ran.map η).naturality (P.unop.iso.inv ≫ D.cone P.unop.x).op)).symm
  rw [hRanVal]
  have hεVal := congrArg
    (fun g => g ((f.op.ran.obj ℱ).map (P.unop.iso.inv ≫ D.cone P.unop.x).op s))
    (congr_app (f.op.ranCounit.naturality η) (op P.unop.y))
  simp only [Functor.whiskerLeft_app]
  exact hεVal

/-! ### Stacks 06W6 -/

/-- The pushforward formula for a presheaf along a functor into a category fibred
in groupoids.
The projection from the two-fibre product to `𝒳` pulls the presheaf back by
restriction; its global sections compute the right Kan extension at `y`. -/
@[stacks 06W6 "canonical identification"]
public noncomputable def pushforwardSectionsEquiv
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hf : f ⋙ p𝒴 = p𝒳) (c : p𝒴.ChoiceOfPullbacks)
    {V : 𝒞} (y : p𝒴.Fiber V) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    [∀ (G : 𝒳ᵒᵖ ⥤ Type w), f.op.HasPointwiseRightKanExtension G] :
    (f.op.ran.obj ℱ).obj (op y.1) ≃
      Presheaf.globalSections
        ((TwoFibreProductOver.snd (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f).op ⋙ ℱ) := by
  obtain ⟨y₀, rfl⟩ := y
  exact pushforwardSectionsEquivAux p𝒳 p𝒴 f h𝒴 hf (c.sliceDatum y₀) ℱ

/-- At a pair in the two-fibre product, the section corresponding to a pushforward
section is obtained by restricting along the comparison arrow to `y` and then
applying the counit of the right Kan extension. -/
@[stacks 06W6 "componentwise characterization by the right Kan counit"]
public theorem pushforwardSectionsEquiv_apply
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hf : f ⋙ p𝒴 = p𝒳) (c : p𝒴.ChoiceOfPullbacks)
    {V : 𝒞} (y : p𝒴.Fiber V) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    [∀ (G : 𝒳ᵒᵖ ⥤ Type w), f.op.HasPointwiseRightKanExtension G]
    (s : (f.op.ran.obj ℱ).obj (op y.1))
    (P : TwoFibreProductOver (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f) :
    ((Presheaf.globalSectionsEquivSections
        ((TwoFibreProductOver.snd (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f).op ⋙ ℱ))
      (pushforwardSectionsEquiv p𝒳 p𝒴 f h𝒴 hf c y ℱ s)).1 (op P) =
      (f.op.ranCounit.app ℱ).app (op P.y)
        ((f.op.ran.obj ℱ).map (P.iso.inv ≫ c.map P.x.hom y).op s) := by
  obtain ⟨y₀, rfl⟩ := y
  exact pushforwardSectionsEquivAux_apply p𝒳 p𝒴 f h𝒴 hf (c.sliceDatum y₀) ℱ s P

/-- The pushforward identification commutes with maps of presheaves. -/
@[stacks 06W6 "naturality in the presheaf"]
public theorem pushforwardSectionsEquiv_naturality
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴)
    (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hf : f ⋙ p𝒴 = p𝒳) (c : p𝒴.ChoiceOfPullbacks)
    {V : 𝒞} (y : p𝒴.Fiber V) (ℱ 𝒢 : 𝒳ᵒᵖ ⥤ Type w)
    [∀ (G : 𝒳ᵒᵖ ⥤ Type w), f.op.HasPointwiseRightKanExtension G]
    (η : ℱ ⟶ 𝒢) (s : (f.op.ran.obj ℱ).obj (op y.1)) :
    pushforwardSectionsEquiv p𝒳 p𝒴 f h𝒴 hf c y 𝒢
        (((f.op.ran.map η).app (op y.1)) s) =
      (pushforwardSectionsEquiv p𝒳 p𝒴 f h𝒴 hf c y ℱ s) ≫
        Functor.whiskerLeft
          (TwoFibreProductOver.snd (Over.forget V) p𝒳 p𝒴 (c.sliceFunctor y) f).op η := by
  obtain ⟨y₀, rfl⟩ := y
  exact pushforwardSectionsEquivAux_naturality p𝒳 p𝒴 f h𝒴 hf (c.sliceDatum y₀) ℱ 𝒢 η s
end CategoryTheory.Presheaf

end
