module

public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationReduction

/-!
# Stacks 08U8: morphisms fitting into the cube are lifts of the reduced diagram

Let `D` be the diagram of the four ideal rows of **Stacks 08UA** attached to a commutative cube
of ringed spaces of **Stacks 08U9** whose horizontal arrows are first order thickenings, and let
`D.toFirstOrderLiftDiagram` be the source's reduction of it to the space `X₂`. The proof of
**Stacks 08U8** begins with the bijection between the morphisms of ringed spaces `X'₂ ⟶ X'₁`
fitting into the cube compatibly with `ν` and the homomorphisms `g⁻¹𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of
sheaves of rings on `X₂` fitting into the reduced diagram. This file constructs it.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.liftEquiv`: **the bijection
  of the source's proof** between `D.Lifts` and the lifts of the reduced diagram.

## Implementation notes

A morphism `φ : X'₂ ⟶ X'₁` with `i₂ ≫ φ = g ≫ i₁` has underlying continuous map
`k₂ ≫ g ≫ i₁`, where `k₂` is the inverse of the homeomorphism underlying `i₂`, so it is the same
thing as its comorphism `𝒪_{X'₁} ⟶ (k₂ ≫ g ≫ i₁)_*𝒪_{X'₂}`. Transposing along the equivalence
`k₁_* ⊣ i₁_*` given by the homeomorphism underlying `i₁`, and then along `g⁻¹ ⊣ g_*`, identifies
these comorphisms with the homomorphisms `g⁻¹k₁_*𝒪_{X'₁} ⟶ k₂_*𝒪_{X'₂}`. Each of the three
conditions on `φ` is then read off one of the three conditions on a lift by transposing back:
the face `i₂ ≫ φ = g ≫ i₁` is the compatibility with the reductions, the face
`φ ≫ f'₁ = f'₂ ≫ h'` is the compatibility with the thickened bases, and the compatibility with
`ν` is the compatibility with the ideal modules.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Deformation.ToposThickening
open AlgebraicGeometry.SheafOfModules (inverseImageModule)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- Cancelling a restriction between two equal opens. -/
theorem presheaf_eq_of_map_eq {Z : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} Z)
    {A B T : Opens Z} (hAT : A ≤ T) (f : op A ⟶ op T) (g : op B ⟶ op T) (hAB : A ≤ B)
    (x : F.obj (op A)) (y : F.obj (op B)) (h : F.map f x = F.map g y) :
    x = F.map (homOfLE hAB).op y := by
  have e : x = F.map (homOfLE hAT).op (F.map f x) := by
    rw [presheaf_map_map_apply, presheaf_map_congr F _ (𝟙 _), F.map_id]
    rfl
  rw [e, h, presheaf_map_map_apply]
  exact presheaf_map_congr _ _ _ _

/-- An endomorphism restriction of a presheaf of commutative rings on a space is the identity. -/
theorem presheaf_map_endo {Z : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} Z) {U : (Opens Z)ᵒᵖ}
    (f : U ⟶ U) (x : F.obj U) : F.map f x = x := by
  rw [presheaf_map_congr F f (𝟙 U), F.map_id]
  rfl

/-- Naturality of the comorphism of a morphism of ringed spaces, on sections. -/
theorem c_naturality_apply {A B : RingedSpace.{u, u}} (α : A ⟶ B) {U V : (Opens B.carrier)ᵒᵖ}
    (f : U ⟶ V) (y : B.presheaf.obj U) :
    α.hom.c.app V (B.presheaf.map f y) =
      A.presheaf.map ((Opens.map α.hom.base).op.map f) (α.hom.c.app U y) :=
  congrArg (fun k => k y) (α.hom.c.naturality f)

section HomeoAdj

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X') (hi : IsThickening i)
  (𝒢 : TopCat.Presheaf CommRingCat.{u} X.carrier)

/-- Transposition of a morphism `𝒪_{X'} ⟶ i_*𝒢` along the homeomorphism underlying a
thickening: the morphism `k_*𝒪_{X'} ⟶ 𝒢`, on an open `V` of `X` the given morphism on `k⁻¹V`
followed by the identification of `i⁻¹k⁻¹V` with `V`. -/
def homeoTranspose
    (c : X'.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} i.hom.base).obj 𝒢) :
    (TopCat.Presheaf.pushforward CommRingCat.{u} (thickeningHomeo i hi).inv).obj X'.presheaf ⟶
      𝒢 where
  app V := c.app (op ((Opens.map (thickeningHomeo i hi).inv).obj V.unop)) ≫
    𝒢.map (homOfLE (thickening_preimage_preimage i hi V.unop).ge).op
  naturality U V f := by
    change X'.presheaf.map _ ≫ c.app _ ≫ 𝒢.map _ = (c.app _ ≫ 𝒢.map _) ≫ 𝒢.map f
    rw [← Category.assoc, c.naturality, Category.assoc, Category.assoc]
    change c.app _ ≫ 𝒢.map _ ≫ 𝒢.map _ = c.app _ ≫ 𝒢.map _ ≫ 𝒢.map f
    rw [← 𝒢.map_comp, ← 𝒢.map_comp]
    rfl

/-- The inverse of `homeoTranspose`. -/
def homeoUntranspose
    (a : (TopCat.Presheaf.pushforward CommRingCat.{u} (thickeningHomeo i hi).inv).obj X'.presheaf ⟶
      𝒢) :
    X'.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} i.hom.base).obj 𝒢 where
  app W := X'.presheaf.map (homOfLE (thickening_preimage_preimage' i hi W.unop).le).op ≫
    a.app (op ((Opens.map i.hom.base).obj W.unop))
  naturality U V f := by
    change X'.presheaf.map f ≫ X'.presheaf.map _ ≫ a.app _ = (X'.presheaf.map _ ≫ a.app _) ≫ 𝒢.map _
    rw [Category.assoc, ← a.naturality, ← Category.assoc, ← Category.assoc]
    change (X'.presheaf.map f ≫ X'.presheaf.map _) ≫ a.app _ =
      (X'.presheaf.map _ ≫ X'.presheaf.map _) ≫ a.app _
    rw [← X'.presheaf.map_comp, ← X'.presheaf.map_comp]
    rfl

/-- **Transposition along the homeomorphism underlying a thickening**, as an equivalence. -/
def homeoTransposeEquiv :
    (X'.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} i.hom.base).obj 𝒢) ≃
      ((TopCat.Presheaf.pushforward CommRingCat.{u} (thickeningHomeo i hi).inv).obj X'.presheaf ⟶
        𝒢) where
  toFun := homeoTranspose i hi 𝒢
  invFun := homeoUntranspose i hi 𝒢
  left_inv c := by
    ext W x
    change 𝒢.map _ (c.app _ (X'.presheaf.map _ x)) = c.app (op W) x
    rw [← ConcreteCategory.comp_apply (X'.presheaf.map _), c.naturality,
      ConcreteCategory.comp_apply]
    change 𝒢.map _ (𝒢.map _ (c.app (op W) x)) = c.app (op W) x
    rw [presheaf_map_map_apply, presheaf_map_endo]
  right_inv a := by
    ext V x
    change 𝒢.map _ (a.app _ (X'.presheaf.map _ x)) = a.app (op V) x
    rw [← ConcreteCategory.comp_apply (X'.presheaf.map _)]
    change 𝒢.map _ ((((TopCat.Presheaf.pushforward CommRingCat.{u} (thickeningHomeo i hi).inv).obj
      X'.presheaf).map (homOfLE (thickening_preimage_preimage i hi V).le).op ≫ a.app _) x) = _
    rw [a.naturality, ConcreteCategory.comp_apply, presheaf_map_map_apply, presheaf_map_endo]

/-- `homeoTranspose` is natural in the target. -/
theorem homeoTranspose_comp {𝒢' : TopCat.Presheaf CommRingCat.{u} X.carrier}
    (c : X'.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} i.hom.base).obj 𝒢)
    (φ : 𝒢 ⟶ 𝒢') :
    homeoTranspose i hi 𝒢 c ≫ φ = homeoTranspose i hi 𝒢'
      (c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} i.hom.base).map φ) := by
  ext V x
  change φ.app _ (𝒢.map _ (c.app _ x)) = 𝒢'.map _ (φ.app _ (c.app _ x))
  rw [← ConcreteCategory.comp_apply (𝒢.map _), φ.naturality, ConcreteCategory.comp_apply]

/-- `homeoTranspose` on sections. -/
theorem homeoTranspose_apply
    (c : X'.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} i.hom.base).obj 𝒢)
    (V : Opens X.carrier)
    (x : X'.presheaf.obj (op ((Opens.map (thickeningHomeo i hi).inv).obj V))) :
    (homeoTranspose i hi 𝒢 c).app (op V) x =
      𝒢.map (homOfLE (thickening_preimage_preimage i hi V).ge).op
        (c.app (op ((Opens.map (thickeningHomeo i hi).inv).obj V)) x) := rfl

end HomeoAdj

section Ext

/-- **Morphisms of ringed spaces with the same underlying map are equal when their comorphisms
agree on sections**, up to the restriction between the two equal preimages. -/
theorem ringedSpaceHom_ext_of_app {A B : RingedSpace.{u, u}} {α β : A ⟶ B}
    (hb : α.hom.base = β.hom.base)
    (h : ∀ (W : Opens B.carrier) (y : B.presheaf.obj (op W)),
      α.hom.c.app (op W) y = A.presheaf.map (homOfLE (by rw [hb])).op (β.hom.c.app (op W) y)) :
    α = β := by
  obtain ⟨⟨ba, ca⟩⟩ := α
  obtain ⟨⟨bb, cb⟩⟩ := β
  change ba = bb at hb
  subst hb
  have hc : ca = cb := by
    ext W y
    refine (h W y).trans ?_
    rw [show (homOfLE (le_refl ((Opens.map ba).obj W))).op = 𝟙 _ from rfl, A.presheaf.map_id]
    rfl
  subst hc
  rfl

/-- The comorphisms of equal morphisms of ringed spaces agree on sections. -/
theorem ringedSpaceHom_c_apply_of_eq {A B : RingedSpace.{u, u}} {α β : A ⟶ B} (h : α = β)
    (W : Opens B.carrier) (y : B.presheaf.obj (op W))
    (hle : (Opens.map α.hom.base).obj W ≤ (Opens.map β.hom.base).obj W) :
    α.hom.c.app (op W) y = A.presheaf.map (homOfLE hle).op (β.hom.c.app (op W) y) := by
  subst h
  rw [show (homOfLE hle).op = 𝟙 _ from rfl, A.presheaf.map_id]
  rfl

end Ext

/-- A restriction along an equality of opens can be moved to the other side of an equation. -/
theorem presheaf_map_eq_iff {Z : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} Z) {A B : Opens Z}
    (h₁ : B ≤ A) (h₂ : A ≤ B) (x : F.obj (op A)) (y : F.obj (op B)) :
    F.map (homOfLE h₁).op x = y ↔ x = F.map (homOfLE h₂).op y := by
  constructor <;> rintro rfl <;> rw [presheaf_map_map_apply, presheaf_map_endo]

/-- Two iterated restrictions of a section are one restriction between the same opens. -/
private theorem presheaf_map_map_eq {Z : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} Z)
    {U V W : (Opens Z)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W) (x : F.obj U) :
    F.map g (F.map f x) = F.map h x :=
  (presheaf_map_map_apply F f g x).trans (presheaf_map_congr F _ _ x)

/-- The comorphisms of equal morphisms of ringed spaces agree on sections, after any restrictions
to a common open. -/
private theorem c_apply_map_eq_of_eq {A B : RingedSpace.{u, u}} {α β : A ⟶ B} (h : α = β)
    (W : Opens B.carrier) (y : B.presheaf.obj (op W)) {P : (Opens A.carrier)ᵒᵖ}
    (k₁ : op ((Opens.map α.hom.base).obj W) ⟶ P) (k₂ : op ((Opens.map β.hom.base).obj W) ⟶ P) :
    A.presheaf.map k₁ (α.hom.c.app (op W) y) = A.presheaf.map k₂ (β.hom.c.app (op W) y) := by
  subst h
  exact presheaf_map_congr _ _ _ _

/-- A morphism of sheaves of rings is determined by, and determines, its values on sections. -/
private theorem sheafHom_eq_iff_apply {Z : TopCat.{u}}
    {F G : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}} {f g : F ⟶ G}
    {P Q : ∀ V : Opens Z, F.obj.obj (op V) → G.obj.obj (op V)}
    (hl : ∀ V x, f.hom.app (op V) x = P V x) (hr : ∀ V x, g.hom.app (op V) x = Q V x) :
    f = g ↔ ∀ V x, P V x = Q V x :=
  ⟨fun h V x => (hl V x).symm.trans ((congrArg (fun k => k.hom.app (op V) x) h).trans (hr V x)),
    fun h => sheafHom_ext _ fun V x => by
      obtain ⟨V⟩ := V
      exact (hl V x).trans ((h V x).trans (hr V x).symm)⟩

namespace DeformationIdealDiagram

variable (D : DeformationIdealDiagram.{u})

/-- The underlying continuous map `k₂ ≫ g ≫ i₁ : X'₂ ⟶ X'₁` of every morphism fitting into the
cube. -/
abbrev liftBase : D.cube.X₂'.carrier ⟶ D.cube.X₁'.carrier :=
  (thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv ≫ D.cube.g.hom.base ≫
    D.cube.i₁.hom.base

/-- **The homomorphisms of the reduced diagram are the comorphisms over `k₂ ≫ g ≫ i₁`**: the
transposition along `g⁻¹ ⊣ g_*` and along the homeomorphism underlying `i₁`. -/
def liftHomEquiv : (D.toFirstOrderLiftDiagram.front.O' ⟶ D.toFirstOrderLiftDiagram.back.O') ≃
    (D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :=
  ((ringAdjunction D.cube.g.hom.base).homEquiv _ _).trans
    (Sheaf.homEquiv.trans (homeoTransposeEquiv D.cube.i₁ D.i₁_firstOrder.isThickening _).symm)

/-- The morphism of ringed spaces `X'₂ ⟶ X'₁` over `k₂ ≫ g ≫ i₁` with a given comorphism. -/
def liftMor (c : D.cube.X₁'.presheaf ⟶
    (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :
    D.cube.X₂' ⟶ D.cube.X₁' :=
  ⟨⟨D.liftBase, c⟩⟩

/-- The homomorphism attached to a comorphism, on induced sections. -/
theorem liftHomEquiv_symm_ringUnit (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf)
    (V : Opens D.cube.X₁.carrier)
    (x : (thickenedRing D.cube.i₁ D.i₁_firstOrder.isThickening).obj.obj (op V)) :
    (D.liftHomEquiv.symm c).hom.app (op ((Opens.map D.cube.g.hom.base).obj V))
        (ringUnit D.cube.g.hom.base _ V x) =
      D.cube.X₂'.presheaf.map (homOfLE (opensMap_le (thickeningHomeo D.cube.i₂
        D.i₂_firstOrder.isThickening).inv (opensMap_le D.cube.g.hom.base
          (thickening_preimage_preimage D.cube.i₁ D.i₁_firstOrder.isThickening V).ge))).op
        (c.app (op ((Opens.map (thickeningHomeo D.cube.i₁ D.i₁_firstOrder.isThickening).inv).obj V))
          x) :=
  ringAdjunction_homEquiv_symm_ringUnit D.cube.g.hom.base _ _ V x

/-- The underlying map of every morphism over `k₂ ≫ g ≫ i₁`, composed with `i₂`, is
`g ≫ i₁`. -/
theorem i₂_liftBase : D.cube.i₂.hom.base ≫ D.liftBase = D.cube.g.hom.base ≫ D.cube.i₁.hom.base := by
  rw [liftBase, ← Category.assoc]
  change ((thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).hom ≫
    (thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv) ≫ _ = _
  rw [Iso.hom_inv_id, Category.id_comp]

/-- The transpose along `g` of the homomorphism attached to a comorphism `c`: the comorphism
transposed along the homeomorphism underlying `i₁`. -/
def liftTranspose (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :
    thickenedRing D.cube.i₁ D.i₁_firstOrder.isThickening ⟶
      (ringPushforward D.cube.g.hom.base).obj
        (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening) :=
  ObjectProperty.homMk (homeoTranspose D.cube.i₁ D.i₁_firstOrder.isThickening _ c)

/-- `liftTranspose` on sections. -/
theorem liftTranspose_apply (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf)
    (V : Opens D.cube.X₁.carrier)
    (x : D.cube.X₁'.presheaf.obj (op ((Opens.map (thickeningHomeo D.cube.i₁
      D.i₁_firstOrder.isThickening).inv).obj V))) :
    (D.liftTranspose c).hom.app (op V) x =
      D.cube.X₂'.presheaf.map (homOfLE (opensMap_le (thickeningHomeo D.cube.i₂
        D.i₂_firstOrder.isThickening).inv (opensMap_le D.cube.g.hom.base
          (thickening_preimage_preimage D.cube.i₁ D.i₁_firstOrder.isThickening V).ge))).op
        (c.app (op ((Opens.map (thickeningHomeo D.cube.i₁ D.i₁_firstOrder.isThickening).inv).obj V))
          x) := rfl

/-- The transpose of a homomorphism attached to a comorphism. -/
theorem homEquiv_liftHomEquiv_symm (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :
    (ringAdjunction D.cube.g.hom.base).homEquiv _ _ (D.liftHomEquiv.symm c) = D.liftTranspose c :=
  Equiv.apply_symm_apply _ _

/-- The first preimage appearing in the face `i₂ ≫ φ = g ≫ i₁`. -/
theorem face_le₁ (V : Opens D.cube.X₁.carrier) :
    (Opens.map D.cube.g.hom.base).obj V ≤ (Opens.map D.cube.i₂.hom.base).obj
      ((Opens.map D.liftBase).obj ((Opens.map (thickeningHomeo D.cube.i₁
        D.i₁_firstOrder.isThickening).inv).obj V)) := by
  intro z hz
  change (thickeningHomeo D.cube.i₁ D.i₁_firstOrder.isThickening).inv (D.cube.i₁.hom.base
    (D.cube.g.hom.base ((thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv
      (D.cube.i₂.hom.base z)))) ∈ V
  rw [thickeningHomeo_hom_inv_apply, thickeningHomeo_hom_inv_apply]
  exact hz

/-- The second preimage appearing in the face `i₂ ≫ φ = g ≫ i₁`. -/
theorem face_le₂ (V : Opens D.cube.X₁.carrier) :
    (Opens.map D.cube.g.hom.base).obj V ≤ (Opens.map D.cube.g.hom.base).obj
      ((Opens.map D.cube.i₁.hom.base).obj ((Opens.map (thickeningHomeo D.cube.i₁
        D.i₁_firstOrder.isThickening).inv).obj V)) :=
  opensMap_le _ (thickening_preimage_preimage D.cube.i₁ D.i₁_firstOrder.isThickening V).ge

/-- The two preimages of an open of `X'₁` along `i₂ ≫ φ` and `g ≫ i₁`. -/
theorem face_le₃ (W : Opens D.cube.X₁'.carrier) :
    (Opens.map D.cube.i₂.hom.base).obj ((Opens.map D.liftBase).obj W) ≤
      (Opens.map D.cube.g.hom.base).obj ((Opens.map D.cube.i₁.hom.base).obj W) := by
  intro z hz
  change D.cube.i₁.hom.base (D.cube.g.hom.base ((thickeningHomeo D.cube.i₂
    D.i₂_firstOrder.isThickening).inv (D.cube.i₂.hom.base z))) ∈ W at hz
  rwa [thickeningHomeo_hom_inv_apply] at hz

/-- The sectionwise form of the face `i₂ ≫ φ = g ≫ i₁`, on the opens `k₁⁻¹V`. -/
def ReductionFace (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) : Prop :=
  ∀ (V : Opens D.cube.X₁.carrier)
    (x : D.cube.X₁'.presheaf.obj (op ((Opens.map (thickeningHomeo D.cube.i₁
      D.i₁_firstOrder.isThickening).inv).obj V))),
    D.cube.X₂.presheaf.map (homOfLE (D.face_le₁ V)).op
        (D.cube.i₂.hom.c.app _ (c.app _ x)) =
      D.cube.X₂.presheaf.map (homOfLE (D.face_le₂ V)).op
        (D.cube.g.hom.c.app _ (D.cube.i₁.hom.c.app _ x))

/-- The compatibility of the lift with the reductions, on sections. -/
theorem reduction_comm_iff_face (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :
    D.liftHomEquiv.symm c ≫ D.toFirstOrderLiftDiagram.back.reduction =
        D.toFirstOrderLiftDiagram.front.reduction ≫ D.toFirstOrderLiftDiagram.g ↔
      D.ReductionFace c := by
  let r₂ := thickeningReduction D.cube.i₂ D.i₂_firstOrder.isThickening
  let r₁ := thickeningReduction D.cube.i₁ D.i₁_firstOrder.isThickening
  have key1 : (ringAdjunction D.cube.g.hom.base).homEquiv _ _
      (D.liftHomEquiv.symm c ≫ D.toFirstOrderLiftDiagram.back.reduction) =
      D.liftTranspose c ≫ (ringPushforward D.cube.g.hom.base).map r₂ :=
    ((ringAdjunction D.cube.g.hom.base).homEquiv_naturality_right
      (D.liftHomEquiv.symm c : (ringPullback D.cube.g.hom.base).obj D.frontLayer.O' ⟶ _) r₂).trans
      (congrArg (fun k => k ≫ (ringPushforward D.cube.g.hom.base).map r₂)
        (D.homEquiv_liftHomEquiv_symm c))
  have key2 : (ringAdjunction D.cube.g.hom.base).homEquiv _ _
      (D.toFirstOrderLiftDiagram.front.reduction ≫ D.toFirstOrderLiftDiagram.g) =
      r₁ ≫ comorphism D.cube.g := by
    change (ringAdjunction D.cube.g.hom.base).homEquiv _ _
      ((ringPullback D.cube.g.hom.base).map r₁ ≫ structureMap D.cube.g) = _
    rw [Adjunction.homEquiv_naturality_left, homEquiv_structureMap]
  have hiff : D.liftHomEquiv.symm c ≫ D.toFirstOrderLiftDiagram.back.reduction =
        D.toFirstOrderLiftDiagram.front.reduction ≫ D.toFirstOrderLiftDiagram.g ↔
      D.liftTranspose c ≫ (ringPushforward D.cube.g.hom.base).map r₂ = r₁ ≫ comorphism D.cube.g :=
    ⟨fun h => key1.symm.trans ((congrArg _ h).trans key2),
      fun h => ((ringAdjunction D.cube.g.hom.base).homEquiv _ _).injective
        (key1.trans (h.trans key2.symm))⟩
  have hl : ∀ (V : Opens D.cube.X₁.carrier) x,
      (D.liftTranspose c ≫ (ringPushforward D.cube.g.hom.base).map r₂).hom.app (op V) x =
      D.cube.X₂.presheaf.map (homOfLE (D.face_le₁ V)).op
        (D.cube.i₂.hom.c.app _ (c.app _ x)) := by
    intro V x
    change D.cube.X₂.presheaf.map _ (D.cube.i₂.hom.c.app _ (D.cube.X₂'.presheaf.map _ _)) = _
    refine (congrArg (fun y => D.cube.X₂.presheaf.map _ y) (c_naturality_apply _ _ _)).trans ?_
    exact presheaf_map_map_eq _ _ _ _ _
  have hr : ∀ (V : Opens D.cube.X₁.carrier) x, (r₁ ≫ comorphism D.cube.g).hom.app (op V) x =
      D.cube.X₂.presheaf.map (homOfLE (D.face_le₂ V)).op
        (D.cube.g.hom.c.app _ (D.cube.i₁.hom.c.app _ x)) := by
    intro V x
    change D.cube.g.hom.c.app _ (D.cube.X₁.presheaf.map _ _) = _
    exact c_naturality_apply _ _ _
  rw [hiff]
  exact sheafHom_eq_iff_apply hl hr

/-- **The face `i₂ ≫ φ = g ≫ i₁` is the compatibility of the lift with the reductions.** -/
theorem reduction_comm_iff (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :
    D.liftHomEquiv.symm c ≫ D.toFirstOrderLiftDiagram.back.reduction =
        D.toFirstOrderLiftDiagram.front.reduction ≫ D.toFirstOrderLiftDiagram.g ↔
      D.cube.i₂ ≫ D.liftMor c = D.cube.g ≫ D.cube.i₁ := by
  rw [reduction_comm_iff_face]
  constructor
  · intro h
    refine ringedSpaceHom_ext_of_app D.i₂_liftBase fun W y => ?_
    have hW := thickening_preimage_preimage' D.cube.i₁ D.i₁_firstOrder.isThickening W
    have e := h ((Opens.map D.cube.i₁.hom.base).obj W)
      (D.cube.X₁'.presheaf.map (homOfLE hW.le).op y)
    rw [← ConcreteCategory.comp_apply (D.cube.X₁'.presheaf.map _), c.naturality,
      ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply (D.cube.X₁'.presheaf.map _),
      D.cube.i₁.hom.c.naturality, ConcreteCategory.comp_apply] at e
    change D.cube.X₂.presheaf.map _ (D.cube.i₂.hom.c.app _ (D.cube.X₂'.presheaf.map _ _)) =
      D.cube.X₂.presheaf.map _ (D.cube.g.hom.c.app _ (D.cube.X₁.presheaf.map _ _)) at e
    rw [← ConcreteCategory.comp_apply (D.cube.X₂'.presheaf.map _), D.cube.i₂.hom.c.naturality,
      ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (D.cube.X₁.presheaf.map _),
      D.cube.g.hom.c.naturality, ConcreteCategory.comp_apply] at e
    change D.cube.X₂.presheaf.map _ (D.cube.X₂.presheaf.map _ _) =
      D.cube.X₂.presheaf.map _ (D.cube.X₂.presheaf.map _ _) at e
    rw [presheaf_map_map_apply, presheaf_map_map_apply, presheaf_map_endo] at e
    exact (presheaf_map_eq_iff _ _ (D.face_le₃ W) _ _).1 e
  · intro h V x
    exact c_apply_map_eq_of_eq h _ x _ _

/-- The underlying maps of the two sides of the face `φ ≫ f'₁ = f'₂ ≫ h'` agree. -/
theorem liftBase_f₁' :
    D.liftBase ≫ D.cube.f₁'.hom.base = D.cube.f₂'.hom.base ≫ D.cube.h'.hom.base := by
  have h1 := congrArg (fun k => k.hom.base) D.cube.front_comm
  have h2 := congrArg (fun k => k.hom.base) D.cube.back_comm
  have h3 := congrArg (fun k => k.hom.base) D.cube.base_comm
  dsimp only [SheafedSpace.comp_hom_base] at h1 h2 h3
  rw [liftBase, Category.assoc, Category.assoc, h1, ← Category.assoc D.cube.g.hom.base,
    ← D.source_comm_base, Category.assoc, h3, ← Category.assoc D.cube.f₂.hom.base, ← h2,
    ← Category.assoc, ← Category.assoc]
  change ((thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv ≫
    (thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).hom ≫ _) ≫ _ = _
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The two preimages appearing in the face `φ ≫ f'₁ = f'₂ ≫ h'`. -/
theorem baseFace_le₁ (V : Opens D.cube.S₁.carrier) :
    (Opens.map (thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv).obj
        ((Opens.map D.cube.g.hom.base).obj ((Opens.map D.cube.f₁.hom.base).obj V)) ≤
      (Opens.map D.liftBase).obj ((Opens.map D.cube.f₁'.hom.base).obj
        ((Opens.map (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv).obj V)) := by
  intro z hz
  change (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv (D.cube.f₁'.hom.base
    (D.cube.i₁.hom.base (D.cube.g.hom.base ((thickeningHomeo D.cube.i₂
      D.i₂_firstOrder.isThickening).inv z)))) ∈ V
  rw [thickening_comm_apply D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm,
    thickeningHomeo_hom_inv_apply]
  exact hz

/-- The second preimage appearing in the face `φ ≫ f'₁ = f'₂ ≫ h'`. -/
theorem baseFace_le₂ (V : Opens D.cube.S₁.carrier) :
    (Opens.map (thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv).obj
        ((Opens.map D.cube.g.hom.base).obj ((Opens.map D.cube.f₁.hom.base).obj V)) ≤
      (Opens.map D.cube.f₂'.hom.base).obj ((Opens.map D.cube.h'.hom.base).obj
        ((Opens.map (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv).obj V)) := by
  intro z hz
  have e := ConcreteCategory.congr_hom D.liftBase_f₁' z
  change D.cube.f₁'.hom.base (D.cube.i₁.hom.base (D.cube.g.hom.base ((thickeningHomeo D.cube.i₂
    D.i₂_firstOrder.isThickening).inv z))) = D.cube.h'.hom.base (D.cube.f₂'.hom.base z) at e
  change (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv
    (D.cube.h'.hom.base (D.cube.f₂'.hom.base z)) ∈ V
  rw [← e]
  exact D.baseFace_le₁ V hz

/-- The comparison `gB'` followed by the back structure map, on sections: the comorphism of
`f'₂ ≫ h'`, restricted. -/
theorem frontBaseToBack_apply (V : Opens D.cube.S₁.carrier)
    (w : D.cube.S₁'.presheaf.obj (op ((Opens.map (thickeningHomeo D.cube.t₁
      D.t₁_firstOrder.isThickening).inv).obj V))) :
    D.frontBaseToBack.hom.app (op V) w =
      D.cube.X₂'.presheaf.map (homOfLE (D.baseFace_le₂ V)).op
        (D.cube.f₂'.hom.c.app _ (D.cube.h'.hom.c.app _ w)) := by
  change (thickeningStructureMap D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
      D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening).hom.app _
        (D.gB'Transpose.hom.app (op V) w) = _
  refine (congrArg (fun x => (thickeningStructureMap D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂'
    D.cube.back_comm D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening).hom.app _ x)
      (D.gB'Transpose_apply V w)).trans ?_
  refine (sheafHom_naturality_apply _ _ _ _).trans ?_
  refine (congrArg (fun x => (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening).obj.map _ x)
    (ringAdjunction_homEquiv_symm_ringUnit _ _ _ _ _)).trans ?_
  refine (congrArg (fun x => (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening).obj.map _ x)
    (thickeningStructure_apply D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
      D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening
      ((Opens.map D.cube.h.hom.base).obj V) _)).trans ?_
  refine (congrArg (fun x => (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening).obj.map _
    (D.cube.X₂'.presheaf.map _ (D.cube.f₂'.hom.c.app _ x)))
      (thickeningStructure_apply D.cube.t₂ D.cube.t₁ D.cube.h D.cube.h' D.cube.base_comm.symm
        D.t₂_firstOrder.isThickening D.t₁_firstOrder.isThickening V w)).trans ?_
  refine (congrArg (fun x => (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening).obj.map _
    (D.cube.X₂'.presheaf.map _ x)) (c_naturality_apply _ _ _)).trans ?_
  change D.cube.X₂'.presheaf.map _ (D.cube.X₂'.presheaf.map _ (D.cube.X₂'.presheaf.map _ _)) = _
  rw [presheaf_map_map_apply, presheaf_map_map_apply]
  exact presheaf_map_congr _ _ _ _

/-- The sectionwise form of the face `φ ≫ f'₁ = f'₂ ≫ h'`, on the opens `k⁻¹V`. -/
def BaseFace (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) : Prop :=
  ∀ (V : Opens D.cube.S₁.carrier)
    (w : D.cube.S₁'.presheaf.obj (op ((Opens.map (thickeningHomeo D.cube.t₁
      D.t₁_firstOrder.isThickening).inv).obj V))),
    D.cube.X₂'.presheaf.map (homOfLE (D.baseFace_le₁ V)).op
        (c.app _ (D.cube.f₁'.hom.c.app _ w)) =
      D.cube.X₂'.presheaf.map (homOfLE (D.baseFace_le₂ V)).op
        (D.cube.f₂'.hom.c.app _ (D.cube.h'.hom.c.app _ w))

/-- The two preimages of an open of `S'₁` along `φ ≫ f'₁` and `f'₂ ≫ h'`. -/
theorem baseFace_le₃ (W : Opens D.cube.S₁'.carrier) :
    (Opens.map D.liftBase).obj ((Opens.map D.cube.f₁'.hom.base).obj W) ≤
      (Opens.map D.cube.f₂'.hom.base).obj ((Opens.map D.cube.h'.hom.base).obj W) := by
  intro z hz
  have e := ConcreteCategory.congr_hom D.liftBase_f₁' z
  change D.cube.f₁'.hom.base (D.liftBase z) = D.cube.h'.hom.base (D.cube.f₂'.hom.base z) at e
  change D.cube.h'.hom.base (D.cube.f₂'.hom.base z) ∈ W
  rw [← e]
  exact hz

/-- The preimage of an open of `S'₁` along `φ ≫ f'₁` lies in the preimage of its preimage in
`S₁`. -/
theorem baseFace_le₄ (W : Opens D.cube.S₁'.carrier) :
    (Opens.map D.liftBase).obj ((Opens.map D.cube.f₁'.hom.base).obj W) ≤
      (Opens.map (thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv).obj
        ((Opens.map D.cube.g.hom.base).obj ((Opens.map D.cube.f₁.hom.base).obj
          ((Opens.map D.cube.t₁.hom.base).obj W))) := by
  intro z hz
  change D.cube.f₁'.hom.base (D.cube.i₁.hom.base (D.cube.g.hom.base ((thickeningHomeo D.cube.i₂
    D.i₂_firstOrder.isThickening).inv z))) ∈ W at hz
  change D.cube.t₁.hom.base (D.cube.f₁.hom.base (D.cube.g.hom.base ((thickeningHomeo D.cube.i₂
      D.i₂_firstOrder.isThickening).inv z))) ∈ W
  rw [← thickening_comm_apply D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm]
  exact hz

/-- **The face `φ ≫ f'₁ = f'₂ ≫ h'`, on sections, is the compatibility of the lift with the
thickened bases.** -/
theorem base_comm_iff_face (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :
    D.toFirstOrderLiftDiagram.front.f' ≫ D.liftHomEquiv.symm c =
        D.toFirstOrderLiftDiagram.gB' ≫ D.toFirstOrderLiftDiagram.back.f' ↔
      D.BaseFace c := by
  let str₁ := thickeningStructureMap D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
    D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening
  have key1 : (ringAdjunction D.cube.g.hom.base).homEquiv _ _
      (D.toFirstOrderLiftDiagram.front.f' ≫ D.liftHomEquiv.symm c) = str₁ ≫ D.liftTranspose c :=
    ((ringAdjunction D.cube.g.hom.base).homEquiv_naturality_left str₁
      (D.liftHomEquiv.symm c : (ringPullback D.cube.g.hom.base).obj D.frontLayer.O' ⟶ _)).trans
      (congrArg (fun k => str₁ ≫ k) (D.homEquiv_liftHomEquiv_symm c))
  have key2 : (ringAdjunction D.cube.f₁.hom.base).homEquiv _ _ (str₁ ≫ D.liftTranspose c) =
      thickeningStructure D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
        D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening ≫
      (ringPushforward D.cube.f₁.hom.base).map (D.liftTranspose c) := by
    rw [Adjunction.homEquiv_naturality_right]
    exact congrArg (fun k => k ≫ (ringPushforward D.cube.f₁.hom.base).map (D.liftTranspose c))
      (Equiv.apply_symm_apply _ _)
  have hiff : D.toFirstOrderLiftDiagram.front.f' ≫ D.liftHomEquiv.symm c =
        D.toFirstOrderLiftDiagram.gB' ≫ D.toFirstOrderLiftDiagram.back.f' ↔
      thickeningStructure D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
        D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening ≫
      (ringPushforward D.cube.f₁.hom.base).map (D.liftTranspose c) = D.frontBaseToBack :=
    ⟨fun h => key2.symm.trans ((congrArg _ (key1.symm.trans (congrArg _ h))).trans
        D.homEquiv_frontBaseToBack'),
      fun h => ((ringAdjunction D.cube.g.hom.base).homEquiv _ _).injective
        (key1.trans (((ringAdjunction D.cube.f₁.hom.base).homEquiv _ _).injective
          (key2.trans (h.trans D.homEquiv_frontBaseToBack'.symm))))⟩
  have hl : ∀ (V : Opens D.cube.S₁.carrier) w,
      (thickeningStructure D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
        D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening ≫
      (ringPushforward D.cube.f₁.hom.base).map (D.liftTranspose c)).hom.app (op V) w =
      D.cube.X₂'.presheaf.map (homOfLE (D.baseFace_le₁ V)).op
        (c.app _ (D.cube.f₁'.hom.c.app _ w)) := by
    intro V w
    refine (D.liftTranspose_apply c ((Opens.map D.cube.f₁.hom.base).obj V) _).trans ?_
    refine (congrArg (fun x => D.cube.X₂'.presheaf.map _ (c.app _ x))
      (thickeningStructure_apply D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
        D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening V w)).trans ?_
    refine (congrArg (fun x => D.cube.X₂'.presheaf.map _ x)
      (NatTrans.naturality_apply c (homOfLE (thickening_structure_le D.cube.i₁ D.cube.t₁ D.cube.f₁
        D.cube.f₁' D.cube.front_comm D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening
          V)).op (D.cube.f₁'.hom.c.app _ w))).trans ?_
    exact presheaf_map_map_eq _ _ _ _ _
  rw [hiff]
  exact sheafHom_eq_iff_apply hl D.frontBaseToBack_apply

/-- **The face `φ ≫ f'₁ = f'₂ ≫ h'` is the compatibility of the lift with the thickened
bases.** -/
theorem base_comm_iff (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :
    D.toFirstOrderLiftDiagram.front.f' ≫ D.liftHomEquiv.symm c =
        D.toFirstOrderLiftDiagram.gB' ≫ D.toFirstOrderLiftDiagram.back.f' ↔
      D.liftMor c ≫ D.cube.f₁' = D.cube.f₂' ≫ D.cube.h' := by
  rw [base_comm_iff_face]
  constructor
  · intro h
    refine ringedSpaceHom_ext_of_app D.liftBase_f₁' fun W y => ?_
    have hW := thickening_preimage_preimage' D.cube.t₁ D.t₁_firstOrder.isThickening W
    have e := h ((Opens.map D.cube.t₁.hom.base).obj W)
      (D.cube.S₁'.presheaf.map (homOfLE hW.le).op y)
    rw [c_naturality_apply D.cube.f₁', c_naturality_apply D.cube.h', NatTrans.naturality_apply c,
      c_naturality_apply D.cube.f₂'] at e
    change D.cube.X₂'.presheaf.map _ (D.cube.X₂'.presheaf.map _ _) =
      D.cube.X₂'.presheaf.map _ (D.cube.X₂'.presheaf.map _ _) at e
    rw [presheaf_map_map_apply, presheaf_map_map_apply] at e
    exact presheaf_eq_of_map_eq _ (D.baseFace_le₄ W) _ _ (D.baseFace_le₃ W) _ _ e
  · intro h V w
    exact c_apply_map_eq_of_eq h _ w _ _

/-- The identification of the ideal of `i₁` with `i₁,*𝒢₁`, on sections. -/
def kapp (W : Opens D.cube.X₁'.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.i₁).val.obj (op W)) :
    D.G₁.val.obj (op ((Opens.map D.cube.i₁.hom.base).obj W)) :=
  D.kernelIso₁.hom.val.app (op W) j

/-- The section of the ideal of `i₁` corresponding to a section of `i₁,*𝒢₁` maps to it. -/
theorem layerIdealIncl_kapp (W : Opens D.cube.X₁'.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.i₁).val.obj (op W)) :
    layerIdealIncl D.cube.i₁ D.G₁ D.kernelIso₁ W (D.kapp W j) = idealι D.cube.i₁ W j := by
  change idealι D.cube.i₁ W ((D.kernelIso₁.hom ≫ D.kernelIso₁.inv).val.app (op W) j) = _
  rw [Iso.hom_inv_id]
  rfl

/-- The transpose of the map of ideals that `ν` prescribes to a lift. -/
theorem doubleTranspose_frontIdealToModule_nu :
    doubleTranspose D.cube.g D.cube.i₁ ((modulePullback D.cube.g).map D.frontIdealToModule ≫ D.nu) =
      D.kernelIso₁.hom ≫ (modulePushforward D.cube.i₁).map D.nuTranspose := by
  rw [doubleTranspose, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  exact congrArg (fun k => k ≫ (modulePushforward D.cube.i₁).map D.nuTranspose)
    (Equiv.apply_symm_apply _ _)

/-- The sectionwise form of the compatibility of a morphism `φ : X'₂ ⟶ X'₁` with `ν`: on every
section `j` of the ideal of `i₁`, `φ^♯(j)` is the section of `𝒪_{X'₂}` corresponding to
`ν(j)`. -/
def NuFace (φ : D.cube.X₂' ⟶ D.cube.X₁') : Prop :=
  ∀ (W : Opens D.cube.X₁'.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.i₁).val.obj (op W))
    (hle : (Opens.map D.cube.i₂.hom.base).obj ((Opens.map φ.hom.base).obj W) ≤
      (Opens.map D.cube.g.hom.base).obj ((Opens.map D.cube.i₁.hom.base).obj W)),
    φ.hom.c.app (op W) (idealι D.cube.i₁ W j) =
      layerIdealIncl D.cube.i₂ D.G₂ D.kernelIso₂ ((Opens.map φ.hom.base).obj W)
        (mres D.G₂ hle (pushApp D.nuTranspose _ (D.kapp W j)))

/-- **The compatibility with `ν` of Stacks 08U8, on sections.** -/
theorem isLiftNu_iff (φ : D.cube.X₂' ⟶ D.cube.X₁') (h : D.cube.i₂ ≫ φ = D.cube.g ≫ D.cube.i₁) :
    ((D.liftSquare φ h).firstOrderIdealMap D.i₂_firstOrder D.i₁_firstOrder).1 ≫
        D.kernelIso₂.hom =
      (modulePushforward D.cube.i₂).map
        ((modulePullback D.cube.g).map D.frontIdealToModule ≫ D.nu) ↔ D.NuFace φ := by
  refine (MorphismOfThickenings.firstOrderIdealMap_eq_iff (D.liftSquare φ h) D.i₂_firstOrder
    D.i₁_firstOrder D.G₂ D.kernelIso₂
      ((modulePullback D.cube.g).map D.frontIdealToModule ≫ D.nu)).trans ?_
  have e : ∀ W j, dtApp D.cube.g D.cube.i₁
      ((modulePullback D.cube.g).map D.frontIdealToModule ≫ D.nu) W j =
      pushApp D.nuTranspose _ (D.kapp W j) := fun W j =>
    congrArg (fun k => k.val.app (op W) j) D.doubleTranspose_frontIdealToModule_nu
  exact ⟨fun H W j _ => (H W j).trans (congrArg (fun x => layerIdealIncl D.cube.i₂ D.G₂
      D.kernelIso₂ _ (mres D.G₂ _ x)) (e W j)),
    fun H W j => (H W j ((D.liftSquare φ h).preimage_le W)).trans (congrArg (fun x =>
      layerIdealIncl D.cube.i₂ D.G₂ D.kernelIso₂ _ (mres D.G₂ _ x)) (e W j)).symm⟩

/-- The sectionwise form of the compatibility of a lift with the ideal modules, on induced
sections. -/
def KernelFace (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) : Prop :=
  ∀ (V : Opens D.cube.X₁.carrier) (μ : D.G₁.val.obj (op V)),
    (D.liftTranspose c).hom.app (op V)
        (thickeningKernelInclusionApp D.cube.i₁ D.i₁_firstOrder.isThickening D.G₁ D.kernelIso₁
          V μ) =
      thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂ D.kernelIso₂
        ((Opens.map D.cube.g.hom.base).obj V) (pushApp D.nuTranspose V μ)

/-- The homomorphism attached to a comorphism, on induced sections, is its transpose. -/
theorem liftHomEquiv_symm_ringUnit' (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf)
    (V : Opens D.cube.X₁.carrier)
    (x : (thickenedRing D.cube.i₁ D.i₁_firstOrder.isThickening).obj.obj (op V)) :
    (D.liftHomEquiv.symm c).hom.app (op ((Opens.map D.cube.g.hom.base).obj V))
        (ringUnit D.cube.g.hom.base _ V x) = (D.liftTranspose c).hom.app (op V) x :=
  D.liftHomEquiv_symm_ringUnit c V x

/-- **The compatibility of a lift with the ideal modules is its compatibility on induced
sections.** -/
theorem kernel_comm_iff_face (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :
    (∀ (U : (Opens D.cube.X₂.carrier)ᵒᵖ) (m : D.toFirstOrderLiftDiagram.front.G.val.obj U),
      (D.liftHomEquiv.symm c).hom.app U (D.toFirstOrderLiftDiagram.front.incl m) =
        D.toFirstOrderLiftDiagram.back.incl (D.toFirstOrderLiftDiagram.nuSection m)) ↔
      D.KernelFace c := by
  let L₁ := D.frontLayer
  let g := D.cube.g.hom.base
  let hom := D.liftHomEquiv.symm c
  let O₂ := thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening
  constructor
  · intro h V μ
    have e := h (op ((Opens.map g).obj V)) (moduleUnit g L₁.O L₁.G V μ)
    refine Eq.trans ?_ (e.trans ?_)
    · refine (D.liftHomEquiv_symm_ringUnit' c V _).symm.trans ?_
      exact congrArg (fun x => hom.hom.app _ x)
        (LiftSquare.inverseImage_incl_moduleUnit g L₁ V μ).symm
    · exact congrArg (thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
        D.kernelIso₂ _) (D.nuInverseImage_moduleUnit V μ)
  · intro h U m
    obtain ⟨U⟩ := U
    refine ringSheaf_eq_of_locally_eq O₂ _ _ fun y hy => ?_
    obtain ⟨V, hV, μ, W, hyW, hWU, hWV, em, ei⟩ :=
      LiftSquare.exists_restrict_inverseImageKernelInclusion g L₁ m y hy
    refine ⟨W, hyW, hWU, ?_⟩
    have hl : O₂.obj.map (homOfLE hWU).op (hom.hom.app (op U)
        ((LiftSquare.inverseImageKernelInclusion g L₁).val.app (op U) m)) =
        O₂.obj.map (homOfLE hWV).op (thickeningKernelInclusionApp D.cube.i₂
          D.i₂_firstOrder.isThickening D.G₂ D.kernelIso₂ ((Opens.map g).obj V)
            (pushApp D.nuTranspose V μ)) := by
      refine (sheafHom_naturality_apply _ hom (homOfLE hWU).op _).symm.trans ?_
      refine (congrArg (fun x => hom.hom.app (op W) x) ei).trans ?_
      refine (sheafHom_naturality_apply _ hom (homOfLE hWV).op _).trans ?_
      refine congrArg (fun x => O₂.obj.map (homOfLE hWV).op x) ?_
      exact (D.liftHomEquiv_symm_ringUnit' c V _).trans (h V μ)
    refine hl.trans ?_
    have hr : thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
        D.kernelIso₂ W (mres D.G₂ hWU (D.nuInverseImage.val.app (op U) m)) =
        thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂ D.kernelIso₂
        W (mres D.G₂ hWV (pushApp D.nuTranspose V μ)) := by
      refine congrArg (thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
        D.kernelIso₂ W) ?_
      refine (mres_naturality _ D.nuInverseImage hWU m).symm.trans ?_
      refine (congrArg (fun x => D.nuInverseImage.val.app (op W) x) em).trans ?_
      refine (mres_naturality _ D.nuInverseImage hWV (moduleUnit g L₁.O L₁.G V μ)).trans ?_
      exact congrArg (mres D.G₂ hWV) (D.nuInverseImage_moduleUnit V _)
    refine (thickeningKernelInclusionApp_naturality D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
      D.kernelIso₂ hWV _).symm.trans ?_
    refine hr.symm.trans ?_
    exact thickeningKernelInclusionApp_naturality D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
      D.kernelIso₂ hWU _

/-- The identification of the ideal of `i₁` with `i₁,*𝒢₁` commutes with restriction. -/
theorem kapp_mres {W W' : Opens D.cube.X₁'.carrier} (h : W' ≤ W)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.i₁).val.obj (op W)) :
    D.kapp W' (mres _ h j) = mres D.G₁ (opensMap_le D.cube.i₁.hom.base h) (D.kapp W j) :=
  mres_naturality _ D.kernelIso₁.hom h j

/-- **The compatibility of a lift with the ideal modules is the compatibility with `ν` of the
morphism of ringed spaces it comes from.** -/
theorem kernelFace_iff_nuFace (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf) :
    D.KernelFace c ↔ D.NuFace (D.liftMor c) := by
  constructor
  · intro h W j hle
    have hW := thickening_preimage_preimage' D.cube.i₁ D.i₁_firstOrder.isThickening W
    have e := h ((Opens.map D.cube.i₁.hom.base).obj W) (D.kapp W j)
    have e1 : thickeningKernelInclusionApp D.cube.i₁ D.i₁_firstOrder.isThickening D.G₁
        D.kernelIso₁ ((Opens.map D.cube.i₁.hom.base).obj W) (D.kapp W j) =
        D.cube.X₁'.presheaf.map (homOfLE hW.le).op (idealι D.cube.i₁ W j) := by
      refine (thickeningKernelInclusionApp_apply _ _ _ _ _ _).trans ?_
      refine (congrArg (layerIdealIncl D.cube.i₁ D.G₁ D.kernelIso₁ _)
        (D.kapp_mres hW.le j).symm).trans ?_
      exact (D.layerIdealIncl_kapp _ _).trans (idealι_naturality D.cube.i₁ hW.le j)
    rw [e1, liftTranspose_apply, NatTrans.naturality_apply c] at e
    refine Eq.trans ?_ (e.trans (thickeningKernelInclusionApp_apply _ _ _ _ _ _))
    exact ((presheaf_map_map_apply D.cube.X₂'.presheaf _ _ _).trans
      (presheaf_map_endo D.cube.X₂'.presheaf _ _)).symm
  · intro h V μ
    have hV := thickening_preimage_preimage D.cube.i₁ D.i₁_firstOrder.isThickening V
    let W := (Opens.map (thickeningHomeo D.cube.i₁ D.i₁_firstOrder.isThickening).inv).obj V
    let j := D.kernelIso₁.inv.val.app (op W) (mres D.G₁ hV.le μ)
    have hj : D.kapp W j = mres D.G₁ hV.le μ :=
      congrArg (fun k => k.val.app (op W) (mres D.G₁ hV.le μ)) D.kernelIso₁.inv_hom_id
    have hι : thickeningKernelInclusionApp D.cube.i₁ D.i₁_firstOrder.isThickening D.G₁
        D.kernelIso₁ V μ = idealι D.cube.i₁ W j := rfl
    rw [hι, liftTranspose_apply]
    change D.cube.X₂'.presheaf.map _ ((D.liftMor c).hom.c.app (op W) (idealι D.cube.i₁ W j)) = _
    rw [h W j (D.face_le₃ W), hj, pushApp_mres]
    refine (layerIdealIncl_naturality D.cube.i₂ D.G₂ D.kernelIso₂ _ _).symm.trans ?_
    refine (congrArg (layerIdealIncl D.cube.i₂ D.G₂ D.kernelIso₂ _) ?_).trans
      (thickeningKernelInclusionApp_apply _ _ _ _ _ _).symm
    exact (mres_mres D.G₂ _ _ _).trans (mres_mres D.G₂ _ _ _)

/-- A morphism filling the face `i₂ ≫ φ = g ≫ i₁` has underlying map `k₂ ≫ g ≫ i₁`. -/
theorem base_eq_of_comm (φ : D.cube.X₂' ⟶ D.cube.X₁') (h : D.cube.i₂ ≫ φ = D.cube.g ≫ D.cube.i₁) :
    φ.hom.base = D.liftBase := by
  have hb := congrArg (fun k => k.hom.base) h
  change D.cube.i₂.hom.base ≫ φ.hom.base = D.cube.g.hom.base ≫ D.cube.i₁.hom.base at hb
  rw [liftBase, ← hb, ← Category.assoc]
  change φ.hom.base = ((thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv ≫
    (thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).hom) ≫ φ.hom.base
  rw [Iso.inv_hom_id, Category.id_comp]

/-- The comorphism of a morphism `X'₂ ⟶ X'₁` with underlying map `k₂ ≫ g ≫ i₁`, read over that
map. -/
def comorphOf (φ : D.cube.X₂' ⟶ D.cube.X₁') (hb : φ.hom.base = D.liftBase) :
    D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf :=
  φ.hom.c ≫ (TopCat.Presheaf.pushforwardEq hb D.cube.X₂'.presheaf).hom

/-- A morphism over `k₂ ≫ g ≫ i₁` is the morphism given by its comorphism. -/
theorem liftMor_comorphOf (φ : D.cube.X₂' ⟶ D.cube.X₁') (hb : φ.hom.base = D.liftBase) :
    D.liftMor (D.comorphOf φ hb) = φ := by
  refine ringedSpaceHom_ext_of_app hb.symm fun W y => ?_
  change (TopCat.Presheaf.pushforwardEq hb D.cube.X₂'.presheaf).hom.app (op W)
    (φ.hom.c.app (op W) y) = _
  rw [TopCat.Presheaf.pushforwardEq_hom_app]
  exact presheaf_map_congr _ _ _ _

/-- The comorphism of the morphism given by a comorphism is that comorphism. -/
theorem comorphOf_liftMor (c : D.cube.X₁'.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} D.liftBase).obj D.cube.X₂'.presheaf)
    (hb : (D.liftMor c).hom.base = D.liftBase) : D.comorphOf (D.liftMor c) hb = c := by
  ext W y
  change (TopCat.Presheaf.pushforwardEq hb D.cube.X₂'.presheaf).hom.app (op W) (c.app (op W) y) =
    c.app (op W) y
  rw [TopCat.Presheaf.pushforwardEq_hom_app]
  exact presheaf_map_endo _ _ _

/-- The lift of the reduced diagram attached to a morphism fitting into the cube compatibly
with `ν`. -/
def liftOfIsLift (φ : D.cube.X₂' ⟶ D.cube.X₁') (hφ : D.IsLift φ) :
    D.toFirstOrderLiftDiagram.Lift where
  hom := D.liftHomEquiv.symm (D.comorphOf φ (D.base_eq_of_comm φ hφ.1.1))
  reduction_app U x := congrArg (fun k => k.hom.app U x)
    ((D.reduction_comm_iff _).2 (by rw [liftMor_comorphOf]; exact hφ.1.1))
  base_app U t := congrArg (fun k => k.hom.app U t)
    ((D.base_comm_iff _).2 (by rw [liftMor_comorphOf]; exact hφ.1.2))
  kernel_comm := (D.kernel_comm_iff_face _).2 ((D.kernelFace_iff_nuFace _).2 (by
    rw [liftMor_comorphOf]
    obtain ⟨h, hν⟩ := hφ
    exact (D.isLiftNu_iff φ h.1).1 hν))

/-- The morphism fitting into the cube compatibly with `ν` attached to a lift of the reduced
diagram. -/
theorem isLift_liftMor (p : D.toFirstOrderLiftDiagram.Lift) :
    D.IsLift (D.liftMor (D.liftHomEquiv p.hom)) := by
  have hr := p.reduction_comm
  have hb := p.base_comm
  have hk := p.kernel_comm
  rw [← Equiv.symm_apply_apply D.liftHomEquiv p.hom] at hr hb hk
  have h1 := (D.reduction_comm_iff _).1 hr
  exact ⟨⟨h1, (D.base_comm_iff _).1 hb⟩, (D.isLiftNu_iff _ h1).2
    ((D.kernelFace_iff_nuFace _).1 ((D.kernel_comm_iff_face _).1 hk))⟩

/-- **Stacks Project, Tag 08U8, the bijection of the reduction to one site.** The morphisms of
ringed spaces `X'₂ ⟶ X'₁` fitting into the cube of Tag 08U9 compatibly with `ν` correspond
bijectively to the homomorphisms `g⁻¹𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of sheaves of rings on `X₂` fitting into
the reduced diagram `D.toFirstOrderLiftDiagram` compatibly with `ν`: a morphism `φ` has
underlying map `k₂ ≫ g ≫ i₁`, and its comorphism, transposed along the homeomorphism
underlying `i₁` and along `g⁻¹ ⊣ g_*`, is the homomorphism. The two faces of the cube left
open by the data correspond to the compatibilities with the reductions and with the thickened
bases, and the compatibility with `ν` of Tag 08U8 to the compatibility with the ideal
modules. -/
def liftEquiv : D.Lifts ≃ D.toFirstOrderLiftDiagram.Lift where
  toFun φ := D.liftOfIsLift φ.1 φ.2
  invFun p := ⟨D.liftMor (D.liftHomEquiv p.hom), D.isLift_liftMor p⟩
  left_inv φ := Subtype.ext ((congrArg D.liftMor (Equiv.apply_symm_apply D.liftHomEquiv
    (D.comorphOf φ.1 (D.base_eq_of_comm φ.1 φ.2.1.1)))).trans (D.liftMor_comorphOf _ _))
  right_inv p := FirstOrderLiftDiagram.Lift.ext (D := D.toFirstOrderLiftDiagram)
    ((congrArg D.liftHomEquiv.symm (D.comorphOf_liftMor (D.liftHomEquiv p.hom) _)).trans
      (Equiv.symm_apply_apply _ _))

/-- The homomorphism attached by `liftEquiv` to a morphism `φ` is its comorphism, transposed. -/
theorem liftEquiv_hom (φ : D.Lifts) :
    (D.liftEquiv φ).hom = D.liftHomEquiv.symm (D.comorphOf φ.1 (D.base_eq_of_comm φ.1 φ.2.1.1)) :=
  rfl

/-- The morphism attached by `liftEquiv` to a lift has underlying map `k₂ ≫ g ≫ i₁` and the
transposed homomorphism as comorphism. -/
theorem liftEquiv_symm_apply (p : D.toFirstOrderLiftDiagram.Lift) :
    (D.liftEquiv.symm p).1 = D.liftMor (D.liftHomEquiv p.hom) :=
  rfl

end DeformationIdealDiagram

end AlgebraicGeometry.RingedSpaceThickening

end
