module

public import StacksFrontier.CategoryTheory.Bicategory.CoGrothendieckInverseImage
public import StacksFrontier.CategoryTheory.Comma.LiftConst

/-!
# Morphisms of families of inverse images, read on a single member

Let `F` be a pseudofunctor on `𝒮ᵒᵖ` with values in categories and `G : 𝒟 ⥤ 𝒮` a functor. Two
objects `Y = (X, L)` and `Y' = (X', L')` of `∫ᶜ F` with families of morphisms
`s j : G (A j) ⟶ X` and `s' j : G (A' j) ⟶ X'`, natural in `j` in a category `J`, give two
functors `c, c' : J ⥤ Comma G (forget F)` with constant right-hand side
(`CategoryTheory.Comma.liftConst`), and the families of inverse images `j ↦ (A j, s j^* L)` and
`j ↦ (A' j, s' j^* L')` of `CategoryTheory.Pseudofunctor.CoGrothendieck.inverseImage`.

A natural transformation `θ` between them, together with a morphism `f : X ⟶ X'` such that the
base of every component `θ.app j` lies over `f`, is read on each member as a morphism
`ψ j : s j^* L ⟶ s j^* f^* L'` (`descentFiber`). This file proves, at an arbitrary
pseudofunctor, the three facts that turn the descent of morphisms of quasi-coherent modules
(Stacks 04W6, 04W8) into the full faithfulness of a functor into families of inverse images,
as in Stacks 0E94:

* the morphisms `ψ j` are natural for the transition morphisms of the family
  (`descentFiber_naturality`), so that on two morphisms `u₁ u₂ : c ⟶ j` they satisfy the pairwise
  condition of Stacks 04W3 (`descentFiber_compat`);
* a morphism `φ : L ⟶ f^* L'` whose inverse image along one member is `ψ j₀` has inverse image
  `ψ j` along every member `j` linked to `j₀` by a span `j ⟵ c ⟶ j₀` along whose first leg
  inverse images are injective on morphisms (`map_map_eq_descentFiber_of_span`);
* for such a `φ`, every component `θ.app j` is the inverse image of the morphism of triples
  `(β j, (f, φ))` (`eq_inverseImage_map_of_map_eq`).

All of them are equalities of morphisms in the fibres of an abstract pseudofunctor, proved once
here so that no concrete pseudofunctor ever has to be unfolded to check them.

## Main definitions

* `CategoryTheory.Pseudofunctor.CoGrothendieck.descentFiber`: the morphism `ψ j`.
* `CategoryTheory.NatTrans.transportOfEq`: a natural transformation transported along equalities
  of functors.

## Implementation notes

`θ` is a natural transformation of functors `J ⥤ ∫ᶜ (F ∘ G)` rather than a family of morphisms
with a naturality hypothesis. A concrete family is then passed as a whiskered natural
transformation, and checking its type only compares the objects and morphisms of two functors,
one at a time. A naturality square stated separately would instead have to be compared with the
square of this file as a composite in `∫ᶜ (F ∘ G)`, which unfolds the composition of the
Grothendieck construction and with it the concrete pseudofunctor. For the same reason a concrete
family whose functors agree with `c ⋙ inverseImage F G` only after unfolding is passed through
`CategoryTheory.NatTrans.transportOfEq` along an equality of functors proved object by object
and morphism by morphism (`CategoryTheory.Functor.hext`), never by comparing the functors.
-/

@[expose] public noncomputable section

namespace CategoryTheory.NatTrans

/-- A natural transformation transported along equalities of its source and target functors. -/
def transportOfEq {C D : Type*} [Category C] [Category D] {K K' L L' : C ⥤ D} (h : K = L)
    (h' : K' = L') (θ : K ⟶ K') : L ⟶ L' :=
  eqToHom h.symm ≫ θ ≫ eqToHom h'

/-- The components of a transported natural transformation are those of the original one. -/
theorem transportOfEq_app_heq {C D : Type*} [Category C] [Category D] {K K' L L' : C ⥤ D}
    (h : K = L) (h' : K' = L') (θ : K ⟶ K') (X : C) :
    HEq ((transportOfEq h h' θ).app X) (θ.app X) := by
  subst h h'
  simp [transportOfEq]

end CategoryTheory.NatTrans

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Opposite Bicategory

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

/-- Cancelling two isomorphisms and their inverses after a morphism. -/
theorem _root_.CategoryTheory.Iso.eq_comp_hom_comp_hom_comp_inv_comp_inv {C : Type*} [Category C]
    {P Q R S : C} (θ : P ⟶ Q) (e₁ : Q ≅ R) (e₂ : R ≅ S) :
    θ = (θ ≫ e₁.hom ≫ e₂.hom) ≫ e₂.inv ≫ e₁.inv := by
  simp

section Generic

variable {B : Type*} [Bicategory B] [Strict B] (F : Pseudofunctor B Cat.{v₂, u₂})

/-- **The inverse image along a square with an identity side, of the identity comparison, is the
comparison of the factorization.** -/
theorem squareFiber_mapId {x y y' : B} (q : x ⟶ y) (q' : x ⟶ y') (g : y' ⟶ y) (k : x ⟶ y)
    (h₁ : 𝟙 x ≫ q = k) (h₂ : q' ≫ g = k) (h : q' ≫ g = q) (Y : F.obj x) :
    squareFiber F q q' (𝟙 x) g k h₁ h₂ ((F.mapId x).inv.toNatTrans.app Y) =
      (F.mapComp' q' g q h).hom.toNatTrans.app Y := by
  obtain rfl : k = q := h₁.symm.trans (Category.id_comp q)
  simp only [squareFiber, F.mapComp'_id_comp_inv_app]
  rw [← Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The comparison of the two inverse images along `p₁` and `p₂` of a factorization
`s₀ ≫ pᵢ = k`, pulled back along `v`**, is the comparison along the composites `pᵢ ≫ v`, up to
the comparisons of the factorizations `pᵢ ≫ v = gᵢ`. -/
theorem map_mapComp'_inv_comp_hom {x y z t : B} (s₀ : x ⟶ y) (p₁ p₂ : y ⟶ z) (k : x ⟶ z)
    (h₁ : s₀ ≫ p₁ = k) (h₂ : s₀ ≫ p₂ = k) (v : z ⟶ t) (g₁ g₂ : y ⟶ t) (hg₁ : p₁ ≫ v = g₁)
    (hg₂ : p₂ ≫ v = g₂) (k' : x ⟶ t) (hk : k ≫ v = k') (h₁' : s₀ ≫ g₁ = k')
    (h₂' : s₀ ≫ g₂ = k') (N : F.obj x) :
    (F.map v).toFunctor.map ((F.mapComp' s₀ p₁ k h₁).inv.toNatTrans.app N) ≫
        (F.map v).toFunctor.map ((F.mapComp' s₀ p₂ k h₂).hom.toNatTrans.app N) =
      (F.mapComp' p₁ v g₁ hg₁).inv.toNatTrans.app ((F.map s₀).toFunctor.obj N) ≫
        (F.mapComp' s₀ g₁ k' h₁').inv.toNatTrans.app N ≫
        (F.mapComp' s₀ g₂ k' h₂').hom.toNatTrans.app N ≫
        (F.mapComp' p₂ v g₂ hg₂).hom.toNatTrans.app ((F.map s₀).toFunctor.obj N) := by
  have A₁ := F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app s₀ p₁ v k g₁ k' h₁ hg₁ hk N
  have A₂ := F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app s₀ p₂ v k g₂ k' h₂ hg₂ hk N
  rw [← reassoc_of% A₁]
  refine congrArg (_ ≫ ·) ?_
  rw [← cancel_epi ((F.mapComp' k v k' hk).hom.toNatTrans.app N),
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  simpa using A₂

/-- **The pairwise condition descends along a morphism inverse images along which are injective
on morphisms**: if a morphism `w : s₀^* M ⟶ s₀^* N` satisfies the pairwise condition on the two
composites `pᵢ ≫ v`, it satisfies it on `p₁` and `p₂`. -/
theorem compat_of_compat_comp {x y z t : B} (s₀ : x ⟶ y) (p₁ p₂ : y ⟶ z) (k : x ⟶ z)
    (h₁ : s₀ ≫ p₁ = k) (h₂ : s₀ ≫ p₂ = k) (v : z ⟶ t) (g₁ g₂ : y ⟶ t) (hg₁ : p₁ ≫ v = g₁)
    (hg₂ : p₂ ≫ v = g₂) (k' : x ⟶ t) (hk : k ≫ v = k') (h₁' : s₀ ≫ g₁ = k')
    (h₂' : s₀ ≫ g₂ = k') {M N : F.obj x}
    (w : (F.map s₀).toFunctor.obj M ⟶ (F.map s₀).toFunctor.obj N)
    (hinj : ∀ a b : (F.map p₁).toFunctor.obj ((F.map s₀).toFunctor.obj M) ⟶
        (F.map p₂).toFunctor.obj ((F.map s₀).toFunctor.obj N),
      (F.map v).toFunctor.map a = (F.map v).toFunctor.map b → a = b)
    (H : (F.map g₁).toFunctor.map w ≫ (F.mapComp' s₀ g₁ k' h₁').inv.toNatTrans.app N ≫
        (F.mapComp' s₀ g₂ k' h₂').hom.toNatTrans.app N =
      (F.mapComp' s₀ g₁ k' h₁').inv.toNatTrans.app M ≫
        (F.mapComp' s₀ g₂ k' h₂').hom.toNatTrans.app M ≫ (F.map g₂).toFunctor.map w) :
    (F.map p₁).toFunctor.map w ≫ (F.mapComp' s₀ p₁ k h₁).inv.toNatTrans.app N ≫
        (F.mapComp' s₀ p₂ k h₂).hom.toNatTrans.app N =
      (F.mapComp' s₀ p₁ k h₁).inv.toNatTrans.app M ≫
        (F.mapComp' s₀ p₂ k h₂).hom.toNatTrans.app M ≫ (F.map p₂).toFunctor.map w := by
  apply hinj
  have C := map_mapComp'_inv_comp_hom F s₀ p₁ p₂ k h₁ h₂ v g₁ g₂ hg₁ hg₂ k' hk h₁' h₂'
  have N₁ := F.mapComp'_hom_naturality p₁ v g₁ hg₁ w
  have N₂ := F.mapComp'_hom_naturality p₂ v g₂ hg₂ w
  simp only [Functor.map_comp]
  rw [C N, reassoc_of% (C M)]
  rw [← cancel_epi ((F.mapComp' p₁ v g₁ hg₁).hom.toNatTrans.app ((F.map s₀).toFunctor.obj M))]
  simp only [← reassoc_of% N₁, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rw [← N₂, ← reassoc_of% H]

end Generic

section Vertical

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- A vertical morphism followed by a morphism of `∫ᶜ F` is the morphism with the same base and
the composite fibre. -/
theorem ι_map_comp_eq {a : 𝒮} {M M' : F.obj ⟨op a⟩} (x : M ⟶ M') {W : ∫ᶜ F}
    (m : (ι F a).obj M' ⟶ W) :
    (ι F a).map x ≫ m = (⟨m.base, x ≫ m.fiber⟩ : (ι F a).obj M ⟶ W) := by
  refine (congrArg ((ι F a).map x ≫ ·) (ι_map_fiber_comp_cartesianLift m)).symm.trans ?_
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ cartesianLift W.fiber m.base) ((ι F a).map_comp x m.fiber).symm)).trans ?_
  exact ι_map_fiber_comp_cartesianLift (⟨m.base, x ≫ m.fiber⟩ : (ι F a).obj M ⟶ W)

/-- A morphism of `∫ᶜ F` followed by a vertical morphism is the morphism with the same base and
the composite fibre. -/
theorem comp_ι_map_eq {b : 𝒮} {M M' : F.obj ⟨op b⟩} (x : M ⟶ M') {V : ∫ᶜ F}
    (m : V ⟶ (ι F b).obj M) :
    m ≫ (ι F b).map x =
      (⟨m.base, m.fiber ≫ (F.map m.base.op.toLoc).toFunctor.map x⟩ : V ⟶ (ι F b).obj M') := by
  refine Eq.trans (b := (⟨m.base, m.fiber ≫ (F.map m.base.op.toLoc).toFunctor.map x⟩ :
    V ⟶ (ι F b).obj M') ≫ 𝟙 _) ?_ (Category.comp_id _)
  have e : m.fiber ≫ (F.map m.base.op.toLoc).toFunctor.map
        (x ≫ (F.mapId ⟨op b⟩).inv.toNatTrans.app M') ≫
        (F.mapComp (𝟙 b).op.toLoc m.base.op.toLoc).inv.toNatTrans.app M' =
      (m.fiber ≫ (F.map m.base.op.toLoc).toFunctor.map x) ≫
        (F.map m.base.op.toLoc).toFunctor.map ((F.mapId ⟨op b⟩).inv.toNatTrans.app M') ≫
        (F.mapComp (𝟙 b).op.toLoc m.base.op.toLoc).inv.toNatTrans.app M' :=
    (congrArg (m.fiber ≫ ·) ((congrArg (· ≫ _)
      ((F.map m.base.op.toLoc).toFunctor.map_comp x _)).trans (Category.assoc _ _ _))).trans
      (Category.assoc _ _ _).symm
  exact congrArg (fun φ => (⟨m.base ≫ 𝟙 b, φ⟩ : V ⟶ (ι F b).obj M')) e

/-- A morphism of `∫ᶜ F` with a given fibre, over its own base. -/
theorem hom_eq_mk_of_fiber_eq {a b : ∫ᶜ F} (m : a ⟶ b)
    (φ : a.fiber ⟶ (F.map m.base.op.toLoc).toFunctor.obj b.fiber) (h : m.fiber = φ) :
    m = (⟨m.base, φ⟩ : a ⟶ b) := by
  subst h
  rfl

end Vertical

section Descent

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒟 : Type u₃} [Category.{v₃} 𝒟]
  {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}} {G : 𝒟 ⥤ 𝒮}
  {J : Type u₄} [Category.{v₄} J] {A A' : J ⥤ 𝒟} {Y Y' : ∫ᶜ F}
  {s : ∀ j, G.obj (A.obj j) ⟶ Y.base} {s' : ∀ j, G.obj (A'.obj j) ⟶ Y'.base}
  {hs : ∀ {j' j : J} (u : j' ⟶ j), G.map (A.map u) ≫ s j = s j'}
  {hs' : ∀ {j' j : J} (u : j' ⟶ j), G.map (A'.map u) ≫ s' j = s' j'}

/-- The fibre of the inverse image of a transition morphism of a family with constant right-hand
side is the comparison of the factorization `s j' = G (A u) ≫ s j`. -/
theorem inverseImage_map_liftConst_fiber {j' j : J} (u : j' ⟶ j) :
    ((inverseImage F G).map ((Comma.liftConst (R := forget F) A Y s hs).map u)).fiber =
      (F.mapComp' (s j).op.toLoc (G.map (A.map u)).op.toLoc (s j').op.toLoc
        (congrArg (fun k : G.obj (A.obj j') ⟶ Y.base => k.op.toLoc) (hs u))).hom.toNatTrans.app
          Y.fiber :=
  squareFiber_mapId F (s j').op.toLoc (s j).op.toLoc (G.map (A.map u)).op.toLoc
    (s j' ≫ 𝟙 Y.base).op.toLoc rfl
    (inverseImage_square F G ((Comma.liftConst (R := forget F) A Y s hs).map u)) _ Y.fiber

variable (θ : Comma.liftConst (R := forget F) A Y s hs ⋙ inverseImage F G ⟶
    Comma.liftConst (R := forget F) A' Y' s' hs' ⋙ inverseImage F G)
  (f : Y.base ⟶ Y'.base)
  (hf : ∀ j, G.map (θ.app j).base ≫ s' j = s j ≫ f)

include hf

/-- The square of `θ.app j` over `f`, in `LocallyDiscrete 𝒮ᵒᵖ`. -/
theorem descentFiber_square (j : J) :
    (s' j).op.toLoc ≫ (G.map (θ.app j).base).op.toLoc = (s j ≫ f).op.toLoc :=
  congrArg (fun k : G.obj (A.obj j) ⟶ Y'.base => k.op.toLoc) (hf j)

/-- **The morphism `θ.app j` read on the member `j`**: `s j^* L ⟶ s j^* f^* L'`, the fibre of
`θ.app j` followed by the comparisons of the two factorizations of the square of `θ.app j` over
`f`. -/
def descentFiber (j : J) :
    (F.map (s j).op.toLoc).toFunctor.obj Y.fiber ⟶
      (F.map (s j).op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj Y'.fiber) :=
  (θ.app j).fiber ≫
    (F.mapComp' (s' j).op.toLoc (G.map (θ.app j).base).op.toLoc (s j ≫ f).op.toLoc
      (descentFiber_square θ f hf j)).inv.toNatTrans.app Y'.fiber ≫
    (F.mapComp' f.op.toLoc (s j).op.toLoc (s j ≫ f).op.toLoc rfl).hom.toNatTrans.app Y'.fiber

/-- The morphism read on a member is invertible when the fibre of `θ.app j` is. -/
theorem isIso_descentFiber (j : J) (h : IsIso (θ.app j).fiber) :
    IsIso (descentFiber θ f hf j) := by
  have e : descentFiber θ f hf j = (asIso (θ.app j).fiber ≪≫
      (Cat.Hom.toNatIso (F.mapComp' (s' j).op.toLoc (G.map (θ.app j).base).op.toLoc
        (s j ≫ f).op.toLoc (descentFiber_square θ f hf j))).symm.app Y'.fiber ≪≫
      (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc (s j).op.toLoc (s j ≫ f).op.toLoc rfl)).app
        Y'.fiber).hom := rfl
  rw [e]
  exact Iso.isIso_hom _

/-- The object `(X, f^* L')` of `∫ᶜ F`. -/
abbrev descentTarget : ∫ᶜ F := ⟨Y.base, (F.map f.op.toLoc).toFunctor.obj Y'.fiber⟩

/-- The family `j ↦ (A j, (X, f^* L'), s j)`. -/
abbrev descentComma : J ⥤ Comma G (forget F) :=
  Comma.liftConst (R := forget F) A (descentTarget f) s hs

/-- The cartesian morphism of triples `(A j, (X, f^* L'), s j) ⟶ (A' j, (X', L'), s' j)` given by
the base of `θ.app j` and `(f, 𝟙)`. -/
def descentCartesian (j : J) :
    (descentComma (hs := hs) (Y' := Y') f).obj j ⟶
      (Comma.liftConst (R := forget F) A' Y' s' hs').obj j where
  left := (θ.app j).base
  right := ⟨f, 𝟙 _⟩
  w := hf j

/-- The morphism of triples `(β j, (f, φ))` attached to a morphism `φ : L ⟶ f^* L'`. -/
def descentHom (φ : Y.fiber ⟶ (F.map f.op.toLoc).toFunctor.obj Y'.fiber) (j : J) :
    (Comma.liftConst (R := forget F) A Y s hs).obj j ⟶
      (Comma.liftConst (R := forget F) A' Y' s' hs').obj j where
  left := (θ.app j).base
  right := ⟨f, φ⟩
  w := hf j

/-- The fibre of the inverse image of the cartesian morphism of triples `descentCartesian θ f hf j`
is an isomorphism. -/
theorem isIso_inverseImage_map_descentCartesian_fiber (j : J) :
    IsIso ((inverseImage F G).map (descentCartesian θ f hf j)).fiber :=
  isIso_squareFiber F _ _ _ _ _ _ _ _ (IsIso.id _)

/-- **`θ.app j` is the vertical morphism `ψ j` followed by the inverse image of the cartesian
morphism of triples.** -/
theorem eq_ι_map_descentFiber_comp (j : J) :
    θ.app j = (ι (G.op.toPseudofunctor.comp F) (A.obj j)).map (descentFiber θ f hf j) ≫
      (inverseImage F G).map (descentCartesian θ f hf j) := by
  refine (hom_eq_mk_of_fiber_eq (θ.app j) _ ?_).trans
    (ι_map_comp_eq (F := G.op.toPseudofunctor.comp F) (descentFiber θ f hf j)
      ((inverseImage F G).map (descentCartesian θ f hf j))).symm
  change (θ.app j).fiber = descentFiber θ f hf j ≫ ((F.map (s j).op.toLoc).toFunctor.map (𝟙 _) ≫
    (F.mapComp' f.op.toLoc (s j).op.toLoc (s j ≫ f).op.toLoc rfl).inv.toNatTrans.app Y'.fiber ≫
    (F.mapComp' (s' j).op.toLoc (G.map (θ.app j).base).op.toLoc (s j ≫ f).op.toLoc
      (descentFiber_square θ f hf j)).hom.toNatTrans.app Y'.fiber)
  refine (Iso.eq_comp_hom_comp_hom_comp_inv_comp_inv (θ.app j).fiber
    ((Cat.Hom.toNatIso (F.mapComp' (s' j).op.toLoc (G.map (θ.app j).base).op.toLoc
      (s j ≫ f).op.toLoc (descentFiber_square θ f hf j))).symm.app Y'.fiber)
    ((Cat.Hom.toNatIso (F.mapComp' f.op.toLoc (s j).op.toLoc (s j ≫ f).op.toLoc rfl)).app
      Y'.fiber)).trans ?_
  exact congrArg (descentFiber θ f hf j ≫ ·)
    ((Category.id_comp _).symm.trans (congrArg (· ≫ _)
      (CategoryTheory.Functor.map_id (F.map (s j).op.toLoc).toFunctor
        ((F.map f.op.toLoc).toFunctor.obj Y'.fiber)).symm))

/-- The inverse image of the morphism of triples `(β j, (f, φ))` is `θ.app j` as soon as the
inverse image of `φ` along `s j` is `ψ j`. -/
theorem eq_inverseImage_map_of_map_eq (φ : Y.fiber ⟶ (F.map f.op.toLoc).toFunctor.obj Y'.fiber)
    (j : J) (h : (F.map (s j).op.toLoc).toFunctor.map φ = descentFiber θ f hf j) :
    θ.app j = (inverseImage F G).map (descentHom θ f hf φ j) := by
  refine hom_eq_mk_of_fiber_eq (θ.app j) (inverseImageFiber F G (descentHom θ f hf φ j)) ?_
  change (θ.app j).fiber = (F.map (s j).op.toLoc).toFunctor.map φ ≫
    (F.mapComp' f.op.toLoc (s j).op.toLoc (s j ≫ f).op.toLoc rfl).inv.toNatTrans.app Y'.fiber ≫
    (F.mapComp' (s' j).op.toLoc (G.map (θ.app j).base).op.toLoc (s j ≫ f).op.toLoc
      (descentFiber_square θ f hf j)).hom.toNatTrans.app Y'.fiber
  refine (Iso.eq_comp_hom_comp_hom_comp_inv_comp_inv (θ.app j).fiber
    ((Cat.Hom.toNatIso (F.mapComp' (s' j).op.toLoc (G.map (θ.app j).base).op.toLoc
      (s j ≫ f).op.toLoc (descentFiber_square θ f hf j))).symm.app Y'.fiber)
    ((Cat.Hom.toNatIso (F.mapComp' f.op.toLoc (s j).op.toLoc (s j ≫ f).op.toLoc rfl)).app
      Y'.fiber)).trans ?_
  exact congrArg (· ≫ _) h.symm

/-- The cartesian morphisms of triples `descentCartesian θ f hf j` are natural in `j`. -/
theorem descentCartesian_naturality {j' j : J} (u : j' ⟶ j) :
    (descentComma (hs := hs) (Y' := Y') f).map u ≫ descentCartesian θ f hf j =
      descentCartesian θ f hf j' ≫ (Comma.liftConst (R := forget F) A' Y' s' hs').map u :=
  Comma.hom_ext _ _ (congrArg Hom.base (θ.naturality u))
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- **Naturality of the morphisms read on the members**, as morphisms of `∫ᶜ (F ∘ G)`. -/
theorem ι_map_descentFiber_naturality {j' j : J} (u : j' ⟶ j) :
    (ι (G.op.toPseudofunctor.comp F) (A.obj j')).map (descentFiber θ f hf j') ≫
        (inverseImage F G).map ((descentComma (hs := hs) (Y' := Y') f).map u) =
      (inverseImage F G).map ((Comma.liftConst (R := forget F) A Y s hs).map u) ≫
        (ι (G.op.toPseudofunctor.comp F) (A.obj j)).map (descentFiber θ f hf j) := by
  refine hom_ext_of_comp_right _ _ ((inverseImage F G).map (descentCartesian θ f hf j))
    ((Category.id_comp (A.map u)).trans (Category.comp_id (A.map u)).symm)
    (isIso_inverseImage_map_descentCartesian_fiber θ f hf j) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (((inverseImage F G).map_comp _ _).symm.trans
    ((congrArg (inverseImage F G).map (descentCartesian_naturality θ f hf u)).trans
      ((inverseImage F G).map_comp _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (eq_ι_map_descentFiber_comp θ f hf j').symm).trans ?_
  refine (θ.naturality u).symm.trans ?_
  refine (congrArg (_ ≫ ·) (eq_ι_map_descentFiber_comp θ f hf j)).trans ?_
  exact (Category.assoc _ _ _).symm

/-- **Naturality of the morphisms read on the members**: for `u : j' ⟶ j`, the inverse image of
`ψ j` along `G (A u)` is `ψ j'` up to the comparisons of the factorization `s j' = G (A u) ≫ s j`
on either side. -/
theorem descentFiber_naturality {j' j : J} (u : j' ⟶ j) :
    descentFiber θ f hf j' ≫
        (F.mapComp' (s j).op.toLoc (G.map (A.map u)).op.toLoc (s j').op.toLoc
          (congrArg (fun k : G.obj (A.obj j') ⟶ Y.base => k.op.toLoc) (hs u))).hom.toNatTrans.app
            ((F.map f.op.toLoc).toFunctor.obj Y'.fiber) =
      (F.mapComp' (s j).op.toLoc (G.map (A.map u)).op.toLoc (s j').op.toLoc
          (congrArg (fun k : G.obj (A.obj j') ⟶ Y.base => k.op.toLoc) (hs u))).hom.toNatTrans.app
            Y.fiber ≫
        (F.map (G.map (A.map u)).op.toLoc).toFunctor.map (descentFiber θ f hf j) := by
  have h₁ : (⟨A.map u, descentFiber θ f hf j' ≫
        ((inverseImage F G).map ((descentComma (hs := hs) (Y' := Y') f).map u)).fiber⟩ :
      (inverseImage F G).obj ((Comma.liftConst (R := forget F) A Y s hs).obj j') ⟶
        (inverseImage F G).obj ((descentComma (hs := hs) (Y' := Y') f).obj j)) =
      ⟨A.map u, ((inverseImage F G).map ((Comma.liftConst (R := forget F) A Y s hs).map u)).fiber ≫
        (F.map (G.map (A.map u)).op.toLoc).toFunctor.map (descentFiber θ f hf j)⟩ :=
    (ι_map_comp_eq (F := G.op.toPseudofunctor.comp F) (descentFiber θ f hf j')
      ((inverseImage F G).map ((descentComma (hs := hs) (Y' := Y') f).map u))).symm.trans
      ((ι_map_descentFiber_naturality θ f hf u).trans
        (comp_ι_map_eq (F := G.op.toPseudofunctor.comp F) (descentFiber θ f hf j)
          ((inverseImage F G).map ((Comma.liftConst (R := forget F) A Y s hs).map u))))
  have h' := eq_of_heq (Hom.mk.inj h₁).2
  refine Eq.trans ?_ (h'.trans ?_)
  · exact congrArg (descentFiber θ f hf j' ≫ ·)
      (inverseImage_map_liftConst_fiber (Y := descentTarget f) (hs := hs) u).symm
  · exact congrArg (· ≫ _) (inverseImage_map_liftConst_fiber (Y := Y) (hs := hs) u)

/-- **The pairwise condition** (Stacks 04W3) for the morphism read on a member `j`, on two
morphisms `u₁ u₂ : c ⟶ j`. -/
theorem descentFiber_compat {c j : J} (u₁ u₂ : c ⟶ j) :
    (F.map (G.map (A.map u₁)).op.toLoc).toFunctor.map (descentFiber θ f hf j) ≫
        (F.mapComp' (s j).op.toLoc (G.map (A.map u₁)).op.toLoc (s c).op.toLoc
          (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u₁))).inv.toNatTrans.app
            ((F.map f.op.toLoc).toFunctor.obj Y'.fiber) ≫
        (F.mapComp' (s j).op.toLoc (G.map (A.map u₂)).op.toLoc (s c).op.toLoc
          (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u₂))).hom.toNatTrans.app
            ((F.map f.op.toLoc).toFunctor.obj Y'.fiber) =
      (F.mapComp' (s j).op.toLoc (G.map (A.map u₁)).op.toLoc (s c).op.toLoc
          (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u₁))).inv.toNatTrans.app
            Y.fiber ≫
        (F.mapComp' (s j).op.toLoc (G.map (A.map u₂)).op.toLoc (s c).op.toLoc
          (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u₂))).hom.toNatTrans.app
            Y.fiber ≫
        (F.map (G.map (A.map u₂)).op.toLoc).toFunctor.map (descentFiber θ f hf j) := by
  have h₁ := descentFiber_naturality θ f hf u₁
  have h₂ := descentFiber_naturality θ f hf u₂
  rw [← Category.assoc, ← h₂, ← Cat.Hom.inv_hom_id_toNatTrans_app_assoc
    (F.mapComp' (s j).op.toLoc (G.map (A.map u₁)).op.toLoc (s c).op.toLoc
      (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u₁))) Y.fiber
    ((F.map (G.map (A.map u₁)).op.toLoc).toFunctor.map (descentFiber θ f hf j)), ← h₁]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

/-- **The pairwise condition** (Stacks 04W3) for the morphism read on a member `j`, on two
morphisms `p₁ p₂ : P ⟶ G (A j)` of `𝒮` through which the images of two morphisms
`u₁ u₂ : c ⟶ j` factor by a morphism `v : G (A c) ⟶ P`, inverse images along which are injective
on morphisms. -/
theorem descentFiber_compat_of_factor {c j : J} (u₁ u₂ : c ⟶ j) {P : 𝒮}
    (p₁ p₂ : P ⟶ G.obj (A.obj j)) (hp : p₁ ≫ s j = p₂ ≫ s j) (v : G.obj (A.obj c) ⟶ P)
    (hv₁ : v ≫ p₁ = G.map (A.map u₁)) (hv₂ : v ≫ p₂ = G.map (A.map u₂))
    (hinj : ∀ a b : (F.map p₁.op.toLoc).toFunctor.obj
          ((F.map (s j).op.toLoc).toFunctor.obj Y.fiber) ⟶
        (F.map p₂.op.toLoc).toFunctor.obj
          ((F.map (s j).op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj Y'.fiber)),
      (F.map v.op.toLoc).toFunctor.map a = (F.map v.op.toLoc).toFunctor.map b → a = b) :
    (F.map p₁.op.toLoc).toFunctor.map (descentFiber θ f hf j) ≫
        (F.mapComp' (s j).op.toLoc p₁.op.toLoc (p₁ ≫ s j).op.toLoc rfl).inv.toNatTrans.app
          ((F.map f.op.toLoc).toFunctor.obj Y'.fiber) ≫
        (F.mapComp' (s j).op.toLoc p₂.op.toLoc (p₁ ≫ s j).op.toLoc
          (congrArg (fun k : P ⟶ Y.base => k.op.toLoc) hp.symm)).hom.toNatTrans.app
          ((F.map f.op.toLoc).toFunctor.obj Y'.fiber) =
      (F.mapComp' (s j).op.toLoc p₁.op.toLoc (p₁ ≫ s j).op.toLoc rfl).inv.toNatTrans.app
          Y.fiber ≫
        (F.mapComp' (s j).op.toLoc p₂.op.toLoc (p₁ ≫ s j).op.toLoc
          (congrArg (fun k : P ⟶ Y.base => k.op.toLoc) hp.symm)).hom.toNatTrans.app Y.fiber ≫
        (F.map p₂.op.toLoc).toFunctor.map (descentFiber θ f hf j) :=
  compat_of_compat_comp F (s j).op.toLoc p₁.op.toLoc p₂.op.toLoc (p₁ ≫ s j).op.toLoc rfl
    (congrArg (fun k : P ⟶ Y.base => k.op.toLoc) hp.symm) v.op.toLoc
    (G.map (A.map u₁)).op.toLoc (G.map (A.map u₂)).op.toLoc
    (congrArg (fun k => k.op.toLoc) hv₁) (congrArg (fun k => k.op.toLoc) hv₂) (s c).op.toLoc
    (congrArg (fun k => k.op.toLoc) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ s j) hv₁).trans (hs u₁))))
    (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u₁))
    (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u₂))
    (descentFiber θ f hf j) hinj (descentFiber_compat θ f hf u₁ u₂)

/-- **A morphism `φ : L ⟶ f^* L'` whose inverse image along one member `j₀` is `ψ j₀` has inverse
image `ψ j` along every member `j` linked to `j₀` by a span `j ⟵ c ⟶ j₀`** along whose first leg
inverse images are injective on morphisms. -/
theorem map_map_eq_descentFiber_of_span
    (φ : Y.fiber ⟶ (F.map f.op.toLoc).toFunctor.obj Y'.fiber) {j₀ : J}
    (h₀ : (F.map (s j₀).op.toLoc).toFunctor.map φ = descentFiber θ f hf j₀)
    {c j : J} (u₁ : c ⟶ j) (u₂ : c ⟶ j₀)
    (hinj : ∀ a b : (F.map (s j).op.toLoc).toFunctor.obj Y.fiber ⟶
        (F.map (s j).op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj Y'.fiber),
      (F.map (G.map (A.map u₁)).op.toLoc).toFunctor.map a =
        (F.map (G.map (A.map u₁)).op.toLoc).toFunctor.map b → a = b) :
    (F.map (s j).op.toLoc).toFunctor.map φ = descentFiber θ f hf j := by
  have hφ : ∀ {i : J} (u : c ⟶ i), (F.map (s c).op.toLoc).toFunctor.map φ ≫
      (F.mapComp' (s i).op.toLoc (G.map (A.map u)).op.toLoc (s c).op.toLoc
        (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u))).hom.toNatTrans.app
          ((F.map f.op.toLoc).toFunctor.obj Y'.fiber) =
      (F.mapComp' (s i).op.toLoc (G.map (A.map u)).op.toLoc (s c).op.toLoc
        (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u))).hom.toNatTrans.app
          Y.fiber ≫
        (F.map (G.map (A.map u)).op.toLoc).toFunctor.map
          ((F.map (s i).op.toLoc).toFunctor.map φ) :=
    fun u => F.mapComp'_hom_naturality (s _).op.toLoc (G.map (A.map u)).op.toLoc (s c).op.toLoc
      (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u)) φ
  have hc : (F.map (s c).op.toLoc).toFunctor.map φ = descentFiber θ f hf c :=
    (cancel_mono ((Cat.Hom.toNatIso (F.mapComp' (s j₀).op.toLoc (G.map (A.map u₂)).op.toLoc
      (s c).op.toLoc (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u₂)))).app
        ((F.map f.op.toLoc).toFunctor.obj Y'.fiber)).hom).mp
      ((hφ u₂).trans ((congrArg (_ ≫ ·) (congrArg _ h₀)).trans
        (descentFiber_naturality θ f hf u₂).symm))
  refine hinj _ _ ((cancel_epi ((Cat.Hom.toNatIso (F.mapComp' (s j).op.toLoc
    (G.map (A.map u₁)).op.toLoc (s c).op.toLoc
      (congrArg (fun k : G.obj (A.obj c) ⟶ Y.base => k.op.toLoc) (hs u₁)))).app Y.fiber).hom).mp ?_)
  exact (hφ u₁).symm.trans ((congrArg (· ≫ _) hc).trans (descentFiber_naturality θ f hf u₁))

end Descent

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
