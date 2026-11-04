module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# Systems of derived morphism sets along a directed system of schemes over a base

Let `B` be a scheme and let `j ↦ T_j` be a directed system of schemes over `B`, with transition
morphisms `t_{ij} : T_j ⟶ T_i` over `B` and a cone `T ⟶ T_j` over `B`. For two objects `X`, `Y`
of `D(𝒪_B)` the derived pullbacks to the stages and to the vertex give a system of morphism sets

`Hom_{D(𝒪_{T_j})}(Lk_j^*X, Lk_j^*Y) ⟶ Hom_{D(𝒪_T)}(Lk^*X, Lk^*Y)`,

whose maps apply the derived pullback along the morphisms of the system and read the result
through the comparison isomorphisms of Stacks 0D5S. This file sets up that system and proves the
closure properties of the statement that `Hom(Lk^*X, Lk^*Y)` is its filtered colimit: it depends
on `X` and `Y` only up to isomorphism, it is closed under binary biproducts and distinguished
triangles in `X`, it transfers along morphisms of systems inducing bijections, and it is
unchanged by composing the structure morphisms with a morphism of bases.

## Main definitions

* `Stacks.LimitHomDescent.SchemeSystem`: a directed system of schemes over a base with a cone.
* `Stacks.LimitHomDescent.SchemeSystem.trans` and `proj`: the maps of the system of morphism
  sets.
* `Stacks.LimitHomDescent.SchemeSystem.IsColim`: `Hom(Lk^*X, Lk^*Y)` is the filtered colimit of
  the `Hom(Lk_j^*X, Lk_j^*Y)`.
* `Stacks.LimitHomDescent.SchemeSystem.Hom`: a morphism of systems over the same base.
* `Stacks.LimitHomDescent.SchemeSystem.comp`: a system composed with a morphism of bases.

## Main results

* `Stacks.LimitHomDescent.SchemeSystem.IsColim.of_iso_fst`, `of_iso_snd`, `biprod` and
  `obj₃`: the closure properties in the two arguments.
* `Stacks.LimitHomDescent.SchemeSystem.Hom.isColim_iff`: transfer along a morphism of systems.
* `Stacks.LimitHomDescent.SchemeSystem.isColim_comp_iff`: change of base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback (schemeFactorIso schemeFactorHom)

attribute [local instance 10000] HasDerivedCategory.standard

universe v u

namespace Stacks.LimitHomDescent

/-! ### Factorisations of morphisms of schemes -/

section Factor

variable {V W X Y Z : Scheme.{u}}

/-- The derived category of `𝒪_X`-modules, in the spelling of the derived pullback. -/
abbrev DMod (X : Scheme.{u}) :=
  DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The derived pullback along a morphism of schemes. -/
abbrev pb {X Y : Scheme.{u}} (f : X ⟶ Y) : DMod Y ⥤ DMod X :=
  derivedPullback f.toLRSHom.toShHom

/-- The map attached to a factorisation depends on the factor only through its value. -/
theorem schemeFactorHom_congr {f f' : X ⟶ Y} (hf : f = f') (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k) (h' : f' ≫ g = k) (K L : DMod Z)
    (φ : (pb g).obj K ⟶ (pb g).obj L) :
    schemeFactorHom f g k h K L φ = schemeFactorHom f' g k h' K L φ := by
  subst hf
  rfl

/-- The cocycle identity of the comparison isomorphisms of a factorisation of morphisms of
schemes `c = p ≫ t ≫ a`. -/
theorem schemeFactorIso_assoc (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z) (q : V ⟶ Y)
    (c : V ⟶ Z) (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c) (hpb : p ≫ b = c)
    (M : DMod Z) :
    (schemeFactorIso p t q hq).hom.app ((pb a).obj M) ≫ (schemeFactorIso q a c hc).hom.app M =
      (pb p).map ((schemeFactorIso t a b hb).hom.app M) ≫
        (schemeFactorIso p b c hpb).hom.app M :=
  congrArg Iso.hom (Stacks.DerivedPullback.factorIso_assoc p.toLRSHom.toShHom
    t.toLRSHom.toShHom a.toLRSHom.toShHom b.toLRSHom.toShHom q.toLRSHom.toShHom
    c.toLRSHom.toShHom (congrArg (fun m : W ⟶ Z ↦ m.toLRSHom.toShHom) hb)
    (congrArg (fun m : V ⟶ Y ↦ m.toLRSHom.toShHom) hq)
    (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) hc)
    (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) hpb) M)

/-- The map attached to a factorisation is natural in its source. -/
theorem schemeFactorHom_map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    {K K' : DMod Z} (L : DMod Z) (a : K ⟶ K') (φ : (pb g).obj K' ⟶ (pb g).obj L) :
    schemeFactorHom f g k h K L ((pb g).map a ≫ φ) =
      (pb k).map a ≫ schemeFactorHom f g k h K' L φ := by
  have nat := (schemeFactorIso f g k h).inv.naturality a
  simp only [Functor.comp_map] at nat
  simp only [schemeFactorHom, Iso.homCongr_apply, Functor.map_comp, Category.assoc, Iso.app_hom,
    Iso.app_inv]
  rw [reassoc_of% nat]

/-- The map attached to a factorisation is natural in its target. -/
theorem schemeFactorHom_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K : DMod Z) {L L' : DMod Z} (b : L ⟶ L') (φ : (pb g).obj K ⟶ (pb g).obj L) :
    schemeFactorHom f g k h K L' (φ ≫ (pb g).map b) =
      schemeFactorHom f g k h K L φ ≫ (pb k).map b := by
  have nat := (schemeFactorIso f g k h).hom.naturality b
  simp only [Functor.comp_map] at nat
  simp only [schemeFactorHom, Iso.homCongr_apply, Functor.map_comp, Category.assoc, Iso.app_hom,
    Iso.app_inv, nat]

/-- The map attached to a factorisation is additive. -/
theorem schemeFactorHom_add (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DMod Z) (φ ψ : (pb g).obj K ⟶ (pb g).obj L) :
    schemeFactorHom f g k h K L (φ + ψ) =
      schemeFactorHom f g k h K L φ + schemeFactorHom f g k h K L ψ := by
  simp only [schemeFactorHom, Iso.homCongr_apply, Functor.map_add, Preadditive.comp_add,
    Preadditive.add_comp]

/-- The map attached to a factorisation sends `0` to `0`. -/
theorem schemeFactorHom_zero (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DMod Z) : schemeFactorHom f g k h K L 0 = 0 := by
  simp only [schemeFactorHom, Iso.homCongr_apply, Functor.map_zero, zero_comp, comp_zero]

/-- The map attached to a factorisation commutes with negation. -/
theorem schemeFactorHom_neg (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DMod Z) (φ : (pb g).obj K ⟶ (pb g).obj L) :
    schemeFactorHom f g k h K L (-φ) = -schemeFactorHom f g k h K L φ := by
  simp only [schemeFactorHom, Iso.homCongr_apply, Functor.map_neg, Preadditive.neg_comp,
    Preadditive.comp_neg]

/-- The map attached to a factorisation commutes with subtraction. -/
theorem schemeFactorHom_sub (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DMod Z) (φ ψ : (pb g).obj K ⟶ (pb g).obj L) :
    schemeFactorHom f g k h K L (φ - ψ) =
      schemeFactorHom f g k h K L φ - schemeFactorHom f g k h K L ψ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, schemeFactorHom_add, schemeFactorHom_neg]

/-- The maps attached to the two factorisations through a commutative square agree. -/
private theorem schemeFactorHom_comp_comm (u : V ⟶ W) (t : W ⟶ Y) (s : V ⟶ X) (v : X ⟶ Y)
    (g : Y ⟶ Z) (kW : W ⟶ Z) (kX : X ⟶ Z) (kV : V ⟶ Z) (hsq : u ≫ t = s ≫ v)
    (hW : t ≫ g = kW) (hX : v ≫ g = kX) (hV : u ≫ kW = kV) (hs : s ≫ kX = kV)
    (K L : DMod Z) (φ : (pb g).obj K ⟶ (pb g).obj L) :
    schemeFactorHom u kW kV hV K L (schemeFactorHom t g kW hW K L φ) =
      schemeFactorHom s kX kV hs K L (schemeFactorHom v g kX hX K L φ) := by
  rw [Stacks.DerivedPullback.schemeFactorHom_comp u t g kW (u ≫ t) kV hW rfl
      (by rw [Category.assoc, hW, hV]) hV,
    Stacks.DerivedPullback.schemeFactorHom_comp s v g kX (s ≫ v) kV hX rfl
      (by rw [Category.assoc, hX, hs]) hs]
  exact schemeFactorHom_congr hsq _ _ _ _ K L φ

end Factor

/-! ### Systems of schemes over a base -/

/-- **A directed system of schemes over a base `B`, with a cone over it.** The stages `T_j`, the
structure morphisms `k_j : T_j ⟶ B`, the transition morphisms `t_{ij} : T_j ⟶ T_i` over `B` for
`i ≤ j`, which compose, and a vertex `T` with a structure morphism `T ⟶ B` and projections
`p_j : T ⟶ T_j` over `B` compatible with the transition morphisms. -/
structure SchemeSystem (B : Scheme.{u}) (J : Type v) [Preorder J] where
  /-- The stage `T_j`. -/
  stage : J → Scheme.{u}
  /-- The structure morphism `T_j ⟶ B`. -/
  toBase : ∀ j, stage j ⟶ B
  /-- The transition morphism `T_j ⟶ T_i` for `i ≤ j`. -/
  transition : ∀ {i j : J}, i ≤ j → (stage j ⟶ stage i)
  /-- The transition morphisms lie over `B`. -/
  transition_toBase : ∀ {i j : J} (h : i ≤ j), transition h ≫ toBase i = toBase j
  /-- The transition morphisms compose. -/
  transition_comp : ∀ {i j k : J} (h : i ≤ j) (h' : j ≤ k),
    transition h' ≫ transition h = transition (h.trans h')
  /-- The transition morphism attached to `i ≤ i` is the identity. -/
  transition_refl : ∀ i : J, transition (le_refl i) = 𝟙 (stage i)
  /-- The vertex `T`. -/
  limit : Scheme.{u}
  /-- The structure morphism `T ⟶ B`. -/
  limitToBase : limit ⟶ B
  /-- The projection `T ⟶ T_j`. -/
  proj : ∀ j, limit ⟶ stage j
  /-- The projections lie over `B`. -/
  proj_toBase : ∀ j, proj j ≫ toBase j = limitToBase
  /-- The projections are compatible with the transition morphisms. -/
  proj_transition : ∀ {i j : J} (h : i ≤ j), proj j ≫ transition h = proj i

namespace SchemeSystem

variable {B : Scheme.{u}} {J : Type v} [Preorder J] (S : SchemeSystem.{v, u} B J)

/-- The transition map `Hom(Lk_i^*X, Lk_i^*Y) ⟶ Hom(Lk_j^*X, Lk_j^*Y)` for `i ≤ j`. -/
def trans (X Y : DMod B) (i j : J) (h : i ≤ j) :
    ((pb (S.toBase i)).obj X ⟶ (pb (S.toBase i)).obj Y) →
      ((pb (S.toBase j)).obj X ⟶ (pb (S.toBase j)).obj Y) :=
  schemeFactorHom (S.transition h) (S.toBase i) (S.toBase j) (S.transition_toBase h) X Y

/-- The map `Hom(Lk_j^*X, Lk_j^*Y) ⟶ Hom(Lk^*X, Lk^*Y)` to the vertex. -/
def projHom (X Y : DMod B) (j : J) :
    ((pb (S.toBase j)).obj X ⟶ (pb (S.toBase j)).obj Y) →
      ((pb S.limitToBase).obj X ⟶ (pb S.limitToBase).obj Y) :=
  schemeFactorHom (S.proj j) (S.toBase j) S.limitToBase (S.proj_toBase j) X Y

/-- **`Hom(Lk^*X, Lk^*Y)` is the filtered colimit of the `Hom(Lk_j^*X, Lk_j^*Y)`**, in the
elementwise form `Stacks.IsStagesColimit`. -/
def IsColim (X Y : DMod B) : Prop :=
  Stacks.IsStagesColimit (S.trans X Y) (S.projHom X Y)

variable {S}

/-- The map to the vertex is compatible with the transition maps. -/
theorem projHom_trans (X Y : DMod B) {i j : J} (h : i ≤ j)
    (φ : (pb (S.toBase i)).obj X ⟶ (pb (S.toBase i)).obj Y) :
    S.projHom X Y j (S.trans X Y i j h φ) = S.projHom X Y i φ :=
  Stacks.DerivedPullback.schemeFactorHom_comp (S.proj j) (S.transition h) (S.toBase i)
    (S.toBase j) (S.proj i) S.limitToBase (S.transition_toBase h) (S.proj_transition h)
    (S.proj_toBase i) (S.proj_toBase j) X Y φ

/-- The transition maps compose. -/
theorem trans_trans (X Y : DMod B) {i j k : J} (h : i ≤ j) (h' : j ≤ k)
    (φ : (pb (S.toBase i)).obj X ⟶ (pb (S.toBase i)).obj Y) :
    S.trans X Y j k h' (S.trans X Y i j h φ) = S.trans X Y i k (h.trans h') φ :=
  Stacks.DerivedPullback.schemeFactorHom_comp (S.transition h') (S.transition h) (S.toBase i)
    (S.toBase j) (S.transition (h.trans h')) (S.toBase k) (S.transition_toBase h)
    (S.transition_comp h h') (S.transition_toBase (h.trans h')) (S.transition_toBase h') X Y φ

/-- The transition map is natural in the first argument. -/
theorem trans_map_comp {X X' : DMod B} (Y : DMod B) (a : X ⟶ X') {i j : J} (h : i ≤ j)
    (φ : (pb (S.toBase i)).obj X' ⟶ (pb (S.toBase i)).obj Y) :
    S.trans X Y i j h ((pb (S.toBase i)).map a ≫ φ) =
      (pb (S.toBase j)).map a ≫ S.trans X' Y i j h φ :=
  schemeFactorHom_map_comp _ _ _ _ Y a φ

/-- The map to the vertex is natural in the first argument. -/
theorem projHom_map_comp {X X' : DMod B} (Y : DMod B) (a : X ⟶ X') (j : J)
    (φ : (pb (S.toBase j)).obj X' ⟶ (pb (S.toBase j)).obj Y) :
    S.projHom X Y j ((pb (S.toBase j)).map a ≫ φ) =
      (pb S.limitToBase).map a ≫ S.projHom X' Y j φ :=
  schemeFactorHom_map_comp _ _ _ _ Y a φ

/-- The transition map is natural in the second argument. -/
theorem trans_comp_map (X : DMod B) {Y Y' : DMod B} (b : Y ⟶ Y') {i j : J} (h : i ≤ j)
    (φ : (pb (S.toBase i)).obj X ⟶ (pb (S.toBase i)).obj Y) :
    S.trans X Y' i j h (φ ≫ (pb (S.toBase i)).map b) =
      S.trans X Y i j h φ ≫ (pb (S.toBase j)).map b :=
  schemeFactorHom_comp_map _ _ _ _ X b φ

/-- The map to the vertex is natural in the second argument. -/
theorem projHom_comp_map (X : DMod B) {Y Y' : DMod B} (b : Y ⟶ Y') (j : J)
    (φ : (pb (S.toBase j)).obj X ⟶ (pb (S.toBase j)).obj Y) :
    S.projHom X Y' j (φ ≫ (pb (S.toBase j)).map b) =
      S.projHom X Y j φ ≫ (pb S.limitToBase).map b :=
  schemeFactorHom_comp_map _ _ _ _ X b φ

/-- The transition map sends zero to zero. -/
theorem trans_zero (X Y : DMod B) {i j : J} (h : i ≤ j) : S.trans X Y i j h 0 = 0 :=
  schemeFactorHom_zero _ _ _ _ X Y

/-- The map to the vertex sends zero to zero. -/
theorem projHom_zero (X Y : DMod B) (j : J) : S.projHom X Y j 0 = 0 :=
  schemeFactorHom_zero _ _ _ _ X Y

/-- The transition map commutes with subtraction. -/
theorem trans_sub (X Y : DMod B) {i j : J} (h : i ≤ j)
    (φ ψ : (pb (S.toBase i)).obj X ⟶ (pb (S.toBase i)).obj Y) :
    S.trans X Y i j h (φ - ψ) = S.trans X Y i j h φ - S.trans X Y i j h ψ :=
  schemeFactorHom_sub _ _ _ _ X Y φ ψ

/-- The map to the vertex commutes with subtraction. -/
theorem projHom_sub (X Y : DMod B) (j : J)
    (φ ψ : (pb (S.toBase j)).obj X ⟶ (pb (S.toBase j)).obj Y) :
    S.projHom X Y j (φ - ψ) = S.projHom X Y j φ - S.projHom X Y j ψ :=
  schemeFactorHom_sub _ _ _ _ X Y φ ψ

/-- The map to the vertex commutes with addition. -/
theorem projHom_add (X Y : DMod B) (j : J)
    (φ ψ : (pb (S.toBase j)).obj X ⟶ (pb (S.toBase j)).obj Y) :
    S.projHom X Y j (φ + ψ) = S.projHom X Y j φ + S.projHom X Y j ψ :=
  schemeFactorHom_add _ _ _ _ X Y φ ψ

/-! ### Invariance under isomorphisms -/

/-- The statement depends on its first argument only up to isomorphism. -/
theorem IsColim.of_iso_fst [IsDirected J (· ≤ ·)] {X X' : DMod B} {Y : DMod B} (e : X ≅ X')
    (hX : S.IsColim X Y) : S.IsColim X' Y where
  ι_trans i j h φ := projHom_trans X' Y h φ
  exists_stage ψ := by
    obtain ⟨i, φ, hφ⟩ := hX.exists_stage ((pb S.limitToBase).map e.hom ≫ ψ)
    refine ⟨i, (pb (S.toBase i)).map e.inv ≫ φ, ?_⟩
    rw [projHom_map_comp, hφ, ← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨j, hij, hj⟩ := hX.exists_trans_eq i ((pb (S.toBase i)).map e.hom ≫ φ)
      ((pb (S.toBase i)).map e.hom ≫ φ') (by rw [projHom_map_comp, projHom_map_comp, hφ])
    refine ⟨j, hij, ?_⟩
    rw [trans_map_comp, trans_map_comp] at hj
    simpa only [← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp] using congrArg (fun t => (pb (S.toBase j)).map e.inv ≫ t) hj

/-- The statement depends on its second argument only up to isomorphism. -/
theorem IsColim.of_iso_snd [IsDirected J (· ≤ ·)] (X : DMod B) {Y Y' : DMod B} (e : Y ≅ Y')
    (hY : S.IsColim X Y) : S.IsColim X Y' where
  ι_trans i j h φ := projHom_trans X Y' h φ
  exists_stage ψ := by
    obtain ⟨i, φ, hφ⟩ := hY.exists_stage (ψ ≫ (pb S.limitToBase).map e.inv)
    refine ⟨i, φ ≫ (pb (S.toBase i)).map e.hom, ?_⟩
    rw [projHom_comp_map, hφ, Category.assoc, ← Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨j, hij, hj⟩ := hY.exists_trans_eq i (φ ≫ (pb (S.toBase i)).map e.inv)
      (φ' ≫ (pb (S.toBase i)).map e.inv) (by rw [projHom_comp_map, projHom_comp_map, hφ])
    refine ⟨j, hij, ?_⟩
    rw [trans_comp_map, trans_comp_map] at hj
    simpa only [Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id] using congrArg (fun t => t ≫ (pb (S.toBase j)).map e.hom) hj

/-! ### Binary biproducts in the first argument -/

/-- A morphism out of the image of a binary biproduct under an additive functor is the sum of
its two components. -/
theorem eq_map_fst_comp_add {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {A A' : C} [HasBinaryBiproduct A A'] {W : D}
    (x : F.obj (A ⊞ A') ⟶ W) :
    x = F.map biprod.fst ≫ F.map biprod.inl ≫ x + F.map biprod.snd ≫ F.map biprod.inr ≫ x := by
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← Preadditive.add_comp, ← F.map_add,
    biprod.total, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The statement is closed under binary biproducts in its first argument.** -/
theorem IsColim.biprod [IsDirected J (· ≤ ·)] {X₁ X₂ Y : DMod B} (h₁ : S.IsColim X₁ Y)
    (h₂ : S.IsColim X₂ Y) : S.IsColim (X₁ ⊞ X₂) Y where
  ι_trans i j h φ := projHom_trans _ Y h φ
  exists_stage ψ := by
    obtain ⟨i₁, φ₁, hφ₁⟩ := h₁.exists_stage ((pb S.limitToBase).map biprod.inl ≫ ψ)
    obtain ⟨i₂, φ₂, hφ₂⟩ := h₂.exists_stage ((pb S.limitToBase).map biprod.inr ≫ ψ)
    obtain ⟨m, h₁m, h₂m⟩ := directed_of (· ≤ ·) i₁ i₂
    refine ⟨m, (pb (S.toBase m)).map biprod.fst ≫ S.trans X₁ Y i₁ m h₁m φ₁ +
      (pb (S.toBase m)).map biprod.snd ≫ S.trans X₂ Y i₂ m h₂m φ₂, ?_⟩
    rw [projHom_add, projHom_map_comp, projHom_map_comp, projHom_trans, projHom_trans, hφ₁, hφ₂]
    exact (eq_map_fst_comp_add (pb S.limitToBase) ψ).symm
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨j₁, hij₁, hj₁⟩ := h₁.exists_trans_eq i ((pb (S.toBase i)).map biprod.inl ≫ φ)
      ((pb (S.toBase i)).map biprod.inl ≫ φ') (by rw [projHom_map_comp, projHom_map_comp, hφ])
    obtain ⟨j₂, hij₂, hj₂⟩ := h₂.exists_trans_eq i ((pb (S.toBase i)).map biprod.inr ≫ φ)
      ((pb (S.toBase i)).map biprod.inr ≫ φ') (by rw [projHom_map_comp, projHom_map_comp, hφ])
    obtain ⟨m, h₁m, h₂m⟩ := directed_of (· ≤ ·) j₁ j₂
    refine ⟨m, hij₁.trans h₁m, ?_⟩
    have e₁ := congrArg (S.trans X₁ Y j₁ m h₁m) hj₁
    have e₂ := congrArg (S.trans X₂ Y j₂ m h₂m) hj₂
    simp only [trans_trans, trans_map_comp] at e₁ e₂
    rw [show (hij₁.trans h₁m) = (hij₂.trans h₂m) from rfl] at e₁
    rw [eq_map_fst_comp_add (pb (S.toBase m)) (S.trans _ Y i m _ φ),
      eq_map_fst_comp_add (pb (S.toBase m)) (S.trans _ Y i m _ φ'), e₁, e₂]

/-! ### Distinguished triangles in the first argument -/

section Triangle

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  {A₁ A₂ A₃ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (h : A₃ ⟶ A₁⟦(1 : ℤ)⟧)
  (hT : Triangle.mk f g h ∈ distTriang C) {W : D}

include hT

/-- Exactness of `Hom(F(-), W)` at `F(A₂)` for a distinguished triangle. -/
theorem exists_eq_map_comp₂ (φ : F.obj A₂ ⟶ W) (hφ : F.map f ≫ φ = 0) :
    ∃ ψ : F.obj A₃ ⟶ W, φ = F.map g ≫ ψ :=
  Triangle.yoneda_exact₂ _ (F.map_distinguished _ hT) φ hφ

/-- Exactness of `Hom(F(-), W)` at `F(A₃)` for a distinguished triangle. -/
theorem exists_eq_map_comp₃ (φ : F.obj A₃ ⟶ W) (hφ : F.map g ≫ φ = 0) :
    ∃ ψ : F.obj (A₁⟦(1 : ℤ)⟧) ⟶ W, φ = F.map h ≫ ψ := by
  obtain ⟨ψ, hψ⟩ := Triangle.yoneda_exact₃ _ (F.map_distinguished _ hT) φ hφ
  exact ⟨((F.commShiftIso (1 : ℤ)).hom.app A₁) ≫ ψ, hψ.trans (Category.assoc _ _ _)⟩

/-- Exactness of `Hom(F(-), W)` at `F(A₁⟦1⟧)` for a distinguished triangle. -/
theorem exists_eq_map_comp₁ (φ : F.obj (A₁⟦(1 : ℤ)⟧) ⟶ W) (hφ : F.map h ≫ φ = 0) :
    ∃ ψ : F.obj (A₂⟦(1 : ℤ)⟧) ⟶ W, φ = F.map (f⟦(1 : ℤ)⟧') ≫ ψ := by
  obtain ⟨ψ, hψ⟩ := exists_eq_map_comp₃ F g h (-f⟦(1 : ℤ)⟧') (rot_of_distTriang _ hT) φ hφ
  refine ⟨-ψ, hψ.trans ?_⟩
  rw [F.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]

end Triangle

/-- **The five lemma: the statement is closed under distinguished triangles in its first
argument.** For a distinguished triangle `A₁ ⟶ A₂ ⟶ A₃ ⟶ A₁⟦1⟧` of `D(𝒪_B)`, the statement for
`A₁`, `A₂`, `A₁⟦1⟧` and `A₂⟦1⟧` gives the statement for `A₃`. -/
theorem IsColim.obj₃ [IsDirected J (· ≤ ·)] {A₁ A₂ A₃ Y : DMod B} {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃}
    {h : A₃ ⟶ A₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang (DMod B))
    (h₁ : S.IsColim A₁ Y) (h₂ : S.IsColim A₂ Y) (h₁' : S.IsColim (A₁⟦(1 : ℤ)⟧) Y)
    (h₂' : S.IsColim (A₂⟦(1 : ℤ)⟧) Y) : S.IsColim A₃ Y where
  ι_trans i j hij φ := projHom_trans A₃ Y hij φ
  exists_stage ψ := by
    obtain ⟨i, y, hy⟩ := h₂.exists_stage ((pb S.limitToBase).map g ≫ ψ)
    have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
    obtain ⟨j, hij, hj⟩ := h₁.exists_trans_eq i ((pb (S.toBase i)).map f ≫ y) 0 (by
      rw [projHom_map_comp, hy, projHom_zero, ← Functor.map_comp_assoc, hfg,
        Functor.map_zero, zero_comp])
    rw [trans_map_comp] at hj
    have hj' : (pb (S.toBase j)).map f ≫ S.trans A₂ Y i j hij y = 0 := by
      rw [hj, trans_zero]
    obtain ⟨x, hx⟩ := exists_eq_map_comp₂ (pb (S.toBase j)) f g h hT _ hj'
    have hd : (pb S.limitToBase).map g ≫ (S.projHom A₃ Y j x - ψ) = 0 := by
      rw [Preadditive.comp_sub, ← projHom_map_comp, ← hx, projHom_trans, hy, sub_self]
    obtain ⟨s, hs⟩ := exists_eq_map_comp₃ (pb S.limitToBase) f g h hT _ hd
    obtain ⟨k, z, hz⟩ := h₁'.exists_stage s
    obtain ⟨m, hjm, hkm⟩ := directed_of (· ≤ ·) j k
    refine ⟨m, S.trans A₃ Y j m hjm x - (pb (S.toBase m)).map h ≫ S.trans _ Y k m hkm z, ?_⟩
    rw [projHom_sub, projHom_map_comp, projHom_trans, projHom_trans, hz, ← hs, sub_sub_cancel]
  exists_trans_eq i x x' hxx := by
    have hw : S.projHom A₃ Y i (x - x') = 0 := by
      rw [projHom_sub, hxx, sub_self]
    obtain ⟨j, hij, hj⟩ := h₂.exists_trans_eq i ((pb (S.toBase i)).map g ≫ (x - x')) 0 (by
      rw [projHom_map_comp, hw, comp_zero, projHom_zero])
    rw [trans_map_comp, trans_zero] at hj
    obtain ⟨s, hs⟩ := exists_eq_map_comp₃ (pb (S.toBase j)) f g h hT _ hj
    have hps : (pb S.limitToBase).map h ≫ S.projHom _ Y j s = 0 := by
      rw [← projHom_map_comp, ← hs, projHom_trans, hw]
    obtain ⟨r, hr⟩ := exists_eq_map_comp₁ (pb S.limitToBase) f g h hT _ hps
    obtain ⟨k, q, hq⟩ := h₂'.exists_stage r
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) j k
    obtain ⟨m, hlm, hm⟩ := h₁'.exists_trans_eq l
      (S.trans _ Y j l hjl s - (pb (S.toBase l)).map (f⟦(1 : ℤ)⟧') ≫ S.trans _ Y k l hkl q) 0
      (by
        rw [projHom_sub, projHom_map_comp, projHom_trans, projHom_trans, hq, ← hr, sub_self,
          projHom_zero])
    refine ⟨m, hij.trans (hjl.trans hlm), ?_⟩
    rw [trans_sub, trans_zero, sub_eq_zero, trans_trans, trans_map_comp, trans_trans] at hm
    have hhf : h ≫ f⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
    have key : S.trans A₃ Y i m (hij.trans (hjl.trans hlm)) (x - x') = 0 := by
      rw [← trans_trans A₃ Y hij (hjl.trans hlm), hs, trans_map_comp, hm,
        ← Functor.map_comp_assoc, hhf, Functor.map_zero, zero_comp]
    rwa [trans_sub, sub_eq_zero] at key

/-! ### Morphisms of systems -/

/-- **A morphism of systems over `B`**, from `S'` to `S`: morphisms of schemes from the stages
and the vertex of `S'` to those of `S`, over `B` and compatible with the transition morphisms and
the projections. -/
structure Hom (S' S : SchemeSystem.{v, u} B J) where
  /-- The morphism of stages. -/
  app : ∀ j, S'.stage j ⟶ S.stage j
  app_toBase : ∀ j, app j ≫ S.toBase j = S'.toBase j
  app_transition : ∀ {i j : J} (h : i ≤ j), app j ≫ S.transition h = S'.transition h ≫ app i
  /-- The morphism of vertices. -/
  limitApp : S'.limit ⟶ S.limit
  limitApp_toBase : limitApp ≫ S.limitToBase = S'.limitToBase
  limitApp_proj : ∀ j, limitApp ≫ S.proj j = S'.proj j ≫ app j

namespace Hom

variable {S' : SchemeSystem.{v, u} B J} (α : Hom S' S) (X Y : DMod B)

/-- The map of morphism sets induced by a morphism of systems at a stage. -/
def stageMap (j : J) :
    ((pb (S.toBase j)).obj X ⟶ (pb (S.toBase j)).obj Y) →
      ((pb (S'.toBase j)).obj X ⟶ (pb (S'.toBase j)).obj Y) :=
  schemeFactorHom (α.app j) (S.toBase j) (S'.toBase j) (α.app_toBase j) X Y

/-- The map of morphism sets induced by a morphism of systems at the vertex. -/
def limitMap :
    ((pb S.limitToBase).obj X ⟶ (pb S.limitToBase).obj Y) →
      ((pb S'.limitToBase).obj X ⟶ (pb S'.limitToBase).obj Y) :=
  schemeFactorHom α.limitApp S.limitToBase S'.limitToBase α.limitApp_toBase X Y

/-- The stage maps of a morphism of systems commute with the transition maps. -/
theorem stageMap_trans {i j : J} (h : i ≤ j)
    (φ : (pb (S.toBase i)).obj X ⟶ (pb (S.toBase i)).obj Y) :
    α.stageMap X Y j (S.trans X Y i j h φ) = S'.trans X Y i j h (α.stageMap X Y i φ) := by
  exact schemeFactorHom_comp_comm _ _ _ _ _ _ _ _ (α.app_transition h) _ _ _ _ X Y φ

/-- The vertex map of a morphism of systems commutes with the maps to the vertex. -/
theorem limitMap_projHom (j : J) (φ : (pb (S.toBase j)).obj X ⟶ (pb (S.toBase j)).obj Y) :
    α.limitMap X Y (S.projHom X Y j φ) = S'.projHom X Y j (α.stageMap X Y j φ) := by
  exact schemeFactorHom_comp_comm _ _ _ _ _ _ _ _ (α.limitApp_proj j) _ _ _ _ X Y φ

/-- **Transfer along a morphism of systems inducing bijections on morphism sets.** -/
theorem isColim_iff (hst : ∀ j, Function.Bijective (α.stageMap X Y j))
    (hlim : Function.Bijective (α.limitMap X Y)) :
    S.IsColim X Y ↔ S'.IsColim X Y := by
  constructor
  · intro hS
    refine Stacks.IsStagesColimit.ofEquiv (S'.trans X Y) (S'.projHom X Y)
      (fun j => (Equiv.ofBijective _ (hst j)).symm) (Equiv.ofBijective _ hlim).symm ?_ ?_ hS
    · intro i j h s
      rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, stageMap_trans]
      exact congrArg _ (Equiv.ofBijective_apply_symm_apply _ (hst i) s).symm
    · intro i s
      rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, limitMap_projHom]
      exact congrArg _ (Equiv.ofBijective_apply_symm_apply _ (hst i) s).symm
  · intro hS'
    refine Stacks.IsStagesColimit.ofEquiv (S.trans X Y) (S.projHom X Y)
      (fun j => Equiv.ofBijective _ (hst j)) (Equiv.ofBijective _ hlim) ?_ ?_ hS'
    · intro i j h s
      simp only [Equiv.ofBijective_apply, stageMap_trans]
    · intro i s
      simp only [Equiv.ofBijective_apply, limitMap_projHom]

end Hom

/-! ### Change of base -/

/-- The system `S` read over `B'` through a morphism `f : B ⟶ B'`. -/
def comp {B' : Scheme.{u}} (f : B ⟶ B') : SchemeSystem.{v, u} B' J where
  stage := S.stage
  toBase j := S.toBase j ≫ f
  transition := S.transition
  transition_toBase h := by rw [← Category.assoc, S.transition_toBase]
  transition_comp := S.transition_comp
  transition_refl := S.transition_refl
  limit := S.limit
  limitToBase := S.limitToBase ≫ f
  proj := S.proj
  proj_toBase j := by rw [← Category.assoc, S.proj_toBase]
  proj_transition := S.proj_transition

/-- Conjugating by the comparison isomorphisms of two factorisations through `Lf^*` commutes
with the map attached to a further factorisation. -/
theorem schemeFactorHom_conj {V W Y B' : Scheme.{u}} (t : V ⟶ W) (a : W ⟶ Y) (b : V ⟶ Y)
    (f : Y ⟶ B') (hb : t ≫ a = b) (X Y' : DMod B')
    (φ : (pb a).obj ((pb f).obj X) ⟶ (pb a).obj ((pb f).obj Y')) :
    schemeFactorHom t (a ≫ f) (b ≫ f) (by rw [← Category.assoc, hb]) X Y'
        (((schemeFactorIso a f (a ≫ f) rfl).app X).inv ≫ φ ≫
          ((schemeFactorIso a f (a ≫ f) rfl).app Y').hom) =
      ((schemeFactorIso b f (b ≫ f) rfl).app X).inv ≫
        schemeFactorHom t a b hb ((pb f).obj X) ((pb f).obj Y') φ ≫
          ((schemeFactorIso b f (b ≫ f) rfl).app Y').hom := by
  have hiso : ∀ M : DMod B', (pb t).mapIso ((schemeFactorIso a f (a ≫ f) rfl).app M) ≪≫
      (schemeFactorIso t (a ≫ f) (b ≫ f) (by rw [← Category.assoc, hb])).app M =
      (schemeFactorIso t a b hb).app ((pb f).obj M) ≪≫
        (schemeFactorIso b f (b ≫ f) rfl).app M := fun M =>
    Iso.ext (schemeFactorIso_assoc t a f (a ≫ f) b (b ≫ f) rfl hb rfl
      (by rw [← Category.assoc, hb]) M).symm
  have hX := congrArg Iso.inv (hiso X)
  have hY := congrArg Iso.hom (hiso Y')
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Iso.app_inv, Iso.app_hom] at hX hY
  simp only [schemeFactorHom, Iso.homCongr_apply, Functor.map_comp, Category.assoc, Iso.app_inv,
    Iso.app_hom]
  rw [← reassoc_of% hX, hY]

/-- **Change of base.** The statement for `S` read over `B'` at `X`, `Y` is the statement for
`S` at `Lf^*X`, `Lf^*Y`. -/
theorem isColim_comp_iff [IsDirected J (· ≤ ·)] {B' : Scheme.{u}} (f : B ⟶ B') (X Y : DMod B') :
    (S.comp f).IsColim X Y ↔ S.IsColim ((pb f).obj X) ((pb f).obj Y) := by
  let e : ∀ j : J, ((pb (S.toBase j)).obj ((pb f).obj X) ⟶ (pb (S.toBase j)).obj ((pb f).obj Y))
      ≃ ((pb ((S.comp f).toBase j)).obj X ⟶ (pb ((S.comp f).toBase j)).obj Y) := fun j =>
    Iso.homCongr ((schemeFactorIso (S.toBase j) f (S.toBase j ≫ f) rfl).app X)
      ((schemeFactorIso (S.toBase j) f (S.toBase j ≫ f) rfl).app Y)
  let eT : ((pb S.limitToBase).obj ((pb f).obj X) ⟶ (pb S.limitToBase).obj ((pb f).obj Y))
      ≃ ((pb (S.comp f).limitToBase).obj X ⟶ (pb (S.comp f).limitToBase).obj Y) :=
    Iso.homCongr ((schemeFactorIso S.limitToBase f (S.limitToBase ≫ f) rfl).app X)
      ((schemeFactorIso S.limitToBase f (S.limitToBase ≫ f) rfl).app Y)
  have he : ∀ (i j : J) (h : i ≤ j) (s : (pb (S.toBase i)).obj ((pb f).obj X) ⟶
      (pb (S.toBase i)).obj ((pb f).obj Y)),
      e j (S.trans _ _ i j h s) = (S.comp f).trans X Y i j h (e i s) := fun i j h s =>
    (schemeFactorHom_conj (S.transition h) (S.toBase i) (S.toBase j) f (S.transition_toBase h)
      X Y s).symm
  have heT : ∀ (i : J) (s : (pb (S.toBase i)).obj ((pb f).obj X) ⟶
      (pb (S.toBase i)).obj ((pb f).obj Y)),
      eT (S.projHom _ _ i s) = (S.comp f).projHom X Y i (e i s) := fun i s =>
    (schemeFactorHom_conj (S.proj i) (S.toBase i) S.limitToBase f (S.proj_toBase i) X Y s).symm
  refine ⟨fun h => Stacks.IsStagesColimit.ofEquiv (S.trans _ _) (S.projHom _ _) e eT he heT h,
    fun h => Stacks.IsStagesColimit.ofEquiv ((S.comp f).trans X Y) ((S.comp f).projHom X Y)
      (fun j => (e j).symm) eT.symm ?_ ?_ h⟩
  · intro i j hij s
    apply (e j).injective
    rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]
  · intro i s
    apply eT.injective
    rw [Equiv.apply_symm_apply, heT, Equiv.apply_symm_apply]

end SchemeSystem

end Stacks.LimitHomDescent

end
