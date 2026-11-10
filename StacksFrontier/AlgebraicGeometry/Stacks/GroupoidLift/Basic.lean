module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartDescent.Transport

/-!
# Lifting arrows of a groupoid in presheaves on small algebras

Let `G` be a groupoid in presheaves of sets on the `κ`-small commutative `A'`-algebras whose
presheaf of objects is represented by an `A'`-algebra `P`: for every algebra `C` the arrows
`G.arr C` form a groupoid on the set `P →ₐ[A'] C`, naturally in `C`. This is what a smooth chart
`Spec P → 𝒳` of an algebraic stack produces, an arrow from `u₁` to `u₂` being an isomorphism of
the images of `u₁` and `u₂` in `𝒳`.

Fix a square-zero thickening `C' → C` with kernel `J` and a point `w : P → C`. Its lifts to `C'`
form a torsor under the module `Der w` of `A'`-derivations of `P` with values in `J`. Two lifts
are *related* when an arrow of `G` over `C'` reducing to the identity of `w` joins them; the
differences of related lifts span a submodule `S w`, and `Mod w = Der w / S w` is the module in
which the deformation theory of the chart takes place.

An arrow `r` of `G` over `C` *transports* lifts of its source to lifts of its target: lift `r`
with prescribed source, which is possible when the source map of `G` is formally smooth, and
take the target. The transport is well defined up to relation, and it is affine: its linear part
`Mod (src r) → Mod (tgt r)` is computed from the algebra of quadruples satisfying a linear
relation, `AlgebraicGeometry.Space.ChartDescent.relAlg`.

When `G` has a formally étale chart `b : Hom(Q, -) → G.arr` near the identity of `w`, the
relation is exactly membership of the difference in `S w`, and `S w` is the image of the
derivations of `Q` killed by the source map.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.Groupoid`: the groupoid.
* `AlgebraicGeometry.Stack.GroupoidLift.SqZero`: a square-zero thickening of small algebras.
* `AlgebraicGeometry.Stack.GroupoidLift.Der`, `S`, `Mod`: the modules.
* `AlgebraicGeometry.Stack.GroupoidLift.Tr`: the transport relation.
* `AlgebraicGeometry.Stack.GroupoidLift.transDer`: the linear part of the transport.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.tr_relation`: the transport preserves affine relations.
* `AlgebraicGeometry.Stack.GroupoidLift.transDer_eq`: the transport is affine.
* `AlgebraicGeometry.Stack.GroupoidLift.rel_iff_mem_S`: the relation is membership in `S`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}

/-- A groupoid in presheaves of sets on the `κ`-small `A'`-algebras whose presheaf of objects is
represented by `P`. `comp g f` is `g` after `f`. -/
structure Groupoid (A' : Type u) [CommRing A'] (κ : Cardinal.{u}) (P : Type u) [CommRing P]
    [Algebra A' P] where
  /-- The presheaf of arrows. -/
  arr : SmallAlg A' κ ⥤ Type u
  /-- The source of an arrow. -/
  src : ∀ {C : SmallAlg A' κ}, arr.obj C → (P →ₐ[A'] C.obj)
  /-- The target of an arrow. -/
  tgt : ∀ {C : SmallAlg A' κ}, arr.obj C → (P →ₐ[A'] C.obj)
  /-- The identity arrow of an object. -/
  idt : ∀ {C : SmallAlg A' κ}, (P →ₐ[A'] C.obj) → arr.obj C
  /-- Composition. -/
  comp : ∀ {C : SmallAlg A' κ} (g f : arr.obj C), src g = tgt f → arr.obj C
  /-- Inverse. -/
  inv : ∀ {C : SmallAlg A' κ}, arr.obj C → arr.obj C
  src_map : ∀ {C D : SmallAlg A' κ} (h : C ⟶ D) (g : arr.obj C),
    src (arr.map h g) = h.hom.hom.comp (src g)
  tgt_map : ∀ {C D : SmallAlg A' κ} (h : C ⟶ D) (g : arr.obj C),
    tgt (arr.map h g) = h.hom.hom.comp (tgt g)
  idt_map : ∀ {C D : SmallAlg A' κ} (h : C ⟶ D) (w : P →ₐ[A'] C.obj),
    arr.map h (idt w) = idt (h.hom.hom.comp w)
  comp_map : ∀ {C D : SmallAlg A' κ} (h : C ⟶ D) (g f : arr.obj C) (hgf : src g = tgt f),
    arr.map h (comp g f hgf) = comp (arr.map h g) (arr.map h f) (by rw [src_map, tgt_map, hgf])
  inv_map : ∀ {C D : SmallAlg A' κ} (h : C ⟶ D) (g : arr.obj C),
    arr.map h (inv g) = inv (arr.map h g)
  src_idt : ∀ {C : SmallAlg A' κ} (w : P →ₐ[A'] C.obj), src (idt w) = w
  tgt_idt : ∀ {C : SmallAlg A' κ} (w : P →ₐ[A'] C.obj), tgt (idt w) = w
  src_comp : ∀ {C : SmallAlg A' κ} (g f : arr.obj C) (hgf : src g = tgt f),
    src (comp g f hgf) = src f
  tgt_comp : ∀ {C : SmallAlg A' κ} (g f : arr.obj C) (hgf : src g = tgt f),
    tgt (comp g f hgf) = tgt g
  src_inv : ∀ {C : SmallAlg A' κ} (g : arr.obj C), src (inv g) = tgt g
  tgt_inv : ∀ {C : SmallAlg A' κ} (g : arr.obj C), tgt (inv g) = src g
  comp_idt : ∀ {C : SmallAlg A' κ} (g : arr.obj C), comp g (idt (src g)) (tgt_idt _).symm = g
  idt_comp : ∀ {C : SmallAlg A' κ} (g : arr.obj C), comp (idt (tgt g)) g (src_idt _) = g
  comp_inv : ∀ {C : SmallAlg A' κ} (g : arr.obj C),
    comp g (inv g) (tgt_inv g).symm = idt (tgt g)
  inv_comp : ∀ {C : SmallAlg A' κ} (g : arr.obj C), comp (inv g) g (src_inv g) = idt (src g)
  assoc : ∀ {C : SmallAlg A' κ} (h g f : arr.obj C) (hhg : src h = tgt g) (hgf : src g = tgt f),
    comp (comp h g hhg) f (by rw [src_comp]; exact hgf) =
      comp h (comp g f hgf) (by rw [tgt_comp]; exact hhg)

/-- A square-zero thickening of `κ`-small algebras. -/
structure SqZero (C' C : SmallAlg A' κ) where
  /-- The reduction. -/
  q : C' ⟶ C
  surj : Function.Surjective q.hom.hom
  sq : (RingHom.ker (q.hom.hom : C'.obj →+* C.obj)) ^ 2 = ⊥

variable {P : Type u} [CommRing P] [Algebra A' P]

/-- The source map of a groupoid is formally smooth: an arrow over the reduction of a
square-zero thickening lifts with any prescribed lift of its source. -/
def Groupoid.SrcFormallySmooth (G : Groupoid A' κ P) : Prop :=
  ∀ {C' C : SmallAlg A' κ} (e : SqZero C' C) (r : G.arr.obj C) (ℓ : P →ₐ[A'] C'.obj),
    e.q.hom.hom.comp ℓ = G.src r → ∃ r' : G.arr.obj C', G.arr.map e.q r' = r ∧ G.src r' = ℓ

namespace Groupoid

variable (G : Groupoid A' κ P)

/-- Composition respects equality of the composed arrows. -/
theorem comp_congr {C : SmallAlg A' κ} {g g' f f' : G.arr.obj C} (hg : g = g') (hf : f = f')
    (h : G.src g = G.tgt f) :
    G.comp g f h = G.comp g' f' (by rw [← hg, ← hf]; exact h) := by
  subst hg hf
  rfl

/-- The action of the presheaf of arrows on a composite of algebra maps. -/
theorem map_map {C D E : SmallAlg A' κ} (f : C ⟶ D) (g : D ⟶ E) (x : G.arr.obj C) :
    G.arr.map g (G.arr.map f x) = G.arr.map (f ≫ g) x := by
  rw [Functor.map_comp, types_comp_apply]

/-- The inverse of an identity arrow is itself. -/
theorem inv_idt {C : SmallAlg A' κ} (w : P →ₐ[A'] C.obj) : G.inv (G.idt w) = G.idt w := by
  have h1 := G.comp_idt (G.inv (G.idt w))
  have h2 := G.inv_comp (G.idt w)
  have hs : G.src (G.inv (G.idt w)) = w := by rw [G.src_inv, G.tgt_idt]
  have key : G.comp (G.inv (G.idt w)) (G.idt (G.src (G.inv (G.idt w))))
      (G.tgt_idt _).symm = G.comp (G.inv (G.idt w)) (G.idt w) (G.src_inv _) := by
    congr 2
  rw [key, h2, G.src_idt] at h1
  exact h1.symm

end Groupoid

section Thickening

variable {C' C : SmallAlg A' κ} (e : SqZero C' C)

/-- The product of two elements of the kernel of a square-zero thickening vanishes. -/
theorem SqZero.mul_eq_zero {x y : C'.obj} (hx : e.q.hom.hom x = 0) (hy : e.q.hom.hom y = 0) :
    x * y = 0 :=
  mul_eq_zero_of_ker e.q.hom.hom e.sq hx hy

/-- The `A'`-derivations of an algebra `P` along a point `w : P → C`, with values in the kernel
of the thickening, as linear maps into `C'`. The Leibniz rule is asked along every choice of
lifts of the values of `w`; since the kernel has square zero, all choices give the same
condition. -/
def Der {P : Type u} [CommRing P] [Algebra A' P] (w : P →ₐ[A'] C.obj) :
    Submodule C'.obj (P →ₗ[A'] C'.obj) where
  carrier := {D | (∀ x, e.q.hom.hom (D x) = 0) ∧ ∀ (x y : P) (a b : C'.obj),
    e.q.hom.hom a = w x → e.q.hom.hom b = w y → D (x * y) = a * D y + b * D x}
  add_mem' := by
    rintro D E ⟨hD, hD'⟩ ⟨hE, hE'⟩
    refine ⟨fun x ↦ by simp [hD x, hE x], fun x y a b ha hb ↦ ?_⟩
    simp only [LinearMap.add_apply, hD' x y a b ha hb, hE' x y a b ha hb]
    ring
  zero_mem' := ⟨fun _ ↦ by simp, fun _ _ _ _ _ _ ↦ by simp⟩
  smul_mem' := by
    rintro c D ⟨hD, hD'⟩
    refine ⟨fun x ↦ by simp [hD x], fun x y a b ha hb ↦ ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul, hD' x y a b ha hb]
    ring

variable {e}

/-- A derivation vanishes on `1`. -/
theorem Der.map_one {w : P →ₐ[A'] C.obj} {D : P →ₗ[A'] C'.obj} (hD : D ∈ Der e w) : D 1 = 0 := by
  have h := hD.2 1 1 1 1 (by simp) (by simp)
  simp only [mul_one, one_mul] at h
  linear_combination -h

/-- The Leibniz rule for a derivation along `w`, with respect to a lift `ℓ` of `w`. -/
theorem Der.leibniz {w : P →ₐ[A'] C.obj} {D : P →ₗ[A'] C'.obj} (hD : D ∈ Der e w)
    (ℓ : P →ₐ[A'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w) (x y : P) :
    D (x * y) = ℓ x * D y + ℓ y * D x :=
  hD.2 x y (ℓ x) (ℓ y) (congrArg (fun f : P →ₐ[A'] C.obj ↦ f x) hℓ)
    (congrArg (fun f : P →ₐ[A'] C.obj ↦ f y) hℓ)

/-- Adding a derivation to a lift. -/
def addLift {w : P →ₐ[A'] C.obj} (D : P →ₗ[A'] C'.obj) (hD : D ∈ Der e w)
    (ℓ : P →ₐ[A'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w) : P →ₐ[A'] C'.obj where
  toFun x := ℓ x + D x
  map_one' := by simp [Der.map_one hD]
  map_mul' x y := by
    have hz := e.mul_eq_zero (hD.1 x) (hD.1 y)
    simp only [map_mul, Der.leibniz hD ℓ hℓ]
    linear_combination -hz
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; ring
  commutes' a := by
    have : D (algebraMap A' P a) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, Der.map_one hD, smul_zero]
    simp [this]

/-- The value of a lift plus a derivation. -/
@[simp] theorem addLift_apply {w : P →ₐ[A'] C.obj} (D : P →ₗ[A'] C'.obj) (hD : D ∈ Der e w)
    (ℓ : P →ₐ[A'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w) (x : P) :
    addLift D hD ℓ hℓ x = ℓ x + D x := rfl

/-- A lift plus a derivation is again a lift of the same point. -/
theorem addLift_reduce {w : P →ₐ[A'] C.obj} (D : P →ₗ[A'] C'.obj) (hD : D ∈ Der e w)
    (ℓ : P →ₐ[A'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w) :
    e.q.hom.hom.comp (addLift D hD ℓ hℓ) = w := by
  ext x
  change e.q.hom.hom (ℓ x + D x) = w x
  rw [map_add, hD.1 x, add_zero]
  exact congrArg (fun f : P →ₐ[A'] C.obj ↦ f x) hℓ

/-- The difference of two lifts is a derivation. -/
theorem sub_mem_Der {w : P →ₐ[A'] C.obj} {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj}
    (h₁ : e.q.hom.hom.comp ℓ₁ = w) (h₂ : e.q.hom.hom.comp ℓ₂ = w) :
    ℓ₂.toLinearMap - ℓ₁.toLinearMap ∈ Der e w := by
  have hx : ∀ x, e.q.hom.hom (ℓ₂ x - ℓ₁ x) = 0 := fun x ↦ by
    rw [map_sub, ← AlgHom.comp_apply, ← AlgHom.comp_apply, h₁, h₂, sub_self]
  refine ⟨fun x ↦ hx x, fun x y a b ha hb ↦ ?_⟩
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_mul]
  have ea : e.q.hom.hom (ℓ₂ x - a) = 0 := by
    rw [map_sub, ha, ← AlgHom.comp_apply, h₂, sub_self]
  have eb : e.q.hom.hom (ℓ₁ y - b) = 0 := by
    rw [map_sub, hb, ← AlgHom.comp_apply, h₁, sub_self]
  have z₁ := e.mul_eq_zero ea (hx y)
  have z₂ := e.mul_eq_zero eb (hx x)
  linear_combination z₁ + z₂

/-- The underlying linear map of `addLift D hD ℓ hℓ` is `ℓ + D`. -/
theorem addLift_toLinearMap {w : P →ₐ[A'] C.obj} (D : P →ₗ[A'] C'.obj) (hD : D ∈ Der e w)
    (ℓ : P →ₐ[A'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w) :
    (addLift D hD ℓ hℓ).toLinearMap = ℓ.toLinearMap + D := by
  ext x
  rfl

/-- Every lift is the given lift plus a derivation. -/
theorem eq_addLift {w : P →ₐ[A'] C.obj} {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj}
    (h₁ : e.q.hom.hom.comp ℓ₁ = w) (h₂ : e.q.hom.hom.comp ℓ₂ = w) :
    ℓ₂ = addLift (ℓ₂.toLinearMap - ℓ₁.toLinearMap) (sub_mem_Der h₁ h₂) ℓ₁ h₁ := by
  ext x
  simp

end Thickening

/-! ### Relation and transport -/

section Transport

variable (G : Groupoid A' κ P) {C' C : SmallAlg A' κ} (e : SqZero C' C)

/-- `ℓ₁` is transported to `ℓ₂` along `r`: some lift of `r` has source `ℓ₁` and target `ℓ₂`. -/
def Tr (r : G.arr.obj C) (ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj) : Prop :=
  ∃ g : G.arr.obj C', G.arr.map e.q g = r ∧ G.src g = ℓ₁ ∧ G.tgt g = ℓ₂

/-- Two lifts of `w` are related when an arrow reducing to the identity of `w` joins them. -/
abbrev Rel (w : P →ₐ[A'] C.obj) (ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj) : Prop := Tr G e (G.idt w) ℓ₁ ℓ₂

variable {G e}

/-- The source of a transport lifts the source of the arrow. -/
theorem Tr.reduce_src {r : G.arr.obj C} {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj} (h : Tr G e r ℓ₁ ℓ₂) :
    e.q.hom.hom.comp ℓ₁ = G.src r := by
  obtain ⟨g, hg, h₁, -⟩ := h
  rw [← hg, G.src_map, h₁]

/-- The target of a transport lifts the target of the arrow. -/
theorem Tr.reduce_tgt {r : G.arr.obj C} {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj} (h : Tr G e r ℓ₁ ℓ₂) :
    e.q.hom.hom.comp ℓ₂ = G.tgt r := by
  obtain ⟨g, hg, -, h₂⟩ := h
  rw [← hg, G.tgt_map, h₂]

/-- Every lift is related to itself. -/
theorem rel_refl (ℓ : P →ₐ[A'] C'.obj) : Rel G e (e.q.hom.hom.comp ℓ) ℓ ℓ :=
  ⟨G.idt ℓ, G.idt_map _ _, G.src_idt _, G.tgt_idt _⟩

/-- Transports compose. -/
private theorem tr_comp {r₁ r₂ : G.arr.obj C} (h : G.src r₂ = G.tgt r₁)
    {ℓ₁ ℓ₂ ℓ₃ : P →ₐ[A'] C'.obj} (h₁ : Tr G e r₁ ℓ₁ ℓ₂) (h₂ : Tr G e r₂ ℓ₂ ℓ₃) :
    Tr G e (G.comp r₂ r₁ h) ℓ₁ ℓ₃ := by
  obtain ⟨g₁, hg₁, hs₁, ht₁⟩ := h₁
  obtain ⟨g₂, hg₂, hs₂, ht₂⟩ := h₂
  have hc : G.src g₂ = G.tgt g₁ := by rw [hs₂, ht₁]
  refine ⟨G.comp g₂ g₁ hc, ?_, ?_, ?_⟩
  · rw [G.comp_map, G.comp_congr hg₂ hg₁]
  · rw [G.src_comp, hs₁]
  · rw [G.tgt_comp, ht₂]

/-- Transports invert. -/
private theorem tr_inv {r : G.arr.obj C} {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj} (h : Tr G e r ℓ₁ ℓ₂) :
    Tr G e (G.inv r) ℓ₂ ℓ₁ := by
  obtain ⟨g, hg, hs, ht⟩ := h
  exact ⟨G.inv g, by rw [G.inv_map, hg], by rw [G.src_inv, ht], by rw [G.tgt_inv, hs]⟩

/-- Two transports of the same lift are related. -/
theorem Tr.rel {r : G.arr.obj C} {ℓ m₁ m₂ : P →ₐ[A'] C'.obj} (h₁ : Tr G e r ℓ m₁)
    (h₂ : Tr G e r ℓ m₂) : Rel G e (G.tgt r) m₁ m₂ := by
  have := tr_comp (G.tgt_inv r).symm (tr_inv h₁) h₂
  rwa [G.comp_inv] at this

/-- A related lift may replace the source of a transport. -/
theorem Tr.of_rel_src {r : G.arr.obj C} {ℓ ℓ' m : P →ₐ[A'] C'.obj}
    (hℓ : Rel G e (G.src r) ℓ ℓ') (h : Tr G e r ℓ m) : Tr G e r ℓ' m := by
  have := tr_comp (by rw [G.tgt_inv, G.src_idt]) (tr_inv hℓ) h
  rwa [G.comp_congr rfl (G.inv_idt _), G.comp_idt] at this

/-- A related lift may replace the target of a transport. -/
theorem Tr.of_rel_tgt {r : G.arr.obj C} {ℓ m m' : P →ₐ[A'] C'.obj}
    (h : Tr G e r ℓ m) (hm : Rel G e (G.tgt r) m m') : Tr G e r ℓ m' := by
  have := tr_comp (G.src_idt _) h hm
  rwa [G.idt_comp] at this

/-- Transports compose. -/
theorem Tr.comp {r₁ r₂ : G.arr.obj C} (h : G.src r₂ = G.tgt r₁) {ℓ₁ ℓ₂ ℓ₃ : P →ₐ[A'] C'.obj}
    (h₁ : Tr G e r₁ ℓ₁ ℓ₂) (h₂ : Tr G e r₂ ℓ₂ ℓ₃) : Tr G e (G.comp r₂ r₁ h) ℓ₁ ℓ₃ :=
  tr_comp h h₁ h₂

/-- Transports invert. -/
theorem Tr.inv {r : G.arr.obj C} {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj} (h : Tr G e r ℓ₁ ℓ₂) :
    Tr G e (G.inv r) ℓ₂ ℓ₁ :=
  tr_inv h

/-- The relation on lifts is symmetric. -/
theorem Rel.symm {w : P →ₐ[A'] C.obj} {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj} (h : Rel G e w ℓ₁ ℓ₂) :
    Rel G e w ℓ₂ ℓ₁ := by
  have := h.inv
  rwa [G.inv_idt] at this

/-- The relation on lifts is transitive. -/
theorem Rel.trans {w : P →ₐ[A'] C.obj} {ℓ₁ ℓ₂ ℓ₃ : P →ₐ[A'] C'.obj} (h₁ : Rel G e w ℓ₁ ℓ₂)
    (h₂ : Rel G e w ℓ₂ ℓ₃) : Rel G e w ℓ₁ ℓ₃ := by
  have := Tr.of_rel_tgt h₁ (by rwa [G.tgt_idt])
  exact this

/-- Lifts exist when the source map is formally smooth. -/
theorem exists_tr (hG : G.SrcFormallySmooth) (r : G.arr.obj C) (ℓ : P →ₐ[A'] C'.obj)
    (hℓ : e.q.hom.hom.comp ℓ = G.src r) : ∃ m, Tr G e r ℓ m := by
  obtain ⟨g, hg, hs⟩ := hG e r ℓ hℓ
  exact ⟨G.tgt g, g, hg, hs, rfl⟩

/-- A morphism of thickenings: `φ' : C' → D'` over `φ : C → D`. -/
structure SqZero.Hom {D' D : SmallAlg A' κ} (e : SqZero C' C) (e₂ : SqZero D' D) where
  /-- The map of thickenings. -/
  top : C' ⟶ D'
  /-- The map of reductions. -/
  bot : C ⟶ D
  w : top ≫ e₂.q = e.q ≫ bot

/-- Transports are natural in the thickening. -/
theorem Tr.map {D' D : SmallAlg A' κ} {e₂ : SqZero D' D} (φ : SqZero.Hom e e₂)
    {r : G.arr.obj C} {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj} (h : Tr G e r ℓ₁ ℓ₂) :
    Tr G e₂ (G.arr.map φ.bot r) (φ.top.hom.hom.comp ℓ₁) (φ.top.hom.hom.comp ℓ₂) := by
  obtain ⟨g, hg, hs, ht⟩ := h
  refine ⟨G.arr.map φ.top g, ?_, by rw [G.src_map, hs], by rw [G.tgt_map, ht]⟩
  rw [G.map_map, φ.w, ← G.map_map, hg]

end Transport

/-! ### The modules -/

section Modules

variable (G : Groupoid A' κ P) {C' C : SmallAlg A' κ} (e : SqZero C' C)

/-- The span of the differences of related lifts of `w`. -/
def S (w : P →ₐ[A'] C.obj) : Submodule C'.obj (P →ₗ[A'] C'.obj) :=
  Submodule.span C'.obj {D | ∃ ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj, e.q.hom.hom.comp ℓ₁ = w ∧
    Rel G e w ℓ₁ ℓ₂ ∧ D = ℓ₂.toLinearMap - ℓ₁.toLinearMap}

variable {G e}

/-- The difference of two related lifts lies in `S`. -/
theorem sub_mem_S {w : P →ₐ[A'] C.obj} {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj}
    (h₁ : e.q.hom.hom.comp ℓ₁ = w) (h : Rel G e w ℓ₁ ℓ₂) :
    ℓ₂.toLinearMap - ℓ₁.toLinearMap ∈ S G e w :=
  Submodule.subset_span ⟨ℓ₁, ℓ₂, h₁, h, rfl⟩

/-- `S G e w` consists of derivations. -/
theorem S_le_Der (w : P →ₐ[A'] C.obj) : S G e w ≤ Der e w := by
  refine Submodule.span_le.mpr ?_
  rintro D ⟨ℓ₁, ℓ₂, h₁, h, rfl⟩
  have h₂ := h.reduce_tgt
  rw [G.tgt_idt] at h₂
  exact sub_mem_Der h₁ h₂

variable (G e) in
/-- The module of derivations modulo the differences of related lifts. -/
abbrev Mod (w : P →ₐ[A'] C.obj) : Type u :=
  Der e w ⧸ (S G e w).comap (Der e w).subtype

/-- The class of a derivation. -/
abbrev mkMod {w : P →ₐ[A'] C.obj} (D : P →ₗ[A'] C'.obj) (hD : D ∈ Der e w) : Mod G e w :=
  Submodule.Quotient.mk ⟨D, hD⟩

/-- Two derivations have the same class in `Mod` if and only if their difference lies in `S`. -/
theorem mkMod_eq_mkMod_iff {w : P →ₐ[A'] C.obj} {D₁ D₂ : P →ₗ[A'] C'.obj} (h₁ : D₁ ∈ Der e w)
    (h₂ : D₂ ∈ Der e w) : (mkMod D₁ h₁ : Mod G e w) = mkMod D₂ h₂ ↔ D₁ - D₂ ∈ S G e w := by
  rw [Submodule.Quotient.eq]
  rfl

/-- The class of a derivation in `Mod` vanishes if and only if it lies in `S`. -/
theorem mkMod_eq_zero_iff {w : P →ₐ[A'] C.obj} {D : P →ₗ[A'] C'.obj} (h : D ∈ Der e w) :
    (mkMod D h : Mod G e w) = 0 ↔ D ∈ S G e w := by
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

end Modules

/-! ### The linear part of the transport -/

section Linear

variable {G : Groupoid A' κ P} {C' C : SmallAlg A' κ} {e : SqZero C' C}

/-- The algebra of quadruples, as a thickening of `C`. -/
def relSqZero (hκ : Cardinal.aleph0 ≤ κ) (e : SqZero C' C) (b : C'.obj) :
    SqZero (SmallAlg.mk (relAlg e.q.hom.hom e.sq b) (Chart.relAlg_card_lt hκ e.q e.sq b)) C where
  q := SmallAlg.homMk (relRed e.q.hom.hom e.sq b)
  surj := relRed_surjective e.q.hom.hom e.sq b e.surj
  sq := relRed_ker_sq e.q.hom.hom e.sq b

/-- **The transport preserves affine relations among lifts, up to relation.** -/
theorem tr_relation (hκ : Cardinal.aleph0 ≤ κ) (hG : G.SrcFormallySmooth) (b : C'.obj)
    (r : G.arr.obj C) {ℓ₁ ℓ₂ ℓ₃ ℓ₄ m₁ m₂ m₃ m₄ : P →ₐ[A'] C'.obj}
    (h₂ : e.q.hom.hom.comp ℓ₂ = e.q.hom.hom.comp ℓ₁)
    (h₃ : e.q.hom.hom.comp ℓ₃ = e.q.hom.hom.comp ℓ₁)
    (h₄ : e.q.hom.hom.comp ℓ₄ = e.q.hom.hom.comp ℓ₁)
    (hrel : ∀ x, ℓ₄ x - ℓ₃ x = b * (ℓ₂ x - ℓ₁ x))
    (t₁ : Tr G e r ℓ₁ m₁) (t₂ : Tr G e r ℓ₂ m₂) (t₃ : Tr G e r ℓ₃ m₃) (t₄ : Tr G e r ℓ₄ m₄) :
    (m₄.toLinearMap - m₃.toLinearMap) - b • (m₂.toLinearMap - m₁.toLinearMap) ∈
      S G e (G.tgt r) := by
  let eR := relSqZero hκ e b
  let L : P →ₐ[A'] relAlg e.q.hom.hom e.sq b :=
    relLift e.q.hom.hom e.sq b ℓ₁ ℓ₂ ℓ₃ ℓ₄ h₂ h₃ h₄ hrel
  have hL : eR.q.hom.hom.comp L = G.src r := t₁.reduce_src
  obtain ⟨g, hg, hgs⟩ := hG eR r L hL
  let pr : Fin 4 → (SmallAlg.mk (relAlg e.q.hom.hom e.sq b)
      (Chart.relAlg_card_lt hκ e.q e.sq b) ⟶ C') :=
    fun k ↦ SmallAlg.homMk (relProj e.q.hom.hom e.sq b k)
  have hpr : ∀ k, pr k ≫ e.q = eR.q := fun k ↦
    ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (relRed_eq e.q.hom.hom e.sq b k))
  have key : ∀ (k : Fin 4) (ℓ : P →ₐ[A'] C'.obj), (relProj e.q.hom.hom e.sq b k).comp L = ℓ →
      Tr G e r ℓ ((relProj e.q.hom.hom e.sq b k).comp (G.tgt g)) := by
    intro k ℓ hk
    refine ⟨G.arr.map (pr k) g, ?_, ?_, ?_⟩
    · rw [G.map_map, hpr, hg]
    · rw [G.src_map, hgs]
      exact hk
    · rw [G.tgt_map]
      rfl
  have s₁ := sub_mem_S (key 0 ℓ₁ rfl).reduce_tgt ((key 0 ℓ₁ rfl).rel t₁)
  have s₂ := sub_mem_S (key 1 ℓ₂ rfl).reduce_tgt ((key 1 ℓ₂ rfl).rel t₂)
  have s₃ := sub_mem_S (key 2 ℓ₃ rfl).reduce_tgt ((key 2 ℓ₃ rfl).rel t₃)
  have s₄ := sub_mem_S (key 3 ℓ₄ rfl).reduce_tgt ((key 3 ℓ₄ rfl).rel t₄)
  have hzero : (((relProj e.q.hom.hom e.sq b 3).comp (G.tgt g)).toLinearMap -
      ((relProj e.q.hom.hom e.sq b 2).comp (G.tgt g)).toLinearMap) -
      b • (((relProj e.q.hom.hom e.sq b 1).comp (G.tgt g)).toLinearMap -
        ((relProj e.q.hom.hom e.sq b 0).comp (G.tgt g)).toLinearMap) = 0 := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply, smul_eq_mul]
    rw [relation_of_map e.q.hom.hom e.sq b (G.tgt g) x, sub_self]
  have : (m₄.toLinearMap - m₃.toLinearMap) - b • (m₂.toLinearMap - m₁.toLinearMap) =
      (m₄.toLinearMap - ((relProj e.q.hom.hom e.sq b 3).comp (G.tgt g)).toLinearMap) -
      (m₃.toLinearMap - ((relProj e.q.hom.hom e.sq b 2).comp (G.tgt g)).toLinearMap) -
      b • ((m₂.toLinearMap - ((relProj e.q.hom.hom e.sq b 1).comp (G.tgt g)).toLinearMap) -
        (m₁.toLinearMap - ((relProj e.q.hom.hom e.sq b 0).comp (G.tgt g)).toLinearMap)) +
      ((((relProj e.q.hom.hom e.sq b 3).comp (G.tgt g)).toLinearMap -
      ((relProj e.q.hom.hom e.sq b 2).comp (G.tgt g)).toLinearMap) -
      b • (((relProj e.q.hom.hom e.sq b 1).comp (G.tgt g)).toLinearMap -
        ((relProj e.q.hom.hom e.sq b 0).comp (G.tgt g)).toLinearMap)) := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      AlgHom.toLinearMap_apply]
    ring
  rw [this, hzero, add_zero]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ s₄ s₃) (Submodule.smul_mem _ _
    (Submodule.sub_mem _ s₂ s₁))

variable (hκ : Cardinal.aleph0 ≤ κ) (hG : G.SrcFormallySmooth)

/-- A chosen transport of a lift along an arrow. -/
noncomputable def trans (hG : G.SrcFormallySmooth) (r : G.arr.obj C) (ℓ : P →ₐ[A'] C'.obj)
    (hℓ : e.q.hom.hom.comp ℓ = G.src r) : P →ₐ[A'] C'.obj :=
  (exists_tr hG r ℓ hℓ).choose

/-- The chosen transport `trans hG r ℓ hℓ` is a transport of `ℓ` along `r`. -/
theorem trans_spec (r : G.arr.obj C) (ℓ : P →ₐ[A'] C'.obj)
    (hℓ : e.q.hom.hom.comp ℓ = G.src r) : Tr G e r ℓ (trans hG r ℓ hℓ) :=
  (exists_tr hG r ℓ hℓ).choose_spec

/-- **The linear part of the transport along an arrow**, measured from a base lift `ℓ₀` of the
source; it does not depend on `ℓ₀` (`transDer_eq`). -/
noncomputable def transDer (r : G.arr.obj C) (ℓ₀ : P →ₐ[A'] C'.obj)
    (h₀ : e.q.hom.hom.comp ℓ₀ = G.src r) : Der e (G.src r) →ₗ[C'.obj] Mod G e (G.tgt r) where
  toFun D := mkMod ((trans hG r (addLift D.1 D.2 ℓ₀ h₀) (addLift_reduce _ _ _ _)).toLinearMap -
    (trans hG r ℓ₀ h₀).toLinearMap)
    (sub_mem_Der (trans_spec hG r ℓ₀ h₀).reduce_tgt (trans_spec hG r _ _).reduce_tgt)
  map_add' D E := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    have r₂ := (addLift_reduce D.1 D.2 ℓ₀ h₀).trans h₀.symm
    have r₃ := (addLift_reduce E.1 E.2 ℓ₀ h₀).trans h₀.symm
    have r₄ := (addLift_reduce (D + E).1 (D + E).2 ℓ₀ h₀).trans h₀.symm
    have h := tr_relation hκ hG 1 r r₂ r₃ r₄
      (fun x ↦ by simp only [addLift_apply, Submodule.coe_add, LinearMap.add_apply]; ring)
      (trans_spec hG r ℓ₀ h₀) (trans_spec hG r _ (addLift_reduce D.1 D.2 ℓ₀ h₀))
      (trans_spec hG r _ (addLift_reduce E.1 E.2 ℓ₀ h₀))
      (trans_spec hG r _ (addLift_reduce (D + E).1 (D + E).2 ℓ₀ h₀))
    change _ ∈ S G e (G.tgt r)
    convert h using 1
    simp only [map_sub, map_add, Submodule.subtype_apply, one_smul]
    abel
  map_smul' c D := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    have r₂ := (addLift_reduce D.1 D.2 ℓ₀ h₀).trans h₀.symm
    have r₄ := (addLift_reduce (c • D).1 (c • D).2 ℓ₀ h₀).trans h₀.symm
    have h := tr_relation hκ hG c r r₂ rfl r₄
      (fun x ↦ by
        simp only [addLift_apply, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
      (trans_spec hG r ℓ₀ h₀) (trans_spec hG r _ (addLift_reduce D.1 D.2 ℓ₀ h₀))
      (trans_spec hG r ℓ₀ h₀) (trans_spec hG r _ (addLift_reduce (c • D).1 (c • D).2 ℓ₀ h₀))
    change _ ∈ S G e (G.tgt r)
    convert h using 1
    simp only [map_sub, map_smul, Submodule.subtype_apply]

/-- **The transport is affine**: the difference of two transports is the linear part applied to
the difference of the transported lifts. -/
theorem transDer_eq (r : G.arr.obj C) (ℓ₀ : P →ₐ[A'] C'.obj)
    (h₀ : e.q.hom.hom.comp ℓ₀ = G.src r) {ℓ ℓ' m m' : P →ₐ[A'] C'.obj}
    (hℓ : e.q.hom.hom.comp ℓ = G.src r) (hℓ' : e.q.hom.hom.comp ℓ' = G.src r)
    (t : Tr G e r ℓ m) (t' : Tr G e r ℓ' m') :
    transDer hκ hG r ℓ₀ h₀ ⟨ℓ'.toLinearMap - ℓ.toLinearMap, sub_mem_Der hℓ hℓ'⟩ =
      mkMod (m'.toLinearMap - m.toLinearMap) (sub_mem_Der t.reduce_tgt t'.reduce_tgt) := by
  change mkMod _ _ = _
  rw [mkMod_eq_mkMod_iff]
  have h := tr_relation hκ hG 1 r (hℓ'.trans hℓ.symm) (h₀.trans hℓ.symm)
    ((addLift_reduce _ (sub_mem_Der hℓ hℓ') ℓ₀ h₀).trans hℓ.symm)
    (fun x ↦ by simp)
    t t' (trans_spec hG r ℓ₀ h₀) (trans_spec hG r _ (addLift_reduce _ (sub_mem_Der hℓ hℓ') ℓ₀ h₀))
  rw [one_smul] at h
  exact h

/-- The linear part of the transport vanishes on `S`. -/
theorem transDer_eq_zero_of_mem (r : G.arr.obj C) (ℓ₀ : P →ₐ[A'] C'.obj)
    (h₀ : e.q.hom.hom.comp ℓ₀ = G.src r) {D : P →ₗ[A'] C'.obj} (hDS : D ∈ S G e (G.src r)) :
    ∀ hD : D ∈ Der e (G.src r), transDer hκ hG r ℓ₀ h₀ ⟨D, hD⟩ = 0 := by
  induction hDS using Submodule.span_induction with
  | mem D hD₀ =>
    obtain ⟨ℓ₁, ℓ₂, h₁, hrel, rfl⟩ := hD₀
    intro hD
    have t₁ := trans_spec hG r ℓ₁ h₁
    have t₂ := Tr.of_rel_src hrel t₁
    have h₂ := hrel.reduce_tgt
    rw [G.tgt_idt] at h₂
    rw [transDer_eq hκ hG r ℓ₀ h₀ h₁ h₂ t₁ t₂, mkMod_eq_zero_iff, sub_self]
    exact Submodule.zero_mem _
  | zero => intro hD; exact map_zero _
  | add x y hx hy ihx ihy =>
    intro hD
    have := map_add (transDer hκ hG r ℓ₀ h₀) ⟨x, S_le_Der _ hx⟩ ⟨y, S_le_Der _ hy⟩
    rw [ihx, ihy, add_zero] at this
    exact this
  | smul c x hx ihx =>
    intro hD
    have := map_smul (transDer hκ hG r ℓ₀ h₀) c ⟨x, S_le_Der _ hx⟩
    rw [ihx, smul_zero] at this
    exact this

/-- **The transport on `Mod`.** -/
noncomputable def transMod (r : G.arr.obj C) (ℓ₀ : P →ₐ[A'] C'.obj)
    (h₀ : e.q.hom.hom.comp ℓ₀ = G.src r) : Mod G e (G.src r) →ₗ[C'.obj] Mod G e (G.tgt r) :=
  Submodule.liftQ _ (transDer hκ hG r ℓ₀ h₀) fun D hD ↦
    transDer_eq_zero_of_mem hκ hG r ℓ₀ h₀ hD D.2

/-- The value of `transMod` on the class of a derivation. -/
theorem transMod_mk (r : G.arr.obj C) (ℓ₀ : P →ₐ[A'] C'.obj)
    (h₀ : e.q.hom.hom.comp ℓ₀ = G.src r) (D : P →ₗ[A'] C'.obj) (hD : D ∈ Der e (G.src r)) :
    transMod hκ hG r ℓ₀ h₀ (mkMod D hD) = transDer hκ hG r ℓ₀ h₀ ⟨D, hD⟩ := rfl

end Linear

/-! ### A formally étale chart near the identities -/

section Chart

variable {G : Groupoid A' κ P} {C' C : SmallAlg A' κ} {e : SqZero C' C}
  {Q : Type u} [CommRing Q] [Algebra A' Q]

/-- Precomposition with an algebra map, as a `C'`-linear map. -/
def precomp (C' : SmallAlg A' κ) (φ : P →ₐ[A'] Q) :
    (Q →ₗ[A'] C'.obj) →ₗ[C'.obj] (P →ₗ[A'] C'.obj) where
  toFun E := E.comp φ.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Precomposing a derivation along `v` with an algebra map `φ` gives a derivation along
`v ∘ φ`. -/
theorem Der.comp {v : Q →ₐ[A'] C.obj} {E : Q →ₗ[A'] C'.obj} (hE : E ∈ Der e v)
    (φ : P →ₐ[A'] Q) {w : P →ₐ[A'] C.obj} (hw : v.comp φ = w) :
    E.comp φ.toLinearMap ∈ Der e w := by
  refine ⟨fun x ↦ hE.1 _, fun x y a b ha hb ↦ ?_⟩
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul]
  have hw' : ∀ z, v (φ z) = w z := fun z ↦ congrArg (fun f : P →ₐ[A'] C.obj ↦ f z) hw
  exact hE.2 _ _ a b (ha.trans (hw' x).symm) (hb.trans (hw' y).symm)

/-- The derivations of `Q` along `v` killed by `sV`. -/
def K (e : SqZero C' C) (v : Q →ₐ[A'] C.obj) (sV : P →ₐ[A'] Q) :
    Submodule C'.obj (Q →ₗ[A'] C'.obj) :=
  Der e v ⊓ LinearMap.ker (precomp C' sV)

variable (b : Chart G.arr Q) (hb : b.IsFormallyEtale) (sV tV : P →ₐ[A'] Q)
  (hsV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.src (b.app C v) = v.comp sV)
  (htV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.tgt (b.app C v) = v.comp tV)

include hb hsV htV in
/-- An element of `K` produces a related lift. -/
theorem rel_addLift {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ₁ : P →ₐ[A'] C'.obj} (h₁ : e.q.hom.hom.comp ℓ₁ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K e v sV) :
    Rel G e w ℓ₁ (addLift (E.comp tV.toLinearMap)
      (Der.comp hE.1 tV (by rw [← htV, hv, G.tgt_idt])) ℓ₁ h₁) := by
  have hz : G.arr.map e.q (G.idt ℓ₁) = b.app C v := by rw [G.idt_map, h₁, hv]
  obtain ⟨vt₁, hvt₁, hbvt₁⟩ := (hb C' C e.q e.surj e.sq v (G.idt ℓ₁) hz).exists
  let vt := addLift E hE.1 vt₁ hvt₁
  have hsE : ∀ x, E (sV x) = 0 := fun x ↦
    congrArg (fun f : P →ₗ[A'] C'.obj ↦ f x) (LinearMap.mem_ker.mp hE.2)
  have hs₁ : vt₁.comp sV = ℓ₁ := by rw [← hsV, hbvt₁, G.src_idt]
  have ht₁ : vt₁.comp tV = ℓ₁ := by rw [← htV, hbvt₁, G.tgt_idt]
  refine ⟨b.app C' vt, ?_, ?_, ?_⟩
  · rw [b.natural]
    change b.app C (e.q.hom.hom.comp (addLift E hE.1 vt₁ hvt₁)) = _
    rw [addLift_reduce, hv]
  · rw [hsV]
    ext x
    change vt₁ (sV x) + E (sV x) = ℓ₁ x
    rw [hsE, add_zero, ← AlgHom.comp_apply, hs₁]
  · rw [htV]
    ext x
    change vt₁ (tV x) + E (tV x) = ℓ₁ x + E (tV x)
    rw [← AlgHom.comp_apply, ht₁]

include hb hsV htV in
/-- Related lifts differ by an element of `K`. -/
theorem exists_K_of_rel {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj} (h₁ : e.q.hom.hom.comp ℓ₁ = w) (h : Rel G e w ℓ₁ ℓ₂) :
    ∃ E ∈ K e v sV, precomp C' tV E = ℓ₂.toLinearMap - ℓ₁.toLinearMap := by
  obtain ⟨g, hg, hgs, hgt⟩ := h
  have hz : G.arr.map e.q (G.idt ℓ₁) = b.app C v := by rw [G.idt_map, h₁, hv]
  obtain ⟨vt₁, hvt₁, hbvt₁⟩ := (hb C' C e.q e.surj e.sq v (G.idt ℓ₁) hz).exists
  obtain ⟨vt, hvt, hbvt⟩ := (hb C' C e.q e.surj e.sq v g (hg.trans hv.symm)).exists
  refine ⟨vt.toLinearMap - vt₁.toLinearMap, ⟨sub_mem_Der hvt₁ hvt, ?_⟩, ?_⟩
  · change _ ∈ LinearMap.ker (precomp C' sV)
    rw [LinearMap.mem_ker]
    ext x
    change vt (sV x) - vt₁ (sV x) = 0
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← hsV, ← hsV, hbvt, hbvt₁, hgs, G.src_idt,
      sub_self]
  · ext x
    change vt (tV x) - vt₁ (tV x) = ℓ₂ x - ℓ₁ x
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← htV, ← htV, hbvt, hbvt₁, hgt, G.tgt_idt]

include hb hsV htV in
/-- **`S` is the image of `K`.** -/
theorem S_eq_map_K {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ₁ : P →ₐ[A'] C'.obj} (h₁ : e.q.hom.hom.comp ℓ₁ = w) :
    S G e w = (K e v sV).map (precomp C' tV) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro D ⟨m₁, m₂, hm₁, hrel, rfl⟩
    obtain ⟨E, hE, hEq⟩ := exists_K_of_rel b hb sV tV hsV htV hv hm₁ hrel
    exact ⟨E, hE, hEq⟩
  · rintro D ⟨E, hE, rfl⟩
    have hrel := rel_addLift b hb sV tV hsV htV hv h₁ hE
    have := sub_mem_S h₁ hrel
    rwa [addLift_toLinearMap, add_sub_cancel_left] at this

include hb hsV htV in
/-- **The relation is membership of the difference in `S`.** -/
theorem rel_iff_mem_S {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ₁ ℓ₂ : P →ₐ[A'] C'.obj} (h₁ : e.q.hom.hom.comp ℓ₁ = w) :
    Rel G e w ℓ₁ ℓ₂ ↔ ℓ₂.toLinearMap - ℓ₁.toLinearMap ∈ S G e w := by
  refine ⟨sub_mem_S h₁, fun hS ↦ ?_⟩
  rw [S_eq_map_K b hb sV tV hsV htV hv h₁] at hS
  obtain ⟨E, hE, hEq⟩ := hS
  have hrel := rel_addLift b hb sV tV hsV htV hv h₁ hE
  have : addLift (E.comp tV.toLinearMap)
      (Der.comp hE.1 tV (by rw [← htV, hv, G.tgt_idt])) ℓ₁ h₁ = ℓ₂ := by
    ext x
    have := congrArg (fun f : P →ₗ[A'] C'.obj ↦ f x) hEq
    simp only [precomp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply] at this
    simp [this]
  rwa [this] at hrel

end Chart

end AlgebraicGeometry.Stack.GroupoidLift

end
