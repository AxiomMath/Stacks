module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.DerivationAlong

/-!
# Transport of derivations between two frames of one point

Let `A'` be a commutative ring, let `P` be a class of `A'`-algebras and let `X` be a functor on
the algebras of `P`. A *formally étale chart* of `X` is an `A'`-algebra `R` together with a
natural map `w ↦ ⟨w⟩` from the algebra maps `w : R → C` to the points `X(C)`, which has unique
infinitesimal lifts: for a surjection `π : C → D` with square-zero kernel, a point `g` of `X`
over `C` and an algebra map `w₀ : R → D` with `⟨w₀⟩ = π(g)`, there is exactly one `w : R → C`
with `π ∘ w = w₀` and `⟨w⟩ = g`. This is the situation of an affine étale scheme chart `Spec R`
of an algebraic space, read on rings.

Two algebra maps `w₁, w₂ : R → C` with `⟨w₁⟩ = ⟨w₂⟩` are *frames* of one point of `X`. This file
constructs, for every `C`-module `N`, the transport
`DerAlong w₁ N ≃ₗ[C] DerAlong w₂ N`
of derivations along the first frame to derivations along the second: a derivation `δ` along
`w₁` is an algebra map `R → C ⊕ N` over `w₁`, its point of `X` over `C ⊕ N` lies over the point
`⟨w₁⟩ = ⟨w₂⟩`, and its unique lift along the projection `C ⊕ N → C` through `w₂` is a derivation
along `w₂`. No differentials are involved; everything is read off the lifting property.

## Main definitions

* `Stacks.ChartGlue.FormallyEtaleChart`: the datum of a formally étale chart.
* `Stacks.ChartGlue.FormallyEtaleChart.transport`: the transport of derivations between two
  frames of one point.

## Main results

* `Stacks.ChartGlue.FormallyEtaleChart.transportFun_eq_iff`: the transport is characterised by
  the equality of the points of `X` attached to the two derivations.
* `Stacks.ChartGlue.FormallyEtaleChart.transportFun_postcomp`: naturality in the module.
* `Stacks.ChartGlue.FormallyEtaleChart.transportFun_trans`: transitivity in the frames.
* `Stacks.ChartGlue.FormallyEtaleChart.pt_addHom_transportFun`: for a square-zero ideal `J` of
  `C`, moving the first frame by `δ` and the second by its transport gives the same point of `X`.
* `Stacks.ChartGlue.FormallyEtaleChart.transportFun_baseChange`: compatibility with change of
  the algebra `C`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace Stacks.ChartGlue

variable {A' : Type u} [CommRing A'] (P : ObjectProperty (CommAlgCat.{u} A'))
  (X : P.FullSubcategory ⥤ Type v) (R : Type u) [CommRing R] [Algebra A' R]

/-- A *formally étale chart* of a functor `X` on a class `P` of `A'`-algebras: an `A'`-algebra
`R` with a natural map from algebra maps `R → C` to points of `X` over `C`, with unique
infinitesimal lifts along square-zero surjections. -/
structure FormallyEtaleChart where
  /-- The point of `X` attached to an algebra map out of `R`. -/
  pt : ∀ C : P.FullSubcategory, (R →ₐ[A'] C.obj) → X.obj C
  /-- Naturality of the points. -/
  pt_comp : ∀ {C D : P.FullSubcategory} (h : C ⟶ D) (w : R →ₐ[A'] C.obj),
    pt D (h.hom.hom.comp w) = X.map h (pt C w)
  /-- Unique infinitesimal lifts. -/
  existsUnique_lift : ∀ {C D : P.FullSubcategory} (π : C ⟶ D),
    Function.Surjective π.hom.hom → RingHom.ker π.hom.hom ^ 2 = ⊥ →
      ∀ (g : X.obj C) (w₀ : R →ₐ[A'] D.obj), pt D w₀ = X.map π g →
        ∃! w : R →ₐ[A'] C.obj, π.hom.hom.comp w = w₀ ∧ pt C w = g

namespace FormallyEtaleChart

variable {P X R} (Φ : FormallyEtaleChart P X R)

section Transport

variable {C : P.FullSubcategory} {N : Type u} [AddCommGroup N] [Module C.obj N]
  {hN : P (CommAlgCat.of A' (TrivExt C.obj N))}

variable (hN) in
/-- The trivial square-zero extension of an algebra of `P` by a module, as an object of `P`. -/
abbrev trivExtObj : P.FullSubcategory := ⟨CommAlgCat.of A' (TrivExt C.obj N), hN⟩

variable (hN) in
/-- The projection of the trivial square-zero extension, as a morphism of `P`. -/
abbrev trivExtFst : trivExtObj hN ⟶ C :=
  ObjectProperty.homMk (CommAlgCat.ofHom (TrivExt.fstHom A' C.obj N))

variable (hN) in
/-- The projection of the trivial square-zero extension onto the algebra is surjective. -/
lemma trivExtFst_surjective : Function.Surjective (trivExtFst hN).hom.hom :=
  TrivExt.fstHom_surjective A' C.obj N

variable (hN) in
/-- The kernel of the projection of the trivial square-zero extension has square zero. -/
lemma trivExtFst_ker_sq : RingHom.ker (trivExtFst hN).hom.hom ^ 2 = ⊥ :=
  TrivExt.ker_fstHom_sq A' C.obj N

variable (hN) in
/-- The point of `X` attached to a derivation along a frame. -/
abbrev derPt {w : R →ₐ[A'] C.obj} (δ : DerAlong w N) : X.obj (trivExtObj hN) :=
  Φ.pt (trivExtObj hN) δ.liftHom

/-- The point of a frame is the image of the point of a frame composing to it. -/
private lemma pt_eq_map_of_comp_eq {C D : P.FullSubcategory} (m : C ⟶ D) {w : R →ₐ[A'] C.obj}
    {w' : R →ₐ[A'] D.obj} (e : m.hom.hom.comp w = w') : Φ.pt D w' = X.map m (Φ.pt C w) :=
  e ▸ Φ.pt_comp m w

/-- The point attached to a derivation along `w` maps, under the projection of the trivial
square-zero extension, to the point attached to `w`. -/
lemma map_trivExtFst_derPt {w : R →ₐ[A'] C.obj} (δ : DerAlong w N) :
    X.map (trivExtFst hN) (Φ.derPt hN δ) = Φ.pt C w := by
  exact (Φ.pt_eq_map_of_comp_eq _ δ.fstHom_comp_liftHom).symm

variable {w₁ w₂ : R →ₐ[A'] C.obj}

variable (hN) in
/-- The lift along the second frame of the point attached to a derivation along the first. -/
theorem existsUnique_transport (h : Φ.pt C w₁ = Φ.pt C w₂) (δ : DerAlong w₁ N) :
    ∃! δ' : DerAlong w₂ N, Φ.derPt hN δ' = Φ.derPt hN δ := by
  obtain ⟨W, ⟨hW₁, hW₂⟩, hWu⟩ := Φ.existsUnique_lift (trivExtFst hN) (trivExtFst_surjective hN)
    (trivExtFst_ker_sq hN) (Φ.derPt hN δ) w₂ (h.symm.trans (Φ.map_trivExtFst_derPt δ).symm)
  refine ⟨DerAlong.ofLift W hW₁, ?_, fun δ' hδ' ↦ ?_⟩
  · change Φ.pt (trivExtObj hN) (DerAlong.ofLift W hW₁).liftHom = _
    rw [DerAlong.liftHom_ofLift]
    exact hW₂
  · apply DerAlong.liftHom_injective
    rw [hWu δ'.liftHom ⟨δ'.fstHom_comp_liftHom, hδ'⟩, DerAlong.liftHom_ofLift]

variable (hN) in
/-- **The transport of derivations between two frames of one point.** -/
noncomputable def transportFun (h : Φ.pt C w₁ = Φ.pt C w₂) (δ : DerAlong w₁ N) :
    DerAlong w₂ N :=
  (Φ.existsUnique_transport hN h δ).exists.choose

/-- The transport of a derivation has the same point of `X` as the derivation. -/
lemma derPt_transportFun (h : Φ.pt C w₁ = Φ.pt C w₂) (δ : DerAlong w₁ N) :
    Φ.derPt hN (Φ.transportFun hN h δ) = Φ.derPt hN δ :=
  (Φ.existsUnique_transport hN h δ).exists.choose_spec

/-- **The transport is characterised by the points of `X`.** -/
theorem transportFun_eq_iff (h : Φ.pt C w₁ = Φ.pt C w₂) (δ : DerAlong w₁ N)
    (δ' : DerAlong w₂ N) :
    Φ.transportFun hN h δ = δ' ↔ Φ.derPt hN δ' = Φ.derPt hN δ :=
  ⟨fun e ↦ e ▸ Φ.derPt_transportFun h δ,
    fun e ↦ (Φ.existsUnique_transport hN h δ).unique (Φ.derPt_transportFun h δ) e⟩

/-- The transport from a frame to itself is the identity. -/
lemma transportFun_self (δ : DerAlong w₁ N) : Φ.transportFun hN rfl δ = δ :=
  (Φ.transportFun_eq_iff rfl δ δ).2 rfl

/-- Transport from `w₁` to `w₂` followed by transport from `w₂` to `w₃` is the transport from
`w₁` to `w₃`. -/
lemma transportFun_trans {w₃ : R →ₐ[A'] C.obj} (h₁₂ : Φ.pt C w₁ = Φ.pt C w₂)
    (h₂₃ : Φ.pt C w₂ = Φ.pt C w₃) (δ : DerAlong w₁ N) :
    Φ.transportFun hN h₂₃ (Φ.transportFun hN h₁₂ δ) = Φ.transportFun hN (h₁₂.trans h₂₃) δ :=
  (Φ.transportFun_eq_iff _ _ _).2
    ((Φ.derPt_transportFun (h₁₂.trans h₂₃) δ).trans (Φ.derPt_transportFun h₁₂ δ).symm)

/-- The transport back along the reversed equality inverts the transport. -/
lemma transportFun_symm (h : Φ.pt C w₁ = Φ.pt C w₂) (δ : DerAlong w₁ N) :
    Φ.transportFun hN h.symm (Φ.transportFun hN h δ) = δ := by
  rw [transportFun_trans, transportFun_self]

/-- **Naturality of the transport in the module.** -/
theorem transportFun_postcomp {N' : Type u} [AddCommGroup N'] [Module C.obj N']
    (hN' : P (CommAlgCat.of A' (TrivExt C.obj N'))) (f : N →ₗ[C.obj] N')
    (h : Φ.pt C w₁ = Φ.pt C w₂) (δ : DerAlong w₁ N) :
    Φ.transportFun hN' h (δ.postcomp f) = (Φ.transportFun hN h δ).postcomp f := by
  rw [transportFun_eq_iff]
  let m : trivExtObj hN ⟶ trivExtObj hN' :=
    ObjectProperty.homMk (CommAlgCat.ofHom (TrivExt.map (A' := A') f))
  have key : ∀ {w : R →ₐ[A'] C.obj} (ε : DerAlong w N),
      Φ.derPt hN' (ε.postcomp f) = X.map m (Φ.derPt hN ε) := fun ε ↦
    Φ.pt_eq_map_of_comp_eq _ (DerAlong.liftHom_postcomp f ε)
  rw [key, key, derPt_transportFun]

/-- **The transport is additive and `C`-linear.** -/
theorem transportFun_add (hNN : P (CommAlgCat.of A' (TrivExt C.obj (N × N))))
    (h : Φ.pt C w₁ = Φ.pt C w₂) (δ ε : DerAlong w₁ N) :
    Φ.transportFun hN h (δ + ε) = Φ.transportFun hN h δ + Φ.transportFun hN h ε := by
  have hprod : Φ.transportFun hNN h (δ.prod ε) =
      (Φ.transportFun hN h δ).prod (Φ.transportFun hN h ε) := by
    rw [DerAlong.eq_prod (Φ.transportFun hNN h (δ.prod ε)),
      ← Φ.transportFun_postcomp (hN := hNN) hN, ← Φ.transportFun_postcomp (hN := hNN) hN,
      DerAlong.postcomp_fst_prod, DerAlong.postcomp_snd_prod]
  rw [DerAlong.add_eq_postcomp_prod, DerAlong.add_eq_postcomp_prod,
    Φ.transportFun_postcomp (hN := hNN) hN, hprod]

/-- The transport commutes with scalar multiplication by elements of `C`. -/
theorem transportFun_smul (h : Φ.pt C w₁ = Φ.pt C w₂) (c : C.obj) (δ : DerAlong w₁ N) :
    Φ.transportFun hN h (c • δ) = c • Φ.transportFun hN h δ := by
  rw [DerAlong.smul_eq_postcomp, DerAlong.smul_eq_postcomp, Φ.transportFun_postcomp hN]

variable (hN) in
/-- **The transport of derivations between two frames of one point**, as a `C`-linear
equivalence. -/
noncomputable def transport (hNN : P (CommAlgCat.of A' (TrivExt C.obj (N × N))))
    (h : Φ.pt C w₁ = Φ.pt C w₂) : DerAlong w₁ N ≃ₗ[C.obj] DerAlong w₂ N where
  toFun := Φ.transportFun hN h
  invFun := Φ.transportFun hN h.symm
  map_add' := Φ.transportFun_add hNN h
  map_smul' := Φ.transportFun_smul h
  left_inv := Φ.transportFun_symm h
  right_inv := Φ.transportFun_symm h.symm

/-- The linear equivalence `transport` applied to a derivation is `transportFun`. -/
@[simp] lemma transport_apply (hNN : P (CommAlgCat.of A' (TrivExt C.obj (N × N))))
    (h : Φ.pt C w₁ = Φ.pt C w₂) (δ : DerAlong w₁ N) :
    Φ.transport hN hNN h δ = Φ.transportFun hN h δ := rfl

/-- **Moving two frames of one point by a derivation and by its transport gives one point.**
Let `J` be a square-zero ideal of `C` and let `δ` be a derivation along the first frame with
values in `J`. Then `w₁ + δ` and `w₂ + δ'`, where `δ'` is the transport of `δ`, are again two
frames of one point. -/
theorem pt_addHom_transportFun (J : Ideal C.obj) (hJ : J ^ 2 = ⊥)
    (hJ' : P (CommAlgCat.of A' (TrivExt C.obj J))) (h : Φ.pt C w₁ = Φ.pt C w₂)
    (δ : DerAlong w₁ J) :
    Φ.pt C (DerAlong.addHom J hJ δ) =
      Φ.pt C (DerAlong.addHom J hJ (Φ.transportFun hJ' h δ)) := by
  let m : trivExtObj hJ' ⟶ C :=
    ObjectProperty.homMk (CommAlgCat.ofHom (TrivExt.sumHom (A' := A') J hJ))
  have key : ∀ {w : R →ₐ[A'] C.obj} (ε : DerAlong w J),
      Φ.pt C (DerAlong.addHom J hJ ε) = X.map m (Φ.derPt hJ' ε) := fun ε ↦
    Φ.pt_eq_map_of_comp_eq _ (DerAlong.addHom_eq_comp J hJ ε)
  rw [key, key, derPt_transportFun]

/-- **Compatibility of the transport with change of the algebra.** Let `f : C → D` be a morphism
of `P` and let `N` be a `D`-module, viewed as a `C`-module. The transport between the frames
`w₁, w₂` of a point over `C`, followed by reading derivations along the composites with `f`, is
the transport between the frames `f ∘ w₁, f ∘ w₂` of the image point over `D`. -/
theorem transportFun_baseChange {D : P.FullSubcategory} (f : C ⟶ D)
    [Algebra C.obj D.obj] (hf : ∀ c, algebraMap C.obj D.obj c = f.hom.hom c)
    {N' : Type u} [AddCommGroup N'] [Module C.obj N'] [Module D.obj N']
    [IsScalarTower C.obj D.obj N'] (hC : P (CommAlgCat.of A' (TrivExt C.obj N')))
    (hD : P (CommAlgCat.of A' (TrivExt D.obj N'))) (h : Φ.pt C w₁ = Φ.pt C w₂)
    (h' : Φ.pt D (f.hom.hom.comp w₁) = Φ.pt D (f.hom.hom.comp w₂)) (δ : DerAlong w₁ N') :
    Φ.transportFun hD h' (δ.baseChange f.hom.hom hf) =
      (Φ.transportFun hC h δ).baseChange f.hom.hom hf := by
  rw [transportFun_eq_iff]
  let m : trivExtObj hC ⟶ trivExtObj hD :=
    ObjectProperty.homMk (CommAlgCat.ofHom (TrivExt.baseMap f.hom.hom hf))
  have key : ∀ {w : R →ₐ[A'] C.obj} (ε : DerAlong w N'),
      Φ.derPt hD (ε.baseChange f.hom.hom hf) = X.map m (Φ.derPt hC ε) := fun ε ↦
    Φ.pt_eq_map_of_comp_eq _ (DerAlong.liftHom_baseChange f.hom.hom hf ε)
  rw [key, key, derPt_transportFun]

/-- **Compatibility of the transport with semilinear pushforward.** Let `f : C → D` be a
morphism of `P`, `N` a `C`-module, `N'` a `D`-module and `g : N → N'` an `f`-semilinear map. The
transport over `C` followed by pushforward is the transport over `D` of the pushforward. -/
theorem transportFun_map {D : P.FullSubcategory} (f : C ⟶ D) {N' : Type u} [AddCommGroup N']
    [Module D.obj N'] (g : N →ₛₗ[((f.hom.hom : C.obj →ₐ[A'] D.obj) : C.obj →+* D.obj)] N')
    (hD : P (CommAlgCat.of A' (TrivExt D.obj N'))) (h : Φ.pt C w₁ = Φ.pt C w₂)
    (h' : Φ.pt D (f.hom.hom.comp w₁) = Φ.pt D (f.hom.hom.comp w₂)) (δ : DerAlong w₁ N) :
    Φ.transportFun hD h' (δ.map f.hom.hom g) = (Φ.transportFun hN h δ).map f.hom.hom g := by
  rw [transportFun_eq_iff]
  let m : trivExtObj hN ⟶ trivExtObj hD :=
    ObjectProperty.homMk (CommAlgCat.ofHom (TrivExt.mapSemilinear f.hom.hom g))
  have key : ∀ {w : R →ₐ[A'] C.obj} (ε : DerAlong w N),
      Φ.derPt hD (ε.map f.hom.hom g) = X.map m (Φ.derPt hN ε) := fun ε ↦
    Φ.pt_eq_map_of_comp_eq _ (DerAlong.liftHom_map f.hom.hom g ε)
  rw [key, key, derPt_transportFun]

/-- Recasting a derivation along an equality of frames does not change its point. -/
lemma derPt_cast {w w' : R →ₐ[A'] C.obj} (e : w = w') (δ : DerAlong w N) :
    Φ.derPt hN (δ.cast e) = Φ.derPt hN δ := by
  subst e
  rfl

/-- The transport commutes with recasting derivations along equal frames. -/
lemma transportFun_cast {w₁' w₂' : R →ₐ[A'] C.obj} (e₁ : w₁ = w₁') (e₂ : w₂ = w₂')
    (h : Φ.pt C w₁ = Φ.pt C w₂) (h' : Φ.pt C w₁' = Φ.pt C w₂') (δ : DerAlong w₁ N) :
    Φ.transportFun hN h' (δ.cast e₁) = (Φ.transportFun hN h δ).cast e₂ := by
  rw [transportFun_eq_iff, derPt_cast, derPt_cast, derPt_transportFun]

/-- Two derivations along one frame with the same point of `X` are equal. -/
lemma eq_of_derPt_eq {w : R →ₐ[A'] C.obj} {δ δ' : DerAlong w N}
    (h : Φ.derPt hN δ = Φ.derPt hN δ') : δ = δ' := by
  rw [← Φ.transportFun_self (hN := hN) δ]
  exact (Φ.transportFun_eq_iff rfl δ δ').2 h.symm

/-- The point attached to a pushforward of a derivation. -/
lemma derPt_map {D : P.FullSubcategory} (f : C ⟶ D) {N' : Type u} [AddCommGroup N']
    [Module D.obj N'] (g : N →ₛₗ[((f.hom.hom : C.obj →ₐ[A'] D.obj) : C.obj →+* D.obj)] N')
    (hD : P (CommAlgCat.of A' (TrivExt D.obj N'))) {w : R →ₐ[A'] C.obj} (δ : DerAlong w N) :
    Φ.derPt hD (δ.map f.hom.hom g) =
      X.map (ObjectProperty.homMk (CommAlgCat.ofHom (TrivExt.mapSemilinear f.hom.hom g)) :
        trivExtObj hN ⟶ trivExtObj hD) (Φ.derPt hN δ) := by
  exact Φ.pt_eq_map_of_comp_eq _ (DerAlong.liftHom_map f.hom.hom g δ)

/-- Two derivations along equal frames with the same values have the same point. -/
lemma derPt_eq_of_apply_eq {w w' : R →ₐ[A'] C.obj} (e : w = w') {δ : DerAlong w N}
    {δ' : DerAlong w' N} (h : ∀ r, δ r = δ' r) : Φ.derPt hN δ = Φ.derPt hN δ' := by
  subst e
  rw [DerAlong.ext (funext h)]

/-- **Transport over a thickening, with values in a module over the reduction, is transport over
the reduction.** Let `f : C → D` be a morphism of `P` and let `N` be a `D`-module whose `C`-module
structure is the restriction along `f`. For derivations `δ` along `w₁` over `C` and `δ'` along a
frame `w₁'` of `D` with `f ∘ w₁ = w₁'` and the same values, the transports to `w₂` and to
`w₂' = f ∘ w₂` have the same values. -/
theorem transportFun_reduce {D : P.FullSubcategory} (f : C ⟶ D) [Module D.obj N]
    (hsmul : ∀ (c : C.obj) (n : N), f.hom.hom c • n = c • n)
    (hD : P (CommAlgCat.of A' (TrivExt D.obj N))) {w₁' w₂' : R →ₐ[A'] D.obj}
    (e₁ : f.hom.hom.comp w₁ = w₁') (e₂ : f.hom.hom.comp w₂ = w₂')
    (h : Φ.pt C w₁ = Φ.pt C w₂) (h' : Φ.pt D w₁' = Φ.pt D w₂')
    (δ : DerAlong w₁ N) (δ' : DerAlong w₁' N) (hδ : ∀ r, δ r = δ' r) (r : R) :
    Φ.transportFun hN h δ r = Φ.transportFun hD h' δ' r := by
  let : Algebra C.obj D.obj := (f.hom.hom : C.obj →+* D.obj).toAlgebra
  have : IsScalarTower C.obj D.obj N := ⟨fun c d n ↦ by
    change (f.hom.hom c * d) • n = c • (d • n)
    rw [mul_smul, hsmul]⟩
  have hf : ∀ c, algebraMap C.obj D.obj c = f.hom.hom c := fun _ ↦ rfl
  have h'' : Φ.pt D (f.hom.hom.comp w₁) = Φ.pt D (f.hom.hom.comp w₂) := by
    rw [Φ.pt_comp, Φ.pt_comp, h]
  have hc := Φ.transportFun_cast (C := D) (hN := hD) e₁ e₂ h'' h' (δ.baseChange f.hom.hom hf)
  rw [Φ.transportFun_baseChange (C := C) (D := D) f hf hN hD h h'' δ,
    show (δ.baseChange f.hom.hom hf).cast e₁ = δ' from DerAlong.ext (funext hδ)] at hc
  rw [hc]
  rfl

end Transport

end FormallyEtaleChart

end Stacks.ChartGlue

end
