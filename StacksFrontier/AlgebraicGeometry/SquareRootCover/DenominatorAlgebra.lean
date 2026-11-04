module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import StacksFrontier.AlgebraicGeometry.Properties.DenseRestriction
public import StacksFrontier.AlgebraicGeometry.SquareRootCover.Affine
public import StacksFrontier.RingTheory.ModuleQuadraticExtension

@[expose] public noncomputable section

/-!
# The algebra of denominators of a section on a dense open subset

Let `X` be a reduced scheme, `Ω` a dense open subset of `X` and `u` a section of the structure
sheaf over `Ω`. This file builds the quasi-coherent `𝒪_X`-algebra `𝒪_X ⊕ ℐ`, where `ℐ` is the
ideal of denominators of `u`, in the form in which its relative spectrum can be glued: a
presheaf of commutative rings on the affine opens of `X` whose value on a basic open subset is
the corresponding localization.

## Implementation notes

The quasi-coherence of `ℐ` never appears as a statement about a sheaf of modules. The ideal of
denominators is carried as the module `Stacks.SquareRootCover.denomPairs` of *pairs* `(f, s)`
of sections over `W` with `s = u * f` on `W ⊓ Ω`, which is a submodule of `Γ(X, W) ^ 2` and so
involves no quotient, no choice of extension and no sheafification; the second component is the
value of `μ`, and reducedness enters only through the injectivity of restriction to `W ⊓ Ω`
(`Stacks.DenseRestriction.injective_res`), which makes that value unique.

## References

* [Stacks Project, Tag 0CNZ](https://stacks.math.columbia.edu/tag/0CNZ)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ModuleQuadraticExtension

universe u

namespace Stacks.SquareRootCover

variable {X : Scheme.{u}}

/-- Restriction of sections of the structure sheaf of a scheme along an inclusion of opens, as
a ring homomorphism. -/
abbrev resHom {W V : X.Opens} (h : V ≤ W) : Γ(X, W) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

/-- Restriction from `W` to `V` followed by restriction from `V` to `U` is restriction from `W`
to `U`. -/
lemma resHom_resHom {W V U : X.Opens} (h : V ≤ W) (h' : U ≤ V) (s : Γ(X, W)) :
    resHom h' (resHom h s) = resHom (h'.trans h) s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction from an open to itself is the identity. -/
lemma resHom_self {W : X.Opens} (s : Γ(X, W)) : resHom (le_refl W) s = s := by
  show (X.presheaf.map (homOfLE (le_refl W)).op).hom s = s
  rw [show (homOfLE (le_refl W)).op = 𝟙 (op W) from rfl, X.presheaf.map_id]
  rfl

/-- A dense open subset meets every open subset densely. -/
lemma subset_closure_inf {Ω : X.Opens} (hΩ : Dense (Ω : Set X)) (W : X.Opens) :
    (W : Set X) ⊆ closure ((W ⊓ Ω : X.Opens) : Set X) := by
  intro x hx
  rw [mem_closure_iff]
  intro N hN hxN
  obtain ⟨y, hy⟩ := hΩ.inter_open_nonempty (N ∩ (W : Set X)) (hN.inter W.isOpen) ⟨x, hxN, hx⟩
  exact ⟨y, hy.1.1, hy.1.2, hy.2⟩

variable [IsReduced X] {Ω : X.Opens}

/-- On a reduced scheme with `Ω` dense, a section over `W` is determined by its restriction to
`W ⊓ Ω`. -/
lemma injective_resHom_inf (hΩ : Dense (Ω : Set X)) (W : X.Opens) :
    Function.Injective (resHom (inf_le_left : W ⊓ Ω ≤ W)) :=
  Stacks.DenseRestriction.injective_res _ (subset_closure_inf hΩ W)

variable (u : Γ(X, Ω))

/-- The *module of denominator pairs* of `u` over `W`: the `Γ(X, W)`-submodule of pairs `(f, s)`
of sections over `W` such that `s = u * f` holds on `W ⊓ Ω`. Since `W ⊓ Ω` is dense in `W` and
`X` is reduced, `s` is determined by `f`, so this module is the ideal of denominators of `u`
with multiplication by `u` carried along as the second component. -/
def denomPairs (W : X.Opens) : Submodule Γ(X, W) (Γ(X, W) × Γ(X, W)) where
  carrier := {p | resHom inf_le_left p.2 = resHom (inf_le_right : W ⊓ Ω ≤ Ω) u *
    resHom inf_le_left p.1}
  add_mem' {p q} hp hq := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, map_add] at hp hq ⊢
    rw [hp, hq, mul_add]
  zero_mem' := by simp
  smul_mem' c p hp := by
    simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul] at hp ⊢
    rw [hp]; ring

omit [IsReduced X] in
/-- A pair `(f, s)` of sections over `W` is a denominator pair if and only if `s = u * f` on
`W ⊓ Ω`. -/
lemma mem_denomPairs_iff {W : X.Opens} (p : Γ(X, W) × Γ(X, W)) :
    p ∈ denomPairs u W ↔ resHom inf_le_left p.2 =
      resHom (inf_le_right : W ⊓ Ω ≤ Ω) u * resHom inf_le_left p.1 :=
  Iff.rfl

/-- The first component of a denominator pair, an element of the ideal of denominators. -/
def denomFst (W : X.Opens) : denomPairs u W →ₗ[Γ(X, W)] Γ(X, W) :=
  (LinearMap.fst Γ(X, W) Γ(X, W) Γ(X, W)).comp (denomPairs u W).subtype

/-- The second component of a denominator pair, the product of `u` with the first component. -/
def denomSnd (W : X.Opens) : denomPairs u W →ₗ[Γ(X, W)] Γ(X, W) :=
  (LinearMap.snd Γ(X, W) Γ(X, W) Γ(X, W)).comp (denomPairs u W).subtype

omit [IsReduced X] in
/-- `denomFst` sends a denominator pair to its first component. -/
@[simp] lemma denomFst_apply {W : X.Opens} (p : denomPairs u W) : denomFst u W p = p.1.1 := rfl

omit [IsReduced X] in
/-- `denomSnd` sends a denominator pair to its second component. -/
@[simp] lemma denomSnd_apply {W : X.Opens} (p : denomPairs u W) : denomSnd u W p = p.1.2 := rfl

/-- A denominator pair is determined by its first component. -/
lemma injective_denomFst (hΩ : Dense (Ω : Set X)) (W : X.Opens) :
    Function.Injective (denomFst u W) := by
  intro p q h
  refine Subtype.ext (Prod.ext h (injective_resHom_inf hΩ W ?_))
  rw [(mem_denomPairs_iff u _).mp p.2, (mem_denomPairs_iff u _).mp q.2]
  exact congrArg _ (congrArg _ h)

/-- The symmetry `(u * f) * g = (u * g) * f` of the form on denominator pairs: both sides
restrict to `u * f * g` on `W ⊓ Ω`. -/
lemma denomSnd_mul_denomFst_comm (hΩ : Dense (Ω : Set X)) (W : X.Opens)
    (p q : denomPairs u W) :
    denomSnd u W p * denomFst u W q = denomSnd u W q * denomFst u W p := by
  refine injective_resHom_inf hΩ W ?_
  simp only [denomSnd_apply, denomFst_apply, map_mul]
  rw [(mem_denomPairs_iff u _).mp p.2, (mem_denomPairs_iff u _).mp q.2]
  ring

/-- The quadratic datum of the denominators of `u` over `W`: the module of denominator pairs
with the form `(p, q) ↦ p.2 * q.1`, that is, `(f, g) ↦ (u * f) * g`. -/
def denomDatum (hΩ : Dense (Ω : Set X)) (W : X.Opens) :
    QuadraticDatum Γ(X, W) (denomPairs u W) :=
  pairDatum (denomFst u W) (denomSnd u W) (injective_denomFst u hΩ W)
    (denomSnd_mul_denomFst_comm u hΩ W)

/-- The form of `denomDatum` sends `(p, q)` to `p.2 * q.1`. -/
@[simp] lemma denomDatum_form_apply (hΩ : Dense (Ω : Set X)) (W : X.Opens)
    (p q : denomPairs u W) :
    (denomDatum u hΩ W).form p q = p.1.2 * q.1.1 := rfl

/-- The algebra of denominators of `u` over `W`: the ring `Γ(X, W) ⊕ ℐ(W)` with the
multiplication `(a, f) * (b, g) = (a * b + (u * f) * g, a • g + b • f)`. -/
abbrev denomExt (hΩ : Dense (Ω : Set X)) (W : X.Opens) : Type u :=
  Ext (denomDatum u hΩ W)

/-! ### Restriction, and the presheaf of algebras -/

/-- Restriction of denominator pairs along an inclusion of opens: both components are
restricted, and the defining equation restricts with them. -/
def denomPairsRes {W W' : X.Opens} (h : W' ≤ W) : denomPairs u W →+ denomPairs u W' where
  toFun p := ⟨(resHom h p.1.1, resHom h p.1.2), by
    have hp := congrArg (resHom (inf_le_inf h (le_refl Ω))) ((mem_denomPairs_iff u _).mp p.2)
    rw [map_mul] at hp
    simpa only [mem_denomPairs_iff, resHom_resHom] using hp⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' p q := by apply Subtype.ext; simp

omit [IsReduced X] in
/-- The restriction of a denominator pair is the pair of restrictions of its components. -/
@[simp] lemma denomPairsRes_coe {W W' : X.Opens} (h : W' ≤ W) (p : denomPairs u W) :
    (denomPairsRes u h p).1 = (resHom h p.1.1, resHom h p.1.2) := rfl

/-- Restriction in the algebra of denominators of `u`, as a ring homomorphism. -/
def denomExtRes (hΩ : Dense (Ω : Set X)) {W W' : X.Opens} (h : W' ≤ W) :
    denomExt u hΩ W →+* denomExt u hΩ W' :=
  Ext.map (resHom h) (denomPairsRes u h)
    (fun a p => by apply Subtype.ext; simp [Prod.smul_fst, Prod.smul_snd])
    (fun p q => by simp)

/-- The first component of a restriction is the restriction of the first component. -/
@[simp] lemma fst_denomExtRes (hΩ : Dense (Ω : Set X)) {W W' : X.Opens} (h : W' ≤ W)
    (y : denomExt u hΩ W) : (denomExtRes u hΩ h y).fst = resHom h y.fst := rfl

/-- The second component of a restriction is the restriction of the second component, as a
denominator pair. -/
@[simp] lemma snd_denomExtRes (hΩ : Dense (Ω : Set X)) {W W' : X.Opens} (h : W' ≤ W)
    (y : denomExt u hΩ W) : (denomExtRes u hΩ h y).snd = denomPairsRes u h y.snd := rfl

/-- Restriction in the algebra of denominators from an open to itself is the identity. -/
lemma denomExtRes_self (hΩ : Dense (Ω : Set X)) {W : X.Opens} (y : denomExt u hΩ W) :
    denomExtRes u hΩ (le_refl W) y = y :=
  Ext.ext' (resHom_self y.fst)
    (Subtype.ext (Prod.ext (resHom_self _) (resHom_self _)))

/-- Restriction in the algebra of denominators is transitive: restricting from `W` to `V` and
then to `U` is restricting from `W` to `U`. -/
lemma denomExtRes_denomExtRes (hΩ : Dense (Ω : Set X)) {W V U : X.Opens} (h : V ≤ W) (h' : U ≤ V)
    (y : denomExt u hΩ W) :
    denomExtRes u hΩ h' (denomExtRes u hΩ h y) = denomExtRes u hΩ (h'.trans h) y :=
  Ext.ext' (resHom_resHom h h' y.fst)
    (Subtype.ext (Prod.ext (resHom_resHom h h' _) (resHom_resHom h h' _)))

/-- Restriction in the algebra of denominators commutes with the structure morphism. -/
lemma denomExtRes_algebraMap (hΩ : Dense (Ω : Set X)) {W W' : X.Opens} (h : W' ≤ W)
    (a : Γ(X, W)) :
    denomExtRes u hΩ h (algebraMap Γ(X, W) (denomExt u hΩ W) a)
      = algebraMap Γ(X, W') (denomExt u hΩ W') (resHom h a) :=
  Ext.map_algebraMap _ _ _ _ a

/-- The presheaf of commutative rings `W ↦ Γ(X, W) ⊕ ℐ(W)` on the opens of `X`, where `ℐ` is
the ideal of denominators of `u`. -/
def denomPresheaf (hΩ : Dense (Ω : Set X)) : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj W := CommRingCat.of (denomExt u hΩ W.unop)
  map {_ _} i := CommRingCat.ofHom (denomExtRes u hΩ (leOfHom i.unop))
  map_id _ := CommRingCat.hom_ext (RingHom.ext fun y => denomExtRes_self u hΩ y)
  map_comp {_ _ _} i j := CommRingCat.hom_ext (RingHom.ext fun y =>
    (denomExtRes_denomExtRes u hΩ (leOfHom i.unop) (leOfHom j.unop) y).symm)

/-- The restriction maps of `denomPresheaf` are given by `denomExtRes`. -/
@[simp] lemma denomPresheaf_map_apply (hΩ : Dense (Ω : Set X)) {W W' : X.Opensᵒᵖ} (i : W ⟶ W')
    (y : denomExt u hΩ W.unop) :
    ((denomPresheaf u hΩ).map i).hom y = denomExtRes u hΩ (leOfHom i.unop) y := rfl

/-- The structure morphism `𝒪_X ⟶ 𝒪_X ⊕ ℐ` of the algebra of denominators. -/
def denomStructureMap (hΩ : Dense (Ω : Set X)) : X.presheaf ⟶ denomPresheaf u hΩ where
  app W := CommRingCat.ofHom (Ext.inlHom (denomDatum u hΩ W.unop))
  naturality {_ _} i := CommRingCat.hom_ext (RingHom.ext fun a =>
    (denomExtRes_algebraMap u hΩ (leOfHom i.unop) a).symm)

/-- The structure morphism sends a section `a` to the element `(a, 0)`. -/
@[simp] lemma denomStructureMap_app_apply (hΩ : Dense (Ω : Set X)) (W : X.Opensᵒᵖ)
    (a : Γ(X, W.unop)) :
    ((denomStructureMap u hΩ).app W).hom a = Ext.mk (denomDatum u hΩ W.unop) a 0 := rfl

/-! ### The algebra of denominators localizes on basic opens

This is the quasi-coherence of the ideal of denominators, in the form in which the relative
spectrum is glued. -/

section Localization

omit [IsReduced X] in
/-- Restricting a section over `W` to `W ⊓ Ω` and then to `V ⊓ Ω` agrees with restricting it to
`V` and then to `V ⊓ Ω`. -/
lemma resHom_inf_left_comm {V W : X.Opens} (h : V ≤ W) (s : Γ(X, W)) :
    resHom (inf_le_inf h (le_refl Ω)) (resHom (inf_le_left : W ⊓ Ω ≤ W) s)
      = resHom (inf_le_left : V ⊓ Ω ≤ V) (resHom h s) := by
  rw [resHom_resHom, resHom_resHom]

omit [IsReduced X] in
/-- Restricting a section over `Ω` to `W ⊓ Ω` and then to `V ⊓ Ω` is restricting it to
`V ⊓ Ω`. -/
lemma resHom_inf_right_comm {V W : X.Opens} (h : V ≤ W) (s : Γ(X, Ω)) :
    resHom (inf_le_inf h (le_refl Ω)) (resHom (inf_le_right : W ⊓ Ω ≤ Ω) s)
      = resHom (inf_le_right : V ⊓ Ω ≤ Ω) s := by
  rw [resHom_resHom]

variable (hΩ : Dense (Ω : Set X)) {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))

omit [IsReduced X] in
/-- The algebra map from sections over `U` to sections over the basic open set of `r` is
restriction. -/
lemma algebraMap_basicOpen_eq :
    (algebraMap Γ(X, U) Γ(X, X.basicOpen r)) = resHom (X.basicOpen_le r) :=
  RingHom.algebraMap_toAlgebra _

omit [IsReduced X] in
/-- The image of a section over `U` under the algebra map to sections over the basic open set of
`r` is its restriction. -/
lemma algebraMap_basicOpen_apply (a : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen r) a = resHom (X.basicOpen_le r) a :=
  congrFun (congrArg (fun f : Γ(X, U) →+* Γ(X, X.basicOpen r) => f.toFun)
    (algebraMap_basicOpen_eq r)) a

include hU in
/-- **Clearing denominators in the algebra of denominators.** Every section of `𝒪_X ⊕ ℐ` over
the basic open set of `r` becomes, after multiplication by a power of `r`, the restriction of a
section over `U`. The last factor of `r` is what the reducedness of `X` buys: it turns the
relation `u * f = s`, known only on `D(r) ⊓ Ω`, into the same relation on `U ⊓ Ω`. -/
lemma exists_pow_mul_eq_denomExtRes (z : denomExt u hΩ (X.basicOpen r)) :
    ∃ (n : ℕ) (y : denomExt u hΩ U),
      z * algebraMap Γ(X, X.basicOpen r) (denomExt u hΩ (X.basicOpen r))
        (resHom (X.basicOpen_le r) r) ^ n = denomExtRes u hΩ (X.basicOpen_le r) y := by
  have := hU.isLocalization_basicOpen r
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers r)
    (fun i : Fin 3 => ![z.fst, z.snd.1.1, z.snd.1.2] i)
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff (b : Γ(X, U)) r |>.mp b.2
  obtain ⟨a', ha'⟩ := hb 0
  obtain ⟨f', hf'⟩ := hb 1
  obtain ⟨s', hs'⟩ := hb 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Algebra.smul_def, algebraMap_basicOpen_eq, ← hn,
    map_pow] at ha' hf' hs'
  have key : ∀ c : Γ(X, X.basicOpen r), ∀ c' : Γ(X, U),
      resHom (X.basicOpen_le r) c' = resHom (X.basicOpen_le r) r ^ n * c →
      resHom (X.basicOpen_le r) (r * c') = resHom (X.basicOpen_le r) r ^ (n + 1) * c := by
    intro c c' h
    rw [map_mul, h, pow_succ]
    ring
  have hmem : (r * f', r * s') ∈ denomPairs u U := by
    rw [mem_denomPairs_iff]
    have hp := (mem_denomPairs_iff u z.snd.1).mp z.snd.2
    have h1 := congrArg (resHom (inf_le_left : X.basicOpen r ⊓ Ω ≤ X.basicOpen r)) hf'
    have h2 := congrArg (resHom (inf_le_left : X.basicOpen r ⊓ Ω ≤ X.basicOpen r)) hs'
    rw [map_mul, map_pow] at h1 h2
    have hd : resHom (inf_le_inf (X.basicOpen_le r) (le_refl Ω))
        (resHom (inf_le_left : U ⊓ Ω ≤ U) s'
          - resHom (inf_le_right : U ⊓ Ω ≤ Ω) u * resHom (inf_le_left : U ⊓ Ω ≤ U) f') = 0 := by
      rw [map_sub, map_mul, resHom_inf_left_comm (X.basicOpen_le r),
        resHom_inf_left_comm (X.basicOpen_le r), resHom_inf_right_comm (X.basicOpen_le r),
        h1, h2, hp]
      ring
    have hbas : X.basicOpen ((X.presheaf.map
        (homOfLE (inf_le_left : U ⊓ Ω ≤ U)).op).hom r) ≤ X.basicOpen r ⊓ Ω := by
      rw [Scheme.basicOpen_res]
      exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    have hzero := Stacks.DenseRestriction.mul_eq_zero_of_res_eq_zero_of_basicOpen_le
      (inf_le_inf (X.basicOpen_le r) (le_refl Ω))
      (resHom (inf_le_left : U ⊓ Ω ≤ U) r) _ hbas hd
    rw [map_mul, map_mul]
    linear_combination hzero
  refine ⟨n + 1, Ext.mk _ (r * a') ⟨(r * f', r * s'), hmem⟩, ?_⟩
  rw [← map_pow]
  refine Ext.ext' ?_ (Subtype.ext ?_)
  · rw [Ext.fst_mul_algebraMap, fst_denomExtRes, Ext.fst_mk, mul_comm z.fst]
    exact (key z.fst a' ha').symm
  · rw [Ext.snd_mul_algebraMap, snd_denomExtRes, Ext.snd_mk, denomPairsRes_coe,
      Submodule.coe_smul]
    exact Prod.ext (key z.snd.1.1 f' hf').symm (key z.snd.1.2 s' hs').symm

include hU in
/-- **The algebra of denominators is quasi-coherent**: its sections over the basic open set of
`r` are the localization of its sections over `U` away from `r`. -/
theorem isLocalization_away_denomExt :
    letI := (denomExtRes u hΩ (X.basicOpen_le r)).toAlgebra
    IsLocalization.Away (algebraMap Γ(X, U) (denomExt u hΩ U) r)
      (denomExt u hΩ (X.basicOpen r)) := by
  let := (denomExtRes u hΩ (X.basicOpen_le r)).toAlgebra
  have := hU.isLocalization_basicOpen r
  have hx : ∀ a : Γ(X, U), denomExtRes u hΩ (X.basicOpen_le r)
        (algebraMap Γ(X, U) (denomExt u hΩ U) a)
      = algebraMap Γ(X, X.basicOpen r) (denomExt u hΩ (X.basicOpen r))
        (resHom (X.basicOpen_le r) a) := denomExtRes_algebraMap u hΩ _
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, n, rfl⟩
    show IsUnit (denomExtRes u hΩ (X.basicOpen_le r)
      (algebraMap Γ(X, U) (denomExt u hΩ U) r ^ n))
    rw [map_pow, hx]
    exact ((IsLocalization.map_units Γ(X, X.basicOpen r)
      (⟨r, Submonoid.mem_powers r⟩ : Submonoid.powers r)).map
        (algebraMap Γ(X, X.basicOpen r) (denomExt u hΩ (X.basicOpen r)))).pow n
  · intro z
    obtain ⟨n, y, hy⟩ := exists_pow_mul_eq_denomExtRes u hΩ hU r z
    refine ⟨⟨y, ⟨algebraMap Γ(X, U) (denomExt u hΩ U) r ^ n, n, rfl⟩⟩, ?_⟩
    show z * denomExtRes u hΩ (X.basicOpen_le r)
        (algebraMap Γ(X, U) (denomExt u hΩ U) r ^ n)
      = denomExtRes u hΩ (X.basicOpen_le r) y
    rw [map_pow, hx]
    exact hy
  · intro y y' h
    replace h : denomExtRes u hΩ (X.basicOpen_le r) y = denomExtRes u hΩ (X.basicOpen_le r) y' := h
    have ex : ∀ x x' : Γ(X, U), resHom (X.basicOpen_le r) x = resHom (X.basicOpen_le r) x' →
        ∃ c : Submonoid.powers r, (c : Γ(X, U)) * x = c * x' := fun x x' hx =>
      IsLocalization.exists_of_eq (M := Submonoid.powers r) (S := Γ(X, X.basicOpen r))
        (by rwa [algebraMap_basicOpen_apply, algebraMap_basicOpen_apply])
    obtain ⟨c₁, h₁⟩ := ex _ _ (congrArg Ext.fst h)
    obtain ⟨c₂, h₂⟩ := ex _ _ (congrArg (fun p => (Ext.snd p).1.1) h)
    obtain ⟨c₃, h₃⟩ := ex _ _ (congrArg (fun p => (Ext.snd p).1.2) h)
    obtain ⟨N, hN⟩ := mul_mem (mul_mem c₁.2 c₂.2) c₃.2
    replace hN : r ^ N = (c₁ : Γ(X, U)) * c₂ * c₃ := hN
    refine ⟨⟨algebraMap Γ(X, U) (denomExt u hΩ U) r ^ N, N, rfl⟩, ?_⟩
    have hrN : ∀ w : denomExt u hΩ U,
        (algebraMap Γ(X, U) (denomExt u hΩ U) r ^ N : denomExt u hΩ U) * w
          = Ext.mk _ (((c₁ : Γ(X, U)) * c₂ * c₃) * w.fst)
            (((c₁ : Γ(X, U)) * c₂ * c₃) • w.snd) := by
      intro w
      rw [← map_pow, hN, mul_comm]
      exact Ext.ext' ((Ext.fst_mul_algebraMap w _).trans (mul_comm _ _))
        (Ext.snd_mul_algebraMap w _)
    show (algebraMap Γ(X, U) (denomExt u hΩ U) r ^ N : denomExt u hΩ U) * y
      = (algebraMap Γ(X, U) (denomExt u hΩ U) r ^ N : denomExt u hΩ U) * y'
    rw [hrN, hrN]
    refine Ext.ext' ?_ (Subtype.ext ?_)
    · simp only [Ext.fst_mk]
      linear_combination ((c₂ : Γ(X, U)) * c₃) * h₁
    · simp only [Ext.snd_mk, Submodule.coe_smul]
      refine Prod.ext ?_ ?_
      · show ((c₁ : Γ(X, U)) * c₂ * c₃) * y.snd.1.1 = ((c₁ : Γ(X, U)) * c₂ * c₃) * y'.snd.1.1
        linear_combination ((c₁ : Γ(X, U)) * c₃) * h₂
      · show ((c₁ : Γ(X, U)) * c₂ * c₃) * y.snd.1.2 = ((c₁ : Γ(X, U)) * c₂ * c₃) * y'.snd.1.2
        linear_combination ((c₁ : Γ(X, U)) * c₂) * h₃

end Localization

/-! ### The relative spectrum of the algebra of denominators -/

section Spectrum

variable (hΩ : Dense (Ω : Set X))

/-- The structure morphism of the algebra of denominators, restricted to the small affine
Zariski site of `X`. -/
abbrev denomAffineStructureMap :
    (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶
      (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ denomPresheaf u hΩ :=
  Functor.whiskerLeft _ (denomStructureMap u hΩ)

/-- **Quasi-coherence of the algebra of denominators**: on the basic open set of a section over
an affine open the algebra is the corresponding localization. -/
lemma coequifibered_denomAffineStructureMap :
    (denomAffineStructureMap u hΩ).Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U r
  exact isLocalization_away_denomExt u hΩ U.2 r

/-- The relative gluing datum of the algebra of denominators of `u`. -/
def denomGluingData : (Scheme.AffineZariskiSite.directedCover X).RelativeGluingData :=
  Scheme.AffineZariskiSite.relativeGluingData (coequifibered_denomAffineStructureMap u hΩ)

/-- The diagram of schemes underlying the relative gluing datum of the algebra of denominators
is locally directed. -/
instance : ((denomGluingData u hΩ).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The relative spectrum `Spec_X(𝒪_X ⊕ ℐ)` of the algebra of denominators of `u`. -/
def denomSpec : Scheme.{u} := (denomGluingData u hΩ).glued

/-- The structure morphism of the relative spectrum of the algebra of denominators. -/
def denomSpecToBase : denomSpec u hΩ ⟶ X := (denomGluingData u hΩ).toBase

/-- The chart of the relative spectrum over an affine open `U` of the base: the spectrum of the
sections of the algebra over `U`. -/
def denomChart (U : X.AffineZariskiSite) :
    Spec ((denomPresheaf u hΩ).obj (op U.1)) ⟶ denomSpec u hΩ :=
  colimit.ι (denomGluingData u hΩ).functor U

/-- The chart over `U` followed by the structure morphism is the spectrum of the structure map
over `U` followed by the inclusion of `U`. -/
lemma denomChart_comp_toBase (U : X.AffineZariskiSite) :
    denomChart u hΩ U ≫ denomSpecToBase u hΩ
      = Spec.map ((denomStructureMap u hΩ).app (op U.1)) ≫ U.2.fromSpec := by
  refine ((denomGluingData u hΩ).ι_toBase U).trans ?_
  rw [IsAffineOpen.fromSpec, ← Category.assoc]
  rfl

/-- Each chart of the relative spectrum is an open immersion. -/
instance isOpenImmersion_denomChart (U : X.AffineZariskiSite) :
    IsOpenImmersion (denomChart u hΩ U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (denomGluingData u hΩ).functor U))

/-- The image of the chart over `U` is the preimage of `U` under the structure morphism. -/
lemma opensRange_denomChart (U : X.AffineZariskiSite) :
    (denomChart u hΩ U).opensRange = denomSpecToBase u hΩ ⁻¹ᵁ U.1 :=
  (((denomGluingData u hΩ).toBase_preimage_eq_opensRange_ι U).symm.trans
    (congrArg _ (Scheme.Opens.opensRange_ι U.1)))

/-- Transfer of a property respecting isomorphisms from an arbitrary cartesian square to the
canonical pullback of the same cospan. -/
lemma prop_pullback_snd_of_isPullback {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {A B C D : Scheme.{u}} {p : A ⟶ B} {q : A ⟶ C} {g : B ⟶ D} {f : C ⟶ D}
    (h : IsPullback p q g f) (hq : P q) : P (pullback.snd g f) := by
  have he : pullback.snd g f = h.isoPullback.inv ≫ q :=
    (Iso.eq_inv_comp _).mpr h.isoPullback_hom_snd
  rw [he, P.cancel_left_of_respectsIso]
  exact hq

/-- **The relative spectrum of the algebra of denominators is integral over the base**: its
sections over an affine open are a quadratic extension, and every element of such an extension
is integral. -/
instance isIntegralHom_denomSpecToBase : IsIntegralHom (denomSpecToBase u hΩ) := by
  have hzl : IsZariskiLocalAtTarget @IsIntegralHom :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  have hri : MorphismProperty.RespectsIso @IsIntegralHom :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f hf =>
      have : IsIso f := hf
      inferInstance
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom)
    (Scheme.AffineZariskiSite.directedCover X)).mpr fun U => ?_
  refine prop_pullback_snd_of_isPullback
    ((denomGluingData u hΩ).isPullback_natTrans_ι_toBase U).flip ?_
  have h1 : IsIntegralHom (Spec.map ((denomStructureMap u hΩ).app (op U.1))) :=
    IsIntegralHom.SpecMap_iff.mpr fun y => Ext.isIntegral_elem y
  change IsIntegralHom (Spec.map ((denomStructureMap u hΩ).app (op U.1)) ≫ U.2.isoSpec.inv)
  infer_instance

/-- **The relative spectrum of the algebra of denominators is surjective over the base**: the
structure map of a quadratic extension is injective, so its spectrum is surjective. -/
instance surjective_denomSpecToBase : Surjective (denomSpecToBase u hΩ) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @Surjective)
    (Scheme.AffineZariskiSite.directedCover X)).mpr fun U => ?_
  refine prop_pullback_snd_of_isPullback
    ((denomGluingData u hΩ).isPullback_natTrans_ι_toBase U).flip ?_
  have h1 : Surjective (Spec.map ((denomStructureMap u hΩ).app (op U.1))) :=
    surjective_specMap_of_exists_isPrime_comap_eq _ fun 𝔮 h𝔮 =>
      Ext.exists_isPrime_comap_eq (d := denomDatum u hΩ U.1) 𝔮
  change Surjective (Spec.map ((denomStructureMap u hΩ).app (op U.1)) ≫ U.2.isoSpec.inv)
  infer_instance

/-! ### The square root above `Ω` -/

/-- Over an open subset of `Ω` the ideal of denominators is the whole structure sheaf and the
pair `(1, u)` is a denominator pair, whose form value is `u`: so the image of `u` in the algebra
of denominators over such an open is a square. -/
lemma isSquare_algebraMap_denomExt {V : X.Opens} (hVΩ : V ≤ Ω) :
    IsSquare (algebraMap Γ(X, V) (denomExt u hΩ V) (resHom hVΩ u)) := by
  have hmem : ((1 : Γ(X, V)), resHom hVΩ u) ∈ denomPairs u V := by
    rw [mem_denomPairs_iff]
    simpa only [map_one, mul_one] using resHom_resHom hVΩ inf_le_left u
  exact Ext.isSquare_algebraMap_of_form_eq (x := ⟨_, hmem⟩) (by simp)

/-- A square is reflected along an isomorphism of commutative rings. -/
lemma isSquare_of_isSquare_map {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsIso φ] {a : R}
    (h : IsSquare (φ a)) : IsSquare a := by
  have hinv : (CategoryTheory.inv φ) (φ a) = a := by
    rw [← CommRingCat.comp_apply, IsIso.hom_inv_id]
    rfl
  rw [← hinv]
  exact h.map (CategoryTheory.inv φ).hom

omit [IsReduced X] in
/-- **The sections over an open containing an affine open of the base, of the spectrum of a
ring over that affine open.** They are restriction to the affine open, followed by the ring map
and the canonical identifications. -/
lemma app_specMap_comp_fromSpec {R : CommRingCat.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (φ : Γ(X, V) ⟶ R) {W : X.Opens} (hVW : V ≤ W) :
    (Spec.map φ ≫ hV.fromSpec).app W
      = X.presheaf.map (homOfLE hVW).op ≫ φ ≫ (Scheme.ΓSpecIso R).inv ≫
        (Spec R).presheaf.map (homOfLE le_top).op := by
  rw [Scheme.Hom.comp_app, hV.fromSpec_app_of_le W hVW]
  simp only [Category.assoc]
  rw [Scheme.Hom.naturality, Scheme.ΓSpecIso_inv_naturality_assoc φ]
  rfl

/-- **The square root above `Ω`.** If the image of a section `s` over `W` in the algebra of
denominators over an affine open `U ≤ W` of the base is a square, then the image of `s` in the
local ring of the relative spectrum at every point above `U` is a square. -/
lemma isSquare_germ_denomSpecToBase (U : X.AffineZariskiSite) {W : X.Opens} (hUW : U.1 ≤ W)
    (s : Γ(X, W)) (hs : IsSquare ((denomStructureMap u hΩ).app (op U.1) (resHom hUW s)))
    (p : denomSpec u hΩ) (hp : denomSpecToBase u hΩ p ∈ U.1) :
    IsSquare ((denomSpec u hΩ).presheaf.germ (denomSpecToBase u hΩ ⁻¹ᵁ W) p (hUW hp)
      ((denomSpecToBase u hΩ).app W s)) := by
  have hgsq : IsSquare ((denomChart u hΩ U ≫ denomSpecToBase u hΩ).app W s) := by
    rw [denomChart_comp_toBase,
      app_specMap_comp_fromSpec U.2 ((denomStructureMap u hΩ).app (op U.1)) hUW]
    simp only [CommRingCat.comp_apply]
    exact (hs.map _).map _
  obtain ⟨z, rfl⟩ : p ∈ Set.range (denomChart u hΩ U) := by
    rw [← Scheme.Hom.coe_opensRange, opensRange_denomChart]
    exact hp
  refine isSquare_of_isSquare_map ((denomChart u hΩ U).stalkMap z) ?_
  have hgs := Scheme.Hom.germ_stalkMap_apply (f := denomChart u hΩ U)
    (denomSpecToBase u hΩ ⁻¹ᵁ W) z (hUW hp) ((denomSpecToBase u hΩ).app W s)
  rw [hgs]
  exact hgsq.map ((Spec ((denomPresheaf u hΩ).obj (op U.1))).presheaf.germ
    (denomChart u hΩ U ⁻¹ᵁ (denomSpecToBase u hΩ ⁻¹ᵁ W)) z (hUW hp)).hom

include hΩ in
/-- **(SQ) for a reduced scheme in which `Ω` is dense.** The relative spectrum of the algebra
`𝒪_X ⊕ ℐ` of denominators of `u` is integral and surjective over `X`, and at every point above
`Ω` the image of `u` is a square. -/
theorem exists_isIntegralHom_surjective_isSquare_germ_of_dense :
    ∃ (A : Scheme.{u}) (f : A ⟶ X), IsIntegralHom f ∧ Surjective f ∧
      ∀ (p : A) (hp : f.base p ∈ Ω),
        IsSquare (A.presheaf.germ (f ⁻¹ᵁ Ω) p hp (f.app Ω u)) := by
  refine ⟨denomSpec u hΩ, denomSpecToBase u hΩ, inferInstance, inferInstance, fun p hp => ?_⟩
  obtain ⟨-, ⟨V, hV, rfl⟩, hpV, hVΩ⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hp Ω.isOpen
  exact isSquare_germ_denomSpecToBase u hΩ ⟨V, hV⟩ hVΩ u
    (isSquare_algebraMap_denomExt u hΩ hVΩ) p hpV

end Spectrum

end Stacks.SquareRootCover

end
