module

public import Mathlib.RingTheory.DualNumber
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CoproductImmersion
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwo
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree-two zero-dimensional subschemes of a scheme over an algebraically closed field

Let `k` be an algebraically closed field, let `X` be locally of finite type over `k` through `p`
and let `ℒ` be an invertible module on `X`. This file proves the classification of the degree-two
zero-dimensional closed subschemes of `X` in the form the criterion of
[Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T) consumes, namely the two
propositions `AlgebraicGeometry.HasDegreeTwoPointPairs` and
`AlgebraicGeometry.HasDegreeTwoFatPoints` which
`AlgebraicGeometry.isRelativelyVeryAmple_of_surjectsOnDegreeTwo` takes as hypotheses.

Such a subscheme is either a pair of distinct reduced closed points, the spectrum of `k × k`, or
a single closed point carrying a nonzero tangent direction, the spectrum of `κ(x)[ε]`. Both are
produced here: an ordered pair of distinct closed points lies on the first kind, which carries a
section of `ℒ` vanishing at the first point and not at the second; and a nonzero tangent vector
at a closed point *is* the second kind, along which restriction of the sections of `ℒ` to the
closed point is not injective.

## Main results

* `AlgebraicGeometry.hasDegreeTwoFatPoints`: every nonzero tangent vector at a closed point is a
  closed immersion of the dual-number point, zero-dimensional of degree two over `k`, along which
  restriction of the sections of `ℒ` to the closed point is not injective.
* `AlgebraicGeometry.hasDegreeTwoPointPairs`: every ordered pair of distinct closed points lies
  on a zero-dimensional degree-two closed subscheme through which both residue-field points
  factor, carrying a section of `ℒ` which vanishes at the first and not at the second.
* `AlgebraicGeometry.isRelativelyVeryAmple_of_surjectsOnDegreeTwo_of_complete`: the criterion of
  Tag 0E8T with those two hypotheses discharged.
* `AlgebraicGeometry.isClosedImmersion_of_surjectsOnDegreeTwo`: the closed-immersion form of the
  same, for a morphism to an arbitrary separated `k`-scheme realizing the complete linear system.

## The fat points

* `AlgebraicGeometry.surjective_dottedStalkHom`: the local ring of `X` at a closed point surjects
  onto `κ(x)[ε]` along a nonzero tangent vector. The tangent vector is a derivation `D` of the
  local ring which is nonzero on some `c`, and `r + ℓ·(c - q)` realizes an arbitrary value, the
  ground field exhausting the residue field because it is algebraically closed.
* `AlgebraicGeometry.isClosedImmersion_dottedTangentArrow`: hence such a tangent vector is a
  closed immersion, its source having one point and its image being closed.
* `AlgebraicGeometry.isZeroDimensionalOfDegree_dottedTangentArrow`: the dual-number point is
  zero-dimensional of degree two over `k`.
* `AlgebraicGeometry.not_injective_pullbackSectionTop_dualNumberClosedPoint`: the dual-number
  point is the spectrum of a local ring, over which the pulled-back module is trivial, so `ε` is
  a nonzero section killed by restriction to the closed point.

## The point pairs

* `AlgebraicGeometry.twoPointSubscheme`, `AlgebraicGeometry.firstTwoPoint` and
  `AlgebraicGeometry.secondTwoPoint`: the disjoint union of the two rational points, which is the
  spectrum of `k × k`, and its two points.
* `AlgebraicGeometry.isClosedImmersion_twoPointSubscheme` and
  `AlgebraicGeometry.isZeroDimensionalOfDegree_twoPointSubscheme`: it is a closed subscheme, and
  it is zero-dimensional of degree two over `k`.
* The separating section is the idempotent `(0, 1)` read through a trivialization of the
  pulled-back module, which exists because `k × k` has finitely many maximal ideals and hence
  trivial Picard group.

## Auxiliary results

* `AlgebraicGeometry.finrank_sections_specMap`: for `ψ : k ⟶ A` the `k`-algebra structure which
  `AlgebraicGeometry.IsZeroDimensionalOfDegree` reads off the structure morphism of `Spec A` is
  the one `ψ` gives, so that the degree of `Spec A` over `k` is the dimension of `A`.
* `AlgebraicGeometry.vanishesAlong_unitModule_iff` and
  `AlgebraicGeometry.vanishesAlong_isoUnit_iff`: a global function vanishes along a morphism
  exactly when it pulls back to zero as a function, and that transports along a trivialization.

## What is not proved here

The morphism `φ_{ℒ,V} : X ⟶ 𝐏(V)` of
[Stacks, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY), with its identification of the
pulled-back degree-one twist with `ℒ`, is still a hypothesis, as is completeness of the linear
system it realizes: those are the data that
`AlgebraicGeometry.isRelativelyVeryAmple_of_surjectsOnDegreeTwo_of_complete` inherits from the
criterion of [Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S). Deriving them from
the degree-two hypothesis needs the passage from separation of closed points to generation of
`ℒ` by its global sections, which this repository does not have.

## References

* [Stacks Project, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T)
* [Stacks Project, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S)
* [Stacks Project, Tag 0B2B](https://stacks.math.columbia.edu/tag/0B2B)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Ample (IsInvertibleModule)
open Stacks.Tag01VMVeryAmple (IsRelativelyVeryAmple twistOne)
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.Tag01VMRelativeVeryAmple (symAlgebra)

universe v u

namespace AlgebraicGeometry

/-! ### The dual-number point -/

/-- The nilpotent `ε` of the dual numbers over a nontrivial ring is nonzero. -/
private theorem eps_ne_zero (κ : Type u) [CommRing κ] [Nontrivial κ] :
    (DualNumber.eps : DualNumber κ) ≠ 0 :=
  fun h => one_ne_zero (congrArg TrivSqZeroExt.snd h)

/-- The spectrum of the dual numbers over a field has a single point: every prime ideal
contains the nilpotent `ε`, and the only ideal of `κ[ε]` containing `ε` which is neither zero
nor the whole ring is `(ε)`. -/
theorem subsingleton_spec_dualNumber (κ : Type u) [Field κ] :
    Subsingleton (Spec (.of (DualNumber κ))) := by
  refine ⟨fun z w => ?_⟩
  apply PrimeSpectrum.ext
  have hmem : ∀ v : Spec (.of (DualNumber κ)),
      (DualNumber.eps : DualNumber κ) ∈ v.asIdeal := by
    intro v
    refine v.isPrime.mem_of_pow_mem 2 ?_
    rw [DualNumber.eps_pow_two]
    exact Ideal.zero_mem _
  have hne : ∀ v : Spec (.of (DualNumber κ)), v.asIdeal ≠ ⊥ := fun v hv =>
    eps_ne_zero κ (by simpa only [hv, Ideal.mem_bot] using hmem v)
  have hspan : ∀ v : Spec (.of (DualNumber κ)),
      v.asIdeal = Ideal.span {(DualNumber.eps : DualNumber κ)} := by
    intro v
    rcases DualNumber.ideal_trichotomy v.asIdeal with hb | hs | ht
    · exact (hne v hb).elim
    · exact hs
    · exact (v.isPrime.1 ht).elim
  rw [hspan z, hspan w]

/-- The inclusion of a commutative ring into its dual numbers, as a morphism of `CommRingCat`.
This is the ring map whose spectrum is `AlgebraicGeometry.dualNumberToBase`. -/
def dualNumberInclusion (κ : Type u) [CommRing κ] :
    CommRingCat.of κ ⟶ CommRingCat.of (DualNumber κ) :=
  CommRingCat.ofHom (algebraMap κ (DualNumber κ))

/-- The structure morphism of the dual-number point is the spectrum of the inclusion. -/
theorem specMap_dualNumberInclusion (κ : Type u) [CommRing κ] :
    Spec.map (dualNumberInclusion κ) = dualNumberToBase κ := rfl

/-- The projection `κ[ε] ⟶ κ`, as a morphism of `CommRingCat`. This is the ring map whose
spectrum is `AlgebraicGeometry.dualNumberClosedPoint`. -/
def dualNumberProjection (κ : Type u) [CommRing κ] :
    CommRingCat.of (DualNumber κ) ⟶ CommRingCat.of κ :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom

/-- The closed-point inclusion of the dual-number point is the spectrum of the projection. -/
theorem specMap_dualNumberProjection {X : Scheme.{u}} (x : X) :
    Spec.map (dualNumberProjection ↑(X.residueField x)) = dualNumberClosedPoint X x := rfl

/-- A global function on `Spec R` coming from `R` is zero only if it was. -/
theorem ΓSpecIso_inv_eq_zero_iff {R : CommRingCat.{u}} (r : R) :
    (Scheme.ΓSpecIso R).inv r = 0 ↔ r = 0 := by
  have hinj : Function.Injective (Scheme.ΓSpecIso R).inv :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).injective
  exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => h ▸ map_zero _⟩

/-- Pulling a global function back along `Spec φ` is applying `φ`. -/
theorem appTop_specMap_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) :=
  (congrArg (fun t : R ⟶ Γ(Spec S, ⊤) => t.hom r) (Scheme.ΓSpecIso_inv_naturality φ)).symm

/-- The dual numbers over a commutative ring are free of rank two, the isomorphism being the
pair of coordinates. -/
@[sga "3 II 4.5.1" "partial"]
def dualNumberLinearEquivProd (κ : Type u) [CommRing κ] : DualNumber κ ≃ₗ[κ] κ × κ where
  toFun z := (z.fst, z.snd)
  invFun p := TrivSqZeroExt.inl p.1 + TrivSqZeroExt.inr p.2
  left_inv z := by apply TrivSqZeroExt.ext <;> simp
  right_inv p := by apply Prod.ext <;> simp
  map_add' z w := rfl
  map_smul' r z := rfl

/-- The dual numbers over a field form a two-dimensional vector space. -/
theorem finrank_dualNumber (κ : Type u) [Field κ] : Module.finrank κ (DualNumber κ) = 2 := by
  rw [(dualNumberLinearEquivProd κ).finrank_eq, Module.finrank_prod, Module.finrank_self]

/-! ### Sections of the structure sheaf and of a trivializable module -/

section Unit

/-- The isomorphism `f^* 𝒪_Y ≅ 𝒪_X` carries the pullback of a global section of `𝒪_Y` to its
pullback as a function. -/
theorem pullbackUnitIso_pullbackSectionTop {X Y : Scheme.{u}} (g : X ⟶ Y) (a : Γ(Y, ⊤)) :
    (Scheme.Modules.pullbackUnitIso g).hom.val.app (op ⊤)
        (pullbackSectionTop g (Scheme.unitModule Y) a) = g.appTop a := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_unit
    (f := (Scheme.Modules.pullbackUnitIso g).hom)
  rw [Scheme.Modules.pullbackUnitIso_homEquiv] at h
  exact (congrArg (fun t => t.val.app (op ⊤) a) h).symm

/-- A global section of `𝒪_Y` vanishes along `g` exactly when its pullback as a function is
zero. -/
theorem vanishesAlong_unitModule_iff {X Y : Scheme.{u}} (g : X ⟶ Y) (a : Γ(Y, ⊤)) :
    VanishesAlong g (L := Scheme.unitModule Y) a ↔ g.appTop a = 0 := by
  rw [← pullbackUnitIso_pullbackSectionTop g a]
  exact (map_eq_zero_iff _ (Scheme.Modules.hom_app_injective
    (Scheme.Modules.pullbackUnitIso g) (op ⊤))).symm

/-- The component of an isomorphism of modules undoes the component of its inverse. -/
theorem Scheme.Modules.hom_app_inv_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (U : (Opens X)ᵒᵖ) (s : N.val.obj U) : e.hom.val.app U (e.inv.val.app U s) = s := by
  have h := congrArg (fun t => t.val.app U s) e.inv_hom_id
  change e.hom.val.app U (e.inv.val.app U s) = s at h
  exact h

/-- **A global section of a trivialized module vanishes along `g` exactly when the function it
comes from pulls back to zero.** -/
theorem vanishesAlong_isoUnit_iff {X Y : Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules}
    (e : M ≅ Scheme.unitModule Y) (c : Γ(Y, ⊤)) :
    VanishesAlong g (e.inv.val.app (op ⊤) c) ↔ g.appTop c = 0 := by
  have hnat := pullbackSectionTop_naturality g e.hom (e.inv.val.app (op ⊤) c)
  rw [Scheme.Modules.hom_app_inv_app e (op ⊤) c] at hnat
  refine Iff.trans ?_ (vanishesAlong_unitModule_iff g c)
  change pullbackSectionTop g M (e.inv.val.app (op ⊤) c) = 0 ↔
    pullbackSectionTop g (Scheme.unitModule Y) c = 0
  rw [← hnat]
  exact (map_eq_zero_iff _ (Scheme.Modules.hom_app_injective
    ((Scheme.Modules.pullback g).mapIso e) (op ⊤))).symm

/-- **A trivializable module has a nonzero global section vanishing along `g` whenever the
structure sheaf does.** Transporting a global function along `M ≅ 𝒪_Y` turns a nonzero function
with zero pullback into a nonzero section of `M` vanishing along `g`. -/
theorem exists_ne_zero_vanishesAlong_of_isoUnit {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (e : M ≅ Scheme.unitModule Y) (a : Γ(Y, ⊤)) (ha : a ≠ 0) (hga : g.appTop a = 0) :
    ∃ s : M.val.obj (op ⊤), s ≠ 0 ∧ VanishesAlong g s :=
  ⟨e.inv.val.app (op ⊤) a,
    fun h => ha ((map_eq_zero_iff _ (Scheme.Modules.inv_app_injective e (op ⊤))).mp h),
    (vanishesAlong_isoUnit_iff g e a).mpr hga⟩

end Unit

/-! ### The degree of an affine scheme presented as a spectrum -/

/-- **The degree of `Spec A` over `k` is the dimension of `A`.** For a ring map `ψ : k ⟶ A` the
`k`-algebra structure which `AlgebraicGeometry.IsZeroDimensionalOfDegree` puts on the global
sections of `Spec A` is carried to the one given by `ψ` by `Γ(Spec A, ⊤) ≅ A`. -/
theorem finrank_sections_specMap {k A : Type u} [Field k] [CommRing A]
    (ψ : CommRingCat.of k ⟶ CommRingCat.of A) :
    letI : Algebra k A := ψ.hom.toAlgebra
    letI : Algebra k Γ(Spec (.of A), ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map ψ).appTop).hom.toAlgebra
    Module.finrank k Γ(Spec (.of A), ⊤) = Module.finrank k A := by
  let : Algebra k A := ψ.hom.toAlgebra
  let : Algebra k Γ(Spec (.of A), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map ψ).appTop).hom.toAlgebra
  have hnat := Scheme.ΓSpecIso_inv_naturality ψ
  let e : Γ(Spec (.of A), ⊤) ≃ₐ[k] A :=
    { (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        have hr : algebraMap k Γ(Spec (.of A), ⊤) r = (Scheme.ΓSpecIso (.of A)).inv (ψ r) := by
          rw [RingHom.algebraMap_toAlgebra]
          exact (congrArg (fun t : CommRingCat.of k ⟶ Γ(Spec (.of A), ⊤) => t.hom r) hnat).symm
        rw [hr]
        change (Scheme.ΓSpecIso (.of A)).hom ((Scheme.ΓSpecIso (.of A)).inv (ψ r)) = _
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
        rfl }
  exact e.toLinearEquiv.finrank_eq

/-- **The dual numbers over a field isomorphic to `k` are two-dimensional over `k`**, for the
`k`-algebra structure given by the composite `k ⟶ κ ⟶ κ[ε]`. -/
theorem finrank_dualNumber_of_bijective {k κ : Type u} [Field k] [Field κ]
    (c : CommRingCat.of k ⟶ CommRingCat.of κ) (hc : Function.Bijective c.hom) :
    letI : Algebra k (DualNumber κ) := (c ≫ dualNumberInclusion κ).hom.toAlgebra
    Module.finrank k (DualNumber κ) = 2 := by
  let : Algebra k (DualNumber κ) := (c ≫ dualNumberInclusion κ).hom.toAlgebra
  let e : k ≃+* κ := RingEquiv.ofBijective c.hom hc
  have hsmul (r : k) (z : DualNumber κ) :
      r • z = TrivSqZeroExt.inl (e r) * z := Algebra.smul_def r z
  let L : DualNumber κ ≃ₗ[k] k × k :=
    { toFun := fun z => (e.symm z.fst, e.symm z.snd)
      invFun := fun w => TrivSqZeroExt.inl (e w.1) + TrivSqZeroExt.inr (e w.2)
      left_inv := fun z => by apply TrivSqZeroExt.ext <;> simp
      right_inv := fun w => by apply Prod.ext <;> simp
      map_add' := fun z w => by apply Prod.ext <;> simp
      map_smul' := fun r z => by
        apply Prod.ext
        · change e.symm (r • z).fst = r * e.symm z.fst
          rw [hsmul r z]
          simp [TrivSqZeroExt.fst_mul]
        · change e.symm (r • z).snd = r * e.symm z.snd
          rw [hsmul r z]
          simp [TrivSqZeroExt.snd_mul] }
  rw [L.finrank_eq, Module.finrank_prod, Module.finrank_self]

/-! ### A nonzero tangent vector is a closed immersion of the dual-number point -/

section ClosedImmersion

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- **The local ring of `X` at a closed point surjects onto the dual numbers of the residue
field along a nonzero tangent vector.** Writing `θ` as a derivation `D` of the local ring, the
element `r + ℓ·(c - q)` with `D c ≠ 0` has prescribed image, the ground field mapping onto the
residue field because it is algebraically closed. -/
theorem surjective_dottedStalkHom (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (x : X) (hx : IsClosed ({x} : Set X)) (θ : DottedTangentArrow p x) (hθ : θ ≠ 0) :
    Function.Surjective (dottedStalkHom p x θ).hom := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let e : k ≃+* X.residueField x :=
    RingEquiv.ofBijective (algebraMap k (X.residueField x))
      (bijective_algebraMap_residueField_of_isClosed p x hx)
  let R := X.presheaf.stalk x
  let α : k →+* R :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.presheaf.Γgerm x).hom)
  let : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  let : SMulCommClass (X.residueField x) (X.presheaf.stalk x) (X.residueField x) := ⟨by
    intro r a v
    change r * ((X.residue x a) * v) = (X.residue x a) * (r * v)
    ring⟩
  let D := dottedToDerivation p x θ
  have hres (r : k) : X.residue x (α r) = e r := rfl
  have hbase (r : k) : D.1 (α r) = 0 := by
    have hα : α r = p.stalkMap x
        ((Spec (.of k)).presheaf.germ ⊤ (p x) (by trivial)
          ((Scheme.ΓSpecIso (.of k)).inv r)) := by
      change X.presheaf.germ ⊤ x trivial
          (p.appTop ((Scheme.ΓSpecIso (.of k)).inv r)) = _
      symm
      exact Scheme.Hom.germ_stalkMap_apply p ⊤ x (by trivial)
        ((Scheme.ΓSpecIso (.of k)).inv r)
    rw [hα]
    exact D.2 _
  have hDne : D ≠ 0 := by
    intro hd
    refine hθ ?_
    calc
      θ = derivationToDotted p x D := (derivationToDotted_dottedToDerivation p x θ).symm
      _ = derivationToDotted p x 0 := by rw [hd]
      _ = 0 := rfl
  obtain ⟨c, hc⟩ : ∃ c : R, D.1 c ≠ 0 := by
    by_contra! hn
    exact hDne (Subtype.ext (Derivation.ext hn))
  let g := (dottedStalkHom p x θ).hom
  have hfst (a : R) : (g a).fst = X.residue x a :=
    congrArg (fun φ : CommRingCat.of R ⟶ X.residueField x => φ.hom a)
      (dottedStalkHom_fst p x θ)
  intro z
  let r : k := e.symm z.fst
  let q : k := e.symm (X.residue x c)
  let c₀ : R := c - α q
  let ell : k := e.symm (z.snd / D.1 c)
  have hq : X.residue x (α q) = X.residue x c := by
    rw [hres q]
    exact e.apply_symm_apply _
  have hresc₀ : X.residue x c₀ = 0 := by
    change X.residue x (c - α q) = 0
    rw [map_sub, hq, sub_self]
  have hDc₀ : D.1 c₀ = D.1 c := by
    simp [c₀, map_sub, hbase]
  refine ⟨α r + α ell * c₀, ?_⟩
  apply TrivSqZeroExt.ext
  · change (g (α r + α ell * c₀)).fst = z.fst
    rw [hfst, map_add, map_mul, hres r, hres ell, hresc₀, mul_zero, add_zero]
    exact e.apply_symm_apply _
  · change D.1 (α r + α ell * c₀) = z.snd
    have hderiv : D.1 (α r + α ell * c₀) = X.residue x (α ell) * D.1 c₀ := by
      calc
        D.1 (α r + α ell * c₀) = D.1 (α r) + D.1 (α ell * c₀) := map_add _ _ _
        _ = 0 + (α ell • D.1 c₀ + c₀ • D.1 (α ell)) := by rw [hbase r, D.1.leibniz]
        _ = X.residue x (α ell) * D.1 c₀ := by
          rw [hbase ell]
          change 0 + (X.residue x (α ell) * D.1 c₀ + X.residue x c₀ * 0) = _
          rw [hresc₀]
          ring
    rw [hderiv, hDc₀, show X.residue x (α ell) = z.snd / D.1 c by
      rw [hres ell]; exact e.apply_symm_apply _]
    exact div_mul_cancel₀ _ hc

/-- **The structure morphism of the dual-number point of a closed point is the spectrum of
`k ≅ κ(x) ⟶ κ(x)[ε]`.** Both triangles of the tangent diagram are used: the arrow lies over the
base, and the residue field at a closed point is the base field. -/
theorem dottedTangentArrow_comp_eq_specMap (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (x : X) (hx : IsClosed ({x} : Set X)) (θ : DottedTangentArrow p x) :
    θ.val ≫ p = Spec.map (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x) ≫
      dualNumberInclusion ↑(X.residueField x)) := by
  have h1 : θ.val ≫ p = Spec.map (dualNumberInclusion ↑(X.residueField x)) ≫
      Spec.map (p.residueFieldMap x) ≫ (Spec (.of k)).fromSpecResidueField (p.base x) :=
    θ.property.2
  rw [h1, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← SpecMap_residueFieldIsoBase_inv p x hx, ← Spec.map_comp,
    residueFieldIsoBase_inv_eq p x hx]

/-- **The dual-number point of a closed point is zero-dimensional of degree two over the base
field.** Its space is a single point, and its ring of global sections is `κ(x)[ε]`, which is
two-dimensional over `κ(x)` and hence over `k`, the residue field at a closed point being the
base field. -/
theorem isZeroDimensionalOfDegree_dottedTangentArrow (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X))
    (θ : DottedTangentArrow p x) : IsZeroDimensionalOfDegree (θ.val ≫ p) 2 := by
  let : Subsingleton (Spec (.of (DualNumber (X.residueField x)))) :=
    subsingleton_spec_dualNumber _
  have hbij : Function.Bijective
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom := by
    let : Algebra k ↑(X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
    have h := bijective_algebraMap_residueField_of_isClosed p x hx
    rwa [RingHom.algebraMap_toAlgebra] at h
  rw [dottedTangentArrow_comp_eq_specMap p x hx θ]
  refine ⟨topologicalKrullDim_zero_of_discreteTopology _, ?_⟩
  rw [finrank_sections_specMap]
  exact finrank_dualNumber_of_bijective _ hbij

/-- A morphism out of a one-point scheme which is surjective on stalks and lands in a closed
point is a closed immersion: its underlying map is a closed embedding. -/
theorem isClosedImmersion_of_source_subsingleton {Z : Scheme.{u}} (i : Z ⟶ X)
    [Subsingleton Z] [Nonempty Z] (x : X) (hi : ∀ z : Z, i z = x)
    (hx : IsClosed ({x} : Set X)) (hs : SurjectiveOnStalks i) : IsClosedImmersion i := by
  let := hs
  have hclosedMap : IsClosedMap i.base := by
    intro s _
    by_cases hempty : s = ∅
    · simp [hempty]
    have himage : i.base '' s = {x} := by
      obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨z, hz, hi z⟩, ?_⟩
      rintro _ ⟨w, -, rfl⟩
      exact hi w
    rwa [himage]
  exact { toSurjectiveOnStalks := hs
          isClosedEmbedding := Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
            i.continuous (fun _ _ _ => Subsingleton.elim _ _) hclosedMap }

/-- **A nonzero tangent vector at a closed point is a closed immersion of the dual-number
point.** The local ring surjects onto `κ(x)[ε]`, so the corresponding morphism of spectra is a
closed immersion, and the tangent arrow factors through it. -/
theorem isClosedImmersion_dottedTangentArrow (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (x : X) (hx : IsClosed ({x} : Set X)) (θ : DottedTangentArrow p x) (hθ : θ ≠ 0) :
    IsClosedImmersion θ.val := by
  let : Subsingleton (Spec (.of (DualNumber (X.residueField x)))) :=
    subsingleton_spec_dualNumber (X.residueField x)
  let : IsClosedImmersion (Spec.map (dottedStalkHom p x θ)) :=
    IsClosedImmersion.spec_of_surjective _ (surjective_dottedStalkHom p x hx θ hθ)
  have hcomp : SurjectiveOnStalks θ.val := by
    rw [← dottedStalkHom_spec p x θ]
    infer_instance
  refine isClosedImmersion_of_source_subsingleton θ.val x (fun z => ?_) hx hcomp
  rw [Subsingleton.elim z (IsLocalRing.closedPoint
    (CommRingCat.of (DualNumber (X.residueField x))))]
  exact dotted_closedPoint p x θ

/-! ### The restriction of sections to the closed point of the dual-number point -/

omit [IsAlgClosed k] in
/-- **Restriction of the sections of an invertible module along a tangent vector to the closed
point is not injective.** On the dual-number point, which is the spectrum of a local ring, the
pulled-back module is trivial, so `ε` gives a nonzero section killed by restriction. -/
theorem not_injective_pullbackSectionTop_dualNumberClosedPoint (p : X ⟶ Spec (.of k))
    (x : X) (L : X.Modules) [IsInvertibleModule X L] (θ : DottedTangentArrow p x) :
    ¬ Function.Injective (pullbackSectionTop (dualNumberClosedPoint X x)
      ((Scheme.Modules.pullback θ.val).obj L)) := by
  obtain ⟨e⟩ := Stacks.PicardUFD.isTrivial_of_isInvertible_spec
    (DualNumber ↑(X.residueField x)) ((Scheme.Modules.pullback θ.val).obj L)
  have ha : (Scheme.ΓSpecIso (.of (DualNumber ↑(X.residueField x)))).inv
      (DualNumber.eps : DualNumber ↑(X.residueField x)) ≠ 0 := by
    rw [Ne, ΓSpecIso_inv_eq_zero_iff]
    exact eps_ne_zero _
  have hga : (dualNumberClosedPoint X x).appTop
      ((Scheme.ΓSpecIso (.of (DualNumber ↑(X.residueField x)))).inv
        (DualNumber.eps : DualNumber ↑(X.residueField x))) = 0 := by
    rw [← specMap_dualNumberProjection x, appTop_specMap_ΓSpecIso_inv,
      show dualNumberProjection ↑(X.residueField x)
        (DualNumber.eps : DualNumber ↑(X.residueField x)) = 0 from
        DualNumber.fst_eps, map_zero]
  obtain ⟨s, hs0, hsv⟩ := exists_ne_zero_vanishesAlong_of_isoUnit (dualNumberClosedPoint X x)
    ((Scheme.Modules.pullback θ.val).obj L) e _ ha hga
  exact fun hinj => hs0 (hinj (hsv.trans (map_zero _).symm))

/-- **Every nonzero tangent vector at a closed point of `X` is a fat degree-two point of `X`.**
The dual-number point is a closed immersion, it is zero-dimensional of degree two over `k`, and
restriction of the sections of `ℒ` along it to the closed point is not injective. -/
theorem hasDegreeTwoFatPoints (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (L : X.Modules) [IsInvertibleModule X L] : HasDegreeTwoFatPoints p L :=
  fun x hx θ hθ => ⟨isClosedImmersion_dottedTangentArrow p x hx θ hθ,
    isZeroDimensionalOfDegree_dottedTangentArrow p x hx θ,
    not_injective_pullbackSectionTop_dualNumberClosedPoint p x L θ⟩

end ClosedImmersion


/-! ### The reduced degree-two subschemes -/

section PointPairs

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- The product of two copies of a field is two-dimensional over it. -/
theorem finrank_prod_self (k : Type u) [Field k] :
    letI : Algebra k (k × k) := (CommRingCat.ofHom (algebraMap k (k × k))).hom.toAlgebra
    Module.finrank k (k × k) = 2 := by
  let : Algebra k (k × k) := (CommRingCat.ofHom (algebraMap k (k × k))).hom.toAlgebra
  let L : (k × k) ≃ₗ[k] k × k :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [L.finrank_eq, Module.finrank_prod, Module.finrank_self]

/-- The spectrum of the product of two copies of a field is discrete. -/
instance discreteTopology_spec_prod_self (k : Type u) [Field k] :
    DiscreteTopology (Spec (.of (k × k))) :=
  PrimeSpectrum.primeSpectrumProdHomeo.symm.discreteTopology

/-- The product of two copies of a field has finitely many maximal ideals. -/
instance finite_maximalSpectrum_prod_self (k : Type u) [Field k] :
    Finite (MaximalSpectrum (k × k)) :=
  Finite.of_injective _ MaximalSpectrum.toPrimeSpectrum_injective

/-- **The degree-two subscheme carried by an ordered pair of distinct closed points**: the
disjoint union of the two rational points, which is the spectrum of `k × k`. -/
def twoPointSubscheme (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] {x y : X}
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)) :
    Spec (.of (k × k)) ⟶ X :=
  inv (coprodSpec k k) ≫ Limits.coprod.desc (pointOfClosedPoint p x hx)
    (pointOfClosedPoint p y hy)

/-- The first of the two points of the two-point subscheme. -/
def firstTwoPoint (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    Spec (.of (X.residueField x)) ⟶ Spec (.of (k × k)) :=
  Spec.map (CommRingCat.ofHom (RingHom.fst k k) ≫ (residueFieldIsoBase p x hx).inv)

/-- The second of the two points of the two-point subscheme. -/
def secondTwoPoint (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] {y : X}
    (hy : IsClosed ({y} : Set X)) :
    Spec (.of (X.residueField y)) ⟶ Spec (.of (k × k)) :=
  Spec.map (CommRingCat.ofHom (RingHom.snd k k) ≫ (residueFieldIsoBase p y hy).inv)

variable (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] {x y : X}
  (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X))

/-- The first point of the two-point subscheme lies over the residue-field point of `x`. -/
theorem firstTwoPoint_comp :
    firstTwoPoint p hx ≫ twoPointSubscheme p hx hy = X.fromSpecResidueField x := by
  rw [firstTwoPoint, twoPointSubscheme, Spec.map_comp, ← coprodSpec_inl, Category.assoc,
    Category.assoc, IsIso.hom_inv_id_assoc, Limits.coprod.inl_desc, pointOfClosedPoint,
    ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  exact Category.id_comp _

/-- The second point of the two-point subscheme lies over the residue-field point of `y`. -/
theorem secondTwoPoint_comp :
    secondTwoPoint p hy ≫ twoPointSubscheme p hx hy = X.fromSpecResidueField y := by
  rw [secondTwoPoint, twoPointSubscheme, Spec.map_comp, ← coprodSpec_inr, Category.assoc,
    Category.assoc, IsIso.hom_inv_id_assoc, Limits.coprod.inr_desc, pointOfClosedPoint,
    ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  exact Category.id_comp _

/-- The two-point subscheme is a closed subscheme when the two points are distinct. -/
theorem isClosedImmersion_twoPointSubscheme (hxy : x ≠ y) :
    IsClosedImmersion (twoPointSubscheme p hx hy) := by
  have h : ∀ {z : X} (hz : IsClosed ({z} : Set X)), IsClosedImmersion (pointOfClosedPoint p z hz) :=
    fun hz => isClosedImmersion_of_comp_eq_id p _ (pointOfClosedPoint_comp p _ hz)
  have := h hx
  have := h hy
  have : IsClosedImmersion (Limits.coprod.desc (pointOfClosedPoint p x hx)
      (pointOfClosedPoint p y hy)) := by
    refine isClosedImmersion_coprodDesc _ _ (Set.disjoint_left.mpr ?_)
    rintro _ ⟨z, rfl⟩ ⟨w, hw⟩
    simp only [pointOfClosedPoint_apply] at hw
    exact hxy hw.symm
  exact inferInstanceAs (IsClosedImmersion (inv (coprodSpec k k) ≫ _))

/-- The structure morphism of the two-point subscheme is the diagonal `k ⟶ k × k`. -/
theorem twoPointSubscheme_comp :
    twoPointSubscheme p hx hy ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) := by
  apply (cancel_epi (coprodSpec k k)).mp
  simp only [twoPointSubscheme, Category.assoc, IsIso.hom_inv_id_assoc]
  apply Limits.coprod.hom_ext
  · rw [Limits.coprod.inl_desc_assoc, pointOfClosedPoint_comp, ← Category.assoc,
      coprodSpec_inl, ← Spec.map_comp]
    exact (Spec.map_id _).symm
  · rw [Limits.coprod.inr_desc_assoc, pointOfClosedPoint_comp, ← Category.assoc,
      coprodSpec_inr, ← Spec.map_comp]
    exact (Spec.map_id _).symm

/-- The two-point subscheme is zero-dimensional of degree two over `k`. -/
theorem isZeroDimensionalOfDegree_twoPointSubscheme :
    IsZeroDimensionalOfDegree (twoPointSubscheme p hx hy ≫ p) 2 := by
  rw [twoPointSubscheme_comp]
  refine ⟨topologicalKrullDim_zero_of_discreteTopology _, ?_⟩
  rw [finrank_sections_specMap]
  exact finrank_prod_self k

/-- **Every ordered pair of distinct closed points of `X` lies on a reduced degree-two closed
subscheme carrying a section of `ℒ` which vanishes at the first point and not at the second.**
The subscheme is the disjoint union of the two rational points, the spectrum of `k × k`, whose
Picard group is trivial because it has finitely many maximal ideals; the idempotent `(0, 1)` is
the required section. -/
theorem hasDegreeTwoPointPairs (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (L : X.Modules) [IsInvertibleModule X L] : HasDegreeTwoPointPairs p L := by
  intro x y hx hy hxy
  refine ⟨_, twoPointSubscheme p hx hy, firstTwoPoint p hx, secondTwoPoint p hy,
    isClosedImmersion_twoPointSubscheme p hx hy hxy,
    isZeroDimensionalOfDegree_twoPointSubscheme p hx hy,
    firstTwoPoint_comp p hx hy, secondTwoPoint_comp p hx hy, ?_⟩
  obtain ⟨e₀⟩ := Stacks.PicardUFD.isTrivial_of_isInvertible_spec (k × k)
    ((Scheme.Modules.pullback (twoPointSubscheme p hx hy)).obj L)
  let e : (Scheme.Modules.pullback (twoPointSubscheme p hx hy)).obj L ≅
    Scheme.unitModule (Spec (.of (k × k))) := e₀
  refine ⟨e.inv.val.app (op ⊤) ((Scheme.ΓSpecIso (.of (k × k))).inv ((0, 1) : k × k)), ?_, ?_⟩
  · rw [vanishesAlong_isoUnit_iff, firstTwoPoint, appTop_specMap_ΓSpecIso_inv]
    simp
  · rw [vanishesAlong_isoUnit_iff, secondTwoPoint, appTop_specMap_ΓSpecIso_inv]
    simp

end PointPairs

/-! ### Very ampleness, with the classification discharged -/

section VeryAmple

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- **[Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T), with the classification of
the degree-two subschemes proved.** Let `k` be algebraically closed, let `X` be proper over `k`
through `p`, let `E` be a quasi-coherent `k`-module and let `i : X ⟶ 𝐏(E)` be a morphism over
`k` with `i^* 𝒪_{𝐏(E)}(1) ≅ ℒ` realizing the complete linear system of an invertible `ℒ`. If
`H⁰(X, ℒ) ⟶ H⁰(Z, ℒ|_Z)` is surjective for every closed subscheme `Z ⊆ X` which is
zero-dimensional of degree two over `k`, then `ℒ` is very ample relative to `p`.

This is `AlgebraicGeometry.isRelativelyVeryAmple_of_surjectsOnDegreeTwo` with its two
classification hypotheses supplied: `AlgebraicGeometry.hasDegreeTwoPointPairs` and
`AlgebraicGeometry.hasDegreeTwoFatPoints`. What is still a hypothesis is the morphism to `𝐏(E)`
with its identification of the pulled-back twist, which is the morphism of
[Stacks, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY) inherited from the criterion of
[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S), together with completeness of the
linear system it realizes. -/
@[stacks 0E8T "the degree-two criterion with the classification of the degree-two \
zero-dimensional subschemes into point pairs and fat points PROVED; what is still \
assumed is the Tag 0FCY morphism to 𝐏(E) with its twist identification, inherited from \
Tag 0E8S, and completeness of the linear system it realizes"]
theorem isRelativelyVeryAmple_of_surjectsOnDegreeTwo_of_complete
    {E : (Spec (CommRingCat.of k)).Modules} [E.IsQuasicoherent]
    (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (i : X ⟶ (relativeProj (symAlgebra E)).scheme)
    (h : i ≫ (relativeProj (symAlgebra E)).toBase = p)
    {L : X.Modules} [IsInvertibleModule X L]
    (e : (Scheme.Modules.pullback i).obj (twistOne E) ≅ L)
    {V : Type v} {t : V → (twistOne E).val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, e.hom.val.app (op ⊤) (pullbackSectionTop i (twistOne E) (t v)) = ψ v)
    (hfull : Function.Surjective ψ) (hsurj : SurjectsOnDegreeTwo p L) :
    IsRelativelyVeryAmple p L :=
  isRelativelyVeryAmple_of_surjectsOnDegreeTwo p i h e htψ hfull hsurj
    (hasDegreeTwoPointPairs p L) (hasDegreeTwoFatPoints p L)

/-- **The closed-immersion form of the degree-two criterion.** Let `k` be algebraically closed,
let `X` be proper over `k` through `p`, let `φ : X ⟶ Y` be a morphism of `k`-schemes with `Y`
separated over `k` and let `θ : φ^* ℳ ≅ ℒ` carry a family of global sections of `ℳ` onto all of
`H⁰(X, ℒ)` for an invertible `ℒ`. If `H⁰(X, ℒ) ⟶ H⁰(Z, ℒ|_Z)` is surjective for every
zero-dimensional degree-two closed subscheme `Z ⊆ X`, then `φ` is a closed immersion.

This is the criterion of [Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S) with both
separation conditions supplied from the degree-two hypothesis of Tag 0E8T; the target is
arbitrary, so a morphism to any separated `k`-scheme realizing the complete linear system of `ℒ`
may be fed to it. -/
theorem isClosedImmersion_of_surjectsOnDegreeTwo {Y : Scheme.{u}} (f : X ⟶ Y)
    (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k)) (hfq : f ≫ q = p)
    [IsProper p] [IsSeparated q] {M : Y.Modules} {L : X.Modules} [IsInvertibleModule X L]
    (θ : (Scheme.Modules.pullback f).obj M ≅ L)
    {V : Type v} {t : V → M.val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, θ.hom.val.app (op ⊤) (pullbackSectionTop f M (t v)) = ψ v)
    (hfull : Function.Surjective ψ) (hsurj : SurjectsOnDegreeTwo p L) :
    IsClosedImmersion f :=
  isClosedImmersion_of_separatesClosedPoints_of_separatesTangentVectors f p q hfq θ htψ
    (separatesClosedPoints_of_surjectsOnDegreeTwo p hsurj (hasDegreeTwoPointPairs p L) hfull)
    (separatesTangentVectors_of_surjectsOnDegreeTwo p hsurj (hasDegreeTwoFatPoints p L) hfull)

end VeryAmple

end AlgebraicGeometry

end
