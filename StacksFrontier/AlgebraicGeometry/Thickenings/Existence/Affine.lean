module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.AffineHomOfRingHom
public import StacksFrontier.AlgebraicGeometry.Thickenings.Universal
public import StacksFrontier.RingTheory.Unramified.Thickening

/-!
# Existence of the universal first-order thickening: the affine case

Let `h : Z ⟶ X` be a formally unramified morphism of schemes. This file proves that `Z` admits
a universal first-order thickening over `X`, that is, that
`Stacks.Thickenings.UniversalFirstOrderThickening h` is nonempty, and fixes a choice of one.

The construction is the one of the source: locally it is the spectrum of the *algebraic*
universal first-order thickening, `Algebra.FormallyUnramified.universalFirstOrderThickening`
(Tag 04EB, in `StacksFrontier/RingTheory/Unramified/Thickening.lean`), and the local pieces are
glued over an affine open cover of `Z` subordinate to an affine open cover of `X`.

This file contains the affine case of the construction and the restriction of a universal
first-order thickening to opens; the gluing is carried out in
`StacksFrontier/AlgebraicGeometry/Thickenings/Existence/Gluing.lean`.

## Main results

* `Stacks.Thickenings.isUniversalFirstOrderThickening_resLE`: the restrictions of the inclusion
  and of the structure morphism of a universal first-order thickening to compatible opens of
  `Z'`, `Z` and `X` are a universal first-order thickening of the restricted morphism. This is
  the second assertion of Tag 04FA, and it is also the first of the "general remarks" in the
  proof of Tag 04F3, where it is used to restrict the chosen thickening of a chart to the
  overlaps of an open cover.

## Implementation notes

The existence statement is proved first, as
`Stacks.Thickenings.nonempty_universalFirstOrderThickening`, and the chosen thickening is
`Nonempty.some` of it. The ambient scheme is therefore opaque rather than reducible to the
glued scheme. That is deliberate: by
`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso` the universal property
determines the thickening up to unique isomorphism, so no consumer should depend on the
particular cover used here. It is also forced by the module system — the pieces of the
construction are `private`, so they cannot appear in the exposed body of a public definition.

The gluing is carried out with `AlgebraicGeometry.Scheme.GlueData`. Its cocycle condition is
not checked by hand: the triple overlaps are themselves universal first-order thickenings of
the triple overlaps in `Z`, hence determined up to unique isomorphism, and the transition
isomorphisms are the canonical ones (`Stacks.Thickenings.isoOfIsUniversal`), so every identity
between them follows from uniqueness of lifts.

Two ingredients carry the mathematical weight. Uniqueness of lifts is Mathlib's
`AlgebraicGeometry.FormallyUnramified.hom_ext` (Tag 04F1); it applies because the structure
morphism of each local thickening is formally unramified, which is `Tag 04EC` on the algebra
side. Existence of local lifts against *arbitrary* (not necessarily affine) test thickenings
is `Stacks.Thickenings.affineThickeningSkeleton_existsUnique_lift`, which covers the test
thickening by affine opens, lifts on each, and glues using uniqueness on the overlaps.

## References

* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 04EB](https://stacks.math.columbia.edu/tag/04EB)
* [Stacks Project, Tag 04FA](https://stacks.math.columbia.edu/tag/04FA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- Two lifts of a map out of the closed subscheme of a first-order thickening, both compatible
with the structure morphism to the base, agree when that structure morphism is formally
unramified. This is the uniqueness half of the universal property, and it is the only place
where formal unramifiedness of the ambient thickening is used. -/
private lemma lift_unique_of_formallyUnramified
    {T T' Z Z' X : Scheme.{u}} (j : T ⟶ T')
    (hj : IsFirstOrderThickening j)
    (i : Z ⟶ Z') (h' : Z' ⟶ X) [FormallyUnramified h']
    (a : T ⟶ Z) (b : T' ⟶ X)
    (f g : T' ⟶ Z')
    (hf : j ≫ f = a ≫ i ∧ f ≫ h' = b)
    (hg : j ≫ g = a ≫ i ∧ g ≫ h' = b) : f = g := by
  have : IsClosedImmersion j := hj.1
  apply FormallyUnramified.hom_ext j ⟨2, by simpa using hj.2⟩ h'
  · rw [hf.1, hg.1]
  · rw [hf.2, hg.2]

/-- The preimage of a square-zero ideal under an injective ring map is square-zero. -/
private lemma comap_sq_eq_bot_of_injective {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ) {I : Ideal S} (hI : I ^ 2 = ⊥) :
    I.comap φ ^ 2 = ⊥ := by
  have hle := Ideal.le_comap_pow (K := I) φ 2
  rw [hI, Ideal.comap_bot_of_injective φ hφ] at hle
  exact le_bot_iff.mp hle

/-- The sections over an affine open of a square-zero ideal sheaf form a square-zero ideal. -/
private lemma ideal_sq_eq_bot {Y : Scheme.{u}} {J : Scheme.IdealSheafData Y} (hJ : J ^ 2 = ⊥)
    (V : Y.affineOpens) : J.ideal V ^ 2 = ⊥ := by
  simpa [Scheme.IdealSheafData.ideal_pow] using congrArg (fun K => K.ideal V) hJ

/-- The spectrum of a surjection of rings with square-zero kernel is a first-order thickening. -/
lemma isFirstOrderThickening_specMap {R S : Type u} [CommRing R] [CommRing S]
    (φ : CommRingCat.of R ⟶ CommRingCat.of S)
    (hsurj : Function.Surjective φ.hom) (hker : RingHom.ker φ.hom ^ 2 = ⊥) :
    IsFirstOrderThickening (Spec.map φ) := by
  have hkerApp : RingHom.ker (Spec.map φ).appTop.hom =
      (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom := by
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    have hn := congrArg (fun k : CommRingCat.Hom _ _ => k.hom x)
      (Scheme.ΓSpecIso_naturality φ)
    change (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        ((Spec.map φ).appTop.hom x) = φ.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) at hn
    constructor
    · intro hx
      change φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = 0
      rw [← hn, hx]
      simp
    · intro hx
      apply (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of S)).hom).1
      rwa [map_zero, hn]
  have htop : RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥ := by
    rw [hkerApp]
    exact comap_sq_eq_bot_of_injective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1 hker
  refine ⟨AlgebraicGeometry.IsClosedImmersion.spec_of_surjective φ hsurj, ?_⟩
  apply (Scheme.IdealSheafData.equivOfIsAffine
    (X := Spec (CommRingCat.of R))).injective
  simp only [map_pow, Scheme.ker_of_isAffine]
  simpa using htop

/-- The ring of a universal first-order thickening of `S` over `R` is formally unramified over `R`.
The ring of a universal first-order thickening of `S` over `R` is formally unramified over `R`. -/
lemma formallyUnramified_ring_of_isUniversal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{u} R S)
    (hP : P.IsUniversalFirstOrderThickening) : Algebra.FormallyUnramified R P.Ring :=
  (Algebra.Extension.IsUniversalFirstOrderThickening.formallyUnramified_ring_and_bijective_map
    R hP).1

/-- The universal property of a universal first-order thickening, restated for a surjection
`q : B →ₐ[R] A` with square-zero kernel instead of a quotient map: every `R`-algebra map
`S →ₐ[R] A` lifts uniquely through `q` along `P.Ring → S`. -/
private lemma existsUnique_algHom_lift
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B]
    (P : Algebra.Extension.{u} R S)
    (hP : P.IsUniversalFirstOrderThickening)
    (q : B →ₐ[R] A) (hq : Function.Surjective q)
    (hker : RingHom.ker q.toRingHom ^ 2 = ⊥)
    (a : S →ₐ[R] A) :
    ∃! a' : P.Ring →ₐ[R] B,
      q.comp a' = a.comp (IsScalarTower.toAlgHom R P.Ring S) := by
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := q) hq
  let a₀ : S →ₐ[R] B ⧸ RingHom.ker q.toRingHom := e.symm.toAlgHom.comp a
  obtain ⟨a', ha', huniq⟩ :=
    hP.existsUnique_lift (RingHom.ker q.toRingHom) hker a₀
  refine ⟨a', ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    have hx := DFunLike.congr_fun ha' x
    calc
      q (a' x) = e (Ideal.Quotient.mk (RingHom.ker q.toRingHom) (a' x)) :=
        (Ideal.quotientKerAlgEquivOfSurjective_mk hq (a' x)).symm
      _ = e (a₀ ((IsScalarTower.toAlgHom R P.Ring S) x)) := congrArg e hx
      _ = a ((IsScalarTower.toAlgHom R P.Ring S) x) := by
        change e (e.symm (a ((IsScalarTower.toAlgHom R P.Ring S) x))) = _
        exact e.apply_symm_apply _
  · intro b hb
    apply huniq b
    apply AlgHom.ext
    intro x
    have hx := DFunLike.congr_fun hb x
    apply e.injective
    calc
      e (Ideal.Quotient.mk (RingHom.ker q.toRingHom) (b x)) = q (b x) :=
        Ideal.quotientKerAlgEquivOfSurjective_mk hq (b x)
      _ = a ((IsScalarTower.toAlgHom R P.Ring S) x) := hx
      _ = e (a₀ ((IsScalarTower.toAlgHom R P.Ring S) x)) := by
        change _ = e (e.symm (a ((IsScalarTower.toAlgHom R P.Ring S) x)))
        exact (e.apply_symm_apply _).symm

/-- Global sections of `Z.isoSpec.hom ≫ Spec.map q` for an affine scheme `Z`. -/
private lemma isoSpec_hom_comp_specMap_appTop {Z : Scheme.{u}} [IsAffine Z]
    {P : CommRingCat.{u}} (q : P ⟶ Γ(Z, ⊤)) :
    (Z.isoSpec.hom ≫ Spec.map q).appTop.hom =
      q.hom.comp (Scheme.ΓSpecIso P).hom.hom := by
  rw [Scheme.Hom.comp_appTop]
  have hz : Z.isoSpec.hom.appTop = (Scheme.ΓSpecIso (Γ(Z, ⊤))).hom := by
    change Z.toSpecΓ.appTop = _
    exact Scheme.toSpecΓ_appTop Z
  rw [hz]
  have hn := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality q)
  simpa only [CommRingCat.hom_comp] using hn

/-- Global sections of `Spec.map q ≫ X.isoSpec.inv` for an affine scheme `X`. -/
private lemma specMap_comp_isoSpec_inv_appTop {X : Scheme.{u}} [IsAffine X]
    {P : CommRingCat.{u}} (q : Γ(X, ⊤) ⟶ P) :
    (Spec.map q ≫ X.isoSpec.inv).appTop.hom =
      (Scheme.ΓSpecIso P).inv.hom.comp q.hom := by
  rw [Scheme.Hom.comp_appTop]
  have hx : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso (Γ(X, ⊤))).inv := by
    have hxhom : X.isoSpec.hom.appTop = (Scheme.ΓSpecIso (Γ(X, ⊤))).hom := by
      change X.toSpecΓ.appTop = _
      exact Scheme.toSpecΓ_appTop X
    apply (cancel_mono (Scheme.ΓSpecIso (Γ(X, ⊤))).hom).mp
    rw [← hxhom, ← Scheme.Hom.comp_appTop X.isoSpec.hom X.isoSpec.inv,
      X.isoSpec.hom_inv_id]
    rw [hxhom]
    exact (Iso.inv_hom_id (Scheme.ΓSpecIso (Γ(X, ⊤)))).symm
  rw [hx]
  have hn := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality q)
  simpa only [CommRingCat.hom_comp] using hn.symm

/-- Two morphisms of affine schemes agreeing on global sections are equal. -/
lemma hom_ext_of_appTop_eq {Y X : Scheme.{u}} [IsAffine X]
    (f g : Y ⟶ X) (h : f.appTop.hom = g.appTop.hom) : f = g := by
  have hcat : f.appTop = g.appTop := by
    ext x
    exact DFunLike.congr_fun h x
  apply (cancel_mono X.toSpecΓ).mp
  rw [Scheme.toSpecΓ_naturality f, Scheme.toSpecΓ_naturality g, hcat]

/-- For a closed immersion into an affine scheme, a square-zero defining ideal sheaf has
square-zero ideal of global sections. -/
private lemma ker_appTop_sq_eq_bot {T T' : Scheme.{u}} [IsAffine T']
    (i : T ⟶ T') [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥) :
    (RingHom.ker i.appTop.hom) ^ 2 = ⊥ := by
  have h := ideal_sq_eq_bot hi ⟨⊤, isAffineOpen_top T'⟩
  rwa [Scheme.Hom.ker_apply] at h

/-- A formally unramified morphism of affine schemes is formally unramified on global sections. -/
private lemma formallyUnramified_appTop {Z X : Scheme.{u}} [IsAffine Z] [IsAffine X]
    (h : Z ⟶ X) [FormallyUnramified h] :
    letI : Algebra Γ(X, ⊤) Γ(Z, ⊤) := h.appTop.hom.toAlgebra
    Algebra.FormallyUnramified Γ(X, ⊤) Γ(Z, ⊤) := by
  have htop : h.appTop = h.appLE ⊤ ⊤ (by simp) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  let _ : Algebra Γ(X, ⊤) Γ(Z, ⊤) := h.appTop.hom.toAlgebra
  rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra, htop]
  exact h.formallyUnramified_appLE (isAffineOpen_top X) (isAffineOpen_top Z) (by simp)

/-- The affine case of the universal property, at the level of rings: for a formally unramified
morphism of affine schemes `h : Z ⟶ X` and a first-order thickening `j : T ⟶ T'` of affine
schemes over `X`, the global sections of the algebraic universal first-order thickening of
`Γ(Z, ⊤)` over `Γ(X, ⊤)` map uniquely to `Γ(T', ⊤)` compatibly with the given data. -/
private lemma existsUnique_algHomLift_of_isAffine
    {Z X T T' : Scheme.{u}} [IsAffine Z] [IsAffine X] [IsAffine T']
    (h : Z ⟶ X) [FormallyUnramified h]
    (j : T ⟶ T') (hj : IsFirstOrderThickening j)
    (a : T ⟶ Z) (b : T' ⟶ X) (hab : j ≫ b = a ≫ h) :
    let R := Γ(X, ⊤)
    let S := Γ(Z, ⊤)
    let B := Γ(T', ⊤)
    letI : Algebra R S := h.appTop.hom.toAlgebra
    letI : Algebra R B := b.appTop.hom.toAlgebra
    letI : Algebra.FormallyUnramified R S := formallyUnramified_appTop h
    let P := Algebra.FormallyUnramified.universalFirstOrderThickening R S
    ∃! f : P.Ring →ₐ[R] B,
      j.appTop.hom.comp f.toRingHom =
        a.appTop.hom.comp (IsScalarTower.toAlgHom R P.Ring S).toRingHom := by
  classical
  dsimp only
  let R := Γ(X, ⊤)
  let S := Γ(Z, ⊤)
  let B := Γ(T', ⊤)
  let A := Γ(T, ⊤)
  let : Algebra R S := h.appTop.hom.toAlgebra
  have : Algebra.FormallyUnramified R S := formallyUnramified_appTop h
  let P := Algebra.FormallyUnramified.universalFirstOrderThickening R S
  let hP := Algebra.FormallyUnramified.isUniversalFirstOrderThickening R S
  let : Algebra R B := b.appTop.hom.toAlgebra
  let : Algebra R A := (j ≫ b).appTop.hom.toAlgebra
  have hcomp {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W) :
      f.appTop.hom.comp g.appTop.hom = (f ≫ g).appTop.hom := by
    have hc := congrArg CommRingCat.Hom.hom (Scheme.Hom.comp_appTop f g)
    simpa only [CommRingCat.hom_comp] using hc.symm
  have hqb : j.appTop.hom.comp b.appTop.hom = (j ≫ b).appTop.hom := hcomp j b
  have habase : a.appTop.hom.comp h.appTop.hom = (j ≫ b).appTop.hom := by
    calc
      a.appTop.hom.comp h.appTop.hom = (a ≫ h).appTop.hom := hcomp a h
      _ = (j ≫ b).appTop.hom := congrArg (fun f : T ⟶ X => f.appTop.hom) hab.symm
  let q : B →ₐ[R] A := {
    toRingHom := j.appTop.hom
    commutes' := fun r => congrArg (fun f : R →+* A => f r) hqb
  }
  let a₀ : S →ₐ[R] A := {
    toRingHom := a.appTop.hom
    commutes' := fun r => congrArg (fun f : R →+* A => f r) habase
  }
  let : IsClosedImmersion j := hj.1
  have hq : Function.Surjective q := j.app_surjective ⊤ (isAffineOpen_top T')
  have hker : RingHom.ker q.toRingHom ^ 2 = ⊥ :=
    ker_appTop_sq_eq_bot j hj.2
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_algHom_lift P hP q hq hker a₀
  refine ⟨f, ?_, ?_⟩
  · have hf' := congrArg AlgHom.toRingHom hf
    simpa [q, a₀, AlgHom.comp_toRingHom] using hf'
  · intro g hg
    apply huniq g
    have hg' : q.comp g = a₀.comp (IsScalarTower.toAlgHom R P.Ring S) := by
      apply AlgHom.ext
      intro x
      have hx := congrArg (fun f : P.Ring →+* A => f x) hg
      simpa [q, a₀, AlgHom.comp_apply, IsScalarTower.toAlgHom] using hx
    exact hg'

/-- The affine case of the universal property, at the level of schemes: the spectrum of the
algebraic universal first-order thickening satisfies the unique lifting property against
first-order thickenings of *affine* schemes. Tag 04F3 restricted to affine test objects. -/
private lemma existsUnique_lift_of_isAffine
    {Z X T T' : Scheme.{u}} [IsAffine Z] [IsAffine X] [IsAffine T']
    (h : Z ⟶ X) [FormallyUnramified h]
    (j : T ⟶ T') (hj : IsFirstOrderThickening j)
    (a : T ⟶ Z) (b : T' ⟶ X) (hab : j ≫ b = a ≫ h) :
    let R := Γ(X, ⊤)
    let S := Γ(Z, ⊤)
    letI : Algebra R S := h.appTop.hom.toAlgebra
    letI : Algebra.FormallyUnramified R S := formallyUnramified_appTop h
    let P := Algebra.FormallyUnramified.universalFirstOrderThickening R S
    let q : CommRingCat.of P.Ring ⟶ S := CommRingCat.ofHom (algebraMap P.Ring S)
    let r : R ⟶ CommRingCat.of P.Ring := CommRingCat.ofHom (algebraMap R P.Ring)
    let i := Z.isoSpec.hom ≫ Spec.map q
    let p := Spec.map r ≫ X.isoSpec.inv
    ∃! f : T' ⟶ Spec (CommRingCat.of P.Ring),
      (j ≫ f = a ≫ i) ∧ (f ≫ p = b) := by
  classical
  dsimp only
  let R := Γ(X, ⊤)
  let S := Γ(Z, ⊤)
  let : Algebra R S := h.appTop.hom.toAlgebra
  have : Algebra.FormallyUnramified R S := formallyUnramified_appTop h
  let P := Algebra.FormallyUnramified.universalFirstOrderThickening R S
  let q : CommRingCat.of P.Ring ⟶ S := CommRingCat.ofHom (algebraMap P.Ring S)
  let r : R ⟶ CommRingCat.of P.Ring := CommRingCat.ofHom (algebraMap R P.Ring)
  let i := Z.isoSpec.hom ≫ Spec.map q
  let p := Spec.map r ≫ X.isoSpec.inv
  let : Algebra R (Γ(T', ⊤)) := b.appTop.hom.toAlgebra
  obtain ⟨lift, hlift, _⟩ := existsUnique_algHomLift_of_isAffine h j hj a b hab
  let φ : Γ(Spec (CommRingCat.of P.Ring), ⊤) →+* Γ(T', ⊤) :=
    lift.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).hom.hom
  let f : T' ⟶ Spec (CommRingCat.of P.Ring) := affineHomOfRingHom φ
  have hI : i.appTop.hom =
      (algebraMap P.Ring S).comp (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).hom.hom := by
    simpa [i, q] using
      isoSpec_hom_comp_specMap_appTop (Z := Z) q
  have hPbase : p.appTop.hom =
      (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv.hom.comp (algebraMap R P.Ring) := by
    simpa [p, r] using
      specMap_comp_isoSpec_inv_appTop (X := X) r
  have hfirst : (j ≫ f).appTop.hom = (a ≫ i).appTop.hom := by
    change j.appTop.hom.comp f.appTop.hom = a.appTop.hom.comp i.appTop.hom
    rw [affineHomOfRingHom_appTop, hI]
    have hlift' := congrArg (fun g : P.Ring →+* Γ(T, ⊤) =>
      g.comp (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).hom.hom) hlift
    simpa [φ, RingHom.comp_assoc] using hlift'
  have hRlift : lift.toRingHom.comp (algebraMap R P.Ring) = b.appTop.hom := by
    ext x
    exact lift.commutes' x
  have hsecond : (f ≫ p).appTop.hom = b.appTop.hom := by
    change f.appTop.hom.comp p.appTop.hom = b.appTop.hom
    rw [affineHomOfRingHom_appTop, hPbase]
    ext x
    change lift.toRingHom
      ((Scheme.ΓSpecIso (CommRingCat.of P.Ring)).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv.hom (algebraMap R P.Ring x))) =
      b.appTop.hom x
    have hσ : (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).hom.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv.hom = RingHom.id P.Ring := by
      have hs := congrArg CommRingCat.Hom.hom
        (Iso.inv_hom_id (Scheme.ΓSpecIso (CommRingCat.of P.Ring)))
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_id] using hs
    change lift.toRingHom
      ((Scheme.ΓSpecIso (CommRingCat.of P.Ring)).hom.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv.hom
        (algebraMap R P.Ring x)) = b.appTop.hom x
    rw [hσ]
    exact lift.commutes' x
  have hPformal : Algebra.FormallyUnramified R P.Ring :=
    formallyUnramified_ring_of_isUniversal P
      (Algebra.FormallyUnramified.isUniversalFirstOrderThickening R S)
  have hringformal : r.hom.FormallyUnramified := by
    change (algebraMap R P.Ring).FormallyUnramified
    rw [RingHom.formallyUnramified_algebraMap]
    exact hPformal
  let : FormallyUnramified (Spec.map r) := by
    rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact hringformal
  let : FormallyUnramified p :=
    MorphismProperty.comp_mem (@FormallyUnramified) (Spec.map r) X.isoSpec.inv
      inferInstance inferInstance
  have hf : j ≫ f = a ≫ i ∧ f ≫ p = b :=
    ⟨hom_ext_of_appTop_eq _ _ hfirst, hom_ext_of_appTop_eq _ _ hsecond⟩
  exact ⟨f, hf, fun g hg => lift_unique_of_formallyUnramified j hj i p a b g f hg hf⟩

/-- A first-order thickening of `Z` over `X` whose structure morphism is formally unramified,
without the universal property. This is the output of the affine construction, from which
both the universal property and the gluing data are then derived. -/
structure FirstOrderThickeningSkeleton {Z X : Scheme.{u}} (h : Z ⟶ X) where
  /-- The ambient scheme of the thickening. -/
  ambient : Scheme.{u}
  /-- The inclusion of the original scheme. -/
  inclusion : Z ⟶ ambient
  /-- The structure morphism to the base. -/
  toBase : ambient ⟶ X
  /-- The inclusion is a closed immersion with square-zero defining ideal sheaf. -/
  isFirstOrderThickening : IsFirstOrderThickening inclusion
  /-- The thickening is over the specified base. -/
  inclusion_toBase : inclusion ≫ toBase = h
  /-- The structure morphism is formally unramified. -/
  formallyUnramified_toBase : FormallyUnramified toBase

/-- The first-order thickening of a formally unramified morphism of affine schemes, obtained by
taking the spectrum of the algebraic universal first-order thickening
(`Algebra.FormallyUnramified.universalFirstOrderThickening`). -/
noncomputable def affineThickeningSkeleton
    {Z X : Scheme.{u}} [IsAffine Z] [IsAffine X] (h : Z ⟶ X)
    [FormallyUnramified h] : FirstOrderThickeningSkeleton h := by
  let R := Γ(X, ⊤)
  let S := Γ(Z, ⊤)
  letI : Algebra R S := h.appTop.hom.toAlgebra
  have htop : h.appTop = h.appLE ⊤ ⊤ (by simp) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  have hFU : Algebra.FormallyUnramified R S := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    rw [htop]
    exact h.formallyUnramified_appLE (isAffineOpen_top X) (isAffineOpen_top Z) (by simp)
  letI : Algebra.FormallyUnramified R S := hFU
  let P := Algebra.FormallyUnramified.universalFirstOrderThickening R S
  let hP := Algebra.FormallyUnramified.isUniversalFirstOrderThickening R S
  let q : CommRingCat.of P.Ring ⟶ CommRingCat.of S :=
    CommRingCat.ofHom (algebraMap P.Ring S)
  let r : CommRingCat.of R ⟶ CommRingCat.of P.Ring :=
    CommRingCat.ofHom (algebraMap R P.Ring)
  have hPformal : Algebra.FormallyUnramified R P.Ring :=
    formallyUnramified_ring_of_isUniversal P
      (Algebra.FormallyUnramified.isUniversalFirstOrderThickening R S)
  have hringformal : r.hom.FormallyUnramified := by
    change (algebraMap R P.Ring).FormallyUnramified
    rw [RingHom.formallyUnramified_algebraMap]
    exact hPformal
  letI : FormallyUnramified (Spec.map r) := by
    rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact hringformal
  letI : FormallyUnramified (Spec.map r ≫ X.isoSpec.inv) :=
    MorphismProperty.comp_mem (@FormallyUnramified) (Spec.map r) X.isoSpec.inv
      inferInstance inferInstance
  let i₀ := Spec.map q
  let p₀ := Spec.map r
  haveI : IsClosedImmersion i₀ :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective q P.algebraMap_surjective
  refine ⟨Spec (CommRingCat.of P.Ring), Z.isoSpec.hom ≫ i₀, p₀ ≫ X.isoSpec.inv,
    ?_, ?_, ?_⟩
  · have hfirst := isFirstOrderThickening_specMap q P.algebraMap_surjective
      hP.ker_sq_eq_bot
    refine ⟨by infer_instance, ?_⟩
    rw [Scheme.Hom.ker_comp_of_isIso]
    exact hfirst.2
  · have hrq : r ≫ q = CommRingCat.ofHom h.appTop.hom := by
      ext x
      simp [r, q, ← IsScalarTower.algebraMap_apply, RingHom.algebraMap_toAlgebra]
    have hmodel : affineHomOfRingHom h.appTop.hom = h := by
      apply hom_ext_of_appTop_eq
      simp [affineHomOfRingHom_appTop]
    change Z.isoSpec.hom ≫ Spec.map q ≫ Spec.map r ≫ X.isoSpec.inv = h
    rw [← Category.assoc (Spec.map q) (Spec.map r) X.isoSpec.inv]
    rw [← Spec.map_comp r q, hrq]
    exact hmodel
  · exact ‹FormallyUnramified (Spec.map r ≫ X.isoSpec.inv)›

/-- `affineThickeningSkeleton` has the unique lifting property against first-order thickenings of
affine schemes. -/
lemma affineThickeningSkeleton_existsUnique_lift_of_isAffine
    {Z X T T' : Scheme.{u}} [IsAffine Z] [IsAffine X] [IsAffine T']
    (h : Z ⟶ X) [FormallyUnramified h]
    (j : T ⟶ T') (hj : IsFirstOrderThickening j)
    (a : T ⟶ Z) (b : T' ⟶ X) (hab : j ≫ b = a ≫ h) :
    ∃! f : T' ⟶ (affineThickeningSkeleton h).ambient,
      (j ≫ f = a ≫ (affineThickeningSkeleton h).inclusion) ∧
      (f ≫ (affineThickeningSkeleton h).toBase = b) := by
  simpa [affineThickeningSkeleton] using
    existsUnique_lift_of_isAffine h j hj a b hab

/-- The inverse image of a square-zero ideal sheaf along an open immersion is square-zero. -/
public lemma comap_sq_eq_bot_of_isOpenImmersion
    {Y Z : Scheme.{u}} (J : Scheme.IdealSheafData Y) (v : Z ⟶ Y)
    [IsOpenImmersion v] (hJ : J ^ 2 = ⊥) : (J.comap v) ^ 2 = ⊥ := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.le_def]
    intro U
    change ((J.comap v).ideal U) ^ 2 ≤ (⊥ : Scheme.IdealSheafData Z).ideal U
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    let V : Y.affineOpens := ⟨v ''ᵁ U, U.2.image_of_isOpenImmersion v⟩
    exact (comap_sq_eq_bot_of_injective
      (ConcreteCategory.bijective_of_isIso (v.appIso U).inv).1 (ideal_sq_eq_bot hJ V)).le
  · exact bot_le

/-- The restriction of a first-order thickening to an open subscheme of the ambient scheme is
again a first-order thickening. -/
private lemma isFirstOrderThickening_morphismRestrict {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    (hi : IsFirstOrderThickening i) (U : Z'.Opens) :
    IsFirstOrderThickening (i ∣_ U) := by
  let : IsClosedImmersion (i ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict i U).flip hi.1
  refine ⟨inferInstance, ?_⟩
  let : IsClosedImmersion i := hi.1
  apply Scheme.IdealSheafData.ext
  funext W
  let A : Z'.affineOpens := ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion U.ι⟩
  have hker := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i (i ∣_ U)
    (i ⁻¹ᵁ U).ι U.ι (isPullback_morphismRestrict i U) W
  change ((i ∣_ U).ker.ideal W) ^ 2 = ⊥
  rw [hker]
  exact comap_sq_eq_bot_of_injective
    (ConcreteCategory.bijective_of_isIso (U.ι.appIso W).inv).1 (ideal_sq_eq_bot hi.2 A)

/-- If the closed subscheme of a first-order thickening maps into an open subscheme `U`, then the
whole thickening does, because the two have the same underlying space. -/
lemma exists_factorization_of_isFirstOrderThickening
    {T T' X : Scheme.{u}} (j : T ⟶ T')
    (hj : IsFirstOrderThickening j) (U : X.Opens)
    (a : T ⟶ U.toScheme) (b : T' ⟶ X)
    (hab : a ≫ U.ι = j ≫ b) : ∃ bU : T' ⟶ U.toScheme, bU ≫ U.ι = b := by
  have hrange : Set.range b.base ⊆ Set.range U.ι.base := by
    rintro y ⟨x, rfl⟩
    obtain ⟨t, ht⟩ := hj.isThickening.2 x
    refine ⟨a.base t, ?_⟩
    have heq := congrArg (fun f : T ⟶ X => f.base t) hab
    change U.ι.base (a.base t) = b.base (j.base t) at heq
    rw [← ht]
    exact heq
  let bU := IsOpenImmersion.lift U.ι b hrange
  exact ⟨bU, by simp [bU]⟩

/-- The homeomorphism of underlying spaces given by a thickening. -/
noncomputable def thickeningHomeomorph {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    (hi : IsThickening i) : Z ≃ₜ Z' := by
  letI : IsClosedImmersion i := hi.1
  exact (Equiv.ofBijective i.base ⟨i.isClosedEmbedding.injective, hi.2⟩)
    |>.toHomeomorphOfContinuousClosed i.continuous i.isClosedEmbedding.isClosedMap

/-- The open subscheme of the ambient scheme of a thickening corresponding to an open subscheme
of the closed subscheme. -/
noncomputable def thickeningOpenImage {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    (hi : IsThickening i) (V : Z.Opens) : Z'.Opens := by
  let e := thickeningHomeomorph i hi
  exact ⟨e '' V, e.isOpenMap _ V.2⟩

/-- `thickeningOpenImage i hi V` pulls back to `V` along the inclusion. -/
lemma preimage_thickeningOpenImage {Z Z' : Scheme.{u}} (i : Z ⟶ Z')
    (hi : IsThickening i) (V : Z.Opens) :
    i ⁻¹ᵁ thickeningOpenImage i hi V = V := by
  let e := thickeningHomeomorph i hi
  ext x
  change e x ∈ e '' V ↔ x ∈ V
  simp

section Restriction

variable {Z X : Scheme.{u}} {h : Z ⟶ X}

/-- **Stacks Project, Tag 04FA, the second assertion.** Let `i : Z ⟶ Z'` with structure morphism
`p : Z' ⟶ X` be a universal first-order thickening of `h : Z ⟶ X` over `X`. Let `U ⊆ X` and
`V ⊆ Z` be opens with `h(V) ⊆ U`, and let `W ⊆ Z'` be an open with `Z ∩ W = V` and `p(W) ⊆ U`.
Then the restrictions `i.resLE W V : V ⟶ W` and `p.resLE U W : W ⟶ U` are a universal
first-order thickening of `h|_V : V ⟶ U` over `U`.

That `V ⟶ W` is a first-order thickening is the statement that the restriction of a first-order
thickening to an open subscheme of the ambient scheme is again one. The lifting property is the
lifting property of `Z'` followed by the observation that the resulting lift `T' ⟶ Z'` factors
through the open `W`: the points of `T'` are the points of `T`, which land in `V`, hence in
`W`. -/
@[stacks 04FA "the universal first-order thickening of an open is the corresponding open"]
theorem isUniversalFirstOrderThickening_resLE {Z' : Scheme.{u}} {i : Z ⟶ Z'} {p : Z' ⟶ X}
    (hi : IsUniversalFirstOrderThickening h i p) {U : X.Opens} {V : Z.Opens} {W : Z'.Opens}
    (hWV : i ⁻¹ᵁ W = V) (hWU : W ≤ p ⁻¹ᵁ U) (hVU : V ≤ h ⁻¹ᵁ U) :
    IsUniversalFirstOrderThickening (h.resLE U V hVU) (i.resLE W V hWV.ge) (p.resLE U W hWU) := by
  have hiComp : i.resLE W V hWV.ge ≫ W.ι = V.ι ≫ i := Scheme.Hom.resLE_comp_ι i hWV.ge
  have hpComp : p.resLE U W hWU ≫ U.ι = W.ι ≫ p := Scheme.Hom.resLE_comp_ι p hWU
  refine ⟨?_, ?_, ?_⟩
  · have hbase : IsFirstOrderThickening (i.resLE W (i ⁻¹ᵁ W) le_rfl) := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact isFirstOrderThickening_morphismRestrict i hi.isFirstOrderThickening W
    exact (Scheme.Hom.resLE_congr i le_rfl rfl hWV
      (fun _ _ f => IsFirstOrderThickening f)).mp hbase
  · refine (cancel_mono U.ι).mp ?_
    rw [Category.assoc, hpComp, ← Category.assoc, hiComp, Category.assoc, hi.inclusion_toBase,
      Scheme.Hom.resLE_comp_ι]
  · intro T T' j hj a b hab
    have hab' : j ≫ b ≫ U.ι = (a ≫ V.ι) ≫ h := by
      rw [← Category.assoc, hab, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    obtain ⟨f, hf, hfu⟩ := hi.existsUnique_lift j hj (a ≫ V.ι) (b ≫ U.ι) hab'
    obtain ⟨fW, hfW⟩ := exists_factorization_of_isFirstOrderThickening j hj W
      (a ≫ i.resLE W V hWV.ge) f (by rw [Category.assoc, hiComp, ← Category.assoc, hf.1])
    refine ⟨fW, ⟨?_, ?_⟩, ?_⟩
    · refine (cancel_mono W.ι).mp ?_
      rw [Category.assoc, hfW, Category.assoc, hiComp, ← Category.assoc, hf.1, Category.assoc]
    · refine (cancel_mono U.ι).mp ?_
      rw [Category.assoc, hpComp, ← Category.assoc, hfW, hf.2]
    · intro g hg
      refine (cancel_mono W.ι).mp ?_
      rw [hfW]
      refine hfu (g ≫ W.ι) ⟨?_, ?_⟩
      · rw [← Category.assoc, hg.1, Category.assoc, hiComp, Category.assoc]
      · rw [Category.assoc, ← hpComp, ← Category.assoc, hg.2]

/-- `Stacks.Thickenings.isUniversalFirstOrderThickening_resLE` with `U = ⊤`, read over `X` itself
rather than over `(⊤ : X.Opens)`: the two differ by the isomorphism
`AlgebraicGeometry.Scheme.topIso`, along which the structure morphism `W ⟶ (⊤ : X.Opens)` becomes
the composite `W ⟶ Z' ⟶ X`. This is the form in which the gluing construction below uses the
restriction, since there the base is all of `X`. -/
lemma isUniversalFirstOrderThickening_resLE_top {Z' : Scheme.{u}} {i : Z ⟶ Z'}
    {p : Z' ⟶ X} (hi : IsUniversalFirstOrderThickening h i p) {V : Z.Opens} {W : Z'.Opens}
    (hWV : i ⁻¹ᵁ W = V) :
    IsUniversalFirstOrderThickening (V.ι ≫ h) (i.resLE W V hWV.ge) (W.ι ≫ p) := by
  have hres := isUniversalFirstOrderThickening_resLE hi hWV (U := ⊤) (by simp) (by simp)
  have hh : h.resLE ⊤ V (by simp) ≫ X.topIso.hom = V.ι ≫ h :=
    Scheme.Hom.resLE_comp_ι h (by simp)
  have hp : p.resLE ⊤ W (by simp) ≫ X.topIso.hom = W.ι ≫ p :=
    Scheme.Hom.resLE_comp_ι p (by simp)
  refine ⟨hres.isFirstOrderThickening, ?_, ?_⟩
  · rw [← hh, ← hp, ← Category.assoc, hres.inclusion_toBase]
  · intro T T' j hj a b hab
    obtain ⟨f, hf, hu⟩ := hres.existsUnique_lift j hj a (b ≫ X.topIso.inv) (by
      rw [← Category.assoc, hab, ← hh, Category.assoc, Category.assoc, X.topIso.hom_inv_id,
        Category.comp_id])
    refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
    · rw [← hp, ← Category.assoc, hf.2, Category.assoc, X.topIso.inv_hom_id, Category.comp_id]
    · intro g hg
      refine hu g ⟨hg.1, ?_⟩
      rw [← hg.2, ← hp, Category.assoc, Category.assoc, X.topIso.hom_inv_id, Category.comp_id]

end Restriction

end Stacks.Thickenings

end
