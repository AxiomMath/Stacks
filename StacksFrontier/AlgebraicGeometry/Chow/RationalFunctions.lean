module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import StacksFrontier.AlgebraicGeometry.GenericPointDecomposition.RationalFunctions
public import StacksCore.Tactic.StacksAttribute

/-!
# The ring of rational functions on a scheme

A rational function on a scheme `X` is a rational map `X ⤏ 𝔸¹_ℤ` to the affine line over the
integers, that is, an equivalence class of morphisms `U ⟶ 𝔸¹_ℤ` defined on a dense open
`U ⊆ X`, two such being identified when they agree on a smaller dense open. Since a morphism
`U ⟶ 𝔸¹_ℤ` is the same thing as a section of `𝒪_X` over `U`, these are exactly the "rational
functions" `R(X)` of Stacks 01RU, and the pointwise ring operations on sections over dense
opens make `R(X)` a commutative ring: given two rational functions, restrict representatives to
the intersection of their domains — still dense, because the domains are dense *open* — add or
multiply the corresponding sections there, and read the result back as a morphism to the affine
line.

The ring structure is characterised by the requirement that, for every dense open `U`, the map
sending a section `s ∈ Γ(X, U)` to the rational function it represents is a ring homomorphism;
that characterisation is `Stacks.Chow.rationalFunctionsRing`, the content of Stacks 01RU.

## Main definitions

* `Stacks.Chow.affineLine` — the affine line `𝔸¹` over `Spec ℤ`, with its coordinate
  `Stacks.Chow.coordinate`.
* `Stacks.Chow.rationalFunctions` — the type `R(X)` of rational maps `X ⤏ 𝔸¹_ℤ`.
* `Stacks.Chow.DenseOpen` — a dense open subset of a scheme.
* `Stacks.Chow.ofSection` — the rational function represented by a section on a dense open.
* `Stacks.Chow.ofSectionRingHom` — the same map, as a ring homomorphism.

## Main results

* `Stacks.Chow.rationalFunctionsRing` — there is a commutative ring structure on `R(X)` for
  which every map `Γ(X, U) → R(X)` from the sections on a dense open is a ring homomorphism
  (Stacks 01RU).
* `Stacks.Chow.ofSectionRingHom_apply` — that ring homomorphism is `ofSection`.

## Implementation notes

The carrier is Mathlib's `AlgebraicGeometry.Scheme.RationalMap`, the quotient of partial maps by
agreement on a dense open, rather than a separately constructed direct limit. The ring
operations are therefore defined on representatives: `partialAdd` and `partialMul` restrict two
partial maps to the intersection of their domains and combine the pulled-back coordinate
sections, and the ring axioms are checked by exhibiting a common dense open on which the two
sides agree. Morphisms to the affine line are compared with `AffineSpace.hom_ext`, which reduces
an equality of morphisms to `𝔸(n; S)` to an equality over `S` together with equality of the
pullbacks of the coordinate functions; here `n` is a one-element type and the base is
`Spec ℤ`, whose terminality (`AlgebraicGeometry.specULiftZIsTerminal`) discharges the first
condition.

The commutative ring instance on `R(X)` is the one produced by `rationalFunctionsRing`, so that
the tagged statement, and not an auxiliary construction, is what the instance records.

## References

* [Stacks Project, Tag 01RU](https://stacks.math.columbia.edu/tag/01RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.AlgebraicGeometry.GenericPointDecomposition (lineHom_appTop_coordinate)

open Stacks.AlgebraicGeometry.GenericPointDecomposition (affineLine coordinate lineHom)

/-- A rational function on `X` is a rational map from `X` to the affine line. -/
abbrev rationalFunctions (X : Scheme.{u}) : Type u :=
  X.RationalMap (affineLine : Scheme.{u})

/-- A dense open subset of a scheme, on which a rational function can be represented. -/
abbrev DenseOpen (X : Scheme.{u}) :=
  { U : X.Opens // Dense (U : Set X) }

/-- The rational function represented by a section on a dense open. -/
def ofSection (X : Scheme.{u}) (U : DenseOpen X) (s : Γ(X, U.1)) : rationalFunctions X :=
  (⟨U.1, U.2,
    AffineSpace.homOfVector (specULiftZIsTerminal.from U.1.toScheme)
      (fun _ : ULift.{u} (Fin 1) ↦ U.1.topIso.inv s)⟩ : X.PartialMap affineLine).toRationalMap

/-- The partial map represented by a section on a dense open. -/
private abbrev sectionPartial (X : Scheme.{u}) (U : DenseOpen X) (s : Γ(X, U.1)) :
    X.PartialMap affineLine where
  domain := U.1
  dense_domain := U.2
  hom := lineHom U.1.toScheme (U.1.topIso.inv s)

/-- The partial map, defined everywhere, with a prescribed global section as its coordinate. -/
private abbrev partialConst (X : Scheme.{u}) (c : Γ(X, ⊤)) : X.PartialMap affineLine where
  domain := ⊤
  dense_domain := dense_univ
  hom := lineHom (⊤ : X.Opens).toScheme ((⊤ : X.Opens).topIso.inv c)

private lemma homOfLE_appTop_comp (X : Scheme.{u}) {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (s : Γ(W.toScheme, ⊤)) :
    (X.homOfLE hUV).appTop ((X.homOfLE hVW).appTop s) =
      (X.homOfLE (hUV.trans hVW)).appTop s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  rw [X.homOfLE_homOfLE]

/-- Two partial maps to the affine line are equivalent as soon as their coordinate sections agree
on a dense open contained in both domains. -/
private lemma equiv_of_coordinate_eq (X : Scheme.{u}) (f g : X.PartialMap affineLine)
    (W : X.Opens) (hW : Dense (W : Set X)) (hWf : W ≤ f.domain) (hWg : W ≤ g.domain)
    (h : (X.homOfLE hWf).appTop (f.hom.appTop coordinate) =
      (X.homOfLE hWg).appTop (g.hom.appTop coordinate)) : f.equiv g := by
  refine ⟨W, hW, hWf, hWg, AffineSpace.hom_ext (specULiftZIsTerminal.hom_ext _ _) fun i ↦ ?_⟩
  obtain rfl : i = ULift.up 0 := Subsingleton.elim _ _
  exact h

/-- The sum of two partial maps to the affine line, on the intersection of their domains. -/
private abbrev partialAdd (X : Scheme.{u}) (f g : X.PartialMap affineLine) :
    X.PartialMap affineLine where
  domain := f.domain ⊓ g.domain
  dense_domain := f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2
  hom := lineHom (f.domain ⊓ g.domain).toScheme
    (((X.homOfLE inf_le_left).appTop (f.hom.appTop coordinate)) +
      ((X.homOfLE inf_le_right).appTop (g.hom.appTop coordinate)))

/-- The product of two partial maps to the affine line, on the intersection of their domains. -/
private abbrev partialMul (X : Scheme.{u}) (f g : X.PartialMap affineLine) :
    X.PartialMap affineLine where
  domain := f.domain ⊓ g.domain
  dense_domain := f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2
  hom := lineHom (f.domain ⊓ g.domain).toScheme
    (((X.homOfLE inf_le_left).appTop (f.hom.appTop coordinate)) *
      ((X.homOfLE inf_le_right).appTop (g.hom.appTop coordinate)))

/-- The negation of a partial map to the affine line. -/
private abbrev partialNeg (X : Scheme.{u}) (f : X.PartialMap affineLine) :
    X.PartialMap affineLine where
  domain := f.domain
  dense_domain := f.dense_domain
  hom := lineHom f.domain.toScheme (-f.hom.appTop coordinate)

private lemma sectionPartial_add (X : Scheme.{u}) (U : DenseOpen X) (s t : Γ(X, U.1)) :
    (partialAdd X (sectionPartial X U s) (sectionPartial X U t)).equiv
      (sectionPartial X U (s + t)) :=
  equiv_of_coordinate_eq X _ _ (U.1 ⊓ U.1) (U.2.inter_of_isOpen_left U.2 U.1.2) le_rfl
    inf_le_left (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_add])

private lemma sectionPartial_mul (X : Scheme.{u}) (U : DenseOpen X) (s t : Γ(X, U.1)) :
    (partialMul X (sectionPartial X U s) (sectionPartial X U t)).equiv
      (sectionPartial X U (s * t)) :=
  equiv_of_coordinate_eq X _ _ (U.1 ⊓ U.1) (U.2.inter_of_isOpen_left U.2 U.1.2) le_rfl
    inf_le_left (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_mul])

private lemma sectionPartial_zero (X : Scheme.{u}) (U : DenseOpen X) :
    (sectionPartial X U (0 : Γ(X, U.1))).equiv (partialConst X 0) :=
  equiv_of_coordinate_eq X _ _ U.1 U.2 le_rfl le_top (by simp)

private lemma sectionPartial_one (X : Scheme.{u}) (U : DenseOpen X) :
    (sectionPartial X U (1 : Γ(X, U.1))).equiv (partialConst X 1) :=
  equiv_of_coordinate_eq X _ _ U.1 U.2 le_rfl le_top (by simp)


/-- Two partial maps to the affine line that agree after restriction to a dense open `W` have
the same coordinate section after restriction to any open `V ⊆ W`. -/
private lemma partialMap_coordinate_eq_of_restrict_eq (X : Scheme.{u})
    (f g : X.PartialMap affineLine) (W V : X.Opens)
    (hW : Dense (W : Set X)) (_hV : Dense (V : Set X))
    (hWf : W ≤ f.domain) (hWg : W ≤ g.domain)
    (hVf : V ≤ f.domain) (hVg : V ≤ g.domain) (hVW : V ≤ W)
    (e : (f.restrict W hW hWf).hom = (g.restrict W hW hWg).hom) :
    (X.homOfLE hVf).appTop (f.hom.appTop coordinate) =
      (X.homOfLE hVg).appTop (g.hom.appTop coordinate) := by
  have eV : X.homOfLE hVf ≫ f.hom = X.homOfLE hVg ≫ g.hom := by
    calc
      _ = X.homOfLE hVW ≫ (f.restrict W hW hWf).hom := by
        rw [Scheme.PartialMap.restrict_hom, ← X.homOfLE_homOfLE (U := V) hVW hWf]
        simp only [Category.assoc]
      _ = X.homOfLE hVW ≫ (g.restrict W hW hWg).hom := congrArg (X.homOfLE hVW ≫ ·) e
      _ = _ := by
        rw [Scheme.PartialMap.restrict_hom, ← X.homOfLE_homOfLE (U := V) hVW hWg]
        simp only [Category.assoc]
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    congrArg (fun k => k.appTop coordinate) eV

private lemma partialAdd_compat (X : Scheme.{u}) {f f' g g' : X.PartialMap affineLine}
    (hf : f.equiv f') (hg : g.equiv g') :
    (partialAdd X f g).equiv (partialAdd X f' g') := by
  obtain ⟨W₁, hW₁, hW₁f, hW₁f', e₁⟩ := hf
  obtain ⟨W₂, hW₂, hW₂g, hW₂g', e₂⟩ := hg
  have hV : Dense ((W₁ ⊓ W₂ : X.Opens) : Set X) := hW₁.inter_of_isOpen_left hW₂ W₁.2
  have e₁' := partialMap_coordinate_eq_of_restrict_eq X f f' W₁ _ hW₁ hV
    hW₁f hW₁f' (inf_le_left.trans hW₁f) (inf_le_left.trans hW₁f') inf_le_left e₁
  have e₂' := partialMap_coordinate_eq_of_restrict_eq X g g' W₂ _ hW₂ hV hW₂g hW₂g'
    (inf_le_right.trans hW₂g) (inf_le_right.trans hW₂g') inf_le_right e₂
  refine equiv_of_coordinate_eq X _ _ _ hV (le_inf (inf_le_left.trans hW₁f)
    (inf_le_right.trans hW₂g)) (le_inf (inf_le_left.trans hW₁f') (inf_le_right.trans hW₂g')) ?_
  simp only [lineHom_appTop_coordinate, map_add, homOfLE_appTop_comp, e₁', e₂']

private lemma partialMul_compat (X : Scheme.{u}) {f f' g g' : X.PartialMap affineLine}
    (hf : f.equiv f') (hg : g.equiv g') :
    (partialMul X f g).equiv (partialMul X f' g') := by
  obtain ⟨W₁, hW₁, hW₁f, hW₁f', e₁⟩ := hf
  obtain ⟨W₂, hW₂, hW₂g, hW₂g', e₂⟩ := hg
  have hV : Dense ((W₁ ⊓ W₂ : X.Opens) : Set X) := hW₁.inter_of_isOpen_left hW₂ W₁.2
  have e₁' := partialMap_coordinate_eq_of_restrict_eq X f f' W₁ _ hW₁ hV
    hW₁f hW₁f' (inf_le_left.trans hW₁f) (inf_le_left.trans hW₁f') inf_le_left e₁
  have e₂' := partialMap_coordinate_eq_of_restrict_eq X g g' W₂ _ hW₂ hV hW₂g hW₂g'
    (inf_le_right.trans hW₂g) (inf_le_right.trans hW₂g') inf_le_right e₂
  refine equiv_of_coordinate_eq X _ _ _ hV (le_inf (inf_le_left.trans hW₁f)
    (inf_le_right.trans hW₂g)) (le_inf (inf_le_left.trans hW₁f') (inf_le_right.trans hW₂g')) ?_
  simp only [lineHom_appTop_coordinate, map_mul, homOfLE_appTop_comp, e₁', e₂']

private lemma partialNeg_compat (X : Scheme.{u}) {f g : X.PartialMap affineLine}
    (h : f.equiv g) : (partialNeg X f).equiv (partialNeg X g) := by
  obtain ⟨W, hW, hWf, hWg, e⟩ := h
  have ec := partialMap_coordinate_eq_of_restrict_eq X f g W W hW hW hWf hWg hWf hWg le_rfl e
  exact equiv_of_coordinate_eq X _ _ W hW hWf hWg
    (by simp only [lineHom_appTop_coordinate, map_neg, ec])

private lemma partialAdd_assoc (X : Scheme.{u}) (f g h : X.PartialMap affineLine) :
    (partialAdd X (partialAdd X f g) h).equiv (partialAdd X f (partialAdd X g h)) :=
  equiv_of_coordinate_eq X _ _ ((f.domain ⊓ g.domain) ⊓ h.domain)
    ((f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2).inter_of_isOpen_left
      h.dense_domain (f.domain ⊓ g.domain).2) le_rfl
    (le_inf (inf_le_left.trans inf_le_left)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_add]; ring)

private lemma partialAdd_comm (X : Scheme.{u}) (f g : X.PartialMap affineLine) :
    (partialAdd X f g).equiv (partialAdd X g f) :=
  equiv_of_coordinate_eq X _ _ (f.domain ⊓ g.domain)
    (f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2) le_rfl
    (le_inf inf_le_right inf_le_left)
    (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_add]; rw [add_comm])

private lemma partialAdd_zero_left (X : Scheme.{u}) (f : X.PartialMap affineLine) :
    (partialAdd X (partialConst X 0) f).equiv f :=
  equiv_of_coordinate_eq X _ _ f.domain f.dense_domain (le_inf le_top le_rfl) le_rfl
    (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_add]; simp)

private lemma partialAdd_zero_right (X : Scheme.{u}) (f : X.PartialMap affineLine) :
    (partialAdd X f (partialConst X 0)).equiv f :=
  (partialAdd_comm X f (partialConst X 0)).trans (partialAdd_zero_left X f)

private lemma partialNeg_add_cancel (X : Scheme.{u}) (f : X.PartialMap affineLine) :
    (partialAdd X (partialNeg X f) f).equiv (partialConst X 0) :=
  equiv_of_coordinate_eq X _ _ f.domain f.dense_domain (le_inf le_rfl le_rfl) le_top
    (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_add]; simp)

private lemma partialMul_one_left (X : Scheme.{u}) (f : X.PartialMap affineLine) :
    (partialMul X (partialConst X 1) f).equiv f :=
  equiv_of_coordinate_eq X _ _ f.domain f.dense_domain (le_inf le_top le_rfl) le_rfl
    (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_mul]; simp)

private lemma partialMul_zero_left (X : Scheme.{u}) (f : X.PartialMap affineLine) :
    (partialMul X (partialConst X 0) f).equiv (partialConst X 0) :=
  equiv_of_coordinate_eq X _ _ f.domain f.dense_domain (le_inf le_top le_rfl) le_top
    (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_mul]; simp)

private lemma partialMul_assoc (X : Scheme.{u}) (f g h : X.PartialMap affineLine) :
    (partialMul X (partialMul X f g) h).equiv (partialMul X f (partialMul X g h)) :=
  equiv_of_coordinate_eq X _ _ ((f.domain ⊓ g.domain) ⊓ h.domain)
    ((f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2).inter_of_isOpen_left
      h.dense_domain (f.domain ⊓ g.domain).2) le_rfl
    (le_inf (inf_le_left.trans inf_le_left)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_mul]; ring)

private lemma partialMul_comm (X : Scheme.{u}) (f g : X.PartialMap affineLine) :
    (partialMul X f g).equiv (partialMul X g f) :=
  equiv_of_coordinate_eq X _ _ (f.domain ⊓ g.domain)
    (f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2) le_rfl
    (le_inf inf_le_right inf_le_left)
    (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_mul]; rw [mul_comm])

private lemma partialMul_one_right (X : Scheme.{u}) (f : X.PartialMap affineLine) :
    (partialMul X f (partialConst X 1)).equiv f :=
  (partialMul_comm X f (partialConst X 1)).trans (partialMul_one_left X f)

private lemma partialMul_zero_right (X : Scheme.{u}) (f : X.PartialMap affineLine) :
    (partialMul X f (partialConst X 0)).equiv (partialConst X 0) :=
  (partialMul_comm X f (partialConst X 0)).trans (partialMul_zero_left X f)

private lemma partialAdd_mul_distrib (X : Scheme.{u}) (f g h : X.PartialMap affineLine) :
    (partialMul X (partialAdd X f g) h).equiv
      (partialAdd X (partialMul X f h) (partialMul X g h)) :=
  equiv_of_coordinate_eq X _ _ ((f.domain ⊓ g.domain) ⊓ h.domain)
    ((f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2).inter_of_isOpen_left
      h.dense_domain (f.domain ⊓ g.domain).2) le_rfl
    (le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    (by simp only [lineHom_appTop_coordinate, homOfLE_appTop_comp, map_add, map_mul]; ring)


/-- Addition of rational functions, induced by `partialAdd` on representatives. -/
private def rationalAdd (X : Scheme.{u}) :
    rationalFunctions X → rationalFunctions X → rationalFunctions X :=
  Quotient.map₂ (partialAdd X) (fun _ _ hf _ _ hg ↦ partialAdd_compat X hf hg)

/-- Multiplication of rational functions, induced by `partialMul` on representatives. -/
private def rationalMul (X : Scheme.{u}) :
    rationalFunctions X → rationalFunctions X → rationalFunctions X :=
  Quotient.map₂ (partialMul X) (fun _ _ hf _ _ hg ↦ partialMul_compat X hf hg)

/-- Negation of rational functions, induced by `partialNeg` on representatives. -/
private def rationalNeg (X : Scheme.{u}) : rationalFunctions X → rationalFunctions X :=
  Quotient.map (partialNeg X) (fun _ _ h ↦ partialNeg_compat X h)

/-- The zero rational function. -/
private def rationalZero (X : Scheme.{u}) : rationalFunctions X :=
  (partialConst X (0 : Γ(X, ⊤))).toRationalMap

/-- The unit rational function. -/
private def rationalOne (X : Scheme.{u}) : rationalFunctions X :=
  (partialConst X (1 : Γ(X, ⊤))).toRationalMap

@[simp] private lemma rationalAdd_toRationalMap (X : Scheme.{u})
    (f g : X.PartialMap affineLine) :
    rationalAdd X f.toRationalMap g.toRationalMap = (partialAdd X f g).toRationalMap :=
  Quotient.map₂_mk (partialAdd X) (fun _ _ hf _ _ hg ↦ partialAdd_compat X hf hg) f g

@[simp] private lemma rationalMul_toRationalMap (X : Scheme.{u})
    (f g : X.PartialMap affineLine) :
    rationalMul X f.toRationalMap g.toRationalMap = (partialMul X f g).toRationalMap :=
  Quotient.map₂_mk (partialMul X) (fun _ _ hf _ _ hg ↦ partialMul_compat X hf hg) f g

@[simp] private lemma rationalNeg_toRationalMap (X : Scheme.{u})
    (f : X.PartialMap affineLine) :
    rationalNeg X f.toRationalMap = (partialNeg X f).toRationalMap :=
  Quotient.map_mk (partialNeg X) (fun _ _ h ↦ partialNeg_compat X h) f

private instance instRationalFunctionsZero (X : Scheme.{u}) : Zero (rationalFunctions X) :=
  ⟨rationalZero X⟩

private instance instRationalFunctionsOne (X : Scheme.{u}) : One (rationalFunctions X) :=
  ⟨rationalOne X⟩

private instance instRationalFunctionsAdd (X : Scheme.{u}) : Add (rationalFunctions X) :=
  ⟨rationalAdd X⟩

private instance instRationalFunctionsMul (X : Scheme.{u}) : Mul (rationalFunctions X) :=
  ⟨rationalMul X⟩

private instance instRationalFunctionsNeg (X : Scheme.{u}) : Neg (rationalFunctions X) :=
  ⟨rationalNeg X⟩

/-- The commutative ring structure on rational functions, built from the operations on
representatives. -/
@[instance_reducible] private def rationalFunctionsCommRing (X : Scheme.{u}) :
    CommRing (rationalFunctions X) where
  zero := rationalZero X
  one := rationalOne X
  add := rationalAdd X
  mul := rationalMul X
  neg := rationalNeg X
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro f g h
    change rationalAdd X (rationalAdd X f.toRationalMap g.toRationalMap) h.toRationalMap =
      rationalAdd X f.toRationalMap (rationalAdd X g.toRationalMap h.toRationalMap)
    simp only [rationalAdd_toRationalMap]
    exact Quotient.sound (partialAdd_assoc X f g h)
  zero_add := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    change rationalAdd X (rationalZero X) f.toRationalMap = f.toRationalMap
    simp only [rationalZero, rationalAdd_toRationalMap]
    exact Quotient.sound (partialAdd_zero_left X f)
  add_zero := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    change rationalAdd X f.toRationalMap (rationalZero X) = f.toRationalMap
    simp only [rationalZero, rationalAdd_toRationalMap]
    exact Quotient.sound (partialAdd_zero_right X f)
  add_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro f g
    change rationalAdd X f.toRationalMap g.toRationalMap =
      rationalAdd X g.toRationalMap f.toRationalMap
    simp only [rationalAdd_toRationalMap]
    exact Quotient.sound (partialAdd_comm X f g)
  neg_add_cancel := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    change rationalAdd X (rationalNeg X f.toRationalMap) f.toRationalMap = rationalZero X
    simp only [rationalNeg_toRationalMap, rationalZero, rationalAdd_toRationalMap]
    exact Quotient.sound (partialNeg_add_cancel X f)
  mul_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro f g h
    change rationalMul X (rationalMul X f.toRationalMap g.toRationalMap) h.toRationalMap =
      rationalMul X f.toRationalMap (rationalMul X g.toRationalMap h.toRationalMap)
    simp only [rationalMul_toRationalMap]
    exact Quotient.sound (partialMul_assoc X f g h)
  one_mul := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    change rationalMul X (rationalOne X) f.toRationalMap = f.toRationalMap
    simp only [rationalOne, rationalMul_toRationalMap]
    exact Quotient.sound (partialMul_one_left X f)
  mul_one := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    change rationalMul X f.toRationalMap (rationalOne X) = f.toRationalMap
    simp only [rationalOne, rationalMul_toRationalMap]
    exact Quotient.sound (partialMul_one_right X f)
  zero_mul := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    change rationalMul X (rationalZero X) f.toRationalMap = rationalZero X
    simp only [rationalZero, rationalMul_toRationalMap]
    exact Quotient.sound (partialMul_zero_left X f)
  mul_zero := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    change rationalMul X f.toRationalMap (rationalZero X) = rationalZero X
    simp only [rationalZero, rationalMul_toRationalMap]
    exact Quotient.sound (partialMul_zero_right X f)
  right_distrib := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro f g h
    change rationalMul X (rationalAdd X f.toRationalMap g.toRationalMap) h.toRationalMap =
      rationalAdd X (rationalMul X f.toRationalMap h.toRationalMap)
        (rationalMul X g.toRationalMap h.toRationalMap)
    simp only [rationalAdd_toRationalMap, rationalMul_toRationalMap]
    exact Quotient.sound (partialAdd_mul_distrib X f g h)
  left_distrib := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro f g h
    change rationalMul X f.toRationalMap (rationalAdd X g.toRationalMap h.toRationalMap) =
      rationalAdd X (rationalMul X f.toRationalMap g.toRationalMap)
        (rationalMul X f.toRationalMap h.toRationalMap)
    simp only [rationalAdd_toRationalMap, rationalMul_toRationalMap]
    exact Quotient.sound <| (partialMul_comm X f (partialAdd X g h)).trans <|
      (partialAdd_mul_distrib X g h f).trans <|
        partialAdd_compat X (partialMul_comm X g f) (partialMul_comm X h f)
  mul_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro f g
    change rationalMul X f.toRationalMap g.toRationalMap =
      rationalMul X g.toRationalMap f.toRationalMap
    simp only [rationalMul_toRationalMap]
    exact Quotient.sound (partialMul_comm X f g)

/-- **Stacks 01RU.** The ring structure on rational maps to the affine line is the one induced
by the ring operations on sections on every dense open: there is a commutative ring structure on
`R(X)` for which, for every dense open `U ⊆ X`, the map sending a section `s ∈ Γ(X, U)` to the
rational function it represents is a ring homomorphism. -/
@[stacks 01RU]
theorem rationalFunctionsRing (X : Scheme.{u}) :
    ∃ R : CommRing (rationalFunctions X),
      letI := R
      ∀ U : DenseOpen X,
        ∃ φ : Γ(X, U.1) →+* rationalFunctions X,
          ∀ s, φ s = ofSection X U s := by
  refine ⟨rationalFunctionsCommRing X, ?_⟩
  let _ := rationalFunctionsCommRing X
  intro U
  refine ⟨
    { toFun := ofSection X U
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }, ?_⟩
  · change (sectionPartial X U (1 : Γ(X, U.1))).toRationalMap = (partialConst X 1).toRationalMap
    exact Quotient.sound (sectionPartial_one X U)
  · intro s t
    change (sectionPartial X U (s * t)).toRationalMap =
      (partialMul X (sectionPartial X U s) (sectionPartial X U t)).toRationalMap
    exact (Quotient.sound (sectionPartial_mul X U s t)).symm
  · change (sectionPartial X U (0 : Γ(X, U.1))).toRationalMap = (partialConst X 0).toRationalMap
    exact Quotient.sound (sectionPartial_zero X U)
  · intro s t
    change (sectionPartial X U (s + t)).toRationalMap =
      (partialAdd X (sectionPartial X U s) (sectionPartial X U t)).toRationalMap
    exact (Quotient.sound (sectionPartial_add X U s t)).symm
  · intro s
    rfl

/-- The canonical commutative ring structure on the rational functions of a scheme. -/
instance (X : Scheme.{u}) : CommRing (rationalFunctions X) :=
  (rationalFunctionsRing X).choose

/-- Sections on a dense open map homomorphically to rational functions. -/
def ofSectionRingHom (X : Scheme.{u}) (U : DenseOpen X) :
    Γ(X, U.1) →+* rationalFunctions X :=
  ((rationalFunctionsRing X).choose_spec U).choose

/-- The ring homomorphism `ofSectionRingHom` sends a section to the rational function it
represents. -/
@[simp]
theorem ofSectionRingHom_apply (X : Scheme.{u}) (U : DenseOpen X) (s : Γ(X, U.1)) :
    ofSectionRingHom X U s = ofSection X U s :=
  ((rationalFunctionsRing X).choose_spec U).choose_spec s

end Stacks.Chow
