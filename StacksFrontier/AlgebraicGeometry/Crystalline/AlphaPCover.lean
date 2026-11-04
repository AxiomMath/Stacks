module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# `α_p`-covers, iterated `α_p`-covers, and constant degree

An *`α_p`-cover* is a morphism of schemes of the form

`Spec(C[z]/(z ^ p - c)) ⟶ Spec(C)`,

where `C` is a ring in which the prime `p` vanishes and `c ∈ C`.  Equivalently the source is an
`α_p`-torsor over the target.  An *iterated `α_p`-cover* is a morphism of schemes in
characteristic `p` which is, locally on the target, a composition of finitely many `α_p`-covers.

An `α_p`-cover and a composition of `α_p`-covers may be transported along isomorphisms of the
source and the target, compositions of such compositions are again such, and the source of a
composition of `α_p`-covers over an affine target is affine.

`HasConstantDegree f q` is finite local freeness of degree `q`: locally on the target the
sections of the source are a free module of rank `q` over the sections of the target. An
iterated `α_p`-cover need not have a constant degree.

## Main definitions

* `AlgebraicGeometry.alphaPAlgebra` — the `C`-algebra `C[z]/(z ^ p - c)`.
* `AlgebraicGeometry.alphaPCoverMap` — the morphism `Spec(C[z]/(z ^ p - c)) ⟶ Spec(C)`.
* `AlgebraicGeometry.IsAlphaPCover` — being an `α_p`-cover: being identified, by isomorphisms of
  the source and of the target, with `alphaPCoverMap` for some `C` killing `p` and some `c ∈ C`.
* `AlgebraicGeometry.IsAlphaPCoverComposite` — being a composition of finitely many
  `α_p`-covers, as an inductive predicate whose base case is an isomorphism.
* `AlgebraicGeometry.IsIteratedAlphaPCover` — being an iterated `α_p`-cover: the target is in
  characteristic `p`, and every point of the target has an open neighbourhood over which the
  restriction of the morphism is a composition of finitely many `α_p`-covers.
* `AlgebraicGeometry.HasConstantDegree` — being finite locally free of constant degree `q`.

## Main results

* `AlgebraicGeometry.isAlphaPCover_of_iso` and
  `AlgebraicGeometry.isAlphaPCoverComposite_of_iso` — both notions transport along a
  commuting square whose vertical arrows are isomorphisms.
* `AlgebraicGeometry.isAlphaPCoverComposite_comp` — a composition of two compositions of
  `α_p`-covers is one.
* `AlgebraicGeometry.isAffine_source_of_isAlphaPCoverComposite` — over an affine target the
  source of a composition of `α_p`-covers is affine.

## References

* [Stacks Project, Section 60.26, Tag 07PZ](https://stacks.math.columbia.edu/tag/07PZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### The local model -/

/-- The `C`-algebra `C[z]/(z ^ p - c)`, the ring of the local model of an `α_p`-cover. -/
abbrev alphaPAlgebra (p : ℕ) (C : Type u) [CommRing C] (c : C) : Type u :=
  Polynomial C ⧸ Ideal.span {(Polynomial.X ^ p - Polynomial.C c : Polynomial C)}

/-- The local model of an `α_p`-cover: the morphism `Spec(C[z]/(z ^ p - c)) ⟶ Spec(C)` induced by
the structure map of `C[z]/(z ^ p - c)` as a `C`-algebra. -/
def alphaPCoverMap (p : ℕ) (C : Type u) [CommRing C] (c : C) :
    Spec (CommRingCat.of (alphaPAlgebra p C c)) ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk _).comp (Polynomial.C (R := C))))

/-! ### `α_p`-covers -/

/-- `f` is an `α_p`-cover: there are a ring `C` in which `p` vanishes and an element `c ∈ C` such
that `f` is identified with `Spec(C[z]/(z ^ p - c)) ⟶ Spec(C)` by isomorphisms of its source and
its target. -/
def IsAlphaPCover (p : ℕ) {X' X : Scheme.{u}} (f : X' ⟶ X) : Prop :=
  ∃ (C : Type u) (inst : CommRing C),
    letI := inst
    ∃ (_ : (p : C) = 0) (c : C)
      (e : X ≅ Spec (CommRingCat.of C))
      (e' : X' ≅ Spec (CommRingCat.of (alphaPAlgebra p C c))),
      f ≫ e.hom = e'.hom ≫ alphaPCoverMap p C c

/-- `f` is a composition of finitely many `α_p`-covers.  The base case is an isomorphism, so the
empty composition is included. -/
inductive IsAlphaPCoverComposite (p : ℕ) :
    ∀ {X' X : Scheme.{u}}, (X' ⟶ X) → Prop
  | of_isIso {X' X : Scheme.{u}} (e : X' ⟶ X) (he : IsIso e) : IsAlphaPCoverComposite p e
  | comp {X'' X' X : Scheme.{u}} {g : X'' ⟶ X'} {h : X' ⟶ X} :
      IsAlphaPCover p g → IsAlphaPCoverComposite p h → IsAlphaPCoverComposite p (g ≫ h)

/-- `f` is an iterated `α_p`-cover: its target is in characteristic `p`, and every point of the
target has an open neighbourhood over which the restriction of `f` is a composition of finitely
many `α_p`-covers. -/
def IsIteratedAlphaPCover (p : ℕ) {X' X : Scheme.{u}} (f : X' ⟶ X) : Prop :=
  (p : Γ(X, ⊤)) = 0 ∧
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAlphaPCoverComposite p (f ∣_ U)

/-- `f` is finite locally free of constant degree `q`: around every point of the target there is
an affine open over which the sections of the source form a free module of rank `q` over the
sections of the target. -/
def HasConstantDegree {X' X : Scheme.{u}} (f : X' ⟶ X) (q : ℕ) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    letI := (f.app U).hom.toAlgebra
    Module.Free Γ(X, U) Γ(X', f ⁻¹ᵁ U) ∧ Module.rank Γ(X, U) Γ(X', f ⁻¹ᵁ U) = q

/-! ### Transport along isomorphisms, and composition -/

/-- Precomposing an `α_p`-cover with an isomorphism gives an `α_p`-cover. -/
theorem isAlphaPCover_iso_comp (p : ℕ) {X Y Z : Scheme.{u}}
    (e : X ⟶ Y) [IsIso e] {f : Y ⟶ Z} (hf : IsAlphaPCover p f) :
    IsAlphaPCover p (e ≫ f) := by
  obtain ⟨C, hC, hp, c, i, j, hf⟩ := hf
  exact ⟨C, hC, hp, c, i, asIso e ≪≫ j, by simp [hf]⟩

/-- Precomposing a composition of `α_p`-covers with an isomorphism gives a composition of
`α_p`-covers. -/
theorem isAlphaPCoverComposite_iso_comp (p : ℕ) {X Y Z : Scheme.{u}}
    (e : X ⟶ Y) [IsIso e] {f : Y ⟶ Z} (hf : IsAlphaPCoverComposite p f) :
    IsAlphaPCoverComposite p (e ≫ f) := by
  induction hf with
  | of_isIso f h => exact .of_isIso _ inferInstance
  | comp hg hh =>
    simpa only [Category.assoc] using IsAlphaPCoverComposite.comp
      (isAlphaPCover_iso_comp p e hg) hh

/-- A composition of two compositions of `α_p`-covers is a composition of `α_p`-covers. -/
theorem isAlphaPCoverComposite_comp (p : ℕ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsAlphaPCoverComposite p f)
    (hg : IsAlphaPCoverComposite p g) :
    IsAlphaPCoverComposite p (f ≫ g) := by
  induction hf with
  | of_isIso f h => exact isAlphaPCoverComposite_iso_comp p f hg
  | comp hf hh ih =>
    simpa only [Category.assoc] using IsAlphaPCoverComposite.comp hf (ih hg)

/-- Being an `α_p`-cover transports along a commuting square whose vertical arrows are
isomorphisms. -/
theorem isAlphaPCover_of_iso (p : ℕ) {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (i : X ≅ X') (j : Y ≅ Y')
    (h : f ≫ j.hom = i.hom ≫ g) (hg : IsAlphaPCover p g) :
    IsAlphaPCover p f := by
  obtain ⟨C, hC, hp, c, a, b, hg⟩ := hg
  refine ⟨C, hC, hp, c, j ≪≫ a, i ≪≫ b, ?_⟩
  show f ≫ j.hom ≫ a.hom = (i.hom ≫ b.hom) ≫ _
  rw [← Category.assoc, h, Category.assoc, hg, Category.assoc]

/-- Being a composition of `α_p`-covers transports along a commuting square whose vertical arrows
are isomorphisms. -/
theorem isAlphaPCoverComposite_of_iso (p : ℕ) {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (i : X ≅ X') (j : Y ≅ Y')
    (h : f ≫ j.hom = i.hom ≫ g) (hg : IsAlphaPCoverComposite p g) :
    IsAlphaPCoverComposite p f := by
  have hf : f = (i.hom ≫ g) ≫ j.inv := by
    rw [← h, Category.assoc, j.hom_inv_id, Category.comp_id]
  rw [hf]
  exact isAlphaPCoverComposite_comp p
    (isAlphaPCoverComposite_iso_comp p i.hom hg) (.of_isIso _ inferInstance)

/-! ### Affineness of the source -/

/-- The source of an `α_p`-cover is affine. -/
theorem isAffine_source_of_isAlphaPCover
    {X Y : Scheme.{u}} {f : X ⟶ Y} (p : ℕ) (hf : IsAlphaPCover p f) :
    IsAffine X := by
  obtain ⟨_, _, _, _, _, e', _⟩ := hf
  exact IsAffine.of_isIso e'.hom

/-- Over an affine target, the source of a composition of `α_p`-covers is affine. -/
theorem isAffine_source_of_isAlphaPCoverComposite
    {X Y : Scheme.{u}} [IsAffine Y] {f : X ⟶ Y} (p : ℕ)
    (hf : IsAlphaPCoverComposite p f) : IsAffine X := by
  cases hf with
  | of_isIso f h => exact IsAffine.of_isIso f
  | comp hf hg => exact isAffine_source_of_isAlphaPCover p hf

end AlgebraicGeometry

end
