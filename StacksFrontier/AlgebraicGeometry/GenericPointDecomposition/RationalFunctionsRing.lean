module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions
public import StacksFrontier.AlgebraicGeometry.GenericPointDecomposition.RationalFunctions

/-!
# Computing in the ring of rational functions on a scheme

Rational functions on a scheme form a commutative ring, for the operations computed on
representatives: two rational functions are represented by sections on dense opens, those
sections are restricted to the intersection, and added or multiplied there. This file records
those computation rules for the canonical ring structure, the instance
`Stacks.Chow.instCommRingRationalFunctions` produced by `Stacks.Chow.rationalFunctionsRing`
(Stacks 01RU).

## Main definitions

* `Stacks.AlgebraicGeometry.GenericPointDecomposition.restr`: restriction of a section along an
  inclusion of opens.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.partialAdd`,
  `partialMul`, `partialNeg`: the operations on partial maps to the affine line.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.ofSectionOnRingHom`: a section on the
  restricted scheme of a dense open, regarded as a rational function, as a ring homomorphism.

## Main results

* `Stacks.AlgebraicGeometry.GenericPointDecomposition.ofSectionOn_add`,
  `ofSectionOn_mul`, `ofSectionOn_neg`, `ofSectionOn_zero`, `ofSectionOn_one`: the ring
  operations are computed by the corresponding operations on sections on a common dense open.
  Together with `exists_common₂` and `exists_common₃` these reduce any identity between
  rational functions to the same identity in a ring of sections.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.toRationalMap_partialAdd`,
  `toRationalMap_partialMul`, `toRationalMap_partialNeg`: the ring operations are computed by
  the operations on partial maps.

## Implementation notes

This file declares no instance. It once built a second `CommRing (rationalFunctions X)` by
`Quotient.liftOn₂` on representatives; that structure is not definitionally equal to the one
in `Stacks.Chow`, and on the same carrier the two made `map_add` fail for
`Stacks.Chow.ofSectionRingHom` in any file importing both. The computation rules are now
derived from the canonical structure through `ofSectionOn_eq_ofSectionRingHom`, which identifies
`ofSectionOn` with `Stacks.Chow.ofSectionRingHom` after the isomorphism
`AlgebraicGeometry.Scheme.Opens.topIso` between `Γ(U, ⊤)` and `Γ(X, U)`.

The lemmas `partialAdd_sound`, `partialMul_sound` and `partialNeg_sound` show directly, via
`ofSectionOn_eq_iff`, that the operations on partial maps respect
`AlgebraicGeometry.Scheme.PartialMap.equiv`: given witnesses for the two arguments, their
intersection witnesses the result, because restriction is a ring homomorphism. Density of an
intersection of two dense opens uses only that one of them is open, so no hypothesis on the
scheme is needed.

## References

* [Stacks Project, Tag 01RU](https://stacks.math.columbia.edu/tag/01RU)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointDecomposition

variable {X : Scheme.{u}}

/-- Restriction of a section to a smaller open. -/
noncomputable abbrev restr {U V : X.Opens} (h : V ≤ U) (s : Γ(U, ⊤)) : Γ(V, ⊤) :=
  (X.homOfLE h).appTop s

lemma restr_restr {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (s : Γ(W, ⊤)) :
    restr hUV (restr hVW s) = restr (hUV.trans hVW) s :=
  homOfLE_appTop_appTop hUV hVW s

@[simp]
lemma restr_self {U : X.Opens} (h : U ≤ U) (s : Γ(U, ⊤)) : restr h s = s := by
  simp [restr]

/-- The whole space is a dense open. -/
lemma dense_coe_top : Dense (((⊤ : X.Opens) : Set X)) := by
  simpa only [Opens.coe_top] using dense_univ

/-- A rational function is the one given by its own section. -/
lemma toRationalMap_eq_ofSectionOn (f : X.PartialMap (affineLine : Scheme.{u})) :
    f.toRationalMap = ofSectionOn f.domain f.dense_domain (lineSection f.hom) :=
  (congrArg Scheme.PartialMap.toRationalMap (partialMapOfSection_lineSection f)).symm

/-- Equivalence of partial maps to the affine line, as an equality of restricted sections. -/
lemma equiv_iff_exists_restr_eq {f g : X.PartialMap (affineLine : Scheme.{u})} :
    f.equiv g ↔ ∃ (W : X.Opens) (_ : Dense (W : Set X)) (hWf : W ≤ f.domain)
      (hWg : W ≤ g.domain), restr hWf (lineSection f.hom) = restr hWg (lineSection g.hom) := by
  refine Iff.trans Scheme.PartialMap.toRationalMap_eq_iff.symm ?_
  simp only [toRationalMap_eq_ofSectionOn]
  exact ofSectionOn_eq_iff _ _ _ _

/-- The intersection of the domains of two partial maps is a dense open. -/
lemma dense_inf_domain (f g : X.PartialMap (affineLine : Scheme.{u})) :
    Dense (((f.domain ⊓ g.domain : X.Opens)) : Set X) :=
  f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2

/-- The sum of two partial maps to the affine line. -/
noncomputable abbrev partialAdd (f g : X.PartialMap (affineLine : Scheme.{u})) :
    X.PartialMap (affineLine : Scheme.{u}) :=
  partialMapOfSection _ (dense_inf_domain f g)
    (restr inf_le_left (lineSection f.hom) + restr inf_le_right (lineSection g.hom))

/-- The product of two partial maps to the affine line. -/
noncomputable abbrev partialMul (f g : X.PartialMap (affineLine : Scheme.{u})) :
    X.PartialMap (affineLine : Scheme.{u}) :=
  partialMapOfSection _ (dense_inf_domain f g)
    (restr inf_le_left (lineSection f.hom) * restr inf_le_right (lineSection g.hom))

/-- The negative of a partial map to the affine line. -/
noncomputable abbrev partialNeg (f : X.PartialMap (affineLine : Scheme.{u})) :
    X.PartialMap (affineLine : Scheme.{u}) :=
  partialMapOfSection _ f.dense_domain (-lineSection f.hom)

/-- The section of a sum of partial maps. -/
lemma lineSection_partialAdd (f g : X.PartialMap (affineLine : Scheme.{u})) :
    lineSection (partialAdd f g).hom
      = restr inf_le_left (lineSection f.hom) + restr inf_le_right (lineSection g.hom) :=
  lineSection_partialMapOfSection _ _ _

/-- The section of a product of partial maps. -/
lemma lineSection_partialMul (f g : X.PartialMap (affineLine : Scheme.{u})) :
    lineSection (partialMul f g).hom
      = restr inf_le_left (lineSection f.hom) * restr inf_le_right (lineSection g.hom) :=
  lineSection_partialMapOfSection _ _ _

/-- The section of a negative of a partial map. -/
lemma lineSection_partialNeg (f : X.PartialMap (affineLine : Scheme.{u})) :
    lineSection (partialNeg f).hom = -lineSection f.hom :=
  lineSection_partialMapOfSection _ _ _

/-- The section of a sum, restricted to a dense open contained in both domains. -/
lemma restr_partialAdd (f g : X.PartialMap (affineLine : Scheme.{u})) {W : X.Opens}
    (hW : W ≤ (partialAdd f g).domain) (hf : W ≤ f.domain) (hg : W ≤ g.domain) :
    restr hW (lineSection (partialAdd f g).hom)
      = restr hf (lineSection f.hom) + restr hg (lineSection g.hom) :=
  (congrArg (restr hW) (lineSection_partialAdd f g)).trans
    ((map_add _ _ _).trans
      (congrArg₂ (· + ·) (restr_restr hW inf_le_left (lineSection f.hom))
        (restr_restr hW inf_le_right (lineSection g.hom))))

/-- The section of a product, restricted to a dense open contained in both domains. -/
lemma restr_partialMul (f g : X.PartialMap (affineLine : Scheme.{u})) {W : X.Opens}
    (hW : W ≤ (partialMul f g).domain) (hf : W ≤ f.domain) (hg : W ≤ g.domain) :
    restr hW (lineSection (partialMul f g).hom)
      = restr hf (lineSection f.hom) * restr hg (lineSection g.hom) :=
  (congrArg (restr hW) (lineSection_partialMul f g)).trans
    ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (restr_restr hW inf_le_left (lineSection f.hom))
        (restr_restr hW inf_le_right (lineSection g.hom))))

/-- The section of a negative, restricted to a dense open in its domain. -/
lemma restr_partialNeg (f : X.PartialMap (affineLine : Scheme.{u})) {W : X.Opens}
    (hW : W ≤ (partialNeg f).domain) (hf : W ≤ f.domain) :
    restr hW (lineSection (partialNeg f).hom) = -restr hf (lineSection f.hom) :=
  (congrArg (restr hW) (lineSection_partialNeg f)).trans
    (map_neg _ _)

/-- Two equivalent pairs of partial maps agree on a common dense open contained in all four
domains. -/
private theorem exists_dense_restr_eq_pair {f₁ g₁ f₂ g₂ : X.PartialMap (affineLine : Scheme.{u})}
    (hf : f₁.equiv f₂) (hg : g₁.equiv g₂) :
    ∃ (W : X.Opens) (_ : Dense (W : Set X)) (h₁ : W ≤ f₁.domain) (h₂ : W ≤ g₁.domain)
      (h₃ : W ≤ f₂.domain) (h₄ : W ≤ g₂.domain),
      restr h₁ (lineSection f₁.hom) = restr h₃ (lineSection f₂.hom) ∧
        restr h₂ (lineSection g₁.hom) = restr h₄ (lineSection g₂.hom) := by
  obtain ⟨W₁, hW₁, hW₁a, hW₁b, e₁⟩ := equiv_iff_exists_restr_eq.mp hf
  obtain ⟨W₂, hW₂, hW₂a, hW₂b, e₂⟩ := equiv_iff_exists_restr_eq.mp hg
  refine ⟨W₁ ⊓ W₂, hW₁.inter_of_isOpen_left hW₂ W₁.2, inf_le_left.trans hW₁a,
    inf_le_right.trans hW₂a, inf_le_left.trans hW₁b, inf_le_right.trans hW₂b, ?_, ?_⟩
  · rw [← restr_restr inf_le_left hW₁a, ← restr_restr inf_le_left hW₁b, e₁]
  · rw [← restr_restr inf_le_right hW₂a, ← restr_restr inf_le_right hW₂b, e₂]

lemma partialAdd_sound (f₁ g₁ f₂ g₂ : X.PartialMap (affineLine : Scheme.{u}))
    (hf : f₁.equiv f₂) (hg : g₁.equiv g₂) :
    (partialAdd f₁ g₁).toRationalMap = (partialAdd f₂ g₂).toRationalMap := by
  obtain ⟨W, hW, h₁, h₂, h₃, h₄, e₁, e₂⟩ := exists_dense_restr_eq_pair hf hg
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr (equiv_iff_exists_restr_eq.mpr
    ⟨W, hW, le_inf h₁ h₂, le_inf h₃ h₄, ?_⟩)
  refine (restr_partialAdd f₁ g₁ _ h₁ h₂).trans (Eq.trans ?_ (restr_partialAdd f₂ g₂ _ h₃ h₄).symm)
  rw [e₁, e₂]

lemma partialMul_sound (f₁ g₁ f₂ g₂ : X.PartialMap (affineLine : Scheme.{u}))
    (hf : f₁.equiv f₂) (hg : g₁.equiv g₂) :
    (partialMul f₁ g₁).toRationalMap = (partialMul f₂ g₂).toRationalMap := by
  obtain ⟨W, hW, h₁, h₂, h₃, h₄, e₁, e₂⟩ := exists_dense_restr_eq_pair hf hg
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr (equiv_iff_exists_restr_eq.mpr
    ⟨W, hW, le_inf h₁ h₂, le_inf h₃ h₄, ?_⟩)
  refine (restr_partialMul f₁ g₁ _ h₁ h₂).trans (Eq.trans ?_ (restr_partialMul f₂ g₂ _ h₃ h₄).symm)
  rw [e₁, e₂]

lemma partialNeg_sound (f₁ f₂ : X.PartialMap (affineLine : Scheme.{u})) (hf : f₁.equiv f₂) :
    (partialNeg f₁).toRationalMap = (partialNeg f₂).toRationalMap := by
  obtain ⟨W, hW, hWa, hWb, e⟩ := equiv_iff_exists_restr_eq.mp hf
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
    (equiv_iff_exists_restr_eq.mpr ⟨W, hW, hWa, hWb, ?_⟩)
  refine Eq.trans (restr_partialNeg f₁ _ hWa) ?_
  refine Eq.trans ?_ (restr_partialNeg f₂ _ hWb).symm
  rw [e]

/-- Regarding a section on a dense open as a rational function commutes with restriction. -/
lemma ofSectionOn_restr {U V : X.Opens} (hV : Dense (V : Set X)) (hUV : V ≤ U)
    (hU : Dense (U : Set X)) (s : Γ(U, ⊤)) :
    ofSectionOn V hV (restr hUV s) = ofSectionOn U hU s :=
  ofSectionOn_homOfLE_appTop hV hUV hU s

/-- A section on a dense open, regarded as a rational function, is its image under the canonical
ring homomorphism `Stacks.Chow.ofSectionRingHom`, once `AlgebraicGeometry.Scheme.Opens.topIso`
has moved it from `Γ(U, ⊤)` to `Γ(X, U)`. -/
lemma ofSectionOn_eq_ofSectionRingHom (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(U, ⊤)) :
    ofSectionOn U hU s = Stacks.Chow.ofSectionRingHom X ⟨U, hU⟩ (U.topIso.hom s) := by
  rw [Stacks.Chow.ofSectionRingHom_apply]
  change ofSectionOn U hU s = ofSectionOn U hU (U.topIso.inv (U.topIso.hom s))
  rw [Iso.hom_inv_id_apply]

@[simp]
lemma ofSectionOn_add (U : X.Opens) (hU : Dense (U : Set X)) (s t : Γ(U, ⊤)) :
    ofSectionOn U hU s + ofSectionOn U hU t = ofSectionOn U hU (s + t) := by
  simp only [ofSectionOn_eq_ofSectionRingHom, map_add]

@[simp]
lemma ofSectionOn_mul (U : X.Opens) (hU : Dense (U : Set X)) (s t : Γ(U, ⊤)) :
    ofSectionOn U hU s * ofSectionOn U hU t = ofSectionOn U hU (s * t) := by
  simp only [ofSectionOn_eq_ofSectionRingHom, map_mul]

@[simp]
lemma ofSectionOn_neg (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(U, ⊤)) :
    -ofSectionOn U hU s = ofSectionOn U hU (-s) := by
  simp only [ofSectionOn_eq_ofSectionRingHom, map_neg]

/-- The zero rational function is given by the zero section on any dense open. -/
@[simp]
lemma ofSectionOn_zero (U : X.Opens) (hU : Dense (U : Set X)) :
    ofSectionOn U hU (0 : Γ(U, ⊤)) = 0 := by
  simp only [ofSectionOn_eq_ofSectionRingHom, map_zero]

/-- The unit rational function is given by the unit section on any dense open. -/
@[simp]
lemma ofSectionOn_one (U : X.Opens) (hU : Dense (U : Set X)) :
    ofSectionOn U hU (1 : Γ(U, ⊤)) = 1 := by
  simp only [ofSectionOn_eq_ofSectionRingHom, map_one]

/-- The rational function of the sum of two partial maps is the sum of their rational
functions. -/
lemma toRationalMap_partialAdd (f g : X.PartialMap (affineLine : Scheme.{u})) :
    (partialAdd f g).toRationalMap = f.toRationalMap + g.toRationalMap := by
  rw [toRationalMap_eq_ofSectionOn f, toRationalMap_eq_ofSectionOn g,
    ← ofSectionOn_restr (dense_inf_domain f g) inf_le_left f.dense_domain,
    ← ofSectionOn_restr (dense_inf_domain f g) inf_le_right g.dense_domain, ofSectionOn_add]
  rfl

/-- The rational function of the product of two partial maps is the product of their rational
functions. -/
lemma toRationalMap_partialMul (f g : X.PartialMap (affineLine : Scheme.{u})) :
    (partialMul f g).toRationalMap = f.toRationalMap * g.toRationalMap := by
  rw [toRationalMap_eq_ofSectionOn f, toRationalMap_eq_ofSectionOn g,
    ← ofSectionOn_restr (dense_inf_domain f g) inf_le_left f.dense_domain,
    ← ofSectionOn_restr (dense_inf_domain f g) inf_le_right g.dense_domain, ofSectionOn_mul]
  rfl

/-- The rational function of the negative of a partial map is the negative of its rational
function. -/
lemma toRationalMap_partialNeg (f : X.PartialMap (affineLine : Scheme.{u})) :
    (partialNeg f).toRationalMap = -f.toRationalMap := by
  rw [toRationalMap_eq_ofSectionOn f, ofSectionOn_neg]
  rfl

lemma ofSectionOn_add_eq (U : X.Opens) (hU : Dense (U : Set X)) (s t : Γ(U, ⊤)) :
    ofSectionOn U hU s + ofSectionOn U hU t
      = (partialAdd (partialMapOfSection U hU s) (partialMapOfSection U hU t)).toRationalMap :=
  (toRationalMap_partialAdd _ _).symm

lemma ofSectionOn_mul_eq (U : X.Opens) (hU : Dense (U : Set X)) (s t : Γ(U, ⊤)) :
    ofSectionOn U hU s * ofSectionOn U hU t
      = (partialMul (partialMapOfSection U hU s) (partialMapOfSection U hU t)).toRationalMap :=
  (toRationalMap_partialMul _ _).symm

lemma ofSectionOn_neg_eq (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(U, ⊤)) :
    -ofSectionOn U hU s = (partialNeg (partialMapOfSection U hU s)).toRationalMap :=
  (toRationalMap_partialNeg _).symm

/-- Two rational functions are given by sections on a common dense open. -/
lemma exists_common₂ (a b : rationalFunctions X) :
    ∃ (U : X.Opens) (hU : Dense (U : Set X)) (s t : Γ(U, ⊤)),
      a = ofSectionOn U hU s ∧ b = ofSectionOn U hU t := by
  obtain ⟨U, hU, s, hs⟩ := ofSectionOn_surjective a
  obtain ⟨V, hV, t, ht⟩ := ofSectionOn_surjective b
  exact ⟨U ⊓ V, hU.inter_of_isOpen_left hV U.2, restr inf_le_left s, restr inf_le_right t,
    hs.symm.trans (ofSectionOn_restr _ inf_le_left hU s).symm,
    ht.symm.trans (ofSectionOn_restr _ inf_le_right hV t).symm⟩

/-- Three rational functions are given by sections on a common dense open. -/
lemma exists_common₃ (a b c : rationalFunctions X) :
    ∃ (U : X.Opens) (hU : Dense (U : Set X)) (s t r : Γ(U, ⊤)),
      a = ofSectionOn U hU s ∧ b = ofSectionOn U hU t ∧ c = ofSectionOn U hU r := by
  obtain ⟨U, hU, s, t, hs, ht⟩ := exists_common₂ a b
  obtain ⟨V, hV, r, hr⟩ := ofSectionOn_surjective c
  refine ⟨U ⊓ V, hU.inter_of_isOpen_left hV U.2, restr inf_le_left s, restr inf_le_left t,
    restr inf_le_right r, ?_, ?_, ?_⟩
  · exact hs.trans (ofSectionOn_restr _ inf_le_left hU s).symm
  · exact ht.trans (ofSectionOn_restr _ inf_le_left hU t).symm
  · exact hr.symm.trans (ofSectionOn_restr _ inf_le_right hV r).symm

/-- Regarding a section on a dense open as a rational function is a ring homomorphism. -/
noncomputable def ofSectionOnRingHom (U : X.Opens) (hU : Dense (U : Set X)) :
    Γ(U, ⊤) →+* rationalFunctions X where
  toFun := ofSectionOn U hU
  map_one' := ofSectionOn_one U hU
  map_mul' s t := (ofSectionOn_mul U hU s t).symm
  map_zero' := ofSectionOn_zero U hU
  map_add' s t := (ofSectionOn_add U hU s t).symm

end Stacks.AlgebraicGeometry.GenericPointDecomposition
