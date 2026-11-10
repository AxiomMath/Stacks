module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of differentials of a fibre product of algebraic spaces

Let `f : X ⟶ T` and `g : Y ⟶ T` be morphisms of algebraic spaces over a scheme `S` and let
`p : W ⟶ X`, `q : W ⟶ Y` be the projections of a fibre product of `f` and `g`.  Stacks 05ZD
asserts that the two comparison maps of Stacks 04CX exhibit `Ω_{W/T}` as the direct sum
`p^*Ω_{X/T} ⊕ q^*Ω_{Y/T}`.

This file proves that from the transitivity sequence of Stacks 05Z8, which is available here in
full, together with the base-change isomorphism of Stacks 05ZC for the one cartesian square at
hand, read in both of its two orientations.  Nothing about étale charts is used, and in
particular the chartwise identification with the scheme-level map of Stacks 01V1 — carried as
`AlgebraicGeometry.Space.IsEtaleLocalFibreProductMap` by
`AlgebraicGeometry.Space.isIso_biprodDesc_of_isSheafOfDifferentialsMap` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsBaseChange.lean` — is not used.

## The argument

Write `Ω = Ω_{W/T}` and let `a : p^*Ω_{X/T} ⟶ Ω` and `b : q^*Ω_{Y/T} ⟶ Ω` be the two comparison
maps.  The transitivity sequence of Stacks 05Z8 for `W ⟶ X ⟶ T` is
```
  p^*Ω_{X/T} --a--> Ω --π--> Ω_{W/X} ⟶ 0
```
with `π = AlgebraicGeometry.Space.toRelativeDifferentials`, and the one for `W ⟶ Y ⟶ T` is the
same with `(p, f, a, π)` replaced by `(q, g, b, π')`, `π' : Ω ⟶ Ω_{W/Y}`.  Two things are read
off the sequence: `a ≫ π = 0` and `b ≫ π' = 0`
(`AlgebraicGeometry.Space.pullbackDifferentialsMap_comp_toRelativeDifferentials`), and that `π`
is a *cokernel* of `a` (`AlgebraicGeometry.Space.descOfCompEqZero` and
`AlgebraicGeometry.Space.toRelativeDifferentials_comp_descOfCompEqZero`).

The composites across the two sequences are the base-change comparison maps: `b ≫ π` is the
comparison map of Stacks 04CX for the square with top edge `q`, right edge `g`, left edge `p`
and bottom edge `f`, which is the cartesian square itself, and symmetrically for `a ≫ π'`.  That
is `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp_toRelativeDifferentials`, proved from
the characterizing property alone.  Stacks 05ZC therefore makes both of them invertible, and
`Stacks.Limits.isIso_biprodDesc_of_isIso_of_isCokernel` concludes: a morphism `b ≫ π` of the one
sequence inverting the cokernel map of the other splits it, which makes `a ⊕ b` a split
monomorphism and — because `π` is a cokernel of `a` — an epimorphism as well.

## Main definitions

* `AlgebraicGeometry.Space.toRelativeDifferentialsOfEq` is the canonical map `Ω_{X/B} ⟶ Ω_{X/Y}`
  of Stacks 05Z8 at a morphism `π : X ⟶ B` presented as `f ≫ g` rather than written that way.
  The two projections of a fibre product present its structure morphism in the two ways, and
  only one of them can be the one the statement is written at.

## Main results

* `Stacks.Limits.isIso_biprodDesc_of_isIso_of_isCokernel`: the categorical core, in a
  preadditive category — if `A ≫ π = 0`, `B ≫ π' = 0`, `π` is a cokernel of `A`, and both
  `B ≫ π` and `A ≫ π'` are invertible, then `biprod.desc A B` is invertible.
* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp_toRelativeDifferentials`: a comparison
  map of Stacks 04CX followed by a canonical map of Stacks 05Z8 is again a comparison map of
  Stacks 04CX, for the square whose left edge is the first factor.
* `AlgebraicGeometry.Space.isIso_biprodDesc_of_isPullback`: **Stacks 05ZD**, from the
  transitivity sequence of Stacks 05Z8 and the base change of Stacks 05ZC.

## Implementation notes

The structure morphism of the fibre product is written `p ≫ f`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsBaseChange.lean`, so the canonical map
`π'` to `Ω_{W/Y}` — whose source is `Ω_{W/(q ≫ g)}` as
`AlgebraicGeometry.Space.toRelativeDifferentials` is stated — has to be read at the other
spelling of that morphism.  `AlgebraicGeometry.Space.toRelativeDifferentialsOfEq` is that map,
defined by substituting the equality, and the two facts about it used here are proved by the
same substitution from the corresponding facts about
`AlgebraicGeometry.Space.toRelativeDifferentials`.

The hypothesis under which Stacks 05ZC enters is its conclusion, quantified over the comparison
maps of the square: *every* morphism with the characterizing property of Stacks 04CX for that
square is invertible.  That is the form in which uniqueness
(`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`) makes it applicable to `b ≫ π`,
which is produced here as a comparison map rather than chosen as one.

## References

* [Stacks Project, Tag 05ZD](https://stacks.math.columbia.edu/tag/05ZD)
* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC), the base change of the
  sheaf of differentials.
* [Stacks Project, Tag 05Z8](https://stacks.math.columbia.edu/tag/05Z8), the transitivity
  sequence.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ u

namespace Stacks.Limits

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

/-- **A direct sum split off a cokernel presentation.**  Let `A : P ⟶ O` and `Bm : Q ⟶ O` be
morphisms of a preadditive category, let `π : O ⟶ R` be a cokernel of `A` and let `π' : O ⟶ R'`
annihilate `Bm`.  If the two cross composites `Bm ≫ π` and `A ≫ π'` are invertible then
`A ⊕ Bm : P ⊞ Q ⟶ O` is invertible.

The inverse is `biprod.lift (π' ≫ (A ≫ π')⁻¹) (π ≫ (Bm ≫ π)⁻¹)`: the two cross composites being
invertible and the two straight ones zero makes it a left inverse by the universal property of
the biproduct, so `A ⊕ Bm` is a split monomorphism.  It is also an epimorphism: a morphism out of
`O` killed by `A ⊕ Bm` is killed by `A`, hence factors through the cokernel `π`, and is killed by
`Bm`, so the factorization is killed by the invertible `Bm ≫ π` and therefore vanishes.  A split
monomorphism which is an epimorphism is an isomorphism, in any category.

The cokernel hypothesis is taken as the factorization property rather than as a
`CategoryTheory.Limits.IsColimit`, which is the form the transitivity sequence of Stacks 05Z8
supplies it in; uniqueness of the factorization is not used. -/
theorem isIso_biprodDesc_of_isIso_of_isCokernel {P Q O R R' : C} [HasBinaryBiproduct P Q]
    (A : P ⟶ O) (Bm : Q ⟶ O) (π : O ⟶ R) (π' : O ⟶ R')
    (hAπ : A ≫ π = 0) (hBπ' : Bm ≫ π' = 0)
    (hcok : ∀ ⦃F : C⦄ (k : O ⟶ F), A ≫ k = 0 → ∃ t : R ⟶ F, π ≫ t = k)
    [IsIso (Bm ≫ π)] [IsIso (A ≫ π')] : IsIso (biprod.desc A Bm) := by
  have hepi : Epi (biprod.desc A Bm) := by
    refine ⟨fun {F} k₁ k₂ hk ↦ ?_⟩
    have hA : A ≫ (k₁ - k₂) = 0 := by simpa [sub_eq_zero] using biprod.inl ≫= hk
    have hB : Bm ≫ (k₁ - k₂) = 0 := by simpa [sub_eq_zero] using biprod.inr ≫= hk
    obtain ⟨t, ht⟩ := hcok (k₁ - k₂) hA
    have h0 : (Bm ≫ π) ≫ t = (Bm ≫ π) ≫ 0 := by
      rw [Category.assoc, ht, comp_zero]
      exact hB
    rw [← sub_eq_zero, ← ht, (cancel_epi (Bm ≫ π)).mp h0, comp_zero]
  have e1 : A ≫ π' ≫ inv (A ≫ π') = 𝟙 P := by rw [← Category.assoc, IsIso.hom_inv_id]
  have e2 : A ≫ π ≫ inv (Bm ≫ π) = 0 := by rw [← Category.assoc, hAπ, zero_comp]
  have e3 : Bm ≫ π' ≫ inv (A ≫ π') = 0 := by rw [← Category.assoc, hBπ', zero_comp]
  have e4 : Bm ≫ π ≫ inv (Bm ≫ π) = 𝟙 Q := by rw [← Category.assoc, IsIso.hom_inv_id]
  have hsplit : biprod.desc A Bm ≫
      biprod.lift (π' ≫ inv (A ≫ π')) (π ≫ inv (Bm ≫ π)) = 𝟙 (P ⊞ Q) := by
    ext <;> simp [e1, e2, e3, e4]
  exact ⟨biprod.lift (π' ≫ inv (A ≫ π')) (π ≫ inv (Bm ≫ π)), hsplit, by
    rw [← cancel_epi (biprod.desc A Bm), ← Category.assoc, hsplit, Category.id_comp,
      Category.comp_id]⟩

end Stacks.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y Z X' Y' W T : AlgebraicSpaces B S hS}

/-! ### A comparison map followed by a canonical map of the transitivity sequence -/

/-- The universal derivation `d_{X/B}` followed by the canonical map `Ω_{X/B} ⟶ Ω_{X/Y}` of the
transitivity sequence of Stacks 05Z8 is the universal derivation `d_{X/Y}`, as a morphism of the
underlying sheaves of sets.  This is
`AlgebraicGeometry.Space.toRelativeDifferentials_app_d` read globally. -/
theorem universalDerivationHom_comp_toRelativeDifferentials (m : X' ⟶ Z) (n : Z ⟶ Y') :
    universalDerivationHom B S hS (m ≫ n) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
          (toRelativeDifferentials B S hS m n) =
      universalDerivationHom B S hS m :=
  Sheaf.hom_ext_sections fun U t ↦ toRelativeDifferentials_app_d B S hS m n U t

/-- The composite `f_*d_{X'/B} ∘ f♯` of Stacks 04CX followed by the direct image of the canonical
map `Ω_{X'/B} ⟶ Ω_{X'/Z}` of Stacks 05Z8 is the composite `f_*d_{X'/Z} ∘ f♯` of Stacks 04CX. -/
theorem pushforwardUniversalDerivationHom_comp_toRelativeDifferentials (f : X' ⟶ X)
    (m : X' ⟶ Z) (n : Z ⟶ Y') :
    pushforwardUniversalDerivationHom B S hS f (m ≫ n) ≫
        (smallEtaleDirectImage B S hS f).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
            (toRelativeDifferentials B S hS m n)) =
      pushforwardUniversalDerivationHom B S hS f m := by
  have h1 : structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map
        (universalDerivationHom B S hS (m ≫ n) ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
            (toRelativeDifferentials B S hS m n)) =
      pushforwardUniversalDerivationHom B S hS f (m ≫ n) ≫
        (smallEtaleDirectImage B S hS f).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
            (toRelativeDifferentials B S hS m n)) := by
    rw [Functor.map_comp]
    rfl
  rw [← h1, universalDerivationHom_comp_toRelativeDifferentials]
  rfl

/-- **A comparison map of Stacks 04CX followed by a canonical map of Stacks 05Z8 is a comparison
map of Stacks 04CX.**  If `c : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` is the comparison map of the square whose
top edge is `f` and whose left edge is a composite `m ≫ n`, then `c` followed by the canonical
map `Ω_{X'/Y'} ⟶ Ω_{X'/Z}` of the transitivity sequence of `m` and `n` is the comparison map of
the square with the same top edge `f` and with left edge the first factor `m`.

Only the characterizing property is used: the adjunct is natural in its right argument, and the
canonical map of Stacks 05Z8 carries `d_{X'/Y'}` to `d_{X'/Z}`. -/
theorem isSheafOfDifferentialsMap_comp_toRelativeDifferentials (f : X' ⟶ X) (p : X ⟶ Y)
    (m : X' ⟶ Z) (n : Z ⟶ Y')
    {c : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS (m ≫ n)}
    (hc : IsSheafOfDifferentialsMap B S hS f p (m ≫ n) c) :
    IsSheafOfDifferentialsMap B S hS f p m (c ≫ toRelativeDifferentials B S hS m n) := by
  intro U t
  rw [Adjunction.homEquiv_naturality_right]
  change ((smallEtaleDirectImage B S hS f).map
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
        (toRelativeDifferentials B S hS m n))).hom.app U
      ((((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
        (sheafOfDifferentials B S hS (m ≫ n)) c).val.app U).hom
          ((universalDerivation B S hS p).d t)) = _
  rw [hc U t]
  exact congrArg (fun z ↦ z.hom.app U t)
    (pushforwardUniversalDerivationHom_comp_toRelativeDifferentials B S hS f m n)

/-! ### The canonical map of Stacks 05Z8 at another spelling of the structure morphism -/

/-- The canonical map `Ω_{X'/Y'} ⟶ Ω_{X'/Z}` of the transitivity sequence of Stacks 05Z8, at a
structure morphism `π : X' ⟶ Y'` presented as `m ≫ n` rather than written that way.

The two projections of a fibre product present its structure morphism in two ways, and a
statement about both of them can be written at only one of the two. -/
noncomputable def toRelativeDifferentialsOfEq (m : X' ⟶ Z) (n : Z ⟶ Y') (π : X' ⟶ Y')
    (hπ : m ≫ n = π) :
    sheafOfDifferentials B S hS π ⟶ sheafOfDifferentials B S hS m := by
  subst hπ
  exact toRelativeDifferentials B S hS m n

/-- `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp_toRelativeDifferentials` at a
structure morphism presented as a composite. -/
theorem isSheafOfDifferentialsMap_comp_toRelativeDifferentialsOfEq (f : X' ⟶ X) (p : X ⟶ Y)
    (m : X' ⟶ Z) (n : Z ⟶ Y') (π : X' ⟶ Y') (hπ : m ≫ n = π)
    {c : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS π}
    (hc : IsSheafOfDifferentialsMap B S hS f p π c) :
    IsSheafOfDifferentialsMap B S hS f p m
      (c ≫ toRelativeDifferentialsOfEq B S hS m n π hπ) := by
  subst hπ
  exact isSheafOfDifferentialsMap_comp_toRelativeDifferentials B S hS f p m n hc

/-- A comparison map of Stacks 04CX for the square with left edge `m ≫ n` is
`AlgebraicGeometry.Space.pullbackDifferentialsMap`. -/
private theorem eq_pullbackDifferentialsMap_of_isSheafOfDifferentialsMap (m : X' ⟶ Z)
    (n : Z ⟶ Y')
    {c : (modulePullback B S hS m).obj (sheafOfDifferentials B S hS n) ⟶
      sheafOfDifferentials B S hS (m ≫ n)}
    (hc : IsSheafOfDifferentialsMap B S hS m n (m ≫ n) c) :
    c = pullbackDifferentialsMap B S hS m n :=
  eq_of_isSheafOfDifferentialsMap B S hS m n (m ≫ n) hc
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS m n (m ≫ n) (𝟙 Y') (by simp))

/-- **The two maps of the transitivity sequence of Stacks 05Z8 compose to zero**, at a structure
morphism presented as a composite and at an arbitrary realization of the comparison map.  This is
`AlgebraicGeometry.Space.pullbackDifferentialsMap_comp_toRelativeDifferentials` together with the
uniqueness of the comparison map. -/
theorem comp_toRelativeDifferentialsOfEq_eq_zero (m : X' ⟶ Z) (n : Z ⟶ Y') (π : X' ⟶ Y')
    (hπ : m ≫ n = π)
    {c : (modulePullback B S hS m).obj (sheafOfDifferentials B S hS n) ⟶
      sheafOfDifferentials B S hS π}
    (hc : IsSheafOfDifferentialsMap B S hS m n π c) :
    c ≫ toRelativeDifferentialsOfEq B S hS m n π hπ = 0 := by
  subst hπ
  rw [eq_pullbackDifferentialsMap_of_isSheafOfDifferentialsMap B S hS m n hc]
  exact pullbackDifferentialsMap_comp_toRelativeDifferentials B S hS m n

/-! ### Stacks 05ZD -/

/-- **Stacks 05ZD reduced to Stacks 05ZC.**  Let `f : X ⟶ T` and `g : Y ⟶ T` be morphisms of
algebraic spaces over `S` with the same target and let `p : W ⟶ X`, `q : W ⟶ Y` be the
projections of a fibre product of `f` and `g`.  The two comparison maps of Stacks 04CX exhibit
`Ω_{W/T}` as the direct sum `p^*Ω_{X/T} ⊕ q^*Ω_{Y/T}`, as soon as the base change of Stacks 05ZC
is available at the two orientations of the cartesian square at hand — which is what `h05ZC` and
`h05ZCFlip` are.

Both summands are named by the characterizing property of Stacks 04CX for the square they come
from — the one with top edge `p` and right edge `f`, and the one with top edge `q` and right edge
`g`, both with left edge the structure morphism `p ≫ f` of `W` — so the conclusion is about the
two comparison maps and not about some decomposition of `Ω_{W/T}`.

The proof is the transitivity sequence of Stacks 05Z8 for `W ⟶ X ⟶ T` and for `W ⟶ Y ⟶ T`, both
of them available unconditionally, plus those two instances of Stacks 05ZC.  No étale chart is
used, and in particular the chartwise identification with the scheme-level map of Stacks 01V1 is
not used.

**This is the reduction and not the tag**, since `h05ZC` and `h05ZCFlip` are instances of
Stacks 05ZC; the tag is registered on
`AlgebraicGeometry.Space.isIso_biprodDesc_sheafOfDifferentialsMap_of_isPullback`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareBijective.lean`), where
the two instances are supplied from
`AlgebraicGeometry.Space.schemeSquareDerivationRestriction`. -/
theorem isIso_biprodDesc_of_isPullback (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T)
    (h : IsPullback p q f g)
    (a : (modulePullback B S hS p).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (b : (modulePullback B S hS q).obj (sheafOfDifferentials B S hS g) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (ha : IsSheafOfDifferentialsMap B S hS p f (p ≫ f) a)
    (hb : IsSheafOfDifferentialsMap B S hS q g (p ≫ f) b)
    (h05ZC : ∀ c : (modulePullback B S hS q).obj (sheafOfDifferentials B S hS g) ⟶
        sheafOfDifferentials B S hS p, IsSheafOfDifferentialsMap B S hS q g p c → IsIso c)
    (h05ZCFlip : ∀ c : (modulePullback B S hS p).obj (sheafOfDifferentials B S hS f) ⟶
        sheafOfDifferentials B S hS q, IsSheafOfDifferentialsMap B S hS p f q c → IsIso c) :
    IsIso (biprod.desc a b) := by
  have hπ' : q ≫ g = p ≫ f := h.w.symm
  have hu : IsIso (b ≫ toRelativeDifferentials B S hS p f) :=
    h05ZC _ (isSheafOfDifferentialsMap_comp_toRelativeDifferentials B S hS q g p f hb)
  have hv : IsIso (a ≫ toRelativeDifferentialsOfEq B S hS q g (p ≫ f) hπ') :=
    h05ZCFlip _ (isSheafOfDifferentialsMap_comp_toRelativeDifferentialsOfEq B S hS p f q g
      (p ≫ f) hπ' ha)
  have ha' : a = pullbackDifferentialsMap B S hS p f :=
    eq_pullbackDifferentialsMap_of_isSheafOfDifferentialsMap B S hS p f ha
  refine Stacks.Limits.isIso_biprodDesc_of_isIso_of_isCokernel a b
    (toRelativeDifferentials B S hS p f) (toRelativeDifferentialsOfEq B S hS q g (p ≫ f) hπ')
    (comp_toRelativeDifferentialsOfEq_eq_zero B S hS p f (p ≫ f) rfl ha)
    (comp_toRelativeDifferentialsOfEq_eq_zero B S hS q g (p ≫ f) hπ' hb)
    fun {F} k hk ↦ ⟨descOfCompEqZero B S hS p f k (ha' ▸ hk),
      toRelativeDifferentials_comp_descOfCompEqZero B S hS p f k (ha' ▸ hk)⟩

/-- **Stacks 05ZD from the étale-local step of Stacks 05ZC.**  The same statement as
`AlgebraicGeometry.Space.isIso_biprodDesc_of_isPullback`, with the base change of Stacks 05ZC
supplied from `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isPullback` at the
two orientations of the cartesian square.

What is assumed is therefore `AlgebraicGeometry.Space.IsEtaleLocalBaseChangeMap` for the *base
change* square, which is the input the statements of this file and of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsBaseChange.lean` carry.  It asks chart
by chart for the canonical map of Stacks 01UV of a cartesian square of schemes, so it is not the
invertibility clause of Stacks 04CS, which is proved, as
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`.
The bespoke fibre-product input
`AlgebraicGeometry.Space.IsEtaleLocalFibreProductMap` — asked for by
`AlgebraicGeometry.Space.isIso_biprodDesc_of_isSheafOfDifferentialsMap`, and asking chart by
chart for the map of Stacks 01V1 — is not needed: the transitivity sequence of Stacks 05Z8
reduces the direct-sum statement to the base-change statement.

**This is one step of the reduction and not the tag.**  The tag is registered on
`AlgebraicGeometry.Space.isIso_biprodDesc_sheafOfDifferentialsMap_of_isPullback`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareBijective.lean`), which
takes a cartesian square and the characterizing property of the two maps and nothing else. -/
theorem isIso_biprodDesc_of_isEtaleLocalBaseChangeMap (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ T)
    (g : Y ⟶ T) (h : IsPullback p q f g)
    (a : (modulePullback B S hS p).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (b : (modulePullback B S hS q).obj (sheafOfDifferentials B S hS g) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (ha : IsSheafOfDifferentialsMap B S hS p f (p ≫ f) a)
    (hb : IsSheafOfDifferentialsMap B S hS q g (p ≫ f) b)
    (hetale : IsEtaleLocalBaseChangeMap B S hS q p g f h.flip
      (sheafOfDifferentialsMap B S hS q g p f h.w.symm))
    (hetaleFlip : IsEtaleLocalBaseChangeMap B S hS p q f g h
      (sheafOfDifferentialsMap B S hS p f q g h.w)) :
    IsIso (biprod.desc a b) :=
  isIso_biprodDesc_of_isPullback B S hS p q f g h a b ha hb
    (fun c hc ↦ isIso_of_isSheafOfDifferentialsMap_of_isPullback B S hS q p g f h.flip c
      (sheafOfDifferentialsMap B S hS q g p f h.w.symm) hc
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS q g p f h.w.symm) hetale)
    fun c hc ↦ isIso_of_isSheafOfDifferentialsMap_of_isPullback B S hS p q f g h c
      (sheafOfDifferentialsMap B S hS p f q g h.w) hc
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS p f q g h.w) hetaleFlip

end AlgebraicGeometry.Space

end
