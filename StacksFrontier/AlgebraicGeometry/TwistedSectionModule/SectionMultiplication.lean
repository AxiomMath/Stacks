module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.MonoidalFunctor

/-!
# Multiplying by a section of a tensor power, as a morphism of the ambient category

The whole twisted-section development multiplies by a global section `s` of `L ^⊗ d` *inside*
the modules on a slice site: `Stacks.TwistedSections.shiftPow` is the `k`-fold multiplication,
and `Stacks.TwistedSections.powerDivision` is its inverse. That is what makes the comparison map
of Stacks Tag 0B5L available on an open where `s` is invertible — and it is also what stops the
map built over one open from being compared with the map built over a smaller one, because the
two live on two different sites.

**This file removes the obstruction, by making the multiplication a morphism.** For a section
`σ` of `L ^⊗ j` there is a morphism `Stacks.TwistedSections.twistMul F σ : F ⟶ F ⊙ j` of the
ambient monoidal category — whisker `σ` on the right of `F` and collect the `j` copies of `L` —
and the `k`-fold multiplication by `s` is composition with that morphism:

`Stacks.TwistedSections.shiftPow_eq_comp_twistMul`.

A morphism has a value on the sections over *every* object of the site and commutes with every
restriction map by naturality, with nothing to prove. So a division built on one slice site is
identified, by `twistMul`, with the inverse of a map that already exists on all of them.

The second half of the file carries `twistMul` along a monoidal functor
(`Stacks.TwistedSections.map_twistMul`), which is what connects the morphism on `X` with the
division built after the restriction to an open.

## Main definitions

* `Stacks.TwistedSections.twistZeroIso`: `F ⊙ 0 = F`, as an isomorphism; see the implementation
  notes for why the crossing is made explicit.
* `Stacks.TwistedSections.twistMul`: **multiplication by a section of `L ^⊗ j`, as a morphism
  `F ⟶ F ⊙ j`.**

## Main results

* `Stacks.TwistedSections.shiftPow_eq_actMap`: the `k`-fold multiplication by `s`, from degree
  zero, is the action of `sᵏ`. This is `Stacks.TwistedSections.shiftIter_eq_actMap` at the
  degree-zero start, with the reindexing along `0 + d k = d k` written out.
* `Stacks.TwistedSections.gsmul_shiftPow`: **acting by `A` on the `k`-fold multiple of `u` by `s`
  is acting by the product `sᵏ · A`**, with no commutativity of the section ring: the product
  comes out in the one order `Stacks.TwistedSections.actMap_comp` produces.
* `Stacks.TwistedSections.shiftPow_eq_comp_twistMul`: **the `k`-fold multiplication by `s` is
  composition with `twistMul sᵏ`.**
* `Stacks.TwistedSections.mapTwistPow_comp_twistPowAddIso`: **the associativity of the twist is
  carried along a monoidal functor.**
* `Stacks.TwistedSections.map_twistMul`: **multiplication by a section is carried along a
  monoidal functor** — the morphism built upstairs, carried along `G` and compared with the
  twisted objects downstairs, is the morphism built downstairs from the carried section.

## Implementation notes

**No component formula for a tensorator is used anywhere.** The two functoriality statements are
inductions whose steps are `CategoryTheory.Functor.Monoidal.map_whiskerRight`,
`map_whiskerLeft`, `map_associator`, `map_rightUnitor_inv` and the mutual inverseness of `μ` and
`δ` — all generic. This is the same discipline as
`Stacks.TwistedSections.map_actMap` and `map_mulMap` in
`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/MonoidalFunctor.lean`, and it is what makes
the results available for restriction to an open of a scheme, whose tensorator is
`CategoryTheory.Localization.Monoidal.μ` of a sheafification and has no formula on sections.

**Why the degree reductions are written out.** `Stacks.TwistedSections.twistPow F L 0` is `F`
and `0 + j` is `j`, both by `rfl` and neither syntactically. A composite that crosses either
spelling is *not type-correct at `implicit` transparency*, and then every `rw` touching it fails
with "did not find an occurrence of the pattern". Two devices keep every statement rewritable, and no reducibility attribute is set:

* the crossing `F ⊙ 0 = F` is made once, as the explicit `eqToHom` of `twistZeroIso`, inside
  `twistMul`; so `twistMul F σ : F ⟶ F ⊙ j` has a source in reduced form, and so does
  `map_twistMul`, which is the statement consumers rewrite with;
* the two inductions begin with a `show` that writes every degree in reduced form, which is
  legitimate because `show` works at default transparency.

The same two devices are what
`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/OpenRestrictionShrink.lean` uses on the
geometric side.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
-/
@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections mul mulMap sectionRing HasTrivialSelfBraiding powCongr
  powCongr_rfl)
open Stacks.TensorPowers (natTensorPow)
open Stacks.SectionRingProjQuasicoherent (twistPowAddIso)

universe v₂ u₂ v u

namespace Stacks.TwistedSections

section Shift

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {F L : C}
  [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive]

omit [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive] in
/-- Multiplication by `s` commutes with reindexing the degree of its argument: both are
compositions. -/
theorem shiftBySection_twistCongr {d : ℕ} (s : powSections L d) {m m' : ℕ} (h : m = m')
    (t : twistSections F L m) :
    shiftBySection s (twistCongr h t) =
      twistCongr (congrArg (· + d) h) (shiftBySection s t) := by
  subst h
  simp [twistCongr]

omit [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive] in
/-- The `k`-fold multiplication by `s` from an arbitrary degree is the `k`-fold multiplication
from degree zero, reindexed along `0 + d k = d k`. -/
theorem shiftIter_eq_shiftPow {d : ℕ} (s : powSections L d) (u : twistSections F L 0) :
    ∀ k : ℕ, shiftIter s u k = twistCongr (Nat.zero_add (d * k)).symm (shiftPow s k u)
  | 0 => by simp [twistCongr]
  | k + 1 => by
      rw [shiftIter_succ, shiftIter_eq_shiftPow s u k, shiftBySection_twistCongr,
        twistCongr_trans, shiftPow_succ]

/-- **The `k`-fold multiplication by `s`, from degree zero, is the action of `sᵏ`.** This is
`Stacks.TwistedSections.shiftIter_eq_actMap` at the degree-zero start; the reindexing is the
`0 + d k = d k` that `Stacks.TwistedSections.shiftIter` carries and
`Stacks.TwistedSections.shiftPow` does not. -/
theorem shiftPow_eq_actMap {d : ℕ} (s : powSections L d) (k : ℕ) (u : twistSections F L 0) :
    shiftPow s k u =
      twistCongr (Nat.zero_add (d * k)) (sectionPowOfDegree s k ≫ actMap u (d * k)) := by
  rw [← shiftIter_eq_actMap s u k, shiftIter_eq_shiftPow s u k, twistCongr_trans]
  simp [twistCongr]

/-- **Acting by `A` on the `k`-fold multiple of `u` by `s` is acting by the product `sᵏ · A`.**
No commutativity of the section ring is used: the product appears in the single order
`Stacks.TwistedSections.actMap_comp` produces. -/
theorem gsmul_shiftPow {d p : ℕ} (s : powSections L d) (A : powSections L p) (k : ℕ)
    (u : twistSections F L 0) (h : 0 + (d * k + p) = p + d * k) :
    gsmul A (shiftPow s k u) =
      twistCongr h (mul (sectionPowOfDegree s k) A ≫ actMap u (d * k + p)) := by
  have key : actMap (shiftPow s k u) p =
      mulMap (sectionPowOfDegree s k) p ≫ actMap u (d * k + p) ≫
        eqToHom (congrArg (twistPow F L)
          ((Nat.add_assoc 0 (d * k) p).symm.trans
            (congrArg (· + p) (Nat.zero_add (d * k))))) := by
    rw [shiftPow_eq_actMap s k u, actMap_twistCongr, actMap_comp]
    simp only [Category.assoc, eqToHom_trans]
  rw [gsmul_def, key, ← Category.assoc, ← Stacks.GradedSections.mul_def]
  simp only [twistCongr, Category.assoc, eqToHom_trans]

end Shift

section Mul

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **`F ⊙ 0 = F`, as an isomorphism.** `Stacks.TwistedSections.twistPow_zero` holds by `rfl`,
but not syntactically, so a composite that crosses the two spellings is not type-correct at
`implicit` transparency and no rewrite can touch it. Making the crossing an explicit `eqToHom`,
once, is what keeps every statement below rewritable. -/
def twistZeroIso (F L : C) : F ≅ twistPow F L 0 := eqToIso (twistPow_zero F L).symm

/-- **Multiplication by a section of `L ^⊗ j`, as a morphism `F ⟶ F ⊙ j`.** The section is
whiskered on the right of `F` and the `j` copies of `L` are collected by
`Stacks.SectionRingProjQuasicoherent.twistPowAddIso`; the source is written `F` and the crossing
to `F ⊙ 0` is the explicit `twistZeroIso`. -/
def twistMul (F : C) {L : C} {j : ℕ} (σ : powSections L j) : F ⟶ twistPow F L j :=
  (twistZeroIso F L).hom ≫ (ρ_ (twistPow F L 0)).inv ≫ twistPow F L 0 ◁ σ ≫
    (twistPowAddIso F L 0 j).inv ≫ eqToHom (congrArg (twistPow F L) (Nat.zero_add j))

variable {F L : C}

/-- The two ways of multiplying a morphism out of the unit by a section of `L ^⊗ j` agree: this
is one instance of `CategoryTheory.MonoidalCategory.whisker_exchange` together with the equality
of the two unit constraints of `𝟙_ C`. -/
theorem comp_leftUnitor_inv_whiskerRight {j : ℕ} (σ : powSections L j)
    (w : twistSections F L 0) :
    σ ≫ (λ_ (natTensorPow L j)).inv ≫ w ▷ natTensorPow L j =
      w ≫ (ρ_ (twistPow F L 0)).inv ≫ twistPow F L 0 ◁ σ := by
  have h1 : σ ≫ (λ_ (natTensorPow L j)).inv =
      (λ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ σ := leftUnitor_inv_naturality _
  have h2 : w ≫ (ρ_ (twistPow F L 0)).inv = (λ_ (𝟙_ C)).inv ≫ w ▷ 𝟙_ C := by
    rw [rightUnitor_inv_naturality, ← unitors_inv_equal]
  rw [← Category.assoc, h1, ← Category.assoc, h2, Category.assoc, Category.assoc,
    whisker_exchange]

variable [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive]

/-- **The `k`-fold multiplication by `s` is composition with the morphism `twistMul sᵏ`.** This
is what takes the multiplication out of the twisted-section vocabulary and makes it an honest
morphism of the ambient category, which is the whole point: a morphism has a value on the
sections over every object and is therefore compatible with every restriction. -/
theorem shiftPow_eq_comp_twistMul {d : ℕ} (s : powSections L d) (k : ℕ)
    (w : twistSections F L 0) :
    shiftPow s k w =
      (w ≫ (twistZeroIso F L).inv) ≫ twistMul F (sectionPowOfDegree s k) := by
  have hmain : sectionPowOfDegree s k ≫ actMap w (d * k) =
      (w ≫ (ρ_ (twistPow F L 0)).inv ≫ twistPow F L 0 ◁ sectionPowOfDegree s k) ≫
        (twistPowAddIso F L 0 (d * k)).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, actMap_comp_twistPowAddIso,
      comp_leftUnitor_inv_whiskerRight]
  rw [shiftPow_eq_actMap s k w, twistCongr, hmain, twistMul]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Mul

section Functorial

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (G : C ⥤ D) [G.Monoidal] {F L : C}

/-- Carrying the comparison of the twisted objects along a reindexing of the degree. -/
theorem mapTwistPow_eqToHom {m m' : ℕ} (h : m = m') :
    G.map (eqToHom (congrArg (twistPow F L) h)) ≫ mapTwistPow G F L m' =
      mapTwistPow G F L m ≫ eqToHom (congrArg (twistPow (G.obj F) (G.obj L)) h) := by
  subst h
  simp

/-- Carrying `σ`, whiskered on the right of `F ⊙ m` after the right unitor, along a monoidal
functor: the result is built downstairs from `σ` carried by the unit comparison `ε` and any
comparison `g`. -/
private theorem map_rightUnitor_inv_comp_map_whiskerLeft {N : C} {N' : D} {X' : D} (m : ℕ)
    (σ : 𝟙_ C ⟶ N) (f : G.obj (twistPow F L m) ⟶ X') (g : G.obj N ⟶ N') :
    G.map ((ρ_ (twistPow F L m)).inv) ≫ G.map (twistPow F L m ◁ σ) ≫
        Functor.OplaxMonoidal.δ G (twistPow F L m) N ≫ (f ⊗ₘ g) =
      f ≫ (ρ_ X').inv ≫ X' ◁ (Functor.LaxMonoidal.ε G ≫ G.map σ ≫ g) := by
  rw [Functor.Monoidal.map_rightUnitor_inv, Functor.Monoidal.map_whiskerLeft]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [tensorHom_def, whisker_exchange_assoc, whisker_exchange_assoc, ← Category.assoc,
    ← rightUnitor_inv_naturality]
  simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp]

/-- **The associativity of the twist is carried along a monoidal functor**: the comparison of the
twisted objects intertwines `Stacks.SectionRingProjQuasicoherent.twistPowAddIso` upstairs with
the same isomorphism downstairs, through the oplax tensorator of `G` and the comparison of the
tensor powers.

No component formula for the tensorator is used: the induction consumes only
`CategoryTheory.Functor.Monoidal.map_whiskerRight`,
`CategoryTheory.Functor.Monoidal.map_associator` and the mutual inverseness of `μ` and `δ`. Both
cases begin with a `show` that writes every degree in reduced form: the two recursions make
`F ⊙ (m + (j + 1))` and `F ⊙ (m + j) ⊗ L` definitionally but not syntactically equal, and a
rewrite in the unreduced shape leaves a goal that is not type-correct at `implicit`
transparency. -/
theorem mapTwistPow_comp_twistPowAddIso (m : ℕ) : ∀ j : ℕ,
    mapTwistPow G F L (m + j) ≫ (twistPowAddIso (G.obj F) (G.obj L) m j).hom =
      G.map ((twistPowAddIso F L m j).hom) ≫
        Functor.OplaxMonoidal.δ G (twistPow F L m) (natTensorPow L j) ≫
          (mapTwistPow G F L m ⊗ₘ mapNatTensorPow G L j)
  | 0 => by
      change mapTwistPow G F L m ≫ (ρ_ (twistPow (G.obj F) (G.obj L) m)).inv =
        G.map ((ρ_ (twistPow F L m)).inv) ≫
          Functor.OplaxMonoidal.δ G (twistPow F L m) (𝟙_ C) ≫
            (mapTwistPow G F L m ⊗ₘ Functor.OplaxMonoidal.η G)
      simpa using (map_rightUnitor_inv_comp_map_whiskerLeft G m (𝟙 (𝟙_ C))
        (mapTwistPow G F L m) (Functor.OplaxMonoidal.η G)).symm
  | j + 1 => by
      show (Functor.OplaxMonoidal.δ G (twistPow F L (m + j)) L ≫
            mapTwistPow G F L (m + j) ▷ G.obj L) ≫
          ((twistPowAddIso (G.obj F) (G.obj L) m j).hom ▷ G.obj L ≫
            (α_ (twistPow (G.obj F) (G.obj L) m) (natTensorPow (G.obj L) j) (G.obj L)).hom) =
        G.map ((twistPowAddIso F L m j).hom ▷ L ≫
            (α_ (twistPow F L m) (natTensorPow L j) L).hom) ≫
          Functor.OplaxMonoidal.δ G (twistPow F L m) (natTensorPow L j ⊗ L) ≫
            (mapTwistPow G F L m ⊗ₘ (Functor.OplaxMonoidal.δ G (natTensorPow L j) L ≫
              mapNatTensorPow G L j ▷ G.obj L))
      rw [Functor.map_comp, Functor.Monoidal.map_whiskerRight,
        Functor.Monoidal.map_associator]
      simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
      rw [← Category.assoc (mapTwistPow G F L (m + j) ▷ G.obj L), ← comp_whiskerRight,
        mapTwistPow_comp_twistPowAddIso m j]
      simp only [comp_whiskerRight, Category.assoc]
      rw [← tensorHom_id (mapTwistPow G F L m ⊗ₘ mapNatTensorPow G L j),
        associator_naturality]
      simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp]
      rw [whisker_exchange_assoc]
      simp

/-- **Multiplication by a section is carried along a monoidal functor.** The morphism
`Stacks.TwistedSections.twistMul` built upstairs, carried along `G` and compared with the twisted
objects downstairs, is the morphism built downstairs from the carried section. Every object in
the statement is in reduced form, which is what lets a consumer rewrite with it.

This is what makes the multiplication usable across a change of site: the division produced on a
slice site is the inverse of multiplication by the *carried* section, and this identifies that
with the carried multiplication morphism, which — being a morphism of the ambient category — has
a value on the sections over every object. -/
theorem map_twistMul {j : ℕ} (σ : powSections L j) :
    G.map (twistMul F σ) ≫ mapTwistPow G F L j =
      twistMul (G.obj F) (mapPowSections G σ) := by
  have hτ : G.map ((twistPowAddIso F L 0 j).inv) ≫ mapTwistPow G F L (0 + j) =
      (Functor.OplaxMonoidal.δ G (twistPow F L 0) (natTensorPow L j) ≫
        (mapTwistPow G F L 0 ⊗ₘ mapNatTensorPow G L j)) ≫
          (twistPowAddIso (G.obj F) (G.obj L) 0 j).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, mapTwistPow_comp_twistPowAddIso G 0 j,
      ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hmain : G.map ((ρ_ (twistPow F L 0)).inv ≫ twistPow F L 0 ◁ σ ≫
          (twistPowAddIso F L 0 j).inv ≫
            eqToHom (congrArg (twistPow F L) (Nat.zero_add j))) ≫ mapTwistPow G F L j =
      mapTwistPow G F L 0 ≫ (ρ_ (twistPow (G.obj F) (G.obj L) 0)).inv ≫
        twistPow (G.obj F) (G.obj L) 0 ◁ mapPowSections G σ ≫
          (twistPowAddIso (G.obj F) (G.obj L) 0 j).inv ≫
            eqToHom (congrArg (twistPow (G.obj F) (G.obj L)) (Nat.zero_add j)) := by
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [mapTwistPow_eqToHom G (Nat.zero_add j), reassoc_of% hτ,
      reassoc_of% map_rightUnitor_inv_comp_map_whiskerLeft G 0 σ
        (mapTwistPow G F L 0) (mapNatTensorPow G L j)]
    rfl
  have hz : G.map ((twistZeroIso F L).hom) ≫ mapTwistPow G F L 0 =
      (twistZeroIso (G.obj F) (G.obj L)).hom :=
    (Category.comp_id _).trans (eqToHom_map G (twistPow_zero F L).symm)
  rw [twistMul, twistMul, Functor.map_comp, Category.assoc, hmain,
    ← Category.assoc (G.map ((twistZeroIso F L).hom)), hz]

end Functorial

end Stacks.TwistedSections

end
