module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.InvertibleSection

/-!
# The twisted sections along a monoidal functor, and the comparison map they produce

`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/InvertibleSection.lean` produces the
divisions by the powers of `s` that Stacks Tag 0B5L's comparison map takes as a hypothesis,
provided `s` is an *isomorphism*. A global section of an ample invertible module on a scheme is
not an isomorphism; it becomes one only after restriction to an open inside its nonvanishing
locus. This file carries the twisted sections along a monoidal functor `G : C ⥤ D` and produces
the divisions — hence the comparison map — as soon as `s` becomes invertible in `D`.

The result is Stacks Tag 0B5L's map in the form the `Proj`-side gluing of Stacks Tag 0B5I wants
it: a map out of the degree-zero localization `Γ_*(X, F, L)_{(s)}` of the *global* twisted
sections, landing in the sections of `F` over the open `s` trivializes `L` on, with no hypothesis
left standing.

## Main definitions

* `Stacks.TwistedSections.mapNatTensorPow` and `Stacks.TwistedSections.mapTwistPow`: the
  comparisons `G(L ^⊗ n) ⟶ (G L) ^⊗ n` and `G(F ⊙ m) ⟶ (G F) ⊙ m`, built from the oplax
  tensorator and counit of `G`.
* `Stacks.TwistedSections.mapPowSections` and `Stacks.TwistedSections.mapTwistSections`: the
  induced maps on sections of the tensor powers and on twisted sections.
* `Stacks.TwistedSections.mapTwistSectionsHom`: the same, as a morphism of additive groups.
* `Stacks.TwistedSections.monoidalDivision`: **the divisions by the powers of `s`** obtained by
  carrying a twisted section along `G` and dividing there.
* `Stacks.TwistedSections.localizationLiftOfMonoidal`: **Stacks Tag 0B5L's comparison map**
  `Γ_*(X, F, L)_{(s)} ⟶ Γ(G F)`, for a monoidal `G` after which `s` is invertible.

## Main results

* `Stacks.TwistedSections.mapTwistSections_shiftBySection`: **the one compatibility the whole
  file rests on** — carrying a twisted section along `G` commutes with multiplication by `s`.
  Its proof is one oplax naturality square and one use of `η ≫ ε = 𝟙`.
* `Stacks.TwistedSections.mapTwistSections_shiftIter`: the same for the iterated multiplication,
  by induction.
* `Stacks.TwistedSections.isPowerInvariant_monoidalDivision`: the divisions are power-invariant.
* `Stacks.TwistedSections.shiftPow_monoidalDivision`: the value of the comparison map on `t / sⁿ`
  is *the* section of `G F` whose product with `(G s)ⁿ` is the image of `t`. This is Stacks Tag
  0B5L's description of the map, and what makes the construction faithful rather than arbitrary.
* `Stacks.TwistedSections.mapNatTensorPow_comp`, `mapTwistPow_comp`, `mapPowSections_comp` and
  `mapTwistSections_comp`: **functoriality of the whole construction in `G`** — each of the four
  comparisons for a composite `G ⋙ H` of monoidal functors is the comparison for `H` applied
  after `H` of the comparison for `G`. With `isIso_mapPowSections_comp` this reduces the input of
  `Stacks.TwistedSections.localizationLiftOfMonoidal` at a composite to its input at the second
  factor.
* `Stacks.TwistedSections.mapTwistSections_monoidalDivision`,
  `monoidalDivision_comp` and `localizationLiftOfMonoidal_comp`: **the division after a composite
  is the division after the first factor, carried along the second** — which for two nested
  restrictions of a scheme is the statement that the comparison map over the smaller open is the
  restriction of the comparison map over the larger one. The last of the three says it of the
  comparison *maps*, on the whole degree-zero localization and not only on the fractions, which
  is the form Stacks Tag 0B5I's compatibility field needs.

## Implementation notes

**Only the single-step compatibility is proved, and it is enough.** The power-invariance condition
is phrased with `Stacks.TwistedSections.gsmul` at `Stacks.TwistedSections.sectionPowOfDegree`,
i.e. with the action of the element `sᵏ` of the section ring. Proving that `mapPowSections` sends
`sᵏ` to `(G s)ᵏ` would ask for `mapPowSections` to be a graded ring map, which is the
associativity coherence of `G`. It is not needed: `Stacks.TwistedSections.shiftIter_eq_actMap`
rewrites the action of `sᵏ` as `k` single multiplications, and only the single-step compatibility
is then used — whose proof needs the oplax tensorator's naturality and nothing about its coherence.

**The four composite laws need no formula for the tensorator.** Each of
`Stacks.TwistedSections.mapNatTensorPow_comp` and its three companions is an induction whose step
is one application of `CategoryTheory.Functor.OplaxMonoidal.δ_natural_left` together with the two
composition laws `CategoryTheory.Functor.OplaxMonoidal.comp_η`, `comp_δ` and
`CategoryTheory.Functor.LaxMonoidal.comp_ε` of the composite monoidal structure, which are what
Mathlib's `@[simps]` on the composite instance exports. Nothing is ever asked of a *component* of
the oplax tensorator, so the laws hold for a functor whose tensorator is produced by a universal
property and has no formula on sections — which is the case for restriction to an open of a
scheme, where the tensorator is `CategoryTheory.Localization.Monoidal.μ` of a sheafification.

**`G` is asked to be strong monoidal, not lax.** Carrying a section `t : 𝟙_ C ⟶ F ⊙ m` along `G`
gives `G 𝟙_ C ⟶ G(F ⊙ m)`, which has to be turned into `𝟙_ D ⟶ (G F) ⊙ m`: the source needs the
lax unit `ε` and the target needs the oplax tensorator `δ`. `CategoryTheory.Functor.Monoidal`
supplies both, and `Functor.Monoidal.η_ε` — available only because the two structures are
mutually inverse — is what makes the single-step compatibility come out exactly.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — the comparison
  `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` that makes a pullback of sheaves of modules such a `G`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections sectionRing HasTrivialSelfBraiding)
open Stacks.TensorPowers (natTensorPow)

universe v₃ u₃ v₂ u₂ v u

namespace Stacks.TwistedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (G : C ⥤ D) [G.Monoidal] {F L : C}

section Comparison


/-- **The comparison `G(L ^⊗ n) ⟶ (G L) ^⊗ n`**, by `n` applications of the oplax tensorator of
`G` and one of its counit. -/
def mapNatTensorPow (L : C) :
    (n : ℕ) → (G.obj (natTensorPow L n) ⟶ natTensorPow (G.obj L) n)
  | 0 => Functor.OplaxMonoidal.η G
  | n + 1 => Functor.OplaxMonoidal.δ G (natTensorPow L n) L ≫ mapNatTensorPow L n ▷ G.obj L

/-- The comparison `G(L ^⊗ 0) ⟶ (G L) ^⊗ 0` is the oplax counit of `G`. -/
theorem mapNatTensorPow_zero (L : C) :
    mapNatTensorPow G L 0 = Functor.OplaxMonoidal.η G := rfl

/-- The comparison `G(L ^⊗ (n + 1)) ⟶ (G L) ^⊗ (n + 1)` is the oplax tensorator of `G` followed
by the comparison in degree `n` whiskered by `G L`. -/
theorem mapNatTensorPow_succ (L : C) (n : ℕ) :
    mapNatTensorPow G L (n + 1) =
      Functor.OplaxMonoidal.δ G (natTensorPow L n) L ≫
        mapNatTensorPow G L n ▷ G.obj L := rfl

/-- **The comparison `G(F ⊙ m) ⟶ (G F) ⊙ m`**, by `m` applications of the oplax tensorator of
`G`. No counit appears: the recursion of `Stacks.TwistedSections.twistPow` starts at `F`. -/
def mapTwistPow (F L : C) :
    (m : ℕ) → (G.obj (twistPow F L m) ⟶ twistPow (G.obj F) (G.obj L) m)
  | 0 => 𝟙 _
  | m + 1 => Functor.OplaxMonoidal.δ G (twistPow F L m) L ≫ mapTwistPow F L m ▷ G.obj L

/-- The comparison `G(F ⊙ 0) ⟶ (G F) ⊙ 0` is the identity of `G F`. -/
theorem mapTwistPow_zero (F L : C) : mapTwistPow G F L 0 = 𝟙 (G.obj F) := rfl

/-- The comparison `G(F ⊙ (m + 1)) ⟶ (G F) ⊙ (m + 1)` is the oplax tensorator of `G` followed
by the comparison in degree `m` whiskered by `G L`. -/
theorem mapTwistPow_succ (F L : C) (m : ℕ) :
    mapTwistPow G F L (m + 1) =
      Functor.OplaxMonoidal.δ G (twistPow F L m) L ≫
        mapTwistPow G F L m ▷ G.obj L := rfl

/-- **A section of `L ^⊗ n` carried along `G`.** -/
def mapPowSections {L : C} {n : ℕ} (a : powSections L n) : powSections (G.obj L) n :=
  Functor.LaxMonoidal.ε G ≫ G.map a ≫ mapNatTensorPow G L n

/-- **A twisted section carried along `G`.** -/
def mapTwistSections {F L : C} {m : ℕ} (t : twistSections F L m) :
    twistSections (G.obj F) (G.obj L) m :=
  Functor.LaxMonoidal.ε G ≫ G.map t ≫ mapTwistPow G F L m

/-- **The comparison of the tensor powers is an isomorphism**, `G` being strong monoidal: both
the counit and the tensorator are. -/
instance isIso_mapNatTensorPow (L : C) (n : ℕ) : IsIso (mapNatTensorPow G L n) := by
  induction n with
  | zero => exact (inferInstance : IsIso (Functor.OplaxMonoidal.η G))
  | succ n ih =>
      exact (inferInstance : IsIso (Functor.OplaxMonoidal.δ G (natTensorPow L n) L ≫
        mapNatTensorPow G L n ▷ G.obj L))

/-- **The comparison of the twisted objects is an isomorphism.** -/
instance isIso_mapTwistPow (F L : C) (m : ℕ) : IsIso (mapTwistPow G F L m) := by
  induction m with
  | zero => rw [mapTwistPow_zero]; exact IsIso.id _
  | succ m ih =>
      exact (inferInstance : IsIso (Functor.OplaxMonoidal.δ G (twistPow F L m) L ≫
        mapTwistPow G F L m ▷ G.obj L))

/-- **The one geometric input, reduced to a statement about `G` alone:** a section of a tensor
power is invertible after `G` as soon as its image under `G` is. This is what makes the
hypothesis of `Stacks.TwistedSections.localizationLiftOfMonoidal` checkable — on a scheme, for
`G` the restriction to an open inside the nonvanishing locus of `s`, it is the trivialization
clause of Stacks Tag 01CY. -/
instance isIso_mapPowSections {n : ℕ} (a : powSections L n) [IsIso (G.map a)] :
    IsIso (mapPowSections G a) := by
  rw [mapPowSections]; infer_instance

/-- Carrying a twisted section along `G` commutes with reindexing the degree. -/
theorem mapTwistSections_twistCongr {m m' : ℕ} (h : m = m') (t : twistSections F L m) :
    mapTwistSections G (twistCongr h t) = twistCongr h (mapTwistSections G t) := by
  subst h; rw [twistCongr_rfl, twistCongr_rfl]

/-- The base step of the compatibilities of `G.map` with the unit: the lax unit and the oplax
counit of `G` cancel. -/
private theorem map_comp_eq_η_ε_comp {X : C} {Z : D} (y : 𝟙_ C ⟶ X) (w : G.obj X ⟶ Z) :
    G.map y ≫ w = Functor.OplaxMonoidal.η G ≫ Functor.LaxMonoidal.ε G ≫ G.map y ≫ w := by
  rw [← Category.assoc (Functor.OplaxMonoidal.η G), Functor.Monoidal.η_ε, Category.id_comp]

/-- The inductive step of the compatibilities of `G.map` with the iterated whiskering by `L`: one
naturality square of the oplax tensorator of `G`. -/
private theorem map_whiskerRight_comp_δ {A B : C} {A' B' : D} (L : C) (u : A ⟶ B)
    (w : G.obj B ⟶ B') (v : G.obj A ⟶ A') (u' : A' ⟶ B') (h : G.map u ≫ w = v ≫ u') :
    G.map (u ▷ L) ≫ Functor.OplaxMonoidal.δ G B L ≫ w ▷ G.obj L =
      (Functor.OplaxMonoidal.δ G A L ≫ v ▷ G.obj L) ≫ u' ▷ G.obj L := by
  rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural_left]
  simp only [Category.assoc]
  rw [← comp_whiskerRight, h, comp_whiskerRight]

/-- **The comparison of the twisted objects carries the action along `G`.** The action
`Stacks.TwistedSections.actMap t j` of a twisted section, carried along `G` and compared with the
action of its image, is the comparison of the tensor powers. At `j = 0` this is where the lax
unit and the oplax counit of `G` cancel, by `CategoryTheory.Functor.Monoidal.η_ε`; the inductive
step is one naturality square of the oplax tensorator. -/
theorem map_actMap {m : ℕ} (t : twistSections F L m) (j : ℕ) :
    G.map (actMap t j) ≫ mapTwistPow G F L (m + j) =
      mapNatTensorPow G L j ≫ actMap (mapTwistSections G t) j := by
  induction j with
  | zero => exact map_comp_eq_η_ε_comp G t _
  | succ j ih => exact map_whiskerRight_comp_δ G L _ _ _ _ ih

/-- **The compatibility the construction rests on: carrying a twisted section along `G` commutes
with the action of a section of any tensor power of `L`.** One oplax naturality square moves `t`
past the tensorator, and the lax unit and oplax counit of `G` cancel against each other. -/
theorem mapTwistSections_actMap {j : ℕ} (a : powSections L j) {m : ℕ}
    (t : twistSections F L m) :
    mapTwistSections G (a ≫ actMap t j) =
      mapPowSections G a ≫ actMap (mapTwistSections G t) j := by
  rw [mapTwistSections, mapPowSections, Functor.map_comp]
  simp only [Category.assoc]
  rw [map_actMap]

/-- **Carrying a twisted section along `G` commutes with multiplication by `s`**, for a section
`s` of `L ^⊗ d` of any degree `d`. -/
theorem mapTwistSections_shiftBySection {d : ℕ} (s : powSections L d) {m : ℕ}
    (t : twistSections F L m) :
    mapTwistSections G (shiftBySection s t) =
      shiftBySection (mapPowSections G s) (mapTwistSections G t) := by
  rw [shiftBySection_eq, shiftBySection_eq, mapTwistSections_actMap]

/-- **Carrying a twisted section along `G` commutes with the `k`-fold multiplication by a section
of a tensor power**, by induction from the single-step compatibility. -/
theorem mapTwistSections_shiftPow {d : ℕ} (s : powSections L d) (k : ℕ)
    (u : twistSections F L 0) :
    mapTwistSections G (shiftPow s k u) =
      shiftPow (mapPowSections G s) k (mapTwistSections G u) := by
  induction k with
  | zero => rw [shiftPow_zero, shiftPow_zero]
  | succ k ih => rw [shiftPow_succ, shiftPow_succ, mapTwistSections_shiftBySection, ih]

/-- **Carrying a twisted section along `G` commutes with the graded action of a section.** -/
theorem mapTwistSections_gsmul {j m : ℕ} (a : powSections L j) (t : twistSections F L m) :
    mapTwistSections G (gsmul a t) = gsmul (mapPowSections G a) (mapTwistSections G t) := by
  rw [gsmul_def, gsmul_def, mapTwistSections_twistCongr, mapTwistSections_actMap]

/-- **The comparison of the tensor powers carries multiplication by a section along `G`.** This
is the companion of `Stacks.TwistedSections.map_actMap` for `Stacks.GradedSections.mulMap`, which
is the same recursion read in the section ring rather than in the twisted module: at `j = 0` the
lax unit and the oplax counit of `G` cancel by `CategoryTheory.Functor.Monoidal.η_ε`, and the
inductive step is one naturality square of the oplax tensorator. -/
theorem map_mulMap {i : ℕ} (y : powSections L i) (j : ℕ) :
    G.map (Stacks.GradedSections.mulMap y j) ≫ mapNatTensorPow G L (i + j) =
      mapNatTensorPow G L j ≫ Stacks.GradedSections.mulMap (mapPowSections G y) j := by
  induction j with
  | zero => exact map_comp_eq_η_ε_comp G y _
  | succ j ih => exact map_whiskerRight_comp_δ G L _ _ _ _ ih

/-- **A product of two sections carried along `G` is the product of their images.** -/
theorem mapPowSections_mul {i j : ℕ} (y : powSections L i) (z : powSections L j) :
    mapPowSections G (Stacks.GradedSections.mul y z) =
      Stacks.GradedSections.mul (mapPowSections G y) (mapPowSections G z) := by
  show Functor.LaxMonoidal.ε G ≫ G.map (z ≫ Stacks.GradedSections.mulMap y j) ≫
      mapNatTensorPow G L (i + j) =
    (Functor.LaxMonoidal.ε G ≫ G.map z ≫ mapNatTensorPow G L j) ≫
      Stacks.GradedSections.mulMap (mapPowSections G y) j
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [map_mulMap]

/-- **The unit section is carried to the unit section.** The lax unit and the oplax counit of `G`
cancel in the other order, which is `CategoryTheory.Functor.Monoidal.ε_η`. -/
theorem mapPowSections_id (M : C) :
    mapPowSections G (L := M) (n := 0) (𝟙 (𝟙_ C)) = 𝟙 (𝟙_ D) := by
  show Functor.LaxMonoidal.ε G ≫ G.map (𝟙 (𝟙_ C)) ≫ Functor.OplaxMonoidal.η G = 𝟙 (𝟙_ D)
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Functor.Monoidal.ε_η]

/-- **A section of a tensor power carried along `G` is its degree-zero twisted reading carried
along `G`, followed by the comparison of the tensor powers.** The two readings of a section of
`L ^⊗ k` — as a homogeneous element of the section ring and as a twisted section of degree zero
of `L ^⊗ k` — differ after `G` only by that comparison, which is an isomorphism. -/
theorem mapPowSections_eq_mapTwistSections {k : ℕ} (x : powSections L k) :
    mapPowSections G x =
      mapTwistSections G (F := natTensorPow L k) (L := L) (m := 0) x ≫
        mapNatTensorPow G L k := by
  have h : mapTwistSections G (F := natTensorPow L k) (L := L) (m := 0) x
      = Functor.LaxMonoidal.ε G ≫ G.map x := by
    show Functor.LaxMonoidal.ε G ≫ G.map x ≫ 𝟙 (G.obj (natTensorPow L k))
      = Functor.LaxMonoidal.ε G ≫ G.map x
    rw [Category.comp_id]
  rw [h, mapPowSections]
  exact (Category.assoc _ _ _).symm

end Comparison

section Additive

variable [Preadditive C] [Preadditive D] [G.Additive]


/-- Carrying twisted sections along `G` is additive. -/
theorem mapTwistSections_add {m : ℕ} (t t' : twistSections F L m) :
    mapTwistSections G (t + t') = mapTwistSections G t + mapTwistSections G t' := by
  rw [mapTwistSections, mapTwistSections, mapTwistSections, G.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- The zero twisted section is carried along `G` to zero. -/
theorem mapTwistSections_zero (m : ℕ) :
    mapTwistSections G (0 : twistSections F L m) = 0 := by
  rw [mapTwistSections, G.map_zero, Limits.zero_comp, Limits.comp_zero]

/-- **Carrying a twisted section along `G`, as a morphism of additive groups.** -/
def mapTwistSectionsHom (m : ℕ) :
    twistSections F L m →+ twistSections (G.obj F) (G.obj L) m where
  toFun := mapTwistSections G
  map_zero' := mapTwistSections_zero G m
  map_add' := mapTwistSections_add G

/-- The additive map `mapTwistSectionsHom G m` sends `t` to `mapTwistSections G t`. -/
@[simp] theorem mapTwistSectionsHom_apply (m : ℕ) (t : twistSections F L m) :
    mapTwistSectionsHom G m t = mapTwistSections G t := rfl

end Additive

section Division

variable [Preadditive C] [(tensorRight L).Additive] [Preadditive D] [G.Additive]
  [(tensorRight (G.obj L)).Additive]


/-- **A power of a section is carried along `G` to the same power of its image.** The powers
satisfy `s ^ (k + 1) = sᵏ · s` in the section ring
(`Stacks.TwistedSections.mul_sectionPow_self`), and `mapPowSections` is multiplicative
(`Stacks.TwistedSections.mapPowSections_mul`) and unital
(`Stacks.TwistedSections.mapPowSections_id`), so one induction on the exponent suffices. -/
theorem mapPowSections_sectionPow {d : ℕ} (s : powSections L d) (m : ℕ) :
    mapPowSections G (sectionPowOfDegree s m) = sectionPowOfDegree (mapPowSections G s) m := by
  induction m with
  | zero =>
      rw [sectionPowOfDegree_zero, sectionPowOfDegree_zero]
      exact mapPowSections_id G L
  | succ m ih =>
      rw [← mul_sectionPow_self, ← mul_sectionPow_self, mapPowSections_mul, ih]

/-- **The iterated multiplication by `s` is carried along `G`**, by induction from the
single-step compatibility. -/
theorem mapTwistSections_shiftIter {d : ℕ} (s : powSections L d) {m : ℕ}
    (t : twistSections F L m) (k : ℕ) :
    mapTwistSections G (shiftIter s t k) =
      shiftIter (mapPowSections G s) (mapTwistSections G t) k := by
  induction k with
  | zero => rw [shiftIter_zero, shiftIter_zero]
  | succ k ih =>
      rw [shiftIter_succ, mapTwistSections_twistCongr, mapTwistSections_shiftBySection, ih,
        shiftIter_succ]

/-- **The divisions by the powers of `s`, when `s` becomes invertible after `G`**: carry the
numerator along `G` and divide there. -/
def monoidalDivision {d : ℕ} (s : powSections L d) [IsIso (mapPowSections G s)] (n : ℕ) :
    twistSections F L (d * n) →+ twistSections (G.obj F) (G.obj L) 0 :=
  (powerDivision (mapPowSections G s) n).comp (mapTwistSectionsHom G (d * n))

/-- The division of `t` by `sⁿ` after `G` is the division of `mapTwistSections G t` by
`(mapPowSections G s)ⁿ`. -/
@[simp] theorem monoidalDivision_apply {d : ℕ} (s : powSections L d)
    [IsIso (mapPowSections G s)] (n : ℕ) (t : twistSections F L (d * n)) :
    monoidalDivision G s n t = powerDivision (mapPowSections G s) n (mapTwistSections G t) := rfl

/-- **The value of the division is the section whose product with `(G s)ⁿ` is the image of the
numerator.** This is Stacks Tag 0B5L's description of its map. -/
@[simp] theorem shiftPow_monoidalDivision {d : ℕ} (s : powSections L d)
    [IsIso (mapPowSections G s)] (n : ℕ) (t : twistSections F L (d * n)) :
    shiftPow (mapPowSections G s) n (monoidalDivision G s n t) = mapTwistSections G t :=
  shiftPow_powerDivision (mapPowSections G s) n (mapTwistSections G t)

/-- **The divisions obtained through `G` are power-invariant.** The action of `sᵏ` is `k` single
multiplications by `s` on both sides, and `mapTwistSections` commutes with each of them. -/
theorem isPowerInvariant_monoidalDivision {d : ℕ} (s : powSections L d)
    [IsIso (mapPowSections G s)] :
    IsPowerInvariantOfDegree s (monoidalDivision G s (F := F)) := by
  intro n k t
  rw [monoidalDivision_apply, monoidalDivision_apply, gsmul_sectionPow_eq_shiftIter,
    mapTwistSections_twistCongr, mapTwistSections_twistCongr, mapTwistSections_shiftIter,
    ← gsmul_sectionPow_eq_shiftIter]
  exact isPowerInvariant_powerDivision (mapPowSections G s) n k (mapTwistSections G t)

variable [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- **Stacks Tag 0B5L's comparison map, with no hypothesis left standing.** For a monoidal
functor `G` after which the section `s` of `L ^⊗ d` is invertible — on a scheme, restriction to
an open inside the nonvanishing locus of `s` — the degree-zero localization `Γ_*(X, F, L)_{(s)}`
of the *global* twisted sections maps to the sections of `F` there, by restricting a numerator
and dividing by the power of `s` in the denominator. The degree `d` is arbitrary. -/
def localizationLiftOfMonoidal {d : ℕ} (s : powSections L d) [IsIso (mapPowSections G s)] :
    sectionAtNonvanishingOpenOfDegree F L s →+ twistSections (G.obj F) (G.obj L) 0 :=
  localizationLiftOfDegree s (monoidalDivision G s) (isPowerInvariant_monoidalDivision G s)

/-- **The value of the comparison map on a fraction** `t / sⁿ`. -/
theorem localizationLiftOfMonoidal_mk {d : ℕ} (s : powSections L d)
    [IsIso (mapPowSections G s)] (n : ℕ) (t : twistSections F L (d * n)) :
    localizationLiftOfMonoidal G s
        (⟨LocalizedModule.mk (DirectSum.of (twistSections F L) (d * n) t)
            (⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ :
              Submonoid.powers (homogeneousSectionOfDegree s)),
          mk_mem_sectionAtNonvanishingOpenOfDegree s n t⟩ :
            sectionAtNonvanishingOpenOfDegree F L s) =
      monoidalDivision G s n t :=
  localizationLiftOfDegree_mk s (monoidalDivision G s) (isPowerInvariant_monoidalDivision G s) n t

/-- **The comparison map is characterized by multiplication by `sⁿ`:** the value on `t / sⁿ` is
the unique section of `G F` whose `n`-fold product with `G s` is the image of `t`. -/
theorem shiftPow_localizationLiftOfMonoidal_mk {d : ℕ} (s : powSections L d)
    [IsIso (mapPowSections G s)] (n : ℕ) (t : twistSections F L (d * n)) :
    shiftPow (mapPowSections G s) n
        (localizationLiftOfMonoidal G s
          (⟨LocalizedModule.mk (DirectSum.of (twistSections F L) (d * n) t)
              (⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ :
                Submonoid.powers (homogeneousSectionOfDegree s)),
            mk_mem_sectionAtNonvanishingOpenOfDegree s n t⟩ :
              sectionAtNonvanishingOpenOfDegree F L s)) =
      mapTwistSections G t := by
  rw [localizationLiftOfMonoidal_mk, shiftPow_monoidalDivision]

end Division

section Composite

variable {D₂ : Type u₃} [Category.{v₃} D₂] [MonoidalCategory D₂] (H : D ⥤ D₂) [H.Monoidal]


/-- The inductive step of the composite comparisons: one naturality square of the tensorator of
`H`, after the tensorator of `G ⋙ H` is unfolded. -/
private theorem comp_δ_whiskerRight {X : C} {X' : D} {X'' : D₂} (L : C) (g : G.obj X ⟶ X')
    (k : H.obj X' ⟶ X'') :
    Functor.OplaxMonoidal.δ (G ⋙ H) X L ≫ (H.map g ≫ k) ▷ (G ⋙ H).obj L =
      H.map (Functor.OplaxMonoidal.δ G X L ≫ g ▷ G.obj L) ≫
        Functor.OplaxMonoidal.δ H X' (G.obj L) ≫ k ▷ H.obj (G.obj L) := by
  rw [Functor.OplaxMonoidal.comp_δ, Functor.map_comp, comp_whiskerRight]
  simp only [Category.assoc, Functor.comp_obj]
  rw [Functor.OplaxMonoidal.δ_natural_left_assoc]

/-- **The comparison of the tensor powers for a composite.** The counit of `G ⋙ H` is
`H.map (η G) ≫ η H` and its tensorator is `H.map (δ G _ _) ≫ δ H _ _`, so the induction is one
naturality square of the tensorator of `H` at each step and no component formula for either
tensorator is used. -/
theorem mapNatTensorPow_comp (L : C) (n : ℕ) :
    mapNatTensorPow (G ⋙ H) L n =
      H.map (mapNatTensorPow G L n) ≫ mapNatTensorPow H (G.obj L) n := by
  induction n with
  | zero =>
      rw [mapNatTensorPow_zero, mapNatTensorPow_zero, mapNatTensorPow_zero]
      exact Functor.OplaxMonoidal.comp_η G H
  | succ n ih =>
      rw [mapNatTensorPow_succ, mapNatTensorPow_succ, ih]
      exact comp_δ_whiskerRight G H L _ _

/-- **The comparison of the twisted objects for a composite.** The same induction as
`Stacks.TwistedSections.mapNatTensorPow_comp` with the identity in place of the counit at the
base, the recursion of `Stacks.TwistedSections.twistPow` starting at `F`. -/
theorem mapTwistPow_comp (F L : C) (m : ℕ) :
    mapTwistPow (G ⋙ H) F L m =
      H.map (mapTwistPow G F L m) ≫ mapTwistPow H (G.obj F) (G.obj L) m := by
  induction m with
  | zero =>
      rw [mapTwistPow_zero, mapTwistPow_zero, mapTwistPow_zero]
      exact ((Category.comp_id _).trans (H.map_id (G.obj F))).symm
  | succ m ih =>
      rw [mapTwistPow_succ, mapTwistPow_succ, ih]
      exact comp_δ_whiskerRight G H L _ _

/-- **Carrying a section of a tensor power along a composite is carrying it along each factor in
turn.** Beyond `Stacks.TwistedSections.mapNatTensorPow_comp` this is the composition law
`CategoryTheory.Functor.LaxMonoidal.comp_ε` for the lax unit. -/
theorem mapPowSections_comp {L : C} {n : ℕ} (a : powSections L n) :
    mapPowSections (G ⋙ H) a = mapPowSections H (mapPowSections G a) := by
  rw [mapPowSections, mapPowSections, mapPowSections, Functor.LaxMonoidal.comp_ε,
    mapNatTensorPow_comp, Functor.map_comp, Functor.map_comp]
  simp only [Functor.comp_map, Category.assoc]

/-- **Carrying a twisted section along a composite is carrying it along each factor in turn.** -/
theorem mapTwistSections_comp {F L : C} {m : ℕ} (t : twistSections F L m) :
    mapTwistSections (G ⋙ H) t = mapTwistSections H (mapTwistSections G t) := by
  rw [mapTwistSections, mapTwistSections, mapTwistSections, Functor.LaxMonoidal.comp_ε,
    mapTwistPow_comp, Functor.map_comp, Functor.map_comp]
  simp only [Functor.comp_map, Category.assoc]

/-- **The hypothesis of `Stacks.TwistedSections.localizationLiftOfMonoidal` for a composite is
its hypothesis for the second factor**, at the section carried along the first. This is how the
construction is moved to a smaller open: `G` restricts to the open on which `s` is already
invertible and `H` restricts further, and nothing about `H` is needed beyond its monoidality.
Not an instance: the hypothesis mentions `G` and `H` only through `mapPowSections`, so instance
search cannot read either functor off the goal. -/
theorem isIso_mapPowSections_comp {L : C} {n : ℕ} (a : powSections L n)
    [IsIso (mapPowSections H (mapPowSections G a))] : IsIso (mapPowSections (G ⋙ H) a) := by
  rw [mapPowSections_comp]; infer_instance

end Composite

section CompositeDivision

variable {D₂ : Type u₃} [Category.{v₃} D₂] [MonoidalCategory D₂] (H : D ⥤ D₂) [H.Monoidal]


variable [Preadditive C] [(tensorRight L).Additive] [Preadditive D] [G.Additive]
  [(tensorRight (G.obj L)).Additive] [Preadditive D₂] [H.Additive]
  [(tensorRight (H.obj (G.obj L))).Additive]

/-- **The division carried along `H` is the division after `H`.** Dividing a twisted section by
`sⁿ` after `G` and then carrying the quotient along `H` gives the same section of `H (G ℱ)` as
dividing after the composite. Both sides have the same `n`-fold product with the image of `s`,
by `Stacks.TwistedSections.mapTwistSections_shiftPow` and
`Stacks.TwistedSections.shiftPow_monoidalDivision`, and multiplication by `sⁿ` is injective
(`Stacks.TwistedSections.bijective_shiftPow`), `s` being invertible after the composite.

This is the shrinking step: for `G` the restriction to an open on which `s` is invertible and `H`
a further restriction, it says the comparison map over the smaller open is the restriction of the
comparison map over the larger one — with no hypothesis on `H` beyond its monoidality, and no
component formula for any tensorator. -/
theorem mapTwistSections_monoidalDivision {d : ℕ} (s : powSections L d)
    [IsIso (mapPowSections G s)] [IsIso (mapPowSections H (mapPowSections G s))]
    (n : ℕ) (t : twistSections F L (d * n)) :
    mapTwistSections H (monoidalDivision G s n t) =
      monoidalDivision H (mapPowSections G s) n (mapTwistSections G t) := by
  refine (bijective_shiftPow (mapPowSections H (mapPowSections G s))
    (F := H.obj (G.obj F)) n).1 ?_
  rw [← mapTwistSections_shiftPow, shiftPow_monoidalDivision, shiftPow_monoidalDivision]

variable [BraidedCategory C] [HasTrivialSelfBraiding L]

omit [(tensorRight (H.obj (G.obj L))).Additive] [BraidedCategory C]
  [HasTrivialSelfBraiding L] in
/-- **The division after a composite is the division after the first factor, carried along the
second.** Both sides have the same `n`-fold product with the image of `s` after the composite, by
`Stacks.TwistedSections.shiftPow_monoidalDivision` on the left and, on the right, by
`Stacks.TwistedSections.mapTwistSections_shiftPow` followed by the same; the two spellings of the
twice-carried section and numerator are reconciled by `mapPowSections_comp` and
`mapTwistSections_comp`, and multiplication by that power is injective
(`Stacks.TwistedSections.bijective_shiftPow`).

This is the shrinking step in its primitive form: for `G` the restriction to an open on which `s`
is invertible and `H` a further restriction, it says the division over the smaller open is the
restriction of the division over the larger one — with no hypothesis on `H` beyond its
monoidality, and no component formula for any tensorator. -/
theorem monoidalDivision_comp [(tensorRight ((G ⋙ H).obj L)).Additive] {d : ℕ}
    (s : powSections L d) [IsIso (mapPowSections G s)] [IsIso (mapPowSections (G ⋙ H) s)]
    (n : ℕ) (t : twistSections F L (d * n)) :
    monoidalDivision (G ⋙ H) s n t = mapTwistSections H (monoidalDivision G s n t) := by
  refine (bijective_shiftPow (mapPowSections (G ⋙ H) s)
    (F := (G ⋙ H).obj F) n).1 ?_
  rw [shiftPow_monoidalDivision, mapPowSections_comp, ← mapTwistSections_shiftPow,
    shiftPow_monoidalDivision, ← mapTwistSections_comp]

omit [(tensorRight (H.obj (G.obj L))).Additive] in
/-- **Stacks Tag 0B5L's comparison map after a composite is the comparison map after the first
factor, carried along the second** — as an identity of maps on the *whole* degree-zero
localization, not only on the fractions. The two division families agree by
`monoidalDivision_comp`, and `Stacks.TwistedSections.localizationLift_congr` together with
`localizationLift_comp` promotes that to the lifts.

For two nested restrictions of a scheme this is the statement that the comparison map over the
smaller open is the restriction of the comparison map over the larger one, which is the content
of Stacks Tag 0B5I's compatibility field for a fixed section. -/
theorem localizationLiftOfMonoidal_comp [(tensorRight ((G ⋙ H).obj L)).Additive] {d : ℕ}
    (s : powSections L d) [IsIso (mapPowSections G s)] [IsIso (mapPowSections (G ⋙ H) s)] :
    localizationLiftOfMonoidal (G ⋙ H) s =
      (mapTwistSectionsHom H (F := G.obj F) (L := G.obj L) 0).comp
        (localizationLiftOfMonoidal G s) := by
  refine Eq.trans ?_ (localizationLift_comp
    (mapTwistSectionsHom H (F := G.obj F) (L := G.obj L) 0) s (monoidalDivision G s)
    (isPowerInvariant_monoidalDivision G s))
  exact localizationLift_congr s _ _
    fun n => AddMonoidHom.ext fun t => monoidalDivision_comp G H s n t

end CompositeDivision

end Stacks.TwistedSections

end
