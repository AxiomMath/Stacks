module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

@[expose] public section

/-
# Problem Description

Stacks Tag 08FM (Lemma 21.44.2), in the section "Strictly perfect complexes"
(Tag 08FK).

Throughout, fix a ringed site `(C, O)`, i.e. a site `C` together with a sheaf of rings
`O` on `C`. All complexes below are cochain complexes of `O`-modules.

We formalize:

* Definition 1: a direct summand of a finite free `O`-module.
* Definition 2: a strictly perfect complex (Tag 08FL): bounded, and each term is a direct
  summand of a finite free `O`-module.
* Definition 3: a morphism of complexes (this is just a morphism in
  `CochainComplex (SheafOfModules.{m} R) ℤ`).
* Definition 4: the cone of a morphism of complexes (Mathlib's
  `CochainComplex.mappingCone`).

Main statement (Tag 08FM): if `f : A ⟶ B` is a morphism of complexes of `O`-modules with
`A` and `B` strictly perfect, then the cone `C(f)` is strictly perfect.

The Stacks proof reads in full: "This is immediate from the definitions." Boundedness:
since `A` and `B` are bounded, `C(f)^n = A^{n+1} ⊕ B^n = 0` for all but finitely many `n`.
Term condition: a direct sum of two modules, each a direct summand of a finite free
`O`-module, is again a direct summand of a finite free `O`-module.
-/

open CategoryTheory CategoryTheory.Limits

-- We work over a ringed site `(C, O)`: a site `C` with a sheaf of rings `R = O`.
-- The category of `O`-modules is `SheafOfModules.{m} R`; it is a preadditive (in fact
-- abelian) category. The structure-sheaf-as-a-module is `SheafOfModules.unit R`, and the free
-- `O`-module on an index type `I` is `SheafOfModules.free I`.
--
-- The instances below (`HasWeakSheafify`, `WEqualsLocallyBijective`, `HasSheafCompose`) are
-- the standard mild hypotheses on the ringed site needed in order to form free `O`-modules.
--
-- Universes. All four are independent parameters: the objects `u` and the morphisms `v` of
-- the site, the universe `w` of the sections of the structure sheaf, and the universe `m` of
-- the sections of the modules.
--
-- That `m` is genuinely free costs one `ULift`, for the following reason. The sections of the
-- free module on `I` over a ring whose sections lie in `Type w` are a direct sum of copies of
-- that ring, so `SheafOfModules.free : (I : Type w) → SheafOfModules.{w} R` lands at the ring
-- universe and at no other; likewise `SheafOfModules.unit R : SheafOfModules.{w} R`. A finite
-- free `O`-module therefore does *not* live in `SheafOfModules.{m} R` unless `w ≤ m`, and a
-- module `F : SheafOfModules.{m} R` cannot be compared with one directly. The comparison is
-- made instead in `SheafOfModules.{max m w} R`, after raising the sections of both sides with
-- `Stacks.SheafOfModules.moduleULift`, which is fully faithful; by
-- `isDirectSummandOfFiniteFree_iff_free` the resulting condition is the ordinary retract
-- condition whenever `m` and `w` agree, so nothing is lost at `m = w` and the predicate is
-- available at every other `m` as well.
--
-- `O^{⊕n}` is spelled `SheafOfModules.free (ULift.{w} (Fin n))`: the index type must be the
-- `n`-element type in `Type w`, and `Fin n` is in `Type 0`.
universe u v w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

-- Main Definition(s)

/-- **Definition 1 (Direct summand of a finite free module).**
An `O`-module `F` is a *direct summand of a finite free `O`-module* if there exist an
integer `n ≥ 0` and `O`-module morphisms `i : F ⟶ O^{⊕n}` and `r : O^{⊕n} ⟶ F` with
`r ∘ i = id_F`. Here `O^{⊕n}` is the free `O`-module on `n` generators,
`SheafOfModules.free (ULift (Fin n))`.

This is the "Equivalently" formulation in Definition 1: the existence of such `i`, `r`
with `r ∘ i = id_F` is equivalent to the existence of an `O`-module `G` and an isomorphism
`F ⊕ G ≅ O^{⊕n}`.

The sections of `F` live in `Type m` and those of `O^{⊕n}` in `Type w`, so the two are
compared in `SheafOfModules.{max m w} R`, after raising the sections of each with
`Stacks.SheafOfModules.moduleULift`. For `m = w` this is the plain retract condition
(`isDirectSummandOfFiniteFree_iff_free`); see the note on universes above. -/
def IsDirectSummandOfFiniteFree (F : SheafOfModules.{m} R) : Prop :=
  ∃ (n : ℕ)
      (i : (Stacks.SheafOfModules.moduleULift.{w, m} R).obj F ⟶
        (Stacks.SheafOfModules.moduleULift.{m, w} R).obj
          (SheafOfModules.free (ULift.{w} (Fin n))))
      (r : (Stacks.SheafOfModules.moduleULift.{m, w} R).obj
          (SheafOfModules.free (ULift.{w} (Fin n))) ⟶
        (Stacks.SheafOfModules.moduleULift.{w, m} R).obj F),
    i ≫ r = 𝟙 _

-- Helper lemmas (the natural decomposition of the term condition).

omit [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **Helper 0 (the predicate at equal universes).**
When the sections of the modules and the sections of the structure sheaf live in the same
universe, Definition 1 is the plain condition that `F` be a retract of `O^{⊕n}`: the universe
lift is then an endofunctor of `SheafOfModules.{w} R`, and it is fully faithful, so a
retraction upstairs is the lift of a retraction downstairs.

This is the form in which the ringed-site consumers of the predicate use it. -/
lemma isDirectSummandOfFiniteFree_iff_free (F : SheafOfModules.{w} R) :
    IsDirectSummandOfFiniteFree R F ↔
      ∃ (n : ℕ) (i : F ⟶ SheafOfModules.free (ULift.{w} (Fin n)))
        (r : SheafOfModules.free (ULift.{w} (Fin n)) ⟶ F), i ≫ r = 𝟙 F := by
  have L : (Stacks.SheafOfModules.moduleULift.{w, w} R).FullyFaithful :=
    Stacks.SheafOfModules.moduleULiftFullyFaithful R
  refine ⟨fun ⟨n, i, r, hir⟩ =>
    ⟨n, L.preimage i, L.preimage r, L.map_injective (by simp [hir])⟩, fun ⟨n, i, r, hir⟩ => ?_⟩
  refine ⟨n, (Stacks.SheafOfModules.moduleULift.{w, w} R).map i,
    (Stacks.SheafOfModules.moduleULift.{w, w} R).map r, ?_⟩
  rw [← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]

omit [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **Helper 1 (transport along an iso).**
`IsDirectSummandOfFiniteFree` is invariant under isomorphism: if `F ≅ F'` and `F'` is a
direct summand of a finite free `O`-module, then so is `F`.

Argument: given `i' : F' ⟶ O^{⊕n}`, `r' : O^{⊕n} ⟶ F'` with `i' ≫ r' = 𝟙 F'`, and an iso
`e : F ≅ F'`, take `i := e.hom ≫ i'` and `r := r' ≫ e.inv` — with `e` first carried up by the
universe lift, which is where the comparison happens. Then
`i ≫ r = e.hom ≫ (i' ≫ r') ≫ e.inv = e.hom ≫ 𝟙 ≫ e.inv = e.hom ≫ e.inv = 𝟙 F`. -/
lemma IsDirectSummandOfFiniteFree.of_iso {F F' : SheafOfModules.{m} R}
    (e : F ≅ F') (h : IsDirectSummandOfFiniteFree R F') :
    IsDirectSummandOfFiniteFree R F := by
  obtain ⟨n, i', r', hir⟩ := h
  refine ⟨n, (Stacks.SheafOfModules.moduleULift.{w, m} R).map e.hom ≫ i',
    r' ≫ (Stacks.SheafOfModules.moduleULift.{w, m} R).map e.inv, ?_⟩
  -- `(L e.hom ≫ i') ≫ (r' ≫ L e.inv) = L e.hom ≫ (i' ≫ r') ≫ L e.inv = L (e.hom ≫ e.inv)`.
  simp [reassoc_of% hir]

omit [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **Helper 2 (biproduct of two summands of finite frees).**
If `F` and `G` are each direct summands of finite free `O`-modules, then so is `F ⊞ G`.

Argument: say `F` retracts from `O^{⊕a}` via `iF, rF` (with `iF ≫ rF = 𝟙`) and `G` from
`O^{⊕b}` via `iG, rG`, both after the universe lift. The lift is additive, hence preserves
binary biproducts, so it carries `F ⊞ G` to the biproduct of the lifts and `O^{⊕a} ⊞ O^{⊕b}`
to the biproduct of theirs. Then `biprod.map iF iG` and `biprod.map rF rG` compose to
`biprod.map (iF ≫ rF) (iG ≫ rG) = biprod.map 𝟙 𝟙 = 𝟙`. Finally
`O^{⊕a} ⊞ O^{⊕b} ≅ O^{⊕a} ⨿ O^{⊕b} ≅ O^{⊕(a+b)}` (via `biprod.isoCoprod`, `freeSumIso`, and
`freeFunctor` applied to the equivalence `ULift (Fin a) ⊕ ULift (Fin b) ≃ ULift (Fin (a+b))`
built from `finSumFinEquiv`), so `F ⊞ G` is a direct summand of `O^{⊕(a+b)}`. -/
lemma IsDirectSummandOfFiniteFree.biprod {F G : SheafOfModules.{m} R}
    [HasBinaryBiproduct F G]
    (hF : IsDirectSummandOfFiniteFree R F) (hG : IsDirectSummandOfFiniteFree R G) :
    IsDirectSummandOfFiniteFree R (F ⊞ G) := by
  obtain ⟨a, iF, rF, hF'⟩ := hF
  obtain ⟨b, iG, rG, hG'⟩ := hG
  have : HasBinaryBiproduct (SheafOfModules.free (R := R) (ULift.{w} (Fin a)))
      (SheafOfModules.free (R := R) (ULift.{w} (Fin b))) :=
    HasBinaryBiproduct.of_hasBinaryProduct _ _
  -- `γ : O^{⊕a} ⊞ O^{⊕b} ≅ O^{⊕(a+b)}`, downstairs at the ring universe.
  have γ : SheafOfModules.free (R := R) (ULift.{w} (Fin a))
        ⊞ SheafOfModules.free (R := R) (ULift.{w} (Fin b))
      ≅ SheafOfModules.free (R := R) (ULift.{w} (Fin (a + b))) :=
    biprod.isoCoprod _ _
      ≪≫ SheafOfModules.freeSumIso (R := R) (ULift.{w} (Fin a)) (ULift.{w} (Fin b))
      ≪≫ (SheafOfModules.freeFunctor (R := R)).mapIso
        ((Equiv.ulift.sumCongr Equiv.ulift).trans
          (finSumFinEquiv.trans Equiv.ulift.symm)).toIso
  let L := Stacks.SheafOfModules.moduleULift.{w, m} R
  let L' := Stacks.SheafOfModules.moduleULift.{m, w} R
  let : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBiproducts L
  let : PreservesBinaryBiproducts L' := preservesBinaryBiproducts_of_preservesBiproducts L'
  have hmap : biprod.map iF iG ≫ biprod.map rF rG = 𝟙 _ := by
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [hF', hG']
  refine ⟨a + b,
    (L.mapBiprod F G).hom ≫ biprod.map iF iG ≫ (L'.mapBiprod _ _).inv ≫ (L'.mapIso γ).hom,
    (L'.mapIso γ).inv ≫ (L'.mapBiprod _ _).hom ≫ biprod.map rF rG ≫ (L.mapBiprod F G).inv,
    ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (biprod.map iF iG), hmap, Category.id_comp, Iso.hom_inv_id]

/-- **Definition 2 (Strictly perfect complex — Stacks Tag 08FL).**
A cochain complex `E` of `O`-modules is *strictly perfect* if:
1. (boundedness) `E.X i = 0` for all but finitely many `i ∈ ℤ`; and
2. for every `i ∈ ℤ`, the `O`-module `E.X i` is a direct summand of a finite free
   `O`-module (Definition 1).

This is the global direct-summand condition of Tag 08FL; it is *not* the (in general
weaker and inequivalent) "finite locally free" condition. -/
structure IsStrictlyPerfect (E : CochainComplex (SheafOfModules.{m} R) ℤ) : Prop where
  /-- Boundedness: only finitely many terms of the complex are nonzero. -/
  bounded : {i : ℤ | ¬ IsZero (E.X i)}.Finite
  /-- Each term is a direct summand of a finite free `O`-module. -/
  termDirectSummand : ∀ i, IsDirectSummandOfFiniteFree R (E.X i)

-- Definition 3 (Morphism of complexes). A morphism of complexes
-- `f : A ⟶ B` is simply a morphism in the category `CochainComplex (SheafOfModules.{m} R) ℤ`,
-- i.e. a family `f^i : A.X i ⟶ B.X i` commuting with the differentials.

-- Definition 4 (Cone of a morphism of complexes). The cone `C(f)` of a morphism of
-- complexes `f : A ⟶ B` is `CochainComplex.mappingCone f`, with
-- `C(f).X n ≅ A.X (n+1) ⊕ B.X n`. (Any standard sign convention for the cone differential
-- yields the same conclusion below; the sign convention does not affect the statement.)
-- The hypothesis `[HomologicalComplex.HasHomotopyCofiber f]` records that the cone exists;
-- this always holds for `O`-modules, since `SheafOfModules.{m} R` is an abelian category.

-- Main Statement(s)

omit [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **Statement 1 (Stacks Tag 08FM).**
Let `(C, O)` be a ringed site, and let `f : A ⟶ B` be a morphism of complexes of
`O`-modules. If `A` and `B` are both strictly perfect (Definition 2), then the cone
`C(f) = CochainComplex.mappingCone f` (Definition 4) is strictly perfect.

Proof sketch (Tag 08FM, "immediate from the definitions"):
* Boundedness. By `CochainComplex.mappingCone.isZero_X_iff`,
  `IsZero ((mappingCone f).X i) ↔ IsZero (A.X (i+1)) ∧ IsZero (B.X i)`, so
  `{i | ¬ IsZero ((mappingCone f).X i)} ⊆ {i | ¬ IsZero (A.X (i+1))} ∪ {i | ¬ IsZero (B.X i)}`.
  The second set is `hB.bounded`; the first is the preimage of `hA.bounded` under
  `i ↦ i+1`, hence finite. A finite union of finite sets is finite.
* Term condition. Fix `i`. We have `(mappingCone f).X i ≅ A.X (i+1) ⊞ B.X i` via
  `HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i+1) rfl` (`mappingCone f` is
  definitionally `homotopyCofiber f`, and for `CochainComplex … ℤ` the relation `c.Rel i j`
  is `i+1 = j`). By Helper 2, `A.X (i+1) ⊞ B.X i` is a direct summand of a finite free
  module (since `A.X (i+1)` and `B.X i` are, by `hA.termDirectSummand`,
  `hB.termDirectSummand`); by Helper 1 (transport along that iso) so is
  `(mappingCone f).X i`. -/
@[stacks 08FM]
theorem mappingCone_isStrictlyPerfect
    {A B : CochainComplex (SheafOfModules.{m} R) ℤ} (f : A ⟶ B)
    [HomologicalComplex.HasHomotopyCofiber f]
    (hA : IsStrictlyPerfect R A) (hB : IsStrictlyPerfect R B) :
    IsStrictlyPerfect R (CochainComplex.mappingCone f) := by
  refine ⟨?_, fun i => ?_⟩
  · -- (1) Boundedness.
    -- `{i | ¬ IsZero ((mappingCone f).X i)} ⊆ ((·+1) ⁻¹' {i | ¬ IsZero (A.X i)}) ∪
    --    {i | ¬ IsZero (B.X i)}`, by `mappingCone.isZero_X_iff` (contrapositive: not-zero
    -- of the cone term forces not-zero of `A.X (i+1)` or of `B.X i`).
    -- RHS finite: `(hA.bounded).preimage (by …injective…)` ∪ `hB.bounded`.
    -- Then `Set.Finite.subset`.
    apply Set.Finite.subset
      (s := ((fun i : ℤ => i + 1) ⁻¹' {i | ¬ IsZero (A.X i)}) ∪ {i | ¬ IsZero (B.X i)})
    · exact (hA.bounded.preimage (fun a _ b _ h => by simpa using h)).union hB.bounded
    · intro i hi
      simp only [Set.mem_ofPred_eq] at hi
      simpa using not_and_or.mp ((CochainComplex.mappingCone.isZero_X_iff f i).not.mp hi)
  · -- (2) Term condition.
    have : HasBinaryBiproduct (A.X (i + 1)) (B.X i) :=
      HasBinaryBiproduct.of_hasBinaryProduct _ _
    -- `(mappingCone f).X i ≅ A.X (i+1) ⊞ B.X i`.
    have e : (CochainComplex.mappingCone f).X i ≅ A.X (i + 1) ⊞ B.X i :=
      HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)
    -- transport the biprod's summand structure (Helper 2) along `e` (Helper 1).
    exact IsDirectSummandOfFiniteFree.of_iso R e
      (IsDirectSummandOfFiniteFree.biprod R (hA.termDirectSummand (i + 1))
        (hB.termDirectSummand i))
