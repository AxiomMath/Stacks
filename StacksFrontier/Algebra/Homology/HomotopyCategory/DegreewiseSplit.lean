module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus

import StacksCore.Tactic.StacksAttribute

/-!
# Cones and termwise split sequences

Let `𝒜` be an additive category, let `Comp(𝒜) = CochainComplex 𝒜 ℤ` be the category of
`ℤ`-indexed cochain complexes of `𝒜` and let `K(𝒜) = HomotopyCategory 𝒜 (ComplexShape.up ℤ)` be
its homotopy category. There are two ways of attaching a triangle of `K(𝒜)` to data in `Comp(𝒜)`:

* from a morphism `φ : K ⟶ L`, the *cone triangle*
  `K ⟶ L ⟶ C(φ) --(-p)--> K⟦1⟧`, where `C(φ)ⁿ = Kⁿ⁺¹ ⊕ Lⁿ` is the mapping cone
  (`CochainComplex.mappingCone.triangle`);
* from a *termwise split short exact sequence* `S : A --α--> B --β--> C`, that is a short complex
  of complexes together with a splitting `σ n` of each of its degreewise evaluations, the
  triangle `A ⟶ B ⟶ C --δ--> A⟦1⟧` with `δⁿ = πⁿ⁺¹ ∘ d_Bⁿ ∘ sⁿ`
  (`CochainComplex.triangleOfDegreewiseSplit`).

This file compares the two constructions and proves replacement lemmas for morphisms of
complexes.

Two *replacement* lemmas say that a morphism of complexes may always be improved, up to homotopy
equivalence, to a termwise split injection or surjection: every `α : K ⟶ L` factors as
`α = α' ≫ π` with `α'` termwise split injective and `π` admitting a section which is a homotopy
inverse, and dually as `α = i ≫ α'` with `α'` termwise split surjective and `i` admitting a
retraction which is a homotopy inverse. The witnesses are `L ⊞ C(𝟙 K)` and `K ⊞ C(𝟙 L)⟦-1⟧`,
whose second summands are contractible, so the vanishing bounds of `K` and `L` are inherited and
bounded below, bounded above and bounded complexes stay in their class. Iterating the first
lemma replaces a whole sequence of composable morphisms by a sequence of termwise split
injections.

The *comparison* is exact, in both directions and over the identity in the outer positions. The
rotation of a cone triangle **is** the triangle of a termwise split sequence, namely of
`0 → L → C(φ) → K⟦1⟧ → 0` split by the biproduct decomposition of the cone, whose connecting
morphism is `-φ⟦1⟧` on the nose; conversely the inverse rotation of the triangle of a termwise
split sequence is the cone triangle of its own first map, and the cone triangle of the first map
`α` of a termwise split sequence is isomorphic in `K(𝒜)` to the triangle of that sequence, by an
isomorphism which is the identity on `A` and on `B` and whose third component is the canonical
map `C(α) ⟶ C` given by the projection onto `Bⁿ` followed by `βⁿ`. Every cone triangle is
therefore, over the identity of its first object, the triangle of a termwise split sequence.

Finally two lemmas about morphisms rather than triangles: a morphism of cone triangles in `K(𝒜)`
which is invertible in two positions is invertible in the third, and a composition of two
morphisms of `K(𝒜)` through the middle term of a termwise split sequence vanishes as soon as it
vanishes on both sides of the splitting.

## Main results

* `CochainComplex.exists_factorization_isDegreewiseSplitMono`: the factorization of a morphism
  through a termwise split injection.
* `CochainComplex.exists_isDegreewiseSplitEpi_factorization`: the dual factorization through a
  termwise split surjection.
* `CochainComplex.exists_composableArrows_isDegreewiseSplitMono`: the replacement of a sequence
  of composable morphisms by termwise split injections.
* `CochainComplex.mappingCone.isIso₃_of_isIso₁₂`: two out of three for a morphism of cone
  triangles in `K(𝒜)`.
* `CochainComplex.exists_triangleh_iso_trianglehOfDegreewiseSplit_and_exists_iso_triangleh`: the
  comparison of the two constructions of a triangle of `K(𝒜)`, over the identity in the outer
  positions.
* `CochainComplex.exists_triangleOfDegreewiseSplit_invRotate_iso_mappingCone_triangle`: the
  inverse rotation of the triangle of a termwise split sequence is the cone triangle of its own
  first map.
* `HomotopyCategory.comp_eq_zero_of_degreewiseSplit`: the vanishing of a composition through a
  termwise split sequence.
* `exists_homotopic_comm_of_isTermwiseSplitInjection`,
  `exists_homotopic_comm_of_isTermwiseSplitSurjection`: a square commuting up to homotopy can be
  made to commute on the nose when one of its sides is termwise split.
* `trianglehOfDegreewiseSplit_iso_of_identity`: the triangle of a termwise split sequence does not
  depend on the splittings.
* `exists_factorThrough_mappingCone`, `exists_factor_through_shifted_mappingCone`: if `f ≫ g` is
  null homotopic, then `g` factors through the cone of `f` and `f` through the shifted cone of
  `g`.
* `CochainComplex.mappingCone_homology_exact_cone`,
  `CochainComplex.mappingCone_homology_exact_source`: exactness of the long exact cohomology
  sequence of the shifted cone.

## Implementation notes

Additivity of `𝒜` is spelled out in the form each statement uses: `Preadditive 𝒜` alone where
only homotopies and connecting morphisms occur, together with `HasBinaryBiproducts 𝒜` where cones
are built, and with `HasZeroObject 𝒜` in addition where the pretriangulated structure of `K(𝒜)`
is used.

"Termwise split injection" and "termwise split surjection" in the sense of [Stacks, Tag 014G]
(each component is isomorphic to the inclusion of, resp. the projection onto, a direct summand)
are `HomologicalComplex.Hom.IsDegreewiseSummandInclusion` and
`HomologicalComplex.Hom.IsDegreewiseSummandProjection`. The statements below mostly use the
weaker predicates `HomologicalComplex.Hom.IsDegreewiseSplitMono` and
`HomologicalComplex.Hom.IsDegreewiseSplitEpi` (each component is a split monomorphism, resp.
epimorphism), which agree with the Stacks notions when idempotents split, e.g. in an abelian
category, but are strictly weaker in a general additive category: there a split monomorphism
need not have a complementary summand. In particular the factorization lemmas below conclude
only that the improved morphism is degreewise split mono, resp. epi.

"Is a homotopy equivalence" is either Mathlib's morphism property
`HomologicalComplex.homotopyEquivalences` or, for a morphism of `K(𝒜)`, invertibility, the two
readings agreeing by `HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences`.

The vanishing bounds of the two factorizations are stated degree by degree, the shift by one
degree coming from the term of the cone in degree `n` involving a term of the original complex in
degree `n ± 1`; they imply the statements about bounded below and bounded above complexes by
`CochainComplex.isStrictlyGE_of_ge` and `CochainComplex.isStrictlyLE_of_le`.

Signs. `CochainComplex.mappingCone.triangle φ` has third map the one induced by `-fst φ`, and
`Pretriangulated.Triangle.invRotate` produces a first map carrying a sign of its own; the
statements below use both of Mathlib's conventions unchanged, so that the comparisons are the
identity on the outer objects.

## References

* [Stacks, Tag 013N], [Stacks, Tag 0642], [Stacks, Tag 014M] (the replacement lemmas)
* [Stacks, Tag 014K], [Stacks, Tag 086L] (morphisms of cone triangles)
* [Stacks, Tag 014L], [Stacks, Tag 014N], [Stacks, Tag 014O] (the comparison)
* [Stacks, Tag 011J] (the connecting morphism `δ`)
* [Stacks, Tag 014G] (termwise split injections and surjections)
* [Stacks, Definition 0104] (additive category)
-/

@[expose] public section

/-! ### Termwise split injections and surjections -/

namespace HomologicalComplex.Hom

open CategoryTheory

variable {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- A morphism of complexes `α : K ⟶ L` is a *degreewise split monomorphism* if each component
`α.f n` is a split monomorphism, i.e. admits a retraction. The retractions are not required to be
compatible with the differentials, so that such an `α` need not be a split monomorphism of
complexes.

This is weaker than a termwise split injection in the sense of [Stacks, Tag 014G]
(`HomologicalComplex.Hom.IsDegreewiseSummandInclusion`), which also asks for the complementary
direct summand to exist in the category; the two notions agree when idempotents split
(`HomologicalComplex.Hom.isDegreewiseSummandInclusion_iff_isDegreewiseSplitMono`). -/
public def IsDegreewiseSplitMono (α : K ⟶ L) : Prop :=
  ∀ n, IsSplitMono (α.f n)

/-- A morphism of complexes `β : K ⟶ L` is a *degreewise split epimorphism* if each component
`β.f n` is a split epimorphism, i.e. admits a section. The sections are not required to be
compatible with the differentials, so that such a `β` need not be a split epimorphism of
complexes.

This is weaker than a termwise split surjection in the sense of [Stacks, Tag 014G]
(`HomologicalComplex.Hom.IsDegreewiseSummandProjection`), which also asks for the complementary
direct summand to exist in the category; the two notions agree when idempotents split
(`HomologicalComplex.Hom.isDegreewiseSummandProjection_iff_isDegreewiseSplitEpi`). -/
public def IsDegreewiseSplitEpi (β : K ⟶ L) : Prop :=
  ∀ n, IsSplitEpi (β.f n)

end HomologicalComplex.Hom

/-! ### Termwise split injections and surjections in the sense of Stacks -/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- A morphism `f : X ⟶ Y` is isomorphic, as an arrow, to the inclusion `X' ⟶ X' ⊞ Z` of a
direct summand if and only if there are an object `Z` and an isomorphism `Y ≅ X ⊞ Z` under which
`f` becomes `biprod.inl`. -/
public lemma exists_nonempty_arrow_iso_biprod_inl_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (X' Z : C), Nonempty (Arrow.mk f ≅ Arrow.mk (biprod.inl : X' ⟶ X' ⊞ Z))) ↔
      ∃ (Z : C) (e : Y ≅ X ⊞ Z), f ≫ e.hom = biprod.inl := by
  constructor
  · rintro ⟨X', Z, ⟨e⟩⟩
    refine ⟨Z, Arrow.rightFunc.mapIso e ≪≫
      biprod.mapIso (Arrow.leftFunc.mapIso e).symm (Iso.refl Z), ?_⟩
    have h : f ≫ e.hom.right = e.hom.left ≫ biprod.inl := (Arrow.w_mk_right e.hom).symm
    change f ≫ e.hom.right ≫ biprod.map e.inv.left (𝟙 Z) = biprod.inl
    rw [reassoc_of% h, biprod.inl_map, Arrow.hom_inv_id_left_assoc]
    rfl
  · rintro ⟨Z, e, h⟩
    exact ⟨X, Z, ⟨Arrow.isoMk (Iso.refl X) e (by simp [h])⟩⟩

/-- A morphism `f : Y ⟶ X` is isomorphic, as an arrow, to the projection `X' ⊞ Z ⟶ X'` onto a
direct summand if and only if there are an object `Z` and an isomorphism `Y ≅ X ⊞ Z` under which
`f` becomes `biprod.fst`. -/
public lemma exists_nonempty_arrow_iso_biprod_fst_iff {X Y : C} (f : Y ⟶ X) :
    (∃ (X' Z : C), Nonempty (Arrow.mk f ≅ Arrow.mk (biprod.fst : X' ⊞ Z ⟶ X'))) ↔
      ∃ (Z : C) (e : Y ≅ X ⊞ Z), e.hom ≫ biprod.fst = f := by
  constructor
  · rintro ⟨X', Z, ⟨e⟩⟩
    refine ⟨Z, Arrow.leftFunc.mapIso e ≪≫
      biprod.mapIso (Arrow.rightFunc.mapIso e).symm (Iso.refl Z), ?_⟩
    have h : e.hom.left ≫ biprod.fst = f ≫ e.hom.right := Arrow.w_mk_right e.hom
    change (e.hom.left ≫ biprod.map e.inv.right (𝟙 Z)) ≫ biprod.fst = f
    rw [Category.assoc, biprod.map_fst, reassoc_of% h]
    simp
  · rintro ⟨Z, e, h⟩
    exact ⟨X, Z, ⟨Arrow.isoMk e (Iso.refl X) (by simp [h])⟩⟩

end CategoryTheory.Limits

namespace HomologicalComplex.Hom

open CategoryTheory Limits

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] {ι : Type*}
  {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- A morphism of complexes `α : K ⟶ L` is a *termwise split injection* in the sense of
[Stacks, Tag 014G] if each component `α.f n : K.X n ⟶ L.X n` is isomorphic, as an arrow, to the
inclusion `biprod.inl : X ⟶ X ⊞ Z` of a direct summand, for some objects `X` and `Z` of the
category. The complementary summand `Z` is required to exist in the category; this is stronger
than `IsDegreewiseSplitMono` unless idempotents split
(`isDegreewiseSummandInclusion_iff_isDegreewiseSplitMono`, in
`StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSummand`). -/
@[stacks 014G "termwise split injection: each component is isomorphic, as an arrow, to the
inclusion `X ⟶ X ⊞ Z` of a direct summand"]
public def IsDegreewiseSummandInclusion (α : K ⟶ L) : Prop :=
  ∀ n, ∃ (X Z : C), Nonempty (Arrow.mk (α.f n) ≅ Arrow.mk (biprod.inl : X ⟶ X ⊞ Z))

/-- A morphism of complexes `β : K ⟶ L` is a *termwise split surjection* in the sense of
[Stacks, Tag 014G] if each component `β.f n : K.X n ⟶ L.X n` is isomorphic, as an arrow, to the
projection `biprod.fst : X ⊞ Z ⟶ X` onto a direct summand, for some objects `X` and `Z` of the
category. The complementary summand `Z` is required to exist in the category; this is stronger
than `IsDegreewiseSplitEpi` unless idempotents split
(`isDegreewiseSummandProjection_iff_isDegreewiseSplitEpi`, in
`StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSummand`). -/
@[stacks 014G "termwise split surjection: each component is isomorphic, as an arrow, to the
projection `X ⊞ Z ⟶ X` onto a direct summand"]
public def IsDegreewiseSummandProjection (β : K ⟶ L) : Prop :=
  ∀ n, ∃ (X Z : C), Nonempty (Arrow.mk (β.f n) ≅ Arrow.mk (biprod.fst : X ⊞ Z ⟶ X))

/-- `α` is a termwise split injection iff in each degree there are an object `Z` and an
isomorphism `L.X n ≅ K.X n ⊞ Z` under which `α.f n` is `biprod.inl`. -/
public lemma isDegreewiseSummandInclusion_iff (α : K ⟶ L) :
    α.IsDegreewiseSummandInclusion ↔
      ∀ n, ∃ (Z : C) (e : L.X n ≅ K.X n ⊞ Z), α.f n ≫ e.hom = biprod.inl :=
  forall_congr' fun n => exists_nonempty_arrow_iso_biprod_inl_iff (α.f n)

/-- `β` is a termwise split surjection iff in each degree there are an object `Z` and an
isomorphism `K.X n ≅ L.X n ⊞ Z` under which `β.f n` is `biprod.fst`. -/
public lemma isDegreewiseSummandProjection_iff (β : K ⟶ L) :
    β.IsDegreewiseSummandProjection ↔
      ∀ n, ∃ (Z : C) (e : K.X n ≅ L.X n ⊞ Z), e.hom ≫ biprod.fst = β.f n :=
  forall_congr' fun n => exists_nonempty_arrow_iso_biprod_fst_iff (β.f n)

/-- A termwise split injection is degreewise a split monomorphism. -/
public lemma IsDegreewiseSummandInclusion.isDegreewiseSplitMono {α : K ⟶ L}
    (hα : α.IsDegreewiseSummandInclusion) : α.IsDegreewiseSplitMono := fun n => by
  obtain ⟨Z, e, h⟩ := (isDegreewiseSummandInclusion_iff α).1 hα n
  exact IsSplitMono.mk' ⟨e.hom ≫ biprod.fst, by rw [← Category.assoc, h, biprod.inl_fst]⟩

/-- A termwise split surjection is degreewise a split epimorphism. -/
public lemma IsDegreewiseSummandProjection.isDegreewiseSplitEpi {β : K ⟶ L}
    (hβ : β.IsDegreewiseSummandProjection) : β.IsDegreewiseSplitEpi := fun n => by
  obtain ⟨Z, e, h⟩ := (isDegreewiseSummandProjection_iff β).1 hβ n
  exact IsSplitEpi.mk' ⟨biprod.inl ≫ e.inv, by rw [← h]; simp⟩

end HomologicalComplex.Hom

namespace HomotopyCategory

open CategoryTheory

universe v u

section Nilpotent

variable {ι : Type*} {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] {c : ComplexShape ι}

/-- A composite through a split short complex vanishes as soon as it vanishes on both sides of
the splitting: if `S : X₁ ⟶ X₂ ⟶ X₃` is split, `u : X ⟶ S.X₂` satisfies `u ≫ S.g = 0` and
`v : S.X₂ ⟶ Y` satisfies `S.f ≫ v = 0`, then `u ≫ v = 0`. -/
private lemma comp_eq_zero_of_splitting {S : ShortComplex 𝒜} (σ : S.Splitting) {X Y : 𝒜}
    {u : X ⟶ S.X₂} {v : S.X₂ ⟶ Y} (hu : u ≫ S.g = 0) (hv : S.f ≫ v = 0) : u ≫ v = 0 := by
  rw [← Category.id_comp v, ← σ.id]
  simp [hv, reassoc_of% hu]

/-- Correcting a morphism of complexes by a null homotopic map does not change its homotopy
class: `φ` is homotopic to `φ - Homotopy.nullHomotopicMap hom`, for any family `hom`
concentrated on the relation of the complex shape. -/
private noncomputable def homotopySubNullHomotopicMap {K B : HomologicalComplex 𝒜 c} (φ : K ⟶ B)
    {hom : ∀ i j, K.X i ⟶ B.X j} (hom_zero : ∀ i j, ¬ c.Rel j i → hom i j = 0) :
    Homotopy φ (φ - Homotopy.nullHomotopicMap hom) :=
  Homotopy.equivSubZero.symm ((Homotopy.ofEq (sub_sub_cancel _ _)).trans
    (Homotopy.nullHomotopy _ hom_zero))

/-- If `g : B ⟶ C` admits degreewise sections `s` and `φ ≫ g` is homotopic to `χ`, then `φ` is
homotopic to a morphism `ψ` with `ψ ≫ g = χ`. -/
private lemma exists_homotopic_comp_eq_of_sections {K B C : HomologicalComplex 𝒜 c}
    {g : B ⟶ C} (s : ∀ i, C.X i ⟶ B.X i) (hs : ∀ i, s i ≫ g.f i = 𝟙 (C.X i)) {φ : K ⟶ B}
    {χ : K ⟶ C} (H : Homotopy (φ ≫ g) χ) : ∃ ψ : K ⟶ B, Nonempty (Homotopy φ ψ) ∧ ψ ≫ g = χ := by
  refine ⟨_, ⟨homotopySubNullHomotopicMap φ (hom := fun i j => H.hom i j ≫ s j)
    fun i j hij => by simp [H.zero i j hij]⟩, ?_⟩
  rw [Preadditive.sub_comp, Homotopy.nullHomotopicMap_comp]
  simp [hs, ← H.sub_eq_nullHomotopicMap]

/-- If `f : A ⟶ B` admits degreewise retractions `r` and `f ≫ φ` is homotopic to `χ`, then `φ` is
homotopic to a morphism `ψ` with `f ≫ ψ = χ`. -/
private lemma exists_homotopic_comp_eq_of_retractions {A B L : HomologicalComplex 𝒜 c}
    {f : A ⟶ B} (r : ∀ i, B.X i ⟶ A.X i) (hr : ∀ i, f.f i ≫ r i = 𝟙 (A.X i)) {φ : B ⟶ L}
    {χ : A ⟶ L} (H : Homotopy (f ≫ φ) χ) : ∃ ψ : B ⟶ L, Nonempty (Homotopy φ ψ) ∧ f ≫ ψ = χ := by
  refine ⟨_, ⟨homotopySubNullHomotopicMap φ (hom := fun i j => r i ≫ H.hom i j)
    fun i j hij => by simp [H.zero i j hij]⟩, ?_⟩
  rw [Preadditive.comp_sub, Homotopy.comp_nullHomotopicMap]
  simp [reassoc_of% hr, ← H.sub_eq_nullHomotopicMap]

/-- Let `S : 0 → A → B → C → 0` be a short complex of complexes with a splitting `σ i` in each
degree. If `b : K ⟶ B` and `b' : B ⟶ L` are morphisms of complexes with `b ≫ (B → C)` and
`(A → B) ≫ b'` null homotopic, then `b ≫ b'` is null homotopic. -/
private lemma nonempty_homotopy_comp_zero_of_degreewiseSplit
    {S : ShortComplex (HomologicalComplex 𝒜 c)}
    (σ : ∀ i, (S.map (HomologicalComplex.eval 𝒜 c i)).Splitting)
    {K L : HomologicalComplex 𝒜 c} {b : K ⟶ S.X₂} {b' : S.X₂ ⟶ L}
    (hb : Nonempty (Homotopy (b ≫ S.g) 0)) (hb' : Nonempty (Homotopy (S.f ≫ b') 0)) :
    Nonempty (Homotopy (b ≫ b') 0) := by
  obtain ⟨H⟩ := hb
  obtain ⟨H'⟩ := hb'
  obtain ⟨ψ, ⟨hψ⟩, hψg⟩ :=
    exists_homotopic_comp_eq_of_sections (fun i => (σ i).s) (fun i => (σ i).s_g) H
  obtain ⟨ψ', ⟨hψ'⟩, hfψ'⟩ :=
    exists_homotopic_comp_eq_of_retractions (fun i => (σ i).r) (fun i => (σ i).f_r) H'
  refine ⟨(hψ.comp hψ').trans (Homotopy.ofEq ?_)⟩
  ext i
  exact comp_eq_zero_of_splitting (σ i) (by simp [← HomologicalComplex.comp_f, hψg])
    (by simp [← HomologicalComplex.comp_f, hfψ'])

/-- Let `S : 0 → A → B → C → 0` be a termwise split exact sequence of complexes in a preadditive
category `𝒜`, with a splitting `σ i` in each degree. If `b : K ⟶ B` and `b' : B ⟶ L` are
morphisms of the homotopy category `K(𝒜)` with `b ≫ (B → C) = 0` and `(A → B) ≫ b' = 0`, then
`b' ∘ b = 0` in `K(𝒜)`. -/
@[stacks 086L]
public theorem comp_eq_zero_of_degreewiseSplit
    {S : ShortComplex (HomologicalComplex 𝒜 c)}
    (σ : ∀ i, (S.map (HomologicalComplex.eval 𝒜 c i)).Splitting)
    {K L : HomotopyCategory 𝒜 c}
    (b : K ⟶ (quotient 𝒜 c).obj S.X₂) (b' : (quotient 𝒜 c).obj S.X₂ ⟶ L)
    (hb : b ≫ (quotient 𝒜 c).map S.g = 0) (hb' : (quotient 𝒜 c).map S.f ≫ b' = 0) :
    b ≫ b' = 0 := by
  obtain ⟨K₀, rfl⟩ := quotient_obj_surjective K
  obtain ⟨L₀, rfl⟩ := quotient_obj_surjective L
  obtain ⟨b₀, rfl⟩ := (quotient 𝒜 c).map_surjective b
  obtain ⟨b₀', rfl⟩ := (quotient 𝒜 c).map_surjective b'
  rw [← Functor.map_comp, quotient_map_eq_zero_iff]
  exact nonempty_homotopy_comp_zero_of_degreewiseSplit σ
    ((quotient_map_eq_zero_iff _).mp (by rwa [Functor.map_comp]))
    ((quotient_map_eq_zero_iff _).mp (by rwa [Functor.map_comp]))

end Nilpotent

end HomotopyCategory

namespace CochainComplex

open CategoryTheory Limits

section Factorization

/-- If the second summand of a biproduct of complexes is contractible, the idempotent
`biprod.fst ≫ biprod.inl` is homotopic to the identity. -/
private noncomputable def homotopyFstInlId {A : Type*} [Category A] [Preadditive A]
    {ι : Type*} {c : ComplexShape ι} (X : HomologicalComplex A c) {Y : HomologicalComplex A c}
    [∀ i, HasBinaryBiproduct (X.X i) (Y.X i)] (hY : Homotopy (𝟙 Y) 0) :
    Homotopy ((biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y)) (𝟙 (X ⊞ Y)) := by
  have key : Homotopy ((biprod.snd : X ⊞ Y ⟶ Y) ≫ (biprod.inr : Y ⟶ X ⊞ Y)) 0 := by
    simpa using (hY.compLeft (biprod.snd : X ⊞ Y ⟶ Y)).compRight (biprod.inr : Y ⟶ X ⊞ Y)
  have h := Homotopy.add (Homotopy.refl
    ((biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y))) key
  rw [add_zero, biprod.total] at h
  exact h.symm

/-- A biproduct of two complexes strictly supported by an embedding of shapes is strictly
supported by that embedding. -/
private lemma isStrictlySupported_biprod {A : Type*} [Category A] [Preadditive A]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (K L : HomologicalComplex A c')
    (e : c.Embedding c')
    [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]
    [K.IsStrictlySupported e] [L.IsStrictlySupported e] :
    (K ⊞ L).IsStrictlySupported e where
  isZero i hi := by
    refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso K L i)
    rw [biprod_isZero_iff]
    exact ⟨K.isZero_X_of_isStrictlySupported e i hi, L.isZero_X_of_isStrictlySupported e i hi⟩

/-- Let `α : K ⟶ L` be a morphism of cochain complexes of an additive category. Then there are a
complex `L'`, a factorization `α = α' ≫ π` of `α` through `L'` with `α'` a termwise split
injection, and a section `s : L ⟶ L'` of `π` with `π ≫ s` homotopic to `𝟙 L'`. Moreover `L'`
inherits the vanishing bounds of `K` and `L`, so that `L'` is bounded below, bounded above or
bounded as soon as both `K` and `L` are. -/
@[stacks 013N]
public theorem exists_factorization_isDegreewiseSplitMono {A : Type*} [Category A]
    [Preadditive A] [HasBinaryBiproducts A] {K L : CochainComplex A ℤ} (α : K ⟶ L) :
    ∃ (L' : CochainComplex A ℤ) (α' : K ⟶ L') (π : L' ⟶ L) (s : L ⟶ L'),
      α' ≫ π = α ∧ α'.IsDegreewiseSplitMono ∧ s ≫ π = 𝟙 L ∧
        Nonempty (Homotopy (π ≫ s) (𝟙 L')) ∧
        (∀ a : ℤ, K.IsStrictlyGE (a + 1) → L.IsStrictlyGE a → L'.IsStrictlyGE a) ∧
        (∀ a : ℤ, K.IsStrictlyLE a → L.IsStrictlyLE a → L'.IsStrictlyLE a) := by
  refine ⟨L ⊞ mappingCone (𝟙 K), biprod.lift α (mappingCone.inr (𝟙 K)),
    biprod.fst, biprod.inl, by simp, ?_, by simp, ?_, ?_, ?_⟩
  · intro n
    refine IsSplitMono.mk' ⟨(biprod.snd : L ⊞ mappingCone (𝟙 K) ⟶ mappingCone (𝟙 K)).f n ≫
      (mappingCone.snd (𝟙 K)).v n n (add_zero n), ?_⟩
    rw [← Category.assoc, ← HomologicalComplex.comp_f, biprod.lift_snd]
    exact mappingCone.inr_f_snd_v (𝟙 K) n
  · exact ⟨homotopyFstInlId L (mappingCone.homotopyToZeroOfId K)⟩
  · intro a hK hL
    have := isStrictlyGE_mappingCone (𝟙 K) (a + 1) (a + 1) a
    exact isStrictlySupported_biprod _ _ _
  · intro a hK hL
    have : (mappingCone (𝟙 K)).IsStrictlyLE a := by
      rw [isStrictlyLE_iff]
      intro i hi
      exact (mappingCone.isZero_X_iff (𝟙 K) i).2
        ⟨K.isZero_of_isStrictlyLE a _ (by omega), K.isZero_of_isStrictlyLE a _ (by omega)⟩
    exact isStrictlySupported_biprod _ _ _

end Factorization

section Cofactorization

variable {A : Type*} [Category A] [Preadditive A]

/-- The first projection of a mapping cocone is a termwise split surjection: in degree `n`,
`mappingCocone.inl` is a section of it. -/
private lemma isDegreewiseSplitEpi_mappingCocone_fst {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber φ] :
    (mappingCocone.fst φ).IsDegreewiseSplitEpi := fun n ↦
  IsSplitEpi.mk' ⟨(mappingCocone.inl φ).v n n (add_zero n), by simp⟩

/-- If `g` is a termwise split surjection, so is `biprod.desc f g`: a section of `g.f n`
followed by `biprod.inr` is a section of `(biprod.desc f g).f n`. -/
private lemma isDegreewiseSplitEpi_biprod_desc {ι : Type*} {c : ComplexShape ι}
    {X Y Z : HomologicalComplex A c} [∀ i, HasBinaryBiproduct (X.X i) (Y.X i)] (f : X ⟶ Z)
    {g : Y ⟶ Z} (hg : g.IsDegreewiseSplitEpi) : (biprod.desc f g).IsDegreewiseSplitEpi :=
  fun n ↦
    have := hg n
    IsSplitEpi.mk' ⟨section_ (g.f n) ≫ (biprod.inr : Y ⟶ X ⊞ Y).f n, by
      rw [Category.assoc, ← HomologicalComplex.comp_f, biprod.inr_desc, IsSplitEpi.id]⟩

/-- The mapping cocone of an identity is contractible: it is the shift by `-1` of the cone of
an identity, which is contractible by `CochainComplex.mappingCone.homotopyToZeroOfId`. -/
private noncomputable def homotopyToZeroOfIdMappingCocone [HasBinaryBiproducts A]
    (L : CochainComplex A ℤ) : Homotopy (𝟙 (mappingCocone (𝟙 L))) 0 := by
  change Homotopy (𝟙 ((mappingCone (𝟙 L))⟦(-1 : ℤ)⟧)) 0
  simpa using (mappingCone.homotopyToZeroOfId (K := L)).shift (-1)

/-- The mapping cone of `f : K ⟶ L` is strictly `≤ n` as soon as `K` is strictly `≤ n + 1`
and `L` is strictly `≤ n`; the dual of `CochainComplex.isStrictlyGE_mappingCone`. -/
public lemma isStrictlyLE_mappingCone {K L : CochainComplex A ℤ} (f : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber f] (n₁ n₂ n : ℤ) [K.IsStrictlyLE n₁] [L.IsStrictlyLE n₂]
    (hn₁ : n₁ ≤ n + 1 := by lia) (hn₂ : n₂ ≤ n := by lia) :
    (mappingCone f).IsStrictlyLE n := by
  rw [isStrictlyLE_iff]
  intro i hi
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE n₁ _ (by lia), L.isZero_of_isStrictlyLE n₂ _ (by lia)⟩

/-- The mapping cocone of `φ : K ⟶ L` is strictly `≥ n` as soon as `K` is strictly `≥ n` and
`L` is strictly `≥ n - 1`, the degree `n` part of the cocone involving `L.X (n - 1)`. -/
private lemma isStrictlyGE_mappingCocone [HasBinaryBiproducts A] {K L : CochainComplex A ℤ}
    (φ : K ⟶ L) (n₁ n₂ n : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]
    (hn₁ : n ≤ n₁ := by lia) (hn₂ : n ≤ n₂ + 1 := by lia) :
    (mappingCocone φ).IsStrictlyGE n := by
  have := isStrictlyGE_mappingCone φ n₁ n₂ (n - 1) (by lia) (by lia)
  exact isStrictlyGE_shift (K := mappingCone φ) (n - 1) (-1) n (by lia)

/-- The mapping cocone of `φ : K ⟶ L` is strictly `≤ n` as soon as `K` is strictly `≤ n` and
`L` is strictly `≤ n - 1`, the degree `n` part of the cocone involving `L.X (n - 1)`. -/
private lemma isStrictlyLE_mappingCocone {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber φ] (n₁ n₂ n : ℤ) [K.IsStrictlyLE n₁] [L.IsStrictlyLE n₂]
    (hn₁ : n₁ ≤ n := by lia) (hn₂ : n₂ < n := by lia) :
    (mappingCocone φ).IsStrictlyLE n := by
  have := isStrictlyLE_mappingCone φ n₁ n₂ (n - 1) (by lia) (by lia)
  exact isStrictlyLE_shift (K := mappingCone φ) (n - 1) (-1) n (by lia)

/-- Let `α : K ⟶ L` be a morphism of cochain complexes of an additive category. Then there are a
complex `K'`, a factorization `α = i ≫ α'` of `α` through `K'` with `α'` a termwise split
surjection, and a retraction `s : K' ⟶ K` of `i` with `s ≫ i` homotopic to `𝟙 K'`. Moreover `K'`
inherits the vanishing bounds of `K` and `L`, so that `K'` is bounded below, bounded above or
bounded as soon as both `K` and `L` are. -/
@[stacks 0642]
public theorem exists_isDegreewiseSplitEpi_factorization [HasBinaryBiproducts A]
    {K L : CochainComplex A ℤ} (α : K ⟶ L) :
    ∃ (K' : CochainComplex A ℤ) (i : K ⟶ K') (α' : K' ⟶ L) (s : K' ⟶ K),
      i ≫ α' = α ∧ α'.IsDegreewiseSplitEpi ∧ i ≫ s = 𝟙 K ∧
        Nonempty (Homotopy (s ≫ i) (𝟙 K')) ∧
        (∀ a : ℤ, K.IsStrictlyGE a → L.IsStrictlyGE a → K'.IsStrictlyGE a) ∧
        (∀ a : ℤ, K.IsStrictlyLE a → L.IsStrictlyLE (a - 1) → K'.IsStrictlyLE a) :=
  ⟨K ⊞ mappingCocone (𝟙 L), biprod.inl, biprod.desc α (mappingCocone.fst (𝟙 L)), biprod.fst,
    by simp, isDegreewiseSplitEpi_biprod_desc α (isDegreewiseSplitEpi_mappingCocone_fst (𝟙 L)),
    by simp, ⟨homotopyFstInlId K (homotopyToZeroOfIdMappingCocone L)⟩,
    fun a hK hL ↦
      have := hK
      have := hL
      have := isStrictlyGE_mappingCocone (𝟙 L) a a a
      isStrictlySupported_biprod _ _ _,
    fun a hK hL ↦
      have := hK
      have := hL
      have := isStrictlyLE_mappingCocone (𝟙 L) (a - 1) (a - 1) a
      isStrictlySupported_biprod _ _ _⟩

end Cofactorization

section ComposableArrows

section

variable {V : Type*} [Category V] [Preadditive V] {ι : Type*} {c : ComplexShape ι}
  {K L M : HomologicalComplex V c}

/-- A morphism of complexes which admits a section that is a homotopy inverse for it is a
homotopy equivalence. -/
private lemma homotopyEquivalences_of_comp_eq_id {π : K ⟶ L} {s : L ⟶ K} (hs : s ≫ π = 𝟙 L)
    (h : Homotopy (π ≫ s) (𝟙 K)) : HomologicalComplex.homotopyEquivalences V c π :=
  ⟨{ hom := π
     inv := s
     homotopyHomInvId := h
     homotopyInvHomId := Homotopy.ofEq hs }, rfl⟩

/-- The identity of a complex is a termwise split injection. -/
private lemma isDegreewiseSplitMono_id (K : HomologicalComplex V c) :
    HomologicalComplex.Hom.IsDegreewiseSplitMono (𝟙 K) := fun p ↦ by
  rw [HomologicalComplex.id_f]
  infer_instance

/-- A composition of termwise split injections is a termwise split injection. -/
private lemma isDegreewiseSplitMono_comp {f : K ⟶ L} {g : L ⟶ M}
    (hf : f.IsDegreewiseSplitMono) (hg : g.IsDegreewiseSplitMono) :
    (f ≫ g).IsDegreewiseSplitMono := fun p ↦ by
  have := hf p
  have := hg p
  exact (inferInstance : IsSplitMono (f.f p ≫ g.f p))

end

section

variable {A : Type*} [Category A] [HasZeroMorphisms A]

/-- A property `P` of cochain complexes is *stable under factorization* when it holds for any
complex `L'` as soon as it holds for `K` and `L`, provided `L'` is strictly `≥ a` whenever `K` is
strictly `≥ a + 1` and `L` is strictly `≥ a`, and strictly `≤ a` whenever `K` and `L` are. -/
private def IsStableUnderFactorization (P : ObjectProperty (CochainComplex A ℤ)) : Prop :=
  ∀ ⦃K L L' : CochainComplex A ℤ⦄,
    (∀ a : ℤ, K.IsStrictlyGE (a + 1) → L.IsStrictlyGE a → L'.IsStrictlyGE a) →
    (∀ a : ℤ, K.IsStrictlyLE a → L.IsStrictlyLE a → L'.IsStrictlyLE a) →
    P K → P L → P L'

/-- The bounded below complexes are stable under factorization. -/
private lemma isStableUnderFactorization_plus :
    IsStableUnderFactorization (CochainComplex.plus A) := by
  rintro K L L' hGE - ⟨p, hp⟩ ⟨q, hq⟩
  exact ⟨min (p - 1) q, hGE _ (K.isStrictlyGE_of_ge _ p (by omega))
    (L.isStrictlyGE_of_ge _ q (by omega))⟩

/-- The bounded above complexes are stable under factorization. -/
private lemma isStableUnderFactorization_minus :
    IsStableUnderFactorization (CochainComplex.minus A) := by
  rintro K L L' - hLE ⟨p, hp⟩ ⟨q, hq⟩
  exact ⟨max p q, hLE _ (K.isStrictlyLE_of_le p _ (le_max_left _ _))
    (L.isStrictlyLE_of_le q _ (le_max_right _ _))⟩

end

section

variable {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]

/-- A morphism of cochain complexes `g : K ⟶ M` factors as a termwise split injection
`α : K ⟶ L'` followed by a homotopy equivalence `π : L' ⟶ M`, and `L'` belongs to every class of
complexes which contains `K` and `M` and is stable under factorization. -/
private lemma exists_factorization_isDegreewiseSplitMono_homotopyEquivalences
    {K M : CochainComplex A ℤ} (g : K ⟶ M) :
    ∃ (L' : CochainComplex A ℤ) (α : K ⟶ L') (π : L' ⟶ M), α ≫ π = g ∧
      α.IsDegreewiseSplitMono ∧
      HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ) π ∧
      ∀ P : ObjectProperty (CochainComplex A ℤ), IsStableUnderFactorization P →
        P K → P M → P L' := by
  obtain ⟨L', α, π, s, hαπ, hα, hsπ, ⟨h⟩, hGE, hLE⟩ :=
    exists_factorization_isDegreewiseSplitMono g
  exact ⟨L', α, π, hαπ, hα, homotopyEquivalences_of_comp_eq_id hsπ h, fun _ hP ↦ hP hGE hLE⟩

/-- Let `F : A₀ ⟶ ⋯ ⟶ Aₙ` be a sequence of composable morphisms of cochain complexes and let
`u : K ⟶ A₀` be a homotopy equivalence. Then there are a sequence `G : B₀ ⟶ ⋯ ⟶ Bₙ` whose
arrows are termwise split injections, a morphism of diagrams `φ : G ⟶ F` whose components are
homotopy equivalences, and a termwise split injection `α : K ⟶ B₀` with `α ≫ φ.app 0 = u`;
moreover every `Bᵢ` belongs to any class of complexes containing `K` and all the `Aᵢ` which is
stable under factorization. -/
private lemma exists_composableArrows_of_hom_left {n : ℕ} :
    ∀ (F : ComposableArrows (CochainComplex A ℤ) n) (K : CochainComplex A ℤ) (u : K ⟶ F.left),
      HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ) u →
      ∃ (G : ComposableArrows (CochainComplex A ℤ) n) (φ : G ⟶ F) (α : K ⟶ G.left),
        α.IsDegreewiseSplitMono ∧ α ≫ ComposableArrows.app' φ 0 = u ∧
        (∀ (i : ℕ) (_ : i + 1 ≤ n), (G.map' i (i + 1)).IsDegreewiseSplitMono) ∧
        (∀ i, HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ) (φ.app i)) ∧
        ∀ P : ObjectProperty (CochainComplex A ℤ), IsStableUnderFactorization P →
          (∀ i, P (F.obj i)) → P K → ∀ i, P (G.obj i) := by
  induction n with
  | zero =>
    intro F K u hu
    refine ⟨ComposableArrows.mk₀ K, ComposableArrows.homMk₀ u, 𝟙 K, isDegreewiseSplitMono_id K,
      Category.id_comp u, fun i hi ↦ absurd hi (by omega), fun i ↦ ?_, fun _ _ _ hK _ ↦ hK⟩
    obtain rfl := Fin.fin_one_eq_zero i
    exact hu
  | succ n ih =>
    intro F K u hu
    obtain ⟨L', α', π, hα'π, hα', hπ, hL'⟩ :=
      exists_factorization_isDegreewiseSplitMono_homotopyEquivalences (u ≫ F.map' 0 1)
    obtain ⟨G', φ', α, hα, hαφ, hsplit, hequiv, hstable⟩ := ih F.δ₀ L' π hπ
    have w : (G'.precomp (α' ≫ α)).map' 0 1 ≫ ComposableArrows.app' φ' 0 = u ≫ F.map' 0 1 := by
      change (α' ≫ α) ≫ ComposableArrows.app' φ' 0 = u ≫ F.map' 0 1
      rw [Category.assoc, hαφ]
      exact hα'π
    refine ⟨G'.precomp (α' ≫ α), ComposableArrows.homMkSucc u φ' w, 𝟙 K,
      isDegreewiseSplitMono_id K, Category.id_comp u, ?_, ?_, ?_⟩
    · intro i hi
      obtain _ | i := i
      · exact isDegreewiseSplitMono_comp hα' hα
      · exact hsplit i (by omega)
    · intro i
      obtain ⟨_ | i, hi⟩ := i
      · exact hu
      · exact hequiv ⟨i, by omega⟩
    · intro P hP hF hK i
      obtain ⟨_ | i, hi⟩ := i
      · exact hK
      · exact hstable P hP (fun j ↦ hF _) (hL' P hP hK (hF ⟨1, by omega⟩)) ⟨i, by omega⟩

/-- Let `F : A₀ ⟶ A₁ ⟶ ⋯ ⟶ Aₙ` be a sequence of composable morphisms of cochain complexes of an
additive category. Then there are a sequence `G : B₀ ⟶ B₁ ⟶ ⋯ ⟶ Bₙ` and a morphism of diagrams
`φ : G ⟶ F` such that each `Bᵢ ⟶ Bᵢ₊₁` is a termwise split injection and each `Bᵢ ⟶ Aᵢ` is a
homotopy equivalence. Moreover, if all the `Aᵢ` are bounded below (resp. bounded above), then so
are all the `Bᵢ`. -/
@[stacks 014M]
public theorem exists_composableArrows_isDegreewiseSplitMono {n : ℕ}
    (F : ComposableArrows (CochainComplex A ℤ) n) :
    ∃ (G : ComposableArrows (CochainComplex A ℤ) n) (φ : G ⟶ F),
      (∀ (i : ℕ) (_ : i + 1 ≤ n), (G.map' i (i + 1)).IsDegreewiseSplitMono) ∧
      (∀ i, HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ) (φ.app i)) ∧
      ((∀ i, CochainComplex.plus A (F.obj i)) → ∀ i, CochainComplex.plus A (G.obj i)) ∧
      ((∀ i, CochainComplex.minus A (F.obj i)) → ∀ i, CochainComplex.minus A (G.obj i)) := by
  obtain ⟨G, φ, -, -, -, hsplit, hequiv, hstable⟩ :=
    exists_composableArrows_of_hom_left F F.left (𝟙 _)
      (HomologicalComplex.homotopyEquivalences.of_isIso _)
  exact ⟨G, φ, hsplit, hequiv,
    fun hF ↦ hstable _ isStableUnderFactorization_plus hF (hF ⟨0, by omega⟩),
    fun hF ↦ hstable _ isStableUnderFactorization_minus hF (hF ⟨0, by omega⟩)⟩

end

end ComposableArrows

end CochainComplex

namespace CochainComplex.mappingCone

open CategoryTheory Limits Pretriangulated HomologicalComplex

variable {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜]

/-- Let `f₁ : K₁ ⟶ L₁` and `f₂ : K₂ ⟶ L₂` be morphisms of cochain complexes of an additive
category `𝒜`, and let `φ = (a, b, c)` be a morphism of triangles of the homotopy category `K(𝒜)`
from the cone triangle `K₁ ⟶ L₁ ⟶ C(f₁) ⟶ K₁⟦1⟧` of `f₁` to the cone triangle of `f₂`. If `a`
and `b` are homotopy equivalences, i.e. isomorphisms in `K(𝒜)`, then so is `c`. -/
@[stacks 014K]
public theorem isIso₃_of_isIso₁₂ [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜]
    {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ} {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    (φ : triangleh f₁ ⟶ triangleh f₂) (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) :
    IsIso φ.hom₃ :=
  Pretriangulated.isIso₃_of_isIso₁₂ φ (HomotopyCategory.mappingCone_triangleh_distinguished f₁)
    (HomotopyCategory.mappingCone_triangleh_distinguished f₂) h₁ h₂

end CochainComplex.mappingCone

-- The rotated cone triangle of `φ` is the triangle of the termwise split sequence
-- `0 → L → C(φ) → K[1] → 0`: Mathlib's comparison isomorphism is the identity in all three
-- positions, and its splitting is the biproduct decomposition `C(φ)ⁿ = Kⁿ⁺¹ ⊕ Lⁿ`.
add_to_stacks 014O "the rotated cone triangle is the triangle of a termwise split sequence"
  CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit
add_to_stacks 014O "the degreewise splitting of that sequence"
  CochainComplex.mappingCone.triangleRotateShortComplexSplitting

namespace CochainComplex

open CategoryTheory Category Limits Pretriangulated HomologicalComplex
open CochainComplex.HomComplex

section Comparison

variable {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]
  (S : ShortComplex (CochainComplex 𝒜 ℤ))
  (σ : ∀ n, (S.map (eval 𝒜 (ComplexShape.up ℤ) n)).Splitting)

/-- The retractions of a termwise split short exact sequence of cochain complexes, assembled
into a cochain of degree `-1` from `S.X₂` to `S.X₁⟦1⟧`. -/
public noncomputable def retractionCochain : Cochain S.X₂ (S.X₁⟦(1 : ℤ)⟧) (-1) :=
  Cochain.mk fun p q hpq => (σ p).r ≫ (S.X₁.XIsoOfEq (show p = q + 1 by omega)).hom

omit [HasBinaryBiproducts 𝒜] in
public lemma retractionCochain_v (p q : ℤ) (hpq : p + (-1) = q) :
    (retractionCochain S σ).v p q hpq =
      (σ p).r ≫ (S.X₁.XIsoOfEq (show p = q + 1 by omega)).hom := rfl

/-- The canonical morphism `C(S.f) ⟶ S.X₃` attached to a short complex of cochain complexes:
in degree `n` it is the projection `C(S.f)ⁿ = S.X₂ⁿ ⊕ S.X₁ⁿ⁺¹ → S.X₂ⁿ` followed by `S.gⁿ`. -/
private noncomputable def descHom : mappingCone S.f ⟶ S.X₃ :=
  mappingCone.desc S.f 0 S.g (by simp [S.zero])

/-- The composition `C(S.f) ⟶ S.X₃ --δ--> S.X₁⟦1⟧` of the canonical morphism `descHom` with the
connecting morphism of a termwise split short exact sequence is homotopic to any morphism `t`
satisfying the two properties which characterize the third morphism `-p` of the cone triangle of
`S.f`. -/
private noncomputable def homotopyDescCompHomOfDegreewiseSplit
    (t : mappingCone S.f ⟶ S.X₁⟦(1 : ℤ)⟧)
    (ht₁ : ∀ (p q : ℤ) (hpq : p + (-1) = q), (mappingCone.inl S.f).v p q hpq ≫ t.f q =
      -(S.X₁.shiftFunctorObjXIso 1 q p (by omega)).inv)
    (ht₂ : mappingCone.inr S.f ≫ t = 0) :
    Homotopy (descHom S ≫ homOfDegreewiseSplit S σ) t := by
  refine mappingCone.descHomotopy _ _ _ 0 (retractionCochain S σ) ?_ ?_
  · ext p q hpq
    obtain rfl : p = q + 1 := by omega
    have h := (σ (q + 1)).f_r
    dsimp at h
    simp [retractionCochain_v, ht₁, h, shiftFunctorObjXIso, descHom]
  · ext p
    have h2 := HomologicalComplex.congr_hom ht₂ p
    simp only [Cochain.add_v, Cochain.ofHom_v]
    rw [δ_v (-1) 0 (by omega) (retractionCochain S σ) p p (by omega) (p - 1) (p + 1)
      (by omega) (by omega)]
    have hg := (σ p).g_s
    dsimp at hg h2 ⊢
    have hf := (σ (p + 1)).f_r
    dsimp at hf
    simp [retractionCochain_v, cocycleOfDegreewiseSplit, h2, reassoc_of% hg,
      Preadditive.sub_comp, S.f.comm_assoc, hf, descHom]
    abel

/-- The morphism of triangles of `K(𝒜)` from the cone triangle of `S.f` to the triangle
associated to a termwise split short exact sequence `S`, which is the identity on `S.X₁` and on
`S.X₂` and is the canonical morphism `C(S.f) ⟶ S.X₃` in the third position. -/
private noncomputable def trianglehHom :
    mappingCone.triangleh S.f ⟶ trianglehOfDegreewiseSplit S σ :=
  Triangle.homMk _ _ (𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj S.X₁))
    (𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj S.X₂))
    ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map (descHom S))
    (by
      change (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map S.f ≫ 𝟙 _ =
        𝟙 _ ≫ (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map S.f
      rw [comp_id, id_comp])
    (by
      change (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map (mappingCone.inr S.f) ≫
          (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map (descHom S) =
        𝟙 _ ≫ (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map S.g
      rw [id_comp, ← CategoryTheory.Functor.map_comp, descHom, mappingCone.inr_desc])
    (by
      have h := HomotopyCategory.eq_of_homotopy _ _
        (homotopyDescCompHomOfDegreewiseSplit S σ (mappingCone.triangle S.f).mor₃
          (mappingCone.inl_v_triangle_mor₃_f S.f) (mappingCone.inr_triangleδ S.f))
      change ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map
            (mappingCone.triangle S.f).mor₃ ≫
          ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).commShiftIso
            (1 : ℤ)).hom.app S.X₁) ≫
          (CategoryTheory.shiftFunctor (HomotopyCategory 𝒜 (ComplexShape.up ℤ)) (1 : ℤ)).map (𝟙 _) =
        (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map (descHom S) ≫
          ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map
              (homOfDegreewiseSplit S σ) ≫
            ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).commShiftIso
              (1 : ℤ)).hom.app S.X₁)
      rw [CategoryTheory.Functor.map_id, ← assoc, ← CategoryTheory.Functor.map_comp, h]
      exact comp_id _)

variable [HasZeroObject 𝒜]

private lemma isIso_trianglehHom_hom₃ : IsIso (trianglehHom S σ).hom₃ :=
  Pretriangulated.isIso₃_of_isIso₁₂ (trianglehHom S σ)
    (HomotopyCategory.mappingCone_triangleh_distinguished S.f)
    (trianglehOfDegreewiseSplit_distinguished S σ)
    (by
      change IsIso (𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj S.X₁))
      infer_instance)
    (by
      change IsIso (𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj S.X₂))
      infer_instance)

/-- The cone triangle of the first morphism of a termwise split short exact sequence of cochain
complexes is isomorphic, in `K(𝒜)`, to the triangle associated to the sequence, by an
isomorphism which is the identity on the two first objects. -/
@[sga "4 XVII 1.1.1" "Forward clause"]
private noncomputable def trianglehIso :
    mappingCone.triangleh S.f ≅ trianglehOfDegreewiseSplit S σ :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (@asIso _ _ _ _ (trianglehHom S σ).hom₃ (isIso_trianglehHom_hom₃ S σ))
    (trianglehHom S σ).comm₁ (trianglehHom S σ).comm₂ (trianglehHom S σ).comm₃

end Comparison

section Twist

variable {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]
  {A C : CochainComplex 𝒜 ℤ} (φ : C ⟶ A⟦(1 : ℤ)⟧)

/-- A family `u q : C^q ⟶ A^{q+1}` satisfying `u q ≫ d_A + d_C ≫ u (q+1) = 0` is exactly a
morphism of complexes `C^• ⟶ A^•⟦1⟧`, the shift contributing the sign. -/
public noncomputable def twistHom (u : ∀ q : ℤ, C.X q ⟶ A.X (q + 1))
    (hu : ∀ q : ℤ, u q ≫ A.d (q + 1) (q + 1 + 1) + C.d q (q + 1) ≫ u (q + 1) = 0) :
    C ⟶ A⟦(1 : ℤ)⟧ where
  f q := u q
  comm' q q' hqq' := by
    obtain rfl : q' = q + 1 := hqq'.symm
    rw [CochainComplex.shiftFunctor_obj_d']
    simp only [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg]
    rw [neg_eq_iff_add_eq_zero]
    exact hu q

omit [HasBinaryBiproducts 𝒜] in
/-- The morphism `twistHom u hu` is `u` in every degree. -/
public lemma twistHom_f (u : ∀ q : ℤ, C.X q ⟶ A.X (q + 1))
    (hu : ∀ q : ℤ, u q ≫ A.d (q + 1) (q + 1 + 1) + C.d q (q + 1) ≫ u (q + 1) = 0) (q : ℤ) :
    (twistHom u hu).f q = u q := rfl

/-- The twist of `A^•` by `C^•` along a morphism `φ : C^• ⟶ A^•⟦1⟧`: the cochain complex whose
term in degree `n` is `Aⁿ ⊞ Cⁿ` and whose differential is `(a, x) ↦ (d a + φⁿ x, d x)`. It is
the shift by `-1` of the cone on `φ`. -/
public noncomputable abbrev twist : CochainComplex 𝒜 ℤ :=
  CochainComplex.of (fun n => A.X n ⊞ C.X n)
    (fun n => biprod.lift (biprod.fst ≫ A.d n (n + 1) + biprod.snd ≫ φ.f n)
      (biprod.snd ≫ C.d n (n + 1))) (fun n => by
        have h : φ.f n ≫ (A⟦(1 : ℤ)⟧).d n (n + 1) = C.d n (n + 1) ≫ φ.f (n + 1) := φ.comm _ _
        rw [CochainComplex.shiftFunctor_obj_d'] at h
        simp only [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg] at h
        ext <;> simp [← h])

/-- The inclusion of `A^•` in the twist of `A^•` by `C^•` along `φ`. -/
public noncomputable abbrev twistι : A ⟶ twist φ where
  f _ := biprod.inl
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext <;> simp

/-- The projection of the twist of `A^•` by `C^•` along `φ` onto `C^•`. -/
public noncomputable abbrev twistπ : twist φ ⟶ C where
  f _ := biprod.snd
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    simp

public lemma twistι_comp_twistπ : twistι φ ≫ twistπ φ = 0 := by ext n; simp

/-- The degree-`n` term of the twist is the biproduct of the terms. -/
public lemma twist_X (n : ℤ) : (twist φ).X n = (A.X n ⊞ C.X n) := rfl

/-- The differential of the twist, in terms of the differentials of `A` and `C` and `φ`. -/
public lemma twist_d (n : ℤ) : (twist φ).d n (n + 1) =
    biprod.lift (biprod.fst ≫ A.d n (n + 1) + biprod.snd ≫ φ.f n)
      (biprod.snd ≫ C.d n (n + 1)) := by
  apply CochainComplex.of_d

/-- The inclusion of `A` in the twist is `biprod.inl` in every degree. -/
public lemma twistι_f (n : ℤ) : (twistι φ).f n = biprod.inl := rfl

/-- The projection of the twist onto `C` is `biprod.snd` in every degree. -/
public lemma twistπ_f (n : ℤ) : (twistπ φ).f n = biprod.snd := rfl

/-- The short exact sequence `0 → A^• → twist φ → C^• → 0`. -/
public noncomputable abbrev twistShortComplex : ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk _ _ (twistι_comp_twistπ φ)

/-- The sequence `0 → A^• → twist φ → C^• → 0` is split in every degree. -/
public noncomputable def twistSplitting (n : ℤ) :
    ((twistShortComplex φ).map (eval 𝒜 (ComplexShape.up ℤ) n)).Splitting where
  r := biprod.fst
  s := biprod.inr
  id := biprod.total

/-- The connecting morphism of the termwise split short exact sequence
`0 → A^• → twist φ → C^• → 0` is `φ`. -/
@[sga "4½ Etat_0 1.2.4" "special case"]
public lemma homOfDegreewiseSplit_twistSplitting :
    homOfDegreewiseSplit (twistShortComplex φ) (twistSplitting φ) = φ := by
  ext n
  rw [homOfDegreewiseSplit_f]
  simp [cocycleOfDegreewiseSplit, twistSplitting]

end Twist

/-- Let `𝒜` be an additive category.

(1) Given a termwise split exact sequence of cochain complexes — a short complex `S` together
with a splitting `σ n` of each of its degreewise evaluations — the cone triangle
`S.X₁ → S.X₂ → C(S.f) --(-p)--> S.X₁[1]` of its first map is isomorphic in `K(𝒜)` to the triangle
`S.X₁ → S.X₂ → S.X₃ --δ--> S.X₁[1]` associated to the sequence, by an isomorphism of triangles
which is the identity on `S.X₁` and on `S.X₂` and whose third component is the class of the
canonical morphism `C(S.f) ⟶ S.X₃` given by the projection onto `S.X₂` followed by `S.g`; in
particular that canonical morphism is a homotopy equivalence.

(2) Given a morphism of cochain complexes `f : K ⟶ L`, there are a termwise split exact sequence
`K → L̃ → M` starting at `K` and an isomorphism in `K(𝒜)` from its associated triangle
`K → L̃ → M --δ--> K[1]` to the cone triangle `K → L → C(f) --(-p)--> K[1]` of `f` which is the
identity on `K`. -/
@[stacks 014L, sga "4 XVII 1.1.1" "both final assertions", sga "7 XIII 1.4.2" "partial"]
public theorem exists_triangleh_iso_trianglehOfDegreewiseSplit_and_exists_iso_triangleh
    {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] :
    (∀ (S : ShortComplex (CochainComplex 𝒜 ℤ))
        (σ : ∀ n, (S.map (eval 𝒜 (ComplexShape.up ℤ) n)).Splitting),
        ∃ e : mappingCone.triangleh S.f ≅ trianglehOfDegreewiseSplit S σ,
          e.hom.hom₁ = 𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj S.X₁) ∧
            e.hom.hom₂ = 𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj S.X₂) ∧
            e.hom.hom₃ = (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map
              (mappingCone.desc S.f 0 S.g (by simp))) ∧
      ∀ {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L),
        ∃ (L' M : CochainComplex 𝒜 ℤ) (f' : K ⟶ L') (g : L' ⟶ M) (w : f' ≫ g = 0)
          (σ : ∀ n, ((ShortComplex.mk f' g w).map (eval 𝒜 (ComplexShape.up ℤ) n)).Splitting)
          (e : trianglehOfDegreewiseSplit (ShortComplex.mk f' g w) σ ≅ mappingCone.triangleh f),
          e.hom.hom₁ = 𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj K) := by
  constructor
  · exact fun S σ => ⟨trianglehIso S σ, rfl, rfl, rfl⟩
  · intro K L f
    set φ : mappingCone f ⟶ K⟦(1 : ℤ)⟧ := (mappingCone.triangle f).mor₃ with hφ
    have hcomm : ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map
            (homOfDegreewiseSplit (twistShortComplex φ) (twistSplitting φ)) ≫
          ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) ≫
          (CategoryTheory.shiftFunctor (HomotopyCategory 𝒜 (ComplexShape.up ℤ)) (1 : ℤ)).map
            (𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj K)) =
        𝟙 ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj (mappingCone f)) ≫
          ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map φ ≫
            ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).commShiftIso
              (1 : ℤ)).hom.app K) := by
      simp only [CategoryTheory.Functor.map_id, id_comp,
        homOfDegreewiseSplit_twistSplitting]
      exact Category.comp_id _
    obtain ⟨β, h₁, h₂⟩ := complete_distinguished_triangle_morphism₂
      (trianglehOfDegreewiseSplit (twistShortComplex φ) (twistSplitting φ))
      (mappingCone.triangleh f)
      (trianglehOfDegreewiseSplit_distinguished (twistShortComplex φ) (twistSplitting φ))
      (HomotopyCategory.mappingCone_triangleh_distinguished f) (𝟙 _) (𝟙 _) hcomm
    have hβ : IsIso β :=
      Pretriangulated.isIso₂_of_isIso₁₃
        (Triangle.homMk (trianglehOfDegreewiseSplit (twistShortComplex φ) (twistSplitting φ))
          (mappingCone.triangleh f) (𝟙 _) β (𝟙 _) h₁ h₂ hcomm)
        (trianglehOfDegreewiseSplit_distinguished (twistShortComplex φ) (twistSplitting φ))
        (HomotopyCategory.mappingCone_triangleh_distinguished f)
        (by exact IsIso.id _) (by exact IsIso.id _)
    exact ⟨twist φ, mappingCone f, twistι φ, twistπ φ, twistι_comp_twistπ φ, twistSplitting φ,
      Triangle.isoMk _ _ (Iso.refl _) (@asIso _ _ _ _ β hβ) (Iso.refl _) h₁ h₂ hcomm, rfl⟩

section InvRotate

variable {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]

section

variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)

/-- The morphism of mapping cones induced by a commutative square `φ₁ ≫ b = a ≫ φ₂` is an
isomorphism as soon as `a` and `b` are: its inverse is the morphism induced by the inverse
square. -/
private lemma isIso_mappingCone_map {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} [IsIso a] [IsIso b]
    (comm : φ₁ ≫ b = a ≫ φ₂) : IsIso (mappingCone.map φ₁ φ₂ a b comm) := by
  refine ⟨mappingCone.map φ₂ φ₁ (inv a) (inv b) (by
    rw [IsIso.comp_inv_eq, assoc, comm, IsIso.inv_hom_id_assoc]), ?_, ?_⟩ <;>
      rw [← mappingCone.map_comp] <;> simp [mappingCone.map_id]

/-- A commutative square of isomorphisms `a : K₁ ≅ K₂`, `b : L₁ ≅ L₂` between `φ₁ : K₁ ⟶ L₁` and
`φ₂ : K₂ ⟶ L₂` induces an isomorphism of cone triangles
`mappingCone.triangle φ₁ ≅ mappingCone.triangle φ₂`, namely
`CochainComplex.mappingCone.triangleMap`; in particular its first two components are `a` and `b`
themselves. -/
private noncomputable def mappingConeTriangleIsoOfSquare (a : K₁ ≅ K₂) (b : L₁ ≅ L₂)
    (comm : φ₁ ≫ b.hom = a.hom ≫ φ₂) :
    mappingCone.triangle φ₁ ≅ mappingCone.triangle φ₂ :=
  have : IsIso (mappingCone.triangleMap φ₁ φ₂ a.hom b.hom comm) :=
    Triangle.isIso_of_isIsos _ (by exact inferInstanceAs (IsIso a.hom))
      (by exact inferInstanceAs (IsIso b.hom)) (by exact isIso_mappingCone_map φ₁ φ₂ comm)
  asIso (mappingCone.triangleMap φ₁ φ₂ a.hom b.hom comm)

/-- If a triangle of cochain complexes is isomorphic to the cone triangle of *some* morphism, then
it is isomorphic to the cone triangle of its own first map, by an isomorphism which is the
identity in positions `1` and `2`. -/
private lemma exists_iso_mappingCone_triangle_mor₁_of_iso
    {T : Triangle (CochainComplex 𝒜 ℤ)} {K L : CochainComplex 𝒜 ℤ} {ψ : K ⟶ L}
    (E : T ≅ mappingCone.triangle ψ) :
    ∃ e : T ≅ mappingCone.triangle T.mor₁,
      e.hom.hom₁ = 𝟙 T.obj₁ ∧ e.hom.hom₂ = 𝟙 T.obj₂ :=
  ⟨E ≪≫ mappingConeTriangleIsoOfSquare ψ T.mor₁ (Triangle.π₁.mapIso E).symm
      (Triangle.π₂.mapIso E).symm E.inv.comm₁,
    (Triangle.π₁.mapIso E).hom_inv_id, (Triangle.π₂.mapIso E).hom_inv_id⟩

end

/-- The inverse rotation of the triangle of a termwise split short exact sequence is isomorphic to
the cone triangle of `δ⟦-1⟧`, where `δ = CochainComplex.homOfDegreewiseSplit S σ`. -/
private noncomputable def triangleOfDegreewiseSplitInvRotateIso
    (S : ShortComplex (CochainComplex 𝒜 ℤ))
    (σ : ∀ n, (S.map (eval 𝒜 (ComplexShape.up ℤ) n)).Splitting) :
    (triangleOfDegreewiseSplit S σ).invRotate ≅
      mappingCone.triangle ((homOfDegreewiseSplit S σ)⟦(-1 : ℤ)⟧') :=
  (invRotateIsoRotateRotateShiftFunctorNegOne (CochainComplex 𝒜 ℤ)).app _ ≪≫
    (Triangle.shiftFunctor (CochainComplex 𝒜 ℤ) (-1)).mapIso
      (triangleOfDegreewiseSplitRotateRotateIso S σ) ≪≫
    mappingCone.shiftTriangleIso (homOfDegreewiseSplit S σ) (-1)

/-- Let `𝒜` be an additive category and let `S` be a termwise split short exact sequence of
cochain complexes of `𝒜`, split by `σ`, with associated triangle
`S.X₁ → S.X₂ → S.X₃ --δ--> S.X₁[1]` (`CochainComplex.triangleOfDegreewiseSplit`). Then the
inverse rotation `S.X₃[-1] --δ[-1]--> S.X₁ --S.f--> S.X₂` of that triangle is isomorphic, by an
isomorphism of triangles of complexes which is the identity on `S.X₃[-1]` and on `S.X₁`, to the
cone triangle `S.X₃[-1] --δ[-1]--> S.X₁ --i--> C(δ[-1]) --(-p)--> S.X₃[-1][1]` of its own first
map. -/
@[stacks 014N]
public theorem exists_triangleOfDegreewiseSplit_invRotate_iso_mappingCone_triangle
    (S : ShortComplex (CochainComplex 𝒜 ℤ))
    (σ : ∀ n, (S.map (eval 𝒜 (ComplexShape.up ℤ) n)).Splitting) :
    ∃ e : (triangleOfDegreewiseSplit S σ).invRotate ≅
        mappingCone.triangle (triangleOfDegreewiseSplit S σ).invRotate.mor₁,
      e.hom.hom₁ = 𝟙 ((triangleOfDegreewiseSplit S σ).invRotate.obj₁) ∧
        e.hom.hom₂ = 𝟙 S.X₁ :=
  exists_iso_mappingCone_triangle_mor₁_of_iso (triangleOfDegreewiseSplitInvRotateIso S σ)

end InvRotate

end CochainComplex

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

variable {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜]

/-- A morphism of cochain complexes is a *termwise split injection* in the weak sense used by
the lemmas below if every degree-`n` component admits a retraction (left inverse). This is
weaker than [Stacks, Tag 014G] (`HomologicalComplex.Hom.IsDegreewiseSummandInclusion`), which
also asks for a complementary summand, so lemmas assuming it are more general. -/
def IsTermwiseSplitInjection {C D : CochainComplex 𝒜 ℤ} (f : C ⟶ D) : Prop :=
  ∀ n : ℤ, IsSplitMono (f.f n)

/-- A morphism of cochain complexes is a *termwise split surjection* in the weak sense used by
the lemmas below if every degree-`n` component admits a section (right inverse). This is
weaker than [Stacks, Tag 014G] (`HomologicalComplex.Hom.IsDegreewiseSummandProjection`), which
also asks for a complementary summand, so lemmas assuming it are more general. -/
def IsTermwiseSplitSurjection {C D : CochainComplex 𝒜 ℤ} (g : C ⟶ D) : Prop :=
  ∀ n : ℤ, IsSplitEpi (g.f n)

/-- Consider a square

      A ---f---> B
      |          |
      a          b
      |          |
      v          v
      C ---g---> D

of morphisms of cochain complexes that commutes up to homotopy
(`b ∘ f ∼ g ∘ a`, i.e. `Nonempty (Homotopy (f ≫ b) (a ≫ g))`). If `f` is a
termwise split injection, then there is a morphism `b'` homotopic to `b` such
that the square commutes on the nose: `b' ∘ f = g ∘ a` (`f ≫ b' = a ≫ g`). -/
@[stacks 014H "(1)"]
theorem exists_homotopic_comm_of_isTermwiseSplitInjection {Ac Bc Cc Dc : CochainComplex 𝒜 ℤ}
    (f : Ac ⟶ Bc) (a : Ac ⟶ Cc) (b : Bc ⟶ Dc) (g : Cc ⟶ Dc)
    (hsq : Nonempty (Homotopy (f ≫ b) (a ≫ g)))
    (hf : IsTermwiseSplitInjection f) :
    ∃ b' : Bc ⟶ Dc, Nonempty (Homotopy b' b) ∧ f ≫ b' = a ≫ g := by
  obtain ⟨H⟩ := hsq
  let := fun n => (hf n)
  obtain ⟨b', ⟨hb'⟩, hfb'⟩ := HomotopyCategory.exists_homotopic_comp_eq_of_retractions
    (fun i => retraction (f.f i)) (fun i => IsSplitMono.id (f.f i)) H
  exact ⟨b', ⟨hb'.symm⟩, hfb'⟩

/-- Consider a square of morphisms of cochain complexes `f : A ⟶ B`, `a : A ⟶ C`, `b : B ⟶ D`,
`g : C ⟶ D` that commutes up to homotopy (`Nonempty (Homotopy (f ≫ b) (a ≫ g))`). If `g` is a
termwise split surjection, then there is a morphism `a'` homotopic to `a` such that the square
commutes on the nose: `g ∘ a' = b ∘ f` (`a' ≫ g = f ≫ b`). -/
@[stacks 014H "(2)"]
theorem exists_homotopic_comm_of_isTermwiseSplitSurjection {Ac Bc Cc Dc : CochainComplex 𝒜 ℤ}
    (f : Ac ⟶ Bc) (a : Ac ⟶ Cc) (b : Bc ⟶ Dc) (g : Cc ⟶ Dc)
    (hsq : Nonempty (Homotopy (f ≫ b) (a ≫ g)))
    (hg : IsTermwiseSplitSurjection g) :
    ∃ a' : Ac ⟶ Cc, Nonempty (Homotopy a' a) ∧ a' ≫ g = f ≫ b := by
  obtain ⟨H⟩ := hsq
  let := fun n => (hg n)
  obtain ⟨a', ⟨ha'⟩, ha'g⟩ := HomotopyCategory.exists_homotopic_comp_eq_of_sections
    (fun i => section_ (g.f i)) (fun i => IsSplitEpi.id (g.f i)) H.symm
  exact ⟨a', ⟨ha'.symm⟩, ha'g⟩

end

end

section

@[expose] public section

/-! ### Independence of the triangle of a termwise split sequence from the splittings -/

open CategoryTheory CategoryTheory.Pretriangulated CochainComplex

/-- The triangles in `K(𝒜)` attached to two families of degreewise splittings of a short complex
`S` of cochain complexes are equal. -/
theorem CochainComplex.trianglehOfDegreewiseSplit_eq
    {C : Type*} [Category C] [Preadditive C]
    (S : ShortComplex (CochainComplex C ℤ))
    (σ σ' : (n : ℤ) → (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
    CochainComplex.trianglehOfDegreewiseSplit S σ
      = CochainComplex.trianglehOfDegreewiseSplit S σ' := by
  unfold trianglehOfDegreewiseSplit triangleOfDegreewiseSplit
  simp [HomotopyCategory.eq_of_homotopy _ _ (homotopyHomOfDegreewiseSplit S σ' σ)]

/-- The triangles in `K(𝒜)` attached to two families of degreewise splittings of a short complex
`S` of cochain complexes are equal, so they are isomorphic by an isomorphism whose three
components are the identities of `Q.obj S.X₁`, `Q.obj S.X₂`, `Q.obj S.X₃`. Equality transports
express these identities between the canonically equal objects of the two triangles. -/
@[stacks 05SS, sga "4½ Etat_0 1.2.4"]
theorem trianglehOfDegreewiseSplit_iso_of_identity
    {C : Type*} [Category C] [Preadditive C]
    (S : ShortComplex (CochainComplex C ℤ))
    (σ σ' : (n : ℤ) → (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
    ∃ e : CochainComplex.trianglehOfDegreewiseSplit S σ ≅
          CochainComplex.trianglehOfDegreewiseSplit S σ',
      e.hom.hom₁ = eqToHom (by simp) ∧ e.hom.hom₂ = eqToHom (by simp) ∧
        e.hom.hom₃ = eqToHom (by simp) := by
  have h := trianglehOfDegreewiseSplit_eq S σ σ'
  exact ⟨eqToIso h, by simp [Triangle.eqToHom_hom₁], by simp [Triangle.eqToHom_hom₂],
    by simp [Triangle.eqToHom_hom₃]⟩

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CochainComplex Limits Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- If the composite `f ≫ g` is null-homotopic then `g` factors
through the mapping cone of `f`, via the canonical inclusion `mappingCone.inr f`. -/
@[stacks 08RI "(1)"]
theorem exists_factorThrough_mappingCone
    {K L M : CochainComplex C ℤ} (f : K ⟶ L) (g : L ⟶ M)
    (H : Homotopy (f ≫ g) 0) :
    ∃ gbar : mappingCone f ⟶ M, mappingCone.inr f ≫ gbar = g :=
  ⟨HomologicalComplex.homotopyCofiber.desc f g H,
   HomologicalComplex.homotopyCofiber.inr_desc f g H⟩

/-- The projection `C(g)[-1] ⟶ L`, obtained by shifting the canonical triangle
projection `(mappingCone.triangle g).mor₃ : C(g) ⟶ L[1]` by `[-1]` and using the
identification `(L[1])[-1] ≅ L`. -/
noncomputable def pShift {L M : CochainComplex C ℤ} (g : L ⟶ M) :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj (mappingCone g) ⟶ L :=
  (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map ((mappingCone.triangle g).mor₃) ≫
    (CategoryTheory.shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1 : ℤ) (by ring)).hom.app L

/-- If the composite `f ≫ g` is null-homotopic, then `f[1]` lifts to some `fhat : K[1] ⟶ C(g)`
along the canonical triangle projection `C(g) ⟶ L[1]`. -/
theorem exists_lift_mappingCone_mor₃
    {K L M : CochainComplex C ℤ} (f : K ⟶ L) (g : L ⟶ M)
    (H : Homotopy (f ≫ g) 0) :
    ∃ fhat : (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj K ⟶ mappingCone g,
      fhat ≫ (mappingCone.triangle g).mor₃ =
        (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map f := by
  set α : HomComplex.Cocycle ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj K) L 1
      :=
    (HomComplex.Cocycle.ofHom f).leftShift 1 1 (by omega) with hα
  set β : HomComplex.Cochain ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj K) M 0
      :=
    (HomComplex.Cochain.ofHomotopy H).leftShift 1 0 (by omega) with hβ
  have key : HomComplex.δ 0 1 β +
      (α : HomComplex.Cochain _ _ 1).comp (HomComplex.Cochain.ofHom g) (by omega) = 0 := by
    have hcomp : ((HomComplex.Cochain.ofHom f).leftShift 1 1 (by omega)).comp
          (HomComplex.Cochain.ofHom g) (by omega)
        = (HomComplex.Cochain.ofHom (f ≫ g)).leftShift 1 1 (by omega) := by
      rw [HomComplex.Cochain.ofHom_comp f g,
        HomComplex.Cochain.leftShift_comp (HomComplex.Cochain.ofHom f) 1 1 (by omega)
          (HomComplex.Cochain.ofHom g) (by omega) (by omega)]
      simp
    rw [hβ, hα]
    rw [HomComplex.Cochain.δ_leftShift (HomComplex.Cochain.ofHomotopy H) 1 0 1 (by omega) 0 (by
        omega)]
    rw [HomComplex.δ_ofHomotopy H]
    rw [HomComplex.Cocycle.leftShift_coe, HomComplex.Cocycle.ofHom_coe f]
    rw [hcomp]
    simp only [HomComplex.Cochain.ofHom_zero, sub_zero, Int.negOnePow_one, Units.neg_smul, one_smul,
      neg_add_cancel]
  refine ⟨mappingCone.lift g α β key, ?_⟩
  ext p
  simp only [HomologicalComplex.comp_f, mappingCone.lift_f g α β key p (p + 1) (by omega),
    Preadditive.add_comp, Category.assoc, mappingCone.inr_f_triangle_mor₃_f,
    mappingCone.inl_v_triangle_mor₃_f g (p + 1) p (by omega), comp_zero, add_zero]
  rw [hα, HomComplex.Cocycle.leftShift_coe, HomComplex.Cocycle.ofHom_coe f]
  rw [HomComplex.Cochain.leftShift_v (HomComplex.Cochain.ofHom f) 1 1 (by omega) p (p + 1)
    (by omega) (p + 1) (by omega)]
  rw [HomComplex.Cochain.ofHom_v]
  rw [CochainComplex.shiftFunctor_map_f']
  norm_num
  exact Category.id_comp _

/-- If the composite `f ≫ g` is null-homotopic then `f` factors through the shifted mapping cone
`C(g)[-1]`, via the shifted projection `pShift g`. -/
@[stacks 08RI "(2)"]
theorem exists_factor_through_shifted_mappingCone
    {K L M : CochainComplex C ℤ} (f : K ⟶ L) (g : L ⟶ M)
    (H : Homotopy (f ≫ g) 0) :
    ∃ fbar : K ⟶ (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj (mappingCone g),
      fbar ≫ pShift g = f := by
  obtain ⟨fhat, hfhat⟩ := exists_lift_mappingCone_mor₃ f g H
  refine ⟨(CategoryTheory.shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1 : ℤ) (by
      ring)).inv.app K
      ≫ (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map fhat, ?_⟩
  rw [pShift]
  simp only [Category.assoc]
  rw [← Category.assoc ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map fhat),
    ← Functor.map_comp, hfhat]
  have nat := (CategoryTheory.shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1 : ℤ) (by
      ring)).hom.naturality f
  simp only [Functor.comp_map, Functor.id_map] at nat
  rw [nat, ← Category.assoc, Iso.inv_hom_id_app]
  simp

end

end

section

@[expose] public section

/-!
### An explicit factorisation through the shifted cone

The shifted cone `C(g)[-1]` is Mathlib's `CochainComplex.mappingCocone g`, so a morphism into it
is built by `CochainComplex.mappingCocone.lift`, and its two components are read off by
`CochainComplex.mappingCocone.fst` and `CochainComplex.mappingCocone.snd`. The projection
`pShift g` is `-mappingCocone.fst g` (`pShift_eq_homOf_leftShift_fst`).
-/

open CategoryTheory CochainComplex Limits Pretriangulated

/-- The shifted projection `pShift g : C(g)[-1] ⟶ L` is the morphism attached to the `1`-cocycle
`mappingCone.fst g` shifted by `-1`; equivalently, it is `-mappingCocone.fst g`. -/
theorem pShift_eq_homOf_leftShift_fst {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {L M : CochainComplex C ℤ} (g : L ⟶ M) :
    pShift g = HomComplex.Cocycle.homOf
      ((mappingCone.fst g).leftShift (-1) 0 (by omega)) := by
  ext p
  simp [pShift, mappingCone.triangle, HomComplex.Cocycle.leftShift_coe,
    HomComplex.Cochain.leftShift_v (mappingCone.fst g).1 (-1) 0 (by omega) p p (add_zero p)
      (p + -1) (by omega),
    HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    HomComplex.Cochain.v_comp_XIsoOfEq_hom,
    shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]

/-- If the composite `f ≫ g` is null homotopic by
`H`, this is the morphism `K ⟶ C(g)[-1]` through which `f` factors: its component along
`pShift g` is `f` (see `factorThroughShiftedMappingCone_comp_pShift`) and its component along
`mappingCocone.snd g` is the null homotopy `H` itself (see
`factorThroughShiftedMappingCone_comp_snd`). -/
noncomputable def factorThroughShiftedMappingCone {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {K L M : CochainComplex C ℤ} (f : K ⟶ L) (g : L ⟶ M)
    (H : Homotopy (f ≫ g) 0) :
    K ⟶ (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj (mappingCone g) :=
  mappingCocone.lift g (-f) (HomComplex.Cochain.ofHomotopy H)
    (by simp [HomComplex.δ_ofHomotopy H])

/-- Composing
`factorThroughShiftedMappingCone f g H` with the shifted projection `C(g)[-1] ⟶ L` returns
`f`. -/
theorem factorThroughShiftedMappingCone_comp_pShift {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {K L M : CochainComplex C ℤ} (f : K ⟶ L) (g : L ⟶ M)
    (H : Homotopy (f ≫ g) 0) :
    factorThroughShiftedMappingCone f g H ≫ pShift g = f := by
  rw [pShift_eq_homOf_leftShift_fst]
  refine neg_inj.mp ?_
  rw [← Preadditive.comp_neg]
  exact mappingCocone.lift_fst g (-f) (HomComplex.Cochain.ofHomotopy H)
    (by simp [HomComplex.δ_ofHomotopy H])

/-- Composing
`factorThroughShiftedMappingCone f g H` with the degree `-1` projection
`mappingCocone.snd g : C(g)[-1] ⟶ M` returns the null homotopy `H`, viewed as a cochain of
degree `-1`. -/
theorem factorThroughShiftedMappingCone_comp_snd {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {K L M : CochainComplex C ℤ} (f : K ⟶ L) (g : L ⟶ M)
    (H : Homotopy (f ≫ g) 0) :
    (HomComplex.Cochain.ofHom (factorThroughShiftedMappingCone f g H)).comp
        ((mappingCone.snd g).leftShift (-1) (-1) (by omega)) (by omega) =
      HomComplex.Cochain.ofHomotopy H := by
  have h : (HomComplex.Cochain.ofHom
        (mappingCocone.lift g (-f) (HomComplex.Cochain.ofHomotopy H)
          (by simp [HomComplex.δ_ofHomotopy H]))).comp
        (mappingCocone.snd g) (by omega) = HomComplex.Cochain.ofHomotopy H := by
    rw [mappingCocone.ofHom_lift, mappingCocone.liftCochain_comp_snd]
  exact h

namespace CochainComplex

/-- Composing the identification `Hⁿ(C(g)[-1]) ≅ Hᵐ(C(g))` of `m = n - 1` with the map induced
by the third morphism `C(g) ⟶ L[1]` of the cone triangle and with the identification
`Hᵐ(L[1]) ≅ Hⁿ(L)` gives the map induced by `pShift g : C(g)[-1] ⟶ L`. -/
theorem homologyMap_pShift {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    [CategoryWithHomology C] {L M : CochainComplex C ℤ} (g : L ⟶ M) (n m : ℤ)
    (hm : -1 + n = m) :
    HomologicalComplex.homologyMap (pShift g) n =
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso (-1) n m hm).hom.app
            (mappingCone g) ≫
          HomologicalComplex.homologyMap (mappingCone.triangle g).mor₃ m ≫
        ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 m n
          (by omega)).hom.app L := by
  have h := (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ)
      0).shiftIso_hom_app_comp_shiftMap_of_add_eq_zero (mappingCone.triangle g).mor₃
    (-1 : ℤ) (by omega) m n (by omega)
  rw [Functor.shiftMap] at h
  exact h.symm

/-! ### The long exact sequence of the shifted cone

For a morphism `g : L ⟶ M` of cochain complexes in an abelian category, the cone triangle

`L --g--> M --inr--> C(g) --mor₃--> L[1]`

is distinguished in the homotopy category, and the homology functor is homological there, so the
cone triangle gives a long exact sequence of cohomology objects whose maps are the ones induced
by the canonical maps `g`, `mappingCone.inr g` and `(mappingCone.triangle g).mor₃`. The
connecting morphism `coneHomologyConnecting` out of `Hⁿ(M)` has target `H^{n+1}(C(g)[-1])`.
-/

section ConeHomology

variable {C : Type*} [Category C] [Abelian C] {L M : CochainComplex C ℤ}

open HomotopyCategory

/-- The identification `Hᵐ(C(g)[-1]) ≅ Hⁿ(C(g))`, for `-1 + m = n`. -/
noncomputable abbrev shiftedMappingConeHomologyIso (g : L ⟶ M) (m n : ℤ) (hn : -1 + m = n) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj
        (mappingCone g)).homology m ≅
      (mappingCone g).homology n :=
  ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso (-1) m n hn).app
    (mappingCone g)

/-- The connecting morphism `Hⁿ(M) ⟶ H^{n+1}(C(g)[-1])` of the cone: the map induced by the
canonical inclusion `mappingCone.inr g : M ⟶ C(g)`, read through the identification
`H^{n+1}(C(g)[-1]) ≅ Hⁿ(C(g))`. -/
noncomputable def coneHomologyConnecting (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    M.homology n ⟶
      ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj
        (mappingCone g)).homology m :=
  HomologicalComplex.homologyMap (mappingCone.inr g) n ≫
    (shiftedMappingConeHomologyIso g m n hn).inv

/-- A null homotopic morphism of cochain complexes induces the zero map on cohomology. -/
private theorem homologyMap_eq_zero_of_quotient_map_eq_zero {K K' : CochainComplex C ℤ}
    (φ : K ⟶ K') (hφ : (quotient C (ComplexShape.up ℤ)).map φ = 0) (n : ℤ) :
    HomologicalComplex.homologyMap φ n = 0 := by
  have h := (homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality φ
  dsimp only [Functor.comp_map] at h
  rw [hφ, Functor.map_zero, Limits.zero_comp] at h
  exact Limits.zero_of_epi_comp
    ((homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.app K) h.symm

/-- The composite `Hⁿ(L) ⟶ Hⁿ(M) ⟶ Hⁿ(C(g))` of the cone vanishes. -/
theorem homologyMap_comp_homologyMap_inr (g : L ⟶ M) (n : ℤ) :
    HomologicalComplex.homologyMap g n ≫
        HomologicalComplex.homologyMap (mappingCone.inr g) n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp]
  refine homologyMap_eq_zero_of_quotient_map_eq_zero _ ?_ n
  rw [Functor.map_comp]
  exact Pretriangulated.comp_distTriang_mor_zero₁₂ _
    (mappingCone_triangleh_distinguished g)

/-- Exactness of `Hⁿ(L) ⟶ Hⁿ(M) ⟶ Hⁿ(C(g))`, the long exact sequence of the cone at the
target of `g`. -/
theorem mappingCone_homology_exact₂ (g : L ⟶ M) (n : ℤ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap g n)
      (HomologicalComplex.homologyMap (mappingCone.inr g) n)
      (homologyMap_comp_homologyMap_inr g n)).Exact := by
  have h₁ := ((homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality g).symm
  have h₂ :=
    ((homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality (mappingCone.inr g)).symm
  refine (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app L)
    ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app M)
    ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app (mappingCone g)) h₁ h₂)).1
    ((homologyFunctor C (ComplexShape.up ℤ) 0).homologySequence_exact₂
      (mappingCone.triangleh g) (mappingCone_triangleh_distinguished g) n)

/-- `Hⁿ(g) ≫ ∂ = 0` for the connecting morphism of the cone. -/
theorem homologyMap_comp_coneHomologyConnecting (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    HomologicalComplex.homologyMap g n ≫ coneHomologyConnecting g n m hn = 0 := by
  rw [coneHomologyConnecting, ← Category.assoc, homologyMap_comp_homologyMap_inr,
    Limits.zero_comp]

/-- Exactness of `Hⁿ(L) ⟶ Hⁿ(M) --∂--> H^{n+1}(C(g)[-1])`, the long exact sequence of the
cone at the target of `g`. -/
theorem mappingCone_homology_exact_target (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    (ShortComplex.mk (HomologicalComplex.homologyMap g n) (coneHomologyConnecting g n m hn)
      (homologyMap_comp_coneHomologyConnecting g n m hn)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (mappingCone_homology_exact₂ g n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (shiftedMappingConeHomologyIso g m n hn).symm ?_ ?_
  · simp
  · simp [coneHomologyConnecting]

/-! #### Exactness at the cone and at the source of `g` -/

section Conjugation

variable {X X' Y Y' Z W : C}

omit [Abelian C] in
/-- A morphism conjugated by two isomorphisms, in the form in which the conjugation cancels
against one of them. -/
private theorem hom_comp_eq_comp_hom (eX : X' ≅ X) (eY : Y' ≅ Y) (f : X ⟶ Y) (d : X' ⟶ Y')
    (hd : d = eX.hom ≫ f ≫ eY.inv) : eX.hom ≫ f = d ≫ eY.hom := by
  rw [hd]; simp

/-- A composite that vanishes because its conjugate does. -/
private theorem comp_eq_zero_of_conj (eX : X' ≅ X) (eY : Y' ≅ Y) (f : X ⟶ Y) (p : Y ⟶ Z)
    (d : X' ⟶ Y') (q : Y' ⟶ W) (r : W ⟶ Z) (hd : d = eX.hom ≫ f ≫ eY.inv)
    (hnat : eY.hom ≫ p = q ≫ r) (hz : d ≫ q = 0) : f ≫ p = 0 := by
  have hf : f = eX.inv ≫ d ≫ eY.hom := by rw [hd]; simp
  rw [hf, Category.assoc, Category.assoc, hnat, ← Category.assoc d, hz, Limits.zero_comp,
    Limits.comp_zero]

omit [Abelian C] in
/-- The commuting square of a transport along an isomorphism of the middle term, in the form
`ShortComplex.isoMk` asks for it. -/
private theorem inv_comp_eq_comp_id (e : X ≅ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : c = e.hom ≫ b) :
    e.inv ≫ c = b ≫ 𝟙 Z := by
  rw [hc]; simp

/-- A composite through the inverse of an isomorphism vanishes when the straightened composite
does. -/
private theorem comp_inv_comp_eq_zero (e : X ≅ Y) (a : W ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (hc : c = e.hom ≫ b) (h : a ≫ b = 0) : (a ≫ e.inv) ≫ c = 0 := by
  rw [hc, Category.assoc, Iso.inv_hom_id_assoc, h]

/-- A composite vanishes when a factorisation of its first morphism makes it vanish. -/
private theorem comp_comp_eq_zero (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : W ⟶ Y)
    (hd : d = a ≫ b) (h : b ≫ c = 0) : d ≫ c = 0 := by
  rw [hd, Category.assoc, h, Limits.comp_zero]

end Conjugation

/-- The map `Hⁿ(C(g)) ⟶ Hᵐ(L)` of the long exact sequence of the cone triangle: the
`CategoryTheory.Functor.shiftMap` of the third morphism `C(g) ⟶ L[1]` of that triangle, with its
source and target fixed to be the cohomology objects of `C(g)` and of `L`. -/
noncomputable def coneHomologyToSource (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    (mappingCone g).homology n ⟶ L.homology m :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
    (mappingCone.triangle g).mor₃ n m (by omega)

/-- `pShift g` on cohomology is the identification `Hᵐ(C(g)[-1]) ≅ Hⁿ(C(g))` followed by the map
`Hⁿ(C(g)) ⟶ Hᵐ(L)` of the long exact sequence of the cone triangle. -/
theorem homologyMap_pShift_eq (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    HomologicalComplex.homologyMap (pShift g) m =
      (shiftedMappingConeHomologyIso g m n hn).hom ≫ coneHomologyToSource g n m hn := by
  rw [homologyMap_pShift g m n hn]
  rfl

/-- The connecting morphism of the homology sequence of the cone triangle, read through
`HomotopyCategory.homologyFunctorFactors`, is `coneHomologyToSource`. -/
private theorem homologySequenceδ_triangleh_eq (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    (homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        (mappingCone.triangleh g) n m (by omega) =
      (homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.app (mappingCone g) ≫
        coneHomologyToSource g n m hn ≫
          (homologyFunctorFactors C (ComplexShape.up ℤ) m).inv.app L :=
  CochainComplex.homologySequenceδ_quotient_mapTriangle_obj (mappingCone.triangle g) n m (by omega)

/-- `coneHomologyToSource` and the connecting morphism of the homology sequence of the cone
triangle agree after `HomotopyCategory.homologyFunctorFactors`. -/
private theorem homologyFunctorFactors_comp_coneHomologyToSource (g : L ⟶ M) (n m : ℤ)
    (hn : -1 + m = n) :
    (homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.app (mappingCone g) ≫
        coneHomologyToSource g n m hn =
      (homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
          (mappingCone.triangleh g) n m (by omega) ≫
        (homologyFunctorFactors C (ComplexShape.up ℤ) m).hom.app L :=
  hom_comp_eq_comp_hom ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app (mappingCone g))
    ((homologyFunctorFactors C (ComplexShape.up ℤ) m).app L) (coneHomologyToSource g n m hn)
    ((homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
      (mappingCone.triangleh g) n m (by omega))
    (homologySequenceδ_triangleh_eq g n m hn)

/-- The composite `Hⁿ(M) ⟶ Hⁿ(C(g)) ⟶ Hᵐ(L)` of the cone triangle vanishes. -/
private theorem homologyMap_inr_comp_coneHomologyToSource (g : L ⟶ M) (n m : ℤ)
    (hn : -1 + m = n) :
    HomologicalComplex.homologyMap (mappingCone.inr g) n ≫ coneHomologyToSource g n m hn = 0 := by
  have hz : (mappingCone.triangle g).mor₂ ≫ (mappingCone.triangle g).mor₃ = 0 :=
    mappingCone.inr_triangleδ g
  have h : ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shift n).map
        (mappingCone.triangle g).mor₂ ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (mappingCone.triangle g).mor₃ n m (by omega) = 0 := by
    rw [← Functor.shiftMap_comp', hz, Functor.shiftMap_zero]
  exact h

/-- Exactness of `Hⁿ(M) ⟶ Hⁿ(C(g)) ⟶ Hᵐ(L)`: the long exact sequence of the cone triangle at
the cone, before the shift is put back in. -/
private theorem mappingCone_homology_exact_cone' (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (mappingCone.inr g) n)
      (coneHomologyToSource g n m hn)
      (homologyMap_inr_comp_coneHomologyToSource g n m hn)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((homologyFunctor C (ComplexShape.up ℤ) 0).homologySequence_exact₃
      (mappingCone.triangleh g) (mappingCone_triangleh_distinguished g) n m (by omega))
  exact ShortComplex.isoMk ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app M)
    ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app (mappingCone g))
    ((homologyFunctorFactors C (ComplexShape.up ℤ) m).app L)
    ((homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality (mappingCone.inr g)).symm
    (homologyFunctorFactors_comp_coneHomologyToSource g n m hn)

/-- The composite `Hⁿ(C(g)) ⟶ Hᵐ(L) ⟶ Hᵐ(M)` of the cone triangle vanishes. -/
private theorem coneHomologyToSource_comp_homologyMap (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    coneHomologyToSource g n m hn ≫ HomologicalComplex.homologyMap g m = 0 :=
  comp_eq_zero_of_conj ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app (mappingCone g))
    ((homologyFunctorFactors C (ComplexShape.up ℤ) m).app L) (coneHomologyToSource g n m hn)
    (HomologicalComplex.homologyMap g m)
    ((homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
      (mappingCone.triangleh g) n m (by omega))
    (((homologyFunctor C (ComplexShape.up ℤ) 0).shift m).map (mappingCone.triangleh g).mor₁)
    ((homologyFunctorFactors C (ComplexShape.up ℤ) m).hom.app M)
    (homologySequenceδ_triangleh_eq g n m hn)
    ((homologyFunctorFactors C (ComplexShape.up ℤ) m).hom.naturality g).symm
    ((homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ_comp
      (mappingCone.triangleh g) (mappingCone_triangleh_distinguished g) n m (by omega))

/-- Exactness of `Hⁿ(C(g)) ⟶ Hᵐ(L) ⟶ Hᵐ(M)`: the long exact sequence of the cone triangle at
the source of `g`, before the shift is put back in. -/
private theorem mappingCone_homology_exact_source' (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    (ShortComplex.mk (coneHomologyToSource g n m hn) (HomologicalComplex.homologyMap g m)
      (coneHomologyToSource_comp_homologyMap g n m hn)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((homologyFunctor C (ComplexShape.up ℤ) 0).homologySequence_exact₁
      (mappingCone.triangleh g) (mappingCone_triangleh_distinguished g) n m (by omega))
  exact ShortComplex.isoMk ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app (mappingCone g))
    ((homologyFunctorFactors C (ComplexShape.up ℤ) m).app L)
    ((homologyFunctorFactors C (ComplexShape.up ℤ) m).app M)
    (homologyFunctorFactors_comp_coneHomologyToSource g n m hn)
    ((homologyFunctorFactors C (ComplexShape.up ℤ) m).hom.naturality g).symm

/-- The composite `Hⁿ(M) --∂--> Hᵐ(C(g)[-1]) --pShift--> Hᵐ(L)` of the cone vanishes. -/
theorem coneHomologyConnecting_comp_homologyMap_pShift (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    coneHomologyConnecting g n m hn ≫ HomologicalComplex.homologyMap (pShift g) m = 0 :=
  comp_inv_comp_eq_zero _ _ _ _ (homologyMap_pShift_eq g n m hn)
    (homologyMap_inr_comp_coneHomologyToSource g n m hn)

/-- Exactness of `Hⁿ(M) --∂--> Hᵐ(C(g)[-1]) --pShift--> Hᵐ(L)`, the long exact sequence of the
cone at the shifted cone itself. -/
theorem mappingCone_homology_exact_cone (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    (ShortComplex.mk (coneHomologyConnecting g n m hn)
      (HomologicalComplex.homologyMap (pShift g) m)
      (coneHomologyConnecting_comp_homologyMap_pShift g n m hn)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (mappingCone_homology_exact_cone' g n m hn)
  exact ShortComplex.isoMk (Iso.refl _) (shiftedMappingConeHomologyIso g m n hn).symm
    (Iso.refl _) (Category.id_comp _)
    (inv_comp_eq_comp_id _ _ _ (homologyMap_pShift_eq g n m hn))

/-- The composite `Hᵐ(C(g)[-1]) --pShift--> Hᵐ(L) ⟶ Hᵐ(M)` of the cone vanishes. -/
theorem homologyMap_pShift_comp_homologyMap (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    HomologicalComplex.homologyMap (pShift g) m ≫ HomologicalComplex.homologyMap g m = 0 :=
  comp_comp_eq_zero _ _ _ _ (homologyMap_pShift_eq g n m hn)
    (coneHomologyToSource_comp_homologyMap g n m hn)

/-- Exactness of `Hᵐ(C(g)[-1]) --pShift--> Hᵐ(L) ⟶ Hᵐ(M)`, the long exact sequence of the cone
at the source of `g`. -/
theorem mappingCone_homology_exact_source (g : L ⟶ M) (n m : ℤ) (hn : -1 + m = n) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (pShift g) m)
      (HomologicalComplex.homologyMap g m)
      (homologyMap_pShift_comp_homologyMap g n m hn)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (mappingCone_homology_exact_source' g n m hn)
  exact ShortComplex.isoMk (shiftedMappingConeHomologyIso g m n hn).symm (Iso.refl _)
    (Iso.refl _) (inv_comp_eq_comp_id _ _ _ (homologyMap_pShift_eq g n m hn))
    ((Category.id_comp _).trans (Category.comp_id _).symm)

end ConeHomology

end CochainComplex

end

end
