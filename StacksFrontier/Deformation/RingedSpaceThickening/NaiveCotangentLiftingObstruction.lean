module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The obstruction to lifting a morphism of deformations (Stacks 08U8)

In the situation of the source's diagram, reduced as in its proof to sheaves of rings on one
space, write `NL(α) = (ℐ/ℐ² ⟶ Ω)` for the two-term naive cotangent complex of `𝒪_{X₁}` over
`𝒪_{S₁}` attached to the presentation `α` of Step 1 of the proof, and `𝒢₂ = Ker(i₂^♯)`. Step 1
produces from the two deformations a homomorphism `ξ : ℐ/ℐ² ⟶ 𝒢₂`, and its class in
`Ext¹(NL(α), 𝒢₂)` vanishes exactly when a morphism `X'₂ ⟶ X'₁` fitting into the diagram
compatibly with `ν` exists. The set of those morphisms is then a principal homogeneous space
under `Hom(H⁰(NL(α)), 𝒢₂) = Hom(Ω_{X₁/S₁}, 𝒢₂)`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm`: the two-term complex
  `NL(α) = (ℐ/ℐ² ⟶ Ω)`, presented by the distinguished triangle of its two-term structure.
* `AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.conormalExtClass`: the class in
  `Ext¹(NL(α), 𝒢)` of a homomorphism `ℐ/ℐ² ⟶ 𝒢`, and
  `NaiveCotangentTwoTerm.obstruction`, the restriction of a class in `Ext¹(NL(α), 𝒢)` along
  `Ω ⟶ NL(α)`.
* `AlgebraicGeometry.RingedSpaceThickening.liftingObstruction`: the class of Step 1 of the
  source's proof, the class in `Ext¹(NL(α), 𝒢₂)` of the difference homomorphism `ξ`.
* `AlgebraicGeometry.RingedSpaceThickening.liftTranslate`: translation of a morphism
  `X'₂ ⟶ X'₁` fitting into the diagram by a homomorphism `Ω_{X₁/S₁} ⟶ 𝒢₂`.

## Main results

* `NaiveCotangentTwoTerm.obstruction_eq_zero_iff`: a class in `Ext¹(NL(α), 𝒢)` is the class of
  a homomorphism out of the conormal module exactly when its restriction to the degree `0` term
  vanishes.
* `NaiveCotangentTwoTerm.conormalExtClass_eq_zero_iff`: the class of `ξ : ℐ/ℐ² ⟶ 𝒢` vanishes
  exactly when `ξ` factors as `ℐ/ℐ² ⟶ Ω ⟶ 𝒢`.
* `AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff`: the formal step of
  clause (1) of Stacks 08U8: given a bijection between the lifts and the factorizations of `ξ`
  through `Ω`, the class of `ξ` vanishes exactly when a lift exists.
* `AlgebraicGeometry.RingedSpaceThickening.liftTranslate_zero`,
  `liftTranslate_add` and `existsUnique_liftTranslate`: the formal step of clause (2): under
  such a bijection the lifts form a principal homogeneous space under `Hom(H⁰(NL(α)), 𝒢₂)`.

## Implementation notes

`Ext¹(X, 𝒢)` is the group `X ⟶ 𝒢⟦1⟧` of the ambient triangulated category, as in
`StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic`, and `NL(α)` enters through the
distinguished triangle of its two-term structure rather than through the complex itself. That
triangle is data: the library builds `NL(α)` as
`Stacks.SheafOfModules.presentationNaiveCotangentComplex`, a `CochainComplex` made with
`HomologicalComplex.double`, but does not produce the distinguished triangle relating it to its
two terms.

The class is pinned, not asserted to exist: `liftingObstruction` *is* the class of the
homomorphism `ξ` of Step 1 of the source's proof, so a statement about it is a statement about
that recipe. Likewise `liftTranslate` is a definition and
`liftTranslate_eq` records the formula that determines it, so the principal homogeneous space
structure is pinned too; a bare existence statement for a group action would be satisfied by
any reparametrisation of it.

This file is the formal, category-theoretic part of the source's argument: the set of lifts
enters through an equivalence `e` with the factorizations of `ξ` through `Ω`, and the acting
group is written as the Hom out of the cokernel of the differential of `NL(α)`. The complete
lemma, for an arbitrary diagram of ringed spaces as in the source, with Steps 1 to 3 proved and
the acting group and obstruction group in the source's spelling, is
`AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.lifting_obstruction_and_torsor`
in `StacksFrontier.Deformation.RingedSpaceThickening.DeformationLiftingObstruction`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u v' u'

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### Shifts of morphisms in the image of a full functor -/

section Shift

variable {M : Type u} [Category.{v} M] {D : Type u'} [Category.{v'} D] [HasShift D ℤ]

/-- A morphism between shifts of objects in the image of a full functor is the shift of a
morphism of the category of origin. -/
theorem exists_eq_shift_map (single : M ⥤ D) [single.Full] {A B : M}
    (g : (single.obj A)⟦(1 : ℤ)⟧ ⟶ (single.obj B)⟦(1 : ℤ)⟧) :
    ∃ f : A ⟶ B, g = (single.map f)⟦(1 : ℤ)⟧' := by
  obtain ⟨u, hu⟩ := Functor.map_surjective (shiftFunctor D (1 : ℤ)) g
  obtain ⟨f, hf⟩ := Functor.map_surjective single u
  exact ⟨f, by rw [hf, hu]⟩

end Shift

/-! ### The two-term naive cotangent complex and its degree one Ext group -/

section TwoTerm

variable {M : Type u} [Category.{v} M] {D : Type u'} [Category.{v'} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- The two-term naive cotangent complex `NL(α) = (ℐ/ℐ² ⟶ Ω)` of a presentation, presented
inside a triangulated category by the distinguished triangle
`ℐ/ℐ² ⟶ Ω ⟶ NL(α) ⟶ (ℐ/ℐ²)⟦1⟧` of its two-term structure. -/
structure NaiveCotangentTwoTerm (single : M ⥤ D) where
  /-- The conormal module `ℐ/ℐ²`, the degree `-1` term. -/
  conormal : M
  /-- The degree `0` term `Ω`. -/
  base : M
  /-- The differential `ℐ/ℐ² ⟶ Ω`. -/
  d : conormal ⟶ base
  /-- The complex, as an object of the triangulated category. -/
  obj : D
  /-- The inclusion of the degree `0` term. -/
  incl : single.obj base ⟶ obj
  /-- The projection onto the shifted conormal module. -/
  proj : obj ⟶ (single.obj conormal)⟦(1 : ℤ)⟧
  /-- The two-term structure: the three maps form a distinguished triangle. -/
  distinguished : Triangle.mk (single.map d) incl proj ∈ distTriang D

/-- Every morphism `d : ℐ/ℐ² ⟶ Ω` of `ℬ`-modules is the differential of a two-term complex:
the cone on `d` in the triangulated category, which for `d` the conormal map of a presentation
is `NL(α)`. -/
theorem exists_naiveCotangentTwoTerm (single : M ⥤ D) {C B : M} (d : C ⟶ B) :
    ∃ P : NaiveCotangentTwoTerm single, P.conormal = C ∧ P.base = B := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (single.map d)
  exact ⟨⟨C, B, d, Z, g, h, hT⟩, rfl, rfl⟩

namespace NaiveCotangentTwoTerm

variable {single : M ⥤ D} (P : NaiveCotangentTwoTerm single) (G : M)

/-- The class in `Ext¹(NL(α), 𝒢)` of a homomorphism `f : ℐ/ℐ² ⟶ 𝒢` out of the conormal
module. -/
def conormalExtClass (f : P.conormal ⟶ G) : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧ :=
  P.proj ≫ (single.map f)⟦(1 : ℤ)⟧'

/-- The obstruction to writing a class in `Ext¹(NL(α), 𝒢)` as the class of a homomorphism out
of the conormal module: its restriction along `Ω ⟶ NL(α)`. -/
def obstruction (ξ : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧) :
    single.obj P.base ⟶ (single.obj G)⟦(1 : ℤ)⟧ :=
  P.incl ≫ ξ

/-- The inclusion of the degree `0` term followed by the projection onto the shifted conormal
module is zero. -/
theorem incl_comp_proj : P.incl ≫ P.proj = 0 :=
  comp_distTriang_mor_zero₂₃ _ P.distinguished

/-- The projection onto the shifted conormal module followed by the shifted differential is
zero. -/
theorem proj_comp_shift_d : P.proj ≫ (single.map P.d)⟦(1 : ℤ)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ _ P.distinguished

/-- A class in `Ext¹(NL(α), 𝒢)` is the class of a homomorphism `ℐ/ℐ² ⟶ 𝒢` out of the conormal
module exactly when its restriction to the degree `0` term `Ω` vanishes. -/
theorem obstruction_eq_zero_iff [single.Full] (ξ : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧) :
    P.obstruction G ξ = 0 ↔ ∃ f : P.conormal ⟶ G, ξ = P.conormalExtClass G f := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ P.distinguished ξ h
    obtain ⟨f, hf⟩ := exists_eq_shift_map single g
    refine ⟨f, ?_⟩
    rw [hg, hf]
    rfl
  · rintro ⟨f, rfl⟩
    change P.incl ≫ P.proj ≫ _ = 0
    rw [← Category.assoc, P.incl_comp_proj, Limits.zero_comp]

end NaiveCotangentTwoTerm

end TwoTerm

/-! ### Vanishing of the class of a conormal homomorphism -/

section Factor

variable {M : Type u} [Category.{v} M] [Preadditive M] {D : Type u'} [Category.{v'} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] {single : M ⥤ D} [single.Full] [single.Faithful] [single.Additive]

namespace NaiveCotangentTwoTerm

/-- The class of a homomorphism `ξ : ℐ/ℐ² ⟶ 𝒢` out of the conormal module vanishes in
`Ext¹(NL(α), 𝒢)` exactly when `ξ` factors as `ℐ/ℐ² ⟶ Ω ⟶ 𝒢` through the degree `0` term. -/
theorem conormalExtClass_eq_zero_iff (P : NaiveCotangentTwoTerm single) (G : M)
    (ξ : P.conormal ⟶ G) :
    P.conormalExtClass G ξ = 0 ↔ ∃ θ : P.base ⟶ G, P.d ≫ θ = ξ := by
  constructor
  · intro h
    have h' : (Triangle.mk (single.map P.d) P.incl P.proj).rotate.mor₂ ≫
        (single.map ξ)⟦(1 : ℤ)⟧' = 0 := h
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ P.distinguished)
      ((single.map ξ)⟦(1 : ℤ)⟧') h'
    obtain ⟨θ, hθ⟩ := exists_eq_shift_map single g
    have hg' : (single.map ξ)⟦(1 : ℤ)⟧' =
        (-(single.map P.d)⟦(1 : ℤ)⟧') ≫ (single.map θ)⟦(1 : ℤ)⟧' := by
      rw [hg, hθ]
      rfl
    refine ⟨-θ, single.map_injective (Functor.map_injective (shiftFunctor D (1 : ℤ)) ?_)⟩
    rw [hg']
    simp only [Functor.map_comp, Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp]
  · rintro ⟨θ, rfl⟩
    change P.proj ≫ (single.map (P.d ≫ θ))⟦(1 : ℤ)⟧' = 0
    rw [single.map_comp, Functor.map_comp, ← Category.assoc, P.proj_comp_shift_d,
      Limits.zero_comp]

end NaiveCotangentTwoTerm

end Factor

/-! ### The obstruction class -/

section Obstruction

variable {M : Type u} [Category.{v} M] [Abelian M] {D : Type u'} [Category.{v'} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] {single : M ⥤ D} [single.Full] [single.Faithful] [single.Additive]

/-- The obstruction class of Step 1 of the proof of [Stacks Project, Tag 08U8]: the class in
`Ext¹(NL(α), 𝒢₂)` of the difference homomorphism `ξ : ℐ/ℐ² ⟶ 𝒢₂` read off there from the two
deformations. -/
def liftingObstruction (P : NaiveCotangentTwoTerm single) (G : M) (ξ : P.conormal ⟶ G) :
    P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧ :=
  P.conormalExtClass G ξ

/-- The formal step of clause (1) of [Stacks Project, Tag 08U8]: if the set `Lift` is in
bijection with the factorizations of `ξ : ℐ/ℐ² ⟶ 𝒢₂` through `Ω` (Steps 1 to 3 of the source's
proof), the class of `ξ` in `Ext¹(NL(α), 𝒢₂)` vanishes if and only if `Lift` is nonempty. -/
theorem liftingObstruction_eq_zero_iff (P : NaiveCotangentTwoTerm single) (G : M)
    (ξ : P.conormal ⟶ G) {Lift : Type*} (e : Lift ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ}) :
    liftingObstruction P G ξ = 0 ↔ Nonempty Lift := by
  rw [liftingObstruction, P.conormalExtClass_eq_zero_iff G ξ]
  constructor
  · rintro ⟨θ, hθ⟩
    exact ⟨e.symm ⟨θ, hθ⟩⟩
  · rintro ⟨p⟩
    exact ⟨(e p).1, (e p).2⟩

end Obstruction

/-! ### The principal homogeneous space structure -/

section Torsor

variable {M : Type u} [Category.{v} M] [Abelian M] {D : Type u'} [Category.{v'} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] {single : M ⥤ D}

variable (P : NaiveCotangentTwoTerm single) (G : M) (ξ : P.conormal ⟶ G) {Lift : Type*}
  (e : Lift ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ})

/-- Translation of a morphism `X'₂ ⟶ X'₁` fitting into the source's diagram by a homomorphism
`Ω_{X₁/S₁} = H⁰(NL(α)) ⟶ 𝒢₂`: the corresponding factorization of `ξ` through `Ω` is changed by
the composite `Ω ⟶ H⁰(NL(α)) ⟶ 𝒢₂`. -/
noncomputable def liftTranslate (a : cokernel P.d ⟶ G) (p : Lift) : Lift :=
  e.symm ⟨(e p).1 + cokernel.π P.d ≫ a, by
    rw [Preadditive.comp_add, (e p).2, ← Category.assoc, cokernel.condition, Limits.zero_comp,
      add_zero]⟩

/-- The formula determining `liftTranslate`. -/
theorem liftTranslate_eq (a : cokernel P.d ⟶ G) (p : Lift) :
    (e (liftTranslate P G ξ e a p)).1 = (e p).1 + cokernel.π P.d ≫ a := by
  rw [liftTranslate, Equiv.apply_symm_apply]

/-- `liftTranslate a p = q` exactly when the factorization of `q` is that of `p` plus `π ≫ a`. -/
private theorem liftTranslate_eq_iff (a : cokernel P.d ⟶ G) (p q : Lift) :
    liftTranslate P G ξ e a p = q ↔ (e q).1 = (e p).1 + cokernel.π P.d ≫ a := by
  rw [← e.injective.eq_iff, Subtype.ext_iff, liftTranslate_eq, eq_comm]

/-- The zero homomorphism acts trivially (formal step of clause (2) of Stacks 08U8). -/
theorem liftTranslate_zero (p : Lift) : liftTranslate P G ξ e 0 p = p := by
  rw [liftTranslate_eq_iff, Limits.comp_zero, add_zero]

/-- Translation is additive in the translating homomorphism (formal step of clause (2) of
Stacks 08U8). -/
theorem liftTranslate_add (a b : cokernel P.d ⟶ G) (p : Lift) :
    liftTranslate P G ξ e a (liftTranslate P G ξ e b p) = liftTranslate P G ξ e (a + b) p := by
  refine e.injective (Subtype.ext ?_)
  simp only [liftTranslate_eq, Preadditive.comp_add]
  abel

/-- Translation is simply transitive: any element of `Lift` is carried to any other by exactly
one homomorphism `H⁰(NL(α)) ⟶ 𝒢₂` (formal step of clause (2) of Stacks 08U8). -/
theorem existsUnique_liftTranslate (p q : Lift) :
    ∃! a : cokernel P.d ⟶ G, liftTranslate P G ξ e a p = q := by
  refine ⟨cokernel.desc P.d ((e q).1 - (e p).1) ?_, ?_, ?_⟩
  · rw [Preadditive.comp_sub, (e q).2, (e p).2, sub_self]
  · simp only [liftTranslate_eq_iff, cokernel.π_desc]
    abel
  · intro a ha
    refine (cancel_epi (cokernel.π P.d)).1 ?_
    rw [cokernel.π_desc]
    exact eq_sub_of_add_eq' ((liftTranslate_eq_iff P G ξ e a p q).1 ha).symm

end Torsor

end AlgebraicGeometry.RingedSpaceThickening

end
