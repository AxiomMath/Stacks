module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge

/-!
# Invertibility of the edge morphism in a range of degrees

Let `P : A ⥤ B` be additive, left exact and preserving injective objects, let `Q : B ⥤ D` be
additive, and let `X : A`.  The edge morphism
`Stacks.Cohomology.RightDerivedEdge.edge` of the pair `(P, Q)` is the natural transformation

  `RⁱQ (P X) ⟶ Rⁱ(Q ∘ P) X`.

This file proves that it is an **isomorphism in degree `i` whenever `RqP X = 0` for
`1 ≤ q ≤ i`**, and a **monomorphism in degree `n + 1` whenever `RqP X = 0` for `1 ≤ q ≤ n`**.
It is in particular always an isomorphism in degree zero and always a monomorphism in degree
one, the latter recovering `Stacks.Cohomology.RightDerivedCoEdge.mono_edge_app_one`.

This is the invertibility statement that the Grothendieck spectral sequence of `(P, Q)` would
give by degeneration of its second page in the range `1 ≤ q ≤ n`, obtained here without any
spectral sequence.  It is strictly stronger than the collapse isomorphism
`Stacks.RightDerivedComp.objIso`, which asks for `RqP X = 0` in *every* positive degree.

## Construction

Write `I` for an injective resolution of `X`, `K = P I` for `P` applied to it degreewise (a
cochain complex of injective objects of `B`), `J` for an injective resolution of `P X` and
`φ : J ⟶ K` for a comparison extending `P` applied to the augmentation of `I`.  By
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq` the component of the edge morphism at `X` in
degree `i` is, up to two isomorphisms, the map `Hⁱ(Q J) ⟶ Hⁱ(Q K)` induced by `φ`, so the whole
question is whether that map is invertible.

Left exactness of `P` makes `0 ⟶ P X ⟶ K⁰ ⟶ K¹` exact, and the vanishing hypothesis makes `K`
exact in the degrees `1, …, n`.  In that range `φ` therefore admits a *partial homotopy
inverse*: a family of morphisms `rⁱ : Kⁱ ⟶ Jⁱ` which is a morphism of complexes as far as the
exactness reaches, together with homotopies exhibiting `φ ∘ r` and `r ∘ φ` as the identity.
Each of the three families is built degree by degree out of
`CategoryTheory.ShortComplex.Exact.descToInjective`, and the recursion is carried by the two
structures `JStep` and `KStep` below, whose fields are exactly the data two consecutive degrees
of the chase need.  `JStep` uses the exactness of `J` -- free, `J` being a resolution -- and is
what the monomorphism half needs; `KStep` uses the exactness of `K` one degree further and is
what the epimorphism half needs.  That asymmetry is why the monomorphism statement holds one
degree beyond the isomorphism statement.

Degree zero is the bottom of both recursions and needs no vanishing hypothesis at all: there the
retraction and the two homotopies come from the exactness of the two augmented complexes in
degree zero, which is left exactness of `P` for `K` and the resolution property for `J`.

The two chases themselves are
`CategoryTheory.HomologicalComplex.mono_homologyMap_iff_up_to_refinements` and
`CategoryTheory.HomologicalComplex.epi_homologyMap_iff_up_to_refinements`, and no refinement is
ever needed: the partial homotopy inverse produces the required witness on the nose, so the
epimorphism may be taken to be the identity.  This is the same mechanism as in
`Stacks.Cohomology.RightDerivedCoEdge.mono_homologyMap_map_one`, of which the degree-one
monomorphism statement below is the special case `n = 0`.

## Main definitions

* `Stacks.Cohomology.RightDerivedEdgeIso.JStep`: the data propagated by the recursion on the
  side of `J` -- a partial retraction of `φ` in two consecutive degrees and the homotopy
  exhibiting `φ ∘ r` as the identity.
* `Stacks.Cohomology.RightDerivedEdgeIso.KStep`: the same on the side of `K`, with the homotopy
  exhibiting `r ∘ φ` as the identity.

## Main results

* `Stacks.Cohomology.RightDerivedEdgeIso.isIso_homologyMap_of_exactAt`: the map on `i`-th
  homology induced by a comparison of resolutions is an isomorphism once `K` is exact in the
  degrees `1, …, i`.
* `Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app`: **the edge morphism is an isomorphism
  in degree `i` when `RqP X = 0` for `1 ≤ q ≤ i`.**
* `Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app_zero`: the edge morphism is an
  isomorphism in degree zero, with no vanishing hypothesis.
* `Stacks.Cohomology.RightDerivedEdgeIso.mono_edge_app_succ`: the edge morphism is a
  monomorphism in degree `n + 1` when `RqP X = 0` for `1 ≤ q ≤ n`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedEdgeIso

open RightDerivedCoEdge RightDerivedEdge

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

/-- `P` applied degreewise to an injective resolution.  Its `i`-th homology is `RiP` of the
resolved object, and its terms are injective when `P` preserves injective objects. -/
abbrev mapCplx (P : A ⥤ B) [P.Additive] {X : A} (I : InjectiveResolution X) :
    CochainComplex B ℕ :=
  (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

/-- Exactness of an `ℕ`-indexed cochain complex at `i + 1`, as exactness of the short complex
formed by the two adjacent differentials.  This is `InjectiveResolution.exact_succ` with the
exactness supplied as an argument instead of coming from a resolution. -/
theorem exact_sc_of_exactAt (C : CochainComplex B ℕ) (i : ℕ) (h : C.ExactAt (i + 1)) :
    (ShortComplex.mk _ _ (C.d_comp_d i (i + 1) (i + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ i (i + 1) (i + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 h

/-- `P` applied degreewise to an injective resolution is a complex of injective objects.  This is
a file-local instance, used only to let `CategoryTheory.ShortComplex.Exact.descToInjective`
produce morphisms into the terms of that complex. -/
local instance injective_mapCplx_X (P : A ⥤ B) [P.Additive] [P.PreservesInjectiveObjects]
    {X : A} (I : InjectiveResolution X) (i : ℕ) : Injective ((mapCplx P I).X i) :=
  injective_mapHomologicalComplex_obj P I.cocomplex I.injective i

/-- The degreewise components of a functor applied to a morphism of complexes.  This is a
definitional restatement, needed because the two spellings are only definitionally equal and
the rewriting tactics unify at reducible transparency.  It is deliberately not a `simp` lemma. -/
theorem mapCx_map_f (Q : B ⥤ D) [Q.Additive] {C C' : CochainComplex B ℕ} (ψ : C ⟶ C')
    (i : ℕ) :
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ).f i = Q.map (ψ.f i) :=
  rfl

/-- The differentials of a functor applied to a complex, as a definitional restatement.  It is
deliberately not a `simp` lemma, for the same reason as `mapCx_map_f`. -/
theorem mapCx_obj_d (Q : B ⥤ D) [Q.Additive] (C : CochainComplex B ℕ) (i j : ℕ) :
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d i j = Q.map (C.d i j) :=
  rfl

omit [Abelian D] in
/-- An isomorphism between two isomorphisms is an isomorphism.  This is the counterpart of
`Stacks.Cohomology.RightDerivedCoEdge.mono_sandwich`; it is applied in term position, so that
the two copies of the `HasHomology` instances behind the middle morphism -- the one the
hypothesis carries and the one `Stacks.Cohomology.RightDerivedEdge.edge_app_eq` produces -- are
reconciled at default transparency rather than by instance search. -/
theorem isIso_sandwich {W X' Y' Z' : D} (a : W ≅ X') (b : X' ⟶ Y') (c : Z' ≅ Y')
    (hb : IsIso b) : IsIso (a.hom ≫ b ≫ c.inv) := by
  have := hb
  infer_instance

/-! ### The data carried by the two recursions -/

section Steps

variable (P : A ⥤ B) [P.Additive] {X : A} (I : InjectiveResolution X)
  (J : InjectiveResolution (P.obj X)) (φ : J.cocomplex ⟶ mapCplx P I)

/-- The data propagated by the recursion on the side of `J`: a partial retraction of `φ` in the
degrees `i` and `i + 1`, which is a morphism of complexes in degree `i`, together with the
homotopy exhibiting `φ ∘ r` as the identity in degree `i + 1`.  This is exactly what the
monomorphism chase at degree `i + 1` consumes. -/
structure JStep (i : ℕ) where
  /-- the retraction in degree `i` -/
  r₀ : (mapCplx P I).X i ⟶ J.cocomplex.X i
  /-- the retraction in degree `i + 1` -/
  r₁ : (mapCplx P I).X (i + 1) ⟶ J.cocomplex.X (i + 1)
  /-- the retraction is a morphism of complexes in degree `i` -/
  chain : (mapCplx P I).d i (i + 1) ≫ r₁ = r₀ ≫ J.cocomplex.d i (i + 1)
  /-- the homotopy in degree `i + 1` -/
  h₀ : J.cocomplex.X (i + 1) ⟶ J.cocomplex.X i
  /-- the homotopy in degree `i + 2` -/
  h₁ : J.cocomplex.X (i + 2) ⟶ J.cocomplex.X (i + 1)
  /-- `φ` followed by the retraction is the identity up to homotopy, in degree `i + 1` -/
  hom : φ.f (i + 1) ≫ r₁ =
    𝟙 _ + J.cocomplex.d (i + 1) (i + 2) ≫ h₁ + h₀ ≫ J.cocomplex.d i (i + 1)

/-- The data propagated by the recursion on the side of `K`: a partial retraction of `φ` in the
degrees `i + 1` and `i + 2`, which is a morphism of complexes in degree `i + 1`, together with
the homotopy exhibiting `r ∘ φ` as the identity in degree `i + 1`.  This is exactly what the
epimorphism chase at degree `i + 1` consumes. -/
structure KStep (i : ℕ) where
  /-- the retraction in degree `i + 1` -/
  r₀ : (mapCplx P I).X (i + 1) ⟶ J.cocomplex.X (i + 1)
  /-- the retraction in degree `i + 2` -/
  r₁ : (mapCplx P I).X (i + 2) ⟶ J.cocomplex.X (i + 2)
  /-- the retraction is a morphism of complexes in degree `i + 1` -/
  chain : (mapCplx P I).d (i + 1) (i + 2) ≫ r₁ = r₀ ≫ J.cocomplex.d (i + 1) (i + 2)
  /-- the homotopy in degree `i + 1` -/
  h₀ : (mapCplx P I).X (i + 1) ⟶ (mapCplx P I).X i
  /-- the homotopy in degree `i + 2` -/
  h₁ : (mapCplx P I).X (i + 2) ⟶ (mapCplx P I).X (i + 1)
  /-- the retraction followed by `φ` is the identity up to homotopy, in degree `i + 1` -/
  hom : r₀ ≫ φ.f (i + 1) =
    𝟙 _ + (mapCplx P I).d (i + 1) (i + 2) ≫ h₁ + h₀ ≫ (mapCplx P I).d i (i + 1)

end Steps

/-! ### The inductive steps

Neither step needs left exactness of `P`; the exactness they consume is supplied as an
argument.  The step on the side of `J` does not need `P` to preserve injective objects either,
because both morphisms it builds land in `J`. -/

section Succ

variable (P : A ⥤ B) [P.Additive] {X : A} (I : InjectiveResolution X)
  (J : InjectiveResolution (P.obj X)) (φ : J.cocomplex ⟶ mapCplx P I) (i : ℕ)

/-- If `x ≫ y` is the identity up to the homotopy terms `d ≫ h₁` and `h₀ ≫ d₀`, where `d₀ ≫ d` is
zero, then `x ≫ y ≫ d` is `d` up to the term `d ≫ h₁ ≫ d`. -/
private theorem comp_comp_eq_add_of_hom {a b c e : B} (x : a ⟶ b) (y : b ⟶ a) (d : a ⟶ e)
    (h₁ : e ⟶ a) (h₀ : a ⟶ c) (d₀ : c ⟶ a) (hd : d₀ ≫ d = 0)
    (h : x ≫ y = 𝟙 a + d ≫ h₁ + h₀ ≫ d₀) : x ≫ y ≫ d = d + d ≫ h₁ ≫ d := by
  rw [← Category.assoc, h, Preadditive.add_comp, Preadditive.add_comp, Category.id_comp,
    Category.assoc, Category.assoc, hd, comp_zero, add_zero]

/-- If `d ≫ t` is `d` up to the term `d ≫ h ≫ d`, then `d` kills `t - 𝟙 - h ≫ d`. -/
private theorem comp_sub_sub_eq_zero {a b : B} (d : a ⟶ b) (t : b ⟶ b) (h : b ⟶ a)
    (ht : d ≫ t = d + d ≫ h ≫ d) : d ≫ (t - 𝟙 b - h ≫ d) = 0 := by
  rw [Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id, ht]
  abel

/-- The side condition defining the next retraction: the previous retraction followed by the
differential of `J` is killed by the differential of `K`, because the retraction is a morphism
of complexes one degree below. -/
theorem d_comp_r₁_comp_d (s : JStep P I J φ i) :
    (mapCplx P I).d i (i + 1) ≫ s.r₁ ≫ J.cocomplex.d (i + 1) (i + 2) = 0 := by
  rw [← Category.assoc, s.chain, Category.assoc, J.cocomplex.d_comp_d, comp_zero]

/-- The retraction in degree `i + 2`, extending a `JStep i`: the previous retraction followed by
the differential of `J` is killed by the differential of `K` one degree below, so by exactness
of `K` at `i + 1` and injectivity of `J^{i+2}` it factors through `K^{i+2}`. -/
def jNextR (s : JStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 1)) :
    (mapCplx P I).X (i + 2) ⟶ J.cocomplex.X (i + 2) :=
  (exact_sc_of_exactAt _ i hK).descToInjective (s.r₁ ≫ J.cocomplex.d (i + 1) (i + 2))
    (d_comp_r₁_comp_d P I J φ i s)

/-- The defining property of `jNextR`: it makes the retraction a morphism of complexes one
degree further. -/
@[reassoc]
theorem d_comp_jNextR (s : JStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 1)) :
    (mapCplx P I).d (i + 1) (i + 2) ≫ jNextR P I J φ i s hK =
      s.r₁ ≫ J.cocomplex.d (i + 1) (i + 2) :=
  (exact_sc_of_exactAt _ i hK).comp_descToInjective _ _

/-- The defect of the new retraction, measured one degree below. -/
theorem d_comp_comparison_comp_jNextR (s : JStep P I J φ i)
    (hK : (mapCplx P I).ExactAt (i + 1)) :
    J.cocomplex.d (i + 1) (i + 2) ≫ φ.f (i + 2) ≫ jNextR P I J φ i s hK =
      J.cocomplex.d (i + 1) (i + 2) +
        J.cocomplex.d (i + 1) (i + 2) ≫ s.h₁ ≫ J.cocomplex.d (i + 1) (i + 2) := by
  rw [← HomologicalComplex.Hom.comm_assoc, d_comp_jNextR]
  exact comp_comp_eq_add_of_hom _ _ _ _ _ _ (J.cocomplex.d_comp_d _ _ _) s.hom

/-- The side condition defining the next homotopy on the side of `J`. -/
theorem d_comp_jNextH_sub (s : JStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 1)) :
    J.cocomplex.d (i + 1) (i + 2) ≫ (φ.f (i + 2) ≫ jNextR P I J φ i s hK - 𝟙 _ -
        s.h₁ ≫ J.cocomplex.d (i + 1) (i + 2)) = 0 := by
  exact comp_sub_sub_eq_zero _ _ _ (d_comp_comparison_comp_jNextR P I J φ i s hK)

/-- The homotopy in degree `i + 3` on the side of `J`, extending a `JStep i`: the defect of the
new retraction is killed by the differential of `J` one degree below, so by exactness of `J` at
`i + 2` and injectivity of `J^{i+2}` it factors through `J^{i+3}`. -/
def jNextH (s : JStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 1)) :
    J.cocomplex.X (i + 3) ⟶ J.cocomplex.X (i + 2) :=
  (J.exact_succ (i + 1)).descToInjective
    (φ.f (i + 2) ≫ jNextR P I J φ i s hK - 𝟙 _ - s.h₁ ≫ J.cocomplex.d (i + 1) (i + 2))
    (d_comp_jNextH_sub P I J φ i s hK)

/-- The defining property of `jNextH`. -/
@[reassoc]
theorem d_comp_jNextH (s : JStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 1)) :
    J.cocomplex.d (i + 2) (i + 3) ≫ jNextH P I J φ i s hK =
      φ.f (i + 2) ≫ jNextR P I J φ i s hK - 𝟙 _ -
        s.h₁ ≫ J.cocomplex.d (i + 1) (i + 2) :=
  (J.exact_succ (i + 1)).comp_descToInjective _ _

/-- The inductive step of the recursion on the side of `J`.  It consumes the exactness of `K` in
degree `i + 1`; the exactness of `J` it also uses is free, `J` being a resolution. -/
def jStepSucc (s : JStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 1)) :
    JStep P I J φ (i + 1) where
  r₀ := s.r₁
  r₁ := jNextR P I J φ i s hK
  chain := d_comp_jNextR P I J φ i s hK
  h₀ := s.h₁
  h₁ := jNextH P I J φ i s hK
  hom := by rw [d_comp_jNextH P I J φ i s hK]; abel

variable [P.PreservesInjectiveObjects]

omit [P.PreservesInjectiveObjects] in
/-- The side condition defining the next retraction in the recursion on the side of `K`. -/
theorem d_comp_kr₁_comp_d (s : KStep P I J φ i) :
    (mapCplx P I).d (i + 1) (i + 2) ≫ s.r₁ ≫ J.cocomplex.d (i + 2) (i + 3) = 0 := by
  rw [← Category.assoc, s.chain, Category.assoc, J.cocomplex.d_comp_d, comp_zero]

/-- The retraction in degree `i + 3`, extending a `KStep i`. -/
def kNextR (s : KStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 2)) :
    (mapCplx P I).X (i + 3) ⟶ J.cocomplex.X (i + 3) :=
  (exact_sc_of_exactAt _ (i + 1) hK).descToInjective (s.r₁ ≫ J.cocomplex.d (i + 2) (i + 3))
    (d_comp_kr₁_comp_d P I J φ i s)

omit [P.PreservesInjectiveObjects] in
/-- The defining property of `kNextR`. -/
@[reassoc]
theorem d_comp_kNextR (s : KStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 2)) :
    (mapCplx P I).d (i + 2) (i + 3) ≫ kNextR P I J φ i s hK =
      s.r₁ ≫ J.cocomplex.d (i + 2) (i + 3) :=
  (exact_sc_of_exactAt _ (i + 1) hK).comp_descToInjective _ _

omit [P.PreservesInjectiveObjects] in
/-- The defect of the retraction on the side of `K`, measured one degree below. -/
theorem d_comp_kr₁_comp_comparison (s : KStep P I J φ i) :
    (mapCplx P I).d (i + 1) (i + 2) ≫ s.r₁ ≫ φ.f (i + 2) =
      (mapCplx P I).d (i + 1) (i + 2) +
        (mapCplx P I).d (i + 1) (i + 2) ≫ s.h₁ ≫ (mapCplx P I).d (i + 1) (i + 2) := by
  rw [← Category.assoc, s.chain, Category.assoc, ← HomologicalComplex.Hom.comm]
  exact comp_comp_eq_add_of_hom _ _ _ _ _ _ (HomologicalComplex.d_comp_d _ _ _ _) s.hom

omit [P.PreservesInjectiveObjects] in
/-- The side condition defining the next homotopy on the side of `K`. -/
theorem d_comp_kNextH_sub (s : KStep P I J φ i) :
    (mapCplx P I).d (i + 1) (i + 2) ≫ (s.r₁ ≫ φ.f (i + 2) - 𝟙 _ -
        s.h₁ ≫ (mapCplx P I).d (i + 1) (i + 2)) = 0 := by
  exact comp_sub_sub_eq_zero _ _ _ (d_comp_kr₁_comp_comparison P I J φ i s)

/-- The homotopy in degree `i + 3` on the side of `K`, extending a `KStep i`. -/
def kNextH (s : KStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 2)) :
    (mapCplx P I).X (i + 3) ⟶ (mapCplx P I).X (i + 2) :=
  (exact_sc_of_exactAt _ (i + 1) hK).descToInjective
    (s.r₁ ≫ φ.f (i + 2) - 𝟙 _ - s.h₁ ≫ (mapCplx P I).d (i + 1) (i + 2))
    (d_comp_kNextH_sub P I J φ i s)

/-- The defining property of `kNextH`. -/
@[reassoc]
theorem d_comp_kNextH (s : KStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 2)) :
    (mapCplx P I).d (i + 2) (i + 3) ≫ kNextH P I J φ i s hK =
      s.r₁ ≫ φ.f (i + 2) - 𝟙 _ - s.h₁ ≫ (mapCplx P I).d (i + 1) (i + 2) :=
  (exact_sc_of_exactAt _ (i + 1) hK).comp_descToInjective _ _

/-- The inductive step of the recursion on the side of `K`.  It consumes the exactness of `K` in
degree `i + 2`, one degree further than `jStepSucc` does. -/
def kStepSucc (s : KStep P I J φ i) (hK : (mapCplx P I).ExactAt (i + 2)) :
    KStep P I J φ (i + 1) where
  r₀ := s.r₁
  r₁ := kNextR P I J φ i s hK
  chain := d_comp_kNextR P I J φ i s hK
  h₀ := s.h₁
  h₁ := kNextH P I J φ i s hK
  hom := by rw [d_comp_kNextH P I J φ i s hK]; abel

end Succ

/-! ### The bottom of the two recursions -/

section Base

variable (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [P.PreservesInjectiveObjects]
  {X : A} (I : InjectiveResolution X) (J : InjectiveResolution (P.obj X))
  (φ : J.cocomplex ⟶ mapCplx P I) (hφ : augOf J ≫ φ.f 0 = mapAug P I)

omit [P.PreservesInjectiveObjects] in
include hφ in
/-- The side condition defining `homotopyKZero`: the degree-zero retraction followed by `φ` is
the identity on the image of the augmentation of `K`. -/
theorem mapAug_comp_retractionZero_comp_comparison_sub :
    mapAug P I ≫ (retractionZero P I J ≫ φ.f 0 - 𝟙 _) = 0 := by
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    mapAug_comp_retractionZero, hφ, sub_self]

/-- The degree-one component of the homotopy exhibiting `r ∘ φ` as the identity on `K`: the
difference `retractionZero ∘ φ⁰ - 𝟙` vanishes on the augmentation of `K`, so by exactness of
`0 ⟶ P X ⟶ K⁰ ⟶ K¹` and injectivity of `K⁰` it factors through `K¹`. -/
def homotopyKZero : (mapCplx P I).X 1 ⟶ (mapCplx P I).X 0 :=
  (exact_mapAug P I).descToInjective (retractionZero P I J ≫ φ.f 0 - 𝟙 _)
    (mapAug_comp_retractionZero_comp_comparison_sub P I J φ hφ)

/-- **In degree zero the comparison of resolutions is split by the retraction, up to homotopy on
the side of `K`.**  This is the bottom of the recursion carried by `KStep`. -/
@[reassoc]
theorem retractionZero_comp_comparison :
    retractionZero P I J ≫ φ.f 0 =
      𝟙 _ + (mapCplx P I).d 0 1 ≫ homotopyKZero P I J φ hφ := by
  rw [homotopyKZero, (exact_mapAug P I).comp_descToInjective]
  abel

omit [P.PreservesInjectiveObjects] in
/-- **In degree zero the comparison of resolutions is split by the retraction, up to homotopy on
the side of `J`.**  This is `Stacks.Cohomology.RightDerivedCoEdge.d_comp_homotopyZero`
rearranged; it is the bottom of the recursion carried by `JStep`. -/
@[reassoc]
theorem comparison_comp_retractionZero :
    φ.f 0 ≫ retractionZero P I J = 𝟙 _ + J.cocomplex.d 0 1 ≫ homotopyZero P I J φ hφ := by
  rw [d_comp_homotopyZero]
  abel

omit [P.PreservesInjectiveObjects] in
/-- The bottom of the recursion on the side of `J`, assembled from the degree-zero and
degree-one retractions and homotopies of
`StacksFrontier/Algebra/Homology/RightDerivedCoEdge.lean`.  It needs no vanishing hypothesis. -/
def jStepZero : JStep P I J φ 0 where
  r₀ := retractionZero P I J
  r₁ := retractionOne P I J
  chain := d_comp_retractionOne P I J
  h₀ := homotopyZero P I J φ hφ
  h₁ := homotopyOne P I J φ hφ
  hom := comparison_comp_retractionOne P I J φ hφ

omit [P.PreservesInjectiveObjects] in
/-- The side condition defining the retraction in degree two. -/
theorem d_comp_retractionOne_comp_d :
    (mapCplx P I).d 0 1 ≫ retractionOne P I J ≫ J.cocomplex.d 1 2 = 0 := by
  rw [← Category.assoc, d_comp_retractionOne, Category.assoc, J.cocomplex.d_comp_d, comp_zero]

omit [P.PreservesInjectiveObjects] in
/-- The retraction in degree two: the degree-one retraction followed by the differential of `J`
is killed by the differential of `K` one degree below, so by exactness of `K` at `1` and
injectivity of `J²` it factors through `K²`. -/
def retractionTwo (hK : (mapCplx P I).ExactAt 1) :
    (mapCplx P I).X 2 ⟶ J.cocomplex.X 2 :=
  (exact_sc_of_exactAt _ 0 hK).descToInjective (retractionOne P I J ≫ J.cocomplex.d 1 2)
    (d_comp_retractionOne_comp_d P I J)

omit [P.PreservesInjectiveObjects] in
/-- The defining property of `retractionTwo`. -/
@[reassoc]
theorem d_comp_retractionTwo (hK : (mapCplx P I).ExactAt 1) :
    (mapCplx P I).d 1 2 ≫ retractionTwo P I J hK = retractionOne P I J ≫ J.cocomplex.d 1 2 :=
  (exact_sc_of_exactAt _ 0 hK).comp_descToInjective _ _

/-- The defect of the degree-one retraction on the side of `K`, measured in degree zero. -/
theorem d_comp_retractionOne_comp_comparison :
    (mapCplx P I).d 0 1 ≫ retractionOne P I J ≫ φ.f 1 =
      (mapCplx P I).d 0 1 +
        (mapCplx P I).d 0 1 ≫ homotopyKZero P I J φ hφ ≫ (mapCplx P I).d 0 1 := by
  rw [← Category.assoc, d_comp_retractionOne, Category.assoc, ← HomologicalComplex.Hom.comm,
    ← Category.assoc, retractionZero_comp_comparison P I J φ hφ, Preadditive.add_comp,
    Category.id_comp, Category.assoc]

/-- The side condition defining the degree-two homotopy on the side of `K`. -/
theorem d_comp_homotopyKOne_sub :
    (mapCplx P I).d 0 1 ≫ (retractionOne P I J ≫ φ.f 1 - 𝟙 _ -
        homotopyKZero P I J φ hφ ≫ (mapCplx P I).d 0 1) = 0 := by
  exact comp_sub_sub_eq_zero _ _ _ (d_comp_retractionOne_comp_comparison P I J φ hφ)

/-- The degree-two component of the homotopy exhibiting `r ∘ φ` as the identity on `K`. -/
def homotopyKOne (hK : (mapCplx P I).ExactAt 1) :
    (mapCplx P I).X 2 ⟶ (mapCplx P I).X 1 :=
  (exact_sc_of_exactAt _ 0 hK).descToInjective
    (retractionOne P I J ≫ φ.f 1 - 𝟙 _ - homotopyKZero P I J φ hφ ≫ (mapCplx P I).d 0 1)
    (d_comp_homotopyKOne_sub P I J φ hφ)

/-- The defining property of `homotopyKOne`. -/
@[reassoc]
theorem d_comp_homotopyKOne (hK : (mapCplx P I).ExactAt 1) :
    (mapCplx P I).d 1 2 ≫ homotopyKOne P I J φ hφ hK =
      retractionOne P I J ≫ φ.f 1 - 𝟙 _ -
        homotopyKZero P I J φ hφ ≫ (mapCplx P I).d 0 1 :=
  (exact_sc_of_exactAt _ 0 hK).comp_descToInjective _ _

/-- The bottom of the recursion on the side of `K`.  Unlike `jStepZero` it consumes the
exactness of `K` in degree one: both the retraction in degree two and the homotopy in degree two
are produced from it. -/
def kStepZero (hK : (mapCplx P I).ExactAt 1) : KStep P I J φ 0 where
  r₀ := retractionOne P I J
  r₁ := retractionTwo P I J hK
  chain := d_comp_retractionTwo P I J hK
  h₀ := homotopyKZero P I J φ hφ
  h₁ := homotopyKOne P I J φ hφ hK
  hom := by rw [d_comp_homotopyKOne P I J φ hφ hK]; abel

/-- The recursion on the side of `J`, run up to a bound `n`: a partial retraction of `φ` and the
homotopy exhibiting `φ ∘ r` as the identity, in every degree up to `n + 1`, given the exactness
of `K` in the degrees `1, …, n`. -/
def jStep (n : ℕ) (hK : ∀ q, 1 ≤ q → q ≤ n → (mapCplx P I).ExactAt q) :
    ∀ i, i ≤ n → JStep P I J φ i
  | 0, _ => jStepZero P I J φ hφ
  | (i + 1), hi => jStepSucc P I J φ i (jStep n hK i (by omega)) (hK (i + 1) (by omega) hi)

/-- The recursion on the side of `K`, run up to a bound `n`: a partial retraction of `φ` and the
homotopy exhibiting `r ∘ φ` as the identity, in every degree up to `n`, given the exactness of
`K` in the degrees `1, …, n`. -/
def kStep (n : ℕ) (hK : ∀ q, 1 ≤ q → q ≤ n → (mapCplx P I).ExactAt q) :
    ∀ i, i + 1 ≤ n → KStep P I J φ i
  | 0, hi => kStepZero P I J φ hφ (hK 1 le_rfl hi)
  | (i + 1), hi => kStepSucc P I J φ i (kStep n hK i (by omega)) (hK (i + 2) (by omega) hi)

end Base

/-! ### The two chases -/

section Chases

variable (P : A ⥤ B) [P.Additive] {X : A} (I : InjectiveResolution X)
  (J : InjectiveResolution (P.obj X)) (φ : J.cocomplex ⟶ mapCplx P I)
  (Q : B ⥤ D) [Q.Additive] (i : ℕ)

/-- **The monomorphism half.**  Given the data of a `JStep i`, the map induced on the
`(i + 1)`-st homology by `Q` applied to the comparison of resolutions is a monomorphism: for a
cycle `x₂` of `Q J` in degree `i + 1` whose image in `Q K` is the boundary of `y₁`, the partial
retraction and the homotopy exhibit `x₂` itself as a boundary, so no refinement is needed. -/
theorem mono_homologyMap_succ (s : JStep P I J φ i) :
    Mono (HomologicalComplex.homologyMap
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (i + 1)) := by
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ i (i + 1) (i + 2)
    (by simp) (by simp)]
  intro T x₂ hx₂ y₁ hy₁
  refine ⟨T, 𝟙 T, inferInstance, y₁ ≫ Q.map s.r₀ - x₂ ≫ Q.map s.h₀, ?_⟩
  have hx : x₂ ≫ Q.map (J.cocomplex.d (i + 1) (i + 2)) = 0 := hx₂
  have hy : x₂ ≫ Q.map (φ.f (i + 1)) = y₁ ≫ Q.map ((mapCplx P I).d i (i + 1)) := hy₁
  have hd : ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).d i (i + 1) =
      Q.map (J.cocomplex.d i (i + 1)) := rfl
  rw [Category.id_comp, hd, Preadditive.sub_comp, Category.assoc, Category.assoc,
    ← Q.map_comp s.r₀ (J.cocomplex.d i (i + 1)), ← Q.map_comp s.h₀ (J.cocomplex.d i (i + 1)),
    ← s.chain, Q.map_comp ((mapCplx P I).d i (i + 1)) s.r₁, ← Category.assoc y₁, ← hy,
    Category.assoc, ← Q.map_comp (φ.f (i + 1)) s.r₁, s.hom, Q.map_add, Q.map_add, Q.map_id,
    Preadditive.comp_add, Preadditive.comp_add]
  simp [reassoc_of% hx]

/-- **The epimorphism half.**  Given the data of a `KStep i`, the map induced on the
`(i + 1)`-st homology by `Q` applied to the comparison of resolutions is an epimorphism: a cycle
`y₂` of `Q K` in degree `i + 1` is carried by the partial retraction to a cycle of `Q J`, whose
image differs from `y₂` by the boundary the homotopy provides. -/
theorem epi_homologyMap_succ (s : KStep P I J φ i) :
    Epi (HomologicalComplex.homologyMap
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (i + 1)) := by
  rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ i (i + 1) (i + 2)
    (by simp) (by simp)]
  intro T y₂ hy₂
  have hy : y₂ ≫ Q.map ((mapCplx P I).d (i + 1) (i + 2)) = 0 := hy₂
  refine ⟨T, 𝟙 T, inferInstance, y₂ ≫ Q.map s.r₀, ?_, -(y₂ ≫ Q.map s.h₀), ?_⟩
  · rw [mapCx_obj_d, Category.assoc, ← Q.map_comp, ← s.chain, Q.map_comp, ← Category.assoc, hy,
      zero_comp]
  · rw [Category.id_comp, mapCx_obj_d, mapCx_map_f, Category.assoc,
      ← Q.map_comp s.r₀ (φ.f (i + 1)), s.hom,
      Preadditive.neg_comp, Category.assoc, ← Q.map_comp s.h₀ ((mapCplx P I).d i (i + 1)),
      Q.map_add, Q.map_add, Q.map_id, Preadditive.comp_add, Preadditive.comp_add]
    simp only [Q.map_comp, ← Category.assoc, hy, zero_comp]
    erw [Category.comp_id]
    abel

end Chases

/-! ### Invertibility of the induced map on homology -/

section Homology

variable (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [P.PreservesInjectiveObjects]
  {X : A} (I : InjectiveResolution X) (J : InjectiveResolution (P.obj X))
  (φ : J.cocomplex ⟶ mapCplx P I) (hφ : augOf J ≫ φ.f 0 = mapAug P I)
  (Q : B ⥤ D) [Q.Additive]

include hφ in
/-- **The degree-zero case.**  The map induced on the zeroth homology by `Q` applied to the
comparison of resolutions is always an isomorphism, with no vanishing hypothesis: in degree zero
the homotopy inverse of `φ` exists outright, because left exactness of `P` makes
`0 ⟶ P X ⟶ K⁰ ⟶ K¹` exact and `J` is a resolution. -/
theorem isIso_homologyMap_zero :
    IsIso (HomologicalComplex.homologyMap
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 0) := by
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 := by simp
  have hdJ : ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).d 0 0 = 0 :=
    HomologicalComplex.shape _ 0 0 (by simp)
  have hdK : ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj (mapCplx P I)).d 0 0 = 0 :=
    HomologicalComplex.shape _ 0 0 (by simp)
  have hmono : Mono (HomologicalComplex.homologyMap
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 0) := by
    rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ 0 0 1 hprev (by simp)]
    intro T x₂ hx₂ y₁ hy₁
    refine ⟨T, 𝟙 T, inferInstance, 0, ?_⟩
    have hx : x₂ ≫ Q.map (J.cocomplex.d 0 1) = 0 := hx₂
    have hy : x₂ ≫ Q.map (φ.f 0) = 0 := by
      rw [mapCx_map_f] at hy₁; rw [hy₁, hdK, comp_zero]
    have key : x₂ ≫ Q.map (φ.f 0 ≫ retractionZero P I J) = 0 := by
      rw [Q.map_comp, ← Category.assoc, hy, zero_comp]
    rw [comparison_comp_retractionZero P I J φ hφ, Q.map_add, Q.map_id, Q.map_comp,
      Preadditive.comp_add, ← Category.assoc, hx, zero_comp, add_zero] at key
    have hid : x₂ ≫ 𝟙 (Q.obj (J.cocomplex.X 0)) = x₂ := Category.comp_id x₂
    rw [hid] at key
    rw [Category.id_comp, hdJ, comp_zero, key]
  have hepi : Epi (HomologicalComplex.homologyMap
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 0) := by
    rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ 0 0 1 hprev (by simp)]
    intro T y₂ hy₂
    have hy : y₂ ≫ Q.map ((mapCplx P I).d 0 1) = 0 := hy₂
    refine ⟨T, 𝟙 T, inferInstance, y₂ ≫ Q.map (retractionZero P I J), ?_, 0, ?_⟩
    · rw [mapCx_obj_d, Category.assoc, ← Q.map_comp, ← d_comp_retractionOne P I J, Q.map_comp,
        ← Category.assoc, hy, zero_comp]
    · rw [Category.id_comp, hdK, comp_zero, add_zero, mapCx_map_f, Category.assoc, ← Q.map_comp,
        retractionZero_comp_comparison P I J φ hφ, Q.map_add, Q.map_id, Q.map_comp,
        Preadditive.comp_add, ← Category.assoc, hy, zero_comp, add_zero]
      exact (Category.comp_id y₂).symm
  exact isIso_of_mono_of_epi _

include hφ in
/-- **The map induced on homology by a comparison of resolutions is an isomorphism in every
degree in which `K` is exact below.**  This is the content of the invertibility of the edge
morphism, before any identification of the edge morphism with it. -/
theorem isIso_homologyMap_of_exactAt (i : ℕ)
    (hK : ∀ q, 1 ≤ q → q ≤ i → (mapCplx P I).ExactAt q) :
    IsIso (HomologicalComplex.homologyMap
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i) := by
  cases i with
  | zero => exact isIso_homologyMap_zero P I J φ hφ Q
  | succ i =>
    have hm := mono_homologyMap_succ P I J φ Q i (jStep P I J φ hφ (i + 1) hK i (by omega))
    have he := epi_homologyMap_succ P I J φ Q i (kStep P I J φ hφ (i + 1) hK i le_rfl)
    exact isIso_of_mono_of_epi _

end Homology

/-! ### The edge morphism -/

section Edge

variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [P.PreservesInjectiveObjects]
  (Q : B ⥤ D) [Q.Additive]

omit [HasInjectiveResolutions B] [PreservesFiniteLimits P] [P.PreservesInjectiveObjects] in
/-- `P` applied to the chosen injective resolution is exact in a positive degree exactly when
the corresponding right derived functor of `P` vanishes there. -/
theorem exactAt_mapCplx_of_isZero {X : A} (q : ℕ)
    (h : IsZero ((P.rightDerived q).obj X)) :
    (mapCplx P (injectiveResolution X)).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact h.of_iso ((injectiveResolution X).isoRightDerivedObj P q).symm

/-- **The edge morphism of a composite of right derived functors is an isomorphism in degree `i`
as soon as `RqP X` vanishes for `1 ≤ q ≤ i`.**

This is the degeneration statement that the Grothendieck spectral sequence of `(P, Q)` would
supply, in the range in which its second page has a single nonzero row, proved here directly
from a partial homotopy inverse of the comparison of injective resolutions.  The hypothesis is
*not* the acyclicity of `X` in every positive degree, which is what
`Stacks.RightDerivedComp.objIso` asks for. -/
theorem isIso_edge_app (X : A) (i : ℕ)
    (hX : ∀ q, 1 ≤ q → q ≤ i → IsZero ((P.rightDerived q).obj X)) :
    IsIso ((RightDerivedEdge.edge P Q i).app X) := by
  rw [RightDerivedEdge.edge_app_eq P Q i (injectiveResolution X)
    (injectiveResolution (P.obj X)) (RightDerivedEdge.resolutionComparison P X)
    (RightDerivedEdge.ι_f_zero_comp_resolutionComparison P X)]
  exact isIso_sandwich ((injectiveResolution (P.obj X)).isoRightDerivedObj Q i) _
    ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) i)
    (isIso_homologyMap_of_exactAt P (injectiveResolution X)
      (injectiveResolution (P.obj X)) (RightDerivedEdge.resolutionComparison P X)
      (RightDerivedEdge.ι_f_zero_comp_resolutionComparison P X) Q i
      (fun q hq hqi => exactAt_mapCplx_of_isZero P q (hX q hq hqi)))

/-- **The edge morphism as an isomorphism**, in the range of degrees in which it is invertible:
`RⁱQ (P X) ≅ Rⁱ(Q ∘ P) X` when `RqP X = 0` for `1 ≤ q ≤ i`. Its forward morphism is the edge
morphism, by `edgeAppIso_hom`. -/
def edgeAppIso (X : A) (i : ℕ)
    (hX : ∀ q, 1 ≤ q → q ≤ i → IsZero ((P.rightDerived q).obj X)) :
    (P ⋙ Q.rightDerived i).obj X ≅ ((P ⋙ Q).rightDerived i).obj X :=
  haveI := isIso_edge_app P Q X i hX
  asIso ((RightDerivedEdge.edge P Q i).app X)

/-- The forward morphism of `edgeAppIso` is the edge morphism `RⁱQ (P X) ⟶ Rⁱ(Q ∘ P) X`. -/
@[simp]
theorem edgeAppIso_hom (X : A) (i : ℕ)
    (hX : ∀ q, 1 ≤ q → q ≤ i → IsZero ((P.rightDerived q).obj X)) :
    (edgeAppIso P Q X i hX).hom = (RightDerivedEdge.edge P Q i).app X :=
  rfl

/-- **The edge morphism is an isomorphism in degree zero**, with no vanishing hypothesis: for
`P = f_*` and `Q = Γ(Y, -)` this is the identification `Γ(Y, f_* F) = Γ(X, F)`. -/
theorem isIso_edge_app_zero (X : A) : IsIso ((RightDerivedEdge.edge P Q 0).app X) :=
  isIso_edge_app P Q X 0 fun _ hq hq0 => absurd (hq.trans hq0) (by simp)

/-- **The edge morphism is a monomorphism one degree beyond the range of vanishing.**  Only the
recursion on the side of `J` enters, and it consumes one degree of exactness less than the
recursion on the side of `K`; at `n = 0` this is
`Stacks.Cohomology.RightDerivedCoEdge.mono_edge_app_one`. -/
theorem mono_edge_app_succ (X : A) (n : ℕ)
    (hX : ∀ q, 1 ≤ q → q ≤ n → IsZero ((P.rightDerived q).obj X)) :
    Mono ((RightDerivedEdge.edge P Q (n + 1)).app X) := by
  rw [RightDerivedEdge.edge_app_eq P Q (n + 1) (injectiveResolution X)
    (injectiveResolution (P.obj X)) (RightDerivedEdge.resolutionComparison P X)
    (RightDerivedEdge.ι_f_zero_comp_resolutionComparison P X)]
  exact mono_sandwich ((injectiveResolution (P.obj X)).isoRightDerivedObj Q (n + 1)) _
    ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) (n + 1))
    (mono_homologyMap_succ P (injectiveResolution X) (injectiveResolution (P.obj X))
      (RightDerivedEdge.resolutionComparison P X) Q n
      (jStep P (injectiveResolution X) (injectiveResolution (P.obj X))
        (RightDerivedEdge.resolutionComparison P X)
        (RightDerivedEdge.ι_f_zero_comp_resolutionComparison P X) n
        (fun q hq hqn => exactAt_mapCplx_of_isZero P q (hX q hq hqn)) n le_rfl))

end Edge

end Stacks.Cohomology.RightDerivedEdgeIso

end
