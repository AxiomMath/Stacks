module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.SquareNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.TermwiseSplit

/-!
# Mayer--Vietoris descent for a colimit comparison

Let `(C, J)` be a site, `F` an abelian sheaf on it, and let `Ψ` be a diagram of
Mayer--Vietoris squares indexed by `Iᵒᵖ` together with a Mayer--Vietoris square `T` and a cone of
morphisms `T ⟶ Ψ i`. For each of the four corners of the square and each degree there is then a
canonical **comparison morphism**

`colim_i H^n(Ψ i, F) ⟶ H^n(T, F)`

from the colimit of the cohomology over that corner of the levels to the cohomology over that
corner of the vertex. The main result of this file is that if the comparison morphisms at the
three corners `X₁`, `X₂`, `X₃` are isomorphisms in every degree, then so is the comparison
morphism at the fourth corner `X₄`, provided `I` is a shape along which colimits of abelian
groups are exact — for instance a filtered shape.

## Main definitions

* `Stacks.Cohomology.MayerVietoris.MVFunctor`: a functor into squares of a site all of whose
  values are Mayer--Vietoris squares.
* `Stacks.Cohomology.MayerVietoris.cornerDiagram`: the diagram of cohomology groups over one
  corner of the levels.
* `Stacks.Cohomology.MayerVietoris.cornerComparison`: **the comparison morphism**
  `colim_i H^n(Ψ i, F) ⟶ H^n(T, F)` at one corner.

## Main results

* `Stacks.Cohomology.MayerVietoris.isIso_cornerComparison_X₄`: **the descent**. If the comparison
  is an isomorphism at the corners `X₁`, `X₂`, `X₃` in all degrees, it is an isomorphism at `X₄`
  in all degrees.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w v u v₁ u₁

namespace Stacks.Cohomology.MayerVietoris

/-! ### Pointwise criteria in a functor category -/

section Pointwise

variable {I : Type u₁} [Category.{v₁} I] {D : Type*} [Category* D] [Abelian D]

omit [Abelian D] in
/-- The evaluation functors of a functor category are jointly faithful. -/
theorem jointlyFaithful_evaluation :
    JointlyFaithful (fun j : I => (evaluation I D).obj j) where
  map_injective {_ _} _ _ hfg := by
    ext j
    exact hfg j

/-- A short complex of functors is exact as soon as it is exact at every object. -/
theorem shortComplex_exact_of_pointwise (S : ShortComplex (I ⥤ D))
    (h : ∀ j : I, (S.map ((evaluation I D).obj j)).Exact) : S.Exact :=
  (jointlyFaithful_evaluation.jointlyReflectsIsomorphisms.exact_iff S).2 h

/-- A sequence of functors is exact as soon as it is exact at every object. -/
theorem composableArrows_exact_of_pointwise {n : ℕ} (S : ComposableArrows (I ⥤ D) n)
    (h : ∀ j : I, ComposableArrows.Exact (S ⋙ (evaluation I D).obj j)) : S.Exact :=
  ComposableArrows.Exact.mk
    (ComposableArrows.IsComplex.mk fun i hi => by
      ext j
      exact (h j).toIsComplex.zero i hi)
    fun i hi => shortComplex_exact_of_pointwise _ fun j => (h j).exact i hi

end Pointwise

/-! ### Exact functors and sequences -/

section ExactComp

variable {D : Type*} [Category* D] [Abelian D] {E : Type*} [Category* E] [Abelian E]
  (G : D ⥤ E) [G.PreservesZeroMorphisms] [G.PreservesHomology]

/-- An exact functor carries an exact sequence to an exact sequence. -/
theorem exact_comp {n : ℕ} {S : ComposableArrows D n} (hS : S.Exact) :
    ComposableArrows.Exact (S ⋙ G) :=
  ComposableArrows.Exact.mk
    (ComposableArrows.IsComplex.mk fun i hi => by
      change G.map (S.map' i (i + 1)) ≫ G.map (S.map' (i + 1) (i + 2)) = 0
      rw [← G.map_comp, hS.toIsComplex.zero i hi, G.map_zero])
    fun i hi => (hS.exact i hi).map G

end ExactComp

section SplitBiprod

variable {D : Type*} [Category* D] [Preadditive D] {E : Type*} [Category* E] [Preadditive E]
  (L : D ⥤ E) [L.Additive]

/-- **Invertibility of a comparison at a biproduct term.** Suppose `X` is a biproduct of `A` and
`B` in `D` in the bicone sense, let `L` be an additive functor, let `A'`, `B'` be objects of `E`
with invertible comparisons `L A ⟶ A'` and `L B ⟶ B'`, and let `f : L X ⟶ A' ⊞ B'` be compatible
with the two projections. Then `f` is invertible. -/
theorem isIso_of_additive_of_split_biprod {A B X : D}
    (π₁ : X ⟶ A) (π₂ : X ⟶ B) (ι₁ : A ⟶ X) (ι₂ : B ⟶ X)
    (h₁₁ : ι₁ ≫ π₁ = 𝟙 A) (h₂₂ : ι₂ ≫ π₂ = 𝟙 B)
    (h₁₂ : ι₁ ≫ π₂ = 0) (h₂₁ : ι₂ ≫ π₁ = 0)
    (htot : π₁ ≫ ι₁ + π₂ ≫ ι₂ = 𝟙 X)
    {A' B' : E} [HasBinaryBiproduct A' B'] (a : L.obj A ⟶ A') (b : L.obj B ⟶ B')
    [IsIso a] [IsIso b] (f : L.obj X ⟶ A' ⊞ B')
    (hf₁ : f ≫ biprod.fst = L.map π₁ ≫ a) (hf₂ : f ≫ biprod.snd = L.map π₂ ≫ b) :
    IsIso f := by
  have hf₁' : ∀ {Z : E} (k : A' ⟶ Z), f ≫ biprod.fst ≫ k = L.map π₁ ≫ a ≫ k := fun k => by
    rw [← Category.assoc, hf₁, Category.assoc]
  have hf₂' : ∀ {Z : E} (k : B' ⟶ Z), f ≫ biprod.snd ≫ k = L.map π₂ ≫ b ≫ k := fun k => by
    rw [← Category.assoc, hf₂, Category.assoc]
  refine ⟨biprod.desc (inv a ≫ L.map ι₁) (inv b ≫ L.map ι₂), ?_, ?_⟩
  · rw [biprod.desc_eq, Preadditive.comp_add, hf₁', hf₂', IsIso.hom_inv_id_assoc,
      IsIso.hom_inv_id_assoc, ← L.map_comp, ← L.map_comp, ← L.map_add, htot, L.map_id]
  · refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
      simp only [Category.assoc, biprod.inl_desc_assoc, biprod.inr_desc_assoc, hf₁, hf₂,
        ← Functor.map_comp_assoc, h₁₁, h₂₂, h₁₂, h₂₁, L.map_id, L.map_zero,
        Category.id_comp, Category.comp_id, Limits.zero_comp, Limits.comp_zero,
        IsIso.inv_hom_id, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd]

end SplitBiprod

/-! ### The corners of a square, as functors -/

section Corners

variable (C : Type u) [Category.{v} C]

/-- The top-left corner of a square, as a functor. -/
@[simps, reducible] def evSquare₁ : Square C ⥤ C where
  obj s := s.X₁
  map φ := φ.τ₁

/-- The top-right corner of a square, as a functor. -/
@[simps, reducible] def evSquare₂ : Square C ⥤ C where
  obj s := s.X₂
  map φ := φ.τ₂

/-- The bottom-left corner of a square, as a functor. -/
@[simps, reducible] def evSquare₃ : Square C ⥤ C where
  obj s := s.X₃
  map φ := φ.τ₃

/-- The bottom-right corner of a square, as a functor. -/
@[simps, reducible] def evSquare₄ : Square C ⥤ C where
  obj s := s.X₄
  map φ := φ.τ₄

end Corners

/-! ### Systems of Mayer--Vietoris squares -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- A functor into the squares of a site, all of whose values are Mayer--Vietoris squares. -/
structure MVFunctor (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)]
    (I : Type u₁) [Category.{v₁} I] where
  /-- The underlying diagram of squares. -/
  functor : Iᵒᵖ ⥤ Square C
  /-- Each square has a monomorphic left edge. -/
  mono_f₁₃ (i : Iᵒᵖ) : Mono (functor.obj i).f₁₃
  /-- Each square becomes a pushout of sheaves of types. -/
  isPushout (i : Iᵒᵖ) :
    ((functor.obj i).map (yoneda ⋙ presheafToSheaf J (Type v))).IsPushout

open CochainComplex.FilteredInjective.Hom (biprod_map_id)
open CochainComplex.FilteredInjective.TermwiseSplit (biprod_map_comp_map)

namespace MVFunctor

variable {I : Type u₁} [Category.{v₁} I] (Ψ : MVFunctor J I)

/-- The Mayer--Vietoris square of the system at a level. -/
def sq (i : Iᵒᵖ) : J.MayerVietorisSquare where
  toSquare := Ψ.functor.obj i
  mono_f₁₃ := Ψ.mono_f₁₃ i
  isPushout := Ψ.isPushout i

omit [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in
/-- The underlying square of the Mayer--Vietoris square at a level is the value of the functor. -/
@[simp] theorem sq_toSquare (i : Iᵒᵖ) : (Ψ.sq i).toSquare = Ψ.functor.obj i := rfl

end MVFunctor

/-! ### Monomorphy of the first map of the Mayer--Vietoris sequence -/

/-- **The first map of the Mayer--Vietoris sequence is injective.** The sum of the two
restrictions `H⁰(X₄, F) ⟶ H⁰(X₂, F) ⊞ H⁰(X₃, F)` is a monomorphism. -/
theorem mono_toBiprod_zero (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v}) :
    Mono (S.toBiprod F 0) :=
  ((mayerVietorisInitialSequence_exact S F).exact 0).mono_g rfl

/-! ### The diagrams and the comparison morphisms -/

section Descent

variable {I : Type u₁} [Category.{v₁} I] (F : Sheaf J AddCommGrpCat.{v})
  (Ψ : MVFunctor J I) (T : J.MayerVietorisSquare)
  (leg : ∀ i : Iᵒᵖ, T.toSquare ⟶ Ψ.functor.obj i)
  (hleg : ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j), leg i ≫ Ψ.functor.map a = leg j)

/-- The diagram, indexed by `I`, of the cohomology groups of `F` over one corner of the levels
of the system. -/
def cornerDiagram (e : Square C ⥤ C) (n : ℕ) : I ⥤ AddCommGrpCat.{w} :=
  (Ψ.functor ⋙ e).rightOp ⋙ F.cohomologyPresheaf.{w} n

/-- The value of the diagram at a level. -/
theorem cornerDiagram_obj (e : Square C ⥤ C) (n : ℕ) (i : I) :
    (cornerDiagram F Ψ e n).obj i = Sheaf.H'.{w} F n (e.obj (Ψ.functor.obj (op i))) := rfl

/-- The transition map of the diagram is the restriction along the transition of the system. -/
theorem cornerDiagram_map (e : Square C ⥤ C) (n : ℕ) {i j : I} (a : i ⟶ j) :
    (cornerDiagram F Ψ e n).map a =
      (F.cohomologyPresheaf.{w} n).map (e.map (Ψ.functor.map a.op)).op := rfl

include hleg in
/-- Restriction along a transition, then along a leg, is restriction along a leg. -/
theorem cornerDiagram_map_comp_leg (e : Square C ⥤ C) (n : ℕ) {i j : I} (a : i ⟶ j) :
    (cornerDiagram F Ψ e n).map a ≫ (F.cohomologyPresheaf.{w} n).map (e.map (leg (op j))).op =
      (F.cohomologyPresheaf.{w} n).map (e.map (leg (op i))).op := by
  have key : (e.map (Ψ.functor.map a.op)).op ≫ (e.map (leg (op j))).op =
      (e.map (leg (op i))).op := by
    rw [← op_comp, ← Functor.map_comp, hleg a.op]
  exact ((F.cohomologyPresheaf.{w} n).map_comp _ _).symm.trans
    (congrArg (F.cohomologyPresheaf.{w} n).map key)

include hleg in
/-- The restriction from a level to the vertex, over one corner. -/
def cornerLeg (e : Square C ⥤ C) (n : ℕ) (i : I) :
    (cornerDiagram F Ψ e n).obj i ⟶ Sheaf.H'.{w} F n (e.obj T.toSquare) :=
  (F.cohomologyPresheaf.{w} n).map (e.map (leg (op i))).op

/-- The cocone of restrictions from the levels to the vertex, over one corner. -/
def cornerCocone (e : Square C ⥤ C) (n : ℕ) : Cocone (cornerDiagram F Ψ e n) where
  pt := Sheaf.H'.{w} F n (e.obj T.toSquare)
  ι :=
    { app := cornerLeg F Ψ T leg e n
      naturality := fun _ _ a =>
        (cornerDiagram_map_comp_leg F Ψ T leg hleg e n a).trans (Category.comp_id _).symm }

/-- **The comparison morphism at one corner**: from the colimit of the cohomology over that
corner of the levels to the cohomology over that corner of the vertex. -/
def cornerComparison [HasColimitsOfShape I AddCommGrpCat.{w}] (e : Square C ⥤ C) (n : ℕ) :
    colimit (cornerDiagram F Ψ e n) ⟶ Sheaf.H'.{w} F n (e.obj T.toSquare) :=
  colimit.desc _ (cornerCocone F Ψ T leg hleg e n)

/-- The comparison morphism at one corner restricts, on the colimit inclusion of a level, to the
restriction from that level to the vertex. -/
@[reassoc]
theorem ι_cornerComparison [HasColimitsOfShape I AddCommGrpCat.{w}] (e : Square C ⥤ C) (n : ℕ)
    (i : I) :
    colimit.ι (cornerDiagram F Ψ e n) i ≫ cornerComparison F Ψ T leg hleg e n =
      cornerLeg F Ψ T leg e n i :=
  colimit.ι_desc _ _

/-- The diagram of the biproduct terms of the Mayer--Vietoris sequences of the levels. -/
def middleDiagram (n : ℕ) : I ⥤ AddCommGrpCat.{w} where
  obj i := Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₂ ⊞ Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₃
  map a := biprod.map ((F.cohomologyPresheaf.{w} n).map (Ψ.functor.map a.op).τ₂.op)
    ((F.cohomologyPresheaf.{w} n).map (Ψ.functor.map a.op).τ₃.op)
  map_id i := by
    refine Eq.trans (congrArg₂ biprod.map ?_ ?_) (biprod_map_id _ _) <;> simp
  map_comp {i j k} a b := by
    refine Eq.trans (congrArg₂ biprod.map ?_ ?_) (biprod_map_comp_map _ _ _ _).symm <;> simp

/-- The transition map of the biproduct diagram is the biproduct of the two restrictions. -/
theorem middleDiagram_map (n : ℕ) {i j : I} (a : i ⟶ j) :
    (middleDiagram F Ψ n).map a =
      biprod.map ((F.cohomologyPresheaf.{w} n).map (Ψ.functor.map a.op).τ₂.op)
        ((F.cohomologyPresheaf.{w} n).map (Ψ.functor.map a.op).τ₃.op) := rfl

include hleg in
/-- The restriction from a level to the vertex on the biproduct terms. -/
def middleLeg (n : ℕ) (i : I) :
    (middleDiagram F Ψ n).obj i ⟶ Sheaf.H'.{w} F n T.X₂ ⊞ Sheaf.H'.{w} F n T.X₃ :=
  biprod.map ((F.cohomologyPresheaf.{w} n).map (leg (op i)).τ₂.op)
    ((F.cohomologyPresheaf.{w} n).map (leg (op i)).τ₃.op)

/-- The cocone of restrictions on the biproduct terms. -/
def middleCocone (n : ℕ) : Cocone (middleDiagram F Ψ n) where
  pt := Sheaf.H'.{w} F n T.X₂ ⊞ Sheaf.H'.{w} F n T.X₃
  ι :=
    { app := middleLeg F Ψ T leg n
      naturality := fun i j a => by
        refine Eq.trans ?_ (Category.comp_id _).symm
        refine Eq.trans (biprod_map_comp_map _ _ _ _) (congrArg₂ biprod.map ?_ ?_)
        · exact cornerDiagram_map_comp_leg F Ψ T leg hleg (evSquare₂ C) n a
        · exact cornerDiagram_map_comp_leg F Ψ T leg hleg (evSquare₃ C) n a }

/-- **The comparison morphism at the biproduct term** of the Mayer--Vietoris sequence. -/
def middleComparison [HasColimitsOfShape I AddCommGrpCat.{w}] (n : ℕ) :
    colimit (middleDiagram F Ψ n) ⟶ Sheaf.H'.{w} F n T.X₂ ⊞ Sheaf.H'.{w} F n T.X₃ :=
  colimit.desc _ (middleCocone F Ψ T leg hleg n)

/-- The comparison morphism at the biproduct term restricts, on the colimit inclusion of a level,
to the restriction from that level to the vertex. -/
@[reassoc]
theorem ι_middleComparison [HasColimitsOfShape I AddCommGrpCat.{w}] (n : ℕ) (i : I) :
    colimit.ι (middleDiagram F Ψ n) i ≫ middleComparison F Ψ T leg hleg n =
      middleLeg F Ψ T leg n i :=
  colimit.ι_desc _ _

/-! ### The Mayer--Vietoris sequence of the system -/

/-- The sum of the two restrictions, as a morphism of diagrams. -/
def toBiprodNat (n : ℕ) :
    cornerDiagram F Ψ (evSquare₄ C) n ⟶ middleDiagram F Ψ n where
  app i := (Ψ.sq (op i)).toBiprod F n
  naturality := fun i j a =>
    (toBiprod_naturality_square (S := Ψ.sq (op j)) (S' := Ψ.sq (op i)) F
      (Ψ.functor.map a.op) n).symm

/-- The difference of the two restrictions, as a morphism of diagrams. -/
def fromBiprodNat (n : ℕ) :
    middleDiagram F Ψ n ⟶ cornerDiagram F Ψ (evSquare₁ C) n where
  app i := (Ψ.sq (op i)).fromBiprod F n
  naturality := fun i j a =>
    (fromBiprod_naturality_square (S := Ψ.sq (op j)) (S' := Ψ.sq (op i)) F
      (Ψ.functor.map a.op) n).symm

/-- The connecting morphisms, as a morphism of diagrams. -/
def deltaNat (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    cornerDiagram F Ψ (evSquare₁ C) n₀ ⟶ cornerDiagram F Ψ (evSquare₄ C) n₁ where
  app i := (Ψ.sq (op i)).δ F n₀ n₁ h
  naturality := fun i j a =>
    (delta_naturality_square (S := Ψ.sq (op j)) (S' := Ψ.sq (op i)) F
      (Ψ.functor.map a.op) n₀ n₁ h).symm

/-! ### The biproduct term as a biproduct of diagrams -/

/-- The first projection of the biproduct diagram. -/
def biprodFstNat (n : ℕ) : middleDiagram F Ψ n ⟶ cornerDiagram F Ψ (evSquare₂ C) n where
  app i := biprod.fst (X := Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₂)
    (Y := Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₃)
  naturality := fun _ _ _ => biprod.map_fst _ _

/-- The second projection of the biproduct diagram. -/
def biprodSndNat (n : ℕ) : middleDiagram F Ψ n ⟶ cornerDiagram F Ψ (evSquare₃ C) n where
  app i := biprod.snd (X := Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₂)
    (Y := Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₃)
  naturality := fun _ _ _ => biprod.map_snd _ _

/-- The first inclusion into the biproduct diagram. -/
def biprodInlNat (n : ℕ) : cornerDiagram F Ψ (evSquare₂ C) n ⟶ middleDiagram F Ψ n where
  app i := biprod.inl (X := Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₂)
    (Y := Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₃)
  naturality := fun _ _ _ => (biprod.inl_map _ _).symm

/-- The second inclusion into the biproduct diagram. -/
def biprodInrNat (n : ℕ) : cornerDiagram F Ψ (evSquare₃ C) n ⟶ middleDiagram F Ψ n where
  app i := biprod.inr (X := Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₂)
    (Y := Sheaf.H'.{w} F n (Ψ.functor.obj (op i)).X₃)
  naturality := fun _ _ _ => (biprod.inr_map _ _).symm

/-- The first inclusion followed by the first projection is the identity. -/
theorem biprodInlNat_biprodFstNat (n : ℕ) :
    biprodInlNat F Ψ n ≫ biprodFstNat F Ψ n = 𝟙 _ :=
  NatTrans.ext (funext fun _ => biprod.inl_fst ..)

/-- The second inclusion followed by the second projection is the identity. -/
theorem biprodInrNat_biprodSndNat (n : ℕ) :
    biprodInrNat F Ψ n ≫ biprodSndNat F Ψ n = 𝟙 _ :=
  NatTrans.ext (funext fun _ => biprod.inr_snd ..)

/-- The first inclusion followed by the second projection is zero. -/
theorem biprodInlNat_biprodSndNat (n : ℕ) :
    biprodInlNat F Ψ n ≫ biprodSndNat F Ψ n = 0 :=
  NatTrans.ext (funext fun _ => biprod.inl_snd ..)

/-- The second inclusion followed by the first projection is zero. -/
theorem biprodInrNat_biprodFstNat (n : ℕ) :
    biprodInrNat F Ψ n ≫ biprodFstNat F Ψ n = 0 :=
  NatTrans.ext (funext fun _ => biprod.inr_fst ..)

/-- The sum of the projections followed by the corresponding inclusions is the identity of the
biproduct diagram. -/
theorem biprodNat_total (n : ℕ) :
    biprodFstNat F Ψ n ≫ biprodInlNat F Ψ n + biprodSndNat F Ψ n ≫ biprodInrNat F Ψ n = 𝟙 _ :=
  NatTrans.ext (funext fun _ => biprod.total ..)

/-! ### The colimit of the Mayer--Vietoris sequences -/

section Colim

variable [HasColimitsOfShape I AddCommGrpCat.{w}]
  [HasExactColimitsOfShape I AddCommGrpCat.{w}]

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
include hleg in
/-- The comparison at the biproduct term followed by the first projection is the colimit of the
first projection followed by the comparison at the corner `X₂`. -/
theorem middleComparison_fst (n : ℕ) :
    middleComparison F Ψ T leg hleg n ≫ biprod.fst =
      colim.map (biprodFstNat F Ψ n) ≫ cornerComparison F Ψ T leg hleg (evSquare₂ C) n := by
  refine colimit.hom_ext fun j => ?_
  rw [ι_middleComparison_assoc, ← colimMap_eq, ι_colimMap_assoc, ι_cornerComparison]
  exact biprod.map_fst _ _

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
include hleg in
/-- The comparison at the biproduct term followed by the second projection is the colimit of the
second projection followed by the comparison at the corner `X₃`. -/
theorem middleComparison_snd (n : ℕ) :
    middleComparison F Ψ T leg hleg n ≫ biprod.snd =
      colim.map (biprodSndNat F Ψ n) ≫ cornerComparison F Ψ T leg hleg (evSquare₃ C) n := by
  refine colimit.hom_ext fun j => ?_
  rw [ι_middleComparison_assoc, ← colimMap_eq, ι_colimMap_assoc, ι_cornerComparison]
  exact biprod.map_snd _ _

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
include hleg in
/-- **The comparison at the biproduct term is invertible** as soon as the comparisons at the two
corners `X₂` and `X₃` are. -/
theorem isIso_middleComparison (n : ℕ)
    (h₂ : IsIso (cornerComparison F Ψ T leg hleg (evSquare₂ C) n))
    (h₃ : IsIso (cornerComparison F Ψ T leg hleg (evSquare₃ C) n)) :
    IsIso (middleComparison F Ψ T leg hleg n) :=
  isIso_of_additive_of_split_biprod colim (biprodFstNat F Ψ n) (biprodSndNat F Ψ n)
    (biprodInlNat F Ψ n) (biprodInrNat F Ψ n) (biprodInlNat_biprodFstNat F Ψ n)
    (biprodInrNat_biprodSndNat F Ψ n) (biprodInlNat_biprodSndNat F Ψ n)
    (biprodInrNat_biprodFstNat F Ψ n) (biprodNat_total F Ψ n) _ _ _
    (middleComparison_fst F Ψ T leg hleg n) (middleComparison_snd F Ψ T leg hleg n)

/-- **The six-term window of the Mayer--Vietoris sequence of the system, after the colimit.** -/
def colimSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : ComposableArrows AddCommGrpCat.{w} 5 :=
  ComposableArrows.mk₅ (colim.map (toBiprodNat F Ψ n₀)) (colim.map (fromBiprodNat F Ψ n₀))
    (colim.map (deltaNat F Ψ n₀ n₁ h)) (colim.map (toBiprodNat F Ψ n₁))
    (colim.map (fromBiprodNat F Ψ n₁))

/-- **The colimit of the Mayer--Vietoris sequences is exact.** Along a shape whose colimits of
abelian groups are exact -- a filtered shape, for instance -- the long exact sequences of the
levels give a long exact sequence. -/
theorem colimSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (colimSequence F Ψ n₀ n₁ h).Exact := by
  have hpt : ∀ j : I, ((Ψ.sq (op j)).sequence F n₀ n₁ h).Exact :=
    fun j => (Ψ.sq (op j)).sequence_exact F n₀ n₁ h
  have hz : ∀ {A B D : I ⥤ AddCommGrpCat.{w}} (f : A ⟶ B) (g : B ⟶ D), f ≫ g = 0 →
      colim.map f ≫ colim.map g = 0 := fun f g hfg => by
    rw [← Functor.map_comp, hfg, Functor.map_zero]
  have hex : ∀ {A B D : I ⥤ AddCommGrpCat.{w}} (f : A ⟶ B) (g : B ⟶ D) (w : f ≫ g = 0),
      (∀ j : I, ((ShortComplex.mk f g w).map ((evaluation I _).obj j)).Exact) →
        ((ShortComplex.mk f g w).map colim).Exact := fun f g w h =>
    (shortComplex_exact_of_pointwise _ h).map colim
  have w₀ : toBiprodNat F Ψ n₀ ≫ fromBiprodNat F Ψ n₀ = 0 :=
    NatTrans.ext (funext fun j => (Ψ.sq (op j)).toBiprod_fromBiprod F n₀)
  have w₁ : fromBiprodNat F Ψ n₀ ≫ deltaNat F Ψ n₀ n₁ h = 0 :=
    NatTrans.ext (funext fun j => (Ψ.sq (op j)).fromBiprod_δ F n₀ n₁ h)
  have w₂ : deltaNat F Ψ n₀ n₁ h ≫ toBiprodNat F Ψ n₁ = 0 :=
    NatTrans.ext (funext fun j => (Ψ.sq (op j)).δ_toBiprod F n₀ n₁ h)
  have w₃ : toBiprodNat F Ψ n₁ ≫ fromBiprodNat F Ψ n₁ = 0 :=
    NatTrans.ext (funext fun j => (Ψ.sq (op j)).toBiprod_fromBiprod F n₁)
  refine ComposableArrows.Exact.mk (ComposableArrows.IsComplex.mk ?_) ?_
  · intro i hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by lia
    exacts [hz _ _ w₀, hz _ _ w₁, hz _ _ w₂, hz _ _ w₃]
  · intro i hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by lia
    exacts [hex _ _ w₀ fun j => (hpt j).exact 0, hex _ _ w₁ fun j => (hpt j).exact 1,
      hex _ _ w₂ fun j => (hpt j).exact 2, hex _ _ w₃ fun j => (hpt j).exact 3]

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
include hleg in
/-- The comparison morphisms commute with the sums of the two restrictions. -/
theorem toBiprodNat_comparison_comm (n : ℕ) :
    colim.map (toBiprodNat F Ψ n) ≫ middleComparison F Ψ T leg hleg n =
      cornerComparison F Ψ T leg hleg (evSquare₄ C) n ≫ T.toBiprod F n := by
  refine colimit.hom_ext fun j => ?_
  rw [← colimMap_eq, ι_colimMap_assoc, ι_middleComparison, ι_cornerComparison_assoc]
  exact toBiprod_naturality_square (S := T) (S' := Ψ.sq (op j)) F (leg (op j)) n

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
include hleg in
/-- The comparison morphisms commute with the differences of the two restrictions. -/
theorem fromBiprodNat_comparison_comm (n : ℕ) :
    colim.map (fromBiprodNat F Ψ n) ≫ cornerComparison F Ψ T leg hleg (evSquare₁ C) n =
      middleComparison F Ψ T leg hleg n ≫ T.fromBiprod F n := by
  refine colimit.hom_ext fun j => ?_
  rw [← colimMap_eq, ι_colimMap_assoc, ι_cornerComparison, ι_middleComparison_assoc]
  exact fromBiprod_naturality_square (S := T) (S' := Ψ.sq (op j)) F (leg (op j)) n

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
include hleg in
/-- The comparison morphisms commute with the connecting morphisms. -/
theorem deltaNat_comparison_comm (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    colim.map (deltaNat F Ψ n₀ n₁ h) ≫ cornerComparison F Ψ T leg hleg (evSquare₄ C) n₁ =
      cornerComparison F Ψ T leg hleg (evSquare₁ C) n₀ ≫ T.δ F n₀ n₁ h := by
  refine colimit.hom_ext fun j => ?_
  rw [← colimMap_eq, ι_colimMap_assoc, ι_cornerComparison, ι_cornerComparison_assoc]
  exact delta_naturality_square (S := T) (S' := Ψ.sq (op j)) F (leg (op j)) n₀ n₁ h

/-- **The comparison, as a morphism of Mayer--Vietoris sequences.** -/
def colimSequenceMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    colimSequence F Ψ n₀ n₁ h ⟶ T.sequence F n₀ n₁ h :=
  ComposableArrows.homMk₅ (cornerComparison F Ψ T leg hleg (evSquare₄ C) n₀)
    (middleComparison F Ψ T leg hleg n₀)
    (cornerComparison F Ψ T leg hleg (evSquare₁ C) n₀)
    (cornerComparison F Ψ T leg hleg (evSquare₄ C) n₁)
    (middleComparison F Ψ T leg hleg n₁)
    (cornerComparison F Ψ T leg hleg (evSquare₁ C) n₁)
    (toBiprodNat_comparison_comm F Ψ T leg hleg n₀)
    (fromBiprodNat_comparison_comm F Ψ T leg hleg n₀)
    (deltaNat_comparison_comm F Ψ T leg hleg n₀ n₁ h)
    (toBiprodNat_comparison_comm F Ψ T leg hleg n₁)
    (fromBiprodNat_comparison_comm F Ψ T leg hleg n₁)

/-! ### The initial segment, in degree zero -/

/-- The initial three-term segment of the colimit of the Mayer--Vietoris sequences. -/
def colimInitialSegment : ComposableArrows AddCommGrpCat.{w} 2 :=
  ComposableArrows.mk₂ (colim.map (toBiprodNat F Ψ 0)) (colim.map (fromBiprodNat F Ψ 0))

/-- The initial three-term segment of the Mayer--Vietoris sequence of the vertex. -/
def initialSegment : ComposableArrows AddCommGrpCat.{w} 2 :=
  ComposableArrows.mk₂ (T.toBiprod F 0) (T.fromBiprod F 0)

/-- The comparison on the initial three-term segments. -/
def initialSegmentMap : colimInitialSegment F Ψ ⟶ initialSegment F T :=
  ComposableArrows.homMk₂ (cornerComparison F Ψ T leg hleg (evSquare₄ C) 0)
    (middleComparison F Ψ T leg hleg 0)
    (cornerComparison F Ψ T leg hleg (evSquare₁ C) 0)
    (toBiprodNat_comparison_comm F Ψ T leg hleg 0)
    (fromBiprodNat_comparison_comm F Ψ T leg hleg 0)

/-- The initial segment of the colimit of the Mayer--Vietoris sequences is exact. -/
theorem colimInitialSegment_exact : (colimInitialSegment F Ψ).Exact :=
  ComposableArrows.exact₂_mk _ _ ((colimSequence_exact F Ψ 0 1 rfl).exact 0)

/-- The initial segment of the Mayer--Vietoris sequence of the vertex is exact. -/
theorem initialSegment_exact : (initialSegment F T).Exact :=
  ComposableArrows.exact₂_mk _ _ ((T.sequence_exact F 0 1 rfl).exact 0)

/-- The first map of the initial segment of the colimit of the Mayer--Vietoris sequences is a
monomorphism. -/
theorem mono_colimInitialSegment_map : Mono (colim.map (toBiprodNat F Ψ 0)) := by
  have : ∀ i : I, Mono ((toBiprodNat F Ψ 0).app i) :=
    fun i => mono_toBiprod_zero (Ψ.sq (op i)) F
  have : Mono (toBiprodNat F Ψ 0) := NatTrans.mono_of_mono_app _
  infer_instance

/-! ### The descent -/

include hleg in
/-- **Mayer--Vietoris descent for a colimit comparison.** If the comparison morphism
`colim_i H^m(Ψ i, F) ⟶ H^m(T, F)` is an isomorphism over the corners `X₁`, `X₂` and `X₃` in
every degree, then it is an isomorphism over the corner `X₄` in every degree. -/
theorem isIso_cornerComparison_X₄
    (h₁ : ∀ m : ℕ, IsIso (cornerComparison F Ψ T leg hleg (evSquare₁ C) m))
    (h₂ : ∀ m : ℕ, IsIso (cornerComparison F Ψ T leg hleg (evSquare₂ C) m))
    (h₃ : ∀ m : ℕ, IsIso (cornerComparison F Ψ T leg hleg (evSquare₃ C) m)) :
    ∀ n : ℕ, IsIso (cornerComparison F Ψ T leg hleg (evSquare₄ C) n) := by
  have hbp : ∀ m : ℕ, IsIso (middleComparison F Ψ T leg hleg m) :=
    fun m => isIso_middleComparison F Ψ T leg hleg m (h₂ m) (h₃ m)
  intro n
  match n with
  | 0 =>
    have : IsIso (ComposableArrows.app' (initialSegmentMap F Ψ T leg hleg) 1) := hbp 0
    have : IsIso (ComposableArrows.app' (initialSegmentMap F Ψ T leg hleg) 2) := h₁ 0
    exact Abelian.isIso_of_isIso_of_mono (initialSegmentMap F Ψ T leg hleg)
      (colimInitialSegment_exact F Ψ) (initialSegment_exact F T)
      (mono_colimInitialSegment_map F Ψ) (mono_toBiprod_zero T F) inferInstance inferInstance
  | (m + 1) =>
    have : IsIso (ComposableArrows.app' (colimSequenceMap F Ψ T leg hleg m (m + 1) rfl) 1) :=
      hbp m
    have : IsIso (ComposableArrows.app' (colimSequenceMap F Ψ T leg hleg m (m + 1) rfl) 2) :=
      h₁ m
    have : IsIso (ComposableArrows.app' (colimSequenceMap F Ψ T leg hleg m (m + 1) rfl) 4) :=
      hbp (m + 1)
    have : IsIso (ComposableArrows.app' (colimSequenceMap F Ψ T leg hleg m (m + 1) rfl) 5) :=
      h₁ (m + 1)
    exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' (k := 1) (by omega)
      (colimSequence_exact F Ψ m (m + 1) rfl) (T.sequence_exact F m (m + 1) rfl)
      (colimSequenceMap F Ψ T leg hleg m (m + 1) rfl) 1 2 3 4 5 rfl rfl rfl rfl rfl
      inferInstance inferInstance inferInstance inferInstance

end Colim

end Descent

end Stacks.Cohomology.MayerVietoris

end
