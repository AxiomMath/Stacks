module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.CategoryTheory.BifunctorProdMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of the relative cup product: associativity, commutativity, composition

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi.  The relative cup product of
[Stacks, Tag 0B6C] is

`Rf_*K ⊗^L_{𝒪'} Rf_*L ⟶ Rf_*(K ⊗^L_𝒪 L)`,

the adjoint transpose of the comparison of [Stacks, Tag 07A4] followed by the counit of
`Lf^* ⊣ Rf_*` in both tensor factors.  This file proves the three coherence properties of that
map that the source states right after the construction.

## Main results

Each is proved first in the abstract setting of an adjunction `L ⊣ R` with a bifunctor on each
side and a comparison of the two along `L`, and then instantiated at the relative cup product.

* `adjunctionCupProduct_assoc` and `relativeCupProduct_assoc` — **[Stacks, Tag 0FPL]**,
  associativity: contracting `K ⊗ L` first and contracting `L ⊗ M` first agree.
* `adjunctionCupProduct_braiding` and `relativeCupProduct_braiding` — **[Stacks, Tag 0FPM]**,
  commutativity: the square with the symmetry `ψ` on the source and `Rf_*ψ` on the target
  commutes.
* `adjunctionCupProduct_comp` and `relativeCupProduct_comp` — **[Stacks, Tag 0FPN]**,
  compatibility with the composition of two morphisms of ringed topoi.

## Implementation notes

*What the source draws and what is stated here.*  All three statements of the source are the
commutativity of a square, i.e. an equality of two composites; that is what is stated, and in
each case the two composites differ.  The source draws its diagrams with `⊗^L` treated as
strictly associative and with `R(f' ∘ f)_*` *equal* to `Rf'_* ∘ Rf_*`.  Neither is an equality
here, so the constraints appear explicitly:

* For [Stacks, Tag 0FPL] the two associativity constraints — one for `⊗^L_{𝒪'}` and one for
  `⊗^L_𝒪` — are arguments, since the source's suppressed `Rf_*K ⊗ Rf_*L ⊗ Rf_*M` has to be
  bracketed to be a Lean object.
* For [Stacks, Tag 0FPM] the commutativity constraint `ψ` of [Stacks, Tag 0FPT] is an argument
  on each side, and it occurs as `ψ` on the source of the cup product and as `Rf_*ψ` on its
  target, exactly as in the source's square.
* For [Stacks, Tag 0FPN] the source's `@{=}` edge `R(f' ∘ f)_* = Rf'_*Rf_*` is realized as the
  **identification carried by the composite adjunction**: `R(f' ∘ f)_*` is taken to be
  `Rf_* ⋙ Rf'_*` with the adjunction `L(f')^*Lf^*… ⊣ Rf_* ⋙ Rf'_*` of
  `CategoryTheory.Adjunction.comp`, whose counit is the composition of the two counits.  That
  is precisely the content the source invokes for the edge ([Stacks, Tag 0DV0]), so the two
  `@{=}` edges of the square become identities and nothing is absorbed silently.  This
  repository also has the composition isomorphism
  `Stacks.Cohomology.DerivedBaseChangePasting.derivedPushforwardCompIso`
  `: Rf_* ⋙ Rf'_* ≅ R(f' ∘ f)_*`, an *isomorphism* and not an equality; transporting the
  statement below along it would additionally need the compatibility of [Stacks, Tag 07A4] with
  composition of morphisms of ringed topoi, which this development does not have.

*The hypotheses carried beyond the source.*  The source gets its diagrams from the symmetric
monoidal structure of [Stacks, Tag 0FPT] on `D(𝒪)` and `D(𝒪')` together with the fact that
`Lf^*` is a symmetric monoidal functor for the comparison of [Stacks, Tag 07A4].  This
development has neither the monoidal structure assembled (see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/DerivedSymmetryAndUnit.lean`) nor the
monoidality of the comparison.  Accordingly [Stacks, Tag 0FPL] and [Stacks, Tag 0FPM] below take
the constraints and the monoidality of the comparison as explicit hypotheses, and the clause
strings on their attributes say so.  [Stacks, Tag 0FPN] carries no hypothesis beyond the data of
the two morphisms of ringed topoi.

*Why the abstract layer.*  Each statement is an equality between composites of maps built from a
bifunctor applied to a pair of large objects of a derived category.  Proving the identities over
an arbitrary adjunction and arbitrary bifunctors keeps every term small; the concrete statements
are then one `exact` each.

## References

* [Stacks Project, Tag 0FPL](https://stacks.math.columbia.edu/tag/0FPL)
* [Stacks Project, Tag 0FPM](https://stacks.math.columbia.edu/tag/0FPM)
* [Stacks Project, Tag 0FPN](https://stacks.math.columbia.edu/tag/0FPN)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0DV0](https://stacks.math.columbia.edu/tag/0DV0)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

universe v₀ v₁ v₂ u₀ u₁ u₂ u

/-! ### Transposition lemmas for the abstract cup product -/

section Transpose

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The defining property of `adjunctionCupProduct`: its adjoint transpose is the comparison
followed by the counit in both factors. Tagged `@[reassoc]` so that it can be used as a rewrite
rule in the middle of a composite. -/
@[reassoc]
lemma adjunctionCupProduct_transpose (G H : D) :
    L.map (adjunctionCupProduct adj A B α G H) ≫ adj.counit.app (B.obj (G, H)) =
      α.app (R.obj G, R.obj H) ≫ B.map (adj.counit.app G ×ₘ adj.counit.app H) := by
  have h := (adj.homEquiv (A.obj (R.obj G, R.obj H)) (B.obj (G, H))).symm_apply_apply
    (α.app (R.obj G, R.obj H) ≫ B.map (adj.counit.app G ×ₘ adj.counit.app H))
  rwa [Adjunction.homEquiv_counit] at h

/-- The cup product precomposed with a map, as a single adjoint transpose. -/
lemma adjunctionCupProduct_pre {Z : C} (G H : D) (v : Z ⟶ A.obj (R.obj G, R.obj H)) :
    v ≫ adjunctionCupProduct adj A B α G H =
      adj.homEquiv _ _ (L.map v ≫ α.app (R.obj G, R.obj H) ≫
        B.map (adj.counit.app G ×ₘ adj.counit.app H)) := by
  unfold adjunctionCupProduct
  rw [← Adjunction.homEquiv_naturality_left]
  rfl

/-- The cup product pre- and post-composed with maps, as a single adjoint transpose. -/
lemma adjunctionCupProduct_pre_post {Z : C} (G H : D) (v : Z ⟶ A.obj (R.obj G, R.obj H))
    {W : D} (w : B.obj (G, H) ⟶ W) :
    v ≫ adjunctionCupProduct adj A B α G H ≫ R.map w =
      adj.homEquiv _ _ (L.map v ≫ α.app (R.obj G, R.obj H) ≫
        B.map (adj.counit.app G ×ₘ adj.counit.app H) ≫ w) := by
  unfold adjunctionCupProduct
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left,
    Category.assoc]

/-- The cup product postcomposed with a map, as a single adjoint transpose. -/
private lemma adjunctionCupProduct_post (G H : D) {W : D} (w : B.obj (G, H) ⟶ W) :
    adjunctionCupProduct adj A B α G H ≫ R.map w =
      adj.homEquiv _ _ (α.app (R.obj G, R.obj H) ≫
        B.map (adj.counit.app G ×ₘ adj.counit.app H) ≫ w) := by
  simpa using adjunctionCupProduct_pre_post adj A B α G H (𝟙 _) w

end Transpose

/-! ### Associativity in the abstract setting -/

section Assoc

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **Associativity of the abstract cup product.**  Let `aA` and `aB` be associativity
constraints for the two bifunctors, let `aB` be natural (`haB`), and let the comparison `α` be
compatible with the two constraints (`hα`, the associativity law of a monoidal functor).
Then the square

```
A(A(RG₁, RG₂), RG₃) ----→ A(R B(G₁,G₂), RG₃) ----→ R B(B(G₁,G₂), G₃)
        |                                                 ↑
        | aA                                              | R aB⁻¹
        ↓                                                 |
A(RG₁, A(RG₂, RG₃)) ----→ A(RG₁, R B(G₂,G₃)) ----→ R B(G₁, B(G₂,G₃))
```

commutes: contracting the first two factors first and contracting the last two factors first
give the same map. -/
theorem adjunctionCupProduct_assoc
    (aA : ∀ P Q S : C, A.obj (A.obj (P, Q), S) ⟶ A.obj (P, A.obj (Q, S)))
    (aB : ∀ U V W : D, B.obj (B.obj (U, V), W) ≅ B.obj (U, B.obj (V, W)))
    (haB : ∀ {U U' V V' W W' : D} (u : U ⟶ U') (v : V ⟶ V') (w : W ⟶ W'),
      (aB U V W).hom ≫ B.map (u ×ₘ B.map (v ×ₘ w)) =
        B.map (B.map (u ×ₘ v) ×ₘ w) ≫ (aB U' V' W').hom)
    (hα : ∀ P Q S : C,
      α.app (A.obj (P, Q), S) ≫ B.map (α.app (P, Q) ×ₘ 𝟙 (L.obj S)) ≫
          (aB (L.obj P) (L.obj Q) (L.obj S)).hom =
        L.map (aA P Q S) ≫ α.app (P, A.obj (Q, S)) ≫ B.map (𝟙 (L.obj P) ×ₘ α.app (Q, S)))
    (G₁ G₂ G₃ : D) :
    A.map (adjunctionCupProduct adj A B α G₁ G₂ ×ₘ 𝟙 (R.obj G₃)) ≫
        adjunctionCupProduct adj A B α (B.obj (G₁, G₂)) G₃ =
      aA (R.obj G₁) (R.obj G₂) (R.obj G₃) ≫
        A.map (𝟙 (R.obj G₁) ×ₘ adjunctionCupProduct adj A B α G₂ G₃) ≫
          adjunctionCupProduct adj A B α G₁ (B.obj (G₂, G₃)) ≫ R.map (aB G₁ G₂ G₃).inv := by
  have hlhs : A.map (adjunctionCupProduct adj A B α G₁ G₂ ×ₘ 𝟙 (R.obj G₃)) ≫
      adjunctionCupProduct adj A B α (B.obj (G₁, G₂)) G₃ =
      adj.homEquiv _ _ (α.app (A.obj (R.obj G₁, R.obj G₂), R.obj G₃) ≫
        B.map (α.app (R.obj G₁, R.obj G₂) ×ₘ 𝟙 (L.obj (R.obj G₃))) ≫
        B.map (B.map (adj.counit.app G₁ ×ₘ adj.counit.app G₂) ×ₘ adj.counit.app G₃)) := by
    rw [adjunctionCupProduct_pre]
    congr 1
    slice_lhs 1 2 => rw [bifunctor_comparison_naturality A B α
      (adjunctionCupProduct adj A B α G₁ G₂) (𝟙 (R.obj G₃))]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [← B.map_comp, prod_comp, L.map_id, Category.id_comp,
      adjunctionCupProduct_transpose, bifunctor_map_comp_left]
  rw [hlhs, ← Category.assoc (aA (R.obj G₁) (R.obj G₂) (R.obj G₃)),
    adjunctionCupProduct_pre_post]
  congr 1
  conv_rhs => rw [L.map_comp]
  simp only [Category.assoc]
  slice_rhs 2 3 => rw [bifunctor_comparison_naturality A B α (𝟙 (R.obj G₁))
    (adjunctionCupProduct adj A B α G₂ G₃)]
  simp only [Category.assoc, L.map_id]
  slice_rhs 3 4 => rw [← B.map_comp, prod_comp, Category.id_comp,
    adjunctionCupProduct_transpose, bifunctor_map_comp_right]
  simp only [← Category.assoc]
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
  slice_lhs 3 4 => rw [← haB]
  slice_rhs 1 3 => rw [← hα]
  simp only [Category.assoc]

end Assoc

/-! ### Commutativity in the abstract setting -/

section Braiding

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **Commutativity of the abstract cup product.**  Let `sA` and `sB` be commutativity
constraints for the two bifunctors, let `sB` be natural (`hsB`), and let the comparison `α` be
compatible with the two (`hα`, the constraint law of a braided functor).  Then the square

```
A(RG, RH) --cup--→ R B(G, H)
    | sA                | R sB
    ↓                   ↓
A(RH, RG) --cup--→ R B(H, G)
```

commutes.  The two vertical maps are `sA` on the source and `R sB` on the target, which is the
source's `ψ` and `Rf_*ψ`. -/
theorem adjunctionCupProduct_braiding
    (sA : ∀ P Q : C, A.obj (P, Q) ⟶ A.obj (Q, P))
    (sB : ∀ U V : D, B.obj (U, V) ⟶ B.obj (V, U))
    (hsB : ∀ {U U' V V' : D} (u : U ⟶ U') (v : V ⟶ V'),
      B.map (u ×ₘ v) ≫ sB U' V' = sB U V ≫ B.map (v ×ₘ u))
    (hα : ∀ P Q : C, L.map (sA P Q) ≫ α.app (Q, P) = α.app (P, Q) ≫ sB (L.obj P) (L.obj Q))
    (G H : D) :
    adjunctionCupProduct adj A B α G H ≫ R.map (sB G H) =
      sA (R.obj G) (R.obj H) ≫ adjunctionCupProduct adj A B α H G := by
  rw [adjunctionCupProduct_post, adjunctionCupProduct_pre]
  congr 1
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
  slice_rhs 1 2 => rw [hα]
  slice_rhs 2 3 => rw [← hsB]

end Braiding

/-! ### Compatibility with composition in the abstract setting -/

section Composition

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  {Lf : C₁ ⥤ C₀} {Rf : C₀ ⥤ C₁} (adjf : Lf ⊣ Rf)
  {Lg : C₂ ⥤ C₁} {Rg : C₁ ⥤ C₂} (adjg : Lg ⊣ Rg)
  (B₀ : C₀ × C₀ ⥤ C₀) (B₁ : C₁ × C₁ ⥤ C₁) (B₂ : C₂ × C₂ ⥤ C₂)
  (αf : B₁ ⋙ Lf ⟶ Lf.prod Lf ⋙ B₀) (αg : B₂ ⋙ Lg ⟶ Lg.prod Lg ⋙ B₁)

/-- The comparison of the composite `Lg ⋙ Lf` with the two outer bifunctors: `Lf` applied to the
comparison for `Lg`, followed by the comparison for `Lf`.  This is the monoidal structure of a
composite of two monoidal functors, and it is the identification the source suppresses when it
writes `L(f' ∘ f)^*(A ⊗ B) = L(f' ∘ f)^*A ⊗ L(f' ∘ f)^*B`. -/
def compComparison : B₂ ⋙ (Lg ⋙ Lf) ⟶ (Lg ⋙ Lf).prod (Lg ⋙ Lf) ⋙ B₀ where
  app P := Lf.map (αg.app P) ≫ αf.app (Lg.obj P.1, Lg.obj P.2)
  naturality P Q h := by
    have h1 := αg.naturality h
    have h2 := αf.naturality (Lg.map h.1 ×ₘ Lg.map h.2)
    dsimp at h1 h2 ⊢
    rw [← Category.assoc, ← Lf.map_comp, h1, Lf.map_comp, Category.assoc, h2,
      ← Category.assoc]

/-- The composite comparison at a pair of objects. -/
lemma compComparison_app (P : C₂ × C₂) :
    (compComparison B₀ B₁ B₂ αf αg).app P =
      Lf.map (αg.app P) ≫ αf.app (Lg.obj P.1, Lg.obj P.2) :=
  rfl

/-- **The abstract cup product is compatible with composition.**  For the composite adjunction
`Lg ⋙ Lf ⊣ Rf ⋙ Rg` and the composite comparison `compComparison`, the cup product is the cup
product for `adjg` at the objects `Rf G`, `Rf H`, followed by `Rg` of the cup product for
`adjf`.  No hypothesis beyond the two adjunctions and the two comparisons is needed.

The one input about the composite adjunction is that its counit is the composition of the two
counits, `CategoryTheory.Adjunction.comp_counit_app`, which is where this repository registers
[Stacks, Tag 0DV0]; that is exactly the fact the source's proof appeals to. -/
theorem adjunctionCupProduct_comp (G H : C₀) :
    adjunctionCupProduct (adjg.comp adjf) B₂ B₀ (compComparison B₀ B₁ B₂ αf αg) G H =
      adjunctionCupProduct adjg B₂ B₁ αg (Rf.obj G) (Rf.obj H) ≫
        Rg.map (adjunctionCupProduct adjf B₁ B₀ αf G H) := by
  have hinner : (compComparison B₀ B₁ B₂ αf αg).app ((Rf ⋙ Rg).obj G, (Rf ⋙ Rg).obj H) ≫
        B₀.map ((adjg.comp adjf).counit.app G ×ₘ (adjg.comp adjf).counit.app H) =
      Lf.map (αg.app (Rg.obj (Rf.obj G), Rg.obj (Rf.obj H)) ≫
          B₁.map (adjg.counit.app (Rf.obj G) ×ₘ adjg.counit.app (Rf.obj H))) ≫
        αf.app (Rf.obj G, Rf.obj H) ≫
          B₀.map (adjf.counit.app G ×ₘ adjf.counit.app H) := by
    simp only [compComparison_app, Adjunction.comp_counit_app, Functor.map_comp, Category.assoc]
    rw [bifunctor_map_comp_both]
    have hnat := bifunctor_comparison_naturality B₁ B₀ αf (adjg.counit.app (Rf.obj G))
      (adjg.counit.app (Rf.obj H))
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hnat ⊢
    slice_rhs 2 3 => rw [hnat]
    simp only [Category.assoc]
  rw [adjunctionCupProduct_post, ← Category.assoc, adjunctionCupProduct_pre adjf B₁ B₀ αf G H
      (αg.app (Rg.obj (Rf.obj G), Rg.obj (Rf.obj H)) ≫
        B₁.map (adjg.counit.app (Rf.obj G) ×ₘ adjg.counit.app (Rf.obj H)))]
  show (adjg.comp adjf).homEquiv _ _ _ = _
  rw [hinner, Adjunction.comp_homEquiv]
  rfl

end Composition

/-! ### The derived tensor product as a bifunctor of a pair -/

section UncurriedTensor

attribute [local instance] HasDerivedCategory.standard

/-- The derived tensor product of [Stacks, Tag 06YU] on a ringed topos, read as a functor of the
pair: `(P, Q) ↦ P ⊗^L_𝒪 Q`.  This is the shape the abstract cup product consumes, and it is the
same bifunctor `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct` is built
from. -/
abbrev uncurriedDerivedTensor (W : RingedTopos.{u, u, u})
    [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O).obj M).Additive]
    [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ),
      HomologicalComplex.HasMapBifunctor P Q (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O)
        (ComplexShape.up ℤ)] :
    DerivedModules W.O × DerivedModules W.O ⥤ DerivedModules W.O :=
  Functor.uncurry.obj (derivedTensorProductFunctor W.O)

end UncurriedTensor

/-! ### Associativity and commutativity of the relative cup product of Tag 0B6C -/

section OneMorphism

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **[Stacks, Tag 0FPL].**  The relative cup product of [Stacks, Tag 0B6C] is associative: for
`K`, `L`, `M` in `D(𝒪)` the square

```
(Rf_*K ⊗' Rf_*L) ⊗' Rf_*M --→ Rf_*(K ⊗ L) ⊗' Rf_*M --→ Rf_*((K ⊗ L) ⊗ M)
          |                                                     ↑
          ↓                                                     |
Rf_*K ⊗' (Rf_*L ⊗' Rf_*M) --→ Rf_*K ⊗' Rf_*(L ⊗ M) --→ Rf_*(K ⊗ (L ⊗ M))
```

commutes in `D(𝒪')`.  The upper route contracts `K ⊗ L` first, the lower route contracts
`L ⊗ M` first; the two are different composites.

The source draws the square with `⊗^L` strictly associative, so the associativity constraints
are explicit here: `aY` is the one for `⊗^L_{𝒪'}` and `aX` the one for `⊗^L_𝒪`.  The hypotheses
beyond the source are `haX`, the naturality of `aX`, and `hcomp`, the compatibility of the
comparison of [Stacks, Tag 07A4] with the two constraints — i.e. that `Lf^*` is a monoidal
functor for it.  The source gets both from the symmetric monoidal structure of
[Stacks, Tag 0FPT], which this development does not assemble. -/
@[stacks 0FPL "associativity of the relative cup product, with the associativity constraints of \
  the two derived tensor products supplied as data and their naturality and the monoidality of \
  the comparison of Tag 07A4 for them carried as explicit hypotheses: this development has \
  neither the symmetric monoidal structure of Tag 0FPT assembled nor that monoidality"]
theorem relativeCupProduct_assoc
    (aY : ∀ P Q S : DerivedModules Y.O,
      (uncurriedDerivedTensor Y).obj ((uncurriedDerivedTensor Y).obj (P, Q), S) ⟶
        (uncurriedDerivedTensor Y).obj (P, (uncurriedDerivedTensor Y).obj (Q, S)))
    (aX : ∀ U V W : DerivedModules X.O,
      (uncurriedDerivedTensor X).obj ((uncurriedDerivedTensor X).obj (U, V), W) ≅
        (uncurriedDerivedTensor X).obj (U, (uncurriedDerivedTensor X).obj (V, W)))
    (haX : ∀ {U U' V V' W W' : DerivedModules X.O} (u : U ⟶ U') (v : V ⟶ V') (w : W ⟶ W'),
      (aX U V W).hom ≫
          (uncurriedDerivedTensor X).map (u ×ₘ (uncurriedDerivedTensor X).map (v ×ₘ w)) =
        (uncurriedDerivedTensor X).map ((uncurriedDerivedTensor X).map (u ×ₘ v) ×ₘ w) ≫
          (aX U' V' W').hom)
    (hcomp : ∀ P Q S : DerivedModules Y.O,
      (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app
            ((uncurriedDerivedTensor Y).obj (P, Q), S) ≫
          (uncurriedDerivedTensor X).map
            ((Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app (P, Q) ×ₘ
              𝟙 ((derivedPullback f).obj S)) ≫
          (aX ((derivedPullback f).obj P) ((derivedPullback f).obj Q)
            ((derivedPullback f).obj S)).hom =
        (derivedPullback f).map (aY P Q S) ≫
          (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app
            (P, (uncurriedDerivedTensor Y).obj (Q, S)) ≫
          (uncurriedDerivedTensor X).map (𝟙 ((derivedPullback f).obj P) ×ₘ
            (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app (Q, S)))
    (K L M : DerivedModules X.O) :
    (uncurriedDerivedTensor Y).map
          (relativeCupProduct f hmos K L ×ₘ 𝟙 ((derivedPushforward f).obj M)) ≫
        relativeCupProduct f hmos ((uncurriedDerivedTensor X).obj (K, L)) M =
      aY ((derivedPushforward f).obj K) ((derivedPushforward f).obj L)
            ((derivedPushforward f).obj M) ≫
        (uncurriedDerivedTensor Y).map
            (𝟙 ((derivedPushforward f).obj K) ×ₘ relativeCupProduct f hmos L M) ≫
          relativeCupProduct f hmos K ((uncurriedDerivedTensor X).obj (L, M)) ≫
            (derivedPushforward f).map (aX K L M).inv :=
  adjunctionCupProduct_assoc (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom aY aX haX hcomp K L M

/-- **[Stacks, Tag 0FPM].**  The relative cup product of [Stacks, Tag 0B6C] is commutative: for
`K`, `L` in `D(𝒪)` the square

```
Rf_*K ⊗' Rf_*L --cup--→ Rf_*(K ⊗ L)
      | ψ                     | Rf_*ψ
      ↓                       ↓
Rf_*L ⊗' Rf_*K --cup--→ Rf_*(L ⊗ K)
```

commutes in `D(𝒪')`.  The left edge is the commutativity constraint `sY` of `⊗^L_{𝒪'}` at the
pair `(Rf_*K, Rf_*L)`; the right edge is `Rf_*` applied to the commutativity constraint `sX` of
`⊗^L_𝒪` at `(K, L)`.  These are the source's `ψ` and `Rf_*ψ`, and they are different maps.

The constraint of [Stacks, Tag 0FPT] is supplied as data on each side, because this development
has it only one pair of objects at a time and not as part of an assembled monoidal structure
(`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso`).  The hypotheses beyond the
source are `hsX`, its naturality, and `hcomp`, the compatibility of the comparison of
[Stacks, Tag 07A4] with the two constraints — i.e. that `Lf^*` is a braided functor for it. -/
@[stacks 0FPM "commutativity of the relative cup product, with the commutativity constraints of \
  the two derived tensor products supplied as data and their naturality and the compatibility of \
  the comparison of Tag 07A4 with them carried as explicit hypotheses: this development has \
  neither the symmetric monoidal structure of Tag 0FPT assembled nor that compatibility"]
theorem relativeCupProduct_braiding
    (sY : ∀ P Q : DerivedModules Y.O,
      (uncurriedDerivedTensor Y).obj (P, Q) ⟶ (uncurriedDerivedTensor Y).obj (Q, P))
    (sX : ∀ U V : DerivedModules X.O,
      (uncurriedDerivedTensor X).obj (U, V) ⟶ (uncurriedDerivedTensor X).obj (V, U))
    (hsX : ∀ {U U' V V' : DerivedModules X.O} (u : U ⟶ U') (v : V ⟶ V'),
      (uncurriedDerivedTensor X).map (u ×ₘ v) ≫ sX U' V' =
        sX U V ≫ (uncurriedDerivedTensor X).map (v ×ₘ u))
    (hcomp : ∀ P Q : DerivedModules Y.O,
      (derivedPullback f).map (sY P Q) ≫
          (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app (Q, P) =
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app (P, Q) ≫
          sX ((derivedPullback f).obj P) ((derivedPullback f).obj Q))
    (K L : DerivedModules X.O) :
    relativeCupProduct f hmos K L ≫ (derivedPushforward f).map (sX K L) =
      sY ((derivedPushforward f).obj K) ((derivedPushforward f).obj L) ≫
        relativeCupProduct f hmos L K :=
  adjunctionCupProduct_braiding (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom sY sX hsX hcomp K L

end OneMorphism

/-! ### Compatibility of the relative cup product of Tag 0B6C with composition -/

section TwoMorphisms

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (f' : RingedToposSiteHom Y Z)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosf' : f'.u.IsMorphismOfSites Z.J Y.J)

/-- **[Stacks, Tag 0FPN].**  The relative cup product of [Stacks, Tag 0B6C] is compatible with
composition: for `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')`, `f' : (Sh(C'), 𝒪') ⟶ (Sh(C''), 𝒪'')` and
`K`, `L` in `D(𝒪)` the diagram

```
R(f'f)_*K ⊗'' R(f'f)_*L  ====  Rf'_*Rf_*K ⊗'' Rf'_*Rf_*L
        |                                  |
        ↓                                  ↓
R(f'f)_*(K ⊗ L)  ====  Rf'_*Rf_*(K ⊗ L)  ←--  Rf'_*(Rf_*K ⊗' Rf_*L)
```

commutes in `D(𝒪'')`: the cup product for the composite is the cup product for `f'` at
`(Rf_*K, Rf_*L)` followed by `Rf'_*` of the cup product for `f`.

**How the source's `@{=}` edges are handled.**  The source draws the two horizontal edges as
equalities `R(f' ∘ f)_* = Rf'_* ∘ Rf_*`.  In this development the two functors are not equal:
they are isomorphic by
`Stacks.Cohomology.DerivedBaseChangePasting.derivedPushforwardCompIso`.  Accordingly
`R(f' ∘ f)_*` is realized here as the composite `Rf_* ⋙ Rf'_*` with the composite
adjunction `L(f')^* ⋙ Lf^* ⊣ Rf_* ⋙ Rf'_*` of `CategoryTheory.Adjunction.comp`, whose counit is
the composition of the two counits — which is exactly the identification the source's proof
appeals to ([Stacks, Tag 0DV0]).  With that realization the two `@{=}` edges are identities and
no isomorphism is absorbed silently.  The comparison for the composite is correspondingly the
composite comparison `compComparison`, the monoidal structure of the composite of two monoidal
functors.  The statement holds for every pair of composable morphisms of ringed topoi that are
morphisms of sites.

Transporting this statement to `relativeCupProduct (f'.comp f)` — the cup product built from
`DerivedPullbackOnRingedTopoi.derivedAdjunction (f'.comp f)` and
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (f'.comp f)` — would additionally
require the compatibility of [Stacks, Tag 07A4] with composition of morphisms of ringed topoi,
which this development does not have.  The same gap is recorded on
`derivedBaseChangeMap_projectionFormulaMap_square` in
`Stacks.Cohomology.ProjectionFormulaOnRingedTopoi`. -/
@[stacks 0FPN "compatibility of the relative cup product with composition, with R(f' ∘ f)_* \
  realized as the composite Rf_* ⋙ Rf'_* and its adjunction the composite adjunction of Tag \
  0DV0 (the source's equality edge), and the comparison of Tag 07A4 for the composite taken to \
  be the composite of the two comparisons, for every pair of composable morphisms of sites"]
theorem relativeCupProduct_comp (K L : DerivedModules X.O) :
    adjunctionCupProduct
        ((DerivedPullbackOnRingedTopoi.derivedAdjunction f' hmosf').comp
          (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmosf))
        (uncurriedDerivedTensor Z) (uncurriedDerivedTensor X)
        (compComparison (uncurriedDerivedTensor X) (uncurriedDerivedTensor Y)
          (uncurriedDerivedTensor Z)
          (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmosf).hom
          (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f' hmosf').hom) K L =
      relativeCupProduct f' hmosf' ((derivedPushforward f).obj K)
            ((derivedPushforward f).obj L) ≫
        (derivedPushforward f').map (relativeCupProduct f hmosf K L) :=
  adjunctionCupProduct_comp (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmosf)
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f' hmosf')
    (uncurriedDerivedTensor X) (uncurriedDerivedTensor Y) (uncurriedDerivedTensor Z)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmosf).hom
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f' hmosf').hom K L

end TwoMorphisms

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
