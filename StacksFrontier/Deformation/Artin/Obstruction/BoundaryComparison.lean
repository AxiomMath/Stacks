module

public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Homology.DoubleExtend

/-!
# Comparing the boundary map of a short exact sequence with the triangle of a two-term complex

Two connecting maps are attached to a factorization `d = e ≫ ι` of the differential of a
two-term complex through a short exact sequence `0 → Y --ι--> X --p--> Z → 0` of `A`-modules.

* The sequence has the connecting map `Deformation.Artin.boundaryMap`, a map
  `H¹(K ⊗ᴸ Z) ⟶ H²(K ⊗ᴸ Y)`; the two-term complex `(N --d--> X)` maps to `Z` placed in degree
  zero, because `d ≫ p = e ≫ ι ≫ p = 0`, so the boundary map can be evaluated on classes
  coming from the two-term complex.
* The two-term complex `(N --e--> Y)` has the distinguished triangle
  `Y[0] ⟶ (N ⟶ Y) ⟶ N[-1] ⟶ Y[0]⟦1⟧` and hence the connecting map
  `H¹(K ⊗ᴸ N[-1]) ⟶ H²(K ⊗ᴸ Y)` of `Deformation.Artin.derivedTensorTwoTermδ`, which a class
  on `(N --d--> X)` reaches through the morphism `(N ⟶ X) ⟶ N[-1]` of its own triangle.

**The two agree up to sign.** This is proved first in the derived category of `A`-modules —
where the statement is about `CategoryTheory.ShortComplex.ShortExact.singleδ` and the third
morphism of `Deformation.Artin.twoTermTriangle`, and does not involve `K` — and then after
applying `H¹(K ⊗ᴸ -)`, which is the form the second clause of Stacks 07YY is phrased with:
for the conormal sequence `0 → Im(d) → Ω_{P/Λ} ⊗_P A → Ω_{A/Λ} → 0` of a presentation the
map `(N ⟶ X) ⟶ Z[0]` of the first bullet is `NL(α) ⟶ Ω_{A/Λ}`, and the identity says that
the obstruction boundary, evaluated on the image of a class of `H¹(K ⊗ᴸ NL(α))` in
`H¹(K ⊗ᴸ Ω_{A/Λ})`, is minus the connecting map of `NL(α)` applied to that class.

## Main definitions

* `Deformation.Artin.twoTermToQuotient` — the morphism `(N ⟶ X) ⟶ Z[0]` of cochain complexes
  given by `p` in degree zero, with `Deformation.Artin.eq_twoTermToQuotient` recognising it
  from its degree-zero component.
* `Deformation.Artin.boundaryComparisonComplex` — the complex `(N --(-e, d)--> Y ⊞ X)`, the
  middle term of a degreewise split short exact sequence
  `0 → Y[0] → (N ⟶ Y ⊞ X) → (N ⟶ X) → 0` of cochain complexes
  (`Deformation.Artin.boundaryComparisonShortComplex`). It maps to the sequence
  `0 → Y[0] → X[0] → Z[0] → 0` by `Deformation.Artin.boundaryComparisonHom` and to the
  sequence `0 → Y[0] → (N ⟶ Y) → N[-1] → 0` of the two-term complex by
  `Deformation.Artin.boundaryComparisonTwoTermHom`.

## Main results

* `Deformation.Artin.Q_map_twoTermToQuotient_comp_singleδ` — the comparison in the derived
  category: `Q(p) ≫ singleδ = -(mor₂ ≫ mor₃)`.
* `Deformation.Artin.derivedTensorCohomology_map_comp_boundaryMap` and
  `Deformation.Artin.derivedTensorCohomology_map_comp_boundaryMap'` — the comparison after
  applying `H¹(K ⊗ᴸ -)`, with the connecting map of the triangle written first as the
  connecting map of the tensored triangle and then, by
  `Deformation.Artin.derivedTensorTwoTermδ_eq`, as the degree shift followed by `H²(K ⊗ᴸ e)`.

## Implementation notes

The comparison complex is the only object that has to be built by hand: a degreewise split
short exact sequence of cochain complexes whose third term is the two-term complex `(N ⟶ X)`
and whose first term is `Y[0]` must have `Y ⊕ X` in degree zero, and the sign in its
differential `(-e, d)` is exactly what makes the projection `Y ⊞ X ⟶ X` of a splitting
compatible with the map to `X[0]`. Both comparisons are then instances of the naturality of
the connecting map in the short exact sequence — `DerivedCategory.triangleOfSESδ_naturality`
in the derived category and `CategoryTheory.Functor.homologySequenceδ_naturality` after
applying a homological functor — so no mapping cone and no explicit cocycle is needed, and
the sign appears through the morphism `-𝟙` on the first terms of the second comparison.

The identities `H²(K ⊗ᴸ 𝟙) = 𝟙` and `H²(K ⊗ᴸ (-𝟙)) = -𝟙` are stated as separate lemmas about
an arbitrary complex rather than rewritten in place: the objects of the triangles involved
are only definitionally, not reducibly, the objects of the short complexes they come from, so
the rewriting tactics cannot act on the composites, and the two naturality identities are
combined with `Eq.trans`, which compares types up to full definitional unfolding.

## References

* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated CategoryTheory.Preadditive NaiveCotangent HomologicalComplex
  CochainComplex
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

universe u

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {Sq : ShortComplex (ModuleCat.{u} A)} {N : ModuleCat.{u} A}

/-! ### The comparison complex -/

/-- The differential `(-e, e ≫ ι) : N ⟶ Y ⊞ X` of the comparison complex of a map
`e : N ⟶ Y` into the first term of a short exact sequence `0 → Y --ι--> X → Z → 0`. The sign
on the first component is what makes the map to `X[0]` a morphism of complexes. -/
public def boundaryComparisonDiff (e : N ⟶ Sq.X₁) : N ⟶ Sq.X₁ ⊞ Sq.X₂ :=
  biprod.lift (-e) (e ≫ Sq.f)

/-- The comparison complex `(N --(-e, e ≫ ι)--> Y ⊞ X)`, placed in cohomological degrees
`-1` and `0`. -/
public abbrev boundaryComparisonComplex (e : N ⟶ Sq.X₁) : CochainComplex (ModuleCat.{u} A) ℤ :=
  double (boundaryComparisonDiff e) upIntRelNegOneZero

/-- The inclusion of `Y`, placed in cohomological degree `0`, into the comparison complex. -/
public def boundaryComparisonInclusion (e : N ⟶ Sq.X₁) :
    (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj Sq.X₁ ⟶ boundaryComparisonComplex e :=
  mkHomFromSingle
    (biprod.inl ≫ (doubleXIso₁ (boundaryComparisonDiff e) upIntRelNegOneZero
      NaiveCotangent.TwoTerm.negOne_ne_zero).inv)
    (fun k _ => by
      rw [double_d_eq_zero₀ _ _ _ k (by omega), comp_zero])

/-- The projection of the comparison complex onto the two-term complex `(N --e ≫ ι--> X)`,
given by the second projection of the biproduct in degree `0`. -/
public def boundaryComparisonProjection (e : N ⟶ Sq.X₁) :
    boundaryComparisonComplex e ⟶ double (e ≫ Sq.f) upIntRelNegOneZero :=
  mkHomFromDouble upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero
    (doubleXIso₀ (e ≫ Sq.f) upIntRelNegOneZero).inv
    (biprod.snd ≫
      (doubleXIso₁ (e ≫ Sq.f) upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).inv)
    (by
      rw [double_d (e ≫ Sq.f) upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero]
      simp [boundaryComparisonDiff])
    (fun k _ => by
      rw [double_d_eq_zero₀ _ _ _ k (by omega), comp_zero])

/-- **The canonical morphism from a two-term complex to the quotient.** For a map `e : N ⟶ Y`
into the first term of a short exact sequence `0 → Y --ι--> X --p--> Z → 0`, the composite
`e ≫ ι` is killed by `p`, so `p` in degree `0` is a morphism of cochain complexes
`(N --e ≫ ι--> X) ⟶ Z[0]`. For the conormal sequence of a presentation this is the morphism
underlying `Deformation.Artin.naiveCotangentToDifferentials`. -/
public def twoTermToQuotient (e : N ⟶ Sq.X₁) :
    double (e ≫ Sq.f) upIntRelNegOneZero ⟶
      (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj Sq.X₃ :=
  mkHomToSingle
    ((doubleXIso₁ (e ≫ Sq.f) upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).hom ≫ Sq.g)
    (fun i _ => by
      by_cases hi : i = -1
      · subst hi
        rw [double_d (e ≫ Sq.f) upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero]
        simp [Sq.zero]
      · rw [double_d_eq_zero₀ _ _ i 0 hi, zero_comp])

/-- A morphism of cochain complexes `(N --e ≫ ι--> X) ⟶ Z[0]` is the canonical one as soon as
its degree-zero component is `p`. This identifies a morphism written down elsewhere, such as
the one underlying `Deformation.Artin.naiveCotangentToDifferentials`, with
`Deformation.Artin.twoTermToQuotient`. -/
public theorem eq_twoTermToQuotient {e : N ⟶ Sq.X₁}
    (φ : double (e ≫ Sq.f) upIntRelNegOneZero ⟶
      (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj Sq.X₃)
    (hφ : φ.f 0 =
      (doubleXIso₁ (e ≫ Sq.f) upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).hom ≫
        Sq.g ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Sq.X₃).inv) :
    φ = twoTermToQuotient e := by
  apply to_single_hom_ext
  simp [hφ, twoTermToQuotient]

/-- The short complex `Y[0] ⟶ (N ⟶ Y ⊞ X) ⟶ (N ⟶ X)` of cochain complexes. It is marked
reducible so that its terms are the complexes they are built from at the transparency the
rewriting tactics work at. -/
@[implicit_reducible] public def boundaryComparisonShortComplex (e : N ⟶ Sq.X₁) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  ShortComplex.mk (boundaryComparisonInclusion e) (boundaryComparisonProjection e) (by
    apply from_single_hom_ext
    simp [boundaryComparisonInclusion, boundaryComparisonProjection])

/-! ### The comparison sequence is degreewise split, hence short exact -/

/-- The splitting identity of a biproduct, read through isomorphisms of its two summands and
of the biproduct itself. This is the degree-zero compatibility of the splittings of the
comparison sequence. -/
public theorem biprod_conj_add_eq_id {X Y Z W V : ModuleCat.{u} A} (α : Z ≅ X ⊞ Y) (β : W ≅ X)
    (γ : V ≅ Y) :
    α.hom ≫ biprod.fst ≫ β.inv ≫ β.hom ≫ biprod.inl ≫ α.inv +
      α.hom ≫ biprod.snd ≫ γ.inv ≫ γ.hom ≫ biprod.inr ≫ α.inv = 𝟙 Z := by
  simp only [Iso.inv_hom_id_assoc]
  rw [← assoc biprod.fst, ← assoc biprod.snd, ← Preadditive.comp_add, ← Preadditive.add_comp,
    biprod.total, id_comp, α.hom_inv_id]

/-- In degree `0` the comparison sequence is the biproduct sequence `0 → Y → Y ⊕ X → X → 0`,
split by the first projection and the second inclusion. -/
public def boundaryComparisonSplitting₀ (e : N ⟶ Sq.X₁) :
    ((boundaryComparisonShortComplex e).map
      (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) 0)).Splitting where
  r :=
    (doubleXIso₁ (boundaryComparisonDiff e) upIntRelNegOneZero
      NaiveCotangent.TwoTerm.negOne_ne_zero).hom ≫
      biprod.fst ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Sq.X₁).inv
  s :=
    (doubleXIso₁ (e ≫ Sq.f) upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).hom ≫
      biprod.inr ≫
        (doubleXIso₁ (boundaryComparisonDiff e) upIntRelNegOneZero
          NaiveCotangent.TwoTerm.negOne_ne_zero).inv
  f_r := by simp [boundaryComparisonShortComplex, boundaryComparisonInclusion]
  s_g := by simp [boundaryComparisonShortComplex, boundaryComparisonProjection]
  id := by
    simp only [boundaryComparisonShortComplex, ShortComplex.map_f, ShortComplex.map_g,
      HomologicalComplex.eval_map, boundaryComparisonInclusion, boundaryComparisonProjection,
      mkHomFromSingle_f, mkHomFromDouble_f₁, assoc]
    exact biprod_conj_add_eq_id _ _ _

/-- In degree `-1` the comparison sequence is `0 → N → N`, its first term vanishing. -/
public def boundaryComparisonSplitting₁ (e : N ⟶ Sq.X₁) :
    ((boundaryComparisonShortComplex e).map
      (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1))).Splitting where
  r := 0
  s := (doubleXIso₀ (e ≫ Sq.f) upIntRelNegOneZero).hom ≫
    (doubleXIso₀ (boundaryComparisonDiff e) upIntRelNegOneZero).inv
  f_r := (isZero_single_obj_X (ComplexShape.up ℤ) 0 Sq.X₁ (-1)
    NaiveCotangent.TwoTerm.negOne_ne_zero).eq_of_src _ _
  s_g := by simp [boundaryComparisonShortComplex, boundaryComparisonProjection]
  id := by
    rw [zero_comp, zero_add]
    simp [boundaryComparisonShortComplex, boundaryComparisonProjection]

/-- Away from the degrees `-1` and `0` all three terms of the comparison sequence vanish. -/
public def boundaryComparisonSplitting₂ (e : N ⟶ Sq.X₁) (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ -1) :
    ((boundaryComparisonShortComplex e).map
      (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)).Splitting where
  r := 0
  s := 0
  f_r := (isZero_single_obj_X (ComplexShape.up ℤ) 0 Sq.X₁ n h₀).eq_of_src _ _
  s_g := (isZero_double_X (e ≫ Sq.f) upIntRelNegOneZero n h₁ h₀).eq_of_src _ _
  id := (isZero_double_X (boundaryComparisonDiff e) upIntRelNegOneZero n h₁ h₀).eq_of_src _ _

/-- The degreewise splittings of the comparison sequence. -/
public def boundaryComparisonSplitting (e : N ⟶ Sq.X₁) (n : ℤ) :
    ((boundaryComparisonShortComplex e).map
      (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)).Splitting :=
  if h₀ : n = 0 then h₀ ▸ boundaryComparisonSplitting₀ e
  else if h₁ : n = -1 then h₁ ▸ boundaryComparisonSplitting₁ e
  else boundaryComparisonSplitting₂ e n h₀ h₁

/-- The comparison sequence `0 → Y[0] → (N ⟶ Y ⊞ X) → (N ⟶ X) → 0` is short exact: it is
split in every degree. -/
public theorem shortExact_boundaryComparisonShortComplex (e : N ⟶ Sq.X₁) :
    (boundaryComparisonShortComplex e).ShortExact :=
  shortExact_of_degreewise_shortExact _ fun n => (boundaryComparisonSplitting e n).shortExact

/-! ### The two morphisms out of the comparison sequence -/

/-- The morphism `(N ⟶ Y ⊞ X) ⟶ X[0]` given by `ι ∘ fst + snd` in degree `0`. It is a
morphism of complexes because the differential of the comparison complex is `(-e, e ≫ ι)`. -/
public def boundaryComparisonMid (e : N ⟶ Sq.X₁) :
    boundaryComparisonComplex e ⟶ (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj Sq.X₂ :=
  mkHomFromDouble upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero 0
    ((biprod.fst ≫ Sq.f + biprod.snd) ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Sq.X₂).inv)
    (by simp [boundaryComparisonDiff])
    (fun k _ => by simp)

/-- **The comparison sequence maps to the short exact sequence of modules.** The morphism is
the identity on the first terms and the canonical morphism `(N ⟶ X) ⟶ Z[0]` on the third
ones, so the connecting morphism of the comparison sequence is the connecting morphism of
`0 → Y → X → Z → 0` evaluated on classes coming from the two-term complex. -/
public def boundaryComparisonHom (e : N ⟶ Sq.X₁) :
    boundaryComparisonShortComplex e ⟶
      Sq.map (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0) where
  τ₁ := 𝟙 _
  τ₂ := boundaryComparisonMid e
  τ₃ := twoTermToQuotient e
  comm₁₂ := by
    apply from_single_hom_ext
    simp [boundaryComparisonShortComplex, boundaryComparisonInclusion, boundaryComparisonMid,
      single_map_f_self]
  comm₂₃ := by
    apply from_double_hom_ext (hi₀₁ := upIntRelNegOneZero)
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) 0 Sq.X₃ (-1)
        NaiveCotangent.TwoTerm.negOne_ne_zero).eq_of_tgt _ _
    · have hz : Sq.f ≫ Sq.g ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Sq.X₃).inv = 0 := by
        rw [← assoc, Sq.zero, zero_comp]
      simp [boundaryComparisonShortComplex, boundaryComparisonProjection, boundaryComparisonMid,
        twoTermToQuotient, single_map_f_self, hz]

/-- The morphism `Deformation.Artin.boundaryComparisonHom` is the identity on the first terms. -/
@[simp] public theorem boundaryComparisonHom_τ₁ (e : N ⟶ Sq.X₁) :
    (boundaryComparisonHom e).τ₁ = 𝟙 _ :=
  rfl

/-- On the third terms, `Deformation.Artin.boundaryComparisonHom` is the canonical morphism
`(N ⟶ X) ⟶ Z[0]`. -/
@[simp] public theorem boundaryComparisonHom_τ₃ (e : N ⟶ Sq.X₁) :
    (boundaryComparisonHom e).τ₃ = twoTermToQuotient e :=
  rfl

/-- The morphism `(N ⟶ Y ⊞ X) ⟶ (N ⟶ Y)` given by the identity in degree `-1` and minus the
first projection of the biproduct in degree `0`. -/
public def boundaryComparisonFst (e : N ⟶ Sq.X₁) :
    boundaryComparisonComplex e ⟶ double e upIntRelNegOneZero :=
  mkHomFromDouble upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero
    (doubleXIso₀ e upIntRelNegOneZero).inv
    (-(biprod.fst ≫ (doubleXIso₁ e upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).inv))
    (by
      rw [double_d e upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero]
      simp [boundaryComparisonDiff])
    (fun k _ => by
      rw [double_d_eq_zero₀ _ _ _ k (by omega), comp_zero])

/-- **The comparison sequence maps to the sequence of the two-term complex `(N ⟶ Y)`.** The
morphism is minus the identity on the first terms and the projection `(N ⟶ X) ⟶ N[-1]` on
the third ones; the sign on the first terms is where the sign in the comparison of the two
connecting maps comes from. -/
public def boundaryComparisonTwoTermHom (e : N ⟶ Sq.X₁) :
    boundaryComparisonShortComplex e ⟶ twoTermShortComplex e where
  τ₁ := -𝟙 _
  τ₂ := boundaryComparisonFst e
  τ₃ := twoTermProjection (e ≫ Sq.f)
  comm₁₂ := by
    apply from_single_hom_ext
    simp [boundaryComparisonShortComplex, twoTermShortComplex, boundaryComparisonInclusion,
      boundaryComparisonFst, twoTermInclusion]
  comm₂₃ := by
    apply from_double_hom_ext (hi₀₁ := upIntRelNegOneZero)
    · simp [boundaryComparisonShortComplex, twoTermShortComplex, boundaryComparisonProjection,
        boundaryComparisonFst, twoTermProjection]
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) (-1) N 0 (by omega)).eq_of_tgt _ _

/-- The morphism `Deformation.Artin.boundaryComparisonTwoTermHom` is minus the identity on the
first terms. -/
@[simp] public theorem boundaryComparisonTwoTermHom_τ₁ (e : N ⟶ Sq.X₁) :
    (boundaryComparisonTwoTermHom e).τ₁ = -𝟙 ((boundaryComparisonShortComplex e).X₁) :=
  rfl

/-- On the third terms, `Deformation.Artin.boundaryComparisonTwoTermHom` is the projection
`(N ⟶ X) ⟶ N[-1]` of the triangle of the two-term complex. -/
@[simp] public theorem boundaryComparisonTwoTermHom_τ₃ (e : N ⟶ Sq.X₁) :
    (boundaryComparisonTwoTermHom e).τ₃ = twoTermProjection (e ≫ Sq.f) :=
  rfl

/-! ### The comparison in the derived category -/

/-- **The connecting morphism of a short exact sequence of modules and the connecting
morphism of the triangle of a two-term complex agree up to sign.** Let
`0 → Y --ι--> X --p--> Z → 0` be a short exact sequence of `A`-modules and `e : N ⟶ Y` a map
into its first term. The canonical morphism `(N --e ≫ ι--> X) ⟶ Z[0]` followed by the
connecting morphism `Z[0] ⟶ Y[0]⟦1⟧` of the sequence is minus the projection
`(N --e ≫ ι--> X) ⟶ N[-1]` of the triangle of that two-term complex followed by the
connecting morphism `N[-1] ⟶ Y[0]⟦1⟧` of the triangle of `(N --e--> Y)`.

Both sides are the connecting morphism of the comparison sequence, read through the two
morphisms of short exact sequences out of it; the sign comes from the morphism `-𝟙` on the
first terms of the second one. -/
public theorem Q_map_twoTermToQuotient_comp_singleδ (hSq : Sq.ShortExact) (e : N ⟶ Sq.X₁) :
    DerivedCategory.Q.map (twoTermToQuotient e) ≫ hSq.singleδ =
      -((twoTermTriangle (e ≫ Sq.f)).mor₂ ≫ (twoTermTriangle e).mor₃) := by
  have h₁ := (DerivedCategory.triangleOfSESδ_naturality
    (shortExact_boundaryComparisonShortComplex e)
    (hSq.map_of_exact (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0))
    (boundaryComparisonHom e)).symm
  have h₂ := (DerivedCategory.triangleOfSESδ_naturality
    (shortExact_boundaryComparisonShortComplex e) (shortExact_twoTermShortComplex e)
    (boundaryComparisonTwoTermHom e)).symm
  simp only [boundaryComparisonHom_τ₁, boundaryComparisonHom_τ₃, boundaryComparisonTwoTermHom_τ₁,
    boundaryComparisonTwoTermHom_τ₃, CategoryTheory.Functor.map_id, comp_id] at h₁ h₂
  erw [CategoryTheory.Functor.map_neg, CategoryTheory.Functor.map_neg,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, comp_neg, comp_id] at h₂
  exact h₁.trans (neg_eq_iff_eq_neg.mp h₂.symm)

/-! ### The comparison of the connecting maps on cohomology -/

/-- Composing with a morphism that is an identity. -/
public theorem comp_eq_of_eq_id {X Y : ModuleCat.{u} A} (f : X ⟶ Y) (g : Y ⟶ Y)
    (hg : g = 𝟙 Y) : f ≫ g = f := by
  rw [hg, comp_id]

/-- Composing with a morphism that is minus an identity. -/
public theorem comp_eq_neg_of_eq_neg_id {X Y : ModuleCat.{u} A} (f : X ⟶ Y) (g : Y ⟶ Y)
    (hg : g = -𝟙 Y) : f ≫ g = -f := by
  rw [hg, Preadditive.comp_neg, comp_id]

/-- The functor `H²(K ⊗ᴸ -)` on the derived category sends an identity to an identity. -/
public theorem shiftTwo_derivedTensor_Q_map_id (K : DerivedCategory (ModuleCat.{u} A))
    (X : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift (2 : ℤ)).map
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).map
          (DerivedCategory.Q.map (𝟙 X))) =
      𝟙 (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift (2 : ℤ)).obj
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj
          (DerivedCategory.Q.obj X))) := by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

/-- The functor `H²(K ⊗ᴸ -)` on the derived category sends minus an identity to minus an
identity. -/
public theorem shiftTwo_derivedTensor_Q_map_neg_id (K : DerivedCategory (ModuleCat.{u} A))
    (X : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift (2 : ℤ)).map
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).map
          (DerivedCategory.Q.map (-𝟙 X))) =
      -𝟙 (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift (2 : ℤ)).obj
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj
          (DerivedCategory.Q.obj X))) := by
  rw [CategoryTheory.Functor.map_neg, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_neg, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_neg, CategoryTheory.Functor.map_id]

/-- **The boundary map of a short exact sequence of modules, evaluated on classes coming from
a two-term complex, is minus the connecting map of the triangle of that complex.** For a
short exact sequence `0 → Y --ι--> X --p--> Z → 0` of `A`-modules and a map `e : N ⟶ Y`, the
composite

`H¹(K ⊗ᴸ (N --e ≫ ι--> X)) ⟶ H¹(K ⊗ᴸ Z) ⟶ H²(K ⊗ᴸ Y)`

of `H¹(K ⊗ᴸ -)` applied to the canonical morphism to `Z[0]` with the boundary map of the
sequence is minus the composite

`H¹(K ⊗ᴸ (N --e ≫ ι--> X)) ⟶ H¹(K ⊗ᴸ N[-1]) ⟶ H²(K ⊗ᴸ Y)`

of `H¹(K ⊗ᴸ -)` applied to the projection of the triangle of `(N --e ≫ ι--> X)` with the
connecting map of the tensored triangle of `(N --e--> Y)`. -/
public theorem derivedTensorCohomology_map_comp_boundaryMap
    (K : DerivedCategory (ModuleCat.{u} A)) (hSq : Sq.ShortExact) (e : N ⟶ Sq.X₁) :
    (derivedTensorCohomology A K 1).map
          (DerivedCategory.Q.map (twoTermToQuotient e)) ≫ boundaryMap A K hSq =
      -((derivedTensorCohomology A K 1).map (twoTermTriangle (e ≫ Sq.f)).mor₂ ≫
        DerivedCategory.HomologySequence.δ
          ((CochainComplex.DerivedTensor.derivedTensorProduct K).mapTriangle.obj
            (twoTermTriangle e)) 1 2 (by omega)) := by
  have hA := ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ_naturality
      ((CochainComplex.DerivedTensor.derivedTensorProduct K).mapTriangle.map
        (DerivedCategory.triangleOfSES.map (shortExact_boundaryComparisonShortComplex e)
          (hSq.map_of_exact (single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0))
          (boundaryComparisonHom e))) 1 2 (by omega)).trans
    (comp_eq_of_eq_id _ _
      (shiftTwo_derivedTensor_Q_map_id K (boundaryComparisonShortComplex e).X₁))
  have hB := ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ_naturality
      ((CochainComplex.DerivedTensor.derivedTensorProduct K).mapTriangle.map
        (DerivedCategory.triangleOfSES.map (shortExact_boundaryComparisonShortComplex e)
          (shortExact_twoTermShortComplex e) (boundaryComparisonTwoTermHom e))) 1 2
      (by omega)).trans
    (comp_eq_neg_of_eq_neg_id _ _
      (shiftTwo_derivedTensor_Q_map_neg_id K (boundaryComparisonShortComplex e).X₁))
  exact hA.trans (neg_eq_iff_eq_neg.mp hB.symm)

/-- **The boundary map of a short exact sequence of modules, evaluated on classes coming from
a two-term complex**, in the form `Deformation.Artin.derivedTensorTwoTermδ_eq` computes the
connecting map of a two-term complex: the connecting map of the triangle of `(N --e--> Y)` is
the degree shift `H¹(K ⊗ᴸ N[-1]) ≅ H²(K ⊗ᴸ N)` followed by `H²(K ⊗ᴸ e)`, with no further
sign. -/
public theorem derivedTensorCohomology_map_comp_boundaryMap'
    (K : DerivedCategory (ModuleCat.{u} A)) (hSq : Sq.ShortExact) (e : N ⟶ Sq.X₁) :
    (derivedTensorCohomology A K 1).map
          (DerivedCategory.Q.map (twoTermToQuotient e)) ≫ boundaryMap A K hSq =
      -((derivedTensorCohomology A K 1).map (twoTermTriangle (e ≫ Sq.f)).mor₂ ≫
        (shiftedCohomologyIso A K N).hom ≫ (derivedCohomology A K 2).map e) := by
  have hδ : DerivedCategory.HomologySequence.δ
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).mapTriangle.obj
          (twoTermTriangle e)) 1 2 (by omega) =
      (shiftedCohomologyIso A K N).hom ≫ (derivedCohomology A K 2).map e :=
    derivedTensorTwoTermδ_eq K ⟨↥N, ↥Sq.X₁, e.hom⟩
  rw [derivedTensorCohomology_map_comp_boundaryMap K hSq e, hδ]
  rfl

end Deformation.Artin

end
