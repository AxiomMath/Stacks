module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import StacksFrontier.CategoryTheory.Triangulated.Functor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical δ-functor from complexes to the derived category

This file collects the formalizations of [Stacks, Tag 0152], [Stacks, Tag 0154],
[Stacks, Tag 0153], [Stacks, Tag 08Q2].

## References

* [Stacks, Tag 0152](https://stacks.math.columbia.edu/tag/0152)
* [Stacks, Tag 0154](https://stacks.math.columbia.edu/tag/0154)
* [Stacks, Tag 0153](https://stacks.math.columbia.edu/tag/0153)
* [Stacks, Tag 08Q2](https://stacks.math.columbia.edu/tag/08Q2)
-/

section

/-!
# The canonical `δ`-functor `Comp(𝒜) ⥤ D(𝒜)`

Let `𝒜` be an abelian category. The localization functor
`Q : CochainComplex 𝒜 ℤ ⥤ DerivedCategory 𝒜` from complexes to the derived category carries the
structure of a `δ`-functor in the sense of
[StackProject 0150](https://stacks.math.columbia.edu/tag/0150): to a short exact sequence
`0 → A^• → B^• → C^• → 0` of complexes one attaches the connecting morphism
`δ = -p ∘ q⁻¹ : Q C^• ⟶ (Q A^•)⟦1⟧`, where `q : C(a)^• → C^•` is the quasi-isomorphism from the
cone of `a : A^• → B^•` (an isomorphism in `D(𝒜)`, whence invertible) and `p` is the projection of
that cone onto `A^•⟦1⟧`; the image `(Q A^•, Q B^•, Q C^•, Q a, Q b, δ)` of a short exact sequence
is then a distinguished triangle of `D(𝒜)`, and `δ` is natural in the short exact sequence. The
`δ`-functor is *the canonical one*: its connecting morphism is the named map
`DerivedCategory.triangleOfSESδ`.

If the short exact sequence is moreover split in each degree, with a chosen degreewise splitting
`σ` (a retraction `r` of `a` and a section `s` of `b` in each degree), then its image under `Q` is
computed by the splitting: the connecting morphism is the image of the morphism of complexes
`CochainComplex.homOfDegreewiseSplit S σ`, which in degree `n` is `s ≫ d_{B^•} ≫ r`, so that the
triangle of the `δ`-functor *is* the image of the termwise split triangle of the homotopy category
`K(𝒜)`.

## Main results

* `DerivedCategory.exists_deltaFunctorStructure_δ_eq`: the functor `Q` admits a `δ`-functor
  structure whose connecting morphism is `DerivedCategory.triangleOfSESδ`.
* `DerivedCategory.mapTriangle_triangleOfDegreewiseSplit_eq_triangleOfSES`: for a short exact
  sequence `S` of cochain complexes in an abelian category, together with a degreewise splitting
  `σ`, the image under `Q` of the triangle `CochainComplex.triangleOfDegreewiseSplit S σ` attached
  to the splitting is the triangle `DerivedCategory.triangleOfSES` of the canonical `δ`-functor.

## Implementation notes

A `δ`-functor structure is *data*, and the source pins the datum: `δ = -p ∘ q⁻¹`. The first
statement is therefore the existence of a `CategoryTheory.Functor.DeltaFunctorStructure` on `Q`
*together with* the equation identifying its `δ` with `DerivedCategory.triangleOfSESδ`, which is
`inv (Q.map q) ≫ Q.map (CochainComplex.mappingCone.triangle a).mor₃` followed by the commutation
isomorphism of `Q` with the shift; as `(mappingCone.triangle a).mor₃` is the shift of `-p`, this
is the source's `-p ∘ q⁻¹`, sign included. The two remaining fields of a `δ`-functor structure are
`Prop`-valued, so such a structure on `Q` is determined by its `δ`, and the equation determines
that.

The source adds that the same construction makes `Comp⁺(𝒜) ⥤ D⁺(𝒜)`, `Comp⁻(𝒜) ⥤ D⁻(𝒜)` and
`Comp^b(𝒜) ⥤ D^b(𝒜)` into `δ`-functors. These are restrictions of the one above along fully
faithful triangulated inclusions, which reflect distinguished triangles; they are proved in
`StacksFrontier.Algebra.Homology.DerivedCategory.BoundedDeltaFunctor`, whose
`DerivedCategory.exists_deltaFunctorStructure_δ_eq_and_plus_minus_bounded` states all four.

For a termwise split short exact sequence the source asks only for an *isomorphism* of triangles.
Here the two triangles have the same objects and the same first two morphisms by construction, so
they are equal as soon as their connecting morphisms are, and that equality is the whole content:
mere existence of an isomorphism is formal, since two distinguished triangles with the same first
morphism are already isomorphic by the axioms of a pretriangulated category, with no information
about the third object. The triangle of `K(𝒜)` of the source is
`CochainComplex.trianglehOfDegreewiseSplit S σ`, the image of
`CochainComplex.triangleOfDegreewiseSplit S σ` under `HomotopyCategory.quotient`; since
`HomotopyCategory.quotient ⋙ Qh ≅ Q` (`DerivedCategory.quotientCompQhIso`), taking `Q` rather
than `Qh` describes the same triangle of `D(𝒜)` while keeping the objects of the two triangles
equal instead of merely isomorphic, which is what allows the identification to be an equality.

## References

* [StackProject 0152](https://stacks.math.columbia.edu/tag/0152) (Lemma 13.12.1)
* [StackProject 0154](https://stacks.math.columbia.edu/tag/0154)
-/

universe w v u

open CategoryTheory Category Pretriangulated Preadditive CochainComplex.HomComplex

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)

/-- The cocycle relation satisfied by the pair `(s^n, -δ^n)` attached to a degreewise splitting
`σ` of a short complex `S` of cochain complexes: the identity
`d ∘ s^n - s^{n + 1} ∘ d = a ∘ δ^n` of [StackProject 011J], in the form that
`CochainComplex.mappingCone.lift` asks for. -/
private lemma δ_ofHoms_s_add_neg_cocycleOfDegreewiseSplit_comp_eq_zero :
    δ 0 1 (Cochain.ofHoms (fun p => (σ p).s)) +
      (-cocycleOfDegreewiseSplit S σ).1.comp (Cochain.ofHom S.f) (add_zero 1) = 0 := by
  ext p q hpq
  dsimp
  rw [δ_v 0 1 (by omega) _ p q hpq p q (by omega) (by omega)]
  have r_f : (σ q).r ≫ S.f.f q = 𝟙 _ - S.g.f q ≫ (σ q).s := (σ q).r_f
  have s_g : (σ p).s ≫ S.g.f p = 𝟙 (S.X₃.X p) := (σ p).s_g
  simp only [cocycleOfDegreewiseSplit, Cocycle.mk_coe, Cochain.neg_v,
    Cochain.mk_v, Cochain.comp_v _ _ (add_zero 1) p q q hpq (add_zero q),
    Cochain.ofHom_v, Cochain.ofHoms_v, Int.negOnePow_one, Units.neg_smul, one_smul,
    neg_comp, assoc, ← sub_eq_add_neg]
  rw [r_f, comp_sub, comp_sub, comp_id, ← assoc (S.X₂.d p q), ← S.g.comm p q, assoc,
    reassoc_of% s_g]
  simp

/-- The section `(s^n, -δ^n) : S.X₃ ⟶ mappingCone S.f` of
`CochainComplex.mappingCone.descShortComplex S` attached to a degreewise splitting `σ` of a short
complex `S` of cochain complexes, as in [StackProject 014L] (1). It satisfies two identities *of
complexes*, with no homotopy involved: composed with `descShortComplex S` it is the identity of
`S.X₃`, and composed with the third morphism of the triangle of the cone of `S.f` it is
`CochainComplex.homOfDegreewiseSplit S σ`. -/
private noncomputable def liftOfDegreewiseSplit : S.X₃ ⟶ mappingCone S.f :=
  lift S.f (-cocycleOfDegreewiseSplit S σ) (Cochain.ofHoms (fun p => (σ p).s))
    (δ_ofHoms_s_add_neg_cocycleOfDegreewiseSplit_comp_eq_zero S σ)

private lemma liftOfDegreewiseSplit_comp_descShortComplex :
    liftOfDegreewiseSplit S σ ≫ descShortComplex S = 𝟙 S.X₃ := by
  ext n
  have s_g : (σ n).s ≫ S.g.f n = 𝟙 (S.X₃.X n) := (σ n).s_g
  dsimp [liftOfDegreewiseSplit, descShortComplex]
  rw [lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl]
  simp [s_g]

private lemma liftOfDegreewiseSplit_comp_triangle_mor₃ :
    liftOfDegreewiseSplit S σ ≫ (triangle S.f).mor₃ = homOfDegreewiseSplit S σ := by
  ext n
  dsimp [liftOfDegreewiseSplit, triangle]
  simp [Cochain.rightShift_v _ 1 0 (zero_add 1) n n (add_zero n) (n + 1) rfl,
    homOfDegreewiseSplit_f]

end CochainComplex.mappingCone

namespace DerivedCategory

/-- **The canonical `δ`-functor.** Let `𝒜` be an abelian category. The localization functor
`Q : CochainComplex 𝒜 ℤ ⥤ DerivedCategory 𝒜` has the structure of a `δ`-functor whose connecting
morphism is `DerivedCategory.triangleOfSESδ = -p ∘ q⁻¹`: for every short exact sequence
`0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` of complexes the triangle
`(Q A^•, Q B^•, Q C^•, Q a, Q b, triangleOfSESδ)` is distinguished, and `triangleOfSESδ` is
natural in the short exact sequence. -/
@[stacks 0152 "the functor Comp(𝒜) ⥤ D(𝒜)", sga "4½ Etat_0 3.1.5" "partial"]
public theorem exists_deltaFunctorStructure_δ_eq
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    ∃ h : Functor.DeltaFunctorStructure (CochainComplex C ℤ) (DerivedCategory C) Q,
      ∀ {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact),
        h.δ hS = triangleOfSESδ hS :=
  ⟨{ δ := triangleOfSESδ
     distinguished := triangleOfSES_distinguished
     δ_naturality := triangleOfSESδ_naturality }, fun _ => rfl⟩

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)

open CochainComplex.mappingCone in
/-- The connecting morphism of the canonical `δ`-functor attached to a termwise split short exact
sequence `S` of cochain complexes is the image of `CochainComplex.homOfDegreewiseSplit S σ`. -/
private lemma triangleOfSESδ_eq (hS : S.ShortExact) :
    Q.map (CochainComplex.homOfDegreewiseSplit S σ) ≫ (Q.commShiftIso (1 : ℤ)).hom.app S.X₁ =
      triangleOfSESδ hS := by
  calc Q.map (CochainComplex.homOfDegreewiseSplit S σ) ≫ (Q.commShiftIso (1 : ℤ)).hom.app S.X₁
      = (Q.map (liftOfDegreewiseSplit S σ) ≫ Q.map (triangle S.f).mor₃) ≫
          (Q.commShiftIso (1 : ℤ)).hom.app S.X₁ :=
        congrArg (· ≫ (Q.commShiftIso (1 : ℤ)).hom.app S.X₁) ((Q.map_comp _ _).symm.trans
          (congrArg Q.map (liftOfDegreewiseSplit_comp_triangle_mor₃ S σ))).symm
    _ = Q.map (liftOfDegreewiseSplit S σ) ≫ Q.map (descShortComplex S) ≫ triangleOfSESδ hS :=
        (assoc _ _ _).trans (congrArg (Q.map (liftOfDegreewiseSplit S σ) ≫ ·)
          (descShortComplex_triangleOfSESδ hS).symm)
    _ = triangleOfSESδ hS := by
        rw [← assoc, ← Q.map_comp, liftOfDegreewiseSplit_comp_descShortComplex, Q.map_id, id_comp]

/-- **The `δ`-functor on a termwise split short exact sequence.** Let `𝒜` be an abelian category
and let `S` be a short exact sequence of cochain complexes in `𝒜` which is split in each degree,
with splitting `σ`. Then the image under `Q : Comp(𝒜) ⥤ D(𝒜)` of the distinguished triangle
`(S.X₁, S.X₂, S.X₃, S.f, S.g, CochainComplex.homOfDegreewiseSplit S σ)` attached to the splitting
is the distinguished triangle that the canonical `δ`-functor attaches to `S`; in particular the
connecting morphism `triangleOfSESδ hS` is the image of
`CochainComplex.homOfDegreewiseSplit S σ`. -/
@[stacks 0154]
public theorem mapTriangle_triangleOfDegreewiseSplit_eq_triangleOfSES
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
    Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit S σ) = triangleOfSES hS := by
  dsimp [triangleOfSES, Functor.mapTriangle, CochainComplex.triangleOfDegreewiseSplit]
  exact congrArg (Triangle.mk (Q.map S.f) (Q.map S.g)) (triangleOfSESδ_eq S σ hS)

end DerivedCategory

end

section

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
# Quasi-isomorphic short exact sequences have isomorphic triangles

Let `𝒜` be an abelian category and let `D(𝒜)` denote its derived category, with
localization functor `Q : CochainComplex(𝒜, ℤ) ⥤ D(𝒜)` sending quasi-isomorphisms
to isomorphisms. To every short exact sequence `S` of cochain complexes one associates
a distinguished triangle `tri(S)` in `D(𝒜)` via the δ-functor construction
(Stacks 0152/014Z; `DerivedCategory.triangleOfSES`).

Given two short exact sequences `S₁ : A → B → C` and `S₂ : D → E → F` of cochain
complexes and a morphism of short complexes `Φ = (φ₁, φ₂, φ₃) : S₁ → S₂` such that all
three vertical arrows `φ₁, φ₂, φ₃` are quasi-isomorphisms, the two distinguished
triangles `tri(S₁)` and `tri(S₂)` in `D(𝒜)` are isomorphic. The isomorphism is
realized by the triple `(Q φ₁, Q φ₂, Q φ₃)`.
-/

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- The morphism of triangles `tri(S₁) ⟶ tri(S₂)` in `D(𝒜)` induced by a morphism
`f : S₁ ⟶ S₂` of short exact sequences of cochain complexes. Its three components are
`Q f.τ₁, Q f.τ₂, Q f.τ₃`. This realizes the functoriality of the δ-functor triangle
construction (Stacks 0152). -/
@[sga "4½ Etat_0 3.1.5" "Morphism part of Π"]
noncomputable def triangleMorphismOfSESHom
    {S₁ S₂ : ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    DerivedCategory.triangleOfSES hS₁ ⟶ DerivedCategory.triangleOfSES hS₂ :=
  Triangle.homMk _ _
    (DerivedCategory.Q.map f.τ₁) (DerivedCategory.Q.map f.τ₂) (DerivedCategory.Q.map f.τ₃)
    (by
      change DerivedCategory.Q.map S₁.f ≫ DerivedCategory.Q.map f.τ₂
        = DerivedCategory.Q.map f.τ₁ ≫ DerivedCategory.Q.map S₂.f
      rw [← Functor.map_comp, ← Functor.map_comp, f.comm₁₂])
    (by
      change DerivedCategory.Q.map S₁.g ≫ DerivedCategory.Q.map f.τ₃
        = DerivedCategory.Q.map f.τ₂ ≫ DerivedCategory.Q.map S₂.g
      rw [← Functor.map_comp, ← Functor.map_comp, f.comm₂₃])
    (DerivedCategory.triangleOfSESδ_naturality hS₁ hS₂ f)

/-- The triple `(Q φ₁, Q φ₂, Q φ₃)` is an isomorphism of triangles
`tri(S₁) ⟶ tri(S₂)`, when each `φᵢ` is a quasi-isomorphism: each `Q φᵢ` is then an
isomorphism (`DerivedCategory.isIso_Q_map_iff_quasiIso`), and a morphism of triangles whose
three components are isomorphisms is one (`Triangle.isIso_of_isIsos`). -/
theorem isIso_triangleMorphismOfSESHom
    {S₁ S₂ : ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)
    (h₁ : QuasiIso f.τ₁) (h₂ : QuasiIso f.τ₂) (h₃ : QuasiIso f.τ₃) :
    IsIso (triangleMorphismOfSESHom hS₁ hS₂ f) :=
  Triangle.isIso_of_isIsos _ ((DerivedCategory.isIso_Q_map_iff_quasiIso _ f.τ₁).2 h₁)
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ f.τ₂).2 h₂)
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ f.τ₃).2 h₃)

/-- The two distinguished triangles associated to `S₁` and `S₂` are isomorphic in
`D(𝒜)`, via the canonical isomorphism with components `Q φ₁, Q φ₂, Q φ₃`. -/
@[stacks 0153]
noncomputable def triangleOfSESIsoOfQuasiIsoHom
    {S₁ S₂ : ShortComplex (CochainComplex 𝒜 ℤ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)
    (h₁ : QuasiIso f.τ₁) (h₂ : QuasiIso f.τ₂) (h₃ : QuasiIso f.τ₃) :
    DerivedCategory.triangleOfSES hS₁ ≅ DerivedCategory.triangleOfSES hS₂ :=
  have : IsIso (triangleMorphismOfSESHom hS₁ hS₂ f) :=
    isIso_triangleMorphismOfSESHom hS₁ hS₂ f h₁ h₂ h₃
  asIso (triangleMorphismOfSESHom hS₁ hS₂ f)

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The trick of vanishing compositions

Let `A` be an abelian category and `n ≥ 0` an integer; write `D(A)` for its derived category
and `H^i(K)` for the `i`-th cohomology object of a cochain complex `K`. The canonical
truncations `τ_{≤ a} K` and `τ_{≥ a} K` are `CochainComplex.truncLE` and
`CochainComplex.truncGE`, with structure maps `CochainComplex.ιTruncLE` and
`CochainComplex.πTruncGE`.

1. (Covariant case.) Given composable morphisms of cochain complexes
   `K 0 → K 1 → ... → K n` (with `f j : K j → K (j+1)`) such that
   (1) `H^i(K 0) = 0` for all `i > 0`, and
   (2) for each `0 ≤ j ≤ n-1`, the induced map `H^{-j}(f j) = 0`,
   the composition `K 0 → K n`, viewed in `D(A)`, factors through the canonical map
   `ι : τ_{≤ -n} (K n) → K n`.
2. (Contravariant case.) Given composable morphisms of cochain complexes
   `K n → K (n-1) → ... → K 0` (with `g j : K (j+1) → K j`) such that
   (1) `H^i(K 0) = 0` for all `i < 0`, and
   (2) for each `0 ≤ j ≤ n-1`, the induced map `H^{j}(g j) = 0`,
   the composition `K n → K 0`, viewed in `D(A)`, factors through the canonical map
   `π : K n → τ_{≥ n} (K n)`.

The chain `K 0 → ... → K n` consists of `n` composable morphisms. For `n = 0` it is the single
complex `K 0`, the composition is the identity, and the conclusion reduces to
`τ_{≤ 0} (K 0) → K 0` being an isomorphism in `D(A)` under (1). As `n` increases, the upper
truncation bound `-n` of the first statement moves down. The second statement is the dual of
the first (passing to the opposite category swaps `τ_{≤}` with `τ_{≥}`, reverses morphisms and
negates cohomological degrees); here it is proved by the dual induction.
-/

open CategoryTheory

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

/-! ### The covariant case

The covariant statement is proved by induction on `n`, from a base case (`covariant_base`: the
truncation map `ιTruncLE 0` is an isomorphism in `D(A)` under hypothesis (1)) and an inductive
step (`covariant_step`: a factorization through `τ_{≤-n}` propagates, after composing with a map
whose `H^{-n}` vanishes, to a factorization through `τ_{≤-(n+1)}`). -/

/-- **Base case (covariant).** If `H^i(K_0) = 0` for all `i > 0`, then the
canonical map `ι : τ_{≤0}(K_0) ⟶ K_0` is an isomorphism in `D(A)`.

The map `ιTruncLE 0` is a quasi-isomorphism exactly when `K_0` is cohomologically
concentrated in degrees `≤ 0` (`CochainComplex.quasiIso_ιTruncLE_iff`), which is hypothesis
`h1`, and `Q` turns quasi-isomorphisms into isomorphisms
(`DerivedCategory.isIso_Q_map_iff_quasiIso`). -/
@[sga "4 XVII 7.3.1" "special case"]
theorem covariant_base
    (K0 : CochainComplex A ℤ)
    (h1 : ∀ i : ℤ, 0 < i → Limits.IsZero (K0.homology i)) :
    IsIso (DerivedCategory.Q.map (K0.ιTruncLE 0)) := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso, K0.quasiIso_ιTruncLE_iff, K0.isLE_iff]
  exact fun i hi => (K0.exactAt_iff_isZero_homology i).2 (h1 i hi)

section CovariantStepHelpers

open CategoryTheory.Triangulated Limits Pretriangulated

/-- **Heart detection.** If `X` and `Y` both lie in the heart of the canonical
t-structure at degree `n` (i.e. are `IsLE n` and `IsGE n`), then a morphism
`f : X ⟶ Y` in `D(A)` that vanishes on `H^n` is itself zero.  Proof: both objects
are isomorphic to `(single n)`-objects, and `single n` is fully faithful with
`single n ⋙ H^n ≅ 𝟭`. -/
theorem heart_hom_eq_zero (X Y : DerivedCategory A) (n : ℤ)
    [X.IsLE n] [X.IsGE n] [Y.IsLE n] [Y.IsGE n]
    (f : X ⟶ Y) (hf : (DerivedCategory.homologyFunctor A n).map f = 0) : f = 0 := by
  obtain ⟨x, ⟨ex⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  obtain ⟨y, ⟨ey⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n
  rw [show f = ex.hom ≫ (ex.inv ≫ f ≫ ey.hom) ≫ ey.inv by simp]
  obtain ⟨φ₀, hφ₀⟩ := (DerivedCategory.singleFunctor A n).map_surjective (ex.inv ≫ f ≫ ey.hom)
  have hH : (DerivedCategory.homologyFunctor A n).map ((DerivedCategory.singleFunctor A n).map
      φ₀) = 0 := by
    simp [hφ₀, hf]
  have key : φ₀ = 0 := by
    have iso := DerivedCategory.singleFunctorCompHomologyFunctorIso A n
    have hnat := iso.hom.naturality φ₀
    simp only [Functor.comp_map, Functor.id_map, hH] at hnat
    have h0 : iso.hom.app x ≫ φ₀ = 0 := by simpa using hnat.symm
    exact (cancel_epi (iso.hom.app x)).mp (by simpa using h0)
  rw [← hφ₀, key]
  simp

/-- In a distinguished triangle, `H^n(mor₂)` is an isomorphism provided `H^n` and
`H^{n+1}` of the first object vanish (homology long exact sequence). -/
theorem isIso_homology_mor₂ (T : Pretriangulated.Triangle (DerivedCategory A))
    (hT : T ∈ distinguishedTriangles) (n : ℤ)
    (h1 : IsZero ((DerivedCategory.homologyFunctor A n).obj T.obj₁))
    (h3 : IsZero ((DerivedCategory.homologyFunctor A (n + 1)).obj T.obj₁)) :
    IsIso ((DerivedCategory.homologyFunctor A n).map T.mor₂) := by
  rw [← DerivedCategory.shift_homologyFunctor A n] at h1 ⊢
  rw [← DerivedCategory.shift_homologyFunctor A (n+1)] at h3
  have e2 := (DerivedCategory.homologyFunctor A 0).homologySequence_exact₂ T hT n
  have e3 := (DerivedCategory.homologyFunctor A 0).homologySequence_exact₃ T hT n (n+1) rfl
  have hmono : Mono (((DerivedCategory.homologyFunctor A 0).shift n).map T.mor₂) :=
    e2.mono_g (IsZero.eq_zero_of_src h1 _)
  have hepi : Epi (((DerivedCategory.homologyFunctor A 0).shift n).map T.mor₂) :=
    e3.epi_f (IsZero.eq_zero_of_tgt h3 _)
  exact isIso_of_mono_of_epi _

/-- In a distinguished triangle, `H^n(mor₁)` is an isomorphism provided `H^n` and
`H^{n-1}` of the third object vanish. -/
theorem isIso_homology_mor₁ (T : Pretriangulated.Triangle (DerivedCategory A))
    (hT : T ∈ distinguishedTriangles) (n : ℤ)
    (h2 : IsZero ((DerivedCategory.homologyFunctor A n).obj T.obj₃))
    (h0 : IsZero ((DerivedCategory.homologyFunctor A (n - 1)).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor A n).map T.mor₁) := by
  rw [← DerivedCategory.shift_homologyFunctor A n] at h2 ⊢
  rw [← DerivedCategory.shift_homologyFunctor A (n-1)] at h0
  have e2 := (DerivedCategory.homologyFunctor A 0).homologySequence_exact₂ T hT n
  have e1 := (DerivedCategory.homologyFunctor A 0).homologySequence_exact₁ T hT (n-1) n (by omega)
  have hepi : Epi (((DerivedCategory.homologyFunctor A 0).shift n).map T.mor₁) :=
    e2.epi_f (IsZero.eq_zero_of_tgt h2 _)
  have hmono : Mono (((DerivedCategory.homologyFunctor A 0).shift n).map T.mor₁) :=
    e1.mono_g (IsZero.eq_zero_of_src h0 _)
  exact isIso_of_mono_of_epi _

/-- **General single-degree detection.** A morphism `f : X ⟶ Y` in `D(A)` with
`X` in `D^{≤n}` (`IsLE n`) and `Y` in `D^{≥n}` (`IsGE n`) that vanishes on `H^n`
is zero.  We truncate `X` and `Y` at `n` to reduce to the heart, where
`heart_hom_eq_zero` applies; the truncation maps are isomorphisms on `H^n`. -/
theorem hom_eq_zero_of_isLE_isGE (X Y : DerivedCategory A) (n : ℤ)
    [X.IsLE n] [Y.IsGE n] (f : X ⟶ Y)
    (hf : (DerivedCategory.homologyFunctor A n).map f = 0) : f = 0 := by
  have hTx := DerivedCategory.TStructure.t.triangleLEGE_distinguished (n-1) n (by omega) X
  have hTy := DerivedCategory.TStructure.t.triangleLEGE_distinguished n (n+1) (by omega) Y
  have i1 : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.TStructure.t.triangleLEGE (n-1) n
      (by omega)).obj X).obj₁ (n-1) :=
    inferInstanceAs (DerivedCategory.TStructure.t.IsLE ((DerivedCategory.TStructure.t.truncLE
        (n-1)).obj X) (n-1))
  have i3le : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.TStructure.t.triangleLEGE (n-1)
      n (by omega)).obj X).obj₃ n :=
    inferInstanceAs (DerivedCategory.TStructure.t.IsLE ((DerivedCategory.TStructure.t.truncGE
        n).obj X) n)
  have i3ge : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.TStructure.t.triangleLEGE (n-1)
      n (by omega)).obj X).obj₃ n :=
    inferInstanceAs (DerivedCategory.TStructure.t.IsGE ((DerivedCategory.TStructure.t.truncGE
        n).obj X) n)
  have j1le : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.TStructure.t.triangleLEGE n
      (n+1) (by omega)).obj Y).obj₁ n :=
    inferInstanceAs (DerivedCategory.TStructure.t.IsLE ((DerivedCategory.TStructure.t.truncLE
        n).obj Y) n)
  have j1ge : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.TStructure.t.triangleLEGE n
      (n+1) (by omega)).obj Y).obj₁ n :=
    inferInstanceAs (DerivedCategory.TStructure.t.IsGE ((DerivedCategory.TStructure.t.truncLE
        n).obj Y) n)
  have j3ge : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.TStructure.t.triangleLEGE n
      (n+1) (by omega)).obj Y).obj₃ (n+1) :=
    inferInstanceAs (DerivedCategory.TStructure.t.IsGE ((DerivedCategory.TStructure.t.truncGE
        (n+1)).obj Y) (n+1))
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.yoneda_exact₂ _ hTx f
    (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (n-1) n (by omega) i1 ‹_›)
  obtain ⟨g', hg'⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ hTy g
    (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ n (n+1) (by omega) i3le j3ge)
  have isoTx : IsIso ((DerivedCategory.homologyFunctor A n).map
      ((DerivedCategory.TStructure.t.triangleLEGE (n-1) n (by omega)).obj X).mor₂) :=
    isIso_homology_mor₂ _ hTx n (DerivedCategory.isZero_of_isLE _ (n-1) n (by omega))
      (DerivedCategory.isZero_of_isLE _ (n-1) (n+1) (by omega))
  have isoTy : IsIso ((DerivedCategory.homologyFunctor A n).map
      ((DerivedCategory.TStructure.t.triangleLEGE n (n+1) (by omega)).obj Y).mor₁) :=
    isIso_homology_mor₁ _ hTy n (DerivedCategory.isZero_of_isGE _ (n+1) n (by omega))
      (DerivedCategory.isZero_of_isGE _ (n+1) (n-1) (by omega))
  have hHg' : (DerivedCategory.homologyFunctor A n).map g' = 0 := by
    rw [hg, hg'] at hf
    simp only [Functor.map_comp] at hf
    rw [← cancel_epi ((DerivedCategory.homologyFunctor A n).map
        ((DerivedCategory.TStructure.t.triangleLEGE (n-1) n (by omega)).obj X).mor₂), comp_zero,
      ← cancel_mono ((DerivedCategory.homologyFunctor A n).map
        ((DerivedCategory.TStructure.t.triangleLEGE n (n+1) (by omega)).obj Y).mor₁), zero_comp]
    simpa [Category.assoc] using hf
  simp [hg, hg', heart_hom_eq_zero _ _ n g' hHg']

/-- `H^i(Q f)` is an isomorphism when `f` is a quasi-isomorphism at `i`. -/
private theorem isIso_H_Q_map_of_quasiIsoAt {K L : CochainComplex A ℤ} (f : K ⟶ L) (i : ℤ)
    (hq : QuasiIsoAt f i) :
    IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map f)) := by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hq
  have hnat := DerivedCategory.homologyFunctorFactors_hom_naturality f i
  have : IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map f) ≫
      (DerivedCategory.homologyFunctorFactors A i).hom.app L) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctorFactors A i).hom.app L)

/-- `H^i(Q(ιTruncLE a))` is an isomorphism for `i ≤ a` (the truncation map is a
quasi-isomorphism there). -/
@[sga "4 XVII 1.1.14"]
theorem isIso_H_Q_ιTruncLE (K : CochainComplex A ℤ) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map (K.ιTruncLE a))) := by
  exact isIso_H_Q_map_of_quasiIsoAt _ i (CochainComplex.quasiIsoAt_ιTruncLE K a i hi)

/-- The third object `X₃` of the truncation short exact sequence at bound `a`
(the cofiber of `ιTruncLE a`) lies in `D^{≥a+1}`. -/
theorem Q_truncLE_cofiber_isGE (Kn1 : CochainComplex A ℤ) (a : ℤ)
    (hS : (CochainComplex.shortComplexTruncLE Kn1 a).ShortExact) :
    (DerivedCategory.Q.obj (CochainComplex.shortComplexTruncLE Kn1 a).X₃).IsGE (a+1) := by
  set T := DerivedCategory.triangleOfSES hS
  have hT := DerivedCategory.triangleOfSES_distinguished hS
  have hobj3 : T.obj₃ = DerivedCategory.Q.obj (CochainComplex.shortComplexTruncLE Kn1 a).X₃ := rfl
  have hmor1 : T.mor₁ = DerivedCategory.Q.map (Kn1.ιTruncLE a) := rfl
  rw [← hobj3, DerivedCategory.isGE_iff]
  intro i hi
  have hia : i ≤ a := by omega
  have hiso1 : IsIso ((DerivedCategory.homologyFunctor A i).map T.mor₁) := by
    rw [hmor1]
    exact isIso_H_Q_ιTruncLE Kn1 a i hia
  have e2 := (DerivedCategory.homologyFunctor A 0).homologySequence_exact₂ T hT i
  have e3 := (DerivedCategory.homologyFunctor A 0).homologySequence_exact₃ T hT i (i+1) rfl
  have e1 := (DerivedCategory.homologyFunctor A 0).homologySequence_exact₁ T hT i (i+1) rfl
  have hg0 : ((DerivedCategory.homologyFunctor A 0).shift i).map T.mor₂ = 0 := by
    have : Epi (((DerivedCategory.homologyFunctor A 0).shift i).map T.mor₁) := by
      rw [DerivedCategory.shift_homologyFunctor]
      infer_instance
    exact (e2.epi_f_iff).mp ‹_›
  have hmono1 : Mono (((DerivedCategory.homologyFunctor A 0).shift (i+1)).map T.mor₁) := by
    rw [DerivedCategory.shift_homologyFunctor]
    rcases lt_or_eq_of_le hia with hlt | heq
    · have : IsIso ((DerivedCategory.homologyFunctor A (i+1)).map T.mor₁) := by
        rw [hmor1]
        exact isIso_H_Q_ιTruncLE Kn1 a (i+1) (by omega)
      infer_instance
    · have hz : IsZero ((DerivedCategory.homologyFunctor A (i+1)).obj T.obj₁) := by
        rw [show T.obj₁ = DerivedCategory.Q.obj (Kn1.truncLE a) from rfl]
        exact DerivedCategory.isZero_of_isLE _ a (i+1) (by omega)
      exact ⟨fun _ _ _ => hz.eq_of_tgt _ _⟩
  have hmono_δ : Mono ((DerivedCategory.homologyFunctor A 0).homologySequenceδ T i (i+1) rfl) :=
    e3.mono_g hg0
  rw [← DerivedCategory.shift_homologyFunctor A i]
  exact IsZero.of_mono_eq_zero _ (e1.mono_g_iff.mp hmono1)

/-- `H^n(Q(fn)) = 0` whenever the complex-level homology map `H^n(fn)` vanishes. -/
theorem homologyFunctor_Q_map_eq_zero (Kn Kn1 : CochainComplex A ℤ) (fn : Kn ⟶ Kn1) (n : ℤ)
    (hf : HomologicalComplex.homologyMap fn n = 0) :
    (DerivedCategory.homologyFunctor A n).map (DerivedCategory.Q.map fn) = 0 := by
  have hnat := DerivedCategory.homologyFunctorFactors_hom_naturality fn n
  rw [hf, comp_zero] at hnat
  rwa [← cancel_mono ((DerivedCategory.homologyFunctorFactors A n).hom.app Kn1), zero_comp]

/-- `H^i(Q(πTruncGE a))` is an isomorphism for `a ≤ i` (the truncation map is a
quasi-isomorphism there). -/
@[sga "4 XVII 1.1.14"]
theorem isIso_H_Q_πTruncGE (K : CochainComplex A ℤ) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map (K.πTruncGE a))) := by
  exact isIso_H_Q_map_of_quasiIsoAt _ i (CochainComplex.quasiIsoAt_πTruncGE K a i hi)

/-- If `H^i(Q(f))` is an isomorphism in `D(A)`, then so is the complex-level
homology map `H^i(f)`. -/
theorem homologyMap_iso_of_Q (K L : CochainComplex A ℤ) (f : K ⟶ L) (i : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map f))) :
    IsIso (HomologicalComplex.homologyMap f i) := by
  have hnat := DerivedCategory.homologyFunctorFactors_hom_naturality f i
  have : IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map f) ≫
      (DerivedCategory.homologyFunctorFactors A i).hom.app L) := inferInstance
  rw [hnat] at this
  exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctorFactors A i).hom.app K) _

end CovariantStepHelpers

/-- **Inductive step (covariant).** Suppose a derived-category morphism
`φ : Q(X0) ⟶ Q(K_n)` factors through `Q(ιTruncLE (-n))` (i.e. through
`τ_{≤-n}(K_n)`), and `fn : K_n ⟶ K_{n+1}` induces the zero map on `H^{-n}`.
Then `φ ≫ Q(fn)` factors through `Q(ιTruncLE (-(n+1)))` (i.e. through
`τ_{≤-(n+1)}(K_{n+1})`).

Apply the truncation distinguished
triangle for `K_{n+1}` at the bound `a = -(n+1)`:
  `τ_{≤-(n+1)}(K_{n+1}) → K_{n+1} → τ_{≥-n}(K_{n+1}) → [1]`
(this is `DerivedCategory.triangleOfSES_distinguished` applied to
`CochainComplex.shortComplexTruncLE_shortExact (K_{n+1}) (-(n+1))`; note the third
object is `truncGE ((-(n+1))+1) = truncGE (-n)` with second map `πTruncGE (-n)`).
By homological coyoneda exactness of this distinguished triangle
(`Pretriangulated.Triangle.coyoneda_exact₂`, Stacks 0149), the morphism
`φ ≫ Q(fn)` factors through `Q(ιTruncLE (-(n+1)))` **iff** its composite with the
third map vanishes:
  `(φ ≫ Q(fn)) ≫ Q(πTruncGE (-n)) = 0`   in `D(A)`.
Now use the hypothesis `hφ`, writing `φ = h₀ ≫ Q(ιTruncLE (-n))`.  Then the
left-hand side equals `h₀ ≫ Q(α)` where
  `α := ιTruncLE (-n) ≫ fn ≫ πTruncGE (-n) : τ_{≤-n}(K_n) ⟶ τ_{≥-n}(K_{n+1})`.
The source `τ_{≤-n}(K_n)` lies in `D^{≤-n}` (`IsLE (-n)`) and the target
`τ_{≥-n}(K_{n+1})` lies in `D^{≥-n}` (`IsGE (-n)`); they overlap in the single
degree `-n`.  By the t-structure on `D(A)`, the group `Hom_{D}(X, Y)` for
`X` in `D^{≤-n}` and `Y` in `D^{≥-n}` is identified (via the unit
`X → H^{-n}(X)[n]` and counit `H^{-n}(Y)[n] → Y`) with `Hom_A(H^{-n}X, H^{-n}Y)`;
under this identification `Q(α)` corresponds to the map induced on `H^{-n}`,
which factors through `H^{-n}(fn)`.  Since `H^{-n}(fn) = 0` (hypothesis `hf`),
we get `Q(α) = 0`, hence `(φ ≫ Q(fn)) ≫ Q(πTruncGE (-n)) = h₀ ≫ 0 = 0`, and the
coyoneda exactness yields the desired factorization.

REMARK.  The single-degree-overlap vanishing cannot use the strict-gap lemma
`Triangulated.TStructure.zero_of_isLE_of_isGE` (which needs `n₀ < n₁`).  Instead
one needs the heart-Hom identification for `IsLE a` / `IsGE a` objects at the
SAME degree `a`, combined with `hf`.  Concretely, route through the homology
functor: `Q(α)` is detected by `H^{-n}`, and `H^{-n}(α) = H^{-n}(ιTruncLE(-n)) ≫
H^{-n}(fn) ≫ H^{-n}(πTruncGE(-n))` which contains the factor `H^{-n}(fn) = 0`. -/
theorem covariant_step
    (n : ℕ) (Kn Kn1 : CochainComplex A ℤ) (fn : Kn ⟶ Kn1)
    (hf : HomologicalComplex.homologyMap fn (-(n : ℤ)) = 0)
    (X0 : CochainComplex A ℤ)
    (φ : DerivedCategory.Q.obj X0 ⟶ DerivedCategory.Q.obj Kn)
    (hφ : ∃ h : DerivedCategory.Q.obj X0 ⟶ DerivedCategory.Q.obj (Kn.truncLE (-(n : ℤ))),
        φ = h ≫ DerivedCategory.Q.map (Kn.ιTruncLE (-(n : ℤ)))) :
    ∃ h : DerivedCategory.Q.obj X0 ⟶ DerivedCategory.Q.obj (Kn1.truncLE (-((n:ℤ)+1))),
      φ ≫ DerivedCategory.Q.map fn =
        h ≫ DerivedCategory.Q.map (Kn1.ιTruncLE (-((n:ℤ)+1))) := by
  have hS := CochainComplex.shortComplexTruncLE_shortExact Kn1 (-((n:ℤ)+1))
  have hT := DerivedCategory.triangleOfSES_distinguished hS
  have hmor1 : (DerivedCategory.triangleOfSES hS).mor₁
      = DerivedCategory.Q.map (Kn1.ιTruncLE (-((n:ℤ)+1))) := rfl
  rw [← hmor1]
  apply Pretriangulated.Triangle.coyoneda_exact₂ _ hT
  obtain ⟨h₀, rfl⟩ := hφ
  set g := (CochainComplex.shortComplexTruncLE Kn1 (-((n:ℤ)+1))).g
  have hmor2 : (DerivedCategory.triangleOfSES hS).mor₂ = DerivedCategory.Q.map g := rfl
  rw [hmor2, Category.assoc, Category.assoc, ← DerivedCategory.Q.map_comp,
    ← DerivedCategory.Q.map_comp]
  -- Goal: `h₀ ≫ Q(ιTruncLE(-n) ≫ fn ≫ g) = 0`.  The composite
  -- `α := ιTruncLE(-n) ≫ fn ≫ g : τ_{≤-n}Kn ⟶ X₃` goes from a `D^{≤-n}` object to a
  -- `D^{≥-n}` object, so `Q α` is detected by `H^{-n}`, where it factors through
  -- `H^{-n}(fn) = 0`.
  have hge : (DerivedCategory.Q.obj
      (CochainComplex.shortComplexTruncLE Kn1 (-((n:ℤ)+1))).X₃).IsGE (-(n:ℤ)) := by
    have hc := Q_truncLE_cofiber_isGE Kn1 (-((n:ℤ)+1)) hS
    rwa [show -((n:ℤ)+1) + 1 = -(n:ℤ) by omega] at hc
  have hα : DerivedCategory.Q.map (Kn.ιTruncLE (-(n:ℤ)) ≫ fn ≫ g) = 0 := by
    apply hom_eq_zero_of_isLE_isGE _ _ (-(n:ℤ))
    rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, Functor.map_comp,
      Functor.map_comp, homologyFunctor_Q_map_eq_zero Kn Kn1 fn (-(n:ℤ)) hf]
    simp
  simp [hα]

/-! ### The contravariant case

The duals of the two lemmas above, with `τ_{≤}` ↦ `τ_{≥}`, `ι` ↦ `π` and degrees negated,
proved through the dual truncation triangle `τ_{≤n} K → K → τ_{≥n+1} K → [1]`. -/

/-- **Base case (contravariant).** If `H^i(K_0) = 0` for all `i < 0`, then the
canonical map `π : K_0 ⟶ τ_{≥0}(K_0)` is an isomorphism in `D(A)`.

Dual to `covariant_base`: `πTruncGE 0` is a quasi-isomorphism exactly when `K_0` is
cohomologically concentrated in degrees `≥ 0` (`CochainComplex.quasiIso_πTruncGE_iff`), which is
hypothesis `h1`, and `Q` turns quasi-isomorphisms into isomorphisms. -/
theorem contravariant_base
    (K0 : CochainComplex A ℤ)
    (h1 : ∀ i : ℤ, i < 0 → Limits.IsZero (K0.homology i)) :
    IsIso (DerivedCategory.Q.map (K0.πTruncGE 0)) := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso, K0.quasiIso_πTruncGE_iff, K0.isGE_iff]
  exact fun i hi => (K0.exactAt_iff_isZero_homology i).2 (h1 i hi)

/-- **Inductive step (contravariant).** Suppose `ψ : Q(K_n) ⟶ Q(X0)` factors
through `Q(πTruncGE n)` (i.e. through `τ_{≥n}(K_n)`), and `gn : K_{n+1} ⟶ K_n`
induces the zero map on `H^{n}`.  Then `Q(gn) ≫ ψ` factors through
`Q(πTruncGE (n+1))` (i.e. through `τ_{≥(n+1)}(K_{n+1})`).

Dual to `covariant_step`: use the truncation distinguished
triangle for `K_{n+1}` at the bound `a = n+1`:
  `τ_{≤n}(K_{n+1}) → K_{n+1} → τ_{≥(n+1)}(K_{n+1}) → [1]`,
and the homological (covariant) `Hom_{D}(-, X0)` exactness: `Q(gn) ≫ ψ` factors
through `Q(πTruncGE (n+1))` iff `Q(ιTruncLE n) ≫ Q(gn) ≫ ψ = 0`.  Writing
`ψ = Q(πTruncGE n) ≫ h₀` and using the SAME-degree (`n`) overlap of
`τ_{≤n}(K_{n+1})` (`IsLE n`) with `τ_{≥n}(K_n)` (`IsGE n`), the relevant map is
detected on `H^{n}` and factors through `H^{n}(gn) = 0` (hypothesis `hg`), hence
vanishes.  Same heart-Hom t-structure sub-fact as in `covariant_step`. -/
theorem contravariant_step
    (n : ℕ) (Kn1 Kn : CochainComplex A ℤ) (gn : Kn1 ⟶ Kn)
    (hg : HomologicalComplex.homologyMap gn (n : ℤ) = 0)
    (X0 : CochainComplex A ℤ)
    (ψ : DerivedCategory.Q.obj Kn ⟶ DerivedCategory.Q.obj X0)
    (hψ : ∃ h : DerivedCategory.Q.obj (Kn.truncGE (n : ℤ)) ⟶ DerivedCategory.Q.obj X0,
        ψ = DerivedCategory.Q.map (Kn.πTruncGE (n : ℤ)) ≫ h) :
    ∃ h : DerivedCategory.Q.obj (Kn1.truncGE ((n:ℤ)+1)) ⟶ DerivedCategory.Q.obj X0,
      DerivedCategory.Q.map gn ≫ ψ =
        DerivedCategory.Q.map (Kn1.πTruncGE ((n:ℤ)+1)) ≫ h := by
  have hS := CochainComplex.shortComplexTruncLE_shortExact Kn1 (n:ℤ)
  obtain ⟨h₀, rfl⟩ := hψ
  have hα : DerivedCategory.Q.map (Kn1.ιTruncLE (n:ℤ)) ≫ DerivedCategory.Q.map gn ≫
      DerivedCategory.Q.map (Kn.πTruncGE (n:ℤ)) = 0 := by
    apply hom_eq_zero_of_isLE_isGE _ _ (n:ℤ)
    rw [Functor.map_comp, Functor.map_comp, homologyFunctor_Q_map_eq_zero Kn1 Kn gn (n:ℤ) hg]
    simp
  obtain ⟨h', hh'⟩ := Pretriangulated.Triangle.yoneda_exact₂ _
    (DerivedCategory.triangleOfSES_distinguished hS)
    (DerivedCategory.Q.map gn ≫ DerivedCategory.Q.map (Kn.πTruncGE (n:ℤ)) ≫ h₀)
    ((reassoc_of% hα) h₀ |>.trans Limits.zero_comp)
  refine ⟨inv (DerivedCategory.Q.map
    (Kn1.shortComplexTruncLEX₃ToTruncGE (n:ℤ) ((n:ℤ)+1) rfl)) ≫ h', ?_⟩
  rw [hh', DerivedCategory.triangleOfSES_mor₂,
    ← CochainComplex.g_shortComplexTruncLEX₃ToTruncGE Kn1 (n:ℤ) ((n:ℤ)+1) rfl, Functor.map_comp,
    Category.assoc, IsIso.hom_inv_id_assoc]

/-- The composition of a covariant chain of maps
`K 0 ⟶ K 1 ⟶ ... ⟶ K n`, giving a single morphism `K 0 ⟶ K n`. -/
def chainComp (K : ℕ → CochainComplex A ℤ) (f : ∀ j, K j ⟶ K (j + 1)) :
    ∀ n, K 0 ⟶ K n
  | 0 => 𝟙 _
  | (n + 1) => chainComp K f n ≫ f n

/-- The composition of a contravariant chain of maps
`K n ⟶ K (n-1) ⟶ ... ⟶ K 0`, giving a single morphism `K n ⟶ K 0`. -/
def chainCompOp (K : ℕ → CochainComplex A ℤ) (g : ∀ j, K (j + 1) ⟶ K j) :
    ∀ n, K n ⟶ K 0
  | 0 => 𝟙 _
  | (n + 1) => g n ≫ chainCompOp K g n

/-- Statement 1 (covariant case). If `H^i(K 0) = 0` for `i > 0` and the induced
map `H^{-j}(f j)` vanishes for each `0 ≤ j ≤ n-1`, then the composite
`K 0 ⟶ K n`, viewed in the derived category, factors through the canonical map
`ι : τ_{≤ -n} (K n) ⟶ K n`.

PROOF.  Induction on `n`.
* `n = 0`: `chainComp K f 0 = 𝟙`, and `covariant_base` makes `Q(ιTruncLE 0)`
  invertible, so `h = inv (Q(ιTruncLE 0))` works.
* `n → n+1`: `chainComp K f (m+1) = chainComp K f m ≫ f m`.  The induction
  hypothesis factors `Q(chainComp K f m)` through `Q(ιTruncLE (-m))`; apply
  `covariant_step m (K m) (K (m+1)) (f m)` (its `H^{-m}(f m) = 0` hypothesis is
  `h2 m`), then rewrite `-(↑m+1) = -(↑(m+1))` by `push_cast` to match. -/
@[stacks 08Q2 "(1)"]
theorem main_covariant
    (n : ℕ) (K : ℕ → CochainComplex A ℤ) (f : ∀ j, K j ⟶ K (j + 1))
    (h1 : ∀ i : ℤ, 0 < i → Limits.IsZero ((K 0).homology i))
    (h2 : ∀ j : ℕ, j < n → HomologicalComplex.homologyMap (f j) (-(j : ℤ)) = 0) :
    ∃ h : DerivedCategory.Q.obj (K 0) ⟶ DerivedCategory.Q.obj ((K n).truncLE (-(n : ℤ))),
      DerivedCategory.Q.map (chainComp K f n) =
        h ≫ DerivedCategory.Q.map ((K n).ιTruncLE (-(n : ℤ))) := by
  induction n with
  | zero =>
      have hiso := covariant_base (K 0) h1
      have e : (-((0:ℕ):ℤ)) = (0:ℤ) := by norm_num
      rw [e] at *
      refine ⟨inv (DerivedCategory.Q.map ((K 0).ιTruncLE (0:ℤ))), ?_⟩
      rw [IsIso.inv_hom_id]
      simp [chainComp]
  | succ m ih =>
      have hih := ih (fun j hj => h2 j (by omega))
      have hstep := covariant_step m (K m) (K (m+1)) (f m)
        (h2 m (by omega)) (K 0) (DerivedCategory.Q.map (chainComp K f m)) hih
      have ecast : (-((m:ℤ)+1)) = (-(((m+1:ℕ)):ℤ)) := by omega
      rw [ecast] at hstep
      obtain ⟨h, hh⟩ := hstep
      exact ⟨h, by rwa [chainComp, Functor.map_comp]⟩

/-- Statement 2 (contravariant / dual case). If `H^i(K 0) = 0` for `i < 0` and
the induced map `H^{j}(g j)` vanishes for each `0 ≤ j ≤ n-1`, then the composite
`K n ⟶ K 0`, viewed in the derived category, factors through the canonical map
`π : K n ⟶ τ_{≥ n} (K n)`.

PROOF.  Dual of `main_covariant`, by induction on `n` using `contravariant_base`
(base) and `contravariant_step` (step). -/
@[stacks 08Q2 "(2)", sga "4 XVIII 2.14.2" "partial"]
theorem main_contravariant
    (n : ℕ) (K : ℕ → CochainComplex A ℤ) (g : ∀ j, K (j + 1) ⟶ K j)
    (h1 : ∀ i : ℤ, i < 0 → Limits.IsZero ((K 0).homology i))
    (h2 : ∀ j : ℕ, j < n → HomologicalComplex.homologyMap (g j) (j : ℤ) = 0) :
    ∃ h : DerivedCategory.Q.obj ((K n).truncGE (n : ℤ)) ⟶ DerivedCategory.Q.obj (K 0),
      DerivedCategory.Q.map (chainCompOp K g n) =
        DerivedCategory.Q.map ((K n).πTruncGE (n : ℤ)) ≫ h := by
  induction n with
  | zero =>
      have hiso := contravariant_base (K 0) h1
      have e : ((0:ℕ):ℤ) = (0:ℤ) := by norm_num
      rw [e] at *
      refine ⟨inv (DerivedCategory.Q.map ((K 0).πTruncGE (0:ℤ))), ?_⟩
      rw [IsIso.hom_inv_id]
      simp [chainCompOp]
  | succ m ih =>
      have hih := ih (fun j hj => h2 j (by omega))
      have hstep := contravariant_step m (K (m+1)) (K m) (g m)
        (h2 m (by omega)) (K 0) (DerivedCategory.Q.map (chainCompOp K g m)) hih
      have ecast : ((m:ℤ)+1) = (((m+1:ℕ)):ℤ) := by omega
      rw [ecast] at hstep
      obtain ⟨h, hh⟩ := hstep
      exact ⟨h, by rwa [chainCompOp, Functor.map_comp]⟩

end

end
