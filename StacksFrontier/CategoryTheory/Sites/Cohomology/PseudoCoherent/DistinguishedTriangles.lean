module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalLiftingThroughCohomologyIsomorphisms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence in a distinguished triangle on a ringed site

Let `(C, O)` be a ringed site and let `K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle of
`D(O)`. Then:

1. if `K` is `(m + 1)`-pseudo-coherent and `L` is `m`-pseudo-coherent, so is `M`;
2. if `K` and `M` are `m`-pseudo-coherent, so is `L`;
3. if `L` is `(m + 1)`-pseudo-coherent and `M` is `m`-pseudo-coherent, then `K` is
   `(m + 1)`-pseudo-coherent.

This is Stacks 08FV.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_one_general`,
  `..._two_general`, `..._three_general`: parts (1), (2), (3), at independent site, morphism
  and module universes.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_one`: part (1).
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_two`: part (2).
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_three`: part (3).

## Implementation notes

Part (1) is the substance. A distinguished triangle of `D(O)` is isomorphic to the image of
the mapping-cone triangle of a map `f : K ⟶ L` of complexes (`DerivedCategory.mem_distTriang_iff`),
and Stacks 08FU (2) makes both `K` and `L` themselves pseudo-coherent complexes in the relevant
degrees, so it suffices to show that `C(f)` is an `m`-pseudo-coherent complex. For that, say that
an object `V` of the site *carries an approximation* when there are a strictly perfect complex
`P` of `O|_V`-modules and a map `P ⟶ K|_V` which is invertible on cohomology above `m` and epic
in degree `m`; the objects carrying one form a sieve `approximationSieve`, which is covering
exactly when `K` is `m`-pseudo-coherent. Over an object carrying approximations of both `K` and
`L`, the approximation of `K` may first be replaced by its stupid truncation above `m + 1`
(which is still strictly perfect, still invertible on cohomology above `m + 1` and still epic
in degree `m + 1`, and now vanishes below `m + 1`), so that Stacks 08FQ applies and lifts the
composite `P ⟶ K|_V ⟶ L|_V` through the approximation `Q ⟶ L|_V` up to homotopy on a covering
of `V`. The map of mapping-cone triangles in the homotopy category induced by such a homotopy
square then has an approximation of `C(f)` as its third vertex, by the four-lemma applied to
the two long exact cohomology sequences.

Parts (2) and (3) follow from part (1) applied to a rotation of the triangle, together with the
behaviour of pseudo-coherence under shifts.

Two pieces of bookkeeping:

* Stacks 08FQ restricts along an arrow `g : V ⟶ U` of the covering sieve by
  `SheafOfModules.overFunctor` on the slice `C/U`, landing in sheaves of modules over the
  *iterated* slice `(C/U)/(V → U)`, whereas pseudo-coherence speaks of the slice `C/V`. The two
  are compared by `Stacks.SheafOfModules.sliceBackward`, the pushforward along
  `Over.iteratedSliceBackward`, exactly as in the proof of Stacks 08FU (2); the comparison is
  in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/IteratedSlice.lean`.
* Mathlib's stupid truncation `HomologicalComplex.stupidTrunc` has no inclusion into the
  complex it truncates; `stupidTruncGEι` supplies it for the embedding
  `ComplexShape.embeddingUpIntGE`.

Every statement is available twice. The `_general` form has the objects of the site, the
morphisms of the site and the sections of the structure sheaf at three independent universes
`u`, `v`, `w`, which is what a site whose morphism universe is smaller than its object
universe — the small étale site of an algebraic space, at `RingedSite.{u + 1, u, u}` — needs.
The form without the suffix is its instance at `RingedSite.{u, u, 0}`.

## References

* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w d

namespace AlgebraicGeometry.RingedSite

section Transfer

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

end Transfer

section StupidTrunc

/-- The index of the stupid-truncation embedding `embeddingUpIntGE a` landing on `i`, for
`i ≥ a`. -/
private theorem embeddingUpIntGE_f_toNat (a i : ℤ) (h : a ≤ i) :
    (ComplexShape.embeddingUpIntGE a).f (i - a).toNat = i := by
  rw [ComplexShape.embeddingUpIntGE_f]
  omega

/-- The differential of a stupid truncation, in the degrees where the truncation agrees with
the complex it truncates. -/
private theorem stupidTrunc_d_eq {ι κ : Type*} {c : ComplexShape ι} {c' : ComplexShape κ}
    {A : Type*} [Category A] [HasZeroMorphisms A] [HasZeroObject A]
    (K : HomologicalComplex A c') (e : c.Embedding c') [e.IsRelIff]
    {i j : ι} {i' j' : κ} (hi : e.f i = i') (hj : e.f j = j') :
    (K.stupidTrunc e).d i' j' = (K.stupidTruncXIso e hi).hom ≫ K.d i' j' ≫
      (K.stupidTruncXIso e hj).inv := by
  subst i'
  subst j'
  show ((K.restriction e).extend e).d (e.f i) (e.f j) =
    (((K.restriction e).extendXIso e rfl).hom ≫ 𝟙 ((K.restriction e).X i)) ≫
      (K.restriction e).d i j ≫
        (𝟙 ((K.restriction e).X j) ≫ ((K.restriction e).extendXIso e rfl).inv)
  rw [Category.comp_id, Category.id_comp]
  exact HomologicalComplex.extend_d_eq (K.restriction e) e rfl rfl

variable {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]

/-- The stupid truncation above `a` of a cochain complex vanishes in every degree below `a`. -/
private theorem isZero_stupidTrunc_X_of_lt (K : CochainComplex A ℤ) (a i : ℤ) (h : i < a) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X i) := by
  refine K.isZero_stupidTrunc_X _ i fun n => ?_
  rw [ComplexShape.embeddingUpIntGE_f]
  omega

/-- The degreewise component of the inclusion of the stupid truncation above `a`: the identity
of `Kⁱ` in degrees `i ≥ a`, and zero below. -/
private noncomputable def stupidTruncGEι_f (K : CochainComplex A ℤ) (a i : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X i ⟶ K.X i :=
  if h : a ≤ i then
    (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE a) (embeddingUpIntGE_f_toNat a i h)).hom
  else 0

/-- In degrees at least `a` the inclusion of the stupid truncation above `a` is invertible. -/
private theorem stupidTruncGEι_f_of_le (K : CochainComplex A ℤ) (a i : ℤ) (h : a ≤ i) :
    stupidTruncGEι_f K a i =
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE a)
        (embeddingUpIntGE_f_toNat a i h)).hom :=
  dite_eq_left h

/-- The components of `stupidTruncGEι_f` commute with the differentials. -/
private theorem stupidTruncGEι_f_comm (K : CochainComplex A ℤ) (a i j : ℤ) :
    stupidTruncGEι_f K a i ≫ K.d i j =
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).d i j ≫ stupidTruncGEι_f K a j := by
  by_cases hi : a ≤ i
  · by_cases hij : i + 1 = j
    · have hj : a ≤ j := by omega
      rw [stupidTrunc_d_eq K (ComplexShape.embeddingUpIntGE a)
          (embeddingUpIntGE_f_toNat a i hi) (embeddingUpIntGE_f_toNat a j hj),
        stupidTruncGEι_f_of_le K a i hi, stupidTruncGEι_f_of_le K a j hj]
      simp
    · rw [K.shape i j hij,
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).shape i j hij, comp_zero, zero_comp]
  · exact (isZero_stupidTrunc_X_of_lt K a i (by omega)).eq_of_src _ _

/-- The inclusion of the stupid truncation above `a` into the complex it truncates.

Mathlib constructs the stupid truncation but not this inclusion. -/
private noncomputable def stupidTruncGEι (K : CochainComplex A ℤ) (a : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE a) ⟶ K where
  f i := stupidTruncGEι_f K a i
  comm' i j _ := stupidTruncGEι_f_comm K a i j

/-- The components of `stupidTruncGEι`. -/
private theorem stupidTruncGEι_f_eq (K : CochainComplex A ℤ) (a i : ℤ) :
    (stupidTruncGEι K a).f i = stupidTruncGEι_f K a i := rfl

variable {A : Type*} [Category A] [Abelian A]

/-- In degrees at least `a` the inclusion of the stupid truncation above `a` is an isomorphism. -/
private theorem isIso_stupidTruncGEι_f (K : CochainComplex A ℤ) (a j : ℤ) (hj : a ≤ j) :
    IsIso ((stupidTruncGEι K a).f j) := by
  rw [stupidTruncGEι_f_eq, stupidTruncGEι_f_of_le K a j hj]
  infer_instance

/-- The inclusion of the stupid truncation above `a` is invertible on cohomology in every
degree `> a`: the three terms of the short complex computing cohomology in such a degree sit in
degrees `≥ a`, where the inclusion is an isomorphism. -/
private theorem isIso_homologyMap_stupidTruncGEι (K : CochainComplex A ℤ) (a i : ℤ)
    (hai : a < i) : IsIso (HomologicalComplex.homologyMap (stupidTruncGEι K a) i) := by
  have hprev : (ComplexShape.up ℤ).prev i = i - 1 :=
    ComplexShape.prev_eq' _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)
  have hnext : (ComplexShape.up ℤ).next i = i + 1 :=
    ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp)
  have h₁ : IsIso ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i).map
      (stupidTruncGEι K a)).τ₁ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₁]
    exact isIso_stupidTruncGEι_f K a _ (by rw [hprev]; omega)
  have h₂ : IsIso ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i).map
      (stupidTruncGEι K a)).τ₂ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₂]
    exact isIso_stupidTruncGEι_f K a i (by omega)
  have h₃ : IsIso ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i).map
      (stupidTruncGEι K a)).τ₃ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₃]
    exact isIso_stupidTruncGEι_f K a _ (by rw [hnext]; omega)
  have : IsIso ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i).map
      (stupidTruncGEι K a)) := ShortComplex.isIso_of_isIso _
  rw [← quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff]
  exact ShortComplex.quasiIso_of_isIso _

/-- The inclusion of the stupid truncation above `a` is epic on cohomology in degree `a`: in
that degree the middle and right terms of the short complex computing cohomology are unchanged,
so the map of cycles is already invertible. -/
private theorem epi_homologyMap_stupidTruncGEι (K : CochainComplex A ℤ) (a : ℤ) :
    Epi (HomologicalComplex.homologyMap (stupidTruncGEι K a) a) := by
  have hnext : (ComplexShape.up ℤ).next a = a + 1 :=
    ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel a (a + 1) by simp)
  have h₂ : IsIso ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) a).map
      (stupidTruncGEι K a)).τ₂ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₂]
    exact isIso_stupidTruncGEι_f K a a (by omega)
  have h₃ : Mono ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) a).map
      (stupidTruncGEι K a)).τ₃ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₃]
    exact @IsIso.mono_of_iso _ _ _ _ _
      (isIso_stupidTruncGEι_f K a ((ComplexShape.up ℤ).next a) (by rw [hnext]; omega))
  have : IsIso (ShortComplex.cyclesMap
      ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) a).map
        (stupidTruncGEι K a))) :=
    ShortComplex.isIso_cyclesMap_of_isIso_of_mono _
  show Epi (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) a).map (stupidTruncGEι K a)))
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap _

end StupidTrunc

section Cone

variable {A : Type*} [Category A] [Abelian A]
  {S T : Triangle (HomotopyCategory A (ComplexShape.up ℤ))}

/-- The four-lemma for the two long exact cohomology sequences of a morphism of distinguished
triangles of the homotopy category: if the map of first vertices is epic in degree `i` and
invertible in degree `i + 1`, and the map of second vertices is invertible in degree `i` and
monic in degree `i + 1`, then the map of third vertices is invertible in degree `i`. -/
private theorem isIso_homology₃_of_triangleMap
    (hS : S ∈ distinguishedTriangles) (hT : T ∈ distinguishedTriangles) (φ : S ⟶ T) (i : ℤ)
    (h₁ : Epi (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift i).map φ.hom₁))
    (h₂ : IsIso (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift i).map
      φ.hom₂))
    (h₁' : IsIso (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift (i + 1)).map
      φ.hom₁))
    (h₂' : Mono (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift (i + 1)).map
      φ.hom₂)) :
    IsIso (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift i).map φ.hom₃) := by
  set H := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0
  let rowS : ComposableArrows A 4 := ComposableArrows.mk₄
    ((H.shift i).map S.mor₁) ((H.shift i).map S.mor₂)
    (H.homologySequenceδ S i (i + 1) rfl) ((H.shift (i + 1)).map S.mor₁)
  let rowT : ComposableArrows A 4 := ComposableArrows.mk₄
    ((H.shift i).map T.mor₁) ((H.shift i).map T.mor₂)
    (H.homologySequenceδ T i (i + 1) rfl) ((H.shift (i + 1)).map T.mor₁)
  have exS : rowS.Exact :=
    ComposableArrows.exact_of_δ₀ (H.homologySequence_exact₂ S hS i).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (H.homologySequence_exact₃ S hS i (i + 1) rfl).exact_toComposableArrows
        (H.homologySequence_exact₁ S hS i (i + 1) rfl).exact_toComposableArrows)
  have exT : rowT.Exact :=
    ComposableArrows.exact_of_δ₀ (H.homologySequence_exact₂ T hT i).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (H.homologySequence_exact₃ T hT i (i + 1) rfl).exact_toComposableArrows
        (H.homologySequence_exact₁ T hT i (i + 1) rfl).exact_toComposableArrows)
  let φ' : rowS ⟶ rowT := ComposableArrows.homMk₄
    ((H.shift i).map φ.hom₁) ((H.shift i).map φ.hom₂) ((H.shift i).map φ.hom₃)
    ((H.shift (i + 1)).map φ.hom₁) ((H.shift (i + 1)).map φ.hom₂)
    (by change (H.shift i).map S.mor₁ ≫ (H.shift i).map φ.hom₂ =
          (H.shift i).map φ.hom₁ ≫ (H.shift i).map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by change (H.shift i).map S.mor₂ ≫ (H.shift i).map φ.hom₃ =
          (H.shift i).map φ.hom₂ ≫ (H.shift i).map T.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    (by change H.homologySequenceδ S i (i + 1) rfl ≫ (H.shift (i + 1)).map φ.hom₁ =
          (H.shift i).map φ.hom₃ ≫ H.homologySequenceδ T i (i + 1) rfl
        exact (H.homologySequenceδ_naturality φ i (i + 1) rfl).symm)
    (by change (H.shift (i + 1)).map S.mor₁ ≫ (H.shift (i + 1)).map φ.hom₂ =
          (H.shift (i + 1)).map φ.hom₁ ≫ (H.shift (i + 1)).map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono exS exT φ' h₁ h₂ h₁' h₂'

/-- The epic half of the four-lemma, one step shorter: if the map of second vertices is epic in
degree `i`, and the map of first vertices is epic in degree `i + 1` while the map of second
vertices is monic there, then the map of third vertices is epic in degree `i`. -/
private theorem epi_homology₃_of_triangleMap
    (hS : S ∈ distinguishedTriangles) (hT : T ∈ distinguishedTriangles) (φ : S ⟶ T) (i : ℤ)
    (h₂ : Epi (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift i).map φ.hom₂))
    (h₁' : Epi (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift (i + 1)).map
      φ.hom₁))
    (h₂' : Mono (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift (i + 1)).map
      φ.hom₂)) :
    Epi (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift i).map φ.hom₃) := by
  set H := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0
  let rowS : ComposableArrows A 3 := ComposableArrows.mk₃
    ((H.shift i).map S.mor₂) (H.homologySequenceδ S i (i + 1) rfl)
    ((H.shift (i + 1)).map S.mor₁)
  let rowT : ComposableArrows A 3 := ComposableArrows.mk₃
    ((H.shift i).map T.mor₂) (H.homologySequenceδ T i (i + 1) rfl)
    ((H.shift (i + 1)).map T.mor₁)
  have exS : rowS.Exact :=
    ComposableArrows.exact_of_δ₀
      (H.homologySequence_exact₃ S hS i (i + 1) rfl).exact_toComposableArrows
      (H.homologySequence_exact₁ S hS i (i + 1) rfl).exact_toComposableArrows
  have exT : rowT.Exact :=
    ComposableArrows.exact_of_δ₀
      (H.homologySequence_exact₃ T hT i (i + 1) rfl).exact_toComposableArrows
      (H.homologySequence_exact₁ T hT i (i + 1) rfl).exact_toComposableArrows
  let φ' : rowS ⟶ rowT := ComposableArrows.homMk₃
    ((H.shift i).map φ.hom₂) ((H.shift i).map φ.hom₃)
    ((H.shift (i + 1)).map φ.hom₁) ((H.shift (i + 1)).map φ.hom₂)
    (by change (H.shift i).map S.mor₂ ≫ (H.shift i).map φ.hom₃ =
          (H.shift i).map φ.hom₂ ≫ (H.shift i).map T.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    (by change H.homologySequenceδ S i (i + 1) rfl ≫ (H.shift (i + 1)).map φ.hom₁ =
          (H.shift i).map φ.hom₃ ≫ H.homologySequenceδ T i (i + 1) rfl
        exact (H.homologySequenceδ_naturality φ i (i + 1) rfl).symm)
    (by change (H.shift (i + 1)).map S.mor₁ ≫ (H.shift (i + 1)).map φ.hom₂ =
          (H.shift (i + 1)).map φ.hom₁ ≫ (H.shift (i + 1)).map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
  exact Abelian.epi_of_epi_of_epi_of_mono φ' exS exT h₂ h₁' h₂'

/-- The cone of a homotopy-commuting square approximates the cone of its target map.

Given `γ : P ⟶ Q` and `f : K ⟶ L` and a homotopy `γ ≫ β ∼ α ≫ f`, where `α` is invertible on
cohomology above `m + 1` and epic in degree `m + 1` and `β` is invertible on cohomology above
`m` and epic in degree `m`, the induced map `C(γ) ⟶ C(f)` is invertible on cohomology above `m`
and epic in degree `m`. -/
private theorem exists_mappingCone_approximation {P Q K L : CochainComplex A ℤ}
    (γ : P ⟶ Q) (f : K ⟶ L) (α : P ⟶ K) (β : Q ⟶ L)
    (h : Homotopy (γ ≫ β) (α ≫ f)) (m : ℤ)
    (hαi : ∀ j : ℤ, m + 1 < j → IsIso (HomologicalComplex.homologyMap α j))
    (hαe : Epi (HomologicalComplex.homologyMap α (m + 1)))
    (hβi : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j))
    (hβe : Epi (HomologicalComplex.homologyMap β m)) :
    ∃ c : CochainComplex.mappingCone γ ⟶ CochainComplex.mappingCone f,
      (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap c j)) ∧
      Epi (HomologicalComplex.homologyMap c m) := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let S := CochainComplex.mappingCone.triangleh γ
  let T := CochainComplex.mappingCone.triangleh f
  have hS := HomotopyCategory.mappingCone_triangleh_distinguished γ
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished f
  let φ := completeDistinguishedTriangleMorphism S T hS hT (q.map α) (q.map β)
    (by change q.map γ ≫ q.map β = q.map α ≫ q.map f
        rw [← q.map_comp, ← q.map_comp]
        exact HomotopyCategory.eq_of_homotopy _ _ h)
  let c := q.preimage φ.hom₃
  have hc : q.map c = φ.hom₃ := q.map_preimage _
  have hiα (j : ℤ) (hj : m + 1 < j) :
      IsIso (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift j).map
        φ.hom₁) :=
    (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors A _ j) α).mpr (hαi j hj)
  have heα (j : ℤ) (hj : m < j) :
      Epi (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift j).map φ.hom₁) := by
    refine (epi_map_iff_of_natIso (HomotopyCategory.homologyFunctorFactors A _ j) α).mpr ?_
    show Epi (HomologicalComplex.homologyMap α j)
    by_cases h' : j = m + 1
    · subst j
      exact hαe
    · have := hαi j (by omega)
      infer_instance
  have hiβ (j : ℤ) (hj : m < j) :
      IsIso (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shift j).map
        φ.hom₂) :=
    (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors A _ j) β).mpr (hβi j hj)
  refine ⟨c, fun j hj => ?_, ?_⟩
  · refine (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors A _ j) c).mp ?_
    show IsIso (((HomotopyCategory.homologyFunctor A _ 0).shift j).map (q.map c))
    rw [hc]
    have := hiβ (j + 1) (by omega)
    exact isIso_homology₃_of_triangleMap hS hT φ j
      (heα j hj) (hiβ j hj) (hiα (j + 1) (by omega)) inferInstance
  · refine (epi_map_iff_of_natIso (HomotopyCategory.homologyFunctorFactors A _ m) c).mp ?_
    show Epi (((HomotopyCategory.homologyFunctor A _ 0).shift m).map (q.map c))
    rw [hc]
    have := hiβ (m + 1) (by omega)
    exact epi_homology₃_of_triangleMap hS hT φ m
      ((epi_map_iff_of_natIso (HomotopyCategory.homologyFunctorFactors A _ m) β).mpr hβe)
      (heα (m + 1) (by omega)) inferInstance

end Cone

section Lift

/-- Transport of a lift up to homotopy along an isomorphism `P ⋙ Q ≅ T` of functors: a lift of
`P α` through `P f` up to homotopy becomes a lift of `T α` through `T f` up to homotopy. -/
private theorem exists_lift_homotopy_of_natIso {A₁ A₂ A₃ : Type*}
    [Category A₁] [Category A₂] [Category A₃]
    [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
    (P : A₁ ⥤ A₂) (Q : A₂ ⥤ A₃) (T : A₁ ⥤ A₃) [P.Additive] [Q.Additive] [T.Additive]
    (ε : P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      T.mapHomologicalComplex (ComplexShape.up ℤ))
    {E F G : CochainComplex A₁ ℤ} (α : E ⟶ F) (f : G ⟶ F)
    (β : (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
    (hβ : Homotopy (β ≫ (P.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) :
    ∃ γ : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
        (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj G,
      Nonempty (Homotopy (γ ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) := by
  refine ⟨ε.inv.app E ≫ (Q.mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫ ε.hom.app G, ⟨?_⟩⟩
  have h := ((Q.mapHomotopy hβ).compLeft (ε.inv.app E)).compRight (ε.hom.app F)
  have hf := ε.hom.naturality f
  have hα := NatIso.naturality_1 ε α
  dsimp only [Functor.comp_map] at hf hα
  simpa only [Functor.map_comp, Category.assoc, hf, hα] using h

end Lift

section StrictlyPerfect

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The shift of a strictly perfect complex is strictly perfect: shifting permutes the terms. -/
private theorem isStrictlyPerfect_shift
    (K : CochainComplex (SheafOfModules.{w} R) ℤ) (n : ℤ) (hK : IsStrictlyPerfect R K) :
    IsStrictlyPerfect R (K⟦n⟧) := by
  refine ⟨?_, fun i => ?_⟩
  · apply Set.Finite.subset (s := (fun i : ℤ => n + i) ⁻¹' {i | ¬ IsZero (K.X i)})
    · exact hK.bounded.preimage fun i _ j _ hij => add_left_cancel hij
    · intro i hi
      have e := (CochainComplex.shiftEval (SheafOfModules.{w} R) n i (n + i) rfl).app K
      simp only [Set.mem_ofPred_eq] at hi
      exact fun hz => hi (e.isZero_iff.mpr hz)
  · exact IsDirectSummandOfFiniteFree.of_iso R
      ((CochainComplex.shiftEval (SheafOfModules.{w} R) n i (n + i) rfl).app K)
      (hK.termDirectSummand (n + i))

/-- The stupid truncation above `a` of a strictly perfect complex is strictly perfect: its
terms are those of the complex in degrees at least `a`, and zero below. -/
private theorem isStrictlyPerfect_stupidTruncGE
    (K : CochainComplex (SheafOfModules.{w} R) ℤ) (a : ℤ) (hK : IsStrictlyPerfect R K) :
    IsStrictlyPerfect R (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)) := by
  refine ⟨hK.bounded.subset ?_, fun i => ?_⟩
  · intro i hi
    simp only [Set.mem_ofPred_eq] at hi ⊢
    by_cases hai : a ≤ i
    · exact fun hz => hi ((K.stupidTruncXIso (ComplexShape.embeddingUpIntGE a)
        (embeddingUpIntGE_f_toNat a i hai)).isZero_iff.mpr hz)
    · exact absurd (isZero_stupidTrunc_X_of_lt K a i (by omega)) hi
  · by_cases hai : a ≤ i
    · exact IsDirectSummandOfFiniteFree.of_iso R
        (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE a)
          (embeddingUpIntGE_f_toNat a i hai)) (hK.termDirectSummand i)
    · exact (isDirectSummandOfFiniteFree_iff_free R _).mpr
        ⟨0, 0, 0, (isZero_stupidTrunc_X_of_lt K a i (by omega)).eq_of_src _ _⟩

end StrictlyPerfect

section Site

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] ovFunctorLimits ovFunctorColimits overMapLimits overMapColimits

/-- Restriction of sheaves of `O|_U`-modules along an arrow `V ⟶ U` of the site preserves
epimorphisms. -/
local instance inTrianglesOverMapPreservesEpimorphisms {U V : X.C} (g : V ⟶ U) :
    (SheafOfModules.overMap.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).PreservesEpimorphisms :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesEpimorphisms g

/-- Restriction of cochain complexes of `O|_U`-modules along an arrow `V ⟶ U` of the site. -/
private noncomputable abbrev restrictAlong {U V : X.C} (g : V ⟶ U) :
    CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ ⥤
      CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ :=
  (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
    (ComplexShape.up ℤ)

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Stacks 08FQ**, with the restriction to the slice over an arrow `V ⟶ U` of the covering
sieve expressed by `SheafOfModules.overMap` rather than by restriction to an iterated slice. -/
private theorem exists_coveringSieve_lift_homotopy_overMap (U : X.C)
    {E F G :
      CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (hEa : ∀ j : ℤ, j < a → IsZero (E.X j))
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g →
        ∃ β : (restrictAlong X g).obj E ⟶ (restrictAlong X g).obj G,
          Nonempty (Homotopy (β ≫ (restrictAlong X g).map f)
            ((restrictAlong X g).map α)) := by
  obtain ⟨S, hS, hlift⟩ :=
    exists_coveringSieve_lift_homotopy_general X U α f a hE hEa hf_gt hf_a
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨β, ⟨hβ⟩⟩ := hlift g hg
  exact exists_lift_homotopy_of_natIso
    (SheafOfModules.overFunctor.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
      (Over.mk g))
    (Stacks.SheafOfModules.sliceBackward (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    (Stacks.SheafOfModules.sliceBackwardComplexIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    α f β hβ

/-- An object `U` of the site *carries an `m`-approximation of `K`* if there are a strictly
perfect complex `P` of `O|_U`-modules and a map `P ⟶ K|_U` which is invertible on cohomology in
every degree `> m` and epic on cohomology in degree `m`. -/
private abbrev LocalApproximation
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (U : X.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P ∧
    ∃ α : P ⟶ X.restrictComplex K U,
      (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
      Epi (HomologicalComplex.homologyMap α m)

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Carrying an `m`-approximation is stable under restriction along an arrow of the site:
restriction is exact and carries strictly perfect complexes to strictly perfect complexes. -/
private theorem localApproximation_restrict
    {K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} {m : ℤ}
    {U V : X.C} (g : V ⟶ U) (h : LocalApproximation X K m U) :
    LocalApproximation X K m V := by
  obtain ⟨P, hP, α, hαi, hαe⟩ := h
  refine ⟨(restrictAlong X g).obj P,
    isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP,
    (restrictAlong X g).map α ≫
      ((Stacks.SheafOfModules.overFunctorMapComplexIso
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K).hom,
    ?_, ?_⟩
  · intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have := isIso_homologyMap_map
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) α j (hαi j hj)
    have := AlgebraicGeometry.RingedSite.isIso_homologyMap_of_iso
      ((Stacks.SheafOfModules.overFunctorMapComplexIso
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K) j
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have := epi_homologyMap_map
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) α m hαe
    have := AlgebraicGeometry.RingedSite.isIso_homologyMap_of_iso
      ((Stacks.SheafOfModules.overFunctorMapComplexIso
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K) m
    infer_instance

/-- The sieve of arrows whose source carries an `m`-approximation of `K`. -/
private def approximationSieve
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (U : X.C) : Sieve U where
  arrows {V} _ := LocalApproximation X K m V
  downward_closed := fun h g => localApproximation_restrict X g h

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- If `K` is an `m`-pseudo-coherent complex then `approximationSieve` is a covering sieve of
every object: the definition of pseudo-coherence provides a covering presieve all of whose
arrows have sources carrying an approximation. -/
private theorem approximationSieve_covering
    {K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} {m : ℤ}
    (h : X.IsPseudoCoherentComplexFrom K m) (U : X.C) :
    approximationSieve X K m U ∈ X.J U := by
  obtain ⟨S, hS, hdata⟩ := h U
  exact X.J.superset_covering ((Sieve.generate_le_iff _ _).mpr fun _ _ hf => hdata _ hf) hS

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- An approximation may be replaced by one vanishing below its degree, namely by its stupid
truncation above `m`: that is still strictly perfect, and the inclusion of the truncation is
invertible on cohomology above `m` and epic in degree `m`. -/
private theorem localApproximation_truncate
    {K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} {m : ℤ}
    {U : X.C}
    (h : LocalApproximation X K m U) :
    ∃ P :
      CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P ∧
      ∃ α : P ⟶ X.restrictComplex K U,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m) ∧
        ∀ j : ℤ, j < m → IsZero (P.X j) := by
  obtain ⟨P, hP, α, hαi, hαe⟩ := h
  refine ⟨P.stupidTrunc (ComplexShape.embeddingUpIntGE m),
    isStrictlyPerfect_stupidTruncGE ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P m hP,
    stupidTruncGEι P m ≫ α, ?_, ?_, fun j hj => isZero_stupidTrunc_X_of_lt P m j hj⟩
  · intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have := hαi j hj
    have := isIso_homologyMap_stupidTruncGEι P m j hj
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have := epi_homologyMap_stupidTruncGEι P m
    infer_instance

/-- The key step of part (1): over an object carrying an `(m + 1)`-approximation of `K` and an
`m`-approximation of `L`, the cone of `f : K ⟶ L` carries an `m`-approximation locally.

The `(m + 1)`-approximation of `K` is first truncated so that Stacks 08FQ applies to it, and
lifts its composite into `L|_U` through the approximation of `L` up to homotopy on a covering
sieve; over each arrow of that sieve the cone of the lift is the required approximation, by
`exists_mappingCone_approximation`. -/
private theorem localApproximation_cone (m : ℤ)
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : K ⟶ L) (U : X.C)
    (hK : LocalApproximation X K (m + 1) U) (hL : LocalApproximation X L m U) :
    approximationSieve X (CochainComplex.mappingCone f) m U ∈ X.J U := by
  obtain ⟨P, hP, α, hαi, hαe, hPa⟩ := localApproximation_truncate X hK
  obtain ⟨Q, hQ, β, hβi, hβe⟩ := hL
  set R := SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  set RHC := R.mapHomologicalComplex (ComplexShape.up ℤ)
  set fU := RHC.map f
  obtain ⟨S, hS, hlift⟩ := exists_coveringSieve_lift_homotopy_overMap X U (α ≫ fU) β (m + 1)
    hP hPa (fun j hj => hβi j (by omega))
    (by have := hβi (m + 1) (by omega); infer_instance)
  refine X.J.superset_covering
    (R := approximationSieve X (CochainComplex.mappingCone f) m U) ?_ hS
  intro V g hg
  obtain ⟨γ, ⟨hγ⟩⟩ := hlift g hg
  set F := SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
  set H := F.mapHomologicalComplex (ComplexShape.up ℤ)
  have hγ' : Homotopy (γ ≫ H.map β) (H.map α ≫ H.map fU) := by
    simpa only [Functor.map_comp] using hγ
  obtain ⟨c, hci, hce⟩ := exists_mappingCone_approximation γ (H.map fU) (H.map α) (H.map β)
    hγ' m (fun j hj => isIso_homologyMap_map F α j (hαi j hj))
    (epi_homologyMap_map F α (m + 1) hαe)
    (fun j hj => isIso_homologyMap_map F β j (hβi j hj))
    (epi_homologyMap_map F β m hβe)
  let e : CochainComplex.mappingCone (H.map fU) ≅
      X.restrictComplex (CochainComplex.mappingCone f) V :=
    (CochainComplex.mappingCone.mapHomologicalComplexIso fU F).symm ≪≫
      H.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f R).symm ≪≫
      (Stacks.SheafOfModules.overFunctorMapComplexIso
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app
        (CochainComplex.mappingCone f)
  refine ⟨CochainComplex.mappingCone γ,
    mappingCone_isStrictlyPerfect _ γ
      (isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP)
      (isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hQ),
    c ≫ e.hom, ?_, ?_⟩
  · intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have := hci j hj
    have := AlgebraicGeometry.RingedSite.isIso_homologyMap_of_iso e j
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have := AlgebraicGeometry.RingedSite.isIso_homologyMap_of_iso e m
    infer_instance

/-- The cone of a map between an `(m + 1)`-pseudo-coherent complex and an `m`-pseudo-coherent
complex is `m`-pseudo-coherent, in the derived sense.

The sieve of objects carrying an approximation of the cone contains, by
`localApproximation_cone`, a covering sieve over every arrow of the intersection of the two
approximation sieves of `K` and `L`, which is covering; transitivity of the topology finishes
it. -/
private theorem isPseudoCoherentFrom_mappingCone
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (m : ℤ)
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : K ⟶ L)
    (hK : X.IsPseudoCoherentComplexFrom K (m + 1))
    (hL : X.IsPseudoCoherentComplexFrom L m) :
    X.IsPseudoCoherentFrom (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) m := by
  refine ⟨CochainComplex.mappingCone f, ?_, ⟨Iso.refl _⟩⟩
  intro U
  set S := approximationSieve X K (m + 1) U ⊓ approximationSieve X L m U
  set T := approximationSieve X (CochainComplex.mappingCone f) m U
  have hS : S ∈ X.J U := X.J.intersection_covering
    (approximationSieve_covering X hK U) (approximationSieve_covering X hL U)
  have hT : T ∈ X.J U := X.J.transitive hS T fun V g hg =>
    localApproximation_cone X m f V hg.1 hg.2
  exact ⟨T.arrows, by simpa using hT, fun V g hg => hg⟩

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- Being `m`-pseudo-coherent is invariant under isomorphism in `D(O)`. -/
theorem isPseudoCoherentFrom_of_iso
    {A B : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : ℤ)
    (hA : X.IsPseudoCoherentFrom A m) (e : B ≅ A) : X.IsPseudoCoherentFrom B m := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hA
  exact ⟨K, hK, ⟨eK.trans e.symm⟩⟩

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The shift by `n` of an `m`-pseudo-coherent complex is `(m - n)`-pseudo-coherent.

Restriction to a slice commutes with the shift of cochain complexes
(`Functor.mapCochainComplexShiftIso`), so the shift of a strictly perfect approximation is one
again; the degrees in which it is invertible or epic on cohomology are shifted accordingly. -/
@[sga "6 I 2.5" "a), bounded clause"]
private theorem isPseudoCoherentComplexFrom_shift (m n : ℤ)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : X.IsPseudoCoherentComplexFrom K m) :
    X.IsPseudoCoherentComplexFrom (K⟦n⟧) (m - n) := by
  intro U
  obtain ⟨S, hS, hdata⟩ := hK U
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨P, hP, α, hαiso, hαepi⟩ := hdata f hf
  let F := SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
  let FHC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let η := Functor.mapCochainComplexShiftIso F n
  have hηiso : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap (η.inv.app K) j) :=
    fun j => AlgebraicGeometry.RingedSite.isIso_homologyMap_of_iso (η.app K).symm j
  refine ⟨P⟦n⟧,
    isStrictlyPerfect_shift ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P n hP,
    α⟦n⟧' ≫ η.inv.app K, ?_, ?_⟩
  · intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have hshift : IsIso (HomologicalComplex.homologyMap (α⟦n⟧') j) := by
      have hq : QuasiIsoAt α (n + j) := by
        rw [quasiIsoAt_iff_isIso_homologyMap]
        exact hαiso (n + j) (by omega)
      have hq' : QuasiIsoAt (α⟦n⟧') j :=
        (CochainComplex.quasiIsoAt_shift_iff α n j (n + j) rfl).2 hq
      rwa [quasiIsoAt_iff_isIso_homologyMap] at hq'
    have := hηiso j
    infer_instance
  · let H := HomologicalComplex.homologyFunctor
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
      (ComplexShape.up ℤ) 0
    have hfirst : Epi (HomologicalComplex.homologyMap (α⟦n⟧') (m - n)) := by
      show Epi ((H.shift (m - n)).map (α⟦n⟧'))
      let ε := H.shiftIso n (m - n) m (by omega)
      rw [show (H.shift (m - n)).map (α⟦n⟧') =
        ε.hom.app P ≫ (H.shift m).map α ≫ ε.inv.app (FHC.obj K) from
          (NatIso.naturality_2 ε α).symm]
      have : Epi ((H.shift m).map α) := hαepi
      infer_instance
    rw [HomologicalComplex.homologyMap_comp]
    have := hηiso (m - n)
    exact epi_comp _ _

/-- The shift by `n` of an `m`-pseudo-coherent object of `D(O)` is `(m - n)`-pseudo-coherent. -/
private theorem isPseudoCoherentFrom_shift (m n : ℤ)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPseudoCoherentFrom E m) :
    X.IsPseudoCoherentFrom (E⟦n⟧) (m - n) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  refine ⟨K⟦n⟧, isPseudoCoherentComplexFrom_shift X m n K hK, ⟨?_⟩⟩
  exact (DerivedCategory.Q.commShiftIso n).app K ≪≫
    (shiftFunctor
      (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      n).mapIso e

/-- **Stacks 08FV, part (1)**, with the site, its morphisms and the sections of the structure
sheaf at independent universes. Let `(C, O)` be a ringed site and let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle of `D(O)`. If `K` is `(m + 1)`-pseudo-coherent
and `L` is `m`-pseudo-coherent, then `M` is `m`-pseudo-coherent. -/
@[stacks 08FV "part (1), general universes"]
theorem isPseudoCoherentFrom_of_distinguished_one_general (m : ℤ)
    (T : Triangle
      (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (hK : X.IsPseudoCoherentFrom T.obj₁ (m + 1))
    (hL : X.IsPseudoCoherentFrom T.obj₂ m) :
    X.IsPseudoCoherentFrom T.obj₃ m := by
  obtain ⟨K, L, f, ⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T).mp hT
  have hK'' := isPseudoCoherentFrom_of_iso X (m + 1) hK (asIso e.hom.hom₁).symm
  have hL'' := isPseudoCoherentFrom_of_iso X m hL (asIso e.hom.hom₂).symm
  have hK' : X.IsPseudoCoherentComplexFrom K (m + 1) :=
    isPseudoCoherentComplexFrom_of_iso_general X (DerivedCategory.Q.obj K) (m + 1) hK'' K
      (Iso.refl _)
  have hL' : X.IsPseudoCoherentComplexFrom L m :=
    isPseudoCoherentComplexFrom_of_iso_general X (DerivedCategory.Q.obj L) m hL'' L (Iso.refl _)
  exact isPseudoCoherentFrom_of_iso X m (isPseudoCoherentFrom_mappingCone X m K L f hK' hL')
    ⟨e.hom.hom₃, e.inv.hom₃, e.hom_inv_id_triangle_hom₃, e.inv_hom_id_triangle_hom₃⟩

/-- **Stacks 08FV, part (2)**, at independent site, morphism and module universes. If the
first and third vertices of a distinguished triangle of
`D(O)` are `m`-pseudo-coherent, so is the second.

Apply part (1) to the inverse rotation `M[-1] ⟶ K ⟶ L ⟶ M`. -/
@[stacks 08FV "part (2), general universes"]
theorem isPseudoCoherentFrom_of_distinguished_two_general (m : ℤ)
    (T : Triangle
      (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (hK : X.IsPseudoCoherentFrom T.obj₁ m)
    (hM : X.IsPseudoCoherentFrom T.obj₃ m) :
    X.IsPseudoCoherentFrom T.obj₂ m := by
  have hM' : X.IsPseudoCoherentFrom (T.obj₃⟦(-1 : ℤ)⟧) (m + 1) := by
    simpa using isPseudoCoherentFrom_shift X m (-1) T.obj₃ hM
  simpa using isPseudoCoherentFrom_of_distinguished_one_general X m T.invRotate
    (inv_rot_of_distTriang T hT) hM' hK

/-- **Stacks 08FV, part (3)**, at independent site, morphism and module universes. If the
second vertex of a distinguished triangle of `D(O)` is
`(m + 1)`-pseudo-coherent and the third is `m`-pseudo-coherent, then the first is
`(m + 1)`-pseudo-coherent.

Apply part (1) to the rotation `L ⟶ M ⟶ K[1] ⟶ L[1]` and shift back. -/
@[stacks 08FV "part (3), general universes"]
theorem isPseudoCoherentFrom_of_distinguished_three_general (m : ℤ)
    (T : Triangle
      (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (hL : X.IsPseudoCoherentFrom T.obj₂ (m + 1))
    (hM : X.IsPseudoCoherentFrom T.obj₃ m) :
    X.IsPseudoCoherentFrom T.obj₁ (m + 1) := by
  have hshift : X.IsPseudoCoherentFrom (T.obj₁⟦(1 : ℤ)⟧) m := by
    simpa using isPseudoCoherentFrom_of_distinguished_one_general X m T.rotate
      (rot_of_distTriang T hT) hL hM
  have hback : X.IsPseudoCoherentFrom ((T.obj₁⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧) (m + 1) := by
    simpa using isPseudoCoherentFrom_shift X m (-1) (T.obj₁⟦(1 : ℤ)⟧) hshift
  exact isPseudoCoherentFrom_of_iso X (m + 1) hback (shiftShiftNeg T.obj₁ 1).symm

section DiagonalUniverses

variable (X : RingedSite.{u, u, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Stacks 08FV, part (1).** Let `(C, O)` be a ringed site and let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle of `D(O)`. If `K` is `(m + 1)`-pseudo-coherent
and `L` is `m`-pseudo-coherent, then `M` is `m`-pseudo-coherent. -/
@[stacks 08FV "part (1)"]
theorem isPseudoCoherentFrom_of_distinguished_one (m : ℤ)
    (T : Triangle
      (DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (hK : X.IsPseudoCoherentFrom T.obj₁ (m + 1))
    (hL : X.IsPseudoCoherentFrom T.obj₂ m) :
    X.IsPseudoCoherentFrom T.obj₃ m :=
  isPseudoCoherentFrom_of_distinguished_one_general X m T hT hK hL

/-- **Stacks 08FV, part (2).** If the first and third vertices of a distinguished triangle of
`D(O)` are `m`-pseudo-coherent, so is the second.

Apply part (1) to the inverse rotation `M[-1] ⟶ K ⟶ L ⟶ M`. -/
@[stacks 08FV "part (2)", sga "6 I 2.5" "b)"]
theorem isPseudoCoherentFrom_of_distinguished_two (m : ℤ)
    (T : Triangle
      (DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (hK : X.IsPseudoCoherentFrom T.obj₁ m)
    (hM : X.IsPseudoCoherentFrom T.obj₃ m) :
    X.IsPseudoCoherentFrom T.obj₂ m :=
  isPseudoCoherentFrom_of_distinguished_two_general X m T hT hK hM

/-- **Stacks 08FV, part (3).** If the second vertex of a distinguished triangle of `D(O)` is
`(m + 1)`-pseudo-coherent and the third is `m`-pseudo-coherent, then the first is
`(m + 1)`-pseudo-coherent.

Apply part (1) to the rotation `L ⟶ M ⟶ K[1] ⟶ L[1]` and shift back. -/
@[stacks 08FV "part (3)"]
theorem isPseudoCoherentFrom_of_distinguished_three (m : ℤ)
    (T : Triangle
      (DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (hL : X.IsPseudoCoherentFrom T.obj₂ (m + 1))
    (hM : X.IsPseudoCoherentFrom T.obj₃ m) :
    X.IsPseudoCoherentFrom T.obj₁ (m + 1) :=
  isPseudoCoherentFrom_of_distinguished_three_general X m T hT hL hM

end DiagonalUniverses

end Site

end AlgebraicGeometry.RingedSite

end
