module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
public import StacksFrontier.Homology.HomotopyCategoryFiveLemma
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence in a distinguished triangle

Let `X` be a ringed space, let `m : ℤ` and let `(K, L, M)` be a distinguished triangle in the
derived category of `𝒪_X`-modules. Stacks 08CD says that (1) if `K` is `(m + 1)`-pseudo-coherent
and `L` is `m`-pseudo-coherent then `M` is `m`-pseudo-coherent, (2) if `K` and `M` are
`m`-pseudo-coherent then so is `L`, and (3) if `L` is `(m + 1)`-pseudo-coherent and `M` is
`m`-pseudo-coherent then `K` is `(m + 1)`-pseudo-coherent.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_obj₃_of_distinguished`,
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_obj₂_of_distinguished` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_obj₁_of_distinguished` are the three parts
  of Stacks 08CD.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_mappingCone` is the content: the
  mapping cone of a morphism `f : 𝒜 ⟶ ℬ` of complexes with `𝒜` `(m + 1)`-pseudo-coherent and `ℬ`
  `m`-pseudo-coherent is `m`-pseudo-coherent.
* `AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom.shift` and
  `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.shift`: shifting a complex, resp. an object
  of the derived category, by `n` shifts the bound by `-n`.
* `CochainComplex.stupidTruncGEIncl`: the inclusion of the stupid truncation in degrees `≥ n`.
* `AlgebraicGeometry.RingedSpace.exists_common_approximations`: two complexes which are
  pseudo-coherent with (possibly different) bounds have strictly perfect approximations over a
  *common* open neighbourhood of any given point.

## Implementation notes

The proof is the one in the Stacks Project. Part (1) is the only one with content: a
distinguished triangle in the derived category is isomorphic to the image of the mapping-cone
triangle of a morphism of complexes `f : 𝒜 ⟶ ℬ` (`DerivedCategory.mem_distTriang_iff`), and by
Stacks 08CC part (2) the pseudo-coherence hypotheses transfer to `𝒜` and `ℬ` *as complexes*. Over
a common open neighbourhood `U` of a point one then has strictly perfect approximations
`α : 𝒫 ⟶ 𝒜|_U` and `β : 𝒬 ⟶ ℬ|_U`; replacing `𝒫` by its stupid truncation in degrees `≥ m + 1`
makes it vanish below `m + 1`, so Stacks 08C8 lifts `α ≫ f|_U` through `β` up to homotopy over a
smaller open `W`, and the induced morphism of mapping cones `C(γ) ⟶ C(f)|_W` has the required
cohomological properties by the five lemma applied to the long exact cohomology sequences of the
two mapping-cone triangles. The cone `C(γ)` is strictly perfect by Stacks 08C5.

Parts (2) and (3) follow from part (1) by rotating the triangle, together with the behaviour of
pseudo-coherence under shifts.

All the machinery for moving between an open subspace and a smaller one — the restriction functor
`AlgebraicGeometry.RingedSpace.restrictModulesOfLE`, its transitivity, its exactness, that it
preserves strict perfection, and the reindexing
`AlgebraicGeometry.RingedSpace.restrictOverComplexHom` of the output of Stacks 08C8 — is in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PseudoCoherentIso.lean`, where Stacks 08CC needed
exactly the same devices; see its implementation notes.

Mathlib's `HomologicalComplex.stupidTrunc` has no inclusion morphism yet (its file records this
as a TODO), so `CochainComplex.stupidTruncGEIncl` is built here by hand; its cohomological
properties come from `CategoryTheory.ShortComplex` comparisons, since it is an isomorphism in
every degree `≥ n`.

Universes: as in `StacksFrontier/AlgebraicGeometry/PseudoCoherent/SheafLevel.lean`, the statements
are at `AlgebraicGeometry.RingedSpace.{u, u}` with `𝒪_X`-modules in universe `u`, and the derived
category of `X` is a hypothesis with its own universe.

## References

* [The Stacks Project, Lemma 20.46.9 (08CD)](https://stacks.math.columbia.edu/tag/08CD)
* [The Stacks Project, Lemma 20.46.8 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [The Stacks Project, Lemma 20.46.6 (08C8)](https://stacks.math.columbia.edu/tag/08C8)
* [The Stacks Project, Lemma 20.46.2 (08C5)](https://stacks.math.columbia.edu/tag/08C5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
  StrictlyPerfect

namespace CategoryTheory

universe v₁ u₁

/-- An isomorphism of complexes is an isomorphism on cohomology in every degree. Stated for an
abstract abelian category because instance search for this in the large local contexts of the
proofs about sheaves of modules below does not succeed. -/
public theorem isIso_homologyMap_iso_hom {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {K L : CochainComplex C ℤ} (e : K ≅ L) (j : ℤ) :
    IsIso (HomologicalComplex.homologyMap e.hom j) := inferInstance

/-- An isomorphism of complexes is an epimorphism on cohomology in every degree. -/
public theorem epi_homologyMap_iso_hom {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {K L : CochainComplex C ℤ} (e : K ≅ L) (j : ℤ) :
    Epi (HomologicalComplex.homologyMap e.hom j) :=
  have := isIso_homologyMap_iso_hom e j
  IsIso.epi_of_iso _

end CategoryTheory

namespace CochainComplex

universe v₁ u₁

/-- The inclusion of the stupid truncation in degrees `≥ n` into the complex: the canonical
isomorphism in every degree `≥ n` and the zero morphism below `n`, where the truncation vanishes.

Mathlib's `HomologicalComplex.stupidTrunc` does not yet provide this morphism. The source is
written as `(K.restriction e).extend e` rather than as `K.stupidTrunc e`, which is the same object
by definition, because that is the spelling in which `HomologicalComplex.extend_d_eq` and
`HomologicalComplex.restriction_d_eq` describe the differential. -/
@[ega "0 11.5.1"]
public def stupidTruncGEIncl {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [Limits.HasZeroObject C] (K : CochainComplex C ℤ) (n : ℤ) :
    (K.restriction (ComplexShape.embeddingUpIntGE n)).extend
      (ComplexShape.embeddingUpIntGE n) ⟶ K := by
  let e := ComplexShape.embeddingUpIntGE n
  let f : ∀ i, ((K.restriction e).extend e).X i ⟶ K.X i := fun i => by
    by_cases h : n ≤ i
    · let k := (Int.le.dest h).choose
      have he : e.f k = i := by
        rw [ComplexShape.embeddingUpIntGE_f]
        exact (Int.le.dest h).choose_spec
      exact ((K.restriction e).extendXIso e he).hom ≫ (K.restrictionXIso e he).hom
    · exact 0
  refine HomologicalComplex.Hom.mk f ?_
  intro i j hij
  simp only [ComplexShape.up, ComplexShape.up'] at hij
  subst j
  by_cases h : n ≤ i
  · have h' : n ≤ i + 1 := by omega
    let k := (Int.le.dest h).choose
    have he : e.f k = i := by
      rw [ComplexShape.embeddingUpIntGE_f]
      exact (Int.le.dest h).choose_spec
    let k' := (Int.le.dest h').choose
    have he' : e.f k' = i + 1 := by
      rw [ComplexShape.embeddingUpIntGE_f]
      exact (Int.le.dest h').choose_spec
    have hf : f i = ((K.restriction e).extendXIso e he).hom ≫
        (K.restrictionXIso e he).hom := by simp [f, h, k]
    have hf' : f (i + 1) = ((K.restriction e).extendXIso e he').hom ≫
        (K.restrictionXIso e he').hom := by simp [f, h', k']
    rw [hf, hf', HomologicalComplex.extend_d_eq (K.restriction e) e he he',
      HomologicalComplex.restriction_d_eq K e he he']
    simp [Category.assoc]
  · have hz : IsZero (((K.restriction e).extend e).X i) := by
      apply HomologicalComplex.isZero_extend_X
      intro k hk
      rw [ComplexShape.embeddingUpIntGE_f] at hk
      omega
    rw [show f i = 0 by simp [f, h], hz.eq_of_src (((K.restriction e).extend e).d i (i + 1)) 0]
    simp

/-- The source of `CochainComplex.stupidTruncGEIncl` vanishes in every degree below `n`. -/
public theorem isZero_stupidTruncGE_X {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [Limits.HasZeroObject C] (K : CochainComplex C ℤ) (n i : ℤ) (hi : i < n) :
    IsZero (((K.restriction (ComplexShape.embeddingUpIntGE n)).extend
      (ComplexShape.embeddingUpIntGE n)).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro k hk
  rw [ComplexShape.embeddingUpIntGE_f] at hk
  omega

/-- The inclusion of the stupid truncation in degrees `≥ n` is an isomorphism in every
degree `≥ n`. -/
public theorem isIso_stupidTruncGEIncl_f {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [Limits.HasZeroObject C] (K : CochainComplex C ℤ) (n i : ℤ) (hi : n ≤ i) :
    IsIso ((stupidTruncGEIncl K n).f i) := by
  dsimp [stupidTruncGEIncl]
  rw [dite_eq_left hi]
  infer_instance

/-- The inclusion of the stupid truncation in degrees `≥ n` is a monomorphism in degree `i + 1`
whenever `n ≤ i`. -/
private theorem mono_stupidTruncGEIncl_f_next {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [Limits.HasZeroObject C] (K : CochainComplex C ℤ) (n i : ℤ) (hi : n ≤ i) :
    Mono ((stupidTruncGEIncl K n).f ((ComplexShape.up ℤ).next i)) := by
  have := isIso_stupidTruncGEIncl_f K n ((ComplexShape.up ℤ).next i)
    (by rw [CochainComplex.next]; omega)
  infer_instance

/-- The inclusion of the stupid truncation in degrees `≥ n` is an isomorphism on cohomology in
every degree `> n`, since it is an isomorphism in the three relevant degrees. -/
public theorem isIso_homologyMap_stupidTruncGEIncl {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : CochainComplex C ℤ) (n i : ℤ) (hi : n < i) :
    IsIso (HomologicalComplex.homologyMap (stupidTruncGEIncl K n) i) := by
  show IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map
      (stupidTruncGEIncl K n)))
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · have := isIso_stupidTruncGEIncl_f K n ((ComplexShape.up ℤ).prev i)
      (by rw [CochainComplex.prev]; omega)
    exact IsIso.epi_of_iso ((stupidTruncGEIncl K n).f ((ComplexShape.up ℤ).prev i))
  · exact isIso_stupidTruncGEIncl_f K n i (by omega)
  · exact mono_stupidTruncGEIncl_f_next K n i hi.le

/-- The inclusion of the stupid truncation in degrees `≥ n` is an epimorphism on cohomology in
degree `n`: it is an isomorphism in degree `n` and a monomorphism in degree `n + 1`. -/
public theorem epi_homologyMap_stupidTruncGEIncl {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    Epi (HomologicalComplex.homologyMap (stupidTruncGEIncl K n) n) := by
  show Epi (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map
      (stupidTruncGEIncl K n)))
  have : IsIso ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map
      (stupidTruncGEIncl K n)).τ₂ := isIso_stupidTruncGEIncl_f K n n le_rfl
  have : Mono ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map
      (stupidTruncGEIncl K n)).τ₃ := mono_stupidTruncGEIncl_f_next K n n le_rfl
  have := ShortComplex.isIso_cyclesMap_of_isIso_of_mono
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map
      (stupidTruncGEIncl K n))
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap _

end CochainComplex

namespace StrictlyPerfect

universe u

variable {Y : AlgebraicGeometry.RingedSpace.{u, u}}

/-- A shift of a strictly perfect complex of `𝒪_Y`-modules is strictly perfect: shifting
reindexes the terms by a translation. -/
public theorem isStrictlyPerfect_shift {P : CochainComplex (OXMod.{u, u} Y) ℤ}
    (hP : IsStrictlyPerfect P) (n : ℤ) : IsStrictlyPerfect (P⟦n⟧) where
  bounded := by
    show {i : ℤ | ¬ IsZero (P.X (i + n))}.Finite
    exact hP.bounded.preimage (add_left_injective n).injOn
  directSummand i := hP.directSummand (i + n)

/-- The stupid truncation in degrees `≥ n` of a strictly perfect complex of `𝒪_Y`-modules is
strictly perfect: in degrees `≥ n` its terms are those of the complex, and below `n` they are
zero. -/
public theorem isStrictlyPerfect_stupidTruncGE {K : CochainComplex (OXMod.{u, u} Y) ℤ}
    (hK : IsStrictlyPerfect K) (n : ℤ) :
    IsStrictlyPerfect (K.stupidTrunc (ComplexShape.embeddingUpIntGE n)) := by
  have hiso : ∀ i : ℤ, n ≤ i →
      Nonempty ((K.stupidTrunc (ComplexShape.embeddingUpIntGE n)).X i ≅ K.X i) := by
    intro i hn
    obtain ⟨k, hk⟩ := Int.le.dest hn
    exact ⟨K.stupidTruncXIso _ (show (ComplexShape.embeddingUpIntGE n).f k = i by
      rw [ComplexShape.embeddingUpIntGE_f]
      exact hk)⟩
  refine ⟨hK.bounded.subset fun i hi hz => ?_, fun i => ?_⟩
  · by_cases hn : n ≤ i
    · exact hi (hz.of_iso (hiso i hn).some)
    · exact hi (CochainComplex.isZero_stupidTruncGE_X K n i (not_le.1 hn))
  · by_cases hn : n ≤ i
    · exact isDirectSummandOfFiniteFree_of_iso (hiso i hn).some (hK.directSummand i)
    · exact isDirectSummandOfFiniteFree_of_isZero
        (CochainComplex.isZero_stupidTruncGE_X K n i (not_le.1 hn))

end StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- A strictly perfect approximation of a complex of `𝒪_U`-modules in degrees `≥ m` restricts to
one over any smaller open subspace: restriction preserves strict perfection and is exact, and the
restriction of the restriction of a complex on `X` is its restriction. -/
public theorem exists_restricted_approximation {U V : Opens X.carrier} (h : V ≤ U)
    (A : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ)
    (P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P) (α : P ⟶ restrictComplex A U)
    (hα : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hα₀ : Epi (HomologicalComplex.homologyMap α m)) :
    ∃ Q : CochainComplex (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) ℤ,
      IsStrictlyPerfect Q ∧
      ∃ β : Q ⟶ restrictComplex A V,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
        Epi (HomologicalComplex.homologyMap β m) :=
  ⟨((restrictModulesOfLE X h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    isStrictlyPerfect_restrictModulesOfLE h hP,
    ((restrictModulesOfLE X h).mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫
      (restrictComplexOfLEIso X h A).hom,
    fun j hj => isIso_homologyMap_comp _ _ j
      (isIso_homologyMap_mapHomologicalComplex _ α j (hα j hj))
      (isIso_homologyMap_iso_hom _ j),
    epi_homologyMap_comp _ _ m
      (epi_homologyMap_mapHomologicalComplex _ α m hα₀) (epi_homologyMap_iso_hom _ m)⟩

/-- Two complexes of `𝒪_X`-modules which are `a`-, resp. `b`-pseudo-coherent have strictly
perfect approximations over a *common* open neighbourhood of any given point: intersect the two
neighbourhoods the definition provides and restrict both approximations to the intersection. -/
public theorem exists_common_approximations (A B : CochainComplex (OXMod.{u, u} X) ℤ) (a b : ℤ)
    (hA : IsPseudoCoherentComplexFrom A a) (hB : IsPseudoCoherentComplexFrom B b)
    (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      (∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        ∃ α : P ⟶ restrictComplex A U,
          (∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
          Epi (HomologicalComplex.homologyMap α a)) ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        ∃ α : P ⟶ restrictComplex B U,
          (∀ j : ℤ, b < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
          Epi (HomologicalComplex.homologyMap α b) := by
  obtain ⟨U, hxU, P, hP, α, hα, hα₀⟩ := hA x
  obtain ⟨V, hxV, Q, hQ, β, hβ, hβ₀⟩ := hB x
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩,
    exists_restricted_approximation inf_le_left A a P hP α hα hα₀,
    exists_restricted_approximation inf_le_right B b Q hQ β hβ hβ₀⟩

/-- The mapping cone of a lift up to homotopy is a strictly perfect approximation of the mapping
cone. Let `γ : 𝒫 ⟶ ℰ` be a morphism of strictly perfect complexes of `𝒪_Y`-modules and let
`α : 𝒫 ⟶ 𝒜`, `β : ℰ ⟶ ℬ` make the square against `f : 𝒜 ⟶ ℬ` commute up to homotopy, with `α` an
isomorphism on cohomology above `m + 1` and an epimorphism in degree `m + 1`, and `β` an
isomorphism on cohomology above `m` and an epimorphism in degree `m`. Then `C(f)` receives a
morphism from a strictly perfect complex which is an isomorphism on cohomology above `m` and an
epimorphism in degree `m`.

The complex is `C(γ)`, which is strictly perfect by Stacks 08C5, and the morphism is the one
induced by the homotopy; the five and four lemmas applied to the long exact cohomology sequences
of the two mapping-cone triangles give the two clauses. Stated separately from
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_mappingCone` so that the cohomological
bookkeeping and the geometry are elaborated in different declarations. -/
public theorem exists_pseudoCoherent_mappingCone_map {Y : RingedSpace.{u, u}}
    {P E A B : CochainComplex (OXMod.{u, u} Y) ℤ} {γ : P ⟶ E} {f : A ⟶ B} {α : P ⟶ A} {β : E ⟶ B}
    (hP : IsStrictlyPerfect P) (hE : IsStrictlyPerfect E) (H : Homotopy (γ ≫ β) (α ≫ f)) (m : ℤ)
    (hα : ∀ j : ℤ, m + 1 < j → IsIso (HomologicalComplex.homologyMap α j))
    (hα₀ : Epi (HomologicalComplex.homologyMap α (m + 1)))
    (hβ : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j))
    (hβ₀ : Epi (HomologicalComplex.homologyMap β m)) :
    ∃ (D : CochainComplex (OXMod.{u, u} Y) ℤ) (_ : IsStrictlyPerfect D)
      (δ : D ⟶ CochainComplex.mappingCone f),
      (∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap δ i)) ∧
      Epi (HomologicalComplex.homologyMap δ m) := by
  refine ⟨CochainComplex.mappingCone γ, isStrictlyPerfect_mappingCone γ hP hE,
    CochainComplex.mappingCone.mapOfHomotopy H, ?_, ?_⟩
  · intro i hi
    refine isIso_homologyMap_mappingCone_of_homotopy H i ?_ (hβ i hi) (hα (i + 1) (by omega)) ?_
    · by_cases heq : i = m + 1
      · subst i
        exact hα₀
      · have := hα i (by omega)
        exact IsIso.epi_of_iso _
    · have := hβ (i + 1) (by omega)
      exact IsIso.mono_of_iso _
  · refine epi_homologyMap_mappingCone_of_homotopy H m hβ₀ hα₀ ?_
    have := hβ (m + 1) (by omega)
    exact IsIso.mono_of_iso _

/-- A strictly perfect approximation of a complex of `𝒪_Y`-modules in degrees `≥ m` can be taken
to vanish in every degree below `m`: replace it by its stupid truncation in degrees `≥ m`, whose
inclusion is an isomorphism on cohomology above `m` and an epimorphism in degree `m`. The open
subspace over which the approximation lives plays no role, so this is stated for an arbitrary
ringed space and an arbitrary target complex. -/
public theorem exists_bounded_approximation {Y : RingedSpace.{u, u}}
    {A P₀ : CochainComplex (OXMod.{u, u} Y) ℤ} (m : ℤ)
    (hP₀ : IsStrictlyPerfect P₀) (α₀ : P₀ ⟶ A)
    (hα₀ : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α₀ j))
    (hα₀epi : Epi (HomologicalComplex.homologyMap α₀ m)) :
    ∃ P : CochainComplex (OXMod.{u, u} Y) ℤ,
      IsStrictlyPerfect P ∧ (∀ j : ℤ, j < m → IsZero (P.X j)) ∧
      ∃ α : P ⟶ A,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m) :=
  ⟨(P₀.restriction (ComplexShape.embeddingUpIntGE m)).extend
      (ComplexShape.embeddingUpIntGE m),
    StrictlyPerfect.isStrictlyPerfect_stupidTruncGE hP₀ m,
    fun j hj => CochainComplex.isZero_stupidTruncGE_X P₀ m j hj,
    CochainComplex.stupidTruncGEIncl P₀ m ≫ α₀,
    fun j hj => isIso_homologyMap_comp _ _ j
      (CochainComplex.isIso_homologyMap_stupidTruncGEIncl P₀ m j hj) (hα₀ j hj),
    epi_homologyMap_comp _ _ m
      (CochainComplex.epi_homologyMap_stupidTruncGEIncl P₀ m) hα₀epi⟩

/-- The mapping cone of the restriction to a smaller open subspace `W ≤ U` of the restriction
to `U` of a morphism `f` of complexes of `𝒪_X`-modules is the restriction to `W` of the mapping
cone of `f`.

Restriction is additive, so it commutes with the mapping cone
(`CochainComplex.mappingCone.mapHomologicalComplexIso`), and restricting to `U` and then to `W`
is restricting to `W` (`AlgebraicGeometry.RingedSpace.restrictComplexOfLEIso`). -/
public def mappingConeRestrictComplexOfLEIso (X : RingedSpace.{u, u}) {U W : Opens X.carrier}
    (hWU : W ≤ U) {A B : CochainComplex (OXMod.{u, u} X) ℤ} (f : A ⟶ B) :
    CochainComplex.mappingCone
        (((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (restrictComplexMap f U)) ≅
      restrictComplex (CochainComplex.mappingCone f) W :=
  (CochainComplex.mappingCone.mapHomologicalComplexIso (restrictComplexMap f U)
      (restrictModulesOfLE X hWU)).symm ≪≫
    ((restrictModulesOfLE X hWU).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso f (restrictModules X U)).symm ≪≫
    restrictComplexOfLEIso X hWU (CochainComplex.mappingCone f)

/-- **The content of Stacks 08CD.** The mapping cone of a morphism `f : 𝒜 ⟶ ℬ` of complexes of
`𝒪_X`-modules with `𝒜` `(m + 1)`-pseudo-coherent and `ℬ` `m`-pseudo-coherent is
`m`-pseudo-coherent.

Over a common open neighbourhood `U` of a given point take strictly perfect approximations
`α₀ : 𝒫₀ ⟶ 𝒜|_U` in degrees `≥ m + 1` and `β : 𝒬 ⟶ ℬ|_U` in degrees `≥ m`. Replacing `𝒫₀` by its
stupid truncation `𝒫` in degrees `≥ m + 1` does not change the first clause and makes `𝒫` vanish
below `m + 1`, so Stacks 08C8 lifts `α ≫ f|_U` through `β` up to homotopy over a smaller open
`W` (`AlgebraicGeometry.RingedSpace.exists_local_lift_homotopy_of_le`), by some `γ`. The induced
morphism of mapping cones `C(γ) ⟶ C(f)|_W` is an isomorphism on cohomology above `m` and an
epimorphism in degree `m` by the five lemma
(`CategoryTheory.isIso_homologyMap_mappingCone_of_homotopy`), and `C(γ)` is strictly perfect by
Stacks 08C5. -/
public theorem isPseudoCoherentComplexFrom_mappingCone
    {A B : CochainComplex (OXMod.{u, u} X) ℤ} (f : A ⟶ B) (m : ℤ)
    (hA : IsPseudoCoherentComplexFrom A (m + 1)) (hB : IsPseudoCoherentComplexFrom B m) :
    IsPseudoCoherentComplexFrom (CochainComplex.mappingCone f) m := by
  intro x
  obtain ⟨U, hxU, ⟨P₀, hP₀, α₀, hα₀, hα₀epi⟩, Q, hQ, β, hβ, hβepi⟩ :=
    exists_common_approximations A B (m + 1) m hA hB x
  obtain ⟨P, hP, hPbound, α, hα, hαepi⟩ :=
    exists_bounded_approximation (m + 1) hP₀ α₀ hα₀ hα₀epi
  -- Lift `α ≫ f|_U` through `β` over an open neighbourhood `W ≤ U` of the point.
  obtain ⟨W, hWU, hxW, γ, ⟨H⟩⟩ := exists_local_lift_homotopy_of_le
    (α ≫ restrictComplexMap f U) β (m + 1) hP hPbound (fun j hj => hβ j (by omega))
    (by have := hβ (m + 1) (by omega); exact IsIso.epi_of_iso _) x hxU
  -- The cone of the lift is the required strictly perfect approximation.
  obtain ⟨D, hD, δ, hδ, hδepi⟩ := exists_pseudoCoherent_mappingCone_map
    (isStrictlyPerfect_restrictModulesOfLE hWU hP) (isStrictlyPerfect_restrictModulesOfLE hWU hQ)
    (H.trans (Homotopy.ofEq (Functor.map_comp _ _ _))) m
    (fun j hj => isIso_homologyMap_mapHomologicalComplex _ α j (hα j hj))
    (epi_homologyMap_mapHomologicalComplex _ α (m + 1) hαepi)
    (fun j hj => isIso_homologyMap_mapHomologicalComplex _ β j (hβ j hj))
    (epi_homologyMap_mapHomologicalComplex _ β m hβepi)
  exact ⟨W, hxW, D, hD, δ ≫ (mappingConeRestrictComplexOfLEIso X hWU f).hom,
    fun j hj => isIso_homologyMap_comp _ _ j (hδ j hj) (isIso_homologyMap_iso_hom _ j),
    epi_homologyMap_comp _ _ m hδepi (epi_homologyMap_iso_hom _ m)⟩

/-- Shifting a complex of `𝒪_X`-modules by `n` shifts the pseudo-coherence bound by `-n`: the
shift of a strictly perfect approximation approximates the shift. -/
@[sga "6 I 2.5" "a), bounded clause"]
public theorem IsPseudoCoherentComplexFrom.shift {A : CochainComplex (OXMod.{u, u} X) ℤ} {m : ℤ}
    (hA : IsPseudoCoherentComplexFrom A m) (n : ℤ) :
    IsPseudoCoherentComplexFrom (A⟦n⟧) (m - n) := by
  intro x
  obtain ⟨U, hx, P, hP, α, hα, hα₀⟩ := hA x
  refine ⟨U, hx, P⟦n⟧, isStrictlyPerfect_shift hP n,
    (α⟦n⟧') ≫ ((((restrictModules X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).commShiftIso n).app A).symm.hom, ?_, ?_⟩
  · refine fun j hj => isIso_homologyMap_comp _ _ j ?_ (isIso_homologyMap_iso_hom _ j)
    exact (NatIso.isIso_map_iff
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso n j (n + j) rfl)
      α).mpr (hα (n + j) (by omega))
  · refine epi_homologyMap_comp _ _ (m - n) ?_ (epi_homologyMap_iso_hom _ (m - n))
    exact (NatIso.epi_map_iff
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso n (m - n) m
        (by omega)) α).mpr hα₀

variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- Shifting an object of the derived category of `𝒪_X`-modules by `n` shifts the
pseudo-coherence bound by `-n`. -/
public theorem IsPseudoCoherentFrom.shift {A : DerivedCategory (OXMod.{u, u} X)} {m : ℤ}
    (hA : IsPseudoCoherentFrom A m) (n : ℤ) : IsPseudoCoherentFrom (A⟦n⟧) (m - n) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hA
  exact ⟨P⟦n⟧, hP.shift n,
    ⟨(DerivedCategory.Q.commShiftIso n).app P ≪≫ (shiftFunctor _ n).mapIso e⟩⟩

/-- `m`-pseudo-coherence of an object of the derived category only depends on its isomorphism
class. -/
public theorem IsPseudoCoherentFrom.ofIso {A B : DerivedCategory (OXMod.{u, u} X)} {m : ℤ}
    (hA : IsPseudoCoherentFrom A m) (e : A ≅ B) : IsPseudoCoherentFrom B m := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := hA
  exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩

/-- A distinguished triangle whose first two terms are `(m + 1)`-, resp. `m`-pseudo-coherent is
isomorphic to the image of the mapping-cone triangle of a morphism of complexes whose source and
target are `(m + 1)`-, resp. `m`-pseudo-coherent *as complexes*, by Stacks 08CC part (2). -/
public theorem exists_pseudoCoherent_cone_model (m : ℤ)
    (T : Triangle (DerivedCategory (OXMod.{u, u} X))) (hT : T ∈ distinguishedTriangles)
    (hK : IsPseudoCoherentFrom T.obj₁ (m + 1)) (hL : IsPseudoCoherentFrom T.obj₂ m) :
    ∃ (A B : CochainComplex (OXMod.{u, u} X) ℤ) (f : A ⟶ B),
      Nonempty (T ≅ DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) ∧
      IsPseudoCoherentComplexFrom A (m + 1) ∧ IsPseudoCoherentComplexFrom B m := by
  obtain ⟨A, B, f, ⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T).mp hT
  exact ⟨A, B, f, ⟨e⟩,
    isPseudoCoherentComplexFrom_of_iso T.obj₁ (m + 1) hK A (asIso e.hom.hom₁).symm,
    isPseudoCoherentComplexFrom_of_iso T.obj₂ m hL B (asIso e.hom.hom₂).symm⟩

/-- **Stacks 08CD, part (1).** If the first term of a distinguished triangle in the derived
category of `𝒪_X`-modules is `(m + 1)`-pseudo-coherent and the second is `m`-pseudo-coherent,
then the third is `m`-pseudo-coherent. -/
@[stacks 08CD "part (1)"]
public theorem isPseudoCoherentFrom_obj₃_of_distinguished (m : ℤ)
    (T : Triangle (DerivedCategory (OXMod.{u, u} X))) (hT : T ∈ distinguishedTriangles)
    (hK : IsPseudoCoherentFrom T.obj₁ (m + 1)) (hL : IsPseudoCoherentFrom T.obj₂ m) :
    IsPseudoCoherentFrom T.obj₃ m := by
  obtain ⟨A, B, f, ⟨e⟩, hA, hB⟩ := exists_pseudoCoherent_cone_model m T hT hK hL
  exact ⟨CochainComplex.mappingCone f, isPseudoCoherentComplexFrom_mappingCone f m hA hB,
    ⟨(asIso e.hom.hom₃).symm⟩⟩

/-- **Stacks 08CD, part (2).** If the first and third terms of a distinguished triangle in the
derived category of `𝒪_X`-modules are `m`-pseudo-coherent, then so is the second.

Apply part (1) to the inverse rotation of the triangle, whose first two terms are `M[-1]` and
`K`. -/
@[stacks 08CD "part (2)", sga "6 I 2.5" "b), ringed space"]
public theorem isPseudoCoherentFrom_obj₂_of_distinguished (m : ℤ)
    (T : Triangle (DerivedCategory (OXMod.{u, u} X))) (hT : T ∈ distinguishedTriangles)
    (hK : IsPseudoCoherentFrom T.obj₁ m) (hM : IsPseudoCoherentFrom T.obj₃ m) :
    IsPseudoCoherentFrom T.obj₂ m := by
  refine isPseudoCoherentFrom_obj₃_of_distinguished m T.invRotate
    (inv_rot_of_distTriang T hT) ?_ hK
  simpa using hM.shift (-1)

/-- **Stacks 08CD, part (3).** If the second term of a distinguished triangle in the derived
category of `𝒪_X`-modules is `(m + 1)`-pseudo-coherent and the third is `m`-pseudo-coherent, then
the first is `(m + 1)`-pseudo-coherent.

Apply part (1) to the rotation of the triangle, whose third term is `K[1]`. -/
@[stacks 08CD "part (3)"]
public theorem isPseudoCoherentFrom_obj₁_of_distinguished (m : ℤ)
    (T : Triangle (DerivedCategory (OXMod.{u, u} X))) (hT : T ∈ distinguishedTriangles)
    (hL : IsPseudoCoherentFrom T.obj₂ (m + 1)) (hM : IsPseudoCoherentFrom T.obj₃ m) :
    IsPseudoCoherentFrom T.obj₁ (m + 1) := by
  have h := isPseudoCoherentFrom_obj₃_of_distinguished m T.rotate (rot_of_distTriang T hT) hL hM
  have h' : IsPseudoCoherentFrom (T.obj₁⟦(1 : ℤ)⟧⟦(-1 : ℤ)⟧) (m + 1) := by
    simpa using h.shift (-1)
  exact h'.ofIso (shiftShiftNeg T.obj₁ (1 : ℤ))

end AlgebraicGeometry.RingedSpace

end
