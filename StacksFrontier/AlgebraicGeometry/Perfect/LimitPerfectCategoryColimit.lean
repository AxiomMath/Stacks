module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitPerfectObjectsDescent
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
import StacksCore.Tactic.StacksAttribute

/-!
# The category of perfect objects over a directed limit of schemes

In the situation of [Stacks, Tag 09RD] — a directed inverse system `i ↦ S_i` of quasi-compact and
quasi-separated schemes with affine transition morphisms `f_{ji} : S_j ⟶ S_i`, with limit `S`
and projections `f_i : S ⟶ S_i` — [Stacks, Tag 09RF] asserts that the category of perfect objects
of `D(𝒪_S)` is the colimit of the categories of perfect objects of the `D(𝒪_{S_i})`.

For a directed system of categories this is the conjunction of two statements about the
comparison functor out of the colimit, which are the two clauses of
`AlgebraicGeometry.DescentSituation.perfect_isColimit`:

* *essential surjectivity*: every perfect object of `D(𝒪_S)` is isomorphic to `Lf_i^*E_i` for
  some stage `i` and some perfect `E_i` on `S_i`;
* *full faithfulness*: for perfect `E_i` and `K_i` on a stage `S_i`, the group
  `Hom_{D(𝒪_S)}(Lf_i^*E_i, Lf_i^*K_i)` is the filtered colimit over `j ≥ i` of the groups
  `Hom_{D(𝒪_{S_j})}(Lf_{ji}^*E_i, Lf_{ji}^*K_i)`.

## Main definitions

* `AlgebraicGeometry.DescentSituation.atStage` — the same situation with its chosen index moved
  to a stage `i`.

## Main results

* `AlgebraicGeometry.DescentSituation.perfect_isColimit` — **[Stacks, Tag 09RF]**.
* `AlgebraicGeometry.DescentSituation.exists_transition_iso_of_projection_iso` — an isomorphism
  between the pullbacks to `S` of two perfect objects of a stage `S_i` already exists between
  their pullbacks to some stage `S_j`, `j ≥ i`; the consequence of full faithfulness that the
  source's applications use.

## Implementation notes

Full faithfulness is [Stacks, Tag 09RE] (`AlgebraicGeometry.DescentSituation.isHomColimit`) at
the situation re-based at the stage `i`, since a perfect object has quasi-coherent cohomology
(`AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect`). Essential
surjectivity is `AlgebraicGeometry.DescentSituation.exists_isPerfect_derivedPullback_iso`.

The descent of an isomorphism uses the colimit of homomorphism groups three times: lift the
isomorphism and its inverse to some stage, and observe that the two composites agree with the
identities after pullback to `S`, hence at some later stage. The maps of the colimit system are
conjugations of derived pullback by fixed isomorphisms, so they respect composition and
identities; this is `conj_comp` and `conj_id`, stated for an arbitrary functor because on the
concrete categories of modules the category instances `Functor.map_comp` would need do not
unify syntactically (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent.lean`).

The index set lies in the universe of the schemes, as in [Stacks, Tag 09RE]; over a larger
index set that lemma fails (`AlgebraicGeometry.DescentSituation.exists_not_isHomColimit`).

## References

* [Stacks Project, Lemma 36.29.3 (Tag 09RF)](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Situation 36.29.1 (Tag 09RD)](https://stacks.math.columbia.edu/tag/09RD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace AlgebraicGeometry.DescentSituation

attribute [local instance 10000] HasDerivedCategory.standard

section Conj

variable {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C')

/-- Conjugating the images of a functor by fixed isomorphisms respects composition. -/
theorem conj_comp {a b c : C} {a' b' c' : C'} (ea : F.obj a ≅ a') (eb : F.obj b ≅ b')
    (ec : F.obj c ≅ c') (g : a ⟶ b) (h : b ⟶ c) :
    (ea.inv ≫ F.map g ≫ eb.hom) ≫ (eb.inv ≫ F.map h ≫ ec.hom) =
      ea.inv ≫ F.map (g ≫ h) ≫ ec.hom := by
  simp

/-- Conjugating the images of a functor by fixed isomorphisms respects identities. -/
theorem conj_id {a : C} {a' : C'} (ea : F.obj a ≅ a') : ea.inv ≫ F.map (𝟙 a) ≫ ea.hom = 𝟙 a' := by
  simp

end Conj

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation.{u, u} I)

/-- **The situation re-based at the stage `i`**: the same system, limit and projections, with
the chosen index moved to `i`. -/
abbrev atStage (i : I) : DescentSituation.{u, u} I := { D with base := i }

variable {D}

section HomColimit

variable {D' : DescentSituation.{u, u} I} (E₀ F₀ G₀ : DerivedCategory (D'.stage D'.base).Modules)

/-- The transition map `homTransition` for `i ≤ j` is compatible with composition of morphisms. -/
theorem homTransition_comp (i j : D'.Stages) (h : i ≤ j) (g : stageObj E₀ i ⟶ stageObj F₀ i)
    (g' : stageObj F₀ i ⟶ stageObj G₀ i) :
    homTransition E₀ F₀ i j h g ≫ homTransition F₀ G₀ i j h g' =
      homTransition E₀ G₀ i j h (g ≫ g') :=
  conj_comp (derivedPullback (D'.transition (show i.1 ≤ j.1 from h)).toLRSHom.toShHom)
    ((stageComp h).app E₀) ((stageComp h).app F₀) ((stageComp h).app G₀) g g'

/-- The transition map `homTransition` for `i ≤ j` sends an identity morphism to the identity. -/
theorem homTransition_id (i j : D'.Stages) (h : i ≤ j) :
    homTransition E₀ E₀ i j h (𝟙 _) = 𝟙 _ :=
  conj_id (derivedPullback (D'.transition (show i.1 ≤ j.1 from h)).toLRSHom.toShHom)
    ((stageComp h).app E₀)

/-- The map `homProjection` at the stage `i` is compatible with composition of morphisms. -/
theorem homProjection_comp (i : D'.Stages) (g : stageObj E₀ i ⟶ stageObj F₀ i)
    (g' : stageObj F₀ i ⟶ stageObj G₀ i) :
    homProjection E₀ F₀ i g ≫ homProjection F₀ G₀ i g' = homProjection E₀ G₀ i (g ≫ g') :=
  conj_comp (derivedPullback (D'.projection i.1).toLRSHom.toShHom)
    ((projComp i).app E₀) ((projComp i).app F₀) ((projComp i).app G₀) g g'

/-- The map `homProjection` at the stage `i` sends an identity morphism to the identity. -/
theorem homProjection_id (i : D'.Stages) : homProjection E₀ E₀ i (𝟙 _) = 𝟙 _ :=
  conj_id (derivedPullback (D'.projection i.1).toLRSHom.toShHom) ((projComp i).app E₀)

end HomColimit

/-- **Full faithfulness in [Stacks, Tag 09RF].** For perfect objects `E` and `K` of
`D(𝒪_{S_i})`, `Hom_{D(𝒪_S)}(Lf_i^*E, Lf_i^*K)` is the filtered colimit over the stages `j ≥ i`
of `Hom_{D(𝒪_{S_j})}(Lf_{ji}^*E, Lf_{ji}^*K)`. This is [Stacks, Tag 09RE] at the situation
re-based at `i`. -/
theorem isHomColimit_of_isPerfect (i : I) (E K : DerivedCategory (D.stage i).Modules)
    (hE : IsPerfect (X := (D.stage i).toRingedSpace) E)
    (hK : IsPerfect (X := (D.stage i).toRingedSpace) K) :
    IsHomColimit (D := D.atStage i) E K :=
  isHomColimit (D := D.atStage i) E K (Or.inl ⟨hE, fun n =>
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect (D.stage i) K hK n⟩)

/-- **An isomorphism over the limit descends to a stage.** Let `E` and `F` be perfect objects of
`D(𝒪_{S_i})` whose derived pullbacks to `S` are isomorphic. Then their derived pullbacks to some
stage `S_j`, `j ≥ i`, are already isomorphic. -/
theorem exists_transition_iso_of_projection_iso (i : I) (E F : DerivedCategory (D.stage i).Modules)
    (hE : IsPerfect (X := (D.stage i).toRingedSpace) E)
    (hF : IsPerfect (X := (D.stage i).toRingedSpace) F)
    (e : Nonempty ((derivedPullback (D.projection i).toLRSHom.toShHom).obj E ≅
      (derivedPullback (D.projection i).toLRSHom.toShHom).obj F)) :
    ∃ (j : I) (hij : i ≤ j), Nonempty ((derivedPullback (D.transition hij).toLRSHom.toShHom).obj E ≅
      (derivedPullback (D.transition hij).toLRSHom.toShHom).obj F) := by
  obtain ⟨φ⟩ := e
  have hEF := isHomColimit_of_isPerfect i E F hE hF
  have hFE := isHomColimit_of_isPerfect i F E hF hE
  have hEE := isHomColimit_of_isPerfect i E E hE hE
  have hFF := isHomColimit_of_isPerfect i F F hF hF
  unfold IsHomColimit at hEF hFE hEE hFF
  obtain ⟨j₁, a, ha⟩ := hEF.exists_stage φ.hom
  obtain ⟨j₂, b, hb⟩ := hFE.exists_stage φ.inv
  obtain ⟨k, hk₁, hk₂⟩ := (isDirectedStages (D := D.atStage i)).directed j₁ j₂
  let a' := homTransition (D := D.atStage i) E F j₁ k hk₁ a
  let b' := homTransition (D := D.atStage i) F E j₂ k hk₂ b
  have ha' : homProjection (D := D.atStage i) E F k a' = φ.hom :=
    (hEF.ι_trans j₁ k hk₁ a).trans ha
  have hb' : homProjection (D := D.atStage i) F E k b' = φ.inv :=
    (hFE.ι_trans j₂ k hk₂ b).trans hb
  obtain ⟨l₁, hl₁, h₁⟩ := hEE.exists_trans_eq k (a' ≫ b') (𝟙 _) (by
    rw [← homProjection_comp, ha', hb', homProjection_id]
    exact φ.hom_inv_id)
  obtain ⟨l₂, hl₂, h₂⟩ := hFF.exists_trans_eq k (b' ≫ a') (𝟙 _) (by
    rw [← homProjection_comp, ha', hb', homProjection_id]
    exact φ.inv_hom_id)
  obtain ⟨m, hm₁, hm₂⟩ := (isDirectedStages (D := D.atStage i)).directed l₁ l₂
  have e₁ : homTransition (D := D.atStage i) E E k m (hl₁.trans hm₁) (a' ≫ b') = 𝟙 _ := by
    rw [← homTransition_homTransition (D := D.atStage i) E E k l₁ m hl₁ hm₁, h₁,
      homTransition_id, homTransition_id]
  have e₂ : homTransition (D := D.atStage i) F F k m (hl₂.trans hm₂) (b' ≫ a') = 𝟙 _ := by
    rw [← homTransition_homTransition (D := D.atStage i) F F k l₂ m hl₂ hm₂, h₂,
      homTransition_id, homTransition_id]
  refine ⟨m.1, m.2, ⟨⟨homTransition (D := D.atStage i) E F k m (hl₁.trans hm₁) a',
    homTransition (D := D.atStage i) F E k m (hl₁.trans hm₁) b', ?_, ?_⟩⟩⟩
  · exact (homTransition_comp (D' := D.atStage i) E F E k m _ a' b').trans e₁
  · exact (homTransition_comp (D' := D.atStage i) F E F k m _ b' a').trans e₂

/-- **[Stacks, Tag 09RF].** In the situation of [Stacks, Tag 09RD], the category of perfect
objects of `D(𝒪_S)` is the colimit of the categories of perfect objects of `D(𝒪_{S_i})`: the
comparison functor out of the colimit, induced by derived pullback along the projections, is

1. essentially surjective — every perfect object of `D(𝒪_S)` is isomorphic to the derived
   pullback of a perfect object of `D(𝒪_{S_i})` for some `i`; and
2. fully faithful — for perfect `E` and `K` on a stage `S_i`, the group
   `Hom_{D(𝒪_S)}(Lf_i^*E, Lf_i^*K)` is the filtered colimit over `j ≥ i` of the groups
   `Hom_{D(𝒪_{S_j})}(Lf_{ji}^*E, Lf_{ji}^*K)`.

A morphism of the colimit category between objects living at two stages is a morphism after
pullback to a common later stage, so the second clause, stated for two objects of one stage, is
the whole of full faithfulness. -/
@[stacks 09RF]
theorem perfect_isColimit :
    (∀ (E : DerivedCategory D.limitScheme.Modules),
      IsPerfect (X := D.limitScheme.toRingedSpace) E →
      ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (D.stage i).Modules),
        IsPerfect (X := (D.stage i).toRingedSpace) Eᵢ ∧
          Nonempty ((derivedPullback (D.projection i).toLRSHom.toShHom).obj Eᵢ ≅ E)) ∧
    (∀ (i : I) (E K : DerivedCategory (D.stage i).Modules),
      IsPerfect (X := (D.stage i).toRingedSpace) E →
      IsPerfect (X := (D.stage i).toRingedSpace) K → IsHomColimit (D := D.atStage i) E K) :=
  ⟨fun E hE => D.exists_isPerfect_derivedPullback_iso E hE,
    fun i E K hE hK => isHomColimit_of_isPerfect i E K hE hK⟩

end AlgebraicGeometry.DescentSituation

end
