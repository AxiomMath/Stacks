module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening

/-!
# Sections of an étale scheme across a thickening

Let `i : S₀ ⟶ S` be a closed immersion of schemes which is surjective on points — a thickening,
of unbounded order — and let `g : E ⟶ S` be étale. Stacks 039R says that base change along `i`
is an equivalence from the category of schemes étale over `S` to the category of schemes étale
over `S₀`. This file records the consequence of that equivalence for *sections*: a section of
`g` over `S₀`, that is a morphism `σ₀ : S₀ ⟶ E` with `σ₀ ≫ g = i`, extends to a section of `g`
over `S` in exactly one way.

## Main results

* `Stacks.Etale.existsUnique_section_of_isClosedImmersion_of_surjective`: the unique extension.

## Implementation notes

The equivalence of Stacks 039R is an equivalence of the categories
`AlgebraicGeometry.Scheme.Etale`, so the statement about sections is the statement about
morphisms out of the *identity object* `𝟙 S`, which base change sends to the étale `S₀`-scheme
`S ×_S S₀` rather than to `𝟙 S₀` on the nose. Rather than build the comparison isomorphism —
which needs `IsIso (pullback.snd (𝟙 S) i)` for the `HasPullback` instance that
`MorphismProperty.Over.pullback` happens to pick, and instance resolution does not see through
that choice — the proof uses the canonical morphism `S₀ ⟶ S ×_S S₀` with components `i` and
`𝟙 S₀`, which is a retraction of the second projection. Composing with it is enough to recover
`i ≫ σ` from the base-changed morphism, and that is all the argument needs in either direction.

For the same reason the proof uses `Eq.trans` and `exact` throughout and never `rw` on a goal
mentioning base change: in these `MorphismProperty.Over` terms the morphism property `@Etale`
appears without its coercion to `CategoryTheory.MorphismProperty`, so the motive `rw` builds is
not type-correct.

## What this is for

The unbounded case of Stacks 05ZH on algebraic spaces. The lifting theorem of Stacks 0611 is
available at every finite order
(`AlgebraicGeometry.Space.FormallyEtale.existsUnique_lift_of_isNthOrderThickening`) and not for
a thickening whose defining ideal is nil but not nilpotent, because formal étaleness is a
condition about square-zero extensions only. For a target that is *étale*, and not merely
formally étale, the order is no obstacle: this lemma is the order-free replacement, on schemes.

Its counterpart on algebraic spaces is
`AlgebraicGeometry.Space.existsUnique_section_of_isThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleSection.lean`, which is proved
without passing through charts at all: a section of an étale morphism is an open immersion, and
the open subspaces of a thickening are those of the ambient space by Stacks 05ZP, which carries
no order hypothesis. That is what gives Stacks 05ZH at unbounded order,
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening_range`.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Etale

variable {S₀ S : Scheme.{u}}

/-- **A section of an étale morphism over a thickening extends uniquely.** Let `i : S₀ ⟶ S` be a
closed immersion which is surjective on points, and let `g : E ⟶ S` be étale. Then every
morphism `σ₀ : S₀ ⟶ E` with `σ₀ ≫ g = i` is the restriction along `i` of exactly one section of
`g` over `S`.

No bound on the order of the thickening is assumed: `i` is an arbitrary surjective closed
immersion. The statement is the equivalence of Stacks 039R,
`Stacks.Etale.etalePullback_isEquivalence_of_surjective_isClosedImmersion`, read on morphisms out
of the identity object of the étale site of `S`. -/
theorem existsUnique_section_of_isClosedImmersion_of_surjective (i : S₀ ⟶ S)
    [IsClosedImmersion i] (hi : Function.Surjective i.base)
    {E : Scheme.{u}} (g : E ⟶ S) [Etale g] (σ₀ : S₀ ⟶ E) (hσ₀ : σ₀ ≫ g = i) :
    ∃! σ : S ⟶ E, σ ≫ g = 𝟙 S ∧ i ≫ σ = σ₀ := by
  let : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) i := ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  set F : S.Etale ⥤ S₀.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ i
  have hF : F.IsEquivalence :=
    etalePullback_isEquivalence_of_surjective_isClosedImmersion i hi
  have := hF.full
  have := hF.faithful
  set A : S.Etale := Scheme.Etale.mk (𝟙 S)
  set Bo : S.Etale := Scheme.Etale.mk g
  -- `pullback (𝟙 S) i` has a canonical section over `S₀`.
  have hfstsnd : pullback.fst (𝟙 S) i = pullback.snd (𝟙 S) i ≫ i := by
    simpa using pullback.condition (f := (𝟙 S)) (g := i)
  have hl₁ : pullback.lift (f := (𝟙 S)) (g := i) i (𝟙 S₀) (by simp) ≫ pullback.fst (𝟙 S) i
      = i := pullback.lift_fst _ _ _
  have hl₂ : pullback.lift (f := (𝟙 S)) (g := i) i (𝟙 S₀) (by simp) ≫ pullback.snd (𝟙 S) i
      = 𝟙 S₀ := pullback.lift_snd _ _ _
  -- The two components of base change, on a morphism out of the identity object.
  have hmapfst : ∀ a : A ⟶ Bo,
      (F.map a).left ≫ pullback.fst g i = pullback.fst (𝟙 S) i ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  have hmapsnd : ∀ a : A ⟶ Bo,
      (F.map a).left ≫ pullback.snd g i = pullback.snd (𝟙 S) i :=
    fun a ↦ MorphismProperty.Over.w (F.map a)
  -- The morphism of étale sites built from `σ₀`.
  have hτcond : (pullback.snd (𝟙 S) i ≫ σ₀) ≫ g = pullback.snd (𝟙 S) i ≫ i := by
    rw [Category.assoc, hσ₀]
  set τ : F.obj A ⟶ F.obj Bo :=
    MorphismProperty.Over.homMk
      (pullback.lift (pullback.snd (𝟙 S) i ≫ σ₀) (pullback.snd (𝟙 S) i) hτcond)
      (pullback.lift_snd _ _ _)
  have hτfst : τ.left ≫ pullback.fst g i = pullback.snd (𝟙 S) i ≫ σ₀ :=
    pullback.lift_fst _ _ _
  have hτsnd : τ.left ≫ pullback.snd g i = pullback.snd (𝟙 S) i :=
    pullback.lift_snd _ _ _
  -- A section restricting to `σ₀` is exactly a morphism `A ⟶ Bo` whose base change is `τ`.
  have hkey : ∀ (σ : S ⟶ E) (hσ : σ ≫ g = 𝟙 S),
      (i ≫ σ = σ₀ ↔
        F.map (MorphismProperty.Over.homMk (A := A) (B := Bo) σ hσ) = τ) := by
    intro σ hσ
    constructor
    · intro h
      have hmid : pullback.fst (𝟙 S) i ≫ σ = pullback.snd (𝟙 S) i ≫ σ₀ := by
        rw [hfstsnd, Category.assoc, h]
      refine MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)
      · exact ((hmapfst _).trans hmid).trans hτfst.symm
      · exact (hmapsnd _).trans hτsnd.symm
    · intro h
      have h' : pullback.fst (𝟙 S) i ≫ σ = pullback.snd (𝟙 S) i ≫ σ₀ :=
        ((hmapfst (MorphismProperty.Over.homMk (A := A) (B := Bo) σ hσ)).symm.trans
          (congrArg (fun φ : F.obj A ⟶ F.obj Bo ↦ φ.left ≫ pullback.fst g i) h)).trans hτfst
      have h'' := congrArg
        (fun φ : pullback (𝟙 S) i ⟶ E ↦ pullback.lift (f := (𝟙 S)) (g := i) i (𝟙 S₀) (by simp)
          ≫ φ) h'
      simp only [← Category.assoc, hl₁, hl₂, Category.id_comp] at h''
      exact h''
  obtain ⟨a, ha⟩ := Functor.Full.map_surjective (F := F) τ
  have haw : a.left ≫ g = 𝟙 S := MorphismProperty.Over.w a
  have hrepack : MorphismProperty.Over.homMk (A := A) (B := Bo) a.left haw = a :=
    MorphismProperty.Over.Hom.ext rfl
  have ha' : F.map (MorphismProperty.Over.homMk (A := A) (B := Bo) a.left haw) = τ :=
    (congrArg F.map hrepack).trans ha
  refine ⟨a.left, ⟨haw, (hkey a.left haw).2 ha'⟩, ?_⟩
  rintro σ ⟨hσ, hσi⟩
  exact congrArg (fun φ : A ⟶ Bo ↦ φ.left) (F.map_injective (((hkey σ hσ).1 hσi).trans ha'.symm))

end Stacks.Etale

end
