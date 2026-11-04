module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree

/-!
# Topological properties across a morphism of thickenings

A *morphism of thickenings* is a commutative square

```
X --φ.left--→ S
|             |
i             j
↓             ↓
X' -φ.right-→ S'
```

in which `i` and `j` are thickenings, that is a morphism `φ` in the arrow category of schemes
whose source and target arrows are thickenings. Since `i` and `j` are homeomorphisms on points
— universal homeomorphisms, even — the vertical morphisms `φ.left` and `φ.right` have the same
topology, and every property of a morphism of schemes that only depends on the topology of its
base changes holds for one exactly when it holds for the other.

This file records that equivalence for quasi-compactness, surjectivity, universal closedness,
universal injectivity and universal openness.

## Main results

* `Stacks.Thickenings.quasiCompact_left_iff_right`
* `Stacks.Thickenings.surjective_left_iff_right`
* `Stacks.Thickenings.universallyClosed_left_iff_right`
* `Stacks.Thickenings.universallyInjective_left_iff_right`
* `Stacks.Thickenings.universallyOpen_left_iff_right`

each comparing the two vertical morphisms of a morphism of thickenings.

## Implementation notes

The square is a `CategoryTheory.Arrow.Hom`, so its commutativity is the field `w` and no
separate hypothesis is needed. For quasi-compactness the two underlying maps are compared
through the homeomorphisms induced by `i` and `j`; for the three universal properties the
argument is a cancellation along a universal homeomorphism, using
`Stacks.Thickenings.IsThickening.universalHomeomorphism` and the two-out-of-three property of
universal homeomorphisms.

## References

* [Stacks Project, Tag 09ZV](https://stacks.math.columbia.edu/tag/09ZV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

/-- The commutativity of a square of schemes, evaluated on points. -/
private theorem apply_left_eq_apply_right {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (φ : Arrow.mk i ⟶ Arrow.mk j) (x : X) : j (φ.left x) = φ.right (i x) := by
  have hcomm : φ.left ≫ j = i ≫ φ.right := φ.w
  simpa only [← Scheme.Hom.comp_apply] using congrArg (fun k : X ⟶ S' => k x) hcomm

/-- Quasi-compactness is preserved and reflected by a morphism of thickenings. -/
@[stacks 09ZV "quasi_compact"]
theorem quasiCompact_left_iff_right
    {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (φ : Arrow.mk i ⟶ Arrow.mk j)
    (hi : IsThickening i) (hj : IsThickening j) :
    QuasiCompact φ.left ↔ QuasiCompact φ.right := by
  have hI : IsHomeomorph i.base := MorphismProperty.universally_le _ _
    (IsThickening.universalHomeomorphism hi).universally_isHomeomorph
  have hJ : IsHomeomorph j.base := MorphismProperty.universally_le _ _
    (IsThickening.universalHomeomorphism hj).universally_isHomeomorph
  have hw := apply_left_eq_apply_right φ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hEq : (φ.right : X' → S') = (j : S → S') ∘ φ.left ∘ hI.homeomorph.symm := by
      funext x
      calc
        φ.right x = φ.right (i (hI.homeomorph.symm x)) :=
          congrArg φ.right (hI.homeomorph.apply_symm_apply x).symm
        _ = j (φ.left (hI.homeomorph.symm x)) := (hw _).symm
    rw [quasiCompact_iff_isSpectralMap, hEq]
    exact hJ.homeomorph.isProperMap.isSpectralMap.comp
      (quasiCompact_iff_isSpectralMap.mp h |>.comp
        hI.homeomorph.symm.isProperMap.isSpectralMap)
  · have hEq : (φ.left : X → S) = (hJ.homeomorph.symm : S' → S) ∘ φ.right ∘ i := by
      funext x
      apply hJ.homeomorph.injective
      calc
        j (φ.left x) = φ.right (i x) := hw x
        _ = j (hJ.homeomorph.symm (φ.right (i x))) :=
          (hJ.homeomorph.apply_symm_apply _).symm
    rw [quasiCompact_iff_isSpectralMap, hEq]
    exact hJ.homeomorph.symm.isProperMap.isSpectralMap.comp
      (quasiCompact_iff_isSpectralMap.mp h |>.comp hI.homeomorph.isProperMap.isSpectralMap)

/-- The two vertical maps in a morphism of thickenings are simultaneously surjective. -/
@[stacks 09ZV "surjective"]
theorem surjective_left_iff_right
    {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j)
    (f : Arrow.mk i ⟶ Arrow.mk j) :
    Surjective f.left ↔ Surjective f.right := by
  rw [surjective_iff, surjective_iff]
  constructor
  · intro hf y'
    obtain ⟨y, rfl⟩ := hj.2 y'
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨i x, (apply_left_eq_apply_right f x).symm⟩
  · intro hf y
    obtain ⟨x', hx'⟩ := hf (j y)
    obtain ⟨x, hx⟩ := hi.2 x'
    exact ⟨x, hj.1.isClosedEmbedding.injective
      (by rw [apply_left_eq_apply_right f x, hx, hx'])⟩

/-- Universal closedness is invariant under a morphism of thickenings. -/
@[stacks 09ZV "universally_closed"]
theorem universallyClosed_left_iff_right {i j : Arrow Scheme.{u}} (φ : i ⟶ j)
    (hi : IsThickening i.hom) (hj : IsThickening j.hom) :
    UniversallyClosed φ.left ↔ UniversallyClosed φ.right := by
  have _ : IsClosedImmersion i.hom := hi.1
  have _ : IsClosedImmersion j.hom := hj.1
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have _ : UniversallyClosed (i.hom ≫ φ.right) := by rw [← φ.w]; infer_instance
    have _ : Surjective i.hom := ⟨hi.2⟩
    exact UniversallyClosed.of_comp_surjective i.hom φ.right
  · have _ : UniversallyClosed (φ.left ≫ j.hom) := by rw [φ.w]; infer_instance
    have _ : IsSeparated j.hom := isSeparated_of_injective (f := j.hom)
      (show Function.Injective j.hom from j.hom.isClosedEmbedding.injective)
    exact UniversallyClosed.of_comp_of_isSeparated φ.left j.hom

/-- Universal injectivity may be cancelled against a universal homeomorphism on the left. -/
private theorem universallyInjective_of_comp_left_of_universalHomeomorphism
    {X Y Z : Scheme.{u}} {i : X ⟶ Y} {f : Y ⟶ Z}
    (hi : UniversalHomeomorphism i)
    (h : UniversallyInjective (i ≫ f)) : UniversallyInjective f := by
  refine ⟨MorphismProperty.universally_mk' _ f ?_⟩
  intro T k hpull
  let p := pullback.snd k f
  exact Function.Injective.of_comp_right
    (h.universally_injective (pullback.snd p i) k _
      ((IsPullback.of_hasPullback p i).paste_horiz (IsPullback.of_hasPullback k f)))
    (hi.universally_isHomeomorph (pullback.snd p i) p (pullback.fst p i)
      (IsPullback.of_hasPullback p i)).surjective

/-- Universal injectivity is unchanged when a morphism of thickenings is passed from the
closed subschemes to the ambient schemes. -/
@[stacks 09ZV "universally_injective"]
theorem universallyInjective_left_iff_right {X X' S S' : Scheme.{u}}
    {i : X ⟶ X'} {j : S ⟶ S'} (hi : IsThickening i)
    (hj : IsThickening j) (f : Arrow.mk i ⟶ Arrow.mk j) :
    UniversallyInjective f.left ↔ UniversallyInjective f.right := by
  have _ : Mono i := by have _ : IsClosedImmersion i := hi.1; infer_instance
  have _ : Mono j := by have _ : IsClosedImmersion j := hj.1; infer_instance
  refine ⟨fun hleft => ?_, fun hright => ?_⟩
  · apply universallyInjective_of_comp_left_of_universalHomeomorphism
      (IsThickening.universalHomeomorphism hi)
    exact f.w ▸ MorphismProperty.comp_mem (@UniversallyInjective) f.left j hleft inferInstance
  · apply (MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
      (P := @UniversallyInjective)).of_postcomp f.left j inferInstance
    exact f.w.symm ▸
      MorphismProperty.comp_mem (@UniversallyInjective) i f.right inferInstance hright

/-- **The identity is a universal homeomorphism.** Every pullback of it is an isomorphism, and an
isomorphism of schemes is a homeomorphism on points. This is the library's one proof of the fact;
`Stacks.Thickenings` is where it lives because this module has the smallest import closure of the
three places that needed it. -/
public theorem universalHomeomorphism_id (X : Scheme.{u}) :
    UniversalHomeomorphism (𝟙 X) := by
  rw [universalHomeomorphism_iff]
  have _ : (topologically @IsHomeomorph).RespectsIso :=
    topologically_respectsIso (P := @IsHomeomorph) (fun e => e.isHomeomorph)
      (by intros; exact ‹IsHomeomorph _›.comp ‹IsHomeomorph _›)
  apply MorphismProperty.universally_mk' (P := topologically @IsHomeomorph) (𝟙 X)
  intro T i _
  exact topologically_iso_le (P := @IsHomeomorph) (fun e => e.isHomeomorph)
    (pullback.fst i (𝟙 X)) inferInstance

/-- The relative diagonal of a universal homeomorphism is a universal homeomorphism. -/
private theorem universalHomeomorphism_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : UniversalHomeomorphism f) :
    UniversalHomeomorphism (pullback.diagonal f) := by
  apply universalHomeomorphism_hasTwoOutOfThreeProperty.of_postcomp
    (pullback.diagonal f) (pullback.fst f f)
  · exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (topologically @IsHomeomorph).universally)
      (IsPullback.of_hasPullback f f).flip hf.universally_isHomeomorph⟩
  · simpa only [pullback.diagonal_fst] using universalHomeomorphism_id X

/-- A universal homeomorphism is universally open. -/
private theorem universallyOpen_of_universalHomeomorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : UniversalHomeomorphism f) : UniversallyOpen f := by
  rw [UniversallyOpen.eq]
  exact MorphismProperty.universally_mono (fun _ _ _ h => h.isOpenMap) f
    hf.universally_isHomeomorph

/-- Universal openness may be cancelled against a universal homeomorphism on the left. -/
private theorem universallyOpen_of_precomp_universalHomeomorphism
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z)
    (hi : UniversalHomeomorphism i) (hif : UniversallyOpen (i ≫ f)) :
    UniversallyOpen f := by
  rw [UniversallyOpen.eq]
  apply MorphismProperty.universally_mk' (P := topologically @IsOpenMap) f
  intro T t _
  have hpb₂ := IsPullback.of_hasPullback (pullback.snd t f) i
  have hopen := hif.universally_isOpenMap
    (pullback.snd (pullback.snd t f) i) t
    (pullback.fst (pullback.snd t f) i ≫ pullback.fst t f)
    (hpb₂.paste_horiz (IsPullback.of_hasPullback t f))
  have hhomeo := hi.universally_isHomeomorph _ _ _ hpb₂
  change IsOpenMap ((pullback.fst t f) ∘ (pullback.fst (pullback.snd t f) i)) at hopen
  show IsOpenMap (pullback.fst t f)
  exact IsOpenMap.of_comp hhomeo.continuous hhomeo.surjective hopen

/-- Universal openness may be cancelled against a universal homeomorphism on the right. -/
private theorem universallyOpen_of_postcomp_universalHomeomorphism
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    (hj : UniversalHomeomorphism j) (hfj : UniversallyOpen (f ≫ j)) :
    UniversallyOpen f := by
  let P : MorphismProperty Scheme.{u} := @UniversallyOpen.{u}
  let Q : MorphismProperty Scheme.{u} :=
    MorphismProperty.universally (topologically @IsHomeomorph)
  have hle : Q ≤ P.diagonal := by
    intro _ _ g hg
    show UniversallyOpen (pullback.diagonal g)
    exact universallyOpen_of_universalHomeomorphism _
      (universalHomeomorphism_diagonal g ((universalHomeomorphism_iff g).2 hg))
  have _ : P.IsStableUnderBaseChange := inferInstance
  have _ : P.IsMultiplicative := inferInstance
  have _ : P.HasOfPostcompProperty Q :=
    (MorphismProperty.hasOfPostcompProperty_iff_le_diagonal (P := P) (Q := Q)).2 hle
  exact P.of_postcomp f j hj.universally_isHomeomorph hfj

/-- Universal openness is unchanged when a morphism of schemes is replaced by the
corresponding morphism of thickenings. -/
@[stacks 09ZV "universally_open"]
theorem universallyOpen_left_iff_right
    {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j)
    (f : Arrow.mk i ⟶ Arrow.mk j) :
    UniversallyOpen f.left ↔ UniversallyOpen f.right := by
  have hI := IsThickening.universalHomeomorphism hi
  have hJ := IsThickening.universalHomeomorphism hj
  have _ := universallyOpen_of_universalHomeomorphism i hI
  have _ := universallyOpen_of_universalHomeomorphism j hJ
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have hcomp : UniversallyOpen (f.left ≫ j) := inferInstance
    exact universallyOpen_of_precomp_universalHomeomorphism i f.right hI (f.w ▸ hcomp)
  · have hcomp : UniversallyOpen (i ≫ f.right) := inferInstance
    exact universallyOpen_of_postcomp_universalHomeomorphism f.left j hJ (f.w.symm ▸ hcomp)

end Stacks.Thickenings

end
