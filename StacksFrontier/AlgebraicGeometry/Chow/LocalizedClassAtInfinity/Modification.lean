module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedClassAtInfinity.Construction
public import StacksFrontier.AlgebraicGeometry.Chow.ClosedCoverChernBaseChange

/-!
# The class of Stacks 0F9K is unchanged by a proper modification

Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let `Z ⊆ X` be a closed subscheme,
let `T ⊆ W_∞` be a closed subscheme containing every point of `W_∞` over `X \ Z`, and let
`E = W_∞ ×_X Z`. Let `g : W' ⟶ W` be proper and an isomorphism over `𝐀¹_X`, with
`g_∞ : W'_∞ ⟶ W_∞`, `E' = W'_∞ ×_X Z = g_∞^{-1}(E)` and `T' = g_∞^{-1}(T)`.

For `κ ∈ A^p(E)` vanishing on `T ∩ E` and a class `κ' ∈ A^p(E')` operating on the test schemes
of `E'` as `κ` does on them viewed over `E` (that is, `κ'` is the restriction of `κ`), the
classes `(E' ⟶ Z)_* ∘ κ'' ∘ C'` and `(E ⟶ Z)_* ∘ κ''' ∘ C` of Stacks 0F9K built from `W'` and
from `W` agree. This is the argument of Stacks 0FAU, at the level of the class `κ`.

## Main results

* `Stacks.Chow.GysinAtInfinity.localizedClassAtInfinityOf_modification`.

## Implementation notes

The proof is the source's: `C = g_{∞,*} ∘ C'` (Stacks 0FAQ); the localized class of `κ'` for
`W'_∞ = T' ∪ E'` is the restriction (Remark 0F9Z) of that of `κ` for `W_∞ = T ∪ E` (Stacks 0GUG);
and the latter commutes with proper pushforward along the base change of `g_∞` because it is a
bivariant class. The chain of equalities on cap operations is
`Stacks.Chow.eq_of_isLocalizedClassAtInfinity_of_modification`.

The structure morphism of `W'_∞` is taken to be `W'_∞ ⟶ W_∞ ⟶ S`, which is the one the restriction
of Remark 0F9Z produces; `Stacks.Chow.GysinAtInfinity.localizedClassAtInfinityOf_congr` says that
this choice does not matter.

## References

* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 0GUG](https://stacks.math.columbia.edu/tag/0GUG)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### A Chow cohomology class as a family of cap operations -/

/-- The cap operations `α ↦ κ ∩ α` of a Chow cohomology class `κ ∈ A^p(Z)` on the test schemes
of `Z`, as the family of cap operations in which the characterization of Stacks 0F9H used by
Stacks 0GUG is phrased. -/
def chernCapFamilyOfComponent (C : ChowSituation.{u}) {Z : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] {p : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p) : ChernCapFamily C sZ p where
  cap g _ k := κ.idRule C sZ (gysinSystemOfInvertible C) g k
  cap_naturality g _ g' _ ι _ hι k α := (idRule_chowPush C sZ κ g' g ι hι k α).symm

/-- The localized class of Stacks 0F9H of `κ` satisfies the characterization of Stacks 0F9H in
the form `Stacks.Chow.IsClosedCoverChernClass` in which Stacks 0GUG is stated. -/
theorem isClosedCoverChernClass_closedCoverLocalizedClass (C : ChowSituation.{u})
    {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X)
    [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {p : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p)
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) (pullback.snd i₁ i₂) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0) :
    IsClosedCoverChernClass C (gysinSystemOfInvertible C) sX i₁ i₂ p
      (chernCapFamilyOfComponent C (i₂ ≫ sX) κ)
      (closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover κ hκ) :=
  ⟨fun g _ k α ↦ closedCoverLocalizedClass_cap_pushforward_right C sX _ _ i₁ rfl i₂ rfl hcover κ
      hκ g k α,
    fun g _ k α ↦ closedCoverLocalizedClass_cap_pushforward_left C sX _ _ i₁ rfl i₂ rfl hcover κ
      hκ g k α⟩

/-- The characterization of Stacks 0F9H determines the class: a class satisfying it for a family
of cap operations that is that of `κ` is the localized class of `κ`. -/
theorem eq_closedCoverLocalizedClass_of_isClosedCoverChernClass (C : ChowSituation.{u})
    {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X)
    [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {p : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p)
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) (pullback.snd i₁ i₂) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)
    (amb : ChernCapFamily C (i₂ ≫ sX) p)
    (hamb : ∀ {V : Scheme.{u}} (v : V ⟶ X₂) [LocallyOfFiniteType v] (k : ℤ)
      (α : chowGroup C (v ≫ (i₂ ≫ sX)) k),
      amb.cap v k α = κ.idRule C (i₂ ≫ sX) (gysinSystemOfInvertible C) v k α)
    (c : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl p)
    (hc : IsClosedCoverChernClass C (gysinSystemOfInvertible C) sX i₁ i₂ p amb c) :
    c = closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover κ hκ :=
  eq_closedCoverLocalizedClass C sX _ _ i₁ rfl i₂ rfl hcover κ hκ c
    (fun g _ k α ↦ (hc.1 g k α).trans (hamb _ k α)) (fun g _ k α ↦ hc.2 g k α)

namespace GysinAtInfinity

/-! ### The geometry of the modification -/

section Geometry

variable {X W W' Z S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (iZ : Z ⟶ X)
  (g : W' ⟶ W)

/-- `E' = W'_∞ ×_X Z` is the inverse image `g_∞^{-1}(E)` of `E = W_∞ ×_X Z`. -/
def infinityPreimageModificationIso :
    pullback (preimageInclusion f b iZ) (infinityMap f b g) ≅
      pullback (modificationProjectionAtInfinity f (g ≫ b)) iZ :=
  pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso (modificationProjectionAtInfinity f b) iZ (infinityMap f b g) ≪≫
      pullback.congrHom (infinityMap_comp_projection f b g) rfl

/-- Under `infinityPreimageModificationIso`, the inclusion `E' ⟶ W'_∞` corresponds to the second
projection `E ×_{W_∞} W'_∞ ⟶ W'_∞`. -/
@[reassoc (attr := simp)]
theorem infinityPreimageModificationIso_hom_ι :
    (infinityPreimageModificationIso f b iZ g).hom ≫ preimageInclusion f (g ≫ b) iZ =
      pullback.snd _ _ := by
  simp [infinityPreimageModificationIso]

/-- Under `infinityPreimageModificationIso`, the projection `E' ⟶ Z` corresponds to the first
projection to `E` followed by the projection `E ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem infinityPreimageModificationIso_hom_toClosed :
    (infinityPreimageModificationIso f b iZ g).hom ≫ preimageProjection f (g ≫ b) iZ =
      pullback.fst _ _ ≫ preimageProjection f b iZ := by
  simp [infinityPreimageModificationIso]

/-- `T' = g_∞^{-1}(T)` contains every point of `W'_∞` lying over `X \ Z` if `T` contains every
point of `W_∞` lying over `X \ Z`. -/
theorem preimage_mem_range {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b)
    (hT : ∀ w : modificationFibreAtInfinity f b,
      (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
    (w : modificationFibreAtInfinity f (g ≫ b))
    (hw : (modificationProjectionAtInfinity f (g ≫ b)).base w ∉ Set.range iZ.base) :
    w ∈ Set.range (pullback.snd iT (infinityMap f b g)).base := by
  rw [Scheme.Pullback.range_snd]
  refine hT _ ?_
  rwa [← Scheme.Hom.comp_apply, infinityMap_comp_projection]

variable {T : Scheme.{u}} (t : T ⟶ X)

/-- The base change of `E' ⟶ E` to a test scheme `t : T ⟶ X`, as a morphism
`E ×_{W_∞} (W'_∞ ×_X T) ⟶ E ×_{W_∞} (W_∞ ×_X T)`. -/
def infinityPreimageTestMap :
    pullback (preimageInclusion f b iZ)
        (pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t ≫ infinityMap f b g) ⟶
      pullback (preimageInclusion f b iZ) (pullback.fst (modificationProjectionAtInfinity f b) t) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ testInfinityMap f b g t)
    (by rw [pullback.condition, Category.assoc, testInfinityMap_fst])

/-- `infinityPreimageTestMap` commutes with the first projections to `E`. -/
@[reassoc (attr := simp)]
theorem infinityPreimageTestMap_fst :
    infinityPreimageTestMap f b iZ g t ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The second component of `infinityPreimageTestMap` is the base change `testInfinityMap` of
`g_∞`. -/
@[reassoc (attr := simp)]
theorem infinityPreimageTestMap_snd :
    infinityPreimageTestMap f b iZ g t ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ testInfinityMap f b g t :=
  pullback.lift_snd _ _ _

/-- The square formed by `infinityPreimageTestMap`, `testInfinityMap` and the second projections
to `W'_∞ ×_X T` and `W_∞ ×_X T` is a pullback square. -/
theorem isPullback_infinityPreimageTestMap :
    IsPullback (pullback.snd (preimageInclusion f b iZ)
        (pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t ≫ infinityMap f b g))
      (infinityPreimageTestMap f b iZ g t) (testInfinityMap f b g t)
      (pullback.snd (preimageInclusion f b iZ)
        (pullback.fst (modificationProjectionAtInfinity f b) t)) := by
  refine IsPullback.of_bot ?_ (infinityPreimageTestMap_snd f b iZ g t).symm
    (IsPullback.of_hasPullback _ _).flip
  rw [infinityPreimageTestMap_fst, testInfinityMap_fst]
  exact (IsPullback.of_hasPullback _ _).flip

/-- The identification `E ×_{W_∞} (W'_∞ ×_X T) ≅ E' ×_{W'_∞} (W'_∞ ×_X T)`. -/
def infinityPreimageTestIso :
    pullback (preimageInclusion f b iZ)
        (pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t ≫ infinityMap f b g) ≅
      pullback (preimageInclusion f (g ≫ b) iZ)
        (pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t) :=
  (pullbackLeftPullbackSndIso (preimageInclusion f b iZ) (infinityMap f b g)
      (pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t)).symm ≪≫
    transportPullbackIso (pullback.snd (preimageInclusion f b iZ) (infinityMap f b g))
      (preimageInclusion f (g ≫ b) iZ) (infinityPreimageModificationIso f b iZ g)
      (infinityPreimageModificationIso_hom_ι f b iZ g) _

/-- The first component of `infinityPreimageTestIso` is the reassociation isomorphism followed by
the first projection and `infinityPreimageModificationIso`. -/
@[reassoc (attr := simp)]
theorem infinityPreimageTestIso_hom_fst :
    (infinityPreimageTestIso f b iZ g t).hom ≫ pullback.fst _ _ =
      (pullbackLeftPullbackSndIso (preimageInclusion f b iZ) (infinityMap f b g)
          (pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t)).inv ≫
        pullback.fst _ _ ≫ (infinityPreimageModificationIso f b iZ g).hom := by
  simp [infinityPreimageTestIso]

/-- `infinityPreimageTestIso` commutes with the second projections to `W'_∞ ×_X T`. -/
@[reassoc (attr := simp)]
theorem infinityPreimageTestIso_hom_snd :
    (infinityPreimageTestIso f b iZ g t).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [infinityPreimageTestIso]

end Geometry

/-! ### Invariance under a proper modification -/

section Modification

variable (C : ChowSituation.{u}) {X W W' Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (iZ : Z ⟶ X) [IsClosedImmersion iZ]
  (sW : modificationFibreAtInfinity f b ⟶ C.S) [LocallyOfFiniteType sW]
  (hsW : modificationProjectionAtInfinity f b ≫ f = sW)
  {T : Scheme.{u}} (iT : T ⟶ modificationFibreAtInfinity f b) [IsClosedImmersion iT]
  (hT : ∀ w : modificationFibreAtInfinity f b,
    (modificationProjectionAtInfinity f b).base w ∉ Set.range iZ.base → w ∈ Set.range iT.base)
  (g : W' ⟶ W) [IsProper g] (hg : IsIso (pullback.snd g (chartInclusion f b)))

include hsW in
omit [LocallyOfFiniteType f] [IsProper b] [IsClosedImmersion iZ] [LocallyOfFiniteType sW]
  [IsProper g] in
/-- The structure morphism `W'_∞ ⟶ X ⟶ S` is `W'_∞ ⟶ W_∞ ⟶ S`. -/
theorem modificationProjectionAtInfinity_comp_eq :
    modificationProjectionAtInfinity f (g ≫ b) ≫ f = infinityMap f b g ≫ sW := by
  rw [← infinityMap_comp_projection f b g, Category.assoc, hsW]

/-- **The argument of Stacks 0FAU, at the level of the class on `E`.** Let `g : W' ⟶ W` be
proper and an isomorphism over `𝐀¹_X`, let `κ ∈ A^p(E)` vanish on `T ∩ E`, and let
`κ' ∈ A^p(E')` be the restriction of `κ` along `E' = g_∞^{-1}(E) ⟶ E`, in the sense that it caps
on every test scheme of `E'` as `κ` does on it viewed over `E`. Then the class of Stacks 0F9K built
from `b ∘ g`, `T' = g_∞^{-1}(T)` and `κ'` equals the class built from `b`, `T` and `κ`. -/
theorem localizedClassAtInfinityOf_modification {p : ℤ}
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) (preimageInclusion f b iZ ≫ sW) p)
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) (preimageInclusion f b iZ ≫ sW)
      (pullback.snd iT (preimageInclusion f b iZ)) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)
    (κ' : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (preimageInclusion f (g ≫ b) iZ ≫ (infinityMap f b g ≫ sW)) p)
    (hκ' : chowCohomologyRestriction C (gysinSystemOfInvertible C)
      (preimageInclusion f (g ≫ b) iZ ≫ (infinityMap f b g ≫ sW))
      (pullback.snd (pullback.snd iT (infinityMap f b g)) (preimageInclusion f (g ≫ b) iZ)) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ' = 0)
    (hκκ' : ∀ {V : Scheme.{u}}
      (v : V ⟶ pullback (modificationProjectionAtInfinity f (g ≫ b)) iZ) [LocallyOfFiniteType v]
      (k : ℤ) (α : chowGroup C (v ≫ (preimageInclusion f (g ≫ b) iZ ≫ (infinityMap f b g ≫ sW))) k),
      (ChernCapFamily.restrict C (preimageInclusion f b iZ ≫ sW)
          (preimageInclusion f (g ≫ b) iZ ≫ (infinityMap f b g ≫ sW))
          (baseChangeWitnessProjection (infinityMap f b g) (preimageInclusion f b iZ)
            (infinityPreimageModificationIso f b iZ g))
          (baseChangeWitnessProjection_comp_structureMorphism (infinityMap f b g)
            (preimageInclusion f b iZ) (preimageInclusion f (g ≫ b) iZ)
            (infinityPreimageModificationIso f b iZ g)
            (infinityPreimageModificationIso_hom_ι f b iZ g) sW) p
          (chernCapFamilyOfComponent C _ κ)).cap v k α =
        κ'.idRule C _ (gysinSystemOfInvertible C) v k α) :
    haveI := hA
    haveI := hg
    localizedClassAtInfinityOf C f (g ≫ b) (isIso_pullbackSnd_comp f b g) iZ
        (infinityMap f b g ≫ sW) (modificationProjectionAtInfinity_comp_eq C f b sW hsW g)
        (pullback.snd iT (infinityMap f b g)) (preimage_mem_range f b iZ g iT hT) κ' hκ' =
      localizedClassAtInfinityOf C f b hA iZ sW hsW iT hT κ hκ := by
  have := hA
  have := hg
  set gInf := infinityMap f b g with hgInf
  set iE := preimageInclusion f b iZ
  set iE' := preimageInclusion f (g ≫ b) iZ
  set iT' := pullback.snd iT gInf
  set θ := infinityPreimageModificationIso f b iZ g
  have hθ : θ.hom ≫ iE' = pullback.snd iE gInf := infinityPreimageModificationIso_hom_ι f b iZ g
  have hgys : (gysinSystemOfInvertible C).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C
  set cE := closedCoverLocalizedClass C sW (iT ≫ sW) (iE ≫ sW) iT rfl iE rfl
    (range_union_range_preimageInclusion f b iZ iT hT) κ hκ
  set cE' := closedCoverLocalizedClass C (gInf ≫ sW) (iT' ≫ (gInf ≫ sW)) (iE' ≫ (gInf ≫ sW)) iT'
    rfl iE' rfl (range_union_range_preimageInclusion f (g ≫ b) iZ iT'
      (preimage_mem_range f b iZ g iT hT)) κ' hκ'
  -- Stacks 0GUG: the localized class over `W'_∞` is the restriction of the one over `W_∞`.
  have hres : cE' = bivariantTransport C (gysinSystemOfInvertible C)
      (pullback.fst iE gInf ≫ (iE ≫ sW)) (iE' ≫ (gInf ≫ sW)) (gInf ≫ sW) (pullback.snd iE gInf)
      (pullbackSnd_comp_structureMorphism_eq C (iE ≫ sW) sW iE rfl gInf) iE' rfl θ hθ p hgys
      (bivariantRestriction C (gysinSystemOfInvertible C) (iE ≫ sW) sW iE rfl gInf p hgys cE) := by
    refine closedCoverChern_eq_bivariantTransport_bivariantRestriction gInf (Iso.refl _)
      (Category.id_comp _) θ hθ hgys (chernCapFamilyOfComponent C _ κ) cE
      (isClosedCoverChernClass_closedCoverLocalizedClass C sW iT iE _ κ hκ) cE' ?_ ?_
    · refine ⟨fun g' _ k α ↦ ?_, fun g' _ k α ↦ ?_⟩
      · rw [hκκ']
        exact closedCoverLocalizedClass_cap_pushforward_right C (gInf ≫ sW) _ _ iT' rfl iE' rfl
          _ κ' hκ' g' k α
      · exact closedCoverLocalizedClass_cap_pushforward_left C (gInf ≫ sW) _ _ iT' rfl iE' rfl
          _ κ' hκ' g' k α
    · intro c d hc hd
      have key := fun e (he : IsClosedCoverChernClass C (gysinSystemOfInvertible C) (gInf ≫ sW)
          iT' iE' p _ e) ↦
        eq_closedCoverLocalizedClass_of_isClosedCoverChernClass C (gInf ≫ sW) iT' iE'
          (range_union_range_preimageInclusion f (g ≫ b) iZ iT'
            (preimage_mem_range f b iZ g iT hT)) κ' hκ' _ (fun v _ k α ↦ hκκ' v k α) e he
      exact (key c hc).trans (key d hd).symm
  refine eq_of_isLocalizedClassAtInfinity_of_modification C (gysinSystemOfInvertible C) f sW
    (iE ≫ sW) (gInf ≫ sW) (iE' ≫ (gInf ≫ sW)) iZ (modificationProjectionAtInfinity f b) hsW iE rfl
    (modificationProjectionAtInfinity f (g ≫ b))
    (modificationProjectionAtInfinity_comp_eq C f b sW hsW g) iE' rfl gInf
    (infinityMap_comp_projection f b g) p
    (fun t _ ↦ infinityPreimageBaseChange C f b iZ t) (fun t _ ↦ inferInstance)
    (fun t _ ↦ infinityPreimageBaseChange_comp C f b iZ sW hsW t)
    (fun t _ ↦ infinityPreimageBaseChange C f (g ≫ b) iZ t) (fun t _ ↦ inferInstance)
    (fun t _ ↦ infinityPreimageBaseChange_comp C f (g ≫ b) iZ (gInf ≫ sW)
      (modificationProjectionAtInfinity_comp_eq C f b sW hsW g) t)
    (fun t _ ↦ testInfinityMap f b g t) (fun t _ ↦ inferInstance)
    (fun t _ ↦ testInfinityMap_fst f b g t)
    (fun t _ ↦ infinityPreimageTestIso f b iZ g t) (fun t _ ↦ ?_)
    (fun t _ ↦ infinityPreimageTestMap f b iZ g t)
    (fun t _ ↦ isPullback_infinityPreimageTestMap f b iZ g t)
    (fun t _ ↦ infinityPreimageTestMap_fst f b iZ g t) (fun t _ ↦ ?_) (fun t _ k α ↦ ?_)
    (fun t _ k x ↦ ?_)
    (pushAtInfinity_isLocalizedClassAtInfinity C f b hA iZ sW hsW cE)
    (pushAtInfinity_isLocalizedClassAtInfinity C f (g ≫ b) (isIso_pullbackSnd_comp f b g) iZ
      (gInf ≫ sW) (modificationProjectionAtInfinity_comp_eq C f b sW hsW g) cE')
  · -- the identification lies over the base
    rw [← Category.assoc, infinityPreimageTestIso_hom_fst, Category.assoc, Category.assoc,
      ← Category.assoc θ.hom, hθ, ← Category.assoc (pullback.snd iE gInf), ← pullback.condition,
      Category.assoc]
    exact pullbackLeftPullbackSndIso_inv_fst_assoc _ _ _ _
  · -- the base changes of `E' ⟶ Z`, `E ⟶ Z` and `E' ⟶ E` are compatible
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, infinityPreimageBaseChange_fst, infinityPreimageTestMap_fst_assoc,
        infinityPreimageTestIso_hom_fst_assoc, infinityPreimageModificationIso_hom_toClosed]
      exact pullbackLeftPullbackSndIso_inv_fst_assoc _ _ _ _
    · simp only [Category.assoc, infinityPreimageBaseChange_snd, infinityPreimageTestMap_snd_assoc,
        infinityPreimageTestIso_hom_snd_assoc, testInfinityMap_snd]
  · -- Stacks 0FAQ: `g_{∞,*} ∘ C' = C`
    have h0 := congrArg (fun c ↦ c.cap t k α) (properPushforward_gysinAtInfinityClass C f b g hA hg)
    rw [classAtInfinityOf, classAtInfinityOf, BivariantClass.congrSource_cap,
      BivariantClass.congrSource_cap, ← h0]
    refine (congrArg (chowGroupCongr C _ (k - 0))
      (canonicalBivariantProperPushforward_copy_cap C
        (modificationProjectionAtInfinity f (g ≫ b) ≫ f)
        (modificationProjectionAtInfinity f b ≫ f) f
        gInf (modificationProjectionAtInfinity f b) (modificationProjectionAtInfinity f (g ≫ b))
        (infinityMap_comp_projection f b g).symm
        (by rw [← Category.assoc, infinityMap_comp_projection]) rfl rfl 0 _ t
        (testInfinityMap f b g t) (testInfinityMap_fst f b g t) (testInfinityMap_snd f b g t)
        (testInfinityMap_comp_structure C f b g t) k α)).trans ?_
    exact properChowPushforward_chowGroupCongr C _ _ (testInfinityMap f b g t) _ _ (k - 0) _ _ _
  · -- Stacks 0GUG: `c'_p(Q'|_{E'})` is the restriction of `c'_p(Q|_E)`
    rw [hres, bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestriction_cap,
      bivariantRestrictionCap_apply, chowPushforwardOfIso_comp_apply]
    rfl

end Modification

end GysinAtInfinity

end Stacks.Chow

end
