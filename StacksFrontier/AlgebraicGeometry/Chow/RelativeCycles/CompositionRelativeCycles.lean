module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSubintegral
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompositionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassFacet
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatModuleRelativeCycle

/-!
# Compositions of cycle classes are relative cycles

Let `X --f--> Y --g--> S` be morphisms of schemes, both locally of finite type, with `S` locally
Noetherian, and let `r, e ≥ 0`. This file proves that the composition `α ∘ β` of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Composition` is a relative `(r + e)`-cycle on
`X/S` whenever `α` and `β` are *cycle classes*: finite integral combinations of the families
`[Z/X/Y]_r` and `[W/Y/S]_e` of closed subschemes flat over the respective bases. Over a discrete
valuation ring the second hypothesis is vacuous, because there every relative `e`-cycle is such a
combination (Lemma 0H5A).

This is the last two paragraphs of the proof of
[Stacks, Lemma 0H6R](https://stacks.math.columbia.edu/tag/0H6R): the bilinear reduction to a pair
of generators, and the computation of the composition of two generators as the family of a single
closed subscheme flat over `S`.

## Main definitions

* `Stacks.Chow.compFamilyHom` — the composition `α ∘ β` as a bilinear map, i.e. as an additive
  homomorphism in `α` whose values are additive homomorphisms in `β`.

## Main results

* `Stacks.Chow.isRelativeCycle_familyAssociatedToClosedSubscheme_of_flat` — the family
  `[Z/X/S]_r` of a closed subscheme flat over `S` of relative dimension at most `r` is a relative
  `r`-cycle. This is the flat case of Lemma 0H57, read on the closed subscheme rather than on its
  structure sheaf.
* `Stacks.Chow.isRelativeCycle_compFamily_familyAssociatedToClosedSubscheme` — the composition of
  two such generators is a relative cycle: by Lemma 0H6M it is the family of the closed subscheme
  `Z ×_Y W ⊆ X`, which is flat over `S` of relative dimension at most `r + e`.
* `Stacks.Chow.isRelativeCycle_compFamily_cycleClassMap` — the composition of two cycle classes
  is a relative cycle.
* `Stacks.Chow.isRelativeCycle_compFamily_cycleClassMap_dvr` — over the spectrum of a discrete
  valuation ring, the composition of a cycle class on `X/Y` with an arbitrary relative `e`-cycle
  on `Y/S` is a relative cycle.

## Implementation notes

The generator case uses the closed-subscheme reading of flatness rather than the one of
Definition 0CWG that Lemma 0H57 is stated with: `Flat (i ≫ f)` says `Z` is flat over the base
everywhere, which is what the fibre product `Z ×_Y W` inherits from its two factors, and it gives
`IsFlatOver` for `i_* 𝒪_Z` by `Stacks.Chow.isFlatOver_pushforwardStructureSheaf`. The family of
the closed subscheme is identified with the family of that module by
`Stacks.Chow.familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule`, and flatness of the
module gives the valuative condition by
`Stacks.Chow.isRelativeCycle_familyAssociatedToModule_of_isFlatOver`.

The flatness of `Z ×_Y W` over `S` is read off the pullback square: the projection
`Z ×_Y W ⟶ W` is the base change of the flat morphism `Z ⟶ Y`, and `W ⟶ S` is flat, so the
composite to `S` is flat. The relative dimension bound is
`Stacks.Chow.fibreDim_pullbackClosedSubschemes_le`, which needs no flatness at all.

Bilinearity is Tag 0H6I. It is packaged as `Stacks.Chow.compFamilyHom` so that the reduction to
generators is the usual induction on a free abelian group: the set of pairs whose composition
lands in the subgroup `z(X/S, r + e)` of relative cycles is closed under the group operations in
each variable separately.

Over a discrete valuation ring the cycle class homomorphism of Equation 0H58 is surjective onto
`z(Y/S, e)` by Lemma 0H5A, so the hypothesis on the second argument can be dropped there. The
corresponding reduction of the *first* argument is Lemma 0H59, over the base `Y`, which this file
does not use.

## References

* [Stacks Project, Lemma 0H6R](https://stacks.math.columbia.edu/tag/0H6R)
* [Stacks Project, Lemma 0H6M](https://stacks.math.columbia.edu/tag/0H6M)
* [Stacks Project, Lemma 0H6I](https://stacks.math.columbia.edu/tag/0H6I)
* [Stacks Project, Lemma 0H57](https://stacks.math.columbia.edu/tag/0H57)
* [Stacks Project, Equation 0H58](https://stacks.math.columbia.edu/tag/0H58)
* [Stacks Project, Lemma 0H5A](https://stacks.math.columbia.edu/tag/0H5A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The family of a closed subscheme flat over the base -/

/-- The family `[Z/X/S]_r` of cycles on the fibres of `X/S` attached to a closed subscheme
`i : Z ⟶ X` which is flat over `S` and of relative dimension at most `r` over `S` is a relative
`r`-cycle.

This is the case of Lemma 0H57 in which `Z` is flat over `S` everywhere, read on the closed
subscheme: the direct image `i_* 𝒪_Z` is then flat over `S`, and the family of the closed
subscheme is the family of that module. -/
theorem isRelativeCycle_familyAssociatedToClosedSubscheme_of_flat {X S Z : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (i : Z ⟶ X)
    [IsClosedImmersion i] [Flat (i ≫ f)] (r : ℕ)
    (hZ : ∀ s : S,
      topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) ≤ (r : WithBot ℕ∞)) :
    IsRelativeCycle f r (familyAssociatedToClosedSubscheme f i r) := by
  rw [familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule f i r hZ]
  exact isRelativeCycle_familyAssociatedToModule_of_isFlatOver f
    ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) r
    (isFlatOver_pushforwardStructureSheaf i f) _

/-- The fibre product `Z ×_Y W` of a closed subscheme `Z ⊆ X` flat over `Y` with a closed
subscheme `W ⊆ Y` flat over `S` is flat over `S`: its projection to `W` is the base change of
`Z ⟶ Y` along `W ⟶ Y`, and `W` is flat over `S`. -/
theorem flat_pullbackClosedSubschemes_comp {X Y S Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (i : Z ⟶ X) [Flat (i ≫ f)] (j : W ⟶ Y) [Flat (j ≫ g)] :
    Flat ((pullback.fst (i ≫ f) j ≫ i) ≫ f ≫ g) := by
  have hsnd : Flat (pullback.snd (i ≫ f) j) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (i ≫ f) j) inferInstance
  have heq : (pullback.fst (i ≫ f) j ≫ i) ≫ f ≫ g =
      pullback.snd (i ≫ f) j ≫ j ≫ g := by
    rw [Category.assoc, ← Category.assoc i f g, ← Category.assoc,
      pullback.condition (f := i ≫ f) (g := j), Category.assoc]
  rw [heq]
  exact @Flat.comp _ _ _ _ _ hsnd inferInstance

/-! ### The composition of two generators -/

/-- **The last paragraph of the proof of Stacks Project, Lemma 0H6R.** Let `Z ⊆ X` be a closed
subscheme flat over `Y` of relative dimension at most `r`, and let `W ⊆ Y` be a closed subscheme
flat over `S` of relative dimension at most `e`. Then the composition
`[Z/X/Y]_r ∘ [W/Y/S]_e` is a relative `(r + e)`-cycle on `X/S`.

By Lemma 0H6M the composition is the family `[Z ×_Y W/X/S]_{r + e}` of the closed subscheme
`Z ×_Y W ⊆ X`, which is flat over `S` of relative dimension at most `r + e`, so Lemma 0H57
applies to it. -/
theorem isRelativeCycle_compFamily_familyAssociatedToClosedSubscheme {X Y S Z W : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g]
    [IsLocallyNoetherian S] (r e : ℕ) (i : Z ⟶ X) [IsClosedImmersion i] [Flat (i ≫ f)]
    (hZ : ∀ y : Y, topologicalKrullDim (pullback i (f.fiberι y) : Scheme.{u}) ≤ (r : WithBot ℕ∞))
    (j : W ⟶ Y) [IsClosedImmersion j] [Flat (j ≫ g)]
    (hW : ∀ t : S,
      topologicalKrullDim (pullback j (g.fiberι t) : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    IsRelativeCycle (f ≫ g) (r + e)
      (compFamily f g r e (familyAssociatedToClosedSubscheme f i r)
        (familyAssociatedToClosedSubscheme g j e)) := by
  rw [compFamily_familyAssociatedToClosedSubscheme f g r e i hZ j hW]
  have : Flat ((pullback.fst (i ≫ f) j ≫ i) ≫ f ≫ g) :=
    flat_pullbackClosedSubschemes_comp f g i j
  exact isRelativeCycle_familyAssociatedToClosedSubscheme_of_flat (f ≫ g)
    (pullback.fst (i ≫ f) j ≫ i) (r + e) (fibreDim_pullbackClosedSubschemes_le f g r e i hZ j hW)

/-! ### Bilinearity of the composition -/

/-- The composition with the zero family on `Y/S` is zero, by additivity in that argument. -/
theorem compFamily_zero_right {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y ⟶ S) [LocallyOfFiniteType g] (r e : ℕ) (α : FamilyOfCycles f r) :
    compFamily f g r e α 0 = 0 := by
  have h := compFamily_add_right f g r e α 0 0
  rw [zero_add] at h
  exact add_eq_left.mp h.symm

/-- The composition of the zero family on `X/Y` is zero, by additivity in that argument. -/
theorem compFamily_zero_left {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y ⟶ S) [LocallyOfFiniteType g] (r e : ℕ) (β : FamilyOfCycles g e) :
    compFamily f g r e 0 β = 0 := by
  have h := compFamily_add_left f g r e 0 0 β
  rw [zero_add] at h
  exact add_eq_left.mp h.symm

/-- The composition of families of cycles on fibres as a bilinear map: an additive homomorphism
in the family on `X/Y` whose values are additive homomorphisms in the family on `Y/S`. -/
def compFamilyHom {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S)
    [LocallyOfFiniteType g] (r e : ℕ) :
    FamilyOfCycles f r →+ FamilyOfCycles g e →+ FamilyOfCycles (f ≫ g) (r + e) where
  toFun α :=
    { toFun := compFamily f g r e α
      map_zero' := compFamily_zero_right f g r e α
      map_add' := compFamily_add_right f g r e α }
  map_zero' := AddMonoidHom.ext (compFamily_zero_left f g r e)
  map_add' α₁ α₂ := AddMonoidHom.ext (compFamily_add_left f g r e α₁ α₂)

/-- Evaluating the bilinear map `compFamilyHom` at `α` and `β` gives the composition
`compFamily f g r e α β`. -/
@[simp]
theorem compFamilyHom_apply {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ S)
    [LocallyOfFiniteType g] (r e : ℕ) (α : FamilyOfCycles f r) (β : FamilyOfCycles g e) :
    compFamilyHom f g r e α β = compFamily f g r e α β :=
  rfl

/-- An additive homomorphism out of a free abelian group lands in a subgroup as soon as it does on
the generators. -/
private theorem map_mem_of_forall_of_mem {A G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (φ : FreeAbelianGroup A →+ G) (h : ∀ a, φ (FreeAbelianGroup.of a) ∈ H)
    (a : FreeAbelianGroup A) : φ a ∈ H := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simpa only [map_zero] using H.zero_mem
  | of a => exact h a
  | neg a ha => simpa only [map_neg] using H.neg_mem ha
  | add c₁ c₂ h₁ h₂ => simpa only [map_add] using H.add_mem h₁ h₂

/-- The bilinear reduction to generators: if the composition of `u a` with `v b` is a relative
cycle for all `a` and `b`, then so is the composition of an arbitrary integral combination of the
`u a` with an arbitrary integral combination of the `v b`. -/
theorem isRelativeCycle_compFamily_lift {X Y S : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y ⟶ S) [LocallyOfFiniteType g] [IsLocallyNoetherian S] (r e : ℕ) {A B : Type*}
    (u : A → FamilyOfCycles f r) (v : B → FamilyOfCycles g e)
    (hgen : ∀ (a : A) (b : B), IsRelativeCycle (f ≫ g) (r + e) (compFamily f g r e (u a) (v b)))
    (a : FreeAbelianGroup A) (b : FreeAbelianGroup B) :
    IsRelativeCycle (f ≫ g) (r + e)
      (compFamily f g r e (FreeAbelianGroup.lift u a) (FreeAbelianGroup.lift v b)) := by
  change compFamilyHom f g r e (FreeAbelianGroup.lift u a) (FreeAbelianGroup.lift v b) ∈
    relativeCycles (f ≫ g) (r + e)
  refine map_mem_of_forall_of_mem (relativeCycles (f ≫ g) (r + e))
    ((AddMonoidHom.eval (FreeAbelianGroup.lift v b)).comp
      ((compFamilyHom f g r e).comp (FreeAbelianGroup.lift u))) (fun a' ↦ ?_) a
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, FreeAbelianGroup.lift_apply_of]
  exact map_mem_of_forall_of_mem (relativeCycles (f ≫ g) (r + e))
    ((compFamilyHom f g r e (u a')).comp (FreeAbelianGroup.lift v)) 
    (fun b' ↦ by simpa using hgen a' b') b

/-! ### Compositions of cycle classes -/

/-- The cycle class homomorphism of Tag 0H6V is the lift of the families of the closed subschemes
underlying the Hilbert data. -/
theorem cycleClassMap_eq_lift {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (r : ℕ) (c : FreeAbelianGroup (HilbertCycleDatum f r)) :
    cycleClassMap f r c =
      FreeAbelianGroup.lift
        (fun Z : HilbertCycleDatum f r ↦ familyAssociatedToClosedSubscheme f Z.ideal.subschemeι r)
        c :=
  FreeAbelianGroup.lift_unique _ (cycleClassMap f r) (x := c) fun Z ↦ by
    rw [cycleClassMap_of, HilbertCycleDatum.cycleFamily_eq_familyAssociatedToClosedSubscheme f Z]

/-- **The bilinear step of the proof of Stacks Project, Lemma 0H6R.** The composition of a cycle
class on `X/Y` with a cycle class on `Y/S` is a relative `(r + e)`-cycle on `X/S`.

By bilinearity (Tag 0H6I) this reduces to a pair of generators, which is
`Stacks.Chow.isRelativeCycle_compFamily_familyAssociatedToClosedSubscheme`. -/
theorem isRelativeCycle_compFamily_cycleClassMap {X Y S : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (g : Y ⟶ S) [LocallyOfFinitePresentation g]
    [IsLocallyNoetherian S] (r e : ℕ) (a : FreeAbelianGroup (HilbertCycleDatum f r))
    (b : FreeAbelianGroup (HilbertCycleDatum g e)) :
    IsRelativeCycle (f ≫ g) (r + e)
      (compFamily f g r e (cycleClassMap f r a) (cycleClassMap g e b)) := by
  rw [cycleClassMap_eq_lift f r a, cycleClassMap_eq_lift g e b]
  refine isRelativeCycle_compFamily_lift f g r e _ _ (fun Z W ↦ ?_) a b
  have : Flat (Z.ideal.subschemeι ≫ f) := Z.flat
  have : Flat (W.ideal.subschemeι ≫ g) := W.flat
  exact isRelativeCycle_compFamily_familyAssociatedToClosedSubscheme f g r e
    Z.ideal.subschemeι (Z.topologicalKrullDim_pullback_fiberι_le f)
    W.ideal.subschemeι (W.topologicalKrullDim_pullback_fiberι_le g)

/-- **Stacks Project, Lemma 0H6R over a discrete valuation ring, for a cycle class on `X/Y`.**
If `α` is a cycle class on `X/Y` and `β` is *any* relative `e`-cycle on `Y/Spec R` with `R` a
discrete valuation ring, then `α ∘ β` is a relative `(r + e)`-cycle on `X/Spec R`.

The hypothesis on `β` of
`Stacks.Chow.isRelativeCycle_compFamily_cycleClassMap` is vacuous over a discrete valuation
ring: there the cycle class homomorphism of Equation 0H58 is surjective onto `z(Y/Spec R, e)` by
Lemma 0H5A. -/
theorem isRelativeCycle_compFamily_cycleClassMap_dvr {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (g : Y ⟶ Spec (.of R)) [LocallyOfFiniteType g] [QuasiCompact g] (r e : ℕ)
    (a : FreeAbelianGroup (HilbertCycleDatum f r)) {β : FamilyOfCycles g e}
    (hβ : IsRelativeCycle g e β) :
    IsRelativeCycle (f ≫ g) (r + e) (compFamily f g r e (cycleClassMap f r a) β) := by
  obtain ⟨b, hb⟩ := surjective_relativeCycleClassMap (r := e) g ⟨β, hβ⟩
  have hb' : cycleClassMap g e b = β := by
    rw [← relativeCycleClassMap_val g b, hb]
  rw [← hb']
  exact isRelativeCycle_compFamily_cycleClassMap f g r e a b

/-! ### Reduction of the composition to a base which is the spectrum of a discrete valuation
ring -/

/-- **The first paragraph of the proof of Stacks Project, Lemma 0H6R.** The composition `α ∘ β`
is a relative `(r + e)`-cycle on `X/S` as soon as, for every discrete valuation ring `R` and
every morphism `c : Spec R ⟶ S`, the composition of the base changes of `α` and `β` over
`Spec R` carries the generic member to the closed member under the specialization map.

The formation of `α ∘ β` is compatible with base change by Tag 0H6K: the composition of the base
changes is the base change of `α ∘ β`, read through the canonical isomorphism
`(X ×_Y (Y ×_S Spec R))_t ≅ (X ×_S Spec R)_t` of the fibres. Transport along that isomorphism
commutes with specialization by the open-immersion case of Tag 0H4L and is injective, so the
valuative condition for `α ∘ β` at `c` is the displayed identity. -/
theorem isRelativeCycle_compFamily_of_forall_dvr {X Y S : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ S) [LocallyOfFiniteType g] [IsLocallyNoetherian S] (r e : ℕ)
    (α : FamilyOfCycles f r) (β : FamilyOfCycles g e)
    (hdvr : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (c : Spec (.of R) ⟶ S),
      specializationCycle (pullback.snd f (pullback.fst g c) ≫ pullback.snd g c) (r + e)
          (compFamily (pullback.snd f (pullback.fst g c)) (pullback.snd g c) r e
            (baseChangeFamily f (pullback.fst g c) r α) (baseChangeFamily g c e β)
            (genericPoint (Spec (.of R)))) =
        compFamily (pullback.snd f (pullback.fst g c)) (pullback.snd g c) r e
          (baseChangeFamily f (pullback.fst g c) r α) (baseChangeFamily g c e β)
          (IsLocalRing.closedPoint R)) :
    IsRelativeCycle (f ≫ g) (r + e) (compFamily f g r e α β) := by
  intro R _ _ _ c
  have hsp := hdvr R c
  rw [compFamily_baseChangeFamily f g c (genericPoint (Spec (.of R))) r e α β,
    compFamily_baseChangeFamily f g c (IsLocalRing.closedPoint R) r e α β,
    specializationCycle_fiberCycleRestrict (pullback.snd (f ≫ g) c)
      (pullback.snd f (pullback.fst g c) ≫ pullback.snd g c)
      (pullbackRightPullbackFstIso g c f).hom (pullbackRightPullbackFstIso_hom_snd g c f)
      (r + e) (baseChangeFamily (f ≫ g) c (r + e) (compFamily f g r e α β)
        (genericPoint (Spec (.of R))))] at hsp
  exact fiberCycleRestrict_injective_of_isIso (pullback.snd (f ≫ g) c)
    (pullback.snd f (pullback.fst g c) ≫ pullback.snd g c)
    (pullbackRightPullbackFstIso g c f).hom (pullbackRightPullbackFstIso_hom_snd g c f)
    (IsLocalRing.closedPoint R) (r + e) hsp

end Stacks.Chow

end
