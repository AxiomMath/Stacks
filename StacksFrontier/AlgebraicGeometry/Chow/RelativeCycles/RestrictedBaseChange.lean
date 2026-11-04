module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeRelative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSubintegral
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassFacet

/-!
# Restricting a base-changed family of cycles to an open subscheme of the base

Let `f : X ⟶ S` be locally of finite type, let `g : T ⟶ S` be a morphism and let `α` be a family
of `r`-cycles on the fibres of `X/S`. For an open immersion `i : V ⟶ T`, the restriction of the
base change `g^*α` to the fibres of `X ×_S V ⟶ V` is the base change `(i ≫ g)^*α`. This is the
clause of [Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R) saying that base change commutes
with restriction to an open subscheme of the base, for families of cycles on fibres.

As an application, the coproduct clause of the Noetherian induction in the proof of
[Tag 0H59](https://stacks.math.columbia.edu/tag/0H59) holds for
`Stacks.Chow.PullbackInCycleClassImage`.

## Main results

* `Stacks.Chow.baseChangeFamily_apply_of_isIso_residueFieldMap` — at a point where the residue
  field extension is trivial, the base change of a family of cycles is the transport of the
  member over the image point.
* `Stacks.Chow.restrictedFamily_eq_baseChangeFamily` — restriction along an open immersion of the
  base is base change along it.
* `Stacks.Chow.restrictedFamily_baseChangeFamily` — restriction of `g^*α` along an open immersion
  `i` of the base is `(i ≫ g)^*α`.
* `Stacks.Chow.pullbackInCycleClassImage_coprod_desc` — the coproduct clause of the Noetherian
  induction for Tag 0H59.

## Implementation notes

The restriction of `g^*α` along `i` is computed in three steps, each a statement about a single
fibre: the square defining `X ×_S V` is compared with the tautological square
`(X ×_S T) ×_T V` through the pasting isomorphism, restriction along the tautological square is
base change along `i` (the residue field extensions of an open immersion are trivial), and base
change along `i` after base change along `g` is base change along `i ≫ g`, transported along the
same pasting isomorphism (Tag 0H4X (2),
`Stacks.Chow.baseChangeFamily_baseChangeFamily_of_locallyOfFiniteType`).

## References

* [Stacks Project, Lemma 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
* [Stacks Project, Lemma 0H4X](https://stacks.math.columbia.edu/tag/0H4X)
* [Stacks Project, Lemma 0H59](https://stacks.math.columbia.edu/tag/0H59)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Extensionality on fibres -/

/-- Two morphisms into a fibre agree if they agree after the fibre inclusion and the projection
to the spectrum of the residue field. -/
private theorem fiber_hom_ext {X S A : Scheme.{u}} (p : X ⟶ S) (s : S) {a b : A ⟶ p.fiber s}
    (h₁ : a ≫ p.fiberι s = b ≫ p.fiberι s)
    (h₂ : a ≫ p.fiberToSpecResidueField s = b ≫ p.fiberToSpecResidueField s) : a = b :=
  pullback.hom_ext h₁ h₂

/-- Fibrewise cycles are equal if their coefficients are. -/
private theorem fiberCycleGroup_ext {X S : Scheme.{u}} {p : X ⟶ S} [LocallyOfFiniteType p]
    {s : S} {r : ℕ} {c d : FiberCycleGroup p s r}
    (h : ∀ x, (c : AlgebraicCycle (p.fiber s) ℤ) x = (d : AlgebraicCycle (p.fiber s) ℤ) x) :
    c = d :=
  Subtype.ext (Function.locallyFinsuppWithin.ext h)

/-! ### Base change at a point with trivial residue field extension -/

/-- At a point `t` where `κ(g t) ⟶ κ(t)` is an isomorphism, the coefficient of the base change of
a family of cycles at a point of the fibre over `t` is the coefficient of the original member at
the image point: the multiplicity in `Stacks.Chow.baseChangeFamily_apply` is one. -/
theorem baseChangeFamily_apply_of_isIso_residueFieldMap {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (t : S') [hres : IsIso (g.residueFieldMap t)] (r : ℕ)
    (α : FamilyOfCycles f r) (x : (pullback.snd f g).fiber t) :
    (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) := by
  rw [← fiberCycleAddEquiv_apply f g t hres r (α (g t)) x]
  by_cases hdim : relativeDimension (fieldChowSituation (S'.residueField t)).dimensionFunction
      ((pullback.snd f g).fiberToSpecResidueField t) x = (r : ℤ)
  · have hiso : IsIso (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
        pullback.condition t) :=
      @AlgebraicGeometry.isIso_baseChangeFiberMap _ _ _ f g t hres
    have hweight : flatPullbackWeight (fieldChowSituation (S'.residueField t))
        ((pullback.snd f g).fiberToSpecResidueField t)
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
        (r : ℤ) x = 1 :=
      flatPullbackWeight_of_isOpenImmersion (fieldChowSituation (S'.residueField t))
        ((pullback.snd f g).fiberToSpecResidueField t) _ (r : ℤ) x hdim
    have hleft : (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
        (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
            (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
              pullback.condition t x) *
          flatPullbackWeight (fieldChowSituation (S'.residueField t))
            ((pullback.snd f g).fiberToSpecResidueField t)
            (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
            (r : ℤ) x :=
      baseChangeFamily_apply f g r α t x
    rw [hleft, hweight, mul_one, fiberCycleAddEquiv_apply f g t hres r (α (g t)) x]
  · rw [fiberCycleGroup_apply_eq_zero (pullback.snd f g) t r (baseChangeFamily f g r α t) x hdim,
      fiberCycleGroup_apply_eq_zero (pullback.snd f g) t r
        (fiberCycleAddEquiv f g t hres r (α (g t))) x hdim]

/-- **Restriction along an open immersion of the base is base change along it.** For an open
immersion `i : V ⟶ S`, the restriction of a family of cycles on the fibres of `X/S` to the fibres
of `X ×_S V ⟶ V` along the tautological cartesian square is the base change along `i`. -/
theorem restrictedFamily_eq_baseChangeFamily {X S V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (i : V ⟶ S) [IsOpenImmersion i] (r : ℕ) (α : FamilyOfCycles f r) :
    (restrictedFamily f (pullback.snd f i) (pullback.fst f i) i pullback.condition r α).1 =
      baseChangeFamily f i r α := by
  funext t
  refine fiberCycleGroup_ext fun x ↦ ?_
  rw [(restrictedFamily f (pullback.snd f i) (pullback.fst f i) i pullback.condition r α).2 t x,
    baseChangeFamily_apply_of_isIso_residueFieldMap f i t r α x]

/-! ### Changing the square along which one restricts -/

/-- The fibre map of a commutative square factors through the fibre map of a second square over
the same base map, when the top edge of the first factors through that of the second. -/
theorem restrictedFiberMap_eq_fiberRestrict_comp {W T U₁ U₂ V : Scheme.{u}} (p : W ⟶ T)
    (p₁ : U₁ ⟶ V) (p₂ : U₂ ⟶ V) (j₁ : U₁ ⟶ W) (j₂ : U₂ ⟶ W) (i : V ⟶ T)
    (h₁ : j₁ ≫ p = p₁ ≫ i) (h₂ : j₂ ≫ p = p₂ ≫ i) (e : U₁ ⟶ U₂) (he₁ : e ≫ j₂ = j₁)
    (he₂ : e ≫ p₂ = p₁) (t : V) :
    restrictedFiberMap p p₁ j₁ i h₁ t =
      fiberRestrict p₂ p₁ e he₂ t ≫ restrictedFiberMap p p₂ j₂ i h₂ t := by
  refine fiber_hom_ext p (i t) ?_ ?_
  · rw [restrictedFiberMap_fiberι, Category.assoc, restrictedFiberMap_fiberι,
      fiberRestrict_fiberι_assoc, he₁]
  · rw [restrictedFiberMap_comp_fiberToSpecResidueField, Category.assoc,
      restrictedFiberMap_comp_fiberToSpecResidueField,
      fiberRestrict_fiberToSpecResidueField_assoc]

/-- **Restriction along two squares over the same open immersion of the base.** If the top edge
of the first square factors through that of the second by an open immersion `e`, the restriction
along the first square is the restriction along the second followed by restriction of fibrewise
cycles along `e`. -/
theorem restrictedFamily_apply_eq_fiberCycleRestrict {W T U₁ U₂ V : Scheme.{u}} (p : W ⟶ T)
    [LocallyOfFiniteType p] (p₁ : U₁ ⟶ V) [LocallyOfFiniteType p₁] (p₂ : U₂ ⟶ V)
    [LocallyOfFiniteType p₂] (j₁ : U₁ ⟶ W) [IsOpenImmersion j₁] (j₂ : U₂ ⟶ W)
    [IsOpenImmersion j₂] (i : V ⟶ T) [IsOpenImmersion i] (h₁ : j₁ ≫ p = p₁ ≫ i)
    (h₂ : j₂ ≫ p = p₂ ≫ i) (e : U₁ ⟶ U₂) [IsOpenImmersion e] (he₁ : e ≫ j₂ = j₁)
    (he₂ : e ≫ p₂ = p₁) (r : ℕ) (β : FamilyOfCycles p r) (t : V) :
    (restrictedFamily p p₁ j₁ i h₁ r β).1 t =
      fiberCycleRestrict p₂ p₁ e he₂ t r ((restrictedFamily p p₂ j₂ i h₂ r β).1 t) := by
  refine fiberCycleGroup_ext fun x ↦ ?_
  rw [(restrictedFamily p p₁ j₁ i h₁ r β).2 t x, fiberCycleRestrict_apply,
    (restrictedFamily p p₂ j₂ i h₂ r β).2 t,
    restrictedFiberMap_eq_fiberRestrict_comp p p₁ p₂ j₁ j₂ i h₁ h₂ e he₁ he₂ t,
    Scheme.Hom.comp_apply]

/-- **Restriction along a square over the identity of the base** is restriction of fibrewise
cycles along the top edge. -/
theorem restrictedFamily_id_apply {W T U : Scheme.{u}} (p : W ⟶ T) [LocallyOfFiniteType p]
    (p₁ : U ⟶ T) [LocallyOfFiniteType p₁] (j : U ⟶ W) [IsOpenImmersion j]
    (h : j ≫ p = p₁ ≫ 𝟙 T) (h' : j ≫ p = p₁) (r : ℕ) (β : FamilyOfCycles p r) (t : T) :
    (restrictedFamily p p₁ j (𝟙 T) h r β).1 t = fiberCycleRestrict p p₁ j h' t r (β t) := by
  have hmap : restrictedFiberMap p p₁ j (𝟙 T) h t = fiberRestrict p p₁ j h' t := by
    refine fiber_hom_ext p t ?_ ?_
    · exact (restrictedFiberMap_fiberι p p₁ j (𝟙 T) h t).trans
        (fiberRestrict_fiberι p p₁ j h' t).symm
    · refine (restrictedFiberMap_comp_fiberToSpecResidueField p p₁ j (𝟙 T) h t).trans ?_
      simp [fiberRestrict_fiberToSpecResidueField]
  refine fiberCycleGroup_ext fun x ↦ ?_
  rw [(restrictedFamily p p₁ j (𝟙 T) h r β).2 t x, fiberCycleRestrict_apply, ← hmap]
  rfl

/-- **Rigidity at one point.** Two families of cycles whose restrictions along a cartesian
square of open immersions agree over a point `t` agree over its image. -/
theorem fiberCycle_eq_of_restrictedFamily_apply_eq_of_isPullback {W T W₁ T₁ : Scheme.{u}}
    (p : W ⟶ T) [LocallyOfFiniteType p] (p₁ : W₁ ⟶ T₁) [LocallyOfFiniteType p₁] (j : W₁ ⟶ W)
    [IsOpenImmersion j] (i : T₁ ⟶ T) [IsOpenImmersion i] (h : j ≫ p = p₁ ≫ i)
    (hrange : (p : W → T) ⁻¹' Set.range (i : T₁ → T) ⊆ Set.range (j : W₁ → W)) {r : ℕ}
    (β γ : FamilyOfCycles p r) (t : T₁)
    (hres : (restrictedFamily p p₁ j i h r β).1 t = (restrictedFamily p p₁ j i h r γ).1 t) :
    β (i t) = γ (i t) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  obtain ⟨x, rfl⟩ :=
    surjective_restrictedFiberMap_of_preimage_subset_range p p₁ j i h hrange t y
  simpa only [(restrictedFamily p p₁ j i h r β).2 t x, (restrictedFamily p p₁ j i h r γ).2 t x]
    using congrArg (fun c : FiberCycleGroup p₁ t r ↦ (c : AlgebraicCycle (p₁.fiber t) ℤ) x) hres

/-- Restriction along a square of open immersions at a point `t` only depends on the member of
the family over the image of `t`. -/
theorem restrictedFamily_apply_congr {W T W₁ T₁ : Scheme.{u}} (p : W ⟶ T) [LocallyOfFiniteType p]
    (p₁ : W₁ ⟶ T₁) [LocallyOfFiniteType p₁] (j : W₁ ⟶ W) [IsOpenImmersion j] (i : T₁ ⟶ T)
    [IsOpenImmersion i] (h : j ≫ p = p₁ ≫ i) {r : ℕ} (β γ : FamilyOfCycles p r) (t : T₁)
    (he : β (i t) = γ (i t)) :
    (restrictedFamily p p₁ j i h r β).1 t = (restrictedFamily p p₁ j i h r γ).1 t := by
  refine fiberCycleGroup_ext fun x ↦ ?_
  rw [(restrictedFamily p p₁ j i h r β).2 t x, (restrictedFamily p p₁ j i h r γ).2 t x, he]

/-! ### Restriction of fibrewise cycles along a composite -/

/-- Restriction of fibrewise cycles along two open immersions in succession is restriction along
their composite. -/
theorem fiberCycleRestrict_fiberCycleRestrict {X₁ X₂ X₃ S : Scheme.{u}} (p₁ : X₁ ⟶ S)
    [LocallyOfFiniteType p₁] (p₂ : X₂ ⟶ S) [LocallyOfFiniteType p₂] (p₃ : X₃ ⟶ S)
    [LocallyOfFiniteType p₃] (e₁ : X₂ ⟶ X₁) [IsOpenImmersion e₁] (e₂ : X₃ ⟶ X₂)
    [IsOpenImmersion e₂] (h₁ : e₁ ≫ p₁ = p₂) (h₂ : e₂ ≫ p₂ = p₃) (s : S) (r : ℕ)
    (c : FiberCycleGroup p₁ s r) :
    fiberCycleRestrict p₂ p₃ e₂ h₂ s r (fiberCycleRestrict p₁ p₂ e₁ h₁ s r c) =
      fiberCycleRestrict p₁ p₃ (e₂ ≫ e₁) (by rw [Category.assoc, h₁, h₂]) s r c := by
  have hcomp : fiberRestrict p₂ p₃ e₂ h₂ s ≫ fiberRestrict p₁ p₂ e₁ h₁ s =
      fiberRestrict p₁ p₃ (e₂ ≫ e₁) (by rw [Category.assoc, h₁, h₂]) s := by
    refine fiber_hom_ext p₁ s ?_ ?_
    · rw [Category.assoc, fiberRestrict_fiberι, fiberRestrict_fiberι_assoc,
        fiberRestrict_fiberι]
    · rw [Category.assoc, fiberRestrict_fiberToSpecResidueField,
        fiberRestrict_fiberToSpecResidueField, fiberRestrict_fiberToSpecResidueField]
  refine fiberCycleGroup_ext fun x ↦ ?_
  rw [fiberCycleRestrict_apply, fiberCycleRestrict_apply, fiberCycleRestrict_apply, ← hcomp,
    Scheme.Hom.comp_apply]

/-- Restriction of fibrewise cycles along an open immersion equal to the identity does nothing. -/
theorem fiberCycleRestrict_eq_self {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (e : X ⟶ X) [IsOpenImmersion e] (h : e ≫ p = p) (he : e = 𝟙 X) (s : S) (r : ℕ)
    (c : FiberCycleGroup p s r) : fiberCycleRestrict p p e h s r c = c := by
  subst he
  have hid : fiberRestrict p p (𝟙 X) h s = 𝟙 _ := by
    refine fiber_hom_ext p s ?_ ?_
    · rw [fiberRestrict_fiberι, Category.comp_id, Category.id_comp]
    · rw [fiberRestrict_fiberToSpecResidueField, Category.id_comp]
  refine fiberCycleGroup_ext fun x ↦ ?_
  rw [fiberCycleRestrict_apply, hid]
  rfl

/-! ### Restriction of a base change along an open immersion of the base -/

/-- **Base change commutes with restriction to an open subscheme of the base**, the clause of
Tag 0H4R for families of cycles on fibres. Let `g : T ⟶ S`, let `i : V ⟶ T` be an open immersion
and let `j : X ×_S V ⟶ X ×_S T` be the induced open immersion, for `h = i ≫ g`. Then the
restriction of `g^*α` to the fibres of `X ×_S V ⟶ V` along the square `(j, i)` is `h^*α`.

The morphism `h` and the open immersion `j` are taken as data characterised by equations rather
than computed, so that the statement applies to any presentation of `X ×_S V`. -/
theorem restrictedFamily_baseChangeFamily {X S T V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : T ⟶ S) (i : V ⟶ T) [IsOpenImmersion i] (h : V ⟶ S)
    (hh : i ≫ g = h) (j : pullback f h ⟶ pullback f g) [IsOpenImmersion j]
    (hj₁ : j ≫ pullback.fst f g = pullback.fst f h)
    (hj₂ : j ≫ pullback.snd f g = pullback.snd f h ≫ i) (r : ℕ) (α : FamilyOfCycles f r) :
    (restrictedFamily (pullback.snd f g) (pullback.snd f h) j i hj₂ r
        (baseChangeFamily f g r α)).1 = baseChangeFamily f h r α := by
  subst hh
  funext t
  let e := pullbackLeftPullbackSndIso f g i
  have he₁ : e.inv ≫ pullback.fst (pullback.snd f g) i = j := pullback.hom_ext
    (by rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst, hj₁])
    (by rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, hj₂])
  rw [restrictedFamily_apply_eq_fiberCycleRestrict (pullback.snd f g) (pullback.snd f (i ≫ g))
      (pullback.snd (pullback.snd f g) i) j (pullback.fst (pullback.snd f g) i) i hj₂
      pullback.condition e.inv he₁ (pullbackLeftPullbackSndIso_inv_snd_snd f g i) r
      (baseChangeFamily f g r α) t,
    restrictedFamily_eq_baseChangeFamily (pullback.snd f g) i r (baseChangeFamily f g r α),
    baseChangeFamily_baseChangeFamily_of_locallyOfFiniteType f g i r α t,
    fiberCycleRestrict_fiberCycleRestrict]
  exact fiberCycleRestrict_eq_self _ _ _ e.inv_hom_id _ r _

/-! ### The coproduct clause of the Noetherian induction for Tag 0H59 -/

/-- **The coproduct clause of the Noetherian induction for Tag 0H59.** If the base changes of `α`
along `g₁ : T₁ ⟶ S` and along `g₂ : T₂ ⟶ S` are in the image of the cycle class map, so is its
base change along `coprod.desc g₁ g₂ : T₁ ⨿ T₂ ⟶ S`.

`Stacks.Chow.exists_cycleClassMap_eq_of_restrictedFamily_coprod` assembles the two cycle classes
and shows that every family with the right restrictions to the two summands is the assembled
class; that `(coprod.desc g₁ g₂)^*α` has those restrictions is
`Stacks.Chow.restrictedFamily_baseChangeFamily`. -/
theorem pullbackInCycleClassImage_coprod_desc {X S T₁ T₂ : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (r : ℕ) (α : FamilyOfCycles f r)
    (g₁ : T₁ ⟶ S) (g₂ : T₂ ⟶ S) (H₁ : PullbackInCycleClassImage f r α g₁)
    (H₂ : PullbackInCycleClassImage f r α g₂) :
    PullbackInCycleClassImage f r α (coprod.desc g₁ g₂) :=
  exists_cycleClassMap_eq_of_restrictedFamily_coprod f r α g₁ g₂ H₁ H₂ _
    (restrictedFamily_baseChangeFamily f (coprod.desc g₁ g₂) coprod.inl g₁
      (coprod.inl_desc g₁ g₂) (coprodBaseChangeInl f g₁ g₂) (pullback.lift_fst _ _ _)
      (coprodBaseChangeInl_snd f g₁ g₂) r α)
    (restrictedFamily_baseChangeFamily f (coprod.desc g₁ g₂) coprod.inr g₂
      (coprod.inr_desc g₁ g₂) (coprodBaseChangeInr f g₁ g₂) (pullback.lift_fst _ _ _)
      (coprodBaseChangeInr_snd f g₁ g₂) r α)

end Stacks.Chow

end
