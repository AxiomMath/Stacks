module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatPullbackFamily
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.SeminormalLift
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative cycles and base change along a universal homeomorphism

Let `g : S' ⟶ S` be a universal homeomorphism of locally Noetherian schemes which induces
isomorphisms on all residue fields, let `f : X ⟶ S` be locally of finite type, let `X' = S' ×_S X`
and let `r ≥ 0`. Base change along `g` is then a bijection `z(X/S, r) ⟶ z(X'/S', r)` of groups of
relative `r`-cycles.

## Main definitions

* `Stacks.Chow.relativeCyclesAddEquivOfUniversalHomeomorphism` — **Stacks 0H5G**: base change
  along `g` as an additive equivalence `z(X/S, r) ≃ z(X'/S', r)`.

## Main results

* `Stacks.Chow.baseChangeFamily_eq_baseChangeFamilyOfResidueIso` — along a morphism inducing
  isomorphisms on residue fields the base change of a family of cycles on fibres is the
  fibrewise transport of that family, with no multiplicity.
* `Stacks.Chow.baseChangeFamilyOfCyclesAddEquiv_eq_baseChangeFamily` — the additive equivalence
  of Stacks 0H4Y is base change of families of cycles on fibres.
* `Stacks.Chow.baseChangeFamily_baseChangeFamily` — base change to `S'` followed by base change
  to a further base `T` is base change to `T`, read through the comparison isomorphism
  `(X ×_S S') ×_{S'} T ≅ X ×_S T`.
* `Stacks.Chow.isRelativeCycle_baseChangeFamily_iff` — a family of `r`-cycles on the fibres of
  `X/S` is a relative `r`-cycle if and only if its base change is one.
* `Stacks.Chow.relativeCyclesAddEquivOfUniversalHomeomorphism_coe` — **Stacks 0H5G**: that
  equivalence is base change, read on the underlying families of fibrewise cycles.

## Implementation notes

### The route

The bijection on all families of cycles on fibres is Stacks 0H4Y, available as
`Stacks.Chow.baseChangeFamilyOfCyclesAddEquiv` because a universal homeomorphism is bijective on
points. What has to be added is that it matches the subgroups of relative cycles, which is the
valuative criterion of Definition 0H50 on both sides.

Both directions of that comparison rest on one identity: for `h' : T ⟶ S'` the base change of
`g^*α` along `h'` is the base change of `α` along `h' ≫ g`, read through the comparison
isomorphism `(X ×_S S') ×_{S'} T ≅ X ×_S T`. Since the isomorphism is in particular an open
immersion, reading through it is `Stacks.Chow.fiberCycleRestrict`, and the two inputs needed —
that it commutes with the specialization map and that it is injective — are the open-immersion
case of Tag 0H4L, `Stacks.Chow.specializationCycle_fiberCycleRestrict`, and the surjectivity on
points of an isomorphism. The valuative condition for `α` at a morphism `h : Spec R ⟶ S` and the
valuative condition for `g^*α` at a lift `h'` of `h` are therefore equivalent.

What makes every morphism `h : Spec R ⟶ S` from the spectrum of a discrete valuation ring admit
such a lift is `AlgebraicGeometry.exists_comp_eq_of_isSeminormal`: `Spec R` is a seminormal
scheme because a discrete valuation ring is an integrally closed domain.

### Multiplicities

The coefficient formula for a general base change of a family of cycles on fibres,
`Stacks.Chow.baseChangeFamily_apply`, carries the multiplicity with which a point enters the
inverse image of the reduced closure of its image. For `g` inducing isomorphisms on residue
fields the morphism of fibres is an isomorphism, so that multiplicity is one on the points of
relative dimension `r` and both descriptions of the base change vanish elsewhere, being cycles
of relative dimension `r`. That is `Stacks.Chow.baseChangeFamily_eq_baseChangeFamilyOfResidueIso`
and it is what pins the equivalence of Stacks 0H4Y to base change.

## References

* [Stacks Project, Lemma 0H5G](https://stacks.math.columbia.edu/tag/0H5G)
* [Stacks Project, Lemma 0H4Y](https://stacks.math.columbia.edu/tag/0H4Y)
* [Stacks Project, Lemma 0H4L](https://stacks.math.columbia.edu/tag/0H4L)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Two elementary facts about fibrewise cycle groups -/

/-- A fibrewise `r`-cycle vanishes at every point of relative dimension other than `r`. -/
theorem fiberCycleGroup_apply_eq_zero {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (s : S) (r : ℕ) (c : FiberCycleGroup p s r) (x : p.fiber s)
    (hx : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (p.fiberToSpecResidueField s) x ≠ (r : ℤ)) :
    (c : AlgebraicCycle (p.fiber s) ℤ) x = 0 := by
  by_contra hne
  exact hx ((mem_cyclesOfDimension_iff_forall_point _ _ _ _).1 c.2 x hne)

/-- The morphism of fibres induced by an isomorphism of the source over the base is an
isomorphism. -/
private theorem isIso_fiberRestrict_of_isIso {X S U : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFiniteType p] (pU : U ⟶ S) [LocallyOfFiniteType pU] (j : U ⟶ X) [IsIso j]
    (hj : j ≫ p = pU) (s : S) : IsIso (fiberRestrict p pU j hj s) :=
  (isPullback_pullbackRestrict p pU j hj (S.fromSpecResidueField s)).flip.isIso_fst_of_isIso

/-- Restriction of fibrewise cycles along an isomorphism of the source over the base is
injective: the induced morphism of fibres is again an isomorphism, hence surjective. No dimension
hypothesis is needed; for an open immersion under the dimension hypothesis of Tag 0H5F see
`Stacks.Chow.fiberCycleRestrict_injective`. -/
theorem fiberCycleRestrict_injective_of_isIso {X S U : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFiniteType p] (pU : U ⟶ S) [LocallyOfFiniteType pU] (j : U ⟶ X) [IsIso j]
    (hj : j ≫ p = pU) (s : S) (r : ℕ) :
    Function.Injective (fiberCycleRestrict p pU j hj s r) := by
  have hiso := isIso_fiberRestrict_of_isIso p pU j hj s
  intro c d hcd
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  have hx : fiberRestrict p pU j hj s (inv (fiberRestrict p pU j hj s) x) = x := by
    change ((inv (fiberRestrict p pU j hj s) ≫ fiberRestrict p pU j hj s)) x = x
    rw [IsIso.inv_hom_id]
    rfl
  simpa only [fiberCycleRestrict_apply, hx] using congrArg (fun e : FiberCycleGroup pU s r =>
    (e : AlgebraicCycle (pU.fiber s) ℤ) (inv (fiberRestrict p pU j hj s) x)) hcd

/-! ### Base change along a morphism inducing isomorphisms on residue fields -/

variable {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)

/-- Along a morphism inducing isomorphisms on all residue fields the base change of a family of
cycles on fibres is the fibrewise transport of that family: the multiplicity in
`Stacks.Chow.baseChangeFamily_apply` is one at every point of relative dimension `r`, and off
relative dimension `r` both families vanish. -/
theorem baseChangeFamily_eq_baseChangeFamilyOfResidueIso
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ) (α : FamilyOfCycles f r) :
    baseChangeFamily f g r α = baseChangeFamilyOfResidueIso f g hres r α := by
  funext t
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  by_cases hdim : relativeDimension (fieldChowSituation (S'.residueField t)).dimensionFunction
      ((pullback.snd f g).fiberToSpecResidueField t) x = (r : ℤ)
  · have hiso : IsIso (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
        pullback.condition t) :=
      @AlgebraicGeometry.isIso_baseChangeFiberMap _ _ _ f g t (hres t)
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
    rw [hleft, hweight, mul_one, baseChangeFamilyOfResidueIso_apply f g hres r α t x]
  · rw [fiberCycleGroup_apply_eq_zero (pullback.snd f g) t r (baseChangeFamily f g r α t) x hdim,
      fiberCycleGroup_apply_eq_zero (pullback.snd f g) t r
        (baseChangeFamilyOfResidueIso f g hres r α t) x hdim]

/-- **Stacks Project, Tag 0H4Y.** The additive equivalence of groups of families of cycles on
fibres attached to a morphism bijective on points and inducing isomorphisms on residue fields is
base change of families of cycles. -/
theorem baseChangeFamilyOfCyclesAddEquiv_eq_baseChangeFamily (hg : Function.Bijective g)
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ) (α : FamilyOfCycles f r) :
    baseChangeFamilyOfCyclesAddEquiv f g hg hres r α = baseChangeFamily f g r α := by
  rw [baseChangeFamily_eq_baseChangeFamilyOfResidueIso f g hres r α]
  funext t
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  rw [baseChangeFamilyOfCyclesAddEquiv_apply f g hg hres r α t x,
    baseChangeFamilyOfResidueIso_apply f g hres r α t x]

/-! ### Composing two base changes -/

variable {T : Scheme.{u}} (h' : T ⟶ S')

omit [LocallyOfFiniteType f] in
/-- The comparison isomorphism `(X ×_S S') ×_{S'} T ≅ X ×_S T` carries the morphism of fibres
over `t` induced by the projection to `X ×_S S'`, followed by the morphism of fibres induced by
the projection to `X`, to the morphism of fibres induced by the projection to `X` of the direct
base change. -/
theorem restrictedFiberMap_comp_restrictedFiberMap (t : T) :
    restrictedFiberMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h')
          (pullback.fst (pullback.snd f g) h') h' pullback.condition t ≫
        restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition (h' t) =
      fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
          (pullbackLeftPullbackSndIso f g h').hom
          (pullbackLeftPullbackSndIso_hom_snd f g h') t ≫
        restrictedFiberMap f (pullback.snd f (h' ≫ g)) (pullback.fst f (h' ≫ g)) (h' ≫ g)
          pullback.condition t := by
  have hL₁ : (restrictedFiberMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h')
          (pullback.fst (pullback.snd f g) h') h' pullback.condition t ≫
        restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition (h' t)) ≫
      f.fiberι (g (h' t)) =
      ((pullback.snd (pullback.snd f g) h').fiberι t ≫
        pullback.fst (pullback.snd f g) h') ≫ pullback.fst f g := by
    rw [Category.assoc, restrictedFiberMap_fiberι, ← Category.assoc, restrictedFiberMap_fiberι]
  have hR₁ : (fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
          (pullbackLeftPullbackSndIso f g h').hom
          (pullbackLeftPullbackSndIso_hom_snd f g h') t ≫
        restrictedFiberMap f (pullback.snd f (h' ≫ g)) (pullback.fst f (h' ≫ g)) (h' ≫ g)
          pullback.condition t) ≫ f.fiberι ((h' ≫ g) t) =
      ((pullback.snd (pullback.snd f g) h').fiberι t ≫
        pullback.fst (pullback.snd f g) h') ≫ pullback.fst f g := by
    rw [Category.assoc, restrictedFiberMap_fiberι, ← Category.assoc, fiberRestrict_fiberι,
      Category.assoc, pullbackLeftPullbackSndIso_hom_fst, ← Category.assoc]
  have hL₂ : (restrictedFiberMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h')
          (pullback.fst (pullback.snd f g) h') h' pullback.condition t ≫
        restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition (h' t)) ≫
      f.fiberToSpecResidueField (g (h' t)) =
      ((pullback.snd (pullback.snd f g) h').fiberToSpecResidueField t ≫
        Spec.map (h'.residueFieldMap t)) ≫ Spec.map (g.residueFieldMap (h' t)) := by
    rw [Category.assoc, restrictedFiberMap_comp_fiberToSpecResidueField, ← Category.assoc,
      restrictedFiberMap_comp_fiberToSpecResidueField]
  have hR₂ : (fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
          (pullbackLeftPullbackSndIso f g h').hom
          (pullbackLeftPullbackSndIso_hom_snd f g h') t ≫
        restrictedFiberMap f (pullback.snd f (h' ≫ g)) (pullback.fst f (h' ≫ g)) (h' ≫ g)
          pullback.condition t) ≫ f.fiberToSpecResidueField ((h' ≫ g) t) =
      ((pullback.snd (pullback.snd f g) h').fiberToSpecResidueField t ≫
        Spec.map (h'.residueFieldMap t)) ≫ Spec.map (g.residueFieldMap (h' t)) := by
    rw [Category.assoc, restrictedFiberMap_comp_fiberToSpecResidueField, ← Category.assoc,
      fiberRestrict_fiberToSpecResidueField,
      (congrArg Spec.map (Scheme.residueFieldMap_comp h' g t)).trans (Spec.map_comp _ _)]
    exact (Category.assoc _ _ _).symm
  exact pullback.hom_ext (hL₁.trans hR₁.symm) (hL₂.trans hR₂.symm)

/-- Base change of a family of cycles on fibres along `g` followed by base change along
`h' : T ⟶ S'` is base change along `h' ≫ g`, read through the comparison isomorphism
`(X ×_S S') ×_{S'} T ≅ X ×_S T`.

The coefficient of either side at a point of the fibre over `t` is the coefficient of `α` at the
image point in the fibre of `X/S`, times the multiplicity with which the point enters the inverse
image of the reduced closure of that image; the images agree by
`Stacks.Chow.restrictedFiberMap_comp_restrictedFiberMap` and the multiplicities agree by
`Stacks.Chow.flatPullbackWeight_eq_of_isIso`, the two legs of the square being the isomorphisms
induced on fibres by `g` and by the comparison isomorphism. -/
theorem baseChangeFamily_baseChangeFamily
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ) (α : FamilyOfCycles f r) (t : T) :
    baseChangeFamily (pullback.snd f g) h' r (baseChangeFamily f g r α) t =
      fiberCycleRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
        (pullbackLeftPullbackSndIso f g h').hom
        (pullbackLeftPullbackSndIso_hom_snd f g h') t r
        (baseChangeFamily f (h' ≫ g) r α t) := by
  have hu₁ := isIso_fiberRestrict_of_isIso (pullback.snd f (h' ≫ g))
    (pullback.snd (pullback.snd f g) h') (pullbackLeftPullbackSndIso f g h').hom
    (pullbackLeftPullbackSndIso_hom_snd f g h') t
  have hu₀ : IsIso (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition (h' t)) :=
    @AlgebraicGeometry.isIso_baseChangeFiberMap _ _ _ f g (h' t) (hres (h' t))
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  have hweight := flatPullbackWeight_eq_of_isIso (fieldChowSituation (T.residueField t))
    ((pullback.snd (pullback.snd f g) h').fiberToSpecResidueField t)
    ((pullback.snd f (h' ≫ g)).fiberToSpecResidueField t)
    (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition (h' t))
    (fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
      (pullbackLeftPullbackSndIso f g h').hom
      (pullbackLeftPullbackSndIso_hom_snd f g h') t)
    (fiberRestrict_fiberToSpecResidueField (pullback.snd f (h' ≫ g))
      (pullback.snd (pullback.snd f g) h') (pullbackLeftPullbackSndIso f g h').hom
      (pullbackLeftPullbackSndIso_hom_snd f g h') t)
    (restrictedFiberMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h')
      (pullback.fst (pullback.snd f g) h') h' pullback.condition t)
    (restrictedFiberMap f (pullback.snd f (h' ≫ g)) (pullback.fst f (h' ≫ g)) (h' ≫ g)
      pullback.condition t)
    (restrictedFiberMap_comp_restrictedFiberMap f g h' t) (r : ℤ) y
  have hpt := congrArg
    (fun m : (pullback.snd (pullback.snd f g) h').fiber t ⟶ f.fiber ((h' ≫ g) t) => m y)
    (restrictedFiberMap_comp_restrictedFiberMap f g h' t)
  have hLHS : (baseChangeFamily (pullback.snd f g) h' r (baseChangeFamily f g r α) t :
        AlgebraicCycle ((pullback.snd (pullback.snd f g) h').fiber t) ℤ) y =
      (baseChangeFamily f g r α (h' t) :
            AlgebraicCycle ((pullback.snd f g).fiber (h' t)) ℤ)
          (restrictedFiberMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h')
            (pullback.fst (pullback.snd f g) h') h' pullback.condition t y) *
        flatPullbackWeight (fieldChowSituation (T.residueField t))
          ((pullback.snd (pullback.snd f g) h').fiberToSpecResidueField t)
          (restrictedFiberMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h')
            (pullback.fst (pullback.snd f g) h') h' pullback.condition t) (r : ℤ) y :=
    baseChangeFamily_apply (pullback.snd f g) h' r (baseChangeFamily f g r α) t y
  have hRHS : (baseChangeFamily f (h' ≫ g) r α t :
        AlgebraicCycle ((pullback.snd f (h' ≫ g)).fiber t) ℤ)
      (fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
        (pullbackLeftPullbackSndIso f g h').hom
        (pullbackLeftPullbackSndIso_hom_snd f g h') t y) =
      (α ((h' ≫ g) t) : AlgebraicCycle (f.fiber ((h' ≫ g) t)) ℤ)
          ((restrictedFiberMap f (pullback.snd f (h' ≫ g)) (pullback.fst f (h' ≫ g)) (h' ≫ g)
            pullback.condition t)
            (fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
              (pullbackLeftPullbackSndIso f g h').hom
              (pullbackLeftPullbackSndIso_hom_snd f g h') t y)) *
        flatPullbackWeight (fieldChowSituation (T.residueField t))
          ((pullback.snd f (h' ≫ g)).fiberToSpecResidueField t)
          (restrictedFiberMap f (pullback.snd f (h' ≫ g)) (pullback.fst f (h' ≫ g)) (h' ≫ g)
            pullback.condition t) (r : ℤ)
          (fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
            (pullbackLeftPullbackSndIso f g h').hom
            (pullbackLeftPullbackSndIso_hom_snd f g h') t y) :=
    baseChangeFamily_apply f (h' ≫ g) r α t _
  rw [fiberCycleRestrict_apply, hRHS, hLHS,
    baseChangeFamily_eq_baseChangeFamilyOfResidueIso f g hres r α,
    baseChangeFamilyOfResidueIso_apply f g hres r α (h' t) _, hweight]
  exact congrArg (fun z : f.fiber ((h' ≫ g) t) =>
      (α ((h' ≫ g) t) : AlgebraicCycle (f.fiber ((h' ≫ g) t)) ℤ) z *
        flatPullbackWeight (fieldChowSituation (T.residueField t))
          ((pullback.snd f (h' ≫ g)).fiberToSpecResidueField t)
          (restrictedFiberMap f (pullback.snd f (h' ≫ g)) (pullback.fst f (h' ≫ g)) (h' ≫ g)
            pullback.condition t) (r : ℤ)
          (fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
            (pullbackLeftPullbackSndIso f g h').hom
            (pullbackLeftPullbackSndIso_hom_snd f g h') t y)) hpt

/-- The valuative condition for `g^*α` at `k` is equivalent to the valuative condition for `α` at
`k ≫ g`. -/
private theorem specializationCycle_baseChangeFamily_iff {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ)
    (α : FamilyOfCycles f r) (k : Spec (.of R) ⟶ S') :
    specializationCycle (pullback.snd (pullback.snd f g) k) r
        (baseChangeFamily (pullback.snd f g) k r (baseChangeFamily f g r α)
          (genericPoint (Spec (.of R)))) =
      baseChangeFamily (pullback.snd f g) k r (baseChangeFamily f g r α)
        (IsLocalRing.closedPoint R) ↔
    specializationCycle (pullback.snd f (k ≫ g)) r
        (baseChangeFamily f (k ≫ g) r α (genericPoint (Spec (.of R)))) =
      baseChangeFamily f (k ≫ g) r α (IsLocalRing.closedPoint R) := by
  rw [baseChangeFamily_baseChangeFamily f g k hres r α (genericPoint (Spec (.of R))),
    baseChangeFamily_baseChangeFamily f g k hres r α (IsLocalRing.closedPoint R),
    specializationCycle_fiberCycleRestrict (pullback.snd f (k ≫ g))
      (pullback.snd (pullback.snd f g) k) (pullbackLeftPullbackSndIso f g k).hom
      (pullbackLeftPullbackSndIso_hom_snd f g k) r
      (baseChangeFamily f (k ≫ g) r α (genericPoint (Spec (.of R))))]
  exact (fiberCycleRestrict_injective_of_isIso (pullback.snd f (k ≫ g))
    (pullback.snd (pullback.snd f g) k) (pullbackLeftPullbackSndIso f g k).hom
    (pullbackLeftPullbackSndIso_hom_snd f g k) (IsLocalRing.closedPoint R) r).eq_iff

/-! ### Stacks 0H5G -/

section Main

variable [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [UniversalHomeomorphism g]

/-- A family of `r`-cycles on the fibres of `X/S` is a relative `r`-cycle if and only if its base
change along a universal homeomorphism `g : S' ⟶ S` inducing isomorphisms on all residue fields
is a relative `r`-cycle on `X'/S'`.

Both directions compare the valuative condition for `α` at `h' ≫ g` with the valuative condition
for `g^*α` at `h'`, using `Stacks.Chow.baseChangeFamily_baseChangeFamily` and the open-immersion
case of Tag 0H4L. For the converse direction every morphism from the spectrum of a discrete
valuation ring to `S` is of the form `h' ≫ g`, because such a spectrum is seminormal. -/
theorem isRelativeCycle_baseChangeFamily_iff
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ) (α : FamilyOfCycles f r) :
    IsRelativeCycle f r α ↔
      IsRelativeCycle (pullback.snd f g) r (baseChangeFamily f g r α) := by
  refine ⟨fun hα R _ _ _ h' ↦ ?_, fun hβ R _ _ _ h ↦ ?_⟩
  · exact (specializationCycle_baseChangeFamily_iff f g hres r α h').2 (hα R (h' ≫ g))
  · obtain ⟨h', rfl⟩ := exists_comp_eq_of_isSeminormal g hres h
      (isSeminormal_spec_of_isDiscreteValuationRing R)
    exact (specializationCycle_baseChangeFamily_iff f g hres r α h').1 (hβ R h')

/-- **Stacks Project, Lemma 0H5G.** Let `g : S' ⟶ S` be a universal homeomorphism of locally
Noetherian schemes which induces isomorphisms on all residue fields, let `f : X ⟶ S` be locally
of finite type, let `X' = S' ×_S X` and let `r ≥ 0`. Base change along `g` is an additive
equivalence `z(X/S, r) ≃ z(X'/S', r)` of groups of relative `r`-cycles. -/
@[stacks 0H5G "the bijection z(X/S, r) → z(X'/S', r) determined by base change"]
def relativeCyclesAddEquivOfUniversalHomeomorphism
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ) :
    ↥(relativeCycles f r) ≃+ ↥(relativeCycles (pullback.snd f g) r) where
  toFun α := ⟨baseChangeFamilyOfCyclesAddEquiv f g
    (bijective_base_of_universalHomeomorphism g) hres r α.1, by
      rw [baseChangeFamilyOfCyclesAddEquiv_eq_baseChangeFamily f g
        (bijective_base_of_universalHomeomorphism g) hres r α.1]
      exact (isRelativeCycle_baseChangeFamily_iff f g hres r α.1).mp α.2⟩
  invFun β := ⟨(baseChangeFamilyOfCyclesAddEquiv f g
    (bijective_base_of_universalHomeomorphism g) hres r).symm β.1, by
      refine (isRelativeCycle_baseChangeFamily_iff f g hres r _).mpr ?_
      rw [← baseChangeFamilyOfCyclesAddEquiv_eq_baseChangeFamily f g
          (bijective_base_of_universalHomeomorphism g) hres r,
        (baseChangeFamilyOfCyclesAddEquiv f g
          (bijective_base_of_universalHomeomorphism g) hres r).apply_symm_apply]
      exact β.2⟩
  left_inv α := Subtype.ext ((baseChangeFamilyOfCyclesAddEquiv f g
    (bijective_base_of_universalHomeomorphism g) hres r).symm_apply_apply α.1)
  right_inv β := Subtype.ext ((baseChangeFamilyOfCyclesAddEquiv f g
    (bijective_base_of_universalHomeomorphism g) hres r).apply_symm_apply β.1)
  map_add' α β := Subtype.ext (map_add (baseChangeFamilyOfCyclesAddEquiv f g
    (bijective_base_of_universalHomeomorphism g) hres r) α.1 β.1)

/-- **Stacks Project, Lemma 0H5G.** The additive equivalence of relative `r`-cycles attached to a
universal homeomorphism inducing isomorphisms on all residue fields is base change: the family of
fibrewise cycles underlying the image of `α` is the base change of the family underlying `α`. -/
@[simp, stacks 0H5G "the bijection is base change of families of cycles on fibres"]
theorem relativeCyclesAddEquivOfUniversalHomeomorphism_coe
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ) (α : ↥(relativeCycles f r)) :
    (relativeCyclesAddEquivOfUniversalHomeomorphism f g hres r α).1 =
      baseChangeFamily f g r α.1 :=
  baseChangeFamilyOfCyclesAddEquiv_eq_baseChangeFamily f g
    (bijective_base_of_universalHomeomorphism g) hres r α.1

end Main

end Stacks.Chow

end

