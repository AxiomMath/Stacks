module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Compatibilities
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatPullbackSupport
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationFlatPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat descent for relative cycles

Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian, let `r, e ≥ 0`, let `α` be
a family of `r`-cycles on the fibres of `X/S`, and let `{f_i : X_i ⟶ X}` be a jointly surjective
family of flat morphisms, locally of finite type and of relative dimension `e`. This file proves
Lemma 0H53: `α` is a relative `r`-cycle if and only if every flat pullback `f_i^*α` is a relative
`(r+e)`-cycle.

The three ingredients are supplied here or imported:

* base change of the base scheme commutes with flat pullback of families of cycles on fibres,
  part (3) of Lemma 0H4P, imported as `Stacks.Chow.baseChangeFamily_flatPullbackFamily` from
  `./Compatibilities.lean`. It is used here one fibre at a time, which is
  `Stacks.Chow.baseChangeFamily_flatPullbackFamily_apply` below.
* specialization commutes with flat pullback over a discrete valuation ring, which is Lemma 0H4L,
  imported as `Stacks.Chow.specializationCycle_baseChangedFiberCycleFlatPullback`.
* the flat pullbacks along a jointly surjective family are jointly injective,
  `Stacks.Chow.eq_of_forall_baseChangedFiberCycleFlatPullback`. A cycle with a nonzero
  coefficient at a point `y` has a nonzero coefficient, in one of the pullbacks, at a generic
  point of the inverse image of the reduced closure of `y`: such a point lies over `y` and has
  relative dimension `e` more by Tag 02R8, so the pullback weight there does not vanish.

## Main results

* `Stacks.Chow.baseChangeFamily_flatPullbackFamily_apply` — Lemma 0H4P part (3) on one fibre.
* `Stacks.Chow.eq_zero_of_forall_flatPullback_eq_zero` — a cycle all of whose flat pullbacks
  along a jointly surjective family vanish is zero.
* `Stacks.Chow.eq_of_forall_baseChangedFiberCycleFlatPullback` — the joint injectivity used over
  the closed point of a discrete valuation ring.
* `Stacks.Chow.isRelativeCycle_flatPullbackFamily` — **the flat pullback clause of Lemma 0H51**:
  the flat pullback of a relative `r`-cycle along a single flat morphism locally of finite type
  and of relative dimension `e` is a relative `(r + e)`-cycle.
* `Stacks.Chow.isRelativeCycle_iff_forall_flatPullbackFamily` — **Lemma 0H53**.
* `Stacks.Chow.mem_relativeCycles_iff_forall_flatPullbackFamily` — Lemma 0H53 read as membership
  in `z(X/S, r)`.

## Implementation notes

Joint surjectivity is transported along base change by
`Stacks.Chow.exists_pullbackRestrict_eq`, which is applied twice to reach the fibres of a base
change: once along `g : T ⟶ S`, and once along the morphism from the spectrum of a residue
field, since `Stacks.Chow.fiberRestrict` is by definition the second of these base changes.

## References

* [Stacks Project, Lemma 0H53](https://stacks.math.columbia.edu/tag/0H53)
* [Stacks Project, Lemma 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
* [Stacks Project, Lemma 0H4L](https://stacks.math.columbia.edu/tag/0H4L)
* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace Stacks.Chow

/-! ### Base change of a flat pullback of a family of cycles on fibres -/

/-- **Stacks Project, Lemma 0H4P, part (3), read on a single fibre.** The base change along
`g : T ⟶ S` of the flat pullback `j^*α`, taken on the fibre over `t`, is the flat pullback along
the base change of `j` of the fibre of `g^*α` over `t`.

This is the equality of the two families, `Stacks.Chow.baseChangeFamily_flatPullbackFamily` of
`./Compatibilities.lean`, evaluated at `t`: the flat pullback of a family at a point is the flat
pullback on that fibre by `Stacks.Chow.flatPullbackFamily_apply`, and
`Stacks.Chow.baseChangedFiberCycleFlatPullback` is that homomorphism by definition. -/
theorem baseChangeFamily_flatPullbackFamily_apply {X S U T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [LocallyOfFiniteType j] [Flat j] (hj : j ≫ f = fU) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e) (g : T ⟶ S) (r : ℕ)
    (α : FamilyOfCycles f r) (t : T) :
    baseChangeFamily fU g (r + e) (flatPullbackFamily f fU j hj e he r α) t =
      baseChangedFiberCycleFlatPullback f fU j hj e he g t r (baseChangeFamily f g r α t) := by
  rw [baseChangeFamily_flatPullbackFamily f fU j hj e he g r α]
  rfl

/-! ### Joint injectivity of flat pullback along a jointly surjective family -/

/-- A cycle all of whose flat pullbacks along a jointly surjective family of flat morphisms of
relative dimension `e` vanish is itself zero.

At a point `y` carrying a nonzero coefficient, pick a member of the family with a point above
`y`; inside the inverse image of the reduced closure of `y` that point generizes to a generic
point, which lies over `y` and has relative dimension `e` more, so the pullback reads the
coefficient at `y` there with a nonzero weight. -/
theorem eq_zero_of_forall_flatPullback_eq_zero (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {Idx : Type v} {Tm : Idx → Scheme.{u}}
    (sT : ∀ i, Tm i ⟶ C.S) [∀ i, LocallyOfFiniteType (sT i)] (m : ∀ i, Tm i ⟶ Y)
    [∀ i, LocallyOfFiniteType (m i)] [∀ i, Flat (m i)] (hbase : ∀ i, m i ≫ sY = sT i) (e : ℕ)
    (hrel : ∀ i, AlgebraicGeometry.RelativeDimension (m i) e)
    (hsurj : ∀ y : Y, ∃ i, ∃ x : Tm i, (m i).base x = y) (k : ℤ) (c : CycleGroup C sY k)
    (hpb : ∀ i, flatPullback C (sT i) sY (m i) (hbase i) e (hrel i) k c = 0) :
    c = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  change (c : AlgebraicCycle Y ℤ) y = 0
  by_contra hne
  obtain ⟨i, x, hxy⟩ := hsurj y
  obtain ⟨ξ, -, hιy⟩ := exists_comap_genericPoint_over (m i) y x hxy
  have hdim : relativeDimension C.dimensionFunction (sT i)
      ((((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap (m i)).subschemeι).base ξ.1) = k + (e : ℤ) := by
    rw [relativeDimension_comap_genericPoint_eq_add C sY (sT i) (m i) (hbase i) e (hrel i) y ξ,
      (mem_cyclesOfDimension_iff_forall_point C sY k (c : AlgebraicCycle Y ℤ)).1 c.2 y hne]
  have hcoeff : (flatPullback C (sT i) sY (m i) (hbase i) e (hrel i) k c).1
      ((((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap (m i)).subschemeι).base ξ.1) = 0 := by
    rw [hpb i]
    rfl
  rw [flatPullback_apply C (sT i) sY (m i) (hbase i) e (hrel i) k c _, hιy] at hcoeff
  exact mul_ne_zero hne
    (flatPullbackWeight_ne_zero_of_genericPoint C (sT i) (m i) (k + (e : ℤ)) y _ ξ rfl hιy hdim)
    hcoeff

/-! ### Transporting joint surjectivity along base change -/

/-- Joint surjectivity of a family of morphisms of schemes over `S` is inherited by the family of
base changes along `g : T ⟶ S`: a point of `X ×_S T` whose image in `X` is hit by `p i` is hit by
the base change of `p i`, since the image of a base change is the inverse image of the image. -/
theorem exists_pullbackRestrict_eq {Idx : Type v} {X S T : Scheme.{u}} {Y : Idx → Scheme.{u}}
    (f : X ⟶ S) (fY : ∀ i, Y i ⟶ S) (p : ∀ i, Y i ⟶ X) (hY : ∀ i, p i ≫ f = fY i)
    (hsurj : ∀ x : X, ∃ i, ∃ y : Y i, (p i).base y = x) (g : T ⟶ S)
    (w : (pullback f g : Scheme.{u})) :
    ∃ i, ∃ v : (pullback (fY i) g : Scheme.{u}),
      (pullbackRestrict f (fY i) (p i) (hY i) g).base v = w := by
  obtain ⟨i, y, hy⟩ := hsurj ((pullback.fst f g).base w)
  refine ⟨i, ?_⟩
  have hrange : Set.range (pullbackRestrict f (fY i) (p i) (hY i) g).base =
      (pullback.fst f g).base ⁻¹' Set.range (p i).base := by
    rw [show (pullbackRestrict f (fY i) (p i) (hY i) g) =
      pullback.map (fY i) g f g (p i) (𝟙 _) (𝟙 _) (by simpa using (hY i).symm) (by simp) from rfl,
      Scheme.Pullback.range_map (f := fY i) (g := g) f g (p i) (𝟙 T) (𝟙 S)
        (by simpa using (hY i).symm) (by simp)]
    simp
  exact (Set.ext_iff.mp hrange w).mpr ⟨y, hy⟩

/-- The fibre over `t` of the base change of a jointly surjective family of morphisms of schemes
over `S` is again jointly surjective: the fibre morphisms are the base changes of the base
changes along the morphism from the spectrum of the residue field at `t`. -/
theorem exists_fiberRestrict_pullbackRestrict_eq {Idx : Type v} {X S T : Scheme.{u}}
    {Y : Idx → Scheme.{u}} (f : X ⟶ S) (fY : ∀ i, Y i ⟶ S) (p : ∀ i, Y i ⟶ X)
    (hY : ∀ i, p i ≫ f = fY i) (hsurj : ∀ x : X, ∃ i, ∃ y : Y i, (p i).base y = x) (g : T ⟶ S)
    (t : T) (x : (pullback.snd f g).fiber t) :
    ∃ i, ∃ v : (pullback.snd (fY i) g).fiber t,
      (fiberRestrict (pullback.snd f g) (pullback.snd (fY i) g)
        (pullbackRestrict f (fY i) (p i) (hY i) g)
        (pullbackRestrict_snd f (fY i) (p i) (hY i) g) t).base v = x :=
  exists_pullbackRestrict_eq (pullback.snd f g) (fun i => pullback.snd (fY i) g)
    (fun i => pullbackRestrict f (fY i) (p i) (hY i) g)
    (fun i => pullbackRestrict_snd f (fY i) (p i) (hY i) g)
    (exists_pullbackRestrict_eq f fY p hY hsurj g) (T.fromSpecResidueField t) x

/-- The flat pullbacks of fibrewise cycles along the fibres of a jointly surjective family of
flat morphisms, base changed to a scheme over the base, are jointly injective. This is the input
the source of Lemma 0H53 draws from joint surjectivity. -/
theorem eq_of_forall_baseChangedFiberCycleFlatPullback {Idx : Type v} {X S T : Scheme.{u}}
    {Y : Idx → Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (p : ∀ i, Y i ⟶ X)
    [∀ i, LocallyOfFiniteType (p i)] [∀ i, Flat (p i)] (fY : ∀ i, Y i ⟶ S)
    [∀ i, LocallyOfFiniteType (fY i)] (hY : ∀ i, p i ≫ f = fY i) (e : ℕ)
    (he : ∀ i, AlgebraicGeometry.RelativeDimension (p i) e)
    (hsurj : ∀ x : X, ∃ i, ∃ y : Y i, (p i).base y = x) (g : T ⟶ S) (t : T) (r : ℕ)
    (c d : FiberCycleGroup (pullback.snd f g) t r)
    (hcd : ∀ i, baseChangedFiberCycleFlatPullback f (fY i) (p i) (hY i) e (he i) g t r c =
      baseChangedFiberCycleFlatPullback f (fY i) (p i) (hY i) e (he i) g t r d) :
    c = d :=
  sub_eq_zero.mp <|
    eq_zero_of_forall_flatPullback_eq_zero (fieldChowSituation (T.residueField t))
      ((pullback.snd f g).fiberToSpecResidueField t)
      (fun i => (pullback.snd (fY i) g).fiberToSpecResidueField t)
      (fun i => fiberRestrict (pullback.snd f g) (pullback.snd (fY i) g)
        (pullbackRestrict f (fY i) (p i) (hY i) g)
        (pullbackRestrict_snd f (fY i) (p i) (hY i) g) t)
      (fun i => fiberRestrict_fiberToSpecResidueField (pullback.snd f g)
        (pullback.snd (fY i) g) (pullbackRestrict f (fY i) (p i) (hY i) g)
        (pullbackRestrict_snd f (fY i) (p i) (hY i) g) t)
      e
      (fun i => relativeDimension_fiberRestrict (pullback.snd f g) (pullback.snd (fY i) g)
        (pullbackRestrict f (fY i) (p i) (hY i) g)
        (pullbackRestrict_snd f (fY i) (p i) (hY i) g) t
        (relativeDimension_pullbackRestrict f (fY i) (p i) (hY i) g (he i)))
      (exists_fiberRestrict_pullbackRestrict_eq f fY p hY hsurj g t) (r : ℤ) (c - d)
      fun i => by rw [map_sub, sub_eq_zero]; exact hcd i

/-! ### Tag 0H51, the flat pullback clause -/

/-- The valuative identity for `j^*α` at `g : Spec R ⟶ S` holds if and only if the flat pullback of
the valuative identity for `α` does. -/
private theorem specializationCycle_flatPullbackFamily_iff {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [LocallyOfFiniteType j] [Flat j] (hj : j ≫ f = fU) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e) {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (g : Spec (.of R) ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) :
    specializationCycle (pullback.snd fU g) (r + e)
        (baseChangeFamily fU g (r + e) (flatPullbackFamily f fU j hj e he r α)
          (genericPoint (Spec (.of R)))) =
      baseChangeFamily fU g (r + e) (flatPullbackFamily f fU j hj e he r α)
        (IsLocalRing.closedPoint R) ↔
    baseChangedFiberCycleFlatPullback f fU j hj e he g (IsLocalRing.closedPoint R) r
        (specializationCycle (pullback.snd f g) r
          (baseChangeFamily f g r α (genericPoint (Spec (.of R))))) =
      baseChangedFiberCycleFlatPullback f fU j hj e he g (IsLocalRing.closedPoint R) r
        (baseChangeFamily f g r α (IsLocalRing.closedPoint R)) := by
  rw [baseChangeFamily_flatPullbackFamily_apply f fU j hj e he g r α (genericPoint (Spec (.of R))),
    baseChangeFamily_flatPullbackFamily_apply f fU j hj e he g r α (IsLocalRing.closedPoint R),
    specializationCycle_baseChangedFiberCycleFlatPullback f fU j hj e he g r]

/-- **Stacks Project, Lemma 0H51, the flat pullback clause.** Let `f : X ⟶ S` be locally of
finite type with `S` locally Noetherian and let `j : U ⟶ X` be a flat morphism, locally of finite
type and of relative dimension `e`, with `j ≫ f = f_U`. Then the flat pullback `j^*α` of a
relative `r`-cycle `α` on `X/S` is a relative `(r + e)`-cycle on `U/S`.

The valuative condition for `j^*α` at a morphism `g : Spec R ⟶ S` from the spectrum of a discrete
valuation ring is the valuative condition for `α` at `g`, pulled back along the base change of
`j`: base change of the base scheme commutes with flat pullback by Lemma 0H4P part (3),
`Stacks.Chow.baseChangeFamily_flatPullbackFamily`, and specialization commutes with flat pullback
by Lemma 0H4L, `Stacks.Chow.specializationCycle_baseChangedFiberCycleFlatPullback`.

No surjectivity is involved; this is the single-morphism statement whose family form is the
forward direction of `Stacks.Chow.isRelativeCycle_iff_forall_flatPullbackFamily` below. -/
@[stacks 0H51 "flat pullback along a flat morphism of relative dimension e"]
theorem isRelativeCycle_flatPullbackFamily {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (fU : U ⟶ S) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j] (hj : j ≫ f = fU) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e) (r : ℕ) {α : FamilyOfCycles f r}
    (hα : IsRelativeCycle f r α) :
    IsRelativeCycle fU (r + e) (flatPullbackFamily f fU j hj e he r α) := by
  intro R _ _ _ g
  exact (specializationCycle_flatPullbackFamily_iff f fU j hj e he g r α).2 (by rw [hα R g])

/-! ### Tag 0H53 -/

/-- **Stacks Project, Lemma 0H53.** Let `f : X ⟶ S` be a morphism of schemes with `S` locally
Noetherian and `f` locally of finite type, let `r, e ≥ 0` and let `α` be a family of `r`-cycles
on the fibres of `X/S`. Let `{f_i : X_i ⟶ X}` be a jointly surjective family of flat morphisms,
locally of finite type and of relative dimension `e`. Then `α` is a relative `r`-cycle if and
only if every flat pullback `f_i^*α` is a relative `(r+e)`-cycle.

The proof is the one in the source. Both directions are read off after base change to the
spectrum of a discrete valuation ring: there the valuative identity for `f_i^*α` is the identity
`sp(f_{i,η}^*α_η) = f_{i,0}^*α_0`, and base change of a flat pullback
(`Stacks.Chow.baseChangeFamily_flatPullbackFamily_apply`, Lemma 0H4P part (3)) with the
commutation of specialization and flat pullback
(`Stacks.Chow.specializationCycle_baseChangedFiberCycleFlatPullback`, Lemma 0H4L) turns it into
`f_{i,0}^*(sp(α_η)) = f_{i,0}^*α_0`. That is implied by the valuative identity for `α`, which
gives the forward direction, and implies it because the `f_{i,0}^*` are jointly injective by
`Stacks.Chow.eq_of_forall_baseChangedFiberCycleFlatPullback`, which gives the converse. -/
@[stacks 0H53 "both directions, for a jointly surjective family of flat morphisms of relative \
dimension e"]
theorem isRelativeCycle_iff_forall_flatPullbackFamily {Idx : Type v} {X S : Scheme.{u}}
    {Y : Idx → Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S]
    (p : ∀ i, Y i ⟶ X) [∀ i, LocallyOfFiniteType (p i)] [∀ i, Flat (p i)]
    (fY : ∀ i, Y i ⟶ S) [∀ i, LocallyOfFiniteType (fY i)] (hY : ∀ i, p i ≫ f = fY i) (e : ℕ)
    (he : ∀ i, AlgebraicGeometry.RelativeDimension (p i) e)
    (hsurj : ∀ x : X, ∃ i, ∃ y : Y i, (p i).base y = x) (r : ℕ) (α : FamilyOfCycles f r) :
    IsRelativeCycle f r α ↔
      ∀ i, IsRelativeCycle (fY i) (r + e)
        (flatPullbackFamily f (fY i) (p i) (hY i) e (he i) r α) := by
  refine ⟨fun hα i => isRelativeCycle_flatPullbackFamily f (fY i) (p i) (hY i) e (he i) r hα,
    fun hall R _ _ _ g => eq_of_forall_baseChangedFiberCycleFlatPullback f p fY hY e he hsurj g
      (IsLocalRing.closedPoint R) r _ _ fun i => ?_⟩
  exact (specializationCycle_flatPullbackFamily_iff f (fY i) (p i) (hY i) e (he i) g r α).1
    (hall i R g)

/-- **Stacks Project, Lemma 0H53, membership form.** A family of `r`-cycles on the fibres of
`X/S` lies in `z(X/S, r)` if and only if each of its flat pullbacks along a jointly surjective
family of flat morphisms, locally of finite type and of relative dimension `e`, lies in
`z(X_i/S, r + e)`. -/
theorem mem_relativeCycles_iff_forall_flatPullbackFamily {Idx : Type v} {X S : Scheme.{u}}
    {Y : Idx → Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S]
    (p : ∀ i, Y i ⟶ X) [∀ i, LocallyOfFiniteType (p i)] [∀ i, Flat (p i)]
    (fY : ∀ i, Y i ⟶ S) [∀ i, LocallyOfFiniteType (fY i)] (hY : ∀ i, p i ≫ f = fY i) (e : ℕ)
    (he : ∀ i, AlgebraicGeometry.RelativeDimension (p i) e)
    (hsurj : ∀ x : X, ∃ i, ∃ y : Y i, (p i).base y = x) (r : ℕ) (α : FamilyOfCycles f r) :
    α ∈ relativeCycles f r ↔
      ∀ i, flatPullbackFamily f (fY i) (p i) (hY i) e (he i) r α ∈
        relativeCycles (fY i) (r + e) :=
  isRelativeCycle_iff_forall_flatPullbackFamily f p fY hY e he hsurj r α

end Stacks.Chow

end
