module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.AssociatedToModule
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatPullbackFamily
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMapBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Effective cycles and effective families of cycles on fibres

A cycle on a scheme is *effective* when it is a nonnegative combination of integral closed
subschemes; since a cycle is recorded by its coefficient function, this says exactly that all
of its coefficients are nonnegative. A family of `r`-cycles on the fibres of `f : X ⟶ S` is
*effective* when the cycle it carries on every fibre is effective, and the effective families
form an additive submonoid of the group of all families.

Effectivity is a condition on each coefficient separately, so it is inherited by restriction
to open subschemes `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`, and conversely it can be tested on any
family of such open subschemes whose members cover `X`: that is, effectivity may be checked
Zariski locally on `X` and on `S`.

## Main definitions

* `Stacks.Chow.IsEffectiveCycle` — a cycle has nonnegative coefficients.
* `Stacks.Chow.IsEffectiveFamily` — a family of cycles on fibres is fibrewise effective.
* `Stacks.Chow.effectiveFamilies` — the additive submonoid of effective families.

## Main results

* `Stacks.Chow.isEffectiveFamily_restrictedFamily` — restriction preserves effectivity.
* `Stacks.Chow.isEffectiveFamily_iff_forall_restrictedFamily` — effectivity may be checked on
  the members of any family of open restrictions covering `X`.
* `Stacks.Chow.isEffectiveFamily_baseChangeFamily`,
  `Stacks.Chow.isEffectiveFamily_flatPullbackFamily`,
  `Stacks.Chow.isEffectiveFamily_properPushforwardFamily` — base change, flat pullback and proper
  pushforward preserve effectivity. Together with restriction these are the four assertions of
  Lemma 0H5S.

## Implementation notes

The coefficients of a cycle form an element of `Function.locallyFinsupp`, whose order is
pointwise, so effectivity of a cycle `c` is both `0 ≤ c` and `∀ x, 0 ≤ c x`; the pointwise form
is taken as the definition and `Stacks.Chow.isEffectiveCycle_iff_nonneg` identifies the two.

The hypotheses that `S` is locally Noetherian and that `f` is locally of finite type are needed
to speak of relative cycles, not to speak of effectivity, so the definitions here do not carry
the locally Noetherian hypothesis; the lemmas carry it.

The source defines effectivity for a relative `r`-cycle (Definition 0H5R); what is defined here
is the condition on an arbitrary family of `r`-cycles on fibres, which is the generality the
lemmas of Tags 0H5S, 0H5T, 0H5U and 0H5V are proved in, none of them using the valuative
condition. The source's definition, and the monoid `z^eff(X/S, r)` it names, are
`Stacks.Chow.IsEffectiveRelativeCycle` and `Stacks.Chow.effectiveRelativeCycles` in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EffectiveRelative`.

## References

* [Stacks Project, Tag 0H47](https://stacks.math.columbia.edu/tag/0H47)
* [Stacks Project, Tag 0H5R](https://stacks.math.columbia.edu/tag/0H5R)
* [Stacks Project, Tag 0H5S](https://stacks.math.columbia.edu/tag/0H5S)
* [Stacks Project, Tag 0H5T](https://stacks.math.columbia.edu/tag/0H5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Chow

/-! ### Effective cycles -/

/-- **Stacks Project, Tag 0H47.** A cycle is *effective* when it can be written as a sum
`∑ n_Z [Z]` of integral closed subschemes with all `n_Z ≥ 0`, that is, when every coefficient
of the cycle is nonnegative. -/
@[stacks 0H47, ega "IV 21.6.1", ega "IV 21.6.2" "(X)"]
def IsEffectiveCycle {X : Scheme.{u}} (c : AlgebraicCycle X ℤ) : Prop :=
  ∀ x : X, 0 ≤ c x

/-- Effectivity of a cycle is nonnegativity in the pointwise order on coefficients. -/
theorem isEffectiveCycle_iff_nonneg {X : Scheme.{u}} (c : AlgebraicCycle X ℤ) :
    IsEffectiveCycle c ↔ 0 ≤ c :=
  Iff.rfl

/-- The zero cycle is effective. -/
theorem isEffectiveCycle_zero {X : Scheme.{u}} :
    IsEffectiveCycle (0 : AlgebraicCycle X ℤ) := fun _ => le_refl 0

/-- A sum of effective cycles is effective. -/
theorem IsEffectiveCycle.add {X : Scheme.{u}} {c d : AlgebraicCycle X ℤ}
    (hc : IsEffectiveCycle c) (hd : IsEffectiveCycle d) : IsEffectiveCycle (c + d) :=
  fun x => by simpa using add_nonneg (hc x) (hd x)

/-! ### Effective families of cycles on fibres -/

/-- A family of `r`-cycles on the fibres of `f : X ⟶ S` is *effective* when the cycle it carries
on the scheme-theoretic fibre over every point of `S` is an effective cycle.

Effectivity of a *relative* `r`-cycle, Stacks Project Definition 0H5R, is this condition on the
underlying family: see `Stacks.Chow.IsEffectiveRelativeCycle`. -/
def IsEffectiveFamily {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) : Prop :=
  ∀ s : S, IsEffectiveCycle (α s : AlgebraicCycle (f.fiber s) ℤ)

/-- A family of cycles on fibres is effective exactly when every coefficient of every one of
its fibre cycles is nonnegative. -/
theorem isEffectiveFamily_iff {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) :
    IsEffectiveFamily f r α ↔
      ∀ (s : S) (x : f.fiber s), 0 ≤ (α s : AlgebraicCycle (f.fiber s) ℤ) x :=
  Iff.rfl

/-- The effective families of `r`-cycles on the fibres of `X/S` form an additive submonoid of the
group of all such families.

The monoid `z^eff(X/S, r)` of Stacks Project Definition 0H5R is the part of this submonoid lying
in the group `z(X/S, r)` of relative `r`-cycles: see `Stacks.Chow.effectiveRelativeCycles`. -/
def effectiveFamilies {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) :
    AddSubmonoid (FamilyOfCycles f r) where
  carrier := {α | IsEffectiveFamily f r α}
  zero_mem' := fun _ => isEffectiveCycle_zero
  add_mem' := fun hα hβ s => (hα s).add (hβ s)

/-- Membership in the submonoid of effective families is fibrewise effectivity. -/
@[simp]
theorem mem_effectiveFamilies {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) :
    α ∈ effectiveFamilies f r ↔ IsEffectiveFamily f r α :=
  Iff.rfl

/-! ### Restriction to open subschemes -/

/-- **Stacks Project, Tag 0H5S.** The restriction of an effective family of `r`-cycles on the
fibres of `X/S` to open subschemes `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V` is effective. -/
@[stacks 0H5S "restriction"]
theorem isEffectiveFamily_restrictedFamily {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (fU : U ⟶ V) (j : U ⟶ X)
    [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i) (r : ℕ)
    (α : FamilyOfCycles f r) (hα : IsEffectiveFamily f r α) :
    letI : LocallyOfFiniteType fU := by
      let : LocallyOfFiniteType (fU ≫ i) := h ▸ inferInstance
      exact locallyOfFiniteType_of_comp fU i
    IsEffectiveFamily fU r (restrictedFamily f fU j i h r α).1 := by
  let : LocallyOfFiniteType fU := by
    let : LocallyOfFiniteType (fU ≫ i) := h ▸ inferInstance
    exact locallyOfFiniteType_of_comp fU i
  intro t x
  rw [(restrictedFamily f fU j i h r α).2 t x]
  exact hα (i t) _

/-! ### Effectivity is Zariski local -/

/-- A point of a fibre of `f` lies over the image of its open-subscheme preimage: if a point of
the fibre over `s` is carried to `j u` in `X`, then `s` is the image of `fU u`. -/
private theorem eq_image_of_fiberι_eq {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) (j : U ⟶ X) (i : V ⟶ S) (h : j ≫ f = fU ≫ i)
    (u : U) {s : S} (x : f.fiber s) (hx : f.fiberι s x = j u) : s = i (fU u) := by
  have hfz : f (f.fiberι s x) = s := by
    apply Set.mem_singleton_iff.mp
    change f.fiberι s x ∈ f ⁻¹' {s}
    rw [← f.range_fiberι]
    exact ⟨x, rfl⟩
  have hju : f (j u) = i (fU u) := by
    have hh := congrArg (fun q : U ⟶ S => q u) h
    simpa using hh
  rw [← hfz, hx, hju]

/-- The canonical map of fibres carries the tautological point of the fibre of `fU` through
`u : U` to the point of the fibre of `f` sitting over `j u`. -/
private theorem restrictedFiberMap_asFiber_of_fiberι_eq {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i] (h : j ≫ f = fU ≫ i) (u : U)
    (x : f.fiber (i (fU u))) (hx : f.fiberι (i (fU u)) x = j u) :
    restrictedFiberMap f fU j i h (fU u) (fU.asFiber u) = x := by
  apply (f.fiberι (i (fU u))).isEmbedding.injective
  calc
    f.fiberι (i (fU u)) (restrictedFiberMap f fU j i h (fU u) (fU.asFiber u))
        = j (fU.fiberι (fU u) (fU.asFiber u)) :=
      congrArg (fun q : fU.fiber (fU u) ⟶ X => q (fU.asFiber u))
        (restrictedFiberMap_fiberι f fU j i h (fU u))
    _ = j u := by rw [Scheme.Hom.fiberι_asFiber]
    _ = f.fiberι (i (fU u)) x := hx.symm

/-- **Stacks Project, Tag 0H5T.** Effectivity of a family of `r`-cycles on the fibres of `X/S`
may be checked Zariski locally on `X` and on `S`: given open subschemes `U a ⊆ X` and
`V a ⊆ S` with `f(U a) ⊆ V a` and with the `U a` covering `X`, the family is effective exactly
when each of its restrictions is. -/
@[stacks 0H5T]
theorem isEffectiveFamily_iff_forall_restrictedFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] {ι : Type v} {U V : ι → Scheme.{u}}
    (fU : ∀ a : ι, U a ⟶ V a) (j : ∀ a : ι, U a ⟶ X) [∀ a : ι, IsOpenImmersion (j a)]
    (i : ∀ a : ι, V a ⟶ S) [∀ a : ι, IsOpenImmersion (i a)]
    (h : ∀ a : ι, j a ≫ f = fU a ≫ i a) (hcover : ∀ x : X, ∃ a : ι, x ∈ Set.range (j a))
    (r : ℕ) (α : FamilyOfCycles f r) :
    letI : ∀ a : ι, LocallyOfFiniteType (fU a) := fun a => by
      let : LocallyOfFiniteType (fU a ≫ i a) := h a ▸ inferInstance
      exact locallyOfFiniteType_of_comp (fU a) (i a)
    IsEffectiveFamily f r α ↔
      ∀ a : ι, IsEffectiveFamily (fU a) r
        (restrictedFamily f (fU a) (j a) (i a) (h a) r α).1 := by
  let : ∀ a : ι, LocallyOfFiniteType (fU a) := fun a => by
    let : LocallyOfFiniteType (fU a ≫ i a) := h a ▸ inferInstance
    exact locallyOfFiniteType_of_comp (fU a) (i a)
  refine ⟨fun hα a => isEffectiveFamily_restrictedFamily f (fU a) (j a) (i a) (h a) r α hα,
    fun hres s x => ?_⟩
  obtain ⟨a, u, hu⟩ := hcover (f.fiberι s x)
  have hs : s = i a (fU a u) :=
    eq_image_of_fiberι_eq f (fU a) (j a) (i a) (h a) u x hu.symm
  subst hs
  have hx := restrictedFiberMap_asFiber_of_fiberι_eq f (fU a) (j a) (i a) (h a) u x hu.symm
  have hcoeff :=
    (restrictedFamily f (fU a) (j a) (i a) (h a) r α).2 (fU a u) ((fU a).asFiber u)
  rw [hx] at hcoeff
  have hval := hres a (fU a u) ((fU a).asFiber u)
  rwa [hcoeff] at hval

end Stacks.Chow

namespace Stacks.Chow

open TopologicalSpace

/-!
### Flat pullback detects effectivity

Effectivity is also detected by a jointly surjective family of flat pullbacks: flat pullback
multiplies the coefficient at a point by the multiplicity of a component of an inverse image, a
nonnegative number which is strictly positive at the generic points that carry it, so pulling
back preserves effectivity and, the pullbacks being jointly surjective, loses no information.
What makes that multiplicity *carry* the coefficient is the delta-dimension computation of
[Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8): along a flat morphism of
relative dimension `e` the generic points of the inverse image of the reduced closure of a point
of relative dimension `k` have relative dimension `k + e`, which is exactly the dimension at
which flat pullback reads multiplicities.

## Main results

* `Stacks.Chow.componentMultiplicity_nonneg`, `Stacks.Chow.flatPullbackWeight_nonneg` — the
  multiplicity of a component of a closed subscheme, and the weight of a flat pullback, are
  nonnegative.
* `Stacks.Chow.flatPullbackWeight_pos_of_genericPoint` — that weight is strictly positive at a
  generic point of the inverse image of the reduced closure of the image point.
* `Stacks.Chow.relativeDimension_comap_genericPoint_eq_add` — along a flat morphism of relative
  dimension `e`, a generic point of the inverse image of the reduced closure of `y` has
  relative dimension `e` more than `y`.
* `Stacks.Chow.flatPullback_nonneg`, `Stacks.Chow.nonneg_of_forall_flatPullback_nonneg` — flat
  pullback preserves effectivity, and reflects it along a jointly surjective family.
* `Stacks.Chow.isEffectiveFamily_iff_forall_flatPullback` — effectivity of a family of cycles on
  fibres may be tested on its flat pullbacks along a jointly surjective family of flat morphisms
  locally of finite type and of relative dimension `e`.

## Implementation notes

The fibrewise flat pullback of a family of cycles *is* constructed in this repository, as
`Stacks.Chow.flatPullbackFamily`, which reads coefficients through the induced morphism of
fibres `Stacks.Chow.fiberRestrict`. The statements below nevertheless specify the coefficients
of the pullback family by the coefficient rule of flat pullback rather than by applying that
construction, read through `AlgebraicGeometry.Scheme.Hom.fiberMap`, so that they apply to any
family obeying the rule; this is exactly how `Stacks.Chow.IsBaseChangedFlatPullback` specifies
the restriction of a family.

## References

* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0H5V](https://stacks.math.columbia.edu/tag/0H5V)
-/

/-! #### Nonnegativity of multiplicities -/

/-- The multiplicity of an irreducible component of a closed subscheme is nonnegative, being the
length of a module. -/
theorem componentMultiplicity_nonneg {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (ξ : genericPoints Z) : 0 ≤ componentMultiplicity i ξ := by
  unfold componentMultiplicity
  positivity

/-- The coefficients of the cycle of a closed subscheme are nonnegative. -/
theorem closedSubschemeCycleCoeff_nonneg (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ) (x : X) :
    0 ≤ closedSubschemeCycleCoeff C f i k x := by
  unfold closedSubschemeCycleCoeff
  split_ifs with h
  · exact componentMultiplicity_nonneg i (Classical.choose h)
  · exact le_rfl

/-- The weight with which a point enters a flat pullback is nonnegative. -/
theorem flatPullbackWeight_nonneg (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (f : X' ⟶ X) (j : ℤ) (x' : X') :
    0 ≤ flatPullbackWeight C sX' f j x' :=
  closedSubschemeCycleCoeff_nonneg C sX' _ j x'

/-- The weight with which a point enters a flat pullback is nonzero at a generic point of the
inverse image of the reduced closure of its image, provided the dimension matches: the stalk
there is a nonzero module of finite length over the ambient stalk. -/
theorem flatPullbackWeight_ne_zero_of_genericPoint (C : ChowSituation.{u}) {T Y : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (h : T ⟶ Y) (j : ℤ) (y : Y) (x : T)
    (ξ : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap h).subscheme))
    (hξ : (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap h).subschemeι) ξ.1 = x)
    (hmap : h.base x = y)
    (hdim : relativeDimension C.dimensionFunction sT x = j) :
    flatPullbackWeight C sT h j x ≠ 0 := by
  classical
  cases hmap
  unfold flatPullbackWeight closedSubschemeCycleCoeff
  let H : ∃ η : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h.base x} : Set Y))).comap h).subscheme),
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({h.base x} : Set Y))).comap h).subschemeι) η.1 = x ∧
        relativeDimension C.dimensionFunction sT x = j :=
    ⟨ξ, hξ, hdim⟩
  rw [dite_eq_left H]
  have hchoose : Classical.choose H = ξ := by
    apply Subtype.ext
    let i := ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h.base x} : Set Y))).comap h).subschemeι
    have : IsClosedImmersion i := by infer_instance
    apply i.isClosedEmbedding.injective
    exact (Classical.choose_spec H).1.trans hξ.symm
  rw [hchoose]
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : LocallyOfFiniteType
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({h.base x} : Set Y))).comap h).subschemeι) := by infer_instance
  have : IsLocallyNoetherian
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({h.base x} : Set Y))).comap h).subscheme) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({h.base x} : Set Y))).comap h).subschemeι)
  exact componentMultiplicity_ne_zero (X := T)
    (Z := ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h.base x} : Set Y))).comap h).subscheme)
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h.base x} : Set Y))).comap h).subschemeι) ξ

/-- The weight with which a point enters a flat pullback is strictly positive at a generic point
of the inverse image of the reduced closure of its image, provided the dimension matches. -/
theorem flatPullbackWeight_pos_of_genericPoint (C : ChowSituation.{u}) {T Y : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (h : T ⟶ Y) (j : ℤ) (y : Y) (x : T)
    (ξ : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap h).subscheme))
    (hξ : (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap h).subschemeι) ξ.1 = x)
    (hmap : h.base x = y)
    (hdim : relativeDimension C.dimensionFunction sT x = j) :
    0 < flatPullbackWeight C sT h j x :=
  lt_of_le_of_ne (flatPullbackWeight_nonneg C sT h j x)
    (Ne.symm (flatPullbackWeight_ne_zero_of_genericPoint C sT h j y x ξ hξ hmap hdim))

/-! #### Relative dimension of the inverse image of the closure of a point -/

/-- **Stacks 02R8.** Along a flat morphism of relative dimension `e`, a generic point of the
scheme-theoretic inverse image of the reduced closure of `y` has relative dimension `e` more
than `y`.

The inverse image is the fibre product with the integral closed subscheme `closure {y}`, whose
components all have delta-dimension `dim_δ(closure {y}) + e`, and neither the closed immersion
of the inverse image into the source nor the comparison with the fibre product changes a
relative dimension. -/
private theorem relativeDimension_eq_add_of_pullbackIso (C : ChowSituation.{u})
    {T Y W Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] (h : T ⟶ Y) [LocallyOfFiniteType h] [Flat h]
    (hbase : h ≫ sY = sT) (e : ℕ) (hrel : AlgebraicGeometry.RelativeDimension h e)
    (i : W ⟶ Y) [IsClosedImmersion i] [IrreducibleSpace W] (y : Y)
    (hy : i.base (genericPoint W) = y) (ι : Z ⟶ T) [IsClosedImmersion ι]
    (φ : Z ≅ pullback h i) (hφ : φ.hom ≫ pullback.fst h i = ι) (ξ : genericPoints Z) :
    relativeDimension C.dimensionFunction sT (ι.base ξ.1) =
      relativeDimension C.dimensionFunction sY y + (e : ℤ) := by
  -- The two structure morphisms of the inverse image agree.
  have hcomp : φ.hom ≫ pullback.snd h i ≫ i ≫ sY = ι ≫ sT := by
    have hcond : pullback.snd h i ≫ i = pullback.fst h i ≫ h := pullback.condition.symm
    calc φ.hom ≫ pullback.snd h i ≫ i ≫ sY
        = φ.hom ≫ (pullback.snd h i ≫ i) ≫ sY := by simp
      _ = φ.hom ≫ (pullback.fst h i ≫ h) ≫ sY := by rw [hcond]
      _ = (φ.hom ≫ pullback.fst h i) ≫ h ≫ sY := by simp
      _ = ι ≫ sT := by rw [hφ, hbase]
  have hmain := deltaDimension_irreducibleComponent_pullback_snd_comp C sY h e hrel i
    ⟨closure ({φ.hom.base ξ.1} : Set (pullback h i : Scheme.{u})), (genericPointsIso φ ξ).2⟩
  rw [deltaDimension_eq_of_isGenericPoint C (pullback.snd h i ≫ i ≫ sY) _ (φ.hom.base ξ.1)
      isGenericPoint_closure,
    ← relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction φ.hom
      (pullback.snd h i ≫ i ≫ sY) ξ.1 (ConcreteCategory.bijective_of_isIso _), hcomp,
    relativeDimension_comp_closedImmersion C.dimensionFunction ι sT ξ.1,
    deltaDimension_eq_of_isGenericPoint C (i ≫ sY) _ (genericPoint W) (genericPoint_spec W),
    relativeDimension_comp_closedImmersion C.dimensionFunction i sY (genericPoint W),
    hy] at hmain
  exact hmain

/-- **Stacks 02R8.** Along a flat morphism of relative dimension `e`, a generic point of the
scheme-theoretic inverse image of the reduced closure of `y` has relative dimension `e` more
than `y`. -/
theorem relativeDimension_comap_genericPoint_eq_add (C : ChowSituation.{u}) {T Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sT : T ⟶ C.S) [LocallyOfFiniteType sT]
    (h : T ⟶ Y) [LocallyOfFiniteType h] [Flat h] (hbase : h ≫ sY = sT) (e : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension h e) (y : Y)
    (ξ : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap h).subscheme)) :
    relativeDimension C.dimensionFunction sT
        ((((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({y} : Set Y))).comap h).subschemeι).base ξ.1) =
      relativeDimension C.dimensionFunction sY y + (e : ℤ) := by
  have hirr : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).subscheme := vanishingSubscheme_irreducibleSpace y
  have hy : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).subschemeι.base
        (genericPoint (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({y} : Set Y))).subscheme) = y := by
    have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).subschemeι.base = closure ({y} : Set Y) := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      simp
    have himg := (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).subschemeι.isClosedEmbedding.closure_image_eq
        ({genericPoint (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({y} : Set Y))).subscheme} : Set _)
    rw [genericPoint_spec _] at himg
    have hgen : closure ({(Scheme.IdealSheafData.vanishingIdeal
                              (Closeds.closure ({y} : Set Y))).subschemeι.base
                            (genericPoint (Scheme.IdealSheafData.vanishingIdeal
                              (Closeds.closure ({y} : Set Y))).subscheme)} : Set Y) =
        closure ({y} : Set Y) := by
      simpa [Set.image_univ, hrange] using himg
    exact IsGenericPoint.eq hgen isGenericPoint_closure
  exact relativeDimension_eq_add_of_pullbackIso C sY sT h hbase e hrel _ y hy _
    ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).comapIso h)
    ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comapIso_hom_fst h) ξ

/-! #### Flat pullback and effectivity -/

/-- Flat pullback carries effective cycles to effective cycles: a pulled-back coefficient is the
original coefficient times a nonnegative weight. -/
theorem flatPullback_nonneg (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (c : CycleGroup C sX k)
    (hc : 0 ≤ (c : AlgebraicCycle X ℤ)) :
    0 ≤ ((flatPullback C sX' sX f hbase r hf k c : CycleGroup C sX' (k + (r : ℤ))) :
      AlgebraicCycle X' ℤ) := by
  intro x'
  rw [flatPullback_apply C sX' sX f hbase r hf k c x']
  exact mul_nonneg (hc _) (flatPullbackWeight_nonneg C sX' f (k + (r : ℤ)) x')

/-- A cycle all of whose flat pullbacks along a jointly surjective family of flat morphisms of
relative dimension `e` are effective is itself effective.

At a point `y` with a negative coefficient, pick a member of the family with a point above `y`;
inside the inverse image of the reduced closure of `y` that point generizes to a generic point,
which lies over `y` and has relative dimension `e` more, so the pullback reads the coefficient
at `y` there with a strictly positive weight. -/
theorem nonneg_of_forall_flatPullback_nonneg (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {Idx : Type*} {T : Idx → Scheme.{u}}
    (sT : ∀ i, T i ⟶ C.S) [∀ i, LocallyOfFiniteType (sT i)] (h : ∀ i, T i ⟶ Y)
    [∀ i, LocallyOfFiniteType (h i)] [∀ i, Flat (h i)] (hbase : ∀ i, h i ≫ sY = sT i) (e : ℕ)
    (hrel : ∀ i, AlgebraicGeometry.RelativeDimension (h i) e)
    (hsurj : ∀ y : Y, ∃ i, ∃ x : T i, (h i).base x = y) (k : ℤ) (c : CycleGroup C sY k)
    (hpb : ∀ i, 0 ≤ ((flatPullback C (sT i) sY (h i) (hbase i) e (hrel i) k c :
      CycleGroup C (sT i) (k + (e : ℤ))) : AlgebraicCycle (T i) ℤ)) :
    0 ≤ (c : AlgebraicCycle Y ℤ) := by
  intro y
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨i, x, hxy⟩ := hsurj y
  obtain ⟨ξ, -, hιy⟩ := exists_comap_genericPoint_over (h i) y x hxy
  have hk : relativeDimension C.dimensionFunction sY y = k :=
    (mem_cyclesOfDimension_iff_forall_point C sY k (c : AlgebraicCycle Y ℤ)).1 c.2 y
      (ne_of_lt hneg)
  have hdim : relativeDimension C.dimensionFunction (sT i)
      ((((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap (h i)).subschemeι).base ξ.1) = k + (e : ℤ) := by
    rw [relativeDimension_comap_genericPoint_eq_add C sY (sT i) (h i) (hbase i) e (hrel i) y ξ,
      hk]
  have hwpos := flatPullbackWeight_pos_of_genericPoint C (sT i) (h i) (k + (e : ℤ)) y
    ((((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap (h i)).subschemeι).base ξ.1) ξ rfl hιy hdim
  have hcoeff := hpb i ((((Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({y} : Set Y))).comap (h i)).subschemeι).base ξ.1)
  rw [flatPullback_apply C (sT i) sY (h i) (hbase i) e (hrel i) k c _, hιy] at hcoeff
  exact (mul_neg_of_neg_of_pos hneg hwpos).not_ge hcoeff

/-! #### Effectivity of a family is detected by flat pullback -/

/-- **Stacks Project, Tag 0H5V, fibrewise.** Let `α` be a family of `r`-cycles on the fibres of
`X/S` and let `{X'_i/S}` be schemes locally of finite type over `S` whose fibres map to those of
`X/S` by flat morphisms of relative dimension `e` which are jointly surjective on every fibre.
If `β i` is the fibrewise flat pullback of `α`, then `α` is effective if and only if every `β i`
is.

Both directions are coefficientwise: the weight of a flat pullback is nonnegative, and at a
generic point of the inverse image of the reduced closure of a point of the fibre it is strictly
positive. -/
theorem isEffectiveFamily_iff_forall {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {r e : ℕ} (α : FamilyOfCycles f r) {Idx : Type*} {X' : Idx → Scheme.{u}}
    (f' : ∀ i, X' i ⟶ S) [∀ i, LocallyOfFiniteType (f' i)]
    (p : ∀ (i : Idx) (s : S), (f' i).fiber s ⟶ f.fiber s)
    [∀ i s, LocallyOfFiniteType (p i s)] [∀ i s, Flat (p i s)]
    (hp : ∀ (i : Idx) (s : S),
      p i s ≫ f.fiberToSpecResidueField s = (f' i).fiberToSpecResidueField s)
    (hrel : ∀ (i : Idx) (s : S), AlgebraicGeometry.RelativeDimension (p i s) e)
    (hsurj : ∀ (s : S) (x : f.fiber s), ∃ i, ∃ x' : (f' i).fiber s, (p i s).base x' = x)
    (β : ∀ i, FamilyOfCycles (f' i) (r + e))
    (hβ : ∀ (i : Idx) (s : S) (x : (f' i).fiber s),
      (β i s : AlgebraicCycle ((f' i).fiber s) ℤ) x =
        (α s : AlgebraicCycle (f.fiber s) ℤ) ((p i s).base x) *
          flatPullbackWeight (fieldChowSituation (S.residueField s))
            ((f' i).fiberToSpecResidueField s) (p i s) ((r : ℤ) + (e : ℤ)) x) :
    IsEffectiveFamily f r α ↔ ∀ i, IsEffectiveFamily (f' i) (r + e) (β i) := by
  constructor
  · intro hα i s x
    rw [hβ i s x]
    exact mul_nonneg ((isEffectiveFamily_iff f r α).1 hα s _)
      (flatPullbackWeight_nonneg (fieldChowSituation (S.residueField s))
        ((f' i).fiberToSpecResidueField s) (p i s) ((r : ℤ) + (e : ℤ)) x)
  · intro hβ' s
    rw [isEffectiveCycle_iff_nonneg]
    refine nonneg_of_forall_flatPullback_nonneg (fieldChowSituation (S.residueField s))
      (f.fiberToSpecResidueField s) (fun i => (f' i).fiberToSpecResidueField s) (p · s)
      (fun i => hp i s) e (fun i => hrel i s) (hsurj s) (r : ℤ) (α s) ?_
    intro i x
    rw [flatPullback_apply (fieldChowSituation (S.residueField s))
      ((f' i).fiberToSpecResidueField s) (f.fiberToSpecResidueField s) (p i s) (hp i s) e
      (hrel i s) (r : ℤ) (α s) x, ← hβ i s x]
    exact (isEffectiveFamily_iff (f' i) (r + e) (β i)).1 (hβ' i) s x

/-- **Stacks Project, Tag 0H5V.** Let `α` be a family of `r`-cycles on the fibres of `X/S` and
let `{g i : X' i ⟶ X}` be a jointly surjective family of flat morphisms, locally of finite type
and of relative dimension `e`. If `β i` is the flat pullback of `α` along `g i`, then `α` is
effective if and only if every `β i` is.

The fibres of `g i ≫ f` map to those of `f` by the base changes of the `g i`, again flat,
locally of finite type and of relative dimension `e`, and jointly surjective on every fibre, so
this is the fibrewise `Stacks.Chow.isEffectiveFamily_iff_forall`. -/
@[stacks 0H5V]
theorem isEffectiveFamily_iff_forall_flatPullback {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {r e : ℕ} (α : FamilyOfCycles f r) {Idx : Type*}
    {X' : Idx → Scheme.{u}} (g : ∀ i, X' i ⟶ X) [∀ i, LocallyOfFiniteType (g i)]
    [∀ i, Flat (g i)] (hrel : ∀ i, AlgebraicGeometry.RelativeDimension (g i) e)
    (hsurj : ∀ x : X, ∃ i, ∃ x' : X' i, (g i).base x' = x)
    (β : ∀ i, FamilyOfCycles (g i ≫ f) (r + e))
    (hβ : ∀ (i : Idx) (s : S) (x : (g i ≫ f).fiber s),
      (β i s : AlgebraicCycle ((g i ≫ f).fiber s) ℤ) x =
        (α s : AlgebraicCycle (f.fiber s) ℤ) ((f.fiberMap (g i) s).base x) *
          flatPullbackWeight (fieldChowSituation (S.residueField s))
            ((g i ≫ f).fiberToSpecResidueField s) (f.fiberMap (g i) s)
            ((r : ℤ) + (e : ℤ)) x) :
    IsEffectiveFamily f r α ↔ ∀ i, IsEffectiveFamily (g i ≫ f) (r + e) (β i) :=
  isEffectiveFamily_iff_forall f α (fun i => g i ≫ f) (fun i s => f.fiberMap (g i) s)
    (fun i s => f.fiberMap_fiberToSpecResidueField (g i) s)
    (fun i s => Scheme.Hom.relativeDimension_fiberMap f (g i) s e (hrel i))
    (fun s x => f.surjective_fiberMap_of_forall_exists g hsurj s x) β hβ

/-!
### Base change detects effectivity

A coefficient of the base change `g^*α` of a family of cycles on fibres along `g : S' ⟶ S` is,
by `Stacks.Chow.baseChangeFamily_apply`, a coefficient of `α` times the multiplicity with which
the point occurs in the residue-field base change of the reduced closure of the point carrying
that coefficient. The multiplicity is nonnegative, so base change preserves effectivity for any
`g`; and when `g` is surjective every coefficient of `α` is witnessed by a coefficient of
`g^*α` at which the multiplicity is nonzero, so base change also reflects effectivity.

## Main results

* `Stacks.Chow.isEffectiveFamily_baseChangeFamily` — base change along an arbitrary morphism of
  bases preserves effectivity.
* `Stacks.Chow.isEffectiveFamily_iff_baseChangeFamily` — along a surjective morphism of bases a
  family is effective exactly when its base change is.

## References

* [Stacks Project, Tag 0H5S](https://stacks.math.columbia.edu/tag/0H5S)
* [Stacks Project, Tag 0H5U](https://stacks.math.columbia.edu/tag/0H5U)
-/

/-- **Stacks Project, Tag 0H5S, base change.** The base change of an effective family of
`r`-cycles on the fibres of `X/S` along any morphism `g : S' ⟶ S` of bases is effective; no
surjectivity of `g` is needed. -/
@[stacks 0H5S "base change"]
theorem isEffectiveFamily_baseChangeFamily {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (g : S' ⟶ S) (r : ℕ)
    (α : FamilyOfCycles f r) (hα : IsEffectiveFamily f r α) :
    IsEffectiveFamily (pullback.snd f g) r (baseChangeFamily f g r α) := by
  intro t y
  rw [baseChangeFamily_apply f g r α t y]
  exact mul_nonneg (hα (g t) _) (closedSubschemeCycleCoeff_nonneg _ _ _ _ _)

/-- **Stacks Project, Tag 0H5U.** Let `α` be a family of `r`-cycles on the fibres of `X/S` and
let `g : S' ⟶ S` be surjective. Then `α` is effective if and only if its base change `g^*α` is
effective.

Effectivity is a condition on each coefficient separately, and a coefficient of `g^*α` is a
coefficient of `α` times a multiplicity. The multiplicity is nonnegative, which gives the
forward implication. For the converse, surjectivity supplies a point `t` of `S'` over a given
point of `S`, and over `t` the fibre of the base change has a point lying over the chosen point
of the fibre of `f` at which that multiplicity is nonzero, hence positive; so a negative
coefficient of `α` would make a coefficient of `g^*α` negative. -/
@[stacks 0H5U]
theorem isEffectiveFamily_iff_baseChangeFamily {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (g : S' ⟶ S) [Surjective g] (r : ℕ)
    (α : FamilyOfCycles f r) :
    IsEffectiveFamily f r α ↔
      IsEffectiveFamily (pullback.snd f g) r (baseChangeFamily f g r α) := by
  refine ⟨isEffectiveFamily_baseChangeFamily f g r α, fun hbc => ?_⟩
  rw [isEffectiveFamily_iff]
  intro s x
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨t, ht⟩ := Scheme.Hom.surjective g s
  subst ht
  have hdim : relativeDimension
      (fieldChowSituation ↥(S.residueField (g t))).dimensionFunction
      (f.fiberToSpecResidueField (g t)) x = (r : ℤ) :=
    (mem_cyclesOfDimension_iff_forall_point _ _ _ _).1 (α (g t)).2 x (ne_of_lt hneg)
  obtain ⟨y, hy, hc⟩ := exists_fiber_point_closedSubschemeCycleCoeff_ne_zero f g r t x hdim
  have hpos := lt_of_le_of_ne (closedSubschemeCycleCoeff_nonneg _ _ _ _ _) (Ne.symm hc)
  have hval := (isEffectiveFamily_iff (pullback.snd f g) r _).1 hbc t y
  rw [baseChangeFamily_apply f g r α t y, hy] at hval
  exact (mul_neg_of_neg_of_pos hneg hpos).not_ge hval

/-!
### Flat pullback and proper pushforward preserve effectivity

The two remaining operations of Lemma 0H5S are coefficientwise for the same reason as the first
two. A coefficient of the flat pullback `j^*α` of a family along a flat morphism `j : U ⟶ X` of
schemes over `S`, locally of finite type and of relative dimension `e`, is a coefficient of `α`
times the weight of the flat pullback, which is a multiplicity and hence nonnegative. A
coefficient of the proper pushforward `p_*α` along a proper morphism `p : X ⟶ Y` of schemes over
`S` is a locally finite sum of coefficients of `α`, each weighted by a residue-field degree or by
zero, and both weights are nonnegative.

## Main results

* `Stacks.Chow.properPushforward_nonneg` — proper pushforward preserves effectivity of a cycle.
* `Stacks.Chow.isEffectiveFamily_flatPullbackFamily` — flat pullback preserves effectivity of a
  family of cycles on fibres.
* `Stacks.Chow.isEffectiveFamily_properPushforwardFamily` — proper pushforward preserves
  effectivity of a family of cycles on fibres.
-/

/-- Proper pushforward carries effective cycles to effective cycles: a pushed-forward coefficient
is a locally finite sum of the coefficients above the point, each weighted by a residue-field
degree when the delta-dimension is preserved and by zero otherwise. -/
theorem properPushforward_nonneg (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p]
    (hp : p ≫ sY = sX) (k : ℤ) (c : CycleGroup C sX k)
    (hc : 0 ≤ (c : AlgebraicCycle X ℤ)) :
    0 ≤ ((properPushforward C sX sY p hp k c : CycleGroup C sY k) :
      AlgebraicCycle Y ℤ) := by
  intro y
  rw [properPushforward_apply C sX sY p hp k c y]
  refine finsum_nonneg fun x => finsum_nonneg fun _ => mul_nonneg (hc x) ?_
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

/-- **Stacks Project, Tag 0H5S, flat pullback.** The flat pullback of an effective family of
`r`-cycles on the fibres of `X/S` along a flat morphism `j : U ⟶ X` of schemes over `S`, locally
of finite type and of relative dimension `e`, is an effective family of `(r+e)`-cycles on the
fibres of `U/S`. -/
@[stacks 0H5S "flat pullback"]
theorem isEffectiveFamily_flatPullbackFamily {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (fU : U ⟶ S) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e) (r : ℕ) (α : FamilyOfCycles f r)
    (hα : IsEffectiveFamily f r α) :
    IsEffectiveFamily fU (r + e) (flatPullbackFamily f fU j h e he r α) := by
  intro s y
  rw [flatPullbackFamily_apply f fU j h e he r α s,
    fiberCycleFlatPullback_apply f fU j h e he s r (α s) y]
  exact mul_nonneg (hα s _) (flatPullbackWeight_nonneg _ _ _ _ _)

/-- **Stacks Project, Tag 0H5S, proper pushforward.** The proper pushforward of an effective
family of `r`-cycles on the fibres of `X/S` along a proper morphism `p : X ⟶ Y` of schemes over
`S` is an effective family of `r`-cycles on the fibres of `Y/S`. -/
@[stacks 0H5S "proper pushforward"]
theorem isEffectiveFamily_properPushforwardFamily {X Y S : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] [IsLocallyNoetherian S] (sY : Y ⟶ S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (r : ℕ) (α : FamilyOfCycles sX r)
    (hα : IsEffectiveFamily sX r α) :
    IsEffectiveFamily sY r (properPushforwardFamily sX sY p hp r α) := fun s =>
  properPushforward_nonneg (fieldChowSituation (S.residueField s))
    (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s)
    (inducedFiberMap sX sY p hp s) (inducedFiberMap_fiberToSpecResidueField sX sY p hp s)
    (r : ℤ) (α s) (hα s)

end Stacks.Chow
