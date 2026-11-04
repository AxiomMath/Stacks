module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of relative cycles to a large open subscheme

Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of finite type, let `r ≥ 0` and let
`j : U ⟶ X` be an open immersion over `S`. Restriction of families of cycles on fibres along `j`
carries relative `r`-cycles to relative `r`-cycles; that is the restriction clause of Tag 0H51,
proved in `StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction`. This
file shows that restriction is a *bijection* `z(X/S, r) ⟶ z(U/S, r)` as soon as the closed
complement of `U` has relative dimension `< r` over `S`, that is, as soon as
`dim(X_s \ U_s) < r` for every point `s` of `S`.

The inverse is extension by zero, constructed here and not chosen: on each fibre a cycle on
`U_s` is extended to `X_s` by `AlgebraicCycle.map` along the open immersion `U_s ⟶ X_s`, whose
coefficient at a point of `U_s` is the old coefficient and whose coefficient off `U_s` is zero.
Extension is a two-sided inverse of restriction on fibrewise cycle groups: one composite is the
identity because the fibre of an open immersion over a point of its image is that point, with
residue degree one and unchanged relative dimension — this is the computation behind the
surjectivity statement of Tag 02RC — and the other is the identity because a cycle of
delta-dimension `r` is supported in points of delta-dimension `r`, all of which lie in `U_s` by
the dimension hypothesis.

What remains is that extension by zero carries relative `r`-cycles to relative `r`-cycles. The
valuative condition of Definition 0H50 is tested after base change to the spectrum of a discrete
valuation ring `R`, so the dimension hypothesis has to travel along the base change. It does:
a point of `(X ×_S R)_t` outside `(U ×_S R)_t` maps to a point of `X_{g t}` outside `U_{g t}`,
because the base change of `j` is the inverse image of `j`; and its delta-dimension does not
exceed the delta-dimension of that image, because the fibre of the base change is the residue
field base change of the fibre, to which the dimension bound of Tag 0FVI applies with vanishing
shift. Restriction over the closed point of `Spec R` is therefore injective, and the two sides
of the valuative identity have the same restriction by the open-immersion case of Tag 0H4L
together with the compatibility of base change with restriction.

## Main definitions

* `Stacks.Chow.cycleGroupExtend` — extension by zero of a cycle along an open immersion.
* `Stacks.Chow.cycleGroupRestrictEquiv` — restriction of cycles as an additive equivalence, for
  an open immersion whose complement has delta-dimension `< k`.
* `Stacks.Chow.fiberCycleExtend` — extension by zero of a fibrewise cycle.
* `Stacks.Chow.ComplementFibreDimensionLT` — the hypothesis `dim(X_s \ U_s) < r` of Tag 0H5F.
* `Stacks.Chow.extendedFamily` — the family of cycles on the fibres of `X/S` obtained from a
  family on the fibres of `U/S` by extending each member by zero.
* `Stacks.Chow.relativeCyclesRestrictEquiv` — **Tag 0H5F**: restriction as a bijection
  `z(X/S, r) ⟶ z(U/S, r)`.

## Main results

* `Stacks.Chow.range_pullbackRestrict`, `Stacks.Chow.range_fiberRestrict` — the base change of
  an open immersion, and the induced open immersion of fibres, have as image the inverse image
  of the image of the original open immersion.
* `Stacks.Chow.relativeDimension_le_of_restrictedFiberMap` — the delta-dimension of a point of
  the fibre of a base change is at most the delta-dimension of its image in the fibre over the
  image point.
* `Stacks.Chow.ComplementFibreDimensionLT.baseChange` — the dimension hypothesis of Tag 0H5F is
  stable under base change of the base scheme.
* `Stacks.Chow.cycleGroupRestrict_injective`, `Stacks.Chow.fiberCycleRestrict_injective` —
  injectivity of restriction under the dimension hypothesis.
* `Stacks.Chow.isRelativeCycle_extendedFamily` — the extension by zero of a relative `r`-cycle
  on `U/S` is a relative `r`-cycle on `X/S`.
* `Stacks.Chow.relativeCyclesRestrictEquiv_apply`,
  `Stacks.Chow.relativeCyclesRestrictEquiv_symm_apply` — the two directions of the bijection are
  fibrewise restriction and fibrewise extension by zero.

## Implementation notes

The hypothesis `dim(X_s \ U_s) < r` is carried in the pointwise form
`Stacks.Chow.ComplementFibreDimensionLT`: every point of `X_s` outside `U_s` has
delta-dimension `< r`. For a scheme locally of finite type over a field the delta-dimension of a
point is the dimension of the closure of that point, so the supremum of the delta-dimensions of
the points of the closed set `X_s \ U_s` is its dimension; the pointwise form therefore says
exactly that this dimension is `< r`, and it avoids equipping the complement with a scheme
structure.

An open subscheme of `X` is given by an open immersion `j : U ⟶ X` together with a structure
morphism `f_U : U ⟶ S` and the identity `j ≫ f = f_U`, matching the convention of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction`, so that the
results apply to the open immersions produced by base change.

## References

* [Stacks Project, Lemma 0H5F](https://stacks.math.columbia.edu/tag/0H5F)
* [Stacks Project, Lemma 0H53](https://stacks.math.columbia.edu/tag/0H53)
* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Tag 0H4L](https://stacks.math.columbia.edu/tag/0H4L)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Extension by zero of a cycle along an open immersion -/

/-- The coefficient of the extension by zero at a point of the open subscheme is the old
coefficient: the fibre of an open immersion over a point of its image is that one point, of
residue degree one and of the same relative dimension. -/
private theorem cycleExtendCoeff_image (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hj : j ≫ sX = sU) (c : AlgebraicCycle U ℤ) (z : U) :
    AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
      (relativeDimension C.dimensionFunction sX) c (j.base z) = c z := by
  have hfibre : j.base ⁻¹' {j.base z} = {z} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hw ↦ j.isOpenEmbedding.injective hw, fun hw ↦ hw ▸ rfl⟩
  have hdim : relativeDimension C.dimensionFunction sX (j.base z) =
      relativeDimension C.dimensionFunction sU z := by
    subst hj
    exact (relativeDimension_comp_isOpenImmersion C.dimensionFunction j sX z).symm
  rw [AlgebraicCycle.map, Function.locallyFinsupp.map_apply, hfibre, finsum_mem_singleton,
    AlgebraicCycle.mapCoeff, hdim, residueDegree_eq_one_of_isOpenImmersion]
  simp

/-- The coefficient of the extension by zero vanishes off the open subscheme: there the fibre of
the open immersion is empty. -/
private theorem cycleExtendCoeff_notMem_range (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (c : AlgebraicCycle U ℤ) (x : X)
    (hx : x ∉ Set.range j.base) :
    AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
      (relativeDimension C.dimensionFunction sX) c x = 0 := by
  have hfibre : j.base ⁻¹' {x} = ∅ := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun hw ↦ hx ⟨w, hw⟩
  rw [AlgebraicCycle.map, Function.locallyFinsupp.map_apply, hfibre, finsum_mem_empty]

/-- **Stacks Project, Tag 02RC.** Extension by zero of a `k`-cycle along an open immersion
`j : U ⟶ X` over the base: the coefficient at a point of `U` is kept and the coefficient off `U`
is zero. This is the section of restriction exhibited in the proof that restriction of cycles to
an open subscheme is surjective. -/
def cycleGroupExtend (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ) :
    CycleGroup C sU k →+ CycleGroup C sX k :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : QuasiCompact j := inferInstance
  { toFun := fun d => ⟨AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
        (relativeDimension C.dimensionFunction sX) d.1,
      map_mem_cyclesOfDimension_of_isOpenImmersion C sX sU j hj k d⟩
    map_zero' := by
      apply Subtype.ext
      apply Function.locallyFinsuppWithin.ext
      intro x
      change AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
        (relativeDimension C.dimensionFunction sX) (0 : AlgebraicCycle U ℤ) x = 0
      by_cases hx : x ∈ Set.range j.base
      · obtain ⟨z, rfl⟩ := hx
        rw [cycleExtendCoeff_image C sX sU j hj]
        rfl
      · exact cycleExtendCoeff_notMem_range C sX sU j _ x hx
    map_add' := fun a b => by
      apply Subtype.ext
      apply Function.locallyFinsuppWithin.ext
      intro x
      change AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
          (relativeDimension C.dimensionFunction sX) (a.1 + b.1) x =
        AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
          (relativeDimension C.dimensionFunction sX) a.1 x +
        AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
          (relativeDimension C.dimensionFunction sX) b.1 x
      by_cases hx : x ∈ Set.range j.base
      · obtain ⟨z, rfl⟩ := hx
        rw [cycleExtendCoeff_image C sX sU j hj, cycleExtendCoeff_image C sX sU j hj,
          cycleExtendCoeff_image C sX sU j hj]
        rfl
      · rw [cycleExtendCoeff_notMem_range C sX sU j _ x hx,
          cycleExtendCoeff_notMem_range C sX sU j _ x hx,
          cycleExtendCoeff_notMem_range C sX sU j _ x hx, add_zero] }

/-- The coefficient of an extension by zero at a point of the open subscheme. -/
@[simp]
theorem cycleGroupExtend_apply_image (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ) (d : CycleGroup C sU k) (z : U) :
    (cycleGroupExtend C sX sU j hj k d).1 (j.base z) = d.1 z := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let _ : QuasiCompact j := inferInstance
  exact cycleExtendCoeff_image C sX sU j hj d.1 z

/-- The coefficient of an extension by zero vanishes off the open subscheme. -/
theorem cycleGroupExtend_apply_of_notMem_range (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ) (d : CycleGroup C sU k) (x : X)
    (hx : x ∉ Set.range j.base) : (cycleGroupExtend C sX sU j hj k d).1 x = 0 := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let _ : QuasiCompact j := inferInstance
  exact cycleExtendCoeff_notMem_range C sX sU j d.1 x hx

/-- Restricting an extension by zero returns the original cycle. -/
@[simp]
theorem cycleGroupRestrict_cycleGroupExtend (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ) (d : CycleGroup C sU k) :
    cycleGroupRestrict C sX sU j hj k (cycleGroupExtend C sX sU j hj k d) = d := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [cycleGroupRestrict_apply, cycleGroupExtend_apply_image]

/-- Extending a restriction by zero returns the original cycle, provided every point outside the
open subscheme has delta-dimension `< k`: such a point cannot carry a nonzero coefficient of a
`k`-cycle. -/
theorem cycleGroupExtend_cycleGroupRestrict (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ)
    (hdim : ∀ x : X, x ∉ Set.range j.base → relativeDimension C.dimensionFunction sX x < k)
    (c : CycleGroup C sX k) :
    cycleGroupExtend C sX sU j hj k (cycleGroupRestrict C sX sU j hj k c) = c := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ Set.range j.base
  · obtain ⟨z, rfl⟩ := hx
    rw [cycleGroupExtend_apply_image, cycleGroupRestrict_apply]
  · rw [cycleGroupExtend_apply_of_notMem_range C sX sU j hj k _ x hx]
    by_contra hne
    exact (hdim x hx).ne
      ((mem_cyclesOfDimension_iff_forall_point C sX k c.1).mp c.2 x (Ne.symm hne))

/-- Restriction of cycles to an open subscheme whose complement has delta-dimension `< k` is
injective. -/
theorem cycleGroupRestrict_injective (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ)
    (hdim : ∀ x : X, x ∉ Set.range j.base → relativeDimension C.dimensionFunction sX x < k) :
    Function.Injective (cycleGroupRestrict C sX sU j hj k) :=
  Function.LeftInverse.injective (cycleGroupExtend_cycleGroupRestrict C sX sU j hj k hdim)

/-- **Stacks Project, Tag 02RC.** Restriction of `k`-cycles to an open subscheme whose complement
has delta-dimension `< k` is an additive equivalence, with inverse the extension by zero. -/
def cycleGroupRestrictEquiv (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ)
    (hdim : ∀ x : X, x ∉ Set.range j.base → relativeDimension C.dimensionFunction sX x < k) :
    CycleGroup C sX k ≃+ CycleGroup C sU k where
  toFun := cycleGroupRestrict C sX sU j hj k
  invFun := cycleGroupExtend C sX sU j hj k
  left_inv := cycleGroupExtend_cycleGroupRestrict C sX sU j hj k hdim
  right_inv := cycleGroupRestrict_cycleGroupExtend C sX sU j hj k
  map_add' a b := map_add (cycleGroupRestrict C sX sU j hj k) a b

/-! ### The image of the base change of an open immersion -/

/-- The base change of an open immersion `j : U ⟶ X` of schemes over `S` along `g : T ⟶ S` has
as image the inverse image of the image of `j`. -/
theorem range_pullbackRestrict {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (g : T ⟶ S) :
    Set.range (pullbackRestrict f fU j h g).base =
      (pullback.fst f g).base ⁻¹' Set.range j.base := by
  have hmap := Scheme.Pullback.range_map (f := fU) (g := g) f g j (𝟙 T) (𝟙 S)
    (by simpa using h.symm) (by simp)
  rw [show (pullbackRestrict f fU j h g) =
    pullback.map fU g f g j (𝟙 _) (𝟙 _) (by simpa using h.symm) (by simp) from rfl, hmap]
  simp

/-- The open immersion of scheme-theoretic fibres induced by an open immersion `j : U ⟶ X` of
schemes over `S` has as image the inverse image in `X_s` of the image of `j`. -/
theorem range_fiberRestrict {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (s : S) :
    Set.range (fiberRestrict f fU j h s).base = (f.fiberι s).base ⁻¹' Set.range j.base :=
  range_pullbackRestrict f fU j h (S.fromSpecResidueField s)

/-! ### Delta-dimension and base change of the base scheme -/

/-- **A case of Stacks Project, Tag 0FVI, part (1).** The delta-dimension of a point of the fibre
of a base change `X ×_S T ⟶ T` is at most the delta-dimension of its image in the fibre of
`X ⟶ S` over the image point.

The fibre of the base change over `t` is the base change of the fibre over `g t` along the
residue field extension `κ(t)/κ(g t)`, whose dimension shift vanishes. The image point lies in
its own integral closed subscheme, whose delta-dimension is the delta-dimension of that point,
and the point itself lies in the base change of that closed subscheme. -/
theorem relativeDimension_le_of_restrictedFiberMap {X S T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : T ⟶ S) (t : T) (x : (pullback.snd f g).fiber t) :
    relativeDimension (fieldChowSituation (T.residueField t)).dimensionFunction
        ((pullback.snd f g).fiberToSpecResidueField t) x ≤
      relativeDimension (fieldChowSituation (S.residueField (g t))).dimensionFunction
        (f.fiberToSpecResidueField (g t))
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) := by
  set B := residueFieldBaseChangeSituation g t
  set q := f.fiberToSpecResidueField (g t)
  set y := restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x
  set i := (integralComponentAt y).subschemeι with hi
  have hZ : schemeDeltaDimension B.base (i ≫ q) =
      ((relativeDimension B.base.dimensionFunction q y : ℤ) : EInt) :=
    schemeDeltaDimension_integralComponentAt B.base q y
  have hbound := schemeDeltaDimension_baseChange_closedSubscheme_le B q i hZ.le
  set x' := (fibreBaseChangeIso f g t).hom x
  have hfst : pullback.fst q B.g x' = y := fst_fibreBaseChangeIso_hom f g t x
  have hmem : pullback.fst q B.g x' ∈ Set.range i := by
    rw [hfst, hi, Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    exact subset_closure rfl
  obtain ⟨w, hw⟩ : x' ∈ Set.range (pullback.snd i (pullback.fst q B.g)) := by
    rwa [Scheme.Pullback.range_snd]
  have hdimx : relativeDimension B.baseChange.dimensionFunction
      ((pullback.snd f g).fiberToSpecResidueField t) x =
      relativeDimension B.baseChange.dimensionFunction (pullback.snd q B.g) x' := by
    rw [← fibreBaseChangeIso_hom_snd f g t]
    exact relativeDimension_comp_isOpenImmersion B.baseChange.dimensionFunction
      (fibreBaseChangeIso f g t).hom (pullback.snd q B.g) x
  have hle := relativeDimension_le_of_schemeDeltaDimension_le B.baseChange (pullback.snd q B.g)
    (pullback.snd i (pullback.fst q B.g)) (by simpa using hbound) w
  rw [hw] at hle
  rwa [hdimx]

/-! ### The dimension hypothesis of Tag 0H5F -/

/-- **The hypothesis of Stacks Project, Lemma 0H5F.** The closed complement of the open
subscheme `j : U ⟶ X` has relative dimension `< r` over `S`: for every point `s` of `S`, every
point of the fibre `X_s` outside `U_s` has delta-dimension `< r`.

For a scheme locally of finite type over a field, the delta-dimension of a point is the dimension
of the closure of that point, so this says exactly that `dim(X_s \ U_s) < r`. -/
def ComplementFibreDimensionLT {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) (h : j ≫ f = fU) (r : ℕ) : Prop :=
  ∀ (s : S) (x : f.fiber s), x ∉ Set.range (fiberRestrict f fU j h s).base →
    relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) x < (r : ℤ)

/-- The dimension hypothesis of Tag 0H5F is stable under base change of the base scheme: the
base change of `j` is the inverse image of `j`, so a point of the fibre of `X ×_S T` outside the
base change of `U` maps to a point of the corresponding fibre of `X` outside `U`, and its
delta-dimension does not exceed the delta-dimension of that image. -/
theorem ComplementFibreDimensionLT.baseChange {X S U T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ)
    (hdim : ComplementFibreDimensionLT f fU j h r) (g : T ⟶ S) :
    ComplementFibreDimensionLT (pullback.snd f g) (pullback.snd fU g)
      (pullbackRestrict f fU j h g) (pullbackRestrict_snd f fU j h g) r := by
  intro t x hx
  set w := restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x
  have hxw : f.fiberι (g t) w = pullback.fst f g ((pullback.snd f g).fiberι t x) := by
    have hmap := congrArg (fun m : (pullback.snd f g).fiber t ⟶ X => m x)
      (restrictedFiberMap_fiberι f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
    simpa only [Scheme.Hom.comp_apply] using hmap
  have hxnot : (pullback.snd f g).fiberι t x ∉ Set.range (pullbackRestrict f fU j h g).base := by
    rwa [range_fiberRestrict (pullback.snd f g) (pullback.snd fU g)
      (pullbackRestrict f fU j h g) (pullbackRestrict_snd f fU j h g) t] at hx
  have hwnot : w ∉ Set.range (fiberRestrict f fU j h (g t)).base := by
    rw [range_fiberRestrict f fU j h (g t)]
    intro hcon
    rw [range_pullbackRestrict f fU j h g] at hxnot
    exact hxnot (by simpa only [Set.mem_preimage, ← hxw] using hcon)
  exact (relativeDimension_le_of_restrictedFiberMap f g t x).trans_lt (hdim (g t) w hwnot)

/-! ### Extension by zero of a fibrewise cycle -/

/-- Extension by zero of fibrewise `r`-cycles along an open immersion of the source over a fixed
base: the coefficient at a point of `U_s` is kept and the coefficient off `U_s` is zero. -/
def fiberCycleExtend {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ S)
    [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU) (s : S) (r : ℕ) :
    FiberCycleGroup fU s r →+ FiberCycleGroup f s r :=
  have : IsOpenImmersion (fiberRestrict f fU j h s) := isOpenImmersion_fiberRestrict f fU j h s
  cycleGroupExtend (fieldChowSituation (S.residueField s)) (f.fiberToSpecResidueField s)
    (fU.fiberToSpecResidueField s) (fiberRestrict f fU j h s)
    (fiberRestrict_fiberToSpecResidueField f fU j h s) (r : ℤ)

/-- Restricting an extension by zero of a fibrewise cycle returns the original cycle. -/
@[simp]
theorem fiberCycleRestrict_fiberCycleExtend {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (s : S) (r : ℕ) (d : FiberCycleGroup fU s r) :
    fiberCycleRestrict f fU j h s r (fiberCycleExtend f fU j h s r d) = d :=
  have : IsOpenImmersion (fiberRestrict f fU j h s) := isOpenImmersion_fiberRestrict f fU j h s
  cycleGroupRestrict_cycleGroupExtend (fieldChowSituation (S.residueField s))
    (f.fiberToSpecResidueField s) (fU.fiberToSpecResidueField s) (fiberRestrict f fU j h s)
    (fiberRestrict_fiberToSpecResidueField f fU j h s) (r : ℤ) d

/-- Extending the restriction of a fibrewise `r`-cycle by zero returns the original cycle, under
the dimension hypothesis of Tag 0H5F. -/
theorem fiberCycleExtend_fiberCycleRestrict {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ)
    (hdim : ComplementFibreDimensionLT f fU j h r) (s : S) (c : FiberCycleGroup f s r) :
    fiberCycleExtend f fU j h s r (fiberCycleRestrict f fU j h s r c) = c :=
  have : IsOpenImmersion (fiberRestrict f fU j h s) := isOpenImmersion_fiberRestrict f fU j h s
  cycleGroupExtend_cycleGroupRestrict (fieldChowSituation (S.residueField s))
    (f.fiberToSpecResidueField s) (fU.fiberToSpecResidueField s) (fiberRestrict f fU j h s)
    (fiberRestrict_fiberToSpecResidueField f fU j h s) (r : ℤ) (hdim s) c

/-- Restriction of fibrewise `r`-cycles is injective under the dimension hypothesis of
Tag 0H5F. -/
theorem fiberCycleRestrict_injective {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU)
    (r : ℕ) (hdim : ComplementFibreDimensionLT f fU j h r) (s : S) :
    Function.Injective (fiberCycleRestrict f fU j h s r) :=
  Function.LeftInverse.injective (fiberCycleExtend_fiberCycleRestrict f fU j h r hdim s)

/-! ### Extension by zero of a family of cycles on fibres -/

/-- The family of `r`-cycles on the fibres of `X/S` obtained from a family on the fibres of `U/S`
by extending each member by zero. -/
def extendedFamily {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ S)
    [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ)
    (β : FamilyOfCycles fU r) : FamilyOfCycles f r :=
  fun s => fiberCycleExtend f fU j h s r (β s)

/-- The restriction of an extended family is the original family. -/
@[simp]
theorem fiberCycleRestrict_extendedFamily {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ) (β : FamilyOfCycles fU r) (s : S) :
    fiberCycleRestrict f fU j h s r (extendedFamily f fU j h r β s) = β s :=
  fiberCycleRestrict_fiberCycleExtend f fU j h s r (β s)

/-- **The converse of the restriction clause of Stacks Project, Lemma 0H51, for an open immersion
whose complement has relative dimension `< r`.** The extension by zero of a relative `r`-cycle on
`U/S` is a relative `r`-cycle on `X/S`.

After base change to the spectrum of a discrete valuation ring `R`, the restriction to the base
change of `U` of the two sides of the valuative identity agree: on the left by the open-immersion
case of Tag 0H4L and the compatibility of base change with restriction, on the right because the
restriction of the extended family is the given family. The dimension hypothesis survives the
base change, so restriction over the closed point of `Spec R` is injective and the two sides are
equal. -/
theorem isRelativeCycle_extendedFamily {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ)
    (hdim : ComplementFibreDimensionLT f fU j h r) {β : FamilyOfCycles fU r}
    (hβ : IsRelativeCycle fU r β) : IsRelativeCycle f r (extendedFamily f fU j h r β) := by
  intro R _ _ _ g
  set α := extendedFamily f fU j h r β
  refine fiberCycleRestrict_injective (pullback.snd f g) (pullback.snd fU g)
    (pullbackRestrict f fU j h g) (pullbackRestrict_snd f fU j h g) r
    (ComplementFibreDimensionLT.baseChange f fU j h r hdim g) (IsLocalRing.closedPoint R) ?_
  rw [← specializationCycle_fiberCycleRestrict (pullback.snd f g) (pullback.snd fU g)
      (pullbackRestrict f fU j h g) (pullbackRestrict_snd f fU j h g) r
      (baseChangeFamily f g r α (genericPoint (Spec (.of R)))),
    ← baseChangeFamily_fiberCycleRestrict f fU j h g r α (genericPoint (Spec (.of R))),
    ← baseChangeFamily_fiberCycleRestrict f fU j h g r α (IsLocalRing.closedPoint R)]
  have hres : (fun s => fiberCycleRestrict f fU j h s r (α s)) = β :=
    funext fun s => fiberCycleRestrict_extendedFamily f fU j h r β s
  rw [hres]
  exact hβ R g

/-! ### Tag 0H5F -/

/-- **Stacks Project, Lemma 0H5F.** Let `S` be a locally Noetherian scheme, let `X` be a scheme
locally of finite type over `S`, let `r ≥ 0` and let `j : U ⟶ X` be an open immersion over `S`
such that the complement of `U` has relative dimension `< r` over `S`, that is
`dim(X_s \ U_s) < r` for all `s ∈ S`. Then restriction is a bijection
`z(X/S, r) ⟶ z(U/S, r)`.

The inverse is extension by zero, not a chosen section: fibrewise, the cycle on `X_s` keeps the
coefficients of the cycle on `U_s` and vanishes off `U_s`. -/
@[stacks 0H5F "restriction is a bijection z(X/S, r) → z(U/S, r)"]
def relativeCyclesRestrictEquiv {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ)
    (hdim : ComplementFibreDimensionLT f fU j h r) :
    relativeCycles f r ≃+ relativeCycles fU r where
  toFun α := ⟨fun s => fiberCycleRestrict f fU j h s r (α.1 s),
    isRelativeCycle_fiberCycleRestrict f fU j h r α.2⟩
  invFun β := ⟨extendedFamily f fU j h r β.1,
    isRelativeCycle_extendedFamily f fU j h r hdim β.2⟩
  left_inv α := Subtype.ext (funext fun s =>
    fiberCycleExtend_fiberCycleRestrict f fU j h r hdim s (α.1 s))
  right_inv β := Subtype.ext (funext fun s =>
    fiberCycleRestrict_extendedFamily f fU j h r β.1 s)
  map_add' α β := Subtype.ext (funext fun s =>
    map_add (fiberCycleRestrict f fU j h s r) (α.1 s) (β.1 s))

/-- The bijection of Tag 0H5F is fibrewise restriction of cycles. -/
@[simp]
theorem relativeCyclesRestrictEquiv_apply {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (fU : U ⟶ S) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ)
    (hdim : ComplementFibreDimensionLT f fU j h r) (α : relativeCycles f r) (s : S) :
    (relativeCyclesRestrictEquiv f fU j h r hdim α).1 s =
      fiberCycleRestrict f fU j h s r (α.1 s) :=
  rfl

/-- The inverse of the bijection of Tag 0H5F is fibrewise extension by zero. -/
@[simp]
theorem relativeCyclesRestrictEquiv_symm_apply {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (fU : U ⟶ S) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ)
    (hdim : ComplementFibreDimensionLT f fU j h r) (β : relativeCycles fU r) (s : S) :
    ((relativeCyclesRestrictEquiv f fU j h r hdim).symm β).1 s =
      fiberCycleExtend f fU j h s r (β.1 s) :=
  rfl

end Stacks.Chow

end
