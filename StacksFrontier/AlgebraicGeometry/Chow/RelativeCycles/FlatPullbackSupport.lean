module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatPullbackFamily
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.CycleSupport
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of a flat pullback of a family of cycles

Let `f : X ⟶ S` be locally of finite type, let `α` be a family of `r`-cycles on the fibres of
`X/S` and let `j : U ⟶ X` be a flat morphism, locally of finite type and of relative dimension
`e`, viewed as a morphism of schemes over `S`. The support of the flat pullback `j^*α`, a family
of `(r+e)`-cycles on the fibres of `U/S`, is the inverse image of the support of `α` along `j`.

The fibrewise statement is the compatibility of the support of a single cycle with flat pullback
in a fixed Chow situation, which is proved first. One inclusion is formal: the coefficient of a
flat pullback at a point is a multiple of the coefficient of the cycle at its image, so the
support of the pullback is contained in the inverse image of the support, which is closed. For
the other, let `x` be a point of `U` whose image lies in the support of a cycle `z`, that is in
the closure of some point `a` with `z a ≠ 0`. Since `j` is flat it is generalizing, so the
generalization `a` of the image of `x` lifts to a generalization `v` of `x` over `a`. The point
`v` need not carry a nonzero coefficient, but it is a specialization of the image `y` of a
generic point of the scheme-theoretic inverse image of the reduced closure of `a`; at such a
point the weight entering the pullback is nonzero, and its relative dimension is that of `a`
plus `e`, which is what the dimension condition in the definition of the weight asks for. So the
coefficient of the pullback at `y` is a product of two nonzero integers, and `x` lies in the
closure of `y`.

Globally the support of a family is the union over the base of the images of the supports of its
members, so the two descriptions are matched point by point: a point of `U` lies in the fibre
over its image in `S`, its image in `X` lies in the fibre of `f` over the same point, and the
induced morphism of fibres is compatible with the inclusions of the fibres into the total
spaces.

## Main results

* `Stacks.Chow.tsupport_flatPullback` — the support of a flat pullback of a cycle is the inverse
  image of its support.
* `Stacks.Chow.tsupport_fiberCycleFlatPullback` — the fibrewise form of the compatibility.
* `Stacks.Chow.supportOfFamily_flatPullbackFamily` — the support of a flat pullback of a family
  of cycles is the inverse image of the support of the original family.

## Implementation notes

The reduced closure of a point is represented by the subscheme of its vanishing ideal sheaf and
its inverse image by the `comap` of that ideal sheaf, exactly as in the definition of the flat
pullback weight.

The support of a family of cycles is rarely closed in the total space, so the global statement
is an equality of subsets and not of closed subsets; the inverse image of the support of `α` is
nonetheless exactly the support of `j^*α`, with no closure taken.

A point `x` of `U` is viewed as a point of the fibre over its image in `S` through
`AlgebraicGeometry.Scheme.Hom.asFiber`.

## References

* [Stacks Project, Tag 0H4V](https://stacks.math.columbia.edu/tag/0H4V)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The support of a cycle under flat pullback -/

/-- The support of a flat pullback of a cycle is the inverse image of its support. -/
theorem tsupport_flatPullback (C : ChowSituation.{u}) {T Y : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (h : T ⟶ Y)
    [LocallyOfFiniteType h] [Flat h] (hbase : h ≫ sY = sT) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension h e) (k : ℤ) (z : CycleGroup C sY k) :
    tsupport (flatPullback C sT sY h hbase e he k z).1 = h ⁻¹' tsupport z.1 := by
  apply subset_antisymm
  · refine closure_minimal ?_ ((isClosed_tsupport _).preimage h.continuous)
    intro x hx
    rw [Function.mem_support, flatPullback_apply] at hx
    exact subset_closure (Function.mem_support.mpr (mul_ne_zero_iff.mp hx).1)
  · intro x hx
    have hlfs : LocallyFiniteSupport ⇑(z.1 : AlgebraicCycle Y ℤ) :=
      Function.locallyFinsupp.locallyFiniteSupport z.1
    rw [Set.mem_preimage, tsupport_eq_biUnion_closure_singleton hlfs] at hx
    obtain ⟨a, ha, hclos⟩ := Set.mem_iUnion₂.mp hx
    have hza : z.1 a ≠ 0 := Function.mem_support.mp ha
    obtain ⟨v, hvx, hva⟩ := Flat.generalizingMap h (specializes_iff_mem_closure.mpr hclos)
    obtain ⟨ξ, hξv, hξa⟩ := exists_comap_genericPoint_over h a v hva
    set y := (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({a} : Set Y))).comap h).subschemeι).base ξ.1 with hy
    have hk : relativeDimension C.dimensionFunction sY a = k :=
      (mem_cyclesOfDimension_iff_forall_point C sY k (z.1 : AlgebraicCycle Y ℤ)).mp z.2 a hza
    have hdim : relativeDimension C.dimensionFunction sT y = k + (e : ℤ) := by
      rw [hy, relativeDimension_comap_genericPoint_eq_add C sY sT h hbase e he a ξ, hk]
    have hweight := flatPullbackWeight_ne_zero_of_genericPoint C sT h (k + (e : ℤ)) a y ξ rfl
      hξa hdim
    have hysupport : y ∈ Function.support ⇑(flatPullback C sT sY h hbase e he k z).1 := by
      rw [Function.mem_support, flatPullback_apply, hξa]
      exact mul_ne_zero hza hweight
    exact closure_mono (Set.singleton_subset_iff.mpr hysupport)
      (specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hξv).trans hvx))

/-! ### The support of a flat pullback of a family of cycles -/

/-- The fibrewise form: the support of the flat pullback of the member of a family over `s` is
the inverse image of the support of that member along the induced morphism of fibres. -/
theorem tsupport_fiberCycleFlatPullback {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j]
    (hj : j ≫ f = fU) (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (s : S) (r : ℕ)
    (c : FiberCycleGroup f s r) :
    tsupport (fiberCycleFlatPullback f fU j hj e he s r c :
        AlgebraicCycle (fU.fiber s) ℤ) =
      fiberRestrict f fU j hj s ⁻¹' tsupport (c : AlgebraicCycle (f.fiber s) ℤ) :=
  tsupport_flatPullback (fieldChowSituation (S.residueField s)) (fU.fiberToSpecResidueField s)
    (f.fiberToSpecResidueField s) (fiberRestrict f fU j hj s)
    (fiberRestrict_fiberToSpecResidueField f fU j hj s) e
    (relativeDimension_fiberRestrict f fU j hj s he) (r : ℤ) c

/-- The fibre morphism induced by `j` is compatible with the inclusions of the fibres into the
total spaces, pointwise. -/
theorem fiberι_fiberRestrict_apply {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    (hj : j ≫ f = fU) (t : S) (y : fU.fiber t) :
    f.fiberι t (fiberRestrict f fU j hj t y) = j (fU.fiberι t y) :=
  congrArg (fun m : fU.fiber t ⟶ X => m y) (fiberRestrict_fiberι f fU j hj t)

/-- The support of a flat pullback of a family of cycles is the inverse image of the support of
the family, with the structure morphism of the source assumed locally of finite type. -/
private theorem supportOfFamily_flatPullbackFamily_aux {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [LocallyOfFiniteType j] [Flat j] (hj : j ≫ f = fU) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e) (r : ℕ) (α : FamilyOfCycles f r) :
    supportOfFamily fU (flatPullbackFamily f fU j hj e he r α) = j ⁻¹' supportOfFamily f α := by
  ext x
  simp only [Set.mem_preimage, mem_supportOfFamily]
  constructor
  · rintro ⟨t, y, hy, hyx⟩
    rw [flatPullbackFamily_apply, tsupport_fiberCycleFlatPullback] at hy
    exact ⟨t, fiberRestrict f fU j hj t y, hy, by rw [fiberι_fiberRestrict_apply, hyx]⟩
  · rintro ⟨s, z, hz, hzx⟩
    have hfz : f (f.fiberι s z) = s := (f.range_fiberι s).le ⟨z, rfl⟩
    obtain rfl : s = fU x := by
      have hjx : f (j x) = fU x := by simpa using congrArg (fun m : U ⟶ S => m x) hj
      rw [← hjx, ← hzx, hfz]
    refine ⟨fU x, fU.asFiber x, ?_, Scheme.Hom.fiberι_asFiber _ _⟩
    rw [flatPullbackFamily_apply, tsupport_fiberCycleFlatPullback]
    have hmx : fiberRestrict f fU j hj (fU x) (fU.asFiber x) = z :=
      (f.fiberι (fU x)).isEmbedding.injective (by
        rw [fiberι_fiberRestrict_apply, Scheme.Hom.fiberι_asFiber, hzx])
    exact Set.mem_preimage.mpr (hmx ▸ hz)

/-- **Stacks Project, Tag 0H4V, the flat pullback clause.** Taking the support of a family of
cycles on the fibres is compatible with flat pullback: the support of `j^*α` is the inverse
image of the support of `α` along `j`. -/
@[stacks 0H4V "flat pullback"]
theorem supportOfFamily_flatPullbackFamily {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j]
    (hj : j ≫ f = fU) (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (r : ℕ)
    (α : FamilyOfCycles f r) :
    letI : LocallyOfFiniteType fU := hj ▸ (inferInstance : LocallyOfFiniteType (j ≫ f))
    supportOfFamily fU (flatPullbackFamily f fU j hj e he r α) = j ⁻¹' supportOfFamily f α :=
  let : LocallyOfFiniteType fU := hj ▸ (inferInstance : LocallyOfFiniteType (j ≫ f))
  supportOfFamily_flatPullbackFamily_aux f fU j hj e he r α

end Stacks.Chow

end
