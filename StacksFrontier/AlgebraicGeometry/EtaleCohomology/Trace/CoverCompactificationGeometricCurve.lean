module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.DenseOpenGeometricallyIrreducible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.EtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparableClosure

/-!
# The geometric fibre of the compactification of a geometrically irreducible cover

Let `C : V ⟶ V̄` be the smooth projective compactification of a connected finite étale cover
`V ⟶ U` of a smooth curve over a perfect field `k` (`AlgebraicGeometry.CoverCompactification`).
If `V` is geometrically irreducible over `k`, so is `V̄`, `V` being a dense open of it; hence for
every extension `K` of `k` the base change `V̄_K` is a smooth proper curve over `K`
([Stacks, Tag 0BY9] for the dimension). A smooth scheme over a perfect field whose base change to
an algebraic closure is connected is geometrically irreducible ([Stacks, Tag 0387] and normality
of smooth schemes), which gives the hypothesis for a smooth curve `U` with `U_k̄` connected.

These are the hypotheses under which `H²(V̄_k̄, ℤ/m) ≅ ℤ/m`
(`Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_two_constant`), used in the
proof of [Stacks, Tag 03VK].

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_of_connectedSpace_pullback_isAlgClosure`.
* `AlgebraicGeometry.CoverCompactification.geometricallyIrreducible_q` and
  `AlgebraicGeometry.CoverCompactification.geometricallyIrreducible_j_comp_q`.
* `AlgebraicGeometry.CoverCompactification.isCurve_fieldBaseChange`,
  `AlgebraicGeometry.CoverCompactification.smooth_fieldBaseChange`,
  `AlgebraicGeometry.CoverCompactification.isProper_fieldBaseChange`.

## References

* [Stacks Project, Tag 0387](https://stacks.math.columbia.edu/tag/0387)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A smooth scheme over a perfect field whose base change to an algebraic closure is connected
is geometrically irreducible**: the algebraic closure is a separable closure, so the scheme is
geometrically connected ([Stacks, Tag 0387]), and a geometrically connected smooth scheme is
geometrically irreducible. -/
theorem geometricallyIrreducible_of_connectedSpace_pullback_isAlgClosure {k : Type u} [Field k]
    [PerfectField k] (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h : ConnectedSpace
      ↥(pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) :
    GeometricallyIrreducible f :=
  geometricallyIrreducible_of_geometricallyConnected_of_smooth f
    ((geometricallyConnected_iff_connectedSpace_baseChange k kbar f).2 h)

namespace CoverCompactification

variable {k : Type u} [Field k] {U Ub V : Scheme.{u}} {pUb : Ub ⟶ Spec (.of k)} {jU : U ⟶ Ub}
  {f : V ⟶ U} [ConnectedSpace V] (C : CoverCompactification k pUb jU f)

/-- **The compactification of a geometrically irreducible cover is geometrically irreducible**:
`V` is a dense open of `V̄`. -/
theorem geometricallyIrreducible_q (h : GeometricallyIrreducible (C.j ≫ C.q)) :
    GeometricallyIrreducible C.q :=
  geometricallyIrreducible_of_dense_isOpenImmersion C.j C.q C.j.denseRange h

omit [ConnectedSpace ↥V] in
/-- `V` is geometrically irreducible over `k` through `V̄` as soon as it is through `U`. -/
theorem geometricallyIrreducible_j_comp_q {pU : U ⟶ Spec (.of k)} (hjU : jU ≫ pUb = pU)
    (h : GeometricallyIrreducible (f ≫ pU)) : GeometricallyIrreducible (C.j ≫ C.q) := by
  have e : C.j ≫ C.q = f ≫ pU := by rw [← C.hq, reassoc_of% C.w, hjU]
  rw [e]
  exact h

/-- **`V̄_K` is a curve over `K`** for every extension `K` of `k`, if `V` is geometrically
irreducible over `k`. -/
theorem isCurve_fieldBaseChange (K : Type u) [Field K] [Algebra k K]
    (h : GeometricallyIrreducible (C.j ≫ C.q)) :
    IsCurve K (pullback.snd (Over.mk C.q).hom (Stacks.Frobenius.specAlgebraMap k K)) :=
  have := C.geometricallyIrreducible_q h
  isCurve_pullback_snd k K C.q

omit [ConnectedSpace ↥V] in
/-- `V̄_K` is smooth over `K`. -/
theorem smooth_fieldBaseChange (K : Type u) [Field K] [Algebra k K] :
    Smooth (pullback.snd (Over.mk C.q).hom (Stacks.Frobenius.specAlgebraMap k K)) :=
  inferInstanceAs (Smooth (pullback.snd C.q _))

omit [ConnectedSpace ↥V] in
/-- `V̄_K` is proper over `K`. -/
theorem isProper_fieldBaseChange (K : Type u) [Field K] [Algebra k K] :
    IsProper (pullback.snd (Over.mk C.q).hom (Stacks.Frobenius.specAlgebraMap k K)) :=
  inferInstanceAs (IsProper (pullback.snd C.q _))

end CoverCompactification

end AlgebraicGeometry
