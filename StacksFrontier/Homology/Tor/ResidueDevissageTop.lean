module

public import StacksFrontier.Homology.Tor.ExtremalDegreesTop
public import StacksFrontier.Homology.Tor.ResidueDevissage

/-!
# The dévissage at the top alone, for an object bounded above only

`StacksFrontier.Homology.Tor.ResidueDevissage` runs the extremal-degree theorem at an object `T`
whose cohomology is finite and killed by a maximal ideal, and asks `T` to be bounded on **both**
sides.  This file runs the same dévissage against the one-sided theorem
`StacksDraft.ExtremalDegrees.extremalDegrees_top` instead, so that `T` need only be bounded
above — at the cost of the way-out right exactness of `F`, which for the derived tensor products
of `D(A)` is `CochainComplex.DerivedTensor.wayOut_tensor` and so costs nothing.

## What is one-sided and what is not

The dévissage itself is already one-sided: of its four consequences only two are used here, the
*upper* window bound `StacksDraft.ResidueDevissage.isLE_map_single_of_isTorsionBySet` and the
nonvanishing at the top degree, and neither mentions a lower bound.  What was two-sided is the
extremal-degree theorem they feed, and that is what
`StacksFrontier.Homology.Tor.ExtremalDegreesTop` replaces.

The conclusion is correspondingly one-sided: `d = 0` alone, where the two-sided
`StacksDraft.ResidueDevissage.eq_zero_of_iso_of_isTorsionBySet` gives `c = 0 ∧ d = 0`.  So this
says that `F(κ[0])` has no cohomology **above** degree zero and does not vanish there.  Putting
the bottom of its window at zero as well is not a degree count and is not here; see the module
documentation of `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessResidueWindowTop`.

## Main results

* `StacksDraft.ResidueDevissage.extremalDegrees_top_of_isTorsionBySet` — **the top extremal
  degree adds**, for a `T` bounded above only: with `F` way-out right exact with slack `p`,
  `F(κ[0])` in `D^{≤ d}` with nonvanishing `d`-th cohomology and `H^b(T) ≠ 0`, the object `F(T)`
  lies in `D^{≤ b + d}` and its `(b + d)`-th cohomology is nonzero.
* `StacksDraft.ResidueDevissage.eq_zero_of_isLE_of_iso_of_isTorsionBySet` — **read back off a
  fixed object**: if moreover `F(T) ≅ T`, then `d = 0`.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.ResidueDevissage

universe u w w'

variable {A : Type u} [CommRing A]
  {D : Type w} [Category.{w'} D] [Abelian D]

/-- **The extremal degree at the top adds, for an object bounded above only whose cohomology is
killed by a maximal ideal.**

Let `F : D(A) → D(D)` be exact and way-out right exact with slack `p` — it carries `D^{≤ n}` into
`D^{≤ n + p}` for every `n` — let `T` lie in `D^{≤ b}` with every cohomology module finite and
killed by the maximal ideal `m` and with `H^b(T) ≠ 0`, and let `F(κ[0])` lie in `D^{≤ d}` with
nonvanishing `d`-th cohomology, for the residue field `κ = A / m`.  Then `F(T)` lies in
`D^{≤ b + d}` and its cohomology in degree `b + d` is nonzero — so `b + d` is its top
nonvanishing degree.

**`T` is not assumed bounded below.**  This is
`StacksDraft.ExtremalDegrees.extremalDegrees_top` with its two hypotheses on the behaviour of `F`
at the single complexes of the cohomology modules of `T` discharged from its behaviour at the
residue field alone — the window one by the dévissage, the nonvanishing one by the retraction,
exactly as in the two-sided
`StacksDraft.ResidueDevissage.extremalDegrees_of_isTorsionBySet`, whose other two hypotheses are
the ones the one-sided theorem does without. -/
theorem extremalDegrees_top_of_isTorsionBySet
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (m : Ideal A) [m.IsMaximal]
    (T : DerivedCategory (ModuleCat.{u} A)) (b d p : ℤ) (hb : T.IsLE b)
    (hway : ∀ (Y : DerivedCategory (ModuleCat.{u} A)) (n : ℤ), Y.IsLE n →
      (F.obj Y).IsLE (n + p))
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hLE : (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ m)))).IsLE d)
    (hd : ¬ IsZero ((homologyFunctor D d).obj
      (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ m))))))
    (htop : ¬ IsZero ((homologyFunctor (ModuleCat.{u} A) b).obj T)) :
    (F.obj T).IsLE (b + d) ∧ ¬ IsZero ((homologyFunctor D (b + d)).obj (F.obj T)) := by
  refine ExtremalDegrees.extremalDegrees_top F T b d p hb hway (fun i => ?_) ?_
  · have := hfin i
    exact isLE_map_single_of_isTorsionBySet F m d hLE _ (hkill i)
  · exact not_isZero_homology_map_single_of_isTorsionBySet F m _ (hkill b) htop d hd

/-- **The top of the residue-field window of an exact, way-out right exact endofunctor that
fixes `T` is degree zero.**

Let `T` lie in `D^{≤ b}` with all of its cohomology finite and killed by the maximal ideal `m`
and with `H^b(T) ≠ 0`, let `F` be exact and way-out right exact with slack `p`, let `F(T) ≅ T`,
and let `F(κ[0])` lie in `D^{≤ d}` with nonvanishing `d`-th cohomology.  Then `d = 0`: `F`
carries the residue field to an object with no cohomology above degree zero, nonzero there.

**`T` is not assumed bounded below**, which is the whole content of the statement; the two-sided
`StacksDraft.ResidueDevissage.eq_zero_of_iso_of_isTorsionBySet` concludes `c = 0` as well and
cannot do without it.  The reader is
`StacksDraft.ExtremalDegrees.eq_zero_of_isLE_of_iso`: `b` is the top nonvanishing degree of `T`
and `b + d` is the top nonvanishing degree of `F(T)`, and the two objects are isomorphic. -/
theorem eq_zero_of_isLE_of_iso_of_isTorsionBySet
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    [F.CommShift ℤ] [F.IsTriangulated] (m : Ideal A) [m.IsMaximal]
    (T : DerivedCategory (ModuleCat.{u} A)) (b d p : ℤ) (hb : T.IsLE b)
    (hway : ∀ (Y : DerivedCategory (ModuleCat.{u} A)) (n : ℤ), Y.IsLE n →
      (F.obj Y).IsLE (n + p))
    (hkill : ∀ i : ℤ, Module.IsTorsionBySet A
      ((homologyFunctor (ModuleCat.{u} A) i).obj T) (m : Set A))
    (hfin : ∀ i : ℤ, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj T))
    (hLE : (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ m)))).IsLE d)
    (hd : ¬ IsZero ((homologyFunctor (ModuleCat.{u} A) d).obj
      (F.obj ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ m))))))
    (htop : ¬ IsZero ((homologyFunctor (ModuleCat.{u} A) b).obj T))
    (e : F.obj T ≅ T) :
    d = 0 := by
  obtain ⟨h₁, h₂⟩ := extremalDegrees_top_of_isTorsionBySet F m T b d p hb hway hkill hfin
    hLE hd htop
  exact ExtremalDegrees.eq_zero_of_isLE_of_iso T (F.obj T) b d hb htop e h₁ h₂

end StacksDraft.ResidueDevissage

end
