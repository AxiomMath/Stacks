module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechCompatibility.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.CechLevelPullback

/-!
# Bridges for the cohomological descent spectral sequence of a finite surjection

Tag 09Z2 computes the étale cohomology of a sheaf on `Y` from the cohomology of its inverse
image on the levels of the Čech nerve of a finite surjection `f : X ⟶ Y`. Two identifications are
needed before the hyper-`Ext` spectral sequence of
`StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence` can be read as a statement
about étale cohomology, and this file supplies them. The geometry of the Čech levels themselves —
that each is finite and surjective over the base — is
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FiniteDescent/CechLevelPullback.lean`.

The first is bookkeeping about gradings: étale cohomology in this repository is
`CategoryTheory.Sheaf.H`, which is Mathlib's `ℕ`-graded `CategoryTheory.Abelian.Ext` out of the
constant sheaf `ℤ`, whereas the spectral sequence is stated with the `ℤ`-graded
`CategoryTheory.Abelian.zExt`, a `ShiftedHom` group in the derived category. The two agree in the
nonnegative degrees, by Mathlib's `CategoryTheory.Abelian.Ext.homAddEquiv`.

The second is the geometric input at the first page: for a finite morphism the direct image is
exact and preserves injectives, so `H^q(W, g⁻¹F) = H^q(Y, g_* g⁻¹F)`. This is the content of
Tag 04C2 as packaged by `Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv`, which asks
only for an integral morphism; a finite morphism is integral.

## Main results

* `Stacks.EtaleCohomology.sheafHAddEquivZExt` — **étale cohomology is the `ℤ`-graded
  `zExt` the spectral-sequence machinery is stated with.**
* `Stacks.EtaleCohomology.sheafHSmallEtalePullbackPushforwardAddEquiv` — **for a finite
  `g : W ⟶ Y`, `H^q(W, g⁻¹F) ≅ H^q(Y, g_* g⁻¹F)`.**

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/EtaleCohomology/ClosedPointDirectSumCohomology.lean`, the
Grothendieck abelian structure of abelian sheaves on the small étale site relative to `u + 1` is
installed as a *local* instance, so that `CategoryTheory.Sheaf.H` elaborates with no `HasExt`
hypothesis; Mathlib keeps `HasExt` instances scarce, so it is deliberately not exported.
Coefficients are `AddCommGrpCat.{u + 1}` for `X : Scheme.{u}` and the `Ext` universe is `u + 1`,
the convention of the whole `Stacks.EtaleCohomology` namespace. The derived-category universe
appearing in `zExt` is left as a free instance argument, because the spectral sequence is stated
for an arbitrary `HasDerivedCategory` instance and callers install their own.

The Čech levels are the wide pullbacks of Mathlib's `CategoryTheory.Arrow.cechNerve`, so the
inductive step is proved by exhibiting a `CategoryTheory.IsPullback` square by hand from the
`WidePullback` universal property; the index juggling is `Fin.lastCases`, the last face map of
the simplex category being `Fin.succAbove (Fin.last _) = Fin.castSucc`. The base case needs the
zeroth level to *be* `X`: the single projection out of a one-fold fibre product is an
isomorphism.

## References

* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 0AVI](https://stacks.math.columbia.edu/tag/0AVI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology

-- Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
-- `AddCommGrpCat.{u + 1}` form a Grothendieck abelian category relative to `u + 1`, which is
-- what makes `HasExt.{u + 1}` available, and so `CategoryTheory.Sheaf.H` elaborate, without any
-- hypothesis. It is kept local, as in the file that proves it.
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtaleTopology

/-- **Étale cohomology is the `ℤ`-graded `Ext`-group the hyper-`Ext` spectral sequence is stated
with.** For `F` an abelian sheaf on the small étale site of `X` and `q : ℕ`, the group
`CategoryTheory.Sheaf.H F q` — Mathlib's `ℕ`-graded `Ext` out of the constant sheaf `ℤ` — is the
degree-`q` part of the `ℤ`-graded `CategoryTheory.Abelian.zExt` out of the same constant sheaf,
which is the grading of the first page of
`StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence`.

This is Mathlib's `CategoryTheory.Abelian.Ext.homAddEquiv` at the constant sheaf `ℤ`; it is
recorded here because it is what turns the first page of that spectral sequence into étale
cohomology groups. -/
public def sheafHAddEquivZExt {X : Scheme.{u}}
    [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology X) Ab.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (q : ℕ) :
    Sheaf.H.{u + 1, u + 1} F q ≃+
      Abelian.zExt ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F (q : ℤ) :=
  Abelian.Ext.homAddEquiv

/-- **Direct image along a finite morphism does not change the global étale cohomology of an
inverse image.** For `g : W ⟶ Y` finite and `F` an abelian sheaf on the small étale site of `Y`,
the degree-`q` cohomology of `g⁻¹F` over `W` and of `g_* g⁻¹F` over `Y` are the same group.

This is `Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv`, which holds for an
integral morphism, applied to `g⁻¹F`; a finite morphism is integral. It is the first-page
identification tag 09Z2 needs, the levels of the Čech nerve of a finite surjection being finite
over the base. -/
public def sheafHSmallEtalePullbackPushforwardAddEquiv {W Y : Scheme.{u}} (g : W ⟶ Y)
    [IsFinite g] (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (q : ℕ) :
    Sheaf.H.{u + 1, u + 1} ((smallEtalePullbackAb g).obj F) q ≃+
      Sheaf.H.{u + 1, u + 1}
        ((smallEtalePushforwardAb g).obj ((smallEtalePullbackAb g).obj F)) q :=
  sheafHSmallEtalePushforwardAddEquiv g ((smallEtalePullbackAb g).obj F) q

end Stacks.EtaleCohomology

end
