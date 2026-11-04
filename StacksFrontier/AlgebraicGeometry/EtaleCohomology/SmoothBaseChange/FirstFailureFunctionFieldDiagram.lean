module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstFailureFunctionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SeparablyClosedExtension

/-!
# A first failure of étale base change, over the function field of the base

Let `f : X ⟶ S` be a morphism of schemes and `n` an integer invertible on `S`, as in the
condition `BC(f, n, q₀)` of [Stacks, Tag 0F02]. Suppose `BC(f, n, q)` holds while
`BC(f, n, q + 1)` fails. [Stacks, Tag 0F1D] produces a diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |
S  ←--  S'  ←---  Spec K(S')
```

with both squares cartesian, `S'` affine, integral and normal with algebraically closed function
field `K(S')`, the bottom right arrow the canonical morphism from the spectrum of the function
field, and a divisor `d` of `n` with `R^{q+1} h_*(ℤ/dℤ)` nonzero.

The source's proof starts from the diagram of [Stacks, Tag 0F08], in which the bottom right
corner is `Spec K` for an algebraically closed extension `K` of `K(S')`, and descends from `K` to
`K(S')`. Writing `Y₀ = X' ×_{S'} Spec K(S')` and `π : Y ⟶ Y₀` for the induced morphism, the square

```
Y₀  ←-π-  Y
|         |
Spec K(S') ←-- Spec K
```

is cartesian, so [Stacks, Tag 0F0B] (2) (this is where `n` invertible on `S` is used) says the
derived unit `ℤ/dℤ ⟶ Rπ_* π⁻¹(ℤ/dℤ)` on `Y₀` is invertible, and the relative Leray
identification `Rh_* = Rh₀_* ∘ Rπ_*` gives `R^{q+1} h_*(ℤ/dℤ) ≅ R^{q+1} h₀_*(ℤ/dℤ)`.

## Main definitions

* `Stacks.EtaleCohomology.FirstFailureFunctionField.FunctionFieldFailure` — the conclusion of
  [Stacks, Tag 0F1D].

## Main results

* `Stacks.EtaleCohomology.FirstFailureFunctionField.functionFieldFailure_of_normalFailureDiagram`
  — the conclusion of [Stacks, Tag 0F08] implies that of [Stacks, Tag 0F1D] when `n` is
  invertible on `S`, given the assertion `SmoothLimitBaseChange` of [Stacks, Tag 0F09].
* `Stacks.EtaleCohomology.FirstFailureFunctionField.functionFieldFailure_of_firstFailure` —
  [Stacks, Tag 0F1D] at the source's hypotheses, given [Stacks, Tag 0F08] and
  `SmoothLimitBaseChange`.

The ingredients of the proof are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstFailureFunctionField`.

## Implementation notes

Degrees are indexed as in `BaseChangeHigher/FirstFailureDiagram.lean`: the source's `q ≥ 1` with
`BC(f, n, q - 1)` true and `BC(f, n, q)` false reads as degree `q + 1` with `BC(f, n, q)` true and
`BC(f, n, q + 1)` false. Normality of the integral affine `S'` is normality of its ring of global
sections, as in `FirstFailureDiagram.NormalFailureDiagram`. The sheaf `ℤ/dℤ` in the conclusion is
the constant sheaf on `Y` itself.

`n` invertible on `S` means that `n` is a unit in `Γ(S, 𝒪_S)`. It makes `d` invertible in
`K(S')`, which is the torsion hypothesis [Stacks, Tag 0F0B] needs.

[Stacks, Tag 0F0B] (2) is `Stacks.EtaleCohomology.isIso_derivedUnit_app_of_isSepClosed`, stated
for an arbitrary scheme over a separably closed field, without quasi-compactness or
quasi-separatedness: the scheme `Y₀` it is applied to here is not quasi-compact over `K(S')` in
general, and the source's proof of (2) is local. That theorem takes the assertion
`SmoothLimitBaseChange` of [Stacks, Tag 0F09] as an argument, and so do the two results below that
use it.

Two inputs of the proof are not proved in this repository, and both declarations that use them
are unregistered. `hFirstFailure` has the type of [Stacks, Tag 0F08] exactly (BC(f, n, q) and not
BC(f, n, q + 1) give `NormalFailureDiagram f n (q + 1)`). `hSmoothLimit` is
`SmoothLimitBaseChange`, which the source derives from the smooth base change theorem
[Stacks, Tag 0EYU].

## References

* [Stacks Project, Tag 0F1D](https://stacks.math.columbia.edu/tag/0F1D)
* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
* [Stacks Project, Tag 0F0B](https://stacks.math.columbia.edu/tag/0F0B)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.FirstFailureFunctionField

attribute [local instance] HasDerivedCategory.standard

open FirstFailureDiagram

/-- **The conclusion of [Stacks, Tag 0F1D]**, in degree `r`. There are cartesian squares

```
X  ←-p-  X'  ←-h-  Y
|f       |f'       |e
S  ←-s-  S'  ←---  Spec K(S')
```

in which `S'` is affine, integral and normal with algebraically closed function field `K(S')`,
the bottom right arrow is the canonical morphism `Spec K(S') ⟶ S'` (the morphism from the
spectrum of the stalk at the generic point), and an integer `d ∣ n` with `R^r h_*(ℤ/dℤ)` nonzero,
`ℤ/dℤ` being the constant sheaf on `Y`. -/
public def FunctionFieldFailure {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (r : ℕ) : Prop :=
  ∃ (S' X' Y : Scheme.{u}) (_ : IsAffine S') (_ : IsIntegral S')
    (_ : IsNormalDomain Γ(S', ⊤)) (_ : IsAlgClosed S'.functionField)
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (_hp : IsPullback p f' f s)
    (h : Y ⟶ X') (e : Y ⟶ Spec S'.functionField)
    (_sq : IsPullback h e f' (S'.fromSpecStalk (genericPoint S')))
    (d : ℕ) (_ : (d : ℤ) ∣ n),
    ¬ IsZero (((smallEtalePushforwardAb h).rightDerived r).obj (constantZMod Y d))

/-- **The diagram of [Stacks, Tag 0F08] gives the diagram of [Stacks, Tag 0F1D].** Let `n` be
invertible on `S`, and take a diagram over an algebraically closed `K` dominating `S'` with
`R^r h_*(ℤ/dℤ)` nonzero. Replacing `Spec K` by `Spec K(S')` keeps `R^r h_*(ℤ/dℤ)` nonzero. -/
public theorem functionFieldFailure_of_normalFailureDiagram {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (r : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    (hSmoothLimit : SmoothLimitBaseChange.{u}) (hfail : NormalFailureDiagram f n r) :
    FunctionFieldFailure f n r := by
  obtain ⟨S', X', Y, haff, hint, hnorm, hfun, s, p, f', hp, K, hK, hKcl, g, hdom, h, e, sq,
    d, hd, hNZ⟩ := hfail
  obtain ⟨φ, hφ⟩ := exists_specMap_comp_fromSpecStalk_genericPoint g
  let g₀ := S'.fromSpecStalk (genericPoint S')
  let h₀ := pullback.fst f' g₀
  let e₀ := pullback.snd f' g₀
  refine ⟨S', X', pullback f' g₀, haff, hint, hnorm, hfun, s, p, f', hp, h₀, e₀,
    IsPullback.of_hasPullback f' g₀, d, hd, ?_⟩
  let π : Y ⟶ pullback f' g₀ := pullback.lift h (e ≫ Spec.map φ) (by
    rw [Category.assoc, hφ]
    exact sq.w)
  have hπfst : π ≫ h₀ = h := pullback.lift_fst _ _ _
  have hπsnd : π ≫ e₀ = e ≫ Spec.map φ := pullback.lift_snd _ _ _
  have hField : IsPullback π e e₀ (Spec.map φ) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback f' g₀) ?_ hπsnd
    rwa [hπfst, show Spec.map φ ≫ g₀ = g from hφ]
  have : Nonempty (⊤ : S'.Opens) := ⟨⟨genericPoint S', trivial⟩⟩
  have hnk : IsUnit (n : S'.functionField) := by
    simpa using IsUnit.map (s.appTop ≫ S'.germToFunctionField ⊤).hom hn
  have hdk : IsUnit (d : S'.functionField) := by
    have hdZ : ((d : ℤ) : S'.functionField) ∣ (n : S'.functionField) :=
      map_dvd (Int.castRingHom S'.functionField) hd
    simpa using isUnit_of_dvd_unit hdZ hnk
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hdk
  have hdΓ : IsUnit (d : Γ(Spec (.of S'.functionField), ⊤)) := by
    simpa using IsUnit.map (Scheme.ΓSpecIso (.of S'.functionField)).inv.hom hdk
  let : Algebra S'.functionField K := φ.hom.toAlgebra
  have hUnit := isIso_derivedUnit_app_of_isSepClosed hSmoothLimit
    (k := S'.functionField) (K := K) e₀ π e hField
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (constantZMod (pullback f' g₀) d))
    (hasTorsionOrdersInvertibleOn_homology_single
      (hasTorsionOrdersInvertibleOn_constantZMod hdpos hdΓ))
  exact fun hz => hNZ <|
    (hz.of_iso (rightDerivedConstantZModIsoOfIsIsoUnit π h₀ h hπfst d hUnit r)).of_iso
      (((smallEtalePushforwardAb h).rightDerived r).mapIso
        ((smallEtalePullbackAbConstantIso e).app _))

/-- **[Stacks, Tag 0F1D] from a first failure of base change**, with the normalized diagram
of [Stacks, Tag 0F08] and the assertion `SmoothLimitBaseChange` of [Stacks, Tag 0F09] supplied
as arguments.

With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], `n` invertible on `S`, `BC(f, n, q)` true
and `BC(f, n, q + 1)` false, there are cartesian squares `X' = X ×_S S'` and
`Y = X' ×_{S'} Spec K(S')`, with `S'` affine, integral and normal with algebraically closed
function field `K(S')`, and a divisor `d` of `n` with `R^{q+1} h_*(ℤ/dℤ)` nonzero. -/
public theorem functionFieldFailure_of_firstFailure {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ)
    (q : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (hprev : BaseChangeHolds f n (q : ℤ))
    (hfail : ¬ BaseChangeHolds f n ((q : ℤ) + 1))
    (hFirstFailure : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ),
      BaseChangeHolds f n (q : ℤ) → ¬ BaseChangeHolds f n ((q : ℤ) + 1) →
        NormalFailureDiagram f n (q + 1))
    (hSmoothLimit : SmoothLimitBaseChange.{u}) :
    FunctionFieldFailure f n (q + 1) :=
  functionFieldFailure_of_normalFailureDiagram f n (q + 1) hn hSmoothLimit
    (hFirstFailure f n q hprev hfail)

end Stacks.EtaleCohomology.FirstFailureFunctionField

end
