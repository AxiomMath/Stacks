module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ZeroSchemeCartesianSquare
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback

/-!
# Stacks 0B71: the Gysin map of an invertible module against flat pullback

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `X'` be
schemes locally of finite type over `S`, let `f : X' ⟶ X` be flat of relative dimension `r`, let
`L` be an invertible module on `X` with global section `s`, and let `i : D = Z(s) ⟶ X` be the zero
scheme of `s`. Writing `L' = f^*L`, `s' = f^*s`, `D' = Z(s')` and `i' : D' ⟶ X'`, Remark 0B6Y
produces the square

  `D' --i'--> X'`
  `|g          |f`
  `D  --i-->  X`

and Stacks 0B71 is the identity

  `(i')^* f^* α = g^* i^* α`  in  `CH_{k+r}(D')`,  for every `α ∈ Z_{k+1}(X)`.

`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback` proves that identity with five inputs
carried as parameters: the two first-Chern component rules of the Gysin maps on `X` and on `X'`,
the invertibility of `f^*L`, the morphism `g` together with its flatness and relative dimension,
the vanishing of Stacks 02S1 along `g`, and the compatibility of the two rules on integral
components. This file removes the first three of those: the component rules are supplied by the
first Chern class of `L` and of `f^*L`, so both Gysin maps become
`Stacks.Chow.gysinHomomorphismOfInvertible`, the declaration carrying the Stacks 02T8 attribute;
the invertibility of `f^*L` is the instance `Stacks.Divisors.pullback_isInvertible` (Stacks 0B8L);
and `g` is the canonical `Stacks.Chow.zeroSchemePullbackHom`, whose flatness and relative dimension
come from the cartesian square of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ZeroSchemeCartesianSquare`.

It then proves the identity outright — not assuming any case of it — for the fundamental cycle of
a closed subscheme meeting the zero scheme properly, which is the first case of the source's proof.

## Main results

* `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_cycleAssociatedToClosedSubscheme` —
  **Stacks 0B71** on the fundamental cycle of a closed subscheme meeting the zero scheme properly.
* `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_comap`,
  `Stacks.Chow.flatPullback_zeroSchemePullbackHom_cycleAssociatedToClosedSubscheme` — Stacks 02RB
  in the `Scheme.IdealSheafData.comap` presentation, along `f` and along `g`.
* `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback` — Stacks 0B71 for an arbitrary cycle,
  with the component rules, the invertibility of `f^*L` and the morphism `g` discharged, and the
  identity on integral components carried.

## Implementation notes

### The case of a closed subscheme, and why it is the proved one

The source reduces to `α = [W]` for `W ⊆ X` an integral closed subscheme and splits into the cases
`W ⊄ D` and `W ⊆ D`. In the first case it identifies `W' ∩ D' = g^{-1}(W ∩ D)` as closed
subschemes of `D'` and concludes by Stacks 02RE.
`Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_cycleAssociatedToClosedSubscheme` is that
case, for an arbitrary closed subscheme rather than only an integral one, and it is assembled from
four results of the library:

* **Stacks 02RB**, through `Stacks.Chow.closedSubschemeCycleCoeff_comap`:
  `f^*[Z]_{k+1} = [f^{-1}Z]_{k+1+r}`;
* **Stacks 02TB (1)**,
  `Stacks.Chow.gysinHomomorphismOfInvertible_cycleAssociatedToClosedSubscheme`, twice:
  `i^*[Z]_{k+1} = [Z ∩ D]_k` on `X` and `(i')^*[f^{-1}Z]_{k+1+r} = [f^{-1}Z ∩ D']_{k+r}` on `X'`;
* **Stacks 02RB** again, along `g`: `g^*[Z ∩ D]_k = [g^{-1}(Z ∩ D)]_{k+r}`;
* the cartesian square, through `Stacks.Chow.comap_zeroSchemePullbackHom`, which identifies
  `g^{-1}(Z ∩ D)` with `f^{-1}Z ∩ D'`.

### What is carried, and what each carried hypothesis is

* `hfac`, the vanishing of **Stacks 02S1** along `g`. It is what makes the map
  `g^* : CH_k(D) ⟶ CH_{k+r}(D')` of Stacks 0FVK exist at all, so the right hand side of the tag
  cannot be written down without it. It is a theorem, proved unconditionally for an arbitrary flat
  morphism of relative dimension `r` as
  `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` in
  `StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence`. It is carried as a
  `Prop` here to keep these statements parallel to those of
  `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback`, which cannot reach that proof, and it
  is threaded the same way in `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`. It is
  substituted in `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackDischarge`.
* `hZ`, `hDZ`, `hZ'`, `hDZ'`, `hZD` in the closed-subscheme statement: the delta-dimension bounds
  and the conditions that the two intersections `Z ∩ D` and `f^{-1}Z ∩ D'` are effective Cartier
  divisors. These are exactly the hypotheses of Stacks 02TB (1) and of Stacks 02RB as this
  repository states them, taken at the two schemes of the square; the source gets them for an
  integral `W ⊄ D` from the integrality of `W` and the flatness of `f`. `hZ'` is **Stacks 02RE
  (1)** in the `Scheme.IdealSheafData.comap` presentation: the `pullback.fst` presentation of the
  same bound is `Stacks.Chow.schemeDeltaDimension_pullback_le`, and translating it needs the
  invariance of the delta-dimension under an isomorphism of possibly reducible schemes, which this
  repository has only for irreducible ones (`Stacks.Chow.schemeDeltaDimension_of_iso`).
* `hcomp` in the arbitrary-cycle statement, the identity of the tag on integral components. The
  source proves it by Stacks 02RE when the component is not contained in the zero scheme and by
  Stacks 02SS when it is. Stacks 02SS is available in this repository only under the component
  hypothesis `Stacks.Chow.FirstChernCapRationallyCompatibleWithFlatPullback` of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullbackInvertible`, and the contained case
  additionally needs the commutation of flat pullback with proper pushforward across the square
  `f^{-1}W ⟶ W`, `D' ⟶ D`, which this repository has only when both legs are isomorphisms
  (`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange`). So
  `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback` carries that case and **does not** carry
  the `@[stacks 0B71]` attribute: it would be the tag's own statement assumed on components. The
  attribute sits only on the case that is proved.

### The degree transport

The flat pullback of a `(k+1)`-cycle has degree `(k + 1) + r`, while the Gysin map in degree
`k + r` consumes a cycle of degree `(k + r) + 1`. These are the same integer and not the same
term, so a transport along `k + 1 + r = k + r + 1` appears in both statements, as it does in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback`. It is discharged by `omega` rather than
carried, and `Stacks.Chow.val_cycleGroup_cast` says it does not change the coefficient function.

## References

* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)

/-! ### Stacks 02RB in the `comap` presentation -/

/-- Stacks 02RB for a general flat morphism `q`: flat pullback of the cycle of a closed subscheme
is the cycle of its scheme-theoretic inverse image. -/
private theorem flatPullback_cycleAssociatedToClosedSubscheme_comap_aux (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (q : X' ⟶ X) [LocallyOfFiniteType q] [Flat q] (hbase : q ≫ sX = sX')
    (r : ℕ) (hq : AlgebraicGeometry.RelativeDimension q r) (I : X.IdealSheafData) (d : ℤ)
    (hI : schemeDeltaDimension C (I.subschemeι ≫ sX) ≤ (d : EInt)) :
    flatPullback C sX' sX q hbase r hq d (cycleAssociatedToClosedSubscheme C sX I.subschemeι d) =
      cycleAssociatedToClosedSubscheme C sX' (I.comap q).subschemeι (d + (r : ℤ)) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x'
  rw [flatPullback_apply]
  show _ = closedSubschemeCycleCoeff C sX' (I.comap q).subschemeι (d + (r : ℤ)) x'
  rw [closedSubschemeCycleCoeff_comap C sX' sX q hbase r hq I d hI x']
  rfl

/-- **Stacks 02RB.** The flat pullback of the fundamental cycle of a closed subscheme of
delta-dimension at most `k + 1`, transported into the degree `(k + r) + 1` that the Gysin map in
degree `k + r` consumes, is the fundamental cycle of the scheme-theoretic inverse image. -/
theorem flatPullback_cycleAssociatedToClosedSubscheme_comap
    (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt)) :
    ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
        flatPullback C (f ≫ p) p f rfl r hf (k + 1)
          (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)) :
      CycleGroup C (f ≫ p) (k + (r : ℤ) + 1)) =
      cycleAssociatedToClosedSubscheme C (f ≫ p) (Z.comap f).subschemeι (k + (r : ℤ) + 1) := by
  rw [flatPullback_cycleAssociatedToClosedSubscheme_comap_aux C (f ≫ p) p f rfl r hf Z (k + 1) hZ]
  suffices ∀ (j : ℤ) (h : k + 1 + (r : ℤ) = j),
      (h ▸ cycleAssociatedToClosedSubscheme C (f ≫ p) (Z.comap f).subschemeι (k + 1 + (r : ℤ)) :
        CycleGroup C (f ≫ p) j) =
      cycleAssociatedToClosedSubscheme C (f ≫ p) (Z.comap f).subschemeι j from this _ _
  rintro _ rfl
  rfl

/-- **Stacks 02RB along the comparison morphism of Remark 0B6Y.** The flat pullback along `g` of
the fundamental cycle of a closed subscheme of `D` of delta-dimension at most `k` is the
fundamental cycle of its scheme-theoretic inverse image in `D'`. -/
theorem flatPullback_zeroSchemePullbackHom_cycleAssociatedToClosedSubscheme
    (I : (Stacks.Divisors.zeroScheme X L s).subscheme.IdealSheafData)
    (hI : schemeDeltaDimension C
      (I.subschemeι ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)) ≤ (k : EInt)) :
    flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
        (relativeDimension_zeroSchemePullbackHom f L s r hf) k
        (cycleAssociatedToClosedSubscheme C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) I.subschemeι k) =
      cycleAssociatedToClosedSubscheme C
        ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        (I.comap (zeroSchemePullbackHom f L s)).subschemeι (k + (r : ℤ)) :=
  flatPullback_cycleAssociatedToClosedSubscheme_comap_aux C _ _ _
    (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
    (relativeDimension_zeroSchemePullbackHom f L s r hf) I k hI

/-! ### Stacks 0B71 -/

/-- **Stacks 0B71 on the fundamental cycle of a closed subscheme meeting the zero scheme
properly.** For a closed subscheme `Z ⊆ X` of delta-dimension at most `k + 1` whose intersection
with `D = Z(s)` is an effective Cartier divisor on `Z`, and whose inverse image `f^{-1}Z` meets
`D' = Z(f^*s)` in the same way,

  `(i')^* f^* [Z]_{k+1} = g^* i^* [Z]_{k+1}`  in  `CH_{k+r}(D')`.

Here `i^*` and `(i')^*` are the Gysin maps `Stacks.Chow.gysinHomomorphismOfInvertible` of
Stacks 02T8 for `(L, s)` and for `(f^*L, f^*s)`, `f^*` is the flat pullback of cycles of
Stacks 02RB, and `g^*` is the flat pullback on Chow groups of Stacks 0FVK along the comparison
morphism `Stacks.Chow.zeroSchemePullbackHom` of Remark 0B6Y, whose flatness and relative dimension
are supplied by the cartesian square and are **not** hypotheses. No first Chern class component
rule is a parameter, and the invertibility of `f^*L` is an instance.

This is the first case of the source's proof, for an arbitrary closed subscheme rather than only
an integral one. Carried: the vanishing of **Stacks 02S1** along `g`, without which the right hand
side does not exist, and the five side conditions of Stacks 02TB (1) and Stacks 02RB at the two
schemes of the square; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackInvertible`. -/
@[stacks 0B71 "closed subscheme meeting the zero scheme properly; 02S1 along g carried"]
theorem gysinHomomorphismOfInvertible_flatPullback_cycleAssociatedToClosedSubscheme
    (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Divisors.zeroScheme X L s).comap Z.subschemeι))
    (hZ' : schemeDeltaDimension C ((Z.comap f).subschemeι ≫ (f ≫ p)) ≤
      ((k + (r : ℤ) + 1 : ℤ) : EInt))
    (hDZ' : Stacks.Divisors.IsEffectiveCartierDivisor
      ((pullbackZeroScheme f L s).comap (Z.comap f).subschemeι))
    (hZD : schemeDeltaDimension C
      ((Z.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι ≫
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)) ≤ (k : EInt))
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
      (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
      (relativeDimension_zeroSchemePullbackHom f L s r hf) k) :
    gysinHomomorphismOfInvertible C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L) (pullbackGlobalSections f L s)
        ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
          flatPullback C (f ≫ p) p f rfl r hf (k + 1)
            (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1))) =
      flatPullbackChow C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
        (relativeDimension_zeroSchemePullbackHom f L s r hf) k hfac
        (gysinHomomorphismOfInvertible C p k L s
          (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1))) := by
  have hL := gysinHomomorphismOfInvertible_cycleAssociatedToClosedSubscheme C (f ≫ p)
    (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
    (Stacks.Divisors.sectionsOfTop ((Scheme.Modules.pullback f).obj L)
      (pullbackGlobalSections f L s)) (Z.comap f)
    (by simpa only [Stacks.Divisors.sectionsOfTop_eval_top] using hZ')
    (by simpa only [Stacks.Divisors.sectionsOfTop_eval_top] using hDZ')
  have hR := gysinHomomorphismOfInvertible_cycleAssociatedToClosedSubscheme C p k L
    (Stacks.Divisors.sectionsOfTop L s) Z
    (by simpa only [Stacks.Divisors.sectionsOfTop_eval_top] using hZ)
    (by simpa only [Stacks.Divisors.sectionsOfTop_eval_top] using hDZ)
  rw [Stacks.Divisors.sectionsOfTop_eval_top ((Scheme.Modules.pullback f).obj L)
    (pullbackGlobalSections f L s)] at hL
  rw [Stacks.Divisors.sectionsOfTop_eval_top L s] at hR
  rw [flatPullback_cycleAssociatedToClosedSubscheme_comap f C p r hf k Z hZ, hL, hR]
  show (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
      ((Z.comap f).comap (pullbackZeroScheme f L s).subschemeι).subschemeι (k + (r : ℤ))) :
      chowGroup C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ))) = _
  rw [← comap_zeroSchemePullbackHom f L s Z,
    ← flatPullback_zeroSchemePullbackHom_cycleAssociatedToClosedSubscheme f L s C p r hf k
      (Z.comap (Stacks.Divisors.zeroScheme X L s).subschemeι) hZD]
  rfl

/-- **Stacks 0B71 for an arbitrary cycle**, at the Gysin map of an invertible module and over the
canonical square of Remark 0B6Y:

  `(i')^* f^* α = g^* i^* α`  in  `CH_{k+r}(D')`,  for every `α ∈ Z_{k+1}(X)`.

This is `Stacks.Chow.gysinHomomorphism_flatPullback` with three of its five inputs discharged: both
Gysin maps are `Stacks.Chow.gysinHomomorphismOfInvertible`, so no first Chern class component rule
is a parameter; the invertibility of `f^*L` (Stacks 0B8L) is an instance; and `g` is the canonical
comparison morphism, its flatness and relative dimension coming from the cartesian square.

Two hypotheses remain: the vanishing of Stacks 02S1 along `g`, and the identity of the tag on
integral components. **No `@[stacks 0B71]` attribute is placed on this declaration**, because the
second of those is the tag's own statement assumed on components; the attribute sits on
`Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_cycleAssociatedToClosedSubscheme`, which
assumes no case of the tag. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackInvertible`. -/
theorem gysinHomomorphismOfInvertible_flatPullback
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
      (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
      (relativeDimension_zeroSchemePullbackHom f L s r hf) k)
    (hcomp : GysinCompatibleWithFlatPullback C p f r k L s
      (firstChernComponentClass C p k L)
      (firstChernComponentClass C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L))
      (zeroSchemePullbackHom f L s) (relativeDimension_zeroSchemePullbackHom f L s r hf)
      (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl))
    (α : CycleGroup C p (k + 1)) :
    gysinHomomorphismOfInvertible C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L) (pullbackGlobalSections f L s)
        ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
          flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) =
      flatPullbackChow C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
        (relativeDimension_zeroSchemePullbackHom f L s r hf) k hfac
        (gysinHomomorphismOfInvertible C p k L s α) :=
  gysinHomomorphism_flatPullback C p f r hf k L s (firstChernComponentClass C p k L)
    (firstChernComponentClass C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L))
    (zeroSchemePullbackHom f L s) (relativeDimension_zeroSchemePullbackHom f L s r hf)
    (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) hfac hcomp (by omega) α

end Stacks.Chow

end
