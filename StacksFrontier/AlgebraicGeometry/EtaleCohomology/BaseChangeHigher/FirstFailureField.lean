module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FieldPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover

/-!
# A failure of étale base change is already visible over a field

Let `f : X ⟶ S` be a morphism of schemes and `n` an integer, as in the condition `BC(f, n, q₀)`
of [Stacks, Tag 0F02]. If `BC(f, n, q)` holds while `BC(f, n, q + 1)` fails, then the failure can
be realized over the spectrum of a field: there are a commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  Spec K
```

with both squares cartesian and `K` a field, and an abelian sheaf `F` on the small étale site of
`Spec K` annihilated by `n`, for which `(f')⁻¹ R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹ F` is not an
isomorphism. This is [Stacks, Tag 0F07].

The route is the source's. A counterexample over a general base exists because `BC(f, n, q + 1)`
fails, and sits in degree exactly `q + 1` because `BC(f, n, q)` holds. Its base is shrunk to an
affine open of `S'`, which makes the base of the sheaf quasi-compact and quasi-separated, and the
dévissage `AlgebraicGeometry.exists_field_point` of [Stacks, Tag 0F06] is applied to the property

> `BaseChangeFailsOver`: the base change map in degree `q + 1` still fails after pulling the
> sheaf back along `T' ⟶ T`,

which produces the field-valued point at which the failure persists.

## Main definitions

* `Stacks.EtaleCohomology.BaseChangeFailsOver` — the property of a scheme over the base of the
  sheaf that the base change map in a given degree fails there, for the pullback of the sheaf.

## Main results

* `Stacks.EtaleCohomology.exists_not_isIso_higherBaseChangeMapAb_succ` — the opening of the
  source's proof: a first failure of base change produces a counterexample in degree exactly
  `q + 1`.

## Implementation notes

The index convention is the one the rest of this development uses: the source's `q ≥ 1` with
`BC(f, n, q - 1)` true and `BC(f, n, q)` false is read as degree `q + 1` with `BC(f, n, q)` true
and `BC(f, n, q + 1)` false, so that no subtraction on `ℤ` has to be moved across the
`Stacks.EtaleCohomology.BaseChangeHolds` argument.

The source's property `P(T')` says that a *fixed* class `ξ` in a stalk of `R^{q+1}h_*e⁻¹F`
escapes the image of the base change map after pullback to `T'`. It is replaced here by the
existential statement that the base change map over `T'` fails to be an isomorphism, which needs
neither geometric points nor stalks; the two differ exactly in that the existential form does not
record that the failures at the various `T'` are witnessed by one compatible class, and that is
why the limit hypothesis is granted below rather than deduced from a colimit formula.

## The four inputs that are carried

Each of the four hypotheses is quantified over arbitrary base extensions of `f`, arbitrary
quasi-compact quasi-separated bases for the sheaf, arbitrary `n`-torsion sheaves on them and (for
three of the four) arbitrary degrees, so that none of them is the conclusion of
[Stacks, Tag 0F07] in disguise.

* `hShrink` is the source's sentence *"Of course we may and do replace `S'` by an affine open of
  `S'`"*: Zariski locality on the base of the degree-`r` base change map. Invertibility of a
  morphism of abelian sheaves on a small étale site is étale-local
  (`Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb` and the covering criterion
  in `EtaleLocality`), but identifying the restriction of the base change map to the base
  extension along an affine `V ⟶ S'` with the base change map of the restricted diagram needs
  `(R^r h_* G)|_{X_V} ≅ R^r h_{V,*}(G|_{Y_V})`, the *derived* form of the restriction
  compatibility; `BaseChangeHigher/EtaleLocality.lean` provides it only for the underived direct
  image, and the one derived form the development has,
  `Stacks.Cohomology.Localization.derivedPushforwardOverFunctorIso` ([Stacks, Tag 0D6G]), is for
  sheaves of modules on a ringed site in the unbounded derived category, not for abelian sheaves
  on small étale sites in the degreewise bounded below convention `Functor.rightDerived r` that
  the base change map of [Stacks, Tag 0F02] is built from.
* `h04DZ` is hypothesis (1) of the dévissage, invariance of the property under a thickening of
  the base, and is [Stacks, Tag 04DZ], topological invariance of the small étale site under a
  thickening. `EtaleCohomology/TopologicalInvariance/Basic.lean` records
  `isCoverDense_smallEtaleBaseChange_iff` as the input the development does not have, and
  `ProperBaseChange/Proper.lean` records that essential surjectivity, the remaining and hard
  content of Tag 04DZ, is never proved.
* `h09YQ` is hypothesis (2), passage to a cofiltered limit of quasi-compact quasi-separated
  bases with affine transition morphisms, and is [Stacks, Tag 09YQ] in its relative form. The
  development has only the affine case, `Colimits/AffineEtaleCohomologyColimit.lean`, tagged
  `09YQ "the affine case"`, and already carries the general statement as a named hypothesis
  `h09YQ` in `CohomologicalDimensionLimits.lean`.
* `hLeray` is hypothesis (3), the closed subscheme / quasi-compact open complement step, whose
  proof in the source runs through the relative Leray spectral sequence of [Stacks, Tag 0734]
  for abelian sheaves on small étale sites. The development carries that spectral sequence only
  hypothetically, in `BaseChangeHigher/IntegralBase.lean` (tagged `0F05 "with 0EYP, relative
  Leray and base change pasting as explicit hypotheses"`) and in
  `BaseChangeHigher/IntegralSurjectiveCover.lean`; `Stacks.Cohomology.Leray` has it for sheaves
  of modules on a ringed site only. Its degree is fixed at `q + 1`, because the source's proof of
  hypothesis (3) uses `BC(f, n, q)` in the degree below.

## References

* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 0F06](https://stacks.math.columbia.edu/tag/0F06)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Thickenings

universe u

namespace Stacks.EtaleCohomology

/-- **The property the dévissage of [Stacks, Tag 0F06] is applied to.** For a base extension
`fV : X_V ⟶ V` of a morphism of schemes, a base `g₀ : T₀ ⟶ V` for the sheaf, a morphism
`t₀ : T₀ ⟶ T` and an abelian sheaf `F` on the small étale site of `T`, a scheme `T'` over `T₀`
has this property in degree `r` when the base change map
`(fV)⁻¹ R^r g'_* F' ⟶ R^r h'_* (e')⁻¹ F'` of the diagram obtained by base change to `T'`, at the
pullback `F'` of `F` along `T' ⟶ T₀ ⟶ T`, is not an isomorphism. -/
public def BaseChangeFailsOver {V X_V T₀ T : Scheme.{u}} (fV : X_V ⟶ V) (g₀ : T₀ ⟶ V)
    (t₀ : T₀ ⟶ T) (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (r : ℕ) (T' : Scheme.{u})
    (π : T' ⟶ T₀) : Prop :=
  ∃ (Y' : Scheme.{u}) (h' : Y' ⟶ X_V) (e' : Y' ⟶ T') (g' : T' ⟶ V) (_hg : g' = π ≫ g₀)
    (sq' : IsPullback h' e' fV g'),
    ¬ IsIso ((higherBaseChangeMapAb fV g' h' e' sq'.w r).app
      ((smallEtalePullbackAb (π ≫ t₀)).obj F))

/-- **The opening of the proof of [Stacks, Tag 0F07].** If `BC(f, n, q)` holds and
`BC(f, n, q + 1)` fails, then there are a diagram of two cartesian squares with `g` quasi-compact
and quasi-separated and an abelian sheaf `F` on the small étale site of `T` annihilated by `n`
whose base change map `(f')⁻¹ R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹ F` is not an isomorphism: the
failure of `BC(f, n, q + 1)` is a failure in a single degree, and `BC(f, n, q)` forces that
degree to be `q + 1`. -/
public theorem exists_not_isIso_higherBaseChangeMapAb_succ {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (q : ℕ) (hprev : BaseChangeHolds f n (q : ℤ))
    (hfail : ¬ BaseChangeHolds f n ((q : ℤ) + 1)) :
    ∃ (S' X' T Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (_hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
      (sq : IsPullback h e f' g) (_ : QuasiCompact g) (_ : QuasiSeparated g)
      (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}),
      (∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0) ∧
        ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) := by
  by_contra hcon
  refine hfail ?_
  intro S' X' T Y s p f' hp g h e sq hqc hqs F hF q' hq'
  rcases le_or_gt (q' : ℤ) (q : ℤ) with hle | hgt
  · exact hprev s p f' hp g h e sq F hF q' hle
  · have hq'q : q' = q + 1 := by omega
    subst hq'q
    by_contra hni
    exact hcon ⟨S', X', T, Y, s, p, f', hp, g, h, e, sq, hqc, hqs, F, hF, hni⟩

end Stacks.EtaleCohomology

end
