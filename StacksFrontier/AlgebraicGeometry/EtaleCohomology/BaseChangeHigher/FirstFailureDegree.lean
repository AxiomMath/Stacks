module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding

/-!
# The degree in which étale base change first fails

Let `f : X ⟶ S` be a morphism of schemes and `n` an integer, and suppose the base change
condition `BC(f, n, q)` of [Stacks, Tag 0F02] holds while `BC(f, n, q + 1)` fails. Then a
counterexample exists in degree exactly `q + 1`, and the base change map it fails for is a
monomorphism: the diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  T
```

with both squares cartesian, `g` quasi-compact and quasi-separated, and an abelian sheaf `F` on
the small étale site of `T` annihilated by `n`, can be chosen so that
`(f')⁻¹R^{q+1}g_* F ⟶ R^{q+1}h_* e⁻¹F` is injective but not an isomorphism.

This is the opening of the proof of [Stacks, Tag 0F07]. That the failure sits in degree `q + 1`
rather than in some lower degree is forced by `BC(f, n, q)`, since `BC` asserts invertibility in
*all* degrees up to its index; injectivity is part (1) of [Stacks, Tag 0F03], which applies
because `BC(f, n, q)` holds in the degree below.

## Main results

* `Stacks.EtaleCohomology.exists_mono_not_isIso_higherBaseChangeMapAb` — the counterexample in
  degree `q + 1`, with its base change map a monomorphism.
* `Stacks.EtaleCohomology.exists_nonzero_cokernel_higherBaseChangeMapAb` — the same
  counterexample read through its cokernel, which is therefore nonzero.

## Implementation notes

The counterexample is indexed by `q : ℕ` with `BC(f, n, q)` holding and `BC(f, n, q + 1)`
failing, rather than by a `q ≥ 1` with `BC(f, n, q - 1)` holding and `BC(f, n, q)` failing: the
two are the same hypothesis, and the first spelling is the one in which part (1) of
[Stacks, Tag 0F03] is stated here, so no subtraction on `ℤ` has to be moved across the
`BaseChangeHolds` argument.

The diagram, the quasi-compactness and quasi-separatedness of `g` and the annihilation of `F` by
`n` are existentially bound in exactly the spelling `Stacks.EtaleCohomology.BaseChangeHolds`
uses, so that the result can be fed back to it.

## What is missing for [Stacks, Tag 0F07]

[Stacks, Tag 0F07] strengthens the counterexample produced here to one whose base is the
spectrum of a field. Its proof shrinks `S'` to an affine open, picks a geometric point `x̄` of
`X'` and a stalk class `ξ` outside the image of the base change map, and applies the dévissage
`AlgebraicGeometry.exists_field_point` ([Stacks, Tag 0F06], already available) to the property

> `P(T')`: the image of `ξ` in `(R^{q+1}h'_*(e')⁻¹F')_{x̄}` is not in the image of
> `((f')⁻¹R^{q+1}g'_*F')_{x̄}`,

for `π : T' ⟶ T` quasi-compact and quasi-separated, `F' = π⁻¹F`, `Y' = Y ×_T T'`,
`g' = g ∘ π` and `h' = h ∘ π'`. Neither `P` nor the three hypotheses of the dévissage can be
written down yet; what is absent is:

* **Functoriality of the base change map in the base.** `P` is about the comparison square
  relating `higherBaseChangeMapAb` for `(f', g, h, e)` to the one for `(f', g', h', e')`, i.e.
  the pasting of the square along `π`. No such compatibility exists for
  `Stacks.EtaleCohomology.higherBaseChangeMapAb`; the tag comments on
  `Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap` record the same gap, pasting of
  base change maps being carried for ringed topoi on sheaves of modules and for the unbounded
  derived étale comparison but not for the bounded below
  `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`.
* **Invariance of the base change map under a thickening of the base**, hypothesis (1) of the
  dévissage. [Stacks, Tag 03SI] is available as an equivalence of small étale topoi
  (`Stacks.EtaleCohomology.smallEtaleInverseImage_isEquivalence_of_universalHomeomorphism`), but
  not as a compatibility of that equivalence with higher direct images along `h'`.
* **The colimit formula of [Stacks, Tag 0EYM]**, hypothesis (2) of the dévissage:
  `R^{q+1}h'_*(e')⁻¹F' = colim_i R^{q+1}h_{i,*}e_i⁻¹F_i` for a cofiltered limit of
  quasi-compact quasi-separated schemes over `T` with affine transition morphisms. The transition
  and cocone maps exist, but their own tag comments state that the colimit assertion is not
  proved.
* **The closed/open step**, hypothesis (3) of the dévissage, which additionally needs the
  relative Leray spectral sequence of [Stacks, Tag 0734] for *abelian* sheaves on a small étale
  site — `Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence` is for sheaves of
  modules on a ringed site — and [Stacks, Tag 0959], `e⁻¹i_* = i'_*e_Z⁻¹`, for abelian sheaves on
  the small étale sites, `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeNatTrans` being for
  sheaves of sets on the big étale site model.

## References

* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **A first failure of étale base change is injective and sits in the expected degree.** If
`BC(f, n, q)` holds and `BC(f, n, q + 1)` fails, there are a diagram of two cartesian squares
with quasi-compact quasi-separated `g` and an abelian sheaf `F` on the small étale site of `T`
annihilated by `n` whose base change map `(f')⁻¹R^{q+1}g_* F ⟶ R^{q+1}h_* e⁻¹F` is a
monomorphism and not an isomorphism. This is the opening of the proof of [Stacks, Tag 0F07]. -/
public theorem exists_mono_not_isIso_higherBaseChangeMapAb {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (q : ℕ) (hprev : BaseChangeHolds f n (q : ℤ))
    (hfail : ¬ BaseChangeHolds f n ((q : ℤ) + 1)) :
    ∃ (S' X' T Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (_hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
      (sq : IsPullback h e f' g) (_ : QuasiCompact g) (_ : QuasiSeparated g)
      (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}),
      (∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0) ∧
        Mono ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) ∧
        ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) := by
  by_contra hcon
  refine hfail ?_
  intro S' X' T Y s p f' hp g h e sq hqc hqs F hF q' hq'
  rcases le_or_gt (q' : ℤ) (q : ℤ) with hle | hgt
  · exact hprev s p f' hp g h e sq F hF q' hle
  · have hq'q : q' = q + 1 := by omega
    subst hq'q
    by_contra hni
    exact hcon ⟨S', X', T, Y, s, p, f', hp, g, h, e, sq, hqc, hqs, F, hF,
      mono_higherBaseChangeMapAb_app_of_annihilated (f := f) (n := n) (q := q) (s := s) (p := p)
        (f' := f') (g := g) (h := h) (e := e) (hbc := hprev) (sq₁ := hp) (sq := sq) (hF := hF),
      hni⟩

/-- **A first failure of étale base change has nonzero cokernel.** The counterexample of
`Stacks.EtaleCohomology.exists_mono_not_isIso_higherBaseChangeMapAb`, read through the cokernel
of its base change map: a monomorphism in an abelian category is an isomorphism exactly when its
cokernel vanishes, so the failure is recorded by a nonzero object. -/
public theorem exists_nonzero_cokernel_higherBaseChangeMapAb {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (q : ℕ) (hprev : BaseChangeHolds f n (q : ℤ))
    (hfail : ¬ BaseChangeHolds f n ((q : ℤ) + 1)) :
    ∃ (S' X' T Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (_hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
      (sq : IsPullback h e f' g) (_ : QuasiCompact g) (_ : QuasiSeparated g)
      (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}),
      (∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0) ∧
        ¬ IsZero (cokernel ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)) := by
  obtain ⟨S', X', T, Y, s, p, f', hp, g, h, e, sq, hqc, hqs, F, hF, hmono, hni⟩ :=
    exists_mono_not_isIso_higherBaseChangeMapAb f n q hprev hfail
  refine ⟨S', X', T, Y, s, p, f', hp, g, h, e, sq, hqc, hqs, F, hF, fun hzero => hni ?_⟩
  have hepi : Epi ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) :=
    (Preadditive.epi_iff_isZero_cokernel _).2 hzero
  exact isIso_of_mono_of_epi _

end Stacks.EtaleCohomology

end
