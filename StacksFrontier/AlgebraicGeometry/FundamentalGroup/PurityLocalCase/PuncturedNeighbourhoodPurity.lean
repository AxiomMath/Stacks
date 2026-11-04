module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.HypersurfacePurity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.PuncturedNeighbourhoodComplement

/-!
# Finite étale covers of a punctured closed fibre come from the punctured spectrum

In the local Lefschetz situation `(A, f)` of Tag 0BLF write `X = Spec A`, let `U = X ∖ {𝔪}` be the
punctured spectrum of `A` and `U₀` the punctured spectrum of `A / fA`.  The restriction functor
`FÉt_U ⥤ FÉt_{U₀}` factors, through any open `U'` of `X` with `U₀ ⊆ U' ⊆ U`, as

```
FÉt_U ⟶ FÉt_{U'} ⟶ FÉt_{U₀}.
```

This file records that factorization and runs it in the direction the proofs of Tags 0EK9 and 0EKA
take: a finite étale cover of `U₀` that comes from some such `U'` comes from `U` itself, because
purity at the points `U'` omits extends the cover across them.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.nbhdRestriction_isNeighbourhood_UOpen` and
  `AlgebraicGeometry.LocalLefschetzSituation.U₀ToU_eq_nbhdRestriction_comp_homOfLE` — the morphism
  `U₀ ⟶ U` is the canonical morphism of the largest neighbourhood, and it factors through every
  neighbourhood.
* `…LocalLefschetzSituation.essSurj_finiteEtaleBaseChange_U₀ToU_of_essSurj_restriction` — if
  restriction from `U` to every open `U'` with `U₀ ⊆ U' ⊆ U` is essentially surjective, and every
  finite étale cover of `U₀` is the restriction of a cover of some such `U'`, then restriction
  `FÉt_U ⥤ FÉt_{U₀}` is essentially surjective.
* `…LocalLefschetzSituation.essSurj_finiteEtaleBaseChange_U₀ToU_of_forall_exists_nbhd` — the same
  with the first hypothesis replaced by purity for `(A_f)_𝔭` at every maximal ideal `𝔭 ⊂ A_f`,
  which is hypothesis (4) of Tags 0EK9 and 0EKA.
* `AlgebraicGeometry.LocalLefschetzSituation.hasPurity_quotientRing_of_forall_exists_nbhd` — with
  purity for `A` on top of that, purity holds for `A / fA`.

## What is and is not proved

Nothing here is a Stacks tag and nothing is tagged.  The two factorization lemmas are
unconditional.  The three essential-surjectivity statements carry one hypothesis beyond the
ring-theoretic ones, written out in this development's own vocabulary and quantified in the
statement that uses it:

> every finite étale cover of `U₀` is isomorphic to the restriction along
> `AlgebraicGeometry.LocalLefschetzSituation.nbhdRestriction` of a finite étale cover of some open
> `U'` of `X` with `U₀ ⊆ U' ⊆ U`.

That hypothesis is, verbatim, the `essSurj` field of
`AlgebraicGeometry.LocalLefschetzSituation.IsColimitRestrictionEquivalence`, the essential
surjectivity clause of Tag 0BLV.  Together with hypothesis (4) it is the *only* thing still
missing between the hypotheses of Tag 0EKA and its conclusion, and hypotheses (1), (2) and (3) of
Tag 0EKA appear nowhere below because the source uses them only to reach Tag 0BLV.

The library's carrier of Tag 0BLV,
`AlgebraicGeometry.LocalLefschetzSituation.isColimitRestrictionEquivalence`, cannot discharge it:
that carrier takes
`AlgebraicGeometry.LocalLefschetzSituation.RestrictionToClosedFibreIsEquivalence` — purity for
`A / fA` — as an explicit hypothesis, and purity for `A / fA` is the conclusion of Tag 0BPC, which
the source deduces *from* Tag 0EKA.  Supplying it there would make the deduction circular, so the
clause is carried instead.

## Implementation notes

The opens `U'` with `U₀ ⊆ U' ⊆ U` are
`AlgebraicGeometry.LocalLefschetzSituation.IsNeighbourhood`; restriction from `U` to such a `U'` is
base change along `AlgebraicGeometry.Scheme.homOfLE`, and restriction from `U'` to `U₀` is base
change along `AlgebraicGeometry.LocalLefschetzSituation.nbhdRestriction`.  Those are the shapes in
which the clauses of Tag 0BLV are stated, which is why the hypothesis is phrased with them rather
than with an arbitrary lift of `U₀ ⟶ U` through `U'`.  The factorization of `U₀ ⟶ U` through `U'`
is obtained by cancelling the monomorphism `U ⟶ X`, and the two restrictions are composed through
the canonical comparison `AlgebraicGeometry.finiteEtaleBaseChangeComp`, each base change being a
separately chosen pullback.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0BLV](https://stacks.math.columbia.edu/tag/0BLV)
* [Stacks Project, Tag 0EK9](https://stacks.math.columbia.edu/tag/0EK9)
* [Stacks Project, Tag 0EKA](https://stacks.math.columbia.edu/tag/0EKA)
* [Stacks Project, Tag 0DXZ](https://stacks.math.columbia.edu/tag/0DXZ)
* [Stacks Project, Tag 0BPC](https://stacks.math.columbia.edu/tag/0BPC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocalLefschetzSituation

variable (S : LocalLefschetzSituation.{u})

/-! ### Restriction to `U₀` factors through a neighbourhood -/

/-- The canonical morphism `U₀ ⟶ U'` of the largest neighbourhood `U' = U` is the morphism
`U₀ ⟶ U` of the situation: both compose with the open immersion `U ⟶ X` to `U₀ ⟶ X₀ ⟶ X`. -/
theorem nbhdRestriction_isNeighbourhood_UOpen :
    S.nbhdRestriction S.isNeighbourhood_UOpen = S.U₀ToU := by
  apply (cancel_mono S.UOpen.ι).1
  rw [S.nbhdRestriction_comp_ι, S.U₀ToU_comp_immersion]
  rfl

/-- **The morphism `U₀ ⟶ U` factors through every open `U'` with `U₀ ⊆ U' ⊆ U`**, as the canonical
morphism `U₀ ⟶ U'` of that neighbourhood followed by the inclusion `U' ⟶ U`. -/
theorem U₀ToU_eq_nbhdRestriction_comp_homOfLE {W : S.X.Opens} (hW : S.IsNeighbourhood W) :
    S.U₀ToU = S.nbhdRestriction hW ≫ S.X.homOfLE hW.1 := by
  rw [S.nbhdRestriction_comp_homOfLE S.isNeighbourhood_UOpen hW hW.1,
    S.nbhdRestriction_isNeighbourhood_UOpen]

/-! ### Essential surjectivity of restriction from `U` to `U₀` -/

/-- **A finite étale cover of `U₀` defined over a neighbourhood is defined over `U`.** Suppose
restriction of finite étale covers from `U` to every open `U'` with `U₀ ⊆ U' ⊆ U` is essentially
surjective, and suppose every finite étale cover of `U₀` is isomorphic to the restriction of a
finite étale cover of some such `U'`.  Then restriction `FÉt_U ⥤ FÉt_{U₀}` is essentially
surjective.

Given a cover `C` of `U₀`, the second hypothesis produces `U'` and a cover `B` of `U'` restricting
to `C`; the first produces a cover of `U` restricting to `B`; and `U₀ ⟶ U` factors as
`U₀ ⟶ U' ⟶ U`, so restricting that cover to `U₀` recovers `C`. -/
theorem essSurj_finiteEtaleBaseChange_U₀ToU_of_essSurj_restriction
    (hrestr : ∀ {W : S.X.Opens} (hW : S.IsNeighbourhood W),
      (finiteEtaleBaseChange (S.X.homOfLE hW.1)).EssSurj)
    (hnbhd : ∀ C : FiniteEtaleOver S.U₀, ∃ (W : S.X.Opens) (hW : S.IsNeighbourhood W)
      (B : FiniteEtaleOver W.toScheme),
      Nonempty ((finiteEtaleBaseChange (S.nbhdRestriction hW)).obj B ≅ C)) :
    (finiteEtaleBaseChange S.U₀ToU).EssSurj := by
  refine ⟨fun C => ?_⟩
  obtain ⟨W, hW, B, ⟨e⟩⟩ := hnbhd C
  have : (finiteEtaleBaseChange (S.X.homOfLE hW.1)).EssSurj := hrestr hW
  exact ⟨(finiteEtaleBaseChange (S.X.homOfLE hW.1)).objPreimage B,
    ⟨(finiteEtaleBaseChangeComp (S.nbhdRestriction hW) (S.X.homOfLE hW.1) S.U₀ToU
      (S.U₀ToU_eq_nbhdRestriction_comp_homOfLE hW)).app _ ≪≫
    (finiteEtaleBaseChange (S.nbhdRestriction hW)).mapIso
      ((finiteEtaleBaseChange (S.X.homOfLE hW.1)).objObjPreimageIso B) ≪≫ e⟩⟩

/-- **The conclusion of Tags 0EK9 and 0EKA, from hypothesis (4) and the essential surjectivity
clause of Tag 0BLV.** Suppose purity holds for `(A_f)_𝔭` at every maximal ideal `𝔭 ⊂ A_f`, and
suppose every finite étale cover of `U₀` is isomorphic to the restriction of a finite étale cover
of some open `U'` of `X` with `U₀ ⊆ U' ⊆ U`.  Then the restriction functor `FÉt_U ⥤ FÉt_{U₀}` is
essentially surjective.

The points of `U` that `U'` omits are maximal ideals of `A_f`, so purity is available at each of
them and the cover over `U'` extends across them to a cover of `U`. -/
theorem essSurj_finiteEtaleBaseChange_U₀ToU_of_forall_exists_nbhd
    (haway : ∀ (p : Ideal (Localization.Away S.f)) [p.IsMaximal],
      HasPurity (Localization.AtPrime p))
    (hnbhd : ∀ C : FiniteEtaleOver S.U₀, ∃ (W : S.X.Opens) (hW : S.IsNeighbourhood W)
      (B : FiniteEtaleOver W.toScheme),
      Nonempty ((finiteEtaleBaseChange (S.nbhdRestriction hW)).obj B ≅ C)) :
    (finiteEtaleBaseChange S.U₀ToU).EssSurj :=
  S.essSurj_finiteEtaleBaseChange_U₀ToU_of_essSurj_restriction
    (fun hW => S.essSurj_restriction_of_hasPurity_away hW haway) hnbhd

/-- **The proof of Tags 0DXZ and 0BPC, from hypotheses (3) and (4) and the essential surjectivity
clause of Tag 0BLV.** Purity holds for `A / fA` as soon as purity holds for `A`, purity holds for
`(A_f)_𝔭` at every maximal ideal `𝔭 ⊂ A_f`, and every finite étale cover of `U₀` is isomorphic to
the restriction of a finite étale cover of some open `U'` of `X` with `U₀ ⊆ U' ⊆ U`. -/
theorem hasPurity_quotientRing_of_forall_exists_nbhd
    (haway : ∀ (p : Ideal (Localization.Away S.f)) [p.IsMaximal],
      HasPurity (Localization.AtPrime p))
    (hnbhd : ∀ C : FiniteEtaleOver S.U₀, ∃ (W : S.X.Opens) (hW : S.IsNeighbourhood W)
      (B : FiniteEtaleOver W.toScheme),
      Nonempty ((finiteEtaleBaseChange (S.nbhdRestriction hW)).obj B ≅ C))
    (hpurity : HasPurity S.A) :
    HasPurity S.quotientRing :=
  S.hasPurity_quotientRing_of_essSurj_U₀ToU
    (S.essSurj_finiteEtaleBaseChange_U₀ToU_of_forall_exists_nbhd haway hnbhd) hpurity

end AlgebraicGeometry.LocalLefschetzSituation

end
