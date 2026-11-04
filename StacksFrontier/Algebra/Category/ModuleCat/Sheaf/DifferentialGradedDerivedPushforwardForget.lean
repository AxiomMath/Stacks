module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardComposition

/-!
# A square of derived pushforwards from a square of derived pullbacks

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, presented as a
functor `u : D ⥤ C` in the direction opposite to `f` together with the structure map
`σ : O_D ⟶ f_*O_C`. Let `A` be a sheaf of differential graded `O_C`-algebras, `B` one of
`O_D`-algebras and `φ : B ⟶ f_*A` a homomorphism. Let moreover `Z` be a sheaf of differential
graded `O_C`-algebras with a homomorphism `Z ⟶ A`, let `W` be one of `O_D`-algebras with a
homomorphism `W ⟶ B`, and let `χ : W ⟶ f_*Z`. Then the square

`Rf_* ∘ R(id_D)_* = R(id_C)_* ∘ Rf_* : D(A, d) ⟶ D(W, d)`

commutes, where `R(id_C)_* : D(A, d) ⟶ D(Z, d)` and `R(id_D)_* : D(B, d) ⟶ D(W, d)` are the
derived pushforwards along the identity morphisms of ringed topoi, that is the derived
restrictions of scalars.

This file proves that square the way the source's Tag 0FTU does, from the square of the four
derived pullbacks and uniqueness of adjoints, with all eight derived functors as data. The
restrictions of scalars of
[Stacks, Tag 0FTW](https://stacks.math.columbia.edu/tag/0FTW) are exact, and there the square
is obtained with no derived pullback and no adjunction at all; Tag 0FTW is registered on
`SheafOfModules.DifferentialGradedModule.derivedToposPushforwardForgetIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforwardForget`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedPushforwardSquareIsoOfAdjunctions`:
  uniqueness of adjoints in the shape of a square — from four adjunctions and an isomorphism
  between the two composites of the left adjoints, an isomorphism between the two composites of
  the right adjoints.

## Main results

* `SheafOfModules.DifferentialGradedModule.nonempty_derivedPushforward_comp_restriction_iso`:
  the square of derived pushforwards commutes.

## Implementation notes

The four derived pushforwards and the four derived pullbacks are carried as data, with their
comparison maps and their derived-value conditions, by
`SheafOfModules.DifferentialGradedModule.DerivedPushPullData`, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardComposition`:
the homotopy category of sheaves of differential graded modules carries no triangulated
structure in this development, so the right derived extension of the direct image is not known
to exist and cannot be constructed at this generality.

The proof is the source's own for Tag 0FTU. Each situation has its derived pullback left
adjoint to its derived pushforward by
[Stacks, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR), which is
`SheafOfModules.DifferentialGradedModule.DerivedPushPullData.nonempty_adjunction`; the two
composites of the right adjoints then have isomorphic left adjoints, and the conclusion is
uniqueness of adjoints. The square of the four derived pullbacks is the input, which the source
cites from [Stacks, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI) through Tag 0FTU; it is
produced for the derived pullbacks of exact pairs by
`SheafOfModules.DifferentialGradedModule.derivedPullbackOfInvertsSquareIso`.

Since the four adjunctions are only known to exist, the conclusion is `Nonempty` of an
isomorphism, as for Tag 0FTU next door; and since the derived pushforwards are pinned only up
to isomorphism, the source's equality of functors is an isomorphism.

The universes of the two sites and of their morphisms and of the homogeneous pieces of the four
algebras are independent. The two sheaves of rings share a universe because the structure map
relates them, and the module sections share a universe because the direct image of sheaves of
modules preserves it.

## References

* [Stacks Project, Tag 0FTW](https://stacks.math.columbia.edu/tag/0FTW)
* [Stacks Project, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU)
* [Stacks Project, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR)
* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
-/

@[expose] public section

open CategoryTheory

namespace SheafOfModules

namespace DifferentialGradedModule

universe t₂ a₂ a₂' b₂ b₂' m₂ v₂ u₂ v₂' u₂'

variable {C : Type u₂} [Category.{v₂} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t₂}}
  {C' : Type u₂'} [Category.{v₂'} C'] {J' : GrothendieckTopology C'}
  {R' : Sheaf J' RingCat.{t₂}}
  [HasSheafify J AddCommGrpCat.{m₂}] [J.WEqualsLocallyBijective AddCommGrpCat.{m₂}]
  [HasSheafify J' AddCommGrpCat.{m₂}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m₂}]
  {A : DifferentialGradedAlgebra.{t₂, a₂} R} {B : DifferentialGradedAlgebra.{t₂, a₂'} R'}
  {Z : DifferentialGradedAlgebra.{t₂, b₂} R} {W : DifferentialGradedAlgebra.{t₂, b₂'} R'}

/-- Uniqueness of adjoints in the shape of a square: given `Lf ⊣ Rf`, `lA ⊣ rA`, `lB ⊣ rB`,
`Lg ⊣ Rg` and an isomorphism `lB ⋙ Lf ≅ Lg ⋙ lA` between the two composites of the left
adjoints, the two composites `Rf ⋙ rB` and `rA ⋙ Rg` of the right adjoints are isomorphic.
Indeed both are right adjoint to `lB ⋙ Lf` after transport along the given isomorphism. -/
noncomputable def derivedPushforwardSquareIsoOfAdjunctions
    {Rf : derivedCategory.{t₂, a₂, m₂} A ⥤ derivedCategory.{t₂, a₂', m₂} B}
    {Lf : derivedCategory.{t₂, a₂', m₂} B ⥤ derivedCategory.{t₂, a₂, m₂} A}
    {rA : derivedCategory.{t₂, a₂, m₂} A ⥤ derivedCategory.{t₂, b₂, m₂} Z}
    {lA : derivedCategory.{t₂, b₂, m₂} Z ⥤ derivedCategory.{t₂, a₂, m₂} A}
    {rB : derivedCategory.{t₂, a₂', m₂} B ⥤ derivedCategory.{t₂, b₂', m₂} W}
    {lB : derivedCategory.{t₂, b₂', m₂} W ⥤ derivedCategory.{t₂, a₂', m₂} B}
    {Rg : derivedCategory.{t₂, b₂, m₂} Z ⥤ derivedCategory.{t₂, b₂', m₂} W}
    {Lg : derivedCategory.{t₂, b₂', m₂} W ⥤ derivedCategory.{t₂, b₂, m₂} Z}
    (adjf : Lf ⊣ Rf) (adjA : lA ⊣ rA) (adjB : lB ⊣ rB) (adjg : Lg ⊣ Rg)
    (e : lB ⋙ Lf ≅ Lg ⋙ lA) :
    Rf ⋙ rB ≅ rA ⋙ Rg :=
  (adjB.comp adjf).rightAdjointUniq (Adjunction.ofNatIsoLeft (adjg.comp adjA) e.symm)

/-- **The square of derived pushforwards from a square of derived pullbacks.** Let `f` be a
morphism of ringed sites, let `A` and `B` be sheaves of differential graded algebras over the
two structure sheaves with a homomorphism `φ : B ⟶ f_*A`, and let `Z ⟶ A`, `W ⟶ B` and
`χ : W ⟶ f_*Z` be homomorphisms of sheaves of differential graded algebras, the first two over
the identity morphisms of ringed sites. Given the derived pushforward and the derived pullback
of each of the four situations, with their comparison maps and their derived-value conditions,
and given the square of the four derived pullbacks, the square of the four derived pushforwards
commutes. Each of the four situations has its derived pullback left adjoint to its derived
pushforward by [Stacks, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR), and the
conclusion is uniqueness of adjoints. For the restrictions of scalars of
[Stacks, Tag 0FTW](https://stacks.math.columbia.edu/tag/0FTW) themselves, where the square needs
no derived pullback at all, see
`SheafOfModules.DifferentialGradedModule.nonempty_derivedPushforward_restriction_square_iso`. -/
theorem nonempty_derivedPushforward_comp_restriction_iso
    {uf : C' ⥤ C} [uf.IsContinuous J' J] {σ : R'.obj ⟶ uf.op ⋙ R.obj}
    {σA : R.obj ⟶ (𝟭 C).op ⋙ R.obj} {σB : R'.obj ⟶ (𝟭 C').op ⋙ R'.obj}
    {φ : DifferentialGradedAlgebra.SemilinearHom uf σ B A}
    {ιA : DifferentialGradedAlgebra.SemilinearHom (𝟭 C) σA Z A}
    {ιB : DifferentialGradedAlgebra.SemilinearHom (𝟭 C') σB W B}
    {χ : DifferentialGradedAlgebra.SemilinearHom uf σ W Z}
    [(quasiIsomorphisms.{t₂, a₂, m₂} A).HasLeftCalculusOfFractions]
    [(quasiIsomorphisms.{t₂, a₂', m₂} B).HasLeftCalculusOfFractions]
    [(quasiIsomorphisms.{t₂, a₂', m₂} B).HasRightCalculusOfFractions]
    [(quasiIsomorphisms.{t₂, b₂, m₂} Z).HasLeftCalculusOfFractions]
    [(quasiIsomorphisms.{t₂, b₂, m₂} Z).HasRightCalculusOfFractions]
    [(quasiIsomorphisms.{t₂, b₂', m₂} W).HasRightCalculusOfFractions]
    {Pφ : PullbackData φ} {Eφ : Pφ.HomotopyExtension} (Dφ : DerivedPushPullData Pφ Eφ)
    {PA : PullbackData ιA} {EA : PA.HomotopyExtension} (DA : DerivedPushPullData PA EA)
    {PB : PullbackData ιB} {EB : PB.HomotopyExtension} (DB : DerivedPushPullData PB EB)
    {Pχ : PullbackData χ} {Eχ : Pχ.HomotopyExtension} (Dχ : DerivedPushPullData Pχ Eχ)
    (e : DB.derivedPullback ⋙ Dφ.derivedPullback ≅
      Dχ.derivedPullback ⋙ DA.derivedPullback) :
    Nonempty (Dφ.derivedPushforward ⋙ DB.derivedPushforward ≅
      DA.derivedPushforward ⋙ Dχ.derivedPushforward) := by
  obtain ⟨adjf⟩ := Dφ.nonempty_adjunction
  obtain ⟨adjA⟩ := DA.nonempty_adjunction
  obtain ⟨adjB⟩ := DB.nonempty_adjunction
  obtain ⟨adjg⟩ := Dχ.nonempty_adjunction
  exact ⟨derivedPushforwardSquareIsoOfAdjunctions adjf adjA adjB adjg e⟩

end DifferentialGradedModule

end SheafOfModules

end
