module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.UpperShriekExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriekAffineEtaleUnbounded
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 0GLK: the cohomology sheaves of `Rf^!` on the affine étale site

Let `f : X ⟶ Y` be a separated finite type morphism of quasi-compact and quasi-separated
schemes, let `Λ` be a torsion ring and let `K ∈ D(Y_étale, Λ)`.  For `n ∈ ℤ` the cohomology sheaf
`H^n(Rf^! K)` restricted to `X_{affine, étale}` is the sheaf associated to the presheaf
```
U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[n]).
```

## Main results

* `Stacks.EtaleCohomology.derivedUpperShriekHomologyAffineEtaleUnbounded`: the isomorphism, for a
  compactification `j` of `f` and `Rf^!` the right adjoint of `Rf_! = R(fbar)_* ∘ j_!` of
  [Stacks, Tag 0G2C].
* `Stacks.EtaleCohomology.derivedUpperShriek_homology_affineEtale`: **[Stacks, Tag 0GLK]**, with
  the compactification produced by Nagata's theorem, [Stacks, Tag 0F41], and the identification
  holding for every compactification.

## Implementation notes

`Rf_!` and `Rf^!` are the ones of [Stacks, Tag 0G2C] in this repository: `Rf_!` is read off a
compactification `j`, and `Rf^!` is `CategoryTheory.Functor.rightAdjoint` of it.  The statement
is proved for *every* compactification, and Nagata's theorem supplies one, so no compactification
is assumed.  A ring is torsion exactly when `n = 0` in it for some `n ≥ 1`; this is how the
hypothesis is stated.  Following the conventions of the source, rings are commutative.  The ring
lies in `Type`, the universe in which [Stacks, Tag 0G2C] is available
(`Stacks.EtaleCohomology.DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded`); this is
not a mathematical restriction.  The two presheaves take values in abelian groups and the
cohomology sheaf is compared through its underlying abelian sheaf, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriekAffineEtale`.

## References

* [Stacks Project, Tag 0GLK](https://stacks.math.columbia.edu/tag/0GLK)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)

include hn hΛ in
/-- The isomorphism of Stacks Tag 0GLK for a compactification `j` of `f`: with `Rf^!` the right
adjoint of `Rf_! = R(fbar)_* ∘ j_!` of [Stacks, Tag 0G2C], the cohomology sheaf `H^m(Rf^! K)`
restricted to `X_{affine, étale}` is the sheaf associated to
`U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[m])`. -/
def derivedUpperShriekHomologyAffineEtaleUnbounded {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] (j : CompactificationOf (Over.mk f))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ Y)) (m : ℤ) :
    letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f j
    (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{u + 1 + 1}).obj
        (affineEtaleLowerShriekHomPresheafUnbounded.{u, 0} f j Λ K m) ≅
      (affineEtaleAbelianRestriction.{u, 0} Λ X).obj
        ((DerivedCategory.homologyFunctor _ m).obj
          ((derivedLowerShriekUnbounded.{u, 0} f j Λ).rightAdjoint.obj K)) :=
  letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f j
  derivedUpperShriekHomologyAffineEtaleOfAdjunction.{u, 0} j Λ
    (Adjunction.ofIsLeftAdjoint _) K m

include hn hΛ in
/-- **Stacks Project, Tag 0GLK.** Let `f : X ⟶ Y` be a separated finite type morphism of
quasi-compact and quasi-separated schemes, let `Λ` be a torsion ring (`n = 0` in `Λ` for some
`n ≥ 1`) and let `K ∈ D(Y_étale, Λ)`.  For `m ∈ ℤ` the cohomology sheaf `H^m(Rf^! K)` restricted
to `X_{affine, étale}` is the sheaf associated to the presheaf
`U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K[m])`.

Here `Rf_! = R(fbar)_* ∘ j_!` is read off a compactification `j` of `f`, which exists by Nagata's
theorem ([Stacks, Tag 0F41]), and `Rf^!` is its right adjoint of [Stacks, Tag 0G2C].  The
identification holds for every compactification.  The functoriality of `R(U ⟶ Y)_! Λ` in `U` is
that of the discussion preceding the lemma, and the identification is one of presheaves: the
transition maps are those the source leaves to the reader.  The ring `Λ` lies in `Type`, the
universe in which [Stacks, Tag 0G2C] is available. -/
@[stacks 0GLK, sga "4½ Arcata 4.5.1" "more general", sga "7 XIII 2.1.6" "more general"]
theorem derivedUpperShriek_homology_affineEtale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    (∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) ∧
      ∀ (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, 0} Λ Y))
        (m : ℤ),
        letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f j
        Nonempty ((presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{u + 1 + 1}).obj
            (affineEtaleLowerShriekHomPresheafUnbounded.{u, 0} f j Λ K m) ≅
          (affineEtaleAbelianRestriction.{u, 0} Λ X).obj
            ((DerivedCategory.homologyFunctor _ m).obj
              ((derivedLowerShriekUnbounded.{u, 0} f j Λ).rightAdjoint.obj K))) :=
  ⟨hasCompactification_of_compactSpace_quasiSeparatedSpace f,
    fun j K m ↦ ⟨derivedUpperShriekHomologyAffineEtaleUnbounded Λ n hn hΛ f j K m⟩⟩

end Stacks.EtaleCohomology
