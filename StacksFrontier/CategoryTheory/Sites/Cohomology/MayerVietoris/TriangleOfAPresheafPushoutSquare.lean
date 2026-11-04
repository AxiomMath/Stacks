module

public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.FreeAbelianSheavesOfAPresheafSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.ShortExactSectionsAndComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The Mayer–Vietoris triangle of a pushout square of presheaves of sets

Let `(C, J)` be a small site and let

```
D ⟶ F
↓    ↓
E ⟶ G
```

be a commutative square of presheaves of sets on `C` such that `G^# = E^# ∐_{D^#} F^#` and
`D^# ⟶ F^#` is injective. [Stacks, Tag 0EVZ] asserts that there is then a canonical
distinguished triangle

`RΓ(G, K) ⟶ RΓ(E, K) ⊕ RΓ(F, K) ⟶ RΓ(D, K) ⟶ RΓ(G, K)[1]`

functorial in `K` in the derived category of abelian sheaves, where `RΓ(K, -)` is the
cohomology over a presheaf of sets of [Stacks, Tag 079X].

This file proves it, by instantiating the Mayer–Vietoris comparison engine of
[Stacks, Tag 0F16] at the system of section functors over presheaves of sets.
[Stacks, Tag 0EVY] is the same statement for a square of objects of the site; the source
deduces this one from it by enlarging the site until the four sheaves are representable,
which is not what happens here — the engine never needed the corners to be objects of the
site, only a contravariant system of additive section functors, so the presheaf case is a
second instantiation of it rather than a reduction to the first.

## Main definitions

* `Stacks.MayerVietoris.PresheafSquare.derivedCSquareData`: the derived-section functors
  `RΓ(-, K)` over the four presheaves, the derived functor of the mapping cocone, and the three
  descended natural transformations of Stacks 0F16, at a square of presheaves of sets.
* `Stacks.MayerVietoris.PresheafSquare.cSquareTriangle`: the Mayer–Vietoris triangle of the
  square at a derived object, available once the comparison is invertible there.

## Main results

* `Stacks.MayerVietoris.PresheafSquare.isIso_derivedCSquare_of_isPushout`: **Stacks 0EVZ**, the
  canonical comparison is an isomorphism of functors on the whole derived category.
* `Stacks.MayerVietoris.PresheafSquare.cSquareTriangle_distinguished`: **Stacks 0EVZ**, the
  resulting triangle is distinguished at every derived object.
* `Stacks.MayerVietoris.PresheafSquare.cSquareTriangle_functorial`: every morphism of derived
  objects induces a unique morphism of Mayer–Vietoris triangles with the expected components,
  which is the functoriality in `K` that the source asserts.

## Implementation notes

The site is taken small and all four universes are collapsed to `u`. That is forced by the
derived half rather than chosen: the comparison is built from K-injective resolutions, which
need `Sheaf J AddCommGrpCat.{u}` to be Grothendieck abelian, and `AddCommGrpCat.{u}` has
`u`-indexed coproducts only. It is the generality of the source, where a site has a set of
objects, and it is the convention of the other presheaf-coefficient statements of this chapter.

The sections over a presheaf of sets, and the short exact sequence of sections at an injective
abelian sheaf which is the whole sheaf-theoretic content of the tag, are
`Stacks.MayerVietoris.PresheafSquare.presheafSections` and
`Stacks.MayerVietoris.PresheafSquare.shortExact_sectionsShortComplex`.

Unlike `Stacks.Cohomology.MayerVietoris.isIso_derivedCSquare_of_isPushout` for Tag 0EVY, which
is stated for sheaves of modules on a ringed site, the coefficients here are abelian sheaves:
that is the category `D(C)` the source's statement names, and the free abelian sheaf on a
presheaf of sets is what corepresents sections over it.

## References

* [Stacks Project, Tag 0EVZ](https://stacks.math.columbia.edu/tag/0EVZ)
* [Stacks Project, Tag 0EVY](https://stacks.math.columbia.edu/tag/0EVY)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 079X](https://stacks.math.columbia.edu/tag/079X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.MayerVietoris.CanonicalMapOfComplexes

namespace Stacks.MayerVietoris.PresheafSquare

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type u)] [HasSheafify J AddCommGrpCat.{u}]

/-- **Abelian sheaves on a small site are Grothendieck abelian**, which is what supplies the
K-injective resolutions the derived construction runs on. -/
instance isGrothendieckAbelian_sheaf :
    IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u}) :=
  Sheaf.isGrothendieckAbelian_of_small J AddCommGrpCat.{u}

omit [HasWeakSheafify J (Type u)] in
/-- Every complex of abelian sheaves on a small site admits a K-injective resolution whose
terms are injective objects. -/
theorem exists_kInjectiveResolution_injective
    (K : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) :
    ∃ (I : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f ∧ ∀ p : ℤ, Injective (I.X p) :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor (Sheaf J AddCommGrpCat.{u})).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion (Sheaf J AddCommGrpCat.{u})).app K,
    inferInstance, inferInstance, fun _ => inferInstance⟩

variable (sq : Square (Cᵒᵖ ⥤ Type u))

/-- **The derived construction of Stacks 0F16 over a square of presheaves of sets**: the derived
sections `RΓ(-, K)` over the four presheaves, the derived functor of the mapping cocone of the
signed restriction map, and the three descended natural transformations, each identified on a
K-injective representative with its chain-level construction. -/
def derivedCSquareData : General.DerivedCSquareData (presheafSections J) sq :=
  General.derivedCSquareDataOfIsGrothendieckAbelian (presheafSections J) sq

/-- **Stacks 0EVZ.** If the sheafifications of a square of presheaves of sets form a pushout
square and `D^# ⟶ F^#` is a monomorphism, then the canonical natural transformation of
Stacks 0F16 from derived sections over `G` to the mapping cocone is an isomorphism, so that the
Mayer–Vietoris triangle is defined at every object of the derived category of abelian
sheaves. -/
@[stacks 0EVZ "the canonical comparison"]
theorem isIso_derivedCSquare_of_isPushout
    (hpushout : (sq.map (presheafToSheaf J (Type u))).IsPushout)
    (hmono : Mono ((presheafToSheaf J (Type u)).map sq.f₁₂)) :
    IsIso (derivedCSquareData J sq).derivedCSquare :=
  Stacks.Cohomology.MayerVietoris.General.isIso_derivedCSquare_of_sectionsShortExact
    (presheafSections J) sq (derivedCSquareData J sq)
    (fun K => exists_kInjectiveResolution_injective J K)
    (fun ℱ hℱ => shortExact_sectionsShortComplex J sq hpushout hmono ℱ hℱ)

section Triangle

variable (hpushout : (sq.map (presheafToSheaf J (Type u))).IsPushout)
  (hmono : Mono ((presheafToSheaf J (Type u)).map sq.f₁₂))

include hpushout hmono

/-- The comparison is invertible at every derived object, which is what makes the
Mayer–Vietoris triangle of the square available there. -/
theorem isCSquareIso (K : DerivedCategory (Sheaf J AddCommGrpCat.{u})) :
    (derivedCSquareData J sq).IsCSquareIso K :=
  have := isIso_derivedCSquare_of_isPushout J sq hpushout hmono
  inferInstance

/-- **The Mayer–Vietoris triangle of a square of presheaves of sets**,
`RΓ(G, K) ⟶ RΓ(E, K) ⊕ RΓ(F, K) ⟶ RΓ(D, K) ⟶ RΓ(G, K)[1]`. -/
def cSquareTriangle (K : DerivedCategory (Sheaf J AddCommGrpCat.{u})) :
    Triangle (DerivedCategory AddCommGrpCat.{u}) :=
  haveI := isCSquareIso J sq hpushout hmono K
  (derivedCSquareData J sq).cSquareTriangle K

/-- **Stacks 0EVZ.** The Mayer–Vietoris triangle of a square of presheaves of sets whose
sheafifications form a pushout square with monomorphic `D^# ⟶ F^#` is a distinguished triangle
of the derived category of abelian groups, at every object of the derived category of abelian
sheaves. -/
@[stacks 0EVZ "the triangle is distinguished"]
theorem cSquareTriangle_distinguished (K : DerivedCategory (Sheaf J AddCommGrpCat.{u})) :
    cSquareTriangle J sq hpushout hmono K ∈ distTriang (DerivedCategory AddCommGrpCat.{u}) :=
  have := isCSquareIso J sq hpushout hmono K
  (derivedCSquareData J sq).cSquareTriangle_distinguished K

/-- **Stacks 0EVZ, the functoriality in the derived object.** Every morphism of derived objects
induces a unique morphism of Mayer–Vietoris triangles whose three components are the maps
induced on derived sections and on the mapping cocone. -/
@[stacks 0EVZ "functoriality of the triangle in the derived object"]
theorem cSquareTriangle_functorial
    {K K' : DerivedCategory (Sheaf J AddCommGrpCat.{u})} (f : K ⟶ K') :
    ∃! t : cSquareTriangle J sq hpushout hmono K ⟶ cSquareTriangle J sq hpushout hmono K',
      t.hom₁ = ((derivedCSquareData J sq).derivedSections sq.X₄).map f ∧
        t.hom₂ = ((derivedCSquareData J sq).sectionsData.biprodFunctor sq).map f ∧
        t.hom₃ = ((derivedCSquareData J sq).derivedSections sq.X₁).map f :=
  have := isCSquareIso J sq hpushout hmono K
  have := isCSquareIso J sq hpushout hmono K'
  (derivedCSquareData J sq).cSquareTriangle_functorial f

end Triangle

end Stacks.MayerVietoris.PresheafSquare

end
