module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 083I: the base-change loci of a map of modules under a flat pullback

In the situation of Stacks 083F — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
and a map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — a morphism `g : X' ⟶ X` of algebraic
spaces gives a situation of Stacks 083F on `X'`: the structure morphism `g ≫ f : X' ⟶ Y` and the
inverse image `u' = g^*u : g^*ℱ ⟶ g^*𝒢`, the two inverse images being quasi-coherent by
Stacks 03GA.

**Stacks 083I** compares the four base-change loci of `u` with those of `u'` when `g` is flat:

1. if `𝒢` is of finite type and the image of `|X'| ⟶ |X|` contains the support of `𝒢`, then
   `F_surj = F'_surj` and `F_zero = F'_zero`;
2. if `ℱ` is of finite type and the image of `|X'| ⟶ |X|` contains the support of `ℱ`, then
   `F_inj = F'_inj` and `F_zero = F'_zero`;
3. if `ℱ` and `𝒢` are of finite type and the image of `|X'| ⟶ |X|` contains the supports of
   both, then `F_iso = F'_iso`.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.inverseImageSituation`: the situation on `X'`
  obtained by pulling the map of modules back along `g : X' ⟶ X`, with the quasi-coherence of
  the two inverse images supplied by Stacks 03GA.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.surjFunctor_and_zeroFunctor_inverseImageSituation_eq`
  is **Stacks 083I part (1)**,
  `.injFunctor_and_zeroFunctor_inverseImageSituation_eq` is **part (2)** and
  `.isoFunctor_inverseImageSituation_eq` is **part (3)**.

## Implementation notes

`AlgebraicGeometry.Space.ModuleMapSituation.inverseImageSituation` is
`AlgebraicGeometry.Space.ModuleMapSituation.pullbackSituation` with its two quasi-coherence
arguments discharged by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`
(Stacks 03GA) from the quasi-coherence of `ℱ` and `𝒢`, so the three parts are the comparisons of
`AlgebraicGeometry.Space.ModuleMapSituation.surjFunctor_and_zeroFunctor_pullbackSituation_eq`,
`.injFunctor_and_zeroFunctor_pullbackSituation_eq` and `.isoFunctor_pullbackSituation_eq` at
those two proofs.  It is reducible, as `pullbackSituation` is, so that its test schemes are those
of the original situation on the nose.

## References

* [Stacks Project, Tag 083I](https://stacks.math.columbia.edu/tag/083I)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ModuleMapSituation

variable (D : ModuleMapSituation.{u, u} B S hS) {X' : AlgebraicSpaces B S hS} (g : X' ⟶ D.X)

/-- The inverse image of the situation of Stacks 083F along a morphism `g : X' ⟶ X` of the
source space: the structure morphism is `g ≫ f : X' ⟶ Y` and the map of modules is
`u' = g^*u : g^*ℱ ⟶ g^*𝒢`, the two inverse images being quasi-coherent by Stacks 03GA.

This is reducible: its target space is `D.Y` on the nose, so that the test schemes of the two
situations are the same category. -/
@[reducible]
def inverseImageSituation : ModuleMapSituation.{u, u} B S hS :=
  D.pullbackSituation g
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g D.F
      D.quasicoherent_F)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g D.G
      D.quasicoherent_G)

/-- **Stacks 083I part (1).**  In Situation 083F let `g : X' ⟶ X` be a flat morphism of
algebraic spaces and let `u' : ℱ' ⟶ 𝒢'` be the pullback of `u` to `X'`.  If `𝒢` is of finite
type and the image of `|X'| ⟶ |X|` contains the support of `𝒢`, then `F_surj = F'_surj` and
`F_zero = F'_zero`. -/
@[stacks 083I "part (1): F_surj = F'_surj and F_zero = F'_zero"]
theorem surjFunctor_and_zeroFunctor_inverseImageSituation_eq (hgflat : IsFlat B S hS g.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    D.surjFunctor (modulePullbackSystem B S hS) =
        (D.inverseImageSituation g).surjFunctor (modulePullbackSystem B S hS) ∧
      D.zeroFunctor (modulePullbackSystem B S hS) =
        (D.inverseImageSituation g).zeroFunctor (modulePullbackSystem B S hS) :=
  D.surjFunctor_and_zeroFunctor_pullbackSituation_eq g _ _ hgflat hGft hGsupp

/-- **Stacks 083I part (2).**  In Situation 083F let `g : X' ⟶ X` be a flat morphism of
algebraic spaces and let `u' : ℱ' ⟶ 𝒢'` be the pullback of `u` to `X'`.  If `ℱ` is of finite
type and the image of `|X'| ⟶ |X|` contains the support of `ℱ`, then `F_inj = F'_inj` and
`F_zero = F'_zero`. -/
@[stacks 083I "part (2): F_inj = F'_inj and F_zero = F'_zero"]
theorem injFunctor_and_zeroFunctor_inverseImageSituation_eq (hgflat : IsFlat B S hS g.hom)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    D.injFunctor (modulePullbackSystem B S hS) =
        (D.inverseImageSituation g).injFunctor (modulePullbackSystem B S hS) ∧
      D.zeroFunctor (modulePullbackSystem B S hS) =
        (D.inverseImageSituation g).zeroFunctor (modulePullbackSystem B S hS) :=
  D.injFunctor_and_zeroFunctor_pullbackSituation_eq g _ _ hgflat hFft hFsupp

/-- **Stacks 083I part (3).**  In Situation 083F let `g : X' ⟶ X` be a flat morphism of
algebraic spaces and let `u' : ℱ' ⟶ 𝒢'` be the pullback of `u` to `X'`.  If `ℱ` and `𝒢` are of
finite type and the image of `|X'| ⟶ |X|` contains the supports of `ℱ` and `𝒢`, then
`F_iso = F'_iso`. -/
@[stacks 083I "part (3): F_iso = F'_iso"]
theorem isoFunctor_inverseImageSituation_eq (hgflat : IsFlat B S hS g.hom)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hFsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom))
    (hGsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    D.isoFunctor (modulePullbackSystem B S hS) =
      (D.inverseImageSituation g).isoFunctor (modulePullbackSystem B S hS) :=
  D.isoFunctor_pullbackSituation_eq g _ _ hgflat hFft hGft hFsupp hGsupp

end ModuleMapSituation

end AlgebraicGeometry.Space

end
