module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapIsoLocusRepresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# Flattening a map: the isomorphism locus of a surjection out of a pure module is closed

In Situation Stacks 083F — a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` and a
map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — Stacks 0CWD says: if `f` is of finite
presentation, `ℱ` is of finite presentation, flat over `B` and pure relative to `B`, and `u` is
surjective, then `F_iso` is representable by a closed immersion `Z ⟶ B`, of finite presentation
when `𝒢` is of finite presentation.

The proof is the source's.  Let `𝒦 = Ker(u)` and `v : 𝒦 ⟶ ℱ` the inclusion, the situation
`AlgebraicGeometry.Space.ModuleMapSituation.kernelSituation`.  By Stacks 0CVM on the exact
sequence `𝒦 ⟶ ℱ ⟶ 𝒢 ⟶ 0`
(`AlgebraicGeometry.Space.ModuleMapSituation.isIsoAt_iff_kernelSituation_isZeroAt`) we have
`F_{u,iso} = F_{v,zero}`.  Stacks 0CWC applied to `v`, whose target module is `ℱ`
(`AlgebraicGeometry.Space.ModuleMapSituation.isClosedSubspace_zeroSubfunctor_of_isPureRelative`),
says that `F_{v,zero}` is a closed subspace of `B`.  If `𝒢` is of finite presentation then `𝒦`
is of finite type by Stacks 082T
(`AlgebraicGeometry.Space.ModuleMapSituation.isFiniteTypeOnSite_kernelSituation_F`), and the
finite-presentation clause of Stacks 0CWC gives the last assertion.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.fpSourcePrePureSituation`: the situation of
  Stacks 0CV6 formed by `f` and the *source* module `ℱ`, whose purity is hypothesis (2) of
  Stacks 0CWD.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isoLocusRepresentation_of_isPureRelative`:
  **Stacks 0CWD**, with conclusion
  `AlgebraicGeometry.Space.ModuleMapSituation.IsoLocusRepresentation`.

## Implementation notes

The final sentence of the source reads "`Z ⟶ S` is of finite presentation if `𝒢` is of finite
presentation".  Taken literally this is false, and the source's proof proves `Z ⟶ B` instead:
with `B` the spectrum of a ring that is not of finite presentation over `S`, `X = B`, `f = id`
and `u = id : 𝒪_X ⟶ 𝒪_X`, every hypothesis holds (`𝒪_X` is finite over `B`, hence pure
relative to `B`), `𝒢 = 𝒪_X` is of finite presentation, and `F_iso` is all of `B`, so `Z = B` is
not of finite presentation over `S`.  The sentence is the scheme version, Stacks 05PF, copied
over: there the base of the situation is called `S`.  The proof deduces the clause from the
finite-presentation clause of Stacks 0CWC, which is about `F_zero ⟶ B`.  It is formalized here
as finite presentation of `Z ⟶ B`.

Purity of `ℱ` relative to `B` is `AlgebraicGeometry.Space.IsPureRelative`, Stacks 0CVD
part (5), of the situation `fpSourcePrePureSituation`.  The finite-type and decency conditions of
that situation are derived from (1) and (2), exactly as for the target module in Stacks 0CWC
(`AlgebraicGeometry.Space.ModuleMapSituation.fpTargetPrePureSituation`).  The point of the base
is a parameter because the situation of Stacks 0CV6 carries one, and the hypothesis quantifies
over it.

## References

* [Stacks Project, Tag 0CWD](https://stacks.math.columbia.edu/tag/0CWD)
* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
* [Stacks Project, Tag 0CVM](https://stacks.math.columbia.edu/tag/0CVM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The situation of Stacks 0CV6 formed by the morphism `f` of Stacks 083F and the **source**
module `ℱ` of the map, at a point `y` of the base, when `f` and `ℱ` are of finite presentation:
the morphism is of finite type and decent, and the module of finite type, because finite
presentation gives all three.  Purity of `ℱ` relative to `B`, hypothesis (2) of Stacks 0CWD, is
`AlgebraicGeometry.Space.IsPureRelative` of this situation. -/
abbrev fpSourcePrePureSituation (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F) (y : points B S hS D.Y.1) :
    PrePureSituation.{u, u} B S hS where
  X := D.X.1
  Y := D.Y.1
  hX := D.X.2
  hY := D.Y.2
  f := D.f.hom
  finiteType := isFiniteType_of_isFinitePresentation B S hS hf
  decent := isDecent_of_isFinitePresentation B S hS D.f hf
  F := D.F
  moduleFiniteType := SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite D.F
  moduleQuasicoherent := D.quasicoherent_F
  y := y

/-- The source module of a situation is the target module of its kernel situation, so the
purity situation of the source is that of the target of the kernel situation, on the nose. -/
theorem fpSourcePrePureSituation_eq_kernelSituation (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F) (y : points B S hS D.Y.1) :
    D.fpSourcePrePureSituation hf hFfp y =
      (D.kernelSituation).fpTargetPrePureSituation hf hFfp y :=
  rfl

/-- **Stacks 0CWD.**  In Situation 083F, assume (1) `f` is of finite presentation, (2) `ℱ` is of
finite presentation, flat over `B` and pure relative to `B`, and (3) `u` is surjective.  Then
`F_iso` is representable by a closed immersion `Z ⟶ B`: there is a closed subspace `Z` of `B`
such that a scheme `T` over `B` lies in `F_iso` — the base change `u_T` is an isomorphism —
exactly when its structure morphism factors through `Z`.  Moreover `Z ⟶ B` is of finite
presentation if `𝒢` is of finite presentation.

The source writes `Z ⟶ S` in the last sentence, which is false as written; its proof gives
`Z ⟶ B`, and that is what is stated.  See the implementation notes of this file. -/
@[stacks 0CWD "F_iso is represented by a closed subspace Z of the base, and Z → B is of finite \
presentation when 𝒢 is of finite presentation (the source's 'Z → S' is a misprint for Z → B, \
see the module notes)"]
theorem isoLocusRepresentation_of_isPureRelative
    (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hFflat : _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.F)
    (hpure : ∀ y : points B S hS D.Y.1, IsPureRelative (D.fpSourcePrePureSituation hf hFfp y))
    [Epi D.u] :
    D.IsoLocusRepresentation :=
  D.isoLocusRepresentation_of_kernelSituation
    (SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite D.F)
    ((D.kernelSituation).zeroLocusRepresentation_of_isClosedSubspace
      (isClosedSubspace_zeroSubfunctor_of_isPureRelative B S hS D.kernelSituation hf hFfp hFflat
        hpure)
      (isFinitePresentation_zeroSubfunctor_ι_of_isPureRelative B S hS D.kernelSituation hf hFfp
        hFflat hpure))

end AlgebraicGeometry.Space.ModuleMapSituation

end
