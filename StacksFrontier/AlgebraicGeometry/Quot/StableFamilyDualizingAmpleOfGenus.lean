module

public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyAmpleDualizingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableHasGenusIff
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof

/-!
# Ampleness of a fibrewise dualizing module near a point of a prestable family of genus `g ≥ 2`

`CurveFamily.hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of_openAmpleLocus`
proves the argument of Stacks 0E74 from two inputs of the family side, the open locus of relative
ampleness and the fibre reading of prestability, and with the genus condition read on the fibres.
All three hold:

* `AlgebraicGeometry.openAmpleLocus`: the open locus of relative ampleness, which is Stacks 0D3D
  (`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`) at
  the base `Spec ℤ`;
* `AlgebraicGeometry.prestableFibreReading`: a fibre of a prestable family over the residue field
  of a point is at-worst-nodal, of dimension one, with `H⁰ = κ(s)`
  (`AlgebraicGeometry.C1590Private.fibre_properties_of_isPrestableCurveFamily`);
* `AlgebraicGeometry.CurveFamily.hasFibreGenus_of_hasGenus`: a prestable family of genus `g`, that
  is with `R¹f_*𝒪_X` finite locally free of rank `g` (Stacks 0E6V), has all its fibres of genus
  `g` (`AlgebraicGeometry.C1590Private.hasGenus_iff_hasFibresOfGenus_of`, with the étale local
  scheme charts of Stacks 0E6F).

## Main results

* `hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of_isDualizingOnFibres`:
  for a prestable family of curves `X → S` of genus `g ≥ 2`, an invertible module `ω` on `X` which
  restricts on every fibre to its dualizing sheaf, and a point `s ∈ S`, the fibre `X_s` has no
  rational tail and no rational bridge exactly when `ω` is ample on `f⁻¹(U)` relative to `U` for
  some open `U ∋ s`.

## Implementation notes

The module `ω` is an argument: the relative dualizing sheaf `ω_{X/S}` of Stacks 0E6Q is such a
module (Stacks 0E6R and the identification over a field in Section 0E6N), and the statement holds
for every such module.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The open locus of relative ampleness** (`AlgebraicGeometry.OpenAmpleLocus`) holds: it is
Stacks 0D3D over `Spec ℤ`. -/
theorem openAmpleLocus : OpenAmpleLocus B hZ := fun _ _ _ hf _ hL =>
  Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper B integerBase hZ hf hL

/-- **The fibre reading of prestability** (`AlgebraicGeometry.PrestableFibreReading`) holds: a
fibre of a prestable family of curves over the residue field of a point of the base is
at-worst-nodal, of dimension one, with `H⁰ = κ(s)`. -/
theorem prestableFibreReading : PrestableFibreReading B hZ := by
  intro X hX s V v q h
  obtain ⟨-, hdim, hiso, hnod⟩ := C1590Private.fibre_properties_of_isPrestableCurveFamily hX
    (X.residueFieldPoint s) v q (by rw [C1590Private.yonedaEquiv_symm_value]; exact h)
  have : IsIso ((Scheme.ΓSpecIso (.of (((BigFppfOver.toScheme B integerBase hZ).obj
      X.base).residueField s))).inv ≫ (CurveFamily.fibreMap B hZ X s v).appTop) := hiso
  have : IsIso (CurveFamily.fibreMap B hZ X s v).appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso _).inv _
  exact ⟨hnod, hdim, ConcreteCategory.bijective_of_isIso _⟩

variable {B hZ}

namespace CurveFamily

/-- **The fibres of a prestable family of genus `g` have genus `g`.** If `R¹f_*𝒪_X` is finite
locally free of rank `g`, every scheme presenting the fibre over the residue field of a point of
the base has genus `g`. -/
theorem hasFibreGenus_of_hasGenus {X : CurveFamily B hZ} (hX : IsPrestableCurveFamily B hZ X)
    {g : ℕ} (hgen : CurveFamily.HasGenus B hZ X g) : X.HasFibreGenus B hZ g := by
  have hfib := (C1590Private.hasGenus_iff_hasFibresOfGenus_of
    (C1590Private.hasEtaleLocalSchemeCharts B hZ) X hX g).1 hgen
  intro s V v q h
  exact (hfib (X.residueFieldPoint s)).genus_eq v q
    (by rw [C1590Private.yonedaEquiv_symm_value]; exact h)

/-- **The argument of Stacks 0E74 for a fibrewise dualizing module.** Let `f : X → S` be a
prestable family of curves of genus `g ≥ 2` (`R¹f_*𝒪_X` finite locally free of rank `g`), let `ω`
be an invertible module on `X` restricting on every fibre to its dualizing sheaf, and let `s ∈ S`.
The following are equivalent:

1. the fibre `X_s` (presented by a scheme of the site) has no rational tail and no rational
   bridge;
2. there is an open `U ∋ s` of `S` such that `ω` is ample on `f⁻¹(U)` relative to `U`: on every
   base change of `f` along `U ⊆ S` the pullback of `ω` is relatively ample. -/
theorem hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of_isDualizingOnFibres
    (X : CurveFamily B hZ) (hX : IsPrestableCurveFamily B hZ X) (g : ℕ)
    (hgen : CurveFamily.HasGenus B hZ X g) (hg : 2 ≤ g)
    (ω : Space.Modules.{u, u} B integerBase hZ X.total.obj X.total.property)
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property ω)
    (hω : X.IsDualizingOnFibres B hZ ω)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    (∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ X.residuePoint B hZ s)
        (q : yoneda.obj V ⟶ X.total.obj),
        X.IsFibrePresentation B hZ s v q ∧
          HasNoRationalTailNoRationalBridge
            (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
            (X.fibreMap B hZ s v)) ↔
      ∃ U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens, s ∈ U ∧
        ∀ ⦃X₁ : AlgebraicSpaces B integerBase hZ⦄ (p₁ : X₁ ⟶ X.total)
          (f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)),
          IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)) →
            Space.IsRelativelyAmple B integerBase hZ f₁
              ((Space.modulePullback B integerBase hZ p₁).obj ω) :=
  hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of_openAmpleLocus
    (openAmpleLocus B hZ) (prestableFibreReading B hZ) X hX g (hasFibreGenus_of_hasGenus hX hgen)
    hg ω hωinv hω s

end CurveFamily

end AlgebraicGeometry

end
