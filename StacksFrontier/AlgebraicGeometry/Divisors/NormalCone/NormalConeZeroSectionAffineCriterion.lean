module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalPushforwardSections
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeZeroSectionFactor
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.PairComposition
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# The factorization through the zero section of a normal cone, checked on affine opens

Let `D ⊆ X` be an effective Cartier divisor, so that the normal cone `C_DX` is a line bundle over
`D` with zero section `o : D ⟶ C_DX`.
`Stacks.Conormal.eq_comp_normalConeZeroSection_iff` turns the factorization of a morphism
`m : T ⟶ C_DX` through `o` into the vanishing of one morphism of `𝒪_D`-modules — the module
component of the relative-spectrum pair that the functor of points of the total space of the
conormal line bundle attaches to `m`. That morphism of modules has to be checked over *every*
open of `D`, while everything the library can compute about the pair of a morphism of relative
spectra — `Stacks.RelativeSpec.pairToHom_appLE` and its specializations — is stated over the
**affine** opens of the base only.

This file restates the criterion as a condition over the affine opens of `D` alone.

## Main results

* `Stacks.RelativeSpec.algebraHomPair` and
  `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_eq_pairToHom`: the morphism of relative
  spectra induced by a morphism of algebras on one base is `Stacks.RelativeSpec.pairToHom` of a
  named pair, so `Stacks.RelativeSpec.comp_pairToHom` applies to a composite ending in it.
* `Stacks.LineBundle.Situation.totalSpaceHomEquiv_snd_eq_zero_iff`: **the module component of the
  pair attached to `pairToHom q` vanishes exactly when the module morphism read off `q` does.**
  This is the `.2` extraction from the round-trip identity of [Stacks, Tag 01LV], as an `Iff`
  between two equations in fixed modules.
* `Stacks.LineBundle.Situation.algebraPairEquiv_eq_zero_iff`: **the module morphism read off an
  algebra datum vanishes exactly when the datum kills the degree-one homogeneous sections over
  the affine opens of the base.**
* `Stacks.LineBundle.Situation.vectorBundlePair`,
  `Stacks.LineBundle.Situation.vectorBundleToTotalSpace_eq_pairToHom` and
  `Stacks.LineBundle.Situation.totalSpaceHomEquiv_comp_vectorBundleToTotalSpace_snd_eq_zero_iff`:
  the same for a morphism into the total space written through the vector bundle of the line
  bundle.
* `Stacks.Conormal.totalSpaceIsoNormalCone_inv_eq`: the inverse of the identification of the
  total space with the normal cone is `Stacks.Conormal.normalConeToNormalBundle` followed by
  `Stacks.LineBundle.Situation.vectorBundleToTotalSpace`.
* `Stacks.Conormal.eq_comp_normalConeZeroSection_iff_affineOpens` and
  `Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection_iff_affineOpens`: **the
  factorization through the zero section, as a condition on the sections over the affine opens of
  the divisor in degree one.** The second is the form for the composite
  `C_ZY ⟶ C_ZX ⟶ C_YX` of a nested pair of closed immersions.

## Implementation notes

The passage from every open to the affine opens is
`Stacks.BasisRestriction.moduleSheafHom_ext_onBasis` ([Stacks, Tag 009U]) at the basis of affine
opens, `AlgebraicGeometry.Scheme.isBasis_affineOpens`.

`Stacks.LineBundle.Situation.totalSpaceHomEquiv_pairToHom` is an equation between two terms of a
`Σ`-type whose first components agree only propositionally; the goals here mention the pair only
through `Sigma.snd` and the `0` of the module that `Sigma.fst` names, so it applies as an
ordinary rewrite. Where `congrArg` and `iff_of_eq` replace a rewrite, it is because
`AlgebraSheaf D.X` and `AlgebraSheaf D.relativeSpecSituation.base` agree only after unfolding
`Stacks.LineBundle.Situation.relativeSpecSituation`, which `rw` does not do.

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeSpec

universe u


namespace Stacks.RelativeSpec

variable (s : RelativeSpecSituation.{u}) (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent)
  (ψ : s.algebra ⟶ B)

/-- **The relative-spectrum pair of the comparison induced by a morphism of algebras on one
base**: the structure morphism of the relative spectrum of the second algebra, together with that
algebra's universal map precomposed with `ψ`. -/
def algebraHomPair : RelativeSpecPair s (gluedSpectrum (s.withAlgebra B hB)).scheme :=
  ⟨(gluedSpectrum (s.withAlgebra B hB)).toBase,
    algebraHomAsUnder ψ ≫ universalAlgebraMap (s.withAlgebra B hB)⟩

/-- **The comparison of relative spectra along a morphism of algebras is the morphism attached to
`Stacks.RelativeSpec.algebraHomPair`.** -/
theorem relativeSpectrumMapOfAlgebraHom_eq_pairToHom :
    relativeSpectrumMapOfAlgebraHom s B hB ψ = pairToHom (algebraHomPair s B hB ψ) := rfl

end Stacks.RelativeSpec

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The module component of the pair attached to the morphism of a relative-spectrum pair
vanishes exactly when the module morphism read off that pair does.** This is the round-trip
identity `Stacks.LineBundle.Situation.totalSpaceHomEquiv_pairToHom` of [Stacks, Tag 01LV] with
both sides' second components compared inside one fixed module. -/
theorem Situation.totalSpaceHomEquiv_snd_eq_zero_iff {T : Scheme.{u}}
    (q : RelativeSpecPair D.relativeSpecSituation T) :
    (D.totalSpaceHomEquiv T (pairToHom q)).2 = 0 ↔ D.algebraPairEquiv q.1 q.2 = 0 := by
  rw [Situation.totalSpaceHomEquiv_pairToHom]

/-- **The morphism of `𝒪_X`-modules `L ⟶ g_* 𝒪_T` read off an algebra datum vanishes exactly when
the datum kills the degree-one homogeneous sections over the affine opens of `X`.** -/
theorem Situation.algebraPairEquiv_eq_zero_iff {T : Scheme.{u}} (g : T ⟶ D.X)
    (φ : Under.mk D.algebraSheaf.hom.hom ⟶ Under.mk g.c) :
    D.algebraPairEquiv g φ = 0 ↔
      ∀ (U : D.X.affineOpens) (x : D.L.val.obj (op U.1)),
        (φ.right.app (op U.1)).hom
          (D.algebraSheafIncl 1 U.1 (D.symmetricAlgebraGen.val.app (op U.1) x)) = 0 := by
  have key (ψ : D.L ⟶ (Scheme.Modules.pushforward g).obj
        (SheafOfModules.unit T.ringCatSheaf))
      (hψ : ∀ U : D.X.affineOpens,
        (D.algebraPairEquiv g φ).val.app (op U.1) = ψ.val.app (op U.1)) :
      D.algebraPairEquiv g φ = ψ :=
    Stacks.BasisRestriction.moduleSheafHom_ext_onBasis D.L _
      (fun U : D.X.affineOpens => U.1)
      (by rw [Subtype.range_coe]; exact D.X.isBasis_affineOpens) _ ψ hψ
  refine ⟨fun h U x => ?_, fun h => key 0 fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
  · rw [← D.algebraPairEquiv_val_app g φ U.1 x, h]
    rfl
  · rw [D.algebraPairEquiv_val_app g φ U.1 x, h U x]
    rfl

/-- **The relative-spectrum pair of the comparison from the vector bundle of the line bundle to
the total space.** The comparison is induced by
`Stacks.LineBundle.Situation.algebraSheafIsoSymmetricAlgebraSheaf`, so this is
`Stacks.RelativeSpec.algebraHomPair` of that isomorphism. -/
abbrev Situation.vectorBundlePair :
    RelativeSpecPair D.relativeSpecSituation
      (gluedSpectrum (D.relativeSpecSituation.withAlgebra
        (AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf D.X D.L)
        D.isQuasicoherent_symmetricAlgebraSheaf)).scheme :=
  algebraHomPair D.relativeSpecSituation
    (AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf D.X D.L)
    D.isQuasicoherent_symmetricAlgebraSheaf D.algebraSheafIsoSymmetricAlgebraSheaf.hom

/-- The comparison from the vector bundle to the total space is the morphism attached to
`Stacks.LineBundle.Situation.vectorBundlePair`. -/
theorem Situation.vectorBundleToTotalSpace_eq_pairToHom :
    D.vectorBundleToTotalSpace = pairToHom D.vectorBundlePair := rfl

/-- **The module component of the pair attached to a morphism into the total space factored
through the vector bundle vanishes exactly when the pulled-back algebra datum kills the degree-one
homogeneous sections over the affine opens of the base.** -/
theorem Situation.totalSpaceHomEquiv_comp_vectorBundleToTotalSpace_snd_eq_zero_iff
    {T : Scheme.{u}} (k : T ⟶ AlgebraicGeometry.Scheme.Modules.vectorBundle D.X D.L) :
    (D.totalSpaceHomEquiv T (k ≫ D.vectorBundleToTotalSpace)).2 = 0 ↔
      ∀ (U : D.X.affineOpens) (x : D.L.val.obj (op U.1)),
        ((RelativeSpecPair.pullback k D.vectorBundlePair).2.right.app (op U.1)).hom
          (D.algebraSheafIncl 1 U.1 (D.symmetricAlgebraGen.val.app (op U.1) x)) = 0 := by
  refine Iff.trans (iff_of_eq (congrArg
    (fun z : T ⟶ D.totalSpace => ((D.totalSpaceHomEquiv T z).2 = 0))
    ((congrArg (k ≫ ·) D.vectorBundleToTotalSpace_eq_pairToHom).trans
      (comp_pairToHom k D.vectorBundlePair)))) ?_
  exact (D.totalSpaceHomEquiv_snd_eq_zero_iff _).trans (D.algebraPairEquiv_eq_zero_iff _ _)

end Stacks.LineBundle

namespace Stacks.Conormal

variable {X : Scheme.{u}} (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra D.subschemeι)]
  [(conormalAlgebraSheaf D.subschemeι).IsQuasicoherent]

/-- **The inverse of the identification of the total space of the conormal line bundle with the
normal cone is the Tag 0637 morphism `C_DX ⟶ N_DX` followed by the comparison from the vector
bundle to the total space.** -/
theorem totalSpaceIsoNormalCone_inv_eq :
    (totalSpaceIsoNormalCone D).inv =
      normalConeToNormalBundle D.subschemeι ≫
        (conormalSituation D).vectorBundleToTotalSpace :=
  rfl

/-- **A morphism into the normal cone of an effective Cartier divisor factors through the zero
section exactly when one algebra datum kills the degree-one homogeneous sections over the affine
opens of the divisor.**

This is `Stacks.Conormal.eq_comp_normalConeZeroSection_iff` with its right-hand side — a morphism
of `𝒪_D`-modules which has to vanish over every open — replaced by a condition over the affine
opens only. -/
theorem eq_comp_normalConeZeroSection_iff_affineOpens {T : Scheme.{u}}
    (m : T ⟶ normalCone D.subschemeι) (g : T ⟶ D.subscheme)
    (hbase : m ≫ normalConeToBase D.subschemeι = g) :
    m = g ≫ normalConeZeroSection D ↔
      ∀ (U : D.subscheme.affineOpens)
        (x : (conormalSheafDegreeOne D.subschemeι).val.obj (op U.1)),
        ((RelativeSpecPair.pullback (m ≫ normalConeToNormalBundle D.subschemeι)
            (conormalSituation D).vectorBundlePair).2.right.app (op U.1)).hom
          ((conormalSituation D).algebraSheafIncl 1 U.1
            ((conormalSituation D).symmetricAlgebraGen.val.app (op U.1) x)) = 0 := by
  have hassoc : m ≫ (totalSpaceIsoNormalCone D).inv =
      (m ≫ normalConeToNormalBundle D.subschemeι) ≫
        (conormalSituation D).vectorBundleToTotalSpace :=
    (congrArg (m ≫ ·) (totalSpaceIsoNormalCone_inv_eq D)).trans (Category.assoc _ _ _).symm
  rw [eq_comp_normalConeZeroSection_iff D m g hbase, hassoc]
  exact Stacks.LineBundle.Situation.totalSpaceHomEquiv_comp_vectorBundleToTotalSpace_snd_eq_zero_iff
    (conormalSituation D) _

/-! ### The form the nested pair of divisors needs -/

section Nested

variable {X : Scheme.{u}} (DY : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra DY.subschemeι)]
  [(conormalAlgebraSheaf DY.subschemeι).IsQuasicoherent]
  {Z : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ]
  [(conormalAlgebraSheaf iZ).IsQuasicoherent]
  (f : Z ⟶ DY.subscheme) [IsClosedImmersion f]
  [(conormalAlgebraSheaf f).IsQuasicoherent] (hf : f ≫ DY.subschemeι = iZ)

/-- **The factorization of `C_ZY ⟶ C_ZX ⟶ C_YX` through the zero section `o : Y ⟶ C_YX` is
equivalent to one vanishing on the sections over the affine opens of `Y` in degree one.**

This is `Stacks.Conormal.normalConeNested_eq_comp_normalConeZeroSection_iff` with its
module-morphism condition reduced to the affine opens of the base. -/
theorem normalConeNested_eq_comp_normalConeZeroSection_iff_affineOpens :
    normalConeMapOfSquare f iZ (𝟙 Z) DY.subschemeι ((Category.id_comp iZ).trans hf.symm) ≫
          normalConeMapOfFactorization iZ DY.subschemeι f hf =
        normalConeToBase f ≫ f ≫ normalConeZeroSection DY ↔
      ∀ (U : DY.subscheme.affineOpens)
        (x : (conormalSheafDegreeOne DY.subschemeι).val.obj (op U.1)),
        ((RelativeSpecPair.pullback
            ((normalConeMapOfSquare f iZ (𝟙 Z) DY.subschemeι
                  ((Category.id_comp iZ).trans hf.symm) ≫
                normalConeMapOfFactorization iZ DY.subschemeι f hf) ≫
              normalConeToNormalBundle DY.subschemeι)
            (conormalSituation DY).vectorBundlePair).2.right.app (op U.1)).hom
          ((conormalSituation DY).algebraSheafIncl 1 U.1
            ((conormalSituation DY).symmetricAlgebraGen.val.app (op U.1) x)) = 0 := by
  rw [← Category.assoc (normalConeToBase f) f (normalConeZeroSection DY)]
  exact eq_comp_normalConeZeroSection_iff_affineOpens DY _ _
    (normalConeNested_comp_normalConeToBase DY iZ f hf)

end Nested

end Stacks.Conormal

end
