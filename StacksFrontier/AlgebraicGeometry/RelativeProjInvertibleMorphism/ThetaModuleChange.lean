module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ModuleChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaTargetChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

/-!
# The map `θ` of Tag 01O9 under an isomorphism of the invertible module

Let `f : X ⟶ S` be a morphism of schemes, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an
invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of graded algebras, with the
open `U(ψ)`, the morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` and the map of graded algebras
`θ : r^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` of [Stacks, Tag 01O9].  An isomorphism `e : ℒ ≅ ℒ'`
transports `ψ` to `ψ' = e ∘ ψ` (`…RelativeProjQcohSheaf.Twisting.congrModule`), and
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/ModuleChange.lean` shows
`U(ψ') = U(ψ)` and `r_{ℒ',ψ'} = r_{ℒ,ψ}`.  This file proves the companion statement for `θ`:
**`θ_{ψ'}` is `θ_ψ` followed by the isomorphism `⨁_d ℒ^{⊗ d} ≅ ⨁_d ℒ'^{⊗ d}` that `e` induces**,
read through the canonical identifications of the sources and of the opens.

## Main definitions

* `…RelativeProjInvertibleMorphism.laurentOnCongrIso`: `⨁_d ℒ^{⊗ d}|_U ≅ ⨁_d ℒ'^{⊗ d}|_U`, the
  restriction to an open of the isomorphism of Laurent algebras induced by `e`
  (`…LaurentAlgebraCongr.laurentCongrIso`).
* `…RelativeProjInvertibleMorphism.GradedPowerMap.thetaTransportHom`: `θ_P` read along an open
  `U₁ ⊆ U(P)`, a morphism `r' : U₁ ⟶ Proj_S(𝒜)` with `j ≫ r_P = r'`, and an isomorphism of the
  invertible modules.

## Main results

* `…RelativeProjInvertibleMorphism.homOfLE_globalMorphism_congrModule`: `j ≫ r_ψ = r_{e ∘ ψ}` for
  the identification `j : U(e ∘ ψ) ⟶ U(ψ)` of the two equal opens.
* `…RelativeProjInvertibleMorphism.powCompare_value_congrModule`: the values of `e ∘ ψ` are those
  of `ψ` transported by `e`.
* `…RelativeProjInvertibleMorphism.theta_congrModule_clauseOne`: `θ_{e ∘ ψ}` takes, on the
  sections `ψ_{Proj}(a)` that characterize it, the values of `θ_ψ` transported by `e`.
* `…RelativeProjInvertibleMorphism.theta_congrModule`: **`θ_{e ∘ ψ}` is `θ_ψ` read along
  `U(e ∘ ψ) = U(ψ)` and followed by the isomorphism induced by `e`**, as maps of graded algebras.

## Implementation notes

The identity `theta_congrModule` is proved through the characterization of `θ` by clause (1)
(`GradedPowerMap.eq_theta_of_clauseOne`), after evaluating the transported map on the sections that
characterize it (`thetaTransport_clauseOne`).  That evaluation is carried out with the open `U₁`
and the morphism `r'` free variables, and instantiated at `U(e ∘ ψ)` and `r_{e ∘ ψ}` only in the
final statement.  Written at `U(e ∘ ψ)` directly, every kernel check of the evaluation exceeds the
kernel's budget: the open `U(e ∘ ψ)` then occurs in the types of the sections spelled both as
`Scheme.Opens` and as `TopologicalSpace.Opens` of the underlying space, and reconciling the two
spellings makes the kernel unfold `U(e ∘ ψ)`; the transport along `j ≫ r_ψ = r_{e ∘ ψ}` likewise
must not be reduced.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

open GradedPowerMap (twD Otw psiU)

/-! ### `⨁_d ℒ^{⊗ d}|_U ≅ ⨁_d ℒ'^{⊗ d}|_U` -/

section LaurentOnCongr

variable {T : Scheme.{u}} {L L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  [Stacks.Ample.IsInvertibleModule T L'] (e : L ≅ L') (U : T.Opens)

/-- `ℒ^{⊗ n}|_U ≅ ℒ'^{⊗ n}|_U`, the restriction of the comparison of the integral tensor powers
induced by `e`. -/
def laurentOnCongrPieceIso (n : ℤ) : (laurentOn L U).piece n ≅ (laurentOn L' U).piece n :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso (LaurentCongr.congrIso e n)

/-- **`⨁_d ℒ^{⊗ d}|_U ≅ ⨁_d ℒ'^{⊗ d}|_U`** as sheaves of graded algebras: the restriction to `U`
of the isomorphism of Laurent algebras induced by `e`. -/
def laurentOnCongrIso : laurentOn L U ≅ laurentOn L' U :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso (A := laurentOn L U) (B := laurentOn L' U)
    (fun n => laurentOnCongrPieceIso e U n)
    (fun i k W x y =>
      (LaurentAlgebraCongr.laurentCongrIso e).hom.map_mul i k (op (U.ι ''ᵁ W.unop)) x y)

/-- The degree-`n` component of `laurentOnCongrIso` is `laurentOnCongrPieceIso`. -/
theorem laurentOnCongrIso_hom_app (n : ℤ) :
    (laurentOnCongrIso e U).hom.app n = (laurentOnCongrPieceIso e U n).hom :=
  rfl

end LaurentOnCongr

/-! ### `θ` under `ℒ ≅ ℒ'` -/

section Theta

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L] [Stacks.Ample.IsInvertibleModule T L']
  (ψ : Twisting f (situationAlgebra A) 1 L) (e : L ≅ L')

/-- **The values of `e ∘ ψ` are the values of `ψ` transported by `e`**, in the form of
[Stacks, Tag 01O8]'s data. -/
theorem value_congrModule (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) :
    (natPowCongr e n).hom.app (f ⁻¹ᵁ V) ((toGradedPowerMap ψ).value n V a) =
      (toGradedPowerMap (ψ.congrModule e)).value n V a := by
  rw [toGradedPowerMap_value, toGradedPowerMap_value]
  exact valueSec_congrModule ψ e n V a

/-- `U(e ∘ ψ) ⊆ U(ψ)` (they are equal, `coveringOpen_congrModule`). -/
theorem coveringOpen_congrModule_le :
    (toGradedPowerMap (ψ.congrModule e)).coveringOpen ≤ (toGradedPowerMap ψ).coveringOpen :=
  (coveringOpen_congrModule ψ e).le

/-- **`j ≫ r_{ℒ,ψ} = r_{ℒ',e ∘ ψ}`** for the identification `j : U(e ∘ ψ) ⟶ U(ψ)` of the equal
opens. -/
theorem homOfLE_globalMorphism_congrModule :
    T.homOfLE (coveringOpen_congrModule_le ψ e) ≫
        (toGradedPowerMap ψ).globalMorphism (relativeProj A) =
      (toGradedPowerMap (ψ.congrModule e)).globalMorphism (relativeProj A) :=
  GradedPowerMap.homOfLE_globalMorphism_of_valueIso (toGradedPowerMap ψ)
    (toGradedPowerMap (ψ.congrModule e)) (natPowCongr e) (value_congrModule ψ e) (relativeProj A)

/-- **The value of `e ∘ ψ`, read in `ℒ'^{⊗ d}`, is the value of `ψ` read in `ℒ^{⊗ d}` and
transported by `e`.** -/
theorem powCompare_value_congrModule (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    (powCompare L' d).hom.app (f ⁻¹ᵁ V) ((toGradedPowerMap (ψ.congrModule e)).value d V a) =
      (LaurentCongr.congrIso e (d : ℤ)).hom.val.app (op (f ⁻¹ᵁ V))
        ((powCompare L d).hom.app (f ⁻¹ᵁ V) ((toGradedPowerMap ψ).value d V a)) :=
  (congrArg ((powCompare L' d).hom.app (f ⁻¹ᵁ V)) (value_congrModule ψ e d V a)).symm.trans
    (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app (powCompare L' d)
      (f ⁻¹ᵁ V) _)

/-- **`θ` is invariant under `ℒ ≅ ℒ'`, on the sections that characterize it**: for every open
`V` of the base, `d ≥ 0` and `a ∈ 𝒜_d(V)`, the map `θ_{e ∘ ψ}` of [Stacks, Tag 01O9] carries the
pullback of the section `ψ_{Proj}(a)` of `𝒪(d)` to `e(ψ(a))` restricted to `U(e ∘ ψ)`: the value
`θ_ψ` takes there (`GradedPowerMap.theta_clauseOne`), transported by the isomorphism
`ℒ^{⊗ d} ≅ ℒ'^{⊗ d}` induced by `e`.  Together with the characterization of `θ` by these values
(`GradedPowerMap.eq_theta_of_clauseOne`) this determines `θ_{e ∘ ψ}` from `θ_ψ` and `e`. -/
theorem theta_congrModule_clauseOne (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    ((toGradedPowerMap (ψ.congrModule e)).powK d).presheaf.map
        (eqToHom ((toGradedPowerMap (ψ.congrModule e)).toBase_preimage_eq V)).op
        (((toGradedPowerMap (ψ.congrModule e)).theta.app d).val.app
          (op ((toGradedPowerMap (ψ.congrModule e)).globalMorphism (relativeProj A) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V)))
          (pullbackUnit ((toGradedPowerMap (ψ.congrModule e)).globalMorphism
              (relativeProj A)).toLRSHom.toShHom
            (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a))) =
      (tensorPowerModule T L' d).presheaf.map
        (homOfLE ((toGradedPowerMap (ψ.congrModule e)).coveringOpen.ι.image_preimage_le
          (f ⁻¹ᵁ V))).op
        ((LaurentCongr.congrIso e (d : ℤ)).hom.val.app (op (f ⁻¹ᵁ V))
          ((powCompare L d).hom.app (f ⁻¹ᵁ V) ((toGradedPowerMap ψ).value d V a))) :=
  ((toGradedPowerMap (ψ.congrModule e)).theta_clauseOne V d a).trans
    (congrArg ((tensorPowerModule T L' d).presheaf.map
      (homOfLE ((toGradedPowerMap (ψ.congrModule e)).coveringOpen.ι.image_preimage_le
        (f ⁻¹ᵁ V))).op) (powCompare_value_congrModule ψ e V d a))

end Theta


/-! ### `θ` transported along an open `U₁ ⊆ U(P)` and an isomorphism of the invertible modules

For a datum `P` of Tag 01O8, an open `U₁ ⊆ U(P)`, a morphism `r' : U₁ ⟶ Proj_S(𝒜)` with
`j ≫ r_P = r'` and an isomorphism `e : ℒ_P ≅ ℒ'`, the map `θ_P` read along `j` and `e` is a map of
graded algebras `r'^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ'^{⊗ d}|_{U₁}` (`GradedPowerMap.thetaTransportHom`). The
open `U₁` and the morphism `r'` are kept variables while the transported map is evaluated on
sections, and are instantiated at `U(e ∘ ψ)` and `r_{e ∘ ψ}` only at the end: the kernel then never
has to compare the glued morphisms `j ≫ r_ψ` and `r_{e ∘ ψ}`, nor to unfold the open `U(e ∘ ψ)`. -/

namespace GradedPowerMap

section Transport

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  (P : GradedPowerMap A f) {L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L']
  (e : P.L ≅ L') {U₁ : T.Opens} (hU : U₁ ≤ P.coveringOpen)
  {r' : U₁.toScheme ⟶ (relativeProj A).scheme}
  (hr : T.homOfLE hU ≫ P.globalMorphism (relativeProj A) = r')

/-- `j^*r_P^*(⨁_d 𝒪(d)) ≅ r'^*(⨁_d 𝒪(d))` along `j ≫ r_P = r'`, for the inclusion
`j : U₁ ⟶ U(P)`: the pseudofunctoriality of the inverse image of graded algebras, followed by the
congruence along `j ≫ r_P = r'`. -/
def thetaTransportSourceIso :
    Stacks.Conormal.gradedPullback (T.homOfLE hU)
        (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A)) (twD A).algebra) ≅
      Stacks.Conormal.gradedPullback r' (twD A).algebra :=
  Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso
      (twD A).algebra (T.homOfLE hU) (P.globalMorphism (relativeProj A)) ≪≫
    Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso
      (twD A).algebra hr

/-- `j^*(⨁_d ℒ^{⊗ d}|_{U(P)}) ≅ ⨁_d ℒ'^{⊗ d}|_{U₁}`: the restriction along `U₁ ⊆ U(P)`, followed
by the isomorphism induced by `e`. -/
def thetaTransportTargetIso :
    Stacks.Conormal.gradedPullback (T.homOfLE hU) (laurentOn P.L P.coveringOpen) ≅
      laurentOn L' U₁ :=
  laurentOnHomOfLEIso P.L hU ≪≫ laurentOnCongrIso e U₁

/-- **`θ_P` transported to `U₁`**: `θ_P` read along `j : U₁ ⟶ U(P)` and `j ≫ r_P = r'`, followed
by the isomorphism `⨁_d ℒ^{⊗ d} ≅ ⨁_d ℒ'^{⊗ d}` induced by `e`. -/
def thetaTransportHom :
    SheafOfModules.GradedAlgebra.Hom (Stacks.Conormal.gradedPullback r' (twD A).algebra)
      (laurentOn L' U₁) :=
  (P.thetaTransportSourceIso hU hr).inv ≫
    pullbackGradedAlgebraMap (T.homOfLE hU).toLRSHom.toShHom P.theta ≫
      (P.thetaTransportTargetIso e hU).hom

/-- The degree-`d` component of `thetaTransportHom`. -/
theorem thetaTransportHom_app (d : ℤ) :
    (P.thetaTransportHom e hU hr).app d =
      ((Scheme.Modules.pullbackCongr hr).inv.app (Otw A d) ≫
        (Scheme.Modules.pullbackComp (T.homOfLE hU)
          (P.globalMorphism (relativeProj A))).inv.app (Otw A d)) ≫
        (Scheme.Modules.pullback (T.homOfLE hU)).map
          (X := (Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj (Otw A d))
          (Y := (laurentOn P.L P.coveringOpen).piece d) (P.theta.app d) ≫
        (laurentOnHomOfLEPieceIso P.L hU d).hom ≫ (laurentOnCongrPieceIso e U₁ d).hom := by
  subst hr
  simp only [thetaTransportHom, thetaTransportSourceIso, thetaTransportTargetIso, Iso.trans_hom,
    Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso,
    SheafOfModules.GradedAlgebra.categoryStruct_comp_app, laurentOnHomOfLEIso, laurentOnCongrIso]
  rfl

omit [Stacks.Ample.IsInvertibleModule T L'] in
include hr in
/-- `r'^{-1}(π^{-1}(V)) ⊆ j^{-1}(r_P^{-1}(π^{-1}(V)))`. -/
theorem preimage_le_of_homOfLE_comp_eq (V : S.Opens) :
    r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      T.homOfLE hU ⁻¹ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) := by
  subst hr
  exact le_rfl

omit [Stacks.Ample.IsInvertibleModule T L'] in
include hr in
/-- `r'^{-1}(π^{-1}(V)) ⊆ (j ≫ r_P)^{-1}(π^{-1}(V))`. -/
theorem preimage_le_comp_of_homOfLE_comp_eq (V : S.Opens) :
    r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      (T.homOfLE hU ≫ P.globalMorphism (relativeProj A)) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) := by
  subst hr
  exact le_rfl

end Transport

end GradedPowerMap

/-! ### `θ` under `ℒ ≅ ℒ'`, as a morphism -/

section ThetaCongr

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L] [Stacks.Ample.IsInvertibleModule T L']
  (ψ : Twisting f (situationAlgebra A) 1 L) (e : L ≅ L') {U₁ : T.Opens}
  (hU : U₁ ≤ (toGradedPowerMap ψ).coveringOpen) {r' : U₁.toScheme ⟶ (relativeProj A).scheme}
  (hr : T.homOfLE hU ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A) = r')

omit [Stacks.Ample.IsInvertibleModule T L'] in
/-- `θ_ψ` read along `j` and `j ≫ r_ψ = r'`, on a pulled-back homogeneous section: the
restriction of `ψ(a)`. -/
theorem thetaTransport_restrict_app_pullbackUnit (V : S.Opens) (d : ℕ)
    (a : Γ(A.piece (d : ℤ), V)) :
    (laurentOnHomOfLEPieceIso L hU d).hom.val.app (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
        (((Scheme.Modules.pullback (T.homOfLE hU)).map
            (X := (Scheme.Modules.pullback ((toGradedPowerMap ψ).globalMorphism
              (relativeProj A))).obj (Otw A d))
            (Y := (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d)
            ((toGradedPowerMap ψ).theta.app d)).val.app (op
              (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
          (((Scheme.Modules.pullbackComp (T.homOfLE hU) ((toGradedPowerMap ψ).globalMorphism
            (relativeProj A))).inv.app (Otw A d)).val.app (op
              (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
            (((Scheme.Modules.pullbackCongr hr).inv.app (Otw A d)).val.app
              (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
              (pullbackUnit r'.toLRSHom.toShHom (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
                (psiU A d V a))))) =
      (tensorPowerModule T L d).val.map (homOfLE (image_le_image_of_le_preimage_homOfLE hU _
        ((toGradedPowerMap ψ).preimage_le_of_homOfLE_comp_eq hU hr V))).op
        ((tensorPowerModule T L d).presheaf.map
          (homOfLE ((toGradedPowerMap ψ).image_preimage_preimage_le V)).op
          ((powCompare L d).hom.app (f ⁻¹ᵁ V) ((toGradedPowerMap ψ).value d V a))) := by
  have h4 := ((toGradedPowerMap ψ).preimage_le_of_homOfLE_comp_eq hU hr V)
  have h' := (toGradedPowerMap ψ).preimage_le_comp_of_homOfLE_comp_eq hU hr V
  have s1 : pullbackUnit r'.toLRSHom.toShHom (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
    (psiU A d V a) =
      pullbackSection r' (Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V) _ le_rfl (psiU A d V a) :=
    (Stacks.Conormal.pullbackSection_self r' (Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V)
      (psiU A d V a)).symm
  have s2 := pullbackSection_congr_inv hr (Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V) _ h' le_rfl
    (psiU A d V a)
  have s3 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection
    (T.homOfLE hU) ((toGradedPowerMap ψ).globalMorphism (relativeProj A)) (Otw A d)
      ((relativeProj A).toBase ⁻¹ᵁ V) _ _ le_rfl h4 h' (psiU A d V a)
  have s5 := laurentOnHomOfLE_theta_pullbackSection ψ hU d ((relativeProj A).toBase ⁻¹ᵁ V) _ h4
    (psiU A d V a)
  have s6 := (toGradedPowerMap ψ).thetaPush_psiU V d a
  rw [s1, s2, s3]
  refine s5.trans ?_
  exact congrArg ((tensorPowerModule T L d).val.map
    (homOfLE (image_le_image_of_le_preimage_homOfLE hU _ h4)).op) s6

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- An isomorphism of modules, restricted to an open, on a twice restricted section. -/
theorem restrictFunctor_mapIso_hom_val_app_map {M M' : T.Modules} (φ : M ≅ M') (U : T.Opens)
    {W : U.toScheme.Opens} {O O' : T.Opens} (hW : U.ι ''ᵁ W ≤ O') (h0 : O' ≤ O)
    (x : Γ(M, O)) (y : Γ(M', O)) (hxy : φ.hom.val.app (op O) x = y) :
    ((Scheme.Modules.restrictFunctor U.ι).mapIso φ).hom.val.app (op W)
        (M.val.map (homOfLE hW).op (M.presheaf.map (homOfLE h0).op x)) =
      M'.val.map (homOfLE hW).op (M'.presheaf.map (homOfLE h0).op y) := by
  subst hxy
  have s7 := PresheafOfModules.naturality_apply φ.hom.val (homOfLE hW).op
    (M.presheaf.map (homOfLE h0).op x)
  have s8 := PresheafOfModules.naturality_apply φ.hom.val (homOfLE h0).op x
  exact s7.trans (congrArg (M'.val.map (homOfLE hW).op) s8)

/-- The isomorphism induced by `e` on a restricted value of `ψ`: the restricted value of
`e ∘ ψ`. -/
theorem laurentOnCongrPieceIso_restrict_value (V : S.Opens) (d : ℕ)
    (a : Γ(A.piece (d : ℤ), V)) :
    (laurentOnCongrPieceIso e U₁ d).hom.val.app (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
      ((tensorPowerModule T L d).val.map (homOfLE (image_le_image_of_le_preimage_homOfLE hU _
        ((toGradedPowerMap ψ).preimage_le_of_homOfLE_comp_eq hU hr V))).op
        ((tensorPowerModule T L d).presheaf.map
          (homOfLE ((toGradedPowerMap ψ).image_preimage_preimage_le V)).op
          ((powCompare L d).hom.app (f ⁻¹ᵁ V) ((toGradedPowerMap ψ).value d V a)))) =
      (tensorPowerModule T L' d).val.map (homOfLE (image_le_image_of_le_preimage_homOfLE hU _
        ((toGradedPowerMap ψ).preimage_le_of_homOfLE_comp_eq hU hr V))).op
        ((tensorPowerModule T L' d).presheaf.map
          (homOfLE ((toGradedPowerMap ψ).image_preimage_preimage_le V)).op
          ((powCompare L' d).hom.app (f ⁻¹ᵁ V)
            ((toGradedPowerMap (ψ.congrModule e)).value d V a))) :=
  restrictFunctor_mapIso_hom_val_app_map (LaurentCongr.congrIso e (d : ℤ)) U₁ _
    ((toGradedPowerMap ψ).image_preimage_preimage_le V) _ _
    (powCompare_value_congrModule ψ e V d a).symm

/-- **`θ_ψ` transported to `U₁`, on a pulled-back homogeneous section**: the pullback along `r'` of
the section `ψ_{Proj}(a)` of `𝒪(d)` is carried to `e(ψ(a))`, restricted. -/
theorem thetaTransport_app_pullbackUnit (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    (laurentOnCongrPieceIso e U₁ d).hom.val.app (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
      ((laurentOnHomOfLEPieceIso L hU d).hom.val.app (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
        (((Scheme.Modules.pullback (T.homOfLE hU)).map
            (X := (Scheme.Modules.pullback ((toGradedPowerMap ψ).globalMorphism
              (relativeProj A))).obj (Otw A d))
            (Y := (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d)
            ((toGradedPowerMap ψ).theta.app d)).val.app (op
              (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
          (((Scheme.Modules.pullbackComp (T.homOfLE hU) ((toGradedPowerMap ψ).globalMorphism
            (relativeProj A))).inv.app (Otw A d)).val.app (op
              (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
            (((Scheme.Modules.pullbackCongr hr).inv.app (Otw A d)).val.app
              (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
              (pullbackUnit r'.toLRSHom.toShHom (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
                (psiU A d V a)))))) =
      (tensorPowerModule T L' d).val.map (homOfLE (image_le_image_of_le_preimage_homOfLE hU _
        ((toGradedPowerMap ψ).preimage_le_of_homOfLE_comp_eq hU hr V))).op
        ((tensorPowerModule T L' d).presheaf.map
          (homOfLE ((toGradedPowerMap ψ).image_preimage_preimage_le V)).op
          ((powCompare L' d).hom.app (f ⁻¹ᵁ V)
            ((toGradedPowerMap (ψ.congrModule e)).value d V a))) :=
  (congrArg (fun z => (laurentOnCongrPieceIso e U₁ d).hom.val.app
    (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))) z)
    (thetaTransport_restrict_app_pullbackUnit ψ hU hr V d a)).trans
    (laurentOnCongrPieceIso_restrict_value ψ e hU hr V d a)

attribute [local irreducible] laurentOnHomOfLEPieceIso laurentOnCongrPieceIso in
/-- The degree-`d` component of the transported `θ_ψ` on a pulled-back section, as its factors
applied in turn. -/
theorem thetaTransport_comp_apply (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    (((Scheme.Modules.pullbackCongr hr).inv.app (Otw A d) ≫
        (Scheme.Modules.pullbackComp (T.homOfLE hU) ((toGradedPowerMap ψ).globalMorphism
          (relativeProj A))).inv.app (Otw A d)) ≫
        (Scheme.Modules.pullback (T.homOfLE hU)).map
          (X := (Scheme.Modules.pullback ((toGradedPowerMap ψ).globalMorphism
            (relativeProj A))).obj (Otw A d))
          (Y := (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d)
          ((toGradedPowerMap ψ).theta.app d) ≫
        (laurentOnHomOfLEPieceIso L hU d).hom ≫ (laurentOnCongrPieceIso e U₁ d).hom).val.app
          (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
        (pullbackUnit r'.toLRSHom.toShHom (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
          (psiU A d V a)) =
      (laurentOnCongrPieceIso e U₁ d).hom.val.app (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
      ((laurentOnHomOfLEPieceIso L hU d).hom.val.app (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
        (((Scheme.Modules.pullback (T.homOfLE hU)).map
            (X := (Scheme.Modules.pullback ((toGradedPowerMap ψ).globalMorphism
              (relativeProj A))).obj (Otw A d))
            (Y := (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d)
            ((toGradedPowerMap ψ).theta.app d)).val.app (op
              (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
          (((Scheme.Modules.pullbackComp (T.homOfLE hU) ((toGradedPowerMap ψ).globalMorphism
            (relativeProj A))).inv.app (Otw A d)).val.app (op
              (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
            (((Scheme.Modules.pullbackCongr hr).inv.app (Otw A d)).val.app
              (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
              (pullbackUnit r'.toLRSHom.toShHom (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
                (psiU A d V a)))))) := rfl

/-- **`θ_ψ` transported to `U₁` satisfies clause (1) of [Stacks, Tag 01O9] for `e ∘ ψ`**, in the
form of `GradedPowerMap.eq_theta_of_clauseOne` with `U(e ∘ ψ)` and `r_{e ∘ ψ}` replaced by the
variables `U₁` and `r'`. -/
theorem thetaTransport_clauseOne
    (hV : ∀ V : S.Opens, (U₁.ι ≫ f) ⁻¹ᵁ V = r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
    (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    ((tensorPowerModule T L' d).restrict U₁.ι).presheaf.map (eqToHom (hV V)).op
        ((((toGradedPowerMap ψ).thetaTransportHom e hU hr).app d).val.app
          (op (r' ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
          (pullbackUnit r'.toLRSHom.toShHom (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
            (psiU A d V a))) =
      (tensorPowerModule T L' d).presheaf.map
        (homOfLE (U₁.ι.image_preimage_le (f ⁻¹ᵁ V))).op
        ((powCompare L' d).hom.app (f ⁻¹ᵁ V)
          ((toGradedPowerMap (ψ.congrModule e)).value d V a)) := by
  rw [(toGradedPowerMap ψ).thetaTransportHom_app e hU hr (d : ℤ)]
  have k := (thetaTransport_comp_apply ψ e hU hr V d a).trans
    (thetaTransport_app_pullbackUnit ψ e hU hr V d a)
  refine (congrArg (((tensorPowerModule T L' d).restrict U₁.ι).presheaf.map
    (eqToHom (hV V)).op) k).trans ?_
  exact map_map3 (tensorPowerModule T L' d)
    (homOfLE ((toGradedPowerMap ψ).image_preimage_preimage_le V)).op
    (homOfLE
      (image_le_image_of_le_preimage_homOfLE hU _
        ((toGradedPowerMap ψ).preimage_le_of_homOfLE_comp_eq hU hr V))).op
    (U₁.ι.opensFunctor.map (eqToHom (hV V))).op
    (homOfLE (U₁.ι.image_preimage_le (f ⁻¹ᵁ V))).op
    ((powCompare L' d).hom.app (f ⁻¹ᵁ V) ((toGradedPowerMap (ψ.congrModule e)).value d V a))

omit hU hr in
/-- **`θ` of [Stacks, Tag 01O9] does not change under an isomorphism of the invertible module**:
for `e : ℒ ≅ ℒ'`, `θ_{e ∘ ψ} : r_{e ∘ ψ}^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ'^{⊗ d}|_{U(e ∘ ψ)}` is `θ_ψ` read
along the identification `j : U(e ∘ ψ) = U(ψ)` (with `j ≫ r_ψ = r_{e ∘ ψ}`) and followed by the
isomorphism `⨁_d ℒ^{⊗ d} ≅ ⨁_d ℒ'^{⊗ d}` induced by `e`. -/
theorem theta_congrModule :
    (toGradedPowerMap (ψ.congrModule e)).theta =
      (toGradedPowerMap ψ).thetaTransportHom e (coveringOpen_congrModule_le ψ e)
        (homOfLE_globalMorphism_congrModule ψ e) :=
  ((toGradedPowerMap (ψ.congrModule e)).eq_theta_of_clauseOne
    (thetaTransport_clauseOne ψ e (coveringOpen_congrModule_le ψ e)
      (homOfLE_globalMorphism_congrModule ψ e)
      (toGradedPowerMap (ψ.congrModule e)).toBase_preimage_eq)).symm

end ThetaCongr

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
