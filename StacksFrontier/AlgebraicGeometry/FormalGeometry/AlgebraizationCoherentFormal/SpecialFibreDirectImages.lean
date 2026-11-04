module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ProperLocalBaseAlgebraization
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionRelativeLeray.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AnnihilatedFullyFaithful
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct images of the first term along the special fibre

Let `p : X ⟶ Spec R` be proper over a Noetherian local ring `(R, 𝔪)`, let `j : U ⟶ X` be the
inclusion of an open, and let `(F_n)` be an object of `Coh(U, 𝔪𝒪_U)`. The closing paragraph of
Stacks Remark 0EJV observes that the hypotheses on `j_*F_1` and `R¹j_*F_1` only concern the
special fibre: `F_1` is annihilated by `𝔪`, so it is a coherent module on `U_1`, and the direct
images along `j` agree with the direct images along the special fibre `j₁ : U_1 ⟶ X_1` of `j`.

## Main results

* `Stacks.Algebraization.specialFibreMap`: the morphism `j₁ : U_1 ⟶ X_1`.
* `Stacks.Algebraization.pushforwardSpecialFibreIso`,
  `Stacks.Algebraization.rightDerivedPushforwardSpecialFibreIso`: for a module `G` on `U_1`,
  `Rⁿj_*(i_{U,*}G) ≅ i_*(Rⁿj₁_*G)`, from the Leray isomorphism for the closed immersion `i_U` and
  exactness of `i_*`.
* `Stacks.Algebraization.exists_pushforward_specialFibre_iso`: a coherent module on `U`
  annihilated by `ℐ|_U` is the direct image of a coherent module on `U_1`.
* `Stacks.Algebraization.exists_specialFibre_directImage_iso`: the closing paragraph of
  Stacks 0EJV for `F_1`.

## References

* [Stacks Project, Tag 0EJV](https://stacks.math.columbia.edu/tag/0EJV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.FormalFunctions
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

section SpecialFibre

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens)

/-- The special fibre `j₁ : U₁ ⟶ X₁` of the inclusion `j : U ⟶ X`, for the closed subschemes cut
out by `ℐ` and by its restriction to `U`. -/
abbrev specialFibreMap : (I.comap U.ι).subscheme ⟶ I.subscheme :=
  Scheme.IdealSheafData.subschemeMap (I.comap U.ι) I U.ι (I.le_map_comap U.ι)

/-- The square formed by `j₁ : U_1 ⟶ X_1`, `j : U ⟶ X` and the closed immersions `U_1 ⟶ U`,
`X_1 ⟶ X` commutes. -/
theorem specialFibreMap_subschemeι :
    specialFibreMap I U ≫ I.subschemeι = (I.comap U.ι).subschemeι ≫ U.ι :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- `j_* (i_* G) = i_* (j₁_* G)`. -/
def pushforwardSpecialFibreIso (G : (I.comap U.ι).subscheme.Modules) :
    (Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pushforward
        (I.comap U.ι).subschemeι).obj G) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pushforward (specialFibreMap I U)).obj G) :=
  ((Scheme.Modules.pushforwardComp (I.comap U.ι).subschemeι U.ι).app G).symm ≪≫
    (Scheme.Modules.pushforwardCongr (specialFibreMap_subschemeι I U).symm).app G ≪≫
    (Scheme.Modules.pushforwardComp (specialFibreMap I U) I.subschemeι).app G

/-- `Rⁿ j_* (i_* G) = i_* (Rⁿ j₁_* G)`. -/
def rightDerivedPushforwardSpecialFibreIso (G : (I.comap U.ι).subscheme.Modules) (n : ℕ) :
    ((Scheme.Modules.pushforward U.ι).rightDerived n).obj ((Scheme.Modules.pushforward
        (I.comap U.ι).subschemeι).obj G) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj
        (((Scheme.Modules.pushforward (specialFibreMap I U)).rightDerived n).obj G) :=
  have : PreservesFiniteColimits (Scheme.Modules.pushforward I.subschemeι) :=
    AlgebraicGeometry.preservesFiniteColimits_pushforward_of_isClosedImmersion I.subschemeι
  have : (Scheme.Modules.pushforward I.subschemeι).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.rightDerivedPushforwardObjIso
      (I.comap U.ι).subschemeι U.ι G n).symm ≪≫
    ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Scheme.Modules.pushforwardCongr (specialFibreMap_subschemeι I U).symm) n).app G) ≪≫
    ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (Scheme.Modules.pushforward (specialFibreMap I U))
      (Scheme.Modules.pushforward I.subschemeι)
      (Scheme.Modules.pushforward (specialFibreMap I U ≫ I.subschemeι))
      (Scheme.Modules.pushforwardComp _ _) n).app G).symm

/-- A module on `U` annihilated by `ℐ|_U` is the direct image of a module on `U₁`. -/
theorem exists_pushforward_specialFibre_iso [IsLocallyNoetherian X] (M : U.toScheme.Modules)
    [M.IsCoherent] (hM : idealPowerMultiple (I.comap U.ι) 1 M = ⊥) :
    ∃ G : (I.comap U.ι).subscheme.Modules, G.IsCoherent ∧
      Nonempty ((Scheme.Modules.pushforward (I.comap U.ι).subschemeι).obj G ≅ M) := by
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsLocallyNoetherian (I.comap U.ι).subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (I.comap U.ι).subschemeι
  have hker : (I.comap U.ι).subschemeι.ker = I.comap U.ι := Scheme.IdealSheafData.ker_subschemeι _
  have hunit := Stacks.Coherent.isIso_unit_app_of_idealPowerMultiple_ker_eq_bot
    (I.comap U.ι).subschemeι M (by rw [hker]; exact hM)
  exact ⟨(Scheme.Modules.pullback (I.comap U.ι).subschemeι).obj M,
    AlgebraicGeometry.isCoherent_pullback _ M,
    ⟨(@asIso _ _ _ _ ((Scheme.Modules.pullbackPushforwardAdjunction
      (I.comap U.ι).subschemeι).unit.app M) hunit).symm⟩⟩

/-- **Stacks 0EJV, the closing paragraph: `j_*F_1` and `R¹j_*F_1` are conditions on the special
fibre.** Let `(R, 𝔪)` be a Noetherian local ring, `p : X ⟶ Spec R` proper, `U ⊆ X` open with
inclusion `j`, and `(F_n)` an object of `Coh(U, 𝔪𝒪_U)`. Write `i : X_1 ⟶ X` and `i_U : U_1 ⟶ U`
for the special fibres and `j₁ : U_1 ⟶ X_1` for the special fibre of `j`. Then `F_1` is a coherent
sheaf on `U_1`: there is a coherent `𝒪_{U_1}`-module `G` with `i_{U,*} G ≅ F_1`; and
`j_*F_1 ≅ i_* j₁_* G` and `R¹j_*F_1 ≅ i_* R¹j₁_* G`. -/
@[stacks 0EJV "the closing paragraph: F₁ is a coherent sheaf on the special fibre U₁, and \
j_*F₁ = j₁,*F₁ and R¹j_*F₁ = R¹j₁,*F₁ for the special fibre j₁ : U₁ → X₁ of j"]
theorem exists_specialFibre_directImage_iso
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p] (U : X.Opens)
    (F : Stacks.Coherent.CoherentAdicSystems
      ((baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).comap U.ι)) :
    ∃ G : ((baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).comap U.ι).subscheme.Modules,
      G.IsCoherent ∧
      Nonempty ((Scheme.Modules.pushforward
        ((baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).comap U.ι).subschemeι).obj G ≅
          F.obj.obj (op 0)) ∧
      Nonempty ((Scheme.Modules.pushforward U.ι).obj (F.obj.obj (op 0)) ≅
        (Scheme.Modules.pushforward
          (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).subschemeι).obj
          ((Scheme.Modules.pushforward
            (specialFibreMap (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p) U)).obj G)) ∧
      Nonempty (((Scheme.Modules.pushforward U.ι).rightDerived 1).obj (F.obj.obj (op 0)) ≅
        (Scheme.Modules.pushforward
          (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).subschemeι).obj
          (((Scheme.Modules.pushforward
            (specialFibreMap (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p) U)).rightDerived
              1).obj G)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : (F.obj.obj (op 0)).IsCoherent := F.property.isCoherent 0
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_pushforward_specialFibre_iso
    (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p) U (F.obj.obj (op 0))
    (F.property.idealPowerMultiple_eq_bot 0)
  exact ⟨G, hG, ⟨e⟩,
    ⟨(Scheme.Modules.pushforward U.ι).mapIso e.symm ≪≫ pushforwardSpecialFibreIso _ U G⟩,
    ⟨((Scheme.Modules.pushforward U.ι).rightDerived 1).mapIso e.symm ≪≫
      rightDerivedPushforwardSpecialFibreIso _ U G 1⟩⟩

end SpecialFibre

end Stacks.Algebraization

end
