module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeMorphism
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.RingTheory.LocalCohomology.UniformCohomologyBound
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rigidity of a closed subscheme containing every adic thickening

Let `A` be a Noetherian ring complete with respect to an ideal `I`, write `𝓘 = I · 𝒪_W`, and let
`W` be proper over `Spec A`. A closed immersion `i : Z ⟶ W` through which every adic base change
`Wₙ = W ×_{Spec A} Spec (A / Iⁿ⁺¹)` factors is an isomorphism.

The argument is the one the Stacks project uses at the last step of [Stacks, Tag 0A42] and in the
monomorphism clause of [Stacks, Tag 0899]. Write `τ : 𝒪_W ⟶ i_* 𝒪_Z` for the unit of the closed
immersion; its kernel is the ideal sheaf `i.ker`. A factorization of `Wₙ ⟶ W` through `Z` forces
`i.ker ≤ 𝓘ⁿ⁺¹`, because `Wₙ ⟶ W` is the closed immersion cut out by `𝓘ⁿ⁺¹`
(`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst`). So on every affine open the
kernel inclusion lands inside `𝓘ⁿ⁺¹`, hence inside the subsheaf `𝓘ⁿ⁺¹ · 𝒪_W`, hence dies in the
quotient `𝒪_W / 𝓘ⁿ⁺¹𝒪_W` — that is, the `n`-th term of the completion of the kernel inclusion
is zero, for every `n`. The completion functor of [Stacks, Tag 0880] is **faithful** for a proper
morphism over a Noetherian adically complete base — that half of [Stacks, Tag 0883] is carried
outright by `Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper` — so the kernel
inclusion is itself zero, `τ` is a monomorphism, and `i.ker = ⊥`.

Only faithfulness is used, never essential surjectivity; in particular nothing here rests on
[Stacks, Tag 088C], whose `hDev` hypothesis the library still carries.

## Main results

* `Stacks.AdicClosedSubschemeRigidity.isIso_of_isClosedImmersion_of_ker_le_baseIdealSheaf_pow` —
  a closed immersion into a proper `W` whose ideal sheaf lies in every power of `𝓘` is an
  isomorphism.
* `Stacks.AdicClosedSubschemeRigidity.adicRigidity` — `AlgebraicGeometry.AdicRigidity A I`,
  discharged for every Noetherian `I`-adically complete `A`.

## References

* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.AdicClosedSubschemeRigidity

/-! ### Two maps of sheaves of modules agreeing on affine opens are equal -/

/-- Affine opens form a basis, so a map of sheaves of modules is determined by its values on
them. -/
public lemma modules_hom_ext_affine {X : Scheme.{u}} {F G : X.Modules} (α β : F ⟶ G)
    (h : ∀ U : X.affineOpens, Scheme.Modules.Hom.app α U = Scheme.Modules.Hom.app β U) :
    α = β := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  apply TopCat.Sheaf.hom_ext F.presheaf ⟨G.presheaf, G.isSheaf⟩
    (B := fun U : X.affineOpens => U.1)
  · simpa using X.isBasis_affineOpens
  · exact h

/-- **A map into `𝒪_X` whose affine-local values lie in `J(U) ^ n` dies in `𝒪_X / Jⁿ𝒪_X`.** -/
public lemma comp_idealPowerQuotient_eq_zero {X : Scheme.{u}} (J : X.IdealSheafData) (n : ℕ)
    {F : SheafOfModules.{u} X.ringCatSheaf}
    (α : F ⟶ SheafOfModules.unit X.ringCatSheaf)
    (h : ∀ (U : X.affineOpens) (x : F.val.obj (op U.1)),
      α.val.app (op U.1) x ∈ J.ideal U ^ n) :
    α ≫ cokernel.π (C := SheafOfModules.{u} X.ringCatSheaf)
      (idealPowerMultiple J n (SheafOfModules.unit X.ringCatSheaf)).ι = 0 := by
  set N := idealPowerMultiple J n (SheafOfModules.unit X.ringCatSheaf)
  refine modules_hom_ext_affine _ _ fun U => ?_
  ext x
  have hx : α.val.app (op U.1) x ∈ N.toSubmodule.obj (op U.1) := by
    refine (idealPowerMultiple_le_iff J n _ N).mp le_rfl U ?_
    show α.val.app (op U.1) x ∈
      (J.ideal U ^ n) • (⊤ : Submodule (X.presheaf.obj (op U.1)) (X.presheaf.obj (op U.1)))
    rw [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id]
    exact h U x
  let y : N.toSheafOfModules.val.obj (op U.1) := ⟨α.val.app (op U.1) x, hx⟩
  show (N.ι ≫ cokernel.π N.ι).val.app (op U.1) y = 0
  simp only [cokernel.condition]
  rfl

/-! ### Faithfulness of the completion functor, read on the projections -/

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]

/-- **The projection to the `n`-th term of the completion is an epimorphism**: it is the cokernel
projection of `𝓘ⁿ⁺¹F ⟶ F` followed by an `eqToHom`. -/
public lemma epi_completionProjection {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    Epi (Stacks.Algebraization.completionProjection X J F n) := by
  have hfac : Stacks.Algebraization.completionProjection X J F n =
      cokernel.π (idealPowerMultiple J (n + 1) F.obj).ι ≫
        eqToHom (Stacks.Algebraization.completionFunctor_obj X J F n).symm := rfl
  rw [hfac]
  exact @epi_comp _ _ _ _ _ _ inferInstance _
    (IsIso.epi_of_iso (eqToHom (Stacks.Algebraization.completionFunctor_obj X J F n).symm))

/-- **Two maps of coherent modules with the same composites into every term of the completion of
the target are equal**, for a proper morphism over a Noetherian adically complete base. This is
the faithfulness half of [Stacks, Tag 0883], read through the projections. -/
public lemma coherent_hom_ext_of_completionProjection {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) [IsProper fX] [IsLocallyNoetherian X]
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (α β : F ⟶ G)
    (h : ∀ n, α.hom ≫ Stacks.Algebraization.completionProjection X (baseIdealSheaf A I fX) G n =
      β.hom ≫ Stacks.Algebraization.completionProjection X (baseIdealSheaf A I fX) G n) :
    α = β := by
  set J := baseIdealSheaf A I fX
  obtain ⟨hff⟩ := Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper A I fX
  have : (Stacks.Algebraization.completionFunctor X J).Faithful := hff.faithful
  apply (Stacks.Algebraization.completionFunctor X J).map_injective
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  have := epi_completionProjection J F n.unop
  apply (cancel_epi (Stacks.Algebraization.completionProjection X J F n.unop)).mp
  rw [Stacks.Algebraization.completionFunctor_map_quotient,
    Stacks.Algebraization.completionFunctor_map_quotient]
  exact h n.unop

/-! ### The rigidity statement -/

/-- **A closed immersion into a proper scheme whose ideal sheaf lies in every power of `𝓘` is an
isomorphism.** See the module documentation for the argument. -/
@[ega "III 5.1.8" "Injectivity of Z ↦ Ẑ"]
public theorem isIso_of_isClosedImmersion_of_ker_le_baseIdealSheaf_pow {W Z : Scheme.{u}}
    (fW : W ⟶ Spec (.of A)) [IsProper fW] (i : Z ⟶ W) [IsClosedImmersion i]
    (h : ∀ n : ℕ, i.ker ≤ baseIdealSheaf A I fW ^ (n + 1)) : IsIso i := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian fW
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  set OW : SheafOfModules.{u} W.ringCatSheaf := SheafOfModules.unit W.ringCatSheaf
  set OZ : SheafOfModules.{u} Z.ringCatSheaf := SheafOfModules.unit Z.ringCatSheaf
  set τ : OW ⟶ (Scheme.Modules.pushforward i).obj OZ :=
    SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  have : OZ.IsCoherent := inferInstanceAs (SheafOfModules.unit Z.ringCatSheaf).IsCoherent
  have : ((Scheme.Modules.pushforward i).obj OZ).IsCoherent :=
    AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion i OZ
  have : (kernel (C := SheafOfModules.{u} W.ringCatSheaf) τ).IsCoherent :=
    SheafOfModules.kernel_isCoherent τ
  set F : AlgebraicGeometry.SheafOfModules.CoherentModules W.ringCatSheaf :=
    ⟨kernel (C := SheafOfModules.{u} W.ringCatSheaf) τ, inferInstance⟩
  set G : AlgebraicGeometry.SheafOfModules.CoherentModules W.ringCatSheaf :=
    ⟨OW, inferInstance⟩
  set α : F ⟶ G :=
    ObjectProperty.homMk (kernel.ι (C := SheafOfModules.{u} W.ringCatSheaf) τ)
  set β : F ⟶ G :=
    ObjectProperty.homMk (0 : kernel (C := SheafOfModules.{u} W.ringCatSheaf) τ ⟶ OW) with hβ
  have heq : α = β := by
    refine coherent_hom_ext_of_completionProjection A I fW α β fun n => ?_
    have hz : α.hom ≫ cokernel.π (C := SheafOfModules.{u} W.ringCatSheaf)
        (idealPowerMultiple (baseIdealSheaf A I fW) (n + 1) G.obj).ι = 0 := by
      refine comp_idealPowerQuotient_eq_zero _ _ _ fun U x => ?_
      have hx : α.hom.val.app (op U.1) x ∈ i.ker.ideal U := by
        rw [Scheme.Hom.ker_apply]
        exact congrArg
          (fun a : kernel (C := SheafOfModules.{u} W.ringCatSheaf) τ ⟶
              (Scheme.Modules.pushforward i).obj OZ => a.val.app (op U.1) x)
          (kernel.condition τ)
      exact h n U hx
    have hβz : β.hom ≫ cokernel.π (C := SheafOfModules.{u} W.ringCatSheaf)
        (idealPowerMultiple (baseIdealSheaf A I fW) (n + 1) G.obj).ι = 0 := by
      simp [hβ]
    exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ eqToHom
      (Stacks.Algebraization.completionFunctor_obj W (baseIdealSheaf A I fW) G n).symm)
      (hz.trans hβz.symm)).trans (Category.assoc _ _ _)
  have : Mono τ := Abelian.mono_of_kernel_ι_eq_zero τ (congrArg (fun a : F ⟶ G => a.hom) heq)
  refine IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (Scheme.IdealSheafData.ext ?_)
  funext U
  rw [Scheme.Hom.ker_apply]
  refine (RingHom.injective_iff_ker_eq_bot _).mp ?_
  have : Mono ((SheafOfModules.forget W.ringCatSheaf).map τ) :=
    Functor.map_mono (SheafOfModules.forget W.ringCatSheaf) τ
  exact PresheafOfModules.injective_of_mono
    ((SheafOfModules.forget W.ringCatSheaf).map τ) (op U.1)

/-- **`AlgebraicGeometry.AdicRigidity`, discharged.** A closed immersion into a scheme proper over
`Spec A` through which every adic base change factors is an isomorphism, for every Noetherian
`I`-adically complete `A`.

A factorization `kₙ : Wₙ ⟶ Z` with `kₙ ≫ i = pₙ` makes `i.ker ≤ (pₙ).ker`, and `(pₙ).ker` is
`𝓘ⁿ⁺¹` by `Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst`. -/
@[ega "III 5.1.8" "Injectivity of Z ↦ Ẑ"]
public theorem adicRigidity : AlgebraicGeometry.AdicRigidity A I := by
  intro W Z fW _ i _ hfac
  refine isIso_of_isClosedImmersion_of_ker_le_baseIdealSheaf_pow A I fW i fun n => ?_
  obtain ⟨k, hk⟩ := hfac n
  have hker : i.ker ≤ (pullback.fst fW (adicThickeningι A I n)).ker := by
    rw [← hk, Scheme.Hom.ker_comp, ← Scheme.IdealSheafData.map_bot i]
    exact Scheme.IdealSheafData.map_mono i bot_le
  rw [← baseIdealSheaf_pow]
  exact hker.trans
    (Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst A (I ^ (n + 1)) fW).ge

end Stacks.AdicClosedSubschemeRigidity

end
