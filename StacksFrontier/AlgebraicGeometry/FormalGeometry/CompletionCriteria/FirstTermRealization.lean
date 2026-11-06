module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalShortExactSequences
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FiniteLocallyFreeComplementAffine

/-!
# The module algebraizing the first term of the system

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`, and let `(F_n)` be a coherent `I`-adic
system on `U` with `I = (f)` principal — condition (1) of Stacks 0DXW.

The finiteness half of the source's proof of that tag runs over the `A`-module `A/fA`, so it
needs the first term `F_1` of the system presented as `M^~|_U` for a finite `A`-module `M` that
is itself annihilated by `f`. This file produces such an `M`.

## Main results

* `Stacks.Algebraization.tilde_map_smul_id` — the sheaf attached to multiplication by `r` on a
  module is multiplication by `r` on the attached sheaf.
* `Stacks.Algebraization.restrictFunctor_map_mulBySpec` — restriction to an open subscheme of
  `Spec(A)` carries multiplication by `r` to multiplication by the image of `r` in the sections
  over that open.
* `Stacks.Algebraization.tildeRestrictCokernelIso` — `M ↦ (M^~)|_W` preserves the cokernel of
  multiplication by a scalar, being a left adjoint.
* `Stacks.Algebraization.exists_finiteModule_smul_eq_zero_tilde_restrict_iso` — **the
  conclusion**: `F_1` is `M^~|_U` for a finite `A`-module `M` with `fM = 0`.

## Implementation notes

Multiplication by `r` on `𝒪_{Spec A}`-modules is `Stacks.Algebraization.mulBySpec`, the
endomorphism of the identity functor attached to the global section `r` defines; its restriction
to `U` is `Stacks.Algebraization.mulBySection`, which is the spelling the rest of the proof of
Stacks 0DXW uses. The identification of `M^~` of multiplication by `r` with multiplication by `r`
is proved through the full faithfulness of `M ↦ M^~` and the unit of its adjunction with global
sections, not by computing sections.

Typeclass synthesis does not see the instances about `AlgebraicGeometry.tilde.functor` at the
spelling `CommRingCat.of A`, so the results above are stated for a variable `R : CommRingCat` and
applied at `CommRingCat.of A`.

## References

* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

-- The sheaf of rings of a scheme is commutative, at the spelling instance search needs for
-- `Stacks.SheafOfModules.terminalSectionToEnd`; `mulCommutativeRingCatSheaf` of
-- `PrincipalNonzerodivisor.lean` is that statement, made a local instance here.
attribute [local instance] mulCommutativeRingCatSheaf

/-- Multiplication by `r ∈ R` on `𝒪_{Spec R}`-modules. -/
def mulBySpec (R : CommRingCat.{u}) (r : R) :
    End (𝟭 (_root_.SheafOfModules.{u} (Spec R).ringCatSheaf)) :=
  Stacks.SheafOfModules.terminalSectionToEnd (Spec R).ringCatSheaf
    (⊤ : (Spec R).Opens) isTerminalTop ((Scheme.ΓSpecIso R).inv.hom r)

/-- Global sections of multiplication by `r` is multiplication by `r`. -/
theorem moduleSpecΓFunctor_map_mulBySpec {R : CommRingCat.{u}} (r : R)
    (N : (Spec R).Modules) :
    (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).map ((mulBySpec R r).asHom.app N) =
      r • 𝟙 ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj N) :=
  rfl

/-- The sheaf attached to multiplication by `r` on a module is multiplication by `r` on the
attached sheaf. -/
theorem tilde_map_smul_id {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (r : R) :
    (tilde.functor R).map (r • 𝟙 M) = (mulBySpec R r).asHom.app ((tilde.functor R).obj M) := by
  obtain ⟨a, ha⟩ := (tilde.functor R).map_surjective
    ((mulBySpec R r).asHom.app ((tilde.functor R).obj M))
  have hnatiso : 𝟭 (ModuleCat.{u} R) ≅
      tilde.functor R ⋙ AlgebraicGeometry.moduleSpecΓFunctor (R := R) :=
    tilde.toTildeΓNatIso
  have h1 : (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).map ((tilde.functor R).map a) =
      r • 𝟙 ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj
        ((tilde.functor R).obj M)) := by
    rw [ha]
    exact moduleSpecΓFunctor_map_mulBySpec r _
  have hlin : (r • 𝟙 M) ≫ (hnatiso.app M).hom = (hnatiso.app M).hom ≫
      (r • 𝟙 ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj
        ((tilde.functor R).obj M))) := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Functor.comp_obj,
      Category.comp_id]
  have h2 : a ≫ (hnatiso.app M).hom = (r • 𝟙 M) ≫ (hnatiso.app M).hom := by
    rw [hlin, ← h1]
    exact hnatiso.hom.naturality a
  have key : a = r • 𝟙 M := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun φ : M ⟶ _ => φ ≫ (hnatiso.app M).inv) h2
  rwa [← key]

/-- The local scalar of multiplication by a global section is the restriction of that
section. -/
theorem scalarAt_terminalSectionToEnd (X : Scheme.{u}) (g : Γ(X, ⊤)) (V : X.Opens) :
    Stacks.SheafOfModules.scalarAt
        (Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf (⊤ : X.Opens)
          isTerminalTop g) V =
      (X.presheaf.map (homOfLE (le_top (a := V))).op).hom g := by
  have h : Stacks.SheafOfModules.scalarAt
      (Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf (⊤ : X.Opens)
        isTerminalTop g) V =
      (X.presheaf.map (isTerminalTop.from V).op).hom g * 1 := rfl
  rw [h, mul_one, Subsingleton.elim (isTerminalTop.from V) (homOfLE (le_top (a := V)))]

/-- The local scalar of multiplication by `r` on `Spec R`. -/
theorem scalarAt_mulBySpec {R : CommRingCat.{u}} (r : R) (V : (Spec R).Opens) :
    Stacks.SheafOfModules.scalarAt (mulBySpec R r) V =
      ((Spec R).presheaf.map (homOfLE (le_top (a := V))).op).hom
        ((Scheme.ΓSpecIso R).inv.hom r) :=
  scalarAt_terminalSectionToEnd (Spec R) ((Scheme.ΓSpecIso R).inv.hom r) V

/-- Restriction to an open subscheme of `Spec R` carries multiplication by `r` to
multiplication by the image of `r` in the sections over that open. -/
theorem restrictFunctor_map_mulBySpec {R : CommRingCat.{u}} (W : (Spec R).Opens) (r : R)
    (N : (Spec R).Modules) :
    (Scheme.Modules.restrictFunctor W.ι).map ((mulBySpec R r).asHom.app N) =
      (Stacks.SheafOfModules.terminalSectionToEnd W.toScheme.ringCatSheaf
        (⊤ : W.toScheme.Opens) isTerminalTop
        (((Scheme.ΓSpecIso R).inv ≫ W.ι.appTop).hom r)).asHom.app
          ((Scheme.Modules.restrictFunctor W.ι).obj N) := by
  ext V x
  have hscal : ((Spec R).presheaf.map (homOfLE (le_top (a := W.ι ''ᵁ V))).op).hom
        ((Scheme.ΓSpecIso R).inv.hom r)
      = (W.ι.appIso V).inv.hom
          ((W.toScheme.presheaf.map (homOfLE (le_top (a := V))).op).hom
            (((Scheme.ΓSpecIso R).inv ≫ W.ι.appTop).hom r)) := by
    rw [Scheme.Opens.ι_appIso]
    simp only [Iso.refl_inv, CommRingCat.id_apply, CommRingCat.comp_apply,
      Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.ι_appTop, ← CommRingCat.comp_apply,
      ← Functor.map_comp]
    rfl
  have hL : (Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctor W.ι).map ((mulBySpec R r).asHom.app N)) V) x
      = (Scheme.Modules.Hom.app ((mulBySpec R r).asHom.app N) (W.ι ''ᵁ V)) x := rfl
  rw [hL, Stacks.SheafOfModules.scalarActionLocal (mulBySpec R r) N (W.ι ''ᵁ V) x,
    Stacks.SheafOfModules.scalarActionLocal
      (Stacks.SheafOfModules.terminalSectionToEnd W.toScheme.ringCatSheaf
        (⊤ : W.toScheme.Opens) isTerminalTop
        (((Scheme.ΓSpecIso R).inv ≫ W.ι.appTop).hom r))
      ((Scheme.Modules.restrictFunctor W.ι).obj N) V x,
    scalarAt_mulBySpec, scalarAt_terminalSectionToEnd]
  rw [hscal]
  rfl

section Tilde

variable {R : CommRingCat.{u}} (W : (Spec R).Opens)

/-- **`M ↦ (M^~)|_W` is a left adjoint**, being the composite of `M ↦ M^~`
(`AlgebraicGeometry.tilde.adjunction`) and restriction along an open immersion
(`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`). -/
instance isLeftAdjoint_tildeRestrict :
    (tilde.functor R ⋙ Scheme.Modules.restrictFunctor W.ι).IsLeftAdjoint :=
  ⟨_, ⟨tilde.adjunction.comp (Scheme.Modules.restrictAdjunction W.ι)⟩⟩

/-- **`M ↦ (M^~)|_W` carries the cokernel of multiplication by `r` to the cokernel of
multiplication by `r`**: it is a left adjoint, so it preserves cokernels. -/
def tildeRestrictCokernelIso (M : ModuleCat.{u} R) (r : R) :
    (tilde.functor R ⋙ Scheme.Modules.restrictFunctor W.ι).obj (cokernel (r • 𝟙 M)) ≅
      cokernel ((tilde.functor R ⋙ Scheme.Modules.restrictFunctor W.ι).map (r • 𝟙 M)) :=
  Limits.PreservesCokernel.iso _ _

end Tilde

/-- **Stacks Project, Tag 0DXW (the module algebraizing the first term).** Let `S` be an
algebraization situation whose ideal `I` is the principal ideal generated by `f ∈ A`, and let
`(F_n)` be a coherent `I`-adic system on the open complement `U`. Then the first term `F_1` is
the restriction to `U` of the sheaf attached to a finite `A`-module annihilated by `f`.

The term `F_1` is coherent, so Local Cohomology 0BK0 (1) presents it as `M₀^~|_U` for a finite
`A`-module `M₀`; the module wanted is `M₀/fM₀`. Multiplication by `f` is zero on `F_1`, a term
of a coherent `I`-adic system being annihilated by `I`, hence zero on `M₀^~|_U`; and
`M ↦ (M^~)|_U` preserves the cokernel of multiplication by `f` on `M₀`, being a left adjoint, so
that cokernel's sheaf restricted to `U` is the cokernel of the zero map on `M₀^~|_U`, which is
`F_1`. -/
theorem exists_finiteModule_smul_eq_zero_tilde_restrict_iso
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (hI : S.I = Ideal.span {f}) :
    ∃ M : ModuleCat.{u} (CommRingCat.of S.A), Module.Finite S.A (M : Type u) ∧
      (∀ x : (M : Type u), f • x = 0) ∧
      Nonempty ((AlgebraicGeometry.tilde M).restrict S.U.ι ≅ systemObj S F 0) := by
  have hc : _root_.SheafOfModules.IsCoherent.{u} (systemObj S F 0) := F.property.isCoherent 0
  obtain ⟨M₀, hM₀, ⟨e₀⟩⟩ :=
    @AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl
      (CommRingCat.of S.A) S.noetherianA S.a (systemObj S F 0) hc
  have e₀' : (AlgebraicGeometry.tilde M₀).restrict S.U.ι ≅ systemObj S F 0 := e₀
  let ψ : systemObj S F 0 ⟶ systemObj S F 0 := (mulBySection S f).asHom.app (systemObj S F 0)
  have hz : ψ = 0 := by
    have h1 := mulBySection_pow_app_eq_zero S f hI 1 (systemObj S F 0)
      (F.property.idealPowerMultiple_eq_bot 0)
    rwa [pow_one] at h1
  let φ : (AlgebraicGeometry.tilde M₀).restrict S.U.ι ⟶
      (AlgebraicGeometry.tilde M₀).restrict S.U.ι :=
    (mulBySection S f).asHom.app ((AlgebraicGeometry.tilde M₀).restrict S.U.ι)
  have hn : φ ≫ e₀'.hom = e₀'.hom ≫ ψ :=
    Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.mulF_naturality
      (mulBySection S f) e₀'.hom
  have happ : φ = 0 := (cancel_mono e₀'.hom).1 (by rw [hn, hz, comp_zero, zero_comp])
  have hT : (tilde.functor (CommRingCat.of S.A) ⋙
      Scheme.Modules.restrictFunctor S.U.ι).map (f • 𝟙 M₀) = 0 := by
    show (Scheme.Modules.restrictFunctor S.U.ι).map
      ((tilde.functor (CommRingCat.of S.A)).map (f • 𝟙 M₀)) = 0
    rw [tilde_map_smul_id, restrictFunctor_map_mulBySpec]
    exact happ
  have hsurj : Function.Surjective (cokernel.π (f • 𝟙 M₀)).hom :=
    (ModuleCat.epi_iff_surjective (cokernel.π (f • 𝟙 M₀))).mp inferInstance
  refine ⟨cokernel (f • 𝟙 M₀), ?_, ?_, ?_⟩
  · have hfin : Module.Finite S.A (M₀ : Type u) := hM₀
    exact Module.Finite.of_surjective
      ((cokernel.π (f • 𝟙 M₀)).hom : (M₀ : Type u) →ₗ[S.A] _) hsurj
  · intro x
    obtain ⟨m, rfl⟩ := hsurj x
    have hsm : (f • 𝟙 M₀).hom m = f • m := rfl
    rw [← ((cokernel.π (f • 𝟙 M₀)).hom).map_smul, ← hsm]
    exact congrArg (fun g : M₀ ⟶ cokernel (f • 𝟙 M₀) => g.hom m)
      (cokernel.condition (f • 𝟙 M₀))
  · exact ⟨tildeRestrictCokernelIso S.U M₀ f ≪≫ Limits.cokernelIsoOfEq hT ≪≫
      Limits.cokernelZeroIsoTarget ≪≫ e₀'⟩

end Stacks.Algebraization

end
