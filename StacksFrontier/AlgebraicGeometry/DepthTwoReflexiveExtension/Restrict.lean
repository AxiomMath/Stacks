module

public import StacksFrontier.AlgebraicGeometry.DepthTwoReflexiveExtension.Stalk
public import StacksFrontier.AlgebraicGeometry.DepthTwoReflexiveExtension.Hull
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Reflexivity restricts to an open subscheme, and is local on an open cover

Reflexivity of a coherent module on a locally Noetherian scheme is a stalkwise condition:
`ReflexiveStalkCriterion.isReflexive_of_forall_isReflexive_stalk` gives one direction and
`DepthTwoReflexiveExtension.isReflexive_stalk_of_isReflexive` the other, and coherence supplies
the two finite-presentation hypotheses both of them need -- for `F` directly, and for `F^∨`
through coherence of a dual, which is
`InternalHomLocalKernel.isCoherent_dualSheaf`.

So the two statements of this file are both consequences of one geometric fact: the stalk of the
restriction of a module to an open subscheme *is* the stalk of the module, semilinearly over the
identification of the two local rings.  Mathlib's `Scheme.Modules.restrictStalkNatIso` compares
the two stalks only as abelian groups; `restrictStalkSemilinearEquiv` upgrades it, and the
semilinear transport of `Module.IsReflexive` then runs in both directions.

## Main definitions

* `restrictStalkSemilinearEquiv`: the stalk of `F|_U` at `x` is the stalk of `F` at `x`,
  semilinearly over `Scheme.Opens.stalkIso`.

## Main results

* `isReflexive_of_semilinearEquiv` and `isReflexive_of_semilinearEquiv'`: module reflexivity
  transports along a semilinear equivalence over a ring isomorphism, in both directions.
* `isReflexive_restrict`: **the open-immersion case of the reflexivity half of
  [Stacks, Tag 0EBF]** -- the restriction of a coherent reflexive module to an open subscheme is
  reflexive.
* `isReflexive_of_forall_isReflexive_restrict`: reflexivity of a coherent module is local on an
  open cover.

## Implementation notes

**Two spellings of a point of an open subscheme, and only one of them works.**  The module
structure on the stalk of a module on `U.toScheme` over the local ring there is found by instance
search for a point written `x : U.toScheme`, and is *not* found for the same point written
`x : U` -- this holds for `Module (U.toScheme.presheaf.stalk x) ...` and equally for the
`modStalk`/`ringStalk` spelling of `Stacks.SheafOfModules.SheafHomStalk`.  Every statement here
therefore binds its point at `U.toScheme`.  For the same reason the two transport lemmas take
their `Module.IsReflexive` input as an explicit argument rather than an instance: the stalk
criteria state it at the `modStalk`/`ringStalk` spelling and the transport needs it at the
`TopCat.Presheaf.stalk` spelling, and the two are interchangeable by definitional unfolding but
not by instance search.

**`germ_smul_scheme`.** Mathlib's `PresheafOfModules.germ_smul` is stated for a presheaf of
modules over a presheaf of commutative rings; on a scheme, the module structure instance search
actually finds on a stalk is `Stacks.StalkFreeBridge.instModuleStalk`, and the two agree
definitionally but not syntactically, so `rw` cannot use the Mathlib lemma directly.
`germ_smul_scheme` restates it at the instance a scheme-level goal carries.

**No `backward.isDefEq.respectTransparency` escape is needed.**  The library's proof of Tag 0EBJ
proves the same stalk comparison under that option; writing the local sections of the restriction
at the `Γ(F|_U, V)` spelling rather than at `(F|_U).val.presheaf.obj (op V)` removes the need for
it, because that is the spelling at which the scalar action on sections elaborates.

No tag is attached.  `isReflexive_restrict` is the open-immersion instance of Tag 0EBF's
reflexivity label, which the source states for an arbitrary flat morphism, so it is not a
covering set for that label; and the pair of stalk criteria covers only two of the three
conditions of Tag 0AY3.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveDualHull
open Stacks.AlgebraicGeometry.ReflexiveStalkCriterion
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension

attribute [local instance 2000]
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-! ### Transport of module reflexivity along a semilinear equivalence -/

section Semilinear

variable {R S M N : Type*} [CommSemiring R] [CommSemiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]

/-- The comparison of the two evaluation maps induced by a semilinear equivalence: transporting
a functional on `M` to one on `N` and a functional on the dual of `M` to one on the dual of `N`
carries `Module.Dual.eval R M` to `Module.Dual.eval S N`. -/
theorem dual_eval_comp (r : R ≃+* S) (e : M ≃ₛₗ[(r : R →+* S)] N) :
    ∃ dd : Module.Dual R (Module.Dual R M) ≃ₛₗ[(r : R →+* S)]
      Module.Dual S (Module.Dual S N),
      ⇑(Module.Dual.eval S N) = dd ∘ Module.Dual.eval R M ∘ e.symm := by
  let d : Module.Dual R M ≃ₛₗ[(r : R →+* S)] Module.Dual S N :=
    LinearEquiv.arrowCongr e r.toSemilinearEquiv
  refine ⟨LinearEquiv.arrowCongr d r.toSemilinearEquiv, ?_⟩
  funext n
  ext l
  simp [d, LinearEquiv.arrowCongr_apply, LinearEquiv.arrowCongr_symm_apply]

/-- Module reflexivity transports along a semilinear equivalence over a ring isomorphism. -/
theorem isReflexive_of_semilinearEquiv (r : R ≃+* S) (e : M ≃ₛₗ[(r : R →+* S)] N)
    (hM : Module.IsReflexive R M) : Module.IsReflexive S N := by
  obtain ⟨dd, h⟩ := dual_eval_comp r e
  let := hM
  refine ⟨?_⟩
  rw [h]
  exact dd.bijective.comp ((Module.bijective_dual_eval R M).comp e.symm.bijective)

/-- The same transport, read in the other direction. -/
theorem isReflexive_of_semilinearEquiv' (r : R ≃+* S) (e : M ≃ₛₗ[(r : R →+* S)] N)
    (hN : Module.IsReflexive S N) : Module.IsReflexive R M := by
  obtain ⟨dd, h⟩ := dual_eval_comp r e
  let := hN
  have hb : Function.Bijective (dd ∘ Module.Dual.eval R M ∘ e.symm) := by
    rw [← h]; exact Module.bijective_dual_eval S N
  exact ⟨(Function.Bijective.of_comp_iff _ e.symm.bijective).mp
    ((Function.Bijective.of_comp_iff' dd.bijective _).mp hb)⟩

end Semilinear

/-! ### The stalk of a restriction -/

variable {X : Scheme.{u}}

/-- The germ of a scalar multiple, stated at the module structure on the stalk that instance
search on a scheme actually finds (`Stacks.StalkFreeBridge.instModuleStalk`, which is Mathlib's
presheaf-of-modules instance named at the `AlgebraicGeometry.Scheme.Modules` spelling).  Stating
it at that instance is what makes it usable by `rw`. -/
theorem germ_smul_scheme {Y : Scheme.{u}} (M : Y.Modules) (V : Y.Opens) (y : Y) (hy : y ∈ V)
    (r : Γ(Y, V)) (m : Γ(M, V)) :
    TopCat.Presheaf.germ (C := Ab.{u}) M.val.presheaf V y hy (r • m)
      = Y.presheaf.germ V y hy r •
        TopCat.Presheaf.germ (C := Ab.{u}) M.val.presheaf V y hy m :=
  PresheafOfModules.germ_smul (R := Y.presheaf) M.val y V hy r m

/-- **The stalk of the restriction of a module to an open subscheme is the stalk of the
module**, semilinearly over the identification of the two local rings. -/
noncomputable def restrictStalkSemilinearEquiv (U : X.Opens) (F : X.Modules) (x : U.toScheme) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (F.restrict U.ι).val.presheaf x ≃ₛₗ[
      ((U.stalkIso x).commRingCatIsoToRingEquiv :
        U.toScheme.presheaf.stalk x →+* X.presheaf.stalk x.1)]
      TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x.1 := by
  let e : TopCat.Presheaf.stalk (C := Ab.{u}) (F.restrict U.ι).val.presheaf x ≃+
      TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x.1 :=
    ((Scheme.Modules.restrictStalkNatIso U.ι x).app F).addCommGroupIsoToAddEquiv
  refine { __ := e, map_smul' := ?_ }
  intro r m
  obtain ⟨V, hxV, r₀, hr⟩ := U.toScheme.presheaf.exists_germ_eq r
  obtain ⟨W, hxW, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq
    (F.restrict U.ι).val.presheaf m
  have hx : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  let r₁ : Γ(U.toScheme, V ⊓ W) :=
    U.toScheme.presheaf.map (homOfLE (show V ⊓ W ≤ V from inf_le_left)).op r₀
  let m₁ : Γ(F.restrict U.ι, V ⊓ W) :=
    (F.restrict U.ι).val.presheaf.map (homOfLE (show V ⊓ W ≤ W from inf_le_right)).op m₀
  have hr₁ : U.toScheme.presheaf.germ (V ⊓ W) x hx r₁ = r :=
    (U.toScheme.presheaf.germ_res_apply
      (homOfLE (show V ⊓ W ≤ V from inf_le_left)) x hx r₀).trans hr
  have hm₁ : TopCat.Presheaf.germ (F.restrict U.ι).val.presheaf (V ⊓ W) x hx m₁ = m :=
    (TopCat.Presheaf.germ_res_apply (F.restrict U.ι).val.presheaf
      (homOfLE (show V ⊓ W ≤ W from inf_le_right)) x hx m₀).trans hm
  rw [← hr₁, ← hm₁, ← germ_smul_scheme (F.restrict U.ι) (V ⊓ W) x hx r₁ m₁]
  have he (n : Γ(F.restrict U.ι, V ⊓ W)) :
      e (TopCat.Presheaf.germ (F.restrict U.ι).val.presheaf (V ⊓ W) x hx n) =
        TopCat.Presheaf.germ F.val.presheaf (U.ι ''ᵁ (V ⊓ W)) x.1 ⟨x, hx, rfl⟩ n :=
    congrArg (fun f ↦ (ConcreteCategory.hom f) n)
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app U.ι x F hx)
  change e _ = (U.stalkIso x).hom _ • e _
  rw [he, he]
  have hr₂ := congrArg (fun f ↦ (ConcreteCategory.hom f) r₁) (U.germ_stalkIso_hom x hx)
  change (U.stalkIso x).hom (U.toScheme.presheaf.germ (V ⊓ W) x hx r₁) =
    X.presheaf.germ (U.ι ''ᵁ (V ⊓ W)) x.1 ⟨x, hx, rfl⟩ r₁ at hr₂
  rw [hr₂]
  have hsmul :
      @SMul.smul _ _ ((F.restrict U.ι).val.obj (Opposite.op (V ⊓ W))).isModule.toSMul
          r₁ m₁ =
        @SMul.smul _ _ (F.val.obj (Opposite.op (U.ι ''ᵁ (V ⊓ W)))).isModule.toSMul
          r₁ m₁ := by
    change @SMul.smul _ _
      (F.val.obj (Opposite.op (U.ι ''ᵁ (V ⊓ W)))).isModule.toSMul
      ((U.ι.appIso (V ⊓ W)).inv r₁) m₁ = _
    rw [Scheme.Opens.ι_appIso]
    rfl
  exact (congrArg (fun n ↦ TopCat.Presheaf.germ F.val.presheaf
    (U.ι ''ᵁ (V ⊓ W)) x.1 ⟨x, hx, rfl⟩ n) hsmul).trans
      (PresheafOfModules.germ_smul (R := X.presheaf) F.val x.1
        (U.ι ''ᵁ (V ⊓ W)) ⟨x, hx, rfl⟩ r₁ m₁)


/-! ### Reflexivity restricts, and is local -/

/-- Stalk reflexivity transports from an open subscheme to the ambient scheme. -/
theorem isReflexive_stalk_of_isReflexive_stalk_restrict (U : X.Opens) (F : X.Modules)
    (y : U.toScheme)
    (h : Module.IsReflexive (ToType (ringStalk U.toScheme.sheaf y))
      (ToType (modStalk (F.restrict U.ι) y))) :
    Module.IsReflexive (ToType (ringStalk X.sheaf y.1)) (ToType (modStalk F y.1)) :=
  isReflexive_of_semilinearEquiv (U.stalkIso y).commRingCatIsoToRingEquiv
    (restrictStalkSemilinearEquiv U F y) h

section Coherent

variable [IsLocallyNoetherian X]

/-- The four finite-presentation facts a coherent module on a locally Noetherian scheme carries,
packaged so the stalkwise criterion applies to it.  Coherence of the dual is Stacks 01Y2 at
target the structure sheaf, proved as
`Stacks.AlgebraicGeometry.InternalHomLocalKernel.isCoherent_dualSheaf`. -/
theorem isFinitePresentation_dualSheaf (F : X.Modules) (hF : F.IsCoherent) :
    (dualSheaf F).IsFinitePresentation :=
  let := InternalHomLocalKernel.isCoherent_dualSheaf F hF
  CoherentTFAE.isFinitePresentation_of_isCoherent' (dualSheaf F)

/-- A coherent module and its dual are finitely presented. -/
private theorem isFinitePresentation_and_dualSheaf (F : X.Modules) (hc : F.IsCoherent) :
    F.IsFinitePresentation ∧ (dualSheaf F).IsFinitePresentation :=
  let := hc
  ⟨CoherentTFAE.isFinitePresentation_of_isCoherent' F, isFinitePresentation_dualSheaf F hc⟩

/-- **Reflexivity of a coherent module restricts to an open subscheme.**  This is the
open-immersion case of the reflexivity half of [Stacks, Tag 0EBF]. -/
theorem isReflexive_restrict (U : X.Opens) (F : X.Modules) (hc : F.IsCoherent)
    (hr : IsReflexive F) : IsReflexive (F.restrict U.ι) := by
  let : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  obtain ⟨_, _⟩ := isFinitePresentation_and_dualSheaf F hc
  obtain ⟨_, _⟩ := isFinitePresentation_and_dualSheaf (F.restrict U.ι)
    (AlgebraicGeometry.Modules.isCoherent_restrict F U)
  refine isReflexive_of_forall_isReflexive_stalk (F.restrict U.ι) fun y => ?_
  exact isReflexive_of_semilinearEquiv' (U.stalkIso y).commRingCatIsoToRingEquiv
    (restrictStalkSemilinearEquiv U F y) (isReflexive_stalk_of_isReflexive F hr y.1)

/-- **Reflexivity of a coherent module is local on an open cover.** -/
theorem isReflexive_of_forall_isReflexive_restrict (F : X.Modules) (hc : F.IsCoherent)
    {I : Type u} (V : I → X.Opens) (hV : iSup V = ⊤)
    (h : ∀ i, IsReflexive (F.restrict (V i).ι)) : IsReflexive F := by
  obtain ⟨_, _⟩ := isFinitePresentation_and_dualSheaf F hc
  refine isReflexive_of_forall_isReflexive_stalk F fun x => ?_
  have hx : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let : IsLocallyNoetherian (V i).toScheme := isLocallyNoetherian_of_isOpenImmersion (V i).ι
  obtain ⟨_, _⟩ := isFinitePresentation_and_dualSheaf (F.restrict (V i).ι)
    (AlgebraicGeometry.Modules.isCoherent_restrict F (V i))
  exact isReflexive_stalk_of_isReflexive_stalk_restrict (V i) F ⟨x, hi⟩
    (isReflexive_stalk_of_isReflexive (F.restrict (V i).ι) (h i) ⟨x, hi⟩)

end Coherent

end Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension

end
