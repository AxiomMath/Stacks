module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.AlgebraicGeometry.Duality.PullbackOfDualSheaf
public import StacksFrontier.AlgebraicGeometry.InternalHomCokernel.Biproduct
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullback
import StacksCore.Tactic.StacksAttribute

/-!
# `can` at a finite free sheaf, and the annihilation of its kernel and cokernel

Let `f : (X, O_X) ⟶ (Y, O_Y)` be a morphism of ringed sites and let
`can : f^*(F^∨) ⟶ (f^*F)^∨` be the sheaf-level canonical map from which the `can` of
[Stacks, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB) is built, constructed in
`StacksFrontier.AlgebraicGeometry.Duality.PullbackOfDualSheaf` as
`Stacks.SheafOfModules.PullbackDual.pullbackDualMap`.  This file proves the sheaf-level form of
the last clause of that remark:

* `can` is an isomorphism at a finite free sheaf of modules `O_Y^{⊕r}`;
* an endomorphism of `F` which factors through a finite free sheaf of modules annihilates the
  kernel and the cokernel of `can` at `F`.

The second is the remark's own reason for its last sentence: for an `(A, n, c)`-module `M` and
`a ∈ I^c` the map `a : M → M` factors through a finite free `A/Iⁿ`-module, at which `can` is an
isomorphism, so `a` kills the kernel and the cokernel of `can`.  The factoring step is
`Stacks.LocalCohomology.UniformityIII.IsANCModule.exists_finFree_factorization` of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullback`; the two steps
proved here are what that lemma is fed into.

The feeding is done in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackSource`, for the
source's `can : p^*(M^∨) ⟶ (p^*M)^∨` with `p^*N = f^*(N~)` on `Spec(A/Iⁿ)`; that is where Tag
0GAB is registered.  What is proved here is the general form the factorization is fed into,
for an arbitrary sheaf and an arbitrary morphism of ringed sites, and it therefore carries the
factorization as a hypothesis; it is `kernel_map_pullbackDualMap_eq_zero_of_factorization` and
its cokernel companion, of which the finite free statements below are the case `G = O_Y^{⊕r}`.
None of the statements here is tagged.

## What "annihilates" means here

An endomorphism `e : F ⟶ F` induces an endomorphism of `ker(can_F)` and of `coker(can_F)`,
because the two functors `F ↦ f^*(F^∨)` and `F ↦ (f^*F)^∨` carry `e` to maps which commute with
`can_F` — that commuting square is the functoriality of `can` in the module,
`Stacks.SheafOfModules.PullbackDual.pullbackDualMap_naturality`.  "`e` annihilates the kernel"
is the statement that this induced endomorphism is zero, and that is what
`kernel_map_pullbackDualMap_eq_zero` and `cokernel_map_pullbackDualMap_eq_zero` say.  Taking
`e` to be multiplication by a global section of `O_Y` gives the annihilation by a scalar which
the source states, `kernel_map_pullbackDualMap_smul_eq_zero` and its cokernel companion.

## Main definitions

* `Stacks.SheafOfModules.PullbackDual.finFreeSheaf`: the finite free sheaf of modules
  `O_Z^{⊕r}` on a ringed site, the direct sum of `r` copies of the structure sheaf.

## Main results

* `Stacks.SheafOfModules.PullbackDual.dualModuleSheafMap_add` and
  `Stacks.SheafOfModules.PullbackDual.dualSheafFunctor_additive`: the dual `(-)^∨` is additive.
* `Stacks.SheafOfModules.PullbackDual.isIso_pullbackDualMap_of_sum_id`: `can` is an isomorphism
  at any sheaf of modules whose identity is a finite sum of maps through the structure sheaf.
* `Stacks.SheafOfModules.PullbackDual.isIso_pullbackDualMap_finFree`: **`can` is an isomorphism
  at a finite free sheaf of modules.**
* `Stacks.SheafOfModules.PullbackDual.kernel_map_pullbackDualMap_eq_zero_of_factorization` and
  `Stacks.SheafOfModules.PullbackDual.cokernel_map_pullbackDualMap_eq_zero_of_factorization`: an
  endomorphism of `F` factoring through a sheaf at which `can` is an isomorphism annihilates the
  kernel and the cokernel of `can` at `F`.
* `Stacks.SheafOfModules.PullbackDual.kernel_map_pullbackDualMap_eq_zero` and
  `Stacks.SheafOfModules.PullbackDual.cokernel_map_pullbackDualMap_eq_zero`: **an endomorphism
  of `F` factoring through a finite free sheaf of modules annihilates the kernel and the
  cokernel of `can` at `F`.**
* `Stacks.SheafOfModules.PullbackDual.kernel_map_pullbackDualMap_smul_eq_zero` and
  `Stacks.SheafOfModules.PullbackDual.cokernel_map_pullbackDualMap_smul_eq_zero`: the same for
  multiplication by a global section of `O_Y` which factors through a finite free sheaf of
  modules — the source's "`a` annihilates the kernel and cokernel of `can`".

## Implementation notes

The diagram chase is not repeated: `Stacks.LocalCohomology.UniformityIII.isIso_app_of_sum_id`,
`Stacks.LocalCohomology.UniformityIII.kernel_ι_comp_map_eq_zero` and
`Stacks.LocalCohomology.UniformityIII.map_comp_cokernel_π_eq_zero` of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullback` are statements
about an arbitrary natural transformation between additive functors, and this file instantiates
them at `Stacks.SheafOfModules.PullbackDual.pullbackDualNatTrans`.  What has to be supplied for
that instantiation is additivity of the two functors it runs between.  The pullback is additive
by `AlgebraicGeometry.RingedToposHom.pullbackModules_additive`, restated here as
`ringedSitePullback_additive` because instance synthesis does not find it at the
`ringedSitePullback` spelling.  The dual is additive because `dualModuleSheafMap` is
precomposition — `Stacks.SheafOfModules.InternalHom.internalHomPre_app_eq_sheafInternalHomMapLeft`
— and precomposition in the first variable of the internal Hom presheaf is additive,
`Stacks.PresheafOfModules.InternalHom.internalHomMapLeft_add`.

Finite biproducts of sheaves of modules are not an instance: they follow from finite products,
which are, but `CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts` is a theorem in
Mathlib rather than an instance, so it is a local instance here.

`isMulCommutative_ringSheaf` is needed because sheaves of modules on a ringed site are taken
over the structure sheaf with commutativity forgotten, and the commutativity of the rings of
sections is not found through that forgetting — the same gap that
`AlgebraicGeometry.Scheme.isMulCommutative_ringCatSheaf` fills for a scheme.  It is a `local
instance`, the development already carrying the proposition at another spelling in four places;
its docstring lists them.

The scalar clauses take multiplication by a section of `O_Y` over a terminal object of the site
in the form `Stacks.SheafOfModules.terminalSectionToEnd`, not as the `a • 𝟙 F` of a
`CategoryTheory.Linear` structure on sheaves of `O_X`-modules.  Both spellings are available on
each of the two categories separately
(`Stacks.SheafOfModules.linearOfTerminalSection` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear`), but writing the *conclusion* as
`a • 𝟙 (kernel can_F) = 0` would need the pullback `f^*` to carry multiplication by a section
of `O_Y` to multiplication by its image in `O_X`.  That is a monoidality statement about
`AlgebraicGeometry.RingedToposHom.pullbackModules` — multiplication by a section is
`O ⊗ F ⟶ O ⊗ F` read through the unitor — and neither the unitor description of the module
structure nor that compatibility is available in this development.  The conclusion is therefore
stated as the vanishing of the endomorphism of the kernel that `e` induces, which needs no
linearity of either functor and is the same assertion.

The blowup situation of the source does not appear here, the morphism of ringed sites being
arbitrary.  It is not needed: what the source's last clause asks of the blowup `p` is only that
it be *some* morphism of ringed sites with target `Spec(A/Iⁿ)`, and the factorization the
clause turns on lives on that target, where it is supplied by `M ↦ M~` in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackTilde`.  A pullback
functor `Mod(A/Iⁿ) ⥤ Mod(O_{Yₙ})` is still not available, `Mod(O_{Yₙ})` not being constructed,
and so the sheaves on `Y_n` are still not named anywhere.  The remark's words "scheme
theoretically supported on `Y_c`" are not formalized, there being no scheme in this setting.

## References

* [Stacks Project, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.InternalHom Stacks.LocalCohomology.UniformityIII

namespace Stacks.SheafOfModules.PullbackDual

universe u

/-- The rings of sections of the structure sheaf of a ringed site are commutative, in the
unbundled form that `Stacks.SheafOfModules.terminalSectionToEnd` asks for: the sheaf of rings
that sheaves of modules are taken over is the structure sheaf with commutativity forgotten, and
synthesis does not see the commutativity through that forgetting.

The same proposition is already in the development at the `AlgebraicGeometry.RingedSite.ringSheaf`
spelling, several times over — `isMulCommutative_ringSheaf` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive`,
`isMulCommutative_ringSheaf_obj'` of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Localization`, and two
more — and the family should be collapsed onto one declaration when it is next touched.  It is
repeated here rather than imported because every one of those files sits in an unrelated part
of the development, and it is a `local instance` so that no further global copy is added. -/
local instance isMulCommutative_ringSheaf (Z : RingedSite.{u, u, u}) (U : Z.Cᵒᵖ) :
    IsMulCommutative (((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O).obj.obj U) :=
  inferInstanceAs (IsMulCommutative (Z.O.obj.obj U))

/-! ### The dual is additive -/

/-- **Dualizing is additive**: `(c + d)^∨ = c^∨ + d^∨`.  The dual of a morphism is
precomposition with it on the internal Hom sheaf, and precomposition in the first variable of
the internal Hom presheaf is additive. -/
theorem dualModuleSheafMap_add (Z : RingedSite.{u, u, u})
    {F F' : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)}
    (c d : F' ⟶ F) :
    dualModuleSheafMap Z (c + d) = dualModuleSheafMap Z c + dualModuleSheafMap Z d := by
  have h : ∀ e : F' ⟶ F, dualModuleSheafMap Z e = sheafInternalHomMapLeft Z.J Z.O e :=
    fun e => internalHomPre_app_eq_sheafInternalHomMapLeft Z.O e _
  rw [h, h, h]
  exact _root_.SheafOfModules.hom_ext
    (Stacks.PresheafOfModules.InternalHom.internalHomMapLeft_add Z.O.obj c.val d.val)

/-- **The dual `(-)^∨` is an additive functor.** -/
@[ega "0 4.1.5" "partial"]
instance dualSheafFunctor_additive (Z : RingedSite.{u, u, u}) :
    (dualSheafFunctor Z).Additive where
  map_add := dualModuleSheafMap_add Z _ _

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- **The pullback of sheaves of modules along a morphism of ringed sites is additive.**  This
is `AlgebraicGeometry.RingedToposHom.pullbackModules_additive`, which is an instance, restated
at the `ringedSitePullback` spelling, where instance synthesis does not find it. -/
theorem ringedSitePullback_additive : (ringedSitePullback f).Additive :=
  RingedToposHom.pullbackModules_additive f.ringedToposHom

attribute [local instance] ringedSitePullback_additive

/-! ### `can` is an isomorphism at a finite free sheaf of modules -/

/-- The component of `can` as a natural transformation at `F` is `can` at `F`.  The two
spellings are definitionally equal, but the sheaf types on either side are large enough that
the conversion has to be performed once, by rewriting with this equation, rather than left to
unification inside a larger goal. -/
theorem pullbackDualNatTrans_app
    (F : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :
    (pullbackDualNatTrans f).app (op F) = pullbackDualMap f F := rfl

/-- The action of the source functor of `can` on a morphism is the pullback of the dual. -/
theorem dualSheafFunctor_comp_ringedSitePullback_map
    {F F' : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (c : F' ⟶ F) :
    (dualSheafFunctor Y ⋙ ringedSitePullback f).map c.op =
      (ringedSitePullback f).map (dualModuleSheafMap Y c) := rfl

/-- The action of the target functor of `can` on a morphism is the dual of the pullback. -/
theorem ringedSitePullback_op_comp_dualSheafFunctor_map
    {F F' : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (c : F' ⟶ F) :
    ((ringedSitePullback f).op ⋙ dualSheafFunctor X).map c.op =
      dualModuleSheafMap X ((ringedSitePullback f).map c) := rfl

/-- **`can` is an isomorphism at a sheaf of modules whose identity is a finite sum of maps
through the structure sheaf.**  Such a sheaf is a direct summand of a finite free one; the
finite free case is `isIso_pullbackDualMap_finFree`.

It is the rank-one case `isIso_pullbackDualMap_unit` carried along the finite sum, both
functors between which `can` runs being additive. -/
@[ega "0 5.4.5" "special case"]
theorem isIso_pullbackDualMap_of_sum_id
    {P : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    {ι : Type*} [Fintype ι]
    (p : ι → (P ⟶ _root_.SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
    (q : ι → (_root_.SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⟶ P))
    (h : ∑ i, p i ≫ q i = 𝟙 P) :
    IsIso (pullbackDualMap f P) := by
  have : IsIso ((pullbackDualNatTrans f).app (op (_root_.SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))) :=
    isIso_pullbackDualMap_unit f
  rw [← pullbackDualNatTrans_app]
  refine isIso_app_of_sum_id (pullbackDualNatTrans f)
    (A := op (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
    (fun i => (q i).op) (fun i => (p i).op) ?_
  rw [show (∑ i, (q i).op ≫ (p i).op) = ∑ i, (p i ≫ q i).op from rfl, ← op_sum, h]
  rfl

section FinFree

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- The finite free sheaf of modules `O_Z^{⊕r}` on a ringed site: the direct sum of `r` copies
of the structure sheaf.  This is the sheaf-level counterpart of
`Stacks.LocalCohomology.UniformityIII.finFreeModule`. -/
@[ega "0 5.1.1" "special case"]
noncomputable abbrev finFreeSheaf (Z : RingedSite.{u, u, u}) (r : ℕ) :
    _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O) :=
  ⨁ fun _ : Fin r =>
    _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)

/-- **`can` is an isomorphism at a finite free sheaf of modules.**  In the source this is the
sheaf-level counterpart of the clause "a finite free `A/Iⁿ`-module, for which `can` is an
isomorphism"; here the rank-one case `isIso_pullbackDualMap_unit`, which has no hypotheses, is
carried to rank `r` by the decomposition of the identity of `O_Y^{⊕r}` into `r` maps through
`O_Y`. -/
@[ega "0 5.4.5" "special case"]
theorem isIso_pullbackDualMap_finFree (r : ℕ) :
    IsIso (pullbackDualMap f (finFreeSheaf Y r)) :=
  isIso_pullbackDualMap_of_sum_id f _ _ biproduct.total

/-! ### The kernel and the cokernel of `can` -/

variable {F : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
  {r : ℕ}

/-- The kernel inclusion of `can` at `F` kills the pullback of the dual of an endomorphism of
`F` which factors through a sheaf at which `can` is an isomorphism. -/
theorem kernel_ι_comp_map_pullbackDualMap_eq_zero
    {G : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (hG : IsIso (pullbackDualMap f G)) (α : F ⟶ G) (β : G ⟶ F) :
    kernel.ι (pullbackDualMap f F) ≫
        (ringedSitePullback f).map (dualModuleSheafMap Y (α ≫ β)) = 0 := by
  have : IsIso ((pullbackDualNatTrans f).app (op G)) := hG
  rw [← pullbackDualNatTrans_app, ← dualSheafFunctor_comp_ringedSitePullback_map]
  exact kernel_ι_comp_map_eq_zero (pullbackDualNatTrans f) β.op α.op

/-- The dual of the pullback of an endomorphism of `F` which factors through a sheaf at which
`can` is an isomorphism kills the cokernel projection of `can` at `F`. -/
theorem map_comp_cokernel_π_pullbackDualMap_eq_zero
    {G : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (hG : IsIso (pullbackDualMap f G)) (α : F ⟶ G) (β : G ⟶ F) :
    dualModuleSheafMap X ((ringedSitePullback f).map (α ≫ β)) ≫
        cokernel.π (pullbackDualMap f F) = 0 := by
  have : IsIso ((pullbackDualNatTrans f).app (op G)) := hG
  rw [← pullbackDualNatTrans_app, ← ringedSitePullback_op_comp_dualSheafFunctor_map]
  exact map_comp_cokernel_π_eq_zero (pullbackDualNatTrans f) β.op α.op

/-- **An endomorphism of `F` which factors through a sheaf at which `can` is an isomorphism
annihilates the kernel of `can`.**  The hypothesis-free form of the kernel half of the last
clause of Tag 0GAB: `kernel_map_pullbackDualMap_eq_zero` is this at a finite free sheaf, and
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullbackTilde` is this at
the sheaf `(A/Iⁿ)^{⊕r}~` on `Spec(A/Iⁿ)`, where the factorization is supplied rather than
assumed. -/
theorem kernel_map_pullbackDualMap_eq_zero_of_factorization (e : F ⟶ F)
    {G : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (hG : IsIso (pullbackDualMap f G)) (α : F ⟶ G) (β : G ⟶ F) (hαβ : α ≫ β = e) :
    kernel.map (pullbackDualMap f F) (pullbackDualMap f F)
        ((ringedSitePullback f).map (dualModuleSheafMap Y e))
        (dualModuleSheafMap X ((ringedSitePullback f).map e))
        (pullbackDualMap_naturality f e) = 0 := by
  subst hαβ
  rw [← cancel_mono (kernel.ι (pullbackDualMap f F)), kernel.lift_ι, zero_comp]
  exact kernel_ι_comp_map_pullbackDualMap_eq_zero f hG α β

/-- **An endomorphism of `F` which factors through a sheaf at which `can` is an isomorphism
annihilates the cokernel of `can`.**  The cokernel half of
`kernel_map_pullbackDualMap_eq_zero_of_factorization`. -/
theorem cokernel_map_pullbackDualMap_eq_zero_of_factorization (e : F ⟶ F)
    {G : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)}
    (hG : IsIso (pullbackDualMap f G)) (α : F ⟶ G) (β : G ⟶ F) (hαβ : α ≫ β = e) :
    cokernel.map (pullbackDualMap f F) (pullbackDualMap f F)
        ((ringedSitePullback f).map (dualModuleSheafMap Y e))
        (dualModuleSheafMap X ((ringedSitePullback f).map e))
        (pullbackDualMap_naturality f e) = 0 := by
  subst hαβ
  rw [← cancel_epi (cokernel.π (pullbackDualMap f F)), cokernel.π_desc, comp_zero]
  exact map_comp_cokernel_π_pullbackDualMap_eq_zero f hG α β

/-- **An endomorphism of `F` which factors through a finite free sheaf of modules annihilates
the kernel of `can`.**  An endomorphism `e : F ⟶ F` induces an endomorphism of
`ker(can_F)` — the commuting square it needs is the functoriality of `can` in the module,
`pullbackDualMap_naturality` — and the assertion is that this induced endomorphism is zero.

This is the kernel half of the remark's last sentence, and the hypothesis is the remark's own
reason for it.  For `M` an `(A, n, c)`-module and `a ∈ I^c` the hypothesis is what
`Stacks.LocalCohomology.UniformityIII.IsANCModule.exists_finFree_factorization` supplies, in
the same shape: `a : M → M` factors through a finite free module.  The scalar reading, with `e`
multiplication by a global section of `O_Y`, is
`kernel_map_pullbackDualMap_smul_eq_zero`. -/
theorem kernel_map_pullbackDualMap_eq_zero (e : F ⟶ F)
    (he : ∃ (r : ℕ) (α : F ⟶ finFreeSheaf Y r) (β : finFreeSheaf Y r ⟶ F), α ≫ β = e) :
    kernel.map (pullbackDualMap f F) (pullbackDualMap f F)
        ((ringedSitePullback f).map (dualModuleSheafMap Y e))
        (dualModuleSheafMap X ((ringedSitePullback f).map e))
        (pullbackDualMap_naturality f e) = 0 := by
  obtain ⟨r, α, β, hαβ⟩ := he
  exact kernel_map_pullbackDualMap_eq_zero_of_factorization f e
    (isIso_pullbackDualMap_finFree f r) α β hαβ

/-- **An endomorphism of `F` which factors through a finite free sheaf of modules annihilates
the cokernel of `can`.**  The cokernel half of
`kernel_map_pullbackDualMap_eq_zero`. -/
theorem cokernel_map_pullbackDualMap_eq_zero (e : F ⟶ F)
    (he : ∃ (r : ℕ) (α : F ⟶ finFreeSheaf Y r) (β : finFreeSheaf Y r ⟶ F), α ≫ β = e) :
    cokernel.map (pullbackDualMap f F) (pullbackDualMap f F)
        ((ringedSitePullback f).map (dualModuleSheafMap Y e))
        (dualModuleSheafMap X ((ringedSitePullback f).map e))
        (pullbackDualMap_naturality f e) = 0 := by
  obtain ⟨r, α, β, hαβ⟩ := he
  exact cokernel_map_pullbackDualMap_eq_zero_of_factorization f e
    (isIso_pullbackDualMap_finFree f r) α β hαβ

/-! ### The scalar reading: annihilation by a global section

In the source the endomorphism of `M` is multiplication by an element `a ∈ I^c`.  Its
sheaf-level avatar is multiplication by a section of `O_Y` over a terminal object of the site,
`Stacks.SheafOfModules.terminalSectionToEnd`, and the two clauses above read as the source's
"`a` annihilates the kernel and the cokernel of `can`". -/

section Scalar

variable (T : Y.C) (hT : IsTerminal T)
  (s : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj.obj (op T))

/-- **A global section of `O_Y` whose multiplication on `F` factors through a finite free sheaf
of modules annihilates the kernel of `can`.**  This is the source's "so that `a`
annihilates the kernel of `can`", with `a` a section of the structure sheaf over a terminal
object of the site, which is what an element of `A/Iⁿ` becomes on `Y_n`.  The hypothesis is the
remark's reason, and for an `(A, n, c)`-module and `a ∈ I^c` it is
`Stacks.LocalCohomology.UniformityIII.IsANCModule.exists_finFree_factorization`. -/
theorem kernel_map_pullbackDualMap_smul_eq_zero
    (hs : ∃ (r : ℕ) (α : F ⟶ finFreeSheaf Y r) (β : finFreeSheaf Y r ⟶ F),
      α ≫ β = (Stacks.SheafOfModules.terminalSectionToEnd
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) T hT s).app F) :
    kernel.map (pullbackDualMap f F) (pullbackDualMap f F)
        ((ringedSitePullback f).map (dualModuleSheafMap Y
          ((Stacks.SheafOfModules.terminalSectionToEnd
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) T hT s).app F)))
        (dualModuleSheafMap X ((ringedSitePullback f).map
          ((Stacks.SheafOfModules.terminalSectionToEnd
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) T hT s).app F)))
        (pullbackDualMap_naturality f _) = 0 :=
  kernel_map_pullbackDualMap_eq_zero f _ hs

/-- **A global section of `O_Y` whose multiplication on `F` factors through a finite free sheaf
of modules annihilates the cokernel of `can`.**  The cokernel half of
`kernel_map_pullbackDualMap_smul_eq_zero`. -/
theorem cokernel_map_pullbackDualMap_smul_eq_zero
    (hs : ∃ (r : ℕ) (α : F ⟶ finFreeSheaf Y r) (β : finFreeSheaf Y r ⟶ F),
      α ≫ β = (Stacks.SheafOfModules.terminalSectionToEnd
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) T hT s).app F) :
    cokernel.map (pullbackDualMap f F) (pullbackDualMap f F)
        ((ringedSitePullback f).map (dualModuleSheafMap Y
          ((Stacks.SheafOfModules.terminalSectionToEnd
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) T hT s).app F)))
        (dualModuleSheafMap X ((ringedSitePullback f).map
          ((Stacks.SheafOfModules.terminalSectionToEnd
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) T hT s).app F)))
        (pullbackDualMap_naturality f _) = 0 :=
  cokernel_map_pullbackDualMap_eq_zero f _ hs

end Scalar

end FinFree

end Stacks.SheafOfModules.PullbackDual

end
