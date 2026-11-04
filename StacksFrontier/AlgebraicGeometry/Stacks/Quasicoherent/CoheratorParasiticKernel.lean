module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules

/-!
# The kernel of the coherator is the parasitic modules (Stacks 0779)

Let `𝒳` be an algebraic stack over `S` and let `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` be the right
adjoint of the inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` constructed for **Stacks 0778** in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Coherator.lean`.  **Stacks 0779** says:

1. the kernel of `Q` is exactly the collection of parasitic objects (**Stacks 0773**) of
   `LQCoh^fbc(𝒪_𝒳)`;
2. for every `𝓕` the kernel and the cokernel of the adjunction map `Q 𝓕 ⟶ 𝓕` are parasitic;
3. `Q` is exact and commutes with all limits and all colimits.

The adjunction map of (2) is the counit `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator`
of the adjunction, no new comparison map is built, and the whole of the formal part of
the source's argument is run off that adjunction: a right adjoint commutes with all limits, and
for a *fully faithful* left adjoint the counit becomes an isomorphism after applying the right
adjoint, so `Q (Q 𝓕 ⟶ 𝓕)` is invertible.

## The geometric input, and why it is a hypothesis

Everything else in the source is read off the *explicit* construction of `Q` in **Stacks 0778**:
one chooses a smooth surjective chart `f : U → 𝒳`, writes `𝒳 = [U/R]` for `R = U ×_𝒳 U`, and
`Q` is the composite of `q₂ : 𝓕 ↦ (f^*𝓕|_{U_étale}, α)` with the equivalence
`q₁ : QCoh(U, R, s, t, c) ≅ QCoh(𝒪_𝒳)` of **Stacks 06WT**.  The coherator in this library is
instead the abstract right adjoint produced by the special adjoint functor theorem, and
**Stacks 06WT** is not available (its own proof runs through **Stacks 0GQD**, the comparison of
quasi-coherent modules on a category fibred in groupoids representable by an algebraic space,
which this library does not have either).

So the chart is carried as data and the three facts the source reads off it are carried as
hypotheses, for a functor `r : LQCoh^fbc(𝒪_𝒳) ⥤ 𝒜` playing the role of `q₂`:

* `hrpar` — `r 𝓕 = 0` if and only if `𝓕` is parasitic.  This is the heart of part (1) of the
  source: in one direction `U → 𝒳` is smooth surjective, hence flat, so a parasitic module
  restricts to zero on `U_étale`; in the other, for a flat `x : V → 𝒳` one forms
  `W = V ×_𝒳 U`, whose projection `p : W → U` is flat and whose projection `q : W → V` is
  smooth and surjective, so that `q_{small}^*` is faithful on quasi-coherent modules, and the
  flat base change property (**Stacks 0762**) identifies `p_{small}^*𝓕|_{U_étale}` with
  `q_{small}^*𝓕|_{V_étale}`.
  That equivalence is itself proved, for the *lisse-étale* restriction in place of the
  restriction to `U_étale`: **Stacks 07AR** part (1), that is
  `AlgebraicGeometry.Stack.LisseEtale.isParasitic_iff_isZero_pullbackModules`.  It does not
  remove the hypothesis here, which constrains the functor `r` carried as data: given
  `hrcounit` and `hreq`, `hrpar` is *equivalent* to the conclusion below, so deleting it means
  fixing `r` to a named functor, and that is the step **Stacks 06WT** is needed for.
* `hrcounit` — the adjunction map `Q 𝓕 ⟶ 𝓕` becomes an isomorphism under `r`.  This is the
  source's `q₂ ∘ Q ≅ q₂`, that is the defining property of the construction of **Stacks 0778**.
* `hreq` — `i ⋙ r` is an equivalence.  This is **Stacks 06WT** together with the step of
  **Stacks 0778** which identifies `q₂ ∘ i` as a quasi-inverse of `q₁`.  The equivalence of
  **Stacks 06WT** is not in the library: its construction needs **Stacks 0GQD**, as
  `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientStackQuasicoherentModules.lean`
  records.  It is named here rather than reproved.
* `hrcolim`, `hrfincolim` — `r` commutes with colimits.  The source uses it for direct sums
  only, reducing to that case by exactness and **Stacks 002P**; restriction to `U_étale` is
  restriction along a functor followed by a change of scalars, both of which commute with
  colimits of presheaves of modules (compare
  `AlgebraicGeometry.Stack.isClosedUnderColimitsOfShape_flatBaseChangeModulePresheaves`).

Only the limit half of part (3) is unconditional; it is the one assertion of **Stacks 0779**
that follows from `Q` being a right adjoint.

## Main results

* `AlgebraicGeometry.Stack.isZero_flatBaseChangeQuasicoherator_iff_isParasitic`:
  **Stacks 0779** part (1), both directions.
* `AlgebraicGeometry.Stack.isParasitic_of_isLimit_kernelFork_flatBaseChangeQuasicoherator` and
  `AlgebraicGeometry.Stack.isParasitic_of_isColimit_cokernelCofork_flatBaseChangeQuasicoherator`:
  **Stacks 0779** part (2), for the kernel and for the cokernel.
* `AlgebraicGeometry.Stack.exact_flatBaseChangeQuasicoherator`: **Stacks 0779** part (3), the
  exactness of `Q`.
* `AlgebraicGeometry.Stack.preservesLimitsOfSize_flatBaseChangeQuasicoherator`: **Stacks 0779**
  part (3), that `Q` commutes with all limits.  Unconditional.
* `AlgebraicGeometry.Stack.preservesColimitsOfSize_flatBaseChangeQuasicoherator`:
  **Stacks 0779** part (3), that `Q` commutes with all colimits.

## Implementation notes

The kernel and the cokernel of part (2) are taken as an arbitrary limit kernel fork and an
arbitrary colimit cokernel cofork of the adjunction map, so that nothing has to be assumed
about `LQCoh^fbc(𝒪_𝒳)` having kernels or cokernels — which is **Stacks 0771** part (2), also
absent from the library.  Under that part the forks are the ones computed in the ambient
category `Mod(𝒳_étale, 𝒪_𝒳)`, so the statements are the source's.

Vanishing of an object is `CategoryTheory.Limits.IsZero`, and "the kernel of `Q`" is read as
`IsZero (Q 𝓕)`; the parasitic condition of **Stacks 0773** is
`AlgebraicGeometry.Stack.IsParasitic`, which is stated for the structure sheaf at a named
`AlgebraicGeometry.SiteKind`.  At `SiteKind.etale` that sheaf of rings is the one
`LQCoh^fbc(𝒪_𝒳)` is built over, on the nose, by
`AlgebraicGeometry.FibredSite.ringStructureSheafCore_etale_eq_stack`, so no transport is
needed.

Exactness is delivered as the pair `CategoryTheory.Limits.PreservesFiniteLimits` and
`CategoryTheory.Limits.PreservesFiniteColimits`, the two halves of exactness for an additive
functor between abelian categories.  `Q` preserves zero morphisms because it is a right
adjoint, which is what lets the kernel and cokernel forks be transported along it.

The universes are those of `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator`: the site of
`𝒳` is a `Type (u + 1)` with morphisms in `Type u`, essentially `u`-small, and the module
sections live in `u`.

## References

* [Stacks Project, Tag 002P](https://stacks.math.columbia.edu/tag/002P)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe vA uA vJ uJ vC uC vD uD u w

namespace AlgebraicGeometry.Stack

section Coreflection

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {A : Type uA} [Category.{vA} A]

/-- An equivalence both preserves and reflects zero objects: reflection is
`CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero`, and preservation is the same
statement for the inverse, read through the unit isomorphism. -/
private theorem isZero_obj_iff_of_isEquivalence (F : C ⥤ A) [F.IsEquivalence] (X : C) :
    IsZero (F.obj X) ↔ IsZero X := by
  refine ⟨IsZero.of_full_of_faithful_of_isZero F X, fun hX => ?_⟩
  exact IsZero.of_full_of_faithful_of_isZero F.inv (F.obj X)
    (hX.of_iso (F.asEquivalence.unitIso.app X).symm)

/-- The counit of the adjunction, whiskered by `r`, is a natural isomorphism `Q ⋙ i ⋙ r ≅ r`
as soon as each of its components is invertible. -/
private def whiskerCounitIso {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) (r : D ⥤ A)
    (hrcounit : ∀ F : D, IsIso (r.map (adj.counit.app F))) : Q ⋙ i ⋙ r ≅ r :=
  have : ∀ F : D, IsIso ((Functor.whiskerRight adj.counit r).app F) := hrcounit
  have : IsIso (Functor.whiskerRight adj.counit r) := NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerRight adj.counit r) ≪≫ Functor.leftUnitor r

/-- `Q` is `r` followed by the inverse of the equivalence `i ⋙ r`: whiskering
`AlgebraicGeometry.Stack.whiskerCounitIso` with that inverse and using the unit isomorphism of
the equivalence. -/
private def rightAdjointIsoCompInv {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) (r : D ⥤ A)
    (hrcounit : ∀ F : D, IsIso (r.map (adj.counit.app F))) [(i ⋙ r).IsEquivalence] :
    Q ≅ r ⋙ (i ⋙ r).inv :=
  (Functor.rightUnitor Q).symm ≪≫ Functor.isoWhiskerLeft Q (i ⋙ r).asEquivalence.unitIso ≪≫
    Functor.isoWhiskerRight (whiskerCounitIso adj r hrcounit) (i ⋙ r).inv

/-- An object is in the kernel of `Q` exactly when it is killed by `r`: the counit identifies
`r (i (Q F))` with `r F`, and `i ⋙ r` reflects zero objects. -/
private theorem isZero_obj_iff_isZero_map_obj {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q)
    (r : D ⥤ A) (hrcounit : ∀ F : D, IsIso (r.map (adj.counit.app F)))
    [(i ⋙ r).IsEquivalence] (F : D) : IsZero (Q.obj F) ↔ IsZero (r.obj F) := by
  rw [← isZero_obj_iff_of_isEquivalence (i ⋙ r) (Q.obj F)]
  exact Iso.isZero_iff (@asIso _ _ _ _ _ (hrcounit F))

end Coreflection

section Counit

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) [i.Full] [i.Faithful]

omit [i.Full] [i.Faithful] in
include adj in
/-- A right adjoint preserves zero morphisms, so kernel forks and cokernel coforks can be
transported along `Q`. -/
private theorem preservesZeroMorphisms_rightAdjoint : Q.PreservesZeroMorphisms :=
  have : Q.IsRightAdjoint := adj.isRightAdjoint
  inferInstance

include adj in
/-- The kernel of the adjunction map `Q F ⟶ F` is killed by `Q`.  The left adjoint is fully
faithful, so `Q` applied to the counit is invertible, in particular a monomorphism; and `Q`
preserves the kernel fork, being a right adjoint. -/
private theorem isZero_obj_pt_of_isLimit_kernelFork {F : D}
    {c : KernelFork (adj.counit.app F)} (hc : IsLimit c) : IsZero (Q.obj c.pt) :=
  have := preservesZeroMorphisms_rightAdjoint adj
  have : PreservesLimitsOfSize.{0, 0} Q := adj.rightAdjoint_preservesLimits
  KernelFork.IsLimit.isZero_of_mono (KernelFork.mapIsLimit c hc Q)

include adj in
/-- The cokernel of the adjunction map `Q F ⟶ F` is killed by `Q`, once `Q` is known to be
right exact: `Q` applied to the counit is invertible, in particular an epimorphism. -/
private theorem isZero_obj_pt_of_isColimit_cokernelCofork [PreservesFiniteColimits Q] {F : D}
    {c : CokernelCofork (adj.counit.app F)} (hc : IsColimit c) : IsZero (Q.obj c.pt) :=
  have := preservesZeroMorphisms_rightAdjoint adj
  CokernelCofork.IsColimit.isZero_of_epi (CokernelCofork.mapIsColimit c hc Q)

end Counit

section Stacks

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)
  [EssentiallySmall.{u} 𝒳.val.val.obj]
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf))
  (hpres : PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hlsD : LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))

/-- **Stacks 0779, part (3): the coherator commutes with all limits.**  This is the one
assertion of **Stacks 0779** which needs nothing beyond the adjunction of **Stacks 0778**: `Q`
is a right adjoint, and a right adjoint preserves all limits. -/
@[stacks 0779 "part (3): Q commutes with all limits"]
theorem preservesLimitsOfSize_flatBaseChangeQuasicoherator :
    PreservesLimitsOfSize.{vJ, uJ}
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) :=
  (flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp
    hsep).rightAdjoint_preservesLimits

/-- **Stacks 0779, part (3): the coherator is left exact.**  A special case of
`AlgebraicGeometry.Stack.preservesLimitsOfSize_flatBaseChangeQuasicoherator`; it is the half of
the exactness of `Q` which the source also gets from `Q` being a right adjoint. -/
theorem preservesFiniteLimits_flatBaseChangeQuasicoherator :
    PreservesFiniteLimits
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) :=
  have : PreservesLimitsOfSize.{0, 0}
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) :=
    preservesLimitsOfSize_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed hpres hls
      hlsD hwp hsep
  inferInstance

variable {𝒜 : Type uA} [Category.{vA} 𝒜]
  (r : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids ⥤ 𝒜)
  (hrpar : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
    IsZero (r.obj F) ↔ IsParasitic.{u, w, u} B S hS 𝒳 .etale F.obj.val)
  (hrcounit : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
    IsIso (r.map ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app F)))
  (hreq : (quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc ⋙ r).IsEquivalence)

include hinc hrpar hrcounit hreq in
/-- **Stacks 0779, part (1).**  An object `𝓕` of `LQCoh^fbc(𝒪_𝒳)` is in the kernel of the
coherator `Q` of **Stacks 0778** if and only if it is parasitic (**Stacks 0773**).  Both
directions are proved: the statement is an equality of the two collections.

The counit of the adjunction identifies `r (i (Q 𝓕))` with `r 𝓕`, and `i ⋙ r` is an
equivalence and so reflects zero objects; so `Q 𝓕 = 0` if and only if `r 𝓕 = 0`, which by
`hrpar` is the parasitic condition.  Here `r` stands for the restriction `𝓕 ↦ 𝓕|_{U_étale}`
along a smooth surjective chart `f : U → 𝒳`, through which the source computes `Q`; see the
module documentation for the three hypotheses it carries and for **Stacks 06WT**, which
`hreq` names. -/
@[stacks 0779 "part (1): the kernel of Q is exactly the parasitic objects, in both \
  directions, over the chart data of the construction of Stacks 0778"]
theorem isZero_flatBaseChangeQuasicoherator_iff_isParasitic
    (F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    IsZero ((flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).obj F) ↔
      IsParasitic.{u, w, u} B S hS 𝒳 .etale F.obj.val := by
  have := hreq
  exact (isZero_obj_iff_isZero_map_obj (flatBaseChangeQuasicoheratorAdjunction B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep) r
    hrcounit F).trans (hrpar F)

include hinc hrcounit hreq in
/-- **Stacks 0779, part (3): the coherator commutes with all colimits.**  The source does
*not* get this from adjointness — a right adjoint need not preserve colimits.  It gets it from
the explicit construction: by exactness it suffices to treat direct sums (**Stacks 002P**), and
restriction to `U_étale` commutes with direct sums.

Here that is the hypothesis `hrcolim` on `r`, carried through the identification
`Q ≅ r ⋙ (i ⋙ r)⁻¹` which the counit and `hreq` supply; the inverse of an equivalence
preserves all colimits. -/
@[stacks 0779 "part (3): Q commutes with all colimits, over the chart data of the \
  construction of Stacks 0778"]
theorem preservesColimitsOfSize_flatBaseChangeQuasicoherator
    (hrcolim : PreservesColimitsOfSize.{vJ, uJ} r) :
    PreservesColimitsOfSize.{vJ, uJ}
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) := by
  have := hreq
  have := hrcolim
  exact preservesColimits_of_natIso (rightAdjointIsoCompInv
    (flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep) r hrcounit).symm

include hinc hrcounit hreq in
/-- **Stacks 0779, part (3): the coherator is right exact.**  The right-exactness half of the
exactness of `Q`, obtained from the identification `Q ≅ r ⋙ (i ⋙ r)⁻¹` and the right
exactness of the chart restriction `r`. -/
theorem preservesFiniteColimits_flatBaseChangeQuasicoherator
    (hrfincolim : PreservesFiniteColimits r) :
    PreservesFiniteColimits
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) := by
  have := hreq
  have := hrfincolim
  have := comp_preservesFiniteColimits r
    (quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc ⋙ r).inv
  exact preservesFiniteColimits_of_natIso (rightAdjointIsoCompInv
    (flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep) r hrcounit).symm

include hinc hrcounit hreq in
/-- **Stacks 0779, part (3): the coherator is exact.**  Exactness of an additive functor
between abelian categories is the preservation of finite limits and of finite colimits.  The
first half is `AlgebraicGeometry.Stack.preservesFiniteLimits_flatBaseChangeQuasicoherator`,
which holds because `Q` is a right adjoint; the second is
`AlgebraicGeometry.Stack.preservesFiniteColimits_flatBaseChangeQuasicoherator`, which needs the
chart data. -/
@[stacks 0779 "part (3): Q is exact, over the chart data of the construction of Stacks 0778"]
theorem exact_flatBaseChangeQuasicoherator (hrfincolim : PreservesFiniteColimits r) :
    PreservesFiniteLimits
        (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          hinc hclosed hpres hls hlsD hwp hsep) ∧
      PreservesFiniteColimits
        (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          hinc hclosed hpres hls hlsD hwp hsep) :=
  ⟨preservesFiniteLimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed hpres hls
      hlsD hwp hsep,
    preservesFiniteColimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed hpres hls
      hlsD hwp hsep r hrcounit hreq hrfincolim⟩

include hinc hrpar hrcounit hreq in
/-- **Stacks 0779, part (2), the kernel.**  The kernel of the adjunction map `Q 𝓕 ⟶ 𝓕` is
parasitic.

The left adjoint `i` is fully faithful, so `Q` applied to the counit is invertible, in
particular a monomorphism; `Q` preserves the kernel fork, being a right adjoint; so the kernel
is in the kernel of `Q` and therefore parasitic by part (1).  The kernel is taken as an
arbitrary limit kernel fork, so that nothing is assumed about `LQCoh^fbc(𝒪_𝒳)` having kernels
(**Stacks 0771** part (2)). -/
@[stacks 0779 "part (2), the kernel: the kernel of the adjunction map Q(F) ⟶ F is parasitic"]
theorem isParasitic_of_isLimit_kernelFork_flatBaseChangeQuasicoherator
    {F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids}
    {c : KernelFork ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app F)}
    (hc : IsLimit c) : IsParasitic.{u, w, u} B S hS 𝒳 .etale c.pt.obj.val := by
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).full
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).faithful
  refine (isZero_flatBaseChangeQuasicoherator_iff_isParasitic B E h S hS 𝒳 hinc hclosed hpres
    hls hlsD hwp hsep r hrpar hrcounit hreq c.pt).1 ?_
  exact isZero_obj_pt_of_isLimit_kernelFork (flatBaseChangeQuasicoheratorAdjunction B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep) hc

include hinc hrpar hrcounit hreq in
/-- **Stacks 0779, part (2), the cokernel.**  The cokernel of the adjunction map `Q 𝓕 ⟶ 𝓕` is
parasitic.

`Q` applied to the counit is invertible, in particular an epimorphism; `Q` is right exact by
part (3) and so preserves the cokernel cofork; so the cokernel is in the kernel of `Q` and
therefore parasitic by part (1).  As for the kernel, the cokernel is taken as an arbitrary
colimit cokernel cofork. -/
@[stacks 0779 "part (2), the cokernel: the cokernel of the adjunction map Q(F) ⟶ F is \
  parasitic"]
theorem isParasitic_of_isColimit_cokernelCofork_flatBaseChangeQuasicoherator
    (hrfincolim : PreservesFiniteColimits r)
    {F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids}
    {c : CokernelCofork ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app F)}
    (hc : IsColimit c) : IsParasitic.{u, w, u} B S hS 𝒳 .etale c.pt.obj.val := by
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).full
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).faithful
  have := preservesFiniteColimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed
    hpres hls hlsD hwp hsep r hrcounit hreq hrfincolim
  refine (isZero_flatBaseChangeQuasicoherator_iff_isParasitic B E h S hS 𝒳 hinc hclosed hpres
    hls hlsD hwp hsep r hrpar hrcounit hreq c.pt).1 ?_
  exact isZero_obj_pt_of_isColimit_cokernelCofork (flatBaseChangeQuasicoheratorAdjunction
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp
    hsep) hc

end Stacks

end AlgebraicGeometry.Stack

end
