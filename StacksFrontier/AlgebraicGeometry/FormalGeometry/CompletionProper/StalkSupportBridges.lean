module

public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedFibreVanishing
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreFreeStalk
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.OpenImmersionAdicTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportCompactification
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of a restriction, the Nakayama step, and `β` with proper support

`Stacks.Algebraization.exists_hasProperSupport_iso_completionFunctor_of_isProjectiveMorphism`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/OpenImmersionAdicTransport.lean`)
produces the source's isomorphism `β` in the shape the binder `hTransport` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport` asks for — the
algebraizing module having support proper over the base — from two hypotheses that that file
carries as binders:

* `hSuppRestrict`, that the support of the restriction of a module to an open is the part of its
  support lying in that open;
* `hNak`, **the Nakayama step**: a point of the support of a coherent module which lies in the
  support of the ideal sheaf `𝓘` lies in the support of the first term `G'/𝓘 G'` of the
  completion of that module.

This file discharges both, and so states `β` with proper support with no hypotheses beyond the
data. Neither statement has any geometry in it: both are computations with the stalk at a single
point.

## Main results

* `Stacks.Algebraization.supp_restrictFunctor_eq_preimage` and
  `Stacks.Algebraization.image_supp_restrictFunctor_eq` — `hSuppRestrict`, in the preimage and
  the image spelling; the second is the binder.
* `Stacks.Algebraization.mem_supp_iff_nontrivial_modulesStalk` and
  `Stacks.Algebraization.finite_modulesStalk_of_isCoherent` — the two bridges between the
  support and `Stacks.ModuleSkyscraper.modulesStalkFunctor`, which is the spelling the stalk of
  an ideal-power quotient is computed in.
* `Stacks.Algebraization.mem_supp_idealPowerQuotient_of_mem_supp` — the Nakayama step for an
  arbitrary ideal-power quotient `M / 𝒥 ⁿ M`, `n ≠ 0`.
* `Stacks.Algebraization.mem_supp_completionFunctor_obj_of_mem_supp` — the same at every term of
  the completion, which at `n = 0` is `hNak`.
* `exists_hasProperSupport_iso_completionFunctor_opens_of_isProjectiveMorphism` (in
  `Stacks.Algebraization`) — **`β` with proper support, unconditional**: over a Noetherian
  `I`-adically complete `A` and for `p : Y' ⟶ Spec A` H-projective, every coherent adic system on
  an open `U ⊆ Y'` along `𝓘|_U` whose support is proper over `A` is isomorphic to the completion
  of a coherent `𝒪_U`-module whose support is itself proper over `A`.

## Implementation notes

**`hSuppRestrict`.** No stalk is touched by hand. `AlgebraicGeometry.supp_pullback_eq_preimage`
already computes the support of an *inverse image* along an open immersion, through
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` identifies restriction with it;
the support is invariant under isomorphism by `SheafOfModules.supp_eq_of_iso`. The passage from
the preimage to the image is `Set.image_preimage_eq_inter_range` together with
`AlgebraicGeometry.Scheme.Opens.range_ι`.

**The two bridges.** `SheafOfModules.supp` is defined by nonvanishing of the stalk of the
underlying sheaf of abelian groups, whereas `Stacks.Algebraization.stalk_idealPowerMultiple` and
`Stacks.Algebraization.idealPowerQuotientStalkLinearEquiv` — which compute the stalk of
`M / 𝒥 ⁿ M` as `M_x / 𝒥_x ⁿ M_x` — are stated for
`Stacks.ModuleSkyscraper.modulesStalkFunctor`, the stalk as a module over the local ring. The
carrier of the second is the first, so each bridge is the corresponding statement for the first
spelling read at the second: `mem_supp_iff_nontrivial_modulesStalk` is
`SheafOfModules.mem_supp_iff_nontrivial_stalk` and `finite_modulesStalk_of_isCoherent` is
`AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent`. They are stated because without
them the two halves of the Nakayama argument — nonvanishing and finiteness of the stalk — cannot
be fed to the same lemma.

**The Nakayama step.** With the stalk identified, the statement is that `M_x ≠ 𝒥_x ⁿ M_x` for a
finite nonzero module over the local ring `𝒪_{X,x}`, which is
`Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator`: `𝒥_x` lies in the maximal ideal
exactly because `x` is in the support of `𝒥`
(`AlgebraicGeometry.IdealSheafData.stalk_le_maximalIdeal_iff_mem_support`), and the maximal
ideal lies in the Jacobson radical of every ideal
(`IsLocalRing.maximalIdeal_le_jacobson`), the annihilator included. Finiteness of the stalk is
where coherence of the module is consumed, and it is the only place it is.

The passage from `M / 𝒥 ⁿ M` to the terms of the completion is the *equality* of objects
`Stacks.Algebraization.completionFunctor_obj`, transported with `congrArg` at the predicate
rather than with `rw`: the goal displays `AlgebraicGeometry.Scheme.Modules`, a `def` for
`SheafOfModules _` which agrees with it only at default transparency, so a rewrite motive built
at reducible transparency is not type-correct.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

open Stacks.Coherent Stacks.Cohomology.FormalFunctions

/-! ### The support of a restriction to an open -/

/-- **The support of the restriction of a module along an open immersion is the preimage of its
support.** Restriction is the inverse image
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`) and the support is invariant
under isomorphism, so this is `AlgebraicGeometry.supp_pullback_eq_preimage`. Nothing is assumed
of the module: the support is read off the stalks of the underlying sheaf of abelian groups. -/
public theorem supp_restrictFunctor_eq_preimage {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (F : Y.Modules) :
    _root_.SheafOfModules.supp ((Scheme.Modules.restrictFunctor g).obj F) =
      g.base ⁻¹' _root_.SheafOfModules.supp F :=
  (_root_.SheafOfModules.supp_eq_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback g).app F)).trans
    (AlgebraicGeometry.supp_pullback_eq_preimage g F)

/-- **The support of the restriction of a module to an open is the part of its support lying in
that open.** This is the binder `hSuppRestrict` of
`Stacks.Algebraization.exists_hasProperSupport_iso_completionFunctor_of_isProjectiveMorphism`.
The image of the preimage computed by
`Stacks.Algebraization.supp_restrictFunctor_eq_preimage` is the intersection with the range of
`U.ι`, which is `U`. -/
public theorem image_supp_restrictFunctor_eq {Y' : Scheme.{u}} (U : Y'.Opens) (F : Y'.Modules) :
    U.ι.base '' _root_.SheafOfModules.supp ((Scheme.Modules.restrictFunctor U.ι).obj F) =
      _root_.SheafOfModules.supp F ∩ (U : Set Y') := by
  rw [supp_restrictFunctor_eq_preimage, Set.image_preimage_eq_inter_range]
  congr 1
  exact Scheme.Opens.range_ι U

/-! ### The two stalk bridges -/

open Stacks.ModuleSkyscraper in
/-- **Membership in the support, at the `modulesStalkFunctor` spelling of the stalk.**
`SheafOfModules.mem_supp_iff_nontrivial_stalk` characterizes the support by nonvanishing of the
stalk of the underlying sheaf of abelian groups;
`Stacks.ModuleSkyscraper.modulesStalkFunctor X x` is that same abelian group with its module
structure over `𝒪_{X,x}`, so the two statements are the same one. It is stated because the
stalk of an ideal-power quotient is computed in the second spelling and the support in the
first. -/
public theorem mem_supp_iff_nontrivial_modulesStalk {X : Scheme.{u}} (M : X.Modules) (x : X) :
    x ∈ _root_.SheafOfModules.supp M ↔ Nontrivial ((modulesStalkFunctor X x).obj M) :=
  _root_.SheafOfModules.mem_supp_iff_nontrivial_stalk M x

open Stacks.ModuleSkyscraper in
/-- **The stalk of a coherent module is a finite module over the local ring at the point, at the
`modulesStalkFunctor` spelling of the stalk.** This is
`AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent`, whose module structure is the
same one `Stacks.ModuleSkyscraper.modulesStalkFunctor` carries
(`Stacks.Modules.stalkModule`, i.e. Mathlib's instance for presheaves of modules). Coherence is
used only through finiteness of type. -/
public theorem finite_modulesStalk_of_isCoherent {X : Scheme.{u}} (M : X.Modules)
    [M.IsCoherent] (x : X) :
    Module.Finite (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj M) :=
  AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent M x

/-! ### The Nakayama step -/

open Stacks.ModuleSkyscraper in
/-- **The Nakayama step.** A point of the support of a coherent module `M` which lies in the
support of a quasi-coherent ideal sheaf `𝒥` is in the support of `M / 𝒥 ⁿ M`, for every
`n ≠ 0`.

The stalk of `M / 𝒥 ⁿ M` at `x` is `M_x / 𝒥_x ⁿ M_x`
(`Stacks.Algebraization.idealPowerQuotientStalkLinearEquiv`), so the claim is that the finite
`𝒪_{X,x}`-module `M_x`, which is nonzero because `x ∈ Supp M`, is not equal to `𝒥_x ⁿ M_x`.
That is Nakayama's lemma, `Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator`: `𝒥_x` is
contained in the maximal ideal exactly because `x` lies in the support of `𝒥`
(`AlgebraicGeometry.IdealSheafData.stalk_le_maximalIdeal_iff_mem_support`), `𝒥_x ⁿ ≤ 𝒥_x`
because `n ≠ 0`, and the maximal ideal of a local ring lies in the Jacobson radical of every
ideal (`IsLocalRing.maximalIdeal_le_jacobson`), in particular of the annihilator of `M_x`.

The hypothesis `n ≠ 0` cannot be dropped: `M / 𝒥 ⁰ M` is the zero module, whose support is
empty. -/
public theorem mem_supp_idealPowerQuotient_of_mem_supp {X : Scheme.{u}}
    (J : X.IdealSheafData) (M : X.Modules) [M.IsCoherent] {n : ℕ} (hn : n ≠ 0) {x : X}
    (hx : x ∈ _root_.SheafOfModules.supp M) (hJ : x ∈ J.support) :
    x ∈ _root_.SheafOfModules.supp (idealPowerQuotient J n M) := by
  have : M.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent M
  have hnt : Nontrivial ((modulesStalkFunctor X x).obj M) :=
    (mem_supp_iff_nontrivial_modulesStalk M x).1 hx
  have hfin : Module.Finite (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj M) :=
    finite_modulesStalk_of_isCoherent M x
  have hjac : IdealSheafData.stalk J x ^ n ≤
      (Module.annihilator (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj M)).jacobson :=
    ((Ideal.pow_le_self hn).trans
      ((IdealSheafData.stalk_le_maximalIdeal_iff_mem_support J x).mpr hJ)).trans
        (IsLocalRing.maximalIdeal_le_jacobson _)
  have hne : (IdealSheafData.stalk J x ^ n •
      (⊤ : Submodule (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj M))) ≠ ⊤ :=
    fun h => Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator hjac h.symm
  have : Nontrivial ((modulesStalkFunctor X x).obj M ⧸
      (IdealSheafData.stalk J x ^ n •
        (⊤ : Submodule (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj M)))) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  refine (mem_supp_iff_nontrivial_modulesStalk (idealPowerQuotient J n M) x).2 ?_
  exact (Equiv.nontrivial_congr
    (idealPowerQuotientStalkLinearEquiv J n M x).toEquiv).1 inferInstance

/-! ### `hNak`, and `β` with proper support without binders -/

/-- **Every term of the completion of a coherent module is supported where the module is, at the
points of the support of the ideal sheaf.** This is the binder `hNak` of
`Stacks.Algebraization.exists_hasProperSupport_iso_completionFunctor_of_isProjectiveMorphism`,
which asks for it at `n = 0`.

The `n`-th term of the completion *is* `M / 𝒥 ⁿ⁺¹ M`, by the equality of objects
`Stacks.Algebraization.completionFunctor_obj`, so this is
`Stacks.Algebraization.mem_supp_idealPowerQuotient_of_mem_supp` with `n + 1 ≠ 0`. -/
@[ega "III 5.2.6" "partial"]
public theorem mem_supp_completionFunctor_obj_of_mem_supp {X : Scheme.{u}}
    [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) {x : X}
    (hx : x ∈ _root_.SheafOfModules.supp F.obj) (hJ : x ∈ J.support) :
    x ∈ _root_.SheafOfModules.supp (((completionFunctor X J).obj F).obj.obj (op n)) := by
  have : _root_.SheafOfModules.IsCoherent.{u} F.obj := F.property
  exact Eq.mpr (congrArg (fun Q : X.Modules => x ∈ _root_.SheafOfModules.supp Q)
      (completionFunctor_obj X J F n))
    (mem_supp_idealPowerQuotient_of_mem_supp J F.obj (Nat.succ_ne_zero n) hx hJ)

/-- **The source's isomorphism `β`, with the proper support of `G` that `hTransport` asks for,
unconditionally.** Let `A` be Noetherian and complete with respect to `I`, let
`p : Y' ⟶ Spec A` be H-projective and let `U ⊆ Y'` be open. Then every coherent adic system `𝓖`
on `U` along `𝓘|_U`, `𝓘 = I · 𝒪_{Y'}`, whose first term is supported in a closed subset of `U`
proper over `A`, is isomorphic to the completion of a coherent `𝒪_U`-module whose own support
is proper over `A`.

This is
`Stacks.Algebraization.exists_hasProperSupport_iso_completionFunctor_of_isProjectiveMorphism`
with its two binders discharged: `hNak` by
`Stacks.Algebraization.mem_supp_completionFunctor_obj_of_mem_supp` and `hSuppRestrict` by
`Stacks.Algebraization.image_supp_restrictFunctor_eq`. Everything else — the escape of the
support of the algebraization from outside `j(Y)`, which consumes completeness of `A` and the
universal closedness of `p`, and the properness of the resulting closed set — is already in
that theorem's proof. -/
public theorem exists_hasProperSupport_iso_completionFunctor_opens_of_isProjectiveMorphism
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Y' : Scheme.{u}} (p : Y' ⟶ Spec (.of A))
    (hp : AlgebraicGeometry.IsProjectiveMorphism p) (U : Y'.Opens) :
    letI : IsProper p := isProper_of_isProjectiveMorphism p hp
    letI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
    ∀ (𝓖 : Stacks.Coherent.CoherentAdicSystems ((baseIdealSheaf A I p).comap U.ι))
      (W : Closeds (U : Scheme.{u})),
      _root_.SheafOfModules.supp (𝓖.obj.obj (op 0)) ⊆ (W : Set (U : Scheme.{u})) →
      IsProperOver (U.ι ≫ p) W →
        ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules (U : Scheme.{u}).ringCatSheaf,
          HasProperSupport (U.ι ≫ p) G.obj ∧
          Nonempty (𝓖.obj ≅ ((completionFunctor (U : Scheme.{u})
            ((baseIdealSheaf A I p).comap U.ι)).obj G).obj) := by
  let : IsProper p := isProper_of_isProjectiveMorphism p hp
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
  exact exists_hasProperSupport_iso_completionFunctor_of_isProjectiveMorphism A I p hp U
    (fun F y hy hyI =>
      mem_supp_completionFunctor_obj_of_mem_supp (baseIdealSheaf A I p) F 0 hy hyI)
    (fun F => image_supp_restrictFunctor_eq U F)

end Stacks.Algebraization

end
