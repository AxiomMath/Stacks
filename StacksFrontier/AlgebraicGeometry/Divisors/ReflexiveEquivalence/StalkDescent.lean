module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth

/-!
# Reflexivity is a condition on the stalks, and it descends from an open subscheme

Let `X` be a scheme and `F` an `𝒪_X`-module of finite presentation whose dual is also of finite
presentation — on a locally Noetherian scheme that is automatic for a coherent `F`, by
`Stacks.AlgebraicGeometry.ReflexiveModules.isFinitePresentation_dualSheaf`.  The canonical map
`j : F ⟶ F^∨∨` is then an isomorphism exactly when every stalk `F_x` is a reflexive
`𝒪_{X,x}`-module.

`StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion` proves one direction
of this, namely [Stacks, Tag 0AY3] (1) ⇒ (2), by identifying the stalk of `j` with the algebraic
evaluation map `F_x ⟶ (F_x)^∨∨`; that identification is
`dualStalkEquiv_eq_dualStalkEquiv_toDoubleDual`.  This file proves the converse, (2) ⇒ (1).  The
identification is an equality of two maps into the same module, so it exhibits the stalk of `j`
as the algebraic evaluation map *conjugated by two isomorphisms* — `doubleDualStalkEquiv` is
that conjugator and `doubleDualStalkEquiv_stalkMapOfHom` is the equation — and bijectivity
therefore transfers in both directions.  Globalizing from stalks to the sheaf is
`isIso_of_forall_isIso_stalkMapOfHom`.

The second half of the file is the descent statement this converse was wanted for.  If `F|_U` is
reflexive then the stalks of `F` at the points of `U` are reflexive, so the restriction of `j`
to `U` is an isomorphism (`isIso_restrict_toDoubleDual`); if in addition `F` and `F^∨∨` both
have depth at least two at every point outside `U`, then both are recovered from their
restrictions by Hartogs extension
(`AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two`, which is
[Stacks, Tag 0E9I]), and `j` itself is an isomorphism.  That is
`isReflexive_of_isReflexive_restrict`, the step through which the extension of coherent
reflexive modules across a depth-two complement reduces to the situation over `U`.

Its two depth hypotheses are not an extra burden on the caller.  `two_le_depth_dualSheaf_stalk`
derives depth two for `F^∨` from depth two for `𝒪_X` alone, by reading the stalk of `F^∨` as the
linear dual of the stalk of `F` ([Stacks, Tag 01CP]) and applying the algebraic
`one_le_depth_and_two_le_depth_linearMap`; applied twice this is
`two_le_depth_doubleDual_stalk`, and `isReflexive_doubleDual_of_isReflexive_restrict` is the
resulting unconditional statement: *the reflexive hull of a coherent module whose restriction to
`U` is reflexive is reflexive, as soon as `𝒪_X` has depth two outside `U`*.  So the general
internal-hom depth statement of [Stacks, Tag 0EBC] is **not needed** for this route — only its
dual case, which `dualStalkEquiv` already supplies.

Passing from a stalk of `F|_U` to a stalk of `F` changes the base ring, from `𝒪_{U,u}` to
`𝒪_{X,u}`, so the comparison is *semilinear* over the stalk map of the open immersion; that is
`restrictStalkSemilinearEquiv`, and the transport of reflexivity across it is
`isReflexive_of_semilinearEquiv`.

## Main definitions

* `doubleDualStalkEquiv F x` — the stalk `(F^∨∨)_x` as the double dual of the stalk `F_x`.
* `stalkLinearMapOfHom f x`, `stalkLinearEquivOfIso e x` — the map, respectively the
  equivalence, induced on stalks by a morphism, respectively an isomorphism, of modules on a
  scheme, as a linear map over the local ring.
* `restrictStalkHom j F w` — the comparison `(F|_W)_w ⟶ F_{j w}` of stalks along an open
  immersion, and `restrictStalkSemilinearEquiv` the same map as a semilinear equivalence over
  `openImmersionStalkRingEquiv`.  The ring equivalence is named for the open immersion, not for
  the restriction, so that it is not confused with `LocallyFreeRank.restrictStalkRingEquiv`
  ([Stacks, Tag 01C9]), which compares the stalk of a restricted sheaf of rings on a ringed
  space with the stalk of the sheaf itself and is a different map.

## Main results

* `isCoherent_dualSheaf`, `isCoherent_doubleDual`, `isCoherent_restrict` — the dual, the double
  dual and the restriction to an open of a coherent module on a locally Noetherian scheme are
  coherent.
* `isReflexive_of_forall_isReflexive_stalk` — **[Stacks, Tag 0AY3], (2) implies (1)**.
* `isReflexive_of_iso` — reflexivity of a coherent module is invariant under isomorphism.
* `two_le_depth_dualSheaf_stalk`, `two_le_depth_doubleDual_stalk` — the depth-two clause of
  [Stacks, Tag 0EBC] for the internal hom into `𝒪_X`, and its iterate for the reflexive hull.
* `isIso_of_restrict_of_isIso_unit` — a morphism whose restriction to `U` is an isomorphism and
  whose source and target are both recovered from `U` by Hartogs extension is an isomorphism.
* `isReflexive_of_isReflexive_restrict` — reflexivity descends from an open subscheme whose
  complement carries depth at least two.
* `isReflexive_doubleDual_of_isReflexive_restrict` — the same descent with both depth
  hypotheses discharged: the reflexive hull of a coherent module reflexive over `U` is
  reflexive whenever `𝒪_X` has depth two outside `U`.

## Implementation notes

**No `@[stacks 0AY3]` attribute is placed.** Tag 0AY3 is a three-way equivalence of conditions
on a coherent module over an integral locally Noetherian scheme; what is proved here is the
single implication (2) ⇒ (1), with (3) absent, so an attribute would make the dashboard read
the whole equivalence as formalized.  The same applies to 0AVU, whose three pieces are discussed
in `StacksFrontier/AlgebraicGeometry/Reflexive/DoubleDual.lean`, and to 01Y2, whose
tensor-product clause is not proved here.

`isReflexive_of_semilinearEquiv` takes its two `RingHomInvPair` arguments as instance
hypotheses rather than finding them: `RingHomInvPair.of_ringEquiv` is deliberately *not* an
instance in Mathlib (it would loop), so the semilinear binder cannot even be elaborated without
them and they have to be supplied at each use site.

`isIso_of_forall_isIso_stalkMapOfHom` reflects along `Scheme.Modules.toPresheaf`, not along
`SheafOfModules.toSheaf`.  `Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` and
carries its own category instance, so the `ReflectsIsomorphisms` instance Mathlib states for
`SheafOfModules.toSheaf` is not found at the `X.Modules` spelling, whereas the one Mathlib
states for `Scheme.Modules.toPresheaf` is.  The sheaf morphism the stalkwise criterion needs is
therefore assembled by hand from the underlying morphism of presheaves.

Two declarations here are public versions of computations this library already carries, in
each case only as `private` lemmas that nothing outside their own file can use.
`restrictStalkHom_smul` and `stalkMapOfHom_smul` are `restrictStalkMap_smul` and
`stalkMap_smul` of `StacksFrontier/AlgebraicGeometry/Morphisms/Flat/QuasicoherentCriteria.lean`
and of `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FlatLocus.lean` — two private
copies each — and both groups should be consolidated onto the public one here.  The depth
invariance this file used to restate is `Module.depth_eq_depth_of_linearEquiv` of
`StacksFrontier/RingTheory/Depth/Defs/Defs.lean`, the module that defines `Module.depth`, and is
used from there.

`stalkLinearMapOfHom` is the `Scheme.Modules` map; the deeply namespaced definition of the same
short name in `StacksFrontier/Topology/Sheaves/Sheafify/ModuleStalkTensor.lean` is the
corresponding construction for presheaves of modules on a space and is a different statement.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveEquivalence

variable {X : Scheme.{u}}

/-! ### Coherence of the dual and of the double dual -/

/-- **[Stacks, Tag 01Y2] for the dual.** The dual `F^∨ = SheafHom(F, 𝒪_X)` of a coherent module
on a locally Noetherian scheme is coherent: `F` is of finite presentation, the structure sheaf
is coherent, and the internal hom between such modules is coherent by [Stacks, Tag 01CQ]. -/
public lemma isCoherent_dualSheaf [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] :
    _root_.SheafOfModules.IsCoherent (dualSheaf F) :=
  @Stacks.SheafOfModules.InternalHom.isCoherent_sheafInternalHom'.{u} X inferInstance X.sheaf F
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.SheafOfModules.InternalHom.spaceRingedSite X.sheaf).O))
    (isFinitePresentation_of_isCoherent F)
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit

/-- **[Stacks, Tag 01Y2] for the double dual.** The reflexive hull `F^∨∨` of a coherent module
on a locally Noetherian scheme is coherent.  This is the coherence half of the hull assertion of
[Stacks, Tag 0EBH]. -/
@[stacks 0EBH "hull"]
public lemma isCoherent_doubleDual [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] :
    _root_.SheafOfModules.IsCoherent (dualSheaf (dualSheaf F)) :=
  have := isCoherent_dualSheaf F
  isCoherent_dualSheaf (dualSheaf F)

/-- The restriction of a coherent module to an open subscheme is coherent. -/
public lemma isCoherent_restrict [IsLocallyNoetherian X] (U : X.Opens) (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] :
    _root_.SheafOfModules.IsCoherent (F.restrict U.ι) :=
  have _hUnoeth : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have _hpull := AlgebraicGeometry.isCoherent_pullback U.ι F
  have hresfp : (F.restrict U.ι).IsFinitePresentation :=
    (_root_.SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm
      (isFinitePresentation_of_isCoherent _)
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation _ hresfp

/-! ### The stalk of the double dual -/

/-- The stalk of `F^∨∨` at `x`, read as the double dual of the stalk of `F`: [Stacks, Tag 01CP]
applied to `F` and then to `F^∨`. -/
public noncomputable def doubleDualStalkEquiv (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X) :
    (dualSheaf (dualSheaf F)).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      Module.Dual (X.presheaf.stalk x)
        (Module.Dual (X.presheaf.stalk x) (F.presheaf.stalk x)) :=
  (dualStalkEquiv (dualSheaf F) x).trans (LinearEquiv.dualMap (dualStalkEquiv F x).symm)

/-- **The stalk of the canonical map `F ⟶ F^∨∨` is the algebraic evaluation map.** Under the
identifications of [Stacks, Tag 01CP] the map induced on stalks by `toDoubleDual F` is
`Module.Dual.eval`.  This is the two-sided form of
`dualStalkEquiv_eq_dualStalkEquiv_toDoubleDual`, and it is what makes bijectivity transfer in
both directions between the sheaf and its stalks. -/
public lemma doubleDualStalkEquiv_stalkMapOfHom (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X) (m : F.presheaf.stalk x) :
    doubleDualStalkEquiv F x (stalkMapOfHom (toDoubleDual F) x m) =
      Module.Dual.eval (X.presheaf.stalk x) (F.presheaf.stalk x) m := by
  refine LinearMap.ext fun lam => ?_
  show (dualStalkEquiv F x).symm.dualMap
      (dualStalkEquiv (dualSheaf F) x (stalkMapOfHom (toDoubleDual F) x m)) lam = _
  rw [LinearEquiv.dualMap_apply]
  have h := dualStalkEquiv_eq_dualStalkEquiv_toDoubleDual F x m ((dualStalkEquiv F x).symm lam)
  rw [(dualStalkEquiv F x).apply_symm_apply] at h
  exact h.symm

/-- **[Stacks, Tag 0AY3], (2) implies (1), at a point.** If the stalk of `F` at `x` is a
reflexive module over the local ring there, the map induced on stalks by `toDoubleDual F` is
bijective. -/
public lemma bijective_stalkMapOfHom_toDoubleDual (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X)
    (h : Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    Function.Bijective (stalkMapOfHom (toDoubleDual F) x) := by
  have hcomp : Function.Bijective
      (fun m => doubleDualStalkEquiv F x (stalkMapOfHom (toDoubleDual F) x m)) := by
    simpa [funext (doubleDualStalkEquiv_stalkMapOfHom F x)] using
      Module.bijective_dual_eval (X.presheaf.stalk x) (F.presheaf.stalk x)
  exact (EquivLike.comp_bijective _ (doubleDualStalkEquiv F x)).mp hcomp

/-! ### From the stalks to the sheaf -/

/-- A morphism of modules on a scheme inducing an isomorphism on every stalk is an
isomorphism. -/
public lemma isIso_of_forall_isIso_stalkMapOfHom {F G : X.Modules} (f : F ⟶ G)
    (h : ∀ x : X, IsIso (stalkMapOfHom f x)) : IsIso f := by
  let Fs : TopCat.Sheaf Ab.{u} X := ⟨F.presheaf, F.isSheaf⟩
  let Gs : TopCat.Sheaf Ab.{u} X := ⟨G.presheaf, G.isSheaf⟩
  let fs : Fs ⟶ Gs := ⟨(Scheme.Modules.toPresheaf X).map f⟩
  have hst (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map fs.1) := h x
  have hfs : IsIso fs := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso fs
  have hpre : IsIso ((Scheme.Modules.toPresheaf X).map f) :=
    (TopCat.Sheaf.forget Ab.{u} _).map_isIso fs
  exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)

/-- A morphism of modules on a scheme inducing an isomorphism on the stalks at the points of the
range of an open immersion `j` restricts to an isomorphism along `j`. -/
public lemma isIso_restrict_of_isIso_stalkMapOfHom_on_range {W : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] {F G : X.Modules} (f : F ⟶ G)
    (h : ∀ x : X, x ∈ j.opensRange → IsIso (stalkMapOfHom f x)) :
    IsIso ((Scheme.Modules.restrictFunctor j).map f) := by
  refine isIso_of_forall_isIso_stalkMapOfHom _ fun w => ?_
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso j w) f).mpr
    (h (j w) ((Scheme.Hom.mem_opensRange).mpr ⟨w, rfl⟩))

/-- **[Stacks, Tag 0AY3], (2) implies (1).** A module of finite presentation whose dual is also
of finite presentation and all of whose stalks are reflexive is reflexive. -/
public theorem isReflexive_of_forall_isReflexive_stalk (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation]
    (h : ∀ x : X, Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    IsReflexive F :=
  isIso_of_forall_isIso_stalkMapOfHom _ fun x =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_stalkMapOfHom_toDoubleDual F x (h x))

/-! ### Linearity of the map induced on stalks, and reflexivity along an isomorphism -/

/-- The map induced on stalks by a morphism of modules on a scheme is linear over the local
ring.

This duplicates the `private` lemma `stalkMap_smul` of
`StacksFrontier/AlgebraicGeometry/Morphisms/Flat/QuasicoherentCriteria.lean` and of
`StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FlatLocus.lean`; being `private`
neither is usable here, and the three should be consolidated onto this public one. -/
public theorem stalkMapOfHom_smul {F G : X.Modules} (f : F ⟶ G) (x : X)
    (a : X.presheaf.stalk x) (m : F.presheaf.stalk x) :
    stalkMapOfHom f x (a • m) = a • stalkMapOfHom f x m := by
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, s, rfl⟩ := F.presheaf.exists_germ_eq m
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op r
  let sW : Γ(F, W) := F.presheaf.map (homOfLE inf_le_right).op s
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hxW r,
    ← F.presheaf.germ_res_apply (homOfLE inf_le_right) x hxW s]
  have hF : X.presheaf.germ W x hxW rW • F.presheaf.germ W x hxW sW =
      F.presheaf.germ W x hxW (rW • sW) :=
    (PresheafOfModules.germ_smul F.val x W hxW rW sW).symm
  have hnat (t : Γ(F, W)) :
      stalkMapOfHom f x (F.presheaf.germ W x hxW t) =
        G.presheaf.germ W x hxW (Scheme.Modules.Hom.app f W t) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW f.mapPresheaf t
  rw [hF, hnat, f.app_smul]
  have hG : G.presheaf.germ W x hxW (rW • Scheme.Modules.Hom.app f W sW) =
      X.presheaf.germ W x hxW rW • G.presheaf.germ W x hxW (Scheme.Modules.Hom.app f W sW) :=
    PresheafOfModules.germ_smul G.val x W hxW rW (Scheme.Modules.Hom.app f W sW)
  rw [hG, hnat]

/-- The map induced on stalks by a morphism of modules on a scheme, as a linear map over the
local ring. -/
public noncomputable def stalkLinearMapOfHom {F G : X.Modules} (f : F ⟶ G) (x : X) :
    F.presheaf.stalk x →ₗ[X.presheaf.stalk x] G.presheaf.stalk x where
  toFun := stalkMapOfHom f x
  map_add' := (stalkMapOfHom f x).hom.map_add
  map_smul' := stalkMapOfHom_smul f x

/-- An isomorphism of modules on a scheme induces a linear equivalence of stalks. -/
public noncomputable def stalkLinearEquivOfIso {F G : X.Modules} (e : F ≅ G) (x : X) :
    F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] G.presheaf.stalk x :=
  have _hiso : IsIso (stalkMapOfHom e.hom x) :=
    ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
      (X := F) (Y := G) e).isIso_hom
  LinearEquiv.ofBijective (stalkLinearMapOfHom e.hom x)
    (ConcreteCategory.bijective_of_isIso (stalkMapOfHom e.hom x))

/-- On a locally Noetherian scheme, a coherent module with reflexive stalk at `x` has the map
induced on that stalk by `toDoubleDual F` an isomorphism. -/
private theorem isIso_stalkMapOfHom_toDoubleDual_of_isCoherent [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (x : X)
    (h : Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    IsIso (stalkMapOfHom (toDoubleDual F) x) :=
  have _hFP : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have _hFD : (dualSheaf F).IsFinitePresentation := isFinitePresentation_dualSheaf F
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_stalkMapOfHom_toDoubleDual F x h)

/-- The stalks of a reflexive coherent module on a locally Noetherian scheme are reflexive. -/
private theorem isReflexive_stalk_of_isReflexive_of_isCoherent [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F) (x : X) :
    Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  have _hFP : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have _hFD : (dualSheaf F).IsFinitePresentation := isFinitePresentation_dualSheaf F
  isReflexive_stalk_of_isReflexive F hF x

/-- **Reflexivity is invariant under isomorphism.** Reflexivity of a coherent module on a
locally Noetherian scheme is a condition on its stalks, by the two implications of
[Stacks, Tag 0AY3] between (1) and (2), and an isomorphism induces linear equivalences of
stalks. -/
public theorem isReflexive_of_iso [IsLocallyNoetherian X] {F G : X.Modules}
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G] (e : F ≅ G)
    (hF : IsReflexive F) : IsReflexive G :=
  isIso_of_forall_isIso_stalkMapOfHom _ fun x =>
    have := isReflexive_stalk_of_isReflexive_of_isCoherent F hF x
    isIso_stalkMapOfHom_toDoubleDual_of_isCoherent G x (Module.equiv (stalkLinearEquivOfIso e x))

/-! ### Transport of reflexivity along a change of base ring -/

/-- Reflexivity of a module transports along a semilinear equivalence over a ring
equivalence. -/
public lemma isReflexive_of_semilinearEquiv {R S M N : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] (r : R ≃+* S)
    [RingHomInvPair (r : R →+* S) (r.symm : S →+* R)]
    [RingHomInvPair (r.symm : S →+* R) (r : R →+* S)]
    (e : M ≃ₛₗ[(r : R →+* S)] N) [Module.IsReflexive R M] :
    Module.IsReflexive S N := by
  let d : Module.Dual R M ≃ₛₗ[(r : R →+* S)] Module.Dual S N :=
    LinearEquiv.arrowCongr e r.toSemilinearEquiv
  let dd : Module.Dual R (Module.Dual R M) ≃ₛₗ[(r : R →+* S)]
      Module.Dual S (Module.Dual S N) :=
    LinearEquiv.arrowCongr d r.toSemilinearEquiv
  have h : ⇑(Module.Dual.eval S N) = dd ∘ Module.Dual.eval R M ∘ e.symm := by
    funext n
    ext l
    simp [dd, d, LinearEquiv.arrowCongr_apply, LinearEquiv.arrowCongr_symm_apply]
  constructor
  rw [h]
  exact dd.bijective.comp ((Module.bijective_dual_eval R M).comp e.symm.bijective)

/-! ### Stalks of a restricted module -/

/-- The comparison `(F|_W)_w ⟶ F_{j w}` of stalks along an open immersion `j : W ⟶ X`. -/
public noncomputable def restrictStalkHom {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W) :
    (F.restrict j).presheaf.stalk w ⟶ F.presheaf.stalk (j w) :=
  (Scheme.Modules.restrictStalkNatIso j w).hom.app F

/-- The comparison of stalks along an open immersion is semilinear over the stalk map of that
immersion. -/
public theorem restrictStalkHom_smul {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W) (a : X.presheaf.stalk (j w))
    (m : (F.restrict j).presheaf.stalk w) :
    restrictStalkHom j F w ((j.stalkMap w).hom a • m) = a • restrictStalkHom j F w m := by
  let G := F.restrict j
  obtain ⟨V, hV, r, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨T, hT, t, rfl⟩ := G.presheaf.exists_germ_eq m
  let T' : W.Opens := T ⊓ j ⁻¹ᵁ V
  have hT' : w ∈ T' := ⟨hT, hV⟩
  let r' : Γ(W, T') := W.presheaf.map (homOfLE inf_le_right).op (j.app V r)
  let t' : Γ(G, T') := G.presheaf.map (homOfLE inf_le_left).op t
  let J : X.Opens := j ''ᵁ T'
  have hJ : j w ∈ J := ⟨w, hT', rfl⟩
  have hJV : J ≤ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  let rJ : Γ(X, J) := X.presheaf.map (homOfLE hJV).op r
  have hr : (j.stalkMap w).hom (X.presheaf.germ V (j w) hV r) =
      W.presheaf.germ T' w hT' r' := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (W.presheaf.germ_res_apply (homOfLE inf_le_right) w hT' (j.app V r)).symm
  have hm : G.presheaf.germ T w hT t = G.presheaf.germ T' w hT' t' :=
    (G.presheaf.germ_res_apply (homOfLE inf_le_left) w hT' t).symm
  have hrJ : X.presheaf.germ V (j w) hV r = X.presheaf.germ J (j w) hJ rJ :=
    (X.presheaf.germ_res_apply (homOfLE hJV) (j w) hJ r).symm
  have hscalar : (j.appIso T').inv r' = rJ :=
    congrArg (fun z : Γ(X, V) ⟶ Γ(X, J) => z r)
      (Scheme.Hom.appLE_appIso_inv j (inf_le_right : T' ≤ j ⁻¹ᵁ V))
  let eT : Γ(G, T') ≅ Γ(F, J) := F.restrictAppIso j T'
  let tF : Γ(F, J) := eT.hom t'
  have hsection : eT.hom (r' • t') = rJ • tF := by
    rw [← hscalar]
    exact Scheme.Modules.smul_restrictAppIso_hom_apply j F T' r' t'
  rw [hr, hm, hrJ]
  calc
    _ = restrictStalkHom j F w (G.presheaf.germ T' w hT' (r' • t')) :=
      congrArg (restrictStalkHom j F w)
        (PresheafOfModules.germ_smul G.val w T' hT' r' t').symm
    _ = F.presheaf.germ J (j w) hJ (eT.hom (r' • t')) :=
      congrArg (fun z : Γ(G, T') ⟶ F.presheaf.stalk (j w) => z (r' • t'))
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app j w F hT')
    _ = F.presheaf.germ J (j w) hJ (rJ • tF) := by rw [hsection]
    _ = X.presheaf.germ J (j w) hJ rJ • F.presheaf.germ J (j w) hJ tF :=
      PresheafOfModules.germ_smul F.val (j w) J hJ rJ tF
    _ = _ :=
      congrArg (fun z => X.presheaf.germ J (j w) hJ rJ • z)
        (congrArg (fun z : Γ(G, T') ⟶ F.presheaf.stalk (j w) => z t')
          (Scheme.Modules.germ_restrictStalkNatIso_hom_app j w F hT')).symm

/-- The comparison of local rings along an open immersion, as a ring equivalence in the
direction that the comparison of stalks is semilinear over. -/
public noncomputable def openImmersionStalkRingEquiv {W : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] (w : W) : W.presheaf.stalk w ≃+* X.presheaf.stalk (j w) :=
  (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.symm

/-- The stalk of `F|_W` at `w` is the stalk of `F` at `j w`, semilinearly over
`openImmersionStalkRingEquiv`. -/
public noncomputable def restrictStalkSemilinearEquiv {W : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] (F : X.Modules) (w : W)
    [RingHomInvPair (openImmersionStalkRingEquiv j w :
      W.presheaf.stalk w →+* X.presheaf.stalk (j w))
      ((openImmersionStalkRingEquiv j w).symm :
        X.presheaf.stalk (j w) →+* W.presheaf.stalk w)]
    [RingHomInvPair ((openImmersionStalkRingEquiv j w).symm :
      X.presheaf.stalk (j w) →+* W.presheaf.stalk w)
      (openImmersionStalkRingEquiv j w : W.presheaf.stalk w →+* X.presheaf.stalk (j w))] :
    (F.restrict j).presheaf.stalk w ≃ₛₗ[(openImmersionStalkRingEquiv j w :
      W.presheaf.stalk w →+* X.presheaf.stalk (j w))] F.presheaf.stalk (j w) :=
  have hiso : IsIso (restrictStalkHom j F w) :=
    ((Scheme.Modules.restrictStalkNatIso j w).app F).isIso_hom
  LinearEquiv.ofBijective
    { toFun := restrictStalkHom j F w
      map_add' := (restrictStalkHom j F w).hom.map_add
      map_smul' := fun b m => by
        have h := restrictStalkHom_smul j F w (openImmersionStalkRingEquiv j w b) m
        rwa [show (j.stalkMap w).hom (openImmersionStalkRingEquiv j w b) = b from
          (openImmersionStalkRingEquiv j w).symm_apply_apply b] at h }
    (ConcreteCategory.bijective_of_isIso (restrictStalkHom j F w))

/-- A stalk of `F` at a point in the range of an open immersion `j` is reflexive as soon as the
corresponding stalk of `F|_W` is. -/
public lemma isReflexive_stalk_of_isReflexive_stalk_restrict {W : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] (F : X.Modules) (w : W)
    (h : Module.IsReflexive (W.presheaf.stalk w) ((F.restrict j).presheaf.stalk w)) :
    Module.IsReflexive (X.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) :=
  have : RingHomInvPair (openImmersionStalkRingEquiv j w :
      W.presheaf.stalk w →+* X.presheaf.stalk (j w))
    ((openImmersionStalkRingEquiv j w).symm :
      X.presheaf.stalk (j w) →+* W.presheaf.stalk w) :=
    RingHomInvPair.of_ringEquiv _
  have : RingHomInvPair ((openImmersionStalkRingEquiv j w).symm :
      X.presheaf.stalk (j w) →+* W.presheaf.stalk w)
    (openImmersionStalkRingEquiv j w : W.presheaf.stalk w →+* X.presheaf.stalk (j w)) :=
    RingHomInvPair.of_ringEquiv_symm _
  isReflexive_of_semilinearEquiv _ (restrictStalkSemilinearEquiv j F w)

/-! ### Descent of reflexivity across a depth-two complement -/

/-- **The restriction of the canonical map `F ⟶ F^∨∨` to an open on which `F` is reflexive is an
isomorphism.** Reflexivity of `F|_U` gives reflexive stalks of `F|_U` by [Stacks, Tag 0AY3]
(1) ⇒ (2), hence reflexive stalks of `F` at the points of `U`, hence bijectivity of the stalk
maps of `toDoubleDual F` there. -/
public theorem isIso_restrict_toDoubleDual [IsLocallyNoetherian X] (U : X.Opens)
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (hF : IsReflexive (F.restrict U.ι)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (toDoubleDual F)) := by
  have hUnoeth : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have := isCoherent_restrict U F
  refine isIso_restrict_of_isIso_stalkMapOfHom_on_range U.ι _ fun x hx => ?_
  obtain ⟨u, rfl⟩ := (Scheme.Hom.mem_opensRange).mp hx
  exact isIso_stalkMapOfHom_toDoubleDual_of_isCoherent F (U.ι u)
    (isReflexive_stalk_of_isReflexive_stalk_restrict U.ι F u
      (isReflexive_stalk_of_isReflexive_of_isCoherent (F.restrict U.ι) hF u))

/-- **Hartogs descent for isomorphisms.** A morphism `f : F ⟶ G` of modules on a scheme is an
isomorphism as soon as its restriction to an open `U` is one and both `F` and `G` are recovered
from `U` by the unit of the restriction--direct-image adjunction. -/
public theorem isIso_of_restrict_of_isIso_unit (U : X.Opens) {F G : X.Modules} (f : F ⟶ G)
    (hF : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F))
    (hG : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G))
    (hres : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) : IsIso f := by
  have hpull : IsIso ((Scheme.Modules.pullback U.ι).map f) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) f).mp hres
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.naturality f
  simp only [Functor.id_map, Functor.comp_map] at hnat
  have hcomp : IsIso (f ≫ (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right f
    ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G)

/-- **Reflexivity descends across a depth-two complement.** Let `F` be a coherent module on a
locally Noetherian scheme whose restriction to an open `U` is reflexive.  If `F` and its
reflexive hull `F^∨∨` both have depth at least two at every point outside `U`, then `F` is
reflexive.

This is the step through which the extension of coherent reflexive modules across a depth-two
complement ([Stacks, Tag 0EBJ]) and the coherence–reflexivity clause of [Stacks, Tag 0EY6]
reduce to the situation over `U`.  For `F` coherent and reflexive both depth hypotheses are
supplied by [Stacks, Tag 0EBI] part (1), `depth_stalk_ge_two_of_isReflexive`. -/
public theorem isReflexive_of_isReflexive_restrict [IsLocallyNoetherian X] (U : X.Opens)
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (hFU : IsReflexive (F.restrict U.ι))
    (hFdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x))
    (hHdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        ((dualSheaf (dualSheaf F)).presheaf.stalk x)) :
    IsReflexive F :=
  have : _root_.SheafOfModules.IsCoherent (dualSheaf (dualSheaf F)) := isCoherent_doubleDual F
  isIso_of_restrict_of_isIso_unit U (toDoubleDual F)
    (AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two X F U hFdepth)
    (AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two X
      (dualSheaf (dualSheaf F)) U hHdepth)
    (isIso_restrict_toDoubleDual U F hFU)

/-! ### Depth of the stalks of a dual -/

/-- **The dual of a coherent module inherits depth two from the structure sheaf.** This is the
depth-two clause of [Stacks, Tag 0EBC] in the case of the internal hom into `𝒪_X`, which is the
only case the extension of reflexive modules needs.  The stalk of `F^∨` is the linear dual of
the stalk of `F` by [Stacks, Tag 01CP] (`dualStalkEquiv`), and the depth of a module of linear
maps into a module of depth at least two is at least two
(`one_le_depth_and_two_le_depth_linearMap`, which is [Stacks, Tag 0AV5]). -/
public theorem two_le_depth_dualSheaf_stalk [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (x : X)
    (hx : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ((dualSheaf F).presheaf.stalk x) := by
  have hFP : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have hfin : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (dualStalkEquiv F x)]
  exact (one_le_depth_and_two_le_depth_linearMap
    (R := X.presheaf.stalk x) (M := F.presheaf.stalk x) (N := X.presheaf.stalk x)).2 hx

/-- **The reflexive hull of a coherent module inherits depth two from the structure sheaf.**
`two_le_depth_dualSheaf_stalk` applied twice.  This is the hypothesis `hHdepth` of
`isReflexive_of_isReflexive_restrict`, and supplying it this way is what lets the descent run
without the general internal-hom depth statement of [Stacks, Tag 0EBC]. -/
public theorem two_le_depth_doubleDual_stalk [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (x : X)
    (hx : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      ((dualSheaf (dualSheaf F)).presheaf.stalk x) :=
  have : _root_.SheafOfModules.IsCoherent (dualSheaf F) := isCoherent_dualSheaf F
  two_le_depth_dualSheaf_stalk (dualSheaf F) x hx

/-- **Reflexivity of the reflexive hull, across a depth-two complement.** If `F` is coherent on
a locally Noetherian scheme, `F|_U` is reflexive, and the structure sheaf has depth at least two
at every point outside `U`, then `F^∨∨` is reflexive.

Both depth hypotheses of `isReflexive_of_isReflexive_restrict` are discharged here by
`two_le_depth_doubleDual_stalk`, applied to `F` and to `F^∨∨`; the restriction of `F^∨∨` to `U`
is reflexive because `isIso_restrict_toDoubleDual` makes it isomorphic to `F|_U`. -/
public theorem isReflexive_doubleDual_of_isReflexive_restrict [IsLocallyNoetherian X]
    (U : X.Opens) (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (hFU : IsReflexive (F.restrict U.ι))
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    IsReflexive (dualSheaf (dualSheaf F)) := by
  have hH : _root_.SheafOfModules.IsCoherent (dualSheaf (dualSheaf F)) := isCoherent_doubleDual F
  have hUnoeth : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have hFres : _root_.SheafOfModules.IsCoherent (F.restrict U.ι) := isCoherent_restrict U F
  have hHres : _root_.SheafOfModules.IsCoherent ((dualSheaf (dualSheaf F)).restrict U.ι) :=
    isCoherent_restrict U (dualSheaf (dualSheaf F))
  have _hrestr : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (toDoubleDual F)) :=
    isIso_restrict_toDoubleDual U F hFU
  have hHU : IsReflexive ((dualSheaf (dualSheaf F)).restrict U.ι) :=
    isReflexive_of_iso (asIso ((Scheme.Modules.restrictFunctor U.ι).map (toDoubleDual F))) hFU
  exact isReflexive_of_isReflexive_restrict U (dualSheaf (dualSheaf F)) hHU
    (fun x hx => two_le_depth_doubleDual_stalk F x (hdepth x hx))
    (fun x hx => two_le_depth_doubleDual_stalk (dualSheaf (dualSheaf F)) x (hdepth x hx))

end Stacks.AlgebraicGeometry.ReflexiveEquivalence

end
