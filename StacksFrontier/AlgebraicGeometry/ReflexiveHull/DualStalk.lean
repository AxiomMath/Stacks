module

public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentReflexive
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# The dual of a module of finite presentation is reflexive

Let `X` be an integral locally Noetherian scheme and let `F` be an `𝒪_X`-module.  If `F`, its
dual `F^∨` and its reflexive hull `F^∨∨` are all of finite presentation, then `F^∨` is
reflexive.  This is the instance at `𝒢 = 𝒪_X` of [Stacks, Tag
0AY4](https://stacks.math.columbia.edu/tag/0AY4), which is the input that the reflexive-hull
adjunction of [Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH) needs.

Consequently the adjunction of Tag 0EBH follows from the *single* remaining assumption that the
dual of a coherent module is coherent, which is Tag 01Y2 at `𝒢 = 𝒪_X`: that is
`reflexiveHullAdjunctionOfCoherentDual`, where `reflexiveHullAdjunctionOfDual` of
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/Adjunction.lean` still needed two.

## Method

Reflexivity is `IsIso (toDoubleDual (dualSheaf F))`, and `isIso_of_bijective_stalkHom` reduces
it to bijectivity of the map of stalks at every point.  The canonical map of a dual module is
always a split monomorphism (`toDoubleDual_dualMap_comp`), so the stalk map `s` is injective and
its retraction `r` is surjective; what has to be shown is that `r` is injective.  That follows
from a *counting* argument rather than from any compatibility of the stalk maps with the
algebraic evaluation map: Tag 01CP (`dualStalkEquiv`) identifies the stalks of `F^∨`, `F^∨∨` and
`F^∨∨∨` with the iterated `𝒪_{X,x}`-duals of `M = F_x`, Tag 0AV3
(`isReflexive_linearMap`) says that `Hom(M, 𝒪_{X,x})` is a reflexive module over the Noetherian
domain `𝒪_{X,x}`, and therefore the stalk of `F^∨∨∨` is *abstractly* isomorphic to the stalk of
`F^∨`.  Composing `r` with such an isomorphism gives a surjective endomorphism of a Noetherian
module, which is injective.

This is why the finite-presentation hypotheses on `F^∨` and `F^∨∨` are present: Tag 01CP
computes the stalk of `SheafHom(G, 𝒪_X)` only for `G` of finite presentation, and the argument
applies it at `G = F`, `G = F^∨` and `G = F^∨∨`.  They are hypotheses rather than consequences
because the library has no route to coherence, or finite presentation, of a dual.  That is *not*
for want of Tag 01XZ, which is proved: coherence of `𝒪_X` on a locally Noetherian scheme is
`Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent`, and the equivalence of
coherence with finite presentation is `coherent_tfae`, both in
`StacksFrontier/AlgebraicGeometry/CoherenceCriteria/Basic.lean`.  The other input is the *first*
assertion of Tag 01CQ, that the dual of a module of finite presentation is locally the kernel of
a morphism between finite direct sums of copies of `𝒪_X`;
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/CoherentDual.lean` carries that assertion as the
hypothesis `HasLocalKernelPresentationDual`, and
`Stacks.AlgebraicGeometry.ReflexiveModules.hasLocalKernelPresentationDual` proves it
unconditionally for every scheme, so the hypotheses of this file are met by every coherent
module on an integral locally Noetherian scheme.

## Main definitions

* `oneGerm X x` and `unitStalkEquiv X x`: the germ of the unit section of `𝒪_X` as an element of
  the stalk of `𝒪_X` *as a module over itself*, and the resulting identification of that stalk
  with the local ring.
* `stalkHom f x`: the map of stalks induced by a morphism of `𝒪_X`-modules, as an
  `𝒪_{X,x}`-linear map.

`dualSheafHom F`, the dual `F^∨` packaged as a `SheafHom` of Tag 01CO, and `dualStalkEquiv F x`,
Tag 01CP for the dual, are taken from
`StacksFrontier/AlgebraicGeometry/Reflexive/ExtensionChain/StalkCriterion.lean`; the proofs below
use them at `F`, `F^∨` and `F^∨∨`.

## Main results

* `isIso_of_bijective_stalkHom`: a morphism of `𝒪_X`-modules whose maps of stalks are all
  bijective is an isomorphism.
* `isReflexive_dualSheaf_of_isFinitePresentation`: the dual of a module of finite presentation
  whose dual and reflexive hull are of finite presentation is reflexive, on an integral locally
  Noetherian scheme.
* `isReflexive_dualSheaf_of_isCoherent`: the same conclusion for a coherent module, granted that
  duals of coherent modules are coherent.
* `reflexiveHullAdjunctionOfCoherentDual`: Tag 0EBH's adjunction from that one assumption.

## Implementation notes

`stalkHom f x` is `Stacks.SheafOfModules.SheafHomStalk.stalkLinearMap` at the slice site over
`⊤`; the point of the abbreviation is that a *global* morphism can be fed to it, and that the
resulting linear maps compose (`stalkHom_comp`).  Its underlying function is the one Mathlib's
stalk functor on abelian sheaves produces (`stalkFunctor_map_apply`), which is what connects it
to the stalkwise criterion `ExtensionByZeroModules.isIso_of_stalk_isIso`.

`unitStalkEquiv` is proved from scratch rather than transported from
`Stacks.SheafOfModules.unitStalkLinearEquiv`: the latter is stated for the module structure on
the stalk built in Tag 01CB, which is equal to but not syntactically Mathlib's, and the
transport costs more than the thirty lines of germ chase it would save.

The tag of Tag 0AY4 is withheld.  Tag 0AY4 asserts that `SheafHom(ℱ, 𝒢)` is reflexive for
coherent `ℱ` and coherent reflexive `𝒢`, with no finite-presentation hypothesis on the dual; the
statement proved here is its `𝒢 = 𝒪_X` instance with those hypotheses added.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0AV3](https://stacks.math.columbia.edu/tag/0AV3)
* [Stacks Project, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}}

/-! ### The dual as a `SheafHom` -/

/-- The object underlying `dualSheafHom F` is the dual module. -/
public theorem dualSheafHom_obj (F : X.Modules) : (dualSheafHom F).obj = dualSheaf F := rfl

/-! ### The stalk of the structure sheaf as a module over itself -/

/-- The germ at `x` of the unit section of `𝒪_X`, as an element of the stalk at `x` of the
structure sheaf viewed as a module over itself. -/
public noncomputable def oneGerm (X : Scheme.{u}) (x : X) : modStalk (unitModule X) x :=
  germAt (unitModule X) ⊤ x trivial (oneSection X ⊤)

/-- The unit section has the same germ over every open neighbourhood. -/
public theorem germAt_oneSection (X : Scheme.{u}) (x : X) (W : X.Opens) (hxW : x ∈ W) :
    germAt (unitModule X) W x hxW (oneSection X W) = oneGerm X x := by
  rw [oneGerm, ← germAt_resLE (unitModule X) (le_top (a := W)) hxW (oneSection X ⊤)]
  exact (congrArg _ (map_oneSection X (homOfLE (le_top (a := W))))).symm

/-- The germ at `x` of a local function, at the `ringStalk` spelling of the local ring. -/
public noncomputable abbrev ringGermAt (X : Scheme.{u}) (W : X.Opens) (x : X) (hxW : x ∈ W)
    (a : Γ(X, W)) : ringStalk X.sheaf x :=
  TopCat.Presheaf.germ X.sheaf.obj W x hxW a

/-- A germ of the structure sheaf *as a module over itself* is the germ of the corresponding
function acting on the germ of the unit section. -/
public theorem germAt_eq_smul_oneGerm {X : Scheme.{u}} {x : X} (W : X.Opens) (hxW : x ∈ W)
    (a : Γ(X, W)) :
    germAt (unitModule X) W x hxW a = ringGermAt X W x hxW a • oneGerm X x := by
  rw [← germAt_oneSection X x W hxW, ← germAt_smul (unitModule X) hxW a (oneSection X W)]
  exact congrArg _ (mul_one a).symm

/-- **The stalk of the structure sheaf, as a module over itself, is free of rank one** on the
germ of the unit section.  Surjectivity is `germAt_eq_smul_oneGerm`; injectivity is the
observation that a function whose germ annihilates the unit germ vanishes on a neighbourhood. -/
public noncomputable def unitStalkEquiv (X : Scheme.{u}) (x : X) :
    ringStalk X.sheaf x ≃ₗ[ringStalk X.sheaf x] modStalk (unitModule X) x :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (ringStalk X.sheaf x) _ (oneGerm X x)) <| by
  refine ⟨(injective_iff_map_eq_zero _).mpr ?_, ?_⟩
  · intro a ha
    obtain ⟨W, hxW, α, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.sheaf.obj a
    have h0 : germAt (unitModule X) W x hxW α = germAt (unitModule X) W x hxW 0 := by
      rw [germAt_eq_smul_oneGerm W hxW α, germAt_zero]
      exact ha
    obtain ⟨V, hxV, iV, jV, hV⟩ :=
      TopCat.Presheaf.germ_eq (C := Ab.{u}) (unitModule X).val.presheaf x hxW hxW α 0 h0
    have hres : (ConcreteCategory.hom (X.sheaf.obj.map iV.op)) α = 0 :=
      hV.trans (map_zero ((unitModule X).val.presheaf.map jV.op).hom)
    have hg := TopCat.Presheaf.germ_res_apply X.sheaf.obj iV x hxV α
    rw [hres, map_zero] at hg
    exact hg.symm
  · intro q
    obtain ⟨W, hxW, α, rfl⟩ := exists_germ_eq (unitModule X) q
    exact ⟨ringGermAt X W x hxW α, (germAt_eq_smul_oneGerm W hxW α).symm⟩

/-- `unitStalkEquiv` is the canonical identification: it takes the germ of a function, read as a
section of `𝒪_X` over itself, back to the germ of that function. -/
public theorem unitStalkEquiv_symm_germAt (X : Scheme.{u}) (x : X) (W : X.Opens) (hxW : x ∈ W)
    (a : Γ(X, W)) :
    (unitStalkEquiv X x).symm (germAt (unitModule X) W x hxW a) = ringGermAt X W x hxW a := by
  rw [LinearEquiv.symm_apply_eq]
  exact germAt_eq_smul_oneGerm W hxW a

/-! ### Stalks of a morphism of modules -/

/-- The map of stalks at `x` induced by a morphism of `𝒪_X`-modules, as an `𝒪_{X,x}`-linear
map.  This is `stalkLinearMap` at the slice site over `⊤`. -/
public noncomputable def stalkHom {F G : X.Modules} (f : F ⟶ G) (x : X) :
    modStalk F x →ₗ[ringStalk X.sheaf x] modStalk G x :=
  stalkLinearMap (f.over ⊤) (Opens.mem_top x)

/-- The defining germ formula for `stalkHom`. -/
public theorem stalkHom_germAt {F G : X.Modules} (f : F ⟶ G) (x : X) (W : X.Opens)
    (hxW : x ∈ W) (t : Γ(F, W)) :
    stalkHom f x (germAt F W x hxW t) =
      germAt G W x hxW (Scheme.Modules.Hom.app f W t) :=
  stalkMap_germ (f.over ⊤) (Opens.mem_top x) (le_top (a := W)) hxW t

/-- Taking stalks is functorial. -/
public theorem stalkHom_comp {F G H : X.Modules} (f : F ⟶ G) (g : G ⟶ H) (x : X) :
    stalkHom (f ≫ g) x = (stalkHom g x).comp (stalkHom f x) := by
  refine linearMap_ext fun W hxW t => ?_
  rw [stalkHom_germAt (f ≫ g) x W hxW t, LinearMap.comp_apply,
    stalkHom_germAt f x W hxW t, stalkHom_germAt g x W hxW _]
  rfl

/-- Taking stalks preserves identities. -/
public theorem stalkHom_id (F : X.Modules) (x : X) :
    stalkHom (𝟙 F) x = LinearMap.id := by
  refine linearMap_ext fun W hxW t => ?_
  rw [stalkHom_germAt (𝟙 F) x W hxW t]
  rfl

/-- `stalkHom f x` is the map that Mathlib's stalk functor on abelian sheaves produces, with its
`𝒪_{X,x}`-linearity recorded. -/
public theorem stalkFunctor_map_apply {F G : X.Modules} (f : F ⟶ G) (x : X)
    (m : modStalk F x) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} x).map
        ((ExtensionByZeroModules.toAb (structureSheaf X.sheaf)).map f) m = stalkHom f x m := by
  obtain ⟨W, hxW, t, rfl⟩ := exists_germ_eq F m
  refine Eq.trans ?_ (stalkHom_germAt f x W hxW t).symm
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply (C := Ab.{u}) W x hxW
    ((ExtensionByZeroModules.toAb (structureSheaf X.sheaf)).map f) t

/-- **A morphism of `𝒪_X`-modules which is bijective on every stalk is an isomorphism.** -/
public theorem isIso_of_bijective_stalkHom {F G : X.Modules} (f : F ⟶ G)
    (h : ∀ x : X, Function.Bijective (stalkHom f x)) : IsIso f := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso (structureSheaf X.sheaf) f fun x => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => (h x).1 ?_, fun m => ?_⟩
  · exact ((stalkFunctor_map_apply f x a).symm.trans hab).trans
      (stalkFunctor_map_apply f x b)
  · obtain ⟨a, ha⟩ := (h x).2 m
    exact ⟨a, (stalkFunctor_map_apply f x a).trans ha⟩

/-! ### Reflexivity of the dual -/

/-- **The dual of a module of finite presentation is reflexive**, on an integral locally
Noetherian scheme, provided the dual and the reflexive hull are of finite presentation as well.

The canonical map `j : F^∨ ⟶ F^∨∨∨` is split by the dual of the canonical map of `F`, so its
stalk map `s` has a surjective retraction `r`.  Tag 01CP identifies the stalks of `F^∨` and
`F^∨∨∨` with `Hom(M, R)` and its double `R`-dual, where `M = F_x` is a finite module over the
Noetherian domain `R = 𝒪_{X,x}`; by Tag 0AV3 the first of those is a reflexive module, so the
two stalks are abstractly isomorphic.  Composing `r` with such an isomorphism gives a surjective
endomorphism of a Noetherian module, hence an injective one, so `r` is injective and `s` is
bijective. -/
public theorem isReflexive_dualSheaf_of_isFinitePresentation (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsFiniteType] [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation]
    [(dualSheaf (dualSheaf F)).IsFinitePresentation] :
    IsReflexive (dualSheaf F) := by
  refine isIso_of_bijective_stalkHom _ fun x => ?_
  -- The local ring at `x` is a Noetherian domain and the stalk of `F` is a finite module.
  have hdom : IsDomain (ringStalk X.sheaf x) := by
    show IsDomain (X.presheaf.stalk x); infer_instance
  have hnoe : IsNoetherianRing (ringStalk X.sheaf x) := by
    show IsNoetherianRing (X.presheaf.stalk x); infer_instance
  have : Module.Finite (ringStalk X.sheaf x) (modStalk F x) :=
    SheafOfModules.finite_stalk X.sheaf F x
  -- Tag 0AV3: the dual of the stalk is a reflexive module.
  have : Module.IsReflexive (ringStalk X.sheaf x)
      (modStalk F x →ₗ[ringStalk X.sheaf x] ringStalk X.sheaf x) :=
    isReflexive_linearMap inferInstance
  -- Tag 01CP at `F`, at `F^∨` and at `F^∨∨`, composed into an abstract isomorphism between the
  -- stalks of `F^∨∨∨` and of `F^∨`.
  set R := ringStalk X.sheaf x with hR
  let e1 : modStalk (dualSheaf F) x ≃ₗ[R] (modStalk F x →ₗ[R] R) := dualStalkEquiv F x
  let d2 : modStalk (dualSheaf (dualSheaf F)) x ≃ₗ[R] (modStalk (dualSheaf F) x →ₗ[R] R) :=
    dualStalkEquiv (dualSheaf F) x
  let d3 : modStalk (dualSheaf (dualSheaf (dualSheaf F))) x ≃ₗ[R]
      (modStalk (dualSheaf (dualSheaf F)) x →ₗ[R] R) :=
    dualStalkEquiv (dualSheaf (dualSheaf F)) x
  let e2 := d2.trans (LinearEquiv.arrowCongr e1 (LinearEquiv.refl R R))
  let e3 := d3.trans (LinearEquiv.arrowCongr e2 (LinearEquiv.refl R R))
  let e : modStalk (dualSheaf (dualSheaf (dualSheaf F))) x ≃ₗ[R] modStalk (dualSheaf F) x :=
    e3.trans ((Module.evalEquiv R (modStalk F x →ₗ[R] R)).symm.trans e1.symm)
  -- The stalk of the canonical map is split.
  let s := stalkHom (toDoubleDual (dualSheaf F)) x
  let r := stalkHom (dualMap (toDoubleDual F)) x
  have hsplit : r.comp s = LinearMap.id := by
    rw [← stalkHom_comp, toDoubleDual_dualMap_comp F, stalkHom_id]
  have hrs : ∀ a, r (s a) = a := fun a => LinearMap.congr_fun hsplit a
  have : IsNoetherian R (modStalk (dualSheaf F) x) :=
    isNoetherian_of_linearEquiv e1.symm
  -- A surjective endomorphism of a Noetherian module is injective.
  have hrsurj : Function.Surjective r := fun a => ⟨s a, hrs a⟩
  have hinj : Function.Injective (r.comp (e.symm : _ →ₗ[R] _)) :=
    IsNoetherian.injective_of_surjective_endomorphism _
      (hrsurj.comp (e.symm.surjective))
  have hrinj : Function.Injective r := fun a b hab =>
    e.injective (hinj (by simpa using hab))
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · rw [← hrs a, ← hrs b, hab]
  · exact ⟨r b, hrinj (by rw [hrs (r b)])⟩

/-- **The dual of a coherent module is reflexive**, on an integral locally Noetherian scheme,
granted that the dual of a coherent module is coherent.  That assumption is Tag 01Y2 at
`𝒢 = 𝒪_X`; it is used only to supply the finite-presentation hypotheses of
`isReflexive_dualSheaf_of_isFinitePresentation`, through Tag 01BW. -/
public theorem isReflexive_dualSheaf_of_isCoherent (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X]
    (hDualCoh : ∀ G : X.Modules, _root_.Stacks.SheafOfModules.IsCoherent G →
      _root_.Stacks.SheafOfModules.IsCoherent (dualSheaf G))
    (F : X.Modules) (hF : _root_.Stacks.SheafOfModules.IsCoherent F) :
    IsReflexive (dualSheaf F) := by
  have key : ∀ G : X.Modules, _root_.Stacks.SheafOfModules.IsCoherent G →
      G.IsFinitePresentation := fun G hG => by
    have := _root_.Stacks.SheafOfModules.IsCoherent.sheafOfModules G hG
    exact _root_.isFinitePresentation_of_isCoherent G
  have h1 := hDualCoh F hF
  have : F.IsFinitePresentation := key F hF
  have : (dualSheaf F).IsFinitePresentation := key _ h1
  have : (dualSheaf (dualSheaf F)).IsFinitePresentation := key _ (hDualCoh _ h1)
  have : F.IsFiniteType := by
    have := _root_.Stacks.SheafOfModules.IsCoherent.sheafOfModules F hF
    exact _root_.SheafOfModules.IsCoherent.isFiniteType
  exact isReflexive_dualSheaf_of_isFinitePresentation X F

/-- **Stacks, Tag 0EBH, the adjunction**, on an integral locally Noetherian scheme, from the
single assumption that the dual of a coherent module is coherent — Tag 01Y2 at `𝒢 = 𝒪_X`.

`reflexiveHullAdjunctionOfDual` needs the reflexivity of the dual as a second assumption; here
it is supplied by `isReflexive_dualSheaf_of_isCoherent`.  The tag is withheld for the same
reason as there: the conclusion implies the hypothesis, so the statement is weaker than Tag
0EBH. -/
public noncomputable def reflexiveHullAdjunctionOfCoherentDual (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X]
    (hDualCoh : ∀ F : X.Modules, _root_.Stacks.SheafOfModules.IsCoherent F →
      _root_.Stacks.SheafOfModules.IsCoherent (dualSheaf F)) :
    { p : (Σ L : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
        CoherentReflexiveModules X, L ⊣ CoherentReflexiveModules.ι X) //
      ∀ F : _root_.Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
        ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
          (p.2.unit.app F).hom ≫ eqToHom h = toDoubleDual F.obj } :=
  reflexiveHullAdjunctionOfDual X hDualCoh (isReflexive_dualSheaf_of_isCoherent X hDualCoh)

end Stacks.AlgebraicGeometry.ReflexiveModules

end
