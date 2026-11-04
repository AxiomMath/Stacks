module

public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentExtensionOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FinitePresentationKernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence of the internal Hom on a ringed site

Let `X` be a ringed site and let `F`, `G` be sheaves of `𝒪_X`-modules.
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) asserts, for a ringed *space*,
that `𝓗om_{𝒪_X}(F, G)` is locally the kernel of a map between finite direct sums of copies of
`G`, and consequently that it is coherent as soon as `F` is of finite presentation and `G` is
coherent.  This file proves the coherence assertion on an arbitrary ringed site.

The kernel description is already available there:
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FinitePresentationKernel` proves that
internal Hom against `G` carries a finite coproduct in its first variable to a product and a
cokernel to a kernel, that `𝓗om(𝒪, G) ≅ G`, that a universe lift of the sections of both
arguments changes nothing, and Stacks 0E8H.  What is added here is the *coherence* conclusion,
and what it needs beyond that file is one closure property of coherence that was missing at the
module universe of the internal Hom — finite products — together with the two transfers of
coherence along a universe lift of the sections.

The proof is the source's.  Coherence is local on the site (Stacks 03DN), the internal Hom
commutes with restriction to a slice (Stacks 0E8H), and a coherent sheaf of modules has a finite
global presentation on each member of a family covering the final object; on such a member the
internal Hom out of the presented module is the kernel of a map between finite products of
copies of the target, and kernels and finite products of coherent modules are coherent
(Stacks 01BY(3)).

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_of_bijective_pi`: a sheaf of modules which is a
  **finite product of coherent sheaves of modules on sections** is coherent, at a free module
  universe.
* `Stacks.SheafOfModules.isCoherentOnSite_uliftForPresentation` and
  `Stacks.SheafOfModules.isCoherentOnSite_of_moduleULift`: coherence is unchanged by a universe
  lift of the sections, in both directions.
* `AlgebraicGeometry.RingedSite.bijective_internalHomPre_pi_app`: over every object, the
  sections of the internal Hom out of a finite coproduct are the product of the sections of the
  internal Homs out of the summands.
* `AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheaf_cofan`,
  `..._of_presentation` and `..._of_hasFiniteGlobalPresentation`: **Stacks 01CQ(2) on a ringed
  site** for a module which is a finite coproduct of copies of the structure sheaf, which is
  presented by two such, and which has a finite global presentation.
* `AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheaf`: **Stacks 01CQ(2) on a ringed
  site** — the internal Hom of two coherent sheaves of modules is coherent.

## Implementation notes

**No `@[stacks 01CQ]` attribute is carried.**  That tag is about a ringed space, where both of
its assertions are proved — `Stacks.SheafOfModules.sheafHom_locallyKernelFiniteCoproduct` and
`Stacks.SheafOfModules.sheafHom_isCoherent` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice`, and again through
`StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel`.  What is new here is the
site-level statement, which is not what the tag says.

**Why finite products of coherent modules had to be proved again.**  The module universe of the
internal Hom of a ringed site with objects in `Type u`, morphisms in `Type v` and coefficient
rings in `CommRingCat.{w}` is `max u v m`, never `m`; so every closure property of coherence
used here has to hold at a module universe *above* the universe of the coefficient rings.
Kernels (`Stacks.SheafOfModules.isCoherentOnSite_kernel`), extensions
(`Stacks.SheafOfModules.isCoherentOnSite_middle`) and isomorphisms
(`Stacks.SheafOfModules.isCoherentOnSite_of_iso`) are all available there.  Finite **products**
were not: `Stacks.SheafOfModules.isCoherentOnSite_biprod` and
`Stacks.SheafOfModules.isCoherentOnSite_pi` are stated at the module universe of the coefficient
rings, and that pin is not an artefact of their binders — relaxing it in place was tried and
fails.  Their proof compares the relations among a finite family of sections of the product with
the relations among the first components, through a morphism *out of the relations presheaf and
into the second factor*; the relations presheaf takes values in modules over the coefficient
rings, so its target has to live in the ring universe.
`Stacks.SheafOfModules.isCoherentOnSite_of_bijective_pi` proves the finite-product case by a
route which needs no such comparison: it peels one factor off at a time and reads the remaining
factors as the kernel of the projection onto it, so the only inputs are
`Stacks.SheafOfModules.isCoherentOnSite_middle` and the sectionwise description of that kernel,
both at a free module universe.

**Why the product is given on sections.**
`Stacks.SheafOfModules.isCoherentOnSite_of_bijective_pi` asks for a jointly sectionwise
bijective family rather than for a limit cone, and
`AlgebraicGeometry.RingedSite.bijective_internalHomPre_pi_app` supplies that for the internal
Hom out of a finite coproduct.  `AlgebraicGeometry.RingedSite.isLimitInternalHomSheafFan` is the
same fact as a limit cone and is *not* a substitute: converting it into the sections statement
needs the sections of a categorical product of sheaves of modules to be the product of the
sections, which this tree does not have.  Only the converse direction is available
(`Stacks.SheafOfModules.isLimitFanOfBijectiveApp`), which is why the sections form is the one
proved here.

**The universe bookkeeping.**  Everything is at the module universe `max u v w`, which is where
`AlgebraicGeometry.RingedSite.internalHomSheafULiftUnitIso` and
`AlgebraicGeometry.RingedSite.internalHomSheafULiftIso` live and where
`SheafOfModules.HasFiniteGlobalPresentation` of a module at the ring universe `w` puts its
presenting modules; the lift levels of `SheafOfModules.uliftForPresentation` are matched exactly,
a `ULift` at a different level being a different type even when it lands in the same universe.
`SheafOfModules.exists_coversTop_hasFiniteGlobalPresentation`, which supplies the covering, is at
the module universe of the coefficient rings, so
`AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheaf` is stated there too.

Several applications below carry explicit universe arguments.  That is not decoration: the
module universe appears only inside a `max`, and Lean's universe unifier cannot solve
`max u v w ?t =?= max u v w m` for a metavariable `?t`.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m t

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A sheaf of modules which is a finite product of coherent sheaves of modules on sections is
coherent.**  The product is given by a family of morphisms which is jointly bijective on the
sections over every object, so no limits in the category of sheaves of modules are needed, and
the module universe is free of the universe of the coefficient rings.

The induction peels off the factor at `0`: the projection onto it is a split epimorphism, hence
locally surjective, and its sectionwise kernel is the product of the remaining factors, so
`Stacks.SheafOfModules.isCoherentOnSite_middle` applies.  See the implementation notes for why
`Stacks.SheafOfModules.isCoherentOnSite_pi` cannot be used instead. -/
theorem isCoherentOnSite_of_bijective_pi :
    ∀ (n : ℕ) {H : _root_.SheafOfModules.{m} R} {G : Fin n → _root_.SheafOfModules.{m} R}
      (π : ∀ i, H ⟶ G i),
      (∀ U : Cᵒᵖ, Function.Bijective
        (fun x : H.val.obj U ↦ fun i ↦ (π i).val.app U x)) →
      (∀ i, _root_.SheafOfModules.IsCoherentOnSite (G i)) →
      _root_.SheafOfModules.IsCoherentOnSite H := by
  intro n
  induction n with
  | zero =>
    intro H G π hπ _
    refine isCoherentOnSite_zero ((IsZero.iff_id_eq_zero H).2 ?_)
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
      ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    exact (hπ U).1 (funext fun i ↦ i.elim0)
  | succ n ih =>
    intro H G π hπ hG
    classical
    refine isCoherentOnSite_middle
      (_root_.SheafOfModules.kerIota_comp (π 0)) (_root_.SheafOfModules.kerIsLimit (π 0))
      ?_ ?_ (hG 0)
    · refine _root_.SheafOfModules.isLocallySurjective_of_sections (π 0)
        fun V y ↦ ⟨⊤, J.top_mem V, fun {Bo} g _ ↦ ?_⟩
      obtain ⟨x, hx⟩ := (hπ (op Bo)).2
        (fun i ↦ Fin.cases ((G 0).val.map g.op y) (fun _ ↦ 0) i)
      exact ⟨x, congrFun hx 0⟩
    · refine ih (G := fun i : Fin n ↦ G i.succ)
        (fun i ↦ _root_.SheafOfModules.kerIota (π 0) ≫ π i.succ) (fun U ↦ ⟨?_, ?_⟩) fun i ↦ hG _
      · intro z z' h
        have hz : (π 0).val.app U z.val = 0 := z.2
        have hz' : (π 0).val.app U z'.val = 0 := z'.2
        refine Subtype.ext ((hπ U).1 (funext fun i ↦ ?_))
        induction i using Fin.cases with
        | zero => exact hz.trans hz'.symm
        | succ j => exact congrFun h j
      · intro y
        obtain ⟨x, hx⟩ := (hπ U).2 (fun i ↦ Fin.cases 0 y i)
        refine ⟨⟨x, ?_⟩, funext fun j ↦ congrFun hx j.succ⟩
        exact (_root_.SheafOfModules.mem_kerSubmodule (π 0) U x).2 (congrFun hx 0)

/-- Coherence transfers along a sectionwise additive equivalence over the identity of the rings. -/
private theorem isCoherentOnSite_of_sectionwiseAddEquiv {M : _root_.SheafOfModules.{m} R}
    {N : _root_.SheafOfModules.{t} R} (e : ∀ U, M.val.obj U ≃+ N.val.obj U)
    (he : ∀ U (a : R.obj.obj U) (x : M.val.obj U), e U (a • x) = a • e U x)
    (hn : ∀ {V W} (f : V ⟶ W) (x : M.val.obj V),
      e W (M.val.restrictₛₗ f x) = N.val.restrictₛₗ f (e V x))
    (h : _root_.SheafOfModules.IsCoherentOnSite M) : _root_.SheafOfModules.IsCoherentOnSite N := by
  refine ⟨?_, fun U n s ↦ ?_⟩
  · exact isFiniteType_of_sectionwiseEquiv (fun _ ↦ RingEquiv.refl _) e he hn h.isFiniteType
  · exact CoherentLift.relations_isFiniteType_of_sectionwiseEquiv (fun _ ↦ RingEquiv.refl _)
      (fun _ _ ↦ rfl) e he hn s (h.kernel_isFiniteType U n _)

/-- **Coherence is unchanged by the universe lift of the sections of a sheaf of modules.**  This
is `Stacks.SheafOfModules.isCoherentOnSite_liftModule_iff` for the lift
`SheafOfModules.uliftForPresentation`, which raises the universe of the sections only and leaves
the sheaf of rings alone; that is the lift in which
`SheafOfModules.HasFiniteGlobalPresentation` writes its presentations. -/
theorem isCoherentOnSite_uliftForPresentation {M : _root_.SheafOfModules.{m} R}
    (hM : _root_.SheafOfModules.IsCoherentOnSite M) :
    _root_.SheafOfModules.IsCoherentOnSite
      (_root_.SheafOfModules.uliftForPresentation.{u, v, w, m, t} M) :=
  isCoherentOnSite_of_sectionwiseAddEquiv (fun _ ↦ AddEquiv.ulift.symm)
    (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl) hM

/-- **Coherence descends along the universe lift of the sections of a sheaf of modules.**  This
is the converse direction of `Stacks.SheafOfModules.isCoherentOnSite_uliftForPresentation`, for
the lift `Stacks.SheafOfModules.moduleULift`; it is what carries coherence from the internal Hom
of a ringed site to its `m`-small model on an essentially `m`-small site. -/
theorem isCoherentOnSite_of_moduleULift {A : _root_.SheafOfModules.{m} R}
    (h : _root_.SheafOfModules.IsCoherentOnSite ((moduleULift.{t} R).obj A)) :
    _root_.SheafOfModules.IsCoherentOnSite A :=
  isCoherentOnSite_of_sectionwiseAddEquiv (fun _ ↦ AddEquiv.ulift)
    (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl) h

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}}

/-- **Over every object, the sections of the internal Hom out of a coproduct are the product of
the sections of the internal Homs out of the summands.**  The comparison is the family of
first-variable precomposition maps `AlgebraicGeometry.RingedSite.internalHomPre` along the
injections of the coproduct.

This is the half of Stacks 0GMY(1) that a presentation needs.  The input is
`Stacks.SheafOfModules.overFunctor_preservesColimits`, Stacks 03EJ: restriction to the slice at
`U` carries the coproduct to a coproduct, and the sections of the internal Hom over `U` are by
construction the morphisms of the restrictions, so the statement is the universal property of
that coproduct.  Finiteness of the index is not used.

`AlgebraicGeometry.RingedSite.isLimitInternalHomSheafFan` is this fact as a limit cone; see the
implementation notes for why it is not a substitute. -/
theorem bijective_internalHomPre_pi_app {n : ℕ}
    {P : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (ι : Fin n → (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ P))
    (hP : IsColimit (Cofan.mk P ι))
    (N : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) :
    Function.Bijective (fun α : (internalHomSheaf X P N).val.obj (op U) =>
      fun i => (internalHomPre X (ι i)).val.app (op U) α) := by
  have hpc : PreservesColimitsOfSize.{max u v w, max u v w}
      (SheafOfModules.overFunctor.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    Stacks.SheafOfModules.overFunctor_preservesColimits.{u, v, w, w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  have _ : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    preservesColimitsOfSize_shrink
      (SheafOfModules.overFunctor.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
  have hcol : IsColimit (Cofan.mk ((SheafOfModules.overFunctor.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj P)
      (fun i => (SheafOfModules.overFunctor.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map (ι i))) :=
    Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk P ι) (isColimitOfPreserves _ hP)
  have hcofan := CategoryTheory.Limits.bijective_cofanInj_comp
    (fun i => (SheafOfModules.overFunctor.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map (ι i)) hcol (N.over U)
  have hv : ∀ A : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      Function.Bijective (fun β : A.over U ⟶ N.over U => β.val) :=
    fun _ => ⟨fun _ _ h => SheafOfModules.Hom.ext h, fun γ => ⟨⟨γ⟩, rfl⟩⟩
  have hw := (Equiv.piCongrRight fun _ : Fin n => Equiv.ofBijective _
    (hv (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))).bijective
  refine (Function.Bijective.of_comp_iff _ (hv _)).1 ?_
  exact hw.comp hcofan

/-- **The internal Hom out of a finite coproduct of copies of the structure sheaf of a ringed
site, into a coherent module, is coherent.**  It is the product of `n` copies of the target on
the sections over every object, by
`AlgebraicGeometry.RingedSite.bijective_internalHomPre_pi_app` composed with
`AlgebraicGeometry.RingedSite.internalHomSheafULiftUnitIso`, and a finite product of coherent
modules on sections is coherent by
`Stacks.SheafOfModules.isCoherentOnSite_of_bijective_pi`.

This is where the *finiteness* of the presentation enters. -/
theorem isCoherentOnSite_internalHomSheaf_cofan {n : ℕ}
    {P : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (ι : Fin n → (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ P))
    (hP : IsColimit (Cofan.mk P ι))
    {N : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite (internalHomSheaf X P N) := by
  refine Stacks.SheafOfModules.isCoherentOnSite_of_bijective_pi n
    (G := fun _ : Fin n => N)
    (fun i => internalHomPre X (ι i) ≫ (internalHomSheafULiftUnitIso X N).hom)
    (fun Y => ?_) (fun _ => hN)
  have h := bijective_internalHomPre_pi_app.{u, v, w} ι hP N Y.unop
  have hiso : Function.Bijective
      (fun y : (internalHomSheaf X (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) N).val.obj Y =>
        (internalHomSheafULiftUnitIso X N).hom.val.app Y y) :=
    Function.bijective_iff_has_inverse.2
      ⟨fun x => (internalHomSheafULiftUnitIso X N).inv.val.app Y x,
        fun y => congrFun (congrArg (fun f : _ ⟶ _ => (f.val.app Y).hom)
          (internalHomSheafULiftUnitIso X N).hom_inv_id) y,
        fun x => congrFun (congrArg (fun f : _ ⟶ _ => (f.val.app Y).hom)
          (internalHomSheafULiftUnitIso X N).inv_hom_id) x⟩
  have hw := (Equiv.piCongrRight fun _ : Fin n => Equiv.ofBijective _ hiso).bijective
  exact hw.comp h

/-- **Stacks 01CQ(2) on a ringed site, from an explicit finite presentation.**  The internal Hom
out of the cokernel of a map between two finite coproducts of copies of the structure sheaf,
into a coherent module, is coherent: it is the kernel of the map between the internal Homs out
of the two presenting modules
(`AlgebraicGeometry.RingedSite.isLimitInternalHomSheafKernelFork`), those are coherent by
`AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheaf_cofan`, and the kernel of a map
of coherent sheaves of modules on a site is coherent (Stacks 01BY(3)). -/
theorem isCoherentOnSite_internalHomSheaf_of_presentation {n k : ℕ}
    {P Q M : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (ι : Fin n → (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ P))
    (hP : IsColimit (Cofan.mk P ι))
    (κ : Fin k → (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ Q))
    (hQ : IsColimit (Cofan.mk Q κ))
    (a : Q ⟶ P) (b : P ⟶ M) (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    {N : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite (internalHomSheaf X M N) :=
  Stacks.SheafOfModules.isCoherentOnSite_of_iso
    ((isLimitInternalHomSheafKernelFork.{u, v, w, w} X N a b hab hb).conePointUniqueUpToIso
      (limit.isLimit _)).symm
    (Stacks.SheafOfModules.isCoherentOnSite_kernel
      (isCoherentOnSite_internalHomSheaf_cofan.{u, v, w} ι hP hN)
      (isCoherentOnSite_internalHomSheaf_cofan.{u, v, w} κ hQ hN)
      (internalHomPre X a))

/-- **Stacks 01CQ(2) on a ringed site, from a finite global presentation.**  The internal Hom
out of a sheaf of modules admitting a finite global presentation, into a coherent sheaf of
modules, is coherent.

The presentation presents the universe *lift* of the module, which
`AlgebraicGeometry.RingedSite.internalHomSheafULiftIso` undoes, and coherence of the target
survives the lift by `Stacks.SheafOfModules.isCoherentOnSite_uliftForPresentation`. -/
theorem isCoherentOnSite_internalHomSheaf_of_hasFiniteGlobalPresentation
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : F.HasFiniteGlobalPresentation)
    (hG : SheafOfModules.IsCoherentOnSite G) :
    SheafOfModules.IsCoherentOnSite (internalHomSheaf X F G) := by
  obtain ⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, hb⟩ := hF
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso (internalHomSheafULiftIso X F G)
    (isCoherentOnSite_internalHomSheaf_of_presentation.{u, v, w}
      ι hP.some κ hQ.some a b hab hb.some
      (Stacks.SheafOfModules.isCoherentOnSite_uliftForPresentation.{u, v, w, w, max u v w} hG))

/-- **Stacks 01CQ(2) on a ringed site: the internal Hom of two coherent sheaves of modules is
coherent.**

Coherence is local on the site (Stacks 03DN,
`Stacks.SheafOfModules.isCoherentOnSite_of_coversTop`), the internal Hom commutes with
restriction to a slice (Stacks 0E8H,
`AlgebraicGeometry.RingedSite.internalHomSheafOverIso`), and a coherent sheaf of modules has a
finite global presentation on each member of a family covering the final object
(`SheafOfModules.exists_coversTop_hasFiniteGlobalPresentation`).  On each such member
`AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheaf_of_hasFiniteGlobalPresentation`
applies.

No Noetherian hypothesis and no local finite-presentation hypothesis appear: coherence of the
source supplies the local finite presentations, exactly as in the source's proof of Stacks 01CQ
for a ringed space.  The module universe is that of the coefficient rings, which is where
`SheafOfModules.exists_coversTop_hasFiniteGlobalPresentation` lives; the internal Hom of two
such modules has its sections in `max u v w`. -/
@[ega "0 5.3.5" "more general", ega "I 9.1.1" "more general"]
theorem isCoherentOnSite_internalHomSheaf
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : SheafOfModules.IsCoherentOnSite F) (hG : SheafOfModules.IsCoherentOnSite G) :
    SheafOfModules.IsCoherentOnSite (internalHomSheaf X F G) := by
  let := hF
  obtain ⟨K, Z, hZ, hpres⟩ :=
    SheafOfModules.exists_coversTop_hasFiniteGlobalPresentation F
  refine Stacks.SheafOfModules.isCoherentOnSite_of_coversTop
    (internalHomSheaf X F G) Z hZ fun j ↦ ?_
  refine Stacks.SheafOfModules.isCoherentOnSite_of_iso
    (internalHomSheafOverIso.{u, v, w, w} X (Z j) F G).symm ?_
  exact isCoherentOnSite_internalHomSheaf_of_hasFiniteGlobalPresentation.{max u v, v, w}
    (X := X.over (Z j)) (F.over (Z j)) (G.over (Z j)) (hpres j)
    (Stacks.SheafOfModules.isCoherentOnSite_over G hG (Z j))

end AlgebraicGeometry.RingedSite

end
