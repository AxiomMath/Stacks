module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A coherent sheaf of modules on a site is quasi-coherent

Stacks 03DL lists eight local conditions on a sheaf of modules on a ringed site.  This file
proves that condition (8), coherence, implies condition (6), quasi-coherence, on an arbitrary
site and over an arbitrary sheaf of rings.

Coherence asks two things: that the module be of finite type, and that for *every* object and
*every* finite family of sections over it, the sheaf of relations among that family be of finite
type on the slice site.  Both conditions are finite, and that finiteness is what makes the
implication go through.  Finite type gives a family of objects covering the final object with,
on each member, finitely many sections generating the module; coherence, applied to those
sections, gives on a further covering of each member finitely many relations generating all
relations.  The composite family still covers the final object — this is the one closure
property of a Grothendieck topology that the argument uses, and it is transitivity, packaged as
`CategoryTheory.GrothendieckTopology.CoversTop.over`, not stability under intersections.  On each
member of the composite family the two finite families assemble into a finite global presentation.

## Main definitions

* `SheafOfModules.liftUnit`, `SheafOfModules.liftMod` and `SheafOfModules.liftPow` are the
  universe-lifted structure sheaf, the universe-lifted module, and the finite coproduct of
  copies of the former, in which a global presentation of Stacks 03DE(7) lives.
* `SheafOfModules.powMk` is the section of `SheafOfModules.liftPow` with prescribed
  coefficients, and `SheafOfModules.liftSectionHom` the morphism out of `SheafOfModules.liftUnit`
  determined by a global section.
* `SheafOfModules.powDesc` and `SheafOfModules.powRel` are the two morphisms of the presentation
  built from a finite family of generating sections and a finite family of relations.

## Main results

* `SheafOfModules.hasFiniteGlobalPresentation_of_sections`: a sheaf of modules with finitely
  many global sections generating it locally, and finitely many global relations generating all
  relations locally, has a finite global presentation.  This is the producer for Stacks 03DE(7)
  that the rest of the file consumes.
* `SheafOfModules.hasFiniteGlobalPresentation_over_of_generates` is the same statement with its
  hypotheses read on the ambient site rather than on the slice.
* `PresheafOfModules.Generates.restrict`: generation by finitely many sections is stable under
  restriction along a morphism of the site.
* `SheafOfModules.exists_coversTop_hasFiniteGlobalPresentation`: a coherent sheaf of modules has
  a finite global presentation on each member of a family covering the final object.
* `SheafOfModules.isQuasicoherentOnSite_of_isCoherentOnSite`: **a coherent sheaf of modules on a
  site is quasi-coherent**, as an instance.

## Implementation notes

`SheafOfModules.HasGlobalPresentation` and `SheafOfModules.HasFiniteGlobalPresentation` take
coproducts of copies of `SheafOfModules.uliftForPresentation (SheafOfModules.unit R)` in the
universe `max u v w`, so the presentation has to be built there and not in the module universe.
The coproducts are the finite biproducts of that category: limits in `SheafOfModules` exist and
are computed on sections with no sheafification hypothesis, and the category is preadditive, so
`SheafOfModules.hasFiniteBiproducts` is unconditional.  Working with biproducts rather than with
Mathlib's `SheafOfModules.free` is what keeps the coefficients visible:
`CategoryTheory.Limits.biproduct.total` says that every section of `SheafOfModules.liftPow` is
the sum of its coefficients, which is `SheafOfModules.powMk_coord`, and Mathlib's free sheaf has
no such sectionwise description.  It also sidesteps the universe constraint on
`SheafOfModules.free`, whose module universe is forced to equal the ring universe.

That the presenting morphism is a cokernel is the only step that needs the ambient category to be
abelian, hence the only step that needs sheafification: an epimorphism is the cokernel of its
kernel, and precomposing a cokernel with an epimorphism is again a cokernel.  The two
epimorphisms are produced from local surjectivity on sections by
`SheafOfModules.epi_of_sections`, and the kernel is handled through
`SheafOfModules.exists_kernel_val_app` and `SheafOfModules.kernel_ι_val_app_injective`, which
say that the kernel inclusion is sectionwise a kernel — evaluation at an object preserves it.
The sheafification hypotheses are instances in the universe `max u v w` by
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`, so no hypothesis of
that kind appears in any statement.

The module universe is forced to agree with the ring universe, because
`SheafOfModules.unit R` lives in the ring universe and the presentations here are built from
global sections, and because Stacks 03DN for quasi-coherence
(`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`), which
converts the covering family into the covering sieve of each object, is stated at that universe.

What is proved is `SheafOfModules.HasFiniteGlobalPresentation` on each member of the covering
family, which is stronger than the `SheafOfModules.HasGlobalPresentation` that quasi-coherence
needs.  It does not by itself give `SheafOfModules.IsFinitePresentationOnSite`: that
additionally needs stability of the finite condition under restriction along a morphism of the
site, the finite analogue of `Stacks.SheafOfModules.hasGlobalPresentation_overMap`, which is
`Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap` of
`StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence`; the two together are
`SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite` there.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Sheaves of modules on a site have finite biproducts: finite limits exist and are computed
on sections, and the category is preadditive. -/
noncomputable instance hasFiniteBiproducts : HasFiniteBiproducts (SheafOfModules.{m} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A finite sum of morphisms of sheaves of modules is computed on sections. -/
theorem sum_val_app_apply {M N : SheafOfModules.{m} R} {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) (X : Cᵒᵖ) (x : M.val.obj X) :
    (∑ i ∈ s, f i).val.app X x = ∑ i ∈ s, (f i).val.app X x := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

/-- A locally surjective morphism of sheaves of modules is an epimorphism. -/
theorem epi_of_isLocallySurjective [HasWeakSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] {M N : SheafOfModules.{m} R} (f : M ⟶ N)
    (hf : PresheafOfModules.IsLocallySurjective J f.val) : Epi f := by
  have : (SheafOfModules.toSheaf R).ReflectsEpimorphisms :=
    Functor.reflectsEpimorphisms_of_faithful _
  apply (SheafOfModules.toSheaf R).epi_of_epi_map
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map f) := hf
  exact Sheaf.epi_of_isLocallySurjective _

/-- Local surjectivity of a morphism of sheaves of modules, read on sections: every section of
the target is, on a covering sieve, the image of a section of the source. -/
theorem isLocallySurjective_of_sections {M N : SheafOfModules.{m} R} (f : M ⟶ N)
    (h : ∀ (V : C) (y : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ t : M.val.obj (op B), f.val.app (op B) t = N.val.map g.op y) :
    PresheafOfModules.IsLocallySurjective J f.val := by
  refine ⟨fun {V} y => ?_⟩
  obtain ⟨T, hT, hy⟩ := h V y
  exact J.superset_covering (fun B g hg => hy g hg) hT

/-- A morphism of sheaves of modules which is locally surjective on sections is an
epimorphism. -/
theorem epi_of_sections [HasWeakSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] {M N : SheafOfModules.{m} R} (f : M ⟶ N)
    (h : ∀ (V : C) (y : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ t : M.val.obj (op B), f.val.app (op B) t = N.val.map g.op y) :
    Epi f :=
  epi_of_isLocallySurjective f (isLocallySurjective_of_sections f h)

/-- Evaluating a sheaf of modules at an object preserves zero morphisms. -/
instance evaluation_preservesZeroMorphisms (X : Cᵒᵖ) :
    (SheafOfModules.evaluation R X).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The inclusion of a kernel of sheaves of modules is injective on sections. -/
theorem kernel_ι_val_app_injective {M N : SheafOfModules.{m} R} (b : M ⟶ N) (X : Cᵒᵖ) :
    Function.Injective ((kernel.ι b).val.app X) := by
  have : Mono ((kernel.ι b).val) :=
    inferInstanceAs (Mono ((SheafOfModules.forget R).map (kernel.ι b)))
  exact PresheafOfModules.injective_of_mono (f := (kernel.ι b).val) X

/-- A section killed by a morphism of sheaves of modules comes from a section of its kernel:
evaluation at an object preserves the kernel, so the inclusion of the kernel is sectionwise a
kernel of the map on sections. -/
theorem exists_kernel_val_app {M N : SheafOfModules.{max m w} R} (b : M ⟶ N) (X : Cᵒᵖ)
    (x : M.val.obj X) (hx : b.val.app X x = 0) :
    ∃ y : (kernel b).val.obj X, (kernel.ι b).val.app X y = x := by
  have hlim := KernelFork.mapIsLimit _ (kernelIsKernel b) (SheafOfModules.evaluation R X)
  let φ : ModuleCat.of (R.obj.obj X) (ULift.{m} (R.obj.obj X)) ⟶ M.val.obj X :=
    ModuleCat.ofHom
      { toFun := fun r => r.down • x
        map_add' := fun r r' => add_smul r.down r'.down x
        map_smul' := fun a r => mul_smul a r.down x }
  have hφ : φ ≫ (SheafOfModules.evaluation R X).map b = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    change b.val.app X (r.down • x) = 0
    rw [map_smul, hx, smul_zero]
  refine ⟨hlim.lift (KernelFork.ofι φ hφ) (ULift.up (1 : R.obj.obj X)), ?_⟩
  refine Eq.trans (congrArg
    (fun f : ModuleCat.of (R.obj.obj X) (ULift.{m} (R.obj.obj X)) ⟶ M.val.obj X =>
      f (ULift.up (1 : R.obj.obj X)))
    (hlim.fac (KernelFork.ofι φ hφ) WalkingParallelPair.zero)) ?_
  change (1 : R.obj.obj X) • x = x
  exact one_smul _ x

/-- A section of the structure sheaf read as a ring element. -/
abbrev unitVal {X : Cᵒᵖ} (r : (unit R).val.obj X) : R.obj.obj X := r

/-- A ring element read as a section of the structure sheaf. -/
abbrev unitOf {X : Cᵒᵖ} (r : R.obj.obj X) : (unit R).val.obj X := r

/-- Acting by a ring element on a section of the structure sheaf is ring multiplication. -/
theorem unit_smul {X : Cᵒᵖ} (r : R.obj.obj X) (s : (unit R).val.obj X) :
    (r • s : (unit R).val.obj X) = unitOf (r * unitVal s) := rfl

/-- A morphism out of the structure sheaf is determined by the global section it sends `1` to:
its value on a section `r` is `r` acting on that global section. -/
theorem unitHom_app (M : SheafOfModules.{w} R) (f : unit R ⟶ M) (X : Cᵒᵖ)
    (r : (unit R).val.obj X) :
    f.val.app X r = unitVal r • (M.unitHomEquiv f).eval X := by
  calc f.val.app X r
      = f.val.app X (unitVal r • unitOf (1 : R.obj.obj X)) := by
        rw [show (unitVal r • unitOf (1 : R.obj.obj X) : (unit R).val.obj X) = r from
          mul_one (unitVal r)]
    _ = unitVal r • f.val.app X (unitOf (1 : R.obj.obj X)) := map_smul _ _ _
    _ = unitVal r • (M.unitHomEquiv f).eval X := rfl

/-- The universe-lifted structure sheaf: the object of which a global presentation takes
coproducts. -/
noncomputable abbrev liftUnit (R : Sheaf J RingCat.{w}) : SheafOfModules.{max u v w} R :=
  uliftForPresentation.{u, v, w, w, max u v w} (unit R)

/-- The universe-lifted sheaf of modules: the target of a global presentation. -/
noncomputable abbrev liftMod (N : SheafOfModules.{w} R) : SheafOfModules.{max u v w} R :=
  uliftForPresentation.{u, v, w, w, max u v w} N

/-- A ring element read as a section of the universe-lifted structure sheaf. -/
noncomputable abbrev liftUnitOf {X : Cᵒᵖ} (r : R.obj.obj X) : (liftUnit R).val.obj X :=
  ULift.up (unitOf r)

/-- A section of the universe-lifted structure sheaf read as a ring element. -/
noncomputable abbrev liftUnitVal {X : Cᵒᵖ} (r : (liftUnit R).val.obj X) : R.obj.obj X :=
  unitVal r.down

/-- Raising the universe of the sections of a sheaf of modules is additive. -/
theorem liftMod_up_sum (N : SheafOfModules.{w} R) (X : Cᵒᵖ) {ι : Type*} (s : Finset ι)
    (y : ι → N.val.obj X) :
    (ULift.up (∑ i ∈ s, y i) : (liftMod N).val.obj X) =
      ∑ i ∈ s, (ULift.up (y i) : (liftMod N).val.obj X) :=
  map_sum (AddEquiv.ulift (α := N.val.obj X).symm) y s

/-- The morphism from the universe-lifted structure sheaf to a universe-lifted sheaf of
modules determined by a global section: it sends a section `r` to `r` acting on it. -/
noncomputable def liftSectionHom {N : SheafOfModules.{w} R} (σ : N.sections) :
    liftUnit R ⟶ liftMod N :=
  uliftForPresentationMap.{u, v, w, w, max u v w} (N.unitHomEquiv.symm σ)

/-- The morphism `SheafOfModules.liftSectionHom σ` sends a section `r` to the lift of
`r • σ`. -/
@[simp]
theorem liftSectionHom_val_app_apply {N : SheafOfModules.{w} R} (σ : N.sections) (X : Cᵒᵖ)
    (r : (liftUnit R).val.obj X) :
    (liftSectionHom σ).val.app X r =
      (ULift.up (liftUnitVal r • σ.eval X) : (liftMod N).val.obj X) := by
  rw [liftSectionHom, uliftForPresentationMap_val_app_apply.{u, v, w, w, max u v w}
    (N.unitHomEquiv.symm σ) X r]
  exact congrArg ULift.up (by rw [unitHom_app, Equiv.apply_symm_apply])

/-- The `n`-fold coproduct of copies of the universe-lifted structure sheaf. -/
noncomputable abbrev liftPow (R : Sheaf J RingCat.{w}) (n : ℕ) : SheafOfModules.{max u v w} R :=
  ⨁ (fun _ : Fin n => liftUnit R)

/-- The section of `SheafOfModules.liftPow` with prescribed coefficients. -/
noncomputable def powMk (R : Sheaf J RingCat.{w}) (n : ℕ) (X : Cᵒᵖ)
    (c : Fin n → R.obj.obj X) : (liftPow R n).val.obj X :=
  ∑ i, (biproduct.ι (fun _ : Fin n => liftUnit R) i).val.app X (liftUnitOf (c i))

/-- The section `SheafOfModules.powMk R n X c` is the sum of the images of the coefficients
`c i` under the inclusions into the coproduct. -/
theorem powMk_def (n : ℕ) (X : Cᵒᵖ) (c : Fin n → R.obj.obj X) :
    powMk R n X c =
      ∑ i, (biproduct.ι (fun _ : Fin n => liftUnit R) i).val.app X (liftUnitOf (c i)) := rfl

/-- A morphism out of `SheafOfModules.liftPow` is computed coefficientwise. -/
theorem desc_val_app_powMk {T : SheafOfModules.{max u v w} R} {n : ℕ}
    (β : ∀ _ : Fin n, liftUnit R ⟶ T) (X : Cᵒᵖ) (c : Fin n → R.obj.obj X) :
    (biproduct.desc β).val.app X (powMk R n X c) =
      ∑ i, (β i).val.app X (liftUnitOf (c i)) := by
  rw [powMk_def, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (comp_val_app_apply (biproduct.ι (fun _ : Fin n => liftUnit R) i)
    (biproduct.desc β) X (liftUnitOf (c i))).symm.trans
    (congrArg (fun g : liftUnit R ⟶ T => g.val.app X (liftUnitOf (c i)))
      (biproduct.ι_desc β i))

/-- The coefficients of a section of `SheafOfModules.liftPow` add up to it. -/
theorem powMk_coord (n : ℕ) (X : Cᵒᵖ) (y : (liftPow R n).val.obj X) :
    powMk R n X
        (fun i => liftUnitVal ((biproduct.π (fun _ : Fin n => liftUnit R) i).val.app X y)) =
      y := by
  have h := congrArg (fun f : liftPow R n ⟶ liftPow R n => f.val.app X y)
    (biproduct.total (f := fun _ : Fin n => liftUnit R))
  simp only at h
  rw [sum_val_app_apply] at h
  exact (Finset.sum_congr rfl fun i _ =>
    (comp_val_app_apply (biproduct.π (fun _ : Fin n => liftUnit R) i)
      (biproduct.ι (fun _ : Fin n => liftUnit R) i) X y).symm).trans h

/-- The sections of `SheafOfModules.liftPow` are additive in their coefficients. -/
theorem powMk_sum {ι : Type*} (s : Finset ι) (n : ℕ) (X : Cᵒᵖ)
    (d : ι → Fin n → R.obj.obj X) :
    powMk R n X (fun i => ∑ k ∈ s, d k i) = ∑ k ∈ s, powMk R n X (d k) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, powMk_def]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show liftUnitOf (∑ k ∈ (∅ : Finset ι), d k i) = (0 : (liftUnit R).val.obj X) from rfl,
      map_zero]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, ← ih, powMk_def, powMk_def, powMk_def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_insert hk, show liftUnitOf (d k i + ∑ j ∈ s, d j i) =
      liftUnitOf (d k i) + liftUnitOf (∑ j ∈ s, d j i) from rfl, map_add]

/-- Restriction of a section of `SheafOfModules.liftPow` restricts its coefficients. -/
theorem powMk_restrict {n : ℕ} {X Y : Cᵒᵖ} (f : X ⟶ Y) (c : Fin n → R.obj.obj X) :
    (liftPow R n).val.map f (powMk R n X c) =
      powMk R n Y (fun i => R.obj.map f (c i)) := by
  rw [powMk_def, map_sum, powMk_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← PresheafOfModules.naturality_apply
    (biproduct.ι (fun _ : Fin n => liftUnit R) i).val f]
  rfl

section Producer

variable (N : SheafOfModules.{w} R) {n p : ℕ}
  (σ : Fin n → N.sections) (ρ : Fin p → Fin n → (unit R).sections)

/-- The morphism from the `n`-fold coproduct of copies of the structure sheaf given by `n`
global sections of a sheaf of modules. -/
noncomputable def powDesc : liftPow R n ⟶ liftMod N :=
  biproduct.desc (fun i => liftSectionHom (σ i))

/-- The morphism between coproducts of copies of the structure sheaf given by `p` vectors of
`n` global sections of the structure sheaf. -/
noncomputable def powRel : liftPow R p ⟶ liftPow R n :=
  biproduct.desc (fun k => ∑ i, liftSectionHom (ρ k i) ≫
    biproduct.ι (fun _ : Fin n => liftUnit R) i)

/-- The morphism `SheafOfModules.powDesc N σ` sends the section with coefficients `c` to the
lift of the section `∑ i, c i • σ i`. -/
theorem powDesc_val_app_powMk (X : Cᵒᵖ) (c : Fin n → R.obj.obj X) :
    (powDesc N σ).val.app X (powMk R n X c) = ULift.up (∑ i, c i • (σ i).eval X) := by
  rw [powDesc, desc_val_app_powMk, liftMod_up_sum]
  exact Finset.sum_congr rfl fun i _ => liftSectionHom_val_app_apply (σ i) X (liftUnitOf (c i))

/-- The morphism `SheafOfModules.powRel ρ` sends the `k`-th inclusion of a section `z` to the
section with coefficients `i ↦ z * ρ k i`. -/
theorem powRel_val_app (X : Cᵒᵖ) (k : Fin p) (z : (liftUnit R).val.obj X) :
    (powRel ρ).val.app X ((biproduct.ι (fun _ : Fin p => liftUnit R) k).val.app X z) =
      powMk R n X (fun i => liftUnitVal z * unitVal ((ρ k i).eval X)) := by
  rw [powRel, ← comp_val_app_apply, biproduct.ι_desc, sum_val_app_apply, powMk_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [comp_val_app_apply, liftSectionHom_val_app_apply, unit_smul]

/-- The morphism `SheafOfModules.powRel ρ` sends the section with coefficients `d` to the
section with coefficients `i ↦ ∑ k, d k * ρ k i`. -/
theorem powRel_val_app_powMk (X : Cᵒᵖ) (d : Fin p → R.obj.obj X) :
    (powRel ρ).val.app X (powMk R p X d) =
      powMk R n X (fun i => ∑ k, d k * unitVal ((ρ k i).eval X)) := by
  rw [powMk_def, map_sum, powMk_sum]
  exact Finset.sum_congr rfl fun k _ => powRel_val_app ρ X k (liftUnitOf (d k))

/-- The two morphisms of the presentation compose to zero as soon as the chosen vectors of
coefficients are relations among the chosen sections. -/
theorem powRel_comp_powDesc_eq_zero
    (hρ : ∀ (k : Fin p) (X : Cᵒᵖ), ∑ i, unitVal ((ρ k i).eval X) • (σ i).eval X = 0) :
    powRel ρ ≫ powDesc N σ = 0 := by
  refine biproduct.hom_ext' _ _ fun k => ?_
  rw [comp_zero]
  ext X z
  rw [comp_val_app_apply, comp_val_app_apply, powRel_val_app ρ X k z,
    powDesc_val_app_powMk]
  refine Eq.trans (congrArg ULift.up ?_) rfl
  calc (∑ i, (liftUnitVal z * unitVal ((ρ k i).eval X)) • (σ i).eval X)
      = liftUnitVal z • ∑ i, unitVal ((ρ k i).eval X) • (σ i).eval X := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_smul _ _ _
    _ = 0 := by rw [hρ k X, smul_zero]

section Epi

variable [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- The presenting morphism out of a finite coproduct of copies of the structure sheaf is an
epimorphism as soon as the chosen sections generate locally. -/
theorem epi_powDesc
    (hgen : ∀ (V : C) (x : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ c : Fin n → R.obj.obj (op B),
        ∑ i, c i • (σ i).eval (op B) = N.val.map g.op x) :
    Epi (powDesc N σ) := by
  refine epi_of_sections _ fun V x => ?_
  obtain ⟨T, hT, hx⟩ := hgen V x.down
  refine ⟨T, hT, fun B g hg => ?_⟩
  obtain ⟨c, hc⟩ := hx g hg
  refine ⟨powMk R n (op B) c, ?_⟩
  rw [powDesc_val_app_powMk]
  exact congrArg ULift.up hc

/-- The lift to the kernel of the presenting morphism is an epimorphism as soon as the chosen
relations generate all relations locally. -/
theorem epi_kernel_lift
    (hρ : ∀ (k : Fin p) (X : Cᵒᵖ), ∑ i, unitVal ((ρ k i).eval X) • (σ i).eval X = 0)
    (hrel : ∀ (V : C) (τ : Fin n → R.obj.obj (op V)),
      (∑ i, τ i • (σ i).eval (op V) = 0) → ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ d : Fin p → R.obj.obj (op B), ∀ i,
        ∑ k, d k * unitVal ((ρ k i).eval (op B)) = R.obj.map g.op (τ i)) :
    Epi (kernel.lift (powDesc N σ) (powRel ρ)
      (powRel_comp_powDesc_eq_zero N σ ρ hρ)) := by
  refine epi_of_sections _ fun V y => ?_
  let x : (liftPow R n).val.obj (op V) := (kernel.ι (powDesc N σ)).val.app (op V) y
  let τ : Fin n → R.obj.obj (op V) := fun i =>
    liftUnitVal ((biproduct.π (fun _ : Fin n => liftUnit R) i).val.app (op V) x)
  have hzero : (powDesc N σ).val.app (op V) x = 0 :=
    (comp_val_app_apply (kernel.ι (powDesc N σ)) (powDesc N σ) (op V) y).symm.trans
      (congrArg (fun f : kernel (powDesc N σ) ⟶ liftMod N => f.val.app (op V) y)
        (kernel.condition (powDesc N σ)))
  have hxτ : powMk R n (op V) τ = x := powMk_coord n (op V) x
  have hτzero : ∑ i, τ i • (σ i).eval (op V) = 0 :=
    congrArg ULift.down (show (ULift.up (∑ i, τ i • (σ i).eval (op V)) :
      (liftMod N).val.obj (op V)) = 0 by rwa [← powDesc_val_app_powMk N σ (op V) τ, hxτ])
  obtain ⟨T, hT, hd⟩ := hrel V τ hτzero
  refine ⟨T, hT, fun B g hg => ?_⟩
  obtain ⟨d, hdg⟩ := hd g hg
  refine ⟨powMk R p (op B) d, ?_⟩
  refine kernel_ι_val_app_injective (powDesc N σ) (op B) ?_
  rw [← comp_val_app_apply, kernel.lift_ι, powRel_val_app_powMk, funext hdg,
    ← powMk_restrict, hxτ,
    PresheafOfModules.naturality_apply (kernel.ι (powDesc N σ)).val g.op y]

end Epi

/-- **A finite global presentation from finitely many generating sections with finitely many
generating relations.** -/
theorem hasFiniteGlobalPresentation_of_sections
    (hρ : ∀ (k : Fin p) (X : Cᵒᵖ), ∑ i, unitVal ((ρ k i).eval X) • (σ i).eval X = 0)
    (hgen : ∀ (V : C) (x : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ c : Fin n → R.obj.obj (op B),
        ∑ i, c i • (σ i).eval (op B) = N.val.map g.op x)
    (hrel : ∀ (V : C) (τ : Fin n → R.obj.obj (op V)),
      (∑ i, τ i • (σ i).eval (op V) = 0) → ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ d : Fin p → R.obj.obj (op B), ∀ i,
        ∑ k, d k * unitVal ((ρ k i).eval (op B)) = R.obj.map g.op (τ i)) :
    N.HasFiniteGlobalPresentation := by
  have h1 : HasSheafify J AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, u} J
  have h2 : J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, u, v} J
  have hab := powRel_comp_powDesc_eq_zero N σ ρ hρ
  have hb : Epi (powDesc N σ) := epi_powDesc N σ hgen
  have hl : Epi (kernel.lift (powDesc N σ) (powRel ρ) hab) := epi_kernel_lift N σ ρ hρ hrel
  exact ⟨n, p, liftPow R n, liftPow R p,
    biproduct.ι (fun _ : Fin n => liftUnit R), biproduct.ι (fun _ : Fin p => liftUnit R),
    ⟨biproduct.isColimit _⟩, ⟨biproduct.isColimit _⟩, powRel ρ, powDesc N σ, hab,
    ⟨isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (powDesc N σ)))
      (kernel.lift (powDesc N σ) (powRel ρ) hab) (kernel.lift_ι _ _ _).symm⟩⟩

end Producer

end SheafOfModules

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R' : Cᵒᵖ ⥤ RingCat.{w}}

/-- Restricting along `f` and then along `g` is restricting along `g ≫ f`. -/
theorem restrictₛₗ_op_restrictₛₗ_op (M : PresheafOfModules.{m} R') {X Y Z : C} (f : Y ⟶ X)
    (g : Z ⟶ Y) (x : M.obj (op X)) :
    M.restrictₛₗ g.op (M.restrictₛₗ f.op x) = M.restrictₛₗ (g ≫ f).op x :=
  (M.map_comp_apply f.op g.op x).symm

/-- Generation by finitely many sections is stable under restriction along any morphism of the
site: restrict the generators and reuse the covering sieve. -/
theorem Generates.restrict {M : PresheafOfModules.{m} R'} {U Z : C} {n : ℕ}
    {s : Fin n → M.obj (op U)} (hs : Generates J M s) (h : Z ⟶ U) :
    Generates J M (fun i => M.restrictₛₗ h.op (s i)) := by
  intro V f t
  obtain ⟨S, hS, hgen⟩ := hs V (f ≫ h) t
  refine ⟨S, hS, fun W g hg => ?_⟩
  obtain ⟨a, ha⟩ := hgen W g hg
  refine ⟨a, ?_⟩
  have hc (i : Fin n) : M.restrictₛₗ (g ≫ f).op (M.restrictₛₗ h.op (s i)) =
      M.restrictₛₗ (g ≫ f ≫ h).op (s i) := by
    rw [restrictₛₗ_op_restrictₛₗ_op, Category.assoc]
  simpa only [hc] using ha

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A finite global presentation on a slice site from generators and relations read on the
ambient site.**  The sections `s` are asked to generate `M`, and the vectors `r` of
coefficients are asked to be relations among them which generate all relations locally. -/
theorem hasFiniteGlobalPresentation_over_of_generates (M : SheafOfModules.{w} R) (Z : C)
    {n p : ℕ} (s : Fin n → M.val.obj (op Z)) (r : Fin p → Fin n → R.obj.obj (op Z))
    (hr : ∀ k, ∑ i, r k i • s i = 0)
    (hs : PresheafOfModules.Generates J M.val s)
    (hrel : ∀ (V : C) (hV : V ⟶ Z) (τ : Fin n → R.obj.obj (op V)),
      (∑ i, τ i • M.val.restrictₛₗ hV.op (s i) = 0) →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g →
        ∃ d : Fin p → R.obj.obj (op B), ∀ i,
          ∑ k, d k * R.obj.map (g ≫ hV).op (r k i) = R.obj.map g.op (τ i)) :
    (M.over Z).HasFiniteGlobalPresentation := by
  refine hasFiniteGlobalPresentation_of_sections (M.over Z)
    (fun i => M.sectionOver (s i)) (fun k i => (unit R).sectionOver (unitOf (r k i)))
    (fun k X => ?_) (fun V x => ?_) (fun V τ hτ => ?_)
  · change ∑ i, R.obj.map X.unop.hom.op (r k i) • M.val.restrictₛₗ X.unop.hom.op (s i) = 0
    have h : M.val.restrictₛₗ X.unop.hom.op (∑ i, r k i • s i) = 0 := by
      rw [hr k, map_zero]
    rw [map_sum] at h
    exact (Finset.sum_congr rfl fun i _ =>
      (map_smulₛₗ (M.val.restrictₛₗ X.unop.hom.op) (r k i) (s i)).symm).trans h
  · obtain ⟨S, hS, hgen⟩ := hs V.left V.hom x
    refine ⟨(Sieve.overEquiv V).symm S, J.overEquiv_symm_mem_over V S hS,
      fun B g hg => ?_⟩
    obtain ⟨a, ha⟩ := hgen B.left g.left (by simpa using hg)
    refine ⟨a, ?_⟩
    change ∑ i, a i • M.val.restrictₛₗ B.hom.op (s i) = M.val.restrictₛₗ g.left.op x
    have hw (i : Fin n) : M.val.restrictₛₗ (g.left ≫ V.hom).op (s i) =
        M.val.restrictₛₗ B.hom.op (s i) :=
      M.val.congr_map_apply (congrArg Quiver.Hom.op (Over.w g)) (s i)
    simpa only [hw] using ha
  · obtain ⟨T, hT, hd⟩ := hrel V.left V.hom τ hτ
    refine ⟨(Sieve.overEquiv V).symm T, J.overEquiv_symm_mem_over V T hT,
      fun B g hg => ?_⟩
    obtain ⟨d, hdg⟩ := hd g.left (by simpa using hg)
    refine ⟨d, fun i => ?_⟩
    change ∑ k, d k * R.obj.map B.hom.op (r k i) = R.obj.map g.left.op (τ i)
    have hw (k : Fin p) : R.obj.map (g.left ≫ V.hom).op (r k i) =
        R.obj.map B.hom.op (r k i) := by rw [Over.w g]
    simpa only [hw] using hdg i

/-- A finite linear combination inside the module of relations is taken componentwise. -/
theorem relations_sum_val {A : Type w} [Ring A] {n : ℕ}
    {q : Submodule A (Fin n → A)} {ι : Type*} (t : Finset ι) (c : ι → A) (y : ι → q)
    (k : Fin n) : ((∑ m ∈ t, c m • y m : q)).val k = ∑ m ∈ t, c m * (y m).val k := by
  simp

/-- **A coherent sheaf of modules has finite presentations on a covering family.**  Finite type
gives a covering family with finitely many generating sections on each member; coherence then
gives, on a covering family of each of those, finitely many generating relations among the
restricted sections.  The composite family covers the final object by transitivity, and on each
of its members the module has a finite global presentation. -/
@[ega "0 5.3.2" "more general"]
theorem exists_coversTop_hasFiniteGlobalPresentation (M : SheafOfModules.{w} R)
    [IsCoherentOnSite M] :
    ∃ (K : Type (max u v)) (Z : K → C), J.CoversTop Z ∧
      ∀ k, (M.over (Z k)).HasFiniteGlobalPresentation := by
  classical
  obtain ⟨I, A, hA, hgen⟩ :=
    (IsCoherentOnSite.isFiniteType (R := R) (F := M)).exists_generators
  choose n s hs using hgen
  choose I' W hW hrels using fun i =>
    (IsCoherentOnSite.kernel_isFiniteType (F := M) (A i) (n i) (s i)).exists_generators
  choose p rels hrg using hrels
  refine ⟨Σ i : I, I' i, fun k => (W k.1 k.2).left,
    GrothendieckTopology.CoversTop.over hA hW, fun k => ?_⟩
  obtain ⟨i, j⟩ := k
  refine hasFiniteGlobalPresentation_over_of_generates M (W i j).left
    (fun l => M.val.restrictₛₗ (W i j).hom.op (s i l))
    (fun m l => (rels i j m).val l) (fun m => ?_) ((hs i).restrict (W i j).hom)
    (fun V hV τ hτ => ?_)
  · simpa [Fintype.linearCombination] using LinearMap.mem_ker.mp (rels i j m).property
  · -- read `τ` as a relation over the slice object `Over.mk (hV ≫ (W i j).hom)`
    have hτ' : τ ∈ LinearMap.ker (Fintype.linearCombination (R.obj.obj (op V))
        (fun l => M.val.restrictₛₗ (hV ≫ (W i j).hom).op (s i l))) := by
      rw [LinearMap.mem_ker]
      have h2 : ∑ l, τ l • M.val.restrictₛₗ (hV ≫ (W i j).hom).op (s i l) = 0 := by
        simpa only [PresheafOfModules.restrictₛₗ_op_restrictₛₗ_op] using hτ
      simpa [Fintype.linearCombination] using h2
    obtain ⟨S, hS, hgenS⟩ :=
      hrg i j (Over.mk (hV ≫ (W i j).hom)) (Over.homMk hV) ⟨τ, hτ'⟩
    refine ⟨Sieve.overEquiv (Over.mk (hV ≫ (W i j).hom)) S,
      (J.mem_over_iff S).mp hS, fun B g hg => ?_⟩
    obtain ⟨a, ha⟩ := hgenS (Over.mk (g ≫ (hV ≫ (W i j).hom))) (Over.homMk g)
      ((Sieve.overEquiv_iff S g).mp hg)
    exact ⟨a, fun l => (relations_sum_val Finset.univ a
      (fun m => (PresheafOfModules.relations M.val (s i)).restrictₛₗ
        ((Over.homMk g : Over.mk (g ≫ (hV ≫ (W i j).hom)) ⟶
          Over.mk (hV ≫ (W i j).hom)) ≫ Over.homMk hV).op (rels i j m)) l).symm.trans
      (congrArg (fun y => y.val l) ha)⟩

/-- **Stacks 03DL(8) implies Stacks 03DL(6): a coherent sheaf of modules on a site is
quasi-coherent.** -/
instance isQuasicoherentOnSite_of_isCoherentOnSite (M : SheafOfModules.{w} R)
    [IsCoherentOnSite M] : M.IsQuasicoherentOnSite := by
  obtain ⟨K, Z, hZ, hpres⟩ := exists_coversTop_hasFiniteGlobalPresentation M
  rw [Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation]
  refine ⟨{V : C // (M.over V).HasGlobalPresentation}, fun V => V.1, fun X => ?_, fun V => V.2⟩
  refine J.superset_covering (fun Y f hf => ?_) (hZ X)
  rw [Sieve.mem_ofObjects_iff] at hf ⊢
  obtain ⟨k, ⟨g⟩⟩ := hf
  exact ⟨⟨Z k, (hpres k).hasGlobalPresentation⟩, ⟨g⟩⟩

end SheafOfModules

end

