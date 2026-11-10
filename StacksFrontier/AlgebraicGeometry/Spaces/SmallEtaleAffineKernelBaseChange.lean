module

public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineSectionBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change of a kernel on the small étale site

The kernel clause of Stacks 03M1 for the small étale ringed site of an algebraic space asks that
the kernel of a morphism of quasi-coherent `𝒪_F`-modules be quasi-coherent.  Unlike the direct-sum
and the cokernel clauses it is not a consequence of global presentations on the affine charts
alone: the sections of the kernel over an object of a chart are the kernel of the sections, and
exhibiting *those* as the base change of the sections over the chart needs the base ring change to
be flat.  This file supplies the two inputs that step consumes.

The first is geometric: every morphism of the small étale site is étale, because both of its
objects are étale charts of `F` and étaleness cancels
(`AlgebraicGeometry.Space.etale_of_comp_etale_chart`); so between objects with affine underlying
scheme the induced map of rings of global functions is flat.

The second is module-theoretic: `Module.Descent.isBaseChange_ker` in the shape the span conditions
consume, namely bijectivity of a `LinearMap.liftBaseChange` rather than
`IsBaseChange`.  Given a square of linear maps whose two vertical comparisons are bijective base
changes along a flat ring map, the induced comparison between the kernels is a bijective base
change as well.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.etale_map`: **every morphism of the small étale site induces
  an étale morphism of the underlying schemes.**
* `AlgebraicGeometry.Space.SmallEtale.flat_gamma_of_isAffine`: **between objects with affine
  underlying scheme the induced map of rings of global functions is flat.**
* `Module.BaseChange.bijective_liftBaseChange_ker`: **flat base change commutes with kernels**, in
  the bijective-`liftBaseChange` form.
* `AlgebraicGeometry.Space.SmallEtale.exists_hasSectionBaseChangeOn_pair_of_isQuasicoherentOnSite`:
  **two quasi-coherent modules have one common covering family of a chart with affine underlying
  scheme over whose affine objects each has its sections the base change of its sections over the
  chart.**
* `AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeAt` and
  `AlgebraicGeometry.Space.SmallEtale.hasSectionBaseChangeOn_iff_forall`: the base-change condition
  at a single object, which is what a statement taking it for two modules and concluding it for a
  third has to speak of.
* `AlgebraicGeometry.Space.SmallEtale.injective_app_kernel_ι`,
  `AlgebraicGeometry.Space.SmallEtale.exists_app_kernel_ι_eq` and
  `AlgebraicGeometry.Space.SmallEtale.app_kernel_ι_comp_eq_zero`: **the sections of a kernel of
  `𝒪_F`-modules over an object are the sections of the source killed by the morphism**, in the
  enlarged module universe.

## Implementation notes

No `@[stacks 03M1]` tag is carried, and the kernel clause itself is not proved here.  What is
proved here is every input of its proof, `AlgebraicGeometry.Space.kernel_isQuasicoherentOnSite`:
there the comparison between the two kernels of sections is identified with the restriction map
of the kernel sheaf at a single object, and
`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeAt` transported across
`SheafOfModules.uliftForPresentation`, before
`AlgebraicGeometry.Space.SmallEtale.hasGlobalPresentation_of_hasSectionBaseChangeOn` applies and
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation` concludes; the
resulting `AlgebraicGeometry.Space.isClosedUnderKernels` is the instance hypothesis of
`AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_isClosedUnderKernels`.

`Module.BaseChange.bijective_liftBaseChange_ker` is stated with the comparison between the two
kernels given as data together with the identity describing it, as everywhere in this
development's base-change API: a consumer holds that comparison as a linear map built out of the
restriction maps of a sheaf of modules, and asking for it rather than projecting it keeps the
conclusion about the map the consumer already has.  Its proof is
`LinearMap.tensorKerEquiv` — the flatness input — composed with the two given comparisons; the
`IsBaseChange` packaging of `Module.Descent.isBaseChange_ker` is not used, since converting it to
a statement about `LinearMap.liftBaseChange` would be the same work.

The ring and module structures of the geometric statements are the consumer's own, identified with
the induced maps of global functions by hypothesis, exactly as in
`AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`; no
instance is created.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe m u

namespace Module.BaseChange

/-- **Flat base change commutes with kernels**, in the form the span conditions of this
development consume: bijectivity of a `LinearMap.liftBaseChange`.

Let `Bc` be a flat `A`-algebra, let `g` be an `A`-linear map and `g'` a `Bc`-linear one, and let
`ρ₀` and `ρ₁` be comparisons making the square commute and exhibiting the source and the target of
`g'` as the base changes of those of `g`.  Then the induced comparison `κ` between the kernels
exhibits `LinearMap.ker g'` as the base change of `LinearMap.ker g`.

The isomorphism `Bc ⊗[A] ker g ≅ ker (1 ⊗ g)` is `LinearMap.tensorKerEquiv`, which is where
flatness enters; the two given comparisons then carry `ker (1 ⊗ g)` onto `ker g'`. -/
@[ega "0 20.6.21" "partial"]
theorem bijective_liftBaseChange_ker (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [Module.Flat A Bc]
    {M₀ M₁ N₀ N₁ : Type*}
    [AddCommGroup M₀] [Module A M₀] [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup N₀] [Module A N₀] [Module Bc N₀] [IsScalarTower A Bc N₀]
    [AddCommGroup N₁] [Module A N₁] [Module Bc N₁] [IsScalarTower A Bc N₁]
    (g : M₀ →ₗ[A] M₁) (g' : N₀ →ₗ[Bc] N₁)
    (ρ₀ : M₀ →ₗ[A] N₀) (ρ₁ : M₁ →ₗ[A] N₁)
    (hcomm : ∀ x, ρ₁ (g x) = g' (ρ₀ x))
    (h₀ : Function.Bijective (ρ₀.liftBaseChange Bc))
    (h₁ : Function.Bijective (ρ₁.liftBaseChange Bc))
    (κ : LinearMap.ker g →ₗ[A] LinearMap.ker g')
    (hκ : ∀ x : LinearMap.ker g, ((κ x : N₀)) = ρ₀ (x : M₀)) :
    Function.Bijective (κ.liftBaseChange Bc) := by
  have hker : ∀ z : Bc ⊗[A] (LinearMap.ker g),
      ((κ.liftBaseChange Bc z : LinearMap.ker g') : N₀) =
        ρ₀.liftBaseChange Bc ((LinearMap.tensorKer Bc Bc g z : Bc ⊗[A] M₀)) := by
    intro z
    induction z <;> simp_all
  have hsq : ∀ z : Bc ⊗[A] M₀,
      ρ₁.liftBaseChange Bc (AlgebraTensorModule.lTensor Bc Bc g z) =
        g' (ρ₀.liftBaseChange Bc z) := by
    intro z
    induction z <;> simp_all
  refine ⟨fun z z' hzz' => ?_, fun y => ?_⟩
  · refine (LinearMap.tensorKerEquiv Bc Bc g).injective (Subtype.ext (h₀.1 ?_))
    rw [LinearMap.tensorKerEquiv_apply, LinearMap.tensorKerEquiv_apply, ← hker, ← hker,
      hzz']
  · obtain ⟨z, hz⟩ := h₀.2 (y : N₀)
    have hz0 : AlgebraTensorModule.lTensor Bc Bc g z = 0 := by
      refine h₁.1 ?_
      rw [hsq, hz, map_zero]
      exact y.2
    refine ⟨(LinearMap.tensorKerEquiv Bc Bc g).symm ⟨z, hz0⟩, Subtype.ext ?_⟩
    rw [hker, show (LinearMap.tensorKer Bc Bc g
      ((LinearMap.tensorKerEquiv Bc Bc g).symm ⟨z, hz0⟩) : Bc ⊗[A] M₀) = z from
      congrArg Subtype.val
        ((LinearMap.tensorKerEquiv Bc Bc g).apply_symm_apply ⟨z, hz0⟩), hz]

end Module.BaseChange

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Every morphism of the small étale site of a presheaf induces an étale morphism of the
underlying schemes.**  Both of its objects are étale charts of the presheaf and the triangle over
the presheaf commutes, so this is the cancellation step
`AlgebraicGeometry.Space.etale_of_comp_etale_chart`. -/
theorem etale_map {U W : SmallEtale B S hS F} (h : U ⟶ W) :
    Etale ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map h)) :=
  etale_of_comp_etale_chart B S hS U.property W.property (CostructuredArrow.w h.hom)

/-- **Between two objects of the small étale site with affine underlying scheme the induced map of
rings of global functions is flat.**  The morphism of schemes is étale by
`AlgebraicGeometry.Space.SmallEtale.etale_map`, hence flat, and a flat morphism of affine schemes
has flat map of global functions (`AlgebraicGeometry.Scheme.Hom.flat_appTop`).

This is the flatness input of the kernel clause of Stacks 03M1: it is what makes the sections of a
kernel over an object of a chart the base change of the sections over the chart.  The algebra
structure is the consumer's own, identified with the induced map by `halg`. -/
theorem flat_gamma_of_isAffine {U W : SmallEtale B S hS F} (h : U ⟶ W)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W)))
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U), ⊤)]
    (halg : algebraMap
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map h)).appTop.hom) :
    Module.Flat
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U), ⊤) := by
  have _ := hU
  have _ := hW
  have _ : Etale ((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS F).map h)) := etale_map B S hS F h
  rw [← RingHom.flat_algebraMap_iff, halg]
  exact ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map h)).flat_appTop

/-- **Two quasi-coherent `𝒪_F`-modules have one common covering family of a chart with affine
underlying scheme over whose affine objects each of them has its sections the base change of its
sections over the chart.**

`AlgebraicGeometry.Space.SmallEtale.exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite`
produces a family for each module separately, and the two classes of testing objects it attaches
are different; the kernel of a morphism between the two modules needs them at one object at a
time, so one family refining both is needed.  It is extracted by
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_ofArrows_le_over` from the intersection
of the two covering sieves, which is covering because a Grothendieck topology is closed under
binary intersections; every member of the extracted family factors through a member of each of the
two families (`CategoryTheory.Sieve.mem_ofArrows_iff`), so an object lying over a member of it lies
over a member of each, and the two conditions hold there.

No affineness or finiteness of the two original families is used, and the extracted family carries
both: it is the same refinement the single-module statement itself goes through. -/
theorem exists_hasSectionBaseChangeOn_pair_of_isQuasicoherentOnSite
    (hF : IsAlgebraicSpace B S hS F)
    (M N : SheafOfModules.{m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : (smallEtaleRingedSite B S hS F hF).C)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V))) :
    ∃ (k : ℕ) (Z : Fin k → Over V) (gZ : ∀ i, Z i ⟶ Over.mk (𝟙 V)),
      Sieve.ofArrows Z gZ ∈ ((smallEtaleRingedSite B S hS F hF).J.over V) (Over.mk (𝟙 V)) ∧
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Z i).left))) ∧
        HasSectionBaseChangeOn B S hS F hF
            (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} (M.over V))
            (fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ i, Nonempty (W ⟶ Z i)) ∧
        HasSectionBaseChangeOn B S hS F hF
            (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} (N.over V))
            (fun W => IsAffine ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj W.left)) ∧ ∃ i, Nonempty (W ⟶ Z i)) := by
  obtain ⟨k₁, Y₁, g₁, hcov₁, hbc₁⟩ :=
    exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite B S hS F hF M hM V hV
  obtain ⟨k₂, Y₂, g₂, hcov₂, hbc₂⟩ :=
    exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite B S hS F hF N hN V hV
  obtain ⟨k, Z, gZ, hZaff, hle, hcov, -⟩ :=
    exists_finite_affine_ofArrows_le_over B S hS F hF (Over.mk (𝟙 V)) hV
      (Sieve.ofArrows Y₁ g₁ ⊓ Sieve.ofArrows Y₂ g₂)
      (((smallEtaleRingedSite B S hS F hF).J.over V).intersection_covering hcov₁ hcov₂)
  refine ⟨k, Z, gZ, hcov, hZaff, fun W hW => ?_, fun W hW => ?_⟩
  · obtain ⟨hWaff, i, ⟨b⟩⟩ := hW
    obtain ⟨j, a, -⟩ := (Sieve.mem_ofArrows_iff Y₁ g₁ (b ≫ gZ i)).1
      ((Sieve.ofArrows Y₁ g₁).downward_closed (hle i).1 b)
    exact hbc₁ W ⟨hWaff, j, ⟨a⟩⟩
  · obtain ⟨hWaff, i, ⟨b⟩⟩ := hW
    obtain ⟨j, a, -⟩ := (Sieve.mem_ofArrows_iff Y₂ g₂ (b ≫ gZ i)).1
      ((Sieve.ofArrows Y₂ g₂).downward_closed (hle i).2 b)
    exact hbc₂ W ⟨hWaff, j, ⟨a⟩⟩

/-! ### The base-change condition at a single object -/

/-- **The base-change condition of
`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn` at a single object of the slice.**
The sections over `W` are the base change, along the ring map of global functions induced by the
structural morphism of `W`, of the sections over the chart.

`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn` is this condition quantified over the
objects of a class, which is
`AlgebraicGeometry.Space.SmallEtale.hasSectionBaseChangeOn_iff_forall`; naming the condition at one
object is what lets a statement take it as a hypothesis for two modules and conclude it for a
third, which is how the kernel clause of Stacks 03M1 is proved.  The module structures are written
out exactly as there, so that the comparison spoken of is the same one. -/
def HasSectionBaseChangeAt (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over V))
    (W : Over V) : Prop :=
    let _ : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
        (N.val.obj (op (Over.mk (𝟙 V)))) := inferInstanceAs (Module
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over
          V).obj.obj (op (Over.mk (𝟙 V)))) (N.val.obj (op (Over.mk (𝟙 V)))))
    let _ : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        (N.val.obj (op W)) := inferInstanceAs (Module
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over
          V).obj.obj (op W))
      (N.val.obj (op W)))
    let _ : Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤) := RingHom.toAlgebra
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
        (Over.mkIdTerminal.from W : W ⟶ Over.mk (𝟙 V)).left)).appTop.hom
    let _ : Module Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤) (N.val.obj (op W)) :=
      Module.compHom _ (algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤))
    have _ : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤) (N.val.obj (op W)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Function.Bijective
      ((({ toFun := fun n => N.val.map (Over.mkIdTerminal.from W).op n
           map_add' := map_add (N.val.map (Over.mkIdTerminal.from W).op).hom
           map_smul' := fun c n =>
             (N.val.map_smul (Over.mkIdTerminal.from W).op c n).symm ▸ rfl } :
            N.val.obj (op (Over.mk (𝟙 V))) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj V), ⊤)]
              N.val.obj (op W))).liftBaseChange
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤))

/-- **The condition on a class of objects is the condition at each of them.**  This is the
definition of `AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeOn` read through
`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeAt`, and holds by definition. -/
theorem hasSectionBaseChangeOn_iff_forall (hF : IsAlgebraicSpace B S hS F)
    {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over V))
    (Q : Over V → Prop) :
    HasSectionBaseChangeOn B S hS F hF N Q ↔
      ∀ W : Over V, Q W → HasSectionBaseChangeAt B S hS F hF N W :=
  Iff.rfl

/-! ### The sections of a kernel -/

section Kernel

variable (hF : IsAlgebraicSpace B S hS F)

/-- The inclusion of a kernel of a morphism of `𝒪_F`-modules is injective on the sections over
every object: evaluation at an object preserves monomorphisms, and a monomorphism of modules is
an injective map. -/
theorem injective_app_kernel_ι {M N : Modules.{u, max (u + 1) m} B S hS F hF} (f : M ⟶ N)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) :
    Function.Injective ((kernel.ι f).val.app U) :=
  (ModuleCat.mono_iff_injective _).mp
    ((SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U).map_mono
      (kernel.ι f))

/-- **Kernels of morphisms of `𝒪_F`-modules are computed sectionwise**: a section of the source
killed by the morphism is the image of a section of the kernel.

This is `Stacks.SheafOfModules.exists_kernel_section` with the universe of the module sections
freed from the universe of the coefficient rings, which the enlarged module universe
`max (u + 1) m` of the construction of Stacks 04CK needs.  Evaluation at an object preserves
kernels, so the sections of the kernel are the kernel of the map of sections. -/
theorem exists_app_kernel_ι_eq {M N : Modules.{u, max (u + 1) m} B S hS F hF} (f : M ⟶ N)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ)
    (z : M.val.obj U) (hz : f.val.app U z = 0) :
    ∃ w : (kernel f).val.obj U, (kernel.ι f).val.app U w = z := by
  set G := SheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U with hG
  have hz' : (G.map f) z = 0 := hz
  set k : LinearMap.ker (ModuleCat.Hom.hom (G.map f)) := ⟨z, hz'⟩ with hk
  refine ⟨(PreservesKernel.iso G f).inv ((ModuleCat.kernelIsoKer (G.map f)).inv k), ?_⟩
  have h1 := ConcreteCategory.congr_hom (ModuleCat.kernelIsoKer_inv_kernel_ι (G.map f)) k
  have h2 := ConcreteCategory.congr_hom (PreservesKernel.iso_inv_ι G f)
    ((ModuleCat.kernelIsoKer (G.map f)).inv k)
  change (G.map (kernel.ι f)) ((PreservesKernel.iso G f).inv _) = z
  rw [show (G.map (kernel.ι f)) ((PreservesKernel.iso G f).inv
      ((ModuleCat.kernelIsoKer (G.map f)).inv k))
    = ((PreservesKernel.iso G f).inv ≫ G.map (kernel.ι f))
      ((ModuleCat.kernelIsoKer (G.map f)).inv k) from rfl, h2,
    ← ConcreteCategory.comp_apply, h1]
  rfl

/-- The composite of the inclusion of a kernel with the morphism vanishes on sections. -/
theorem app_kernel_ι_comp_eq_zero {M N : Modules.{u, max (u + 1) m} B S hS F hF} (f : M ⟶ N)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) (x : (kernel f).val.obj U) :
    f.val.app U ((kernel.ι f).val.app U x) = 0 := by
  change (kernel.ι f ≫ f).val.app U x = 0
  rw [kernel.condition f]
  rfl

end Kernel

end AlgebraicGeometry.Space.SmallEtale

end
