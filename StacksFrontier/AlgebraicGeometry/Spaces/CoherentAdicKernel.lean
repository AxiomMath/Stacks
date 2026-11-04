module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicBiproduct

/-!
# Kernels of coherent adic systems on an algebraic space

Let `F` be an algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its
small étale ringed site.  This file analyses the kernel of a morphism of the category
`Coh(F, 𝓘)` of coherent adic systems of `AlgebraicGeometry.Space.CoherentAdicSystems`.

Unlike the cokernel, the kernel in `Coh(F, 𝓘)` is **not** the levelwise one: of the three defining
conditions of a coherent adic system, the levelwise kernel `(K_n) = (ker α_n)` always satisfies
the first two, but its transition maps need neither be surjective nor exhibit `K_n` as the
quotient `K_{n + 1} / 𝓘 ^ (n + 1) K_{n + 1}`.  Indeed the kernel of `K_{n + 1} ⟶ K_n` is the
intersection `K_{n + 1} ∩ 𝓘 ^ (n + 1) E_{n + 1}`, which contains `𝓘 ^ (n + 1) K_{n + 1}` and is
larger in general.

What this file does is isolate that single failure.  The two conditions which do hold are proved
unconditionally, and so is the half of the third one which holds unconditionally; the remaining
two statements — surjectivity of the transition maps of the levelwise kernel, and the
factorization property making `K_n` the quotient of `K_{n + 1}` — are taken as hypotheses, and
everything from them to the universal property of the kernel in `Coh(F, 𝓘)` is discharged.

## Main definitions

* `AlgebraicGeometry.Space.kernelObjIso` — the identification of the value at a level of the
  kernel of a morphism of inverse systems with the kernel of its component there.
* `AlgebraicGeometry.Space.coherentAdicLevelwiseKernel` — the levelwise kernel as an object of
  `Coh(F, 𝓘)`, given that it is one, with
  `AlgebraicGeometry.Space.coherentAdicLevelwiseKernelι` its inclusion into the source.

## Main results

* `AlgebraicGeometry.Space.isCoherent_kernel_obj` and
  `AlgebraicGeometry.Space.idealPowerMultiple_kernel_obj_eq_bot` — **the first two defining
  conditions of a coherent adic system hold for the levelwise kernel**, unconditionally.
* `AlgebraicGeometry.Space.idealPowerMultiple_ι_comp_kernel_map_eq_zero` — **the transition maps
  of the levelwise kernel annihilate `𝓘 ^ (n + 1)` of their source**, unconditionally.
* `AlgebraicGeometry.Space.isCoherentAdicSystem_kernel_of_exists_desc` — the levelwise kernel is
  a coherent adic system as soon as its transition maps are surjective and have the
  factorization property, and
  `AlgebraicGeometry.Space.isCoherentAdicSystem_kernel_of_mono_app` — those two hypotheses are
  free for a levelwise injective morphism, whose levelwise kernel vanishes.
* `AlgebraicGeometry.Space.hasKernel_of_mono_app` — **a levelwise injective morphism of coherent
  adic systems has a kernel in `Coh(F, 𝓘)`**, the zero object.
* `AlgebraicGeometry.Space.coherentAdicLevelwiseKernelIsLimit`,
  `AlgebraicGeometry.Space.hasKernel_of_isCoherentAdicSystem_kernel` and
  `AlgebraicGeometry.Space.preservesLimitParallelPairι` — **if the levelwise kernel is a coherent
  adic system then it is the kernel in `Coh(F, 𝓘)`**, and the inclusion into the inverse systems
  of `𝒪_F`-modules creates that kernel.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed, as in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem`: the term at `n` is the Stacks source's
`E_{n + 1}`, which is why the annihilating exponent at level `n` is `n + 1`.

### What this file does not prove, and where it is proved instead

The hypotheses of `AlgebraicGeometry.Space.isCoherentAdicSystem_kernel_of_exists_desc` are not
discharged here, and they do not hold for a general morphism: already the maps
`ker α_{n + 1} ⟶ ker α_n` need not be surjective.  The repair is the one of the scheme case:
replace the levelwise kernel by the images in `E_m` of the kernels at higher levels, which
stabilize once the level exceeds `m` by a constant.  That first stabilization is
`AlgebraicGeometry.Space.kernelImages_eventuallyConstant`, the second is
`AlgebraicGeometry.Space.stableKernelImageQuotientMap_eventually_isIso`, and the kernel
assembled from them is `AlgebraicGeometry.Space.coherentAdicKernel` in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelObject`, where
`AlgebraicGeometry.Space.hasKernels_coherentAdicSystems` — the space-level counterpart of
`Stacks.Coherent.hasKernels_coherentAdicSystems` — is proved.  Those statements carry the
Noetherian hypothesis, which is why `HasKernels` is not available here and is a theorem taking
explicit arguments rather than an instance.

The Noetherian hypothesis of Stacks 089P belongs on such a statement, as a hypothesis, and not on
`AlgebraicGeometry.Space.CoherentAdicSystems`; for an algebraic space it is spelled
`AlgebraicGeometry.Space.IsNoetherian B S hS hZ F`, as in
`AlgebraicGeometry.Space.exists_idealPowSmul_inf_eq`, and Artin–Rees on a Noetherian algebraic
space is available in exactly that form (Stacks 07UL).  What the stabilization needs beyond the
levelwise form of Artin–Rees is *uniformity in the level*: Artin–Rees applied to the image of
`α_l` inside `E'_l` yields a constant depending on `l`, while the construction needs one constant
serving every level at once.

That uniform constant is available over a Noetherian affine chart, as
`AlgebraicGeometry.Space.exists_chartSectionsKernelImage_eventuallyConstant` in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelStabilization`, and it is obtained
without the affine comparison of Stacks 087W.  The tower of sections `n ↦ E_n(V)` over an affine
chart has surjective transition maps
(`AlgebraicGeometry.Space.surjective_chartSectionsSystem_map`) whose kernels are the ideal-power
multiples (`AlgebraicGeometry.Space.ker_chartSectionsSystem_map_eq_pow_smul`), so the adic
completion of its inverse limit is a finite module over the completion of the ring of the chart
(`AlgebraicGeometry.Space.moduleFinite_chartCompletedSections`), which is Noetherian; Artin–Rees
for a finite module over a Noetherian algebra of the base ring then reads the constant off that
single module, which is the role Stacks 087W plays in the scheme-level argument.

Surjectivity of those transition maps on the sections over an affine chart is the étale
cohomology vanishing of Stacks 03DW in degree zero.  It *is* available in this tree, carrying the
extra hypothesis that the source and the kernel of the epimorphism be cartesian on affine charts:
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_cartesian`.  Both hypotheses are free for a
coherent adic system — its terms are coherent, hence quasi-coherent, hence cartesian by Stacks
03DX(2) (`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`), and
kernels of morphisms of cartesian modules are cartesian
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel`).

Transporting Stacks 087W itself is not available, and that is why the route above avoids it.
Restriction to the slice of the small étale site at a chart, `SheafOfModules.overFunctor`, is
exact and detects isomorphisms on a covering family
(`AlgebraicGeometry.Space.isIso_of_isIso_over_of_isSurjective`), which is what gluing finitely
many constants consumes — but it lands in the modules on the small étale site of the chart, not
in the Zariski modules of its scheme, where Stacks 087W lives.  Restriction to the chart's
scheme, `AlgebraicGeometry.Space.restrictToChartScheme`, does land there and is left exact
(`AlgebraicGeometry.Space.preservesFiniteLimits_restrictToChartSchemeFunctor`), but it is the
pushforward along the morphism of sites `U_étale ⟶ U_Zariski` and so is not right exact; it
therefore does not carry the quotient condition `E_n = E_{n + 1} / 𝓘 ^ (n + 1) E_{n + 1}` and
does not induce a functor on `Coh(F, 𝓘)`.  Making it do so means matching the two structure
sheaves across the equivalence of sites of Stacks 04M0, which the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart` record as not done.

The step *after* the chart-local stabilization is now done, in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelImage` and
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelImageStabilization`: the kernel images
themselves and the comparison morphisms between them are
`AlgebraicGeometry.Space.kernelImageAt`, `AlgebraicGeometry.Space.kernelImageAt_hasMap` and
`AlgebraicGeometry.Space.kernelImageAtProject`, and the global form of the first stabilization of
Stacks 087X is `AlgebraicGeometry.Space.kernelImages_eventuallyConstant`, which turns the
chart-local statement into invertibility of a comparison morphism of `𝒪_F`-modules by the three
inputs it had available: bijectivity on the sections over the finitely many Noetherian affine
charts of a covering family propagates to every affine chart above them for modules cartesian on
affine charts (`AlgebraicGeometry.Space.bijective_val_app_of_bijective_of_cartesian`),
bijectivity over the affine charts of a slice makes a morphism there invertible
(`AlgebraicGeometry.Space.SmallEtale.isIso_of_bijective_app_of_isAffine`), and the restrictions
to the slices at a covering family are jointly conservative
(`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map`).  The stable kernel images it names, and
their inverse system, are
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicStableKernelImage`.

The *second* stabilization of Stacks 087X, and the kernel object built from it, are the space-level
analogues of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.StableKernelLimit` and of
`Stacks.Coherent.hasKernels_coherentAdicSystems`.  The system of stable kernel images
`AlgebraicGeometry.Space.stableKernelImageSystem` is a subsystem of `E` whose terms are coherent
and which `α` annihilates, but it is **not** a coherent adic system: its term at `n` need not be
the quotient of its term at `n + 1` by `𝓘 ^ (n + 1)`.  The repair is to complete each stable
kernel image into a coherent adic system (Stacks 08B4), to assemble the resulting double system
indexed by `ℕᵒᵖ × ℕᵒᵖ`, and to prove that for each fixed quotient level the transition maps in
the image level are eventually isomorphisms; the kernel is then the limit of the double system
over the image level.  The scheme-level proof of that second stabilization runs through the
affine comparison of Stacks 087W
(`Stacks.Coherent.affineStableKernelImageQuotientMap_bijective`), which is what an algebraic
space does not have, and the substitute is the chart tower of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartTower`, as for the *first* stabilization:
`AlgebraicGeometry.Space.exists_chartStableKernelImagePresentation` presents the sections of all
the stable kernel images over one Noetherian affine chart as the images of one submodule of one
module, which is what 087W does at scheme level.

The abelian structure of Stacks 089P (1) above the kernel is
`AlgebraicGeometry.Space.abelian_coherentAdicSystems` in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAbelian`, and
`CategoryTheory.ShortComplex.HasHomology` is therefore free for a short complex of `Coh(F, 𝓘)` on
a Noetherian algebraic space.  The route there is *not* the scheme-level one: at scheme level the
abelian structure is `Stacks.Coherent.isIso_coimageImageComparison`, proved by restricting to an
affine Noetherian open and appealing to the equivalence of `Coh(Spec R, ℐ)` with the finite
modules over the completed ring, and that equivalence is the content of Stacks 087W again and has
no space-level counterpart.  What replaces it is the kernel built here: for a *surjection* the
kernel object surjects onto the levelwise kernels
(`AlgebraicGeometry.Space.kernel_ι_comp_eq_zero_of_epi`), which makes a surjection the cokernel
of its kernel, and the same statement applied to the comparison of a monomorphism with the kernel
of its cokernel makes that comparison invertible.

The normal-epimorphism statement does *not* go through the levelwise kernel.  A levelwise
surjective morphism of coherent adic systems is not the cokernel of its levelwise kernel, which
is not an object of `Coh(F, 𝓘)`; the dual of the argument of
`AlgebraicGeometry.Space.normalMonoOfMonoApp` therefore fails, that one resting on the cokernel
in `Coh(F, 𝓘)` being levelwise.  What is used instead is the image in `E_n` of the *kernel
object*, which is the stable kernel image and not the levelwise kernel.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 07UL](https://stacks.math.columbia.edu/tag/07UL)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 00IN](https://stacks.math.columbia.edu/tag/00IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).Submodule)

/-! ### Monomorphisms of modules on sections -/

/-- A monomorphism of `𝒪_F`-modules is injective on the sections over an object of the small
étale site: the forgetful functor to presheaves of modules preserves monomorphisms, and a
monomorphism of presheaves of modules is injective sectionwise. -/
theorem eq_of_mono_app_eq {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) [Mono φ]
    (X : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) {x y : M.val.obj X}
    (h : φ.val.app X x = φ.val.app X y) : x = y :=
  have : Mono φ.val := (SheafOfModules.forget _).map_mono φ
  PresheafOfModules.injective_of_mono φ.val X h

/-- A module admitting a monomorphism into a module annihilated by `𝓘 ^ k` is itself annihilated
by `𝓘 ^ k`. -/
theorem isPowAnnihilated_of_mono (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N)
    [Mono φ]
    (hN : IsPowAnnihilated B S hS F hF 𝓘 k N) : IsPowAnnihilated B S hS F hF 𝓘 k M := by
  intro U r hr x
  have h1 : φ.val.app (op U) (r • x) = r • φ.val.app (op U) x :=
    (φ.val.app (op U)).hom.map_smul r x
  refine eq_of_mono_app_eq B S hS F hF φ (op U) ?_
  rw [h1, hN U r hr _, map_zero]

/-! ### Levelwise kernels of inverse systems -/

/-- The value at a level of the kernel of a morphism of inverse systems is the kernel of its
component there: limits in a functor category are computed levelwise. -/
def kernelObjIso {X Y : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (g : X ⟶ Y) (n : ℕᵒᵖ) :
    (kernel g).obj n ≅ kernel (g.app n) :=
  PreservesKernel.iso ((evaluation ℕᵒᵖ (Modules.{u, u} B S hS F hF)).obj n) g

/-- Under `AlgebraicGeometry.Space.kernelObjIso`, the component of the inclusion of the kernel is
the inclusion of the kernel of the component. -/
theorem kernelObjIso_inv_comp_app {X Y : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (g : X ⟶ Y)
    (n : ℕᵒᵖ) :
    (kernelObjIso B S hS F hF g n).inv ≫ (kernel.ι g).app n = kernel.ι (g.app n) :=
  PreservesKernel.iso_inv_ι ((evaluation ℕᵒᵖ (Modules.{u, u} B S hS F hF)).obj n) g

/-- Every component of the inclusion of a levelwise kernel is a monomorphism. -/
instance mono_kernel_ι_app {X Y : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (g : X ⟶ Y) (n : ℕᵒᵖ) :
    Mono ((kernel.ι g).app n) := by
  have h : (kernel.ι g).app n =
      (kernelObjIso B S hS F hF g n).hom ≫ kernel.ι (g.app n) := by
    rw [← kernelObjIso_inv_comp_app B S hS F hF g n, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  rw [h]
  infer_instance

/-! ### The levelwise kernel of a morphism of coherent adic systems -/

section Kernel

variable {E E' : CoherentAdicSystems B S hS F hF 𝓘} (α : E ⟶ E')

/-- Every term of the levelwise kernel of a morphism of coherent adic systems is coherent: it is
the kernel of the component there, and coherent modules on an algebraic space are closed under
kernels. -/
theorem isCoherent_kernel_obj (n : ℕ) :
    IsCoherent B S hS F hF ((kernel α.hom).obj (op n)) :=
  (isCoherent.{u, u} B S hS F hF).prop_of_iso (kernelObjIso B S hS F hF α.hom (op n)).symm
    (isCoherent_kernel B S hS F hF (E.property.1 n) (E'.property.1 n) (α.hom.app (op n)))

/-- The term at level `n` of the levelwise kernel of a morphism of coherent adic systems is
annihilated by `𝓘 ^ (n + 1)`, being a submodule of the term at that level of the source. -/
theorem idealPowerMultiple_kernel_obj_eq_bot (n : ℕ) :
    idealPowerMultiple B S hS F hF 𝓘 (n + 1) ((kernel α.hom).obj (op n)) = ⊥ :=
  (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) _).mpr
    (isPowAnnihilated_of_mono B S hS F hF 𝓘 (n + 1) ((kernel.ι α.hom).app (op n))
      ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) _).mp (E.property.2.1 n)))

/-- Each transition map of the levelwise kernel of a morphism of coherent adic systems annihilates
`𝓘 ^ (n + 1)` of its source.

Composed with the inclusion into the source system the transition map becomes the transition map
of the source preceded by that inclusion, which already annihilates `𝓘 ^ (n + 1)` of the
levelwise kernel by minimality; the inclusion is a monomorphism, so it may be cancelled. -/
theorem idealPowerMultiple_ι_comp_kernel_map_eq_zero (n : ℕ) :
    (idealPowerMultiple B S hS F hF 𝓘 (n + 1) ((kernel α.hom).obj (op (n + 1)))).ι ≫
      (kernel α.hom).map (homOfLE (Nat.le_succ n)).op = 0 := by
  have hnat : (kernel α.hom).map (homOfLE (Nat.le_succ n)).op ≫ (kernel.ι α.hom).app (op n) =
      (kernel.ι α.hom).app (op (n + 1)) ≫ E.obj.map (homOfLE (Nat.le_succ n)).op :=
    (kernel.ι α.hom).naturality (homOfLE (Nat.le_succ n)).op
  have h := idealPowerMultiple_ι_comp_comp_eq_zero B S hS F hF 𝓘 (n + 1)
    ((kernel.ι α.hom).app (op (n + 1))) (E.obj.map (homOfLE (Nat.le_succ n)).op)
    (idealPowerMultiple_ι_comp_map_succ_eq_zero B S hS F hF 𝓘 E.property n)
  refine (cancel_mono ((kernel.ι α.hom).app (op n))).mp ?_
  rw [zero_comp, Category.assoc, hnat]
  exact h

/-- **The levelwise kernel of a morphism of coherent adic systems is a coherent adic system as
soon as its transition maps are surjective and have the factorization property** which makes each
term the quotient of the next by `𝓘 ^ (n + 1)`.

The other two defining conditions, and the vanishing of the composite of the transition map with
the inclusion of `𝓘 ^ (n + 1)` of its source, hold for every morphism. -/
theorem isCoherentAdicSystem_kernel_of_exists_desc
    (hepi : ∀ n : ℕ, Epi ((kernel α.hom).map (homOfLE (Nat.le_succ n)).op))
    (hdesc : ∀ (n : ℕ) (T : Modules.{u, u} B S hS F hF)
      (k : (kernel α.hom).obj (op (n + 1)) ⟶ T),
      (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
        ((kernel α.hom).obj (op (n + 1)))).ι ≫ k = 0 →
      ∃ d : (kernel α.hom).obj (op n) ⟶ T,
        (kernel α.hom).map (homOfLE (Nat.le_succ n)).op ≫ d = k) :
    IsCoherentAdicSystem B S hS F hF 𝓘 (kernel α.hom) :=
  isCoherentAdicSystem_of_exists_desc B S hS F hF 𝓘
    (isCoherent_kernel_obj B S hS F hF 𝓘 α)
    (idealPowerMultiple_kernel_obj_eq_bot B S hS F hF 𝓘 α) hepi
    (idealPowerMultiple_ι_comp_kernel_map_eq_zero B S hS F hF 𝓘 α) hdesc

/-- The levelwise kernel of a morphism of coherent adic systems which is injective at every level
is a coherent adic system: all of its terms vanish.

This is the one case in which the hypotheses of
`AlgebraicGeometry.Space.isCoherentAdicSystem_kernel_of_exists_desc` are free, both of them being
statements about morphisms out of a zero module. -/
theorem isCoherentAdicSystem_kernel_of_mono_app (hα : ∀ n : ℕᵒᵖ, Mono (α.hom.app n)) :
    IsCoherentAdicSystem B S hS F hF 𝓘 (kernel α.hom) := by
  have hz : ∀ n : ℕᵒᵖ, IsZero ((kernel α.hom).obj n) := fun n =>
    have := hα n
    (isZero_kernel_of_mono (α.hom.app n)).of_iso (kernelObjIso B S hS F hF α.hom n)
  refine isCoherentAdicSystem_kernel_of_exists_desc B S hS F hF 𝓘 α
    (fun n => ⟨fun g g' _ => (hz (op n)).eq_of_src g g'⟩) fun n T k _ => ⟨0, ?_⟩
  rw [comp_zero]
  exact ((hz (op (n + 1))).eq_of_src k 0).symm

/-! ### The kernel in `Coh(F, 𝓘)` when the levelwise kernel is one -/

variable (h : IsCoherentAdicSystem B S hS F hF 𝓘 (kernel α.hom))

/-- The levelwise kernel of a morphism of coherent adic systems, as an object of `Coh(F, 𝓘)`,
given that it is a coherent adic system. -/
def coherentAdicLevelwiseKernel : CoherentAdicSystems B S hS F hF 𝓘 :=
  ⟨kernel α.hom, h⟩

/-- The inclusion of `AlgebraicGeometry.Space.coherentAdicLevelwiseKernel` into the source. -/
def coherentAdicLevelwiseKernelι :
    coherentAdicLevelwiseKernel B S hS F hF 𝓘 α h ⟶ E :=
  ObjectProperty.homMk (kernel.ι α.hom)

/-- The inclusion of the levelwise kernel is killed by the morphism. -/
theorem coherentAdicLevelwiseKernelι_comp :
    coherentAdicLevelwiseKernelι B S hS F hF 𝓘 α h ≫ α = 0 :=
  ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘) (kernel.condition α.hom)

/-- The inclusion of the coherent adic systems into all inverse systems creates the kernel of a
morphism whose levelwise kernel is a coherent adic system, that levelwise kernel being one. -/
@[instance_reducible]
def createsLimitParallelPairι :
    CreatesLimit (parallelPair α 0)
      (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘)) :=
  createsLimitFullSubcategoryInclusion' (parallelPair α 0)
    ((isLimitMapConeForkEquiv' (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘))
      (coherentAdicLevelwiseKernelι_comp B S hS F hF 𝓘 α h)).symm (kernelIsKernel α.hom)) h

include h in
/-- **If the levelwise kernel of a morphism of coherent adic systems is a coherent adic system,
then the morphism has a kernel in `Coh(F, 𝓘)`.** -/
theorem hasKernel_of_isCoherentAdicSystem_kernel : HasKernel α :=
  have := createsLimitParallelPairι B S hS F hF 𝓘 α h
  hasLimit_of_created (parallelPair α 0)
    (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘))

/-- The kernel fork of `AlgebraicGeometry.Space.coherentAdicLevelwiseKernelι` is a limit: the
levelwise kernel is the kernel of the morphism in `Coh(F, 𝓘)`. -/
def coherentAdicLevelwiseKernelIsLimit :
    IsLimit (KernelFork.ofι (coherentAdicLevelwiseKernelι B S hS F hF 𝓘 α h)
      (coherentAdicLevelwiseKernelι_comp B S hS F hF 𝓘 α h)) :=
  isLimitOfReflects (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘))
    ((isLimitMapConeForkEquiv' (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘))
      (coherentAdicLevelwiseKernelι_comp B S hS F hF 𝓘 α h)).symm (kernelIsKernel α.hom))

include h in
/-- **The kernel in `Coh(F, 𝓘)` of a morphism whose levelwise kernel is a coherent adic system is
that levelwise kernel.** -/
theorem preservesLimitParallelPairι :
    PreservesLimit (parallelPair α 0)
      (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘)) :=
  have := createsLimitParallelPairι B S hS F hF 𝓘 α h
  have := hasKernel_of_isCoherentAdicSystem_kernel B S hS F hF 𝓘 α h
  preservesLimit_of_createsLimit_and_hasLimit _ _

/-- **A morphism of coherent adic systems which is injective at every level has a kernel in
`Coh(F, 𝓘)`**, namely the zero object. -/
theorem hasKernel_of_mono_app (hα : ∀ n : ℕᵒᵖ, Mono (α.hom.app n)) : HasKernel α :=
  hasKernel_of_isCoherentAdicSystem_kernel B S hS F hF 𝓘 α
    (isCoherentAdicSystem_kernel_of_mono_app B S hS F hF 𝓘 α hα)

end Kernel

end AlgebraicGeometry.Space

end
