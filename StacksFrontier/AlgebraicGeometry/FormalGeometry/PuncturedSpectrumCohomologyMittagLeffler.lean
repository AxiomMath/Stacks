module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCompletedSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumMilnorTriangleComparison
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.SchemeOpenSectionsDerived
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.FiniteModule
public import StacksFrontier.RingTheory.LocalCohomology.PuncturedSpectrumDescendingChain

/-!
# Cohomology on the punctured spectrum: descending chains and Mittag-Leffler

Let `(A, 𝔪)` be a Noetherian local ring and let `U = Spec A ∖ {𝔪}` be its punctured spectrum,
read as a ringed space.  This file proves, for the genuine derived sections
`RΓ(U, -) : D(𝒪_U) ⥤ D(A)` of that ringed space:

* **[Stacks, Tag 0DX0] part (2)** — for a coherent `𝒪_U`-module `ℱ` the `A`-module `Hⁱ(U, ℱ)`
  satisfies the descending chain condition for `i > 0`;
* **[Stacks, Tag 0DX1] part (2)** — for an inverse system `(ℱₙ)` of coherent `𝒪_U`-modules the
  inverse system of `A`-modules `n ↦ Hⁱ(U, ℱₙ)` satisfies the Mittag-Leffler condition for
  `i > 0`;
* **the Mittag-Leffler condition in degree zero** — for the tower `ℱ/Iⁿℱ` of quotients of a
  coherent `ℱ` the inverse system `n ↦ Γ(U, ℱ/Iⁿℱ)` is Mittag-Leffler as well, a degree
  [Stacks, Tag 0DX1] part (2) does not reach;
* **the Mittag-Leffler condition in every degree** for that tower, negative degrees included;
* **the comparison `Hⁱ(RΓ(U, ℒ)) ⟶ lim_n Hⁱ(U, ℱ/Iⁿℱ)` is an isomorphism in every degree `i`**,
  for `ℒ` a derived limit of the tower `ℱ/Iⁿℱ`, with the Mittag-Leffler input proved rather than
  assumed. This is the engine of [Stacks, Tag 0DXI]; the tag itself, whose left-hand side is the
  derived `I`-adic completion `RΓ(U, ℱ)^∧` rather than `RΓ(U, ℒ)`, is proved in
  `PuncturedSpectrumDerivedCompletion.lean`, which produces `ℒ` together with the identification
  of `RΓ(U, ℒ)` with `RΓ(U, ℱ)^∧`.

## Main results

* `isMittagLefflerCategorical_of_isZero` and `isMittagLefflerCategorical_of_ker_le_range` — two
  criteria for the Mittag-Leffler condition: a system of zero objects, and a system each of whose
  terms carries a map to an Artinian module whose kernel is contained in every transition image.
* `Stacks.Cohomology.ModuleComparison.homologyDerivedSectionsOverIsoRightDerived` — the
  degree-`n` cohomology of the unbounded derived sections over a base ring of a sheaf of modules
  placed in degree zero is the classical `n`-th right derived functor of sections, **as
  `A`-modules**.
* `Stacks.Cohomology.ModuleComparison.isZero_homology_derivedSectionsOver_single_of_neg` —
  `Hᵐ(X, ℱ) = 0` for `m < 0`: the derived sections of a sheaf of modules placed in degree zero
  lie in `D^{≥0}(A)`.
* `Stacks.Algebraization.isArtinian_homology_puncturedSpectrumDerivedSections` —
  **[Stacks, Tag 0DX0] part (2)**.
* `Stacks.Algebraization.isMittagLefflerCategorical_puncturedSpectrumCohomologySystem` —
  **[Stacks, Tag 0DX1] part (2)**.
* `Stacks.Algebraization.isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_zero` —
  the Mittag-Leffler condition in degree zero for a tower of quotients of a coherent module.
* `Stacks.Algebraization`
  `.isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_of_quotientTower` — the
  Mittag-Leffler condition for such a tower in **every** degree `p : ℤ`.
* `Stacks.Algebraization`
  `.exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections_of_two_le` and
  `Stacks.Algebraization.exists_homologyIso_limit_puncturedSpectrumSections_of_two_le` —
  the comparison at `RΓ(U, ℒ)` in degrees `i ≥ 2`, unconditionally in the Mittag-Leffler input.
* `Stacks.Algebraization.isIso_toLimit_homology_puncturedSpectrumSections_of_two_le` and
  `Stacks.Algebraization.nonempty_homologyIso_limit_puncturedSpectrumSections_of_two_le` — the
  same without the Milnor triangle, and as a bare isomorphism.
* `Stacks.Algebraization.isIso_toLimit_homology_puncturedSpectrumSections_of_isCoherent` and
  `Stacks.Algebraization.exists_homologyIso_limit_puncturedSpectrumSections_of_isCoherent` —
  the comparison at `RΓ(U, ℒ)` in **every** degree, with the Mittag-Leffler input proved rather
  than assumed. In both pairs the comparison map is the one determined by a derived-limit structure
  map of `n ↦ RΓ(U, ℱₙ)`, and the `≅` readings carry its characterization rather than asserting
  that the two `A`-modules are abstractly isomorphic.

## Implementation notes

*The two models of cohomology on the punctured spectrum, reconciled.* `Hⁱ(U, ℱ)` for `ℱ` a sheaf
of modules on the ringed space `U` is read here as the degree-`i` cohomology of
`Stacks.Algebraization.puncturedSpectrumDerivedSections`, which is what
`Stacks.Algebraization.puncturedSpectrumCohomologySystem` and [Stacks, Tag 0DXI] use. The
library's other `A`-module `Hⁱ(U, M̃)`, on which the comparison of [Stacks, Tag 0DWR] in positive
degrees and clause (3) of [Stacks, Tag 0BK0] are stated, is
`Stacks.LocalCohomologySequence.complementCohomologyBase`: the derived functor, on sheaves of
modules on the *ambient* `Spec A`, of the sections over the open `Spec A ∖ V(𝔪)`. The two are
identified here, objectwise and `A`-linearly, by the chain

1. `homologyDerivedSectionsOverIsoRightDerived`, which replaces the total derived functor by the
   classical right derived functor of `Γ(U, -)` on sheaves of modules on `U`;
2. the equality of functors `sectionsOverOpen U ⊤ = moduleGlobalSections U` — the structure sheaf
   of the open subscheme *is* the restricted structure sheaf, so the two categories of sheaves of
   modules and the two global-section functors agree on the nose;
3. [Stacks, Tag 0BK0] part (1), `AlgebraicGeometry.exists_finiteModule_tilde_restrict`, writing
   the coherent `ℱ` as `M̃|_U` for a finite `A`-module `M`;
4. `Stacks.Cohomology.SchemeOpenSections.derivedSectionsOnOpenIso`, which is [Stacks, Tag 01E1]
   (2) for the open immersion `U ⟶ Spec A`, moving the cohomology back to the ambient space;
5. the equality `Spec A ∖ {𝔪} = Spec A ∖ V(𝔪)`, which is `zeroLocus_maximalIdeal`, and the
   agreement of the two restrictions of scalars `A ⟶ Γ(U, 𝒪_U)` — the composite
   `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(U, 𝒪_U)` is `Stacks.Algebraization.puncturedSpectrumScalars` on the
   nose.

Everything but items 3 and 5 is definitional.

*Why no functoriality is needed.* The Mittag-Leffler condition asks only that the images of the
transition maps into each fixed term stabilize, and that follows from the descending chain
condition on that single term. So the system-level statement needs only the objectwise
Artinian conclusion, and [Stacks, Tag 0BK0] part (1) — which chooses the module `M` one sheaf at
a time and produces no inverse system of modules — suffices. This is why [Stacks, Tag 0DX1] part
(2) is obtained here for an arbitrary inverse system of coherent sheaves.

*The three degree ranges of Tag 0DXI.* The Milnor short exact sequence of [Stacks, Tag 0D60] in
degree `i` consumes the Mittag-Leffler condition in degree `i - 1`, and the source discharges it
by citing [Stacks, Tag 0DX1] part (2) — which, read literally, supplies it only for `i - 1 > 0`.
The two remaining ranges are settled here, so that no degree is left conditional.

* `i - 1 < 0`, that is `i ≤ 0`. The system is zero:
  `isZero_homology_derivedSectionsOver_single_of_neg` says that `RΓ(X, ℱ)` for a sheaf of modules
  placed in degree zero has no cohomology below degree zero, and a system of zero objects is
  Mittag-Leffler because a zero object has only one subobject.
* `i - 1 = 0`, that is `i = 1`. This is the degree Tag 0DX1 part (2) really does not cover: the
  modules `Γ(U, ℱ/Iⁿℱ)` need not satisfy the descending chain condition, since `Γ(U, M̃)`
  contains the image of `M`. What holds instead is that each of them is Artinian *modulo the
  image of `Γ(U, ℱ)`*, and that is enough. Writing `πₙ : ℱ ⟶ ℱ/Iⁿℱ` and `Kₙ` for its kernel, the
  long exact sequence of `0 → Kₙ → ℱ → ℱ/Iⁿℱ → 0` gives
  `Γ(U, ℱ) ⟶ Γ(U, ℱ/Iⁿℱ) ⟶ H¹(U, Kₙ)` exact, so the kernel of the connecting map `δₙ` is the
  image of `Γ(πₙ)`; `Kₙ` is coherent, being the kernel of a map of coherent modules, so
  `H¹(U, Kₙ)` is Artinian by part (2) of [Stacks, Tag 0DX0] above. Since `πₙ` factors through
  `π_k` for `k ≥ n`, that kernel is contained in the image of every transition map
  `Γ(U, ℱ/I^kℱ) ⟶ Γ(U, ℱ/Iⁿℱ)`, and `isMittagLefflerCategorical_of_ker_le_range` applies.
* `i - 1 > 0`, that is `i ≥ 2`. This is [Stacks, Tag 0DX1] part (2), proved above.

*Why containing the kernel of a map to an Artinian module suffices.* The transition images
`Dₖ = Im(Fₖ ⟶ Fₙ)` form a descending chain, and each contains `ker δₙ`. A submodule containing
the kernel of `δₙ` is the full preimage of its own image, so `Dₖ ↦ δₙ(Dₖ)` is injective on this
chain; the images form a descending chain in an Artinian module and therefore stabilize, hence so
do the `Dₖ`. That is `isMittagLefflerCategorical_of_ker_le_range`, and it is the reason no
compatibility between the kernels `Kₙ` is needed: as for the Artinian conclusion itself, the
condition is a statement about one term at a time.

*Why the Mittag-Leffler hypothesis had to go.* For a countable tower the Mittag-Leffler condition
implies, and for towers of countable groups is equivalent to, the vanishing of `R¹lim`; and in the
Milnor sequence `0 → R¹lim H^{i-1} → Hⁱ(RΓ(U, ℒ)) → lim Hⁱ → 0` the vanishing of the left-hand
term is exactly what makes the comparison map an isomorphism. Assuming the condition in degree
`i - 1` is therefore assuming the conclusion in degree `i` in another spelling. The earlier
`Stacks.Algebraization.isIso_toLimit_homology_puncturedSpectrumSections` is kept — it is the
general statement for an arbitrary tower satisfying the condition, and the statements below are
it with the condition supplied.

*Why these statements carry no tag.* Their left-hand side is named by a derived limit `ℒ` of the
tower rather than by the derived `I`-adic completion of `RΓ(U, ℱ)`, which is what
[Stacks, Tag 0DXI] asserts. Identifying the two is [Stacks, Tag 0A0K] followed by
[Stacks, Tag 0BLX], and that identification is carried out in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/PuncturedSpectrumDerivedCompletion.lean`, which
*produces* an `ℒ` with both properties at once and so proves the tag with nothing assumed. What
the statements below contribute to it is the Mittag-Leffler input, in every degree.

The comparison map is pinned here as it is there: the morphism `a : RΓ(U, ℒ) ⟶ ∏ₙ RΓ(U, ℱₙ)`
through which it is characterized is required to exhibit `RΓ(U, ℒ)` as a derived limit of
`n ↦ RΓ(U, ℱₙ)`, and the `≅` readings carry that characterization instead of asserting an
abstract isomorphism of `A`-modules. The section "Why the morphism `a` carries the
distinguished-triangle requirement" of `PuncturedSpectrumCompletedSections.lean` says why a bare
existential there would have been weaker than the source and why the triangle is enough.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0DX0](https://stacks.math.columbia.edu/tag/0DX0)
* [Stacks Project, Tag 0DX1](https://stacks.math.columbia.edu/tag/0DX1)
* [Stacks Project, Tag 0DXI](https://stacks.math.columbia.edu/tag/0DXI)

## Tags

local cohomology, punctured spectrum, Mittag-Leffler, descending chain condition, formal
geometry
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AffineBase (moduleGlobalSections)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen)
open Stacks.Cohomology.DerivedSectionsOverBase
open Stacks.Cohomology.ModuleComparison (rightDerivedCompIso sectionsOnOpen)
open Stacks.Cohomology.SchemeOpenSections (derivedSectionsOnOpenIso)

universe u v

attribute [local instance] HasDerivedCategory.standard

/-! ### Two criteria for the Mittag-Leffler condition -/

/-- **An inverse system of zero objects is Mittag-Leffler.** A zero object has exactly one
subobject, so the transition images into a fixed term cannot differ. -/
theorem isMittagLefflerCategorical_of_isZero {C : Type*} [Category C] [Abelian C]
    (F : ℕᵒᵖ ⥤ C) (hF : ∀ n : ℕᵒᵖ, IsZero (F.obj n)) : IsMittagLefflerCategorical F := fun i =>
  ⟨i, le_rfl, fun _ _ =>
    have := Subobject.subsingleton_of_isZero (hF (op i))
    Subsingleton.elim _ _⟩

/-- **A Mittag-Leffler criterion through an Artinian receptacle.** Let `F` be an inverse system
of modules and suppose that each term `Fᵢ` carries a map `dᵢ` to an Artinian module whose kernel
is contained in the image of *every* transition map `Fₖ ⟶ Fᵢ`. Then `F` satisfies the
Mittag-Leffler condition of [Stacks, Tag 02N0].

The terms themselves need not satisfy the descending chain condition: a submodule of `Fᵢ`
containing `ker dᵢ` is the full preimage of its image under `dᵢ`, so the transition images are
determined by their images in the Artinian module, where the descending chain they form
stabilizes. -/
@[ega "0 13.1.2" "special case"]
theorem isMittagLefflerCategorical_of_ker_le_range {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (Q : ℕ → ModuleCat.{v} A) (hQ : ∀ i, IsArtinian A (Q i))
    (d : ∀ i : ℕ, F.obj (op i) ⟶ Q i)
    (hker : ∀ (i k : ℕ) (h : i ≤ k),
      LinearMap.ker (d i).hom ≤ LinearMap.range (F.map (homOfLE h).op).hom) :
    IsMittagLefflerCategorical F := by
  refine isMittagLefflerCategorical_of_forall_exists_range_eq F fun i => ?_
  have hart := hQ i
  let R : ℕ → Submodule A (F.obj (op i)) := fun n =>
    LinearMap.range (F.map (homOfLE (show i ≤ i + n by omega)).op).hom
  have hmono : ∀ a b : ℕ, a ≤ b → R b ≤ R a := by
    intro a b hab
    dsimp only [R]
    rw [inverseSystem_transition_comp F (show i ≤ i + a by omega) (show i + a ≤ i + b by omega),
      ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  have hcomap : ∀ n, Submodule.comap (d i).hom (Submodule.map (d i).hom (R n)) = R n := fun n =>
    Submodule.comap_map_eq_self (hker i (i + n) (by omega))
  let f : ℕ →o (Submodule A (Q i))ᵒᵈ :=
    { toFun := fun n => Submodule.map (d i).hom (R n)
      monotone' := fun a b hab => Submodule.map_mono (hmono a b hab) }
  obtain ⟨c, hc⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨i + c, by omega, fun k hck => ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, k = i + e := ⟨k - i, by omega⟩
  change R e = R c
  rw [← hcomap e, ← hcomap c]
  exact congrArg (Submodule.comap (d i).hom) (hc e (by omega)).symm

namespace Stacks.Cohomology.ModuleComparison

/-- **The cohomology of unbounded derived sections over a base ring is the classical right
derived functor of sections, `A`-linearly.** For a ringed space `X` and a ring homomorphism
`ρ : A ⟶ Γ(X, 𝒪_X)`, the degree-`n` cohomology of `RΓ(X, -)` applied to a sheaf of modules placed
in degree zero is the value of the `n`-th right derived functor of `Γ(X, -)`, read over `A`,
naturally in the sheaf of modules.

This refines `Stacks.Cohomology.ModuleComparison.hfunctorIsoHomologyDerivedSectionsOver`, which
states the same comparison after forgetting the module structures: both of its two inputs are
already `A`-linear, and only the identification of the classical right derived functor with the
repository's `Hfunctor` forgets the scalars. -/
def homologyDerivedSectionsOverIsoRightDerived (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
    (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier))) (n : ℕ) :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0 ⋙
        derivedSectionsOver X ρ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ) ≅
      (sectionsOverOpen X ⊤).rightDerived n ⋙ ModuleCat.restrictScalars ρ :=
  letI : (ModuleCat.restrictScalars.{u} ρ).PreservesHomology :=
    Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars ρ
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (sectionsOver X ρ) (derivedSectionsOver X ρ) (derivedSectionsOverUnit X ρ)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X) n ≪≫
    (rightDerivedCompIso (sectionsOverOpen X ⊤) (ModuleCat.restrictScalars.{u} ρ)
      (sectionsOver X ρ) (Iso.refl _) n).symm

/-- **The derived sections of a sheaf of modules have no cohomology in negative degrees.** For a
ringed space `X` and a ring homomorphism `ρ : A ⟶ Γ(X, 𝒪_X)`, the object `RΓ(X, ℱ)` of `D(A)`
attached to a sheaf of modules `ℱ` placed in degree zero lies in `D^{≥0}(A)`.

The chosen injective resolution of `ℱ`, extended by zero, is a complex vanishing below degree
zero and with injective terms, hence K-injective; so the unit of `RΓ(X, -)` is invertible there
and `RΓ(X, ℱ)` is the image in `D(A)` of the termwise sections of that resolution, a complex that
again vanishes below degree zero. -/
theorem isZero_homology_derivedSectionsOver_single_of_neg (X : RingedSpace.{u, u}) {A : Type u}
    [CommRing A] (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))
    (F : SheafOfModules.{u} (structureSheafRing X)) (m : ℤ) (hm : m < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj
      ((derivedSectionsOver X ρ).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj F))) := by
  let D : CochainComplex (ModuleCat.{u} A) ℤ :=
    ((sectionsOver X ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (injectiveResolution F).cochainComplex
  let e₁ : (derivedSectionsOver X ρ).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj F) ≅
      (derivedSectionsOver X ρ).obj
        (DerivedCategory.Qh.obj (Stacks.DerivedIndexing.resH.obj F)) :=
    (derivedSectionsOver X ρ).mapIso (Stacks.DerivedFunctor.singleIsoResCompQh.app F)
  let e₂ : (derivedSectionsOver X ρ).obj
        (DerivedCategory.Qh.obj (Stacks.DerivedIndexing.resH.obj F)) ≅
      DerivedCategory.Qh.obj (((sectionsOver X ρ).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj (Stacks.DerivedIndexing.resH.obj F)) :=
    ((Stacks.DerivedFunctor.resCompUnitIso (sectionsOver X ρ) (derivedSectionsOver X ρ)
      (derivedSectionsOverUnit X ρ)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)).app
        F).symm
  let e₃ : DerivedCategory.Qh.obj (((sectionsOver X ρ).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj (Stacks.DerivedIndexing.resH.obj F)) ≅
      DerivedCategory.Q.obj D :=
    DerivedCategory.Qh.mapIso
        ((Functor.mapHomotopyCategoryFactors (sectionsOver X ρ) (ComplexShape.up ℤ)).app
          (injectiveResolution F).cochainComplex) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app D
  have : ((derivedSectionsOver X ρ).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).obj F)).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso (e₁ ≪≫ e₂ ≪≫ e₃).symm 0
  exact DerivedCategory.isZero_of_isGE _ 0 m hm

end Stacks.Cohomology.ModuleComparison

namespace Stacks.Algebraization

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-! ### The descending chain condition -/

/-- **Stacks Project, Tag 0DX0, part (2).** Let `(A, 𝔪)` be a Noetherian local ring, let
`U = Spec A ∖ {𝔪}` be its punctured spectrum and let `ℱ` be a coherent `𝒪_U`-module. Then the
`A`-module `Hⁱ(U, ℱ)` satisfies the descending chain condition for every `i > 0`.

As in the source this comes from part (1) through Local Cohomology, Lemma [Stacks, Tag 0BK0]: the
coherent module `ℱ` is `M̃|_U` for a finite `A`-module `M`, the cohomology of `M̃` on the open
`Spec A ∖ V(𝔪)` of the ambient affine scheme computes `Hⁱ(U, ℱ)` by [Stacks, Tag 01E1] (2), and
in positive degrees that module is the local cohomology `H^{i+1}_𝔪(M)`, which is Artinian by part
(1). See the module documentation for the chain of identifications. -/
@[stacks 0DX0 "part (2), for the derived sections of the punctured spectrum read as a ringed \
space"]
theorem isArtinian_homology_puncturedSpectrumDerivedSections [IsNoetherianRing A]
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [hFc : SheafOfModules.IsCoherent F] (p : ℕ) (hp : 1 ≤ p) :
    IsArtinian A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p : ℤ)).obj
      ((puncturedSpectrumDerivedSections A).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (structureSheafRing (puncturedSpectrumRingedSpace A))) 0).obj F))) := by
  have hNoeth : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  set V := Stacks.Divisors.puncturedSpectrum A with hVdef
  have hV : V = zeroLocusCompl (A := CommRingCat.of A) (IsLocalRing.maximalIdeal A) :=
    TopologicalSpace.Opens.ext (congrArg compl zeroLocus_maximalIdeal.symm)
  have hcpt : IsCompact V.1 := by
    rw [hV]
    exact isCompact_zeroLocusCompl _
  -- [Stacks, Tag 0BK0] part (1): the coherent module is `M̃|_U` for a finite `M`.
  have hcoh : _root_.SheafOfModules.IsCoherent (show V.toScheme.Modules from F) :=
    ⟨hFc.isFiniteType, hFc.kernel_isFiniteType⟩
  obtain ⟨hq, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (show V.toScheme.Modules from F)
  have _ := hq
  have _ := hft
  obtain ⟨M, hMfin, ⟨g⟩⟩ := AlgebraicGeometry.exists_finiteModule_tilde_restrict V hcpt
    (show V.toScheme.Modules from F)
  have _ := hMfin
  -- The chain of identifications of the module documentation.
  have e₁ := (Stacks.Cohomology.ModuleComparison.homologyDerivedSectionsOverIsoRightDerived
    (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) p).app F
  have e₂ : ((moduleGlobalSections V.toScheme).rightDerived p).obj ((tilde M).restrict V.ι) ≅
      ((moduleGlobalSections V.toScheme).rightDerived p).obj (show V.toScheme.Modules from F) :=
    ((moduleGlobalSections V.toScheme).rightDerived p).mapIso g
  have e₃ := (derivedSectionsOnOpenIso (Spec (CommRingCat.of A)) V p).app (tilde M)
  have e₄ : (Stacks.LocalCohomologyTilde.globalToBase (CommRingCat.of A)).obj
        (((sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace V).rightDerived p).obj
          (tilde M)) ≅
      (ModuleCat.restrictScalars (puncturedSpectrumScalars A)).obj
        (((moduleGlobalSections V.toScheme).rightDerived p).obj ((tilde M).restrict V.ι)) :=
    (Stacks.LocalCohomologyTilde.globalToBase (CommRingCat.of A)).mapIso e₃
  -- [Stacks, Tag 0DX0] part (1), through the comparison of [Stacks, Tag 0DWR].
  have hart : IsArtinian A (Stacks.LocalCohomology.puncturedSpectrumTildeCohomology A M p) :=
    Stacks.LocalCohomology.isArtinian_puncturedSpectrumTildeCohomology A M p hp
  have hart₂ : IsArtinian A
      ((Stacks.LocalCohomologyTilde.globalToBase (CommRingCat.of A)).obj
        (((sectionsOnOpen (Spec (CommRingCat.of A)).toRingedSpace V).rightDerived p).obj
          (tilde M))) := by
    rw [hV]
    exact hart
  have _ := hart₂
  exact isArtinian_of_linearEquiv (e₁ ≪≫
    (ModuleCat.restrictScalars (puncturedSpectrumScalars A)).mapIso e₂.symm ≪≫
      e₄.symm).symm.toLinearEquiv

/-! ### The Mittag-Leffler condition -/

/-- **Stacks Project, Tag 0DX1, part (2).** Let `(A, 𝔪)` be a Noetherian local ring and let
`U = Spec A ∖ {𝔪}` be its punctured spectrum. Let `(ℱₙ)` be an inverse system of coherent
`𝒪_U`-modules. Then for every `i > 0` the inverse system of `A`-modules `n ↦ Hⁱ(U, ℱₙ)` satisfies
the Mittag-Leffler condition.

As in the source this follows immediately from part (2) of [Stacks, Tag 0DX0]: each term of the
system has the descending chain condition, so the images of the transition maps into a fixed term
are eventually constant. No compatibility between the modules realizing the `ℱₙ` is needed,
because the Mittag-Leffler condition is a statement about one term at a time. -/
@[stacks 0DX1 "part (2), for the derived sections of the punctured spectrum read as a ringed \
space"]
theorem isMittagLefflerCategorical_puncturedSpectrumCohomologySystem [IsNoetherianRing A]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (p : ℕ) (hp : 1 ≤ p) :
    IsMittagLefflerCategorical (puncturedSpectrumCohomologySystem A S (p : ℤ)) := by
  refine Stacks.LocalCohomology.isMittagLefflerCategorical_of_isArtinian _ fun n => ?_
  have _ := hScoherent n
  exact isArtinian_homology_puncturedSpectrumDerivedSections A (S.obj n) p hp

/-- [Stacks, Tag 0DX1] part (2), with the degree read as an integer `p ≥ 1`. -/
theorem isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_of_one_le
    [IsNoetherianRing A]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n)) {p : ℤ} (hp : 1 ≤ p) :
    IsMittagLefflerCategorical (puncturedSpectrumCohomologySystem A S p) := by
  lift p to ℕ using (by omega)
  exact isMittagLefflerCategorical_puncturedSpectrumCohomologySystem A S hScoherent p (by omega)

/-- **The Mittag-Leffler condition in degree zero, for a tower of quotients of a coherent
module.** Let `(A, 𝔪)` be a Noetherian local ring, let `U = Spec A ∖ {𝔪}` be its punctured
spectrum, let `ℱ` be a coherent `𝒪_U`-module and let `(ℱₙ)` be an inverse system of coherent
`𝒪_U`-modules presented as quotients of `ℱ`, by compatible epimorphisms `πₙ : ℱ ⟶ ℱₙ`. Then the
inverse system of `A`-modules `n ↦ Γ(U, ℱₙ)` satisfies the Mittag-Leffler condition.

This is the degree [Stacks, Tag 0DX1] part (2) does not reach, and it is not reachable the same
way: the modules `Γ(U, ℱₙ)` need not satisfy the descending chain condition. What replaces that
is the long exact sequence of `0 → Kₙ → ℱ → ℱₙ → 0`, with `Kₙ` the kernel of `πₙ`, which is
coherent; it exhibits the image of `Γ(πₙ)` as the kernel of the connecting map
`δₙ : Γ(U, ℱₙ) ⟶ H¹(U, Kₙ)` into a module that *is* Artinian, by part (2) of [Stacks, Tag 0DX0]
above. Since `πₙ` factors through `π_k` for every `k ≥ n`, that kernel lies in the image of every
transition map into `Γ(U, ℱₙ)`, which is what
`isMittagLefflerCategorical_of_ker_le_range` asks for. See the module documentation. -/
theorem isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_zero [IsNoetherianRing A]
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n) :
    IsMittagLefflerCategorical (puncturedSpectrumCohomologySystem A S 0) := by
  let := Functor.IsRightDerivedFunctor.commShift
    (derivedSectionsOver (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A))
    (derivedSectionsOverUnit (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
      (ComplexShape.up ℤ)) ℤ
  have := derivedSectionsOver_isTriangulated (puncturedSpectrumRingedSpace A)
    (puncturedSpectrumScalars A)
  let sf := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0
  let H : ℤ → DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
    fun r => DerivedCategory.homologyFunctor (ModuleCat.{u} A) r
  let G : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)) ⥤
      ModuleCat.{u} A := sf ⋙ puncturedSpectrumDerivedSections A ⋙ H 0
  -- `0 → Kₙ → ℱ → ℱₙ → 0`, and the distinguished triangle it gives after `RΓ(U, -)`.
  have hSE : ∀ n : ℕ, (ShortComplex.kernelSequence (π (op n))).ShortExact := fun n =>
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstance
      epi_g := hπ_epi (op n) }
  let T : ℕ → Triangle (DerivedCategory (ModuleCat.{u} A)) := fun n =>
    (puncturedSpectrumDerivedSections A).mapTriangle.obj (hSE n).singleTriangle
  have hT : ∀ n, T n ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) := fun n =>
    (puncturedSpectrumDerivedSections A).map_distinguished _
      (hSE n).singleTriangle_distinguished
  refine isMittagLefflerCategorical_of_ker_le_range _ (fun n => (H 1).obj ((T n).obj₁)) ?_
    (fun n => (H 0).homologySequenceδ (T n) 0 1 rfl) ?_
  · -- `H¹(U, Kₙ)` is Artinian: `Kₙ` is a kernel of coherent modules, so coherent.
    intro n
    have : _root_.SheafOfModules.IsCoherent F :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent ‹_›
    have : _root_.SheafOfModules.IsCoherent (S.obj (op n)) :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent (hScoherent (op n))
    have : SheafOfModules.IsCoherent (kernel (π (op n))) :=
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
        (AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (π (op n)))
    have hart := isArtinian_homology_puncturedSpectrumDerivedSections A
      (kernel (π (op n))) 1 le_rfl
    rwa [Nat.cast_one] at hart
  · -- `ker δₙ` is the image of `Γ(πₙ)`, and `Γ(πₙ)` factors through `Γ(π_k)` for `k ≥ n`.
    intro i k hik
    have hfac : G.map (π (op i)) =
        G.map (π (op k)) ≫ (puncturedSpectrumCohomologySystem A S 0).map (homOfLE hik).op := by
      rw [← hπ_nat ((homOfLE hik).op)]
      exact G.map_comp _ _
    intro x hx
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
      ((H 0).homologySequence_exact₃ (T i) (hT i) 0 1 rfl) x (LinearMap.mem_ker.1 hx)
    refine ⟨(G.map (π (op k))).hom y, ?_⟩
    have h2 : (G.map (π (op i))).hom y = x := hy
    rwa [hfac, ModuleCat.hom_comp] at h2

/-- **The Mittag-Leffler condition in every degree, for a tower of quotients of a coherent
module.** In the situation of
`Stacks.Algebraization.isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_zero`, the
inverse system `n ↦ Hᵖ(U, ℱₙ)` satisfies the Mittag-Leffler condition for *every* `p : ℤ`.

Three ranges: for `p < 0` the system is zero, because `RΓ(U, -)` of a sheaf placed in degree zero
has no cohomology in negative degrees; for `p = 0` this is the previous lemma; for `p > 0` it is
[Stacks, Tag 0DX1] part (2), and neither the quotient presentation nor the coherence of `ℱ` is
used there. -/
theorem isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_of_quotientTower
    [IsNoetherianRing A]
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n)
    (p : ℤ) :
    IsMittagLefflerCategorical (puncturedSpectrumCohomologySystem A S p) := by
  rcases lt_trichotomy p 0 with hp | hp | hp
  · exact isMittagLefflerCategorical_of_isZero _ fun n =>
      Stacks.Cohomology.ModuleComparison.isZero_homology_derivedSectionsOver_single_of_neg
        (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) (S.obj n) p hp
  · subst hp
    exact isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_zero A F S hScoherent π
      hπ_epi hπ_nat
  · exact isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_of_one_le A S hScoherent
      (by omega)

/-! ### Tag 0DXI with the Mittag-Leffler hypothesis discharged -/

section Comparison

-- The three local instances the earlier statement of Tag 0DXI was elaborated with:
-- countable products in the two derived categories, and commutativity of the rings of sections
-- of the structure sheaf of the punctured spectrum, which multiplication by a global section
-- asks for. Re-activating the very declarations that file introduced keeps the statement below
-- literally the statement of that theorem.
attribute [local instance] derivedCategoryModuleCatHasProductsNat
attribute [local instance] derivedCategorySheafOfModulesHasProductsNat
attribute [local instance] puncturedSpectrumRingSheaf_isMulCommutative

/-- **The comparison of [Stacks, Tag 0DXI] at a derived limit, in degrees `i ≥ 2`, with no
Mittag-Leffler hypothesis.** Let
`(A, 𝔪)` be a Noetherian local ring, let `U = Spec A ∖ {𝔪}` be its punctured spectrum, let `ℱ` be
a coherent `𝒪_U`-module and let `I ⊆ A` be an ideal. Let `S` be the adic quotient tower
`n ↦ ℱ/Iⁿℱ`, pinned down by the quotient maps `π` through the universal property of killing
multiplication by `Iⁿ`, and let `ℒ` be a derived limit of that tower in `D(𝒪_U)` — by
[Stacks, Tag 0A0K] that is the derived completion `ℱ^∧`. Then for every `i ≥ 2` the comparison
map `Hⁱ(RΓ(U, ℒ)) ⟶ lim_n Hⁱ(U, ℱ/Iⁿℱ)` is an isomorphism — characterized by its composites with
the limit projections through a morphism `a : RΓ(U, ℒ) ⟶ ∏ₙ RΓ(U, ℱₙ)` required to exhibit
`RΓ(U, ℒ)` as a derived limit of `n ↦ RΓ(U, ℱₙ)`, so that the conclusion is about the comparison
map and not about some map.

This is
`Stacks.Algebraization.exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections`
with its
hypothesis `hML` discharged by
`Stacks.Algebraization.isMittagLefflerCategorical_puncturedSpectrumCohomologySystem`, which is
[Stacks, Tag 0DX1] part (2). The degree restriction is the one that lemma imposes: the Milnor
sequence in degree `i` consumes the Mittag-Leffler condition in degree `i - 1`, and Tag 0DX1 part
(2) supplies it for `i - 1 > 0`. As in that earlier statement the left-hand side is named by
`ℒ` rather than by `RΓ(U, ℱ)^∧`, so this carries no tag; the tag itself is
`Stacks.Algebraization.isIso_toLimit_homology_derivedCompletion_puncturedSpectrumSections` of
`PuncturedSpectrumDerivedCompletion.lean`. -/
theorem exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections_of_two_le
    [IsNoetherianRing A] (I : Ideal A)
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n)
    (hπ_smul : ∀ (n : ℕ) (a : A), a ∈ I ^ n →
      (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
        π (op n) = 0)
    (hπ_univ : ∀ (n : ℕ)
      (G : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) (f : F ⟶ G),
      (∀ a ∈ I ^ n,
        (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
          f = 0) →
      ∃ g : S.obj (op n) ⟶ G, π (op n) ≫ g = f)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))))
    (hL : IsDerivedLimit (S ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L)
    (i : ℤ) (hi : 2 ≤ i) :
    let Hi := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
    let RΓS : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      S ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0 ⋙
        puncturedSpectrumDerivedSections A
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ RΓS.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ RΓS.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : (puncturedSpectrumDerivedSections A).obj L ⟶ ∏ᶜ Y)
      (b : (∏ᶜ Y) ⟶ ((puncturedSpectrumDerivedSections A).obj L)⟦(1 : ℤ)⟧),
      Triangle.mk a d b ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
      ∃ q : Hi.obj ((puncturedSpectrumDerivedSections A).obj L) ⟶
          limit (puncturedSpectrumCohomologySystem A S i),
        (∀ n : ℕ, q ≫ limit.π (puncturedSpectrumCohomologySystem A S i) (op n) =
          Hi.map a ≫ Hi.map (Pi.π Y n)) ∧ IsIso q := by
  exact exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections A I F S hScoherent π
    hπ_epi hπ_nat hπ_smul hπ_univ L hL i
    (isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_of_one_le A S hScoherent
      (by omega))

/-- **The comparison of [Stacks, Tag 0DXI] at a derived limit, in degrees `i ≥ 2`, read as an
isomorphism of `A`-modules.** In
the situation of
`Stacks.Algebraization`
`.exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections_of_two_le`, the
comparison map exhibits the degree-`i` cohomology of `RΓ(U, ℒ)` as isomorphic to the inverse
limit of the `A`-modules `Hⁱ(U, ℱ/Iⁿℱ)`.  The isomorphism keeps the characterization by the
limit projections and `a` is still required to be a derived-limit structure map of
`n ↦ RΓ(U, ℱₙ)`, so what is asserted is that the comparison map is invertible and not merely
that the two modules are abstractly isomorphic. -/
theorem exists_homologyIso_limit_puncturedSpectrumSections_of_two_le
    [IsNoetherianRing A] (I : Ideal A)
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n)
    (hπ_smul : ∀ (n : ℕ) (a : A), a ∈ I ^ n →
      (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
        π (op n) = 0)
    (hπ_univ : ∀ (n : ℕ)
      (G : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) (f : F ⟶ G),
      (∀ a ∈ I ^ n,
        (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
          f = 0) →
      ∃ g : S.obj (op n) ⟶ G, π (op n) ≫ g = f)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))))
    (hL : IsDerivedLimit (S ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L)
    (i : ℤ) (hi : 2 ≤ i) :
    let Hi := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
    let RΓS : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      S ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0 ⋙
        puncturedSpectrumDerivedSections A
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ RΓS.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ RΓS.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : (puncturedSpectrumDerivedSections A).obj L ⟶ ∏ᶜ Y)
      (b : (∏ᶜ Y) ⟶ ((puncturedSpectrumDerivedSections A).obj L)⟦(1 : ℤ)⟧),
      Triangle.mk a d b ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
      ∃ e : Hi.obj ((puncturedSpectrumDerivedSections A).obj L) ≅
          limit (puncturedSpectrumCohomologySystem A S i),
        ∀ n : ℕ, e.hom ≫ limit.π (puncturedSpectrumCohomologySystem A S i) (op n) =
          Hi.map a ≫ Hi.map (Pi.π Y n) := by
  intro Hi RΓS Y d
  obtain ⟨a, b, hT, q, hq, hiso⟩ :=
    exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections_of_two_le
      A I F S hScoherent π hπ_epi hπ_nat hπ_smul hπ_univ L hL i hi
  exact ⟨a, b, hT, asIso q, hq⟩

/-- **The comparison of [Stacks, Tag 0DXI] at a derived limit, in degrees `i ≥ 2`, without the
Milnor triangle.** Let
`(A, 𝔪)` be a Noetherian local ring, let `U = Spec A ∖ {𝔪}` be its punctured spectrum, let `ℱ` be
a coherent `𝒪_U`-module and let `I ⊆ A` be an ideal. Let `S` be the adic quotient tower
`n ↦ ℱ/Iⁿℱ`, pinned down by the quotient maps `π` through the universal property of killing
multiplication by `Iⁿ`, and let `ℒ` be a derived limit of that tower in `D(𝒪_U)` — by
[Stacks, Tag 0A0K] that is the derived completion `ℱ^∧`. Then for every `i ≥ 2` the comparison
map `Hⁱ(RΓ(U, ℒ)) ⟶ lim_n Hⁱ(U, ℱ/Iⁿℱ)`, characterized by its composites with the limit
projections, is an isomorphism.

This is `Stacks.Algebraization.isIso_toLimit_homology_puncturedSpectrumSections` with its
hypothesis `hML` discharged by
`Stacks.Algebraization.isMittagLefflerCategorical_puncturedSpectrumCohomologySystem`, which is
[Stacks, Tag 0DX1] part (2). The degree restriction is the one that lemma imposes: the Milnor
sequence in degree `i` consumes the Mittag-Leffler condition in degree `i - 1`, and Tag 0DX1 part
(2) supplies it for `i - 1 > 0`. The form recording the Milnor triangle that `a` fits into is
`Stacks.Algebraization`
`.exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections_of_two_le`.

The left-hand side is named by a derived limit `ℒ`, so this carries no tag; [Stacks, Tag 0DXI]
itself, in every degree and with the derived completion `RΓ(U, ℱ)^∧` on the left, is
`Stacks.Algebraization.isIso_toLimit_homology_derivedCompletion_puncturedSpectrumSections` of
`PuncturedSpectrumDerivedCompletion.lean`. -/
theorem isIso_toLimit_homology_puncturedSpectrumSections_of_two_le
    [IsNoetherianRing A] (I : Ideal A)
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n)
    (hπ_smul : ∀ (n : ℕ) (a : A), a ∈ I ^ n →
      (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
        π (op n) = 0)
    (hπ_univ : ∀ (n : ℕ)
      (G : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) (f : F ⟶ G),
      (∀ a ∈ I ^ n,
        (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
          f = 0) →
      ∃ g : S.obj (op n) ⟶ G, π (op n) ≫ g = f)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))))
    (hL : IsDerivedLimit (S ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L)
    (i : ℤ) (hi : 2 ≤ i) :
    let Hi := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
    let RΓS : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      S ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0 ⋙
        puncturedSpectrumDerivedSections A
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ RΓS.obj (op n)
    ∃ (a : (puncturedSpectrumDerivedSections A).obj L ⟶ ∏ᶜ Y)
      (q : Hi.obj ((puncturedSpectrumDerivedSections A).obj L) ⟶
        limit (puncturedSpectrumCohomologySystem A S i)),
      (∀ n : ℕ, q ≫ limit.π (puncturedSpectrumCohomologySystem A S i) (op n) =
        Hi.map a ≫ Hi.map (Pi.π Y n)) ∧ IsIso q := by
  exact isIso_toLimit_homology_puncturedSpectrumSections A I F S hScoherent π hπ_epi hπ_nat
    hπ_smul hπ_univ L hL i
    (isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_of_one_le A S hScoherent
      (by omega))

/-- **The comparison of [Stacks, Tag 0DXI] at a derived limit, in degrees `i ≥ 2`, read as an
isomorphism of `A`-modules.** In
the situation of
`Stacks.Algebraization.isIso_toLimit_homology_puncturedSpectrumSections_of_two_le`, the degree-`i`
cohomology of `RΓ(U, ℒ)` is isomorphic to the inverse limit of the `A`-modules
`Hⁱ(U, ℱ/Iⁿℱ)`. -/
theorem nonempty_homologyIso_limit_puncturedSpectrumSections_of_two_le
    [IsNoetherianRing A] (I : Ideal A)
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n)
    (hπ_smul : ∀ (n : ℕ) (a : A), a ∈ I ^ n →
      (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
        π (op n) = 0)
    (hπ_univ : ∀ (n : ℕ)
      (G : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) (f : F ⟶ G),
      (∀ a ∈ I ^ n,
        (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
          f = 0) →
      ∃ g : S.obj (op n) ⟶ G, π (op n) ≫ g = f)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))))
    (hL : IsDerivedLimit (S ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L)
    (i : ℤ) (hi : 2 ≤ i) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((puncturedSpectrumDerivedSections A).obj L) ≅
      limit (puncturedSpectrumCohomologySystem A S i)) := by
  obtain ⟨-, q, -, hq⟩ := isIso_toLimit_homology_puncturedSpectrumSections_of_two_le A I F S
    hScoherent π hπ_epi hπ_nat hπ_smul hπ_univ L hL i hi
  exact ⟨asIso q⟩

/-- **The comparison of [Stacks, Tag 0DXI] at a derived limit, in every degree, with no
Mittag-Leffler hypothesis.** Let
`(A, 𝔪)` be a Noetherian local ring, let `U = Spec A ∖ {𝔪}` be its punctured spectrum, let `ℱ` be
a coherent `𝒪_U`-module and let `I ⊆ A` be an ideal. Let `S` be the adic quotient tower
`n ↦ ℱ/Iⁿℱ`, pinned down by the quotient maps `π` through the universal property of killing
multiplication by `Iⁿ`, and let `ℒ` be a derived limit of that tower in `D(𝒪_U)` — by
[Stacks, Tag 0A0K] that is the derived completion `ℱ^∧`. Then for *every* `i` the comparison map
`Hⁱ(RΓ(U, ℒ)) ⟶ lim_n Hⁱ(U, ℱ/Iⁿℱ)` is an isomorphism — characterized by its composites with the
limit projections through a morphism `a : RΓ(U, ℒ) ⟶ ∏ₙ RΓ(U, ℱₙ)` required to exhibit
`RΓ(U, ℒ)` as a derived limit of `n ↦ RΓ(U, ℱₙ)`, so that the conclusion is about the comparison
map and not about some map.

This is
`Stacks.Algebraization.exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections`
with its
hypothesis `hML` discharged in every degree, by
`Stacks.Algebraization`
`.isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_of_quotientTower`: the degrees
`i ≥ 2` are [Stacks, Tag 0DX1] part (2), the degree `i = 1` is the degree-zero Mittag-Leffler
statement proved above, and the degrees `i ≤ 0` hold because the inverse system in degree `i - 1`
vanishes. No hypothesis is added: the inputs are those of the source statement, and in
particular `hπ_epi` and `hπ_nat` are part of the presentation of the tower as `ℱ/Iⁿℱ`.

As in the earlier statements the left-hand side is named by `ℒ` rather than by `RΓ(U, ℱ)^∧`, so
this carries no tag; the tag itself is
`Stacks.Algebraization.isIso_toLimit_homology_derivedCompletion_puncturedSpectrumSections` of
`PuncturedSpectrumDerivedCompletion.lean`, which produces the `ℒ` this statement quantifies
over. -/
theorem isIso_toLimit_homology_puncturedSpectrumSections_of_isCoherent
    [IsNoetherianRing A] (I : Ideal A)
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n)
    (hπ_smul : ∀ (n : ℕ) (a : A), a ∈ I ^ n →
      (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
        π (op n) = 0)
    (hπ_univ : ∀ (n : ℕ)
      (G : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) (f : F ⟶ G),
      (∀ a ∈ I ^ n,
        (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
          f = 0) →
      ∃ g : S.obj (op n) ⟶ G, π (op n) ≫ g = f)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))))
    (hL : IsDerivedLimit (S ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L)
    (i : ℤ) :
    let Hi := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
    let RΓS : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      S ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0 ⋙
        puncturedSpectrumDerivedSections A
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ RΓS.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ RΓS.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : (puncturedSpectrumDerivedSections A).obj L ⟶ ∏ᶜ Y)
      (b : (∏ᶜ Y) ⟶ ((puncturedSpectrumDerivedSections A).obj L)⟦(1 : ℤ)⟧),
      Triangle.mk a d b ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
      ∃ q : Hi.obj ((puncturedSpectrumDerivedSections A).obj L) ⟶
          limit (puncturedSpectrumCohomologySystem A S i),
        (∀ n : ℕ, q ≫ limit.π (puncturedSpectrumCohomologySystem A S i) (op n) =
          Hi.map a ≫ Hi.map (Pi.π Y n)) ∧ IsIso q :=
  exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections A I F S hScoherent π
    hπ_epi hπ_nat hπ_smul hπ_univ L hL i
    (isMittagLefflerCategorical_puncturedSpectrumCohomologySystem_of_quotientTower A F S
      hScoherent π hπ_epi hπ_nat (i - 1))

/-- **The comparison of [Stacks, Tag 0DXI] at a derived limit, in every degree, read as an
isomorphism of `A`-modules.** In the
situation of
`Stacks.Algebraization.isIso_toLimit_homology_puncturedSpectrumSections_of_isCoherent`, the
comparison map exhibits the degree-`i` cohomology of `RΓ(U, ℒ)` as isomorphic to the inverse
limit of the `A`-modules `Hⁱ(U, ℱ/Iⁿℱ)`, for every `i`.  The isomorphism keeps the
characterization by the limit projections and `a` is still required to be a derived-limit
structure map of `n ↦ RΓ(U, ℱₙ)`, so what is asserted is that the comparison map is invertible
and not merely that the two modules are abstractly isomorphic. -/
theorem exists_homologyIso_limit_puncturedSpectrumSections_of_isCoherent
    [IsNoetherianRing A] (I : Ideal A)
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n)
    (hπ_smul : ∀ (n : ℕ) (a : A), a ∈ I ^ n →
      (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
        π (op n) = 0)
    (hπ_univ : ∀ (n : ℕ)
      (G : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) (f : F ⟶ G),
      (∀ a ∈ I ^ n,
        (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
          f = 0) →
      ∃ g : S.obj (op n) ⟶ G, π (op n) ≫ g = f)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))))
    (hL : IsDerivedLimit (S ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L)
    (i : ℤ) :
    let Hi := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
    let RΓS : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      S ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0 ⋙
        puncturedSpectrumDerivedSections A
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ RΓS.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ RΓS.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : (puncturedSpectrumDerivedSections A).obj L ⟶ ∏ᶜ Y)
      (b : (∏ᶜ Y) ⟶ ((puncturedSpectrumDerivedSections A).obj L)⟦(1 : ℤ)⟧),
      Triangle.mk a d b ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
      ∃ e : Hi.obj ((puncturedSpectrumDerivedSections A).obj L) ≅
          limit (puncturedSpectrumCohomologySystem A S i),
        ∀ n : ℕ, e.hom ≫ limit.π (puncturedSpectrumCohomologySystem A S i) (op n) =
          Hi.map a ≫ Hi.map (Pi.π Y n) := by
  intro Hi RΓS Y d
  obtain ⟨a, b, hT, q, hq, hiso⟩ := isIso_toLimit_homology_puncturedSpectrumSections_of_isCoherent
    A I F S hScoherent π hπ_epi hπ_nat hπ_smul hπ_univ L hL i
  exact ⟨a, b, hT, asIso q, hq⟩

end Comparison

end Stacks.Algebraization

end
