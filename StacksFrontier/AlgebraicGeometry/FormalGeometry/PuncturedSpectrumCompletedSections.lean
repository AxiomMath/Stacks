module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOverBase

/-!
# Completed sections on a punctured spectrum as a limit of cohomologies of adic quotients

Let `(A, 𝔪)` be a Noetherian local ring, let `U = Spec A ∖ {𝔪}` be its punctured spectrum, let
`ℱ` be a coherent `𝒪_U`-module and let `I ⊆ A` be an ideal.  [Stacks, Tag 0DXI] asserts
`Hⁱ(RΓ(U, ℱ)^∧) = lim_n Hⁱ(U, ℱ/Iⁿℱ)` for *every* `i`, the completion being the derived
`I`-adic completion.

This file proves the comparison for the object the source's chain of identities produces: the
derived sections `RΓ(U, ℒ)` of an object `ℒ` of `D(𝒪_U)` that is a derived limit of the tower
`n ↦ ℱ/Iⁿℱ`.  By [Stacks, Tag 0A0K] such an `ℒ` is the derived completion `ℱ^∧`, and by
[Stacks, Tag 0BLX] `RΓ(U, ℱ^∧)` is `RΓ(U, ℱ)^∧`.  The statements here take the derived limit
`ℒ` and the Mittag-Leffler condition as inputs, so that they apply to an arbitrary tower
satisfying it; [Stacks, Tag 0DXI] itself, with the derived `I`-adic completion `RΓ(U, ℱ)^∧` on
the left and nothing assumed, is
`Stacks.Algebraization.isIso_toLimit_homology_derivedCompletion_puncturedSpectrumSections` in
`PuncturedSpectrumDerivedCompletion.lean`.  See "How Tag 0DXI is completed" below.

## Main definitions

* `Stacks.Algebraization.puncturedSpectrumRingedSpace` — the punctured spectrum of a local ring,
  as a ringed space.
* `Stacks.Algebraization.puncturedSpectrumScalars` — the structure map `A ⟶ Γ(U, 𝒪_U)`, along
  which sections of an `𝒪_U`-module are `A`-modules.
* `Stacks.Algebraization.puncturedSpectrumDerivedSections` — `RΓ(U, -) : D(𝒪_U) ⥤ D(A)`.
* `Stacks.Algebraization.puncturedSpectrumCohomologySystem` — the inverse system of `A`-modules
  `n ↦ Hⁱ(U, ℱₙ)` attached to an inverse system `ℱₙ` of `𝒪_U`-modules.

## Main results

* `Stacks.Algebraization.isIso_toLimit_homology_puncturedSpectrumSections` — the comparison of
  [Stacks, Tag 0DXI] for the derived sections of a derived limit of the adic quotient tower: the
  comparison
  map `Hⁱ(RΓ(U, ℒ)) ⟶ lim_n Hⁱ(U, ℱ/Iⁿℱ)` characterized by the limit projections exists and is
  an isomorphism, in every degree `i` — no degree is excluded, and the Mittag-Leffler hypothesis
  is asked for in the single degree `i - 1`.
* `Stacks.Algebraization.nonempty_homologyIso_limit_puncturedSpectrumSections` — the same
  conclusion read as an isomorphism of `A`-modules.

## Implementation notes

*The punctured spectrum.*  `Stacks.Divisors.puncturedSpectrum A` is the open
`Spec A ∖ {𝔪} ⊆ Spec A` of the library; `puncturedSpectrumRingedSpace` is the associated open
subscheme read as a ringed space, which is the shape
`Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver` takes.  Nothing is restated at
the `AlgebraicGeometry.Scheme.Modules` spelling: sheaves of modules on `U` appear throughout as
`SheafOfModules (structureSheafRing (puncturedSpectrumRingedSpace A))`, which is the presentation
both the coherence predicate `SheafOfModules.IsCoherent` and the derived sections functor are
stated at.

*"For all `i`".*  The degree `i` ranges over `ℤ`, and the conclusion is universally quantified
over it; no degree is excluded and no boundedness hypothesis is imposed.

*The adic quotient tower.*  The tower `ℱ/Iⁿℱ` is carried as data — an inverse system `S`
together with quotient maps `π n : ℱ ⟶ Sₙ` — and pinned down by the two clauses `hπ_smul` and
`hπ_univ`: multiplication by any `a ∈ Iⁿ` dies in `Sₙ`, and `π n` is *universal* among maps out
of `ℱ` killing those multiplications.  That is exactly the universal property of `ℱ/Iⁿℱ`, since
`Iⁿℱ` is the image of `⨁_{a ∈ Iⁿ} ℱ ⟶ ℱ`, so the clauses determine each `Sₙ` up to canonical
isomorphism.  Multiplication by `a : A` is `Stacks.Cohomology.DerivedSectionsOverBase.baseSmul`,
the action of the global section `ρ a` of `𝒪_U` on every sheaf of modules.

Those two clauses, like the coherence of `ℱ` and of the terms `Sₙ`, are hypotheses of the source
statement rather than inputs of the derivation below: what the derivation consumes is the
Mittag-Leffler condition `hML` and the derived-limit hypothesis `hL`, and in the source those
are precisely where coherence and the adic structure of the tower enter (through
[Stacks, Tags 0DX1] and [Stacks, Tag 0A0K]).  They are recorded so that the statement is about
`ℱ/Iⁿℱ` and not about an arbitrary tower.

*Vanishing of `R¹lim`.*  The Mittag-Leffler condition on an inverse system of modules makes the
difference map `(xₙ) ↦ (xₙ - xₙ₊₁)` on the product of its terms an epimorphism; this is taken
from the abelian-group formulation of [Stacks, Tag 07KW] and transported to `ModuleCat A` along
the forgetful functor, which preserves the countable products involved.  The left-hand term of
the Milnor short exact sequence is the cokernel of that map, so it vanishes and the comparison
map is both a monomorphism and an epimorphism.

### How Tag 0DXI is completed

The statement of this file takes two of the four inputs the source cites as hypotheses, so that
it is the general comparison for any tower satisfying them; both are proved elsewhere in the
library, and the tag itself is assembled from them in `PuncturedSpectrumDerivedCompletion.lean`.

* [Stacks, Tag 0DX1] part (2) — for an inverse system `ℱₙ` of coherent `𝒪_U`-modules on the
  punctured spectrum, the inverse system `Hⁱ(U, ℱₙ)` satisfies the Mittag-Leffler condition for
  `i > 0`.  This is
  `Stacks.Algebraization.isMittagLefflerCategorical_puncturedSpectrumCohomologySystem` of
  `PuncturedSpectrumCohomologyMittagLeffler.lean`, and the same file proves the condition in
  every degree for the tower `ℱ/Iⁿℱ`.  Here it is the hypothesis `hML`, asked for in the single
  degree `i - 1` that the Milnor sequence in degree `i` consumes.
* [Stacks, Tag 0BLX] — the identity `RΓ(U, ℱ)^∧ = RΓ(U, ℱ^∧)`.  Together with
  [Stacks, Tag 0A0K] it is
  `Stacks.Algebraization.exists_isDerivedLimit_and_iso_derivedCompletion_derivedSections`, which
  produces one `ℒ` that is both a derived limit of the tower and has `RΓ(U, ℒ) ≅ RΓ(U, ℱ)^∧`.
  Here the left-hand side is `Hⁱ(RΓ(U, ℒ))` for a derived limit `ℒ` given as the hypothesis `hL`.

The other two inputs are used directly: [Stacks, Tag 0D60] in the form
`Stacks.Cohomology.DerivedSectionsOverBase.exists_shortExact_homology_derivedSectionsOver`, and
the derived-limit property of `hL`, which for the adic quotient tower is the conclusion of
[Stacks, Tag 0A0K].

## References

* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 0DX1](https://stacks.math.columbia.edu/tag/0DX1)
* [Stacks Project, Tag 0DXI](https://stacks.math.columbia.edu/tag/0DXI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsOverBase

universe u

namespace Stacks.Algebraization

attribute [local instance] HasDerivedCategory.standard

/-! ### Vanishing of the first derived inverse limit of a Mittag-Leffler system -/

section MittagLefflerVanishing

noncomputable local instance limAdditiveOnInvSystemAb :
    (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The image of a transition map of an inverse system of modules, read as a submodule through
the lattice isomorphism `ModuleCat.subobjectModule`, is the range of the corresponding linear
map. -/
theorem subobjectModule_transitionImage {A : Type u} [Ring A]
    {F : ℕᵒᵖ ⥤ ModuleCat.{u} A} (i k : ℕ) (h : i ≤ k) :
    ModuleCat.subobjectModule (F.obj (op i)) (transitionImage F i k h) =
      LinearMap.range (F.map (homOfLE h).op).hom := by
  have heq :
      Subobject.mk (image.ι (F.map (homOfLE h).op)) =
        Subobject.mk (ModuleCat.ofHom (F.map (homOfLE h).op).hom.range.subtype) :=
    Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.imageIsoRange _)
      (ModuleCat.imageIsoRange_hom_subtype _)
  rw [transitionImage, heq]
  exact (ModuleCat.subobjectModule (F.obj (op i))).apply_symm_apply _

/-- Stabilization of the images of the transition maps, as subobjects, implies the Mittag-Leffler
condition for the underlying inverse system of sets. -/
theorem isMittagLeffler_forget_of_isMittagLefflerCategorical {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hF : IsMittagLefflerCategorical F) :
    (F ⋙ forget (ModuleCat.{u} A)).IsMittagLeffler := by
  intro j
  obtain ⟨c, hjc, hstab⟩ := hF j.unop
  refine ⟨op c, (homOfLE hjc).op, ?_⟩
  intro k g
  have hjk : j.unop ≤ k.unop := leOfHom g.unop
  have hgeq : g = (homOfLE hjk).op := Subsingleton.elim _ _
  have hcm : c ≤ max c k.unop := le_max_left _ _
  have hkm : k.unop ≤ max c k.unop := le_max_right _ _
  have hrange : LinearMap.range (F.map (homOfLE (hjc.trans hcm)).op).hom =
      LinearMap.range (F.map (homOfLE hjc).op).hom := by
    have hsub := congrArg (ModuleCat.subobjectModule (F.obj (op j.unop)))
      (hstab (max c k.unop) hcm)
    rwa [subobjectModule_transitionImage, subobjectModule_transitionImage] at hsub
  have hfactor : (F.map (homOfLE (hjc.trans hcm)).op).hom =
      (F.map (homOfLE hjk).op).hom.comp (F.map (homOfLE hkm).op).hom := by
    have hcomp : F.map (homOfLE (hjc.trans hcm)).op =
        F.map (homOfLE hkm).op ≫ F.map (homOfLE hjk).op := by
      rw [← F.map_comp]
      congr 1
    rw [hcomp]
    rfl
  subst hgeq
  intro x hx
  have hx' : x ∈ LinearMap.range (F.map (homOfLE (hjc.trans hcm)).op).hom := by
    rw [hrange]
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy⟩
  rw [hfactor] at hx'
  obtain ⟨y, hy⟩ := hx'
  exact ⟨(F.map (homOfLE hkm).op).hom y, hy⟩

/-- The first derived inverse limit of a Mittag-Leffler inverse system of abelian groups
vanishes: the difference map on the product of the terms is an epimorphism. -/
private theorem epi_delta_of_isMittagLeffler (G : Rlim.InvSystemAb.{u})
    (hG : (G ⋙ forget Ab).IsMittagLeffler) : Epi (Rlim.delta G) := by
  obtain ⟨RF, α, hRF, _, _, hvanish, _⟩ := Rlim.lim_hasRightDerivedFunctor_and_computations.{u}
  obtain ⟨e⟩ := Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor RF α hRF G
  exact (Preadditive.epi_iff_isZero_cokernel _).2 (e.isZero_iff.1 (hvanish G hG))

/-- **The first derived inverse limit of a Mittag-Leffler system of modules vanishes.** The
difference map `(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))` on the product of the terms of an inverse system of
modules satisfying the Mittag-Leffler condition is an epimorphism. -/
theorem epi_milnorDifference_of_isMittagLefflerCategorical {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hF : IsMittagLefflerCategorical F) :
    Epi (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj (op n)) n -
      Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) := by
  let U : ModuleCat.{u} A ⥤ Ab.{u} := forget₂ (ModuleCat.{u} A) Ab.{u}
  let X : ℕ → ModuleCat.{u} A := fun n ↦ F.obj (op n)
  let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦ Pi.π X n -
    Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let d' : (∏ᶜ fun n : ℕ ↦ U.obj (X n)) ⟶ ∏ᶜ fun n : ℕ ↦ U.obj (X n) :=
    Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ U.obj (X n)) n -
      Pi.π (fun n : ℕ ↦ U.obj (X n)) (n + 1) ≫ U.map (F.map (homOfLE (Nat.le_succ n)).op)
  have hAb : Epi d' := by
    have hforget : ((F ⋙ U) ⋙ forget Ab).IsMittagLeffler :=
      isMittagLeffler_forget_of_isMittagLefflerCategorical F hF
    have hdelta := epi_delta_of_isMittagLeffler (F ⋙ U) hforget
    rwa [Rlim.delta_eq_lift] at hdelta
  let e := asIso (piComparison U X)
  have hd : U.map d ≫ e.hom = e.hom ≫ d' := by
    apply Pi.hom_ext
    intro n
    change (U.map d ≫ piComparison U X) ≫ Pi.π _ n = (piComparison U X ≫ d') ≫ Pi.π _ n
    rw [Category.assoc, piComparison_comp_π, ← U.map_comp]
    simp only [d, d', Pi.lift_comp_π, U.map_sub, U.map_comp, Category.assoc,
      Preadditive.comp_sub, piComparison_comp_π_assoc, piComparison_comp_π]
  have hcomp : Epi (U.map d ≫ e.hom) := by rw [hd]; infer_instance
  have hcancel : Epi ((U.map d ≫ e.hom) ≫ e.inv) := inferInstance
  have hmap : Epi (U.map d) := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hcancel
  exact (ModuleCat.epi_iff_surjective d).2 ((AddCommGrpCat.epi_iff_surjective _).1 hmap)

end MittagLefflerVanishing

/-! ### The punctured spectrum and its derived sections over the base -/

section PuncturedSpectrum

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- **The punctured spectrum of a local ring, as a ringed space.** This is the open subscheme
`Spec A ∖ {𝔪}` of `Spec A`, read as a ringed space so that its sheaves of modules and its
`A`-linear derived sections are available. -/
def puncturedSpectrumRingedSpace : RingedSpace.{u, u} :=
  (Stacks.Divisors.puncturedSpectrum A).toScheme.toLocallyRingedSpace.toRingedSpace

/-- **The structure map `A ⟶ Γ(U, 𝒪_U)`** of the punctured spectrum of `A`: the inverse of the
`Γ`–`Spec` adjunction isomorphism followed by the open immersion on global sections.  Sections of
an `𝒪_U`-module are `A`-modules by restriction of scalars along this map. -/
def puncturedSpectrumScalars :
    A →+* (structureSheafRing (puncturedSpectrumRingedSpace A)).obj.obj
      (op (⊤ : Opens (puncturedSpectrumRingedSpace A).carrier)) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    (Stacks.Divisors.puncturedSpectrum A).ι.appLE ⊤ ⊤ (by simp)).hom

/-- **`RΓ(U, -) : D(𝒪_U) ⥤ D(A)`**, the unbounded derived `A`-linear sections on the punctured
spectrum of `A`. -/
abbrev puncturedSpectrumDerivedSections :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  derivedSectionsOver (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A)

/-- **The inverse system `n ↦ Hⁱ(U, ℱₙ)` of `A`-modules** attached to an inverse system of
sheaves of modules on the punctured spectrum of `A`: place each term in degree zero, take derived
sections over `A` and read off cohomology in degree `i`. -/
abbrev puncturedSpectrumCohomologySystem
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) (i : ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  S ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0 ⋙
    puncturedSpectrumDerivedSections A ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) i

end PuncturedSpectrum

/-! ### The comparison map and Tag 0DXI -/

section Comparison

variable (A : Type u) [CommRing A] [IsLocalRing A]

noncomputable local instance derivedCategoryModuleCatHasProductsNat :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

noncomputable local instance derivedCategorySheafOfModulesHasProductsNat :
    HasProductsOfShape ℕ (DerivedCategory
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules
    (structureSheafRing (puncturedSpectrumRingedSpace A))

/-- On the punctured spectrum the rings of sections of the structure sheaf are commutative; this
is the form in which multiplication by a global section asks for it, and instance search does not
see it through the forgetful functor `CommRingCat ⥤ RingCat` that `structureSheafRing` postcomposes
with. -/
local instance puncturedSpectrumRingSheaf_isMulCommutative :
    ∀ V, IsMulCommutative ((structureSheafRing (puncturedSpectrumRingedSpace A)).obj.obj V) :=
  fun V ↦ inferInstanceAs
    (IsMulCommutative ((puncturedSpectrumRingedSpace A).presheaf.obj V))

/-- **The comparison of [Stacks, Tag 0DXI] at a derived limit of the adic quotient
tower.** Let `(A, 𝔪)` be a Noetherian local ring, let `U = Spec A ∖ {𝔪}` be its punctured
spectrum, let `ℱ` be a coherent `𝒪_U`-module and let `I ⊆ A` be an ideal.  Let `S` be the adic
quotient tower `n ↦ ℱ/Iⁿℱ`, pinned down by the quotient maps `π` through the universal property
of killing multiplication by `Iⁿ`, and let `ℒ` be a derived limit of that tower in `D(𝒪_U)` —
by [Stacks, Tag 0A0K] that is the derived completion `ℱ^∧`.  Then for *every* `i` the comparison
map
`Hⁱ(RΓ(U, ℒ)) ⟶ lim_n Hⁱ(U, ℱ/Iⁿℱ)`,
characterized by its composites with the limit projections, is an isomorphism.

The `R¹lim` term of the Milnor short exact sequence of [Stacks, Tag 0D60] vanishes because the
inverse system `n ↦ H^{i-1}(U, ℱ/Iⁿℱ)` is Mittag-Leffler, which is the input `hML`, asked for in
that one degree only.  This is the general comparison for any such tower; it carries no tag.
[Stacks, Tag 0DXI] itself, whose left-hand side is the derived `I`-adic completion
`RΓ(U, ℱ)^∧`, is
`Stacks.Algebraization.isIso_toLimit_homology_derivedCompletion_puncturedSpectrumSections`,
which supplies `hML` by [Stacks, Tag 0DX1] part (2) and its degree-zero and negative-degree
companions, and `ℒ` together with `RΓ(U, ℒ) ≅ RΓ(U, ℱ)^∧` by [Stacks, Tags 0A0K and 0BLX]. -/
theorem isIso_toLimit_homology_puncturedSpectrumSections
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
    (i : ℤ)
    (hML : IsMittagLefflerCategorical (puncturedSpectrumCohomologySystem A S (i - 1))) :
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
  -- `hScoherent` and the four clauses pinning down the tower are hypotheses of the source
  -- statement; in the source they enter through Tags 0DX1 and 0A0K, that is through `hML` and
  -- `hL`, and are not consumed again by the derivation. They are recorded here so that the
  -- statement is about the adic quotient tower of a coherent module and not about an
  -- arbitrary tower.
  have _ : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n) := hScoherent
  have _ : ∀ n : ℕᵒᵖ, Epi (π n) := hπ_epi
  have _ : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n := hπ_nat
  have _ := hπ_smul
  have _ := hπ_univ
  intro Hi RΓS Y
  obtain ⟨a, b, -, hdata⟩ :=
    exists_shortExact_homology_derivedSectionsOver (puncturedSpectrumRingedSpace A)
      (puncturedSpectrumScalars A)
      (S ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L hL
  obtain ⟨e, incl, q, w, -, -, hq, hshort⟩ := hdata i
  refine ⟨a, q, hq, ?_⟩
  have hepi : Epi (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (puncturedSpectrumCohomologySystem A S (i - 1)).obj (op n)) n -
        Pi.π (fun n : ℕ ↦ (puncturedSpectrumCohomologySystem A S (i - 1)).obj (op n)) (n + 1) ≫
          (puncturedSpectrumCohomologySystem A S (i - 1)).map (homOfLE (Nat.le_succ n)).op) :=
    epi_milnorDifference_of_isMittagLefflerCategorical
      (puncturedSpectrumCohomologySystem A S (i - 1)) hML
  have hzero := (Preadditive.epi_iff_isZero_cokernel _).1 hepi
  have hincl : incl = 0 := hzero.eq_of_src _ _
  have : Mono q := hshort.exact.mono_g hincl
  have : Epi q := hshort.epi_g
  exact isIso_of_mono_of_epi _

/-- **The comparison of [Stacks, Tag 0DXI] at a derived limit, as an `A`-module isomorphism.** In
the situation of `Stacks.Algebraization.isIso_toLimit_homology_puncturedSpectrumSections`, the
degree-`i` cohomology of `RΓ(U, ℒ)` is isomorphic to the inverse limit of the `A`-modules
`Hⁱ(U, ℱ/Iⁿℱ)`. -/
theorem nonempty_homologyIso_limit_puncturedSpectrumSections
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
    (i : ℤ)
    (hML : IsMittagLefflerCategorical (puncturedSpectrumCohomologySystem A S (i - 1))) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((puncturedSpectrumDerivedSections A).obj L) ≅
      limit (puncturedSpectrumCohomologySystem A S i)) := by
  obtain ⟨-, q, -, hq⟩ := isIso_toLimit_homology_puncturedSpectrumSections A I F S hScoherent π
    hπ_epi hπ_nat hπ_smul hπ_univ L hL i hML
  exact ⟨asIso q⟩

end Comparison

end Stacks.Algebraization

end
