module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.RingTheory.Tor.TorOneBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# K-injective complexes under change of rings

Let `f : R → S` be a ring map. This file collects the three ways K-injectivity of a cochain
complex of modules travels along `f`:

* along restriction of scalars `(-)_R : Mod_S → Mod_R`, when `f` is flat;
* back along restriction of scalars, when `f` is an epimorphism of rings;
* along coextension of scalars `Hom_R(S, -) : Mod_R → Mod_S`, for any `f`.

All three are instances of one criterion, Stacks Tag 08BJ: a functor with a left adjoint that
preserves acyclicity carries K-injective complexes to K-injective complexes — except for the
epimorphism case, where instead restriction of scalars is *full*, so a null-homotopy downstairs
is the image of one upstairs.

## Background

For a ring `R`, `Mod_R` is the abelian category of left `R`-modules (`ModuleCat R`) and `K(𝒜)`
is the homotopy category of cochain complexes in `𝒜`. A cochain complex is *acyclic* if all its
cohomology objects vanish (`HomologicalComplex.Acyclic`), and *K-injective* (Stacks Tag 070H)
if `Hom_{K(𝒜)}(M, I) = 0` for every acyclic `M` — equivalently, every chain map from an acyclic
complex to it is null-homotopic, which is `CochainComplex.IsKInjective`.

Restriction of scalars `ModuleCat.restrictScalars f` regards an `S`-module as an `R`-module via
`r • n := f r • n`; coextension of scalars `ModuleCat.coextendScalars f` sends an `R`-module `M`
to the `R`-linear maps `S → M` with `(b · φ) b' := φ (b' b)`. Both act degreewise on complexes
via `Functor.mapHomologicalComplex`. Complexes are cochain complexes indexed by `ℤ`, with no
boundedness hypotheses.

## Main definitions

* `coextendComplex`: coextension of scalars applied degreewise to cochain complexes.

## Main results

* `isKInjective_restrictScalars_of_flat`: restriction of scalars along a flat ring map preserves
  K-injectivity.
* `isKInjective_of_restrictScalars_of_isEpi`: for an epimorphism of rings, a complex of
  `S`-modules that is K-injective over `R` is K-injective over `S`.
* `coextend_isKInjective`: coextension of scalars preserves K-injectivity.

## Universes

Module universes are forced to dominate the universe of the *target* ring, because the
adjunctions driving the proofs only exist there. `ModuleCat.restrictCoextendScalarsAdj.{v, u₁, u₂}`
is an adjunction `restrictScalars.{max v u₂, u₁, u₂} f ⊣ coextendScalars.{u₁, u₂, max v u₂} f`,
and this already shows in the functor itself, since `S →ₗ[R] M` lands in `Type (max u₂ w)`.
Stating the modules at a free universe `v` would demand `v = max v u₂`, which is not a solvable
level constraint; setting `u₂ := 0` recovers the `{S : Type}` form, where `max v 0 = v` made the
module universe look free.

Two rings in independent universes `u₁`, `u₂` are fine for the epimorphism and coextension
results. The flat case is stated with `R` and `S` in a single universe because its engine,
`acyclic_extendScalarsComplex_of_flat`, is.

## References

* [Stacks Project, Tag 0915](https://stacks.math.columbia.edu/tag/0915)
* [Stacks Project, Tag 0916](https://stacks.math.columbia.edu/tag/0916)
* [Stacks Project, Tag 0917](https://stacks.math.columbia.edu/tag/0917)
-/

@[expose] public section

open CategoryTheory

universe u₁ u₂ v w

/-! ### Restriction of scalars along a flat ring map -/

section Flat
set_option backward.isDefEq.respectTransparency false

/-- **Stacks Tag 0915.** Let `f : R → S` be a flat ring map of commutative rings. If `I` is a
K-injective complex of `S`-modules, then its restriction of scalars `res_f I` is a K-injective
complex of `R`-modules.

This is the adjoint criterion `CochainComplex.isKInjective_mapHomologicalComplex` (Stacks
13.31.9) applied to the extension–restriction adjunction `(- ⊗_R S) ⊣ res_f` (Stacks 05DQ,
`ModuleCat.extendRestrictScalarsAdj`): the left adjoint `- ⊗_R S` preserves acyclicity by
`acyclic_extendScalarsComplex_of_flat`, which is where flatness enters. -/
@[stacks 0915, sga "4 V 4.9" "special case"]
theorem isKInjective_restrictScalars_of_flat
    {R S : Type u₁} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (I : CochainComplex (ModuleCat.{max v u₁} S) ℤ) (hI : I.IsKInjective) :
    ((CochainComplex.restrictScalars f).obj I).IsKInjective :=
  CochainComplex.isKInjective_mapHomologicalComplex (ModuleCat.restrictScalars.{max v u₁} f)
    (ModuleCat.extendScalars.{u₁,u₁,max v u₁} f) (ModuleCat.extendRestrictScalarsAdj.{v,u₁,u₁} f)
    (acyclic_extendScalarsComplex_of_flat.{u₁,v} f hf) I

end Flat

/-! ### Restriction of scalars along an epimorphism of rings -/

section Epi

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]

/-- Over a ring epimorphism `R → S`, an `R`-linear map between `S`-modules is automatically
`S`-linear. The multiplication map `S ⊗_R M → M` is an isomorphism, so `s • m` corresponds to
`s ⊗ m`, and `1 ⊗ f` carries `s ⊗ m` to `s ⊗ f m`, i.e. `f (s • m)` to `s • f m`. -/
private lemma linearMap_map_smul_of_isEpi [Algebra.IsEpi R S]
    {M N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) (s : S) (m : M) : f (s • m) = s • f m := by
  apply (TensorProduct.lid' R S N).symm.injective
  simp only [TensorProduct.lid'_symm_apply]
  have h : 1 ⊗ₜ[R] (s • m) = s ⊗ₜ[R] m := by
    apply (TensorProduct.lid' R S M).injective
    simp
  calc
    1 ⊗ₜ[R] f (s • m) = s ⊗ₜ[R] f m := by
      simpa using congrArg (TensorProduct.map LinearMap.id f) h
    _ = 1 ⊗ₜ[R] (s • f m) := by
      apply (TensorProduct.lid' R S N).injective
      simp

/-- Restriction of scalars along an epimorphism of rings is a full functor: an `R`-linear map
between `S`-modules is automatically `S`-linear, because `S ⊗_R M = M` identifies `s • m` with
`s ⊗ m`, on which an `R`-linear map acts `S`-linearly. -/
theorem full_restrictScalars_of_isEpi [Algebra.IsEpi R S] :
    (ModuleCat.restrictScalars.{w} (algebraMap R S)).Full where
  map_surjective {X Y} f := by
    let _ : Module R X := Module.compHom X (algebraMap R S)
    let _ : Module R Y := Module.compHom Y (algebraMap R S)
    let f' : X →ₗ[R] Y :=
      { toFun := f
        map_add' := f.hom.map_add
        map_smul' := fun r x ↦ f.hom.map_smul r x }
    let _ : IsScalarTower R S X := .of_algebraMap_smul fun _ _ ↦ rfl
    let _ : IsScalarTower R S Y := .of_algebraMap_smul fun _ _ ↦ rfl
    let g : X →ₗ[S] Y :=
      { f' with
        map_smul' := linearMap_map_smul_of_isEpi f' }
    exact ⟨ModuleCat.ofHom g, by ext x; rfl⟩

/-- **Stacks 0916.** Let `R → S` be an epimorphism of commutative rings. If a complex of
`S`-modules is K-injective when regarded as a complex of `R`-modules, then it is K-injective as
a complex of `S`-modules.

Given an acyclic complex `K` of `S`-modules and a chain map `f : K → I`, restriction of scalars
keeps `K` acyclic, so the hypothesis supplies a null-homotopy of `res f`. Restriction of scalars
is full and faithful here, so that homotopy is the image of a null-homotopy of `f` itself. -/
@[stacks 0916]
theorem isKInjective_of_restrictScalars_of_isEpi [Algebra.IsEpi R S]
    (I : CochainComplex (ModuleCat.{max w u₁ u₂} S) ℤ)
    (hI : CochainComplex.IsKInjective
      (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I :
          CochainComplex (ModuleCat.{max w u₁ u₂} R) ℤ)) :
    CochainComplex.IsKInjective I := by
  let F := ModuleCat.restrictScalars.{max w u₁ u₂} (algebraMap R S)
  let _ : F.Full := full_restrictScalars_of_isEpi
  refine ⟨fun {K} f hK ↦ ?_⟩
  have hKR : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
    fun i ↦ ModuleCat.restrictScalars_map_exact (algebraMap R S) (K.sc i) (hK i)
  obtain ⟨h⟩ := hI.nonempty_homotopy_zero ((F.mapHomologicalComplex _).map f) hKR
  exact ⟨{
    hom := fun i j ↦ F.preimage (h.hom i j)
    zero i j hij := by
      apply F.map_injective
      simp [h.zero i j hij]
    comm i := by
      apply F.map_injective
      simpa [dNext, fromNext, prevD, toPrev] using h.comm i }⟩

end Epi

/-! ### Coextension of scalars -/

section Coextend

/-- The coextension-of-scalars functor `Hom_R(S, -)` is additive: as a right adjoint it
preserves limits, hence finite products. -/
instance coextendScalars_additive {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.coextendScalars.{u₁, u₂, max v u₂} f).Additive := by
  have : Limits.PreservesLimits (ModuleCat.coextendScalars.{u₁, u₂, max v u₂} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{v, u₁, u₂} f).rightAdjoint_preservesLimits
  exact Functor.additive_of_preserves_binary_products _

/-- Coextension of scalars `Hom_R(S, -)` along a ring map `f : R → S`, applied degreewise to
cochain complexes of `R`-modules to produce cochain complexes of `S`-modules. -/
noncomputable def coextendComplex {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    CochainComplex (ModuleCat.{max v u₂} R) ℤ ⥤ CochainComplex (ModuleCat.{max v u₂} S) ℤ :=
  (ModuleCat.coextendScalars.{u₁, u₂, max v u₂} f).mapHomologicalComplex _

/-- Correctness of `coextendComplex`: in each degree the object is `Hom_R(S, -)` applied to the
corresponding term of the original complex. -/
theorem coextendComplex_obj_X {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    (I : CochainComplex (ModuleCat.{max v u₂} R) ℤ) (n : ℤ) :
    ((coextendComplex.{u₁, u₂, v} f).obj I).X n =
      (ModuleCat.coextendScalars.{u₁, u₂, max v u₂} f).obj (I.X n) :=
  rfl

/-- Restriction of scalars carries acyclic complexes of `S`-modules to acyclic complexes of
`R`-modules: it changes neither the underlying abelian groups nor the maps, so it preserves
exactness degreewise. Unlike coextension, it constrains no universe. -/
theorem restrictScalars_acyclic {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    (N : CochainComplex (ModuleCat.{w} S) ℤ) (hN : N.Acyclic) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N).Acyclic := by
  intro i
  have h := hN i
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff] at h ⊢
  exact h

/-- **Stacks Tag 0917.** If `I` is a K-injective complex of `R`-modules, then its degreewise
coextension of scalars `Hom_R(S, I)` is a K-injective complex of `S`-modules.

This is the adjoint criterion `CochainComplex.isKInjective_mapHomologicalComplex` for the
adjunction `ModuleCat.restrictCoextendScalarsAdj f`, whose left adjoint `(-)_R` preserves
acyclicity by `restrictScalars_acyclic`. -/
@[stacks 0917]
theorem coextend_isKInjective {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    (I : CochainComplex (ModuleCat.{max v u₂} R) ℤ) (hI : I.IsKInjective) :
    ((coextendComplex.{u₁, u₂, v} f).obj I).IsKInjective :=
  CochainComplex.isKInjective_mapHomologicalComplex
    (ModuleCat.coextendScalars.{u₁, u₂, max v u₂} f)
    (ModuleCat.restrictScalars.{max v u₂} f)
    (ModuleCat.restrictCoextendScalarsAdj.{v, u₁, u₂} f)
    (restrictScalars_acyclic.{u₁, u₂, max v u₂} f) I

end Coextend

end
