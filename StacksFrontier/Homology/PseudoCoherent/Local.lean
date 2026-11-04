module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.RingTheory.LocalProperties.StandardCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence is local on the base

Let `R` be a commutative ring. Both `m`-pseudo-coherence and pseudo-coherence of an object of
the derived category `D(R)` can be checked after a flat base change which is locally faithful:
after localizing at finitely many elements `f 1, …, f r` generating the unit ideal, or after a
single faithfully flat ring map `R → R'`.

Everything below lives in the namespace `StacksDraft.PseudoCoherence`.

## Main definitions

* `localizationAwayFunctorAux`: derived extension of scalars from `R` to its localization `R_f`
  away from an element `f`.

## Main results

* `isPseudoCoherentFrom_and_isPseudoCoherent_of_localization`: pseudo-coherence descends from
  a finite principal open cover, Stacks 066D.
* `isPseudoCoherentFrom_and_isPseudoCoherent_of_faithfullyFlat_baseChange`: pseudo-coherence
  descends along a faithfully flat ring map, Stacks 068R.

## Implementation notes

The finite list of elements of the source is represented by a family indexed by a finite type.
Localization of an object of `D(R)` is the functor induced by the exact extension-of-scalars
functor along `R → Localization.Away f`; the localization of the cohomology of `K` is computed
by `localizationAwayHomologyIso`, which is what lets the descent statements of Stacks 00EO
apply degreewise.

For a general ring map `f : R →+* S` the source and the target ring may live in different
universes, so the flatness results of `StacksFrontier.Homology.ExtendScalars.Flat`, which pin both
rings to a single universe, are reproved here in the universe-polymorphic form the faithfully
flat descent argument needs. Scalar extension is applied termwise; for commutative rings this
is the source's tensor product of the complex with the target ring.

Both descent arguments run by induction on the number of degrees in which the cohomology of `K`
may fail to vanish, splitting off a finite free module in the top degree at each step and
replacing `K` by the cone; the two-out-of-three property of pseudo-coherence along a
distinguished triangle (Stacks 064R) then propagates the conclusion back.

## References

* [Stacks Project, Tag 066D](https://stacks.math.columbia.edu/tag/066D)
* [Stacks Project, Tag 068R](https://stacks.math.columbia.edu/tag/068R)
-/

@[expose] public section

-- The change-of-rings functors below elaborate deep instance problems.
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

-- We use the standard construction of the derived category of an abelian category, which
-- supplies the triangulated structure and the cohomology functors `Hⁱ`.
attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.PseudoCoherence

universe u v w u' v' w'

/-! ### Shared pseudo-coherence helpers -/

/-- Extension of scalars preserves zero morphisms, independently of the universes of the source
modules and target ring. -/
instance extendScalars_preservesZeroMorphisms
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, v, w} f).PreservesZeroMorphisms :=
  ⟨fun X Y => by
    ext m
    change (1 : S) ⊗ₜ[R,f] ((0 : X →ₗ[R] Y) m) = 0
    simp⟩

/-- Extension of scalars along a flat ring map preserves kernels, in arbitrary universes. -/
theorem preservesKernel_extendScalars_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat)
    {X Y : ModuleCat.{w} R} (g : X ⟶ Y) :
    Limits.PreservesLimit (Limits.parallelPair g 0)
      (ModuleCat.extendScalars.{u, v, w} f) := by
  let _ := f.toAlgebra
  have : Module.Flat R S := hf
  let F := ModuleCat.extendScalars.{u, v, w} f
  let ι : (ModuleCat.kernelCone g).pt ⟶ X := Limits.Fork.ι (ModuleCat.kernelCone g)
  have hcomp0 : ι ≫ g = 0 := Limits.KernelFork.condition (ModuleCat.kernelCone g)
  have hex : Function.Exact ⇑(ModuleCat.Hom.hom ι) ⇑(ModuleCat.Hom.hom g) :=
    LinearMap.exact_subtype_ker_map (ModuleCat.Hom.hom g)
  have hinjF : Function.Injective ⇑(ModuleCat.Hom.hom (F.map ι)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (ModuleCat.Hom.hom ι) Subtype.coe_injective
  have hexF : Function.Exact ⇑(ModuleCat.Hom.hom (F.map ι)) ⇑(ModuleCat.Hom.hom (F.map g)) :=
    Module.Flat.lTensor_exact S hex
  have wF : F.map ι ≫ F.map g = F.map ι ≫ 0 := by
    rw [Limits.comp_zero, ← F.map_comp, hcomp0, F.map_zero]
  have hker : (ModuleCat.Hom.hom (F.map g)).ker =
      (ModuleCat.Hom.hom (F.map ι)).range := hexF.linearMap_ker_eq
  have hmem : ∀ c, (ModuleCat.Hom.hom (F.map ι)) c ∈
      (ModuleCat.Hom.hom (F.map g)).ker := by
    intro c
    rw [hker]
    exact LinearMap.mem_range_self _ c
  let φ := LinearMap.codRestrict (ModuleCat.Hom.hom (F.map g)).ker
    (ModuleCat.Hom.hom (F.map ι)) hmem
  have hφinj : Function.Injective φ := fun a b hab => hinjF (congrArg Subtype.val hab)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [hker] at hy
    obtain ⟨c, hc⟩ := hy
    exact ⟨c, Subtype.ext hc⟩
  let e := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have keyFork : Limits.IsLimit (Limits.Fork.ofι (F.map ι) wF) := by
    refine Limits.IsLimit.ofIsoLimit (ModuleCat.kernelIsLimit (F.map g)) ?_
    refine Limits.Fork.ext e.toModuleIso.symm ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show (ModuleCat.Hom.hom (F.map ι)) (e.symm y) = y.val
    exact congrArg Subtype.val (e.apply_symm_apply y)
  have w0 : ι ≫ g = ι ≫ 0 := by rwa [Limits.comp_zero]
  have key2 : Limits.IsLimit (F.mapCone (Limits.Fork.ofι ι w0)) := by
    refine (Limits.isLimitMapConeForkEquiv F w0).symm ?_
    convert keyFork using 2 <;> exact F.map_zero _ _
  have hforkiso : ModuleCat.kernelCone g ≅ Limits.Fork.ofι ι w0 :=
    Limits.Fork.ext (Iso.refl _) (by simp [ι])
  exact Limits.preservesLimit_of_preserves_limit_cone (ModuleCat.kernelIsLimit g)
    (Limits.IsLimit.ofIsoLimit key2 ((Limits.Cone.functoriality _ F).mapIso hforkiso.symm))

/-- Extension of scalars along a flat ring map preserves finite limits, in arbitrary
universes. -/
theorem preservesFiniteLimits_extendScalars_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, v, w} f) := by
  have : ∀ {X Y : ModuleCat.{w} R}, (g : X ⟶ Y) →
      Limits.PreservesLimit (Limits.parallelPair g 0)
        (ModuleCat.extendScalars.{u, v, w} f) :=
    fun {_ _} g => preservesKernel_extendScalars_of_flat f hf g
  exact Functor.preservesFiniteLimits_of_preservesKernels
    (ModuleCat.extendScalars.{u, v, w} f)

/-- Extension of scalars preserves cokernels, in arbitrary universes: the tensor product is
right exact without any flatness hypothesis. -/
theorem preservesCokernel_extendScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) {X Y : ModuleCat.{w} R} (g : X ⟶ Y) :
    Limits.PreservesColimit (Limits.parallelPair g 0)
      (ModuleCat.extendScalars.{u, v, w} f) := by
  let _ := f.toAlgebra
  let F := ModuleCat.extendScalars.{u, v, w} f
  let π : Y ⟶ (ModuleCat.cokernelCocone g).pt :=
    Limits.Cofork.π (ModuleCat.cokernelCocone g)
  have hcomp0 : g ≫ π = 0 := Limits.CokernelCofork.condition (ModuleCat.cokernelCocone g)
  have hex : Function.Exact ⇑(ModuleCat.Hom.hom g) ⇑(ModuleCat.Hom.hom π) := by
    apply LinearMap.exact_iff.mpr
    show ((ModuleCat.Hom.hom g).range).mkQ.ker =
      (ModuleCat.Hom.hom g).range
    exact Submodule.ker_mkQ _
  have hsurj : Function.Surjective ⇑(ModuleCat.Hom.hom π) :=
    Submodule.mkQ_surjective _
  have hexF : Function.Exact ⇑(ModuleCat.Hom.hom (F.map g))
      ⇑(ModuleCat.Hom.hom (F.map π)) := lTensor_exact S hex hsurj
  have hsurjF : Function.Surjective ⇑(ModuleCat.Hom.hom (F.map π)) :=
    LinearMap.lTensor_surjective S hsurj
  have wF : F.map g ≫ F.map π = 0 ≫ F.map π := by
    rw [Limits.zero_comp, ← F.map_comp, hcomp0, F.map_zero]
  have keyCofork : Limits.IsColimit (Limits.Cofork.ofπ (F.map π) wF) :=
    ModuleCat.isColimitCokernelCofork (F.map g) (F.map π) hexF hsurjF
  have w0 : g ≫ π = 0 ≫ π := by rwa [Limits.zero_comp]
  have key2 : Limits.IsColimit (F.mapCocone (Limits.Cofork.ofπ π w0)) := by
    refine (Limits.isColimitMapCoconeCoforkEquiv F w0).symm ?_
    convert keyCofork using 2 <;> exact F.map_zero _ _
  have hcoforkiso : ModuleCat.cokernelCocone g ≅ Limits.Cofork.ofπ π w0 :=
    Limits.Cofork.ext (Iso.refl _) (by simp [π])
  exact Limits.preservesColimit_of_preserves_colimit_cocone (ModuleCat.cokernelIsColimit g)
    (Limits.IsColimit.ofIsoColimit key2
      ((Limits.Cocone.functoriality _ F).mapIso hcoforkiso.symm))

/-- Extension of scalars preserves finite colimits, in arbitrary universes. -/
theorem preservesFiniteColimits_extendScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{u, v, w} f) := by
  have : ∀ {X Y : ModuleCat.{w} R}, (g : X ⟶ Y) →
      Limits.PreservesColimit (Limits.parallelPair g 0)
        (ModuleCat.extendScalars.{u, v, w} f) :=
    fun {_ _} g => preservesCokernel_extendScalars f g
  exact Functor.preservesFiniteColimits_of_preservesCokernels
    (ModuleCat.extendScalars.{u, v, w} f)

/-- Flat scalar extension commutes with the cohomology of a cochain complex. -/
noncomputable def homology_extendScalarsIso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (i : ℤ) :
    (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homology i ≅
        (ModuleCat.extendScalars.{u, v, w} f).obj (K.homology i) := by
  let F := ModuleCat.extendScalars.{u, v, w} f
  let : Limits.PreservesFiniteLimits F :=
    preservesFiniteLimits_extendScalars_of_flat f hf
  let : Limits.PreservesFiniteColimits F := preservesFiniteColimits_extendScalars f
  let : F.PreservesHomology := Functor.preservesHomologyOfExact F
  exact (K.sc i).mapHomologyIso F

/-- Flat scalar extension commutes with the derived-category cohomology of a cochain
complex. -/
noncomputable def derivedHomology_extendScalarsIso
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≅
      (ModuleCat.extendScalars.{u, v, w} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj
          (DerivedCategory.Q.obj K)) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v w} S) i).app _ ≪≫
    homology_extendScalarsIso f hf K i ≪≫
    (ModuleCat.extendScalars.{u, v, w} f).mapIso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{w} R) i).symm.app K)

/-- A faithfully flat scalar extension reflects vanishing of a module. -/
theorem isZero_of_isZero_extendScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat) (M : ModuleCat.{w} R)
    (h : Limits.IsZero ((ModuleCat.extendScalars.{u, v, w} f).obj M)) :
    Limits.IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  algebraize [f]
  change Subsingleton (TensorProduct R S M) at h
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R S M

/-- A faithfully flat scalar extension reflects vanishing of derived-category cohomology. -/
theorem isZero_derivedHomology_of_isZero_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (i : ℤ)
    (h : Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))) :
    Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj
        (DerivedCategory.Q.obj K)) :=
  isZero_of_isZero_extendScalars f hf _
    (h.of_iso (derivedHomology_extendScalarsIso f hf.flat K i).symm)

/-- A faithfully flat scalar extension reflects finiteness of a module. -/
theorem finite_of_finite_extendScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat) (M : ModuleCat.{w} R)
    (h : Module.Finite S ((ModuleCat.extendScalars.{u, v, w} f).obj M)) :
    Module.Finite R M := by
  algebraize [f]
  change Module.Finite S (TensorProduct R S M) at h
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

/-- Vanishing of the cohomology of the base change in degrees `≥ m` gives `m`-pseudo-coherence
of `K` itself, by faithfully flat descent of vanishing. -/
private theorem isPseudoCoherentFrom_of_baseChange_vanishing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (m : ℤ)
    (hvanish : ∀ i : ℤ, m ≤ i →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)))) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m :=
  isPseudoCoherentFrom_of_homology_isZero (DerivedCategory.Q.obj K) m
    (fun i hi => isZero_derivedHomology_of_isZero_baseChange f hf K i (hvanish i hi))

/-- The top cohomology module of `K` is finite as soon as the base change is
`m`-pseudo-coherent with cohomology vanishing above `n`. -/
private theorem finite_topHomology_of_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (m n : ℤ)
    (hmn : m ≤ n)
    (hK : IsPseudoCoherentFrom
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) m)
    (hvanish : ∀ i : ℤ, n < i →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)))) :
    Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) n).obj
        (DerivedCategory.Q.obj K)) := by
  apply finite_of_finite_extendScalars f hf
  have hfin : Module.Finite S
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) n).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K))) :=
    _root_.PseudoCoherence.finite_homology_of_isPseudoCoherentFrom _ n (hK.mono hmn) hvanish
  exact Module.Finite.equiv
    (derivedHomology_extendScalarsIso f hf.flat K n).toLinearEquiv

/-- Descent of `m`-pseudo-coherence in every degree gives descent of pseudo-coherence. -/
private theorem pseudoCoherent_of_pseudoCoherentFrom_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (K : CochainComplex (ModuleCat.{w} R) ℤ)
    (h : ∀ m : ℤ,
      IsPseudoCoherentFrom
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) m →
        IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m)
    (hK : IsPseudoCoherent
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))) :
    IsPseudoCoherent (DerivedCategory.Q.obj K) :=
  (pseudoCoherent_iff_all _).mpr fun m => h m ((pseudoCoherent_iff_all _).mp hK m)

/-- A finite free module placed in a single degree is a bounded complex of finite free
modules. -/
private theorem boundedFiniteFree_single
    {R : Type u} [Ring R] (P : ModuleCat.{w} R)
    [Module.Finite R P] [Module.Free R P] (n : ℤ) :
    IsBoundedFiniteFree ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj P) := by
  refine ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩, fun i => ?_⟩
  by_cases hi : i = n
  · subst i
    let e := (HomologicalComplex.singleObjXSelf (.up ℤ) n P).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n P i hi)
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton _ _⟩

/-- Scalar extension takes a bounded complex of finite free modules to one. -/
private theorem boundedFiniteFree_extendScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (E : CochainComplex (ModuleCat.{w} R) ℤ) (hE : IsBoundedFiniteFree E) :
    IsBoundedFiniteFree
      (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj E) := by
  let _ := f.toAlgebra
  obtain ⟨⟨a, _⟩, ⟨b, _⟩, hfin⟩ := hE
  refine ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩, fun i => ?_⟩
  have := (hfin i).1
  have := (hfin i).2
  show Module.Finite S (TensorProduct R S (E.X i)) ∧
    Module.Free S (TensorProduct R S (E.X i))
  exact ⟨inferInstance, inferInstance⟩

/-- A projective object surjecting onto `Hⁿ(K)` supplies a chain map from the complex
concentrated in degree `n` which is epi on `Hⁿ`. -/
theorem exists_single_map_epi_homology
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℤ) (P : C) [Projective P]
    (π : P ⟶ K.homology n) [Epi π] :
    ∃ α : (HomologicalComplex.single C (.up ℤ) n).obj P ⟶ K,
      Epi (HomologicalComplex.homologyMap α n) := by
  let l := Projective.factorThru π (K.homologyπ n)
  let α := HomologicalComplex.mkHomFromSingle (l ≫ K.iCycles n)
    (fun j hj => by simp)
  refine ⟨α, ?_⟩
  have hl : l ≫ K.homologyπ n = π := Projective.factorThru_comp _ _
  have hc :
      (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) n P).inv ≫
        HomologicalComplex.cyclesMap α n = l := by
    apply (cancel_mono (K.iCycles n)).mp
    simp [α, Category.assoc]
  have he :
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n P).inv ≫
        HomologicalComplex.homologyMap α n = π := by
    rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ,
      Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, hc, hl]
  exact epi_of_epi_fac he

/-- A chain map which is epi on `Hⁿ` stays epi on derived-category cohomology. -/
theorem epi_derivedHomology_map
    {C : Type*} [Category C] [Abelian C]
    {E K : CochainComplex C ℤ} (α : E ⟶ K) (n : ℤ)
    [hα : Epi (HomologicalComplex.homologyMap α n)] :
    Epi ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map α)) := by
  let eE := (DerivedCategory.homologyFunctorFactors C n).app E
  let eK := (DerivedCategory.homologyFunctorFactors C n).app K
  have h : (DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map α) ≫ eK.hom =
      eE.hom ≫ HomologicalComplex.homologyMap α n :=
    (DerivedCategory.homologyFunctorFactors C n).hom.naturality α
  have he : Epi ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map α) ≫
      eK.hom) := by
    rw [h]
    exact epi_comp' (inferInstance : Epi eE.hom) hα
  exact (epi_comp_iff_of_isIso _ eK.hom).mp he

/-- Flat scalar extension preserves vanishing of derived-category cohomology. -/
theorem isZero_derivedHomology_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (i : ℤ)
    (h : Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj
      (DerivedCategory.Q.obj K))) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K))) :=
  ((ModuleCat.extendScalars.{u, v, w} f).map_isZero h).of_iso
    (derivedHomology_extendScalarsIso f hf K i)

/-- Splitting off the top cohomology: the cone of an approximation from a single degree `n`
has vanishing cohomology in all degrees `≥ n`. -/
theorem isZero_homology_mappingCone_of_single
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℤ) (P : C)
    (α : (HomologicalComplex.single C (.up ℤ) n).obj P ⟶ K)
    [Epi (HomologicalComplex.homologyMap α n)]
    (hK : ∀ i : ℤ, n < i →
      Limits.IsZero ((DerivedCategory.homologyFunctor C i).obj (DerivedCategory.Q.obj K)))
    (i : ℤ) (hi : n ≤ i) :
    Limits.IsZero ((DerivedCategory.homologyFunctor C i).obj
      (DerivedCategory.Q.obj (CochainComplex.mappingCone α))) := by
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α)
  have hT := DerivedCategory.mappingCone_triangle_distinguished α
  have hE : Limits.IsZero ((DerivedCategory.homologyFunctor C (i + 1)).obj T.obj₁) :=
    (HomologicalComplex.isZero_single_obj_homology (.up ℤ) n P (i + 1) (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors C (i + 1)).app _)
  apply (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1)).isZero_X₂
  · by_cases hin : i = n
    · subst i
      exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT n).mp
        (epi_derivedHomology_map α n)
    · exact (hK i (lt_of_le_of_ne hi (Ne.symm hin))).eq_of_src _ _
  · exact hE.eq_of_tgt _ _

/-- The inductive step of faithfully flat descent: replacing `K` by the cone of a finite free
approximation in the top degree `n` shortens the range in which the cohomology of the base
change may fail to vanish, while keeping the descent conclusion available. -/
private theorem exists_cone_descent_step
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Small.{w} R]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (m n : ℤ) (hmn : m ≤ n)
    (hK : IsPseudoCoherentFrom
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)) m)
    (hvanish : ∀ i : ℤ, n < i →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)))) :
    ∃ L : CochainComplex (ModuleCat.{w} R) ℤ,
      IsPseudoCoherentFrom
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj L)) m ∧
      (∀ i : ℤ, n ≤ i →
        Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj L)))) ∧
      (IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m →
        IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m) := by
  have := finite_topHomology_of_baseChange f hf K m n hmn hK hvanish
  let e : ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) n).obj
      (DerivedCategory.Q.obj K)) ≅ K.homology n :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{w} R) n).app K
  have : Module.Finite R (K.homology n) := Module.Finite.equiv e.toLinearEquiv
  obtain ⟨P, _, _, π, _⟩ := exists_finite_free_epi (K.homology n)
  obtain ⟨α, _⟩ := exists_single_map_epi_homology K n P π
  let E := (HomologicalComplex.single (ModuleCat.{w} R) (.up ℤ) n).obj P
  have hE : IsBoundedFiniteFree E := boundedFiniteFree_single P n
  let L := CochainComplex.mappingCone α
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α)
  have hT := DerivedCategory.mappingCone_triangle_distinguished α
  let F := ModuleCat.extendScalars.{u, v, w} f
  let : Limits.PreservesFiniteLimits F :=
    preservesFiniteLimits_extendScalars_of_flat f hf.flat
  let : Limits.PreservesFiniteColimits F := preservesFiniteColimits_extendScalars f
  have : Limits.PreservesColimitsOfShape (Discrete Limits.WalkingPair) F :=
    Limits.PreservesFiniteColimits.preservesFiniteColimits _
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  let D := F.mapDerivedCategory
  have hDE : IsPseudoCoherentFrom (D.obj (DerivedCategory.Q.obj E)) (m + 1) :=
    (isPseudoCoherentFrom_of_boundedFiniteFree _ (boundedFiniteFree_extendScalars f E hE)
      (Iso.refl _) (m + 1)).ofIso (F.mapDerivedCategoryFactors.app E).symm
  have hDK : IsPseudoCoherentFrom (D.obj (DerivedCategory.Q.obj K)) m :=
    hK.ofIso (F.mapDerivedCategoryFactors.app K).symm
  have hDL : IsPseudoCoherentFrom (D.obj (DerivedCategory.Q.obj L)) m :=
    _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_one m (D.mapTriangle.obj T)
      (D.map_distinguished T hT) hDE hDK
  exact ⟨L, hDL.ofIso (F.mapDerivedCategoryFactors.app L),
    fun i hi => isZero_derivedHomology_baseChange f hf.flat _ i
      (isZero_homology_mappingCone_of_single K n P α
        (fun j hj => isZero_derivedHomology_of_isZero_baseChange f hf K j (hvanish j hj)) i hi),
    _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT
      (isPseudoCoherentFrom_of_boundedFiniteFree E hE (Iso.refl _) m)⟩

/-- Faithfully flat descent of `m`-pseudo-coherence, given a bound on the range in which the
cohomology of the base change may fail to vanish. -/
private theorem isPseudoCoherentFrom_of_baseChange_of_bound
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Small.{w} R]
    (f : R →+* S) (hf : f.FaithfullyFlat) (m : ℤ) (d : ℕ)
    (K : CochainComplex (ModuleCat.{w} R) ℤ)
    (hK : IsPseudoCoherentFrom
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)) m)
    (hvanish : ∀ i : ℤ, m + (d : ℤ) ≤ i →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)))) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
  induction d generalizing K with
  | zero =>
    exact isPseudoCoherentFrom_of_baseChange_vanishing f hf K m
      (fun i hi => hvanish i (by simpa using hi))
  | succ d ih =>
    obtain ⟨L, hL, hvanishL, hKL⟩ := exists_cone_descent_step f hf K m (m + d)
      (by omega) hK (fun i hi => hvanish i (by omega))
    exact hKL (ih L hL hvanishL)

/-- Faithfully flat descent of `m`-pseudo-coherence. -/
@[sga "6 III 1.1.3" "special case", sga "6 III 1.10" "b)"]
private theorem isPseudoCoherentFrom_of_faithfullyFlat_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Small.{w} R]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (m : ℤ)
    (hK : IsPseudoCoherentFrom
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)) m) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
  obtain ⟨b, hb⟩ := isPseudoCoherentFrom_boundedAbove hK
  exact isPseudoCoherentFrom_of_baseChange_of_bound f hf m (b - m + 1).toNat K hK
    fun i hi => hb i (by omega)

/-- **Stacks 068R.** Both `m`-pseudo-coherence and pseudo-coherence descend along a faithfully
flat extension of commutative rings. -/
@[stacks 068R]
theorem isPseudoCoherentFrom_and_isPseudoCoherent_of_faithfullyFlat_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{max u w} R) ℤ) (m : ℤ) :
    (IsPseudoCoherentFrom
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, max u w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) m →
      IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m) ∧
    (IsPseudoCoherent
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, max u w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) →
      IsPseudoCoherent (DerivedCategory.Q.obj K)) :=
  ⟨isPseudoCoherentFrom_of_faithfullyFlat_baseChange f hf K m,
    pseudoCoherent_of_pseudoCoherentFrom_descent f K
      (isPseudoCoherentFrom_of_faithfullyFlat_baseChange f hf K)⟩

/-! ### Descent along a finite principal open cover, Stacks 066D

Localization away from an element is flat, so it induces an exact functor on module categories
and hence a functor on derived categories which commutes with cohomology. Finiteness and
vanishing of a module can be tested on a standard cover (Stacks 00EO), which turns the
degreewise bookkeeping into the same cone induction as above. -/

attribute [local instance] localizationAwayCommShift

attribute [local instance] localizationAway_isTriangulated

/-- **Stacks 066D.** Both `m`-pseudo-coherence and pseudo-coherence descend from a finite
principal open cover. -/
@[stacks 066D]
theorem isPseudoCoherentFrom_and_isPseudoCoherent_of_localization
    {R : Type u} [CommRing R] {ι : Type*} [Finite ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{max v u} R)) (m : ℤ) :
    ((∀ i, IsPseudoCoherentFrom ((localizationAwayFunctorAux.{u, v} (f i)).obj K) m) →
      IsPseudoCoherentFrom K m) ∧
    ((∀ i, IsPseudoCoherent ((localizationAwayFunctorAux.{u, v} (f i)).obj K)) →
      IsPseudoCoherent K) := by
  refine ⟨isPseudoCoherentFrom_of_localization f hf K m, fun h ↦ ?_⟩
  exact (pseudoCoherent_iff_all K).2
    (fun n ↦ isPseudoCoherentFrom_of_localization f hf K n
      (fun i ↦ (pseudoCoherent_iff_all
        ((localizationAwayFunctorAux.{u, v} (f i)).obj K)).1 (h i) n))

end StacksDraft.PseudoCoherence
