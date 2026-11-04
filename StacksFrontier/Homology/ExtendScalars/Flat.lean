module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat extension of scalars on complexes

Extension of scalars `ModuleCat.extendScalars f` along a flat ring map `f : R →+* S` is additive,
preserves kernels and finite limits, preserves homology, and sends acyclic cochain complexes of
`R`-modules to acyclic complexes of `S`-modules. The modules live in the universe `max v u`,
where `u` is the universe of `R` and `S`.
-/

@[expose] public section

-- Needed by the `simpa ... using h2` step of `extendScalars_preservesKernel_of_flat`, which
-- unfolds `LinearMap.codRestrict` up to reducible transparency.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u v uR uS uM

/-- `ModuleCat.extendScalars f` along a ring map `f : R →+* S` is an additive functor
(it is a left adjoint): `f` extends scalars by `S ⊗[R] -`, which is additive on morphisms
because `LinearMap.baseChange` is. The ring universes and the module universe are independent,
so this covers every instantiation of `ModuleCat.extendScalars`. -/
instance extendScalars_additive {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) : (ModuleCat.extendScalars.{uR, uS, uM} f).Additive := by
  refine ⟨fun {X Y a b} => ModuleCat.hom_ext ?_⟩
  let _ := f.toAlgebra
  change LinearMap.baseChange S (a.hom + b.hom) =
    LinearMap.baseChange S a.hom + LinearMap.baseChange S b.hom
  exact LinearMap.baseChange_add a.hom b.hom

/-- Extension of scalars along a flat ring map preserves the kernel of every morphism, in
*every* module-size universe `max v u`: the universe-polymorphic left-exactness of the base
change `- ⊗_R S`.

Implementation notes: the module universe is pinned explicitly
(`{X Y : ModuleCat.{max v u} R}` and `ModuleCat.extendScalars.{u,u,max v u}`), because consumers
auto-generalize the module-size universe of `ModuleCat` and so do not unify with a statement
specialized to the ring universe `u` — which is all the `tensorLeft (ModuleCat.of R S)`
formulation can give, since `ModuleCat.of R S : ModuleCat.{u} R`. The result is an `instance`
keyed on `[Fact f.Flat]` (`RingHom.Flat` is a `def`, not a class), so that consumers discharge
it by typeclass synthesis after `haveI : Fact f.Flat := ⟨hf⟩`. -/
@[sga "3 V 9.1" "more general", sga "3 VIB 11.0" "special case"]
instance extendScalars_preservesKernel_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) [hf : Fact f.Flat]
    {X Y : ModuleCat.{max v u} R} (g : X ⟶ Y) :
    Limits.PreservesLimit (Limits.parallelPair g 0)
      (ModuleCat.extendScalars.{u,u,max v u} f) := by
  let := f.toAlgebra
  have : Module.Flat R S := hf.out
  let F := ModuleCat.extendScalars.{u,u,max v u} f
  let ι : (ModuleCat.kernelCone g).pt ⟶ X := Limits.Fork.ι (ModuleCat.kernelCone g)
  have hcomp0 : ι ≫ g = 0 := Limits.KernelFork.condition (ModuleCat.kernelCone g)
  have hFι : ⇑(ModuleCat.Hom.hom (F.map ι)) = ⇑(LinearMap.lTensor S (ModuleCat.Hom.hom ι)) := rfl
  have hFg : ⇑(ModuleCat.Hom.hom (F.map g)) = ⇑(LinearMap.lTensor S (ModuleCat.Hom.hom g)) := rfl
  have hinjF : Function.Injective ⇑(ModuleCat.Hom.hom (F.map ι)) := by
    rw [hFι]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.coe_injective
  have hexF : Function.Exact ⇑(ModuleCat.Hom.hom (F.map ι)) ⇑(ModuleCat.Hom.hom (F.map g)) := by
    rw [hFι, hFg]
    exact Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map (ModuleCat.Hom.hom g))
  have wF : F.map ι ≫ F.map g = F.map ι ≫ 0 := by
    rw [Limits.comp_zero, ← F.map_comp, hcomp0, F.map_zero]
  let φ := LinearMap.codRestrict (ModuleCat.Hom.hom (F.map g)).ker
      (ModuleCat.Hom.hom (F.map ι)) fun c => LinearMap.mem_ker.mpr (hexF.apply_apply_eq_zero c)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [hexF.linearMap_ker_eq] at hy
    obtain ⟨c, hc⟩ := hy
    exact ⟨c, Subtype.ext hc⟩
  let e := LinearEquiv.ofBijective φ ⟨fun _ _ hab => hinjF (congrArg Subtype.val hab), hφsurj⟩
  -- `e : F.obj (ker g) ≃ₗ[S] ker (F.map g).hom`; gives an iso of kernel forks.
  have keyFork : Limits.IsLimit (Limits.Fork.ofι (F.map ι) wF) := by
    refine Limits.IsLimit.ofIsoLimit (ModuleCat.kernelIsLimit (F.map g)) ?_
    refine Limits.Fork.ext e.toModuleIso.symm ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    have h2 : (φ (e.symm y) : (ModuleCat.Hom.hom (F.map g)).ker).val = y.val :=
      congrArg Subtype.val (e.apply_symm_apply y)
    simpa [φ, LinearMap.codRestrict, ModuleCat.kernelCone] using h2
  -- transfer to the image cone of the kernel cone of `g`
  have w0 : ι ≫ g = ι ≫ 0 := hcomp0.trans Limits.comp_zero.symm
  have key2 : Limits.IsLimit (F.mapCone (Limits.Fork.ofι ι w0)) := by
    refine (Limits.isLimitMapConeForkEquiv F w0).symm ?_
    convert keyFork using 2 <;> exact F.map_zero _ _
  have hforkiso : ModuleCat.kernelCone g ≅ Limits.Fork.ofι ι w0 :=
    Limits.Fork.ext (Iso.refl _) (by simp [ι])
  exact Limits.preservesLimit_of_preserves_limit_cone (ModuleCat.kernelIsLimit g) <|
    Limits.IsLimit.ofIsoLimit key2 ((Limits.Cone.functoriality _ F).mapIso hforkiso.symm)

/-- Extension of scalars along a flat ring map preserves finite limits, in every module-size
universe `max v u`.

Implementation note: the module universe is written explicitly to match
`extendScalars_preservesKernel_of_flat` and the universe consumers auto-generalize; see the
universe note there. -/
lemma extendScalars_preservesFiniteLimits_of_flat'
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) :
    Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u,u,max v u} f) := by
  have : Fact f.Flat := ⟨hf⟩
  exact Functor.preservesFiniteLimits_of_preservesKernels
    (ModuleCat.extendScalars.{u,u,max v u} f)

/-- Under flatness of `f`, `extendScalars f` preserves homology; this is exactness of
`- ⊗_R S`. -/
@[ega "III 6.1.1" "special case"]
lemma extendScalars_preservesHomology_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) :
    (ModuleCat.extendScalars.{u,u,max v u} f).PreservesHomology := by
  have : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u,u,max v u} f) :=
    extendScalars_preservesFiniteLimits_of_flat' f hf
  have : Limits.PreservesColimitsOfSize.{0,0} (ModuleCat.extendScalars.{u,u,max v u} f) :=
    (ModuleCat.extendRestrictScalarsAdj.{v,u,u} f).leftAdjoint_preservesColimits
  have : Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{u,u,max v u} f) :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits
      (ModuleCat.extendScalars.{u,u,max v u} f)
  exact Functor.preservesHomologyOfExact (ModuleCat.extendScalars.{u,u,max v u} f)

/-- Extension of scalars along a flat ring map, lifted to complexes, sends acyclic cochain
complexes of `R`-modules to acyclic cochain complexes of `S`-modules. -/
lemma acyclic_extendScalarsComplex_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ) (hM : M.Acyclic) :
    (((ModuleCat.extendScalars.{u,u,max v u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M).Acyclic := by
  have := extendScalars_preservesHomology_of_flat.{u,v} f hf
  exact fun i => (hM i).map (ModuleCat.extendScalars.{u,u,max v u} f)
