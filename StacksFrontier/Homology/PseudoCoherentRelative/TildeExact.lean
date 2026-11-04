module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafAffine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness

/-!
# The functor `M ↦ M^~` on an affine scheme is exact

Let `R` be a commutative ring. Mathlib's `AlgebraicGeometry.tilde.functor R` sends an `R`-module
`M` to the quasi-coherent `𝒪_{Spec R}`-module `M^~`. It is a left adjoint, so it preserves
colimits; this file shows that it also preserves kernels, hence is exact.

The proof is the usual one. Over a standard open `D(g)` the sections of `M^~` are the localization
`M_g`, by the instance `IsLocalizedModule.Away g (tilde.toOpen M (D g)).hom` that Mathlib provides,
and localization of modules is exact. Therefore the canonical comparison
`(ker f)^~ ⟶ ker (f^~)` is an isomorphism on sections over every standard open, and the standard
opens form a basis of `Spec R`, so it is an isomorphism.

## Main results

* `Stacks.AffineTilde.tilde_map_app_basicOpen` identifies the map induced by `tilde.map f` on
  sections over `D(g)` with the localization `IsLocalizedModule.map` of `f`.
* `Stacks.AffineTilde.exact_tilde_map_app_basicOpen`: sections over `D(g)` carry an exact
  sequence of `R`-modules to an exact sequence.
* `Stacks.AffineTilde.isLocalizing_of_bijective_apps`: `AlgebraicGeometry.IsLocalizing` is
  carried along a morphism that is merely bijective on the sections it mentions.
* `Stacks.AffineTilde.isIso_kernelComparison_tildeFunctor`: the comparison
  `(ker f)^~ ⟶ ker (f^~)` is an isomorphism.
* `Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor`: `tilde.functor R` preserves finite
  colimits. Finite limits are `AlgebraicGeometry.tilde.preservesFiniteLimits`.
* `Stacks.AffineTilde.tildeFunctor_preservesHomology`: `tilde.functor R` preserves homology, i.e.
  it is an exact functor.
* `Stacks.AffineTilde.isQuasicoherent_kernel`: the kernel of a morphism of quasi-coherent
  modules on an affine scheme is quasi-coherent, the kernel half of Stacks 01IC.

## Implementation notes

Mathlib computes the sections of a sheaf of modules in two interchangeable ways: as
`SheafOfModules.evaluation`, which is where the `PreservesFiniteLimits` instance lives, and as
the sections of `AlgebraicGeometry.modulesSpecToSheaf`, which is where the `tilde` API lives.
`Stacks.AffineTilde.evaluation_map_eq` records that the two agree on the nose, so both APIs can
be used on the same morphism.

The passage from "isomorphism on standard opens" to "isomorphism" does *not* go through
`TopCat.Sheaf.isIso_iff_isIso_basis` directly: applying that lemma with
`B := PrimeSpectrum.basicOpen` has to unify `Opens (PrimeSpectrum.Top R)` with
`Opens ↥(Spec R).toPresheafedSpace`, and that unification does not terminate inside the
heartbeat limit. It goes instead through `AlgebraicGeometry.isLocalizing_of_isIso_app_top`,
which performs the same reduction inside Mathlib, where it is already compiled. That lemma
needs `AlgebraicGeometry.IsLocalizing` for *both* sheaves, which is why
`Stacks.AffineTilde.isLocalizing_kernel_tilde` is proved first; `⊤ = D(1)`
(`PrimeSpectrum.basicOpen_one`) supplies the top-section hypothesis from the standard-open one.

The sections functor is introduced as a `private abbrev`, and the `Additive` and
`PreservesFiniteLimits` instances for it are restated explicitly: instance search does not see
through the abbreviation to Mathlib's instances for `SheafOfModules.evaluation`. Binding it with
`set` instead is worse — that defeats instance search altogether.

## References

* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum

universe u

namespace Stacks.AffineTilde

variable {R : CommRingCat.{u}}

/-- Every element of the submonoid of powers of `g` acts invertibly on the sections of an
`𝒪_{Spec R}`-module over the standard open `D(g)`. -/
theorem isUnit_algebraMap_powers (g : R) (M : (Spec R).Modules) (x : Submonoid.powers g) :
    IsUnit ((algebraMap R (Module.End R
      ((modulesSpecToSheaf.obj M).presheaf.obj (op (basicOpen g))))) (x : R)) := by
  obtain ⟨n, hn⟩ := x.2
  simp only at hn
  rw [show (x : R) = g ^ n from hn.symm, map_pow]
  exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) g le_rfl).pow n

/-- On sections over the standard open `D(g)`, the morphism `tilde.map f` is the localization
of `f` away from `g`. -/
theorem tilde_map_app_basicOpen {M N : ModuleCat.{u} R} (f : M ⟶ N) (g : R) :
    ((modulesSpecToSheaf.map (tilde.map f)).hom.app (op (basicOpen g))).hom =
      IsLocalizedModule.map (Submonoid.powers g) (tilde.toOpen M (basicOpen g)).hom
        (tilde.toOpen N (basicOpen g)).hom f.hom := by
  refine IsLocalizedModule.ext (Submonoid.powers g) (tilde.toOpen M (basicOpen g)).hom
    (isUnit_algebraMap_powers g (tilde N)) ?_
  ext x
  simp only [IsLocalizedModule.map_apply, LinearMap.coe_comp, Function.comp_apply]
  exact ConcreteCategory.congr_hom (tilde.toOpen_map_app f (basicOpen g)) x

/-- The two ways Mathlib computes the sections of a morphism of `𝒪_{Spec R}`-modules over an
open — through `modulesSpecToSheaf` and through `SheafOfModules.evaluation` — are the same
function. -/
theorem evaluation_map_eq {A B : (Spec R).Modules} (φ : A ⟶ B) (U : (Spec R).Opens) :
    ⇑((modulesSpecToSheaf.map φ).hom.app (op U)) =
      ⇑((SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)).map φ) :=
  rfl

/-- Taking sections over `D(g)` turns an exact sequence of `R`-modules into an exact sequence
of sections of the associated `𝒪_{Spec R}`-modules, because those sections are localizations. -/
theorem exact_tilde_map_app_basicOpen {K M N : ModuleCat.{u} R} (i : K ⟶ M) (f : M ⟶ N)
    (h : Function.Exact i.hom f.hom) (g : R) :
    Function.Exact ((modulesSpecToSheaf.map (tilde.map i)).hom.app (op (basicOpen g))).hom
      ((modulesSpecToSheaf.map (tilde.map f)).hom.app (op (basicOpen g))).hom := by
  rw [tilde_map_app_basicOpen, tilde_map_app_basicOpen]
  exact IsLocalizedModule.map_exact (Submonoid.powers g) (tilde.toOpen K (basicOpen g)).hom
    (tilde.toOpen M (basicOpen g)).hom (tilde.toOpen N (basicOpen g)).hom i.hom f.hom h

/-- Sections over the standard open `D(g)`, as a functor to modules over the ring of sections
on `D(g)`. This is the form of the sections functor that carries Mathlib's
`PreservesFiniteLimits` instance. -/
private abbrev sectionsOver (g : R) : (Spec R).Modules ⥤ ModuleCat Γ(Spec R, basicOpen g) :=
  SheafOfModules.evaluation (Spec R).ringCatSheaf (op (basicOpen g))

/-- Taking sections is additive. -/
private instance sectionsOver_additive (g : R) : (sectionsOver g).Additive :=
  show (SheafOfModules.forget (Spec R).ringCatSheaf ⋙
    PresheafOfModules.evaluation (Spec R).ringCatSheaf.obj (op (basicOpen g))).Additive from
      inferInstance

/-- Taking sections over an open is left exact. -/
private instance sectionsOver_preservesFiniteLimits (g : R) :
    PreservesFiniteLimits (sectionsOver g) :=
  show PreservesFiniteLimits
    (SheafOfModules.evaluation (Spec R).ringCatSheaf (op (basicOpen g))) from inferInstance

/-- `exact_tilde_map_app_basicOpen`, transported to the sections functor `sectionsOver g`. -/
private theorem sectionsOver_exact {K M N : ModuleCat.{u} R} (i : K ⟶ M) (f : M ⟶ N)
    (h : Function.Exact i.hom f.hom) (g : R) :
    Function.Exact ⇑((sectionsOver g).map ((tilde.functor R).map i))
      ⇑((sectionsOver g).map ((tilde.functor R).map f)) :=
  exact_tilde_map_app_basicOpen i f h g

/-- `Stacks.ClosedImmersion.IdealSheafAffine.injective_tilde_map_app_basicOpen`, transported to
the sections functor `sectionsOver g`. -/
private theorem sectionsOver_injective {K M : ModuleCat.{u} R} (i : K ⟶ M)
    (h : Function.Injective i.hom) (g : R) :
    Function.Injective ⇑((sectionsOver g).map ((tilde.functor R).map i)) :=
  Stacks.ClosedImmersion.IdealSheafAffine.injective_tilde_map_app_basicOpen i h g

/-- Over a standard open the comparison `(ker f)^~ ⟶ ker (f^~)` becomes an isomorphism of
modules of sections. -/
private theorem isIso_sectionsOver_kernelComparison {M N : ModuleCat.{u} R} (f : M ⟶ N) (g : R) :
    IsIso ((sectionsOver g).map (kernelComparison f (tilde.functor R))) := by
  have hψι : ((sectionsOver g).map (kernelComparison f (tilde.functor R)) ≫
        kernelComparison ((tilde.functor R).map f) (sectionsOver g)) ≫
        kernel.ι ((sectionsOver g).map ((tilde.functor R).map f)) =
      (sectionsOver g).map ((tilde.functor R).map (kernel.ι f)) := by
    rw [Category.assoc, kernelComparison_comp_ι, ← Functor.map_comp, kernelComparison_comp_ι]
  have hex := sectionsOver_exact (kernel.ι f) f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (ShortComplex.mk (kernel.ι f) f (kernel.condition f))).1
      (ShortComplex.exact_kernel f)) g
  have hinj := sectionsOver_injective (kernel.ι f)
    ((ModuleCat.mono_iff_injective _).1 inferInstance) g
  have hιinj : Function.Injective ⇑(kernel.ι ((sectionsOver g).map ((tilde.functor R).map f))) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hψ : IsIso ((sectionsOver g).map (kernelComparison f (tilde.functor R)) ≫
      kernelComparison ((tilde.functor R).map f) (sectionsOver g)) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, ?_⟩
    · intro a b hab
      refine hinj ?_
      rw [← ConcreteCategory.congr_hom hψι a, ← ConcreteCategory.congr_hom hψι b]
      simp only [ConcreteCategory.comp_apply, hab]
    · intro y
      have hy : (ConcreteCategory.hom ((sectionsOver g).map ((tilde.functor R).map f)))
          (kernel.ι ((sectionsOver g).map ((tilde.functor R).map f)) y) = 0 := by
        simpa using ConcreteCategory.congr_hom
          (kernel.condition ((sectionsOver g).map ((tilde.functor R).map f))) y
      obtain ⟨z, hz⟩ := (hex _).1 hy
      refine ⟨z, hιinj ?_⟩
      rw [← ConcreteCategory.comp_apply, hψι, hz]
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    ((sectionsOver g).map (kernelComparison f (tilde.functor R)))
    (kernelComparison ((tilde.functor R).map f) (sectionsOver g)) inferInstance hψ

/-- The comparison `(ker f)^~ ⟶ ker (f^~)` is an isomorphism on sections over every standard
open, in the form the basis criterion for sheaves asks for. -/
private theorem isIso_app_kernelComparison {M N : ModuleCat.{u} R} (f : M ⟶ N) (g : R) :
    IsIso ((modulesSpecToSheaf.map (kernelComparison f (tilde.functor R))).hom.app
      (op (basicOpen g))) :=
  (ConcreteCategory.isIso_iff_bijective
      ((modulesSpecToSheaf.map (kernelComparison f (tilde.functor R))).hom.app
        (op (basicOpen g)))).2
    ((ConcreteCategory.isIso_iff_bijective
      ((sectionsOver g).map (kernelComparison f (tilde.functor R)))).1
      (isIso_sectionsOver_kernelComparison f g))

/-- The comparison `(ker f)^~ ⟶ ker (f^~)` is an isomorphism on sections over `⊤`, since
`⊤ = D(1)`. -/
private theorem isIso_app_top_kernelComparison {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    IsIso ((modulesSpecToSheaf.map (kernelComparison f (tilde.functor R))).hom.app (op ⊤)) := by
  have h1 := isIso_app_kernelComparison f (1 : R)
  rwa [basicOpen_one] at h1

/-- A morphism of sheaves of `R`-modules on `Spec R` which is bijective on sections over `⊤`
and over every standard open carries `AlgebraicGeometry.IsLocalizing` from its source to its
target. This is `AlgebraicGeometry.isLocalizing_of_iso` with "isomorphism" relaxed to
"bijective on the sections that `IsLocalizing` mentions". -/
theorem isLocalizing_of_bijective_apps
    {M N : TopCat.Sheaf (ModuleCat.{u} R) (Spec R)} (φ : M ⟶ N)
    (htop : Function.Bijective (φ.hom.app (op ⊤)).hom)
    (hbasic : ∀ g : R, Function.Bijective (φ.hom.app (op (basicOpen g))).hom)
    (hM : IsLocalizing M) : IsLocalizing N := by
  intro g
  have h1 : IsLocalizedModule (Submonoid.powers g)
      ((φ.hom.app (op (basicOpen g))).hom ∘ₗ (M.obj.map (basicOpen g).leTop.op).hom) :=
    (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers g)
      (φ.hom.app (op (basicOpen g))).hom (hbasic g)).2 (hM g)
  rw [← ModuleCat.hom_comp, φ.hom.naturality (basicOpen g).leTop.op, ModuleCat.hom_comp] at h1
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers g)
    (φ.hom.app (op ⊤)).hom htop).1 h1

/-- The kernel of a morphism of associated sheaves is localizing, so it is in the image of
`M ↦ M^~`. -/
theorem isLocalizing_kernel_tilde {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    IsLocalizing (modulesSpecToSheaf.obj (kernel ((tilde.functor R).map f))) := by
  refine isLocalizing_of_bijective_apps
    (modulesSpecToSheaf.map (kernelComparison f (tilde.functor R))) ?_ ?_
    (isLocalizing_tilde (kernel f))
  · have := isIso_app_top_kernelComparison f
    exact ConcreteCategory.bijective_of_isIso _
  · intro g
    have := isIso_app_kernelComparison f g
    exact ConcreteCategory.bijective_of_isIso _

/-- The canonical comparison `(ker f)^~ ⟶ ker (f^~)` is an isomorphism: the functor `M ↦ M^~`
takes the kernel of a morphism of `R`-modules to the kernel of its image. -/
theorem isIso_kernelComparison_tildeFunctor {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    IsIso (kernelComparison f (tilde.functor R)) := by
  have h : IsIso (modulesSpecToSheaf.map (kernelComparison f (tilde.functor R))) := by
    exact isLocalizing_of_isIso_app_top (isIso_app_top_kernelComparison f)
      (isLocalizing_tilde (kernel f)) (isLocalizing_kernel_tilde f)
  exact isIso_of_reflects_iso _ modulesSpecToSheaf

/-- `M ↦ M^~` preserves kernels. -/
theorem preservesLimit_parallelPair_tildeFunctor {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (tilde.functor R) :=
  have := isIso_kernelComparison_tildeFunctor f
  PreservesKernel.of_iso_comparison _ _


/-- `M ↦ M^~` is a left adjoint, so it preserves finite colimits. -/
theorem preservesFiniteColimits_tildeFunctor (R : CommRingCat.{u}) :
    PreservesFiniteColimits (tilde.functor R) := inferInstance

/-- `M ↦ M^~` is an exact functor: being both left and right exact, it preserves homology.
This is the exactness of `~` used in the proof of Stacks 01IC. -/
theorem tildeFunctor_preservesHomology (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesHomology :=
  have := AlgebraicGeometry.tilde.preservesFiniteLimits R
  have := preservesFiniteColimits_tildeFunctor R
  inferInstance

/-
Stacks 01HV: `M ↦ M^~` is exact. Its left-adjoint instance gives right exactness; left exactness
is `AlgebraicGeometry.tilde.preservesFiniteLimits`, and exactness in the form of preservation of
homology is `Stacks.AffineTilde.tildeFunctor_preservesHomology`.
-/
add_to_stacks 01HV "tilde_exact: left exactness"
  AlgebraicGeometry.tilde.preservesFiniteLimits
add_to_stacks 01HV "tilde_exact: exactness as preservation of homology"
  Stacks.AffineTilde.tildeFunctor_preservesHomology

/-- On `Spec R` the kernel of a morphism of quasi-coherent modules is quasi-coherent. -/
private theorem isQuasicoherent_kernel_onSpec {M N : (Spec R).Modules} [hM : M.IsQuasicoherent]
    [hN : N.IsQuasicoherent] (f : M ⟶ N) : (kernel f).IsQuasicoherent := by
  obtain ⟨A, ⟨eM⟩⟩ : (tilde.functor R).essImage M := by rw [essImage_tilde]; exact hM
  obtain ⟨B, ⟨eN⟩⟩ : (tilde.functor R).essImage N := by rw [essImage_tilde]; exact hN
  obtain ⟨g, hg⟩ : ∃ g : A ⟶ B, (tilde.functor R).map g = eM.hom ≫ f ≫ eN.inv :=
    ⟨(tilde.functor R).preimage _, (tilde.functor R).map_preimage _⟩
  have := preservesLimit_parallelPair_tildeFunctor g
  have h1 : ((tilde.functor R).obj (kernel g)).IsQuasicoherent := inferInstance
  have h2 : (kernel ((tilde.functor R).map g)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (PreservesKernel.iso (tilde.functor R) g) h1
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (kernel.mapIso f ((tilde.functor R).map g) eM.symm eN.symm (by rw [hg]; simp)).symm h2

/-- Restriction of modules along an open immersion of schemes is left exact, because it is
computed on sections. -/
theorem preservesFiniteLimits_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.toPresheaf Y) :=
    preservesLimitsOfSize_shrink _
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf Y) := inferInstance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ Ab.{u}).obj f.opensFunctor.op) := inferInstance
  have e : Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X ≅
      Scheme.Modules.toPresheaf Y ⋙
        (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op := Iso.refl _
  have : PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf X) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf X)

/-- **Stacks Project, Tag 01IC (kernel).** The kernel of a morphism of quasi-coherent modules
on an affine scheme is quasi-coherent. The cokernel half is
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`. -/
@[stacks 01IC "kernel", ega "I 4.1.1" "affine, kernel"]
instance isQuasicoherent_kernel {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) : (kernel f).IsQuasicoherent := by
  have hF : PreservesFiniteLimits (Scheme.Modules.restrictFunctor X.isoSpec.inv) :=
    preservesFiniteLimits_restrictFunctor X.isoSpec.inv
  have hker : (Scheme.Modules.restrictFunctor X.isoSpec.inv).obj (kernel f) ≅
      kernel ((Scheme.Modules.restrictFunctor X.isoSpec.inv).map f) :=
    PreservesKernel.iso (Scheme.Modules.restrictFunctor X.isoSpec.inv) f
  have h' : (kernel ((Scheme.Modules.restrictFunctor X.isoSpec.inv).map f)).IsQuasicoherent :=
    isQuasicoherent_kernel_onSpec _
  have hG : ((Scheme.Modules.restrictFunctor X.isoSpec.hom).obj
      (kernel ((Scheme.Modules.restrictFunctor X.isoSpec.inv).map f))).IsQuasicoherent :=
    inferInstance
  have eF : (Scheme.Modules.restrictFunctor X.isoSpec.hom).obj
      ((Scheme.Modules.restrictFunctor X.isoSpec.inv).obj (kernel f)) ≅ kernel f :=
    ((Scheme.Modules.restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr X.isoSpec.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId).app (kernel f)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (eF.symm.trans ((Scheme.Modules.restrictFunctor X.isoSpec.hom).mapIso hker)).symm hG

end Stacks.AffineTilde

end
