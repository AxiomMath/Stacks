module

public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.ClauseSixConverse
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGeneration
public import StacksFrontier.AlgebraicGeometry.SchemeModulesSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.GermSpan
import StacksCore.Tactic.StacksAttribute

/-!
# The extension attached to a section of an invertible module vanishing at one point

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `ω` be a coherent `𝒪_X`-module with no nonzero coherent submodule
supported in dimension zero, let `ℒ` be an invertible `𝒪_X`-module with `ω ⊗ ℒ` coherent, and
let `s` be a global section of `ℒ` vanishing at a closed point `x` but at no generic point of an
irreducible component other than `x`. Multiplication by `s` then presents `ω ⊗ ℒ` as an
extension

`0 ⟶ ω ⟶ ω ⊗ ℒ ⟶ 𝒬 ⟶ 0`

with `𝒬` coherent of zero-dimensional support, and the first map vanishes at `x` in the sense
that the image of `ω_x` lies in `𝔪_x (ω ⊗ ℒ)_x`. This is the geometric half of the data that
`AlgebraicGeometry.CohenMacaulayCurveSituation.VanishingSectionData` of
`Curves/VanishingResults/DualizingTwistGeneration.lean` packages; the count of global sections
of `𝒬`, the remaining field of that structure, is not addressed here.

## Main definitions

* `AlgebraicGeometry.sectionMulHom`: **multiplication by a global section** `s` of `ℒ`, as a
  morphism `ω ⟶ ω ⊗ ℒ` landing in the sheafified tensor product of [Stacks, Tag 01CB]. It is
  `Stacks.TensorSectionNonvanishing.mulRight` at the monoidal spelling of the tensor product,
  carried across `Stacks.SchemeModulesSpelling.tensorSheafIsoMonoidal`.

## Main results

* `AlgebraicGeometry.notMem_supp_cokernel_of_surjective_mapFun` and
  `AlgebraicGeometry.notMem_supp_kernel_of_injective_mapFun`: the cokernel and the kernel of a
  morphism of `𝒪_X`-modules are unsupported at a point where its stalk map is surjective, resp.
  injective. The stalk functor of [Stacks, Tag 01AH] is a left adjoint, so it preserves the
  cokernel, and it preserves finite limits, so it preserves the kernel.
* `AlgebraicGeometry.bijective_mapFun_sectionMulHom`: **multiplication by `s` is bijective on the
  stalk at every point of the nonvanishing locus `X_s`**, which is clause 2 of
  [Stacks, Tag 01CY] as `Stacks.AmpleCharacterization.bijective_mapFun_mulRight_unitHom` has it.
* `AlgebraicGeometry.range_modulesStalkFunctor_map_sectionMulHom_le`: **multiplication by `s`
  lands in `𝔪_x (ω ⊗ ℒ)_x` at a point where `s` vanishes.** The germ of a product of sections
  lies in `𝔪_x` times the stalk as soon as the germ of its right factor does, which is
  `Stacks.AmpleCharacterization.germ_tensorSection_mem_maximalSmul`.
* `AlgebraicGeometry.notMem_genericPointsOne_of_isClosed_singleton` and
  `AlgebraicGeometry.mem_nonvanishingLocus_of_mem_genericPointsOne`: the point `x` is not the
  generic point of a one-dimensional component, so the hypothesis on `s` at the generic points
  covers *every* point of `Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.exists_shortExact_sectionMul`: **the whole
  package**, as the existence of a short exact sequence with the four properties listed above.

## Implementation notes

The support statements are read off `Stacks.ModuleSkyscraper.modulesStalkFunctor`, the stalk
functor valued in modules over the local ring, whose underlying abelian group is the stalk that
`SheafOfModules.supp` is defined by; `AlgebraicGeometry.modulesStalkFunctor_map_apply` records
that its action on morphisms is `Stacks.ModuleStalk.mapFun`, by `rfl`.

Multiplication by `s` is built in the *monoidal* spelling of the tensor product, where the whole
calculus of products of sections is available, and then carried to the
`Stacks.SheafOfModules.TensorSheafification` spelling that the consumer uses by the comparison
isomorphism; both the bijectivity and the vanishing statements survive that transport, the first
by `Stacks.AmpleCharacterization.bijective_mapFun_of_iso` and the second by
`Stacks.SectionProduct.mapFun_mem_maximalSmul`.

Coherence of a kernel or a cokernel is `AlgebraicGeometry.CoherentAbelian.isCoherent_kernel` and
`AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel`, but those are instances over a sheaf of
rings spelled `Sheaf (Opens.grothendieckTopology Y) RingCat`, which instance search does not
match against `X.ringCatSheaf`. They are therefore applied through the `_aux` wrappers below, in
the style of `Curves/VanishingResults/DualizingTwistGeneration.lean`. For the same reason the
monomorphy of `kernel.ι` and the epimorphy of `cokernel.π` are produced from the universal
properties rather than by instance search.

## References

* [Stacks Project, Tag 0B58](https://stacks.math.columbia.edu/tag/0B58)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace Opposite
open Stacks.ModuleSkyscraper (modulesStalkFunctor)
open Stacks.AlgebraicGeometry.ComponentDegrees (genericPointsOne mem_genericPointsOne_iff)
open Stacks.Ample (nonvanishingLocus)
open Stacks.TensorSectionNonvanishing (mulRight)

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The stalk functor of Stacks Tag 01AH and the support of Stacks Tag 056J -/

/-- **The stalk functor valued in modules over the local ring acts on morphisms by
`Stacks.ModuleStalk.mapFun`.** Both are the stalk map of the underlying morphism of presheaves of
abelian groups, so this is `rfl`; it exists because the two spellings are used by disjoint parts
of the library. -/
public theorem modulesStalkFunctor_map_apply {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (x : X) (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :
    ((modulesStalkFunctor X x).map φ).hom m = Stacks.ModuleStalk.mapFun φ x m := rfl

/-- A module whose stalk over the local ring at `x` has at most one element is not supported at
`x`: the support of [Stacks, Tag 056J] is the set of points with a nonzero germ, and the carrier
of the stalk module is that stalk. -/
public theorem notMem_supp_of_subsingleton_modulesStalk {X : Scheme.{u}} (M : X.Modules) (x : X)
    (h : Subsingleton ((modulesStalkFunctor X x).obj M)) : x ∉ SheafOfModules.supp M := by
  intro hmem
  obtain ⟨a, ha⟩ := hmem
  exact ha (@Subsingleton.elim _ h a 0)

/-- **The cokernel of a morphism of `𝒪_X`-modules is not supported where the stalk map of that
morphism is surjective.** The stalk functor of [Stacks, Tag 01AH] is a left adjoint, so it
carries the cokernel to the cokernel of the stalk map, which vanishes because a surjective map of
modules is an epimorphism. -/
public theorem notMem_supp_cokernel_of_surjective_mapFun {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (x : X) (h : Function.Surjective (Stacks.ModuleStalk.mapFun φ x)) :
    x ∉ SheafOfModules.supp (cokernel φ) := by
  have hsurj : Function.Surjective ((modulesStalkFunctor X x).map φ) := fun z => by
    obtain ⟨m, hm⟩ := h z
    exact ⟨m, (modulesStalkFunctor_map_apply φ x m).trans hm⟩
  have hepi : Epi ((modulesStalkFunctor X x).map φ) := (ModuleCat.epi_iff_surjective _).mpr hsurj
  have hz : IsZero (cokernel ((modulesStalkFunctor X x).map φ)) :=
    (Preadditive.epi_iff_isZero_cokernel _).mp hepi
  exact notMem_supp_of_subsingleton_modulesStalk (cokernel φ) x
    (ModuleCat.subsingleton_of_isZero
      (hz.of_iso (PreservesCokernel.iso (modulesStalkFunctor X x) φ)))

/-- **The kernel of a morphism of `𝒪_X`-modules is not supported where the stalk map of that
morphism is injective.** The stalk functor of [Stacks, Tag 01AH] preserves finite limits, so it
carries the kernel to the kernel of the stalk map, which vanishes because an injective map of
modules is a monomorphism. -/
public theorem notMem_supp_kernel_of_injective_mapFun {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (x : X) (h : Function.Injective (Stacks.ModuleStalk.mapFun φ x)) :
    x ∉ SheafOfModules.supp (kernel φ) := by
  have hinj : Function.Injective ((modulesStalkFunctor X x).map φ) := fun a b hab =>
    h ((modulesStalkFunctor_map_apply φ x a).symm.trans
      (hab.trans (modulesStalkFunctor_map_apply φ x b)))
  have hmono : Mono ((modulesStalkFunctor X x).map φ) := (ModuleCat.mono_iff_injective _).mpr hinj
  have hz : IsZero (kernel ((modulesStalkFunctor X x).map φ)) :=
    (Preadditive.mono_iff_isZero_kernel _).mp hmono
  exact notMem_supp_of_subsingleton_modulesStalk (kernel φ) x
    (ModuleCat.subsingleton_of_isZero
      (hz.of_iso (PreservesKernel.iso (modulesStalkFunctor X x) φ)))

/-! ### Coherence of kernels and cokernels at the scheme spelling -/

/-- [Stacks, Tag 01BY] (3) for kernels, over a sheaf of rings on a topological space spelled as
`Sheaf (Opens.grothendieckTopology Y) RingCat`. -/
public theorem isCoherent_kernel_of_isCoherent_aux {Y : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}} {A B : SheafOfModules.{u} O}
    (hA : A.IsCoherent) (hB : B.IsCoherent) (ψ : A ⟶ B) : (kernel ψ).IsCoherent :=
  have := hA
  have := hB
  AlgebraicGeometry.CoherentAbelian.isCoherent_kernel ψ

/-- [Stacks, Tag 01BY] (3) for cokernels, over a sheaf of rings on a topological space spelled as
`Sheaf (Opens.grothendieckTopology Y) RingCat`. -/
public theorem isCoherent_cokernel_of_isCoherent_aux {Y : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}} {A B : SheafOfModules.{u} O}
    (hA : A.IsCoherent) (hB : B.IsCoherent) (ψ : A ⟶ B) : (cokernel ψ).IsCoherent :=
  have := hA
  have := hB
  AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel ψ

/-- **The kernel of a morphism of coherent `𝒪_X`-modules on a scheme is coherent**, which is
[Stacks, Tag 01BY] (3). -/
public theorem isCoherent_kernel_of_isCoherent {X : Scheme.{u}} {M N : X.Modules}
    (hM : M.IsCoherent) (hN : N.IsCoherent) (φ : M ⟶ N) : (kernel φ).IsCoherent :=
  isCoherent_kernel_of_isCoherent_aux (O := X.ringCatSheaf) hM hN φ

/-- **The cokernel of a morphism of coherent `𝒪_X`-modules on a scheme is coherent**, which is
[Stacks, Tag 01BY] (3). -/
public theorem isCoherent_cokernel_of_isCoherent {X : Scheme.{u}} {M N : X.Modules}
    (hM : M.IsCoherent) (hN : N.IsCoherent) (φ : M ⟶ N) : (cokernel φ).IsCoherent :=
  isCoherent_cokernel_of_isCoherent_aux (O := X.ringCatSheaf) hM hN φ

/-! ### Points closed in a curve are not generic points of its components -/

/-- **A point whose singleton is closed is not the generic point of a one-dimensional irreducible
component.** The closure of such a point is the singleton, and a singleton has dimension at most
zero, not one. -/
public theorem notMem_genericPointsOne_of_isClosed_singleton {X : Scheme.{u}} {x : X}
    (hx : IsClosed ({x} : Set X)) : x ∉ genericPointsOne X := by
  intro hmem
  have hdim := (mem_genericPointsOne_iff.mp hmem).2
  rw [hx.closure_eq] at hdim
  have hzero : topologicalKrullDim ({x} : Set X) ≤ 0 :=
    Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space
  rw [hdim] at hzero
  norm_num at hzero

/-! ### Multiplication by a global section -/

/-- **Multiplication by a global section `s` of `ℒ`**, as a morphism `ω ⟶ ω ⊗ ℒ` whose target is
the sheafified tensor product of [Stacks, Tag 01CB]. It is
`Stacks.TensorSectionNonvanishing.mulRight` at the monoidal spelling of that tensor product,
followed by the comparison isomorphism
`Stacks.SchemeModulesSpelling.tensorSheafIsoMonoidal`. -/
public def sectionMulHom {X : Scheme.{u}} (ω L : X.Modules) (s : Γ(L, ⊤)) :
    ω ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
        (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj (ω)).obj (L)) :=
  mulRight ω (Stacks.AmpleCharacterization.unitHom L s) ≫
    (Stacks.SchemeModulesSpelling.tensorSheafIsoMonoidal X ω L).hom

/-- Stalkwise, `sectionMulHom` is `mulRight` followed by the comparison isomorphism. -/
private theorem mapFun_sectionMulHom_apply {X : Scheme.{u}} (ω L : X.Modules) (s : Γ(L, ⊤))
    (y : X) (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ω.presheaf y) :
    Stacks.ModuleStalk.mapFun (sectionMulHom ω L s) y m =
      Stacks.ModuleStalk.mapFun
          (Stacks.SchemeModulesSpelling.tensorSheafIsoMonoidal X ω L).hom y
        (Stacks.ModuleStalk.mapFun (mulRight ω (Stacks.AmpleCharacterization.unitHom L s)) y m) :=
  Stacks.ModuleStalk.mapFun_comp _ _ y m

/-- **Multiplication by a global section of an invertible module is bijective on the stalk at
every point of its nonvanishing locus**, which is clause 2 of [Stacks, Tag 01CY]. The comparison
isomorphism contributes a bijection on every stalk. -/
public theorem bijective_mapFun_sectionMulHom {X : Scheme.{u}} (ω L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) {y : X}
    (hy : y ∈ nonvanishingLocus L s) :
    Function.Bijective (Stacks.ModuleStalk.mapFun (sectionMulHom ω L s) y) := by
  have hbij := Stacks.AmpleCharacterization.bijective_mapFun_mulRight_unitHom ω L s
    (W := Stacks.NonvanishingOpen.nonvanishingOpen X L s)
    ((Stacks.NonvanishingOpen.mem_nonvanishingOpen X L s y).mpr hy)
    fun z hz => (Stacks.NonvanishingOpen.mem_nonvanishingOpen X L s z).mp hz
  rw [funext (mapFun_sectionMulHom_apply ω L s y)]
  exact (Stacks.AmpleCharacterization.bijective_mapFun_of_iso _ y).comp hbij

/-- **Multiplication by a global section `s` lands in `𝔪_x (ω ⊗ ℒ)_x` at a point where `s`
vanishes.** A germ of `ω` at `x` is the germ of a section over some open, multiplication by `s`
sends it to the germ of the product of that section with the restriction of `s`, and the germ of
such a product lies in `𝔪_x` times the stalk as soon as the germ of `s` does — which is exactly
what lying outside the nonvanishing locus of [Stacks, Tag 01CY] says. -/
public theorem mem_maximalSmul_mapFun_sectionMulHom {X : Scheme.{u}} (ω L : X.Modules)
    (s : Γ(L, ⊤)) {x : X} (hx : x ∉ nonvanishingLocus L s)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ω.presheaf x) :
    Stacks.ModuleStalk.mapFun (sectionMulHom ω L s) x m ∈
      Stacks.ModuleStalk.maximalSmul ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
          (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj (ω)).obj (L))) x := by
  obtain ⟨W, hxW, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq ω.presheaf m
  have hmem : (L.presheaf.Γgerm x).hom s ∈ Stacks.ModuleStalk.maximalSmul L x := by
    rw [Stacks.Ample.mem_nonvanishingLocus_iff] at hx
    exact not_not.mp hx
  have hvan := Stacks.AmpleCharacterization.germ_tensorSection_mem_maximalSmul ω L hmem W hxW t
    (Stacks.SectionExtension.resTop W s)
    (Stacks.SectionTensorFormula.germ_resTop L s W x hxW)
  rw [mapFun_sectionMulHom_apply, Stacks.ModuleStalk.mapFun_germ,
    Stacks.AmpleCharacterization.mulSec_unitHom]
  exact Stacks.SectionProduct.mapFun_mem_maximalSmul _ x hvan

/-- `AlgebraicGeometry.mem_maximalSmul_mapFun_sectionMulHom` as a bound on the range of the map
of stalk modules, which is the form [Stacks, Tag 0B5F] applies Nakayama's lemma to. -/
public theorem range_modulesStalkFunctor_map_sectionMulHom_le {X : Scheme.{u}} (ω L : X.Modules)
    (s : Γ(L, ⊤)) {x : X} (hx : x ∉ nonvanishingLocus L s) :
    LinearMap.range ((modulesStalkFunctor X x).map (sectionMulHom ω L s)).hom ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x)
          ((modulesStalkFunctor X x).obj
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
                (forget₂ CommRingCat RingCat)
                (X.ringCatSheaf.property)⟩).obj (ω)).obj (L))))) := by
  intro z hz
  obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hz
  exact hm ▸ mem_maximalSmul_mapFun_sectionMulHom ω L s hx m

/-- **A section vanishing at a closed point `x` and at no generic point other than `x` vanishes
at no generic point of a one-dimensional irreducible component at all.** This is the step that
turns the conclusion of [Stacks, Tag 0B58] into the hypothesis that
`AlgebraicGeometry.topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne` asks
for. -/
public theorem mem_nonvanishingLocus_of_mem_genericPointsOne {X : Scheme.{u}} (L : X.Modules)
    (s : Γ(L, ⊤)) {x : X} (hx : IsClosed ({x} : Set X))
    (hgen : ∀ Z ∈ irreducibleComponents X, ∀ y, IsGenericPoint y Z → y ≠ x →
      y ∈ nonvanishingLocus L s)
    {y : X} (hy : y ∈ genericPointsOne X) : y ∈ nonvanishingLocus L s :=
  hgen (closure ({y} : Set X)) (mem_genericPointsOne_iff.mp hy).1 y isGenericPoint_closure
    fun h => notMem_genericPointsOne_of_isClosed_singleton hx (h ▸ hy)

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-- **The extension of `ω` produced by a section of `ℒ` vanishing at a closed point.** In
Situation [Stacks, Tag 0B5D], let `ω` and `ω ⊗ ℒ` be coherent with `ℒ` invertible, let `ω` have
no nonzero coherent submodule supported in dimension zero, and let `s` be a global section of
`ℒ` vanishing at the closed point `x` and at no generic point of an irreducible component other
than `x`. Then multiplication by `s` fits into a short exact sequence

`0 ⟶ ω ⟶ ω ⊗ ℒ ⟶ 𝒬 ⟶ 0`

whose quotient `𝒬` is coherent, hence quasi-coherent, with support of dimension at most zero,
and whose first map has image inside `𝔪_x (ω ⊗ ℒ)_x`.

Exactness at `ω ⊗ ℒ` and surjectivity onto `𝒬 = coker` are formal. Injectivity is the only
place where the hypothesis on `ω` is used: the kernel is coherent by [Stacks, Tag 01BY] and is
unsupported at every generic point of a one-dimensional component, because multiplication by `s`
is bijective on the stalk wherever `s` does not vanish; so its support has dimension at most
zero and the kernel is zero. -/
public theorem exists_shortExact_sectionMul (ω L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] [ω.IsCoherent]
    [((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
        (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj (ω)).obj (L))).IsCoherent]
    (hnosub : ∀ (M : S.X.Modules) (u : M ⟶ ω), Mono u → M.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp M) ≤ 0 → IsZero M)
    (x : S.X) (hx : IsClosed ({x} : Set S.X)) (s : Γ(L, ⊤))
    (hsx : x ∉ nonvanishingLocus L s)
    (hgen : ∀ Z ∈ irreducibleComponents S.X, ∀ y, IsGenericPoint y Z → y ≠ x →
      y ∈ nonvanishingLocus L s) :
    ∃ (Q : S.X.Modules) (α : ω ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
        (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj (ω)).obj (L)))
      (β : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
          (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj (ω)).obj (L)) ⟶ Q)
      (hc : α ≫ β = 0),
      (ShortComplex.mk α β hc).ShortExact ∧ Q.IsCoherent ∧ Q.IsQuasicoherent ∧
      topologicalKrullDim (SheafOfModules.supp Q) ≤ 0 ∧
      LinearMap.range ((modulesStalkFunctor S.X x).map α).hom ≤
        IsLocalRing.maximalIdeal (S.X.presheaf.stalk x) •
          (⊤ : Submodule (S.X.presheaf.stalk x)
            ((modulesStalkFunctor S.X x).obj
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
                  (forget₂ CommRingCat RingCat)
                  (S.X.ringCatSheaf.property)⟩).obj (ω)).obj (L))))) := by
  have hdim1 : topologicalKrullDim (S.X : Type u) ≤ 1 := le_of_eq S.dimension_one
  have hgenAll : ∀ y ∈ genericPointsOne S.X, y ∈ nonvanishingLocus L s :=
    fun y hy => mem_nonvanishingLocus_of_mem_genericPointsOne L s hx hgen hy
  have hbij : ∀ y ∈ nonvanishingLocus L s,
      Function.Bijective (Stacks.ModuleStalk.mapFun (sectionMulHom ω L s) y) :=
    fun y hy => bijective_mapFun_sectionMulHom ω L s hy
  have hkercoh : (kernel (sectionMulHom ω L s)).IsCoherent :=
    isCoherent_kernel_of_isCoherent ‹ω.IsCoherent› ‹_› (sectionMulHom ω L s)
  have hkerdim : topologicalKrullDim
      (SheafOfModules.supp (kernel (sectionMulHom ω L s))) ≤ 0 :=
    topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hdim1 _ hkercoh
      fun y hy => notMem_supp_kernel_of_injective_mapFun _ y (hbij y (hgenAll y hy)).1
  have hmonoι : Mono (kernel.ι (sectionMulHom ω L s)) :=
    ⟨fun _ _ h => Fork.IsLimit.hom_ext (kernelIsKernel (sectionMulHom ω L s)) h⟩
  have hkerzero : IsZero (kernel (sectionMulHom ω L s)) :=
    hnosub _ (kernel.ι (sectionMulHom ω L s)) hmonoι hkercoh hkerdim
  have hmono : Mono (sectionMulHom ω L s) :=
    (Preadditive.mono_iff_isZero_kernel _).mpr hkerzero
  have hepi : Epi (cokernel.π (sectionMulHom ω L s)) :=
    ⟨fun _ _ h => Cofork.IsColimit.hom_ext (cokernelIsCokernel (sectionMulHom ω L s)) h⟩
  have hcokcoh : (cokernel (sectionMulHom ω L s)).IsCoherent :=
    isCoherent_cokernel_of_isCoherent ‹ω.IsCoherent› ‹_› (sectionMulHom ω L s)
  have hcokqc : (cokernel (sectionMulHom ω L s)).IsQuasicoherent :=
    (@Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      _ _ hcokcoh).1
  refine ⟨cokernel (sectionMulHom ω L s), sectionMulHom ω L s,
    cokernel.π (sectionMulHom ω L s), cokernel.condition (sectionMulHom ω L s),
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) hmono hepi, hcokcoh, hcokqc,
    ?_, range_modulesStalkFunctor_map_sectionMulHom_le ω L s hsx⟩
  exact topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hdim1 _ hcokcoh
    fun y hy => notMem_supp_cokernel_of_surjective_mapFun _ y (hbij y (hgenAll y hy)).2

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
