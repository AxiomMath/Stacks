module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomMapLeftConjugate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseShortExact
public import StacksFrontier.AlgebraicGeometry.Duality.Sweep.SecondOrderThickening
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionPreservesInjectives
public import
  StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimits
public import
  StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact

/-!
# The normal sheaf of an ideal sheaf as a first sheaf Ext

Let `Y` be a ringed space, let `ℐ ⊆ 𝒪_Y` be a sheaf of ideals and put `𝒪_X = 𝒪_Y/ℐ`. The
*normal sheaf* `𝒩 = 𝓗om_{𝒪_Y}(ℐ/ℐ², 𝒪_X)` carries a canonical map

`c : 𝒩 ⟶ 𝓔xt¹_{𝒪_Y}(𝒪_X, 𝒪_X)`,

obtained by pushing the second-order thickening sequence `0 ⟶ ℐ/ℐ² ⟶ 𝒪_Y/ℐ² ⟶ 𝒪_X ⟶ 0` of
[Stacks, Tag 0BQX] out along a local homomorphism, and this map is an isomorphism. The map `c`
is built here as the degree-one connecting map of the short exact sequence of internal-Hom
complexes attached to `0 ⟶ ℐ ⟶ 𝒪_Y ⟶ 𝒪_X ⟶ 0`, which is the same map: the connecting
homomorphism of the Ext long exact sequence in the first variable sends a homomorphism
`ℐ ⟶ 𝒪_X` to the class of the pushout of `0 ⟶ ℐ ⟶ 𝒪_Y ⟶ 𝒪_X ⟶ 0` along it, and that pushout
is the pushout of the second-order thickening sequence along the induced map `ℐ/ℐ² ⟶ 𝒪_X`.

## Main definitions

* `Stacks.RingedSpace.sheafExt`: the sheaf Ext `𝓔xt^i_{𝒪_Y}(F, G)`, the `i`-th right derived
  functor of the internal Hom `𝓗om_{𝒪_Y}(F, -)` of [Stacks, Tag 03EN], evaluated at `G`.
* `Stacks.Duality.quotientByIdealSheaf`: the quotient `𝒪_X = 𝒪_Y/ℐ`.
* `Stacks.Duality.idealSquareInclusion`: the canonical inclusion `ℐ² ⟶ ℐ`, and
  `Stacks.Duality.idealQuotientBySquare`: its cokernel `ℐ/ℐ²`, the first term of the
  second-order thickening sequence of [Stacks, Tag 0BQX].
* `Stacks.Duality.normalSheafOfIdealSheaf`: the normal sheaf `𝒩 = 𝓗om_{𝒪_Y}(ℐ/ℐ², 𝒪_X)`.
* `Stacks.Duality.sheafHomComplexSequence`: the short complex of complexes obtained by applying
  the internal-Hom functors of `0 ⟶ ℐ ⟶ 𝒪_Y ⟶ 𝒪_X ⟶ 0` degreewise to a complex.
* `Stacks.Duality.normalSheafToSheafExtOne`: the canonical map `c`.

## Main results

* `Stacks.RingedSpace.isZero_sheafExt_unit_succ`: `𝓔xt^{n+1}_{𝒪_Y}(𝒪_Y, G) = 0`.
* `Stacks.Duality.shortExact_internalHomMapLeft_of_injective`: [Stacks, Tag 01DR] for sheaves of
  modules against the sequence of a sheaf of ideals — `𝓗om_{𝒪_Y}(-, K)` carries
  `0 ⟶ ℐ ⟶ 𝒪_Y ⟶ 𝒪_X ⟶ 0` to a short exact sequence when `K` is injective — and
  `Stacks.Duality.sheafHomComplexSequence_shortExact`, the same degreewise on a complex.
* `Stacks.Duality.internalHomMapLeft_ι_app_quotient_eq_zero`: the ideal sheaf annihilates its
  quotient, in the form of the vanishing of the degree-zero `Ext` map — restricting an
  `𝒪_Y`-linear map `𝒪_Y ⟶ 𝒪_X` to `ℐ` gives zero — together with its section-level form
  `Stacks.Duality.smul_quotientByIdealSheaf_eq_zero`.
* `Stacks.Duality.isIso_internalHomMapLeft_cokernelπ_idealSquareInclusion`: every `𝒪_Y`-linear
  map `ℐ ⟶ 𝒪_X` factors uniquely through `ℐ/ℐ²`, together with its ingredient
  `Stacks.Duality.internalHomMapLeft_idealSquareInclusion_app_quotient_eq_zero`, that such a
  map kills `ℐ²`.
* `Stacks.Duality.isIso_normalSheafToSheafExtOne`: the canonical map `c` is an isomorphism.

## Implementation notes

**Sheaf Ext.** The library had no sheaf Ext when this file was written, only the internal Hom
functor `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor` of [Stacks, Tag 03EN] and
the global Ext groups of the derived category. `Stacks.RingedSpace.sheafExt` is therefore
introduced here, as the right derived functor of that internal Hom in its second variable,
which is the standard definition; it is stated for a ringed space because
`internalHomSecondFunctor` and the enough-injectives instance are what it consumes, and it is
not specific to the duality chapter — it is placed in `Stacks.RingedSpace` so that it can be
moved without renaming.

**Why `c` is the connecting map.** The source constructs `c` by pushing the sequence of
[Stacks, Tag 0BQX] out along a local section of `𝒩`. Writing `c` as the connecting map of the
sequence of internal-Hom complexes gives a definition with a closed term rather than a choice
of a representing extension on each open, and it is the same map, for the reason recorded in
the module header. The injective resolution used is `injectiveResolution`, the resolution that
`CategoryTheory.Functor.rightDerived` itself uses, so no comparison of resolutions enters.

**The four inputs of the proof.** All four are proved here; nothing is assumed.

* That precomposition along `ℐ ↠ ℐ/ℐ²` identifies `𝓗om(ℐ/ℐ², 𝒪_X)` with `𝓗om(ℐ, 𝒪_X)` is
  `Stacks.Duality.isIso_internalHomMapLeft_cokernelπ_idealSquareInclusion`. The monomorphism
  is [Stacks, Tag 0GMY] part (1) at the epimorphism `ℐ ↠ ℐ/ℐ²`; the epimorphism is exactness
  at the middle of `𝓗om(ℐ/ℐ², 𝒪_X) ⟶ 𝓗om(ℐ, 𝒪_X) ⟶ 𝓗om(ℐ², 𝒪_X)` together with the
  vanishing of its second map, `internalHomMapLeft_idealSquareInclusion_app_quotient_eq_zero`,
  that is, that every `𝒪_Y`-linear map `ℐ ⟶ 𝒪_X` kills `ℐ²`. Since
  `Stacks.Duality.idealSquare` is an `sInf` of ideal subsheaves, its sections are not
  generated by products of two sections of `ℐ`, and that vanishing is instead obtained by
  exhibiting an ideal subsheaf containing all such products and contained in the common
  kernel: `killedByLocalHoms`, the sections of `ℐ` killed by every `𝒪_Y`-linear map
  `ℐ|_W ⟶ 𝒪_X|_W` at every level of the slice site over every open `W`. Quantifying over all
  `W` at once, with only a morphism `W' ⟶ X` tying the slice to the open at hand, is what
  makes that membership condition both stable under restriction and local — local because
  `𝒪_X` is a sheaf, hence separated (`CategoryTheory.Presheaf.IsSheaf.isSeparated`), which is
  the only place the sheaf condition of the sheafified cokernel `𝒪_Y/ℐ` is used.
* That restricting an `𝒪_Y`-linear map `𝒪_Y ⟶ 𝒪_X` to `ℐ` gives zero is
  `Stacks.Duality.internalHomMapLeft_ι_app_quotient_eq_zero`. Precomposing with the
  epimorphism `𝓗om(𝒪_Y, 𝒪_Y) ⟶ 𝓗om(𝒪_Y, 𝒪_X)` — an epimorphism because
  `Stacks.SheafOfModules.InternalHom.unitInternalHomNatIso` identifies `𝓗om(𝒪_Y, -)` with the
  identity, which carries the epimorphism `𝒪_Y ↠ 𝒪_X` to one — and using naturality in the
  target reduces it to `internalHomMapLeft_ι_comp_map_pi_eq_zero`: an `𝒪_Y`-linear
  endomorphism of `𝒪_Y` is multiplication by a section, hence carries `ℐ` into `ℐ`, hence
  dies after the projection to `𝒪_X`. The statement the connecting map needs is the vanishing
  of the degree-zero cohomology map at the injective resolution, which
  `homologyMap_eq_zero_of_app_eq_zero` deduces from it; the naturality of
  `CategoryTheory.Functor.toRightDerivedZero` in the *functor* variable, which Mathlib does
  not have, is not needed, because the degree-zero comparison
  `CategoryTheory.InjectiveResolution.toRightDerivedZero'` is an isomorphism for a left exact
  functor and a plain commuting square with it suffices. The section-level form of the
  annihilation, `smul_quotientByIdealSheaf_eq_zero`, is read off by evaluating the vanishing
  at multiplication by a section, `smulSection`.
* The short exactness of `sheafHomComplexSequence` at the injective resolution, which is
  [Stacks, Tag 01DR] for sheaves of modules, is
  `Stacks.Duality.sheafHomComplexSequence_shortExact`. Exactness at the middle term and the
  left-hand monomorphism come from the left exactness of internal Hom in the first variable,
  [Stacks, Tag 0GMY] part (1)
  (`Stacks.SheafOfModules.InternalHom.sheafInternalHomMapLeft_exact_of_exact_epi` and
  `..._mono_of_epi`); the right-hand epimorphism is `epi_internalHomMapLeft_ι`, which spends
  the injectivity of the target by restricting it to an open ([Stacks, Tag 03F3] part (1),
  `Stacks.Cohomology.Localization.injective_over`, which rests in turn on the exactness of
  extension by zero, [Stacks, Tag 03DJ]) and extending along `ℐ|_U ↪ 𝒪_Y|_U` there.
* The vanishing of `𝓔xt¹_{𝒪_Y}(𝒪_Y, 𝒪_X)` is
  `Stacks.RingedSpace.isZero_sheafExt_unit_succ`, proved from the identification
  `Stacks.SheafOfModules.InternalHom.unitInternalHomNatIso` of the internal Hom out of the unit
  with the identity functor together with
  `CategoryTheory.InjectiveResolution.cocomplex_exactAt_succ`.

**Spelling of the structure sheaf.** The ring sheaf is written
`Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf`, the reducible spelling that
`internalHomSecondFunctor` consumes, and not the semireducible
`structureSheafRing Y`. The two are equal by `rfl`, but only the first is
seen through by instance search; `Stacks.Duality.idealSquare` of [Stacks, Tag 0BQX] is stated
in the second spelling and is applied here across that identification.

## References

* [Stacks Project, Tag 0BQW](https://stacks.math.columbia.edu/tag/0BQW)
* [Stacks Project, Tag 0BQX](https://stacks.math.columbia.edu/tag/0BQX)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 01DR](https://stacks.math.columbia.edu/tag/01DR)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 06XV](https://stacks.math.columbia.edu/tag/06XV)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules.InternalHom

universe u

noncomputable section

namespace Stacks.RingedSpace

/-- The category of `𝒪_Y`-modules on a ringed space has enough injectives: it is a
Grothendieck abelian category. -/
public instance enoughInjectivesModules (Y : AlgebraicGeometry.RingedSpace.{u, u}) :
    EnoughInjectives (SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) := inferInstance
  exact IsGrothendieckAbelian.enoughInjectives

/-- Internal Hom out of a fixed sheaf of modules preserves finite limits: by [Stacks, Tag
03EN] it preserves all limits. -/
public instance internalHomSecondFunctor_preservesFiniteLimits
    (Y : AlgebraicGeometry.RingedSpace.{u, u})
    (F : SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    PreservesFiniteLimits (internalHomSecondFunctor.{u, u, u, u}
      (Opens.grothendieckTopology Y.carrier) Y.sheaf F) := by
  have := internalHomSecondFunctor_preservesLimits
    (Opens.grothendieckTopology Y.carrier) Y.sheaf F
  exact PreservesLimits.preservesFiniteLimits _

/-- Internal Hom out of a fixed sheaf of modules is additive: it adds on sections. -/
public instance internalHomSecondFunctor_additive
    (Y : AlgebraicGeometry.RingedSpace.{u, u})
    (F : SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    (internalHomSecondFunctor.{u, u, u, u}
      (Opens.grothendieckTopology Y.carrier) Y.sheaf F).Additive where
  map_add := by intros; ext U x; rfl

/-- **The sheaf Ext** `𝓔xt^i_{𝒪_Y}(F, G)` on a ringed space: the `i`-th right derived functor
of the internal Hom `𝓗om_{𝒪_Y}(F, -)` of [Stacks, Tag 03EN], evaluated at `G`. -/
public def sheafExt (Y : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) (i : ℕ) :
    SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.sheaf) :=
  ((internalHomSecondFunctor.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) Y.sheaf F).rightDerived i).obj G

/-- **The higher sheaf Ext out of the structure sheaf vanishes**: `𝓔xt^{n+1}_{𝒪_Y}(𝒪_Y, G) = 0`.
Internal Hom out of `𝒪_Y` is the identity functor
(`Stacks.SheafOfModules.InternalHom.unitInternalHomNatIso`), so the complex computing the right
derived functors at an injective resolution of `G` is that resolution itself, and an injective
resolution is exact in every positive degree. -/
public lemma isZero_sheafExt_unit_succ (Y : AlgebraicGeometry.RingedSpace.{u, u})
    (G : SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) (n : ℕ) :
    IsZero (sheafExt Y (SheafOfModules.unit
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) G (n + 1)) := by
  refine IsZero.of_iso ?_ ((injectiveResolution G).isoRightDerivedObj _ (n + 1))
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ)
    (n + 1)).mapIso ((NatIso.mapHomologicalComplex
      (unitInternalHomNatIso (Opens.grothendieckTopology Y.carrier) Y.sheaf)
        (ComplexShape.up ℕ)).app (injectiveResolution G).cocomplex))
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ)
    (n + 1)).mapIso ((Functor.mapHomologicalComplexIdIso
      (SheafOfModules.{u}
        (SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (ComplexShape.up ℕ)).app (injectiveResolution G).cocomplex))
  have h := (injectiveResolution G).cocomplex_exactAt_succ n
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h
  exact h

end Stacks.RingedSpace

namespace Stacks.Duality

variable (Y : AlgebraicGeometry.RingedSpace.{u, u})
    (I : (SheafOfModules.unit
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)).Submodule)

/-- The quotient `𝒪_X = 𝒪_Y/ℐ` of the structure sheaf by a sheaf of ideals, as an
`𝒪_Y`-module. -/
public abbrev quotientByIdealSheaf :
    SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.sheaf) :=
  cokernel I.ι

/-- The canonical inclusion `ℐ² ⟶ ℐ` of the square of a sheaf of ideals, the first map of the
second-order thickening sequence of [Stacks, Tag 0BQX]. -/
public def idealSquareInclusion :
    (idealSquare Y I).toSheafOfModules ⟶ I.toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE (SheafOfModules.Submodule.le_iff.mp
    (sInf_le fun U a _b _ha hb => (I.toSubmodule.obj U).smul_mem a hb))⟩

/-- The inclusion `ℐ² ⟶ ℐ` is compatible with the inclusions into `𝒪_Y`. -/
public lemma idealSquareInclusion_comp_ι :
    idealSquareInclusion Y I ≫ I.ι = (idealSquare Y I).ι := rfl

/-- The quotient `ℐ/ℐ²` of a sheaf of ideals by its square: the cokernel of the canonical
inclusion `ℐ² ⟶ ℐ`, hence the first term of the second-order thickening sequence of
[Stacks, Tag 0BQX]. -/
public abbrev idealQuotientBySquare :
    SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.sheaf) :=
  cokernel (idealSquareInclusion Y I)

/-- **The normal sheaf** `𝒩 = 𝓗om_{𝒪_Y}(ℐ/ℐ², 𝒪_Y/ℐ)` of a sheaf of ideals on a ringed
space. -/
public abbrev normalSheafOfIdealSheaf :
    SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.sheaf) :=
  (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
    (idealQuotientBySquare Y I)).obj (quotientByIdealSheaf Y I)

private lemma internalHomMapLeftNatTrans_comp
    {A B C : SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)}
    (f : A ⟶ B) (g : B ⟶ C) :
    internalHomMapLeftNatTrans Y.sheaf g ≫ internalHomMapLeftNatTrans Y.sheaf f =
      internalHomMapLeftNatTrans Y.sheaf (f ≫ g) := by
  ext G
  rfl

private lemma internalHomMapLeftNatTrans_zero
    (A B : SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    internalHomMapLeftNatTrans Y.sheaf (0 : A ⟶ B) = 0 := by
  ext G V x
  have h : (restrFun Y.sheaf.obj V.unop).map (0 : A.val ⟶ B.val) = 0 := by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  change (restrFun Y.sheaf.obj V.unop).map (0 : A.val ⟶ B.val) ≫ x = 0
  rw [h]
  exact zero_comp

/-- The short complex of complexes obtained by applying the internal-Hom functors of
`0 ⟶ ℐ ⟶ 𝒪_Y ⟶ 𝒪_X ⟶ 0` degreewise to a complex `K`: it is
`𝓗om(𝒪_X, K) ⟶ 𝓗om(𝒪_Y, K) ⟶ 𝓗om(ℐ, K)`, the two maps being precomposition with
`𝒪_Y ↠ 𝒪_X` and with `ℐ ↪ 𝒪_Y`. -/
public def sheafHomComplexSequence
    (K : CochainComplex (SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℕ) :
    ShortComplex (CochainComplex (SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex
      (internalHomMapLeftNatTrans Y.sheaf (cokernel.π I.ι)) (ComplexShape.up ℕ)).app K)
    ((NatTrans.mapHomologicalComplex
      (internalHomMapLeftNatTrans Y.sheaf I.ι) (ComplexShape.up ℕ)).app K)
    (by
      apply HomologicalComplex.Hom.ext
      funext n
      change (internalHomMapLeftNatTrans Y.sheaf (cokernel.π I.ι)).app (K.X n) ≫
          (internalHomMapLeftNatTrans Y.sheaf I.ι).app (K.X n) = 0
      rw [← NatTrans.comp_app, internalHomMapLeftNatTrans_comp, cokernel.condition,
        internalHomMapLeftNatTrans_zero]
      rfl)

/-- Left exactness of internal Hom in the first variable: precomposition along `cokernel.π f` and
`f` is exact in the middle, and the former is a monomorphism. -/
private lemma exact_and_mono_internalHomMapLeft_cokernelπ
    {A B : SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.sheaf)} (f : A ⟶ B)
    (K : SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    (∃ h : (internalHomMapLeftNatTrans Y.sheaf (cokernel.π f)).app K ≫
        (internalHomMapLeftNatTrans Y.sheaf f).app K = 0,
      (ShortComplex.mk ((internalHomMapLeftNatTrans Y.sheaf (cokernel.π f)).app K)
        ((internalHomMapLeftNatTrans Y.sheaf f).app K) h).Exact) ∧
    Mono ((internalHomMapLeftNatTrans Y.sheaf (cokernel.π f)).app K) :=
  ⟨sheafInternalHomMapLeft_exact_of_exact_epi (Opens.grothendieckTopology Y.carrier) Y.sheaf
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) K (ShortComplex.exact_cokernel f),
   sheafInternalHomMapLeft_mono_of_epi (Opens.grothendieckTopology Y.carrier) Y.sheaf _⟩

/-- Precomposition along a sheaf of ideals `ℐ ↪ 𝒪_Y` is surjective on sections over every open
when the target is injective: a section over `U` is a morphism `ℐ|_U ⟶ K|_U` on the slice site,
`ℐ|_U ⟶ 𝒪_Y|_U` is a monomorphism there, and `K|_U` is injective by [Stacks, Tag 03F3]. -/
private lemma surjective_internalHomMapLeft_ι_app
    (K : SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Injective K]
    (U : Opens Y.carrier) :
    Function.Surjective
      (((internalHomMapLeftNatTrans Y.sheaf I.ι).app K).val.app (Opposite.op U)) := by
  intro x
  have hinj : Injective (K.over U) :=
    Stacks.Cohomology.Localization.injective_over
      (Opens.grothendieckTopology Y.carrier) _ U K
  have hmono : Mono (I.ι.over U) := by
    change Mono ((SheafOfModules.overFunctor
      (SheafOfModules.Tensor.ringSheaf Y.sheaf) U).map I.ι)
    infer_instance
  let R' := (SheafOfModules.Tensor.ringSheaf Y.sheaf).over U
  let IU : SheafOfModules.{u} R' := I.toSheafOfModules.over U
  let OU : SheafOfModules.{u} R' :=
    (SheafOfModules.unit
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)).over U
  let KU : SheafOfModules.{u} R' := K.over U
  let fU : IU ⟶ OU := I.ι.over U
  let hx : IU ⟶ KU := (SheafOfModules.fullyFaithfulForget R').preimage x
  let y : OU ⟶ KU := Injective.factorThru hx fU
  refine ⟨(SheafOfModules.forget R').map y, ?_⟩
  change (SheafOfModules.forget R').map (fU ≫ y) = x
  rw [Injective.comp_factorThru]
  exact (SheafOfModules.fullyFaithfulForget R').map_preimage (X := IU) (Y := KU) x

/-- Precomposition along a sheaf of ideals `ℐ ↪ 𝒪_Y` is an epimorphism of internal Hom sheaves
when the target is injective. -/
private lemma epi_internalHomMapLeft_ι
    (K : SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Injective K] :
    Epi ((internalHomMapLeftNatTrans Y.sheaf I.ι).app K) := by
  apply SheafOfModules.epi_of_sectionwise_surjective
  intro T
  exact surjective_internalHomMapLeft_ι_app Y I K T.unop

/-- **[Stacks, Tag 01DR] for sheaves of modules, on the ideal sequence.** For an injective sheaf
of `𝒪_Y`-modules `K` the internal Hom `𝓗om_{𝒪_Y}(-, K)` carries `0 ⟶ ℐ ⟶ 𝒪_Y ⟶ 𝒪_X ⟶ 0` to a
short exact sequence

`0 ⟶ 𝓗om(𝒪_X, K) ⟶ 𝓗om(𝒪_Y, K) ⟶ 𝓗om(ℐ, K) ⟶ 0`.

Exactness at the middle term and the left-hand monomorphism are the left exactness of internal
Hom in the first variable, [Stacks, Tag 0GMY] part (1); the right-hand epimorphism is where the
injectivity of `K` is spent, through `epi_internalHomMapLeft_ι`. -/
@[stacks 01DR "for sheaves of modules on a ringed space, against the sequence of a sheaf of \
ideals; the library's `Stacks.Injectives.AbelianDual.dualFunctor_shortExact_of_injective` is the \
statement for the abelian-sheaf internal Hom against an injective abelian sheaf instead"]
public lemma shortExact_internalHomMapLeft_of_injective
    (K : SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Injective K] :
    (ShortComplex.mk
      ((internalHomMapLeftNatTrans Y.sheaf (cokernel.π I.ι)).app K)
      ((internalHomMapLeftNatTrans Y.sheaf I.ι).app K)
      (by
        rw [← NatTrans.comp_app, internalHomMapLeftNatTrans_comp, cokernel.condition,
          internalHomMapLeftNatTrans_zero]
        rfl)).ShortExact := by
  obtain ⟨⟨_, hex⟩, hmono⟩ := exact_and_mono_internalHomMapLeft_cokernelπ Y I.ι K
  exact ShortComplex.ShortExact.mk' hex hmono (epi_internalHomMapLeft_ι Y I K)

/-- **The internal-Hom sequence of a degreewise injective complex is short exact.** This is
`shortExact_internalHomMapLeft_of_injective` in every degree. -/
public lemma sheafHomComplexSequence_shortExact
    (K : CochainComplex (SheafOfModules.{u}
      (SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℕ)
    [∀ n, Injective (K.X n)] :
    (sheafHomComplexSequence Y I K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact shortExact_internalHomMapLeft_of_injective Y I (K.X n)

/-- **The canonical map `c` of [Stacks, Tag 0BQW].** The normal sheaf
`𝒩 = 𝓗om_{𝒪_Y}(ℐ/ℐ², 𝒪_X)` maps canonically to `𝓔xt¹_{𝒪_Y}(𝒪_X, 𝒪_X)`: precompose with
`ℐ ↠ ℐ/ℐ²` to land in `𝓗om_{𝒪_Y}(ℐ, 𝒪_X)`, identify that with the degree-zero cohomology of
`𝓗om_{𝒪_Y}(ℐ, J)` for the injective resolution `J` of `𝒪_X` that the derived functor uses, and
take the degree-one connecting map of `sheafHomComplexSequence`. On a local section of `𝒩` this
is the class of the pushout of the second-order thickening sequence of [Stacks, Tag 0BQX] along
it, which is how the source constructs `c`. -/
@[stacks 0BQW "the canonical map `c` itself; \
`isIso_normalSheafToSheafExtOne` is the assertion that it is an isomorphism"]
public def normalSheafToSheafExtOne :
    normalSheafOfIdealSheaf Y I ⟶
      Stacks.RingedSpace.sheafExt Y (quotientByIdealSheaf Y I) (quotientByIdealSheaf Y I) 1 :=
  (internalHomMapLeftNatTrans Y.sheaf
      (cokernel.π (idealSquareInclusion Y I))).app (quotientByIdealSheaf Y I) ≫
    (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
      I.toSheafOfModules).toRightDerivedZero.app (quotientByIdealSheaf Y I) ≫
    ((injectiveResolution (quotientByIdealSheaf Y I)).isoRightDerivedObj
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        I.toSheafOfModules) 0).hom ≫
    (sheafHomComplexSequence_shortExact Y I
      (injectiveResolution (quotientByIdealSheaf Y I)).cocomplex).δ 0 1 rfl ≫
    ((injectiveResolution (quotientByIdealSheaf Y I)).isoRightDerivedObj
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        (quotientByIdealSheaf Y I)) 1).inv

/-- A functor isomorphic to the identity sends epimorphisms to epimorphisms. -/
private lemma epi_map_of_natIso_id {C : Type*} [Category* C] {F : C ⥤ C} (e : F ≅ 𝟭 C)
    {X Y : C} (f : X ⟶ Y) [Epi f] : Epi (F.map f) := by
  have h2 := e.hom.naturality f
  simp only [Functor.id_map] at h2
  have h3 : F.map f = e.hom.app X ≫ f ≫ e.inv.app Y := by
    rw [← Category.assoc, ← h2, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [h3]
  infer_instance

/-- An `A`-linear endomorphism of a commutative ring `A` maps an ideal into itself: it is
multiplication by the image of `1`. The commutativity is supplied as a hypothesis so that the
lemma applies to the carrier of an object of `RingCat`, which carries only a `Ring` instance. -/
private lemma mem_of_linearMap_apply {A : Type*} [Ring A] (hcomm : ∀ a c : A, a * c = c * a)
    (p : Submodule A A) (f : A →ₗ[A] A) {r : A} (hr : r ∈ p) : f r ∈ p := by
  have h1 : f r = (f 1) • r := by
    conv_lhs => rw [← mul_one r]
    rw [← smul_eq_mul, map_smul, smul_eq_mul, smul_eq_mul, hcomm]
  rw [h1]
  exact p.smul_mem _ hr

/-- Restriction along an identity is the identity, on sections of a presheaf of modules. -/
private lemma presheafOfModules_map_id_apply {C₀ : Type*} [Category* C₀]
    {R₀ : C₀ᵒᵖ ⥤ RingCat} (M : PresheafOfModules R₀) (X : C₀ᵒᵖ) (m : M.obj X) :
    M.map (𝟙 X) m = m := by
  simp
  rfl

/-- The same, for the opposite of an identity. -/
private lemma presheafOfModules_map_op_id_apply {C₀ : Type*} [Category* C₀]
    {R₀ : C₀ᵒᵖ ⥤ RingCat} (M : PresheafOfModules R₀) (X : C₀)
    (m : M.obj (Opposite.op X)) : M.map (𝟙 X).op m = m :=
  presheafOfModules_map_id_apply M _ m

/-- A module morphism kills every multiple of a section that it kills. -/
private lemma smul_apply_eq_zero {A₀ : Type*} [Ring A₀] {M N : ModuleCat A₀} (f : M ⟶ N)
    (r : A₀) {u : M} (hu : f.hom u = 0) : f.hom (r • u) = 0 := by
  rw [map_smul, hu, smul_zero]

/-- A module morphism sends a multiple of a section to zero as soon as the corresponding
multiple of its image vanishes. -/
private lemma apply_smul_eq_zero_of_smul_eq_zero {A₀ : Type*} [Ring A₀] {M N : ModuleCat A₀}
    (f : M ⟶ N) (r : A₀) (u : M) (h : r • f.hom u = 0) : f.hom (r • u) = 0 := by
  rw [map_smul, h]

/-- If a natural transformation of additive functors, the source of which is left exact,
vanishes at an object, then so does the map it induces on the degree-zero cohomology of the
complexes of an injective resolution of that object. -/
private lemma homologyMap_eq_zero_of_app_eq_zero
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] [PreservesFiniteLimits F]
    (α : F ⟶ G) {X : C} (P : InjectiveResolution X) (h : α.app X = 0) :
    HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app P.cocomplex) 0 = 0 := by
  have hzero : F.map (P.ι.f 0) ≫ α.app (P.cocomplex.X 0) = 0 := by
    rw [α.naturality (P.ι.f 0),
      show α.app (((CochainComplex.single₀ C).obj X).X 0) = 0 from h, zero_comp]
  have hsq : P.toRightDerivedZero' F ≫ HomologicalComplex.cyclesMap
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app P.cocomplex) 0 = 0 := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0), Category.assoc,
      HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc, zero_comp]
    exact hzero
  have hcyc : HomologicalComplex.cyclesMap
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app P.cocomplex) 0 = 0 :=
    (cancel_epi (P.toRightDerivedZero' F)).mp (hsq.trans comp_zero.symm)
  rw [← cancel_mono (CochainComplex.isoHomologyπ₀
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex)).inv,
    CochainComplex.isoHomologyπ₀_inv_naturality, hcyc, comp_zero, zero_comp]

/-- The compatible family of restrictions of a section `z` of `M` over `V`, read on the
slice site over `V`. -/
private def smulSectionFamily
    (M : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
        Y.sheaf))
    (V : Opens Y.carrier) (z : M.val.obj (Opposite.op V)) :
    ((restrFun Y.sheaf.obj V).obj M.val).sections :=
  PresheafOfModules.sectionsMk (fun W => M.val.map W.unop.hom.op z) (by
    intro W₁ W₂ g
    have h1 : (((restrFun Y.sheaf.obj V).obj M.val).map g).hom
        ((M.val.map W₁.unop.hom.op).hom z)
        = (M.val.map ((Over.forget V).map g.unop).op).hom
          ((M.val.map W₁.unop.hom.op).hom z) := rfl
    rw [h1, ← PresheafOfModules.map_comp_apply]
    refine M.val.congr_map_apply ?_ z
    exact congrArg Quiver.Hom.op (Over.w g.unop))

/-- At the terminal object of the slice over `V`, the family is `z` itself. -/
private lemma smulSectionFamily_top
    (M : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
        Y.sheaf))
    (V : Opens Y.carrier) (z : M.val.obj (Opposite.op V)) :
    (smulSectionFamily Y M V z).eval (Opposite.op (Over.mk (𝟙 V))) = z := by
  change (M.val.map (𝟙 (Opposite.op V))).hom z = z
  exact presheafOfModules_map_id_apply _ _ z

/-- **Multiplication by a local section.** A section `z` of `M` over `V` defines the
`𝒪_Y|_V`-linear map `𝒪_Y|_V ⟶ M|_V` sending `t` to `t · z`, that is, a section of
`𝓗om_{𝒪_Y}(𝒪_Y, M)` over `V`. -/
private def smulSection
    (M : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
        Y.sheaf))
    (V : Opens Y.carrier) (z : M.val.obj (Opposite.op V)) :
    (restrFun Y.sheaf.obj V).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
          Y.sheaf)).val ⟶
      (restrFun Y.sheaf.obj V).obj M.val :=
  (PresheafOfModules.unitHomEquiv ((restrFun Y.sheaf.obj V).obj M.val)).symm
    (smulSectionFamily Y M V z)

/-- `smulSection` is multiplication by the section, on sections over the slice. -/
private lemma smulSection_app
    (M : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
        Y.sheaf))
    (V : Opens Y.carrier) (z : M.val.obj (Opposite.op V)) (W : (Over V)ᵒᵖ)
    (t : (ORestr Y.sheaf.obj V).obj W) :
    ((smulSection Y M V z).app W).hom t = t • (smulSectionFamily Y M V z).eval W := rfl

/-- `π` kills the sections of `ℐ`. -/
private lemma cokernelπ_apply_eq_zero (W : (Opens Y.carrier)ᵒᵖ)
    (s : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
        Y.sheaf)).val.obj W)
    (hs : s ∈ I.toSubmodule.obj W) :
    ((cokernel.π I.ι).val.app W).hom s = 0 :=
  congrArg (fun (φ : I.toSheafOfModules ⟶ quotientByIdealSheaf Y I) =>
    (φ.val.app W).hom ⟨s, hs⟩) (cokernel.condition I.ι)

/-- Step 1: internal Hom out of the unit sends the cokernel projection to an epimorphism. -/
private lemma epi_internalHomSecondFunctor_unit_map_pi :
    Epi ((internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
          Y.sheaf))).map
      (cokernel.π I.ι)) :=
  epi_map_of_natIso_id
    (unitInternalHomNatIso (Opens.grothendieckTopology Y.carrier) Y.sheaf) _

/-- Step 2a: an `𝒪_Y`-linear endomorphism of `𝒪_Y` carries `ℐ` into `ℐ`, so it dies after
projecting to `𝒪_X`. -/
private lemma internalHomMapLeft_ι_comp_map_pi_eq_zero :
    (internalHomMapLeftNatTrans Y.sheaf I.ι).app
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
            Y.sheaf)) ≫
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        I.toSheafOfModules).map (cokernel.π I.ι) = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((restrFun Y.sheaf.obj V.unop).map I.ι.val ≫ x) ≫
      (restrFun Y.sheaf.obj V.unop).map (cokernel.π I.ι).val = 0
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change ((cokernel.π I.ι).val.app (Opposite.op W.unop.left)).hom
      ((x.app W).hom ((I.ι.val.app (Opposite.op W.unop.left)).hom b)) = 0
  refine cokernelπ_apply_eq_zero Y I _ _ ?_
  exact mem_of_linearMap_apply
    (fun a c => mul_comm (G := Y.sheaf.obj.obj (Opposite.op W.unop.left)) a c)
    (I.toSubmodule.obj (Opposite.op W.unop.left)) (x.app W).hom b.2

/-- **The `Ext⁰` map vanishes**: restricting an `𝒪_Y`-linear map `𝒪_Y ⟶ 𝒪_X` to `ℐ` gives
zero, because `ℐ` annihilates `𝒪_X = 𝒪_Y/ℐ`. -/
public lemma internalHomMapLeft_ι_app_quotient_eq_zero :
    (internalHomMapLeftNatTrans Y.sheaf I.ι).app (quotientByIdealSheaf Y I) = 0 := by
  have := epi_internalHomSecondFunctor_unit_map_pi Y I
  refine (cancel_epi ((internalHomSecondFunctor.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) Y.sheaf
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
          Y.sheaf))).map
      (cokernel.π I.ι))).mp ?_
  rw [comp_zero, (internalHomMapLeftNatTrans Y.sheaf I.ι).naturality (cokernel.π I.ι)]
  exact internalHomMapLeft_ι_comp_map_pi_eq_zero Y I

/-- **The ideal sheaf annihilates its quotient.** -/
public lemma smul_quotientByIdealSheaf_eq_zero (V : Opens Y.carrier)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
      Y.sheaf).obj.obj (Opposite.op V))
    (hr : r ∈ I.toSubmodule.obj (Opposite.op V))
    (z : (quotientByIdealSheaf Y I).val.obj (Opposite.op V)) :
    r • z = 0 := by
  have h0 := internalHomMapLeft_ι_app_quotient_eq_zero Y I
  have h1 := congrArg (fun (φ : (internalHomSecondFunctor.{u, u, u, u}
      (Opens.grothendieckTopology Y.carrier) Y.sheaf
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
          Y.sheaf))).obj
        (quotientByIdealSheaf Y I) ⟶ (internalHomSecondFunctor.{u, u, u, u}
      (Opens.grothendieckTopology Y.carrier) Y.sheaf I.toSheafOfModules).obj
        (quotientByIdealSheaf Y I)) =>
    (φ.val.app (Opposite.op V)).hom
      (smulSection Y (quotientByIdealSheaf Y I) V z)) h0
  have h2 := congrArg (fun (ψ : (restrFun Y.sheaf.obj V).obj I.toSheafOfModules.val ⟶
      (restrFun Y.sheaf.obj V).obj (quotientByIdealSheaf Y I).val) =>
    (ψ.app (Opposite.op (Over.mk (𝟙 V)))).hom (⟨r, hr⟩ :
      ((restrFun Y.sheaf.obj V).obj I.toSheafOfModules.val).obj
        (Opposite.op (Over.mk (𝟙 V))))) h1
  have h3 : ((smulSection Y (quotientByIdealSheaf Y I) V z).app
      (Opposite.op (Over.mk (𝟙 V)))).hom r = 0 := h2
  rw [← smulSectionFamily_top Y (quotientByIdealSheaf Y I) V z]
  exact h3

/-- The sections of `ℐ` killed by every `𝒪_Y`-linear map `ℐ|_W ⟶ 𝒪_X|_W`, for every open
`W` of `Y`, at every level of the slice site over `W`. The quantification over all `W`, with
only a morphism `W' ⟶ X` relating the slice to the open at hand, is what makes membership
both stable under restriction and local. -/
private def killedByLocalHomsPre :
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
        Y.sheaf)).val.Submodule where
  obj X :=
    { carrier := {s | ∃ hs : s ∈ I.obj X, ∀ (W : Opens Y.carrier)
        (y : (restrFun Y.sheaf.obj W).obj I.toSheafOfModules.val ⟶
          (restrFun Y.sheaf.obj W).obj (quotientByIdealSheaf Y I).val)
        (W' : (Over W)ᵒᵖ) (h : W'.unop.left ⟶ X.unop),
        y.app W' (I.toSheafOfModules.val.map h.op ⟨s, hs⟩) = 0}
      add_mem' := by
        rintro a b ⟨ha, Ha⟩ ⟨hb, Hb⟩
        refine ⟨add_mem ha hb, fun W y W' h => ?_⟩
        have e1 : I.toSheafOfModules.val.map h.op (⟨a + b, add_mem ha hb⟩ : I.obj X)
            = I.toSheafOfModules.val.map h.op (⟨a, ha⟩ : I.obj X)
              + I.toSheafOfModules.val.map h.op (⟨b, hb⟩ : I.obj X) :=
          map_add _ (⟨a, ha⟩ : I.obj X) (⟨b, hb⟩ : I.obj X)
        rw [e1]
        have e2 : y.app W' (I.toSheafOfModules.val.map h.op (⟨a, ha⟩ : I.obj X)
              + I.toSheafOfModules.val.map h.op (⟨b, hb⟩ : I.obj X))
            = y.app W' (I.toSheafOfModules.val.map h.op (⟨a, ha⟩ : I.obj X))
              + y.app W' (I.toSheafOfModules.val.map h.op (⟨b, hb⟩ : I.obj X)) :=
          map_add _ _ _
        rw [e2, Ha, Hb, add_zero]
      zero_mem' := by
        refine ⟨zero_mem _, fun W y W' h => ?_⟩
        have e1 : I.toSheafOfModules.val.map h.op (⟨0, zero_mem _⟩ : I.obj X) = 0 :=
          map_zero _
        rw [e1]
        exact map_zero _
      smul_mem' := by
        rintro c a ⟨ha, Ha⟩
        refine ⟨Submodule.smul_mem _ c ha, fun W y W' h => ?_⟩
        have e1 : I.toSheafOfModules.val.map h.op
            (⟨c • a, Submodule.smul_mem _ c ha⟩ : I.obj X)
            = ((Stacks.SheafOfModules.Tensor.ringSheaf
                (J := (Opens.grothendieckTopology Y.carrier))) Y.sheaf).obj.map h.op c •
              I.toSheafOfModules.val.map h.op (⟨a, ha⟩ : I.obj X) :=
          PresheafOfModules.map_smul I.toSheafOfModules.val h.op c (⟨a, ha⟩ : I.obj X)
        rw [e1]
        exact smul_apply_eq_zero (y.app W') _ (Ha W y W' h) }
  map := by
    rintro X X' f s ⟨hs, H⟩
    refine ⟨I.map_mem f hs, fun W y W' h => ?_⟩
    have e1 : I.toSheafOfModules.val.map ((h ≫ f.unop).op) (⟨s, hs⟩ : I.obj X)
        = I.toSheafOfModules.val.map h.op
            (I.toSheafOfModules.val.map f (⟨s, hs⟩ : I.obj X)) :=
      PresheafOfModules.map_comp_apply I.toSheafOfModules.val f h.op (⟨s, hs⟩ : I.obj X)
    have HH := H W y W' (h ≫ f.unop)
    rw [e1] at HH
    exact HH

/-- The ideal subsheaf of sections of `ℐ` killed by every local `𝒪_Y`-linear map to `𝒪_X`.
Membership is local because `𝒪_X` is a sheaf, hence separated. -/
private def killedByLocalHoms :
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Opens.grothendieckTopology Y.carrier)))
        Y.sheaf)).Submodule where
  toSubmodule := killedByLocalHomsPre Y I
  isSheaf := by
    intro X s hcov
    have hsub : (killedByLocalHomsPre Y I).toSubfunctor.sieveOfSection s ≤
        I.toSubmodule.toSubfunctor.sieveOfSection s := fun _ _ ⟨h1, _⟩ ↦ h1
    have hsI : s ∈ I.obj X := I.isSheaf s
      ((Opens.grothendieckTopology Y.carrier).superset_covering hsub hcov)
    refine ⟨hsI, fun W y W' h => ?_⟩
    refine (quotientByIdealSheaf Y I).isSheaf.isSeparated W'.unop.left
      (((killedByLocalHomsPre Y I).toSubfunctor.sieveOfSection s).pullback h)
      ((Opens.grothendieckTopology Y.carrier).pullback_stable h hcov) _ 0 ?_
    intro Z' f hf
    obtain ⟨hs', H'⟩ := hf
    have key := H' W y (Opposite.op (Over.mk (f ≫ W'.unop.hom))) (𝟙 Z')
    have key2 : y.app (Opposite.op (Over.mk (f ≫ W'.unop.hom)))
        (I.toSheafOfModules.val.map ((f ≫ h).op) (⟨s, hsI⟩ : I.obj X)) = 0 :=
      Eq.trans (congrArg (fun z => y.app (Opposite.op (Over.mk (f ≫ W'.unop.hom))) z)
        (presheafOfModules_map_op_id_apply I.toSheafOfModules.val Z'
          (I.toSheafOfModules.val.map ((f ≫ h).op) (⟨s, hsI⟩ : I.obj X))).symm) key
    have hnat := PresheafOfModules.naturality_apply y
      ((Over.homMk f : Over.mk (f ≫ W'.unop.hom) ⟶ W'.unop).op)
      (I.toSheafOfModules.val.map h.op (⟨s, hsI⟩ : I.obj X))
    have e2 : I.toSheafOfModules.val.map ((f ≫ h).op) (⟨s, hsI⟩ : I.obj X)
        = I.toSheafOfModules.val.map f.op
            (I.toSheafOfModules.val.map h.op (⟨s, hsI⟩ : I.obj X)) :=
      PresheafOfModules.map_comp_apply I.toSheafOfModules.val h.op f.op (⟨s, hsI⟩ : I.obj X)
    refine Eq.trans ?_ (map_zero _).symm
    refine hnat.symm.trans ?_
    exact (congrArg (fun z => y.app (Opposite.op (Over.mk (f ≫ W'.unop.hom))) z)
      e2.symm).trans key2

/-- Every local product of two sections of `ℐ` is killed by every local `𝒪_Y`-linear map
`ℐ ⟶ 𝒪_X`, because `ℐ` annihilates `𝒪_X`; hence `ℐ²`, the smallest ideal subsheaf containing
those products, is contained in `killedByLocalHoms`. -/
private lemma idealSquare_le_killedByLocalHoms :
    idealSquare Y I ≤ killedByLocalHoms Y I := by
  refine sInf_le ?_
  intro U a b ha hb
  refine ⟨(I.toSubmodule.obj U).smul_mem a hb, fun W y W' h => ?_⟩
  have e1 : I.toSheafOfModules.val.map h.op
      (⟨a * b, (I.toSubmodule.obj U).smul_mem a hb⟩ : I.obj U)
      = ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (Opens.grothendieckTopology Y.carrier))) Y.sheaf).obj.map h.op a •
        I.toSheafOfModules.val.map h.op (⟨b, hb⟩ : I.obj U) :=
    PresheafOfModules.map_smul I.toSheafOfModules.val h.op a (⟨b, hb⟩ : I.obj U)
  rw [e1]
  refine apply_smul_eq_zero_of_smul_eq_zero (y.app W') _ _ ?_
  exact smul_quotientByIdealSheaf_eq_zero Y I W'.unop.left _ (I.map_mem h.op ha) _

/-- **Every `𝒪_Y`-linear map `ℐ ⟶ 𝒪_X` kills `ℐ²`**: precomposition along the inclusion
`ℐ² ⟶ ℐ` is the zero map on internal Homs into `𝒪_X`. -/
public lemma internalHomMapLeft_idealSquareInclusion_app_quotient_eq_zero :
    (internalHomMapLeftNatTrans Y.sheaf (idealSquareInclusion Y I)).app
      (quotientByIdealSheaf Y I) = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (restrFun Y.sheaf.obj V.unop).map (idealSquareInclusion Y I).val ≫ y = 0
  apply PresheafOfModules.hom_ext
  intro W'
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  obtain ⟨hc1, Hc⟩ := (idealSquare_le_killedByLocalHoms Y I)
    (Opposite.op W'.unop.left) c.2
  refine Eq.trans ?_ (Hc V.unop y W' (𝟙 W'.unop.left))
  exact congrArg (fun z => y.app W' z)
    (presheafOfModules_map_op_id_apply I.toSheafOfModules.val W'.unop.left
      (⟨c.1, hc1⟩ : I.obj (Opposite.op W'.unop.left))).symm

/-- **`Hom(ℐ, 𝒪_X)` factors through `ℐ/ℐ²`**: precomposition along `ℐ ↠ ℐ/ℐ²` identifies
the normal sheaf `𝓗om_{𝒪_Y}(ℐ/ℐ², 𝒪_X)` with `𝓗om_{𝒪_Y}(ℐ, 𝒪_X)`. -/
public lemma isIso_internalHomMapLeft_cokernelπ_idealSquareInclusion :
    IsIso ((internalHomMapLeftNatTrans Y.sheaf
      (cokernel.π (idealSquareInclusion Y I))).app (quotientByIdealSheaf Y I)) := by
  obtain ⟨⟨_, hex⟩, hmono⟩ := exact_and_mono_internalHomMapLeft_cokernelπ Y
    (idealSquareInclusion Y I) (quotientByIdealSheaf Y I)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hmono
    (hex.epi_f (internalHomMapLeft_idealSquareInclusion_app_quotient_eq_zero Y I))

/-- The degree-one connecting map of a short exact sequence of cochain complexes is an
isomorphism when the degree-zero map on cohomology vanishes and the middle complex has no
first cohomology. -/
private lemma shortExact_boundary_isIso
    {C : Type*} [Category* C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℕ)} (hS : S.ShortExact)
    (hij : (ComplexShape.up ℕ).Rel 0 1)
    (hzero : HomologicalComplex.homologyMap S.g 0 = 0)
    (hmid : IsZero (S.X₂.homology 1)) : IsIso (hS.δ 0 1 hij) := by
  have : Mono (hS.δ 0 1 hij) := (hS.homology_exact₃ 0 1 hij).mono_g_iff.mpr hzero
  have : Epi (hS.δ 0 1 hij) := (hS.homology_exact₁ 0 1 hij).epi_f_iff.mpr (hmid.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- **Stacks Project, Tag 0BQW.** Let `Y` be a ringed space, let `ℐ ⊆ 𝒪_Y` be a sheaf of
ideals, put `𝒪_X = 𝒪_Y/ℐ` and let `𝒩 = 𝓗om_{𝒪_Y}(ℐ/ℐ², 𝒪_X)` be the normal sheaf. The
canonical map `c : 𝒩 ⟶ 𝓔xt¹_{𝒪_Y}(𝒪_X, 𝒪_X)` of `normalSheafToSheafExtOne` is an
isomorphism.

All four inputs of the source's proof are proved here:
`isIso_internalHomMapLeft_cokernelπ_idealSquareInclusion` (every `𝒪_Y`-linear map
`ℐ ⟶ 𝒪_X` factors uniquely through `ℐ/ℐ²`), `internalHomMapLeft_ι_app_quotient_eq_zero`
(the degree-zero map vanishes, because `ℐ` annihilates `𝒪_X`),
`sheafHomComplexSequence_shortExact` ([Stacks, Tag 01DR] for sheaves of modules) and
`Stacks.RingedSpace.isZero_sheafExt_unit_succ` (`𝓔xt¹_{𝒪_Y}(𝒪_Y, 𝒪_X) = 0`). -/
@[stacks 0BQW]
public theorem isIso_normalSheafToSheafExtOne :
    IsIso (normalSheafToSheafExtOne Y I) := by
  have t1 : IsIso ((internalHomSecondFunctor.{u, u, u, u}
      (Opens.grothendieckTopology Y.carrier) Y.sheaf
      I.toSheafOfModules).toRightDerivedZero.app (quotientByIdealSheaf Y I)) := inferInstance
  have t2 : IsIso (((injectiveResolution (quotientByIdealSheaf Y I)).isoRightDerivedObj
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        I.toSheafOfModules) 0).hom) := inferInstance
  have t3 : IsIso ((sheafHomComplexSequence_shortExact Y I
      (injectiveResolution (quotientByIdealSheaf Y I)).cocomplex).δ 0 1 rfl) :=
    shortExact_boundary_isIso _ rfl
      (homologyMap_eq_zero_of_app_eq_zero
        (internalHomMapLeftNatTrans Y.sheaf I.ι)
        (injectiveResolution (quotientByIdealSheaf Y I))
        (internalHomMapLeft_ι_app_quotient_eq_zero Y I))
      ((Stacks.RingedSpace.isZero_sheafExt_unit_succ Y (quotientByIdealSheaf Y I) 0).of_iso
        ((injectiveResolution (quotientByIdealSheaf Y I)).isoRightDerivedObj
        (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
          (SheafOfModules.unit _)) 1).symm)
  rw [normalSheafToSheafExtOne]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _
    (isIso_internalHomMapLeft_cokernelπ_idealSquareInclusion Y I) ?_
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ t1 ?_
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ t2 ?_
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ t3 (Iso.isIso_inv _)

end Stacks.Duality

end

end
