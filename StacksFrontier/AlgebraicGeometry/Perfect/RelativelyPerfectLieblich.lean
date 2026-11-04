module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseOpen
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOpenLocality
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectSectionsChart
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTriangulatedCanonical
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeAbsolute
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenStalkExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.Homology.RelativelyPerfect.FlatComplex
public import StacksFrontier.RingTheory.Dualizing.DerivedHomFiniteCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
import all StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
import StacksCore.Tactic.StacksAttribute

/-!
# Relatively perfect objects: Lieblich's definition and condition (B)

This file proves the content of Stacks Remark 0DI9.

**Lieblich's definition.** Let `f : X ⟶ S` be a morphism of schemes. Lieblich calls an object
`E` of `D(𝒪_X)` relatively perfect when

* (A) locally on `X`, `E` is quasi-isomorphic to a finite complex of `S`-flat, finitely
  presented `𝒪_X`-modules.

Whenever Definition 0DI0 applies, i.e. when `f` is flat and locally of finite presentation, an
object is `S`-perfect in the sense of 0DI0 exactly when it satisfies (A). The source's proof is a
footnote: reduce to affines by Lemma 0DI2 and use More on Algebra, Lemma 0DHV.

**Condition (B).** For `f` only locally of finite type, the natural generalisation of 0DI0 is

* (B) `E` is pseudo-coherent relative to `S` (Stacks 09UI) and locally has finite Tor dimension
  as an object of `D(f⁻¹𝒪_S)` (Stacks 08CG),

and it defines a triangulated subcategory of `D(𝒪_X)`. When `f` is flat and locally of finite
presentation it is Definition 0DI0 again.

## Main definitions

* `Scheme.Hom.IsLocallyBoundedFlatFinitePresentation`: condition (A).
* `Scheme.Hom.isPseudoCoherentOfLocallyFiniteTorDimensionOver`: condition (B), with finite Tor
  dimension read at the derived tensor product of Stacks 06YU.

## Main results

* `Scheme.Hom.isRelativelyPerfect_iff_isLocallyBoundedFlatFinitePresentation`: for `f` flat and
  locally of finite presentation, Definition 0DI0 is equivalent to (A).
* `Scheme.Hom.isTriangulated_isPseudoCoherentOfLocallyFiniteTorDimensionOver` and its
  `isClosedUnderIsomorphisms_` companion: for `f` locally of finite type, (B) defines a strictly
  full triangulated subcategory.
* `Scheme.Hom.isPseudoCoherentOfLocallyFiniteTorDimensionOver_iff_isRelativelyPerfect`: for
  `f` flat and locally of finite presentation, (B) is Definition 0DI0.
* `Scheme.Hom.isRelativelyPerfect_iff_isLocallyBoundedFlatFinitePresentation_and_isTriangulated`:
  **Stacks 0DI9**, all three together.

## Implementation notes

In (A), "locally on `X`" is a neighbourhood `U` of every point, "`E|_U`" is the derived pullback
along the open immersion `U ⟶ X` (which for an open immersion is termwise restriction,
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`), a finite complex is a
cochain complex strictly concentrated in some interval `[a, b]`, finitely presented is
`SheafOfModules.IsFinitePresentation` (Stacks 01BN), and `S`-flat is
`AlgebraicGeometry.IsFlatOver` along `U ⟶ X ⟶ S` (Stacks 08KT: every stalk `ℱ_x` is flat over
`𝒪_{S, f x}`).

The equivalence with 0DI0 follows the footnote. Both relative perfectness (by
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_forall_mem`) and (A) are local on `X`, so the
proof runs on the affine charts `Spec Γ(X, U) ⟶ X` of compatible pairs of affine opens
`U ⊆ f⁻¹(V)`. There `f` becomes `Spec Γ(X, U) ⟶ Spec Γ(S, V) ⟶ S`, the second arrow being an
open immersion, so relative perfectness over `S` is relative perfectness over `Spec Γ(S, V)`
(`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_baseOpen_iff`). A relatively perfect object
there is the sheafification of a complex of `Γ(X, U)`-modules perfect relative to `Γ(S, V)`
(Stacks 08E5 and 06Z0 with the affine dictionary
`AlgebraicGeometry.AffinePerfectDescent.isPerfectRelativeTo_tildeObj_iff`, which is Stacks 0DI2 on
one chart), and Stacks 0DHV makes that complex a bounded complex of `Γ(S, V)`-flat, finitely
presented modules. Conversely a bounded complex of finitely presented, `S`-flat
quasi-coherent modules on the chart is the sheafification of its global sections, which are
finitely presented (Stacks 01PC) and `Γ(S, V)`-flat (Stacks 01U4), and Stacks 0DHV applies the
other way.

Condition (B) is stated with no certificate parameter: its Tor clause is
`Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`, part (3) of Stacks 08CG at the
genuine derived tensor product `- ⊗^L_{f⁻¹𝒪_S} -` of Stacks 06YU on each open subspace of
`(X, f⁻¹𝒪_S)`. It is by definition the certificate-parameterised condition
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentOfFiniteTorDimensionRelativeTo` at the canonical
family `AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`, and at that
family the two inputs which the parameterised triangulated statement takes as hypotheses are
theorems: each `- ⊗^L ℱ[0]` commutes with shifts and is exact
(`AlgebraicGeometry.RingedSpace.commShift_canonicalCertificate`,
`AlgebraicGeometry.RingedSpace.isTriangulated_canonicalCertificate`), and finite Tor dimension
passes to smaller opens
(`AlgebraicGeometry.RingedSpace.finiteTorDimensionRestricts_canonicalFamily`, Stacks 09U8). Nothing
is assumed.

The remaining sentences of the remark — that (A) is suspected not to define a triangulated
subcategory, and that (A) is easier to work with in regards to limits — are a conjecture and a
comment, not assertions, and are not formalized.

## References

* [Stacks Project, Remark 36.35.5 (Tag 0DI9)](https://stacks.math.columbia.edu/tag/0DI9)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Tag 0DHV](https://stacks.math.columbia.edu/tag/0DHV)
* [Stacks Project, Definition 37.59.1 (Tag 09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* M. Lieblich, *Moduli of complexes on a proper morphism*, J. Algebraic Geom. 15 (2006).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.LieblichComparison

open AffineRelativeTorAmplitude AffinePerfectDescent

/-- Relative perfectness over the canonical family is invariant under isomorphism. -/
private theorem isPerfectRelativeTo_of_iso {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f]
    {E E' : DerivedCategory (OXMod.{u, u} X.toRingedSpace)} (e : E ≅ E')
    (h : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E' :=
  have := Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo f
    (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
  (Scheme.Hom.isPerfectRelativeTo f
    (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)).prop_of_iso e h

section Affine

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
  [Algebra.FinitePresentation R A]

/-- **A bounded complex of `R`-flat, finitely presented `A`-modules sheafifies to a
`Spec R`-perfect object.** For a flat ring map `R → A` of finite presentation this is the
backward implication of Stacks 0DHV followed by the affine dictionary
`AlgebraicGeometry.AffinePerfectDescent.isPerfectRelativeTo_tildeObj_iff`. -/
theorem isPerfectRelativeTo_tildeObj_of_bounded (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (a b : ℤ) (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hflat : ∀ i, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X i)))
    (hfp : ∀ i, Module.FinitePresentation A (P.X i)) :
    (specMap R A).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) (tildeObj A P) :=
  (isPerfectRelativeTo_tildeObj_iff R A P).2
    ((PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ _).2 ⟨P, a, b, hGE, hLE, hflat, hfp, ⟨Iso.refl _⟩⟩)

/-- **A `Spec R`-perfect object of `D(𝒪_{Spec A})` is the sheafification of a bounded complex of
`R`-flat, finitely presented `A`-modules.** It has quasi-coherent cohomology (Stacks 08E5), so
Stacks 06Z0 presents it as the sheafification of a complex of `A`-modules, which is perfect
relative to `R` by the affine dictionary; the forward implication of Stacks 0DHV replaces that
complex by a bounded one with `R`-flat, finitely presented terms. -/
theorem exists_bounded_of_isPerfectRelativeTo
    (E : DerivedCategory (OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace))
    (hE : (specMap R A).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X i))) ∧
      (∀ i, Module.FinitePresentation A (P.X i)) ∧ Nonempty (tildeObj A P ≅ E) := by
  have hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Spec (CommRingCat.of A)).Modules n).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent (Spec (CommRingCat.of A)) E hE.1
  obtain ⟨K, ⟨eK⟩⟩ := StandardModel.exists_iso_mapDerivedCategory (CommRingCat.of A) E hqc
  obtain ⟨M, ⟨eM⟩⟩ : (DerivedCategory.Q (C := ModuleCat.{u} A)).essImage K :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) K
  have eE : tildeObj A M ≅ E :=
    ((tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors.app M).symm ≪≫
      (tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso eM ≪≫ eK
  have hM := isPerfectRelativeTo_of_iso _ eE.symm hE
  obtain ⟨P, a, b, hGE, hLE, hflat, hfp, ⟨eP⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ _).1 ((isPerfectRelativeTo_tildeObj_iff R A M).1 hM)
  refine ⟨P, a, b, hGE, hLE, hflat, hfp, ⟨?_⟩⟩
  exact ((tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors.app P).symm ≪≫
    (tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso eP.symm ≪≫
    (tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors.app M ≪≫ eE

end Affine

/-- The global sections of a finitely presented module on `Spec R` form a finitely presented
`R`-module: such a module is quasi-coherent, hence the sheafification of its global sections,
and Stacks 01PC applies. -/
theorem moduleFinitePresentation_moduleSpecΓFunctor_obj (R : CommRingCat.{u}) (G : (Spec R).Modules)
    (h : G.IsFinitePresentation) :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj G) := by
  have := h
  have : G.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation G
  exact (tilde_isFinitePresentation_iff ((modulesSpecToSheaf.obj G).presheaf.obj (.op ⊤))).1
    (Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      (asIso (Scheme.Modules.fromTildeΓ G)).symm h)

/-- The global sections of a finitely presented module on `Spec A` which is flat over `S`
along `Spec A ⟶ Spec Γ(S, V) ⟶ S` are flat over `Γ(S, V)` (Stacks 01U4). -/
theorem moduleFlat_moduleSpecΓFunctor_obj {S : Scheme.{u}} {V : S.Opens} (hV : IsAffineOpen V)
    (A : Type u) [CommRing A] [Algebra Γ(S, V) A] (G : (Spec (CommRingCat.of A)).Modules)
    (hG : G.IsFinitePresentation)
    (h : IsFlatOver (specMap Γ(S, V) A ≫ hV.fromSpec).toLRSHom.toShHom G) :
    Module.Flat Γ(S, V)
      ((ModuleCat.restrictScalars (algebraMap Γ(S, V) A)).obj (moduleSpecΓFunctor.obj G)) := by
  have := hG
  have : G.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation G
  exact (isFlatOver_spec_iff_flat_sections hV (CommRingCat.ofHom (algebraMap Γ(S, V) A)) G).1 h

/-- The sheaf `M^~` on `Spec A` attached to an `A`-module `M` which is flat over `Γ(S, V)` is flat
over `S` along `Spec A ⟶ Spec Γ(S, V) ⟶ S` (Stacks 01U4). -/
theorem isFlatOver_tilde_of_flat {S : Scheme.{u}} {V : S.Opens} (hV : IsAffineOpen V)
    (A : Type u) [CommRing A] [Algebra Γ(S, V) A] (M : ModuleCat.{u} A)
    (h : Module.Flat Γ(S, V) ((ModuleCat.restrictScalars (algebraMap Γ(S, V) A)).obj M)) :
    IsFlatOver (specMap Γ(S, V) A ≫ hV.fromSpec).toLRSHom.toShHom
      (tilde (R := CommRingCat.of A) M) := by
  refine (isFlatOver_spec_iff_flat_sections hV (CommRingCat.ofHom (algebraMap Γ(S, V) A))
    (tilde (R := CommRingCat.of A) M)).2 ?_
  let e := tilde.isoTop (R := CommRingCat.of A) M
  let M' := (modulesSpecToSheaf.obj (tilde (R := CommRingCat.of A) M)).presheaf.obj (.op ⊤)
  let : Module Γ(S, V) M' := Module.compHom _ (algebraMap Γ(S, V) A)
  let eR : M' ≃ₗ[Γ(S, V)] (ModuleCat.restrictScalars (algebraMap Γ(S, V) A)).obj M :=
    { toFun := e.inv.hom
      invFun := e.hom.hom
      map_add' := map_add e.inv.hom
      map_smul' := fun r x => e.inv.hom.map_smul (algebraMap Γ(S, V) A r) x
      left_inv := fun x => by simp
      right_inv := fun x => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e.hom_inv_id) x }
  exact Module.Flat.of_linearEquiv eR

section Chart

variable {S : Scheme.{u}} {V : S.Opens} (hV : IsAffineOpen V)
  (A : Type u) [CommRing A] [Algebra Γ(S, V) A] [Module.Flat Γ(S, V) A]
  [Algebra.FinitePresentation Γ(S, V) A]

/-- **The affine chart, from complexes to relative perfectness.** Let `V ⊆ S` be an affine open
and `Γ(S, V) → A` flat and of finite presentation. A bounded complex of finitely presented
`𝒪_{Spec A}`-modules flat over `S` is `S`-perfect along `Spec A ⟶ Spec Γ(S, V) ⟶ S`.

The complex is the sheafification of its complex of global sections, whose terms are finitely
presented over `A` and flat over `Γ(S, V)`; then
`AlgebraicGeometry.LieblichComparison.isPerfectRelativeTo_tildeObj_of_bounded` applies over
`Spec Γ(S, V)`, and relative perfectness over `Spec Γ(S, V)` and over `S` agree because
`Spec Γ(S, V) ⟶ S` is an open immersion. -/
theorem isPerfectRelativeTo_specMap_comp_of_bounded
    (G : CochainComplex (Spec (CommRingCat.of A)).Modules ℤ) (a b : ℤ)
    (hGE : G.IsStrictlyGE a) (hLE : G.IsStrictlyLE b)
    (hfp : ∀ i, (G.X i).IsFinitePresentation)
    (hflat : ∀ i, IsFlatOver (specMap Γ(S, V) A ≫ hV.fromSpec).toLRSHom.toShHom (G.X i)) :
    (specMap Γ(S, V) A ≫ hV.fromSpec).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      (DerivedCategory.Q.obj G) := by
  have : (moduleSpecΓFunctor (R := CommRingCat.of A)).IsRightAdjoint :=
    (tilde.adjunction (R := CommRingCat.of A)).isRightAdjoint
  let N : CochainComplex (ModuleCat.{u} A) ℤ :=
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).mapHomologicalComplex _).obj G
  have hiso : ∀ i, IsIso (Scheme.Modules.fromTildeΓNatTrans.app (G.X i)) := fun i =>
    have := hfp i
    have : (G.X i).IsQuasicoherent :=
      SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (G.X i)
    (inferInstance : IsIso (Scheme.Modules.fromTildeΓ (G.X i)))
  let eG : ((tilde.functor (CommRingCat.of A)).mapHomologicalComplex _).obj N ≅ G :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => asIso (Scheme.Modules.fromTildeΓNatTrans.app (G.X i)))
      (fun i j _ => (Scheme.Modules.fromTildeΓNatTrans.naturality (G.d i j)).symm)
  have hNfp : ∀ i, Module.FinitePresentation A (N.X i) := fun i =>
    moduleFinitePresentation_moduleSpecΓFunctor_obj (CommRingCat.of A) (G.X i) (hfp i)
  have hNflat : ∀ i, Module.Flat Γ(S, V)
      ((ModuleCat.restrictScalars (algebraMap Γ(S, V) A)).obj (N.X i)) := fun i =>
    moduleFlat_moduleSpecΓFunctor_obj hV A (G.X i) (hfp i) (hflat i)
  have hNGE : N.IsStrictlyGE a := Dualizing.isStrictlyGE_mapHomologicalComplex _ G a hGE
  have hNLE : N.IsStrictlyLE b := Dualizing.isStrictlyLE_mapHomologicalComplex _ G b hLE
  have hA := isPerfectRelativeTo_tildeObj_of_bounded Γ(S, V) A N a b hNGE hNLE hNflat hNfp
  have hA' := isPerfectRelativeTo_of_iso _ (DerivedCategory.Q.mapIso eG) hA
  exact (Scheme.Hom.isPerfectRelativeTo_baseOpen_iff (specMap Γ(S, V) A) hV.fromSpec rfl
    (DerivedCategory.Q.obj G)).2 hA'


/-- **The affine chart, from relative perfectness to complexes.** Let `V ⊆ S` be an affine open
and `Γ(S, V) → A` flat and of finite presentation. An object of `D(𝒪_{Spec A})` which is
`S`-perfect along `Spec A ⟶ Spec Γ(S, V) ⟶ S` is isomorphic to a bounded complex of finitely
presented `𝒪_{Spec A}`-modules flat over `S`. -/
theorem exists_bounded_of_isPerfectRelativeTo_specMap_comp
    (E : DerivedCategory (OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace))
    (hE : (specMap Γ(S, V) A ≫ hV.fromSpec).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    ∃ (P : CochainComplex (Spec (CommRingCat.of A)).Modules ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ i, (P.X i).IsFinitePresentation) ∧
      (∀ i, IsFlatOver (specMap Γ(S, V) A ≫ hV.fromSpec).toLRSHom.toShHom (P.X i)) ∧
      Nonempty (E ≅ DerivedCategory.Q.obj P) := by
  have h1 := (Scheme.Hom.isPerfectRelativeTo_baseOpen_iff (specMap Γ(S, V) A) hV.fromSpec rfl
    E).1 hE
  obtain ⟨P, a, b, hGE, hLE, hflat, hfp, ⟨eP⟩⟩ :=
    exists_bounded_of_isPerfectRelativeTo Γ(S, V) A E h1
  have := hGE
  have := hLE
  exact ⟨((tilde.functor (CommRingCat.of A)).mapHomologicalComplex _).obj P, a, b,
    Dualizing.isStrictlyGE_mapHomologicalComplex _ P a hGE,
    Dualizing.isStrictlyLE_mapHomologicalComplex _ P b hLE,
    fun i => (tilde_isFinitePresentation_iff (R := CommRingCat.of A) (P.X i)).2 (hfp i),
    fun i => isFlatOver_tilde_of_flat hV A (P.X i) (hflat i), ⟨eP.symm⟩⟩

/-- `AlgebraicGeometry.LieblichComparison.isPerfectRelativeTo_specMap_comp_of_bounded` for any
morphism equal to `Spec A ⟶ Spec Γ(S, V) ⟶ S`. -/
theorem isPerfectRelativeTo_of_bounded_of_eq (k : Spec (CommRingCat.of A) ⟶ S)
    (hk : specMap Γ(S, V) A ≫ hV.fromSpec = k) [Flat k] [LocallyOfFinitePresentation k]
    (G : CochainComplex (Spec (CommRingCat.of A)).Modules ℤ) (a b : ℤ)
    (hGE : G.IsStrictlyGE a) (hLE : G.IsStrictlyLE b)
    (hfp : ∀ i, (G.X i).IsFinitePresentation)
    (hflat : ∀ i, IsFlatOver k.toLRSHom.toShHom (G.X i)) :
    k.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      (DerivedCategory.Q.obj G) := by
  subst hk
  exact isPerfectRelativeTo_specMap_comp_of_bounded hV A G a b hGE hLE hfp hflat

/-- `AlgebraicGeometry.LieblichComparison.exists_bounded_of_isPerfectRelativeTo_specMap_comp`
for any morphism equal to `Spec A ⟶ Spec Γ(S, V) ⟶ S`. -/
theorem exists_bounded_of_isPerfectRelativeTo_of_eq (k : Spec (CommRingCat.of A) ⟶ S)
    (hk : specMap Γ(S, V) A ≫ hV.fromSpec = k) [Flat k] [LocallyOfFinitePresentation k]
    (E : DerivedCategory (OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace))
    (hE : k.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    ∃ (P : CochainComplex (Spec (CommRingCat.of A)).Modules ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ i, (P.X i).IsFinitePresentation) ∧
      (∀ i, IsFlatOver k.toLRSHom.toShHom (P.X i)) ∧
      Nonempty (E ≅ DerivedCategory.Q.obj P) := by
  subst hk
  exact exists_bounded_of_isPerfectRelativeTo_specMap_comp hV A E hE

end Chart

section OpenImmersion

variable {W' W S : Scheme.{u}} (κ : W' ⟶ W) [IsOpenImmersion κ]

/-- An open immersion of schemes, read as a morphism of ringed spaces, is an open immersion. -/
local instance isOpenImmersion_toShHom : SheafedSpace.IsOpenImmersion κ.toLRSHom.toShHom :=
  (inferInstance : IsOpenImmersion κ)

/-- Pullback of sheaves of modules carries a complex vanishing below `n` to one. -/
theorem isStrictlyGE_modulePullback {Y Z : RingedSpace.{u, u}} (φ : Y ⟶ Z)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (n : ℤ)
    (hK : ∀ i < n, IsZero (K.X i)) :
    CochainComplex.IsStrictlyGE (((modulePullback φ).mapHomologicalComplex _).obj K) n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (modulePullback φ).map_isZero (hK i hi)

/-- Pullback of sheaves of modules carries a complex vanishing above `n` to one. -/
theorem isStrictlyLE_modulePullback {Y Z : RingedSpace.{u, u}} (φ : Y ⟶ Z)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (n : ℤ)
    (hK : ∀ i, n < i → IsZero (K.X i)) :
    CochainComplex.IsStrictlyLE (((modulePullback φ).mapHomologicalComplex _).obj K) n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (modulePullback φ).map_isZero (hK i hi)

/-- **Flatness over the base restricts along an open immersion.** If `F` is flat over `S` along
`g`, its pullback along an open immersion `κ` is flat over `S` along `κ ≫ g`. -/
theorem isFlatOver_modulePullback (g : W ⟶ S) (F : W.Modules)
    (h : IsFlatOver g.toLRSHom.toShHom F) :
    IsFlatOver (κ ≫ g).toLRSHom.toShHom ((modulePullback κ.toLRSHom.toShHom).obj F) :=
  (isFlatOver_iff_of_moduleIso _ ((modulePullbackIsoSchemePullback κ).app F)).2 fun x =>
    Stacks.AlgebraicGeometry.OpenStalkExactness.isFlatOverAt_pullback_comp g κ F x (h _)

/-- The derived pullback along an open immersion of a complex is the termwise pullback. -/
def derivedPullbackQObjIso (P : CochainComplex W.Modules ℤ) :
    (derivedPullback κ.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((modulePullback κ.toLRSHom.toShHom).mapHomologicalComplex _).obj P) :=
  (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso _).app _ ≪≫
    (modulePullback κ.toLRSHom.toShHom).mapDerivedCategoryFactors.app P

end OpenImmersion

/-- The compatible pairs of affine opens `U ⊆ g⁻¹(V)` of a morphism `g : W ⟶ S`, which index the
affine charts `Spec Γ(W, U) ⟶ W` used to test relative perfectness. -/
def AffineChartIndex {W S : Scheme.{u}} (g : W ⟶ S) : Type u :=
  {p : S.Opens × W.Opens // IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.2 ≤ g ⁻¹ᵁ p.1}

/-- **Condition (A) with one chart implies relative perfectness.** For a flat morphism
`g : W ⟶ S` locally of finite presentation, a bounded complex of finitely presented
`𝒪_W`-modules flat over `S` is an `S`-perfect object of `D(𝒪_W)`.

Relative perfectness is local on `W`; on each affine chart `Spec Γ(W, U) ⟶ W` with `U` mapping
into an affine open `V ⊆ S` the pulled back complex is again bounded, finitely presented and
flat over `S`, and
`AlgebraicGeometry.LieblichComparison.isPerfectRelativeTo_specMap_comp_of_bounded` applies. -/
theorem isPerfectRelativeTo_of_bounded {W S : Scheme.{u}} (g : W ⟶ S) [Flat g]
    [LocallyOfFinitePresentation g] (P : CochainComplex W.Modules ℤ) (a b : ℤ)
    (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfp : ∀ i, (P.X i).IsFinitePresentation)
    (hflat : ∀ i, IsFlatOver g.toLRSHom.toShHom (P.X i)) :
    g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      (DerivedCategory.Q.obj P) := by
  refine Scheme.Hom.isPerfectRelativeTo_of_openImmersion_cover g
    (fun k : AffineChartIndex g => Spec Γ(W, k.1.2)) (fun k => k.2.2.1.fromSpec)
    (fun w => ?_) (DerivedCategory.Q.obj P) (fun k => ?_)
  · obtain ⟨V, hV, hwV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show g w ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨U, hU, hwU, hUV⟩ :=
      exists_isAffineOpen_mem_and_subset (show w ∈ g ⁻¹ᵁ V from hwV)
    exact ⟨⟨(V, U), hV, hU, hUV⟩, by rw [hU.range_fromSpec]; exact hwU⟩
  · obtain ⟨⟨V, U⟩, hV, hU, e⟩ := k
    dsimp only
    let : Algebra Γ(S, V) Γ(W, U) := (g.appLE V U e).hom.toAlgebra
    have : Module.Flat Γ(S, V) Γ(W, U) := Scheme.Hom.moduleFlat_appLE g hV hU e rfl
    have : Algebra.FinitePresentation Γ(S, V) Γ(W, U) :=
      Scheme.Hom.algebraFinitePresentation_appLE g hV hU e rfl
    have hk : specMap Γ(S, V) Γ(W, U) ≫ hV.fromSpec = hU.fromSpec ≫ g :=
      IsAffineOpen.SpecMap_appLE_fromSpec g hV hU e
    refine isPerfectRelativeTo_of_iso _ (derivedPullbackQObjIso hU.fromSpec P).symm ?_
    have := hGE
    have := hLE
    exact isPerfectRelativeTo_of_bounded_of_eq hV Γ(W, U) _ hk _ a b
      (isStrictlyGE_modulePullback _ P a fun i hi => P.isZero_of_isStrictlyGE a i hi)
      (isStrictlyLE_modulePullback _ P b fun i hi => P.isZero_of_isStrictlyLE b i hi)
      (fun i => @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ _ (P.X i) (hfp i))
      (fun i => isFlatOver_modulePullback hU.fromSpec g (P.X i) (hflat i))

/-- **Relative perfectness implies condition (A) at every point.** For `f : X ⟶ S` flat and
locally of finite presentation and `E` an `S`-perfect object of `D(𝒪_X)`, every point of `X` has
an (affine) open neighbourhood `U` on which `E|_U` is isomorphic to a bounded complex of
finitely presented `𝒪_U`-modules flat over `S`. -/
theorem exists_opens_bounded_of_isPerfectRelativeTo {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E)
    (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ (P : CochainComplex U.toScheme.Modules ℤ) (a b : ℤ),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i, (P.X i).IsFinitePresentation) ∧
        (∀ i, IsFlatOver (U.ι ≫ f).toLRSHom.toShHom (P.X i)) ∧
        Nonempty ((derivedPullback U.ι.toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show f x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ V from hxV)
  let : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
  have : Module.Flat Γ(S, V) Γ(X, W) := Scheme.Hom.moduleFlat_appLE f hV hW hWV rfl
  have : Algebra.FinitePresentation Γ(S, V) Γ(X, W) :=
    Scheme.Hom.algebraFinitePresentation_appLE f hV hW hWV rfl
  have hk : specMap Γ(S, V) Γ(X, W) ≫ hV.fromSpec = hW.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWV
  obtain ⟨P, a, b, hGE, hLE, hfp, hflat, ⟨eP⟩⟩ :=
    exists_bounded_of_isPerfectRelativeTo_of_eq hV Γ(X, W) _ hk _
      (Scheme.Hom.isPerfectRelativeTo_comp_openImmersion f hW.fromSpec E hE)
  let k := hW.isoSpec.hom
  have hkj : k ≫ hW.fromSpec = W.ι := hW.isoSpec_hom_fromSpec
  have hkj' : k.toLRSHom.toShHom ≫ hW.fromSpec.toLRSHom.toShHom = W.ι.toLRSHom.toShHom := by
    rw [← hkj]
    rfl
  refine ⟨W, hxW, ((modulePullback k.toLRSHom.toShHom).mapHomologicalComplex _).obj P, a, b,
    isStrictlyGE_modulePullback _ P a fun i hi => P.isZero_of_isStrictlyGE a i hi,
    isStrictlyLE_modulePullback _ P b fun i hi => P.isZero_of_isStrictlyLE b i hi,
    fun i => @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ _ (P.X i) (hfp i),
    fun i => ?_, ⟨?_⟩⟩
  · have h := isFlatOver_modulePullback k (hW.fromSpec ≫ f) (P.X i) (hflat i)
    rwa [← Category.assoc, hkj] at h
  · exact ((Stacks.Cohomology.TorAmplitude.derivedPullbackFactorIso _ _ _ hkj').app E).symm ≪≫
      (derivedPullback k.toLRSHom.toShHom).mapIso eP ≪≫ derivedPullbackQObjIso k P

end AlgebraicGeometry.LieblichComparison

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory.ObjectProperty

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Condition (A) of Stacks 0DI9 (Lieblich's relative perfectness).** Locally on `X`, the
object `E` of `D(𝒪_X)` is quasi-isomorphic to a finite complex of `S`-flat, finitely presented
`𝒪_X`-modules: every point of `X` has an open neighbourhood `U` such that `E|_U` is isomorphic in
`D(𝒪_U)` to a cochain complex `P` concentrated in degrees `[a, b]` whose terms are finitely
presented `𝒪_U`-modules flat over `S` along `U ⟶ X ⟶ S`. -/
def IsLocallyBoundedFlatFinitePresentation (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ (P : CochainComplex U.toScheme.Modules ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i, (P.X i).IsFinitePresentation) ∧
      (∀ i, IsFlatOver (U.ι ≫ f).toLRSHom.toShHom (P.X i)) ∧
      Nonempty ((derivedPullback U.ι.toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj P)

/-- **Definition 0DI0 is Lieblich's definition, whenever 0DI0 applies.** For `f : X ⟶ S` flat and
locally of finite presentation, an object of `D(𝒪_X)` is `S`-perfect exactly when, locally on
`X`, it is quasi-isomorphic to a finite complex of `S`-flat, finitely presented `𝒪_X`-modules. -/
theorem isRelativelyPerfect_iff_isLocallyBoundedFlatFinitePresentation [Flat f]
    [LocallyOfFinitePresentation f] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsRelativelyPerfect E ↔ f.IsLocallyBoundedFlatFinitePresentation E := by
  refine ⟨fun h x => LieblichComparison.exists_opens_bounded_of_isPerfectRelativeTo f E h x,
    fun h => ?_⟩
  refine isPerfectRelativeTo_of_forall_mem f E fun x => ?_
  obtain ⟨U, hxU, P, a, b, hGE, hLE, hfp, hflat, ⟨e⟩⟩ := h x
  refine ⟨U, hxU, ?_⟩
  exact LieblichComparison.isPerfectRelativeTo_of_iso _ e.symm
      (LieblichComparison.isPerfectRelativeTo_of_bounded (U.ι ≫ f) P a b hGE hLE hfp hflat)

/-- **Condition (B) of Stacks 0DI9.** The objects `E` of `D(𝒪_X)` which are pseudo-coherent
relative to `S` (Stacks 09UI) and which, viewed in `D(f⁻¹𝒪_S)`, locally have finite Tor dimension
(part (3) of Stacks 08CG), the derived tensor product being the one of Stacks 06YU. -/
def isPseudoCoherentOfLocallyFiniteTorDimensionOver [LocallyOfFiniteType f] :
    ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :=
  fun E => f.IsPseudoCoherent E ∧
    Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base) ((derivedScalarRestriction f).obj E)

/-- Condition (B) is the certificate-parameterised condition
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentOfFiniteTorDimensionRelativeTo` read at the
canonical family of derived tensor products. -/
theorem isPseudoCoherentOfLocallyFiniteTorDimensionOver_eq [LocallyOfFiniteType f] :
    f.isPseudoCoherentOfLocallyFiniteTorDimensionOver =
      isPseudoCoherentOfFiniteTorDimensionRelativeTo f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) :=
  rfl

/-- **Condition (B) defines a strictly full subcategory**: it is invariant under isomorphism in
`D(𝒪_X)`. -/
theorem isClosedUnderIsomorphisms_isPseudoCoherentOfLocallyFiniteTorDimensionOver
    [LocallyOfFiniteType f] :
    f.isPseudoCoherentOfLocallyFiniteTorDimensionOver.IsClosedUnderIsomorphisms := by
  rw [isPseudoCoherentOfLocallyFiniteTorDimensionOver_eq]
  exact isClosedUnderIsomorphisms_isPseudoCoherentOfFiniteTorDimensionRelativeTo f _

/-- **Condition (B) defines a triangulated subcategory of `D(𝒪_X)`**, for `f` locally of finite
type: it contains zero, is stable under all shifts and is closed under extensions. Relative
pseudo-coherence is a triangulated condition by Stacks 09UL and finite Tor dimension by
Stacks 08CJ, using that `- ⊗^L ℱ[0]` is exact and that finite Tor dimension passes to smaller
opens (Stacks 09U8), both of which hold for the derived tensor product of Stacks 06YU. -/
theorem isTriangulated_isPseudoCoherentOfLocallyFiniteTorDimensionOver [LocallyOfFiniteType f] :
    f.isPseudoCoherentOfLocallyFiniteTorDimensionOver.IsTriangulated := by
  rw [isPseudoCoherentOfLocallyFiniteTorDimensionOver_eq]
  exact isTriangulated_isPseudoCoherentOfFiniteTorDimensionRelativeTo f _
    (fun _ F => RingedSpace.commShift_canonicalCertificate _ F)
    (fun _ F => RingedSpace.isTriangulated_canonicalCertificate _ F)
    (RingedSpace.finiteTorDimensionRestricts_canonicalFamily _)

/-- Condition (B) defines a saturated subcategory of `D(𝒪_X)`: a direct summand of an object
satisfying (B) satisfies (B). -/
theorem isSaturated_isPseudoCoherentOfLocallyFiniteTorDimensionOver [LocallyOfFiniteType f] :
    f.isPseudoCoherentOfLocallyFiniteTorDimensionOver.IsSaturated := by
  rw [isPseudoCoherentOfLocallyFiniteTorDimensionOver_eq]
  exact isSaturated_isPseudoCoherentOfFiniteTorDimensionRelativeTo f _

/-- **Condition (B) generalises Definition 0DI0.** For `f` flat and locally of finite
presentation, an object satisfies (B) exactly when it is `S`-perfect: pseudo-coherence relative
to `S` is pseudo-coherence (Stacks 0DII) and the Tor clauses are the same. -/
theorem isPseudoCoherentOfLocallyFiniteTorDimensionOver_iff_isRelativelyPerfect [Flat f]
    [LocallyOfFinitePresentation f] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.isPseudoCoherentOfLocallyFiniteTorDimensionOver E ↔ f.IsRelativelyPerfect E :=
  and_congr (isPseudoCoherent_iff_of_flat_of_locallyOfFinitePresentation f E) Iff.rfl

/-- **Stacks 0DI9.** Let `f : X ⟶ S` be a morphism of schemes.

1. If `f` is flat and locally of finite presentation (so that Definition 0DI0 applies), an object
   `E` of `D(𝒪_X)` is `S`-perfect exactly when it satisfies Lieblich's condition (A): locally on
   `X`, `E` is quasi-isomorphic to a finite complex of `S`-flat, finitely presented
   `𝒪_X`-modules.
2. If `f` is locally of finite type, condition (B) — `E` is pseudo-coherent relative to `S` and
   locally has finite Tor dimension as an object of `D(f⁻¹𝒪_S)` — defines a strictly full
   triangulated subcategory of `D(𝒪_X)`.
3. Condition (B) is the natural generalisation of Definition 0DI0: when `f` is flat and locally of
   finite presentation, (B) holds exactly for the `S`-perfect objects. -/
@[stacks 0DI9, sga "6 III 4.2" "(B)"]
theorem isRelativelyPerfect_iff_isLocallyBoundedFlatFinitePresentation_and_isTriangulated :
    (∀ [Flat f] [LocallyOfFinitePresentation f]
        (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)),
      f.IsRelativelyPerfect E ↔ f.IsLocallyBoundedFlatFinitePresentation E) ∧
    (∀ [LocallyOfFiniteType f],
      f.isPseudoCoherentOfLocallyFiniteTorDimensionOver.IsClosedUnderIsomorphisms ∧
        f.isPseudoCoherentOfLocallyFiniteTorDimensionOver.IsTriangulated) ∧
    (∀ [Flat f] [LocallyOfFinitePresentation f]
        (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)),
      f.isPseudoCoherentOfLocallyFiniteTorDimensionOver E ↔ f.IsRelativelyPerfect E) :=
  ⟨fun E => isRelativelyPerfect_iff_isLocallyBoundedFlatFinitePresentation f E,
    ⟨isClosedUnderIsomorphisms_isPseudoCoherentOfLocallyFiniteTorDimensionOver f,
      isTriangulated_isPseudoCoherentOfLocallyFiniteTorDimensionOver f⟩,
    fun E => isPseudoCoherentOfLocallyFiniteTorDimensionOver_iff_isRelativelyPerfect f E⟩

end AlgebraicGeometry.Scheme.Hom

end
