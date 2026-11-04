module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import StacksFrontier.AlgebraicGeometry.DenseDenominators.Algebra

/-!
# The relative spectrum of the algebra of denominators

The algebra of denominators of a finite algebra `S` over the sections on an open subset `Ω` of
a scheme `Y` is a presheaf of rings on the opens of `Y`. Granted that it localizes on basic
open subsets of affine opens — `Stacks.DenseDenominators.IsQcoh`, which is its quasi-coherence
in the form the relative gluing machinery of [Stacks, Tag 01LH] consumes — its relative
spectrum is a scheme `A` with a morphism to `Y` which is integral and surjective, and over an
affine open of `Ω` the chart of `A` is the spectrum of the whole base change, so it carries a
morphism to the spectrum of `S` over `Y`.

## Main results

* `Stacks.DenseDenominators.IsQcoh` is the quasi-coherence hypothesis.
* `Stacks.DenseDenominators.exists_integralHom_surjective_specSection` is the conclusion: a
  surjective integral morphism `a : A ⟶ Y` such that every point of `A` lying over a point of
  `Ω` has an affine open neighbourhood carrying a morphism to `Spec S` over `Y`.

## Implementation notes

The construction is `AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData` applied to
the structure morphism of the presheaf of denominator algebras, exactly as Mathlib's relative
normalization is built from the presheaf of integral closures. Integrality and surjectivity are
Zariski-local at the target, so they are read off the affine charts, where the morphism is the
spectrum of the structure morphism of the algebra of denominators — integral by
`Stacks.DenseDenominators.isIntegral_sub` and surjective because that morphism is injective.

No sheaf of algebras and no relative spectrum in the sense of [Stacks, Tag 01LP] is needed: the
gluing datum takes a presheaf and a natural transformation and asks only for the localization
property, which is why the construction can be carried out for a subring of a base change that
is not quasi-coherent itself.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.FiniteAlgebraPresentation TensorProduct

universe u

namespace Stacks.DenseDenominators

variable {Y : Scheme.{u}} {Ω : Y.Opens} {S : Type u} [CommRing S] [Algebra Γ(Y, Ω) S]

attribute [local instance] algebraInf algebraSub

variable (P : Presentation Γ(Y, Ω) S)

/-- **Quasi-coherence of the algebra of denominators**, in the form the relative gluing
machinery consumes: on the basic open subset of a section over an affine open, the algebra is
the corresponding localization. -/
def IsQcoh : Prop :=
  ∀ (U : Y.Opens) (_ : IsAffineOpen U) (r : Γ(Y, U)),
    letI := (subRes P (Y.basicOpen_le r)).toAlgebra
    IsLocalization.Away (toSub P U r) (sub P (Y.basicOpen r))

/-! ### The presheaf of denominator algebras -/

/-- The presheaf of rings `W ↦ 𝒪(W) + ℐ(W)·β₁ + ⋯ + ℐ(W)·βₙ` on the opens of `Y`. -/
def subPresheaf : Y.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj W := CommRingCat.of (sub P W.unop)
  map {_ _} i := CommRingCat.ofHom (subRes P (leOfHom i.unop))
  map_id _ := CommRingCat.hom_ext (RingHom.ext fun _ => Subtype.ext (ambRes_self Ω S _))
  map_comp {_ _ _} i j := CommRingCat.hom_ext (RingHom.ext fun _ =>
    Subtype.ext (ambRes_ambRes Ω S (leOfHom i.unop) (leOfHom j.unop) _).symm)

/-- The structure morphism `𝒪_Y ⟶ 𝒜` of the presheaf of denominator algebras. -/
def subStructureMap : Y.presheaf ⟶ subPresheaf P where
  app W := CommRingCat.ofHom (toSub P W.unop)
  naturality {_ _} i := CommRingCat.hom_ext (RingHom.ext fun u =>
    (subRes_toSub P (leOfHom i.unop) u).symm)

/-- The structure morphism of the presheaf of denominator algebras, restricted to the small
affine Zariski site of `Y`. -/
abbrev subAffineStructureMap :
    (Scheme.AffineZariskiSite.toOpensFunctor Y).op ⋙ Y.presheaf ⟶
      (Scheme.AffineZariskiSite.toOpensFunctor Y).op ⋙ subPresheaf P :=
  Functor.whiskerLeft _ (subStructureMap P)

/-- Under the quasi-coherence hypothesis, the structure morphism of the presheaf of denominator
algebras on the small affine Zariski site is coequifibered. -/
lemma coequifibered_subAffineStructureMap (hQ : IsQcoh P) :
    (subAffineStructureMap P).Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U r
  exact hQ U.1 U.2 r

/-- The relative gluing datum of the algebra of denominators. -/
def subGluingData (hQ : IsQcoh P) :
    (Scheme.AffineZariskiSite.directedCover Y).RelativeGluingData :=
  Scheme.AffineZariskiSite.relativeGluingData (coequifibered_subAffineStructureMap P hQ)

/-- The diagram of charts of the relative gluing datum is locally directed. -/
instance (hQ : IsQcoh P) :
    (((subGluingData P hQ).functor ⋙ Scheme.forget)).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The relative spectrum of the algebra of denominators. -/
def subSpec (hQ : IsQcoh P) : Scheme.{u} := (subGluingData P hQ).glued

/-- The structure morphism of the relative spectrum of the algebra of denominators. -/
def subSpecToBase (hQ : IsQcoh P) : subSpec P hQ ⟶ Y := (subGluingData P hQ).toBase

/-- The chart of the relative spectrum over an affine open of the base. -/
def subChart (hQ : IsQcoh P) (U : Y.AffineZariskiSite) :
    Spec ((subPresheaf P).obj (op U.1)) ⟶ subSpec P hQ :=
  colimit.ι (subGluingData P hQ).functor U

/-- The chart over an affine open `U` followed by the structure morphism is the spectrum of the
structure morphism over `U` followed by the inclusion `Spec Γ(Y, U) ⟶ Y`. -/
lemma subChart_comp_toBase (hQ : IsQcoh P) (U : Y.AffineZariskiSite) :
    subChart P hQ U ≫ subSpecToBase P hQ
      = Spec.map ((subStructureMap P).app (op U.1)) ≫ U.2.fromSpec := by
  refine ((subGluingData P hQ).ι_toBase U).trans ?_
  rw [IsAffineOpen.fromSpec, ← Category.assoc]
  rfl

/-- The charts of the relative spectrum are open immersions. -/
instance isOpenImmersion_subChart (hQ : IsQcoh P) (U : Y.AffineZariskiSite) :
    IsOpenImmersion (subChart P hQ U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (subGluingData P hQ).functor U))

/-- The image of the chart over an affine open `U` is the preimage of `U` under the structure
morphism. -/
lemma opensRange_subChart (hQ : IsQcoh P) (U : Y.AffineZariskiSite) :
    (subChart P hQ U).opensRange = subSpecToBase P hQ ⁻¹ᵁ U.1 :=
  ((subGluingData P hQ).toBase_preimage_eq_opensRange_ι U).symm.trans
    (congrArg _ (Scheme.Opens.opensRange_ι U.1))

/-! ### Integrality and surjectivity -/

/-- Transfer of a property respecting isomorphisms from an arbitrary cartesian square to the
canonical pullback of the same cospan. -/
lemma prop_pullback_snd_of_isPullback {P' : MorphismProperty Scheme.{u}} [P'.RespectsIso]
    {A B C D : Scheme.{u}} {p : A ⟶ B} {q : A ⟶ C} {g : B ⟶ D} {f : C ⟶ D}
    (h : IsPullback p q g f) (hq : P' q) : P' (pullback.snd g f) := by
  have he : pullback.snd g f = h.isoPullback.inv ≫ q :=
    (Iso.eq_inv_comp _).mpr h.isoPullback_hom_snd
  rw [he, P'.cancel_left_of_respectsIso]
  exact hq

/-- The relative spectrum of the algebra of denominators is integral over `Y`. -/
instance isIntegralHom_subSpecToBase (hQ : IsQcoh P) : IsIntegralHom (subSpecToBase P hQ) := by
  have hzl : IsZariskiLocalAtTarget @IsIntegralHom :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  have hri : MorphismProperty.RespectsIso @IsIntegralHom :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f hf =>
      have : IsIso f := hf
      inferInstance
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom)
    (Scheme.AffineZariskiSite.directedCover Y)).mpr fun U => ?_
  refine prop_pullback_snd_of_isPullback
    ((subGluingData P hQ).isPullback_natTrans_ι_toBase U).flip ?_
  have h1 : IsIntegralHom (Spec.map ((subStructureMap P).app (op U.1))) :=
    IsIntegralHom.SpecMap_iff.mpr fun γ => isIntegral_sub P γ
  change IsIntegralHom (Spec.map ((subStructureMap P).app (op U.1)) ≫ U.2.isoSpec.inv)
  infer_instance

/-- If `Y` is reduced, `Ω` is dense and `φ` is a `Γ(Y, Ω)`-linear form on `S` with `φ 1 = 1`, the
structure morphism of the relative spectrum of the algebra of denominators is surjective. -/
theorem surjective_subSpecToBase [IsReduced Y] (hΩ : Dense (Ω : Set Y))
    (φ : S →ₗ[Γ(Y, Ω)] Γ(Y, Ω)) (hφ : φ 1 = 1) (hQ : IsQcoh P) :
    Surjective (subSpecToBase P hQ) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @Surjective)
    (Scheme.AffineZariskiSite.directedCover Y)).mpr fun U => ?_
  refine prop_pullback_snd_of_isPullback
    ((subGluingData P hQ).isPullback_natTrans_ι_toBase U).flip ?_
  have hint : Algebra.IsIntegral Γ(Y, U.1) (sub P U.1) :=
    ⟨fun γ => isIntegral_sub P γ⟩
  have hfaith : FaithfulSMul Γ(Y, U.1) (sub P U.1) := by
    refine (faithfulSMul_iff_algebraMap_injective Γ(Y, U.1) (sub P U.1)).mpr ?_
    rw [RingHom.algebraMap_toAlgebra]
    exact injective_toSub P hΩ U.1 φ hφ
  have h1 : Surjective (Spec.map ((subStructureMap P).app (op U.1))) :=
    ⟨Algebra.IsIntegral.comap_surjective Γ(Y, U.1) (sub P U.1)⟩
  show Surjective (Spec.map ((subStructureMap P).app (op U.1)) ≫ U.2.isoSpec.inv)
  infer_instance

/-! ### The morphism to the spectrum of `S` over an affine open of `Ω` -/

/-- Over an open subset of `Ω` the algebra of denominators contains the image of `S`. -/
lemma tmul_one_mem_sub {U : Y.Opens} (hUΩ : U ≤ Ω) (s : S) :
    (1 : Γ(Y, U ⊓ Ω)) ⊗ₜ[Γ(Y, Ω)] s ∈ sub P U := by
  rw [sub_eq_top P hUΩ]
  trivial

/-- The inclusion of `S` in the algebra of denominators over an open subset of `Ω`, where that
algebra is the whole base change. -/
def inclS {U : Y.Opens} (hUΩ : U ≤ Ω) : S →+* sub P U where
  toFun s := ⟨(1 : Γ(Y, U ⊓ Ω)) ⊗ₜ s, tmul_one_mem_sub P hUΩ s⟩
  map_one' := by
    refine Subtype.ext ?_
    change (1 : Γ(Y, U ⊓ Ω)) ⊗ₜ[Γ(Y, Ω)] (1 : S) = ((1 : sub P U) : amb Ω S U)
    rw [OneMemClass.coe_one, Algebra.TensorProduct.one_def]
  map_mul' s t := by
    refine Subtype.ext ?_
    change (1 : Γ(Y, U ⊓ Ω)) ⊗ₜ[Γ(Y, Ω)] (s * t)
      = ((⟨_, tmul_one_mem_sub P hUΩ s⟩ * ⟨_, tmul_one_mem_sub P hUΩ t⟩ : sub P U)
        : amb Ω S U)
    rw [Subring.coe_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_zero' := by
    refine Subtype.ext ?_
    change (1 : Γ(Y, U ⊓ Ω)) ⊗ₜ[Γ(Y, Ω)] (0 : S) = ((0 : sub P U) : amb Ω S U)
    rw [ZeroMemClass.coe_zero, tmul_zero]
  map_add' s t := by
    refine Subtype.ext ?_
    change (1 : Γ(Y, U ⊓ Ω)) ⊗ₜ[Γ(Y, Ω)] (s + t)
      = ((⟨_, tmul_one_mem_sub P hUΩ s⟩ + ⟨_, tmul_one_mem_sub P hUΩ t⟩ : sub P U)
        : amb Ω S U)
    rw [Subring.coe_add, tmul_add]

/-- On `Γ(Y, Ω)`, the inclusion of `S` is the restriction to `U` followed by the structure
morphism of the algebra of denominators. -/
lemma inclS_comp_algebraMap {U : Y.Opens} (hUΩ : U ≤ Ω) :
    (inclS P hUΩ).comp (algebraMap Γ(Y, Ω) S) = (toSub P U).comp (resHom hUΩ) := by
  refine RingHom.ext fun a => Subtype.ext ?_
  show (1 : Γ(Y, U ⊓ Ω)) ⊗ₜ[Γ(Y, Ω)] (algebraMap Γ(Y, Ω) S a)
    = resHom (inf_le_left : U ⊓ Ω ≤ U) (resHom hUΩ a) ⊗ₜ[Γ(Y, Ω)] (1 : S)
  rw [Algebra.algebraMap_eq_smul_one, tmul_smul, smul_tmul', smul_inf, mul_one, resHom_resHom]

/-- **The conclusion.** Granted the quasi-coherence of the algebra of denominators, there is a
surjective integral morphism `a : A ⟶ Y` such that every point of `A` lying over a point of `Ω`
has an affine open neighbourhood in `A` carrying a morphism to the spectrum of `S`, compatibly
over `Y`. -/
theorem exists_integralHom_surjective_specSection [IsReduced Y] (hΩd : Dense (Ω : Set Y))
    (φ : S →ₗ[Γ(Y, Ω)] Γ(Y, Ω)) (hφ : φ 1 = 1) (hQ : IsQcoh P) (hΩ : IsAffineOpen Ω) :
    ∃ (A : Scheme.{u}) (a : A ⟶ Y), IsIntegralHom a ∧ Surjective a ∧
      ∀ α : A, a.base α ∈ Ω → ∃ V : A.Opens, IsAffineOpen V ∧ α ∈ V ∧
        ∃ v : V.toScheme ⟶ Spec (CommRingCat.of S),
          v ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, Ω) S)) ≫ hΩ.fromSpec
            = V.ι ≫ a := by
  have hsurj := surjective_subSpecToBase P hΩd φ hφ hQ
  refine ⟨subSpec P hQ, subSpecToBase P hQ, inferInstance, hsurj, fun α hα => ?_⟩
  obtain ⟨-, ⟨U, hU0, rfl⟩, hαU, hUΩ⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hα Ω.isOpen
  have hU : IsAffineOpen U := hU0
  set US : Y.AffineZariskiSite := ⟨U, hU⟩ with hUS
  obtain ⟨z, hz⟩ : α ∈ Set.range (subChart P hQ US).base := by
    rw [← Scheme.Hom.coe_opensRange, opensRange_subChart]
    exact hαU
  have hiso := isOpenImmersion_subChart P hQ US
  refine ⟨(subChart P hQ US).opensRange, isAffineOpen_opensRange _, ⟨z, hz⟩,
    (subChart P hQ US).isoOpensRange.inv ≫
      Spec.map (CommRingCat.ofHom (inclS P hUΩ)), ?_⟩
  have hinv : (subChart P hQ US).isoOpensRange.inv ≫ subChart P hQ US
      = (subChart P hQ US).opensRange.ι :=
    (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι _).symm
  have hkey : Spec.map (CommRingCat.ofHom (inclS P hUΩ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, Ω) S)) ≫ hΩ.fromSpec
      = Spec.map (CommRingCat.ofHom (toSub P U)) ≫ hU.fromSpec := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      inclS_comp_algebraMap P hUΩ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      show CommRingCat.ofHom (resHom hUΩ) = Y.presheaf.map (homOfLE hUΩ).op from rfl,
      hΩ.map_fromSpec hU (homOfLE hUΩ).op]
  rw [Category.assoc]
  refine (congrArg _ hkey).trans ?_
  rw [← hinv, Category.assoc]
  exact congrArg _ (subChart_comp_toBase P hQ US).symm

end Stacks.DenseDenominators

end
