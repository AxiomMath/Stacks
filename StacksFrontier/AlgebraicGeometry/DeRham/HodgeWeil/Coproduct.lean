module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Pullback
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.TotalCupPairingLaws
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice

/-!
# Hodge cohomology of a disjoint union

Axiom (A1) of Weil cohomology theories (Section 0FID) asks that `H^*(∅) = 0` and that for a
coproduct `X ⨿ Y` with coprojections `i` and `j` the map
`(i^*, j^*) : H^*(X ⨿ Y) ⟶ H^*(X) × H^*(Y)` be bijective. This file proves it for Hodge
cohomology (Remark 0FWE), at the level of the groups `H^q(X, Ω^p_{X/S})` and of the pullbacks
`Stacks.HodgeWeil.hodgePullback` along squares over the identity of the base `S`.

The reason is that cohomology of a sheaf on a disjoint union splits (compare the de Rham case,
Section 0FWC). Let `X = U ⊔ V` with `U` and `V` open and disjoint, with inclusions
`i_U : U ⟶ X` and `i_V : V ⟶ X`. Over every open `W` of `X`, a form on `W` is the pair of its
restrictions to `W ∩ U` and `W ∩ V`, and a form on `W ∩ U` is a form on the open subscheme `U`.
So the canonical maps of the inclusions make `Ω^p_{X/S}` the biproduct
`i_{U*}Ω^p_{U/S} ⊞ i_{V*}Ω^p_{V/S}` of sheaves of `f⁻¹𝒪_S`-modules. Cohomology is additive,
and since `U` and `V` are also closed, the direct images along their inclusions are exact, so
that `H^q(X, i_{U*}Ω^p_{U/S}) = H^q(U, Ω^p_{U/S})`. The coprojections of a coproduct of schemes
are open immersions onto complementary opens, which gives (A1) for coproducts; on an empty
scheme the open `⊤` is disjoint from itself, which gives `H^q(∅, Ω^p_{∅/S}) = 0`.

## Main results

* `Stacks.HodgeWeil.bijective_cohomologyPullback_prod`: for closed embeddings `h₁`, `h₂` of
  ringed spaces into `Z` and an isomorphism `K ⟶ h₁_*K₁ ⊞ h₂_*K₂`, the two pullbacks identify
  `H^n(Z, K)` with `H^n(Z₁, K₁) × H^n(Z₂, K₂)`.
* `Stacks.HodgeWeil.isIso_biprod_lift_formsSinglePushforward`: `Ω^p_{X/S}` is the biproduct of
  the direct images of the forms on two complementary opens.
* `Stacks.HodgeWeil.bijective_hodgePullback_prod_of_disjoint`: Hodge cohomology along a
  decomposition `X = U ⊔ V` into two open and closed pieces.
* `Stacks.HodgeWeil.subsingleton_hodgeCohomologyComponent_of_isEmpty`: the first half of axiom
  (A1), `H^q(∅, Ω^p_{∅/S}) = 0`.
* `Stacks.HodgeWeil.bijective_hodgePullback_prod_of_isColimit`: the second half of axiom (A1),
  for every colimit binary cofan of schemes over `S`.
* `Stacks.HodgeWeil.bijective_hodgePullback_of_isIso`: an isomorphism of `S`-schemes induces a
  bijection on Hodge cohomology.

## Implementation notes

The coproduct is any colimit `BinaryCofan` of schemes, as in
`Stacks.WeilCohomology.FirstChernClassData.CoproductAxiom`, and the coprojections are given
together with commutative squares over `𝟙 S`, the form in which the pullbacks of datum (D1)
are taken for schemes over `S`. Only decompositions into two pieces are stated; a finite
decomposition into open and closed pieces reduces to them by induction on the number of pieces,
which is how `Stacks.WeilCohomology.FirstChernClassData.bijective_pull_of_isOpenImmersion`
obtains it from axiom (A1).

## References

* [Stacks Project, Tag 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso restrictGlobal)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent)

universe u

namespace Stacks.HodgeWeil

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] HasDerivedCategory.standard

/-! ### Maps into binary biproducts -/

section Biproduct

/-- An additive functor to modules carries a morphism into a binary biproduct, followed by the
comparison of biproducts and the identification of a biproduct of modules with the product, to
the pair of its components. -/
theorem map_biprod_lift_comp_apply {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {R : Type u} [Ring R] (G : C ⥤ ModuleCat.{u} R)
    [G.PreservesZeroMorphisms] {A B₁ B₂ : C} [PreservesBinaryBiproduct B₁ B₂ G]
    (g₁ : A ⟶ B₁) (g₂ : A ⟶ B₂) (x : G.obj A) :
    (G.map (biprod.lift g₁ g₂) ≫ (G.mapBiprod B₁ B₂).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom).hom x = ((G.map g₁).hom x, (G.map g₂).hom x) := by
  have h₁ : (ModuleCat.biprodIsoProd (G.obj B₁) (G.obj B₂)).hom ≫
      ModuleCat.ofHom (LinearMap.fst R (G.obj B₁) (G.obj B₂)) = biprod.fst := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_fst, Iso.hom_inv_id_assoc]
  have h₂ : (ModuleCat.biprodIsoProd (G.obj B₁) (G.obj B₂)).hom ≫
      ModuleCat.ofHom (LinearMap.snd R (G.obj B₁) (G.obj B₂)) = biprod.snd := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_snd, Iso.hom_inv_id_assoc]
  have k₁ : G.map (biprod.lift g₁ g₂) ≫ (G.mapBiprod B₁ B₂).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom ≫
        ModuleCat.ofHom (LinearMap.fst R (G.obj B₁) (G.obj B₂)) =
        G.map g₁ := by
    rw [h₁, Functor.mapBiprod_hom, biprod.lift_fst, ← G.map_comp, biprod.lift_fst]
  have k₂ : G.map (biprod.lift g₁ g₂) ≫ (G.mapBiprod B₁ B₂).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom ≫
        ModuleCat.ofHom (LinearMap.snd R (G.obj B₁) (G.obj B₂)) =
        G.map g₂ := by
    rw [h₂, Functor.mapBiprod_hom, biprod.lift_snd, ← G.map_comp, biprod.lift_snd]
  exact Prod.ext (congrArg (fun φ => φ.hom x) k₁) (congrArg (fun φ => φ.hom x) k₂)

/-- **An additive functor to modules carries a decomposition into a biproduct to a product**: if
`biprod.lift g₁ g₂ : A ⟶ B₁ ⊞ B₂` is an isomorphism, then `x ↦ (G(g₁) x, G(g₂) x)` is a bijection
`G(A) ⟶ G(B₁) × G(B₂)`. -/
theorem bijective_map_prod_of_isIso_biprod_lift {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {R : Type u} [Ring R] (G : C ⥤ ModuleCat.{u} R) [G.Additive]
    {A B₁ B₂ : C} (g₁ : A ⟶ B₁) (g₂ : A ⟶ B₂) [IsIso (biprod.lift g₁ g₂)] :
    Function.Bijective fun x => ((G.map g₁).hom x, (G.map g₂).hom x) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts G
  let e := G.mapIso (asIso (biprod.lift g₁ g₂)) ≪≫ G.mapBiprod B₁ B₂ ≪≫
    ModuleCat.biprodIsoProd _ _
  have he : (fun x => ((G.map g₁).hom x, (G.map g₂).hom x)) = e.toLinearEquiv :=
    funext fun x => (map_biprod_lift_comp_apply G g₁ g₂ x).symm
  exact he ▸ e.toLinearEquiv.bijective

/-- A morphism of complexes into a binary biproduct is an isomorphism once its components into
the biproducts of the terms are. -/
theorem isIso_biprod_lift_of_isIso_f {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {ι : Type*} {c : ComplexShape ι} {A B₁ B₂ : HomologicalComplex C c}
    (φ₁ : A ⟶ B₁) (φ₂ : A ⟶ B₂) (h : ∀ n, IsIso (biprod.lift (φ₁.f n) (φ₂.f n))) :
    IsIso (biprod.lift φ₁ φ₂) := by
  have : ∀ n, IsIso ((biprod.lift φ₁ φ₂).f n) := fun n => by
    let G := HomologicalComplex.eval C c n
    have := preservesBinaryBiproducts_of_preservesBiproducts G
    have e : (biprod.lift φ₁ φ₂).f n =
        biprod.lift (φ₁.f n) (φ₂.f n) ≫ (G.mapBiprod B₁ B₂).inv :=
      (Iso.eq_comp_inv _).mpr (biprod.map_lift_mapBiprod G B₁ B₂ φ₁ φ₂)
    rw [e]
    have := h n
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **A morphism of sheaves of modules into a binary biproduct is an isomorphism once it is
bijective on sections**: if `x ↦ (g₁ x, g₂ x)` is a bijection `M(W) ⟶ N₁(W) × N₂(W)` for every
`W`, then `biprod.lift g₁ g₂ : M ⟶ N₁ ⊞ N₂` is an isomorphism. -/
theorem isIso_biprod_lift_of_bijective {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M N₁ N₂ : SheafOfModules.{u} R}
    (g₁ : M ⟶ N₁) (g₂ : M ⟶ N₂)
    (h : ∀ W : Cᵒᵖ, Function.Bijective fun x : M.val.obj W => (g₁.val.app W x, g₂.val.app W x)) :
    IsIso (biprod.lift g₁ g₂) := by
  refine Stacks.SheafOfModules.isIso_of_bijective_app _ fun W => ?_
  let G := _root_.SheafOfModules.evaluation R W
  have := preservesBinaryBiproducts_of_preservesBiproducts G
  let E := G.mapBiprod N₁ N₂ ≪≫ ModuleCat.biprodIsoProd _ _
  have hT : Function.Bijective (G.map (biprod.lift g₁ g₂) ≫ E.hom).hom := by
    have he : ⇑(G.map (biprod.lift g₁ g₂) ≫ E.hom).hom =
        fun x : M.val.obj W => (g₁.val.app W x, g₂.val.app W x) :=
      funext (map_biprod_lift_comp_apply G g₁ g₂)
    exact he ▸ h W
  have hb : Function.Bijective (G.map (biprod.lift g₁ g₂)).hom := by
    have : G.map (biprod.lift g₁ g₂) = (G.map (biprod.lift g₁ g₂) ≫ E.hom) ≫ E.inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [this, ModuleCat.hom_comp]
    exact E.symm.toLinearEquiv.bijective.comp hT
  exact hb

end Biproduct

/-! ### Cohomology along a decomposition into direct images -/

section General

variable {Z Z₁ Z₂ : RingedSpace.{u, u}} (h₁ : Z₁ ⟶ Z) (h₂ : Z₂ ⟶ Z)

/-- The pullback along a morphism of complexes `φ : K ⟶ h_*K'` is `H^n(RΓ(Z, φ))` followed by
`H^n(RΓ(Z, -))` of the comparison `h_*K' ⟶ Rh_*K'` and the Leray identification. -/
theorem cohomologyPullback_apply_comparison
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K₁ : CochainComplex (SheafOfModules.{u} (structureSheafRing Z₁)) ℤ}
    (φ : K ⟶ (pushforwardComplex h₁).obj K₁) (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyPullback h₁ φ n).hom x =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map
          (pushforwardComparisonQ h₁ K₁)) ≫
        (lerayCohomologyIso h₁ (DerivedCategory.Q.obj K₁) n).hom).hom
      (((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map
        (DerivedCategory.Q.map φ))).hom x) :=
  congrArg (lerayCohomologyIso h₁ (DerivedCategory.Q.obj K₁) n).hom
    (Stacks.Cohomology.HomologyPullback.map_map_comp_apply (baseSections Z)
      (DerivedCategory.homologyFunctor _ n) _ _ x)

/-- **Cohomology along a decomposition of a complex into direct images along two closed
embeddings**: if `h₁ : Z₁ ⟶ Z` and `h₂ : Z₂ ⟶ Z` are closed embeddings and
`biprod.lift φ₁ φ₂ : K ⟶ h₁_*K₁ ⊞ h₂_*K₂` is an isomorphism, the two pullbacks identify
`H^n(Z, K)` with `H^n(Z₁, K₁) × H^n(Z₂, K₂)`. -/
theorem bijective_cohomologyPullback_prod
    (hh₁ : Topology.IsClosedEmbedding (ConcreteCategory.hom h₁.hom.base))
    (hh₂ : Topology.IsClosedEmbedding (ConcreteCategory.hom h₂.hom.base))
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K₁ : CochainComplex (SheafOfModules.{u} (structureSheafRing Z₁)) ℤ}
    {K₂ : CochainComplex (SheafOfModules.{u} (structureSheafRing Z₂)) ℤ}
    (φ₁ : K ⟶ (pushforwardComplex h₁).obj K₁) (φ₂ : K ⟶ (pushforwardComplex h₂).obj K₂)
    [IsIso (biprod.lift φ₁ φ₂)] (n : ℤ) :
    Function.Bijective fun x : cohomologyModule (DerivedCategory.Q.obj K) n =>
      ((cohomologyPullback h₁ φ₁ n).hom x, (cohomologyPullback h₂ φ₂ n).hom x) := by
  have := Stacks.Cohomology.DerivedGlobalCupProduct.additive_baseSections Z
  let G : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ ⥤
      ModuleCat.{u} (baseRing Z) :=
    DerivedCategory.Q ⋙ baseSections Z ⋙ DerivedCategory.homologyFunctor _ n
  have := Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_pushforwardComparisonQ
    h₁ hh₁ K₁
  have := Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_pushforwardComparisonQ
    h₂ hh₂ K₂
  let E₁ := asIso ((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map
      (pushforwardComparisonQ h₁ K₁))) ≪≫ lerayCohomologyIso h₁ (DerivedCategory.Q.obj K₁) n
  let E₂ := asIso ((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map
      (pushforwardComparisonQ h₂ K₂))) ≪≫ lerayCohomologyIso h₂ (DerivedCategory.Q.obj K₂) n
  have he : (fun x : cohomologyModule (DerivedCategory.Q.obj K) n =>
      ((cohomologyPullback h₁ φ₁ n).hom x, (cohomologyPullback h₂ φ₂ n).hom x)) =
      Prod.map E₁.toLinearEquiv E₂.toLinearEquiv ∘
        fun x => ((G.map φ₁).hom x, (G.map φ₂).hom x) :=
    funext fun x => Prod.ext (cohomologyPullback_apply_comparison h₁ φ₁ n x)
      (cohomologyPullback_apply_comparison h₂ φ₂ n x)
  exact he ▸ (E₁.toLinearEquiv.bijective.prodMap E₂.toLinearEquiv.bijective).comp
    (bijective_map_prod_of_isIso_biprod_lift G φ₁ φ₂)

end General

/-! ### Sections along two disjoint opens -/

section Sections

/-- **Sections of a sheaf over a union of two disjoint opens are the pairs of sections**: if
`A ⊓ B = ⊥` and `A ⊔ B = W`, restriction `F(W) ⟶ F(A) × F(B)` is bijective. -/
theorem bijective_map_prod_of_disjoint {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {A B W : Opens X} (hAB : A ⊓ B = ⊥) (hW : A ⊔ B = W) (hA : A ≤ W) (hB : B ≤ W) :
    Function.Bijective fun x : F.obj.obj (op W) =>
      (F.obj.map (homOfLE hA).op x, F.obj.map (homOfLE hB).op x) := by
  subst hW
  let e := IsLimit.conePointUniqueUpToIso (F.isProductOfDisjoint A B hAB)
    (AddCommGrpCat.binaryProductLimitCone _ _).isLimit
  have h₁ := IsLimit.conePointUniqueUpToIso_hom_comp (F.isProductOfDisjoint A B hAB)
    (AddCommGrpCat.binaryProductLimitCone _ _).isLimit ⟨WalkingPair.left⟩
  have h₂ := IsLimit.conePointUniqueUpToIso_hom_comp (F.isProductOfDisjoint A B hAB)
    (AddCommGrpCat.binaryProductLimitCone _ _).isLimit ⟨WalkingPair.right⟩
  have he : (fun x : F.obj.obj (op (A ⊔ B)) =>
      (F.obj.map (homOfLE hA).op x, F.obj.map (homOfLE hB).op x)) = e.hom :=
    funext fun x => Prod.ext (ConcreteCategory.congr_hom h₁ x).symm
      (ConcreteCategory.congr_hom h₂ x).symm
  exact he ▸ ConcreteCategory.bijective_of_isIso e.hom

open Scheme.Hom in
/-- **Pulling back differential forms along an open immersion is bijective over the opens inside
its image**: the canonical map `ι^*Ω^d_{X/S} ⟶ Ω^d_{Y/S}` of the étale morphism `ι` is an
isomorphism (Tag 0FLV), and over `W ⊆ ι(Y)` the unit of `ι^* ⊣ ι_*` is the restriction of
sections to `ι(ι⁻¹W) = W`. -/
theorem bijective_relativeDifferentialFormsPullback_of_le_opensRange {X Y S : Scheme.{u}}
    (ι : Y ⟶ X) [IsOpenImmersion ι] (π : X ⟶ S) (π' : Y ⟶ S) (w : ι ≫ π = π' ≫ 𝟙 S) (d : ℤ)
    (W : X.Opens) (hW : W ≤ ι.opensRange) :
    Function.Bijective (relativeDifferentialFormsPullback ι π π' (𝟙 S) w d W) := by
  obtain rfl : π' = ι ≫ π := by simpa using w.symm
  have := isIso_relativeDifferentialFormsMap_of_etale ι π (ι ≫ π) (𝟙 S) w d
  have hmap : Function.Bijective (Scheme.Modules.Hom.app
      (relativeDifferentialFormsMap ι π (ι ≫ π) (𝟙 S) w d) (ι ⁻¹ᵁ W)) :=
    ConcreteCategory.bijective_of_isIso _
  have himg : ι ''ᵁ ι ⁻¹ᵁ W = W := by
    rwa [ι.image_preimage_eq_opensRange_inf, inf_eq_right]
  have hres : Function.Bijective ((relativeDifferentialForms π d).presheaf.map
      (homOfLE (ι.image_preimage_le W)).op) := by
    rw [show homOfLE (ι.image_preimage_le W) = eqToHom himg from Subsingleton.elim _ _,
      eqToHom_op]
    exact ConcreteCategory.bijective_of_isIso _
  have he : Function.Bijective (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback ι).inv.app
        (relativeDifferentialForms π d)) (ι ⁻¹ᵁ W)) :=
    ConcreteCategory.bijective_of_isIso _
  have hcomp : (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback ι).inv.app
      (relativeDifferentialForms π d)) (ι ⁻¹ᵁ W)) ∘
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ι (relativeDifferentialForms π d) W =
      (relativeDifferentialForms π d).presheaf.map (homOfLE (ι.image_preimage_le W)).op :=
    funext (Scheme.Modules.restrictFunctorIsoPullback_inv_unit ι _ W)
  have hunit : Function.Bijective
      (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ι (relativeDifferentialForms π d) W) :=
    (Function.Bijective.of_comp_iff' he _).mp (hcomp ▸ hres)
  exact hmap.comp hunit

open Scheme.Hom in
/-- **Differential forms along a decomposition into two disjoint opens**: if `U ⊓ V = ⊥` and
`U ⊔ V = ⊤`, pulling back along the two inclusions identifies the forms `Ω^d_{X/S}(W)` over any
open `W` with the pairs of forms on `U` over `U ∩ W` and on `V` over `V ∩ W`. -/
theorem bijective_relativeDifferentialFormsPullback_prod {X S : Scheme.{u}} (π : X ⟶ S)
    {U V : X.Opens} (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤) (d : ℤ) (W : X.Opens) :
    Function.Bijective fun ω : Γ(relativeDifferentialForms π d, W) =>
      (relativeDifferentialFormsPullback U.ι π (U.ι ≫ π) (𝟙 S) (Category.comp_id _).symm d W ω,
        relativeDifferentialFormsPullback V.ι π (V.ι ≫ π) (𝟙 S) (Category.comp_id _).symm d W
          ω) := by
  have hpre : ∀ T : X.Opens, T.ι ⁻¹ᵁ (W ⊓ T) = T.ι ⁻¹ᵁ W := fun T => by
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  have hR : ∀ T : X.Opens, Function.Bijective
      ((relativeDifferentialForms (T.ι ≫ π) d).presheaf.map
        (homOfLE (show T.ι ⁻¹ᵁ (W ⊓ T) ≤ T.ι ⁻¹ᵁ W from fun _ hz => hz.1)).op) := fun T => by
    rw [show homOfLE (show T.ι ⁻¹ᵁ (W ⊓ T) ≤ T.ι ⁻¹ᵁ W from fun _ hz => hz.1) =
      eqToHom (hpre T) from Subsingleton.elim _ _, eqToHom_op]
    exact ConcreteCategory.bijective_of_isIso _
  have hP : ∀ T : X.Opens, Function.Bijective (relativeDifferentialFormsPullback T.ι π
      (T.ι ≫ π) (𝟙 S) (Category.comp_id _).symm d (W ⊓ T)) := fun T =>
    bijective_relativeDifferentialFormsPullback_of_le_opensRange T.ι π (T.ι ≫ π)
      (Category.comp_id _).symm d (W ⊓ T) (by rw [Scheme.Opens.opensRange_ι]; exact inf_le_right)
  have hW : W ⊓ U ⊔ W ⊓ V = W := by rw [← inf_sup_left, hcov, inf_top_eq]
  have hUV : W ⊓ U ⊓ (W ⊓ V) = ⊥ := by rw [inf_inf_inf_comm, hdisj, inf_bot_eq]
  have hsplit := bijective_map_prod_of_disjoint
    (⟨(relativeDifferentialForms π d).presheaf, (relativeDifferentialForms π d).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} X) hUV hW inf_le_left inf_le_left
  have hcomp : Prod.map ((relativeDifferentialForms (U.ι ≫ π) d).presheaf.map
        (homOfLE (show U.ι ⁻¹ᵁ (W ⊓ U) ≤ U.ι ⁻¹ᵁ W from fun _ hz => hz.1)).op)
      ((relativeDifferentialForms (V.ι ≫ π) d).presheaf.map
        (homOfLE (show V.ι ⁻¹ᵁ (W ⊓ V) ≤ V.ι ⁻¹ᵁ W from fun _ hz => hz.1)).op) ∘
      (fun ω : Γ(relativeDifferentialForms π d, W) =>
        (relativeDifferentialFormsPullback U.ι π (U.ι ≫ π) (𝟙 S) (Category.comp_id _).symm d W ω,
          relativeDifferentialFormsPullback V.ι π (V.ι ≫ π) (𝟙 S) (Category.comp_id _).symm d W
            ω)) =
      Prod.map (relativeDifferentialFormsPullback U.ι π (U.ι ≫ π) (𝟙 S)
          (Category.comp_id _).symm d (W ⊓ U))
        (relativeDifferentialFormsPullback V.ι π (V.ι ≫ π) (𝟙 S)
          (Category.comp_id _).symm d (W ⊓ V)) ∘
      (fun ω : Γ(relativeDifferentialForms π d, W) =>
        ((relativeDifferentialForms π d).presheaf.map (homOfLE inf_le_left).op ω,
          (relativeDifferentialForms π d).presheaf.map (homOfLE inf_le_left).op ω)) :=
    funext fun ω => Prod.ext (relativeDifferentialFormsPullback_map U.ι π (U.ι ≫ π) (𝟙 S) _ d
        inf_le_left ω).symm
      (relativeDifferentialFormsPullback_map V.ι π (V.ι ≫ π) (𝟙 S) _ d inf_le_left ω).symm
  exact (Function.Bijective.of_comp_iff' ((hR U).prodMap (hR V)) _).mp
    (hcomp ▸ ((hP U).prodMap (hP V)).comp hsplit)

end Sections

/-! ### Hodge cohomology along a decomposition into two open and closed pieces -/

section Hodge

variable {Z S : Scheme.{u}} (f : Z ⟶ S)

/-- The sections of `Ω^p_{X/S}[0]` in a degree other than `0` vanish. -/
theorem subsingleton_formsSingle_X (p : ℕ) {n : ℤ} (hn : n ≠ 0)
    (W : (Opens Z.carrier)ᵒᵖ) : Subsingleton (((formsSingle f p).X n).val.obj W) := by
  have hZ : IsZero ((formsSingle f p).X n) :=
    HomologicalComplex.isZero_single_obj_X _ 0 _ n hn
  exact ModuleCat.isZero_iff_subsingleton.mp
    (((_root_.SheafOfModules.forget _) ⋙ PresheafOfModules.evaluation _ W).map_isZero hZ)

/-- **`Ω^p_{X/S}[0]` is the biproduct of the direct images of the forms on two complementary
opens**: for `U ⊓ V = ⊥` and `U ⊔ V = ⊤`, the canonical maps of the inclusions give an
isomorphism `Ω^p_{X/S}[0] ⟶ i_{U*}Ω^p_{U/S}[0] ⊞ i_{V*}Ω^p_{V/S}[0]`. -/
theorem isIso_biprod_lift_formsSinglePushforward {U V : Z.Opens} (hdisj : U ⊓ V = ⊥)
    (hcov : U ⊔ V = ⊤) (p : ℕ) :
    IsIso (biprod.lift
      (formsSinglePushforward U.ι (U.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm p)
      (formsSinglePushforward V.ι (V.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm p)) := by
  refine isIso_biprod_lift_of_isIso_f _ _ fun n => ?_
  refine isIso_biprod_lift_of_bijective _ _ fun W => ?_
  by_cases hn : n = 0
  · subst hn
    have he : (fun x : ((formsSingle f p).X 0).val.obj W =>
        (((formsSinglePushforward U.ι (U.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm p).f
          0).val.app W x,
        ((formsSinglePushforward V.ι (V.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm p).f
          0).val.app W x)) =
        fun ω => (Scheme.Hom.relativeDifferentialFormsPullback U.ι f (U.ι ≫ f) (𝟙 S)
            (Category.comp_id _).symm (p : ℤ) W.unop ω,
          Scheme.Hom.relativeDifferentialFormsPullback V.ι f (V.ι ≫ f) (𝟙 S)
            (Category.comp_id _).symm (p : ℤ) W.unop ω) :=
      funext fun x => Prod.ext (formsSinglePushforward_f_zero_val_app _ _ _ _ _ p W x)
        (formsSinglePushforward_f_zero_val_app _ _ _ _ _ p W x)
    exact he ▸ bijective_relativeDifferentialFormsPullback_prod f hdisj hcov p W.unop
  · have h₀ := subsingleton_formsSingle_X f p hn W
    have h₁ := subsingleton_pushforwardComplex_single_X
      (inverseImageBaseMap U.ι (U.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm)
      ((Scheme.Hom.deRhamComplex (U.ι ≫ f)).X p) hn W
    have h₂ := subsingleton_pushforwardComplex_single_X
      (inverseImageBaseMap V.ι (V.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm)
      ((Scheme.Hom.deRhamComplex (V.ι ≫ f)).X p) hn W
    exact ⟨fun _ _ _ => @Subsingleton.elim _ h₀ _ _,
      fun _ => ⟨0, Prod.ext (@Subsingleton.elim _ h₁ _ _) (@Subsingleton.elim _ h₂ _ _)⟩⟩

/-- **Hodge cohomology along a decomposition into two open and closed pieces**: if
`U ⊓ V = ⊥` and `U ⊔ V = ⊤`, the pullbacks along the inclusions identify `H^q(X, Ω^p_{X/S})`
with `H^q(U, Ω^p_{U/S}) × H^q(V, Ω^p_{V/S})`. -/
theorem bijective_hodgePullback_prod_of_disjoint {U V : Z.Opens} (hdisj : U ⊓ V = ⊥)
    (hcov : U ⊔ V = ⊤) (p : ℕ) (q : ℤ) :
    Function.Bijective fun x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q =>
      (hodgePullback U.ι (U.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm p q x,
        hodgePullback V.ι (V.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm p q x) := by
  have hc : ∀ {T T' : Z.Opens}, T ⊓ T' = ⊥ → T ⊔ T' = ⊤ → Topology.IsClosedEmbedding
      (ConcreteCategory.hom (inverseImageBaseMap T.ι (T.ι ≫ f) f (𝟙 S)
        (Category.comp_id _).symm).hom.base) := fun {T T'} h₁ h₂ => by
    have hT : (T : Set Z) = (T' : Set Z)ᶜ := by
      ext x
      refine ⟨fun hx hx' => ?_, fun hx => ?_⟩
      · have hm : x ∈ T ⊓ T' := ⟨hx, hx'⟩
        rwa [h₁] at hm
      · have hm : x ∈ T ⊔ T' := by
          rw [h₂]
          trivial
        exact (Opens.mem_sup.mp hm).resolve_right hx
    have hT' : Topology.IsClosedEmbedding T.ι.base := by
      refine ⟨T.ι.isOpenEmbedding.isEmbedding, ?_⟩
      rw [Scheme.Opens.range_ι, hT]
      exact T'.isOpen.isClosed_compl
    exact hT'
  have := isIso_biprod_lift_formsSinglePushforward f hdisj hcov p
  exact bijective_cohomologyPullback_prod
    (inverseImageBaseMap U.ι (U.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm)
    (inverseImageBaseMap V.ι (V.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm) (hc hdisj hcov)
    (hc (by rw [inf_comm, hdisj]) (by rw [sup_comm, hcov]))
    (formsSinglePushforward U.ι (U.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm p)
    (formsSinglePushforward V.ι (V.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm p) q

/-- **Hodge cohomology of the empty scheme vanishes**: `H^q(∅, Ω^p_{∅/S}) = 0`. On an empty
scheme the open `⊤` is disjoint from itself, so the diagonal `x ↦ (x|_⊤, x|_⊤)` is bijective,
which forces the group to be trivial. -/
theorem subsingleton_hodgeCohomologyComponent_of_isEmpty [IsEmpty Z] (p : ℕ) (q : ℤ) :
    Subsingleton (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) := by
  have hbot : (⊤ : Z.Opens) = ⊥ := Opens.ext (Set.eq_empty_of_isEmpty _)
  have h := bijective_hodgePullback_prod_of_disjoint f (U := ⊤) (V := ⊤)
    (by rw [inf_idem, hbot]) (sup_idem _) p q
  refine ⟨fun x y => h.1 (Prod.ext ?_ ?_)⟩
  all_goals
    obtain ⟨z, hz⟩ := h.2 (hodgePullback (⊤ : Z.Opens).ι ((⊤ : Z.Opens).ι ≫ f) f (𝟙 S)
      (Category.comp_id _).symm p q x, 0)
    obtain ⟨z', hz'⟩ := h.2 (hodgePullback (⊤ : Z.Opens).ι ((⊤ : Z.Opens).ι ≫ f) f (𝟙 S)
      (Category.comp_id _).symm p q y, 0)
    exact ((congrArg Prod.fst hz).symm.trans (congrArg Prod.snd hz)).trans
      ((congrArg Prod.fst hz').symm.trans (congrArg Prod.snd hz')).symm

end Hodge

/-! ### Isomorphisms and coproducts -/

section Coproduct

variable {X X' Y Z S : Scheme.{u}}

/-- The pullback on Hodge cohomology depends on the upper morphism of the square only through
the morphism itself. -/
theorem hodgePullback_congr {S' : Scheme.{u}} {g₁ g₂ : X' ⟶ X} (hg : g₁ = g₂) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (w₁ : g₁ ≫ f = f' ≫ g) (w₂ : g₂ ≫ f = f' ≫ g) (p : ℕ) (q : ℤ)
    (x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) :
    hodgePullback g₁ f' f g w₁ p q x = hodgePullback g₂ f' f g w₂ p q x := by
  subst hg
  rfl

/-- **An isomorphism of `S`-schemes induces a bijection on Hodge cohomology**: its pullback has
the pullback along the inverse as a two-sided inverse. -/
theorem bijective_hodgePullback_of_isIso (e : X' ⟶ X) [IsIso e] (fX : X ⟶ S) (fX' : X' ⟶ S)
    (w : e ≫ fX = fX' ≫ 𝟙 S) (p : ℕ) (q : ℤ) :
    Function.Bijective (hodgePullback e fX' fX (𝟙 S) w p q) := by
  have w' : inv e ≫ fX' = fX ≫ 𝟙 S := by
    rw [Category.comp_id, IsIso.inv_comp_eq, w, Category.comp_id]
  refine Function.bijective_iff_has_inverse.mpr
    ⟨hodgePullback (inv e) fX fX' (𝟙 S) w' p q, fun x => ?_, fun x => ?_⟩
  · rw [← hodgePullback_comp_overBase e fX fX' fX (inv e) w w' (by simp) p q x,
      hodgePullback_congr (IsIso.inv_hom_id e) fX fX (𝟙 S) _ (by simp)]
    exact hodgePullback_id fX _ p q x
  · rw [← hodgePullback_comp_overBase (inv e) fX' fX fX' e w' w (by simp) p q x,
      hodgePullback_congr (IsIso.hom_inv_id e) fX' fX' (𝟙 S) _ (by simp)]
    exact hodgePullback_id fX' _ p q x

/-- The pullback along an open immersion `i` is the pullback along the inclusion of its image
followed by a bijection (the pullback along the isomorphism onto the image). -/
private theorem exists_bijective_hodgePullback_eq_comp_opensRange (f : Z ⟶ S) (fX : X ⟶ S)
    (i : X ⟶ Z) [IsOpenImmersion i] (wi : i ≫ f = fX ≫ 𝟙 S) (p : ℕ) (q : ℤ) :
    ∃ e : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras (i.opensRange.ι ≫ f)) p q →
        hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras fX) p q, Function.Bijective e ∧
      ∀ x, hodgePullback i fX f (𝟙 S) wi p q x = e (hodgePullback i.opensRange.ι
        (i.opensRange.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm p q x) := by
  have wi' : i.isoOpensRange.hom ≫ (i.opensRange.ι ≫ f) = fX ≫ 𝟙 S := by
    rw [Scheme.Hom.isoOpensRange_hom_ι_assoc, wi]
  exact ⟨hodgePullback i.isoOpensRange.hom fX (i.opensRange.ι ≫ f) (𝟙 S) wi' p q,
    bijective_hodgePullback_of_isIso _ _ _ wi' p q, fun x =>
    (hodgePullback_congr (Scheme.Hom.isoOpensRange_hom_ι i).symm fX f (𝟙 S) wi
      (by rw [Category.assoc, wi']) p q x).trans
      (hodgePullback_comp_overBase i.opensRange.ι f (i.opensRange.ι ≫ f) fX
        i.isoOpensRange.hom (Category.comp_id _).symm wi' _ p q x)⟩

/-- **Hodge cohomology of a coproduct** (axiom (A1) of Weil cohomology theories, Section 0FID,
for Hodge cohomology): for a coproduct `Z = X ⨿ Y` of `S`-schemes with coprojections `i` and `j`,
`x ↦ (i^*x, j^*x)` identifies `H^q(Z, Ω^p_{Z/S})` with
`H^q(X, Ω^p_{X/S}) × H^q(Y, Ω^p_{Y/S})`. The coprojections are open immersions onto
complementary opens, and Hodge cohomology splits along such a decomposition. -/
theorem bijective_hodgePullback_prod_of_isColimit (f : Z ⟶ S) (fX : X ⟶ S) (fY : Y ⟶ S)
    (i : X ⟶ Z) (j : Y ⟶ Z) (hc : IsColimit (BinaryCofan.mk i j))
    (wi : i ≫ f = fX ≫ 𝟙 S) (wj : j ≫ f = fY ≫ 𝟙 S) (p : ℕ) (q : ℤ) :
    Function.Bijective fun x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q =>
      (hodgePullback i fX f (𝟙 S) wi p q x, hodgePullback j fY f (𝟙 S) wj p q x) := by
  let e := hc.coconePointUniqueUpToIso (coprodIsCoprod X Y)
  have hi : coprod.inl ≫ e.inv = i :=
    hc.comp_coconePointUniqueUpToIso_inv (coprodIsCoprod _ _) ⟨WalkingPair.left⟩
  have hj : coprod.inr ≫ e.inv = j :=
    hc.comp_coconePointUniqueUpToIso_inv (coprodIsCoprod _ _) ⟨WalkingPair.right⟩
  have hinl : IsOpenImmersion (coprod.inl : X ⟶ X ⨿ Y) := inferInstance
  have hinr : IsOpenImmersion (coprod.inr : Y ⟶ X ⨿ Y) := inferInstance
  have : IsOpenImmersion i := by
    rw [← hi]
    exact @IsOpenImmersion.comp _ _ _ _ e.inv hinl inferInstance
  have : IsOpenImmersion j := by
    rw [← hj]
    exact @IsOpenImmersion.comp _ _ _ _ e.inv hinr inferInstance
  have htop := (TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop.{u} _ _ hc⟩
  have hrange : IsCompl (Set.range i.base) (Set.range j.base) := htop.2.2
  have hdisj : i.opensRange ⊓ j.opensRange = ⊥ := by
    refine Opens.ext ?_
    rw [Opens.coe_inf, Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange, Opens.coe_bot]
    exact disjoint_iff.mp hrange.disjoint
  have hcov : i.opensRange ⊔ j.opensRange = ⊤ := by
    refine Opens.ext ?_
    rw [Opens.coe_sup, Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange, Opens.coe_top]
    exact codisjoint_iff.mp hrange.codisjoint
  have hsplit := bijective_hodgePullback_prod_of_disjoint f hdisj hcov p q
  obtain ⟨ei, hei, ki⟩ := exists_bijective_hodgePullback_eq_comp_opensRange f fX i wi p q
  obtain ⟨ej, hej, kj⟩ := exists_bijective_hodgePullback_eq_comp_opensRange f fY j wj p q
  have he : (fun x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q =>
      (hodgePullback i fX f (𝟙 S) wi p q x, hodgePullback j fY f (𝟙 S) wj p q x)) =
      Prod.map ei ej ∘
      fun x => (hodgePullback i.opensRange.ι (i.opensRange.ι ≫ f) f (𝟙 S)
          (Category.comp_id _).symm p q x,
        hodgePullback j.opensRange.ι (j.opensRange.ι ≫ f) f (𝟙 S) (Category.comp_id _).symm
          p q x) :=
    funext fun x => Prod.ext (ki x) (kj x)
  exact he ▸ (hei.prodMap hej).comp hsplit

end Coproduct

end Stacks.HodgeWeil

end
