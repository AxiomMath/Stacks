module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCechCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyComparison

/-! # Stacks 07AK: cohomology on a full subsite containing a presentation

Let `𝒳` be an algebraic stack over `S`, let `τ` be the étale (respectively fppf) topology, and let
`𝒳' ⊆ 𝒳` be a full subcategory such that

1. if `x ⟶ x'` is a morphism of `𝒳` lying over a smooth (respectively flat and locally finitely
   presented) morphism of schemes and `x'` is in `𝒳'`, then so is `x`, and
2. there is an object `x` of `𝒳'` lying over a scheme `U` whose 1-morphism `(Sch/U) ⟶ 𝒳` is
   smooth and surjective.

Give `𝒳'` the topology whose coverings are the families of `𝒳'` that are coverings of `𝒳_τ`.
Stacks 07AK asserts that the inclusion `𝒳' ⟶ 𝒳_τ` is fully faithful, continuous and cocontinuous,
so defines a morphism of topoi `g : Sh(𝒳'_τ) ⟶ Sh(𝒳_τ)`, and that

`H^p(𝒳'_τ, g⁻¹ℱ) = H^p(𝒳_τ, ℱ)`

for every `p ≥ 0` and every abelian sheaf `ℱ` on `𝒳_τ`. This file proves it.

## The proof

`AlgebraicGeometry.Stack.subsiteCohomologyIso` derives the comparison in every degree from two
inputs: the comparison `g_!ℤ ≅ ℤ` of constant sheaves, and the vanishing of the higher cohomology
of `g⁻¹ I` on `𝒳'_τ` for every injective abelian sheaf `I` on `𝒳_τ`. Both are supplied here by the
descent of `StacksFrontier/CategoryTheory/Sites/Cohomology/CoverDescent/Cohomology.lean`, applied to
the class `AlgebraicGeometry.Stack.SmoothOverAtlas` of presheaves on `𝒳` represented by algebraic
stacks smooth over the presentation `x`: it contains the final presheaf, it is closed under
representable covers by objects of `𝒳'`
(`AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_smoothOverAtlas`), and the restriction
of an injective abelian sheaf is acyclic over every object of `𝒳'`
(`AlgebraicGeometry.Stack.subsiteObjectCohomology_eq_zero`, Stacks 0D6X). At the final presheaf
the two conclusions of that descent are exactly the two inputs.

This is the source's proof with its spectral sequences replaced by dévissage along the free
abelian Čech resolutions they are built from: the covering `h_x ⟶ *` of the final presheaf and
the fibre powers `h_{x, n}` of the source are the first two levels of the representable covers
used, and the source's reduction of the fibre powers to algebraic spaces (Case II and III of its
proof) is replaced by the observation that their own representable covers again have fibre powers
represented by algebraic stacks smooth over `U`, so that the class above is closed under the
construction.

## Main results

* `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas`: **Stacks 07AK**, the natural
  isomorphism `H^p(𝒳'_τ, g⁻¹ℱ) ≅ H^p(𝒳_τ, ℱ)`.
* `AlgebraicGeometry.Stack.subsite_cohomology_comparison`: **Stacks 07AK** in full: the inclusion
  is fully faithful, continuous and cocontinuous, the inverse image of the morphism of topoi
  `AlgebraicGeometry.Stack.inclusionToposMorphism` it defines is restriction, and restriction
  preserves cohomology in every degree.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (τ : SiteKind) (P : ObjectProperty 𝒳.val.val.obj)

/-! ### The site-theoretic inputs -/

/-- Restriction of abelian presheaves along the inclusion of a full subsite of an algebraic stack
admits a left Kan extension: the full subsite is essentially small in the coefficient universe,
being a full subcategory of the site of `𝒳`, so the comma categories indexing the Kan extension
are. -/
theorem hasLeftKanExtension_subsite_ab :
    ∀ F : P.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}, P.ι.op.HasLeftKanExtension F := fun F => by
  have := FlatFppf.essentiallySmall_obj_coefficient.{u, w, u + 1} B S hS 𝒳
  have : EssentiallySmall.{u + 1} P.FullSubcategory :=
    essentiallySmall_of_fully_faithful.{u + 1} P.ι
  have : P.ι.op.HasPointwiseLeftKanExtension F := fun Y => by
    have := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow P.ι.op Y) AddCommGrpCat.{u + 1}
    infer_instance
  infer_instance

variable {𝒳 τ P}

/-- **The left adjoint `g_!` of restriction to the full subsite.** -/
theorem isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback
    (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
    (subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology τ) P).IsRightAdjoint := by
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  have := hasLeftKanExtension_subsite_ab 𝒳 P
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous P.ι AddCommGrpCat.{u + 1}
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P)
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))).isRightAdjoint

/-- **The covering-pullback condition of Stacks 00WV for the inclusion of the full subsite**, for
either of the two topologies admitted by Stacks 07AK. -/
theorem preservesCoveringPullbacks_of_isClosedUnderSitePullback
    (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ) :
    Stacks.Sites.PreservesCoveringPullbacks
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) P.ι := by
  rcases hcl with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact preservesCoveringPullbacks_ι_etaleTopology B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etalePrecoverage B)
      (map_mem_schemeEtalePrecoverage_of_mem_etalePrecoverage B) P fun _ _ f hf hy => h f hf hy
  · exact preservesCoveringPullbacks_ι_fppfTopology B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids P fun _ _ f hf hlfp hy => h f hf hlfp hy

/-- **The closure condition of Stacks 07AK (1) gives closure under isomorphisms**: a morphism of
`𝒳` lying over an identity lies over an isomorphism of schemes, which is smooth, flat and locally
of finite presentation. -/
theorem prop_of_isHomLift_id (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)
    {x y : 𝒳.val.val.obj} (f : x ⟶ y) (hf : 𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj y)) f)
    (hy : P y) : P x := by
  have hd : 𝒳.val.val.p.obj x = 𝒳.val.val.p.obj y :=
    IsHomLift.domain_eq 𝒳.val.val.p (𝟙 (𝒳.val.val.p.obj y)) f
  have hmap : 𝒳.val.val.p.map f = eqToHom hd := by
    rw [IsHomLift.fac' 𝒳.val.val.p (𝟙 (𝒳.val.val.p.obj y)) f]
    simp
  have hiso : IsIso (B.inclusion.map (𝒳.val.val.p.map f).left) := by
    rw [hmap, Over.eqToHom_left]
    infer_instance
  rcases hcl with ⟨-, h⟩ | ⟨-, h⟩
  · exact h f inferInstance hy
  · exact h f inferInstance inferInstance hy

/-- **Hypothesis (2) of Stacks 07AK**, in the form the proof uses: the distinguished object of the
1-morphism `(Sch/U) ⟶ 𝒳` named by an object `x` of the subcategory belongs to the subcategory,
being isomorphic to `x` over the identity of `U`. -/
theorem prop_objectMorphism_obj (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)
    {x : 𝒳.val.val.obj} (hx : P x) :
    P ((CatFiberedInGroupoids.homFunctor (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
          schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳).hom).obj
      (Over.mk (𝟙 (𝒳.val.val.p.obj x)))) := by
  let e := Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (𝒳.val.val.p.obj x) (Functor.Fiber.mk (a := x) rfl)
  refine prop_of_isHomLift_id hcl (Functor.Fiber.fiberInclusion.map e.hom) ?_ hx
  exact (e.hom).2

/-! ### The cohomology comparison -/

variable (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)
  (hatlas : ∃ x : 𝒳.val.val.obj, P x ∧
    AlgebraicStacks.IsSmooth B S hS (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
          schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳) ∧
    IsSurjective B S hS (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
          schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳))

include hatlas in
/-- **Stacks 07AK, the cohomology comparison.** Let `𝒳'` be a full subcategory of an algebraic
stack `𝒳` satisfying the two hypotheses of Stacks 07AK for `τ` the étale or the fppf topology.
For every degree `p`,

`H^p(𝒳'_τ, g⁻¹ℱ) ≅ H^p(𝒳_τ, ℱ)`,

naturally in the abelian sheaf `ℱ` on `𝒳_τ`, where `g⁻¹` is restriction to `𝒳'`.

The two inputs of `AlgebraicGeometry.Stack.subsiteCohomologyIso` are the two conclusions of
`Stacks.Sites.CoverDescent.restrictHom_bijective_of_mem` and
`Stacks.Sites.CoverDescent.ext_restriction_eq_zero_of_mem` at the final presheaf, for the class
`AlgebraicGeometry.Stack.SmoothOverAtlas` of the presentation given by hypothesis (2): the
comparison `g_!ℤ ≅ ℤ` is the first, through `Stacks.Sites.CoverDescent.isIso_freeComparison` and
the identification of the free abelian sheaf on the final presheaf with the constant sheaf, and the
acyclicity of restricted injectives is the second. -/
def subsiteCohomologyIsoOfAtlas (q : ℕ) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
    subsiteRestriction B S hS 𝒳.val.val.p (B.baseTopology τ) P ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1}
          (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) q ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) q :=
  haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  haveI := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  haveI := isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback hcl
  haveI := preservesCoveringPullbacks_of_isClosedUnderSitePullback hcl
  let x := hatlas.choose
  let a : schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))
  have h𝔎 := isClosedUnderRepresentableCovers_smoothOverAtlas a τ P hcl
    hatlas.choose_spec.2.1 hatlas.choose_spec.2.2
    (prop_objectMorphism_obj hcl hatlas.choose_spec.1)
  let F₀ := componentPresheaf (𝟭 𝒳.val.val.obj)
  have hF₀ : SmoothOverAtlas 𝒳 a F₀ := Or.inl rfl
  have := isIso_freeComparison.{u + 1, u, u + 1, u + 1}
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) P.ι F₀
    (fun F hF => restrictHom_bijective_of_mem.{u + 1, u, u + 1, u + 1} _ h𝔎 hF₀ F hF)
  let e₁ := freeAbelianSheafIsoConstantSheafOfUnique
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) (P.ι.op ⋙ F₀)
    (fun y => componentPresheafIdUnique (op (P.ι.obj y.unop)))
  let e₂ := freeAbelianSheafIsoConstantSheafOfUnique
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) F₀ componentPresheafIdUnique
  subsiteCohomologyIso B S hS 𝒳.val.val.p (B.baseTopology τ) P
    ((P.ι.sheafPullback AddCommGrpCat.{u + 1} _ _).mapIso e₁.symm ≪≫
      asIso (freeComparison.{u + 1, u, u + 1, u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
        (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) P.ι F₀) ≪≫ e₂)
    (fun I _ n b => Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_iso_first e₁.symm
      (n + 1) (fun c => ext_restriction_eq_zero_of_mem.{u + 1, u + 1, u, u + 1} h𝔎
        (fun I _ d m c => subsiteObjectCohomology_eq_zero B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids (B.baseTopology τ) P I d m c) hF₀ I n c) b) q

include hatlas in
/-- **Stacks 07AK.** Let `𝒳` be an algebraic stack over `S`, let `τ` be the étale or the fppf
topology, and let `𝒳' ⊆ 𝒳` be a full subcategory such that

1. if `x ⟶ x'` is a morphism of `𝒳` lying over a smooth (respectively flat and locally finitely
   presented) morphism of schemes and `x'` is in `𝒳'`, then `x` is in `𝒳'` — this is
   `AlgebraicGeometry.Stack.IsClosedUnderSitePullback`, which also pins `τ` down to one of the two
   admissible topologies; and
2. there is an object `x` of `𝒳'` lying over a scheme `U` whose associated 1-morphism
   `x : (Sch/U)_fppf ⟶ 𝒳` is smooth and surjective.

Give `𝒳'` the topology whose coverings are the families of `𝒳'` that are coverings of `𝒳_τ`. Then
the inclusion `𝒳' ⟶ 𝒳_τ` is fully faithful, continuous and cocontinuous, so it defines a morphism
of topoi `g : Sh(𝒳'_τ) ⟶ Sh(𝒳_τ)` — `AlgebraicGeometry.Stack.inclusionToposMorphism`, whose inverse
image is restriction to `𝒳'` — and `H^p(𝒳'_τ, g⁻¹ℱ) ≅ H^p(𝒳_τ, ℱ)` for all `p ≥ 0` and all abelian
sheaves `ℱ` on `𝒳_τ`, where on abelian sheaves `g⁻¹` is again restriction to `𝒳'`.

The isomorphism of cohomology groups is the natural isomorphism
`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas`. -/
@[stacks 07AK]
theorem subsite_cohomology_comparison :
    P.ι.Full ∧ P.ι.Faithful ∧
      P.ι.IsContinuous (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS
        𝒳.val.val.p τ)) (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) ∧
      P.ι.IsCocontinuous (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS
        𝒳.val.val.p τ)) (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) ∧
      (haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
          𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl;
        Nonempty ((inclusionToposMorphism B S hS 𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids
          hcl).inverseImage ≅ P.ι.sheafPushforwardContinuous (Type (u + 1))
            (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
            (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))) ∧
      ∀ q : ℕ,
        haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
          𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl;
        Nonempty (P.ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ))
            (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) ⋙
          Sheaf.functorH.{u + 1, u + 1, u, u + 1}
            (P.ι.inheritedTopology (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)) q ≅
          Sheaf.functorH.{u + 1, u + 1, u, u + 1}
            (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) q) :=
  ⟨inferInstance, inferInstance,
    isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl,
    isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl,
    ⟨inclusionToposMorphism_inverseImageIso B S hS 𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids
      hcl⟩,
    fun q => ⟨subsiteCohomologyIsoOfAtlas hcl hatlas q⟩⟩

end AlgebraicGeometry.Stack

end
