module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Reduced algebraic stacks are determined by their points (Stacks 050A)

A closed substack of a reduced algebraic stack over `S` whose set of points is all of the points
of the ambient stack is the whole stack.

## Main results

* `AlgebraicGeometry.Stack.prop_of_isReduced_fiber`: an object of a reduced scheme chart of the
  ambient stack lies in a closed substack which is surjective on points.
* `AlgebraicGeometry.Stack.eq_top_of_isClosedSubstack_of_isReducedStack`: **Stacks 050A**.

## Implementation notes

A closed substack is a strictly full subcategory cut out by an object property, so equality with
the ambient stack is equality of that property with `⊤`, and equality of the point sets is
surjectivity of the map on points induced by the inclusion, exactly as in
`AlgebraicGeometry.Stack.IsThickening`.

The proof is the source's, with the presentation replaced by a scheme chart. The inclusion is
representable by algebraic spaces and both a closed immersion and surjective in the relative
sense of Stacks 03YK — the second by Stacks 04XI — so its base change along the tautological
point of a chart `U` is an algebraic space over `U` whose structural morphism is a surjective
closed immersion. Basing that change again at the identity of `U` represents it by a closed
subscheme of `U` surjective onto `U`, which for reduced `U` is `U` itself
(`AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective`, Stacks 0356); the resulting
section of the structural morphism names an object of the substack isomorphic to the given one.
Every chart of a reduced algebraic stack is reduced by the scheme criteria of Stacks 04YF, and
the chart of the algebraic-stack condition is locally essentially surjective, so membership
spreads from the chart to every object: the substack property is inherited by domains of
cartesian morphisms, and it is local on the big fppf site by Stacks 04TU.

## References

* [Stacks Project, Tag 050A](https://stacks.math.columbia.edu/tag/050A)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A substack property is inherited by the domain of a morphism over the base.** Every
morphism of a category fibred in groupoids is strongly cartesian, and the full subcategory cut
out by the property is again fibred in groupoids, so a morphism to an object of the substack
identifies its domain with the corresponding pullback inside the substack. -/
theorem prop_of_isHomLift {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} [P.IsClosedUnderIsomorphisms]
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    {V U : BigFppfOver B S hS} {a x : 𝒳.val.val.obj} (k : V ⟶ U) (ζ : a ⟶ x)
    (hζ : 𝒳.val.val.p.IsHomLift k ζ) (hx : P x) :
    P a := by
  have hcod : 𝒳.val.val.p.obj x = U := by
    have := hζ
    exact IsHomLift.codomain_eq 𝒳.val.val.p k ζ
  obtain ⟨y, ρ, hρ⟩ := hP.choose.exists_lift k (⟨x, hx⟩ : P.FullSubcategory) hcod
  have hιρ : 𝒳.val.val.p.IsHomLift k ρ.hom :=
    PresheafOfCategories.isHomLift_map_of_comp (H := P.ι) (r := 𝒳.val.val.p) rfl k ρ hρ
  have h₁ : 𝒳.val.val.p.IsStronglyCartesian k ζ := by
    have := hζ
    exact 𝒳.val.property.isStronglyCartesian_homLift k ζ
  have h₂ : 𝒳.val.val.p.IsStronglyCartesian k ρ.hom := by
    have := hιρ
    exact 𝒳.val.property.isStronglyCartesian_homLift k ρ.hom
  have := h₁
  have := h₂
  exact P.prop_of_iso
    (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p k ζ ρ.hom) y.property

/-- **A morphism over an isomorphism of the site out of an object of a substack has its codomain
in the substack.** Every morphism of a category fibred in groupoids is strongly cartesian, so one
lying over an isomorphism is itself an isomorphism. -/
theorem prop_of_isHomLift_isIso {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} [P.IsClosedUnderIsomorphisms]
    {V U : BigFppfOver B S hS} {a x : 𝒳.val.val.obj} (k : V ⟶ U) (hk : IsIso k) (φ : a ⟶ x)
    (hφ : 𝒳.val.val.p.IsHomLift k φ) (ha : P a) :
    P x := by
  have := hφ
  have hcart : 𝒳.val.val.p.IsStronglyCartesian k φ :=
    𝒳.val.property.isStronglyCartesian_homLift k φ
  have := hcart
  have := hk
  have : IsIso φ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.val.p k φ
  exact P.prop_of_iso (asIso φ) ha

/-- **An object over a reduced chart lies in a closed substack with all the points.** Let `P` cut
out a closed substack of the algebraic stack `𝒳` over `S` whose inclusion is surjective on
points, in the relative sense of Stacks 03YK, and let `x` be an object of `𝒳` lying over an
object `U` of the big fppf site of `S` whose underlying scheme is reduced. Then `x` lies in the
substack.

The base change of the inclusion along the scheme-valued point named by `x` is an algebraic space
over `U` whose structural morphism is a surjective closed immersion; based again at the identity
of `U` it is a closed subscheme of `U` surjective onto it, hence all of `U` because `U` is
reduced, and the resulting section names an object of the substack isomorphic to `x`. -/
theorem prop_of_isReduced_fiber {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} [P.IsClosedUnderIsomorphisms]
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hrep : IsRepresentableByAlgebraicSpaces B S hS
      (fullSubcategoryInclusion 𝒳 P hP).hom.hom)
    (hci : Stack.IsClosedImmersion B S hS (fullSubcategoryInclusion 𝒳 P hP).hom)
    (hsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) (fullSubcategoryInclusion 𝒳 P hP).hom hrep)
    {U : BigFppfOver B S hS} (hU : IsReduced ((BigFppfOver.toScheme B S hS).obj U))
    (x : 𝒳.val.val.p.Fiber U) :
    P x.1 := by
  classical
  have hyc := fibrePoint_comp B S hS 𝒳.val U x
  obtain ⟨F, hF, e⟩ := hrep U (fibrePoint B S hS 𝒳.val U x) hyc
  have hciU := hci U (fibrePoint B S hS 𝒳.val U x) hyc F hF e
  have hsurjU := hsurj U (fibrePoint B S hS 𝒳.val U x) hyc F hF e
  set X : AlgebraicSpaces B U.left.1 U.left.2 := ⟨F, hF⟩
  set G := (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj X
  set h := (algebraicSpaceMap B S hS U G).hom
  have hhG : h = G.obj.hom := rfl
  -- The base change of the structural morphism along the tautological point of `U`.
  set g₀ : yoneda.obj (Over.mk U.hom) ⟶ yoneda.obj (Over.mk U.hom) := 𝟙 _ with hg₀
  set q := hciU.rep.snd g₀
  set pr := hciU.rep.fst g₀
  have hsq := hciU.rep.isPullback g₀
  have hprw : pr ≫ h = yoneda.map q := by simpa [hg₀] using hsq.w
  have hpriso : IsIso pr := hsq.isIso_fst_of_isIso
  -- It is a closed immersion of schemes, and it is surjective.
  have hqCI : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map q) :=
    hciU.property_snd g₀
  have hqSurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map q) := by
    refine ⟨Space.surjective_of_isSurjective_yonedaMap B S hS q ?_⟩
    rw [← hprw]
    exact Space.isSurjective_comp B S hS (Space.pointsMap_surjective_of_isIso B S hS pr) hsurjU
  -- A surjective closed immersion with reduced target is an isomorphism.
  have hUred : IsReduced ((BigFppfOver.toScheme B S hS).obj (Over.mk U.hom)) := hU
  have hqSchemeIso : IsIso ((BigFppfOver.toScheme B S hS).map q) := by
    have := hqCI
    have := hqSurj
    exact isIso_of_isClosedImmersion_of_surjective _
  have hqIso : IsIso q := by
    have h₁ : IsIso (B.inclusion.map ((BigFppfOver.forget B S hS).map q)) := hqSchemeIso
    have h₂ : IsIso ((BigFppfOver.forget B S hS).map q) := isIso_of_reflects_iso _ B.inclusion
    exact isIso_of_reflects_iso q (BigFppfOver.forget B S hS)
  -- Hence the structural morphism has a section over `U`.
  set s : yoneda.obj (Over.mk U.hom) ⟶ G.obj.left := yoneda.map (inv q) ≫ pr with hs
  have hsh : s ≫ G.obj.hom = 𝟙 _ := by
    rw [hs, ← hhG, Category.assoc, hprw, ← yoneda.map_comp, IsIso.inv_hom_id, yoneda.map_id]
  -- Read the section as a factorization through `U` together with a section of `F`.
  set I := spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom
  set t := (I.hom.app X).app (op (Over.mk U.hom)) (yonedaEquiv s) with ht
  have hm : yonedaEquiv (s ≫ G.obj.hom) = Over.homMk t.1.1 t.2 := by
    rw [yonedaEquiv_comp]
    have hround : (I.inv.app X).app (op (Over.mk U.hom)) t = yonedaEquiv s :=
      ((I.app X).app (op (Over.mk U.hom))).toEquiv.symm_apply_apply _
    rw [ht] at hround ⊢
    rw [← hround]
    exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS U.hom
      X (op (Over.mk U.hom)) _
  have ht1 : t.1.1 = 𝟙 U.left := by
    rw [hsh] at hm
    have hid : (yonedaEquiv (𝟙 (yoneda.obj (Over.mk U.hom)))) = 𝟙 (Over.mk U.hom) := by
      simpa using yonedaEquiv_yoneda_map (𝟙 (Over.mk U.hom))
    rw [hid] at hm
    exact (congrArg (fun k => Over.Hom.left k) hm).symm
  -- The section names a lift of `x` to the substack over an isomorphism of the site.
  obtain ⟨Pt, hPt, -⟩ := PresheafOfCategories.exists_sectionOfObj e.some
    (W := (Over.mk t.1.1 : BigFppfOver B U.left.1 U.left.2)) t.1.2
  obtain ⟨z, φ, hφ⟩ :=
    exists_lift_of_fst_obj B S hS (fullSubcategoryInclusion 𝒳 P hP).hom U x Pt hPt
  have hkIso : IsIso (Over.homMk (Over.mk t.1.1).hom rfl :
      (Over.mk ((Over.mk t.1.1).hom ≫ U.hom) : BigFppfOver B S hS) ⟶ U) := by
    have h₁ : IsIso ((BigFppfOver.forget B S hS).map
        (Over.homMk (Over.mk t.1.1).hom rfl :
          (Over.mk ((Over.mk t.1.1).hom ≫ U.hom) : BigFppfOver B S hS) ⟶ U)) := by
      show IsIso t.1.1
      rw [ht1]
      exact IsIso.id _
    exact isIso_of_reflects_iso _ (BigFppfOver.forget B S hS)
  exact prop_of_isHomLift_isIso B S hS _ hkIso φ hφ z.property

/-- **Stacks 050A.** Let `𝒳` be an algebraic stack over `S` and let `P` cut out a closed substack
of `𝒳`. If `𝒳` is reduced and the inclusion of the substack is surjective on points, then the
substack is the whole of `𝒳`.

Every scheme chart of a reduced algebraic stack is reduced, and the chart supplied by the
algebraic-stack condition is locally essentially surjective; so
`AlgebraicGeometry.Stack.prop_of_isReduced_fiber` puts the image of the tautological object of
that chart in the substack, `AlgebraicGeometry.Stack.prop_of_isHomLift` puts the image of every
object of the chart there, and membership of a substack being local on the big fppf site puts
every object of `𝒳` there. -/
@[stacks 050A]
theorem eq_top_of_isClosedSubstack_of_isReducedStack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (P : ObjectProperty 𝒳.val.val.obj) (hclosed : IsClosedSubstack 𝒳 P)
    (hpoints : IsSurjective B S hS (fullSubcategoryInclusion 𝒳 P hclosed.2.choose))
    (hred : IsReducedStack B S hS 𝒳) :
    P = ⊤ := by
  classical
  have : P.IsClosedUnderIsomorphisms := hclosed.1
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.property.isFibered
  have hci := hclosed.2.choose_spec
  have hsurjrel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS)
      (fullSubcategoryInclusion 𝒳 P hclosed.2.choose).hom hci.1 :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
      (fullSubcategoryInclusion 𝒳 P hclosed.2.choose) hci.1).mp hpoints
  -- The chart of the algebraic-stack condition.
  obtain ⟨hfib, hstacks, hdiag, U, atl, hatlrep, hatlprop⟩ := 𝒳.property
  have hsmooth : AlgebraicStacks.IsSmooth B S hS
      (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom atl) :
        schemeStack.{u, w} B S hS U ⟶ 𝒳) :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hatlrep
      (fun V y hy G hG he => (hatlprop V y hy G hG he).2)
  -- It is reduced, because the stack is.
  have hUred : IsReduced ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_scheme_atlas_iff_forall_scheme B S hS (fun Y : Scheme.{u} => IsReduced Y) 𝒳).1
      hred U _ hsmooth
  -- The image of the tautological object of the chart lies in the substack.
  have hatl0 : P (atl.obj (Over.mk (𝟙 U))) :=
    prop_of_isReduced_fiber B S hS hclosed.2.choose hci.1 hci.2 hsurjrel hUred
      ⟨atl.obj (Over.mk (𝟙 U)), atl.w_obj (Over.mk (𝟙 U))⟩
  -- Hence so does the image of every object of the chart.
  have hall : ∀ z : (schemeFibredCategory B S hS U).val.obj, P (atl.obj z) := by
    intro z
    have hcomm : z.hom ≫ (Over.mk (𝟙 U) : Over U).hom = z.hom := by simp
    set ψ : z ⟶ (Over.mk (𝟙 U) : Over U) := Over.homMk z.hom hcomm with hψ
    have hρ : (schemeFibredCategory B S hS U).val.p.IsHomLift z.hom ψ :=
      IsHomLift.of_fac _ z.hom ψ rfl rfl (by simp only [hψ]; rfl)
    refine prop_of_isHomLift B S hS hclosed.2.choose z.hom (atl.toFunctor.map ψ) ?_ hatl0
    exact PresheafOfCategories.isHomLift_map_of_comp atl.w z.hom ψ hρ
  -- Membership of the substack is local on the site, and the chart is locally essentially
  -- surjective.
  have hfinal : ∀ a : 𝒳.val.val.obj, P a := by
    intro a
    obtain ⟨R, hR, hloc⟩ := localEssSurj_of_isSurjective_isSmooth B S hS
      (Bicategory.InducedBicategory.mkHom atl) hatlrep hatlprop
      (𝒳.val.val.p.obj a) ⟨a, rfl⟩
    refine prop_of_locally_isoOverId hclosed.2.choose ⟨a, rfl⟩ hR ?_
    intro V' k hk
    obtain ⟨z, φ, hφ⟩ := hloc hk
    have hcart : 𝒳.val.val.p.IsCartesian k φ := by
      have := hφ
      have := 𝒳.val.property.isStronglyCartesian_homLift k φ
      exact inferInstance
    exact Functor.isoOverId_pullbackFiber 𝒳.val.val.p P ⟨a, rfl⟩ k φ hcart (hall z)
  ext a
  exact iff_of_true (hfinal a) trivial

end AlgebraicGeometry.Stack

end
