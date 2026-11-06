module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfRestrictionDetectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSmallEtaleEssImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# Étale-local descent of the essential image of `a⁻¹`

Let `a_X` be the comparison morphism from the big fppf topos of an algebraic space `X` to its
small étale topos (`AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleMorphism`, Stacks 0DGI).
For a surjective étale morphism `j : V ⟶ Y` of algebraic spaces, a big fppf sheaf `H` on `Y` lies
in the essential image of `a_Y⁻¹` as soon as `j_{big,fppf}⁻¹H` lies in that of `a_V⁻¹`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_of_isIso_fppfToSmallEtale_pushforward_map` — on the
  essential image of `a_X⁻¹`, `a_{X,*}` reflects isomorphisms.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_essImage_of_isEtale_of_liftingSieve` —
  the descent along an étale `j` such that the arrows whose source lifts through `j` cover every
  object of the big fppf site of `Y`.
* `AlgebraicGeometry.BigFppfSpaceSite.generate_singleton_mem_topology_of_isEtale` — a surjective
  étale morphism generates a covering sieve of the big fppf site.
* `AlgebraicGeometry.BigFppfSpaceSite.liftingSieve_mem_of_isEtale` — along a surjective étale `j`,
  the arrows whose source lifts through `j` cover every object of the big fppf site of `Y`.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_essImage_of_isEtale_of_isSurjective`
  — the étale-local descent.

## References

* [Stacks Project, Tag 0DGL](https://stacks.math.columbia.edu/tag/0DGL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- **`a_{V,*}` of a restriction along an étale `j : V ⟶ Y`, on sections.** If `a_{Y,*}φ` is an
isomorphism, then so is `a_{V,*}` of the restriction of `φ` along `j` on sections over every
object `U` of the spaces-étale site of `V`. -/
theorem isIso_fppfToSmallEtale_pushforward_map_overMap_app {V Y : T.Spaces} (j : V ⟶ Y)
    (het : Space.IsEtale T.schemeSite S T.scheme_mem j.hom)
    {K K' : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))} (φ : K ⟶ K')
    (hφ : IsIso ((fppfToSmallEtaleMorphism T E h Y).pushforward.map φ))
    (U : (Space.SpacesEtale E.fppfSite S E.fppf_mem (etaleSpace T E h V))ᵒᵖ) :
    IsIso (((fppfToSmallEtaleMorphism T E h V).pushforward.map
      (((Over.map j).sheafPushforwardContinuous (Type (u + 1))
        (BigFppfSpaceOver.topology T V) (BigFppfSpaceOver.topology T Y)).map φ)).hom.app U) := by
  have hφp : IsIso ((fppfToSmallEtaleMorphism T E h Y).pushforward.map φ).hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ (Type (u + 1))).map
      ((fppfToSmallEtaleMorphism T E h Y).pushforward.map φ)))
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    let W : Space.SpacesEtale T.schemeSite S T.scheme_mem Y :=
      ⟨Over.mk (U.unop.obj.hom ≫ j), Space.isEtale_comp _ _ _ U.unop.property het⟩
    exact (inferInstance : IsIso (((fppfToSmallEtaleMorphism T
      ⟨eSchemeSite, eSchemeMem, T.schemeSite, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
        eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
          rfl Y).pushforward.map φ).hom.app (op W)))

/-- **A morphism between sheaves in the essential image of `a_X⁻¹` is an isomorphism once its
image under `a_{X,*}` is.** -/
theorem isIso_of_isIso_fppfToSmallEtale_pushforward_map {X : T.Spaces}
    {K K' : Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1))} (φ : K ⟶ K')
    (hK : (fppfToSmallEtaleMorphism T E h X).inverseImage.essImage K)
    (hK' : (fppfToSmallEtaleMorphism T E h X).inverseImage.essImage K')
    (hφ : IsIso ((fppfToSmallEtaleMorphism T E h X).pushforward.map φ)) : IsIso φ := by
  let a := fppfToSmallEtaleMorphism T E h X
  have h₁ : IsIso (a.adj.counit.app K) := (a.adj.isIso_counit_app_iff_mem_essImage).2 hK
  have h₂ : IsIso (a.adj.counit.app K') := (a.adj.isIso_counit_app_iff_mem_essImage).2 hK'
  have hn : a.inverseImage.map (a.pushforward.map φ) ≫ a.adj.counit.app K' =
      a.adj.counit.app K ≫ φ := a.adj.counit.naturality φ
  have : IsIso (a.adj.counit.app K ≫ φ) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (a.adj.counit.app K) φ

/-- **Étale-local descent of the essential image of `a⁻¹`.** Let `j : V ⟶ Y` be an étale
morphism of algebraic spaces such that every object of the big fppf site of `Y` is covered by the
arrows into it whose source lifts through `j`, and let `H` be a big fppf sheaf on `Y` whose
inverse image `j_{big,fppf}⁻¹H` lies in the essential image of `a_V⁻¹`. Then `H` lies in the
essential image of `a_Y⁻¹`. -/
theorem fppfToSmallEtale_essImage_of_isEtale_of_liftingSieve {V Y : T.Spaces}
    (j : V ⟶ Y) (het : Space.IsEtale T.schemeSite S T.scheme_mem j.hom)
    (hcov : ∀ U : Over Y, liftingSieve T j U ∈ BigFppfSpaceOver.topology T Y U)
    {H : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))}
    (hH : (fppfToSmallEtaleMorphism T E h V).inverseImage.essImage
      ((bigFppfMorphism T j).inverseImage.obj H)) :
    (fppfToSmallEtaleMorphism T E h Y).inverseImage.essImage H := by
  let a := fppfToSmallEtaleMorphism T E h Y
  rw [← a.adj.isIso_counit_app_iff_mem_essImage]
  have hu := isIso_fppfToSmallEtaleMorphism_unit T E h Y
  have hε : IsIso (a.pushforward.map (a.adj.counit.app H)) := by
    have : IsIso (a.adj.unit.app (a.pushforward.obj H) ≫
        a.pushforward.map (a.adj.counit.app H)) := by
      rw [a.adj.right_triangle_components H]
      exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
    exact IsIso.of_isIso_comp_left (a.adj.unit.app _) _
  refine isIso_of_isIso_overMap_pushforward_map T j hcov _ ?_
  let ρ := (Over.map j).sheafPushforwardContinuous (Type (u + 1))
    (BigFppfSpaceOver.topology T V) (BigFppfSpaceOver.topology T Y)
  let ι := bigFppfMorphism_inverseImageIso T j
  refine isIso_of_isIso_fppfToSmallEtale_pushforward_map T E h (ρ.map (a.adj.counit.app H))
    (ObjectProperty.prop_of_iso _ (ι.app _)
      (fppfToSmallEtale_essImage_bigFppfInverseImage T E h j ⟨_, ⟨Iso.refl _⟩⟩))
    (ObjectProperty.prop_of_iso _ (ι.app H) hH) ?_
  have key := isIso_fppfToSmallEtale_pushforward_map_overMap_app T E h j het
    (a.adj.counit.app H) hε
  have : IsIso ((sheafToPresheaf _ (Type (u + 1))).map
      ((fppfToSmallEtaleMorphism T E h V).pushforward.map (ρ.map (a.adj.counit.app H)))) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ key
  exact isIso_of_fully_faithful (sheafToPresheaf _ (Type (u + 1))) _

/-- **A surjective étale morphism of algebraic spaces generates a covering sieve** of the big fppf
site. -/
theorem generate_singleton_mem_topology_of_isEtale {V Y : T.Spaces} (j : V ⟶ Y)
    (het : Space.IsEtale T.schemeSite S T.scheme_mem j.hom)
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem j.hom) :
    Sieve.generate (Presieve.singleton j) ∈ T.topology Y := by
  have hEt : Space.IsEtaleCoveringFamily T.schemeSite S T.scheme_mem
      ⟨Y, PreZeroHypercover.singleton j⟩ :=
    { target_isAlgebraicSpace := Y.property
      source_isAlgebraicSpace := fun _ => V.property
      etale := fun _ => het
      jointly_surjective := Set.eq_univ_of_forall fun x =>
        Set.mem_iUnion.2 ⟨PUnit.unit, hsurj x⟩ }
  obtain ⟨⟨Y₁, E₁⟩, hE₁, hU, hCE⟩ :=
    T.covering_representative _ (Space.isFppfCovering_of_isEtaleCovering _ _ _ hEt)
  change Y = Y₁ at hU
  subst hU
  have hpres := PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hCE
  have hpre : E₁.presieve₀ ∈ T.precoverage Y := ⟨E₁, rfl, hE₁⟩
  rw [← hpres, PreZeroHypercover.presieve₀_singleton] at hpre
  exact Precoverage.generate_mem_toGrothendieck hpre

/-- **Along a surjective étale morphism `j : V ⟶ Y`, every object of the big fppf site of `Y` is
covered by the arrows into it whose source lifts through `j`.** -/
theorem liftingSieve_mem_of_isEtale {V Y : T.Spaces} (j : V ⟶ Y)
    (het : Space.IsEtale T.schemeSite S T.scheme_mem j.hom)
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem j.hom) (U : Over Y) :
    liftingSieve T j U ∈ BigFppfSpaceOver.topology T Y U := by
  rw [GrothendieckTopology.mem_over_iff]
  refine T.topology.superset_covering ?_
    (T.topology.pullback_stable U.hom (generate_singleton_mem_topology_of_isEtale T j het hsurj))
  rintro W g ⟨Z, a, b, ⟨⟩, hab⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨a, hab⟩

/-- **Étale-local descent of the essential image of `a⁻¹`, along a surjective étale morphism.**
Let `j : V ⟶ Y` be a surjective étale morphism of algebraic spaces and `H` a big fppf sheaf on `Y`
whose inverse image `j_{big,fppf}⁻¹H` lies in the essential image of `a_V⁻¹`. Then `H` lies in
the essential image of `a_Y⁻¹`. -/
theorem fppfToSmallEtale_essImage_of_isEtale_of_isSurjective
    {V Y : T.Spaces} (j : V ⟶ Y) (het : Space.IsEtale T.schemeSite S T.scheme_mem j.hom)
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem j.hom)
    {H : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))}
    (hH : (fppfToSmallEtaleMorphism T E h V).inverseImage.essImage
      ((bigFppfMorphism T j).inverseImage.obj H)) :
    (fppfToSmallEtaleMorphism T E h Y).inverseImage.essImage H :=
  fppfToSmallEtale_essImage_of_isEtale_of_liftingSieve T E h j het
    (liftingSieve_mem_of_isEtale T j het hsurj) hH

end AlgebraicGeometry.BigFppfSpaceSite

end
