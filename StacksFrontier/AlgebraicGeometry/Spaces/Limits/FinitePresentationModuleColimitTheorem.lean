module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleEssSurj
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackSpanIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit

/-!
# Stacks 07V7: finitely presented modules on a limit of algebraic spaces

Let `X = lim X_i` be the limit of a cofiltered inverse system of quasi-compact and
quasi-separated algebraic spaces with affine transition morphisms (the setting of Stacks 07SK).
The category of finitely presented `𝒪_X`-modules is the colimit of the categories of finitely
presented `𝒪_{X_i}`-modules: the comparison functor, inverse image along the projections
`p_i : X ⟶ X_i`, is

* **faithful**: two morphisms of finitely presented modules on a stage whose inverse images to
  `X` agree already agree at a later stage;
* **full**: every morphism between the inverse images to `X` of two finitely presented modules on
  a stage is, at a later stage `j`, the inverse image of a morphism between their inverse images
  to `X_j`, through the canonical identification `p_j^* ∘ t^* = p_i^*` of iterated inverse
  images (`AlgebraicGeometry.Space.moduleHomRestrict`);
* **essentially surjective**: every finitely presented `𝒪_X`-module is the inverse image of a
  finitely presented module on some stage.

## Main results

* `AlgebraicGeometry.Space.finitePresentationModule_isColimit_of_isLimit_of_baseChangeLimits`:
  **Stacks 07V7**, the three clauses for any limiting cone over the system whose affine charts
  have their limits inside the site; its cone point is an algebraic space by
  `AlgebraicGeometry.Space.isAlgebraicSpace_conePt_of_isLimit` (Stacks 07SF).
* `AlgebraicGeometry.Space.finitePresentationModule_isColimit_of_isLimit`: the same three clauses
  with the cone point given as an algebraic space.
* `AlgebraicGeometry.Space.finitePresentationModule_isColimit_of_hasSiteLimit`: the same for the
  chosen limit `lim D` of presheaves.
* `AlgebraicGeometry.Space.finitePresentationModule_isColimit`: the case of an index category
  small compared to the cofinality of the cutoff, where the limit is formed by Stacks 07SF.

## Implementation notes

**The limit is given.** Situation 07SK fixes an inverse system and its limit `X`; the tagged
statement takes `X` as an algebraic space together with a cone over the system which is limiting
in presheaves on the big fppf site of `S` — equivalently in algebraic spaces, a full subcategory
containing the representables. No bound on the index category is imposed; it is any cofiltered
category in the universe of the site.

**The chapter's standing convention.** The limit is required to be the limit the source
constructs in the proof of Stacks 07SF: the limits, in schemes, of the affine charts
`X_j ×_{X_i} U` of the system lie in the site
(`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`). This is the convention of Section 70.2
(Stacks 07SD) under which the whole chapter, and so Stacks 07V7, is stated: every ring the chapter
considers has its spectrum in the big fppf site. Without it the statement is false in a
size-bounded site: the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartLimitsInSite.lean` give a directed system of
affine schemes of the site whose limit in the site is `S` itself while its limit in schemes is too
large for the site, and on which the faithfulness clause fails. The hypothesis is implied by the
size bound of `AlgebraicGeometry.Space.finitePresentationModule_isColimit` and by the bounded base
changes of Stacks 07SQ, and it holds for every cofiltered system of affine schemes whose limit in
schemes lies in the site, which is what Artin's Axioms, Definition 07XL quantifies over.

**From the chosen limit to a given one.** The three clauses are proved for the chosen limit
`lim D` of presheaves, under `AlgebraicGeometry.Space.HasSiteLimit`, and transported along the
isomorphism of the given limit with it: inverse image along an isomorphism of algebraic spaces is
faithful and its composite with the inverse image along the inverse isomorphism is the identity,
by Stacks 03LU.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

section HasSiteLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hL : HasSiteLimit B S hS D) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))

/-- **Stacks 07V7 for the chosen limit of presheaves.** For a cofiltered inverse system of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms whose limit
`lim D` is an algebraic space with the limits of the affine charts inside the site, inverse image
along the projections to the stages is faithful, full and essentially surjective in the colimit
sense. -/
theorem finitePresentationModule_isColimit_of_hasSiteLimit
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) :
    (∀ (i : I) (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite → ∀ φ ψ : M ⟶ N,
        (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).map φ =
          (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).map ψ →
        ∃ (j : I) (e : j ⟶ i),
          (modulePullback B S hS (stageTransition B S hS D hD e)).map φ =
            (modulePullback B S hS (stageTransition B S hS D hD e)).map ψ) ∧
    (∀ (i : I) (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite →
      ∀ φ : (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).obj M ⟶
        (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).obj N,
        ∃ (j : I) (e : j ⟶ i)
          (ψ : (modulePullback B S hS (stageTransition B S hS D hD e)).obj M ⟶
            (modulePullback B S hS (stageTransition B S hS D hD e)).obj N),
          moduleHomRestrict M N (limitSpaceProjection B S hS D hL hD j)
            (stageTransition B S hS D hD e) (limitSpaceProjection B S hS D hL hD i)
            (limitSpaceProjection_comp B S hS D hL hD e) ψ = φ) ∧
    (∀ P : Modules.{u, u} B S hS (limitSpace B S hS D hL).1 (limitSpace B S hS D hL).2,
      P.IsFinitePresentationOnSite →
        ∃ (k : I) (Q : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD k).1
            (stageAlgebraicSpace B S hS D hD k).2),
          Q.IsFinitePresentationOnSite ∧
            Nonempty (P ≅ (modulePullback B S hS (limitSpaceProjection B S hS D hL hD k)).obj Q)) :=
  ⟨fun i M N hM hN φ ψ h => eventually_eq_of_modulePullback_limitSpaceProjection_eq B S hS
      D hL hD i (hQc i) M N hM hN φ ψ h,
    fun i _ _ hM hN φ => exists_homRestrict_eq_limitProjection B S hS hZ D hL hD hQc hQs i hM hN φ,
    fun P hP => exists_iso_modulePullback_limitProjection B S hS hZ D hL hD hQc hQs P hP⟩

end HasSiteLimit

section GivenLimit

variable {I : Type u} [Category.{u} I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (c : Cone D) (hX : IsAlgebraicSpace B S hS c.pt)

/-- The projection of a given limit of the system to a stage, as a morphism of algebraic spaces
over `S`. -/
def coneProjection (i : I) :
    (⟨c.pt, hX⟩ : AlgebraicSpaces B S hS) ⟶ stageAlgebraicSpace B S hS D hD i :=
  ObjectProperty.homMk (c.π.app i)

/-- The projections of a given limit are compatible with the transition morphisms. -/
theorem coneProjection_comp {i j : I} (e : j ⟶ i) :
    coneProjection B S hS D hD c hX j ≫ stageTransition B S hS D hD e =
      coneProjection B S hS D hD c hX i :=
  ObjectProperty.hom_ext _ (c.w e)

/-- **Stacks 07V7.** Let `X = lim X_i` be the limit of a cofiltered inverse system of
quasi-compact and quasi-separated algebraic spaces over `S` with affine transition morphisms:
an algebraic space `X = c.pt` with a cone `c` over the system that is limiting in presheaves on
the big fppf site of `S`, whose affine charts `X_j ×_{X_i} U` have their limits, in schemes,
inside the site (the chapter's convention, Stacks 07SD, so that the limit `X` is the one
Stacks 07SF constructs). Then the category of finitely
presented `𝒪_X`-modules is the colimit of the categories of finitely presented
`𝒪_{X_i}`-modules: inverse image along the projections `X ⟶ X_i` is

1. faithful in the colimit sense: two morphisms on a stage with equal inverse images to `X` have
   equal inverse images to a later stage;
2. full in the colimit sense: a morphism between inverse images to `X` is, at a later stage, the
   restriction along `X ⟶ X_j` of a morphism between the inverse images to `X_j`;
3. essentially surjective in the colimit sense: every finitely presented `𝒪_X`-module is the
   inverse image of a finitely presented module on some stage.

The index category is any cofiltered category in the universe of the site; no size bound is
imposed on it. -/
theorem finitePresentationModule_isColimit_of_isLimit [IsCofiltered I]
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hc : IsLimit c) (hL : SiteContainsBaseChangeLimits B S hS D) :
    (∀ (i : I) (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite → ∀ φ ψ : M ⟶ N,
        (modulePullback B S hS (coneProjection B S hS D hD c hX i)).map φ =
          (modulePullback B S hS (coneProjection B S hS D hD c hX i)).map ψ →
        ∃ (j : I) (e : j ⟶ i),
          (modulePullback B S hS (stageTransition B S hS D hD e)).map φ =
            (modulePullback B S hS (stageTransition B S hS D hD e)).map ψ) ∧
    (∀ (i : I) (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite →
      ∀ φ : (modulePullback B S hS (coneProjection B S hS D hD c hX i)).obj M ⟶
        (modulePullback B S hS (coneProjection B S hS D hD c hX i)).obj N,
        ∃ (j : I) (e : j ⟶ i)
          (ψ : (modulePullback B S hS (stageTransition B S hS D hD e)).obj M ⟶
            (modulePullback B S hS (stageTransition B S hS D hD e)).obj N),
          moduleHomRestrict M N (coneProjection B S hS D hD c hX j)
            (stageTransition B S hS D hD e) (coneProjection B S hS D hD c hX i)
            (coneProjection_comp B S hS D hD c hX e) ψ = φ) ∧
    (∀ P : Modules.{u, u} B S hS c.pt hX, P.IsFinitePresentationOnSite →
        ∃ (k : I) (Q : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD k).1
            (stageAlgebraicSpace B S hS D hD k).2),
          Q.IsFinitePresentationOnSite ∧
            Nonempty (P ≅ (modulePullback B S hS (coneProjection B S hS D hD c hX k)).obj Q)) := by
  classical
  let iso₀ : c.pt ≅ limit D := hc.conePointUniqueUpToIso (limit.isLimit D)
  have hL₀ : HasSiteLimit B S hS D := ⟨hAffine, IsAlgebraicSpace.of_iso hX iso₀, hL⟩
  let e : (⟨c.pt, hX⟩ : AlgebraicSpaces B S hS) ≅ limitSpace B S hS D hL₀ :=
    ObjectProperty.isoMk _ iso₀
  have he : ∀ i, e.hom ≫ limitSpaceProjection B S hS D hL₀ hD i =
      coneProjection B S hS D hD c hX i := fun i =>
    ObjectProperty.hom_ext _ (hc.conePointUniqueUpToIso_hom_comp (limit.isLimit D) i)
  have he' : ∀ i, e.inv ≫ coneProjection B S hS D hD c hX i =
      limitSpaceProjection B S hS D hL₀ hD i := fun i =>
    ObjectProperty.hom_ext _ (hc.conePointUniqueUpToIso_inv_comp (limit.isLimit D) i)
  have hfaith := faithful_modulePullback_of_isIso e.hom
  have hfaith' := faithful_modulePullback_of_isIso e.inv
  obtain ⟨h₁, h₂, h₃⟩ :=
    finitePresentationModule_isColimit_of_hasSiteLimit B S hS hZ D hL₀ hD hQc hQs
  refine ⟨fun i M N hM hN φ ψ h => ?_, fun i M N hM hN φ => ?_, fun P hP => ?_⟩
  · refine h₁ i M N hM hN φ ψ ?_
    apply (modulePullback B S hS e.hom).map_injective
    apply map_map_eq_of_map_comp_eq B S hS
    rw [he i]
    exact h
  · obtain ⟨j, f, ψ, hψ⟩ := h₂ i M N hM hN
      (moduleHomRestrict M N e.inv (coneProjection B S hS D hD c hX i) _ (he' i) φ)
    refine ⟨j, f, ψ, ?_⟩
    apply moduleHomRestrict_injective e.inv (coneProjection B S hS D hD c hX i) _ (he' i)
    rw [moduleHomRestrict_homRestrict, ← hψ]
    exact moduleHomRestrict_congr (he' j) _ _ _ ψ
  · obtain ⟨k, Q, hQ, ⟨α⟩⟩ := h₃ ((modulePullback B S hS e.inv).obj P)
      (isFinitePresentationOnSite_modulePullback B S hS e.inv P hP)
    refine ⟨k, Q, hQ, ⟨?_⟩⟩
    let X : AlgebraicSpaces B S hS := ⟨c.pt, hX⟩
    let i₁ : P ≅ (modulePullback B S hS (𝟙 X)).obj P := ((modulePullbackIdIso B S hS X).app P).symm
    let i₂ : (modulePullback B S hS (𝟙 X)).obj P ≅
        (modulePullback B S hS (e.hom ≫ e.inv)).obj P :=
      eqToIso (by rw [e.hom_inv_id])
    let i₃ : (modulePullback B S hS (e.hom ≫ e.inv)).obj P ≅
        (modulePullback B S hS e.hom).obj ((modulePullback B S hS e.inv).obj P) :=
      ((modulePullbackCompIso B S hS e.hom e.inv).app P).symm
    let i₄ := (modulePullback B S hS e.hom).mapIso α
    let i₅ : (modulePullback B S hS e.hom).obj
          ((modulePullback B S hS (limitSpaceProjection B S hS D hL₀ hD k)).obj Q) ≅
        (modulePullback B S hS (e.hom ≫ limitSpaceProjection B S hS D hL₀ hD k)).obj Q :=
      (modulePullbackCompIso B S hS e.hom (limitSpaceProjection B S hS D hL₀ hD k)).app Q
    let i₆ : (modulePullback B S hS (e.hom ≫ limitSpaceProjection B S hS D hL₀ hD k)).obj Q ≅
        (modulePullback B S hS (coneProjection B S hS D hD c hX k)).obj Q :=
      eqToIso (by rw [he k])
    exact i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅ ≪≫ i₆

end GivenLimit

section ConeLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (c : Cone D)

include hD in
/-- **The limit of the system is an algebraic space** (Stacks 07SF under the convention 07SD):
the cone point of a limiting cone over a cofiltered inverse system of quasi-compact algebraic
spaces with affine transition morphisms whose affine charts have their limits in the site. -/
theorem isAlgebraicSpace_conePt_of_isLimit
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hc : IsLimit c) (hL : SiteContainsBaseChangeLimits B S hS D) :
    IsAlgebraicSpace B S hS c.pt :=
  (isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hL hD hAffine hQc).of_iso
    ((limit.isLimit D).conePointUniqueUpToIso hc)

/-- **Stacks 07V7.** Let `X = lim X_i` be the limit of a cofiltered inverse system of
quasi-compact and quasi-separated algebraic spaces over `S` with affine transition morphisms:
`X = c.pt` for a cone `c` over the system that is limiting in presheaves on the big fppf site of
`S`, the affine charts `X_j ×_{X_i} U` of the system having their limits, in schemes, inside the
site (the chapter's convention, Stacks 07SD). Then `X` is an algebraic space
(`AlgebraicGeometry.Space.isAlgebraicSpace_conePt_of_isLimit`, Stacks 07SF), and the category of
finitely presented `𝒪_X`-modules is the colimit of the categories of finitely presented
`𝒪_{X_i}`-modules: inverse image along the projections `X ⟶ X_i` is

1. faithful in the colimit sense: two morphisms on a stage with equal inverse images to `X` have
   equal inverse images to a later stage;
2. full in the colimit sense: a morphism between inverse images to `X` is, at a later stage, the
   restriction along `X ⟶ X_j` of a morphism between the inverse images to `X_j`;
3. essentially surjective in the colimit sense: every finitely presented `𝒪_X`-module is the
   inverse image of a finitely presented module on some stage.

The index category is any cofiltered category in the universe of the site. -/
@[stacks 07V7 "the category of finitely presented modules on the limit is the colimit of the \
categories of finitely presented modules on the stages: faithfulness, fullness through the \
canonical identification of iterated inverse images, and essential surjectivity of the comparison; \
for any limiting cone over the system, its cone point being an algebraic space by Stacks 07SF, \
indexed by any cofiltered category in the universe of the site, under the chapter's standing \
convention 07SD that the limits of its affine charts lie in the site; without that convention the \
statement fails in a size-bounded site (see the notes of ChartLimitsInSite)"]
theorem finitePresentationModule_isColimit_of_isLimit_of_baseChangeLimits
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hc : IsLimit c) (hL : SiteContainsBaseChangeLimits B S hS D) :
    let hX := isAlgebraicSpace_conePt_of_isLimit B S hS D hD c hAffine hQc hc hL
    (∀ (i : I) (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite → ∀ φ ψ : M ⟶ N,
        (modulePullback B S hS (coneProjection B S hS D hD c hX i)).map φ =
          (modulePullback B S hS (coneProjection B S hS D hD c hX i)).map ψ →
        ∃ (j : I) (e : j ⟶ i),
          (modulePullback B S hS (stageTransition B S hS D hD e)).map φ =
            (modulePullback B S hS (stageTransition B S hS D hD e)).map ψ) ∧
    (∀ (i : I) (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite →
      ∀ φ : (modulePullback B S hS (coneProjection B S hS D hD c hX i)).obj M ⟶
        (modulePullback B S hS (coneProjection B S hS D hD c hX i)).obj N,
        ∃ (j : I) (e : j ⟶ i)
          (ψ : (modulePullback B S hS (stageTransition B S hS D hD e)).obj M ⟶
            (modulePullback B S hS (stageTransition B S hS D hD e)).obj N),
          moduleHomRestrict M N (coneProjection B S hS D hD c hX j)
            (stageTransition B S hS D hD e) (coneProjection B S hS D hD c hX i)
            (coneProjection_comp B S hS D hD c hX e) ψ = φ) ∧
    (∀ P : Modules.{u, u} B S hS c.pt hX, P.IsFinitePresentationOnSite →
        ∃ (k : I) (Q : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD k).1
            (stageAlgebraicSpace B S hS D hD k).2),
          Q.IsFinitePresentationOnSite ∧
            Nonempty (P ≅ (modulePullback B S hS (coneProjection B S hS D hD c hX k)).obj Q)) :=
  finitePresentationModule_isColimit_of_isLimit B S hS hZ D hD c _ hAffine hQc hQs hc hL

end ConeLimit

/-- **Stacks 07V7 for an index category small compared to the cutoff.** For a cofiltered inverse
system of quasi-compact and quasi-separated algebraic spaces with affine transition morphisms,
indexed by a category whose object type and morphism types are smaller than the cofinality of the
site's cutoff, the category of finitely presented modules on the limit is the colimit of the
categories of finitely presented modules on the stages.

The size bound provides the limit as an algebraic space (Stacks 07SF) and keeps the limits of its
affine charts inside the site (`AlgebraicGeometry.Space.hasSiteLimit_of_lt_cof`); the limit space
`AlgebraicGeometry.Space.limitSpace` is then `AlgebraicGeometry.Space.limitAlgebraicSpace`
(`AlgebraicGeometry.Space.limitSpace_eq_limitAlgebraicSpace`). -/
theorem finitePresentationModule_isColimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hSize : #I < B.cutoff.ord.cof) (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) :
    let hL := hasSiteLimit_of_lt_cof B S hS D hD hSize hHomSize hAffine
    (∀ (i : I) (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite → ∀ φ ψ : M ⟶ N,
        (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).map φ =
          (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).map ψ →
        ∃ (j : I) (e : j ⟶ i),
          (modulePullback B S hS (stageTransition B S hS D hD e)).map φ =
            (modulePullback B S hS (stageTransition B S hS D hD e)).map ψ) ∧
    (∀ (i : I) (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
        (stageAlgebraicSpace B S hS D hD i).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite →
      ∀ φ : (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).obj M ⟶
        (modulePullback B S hS (limitSpaceProjection B S hS D hL hD i)).obj N,
        ∃ (j : I) (e : j ⟶ i)
          (ψ : (modulePullback B S hS (stageTransition B S hS D hD e)).obj M ⟶
            (modulePullback B S hS (stageTransition B S hS D hD e)).obj N),
          moduleHomRestrict M N (limitSpaceProjection B S hS D hL hD j)
            (stageTransition B S hS D hD e) (limitSpaceProjection B S hS D hL hD i)
            (limitSpaceProjection_comp B S hS D hL hD e) ψ = φ) ∧
    (∀ P : Modules.{u, u} B S hS (limitSpace B S hS D hL).1 (limitSpace B S hS D hL).2,
      P.IsFinitePresentationOnSite →
        ∃ (k : I) (Q : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD k).1
            (stageAlgebraicSpace B S hS D hD k).2),
          Q.IsFinitePresentationOnSite ∧
            Nonempty (P ≅ (modulePullback B S hS (limitSpaceProjection B S hS D hL hD k)).obj Q)) :=
  finitePresentationModule_isColimit_of_hasSiteLimit B S hS hZ D _ hD hQc hQs

end AlgebraicGeometry.Space

end
