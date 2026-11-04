module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts

/-!
# Étale-local lifts along a surjective smooth morphism, by affine members

Along a 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids which is representable by
algebraic spaces and whose base changes along scheme-valued points are surjective and smooth,
every object `y` of `𝒴` over `U` lifts étale-locally on `U`
(part (2) of [Stacks Project, Tag 06XH]). This file records the covering in the form needed when
the members are to be manipulated further: an explicit family `e k : W k ⟶ U` of étale morphisms
of the site, jointly surjective, each of whose sources is **affine**, together with a lift of `y`
along `f` over each member.

## Main results

* `AlgebraicGeometry.exists_affine_etaleRefinement_of_smooth_surjective`: a smooth surjective
  morphism of the underlying category of a big fppf site is refined by a jointly surjective family
  of étale morphisms with affine sources.
* `AlgebraicGeometry.Stack.exists_affine_etale_family_lift_of_representable`: the family form of
  part (2) of Stacks 06XH with affine members.

## Implementation notes

The étale neighbourhoods of Tag 055V are shrunk to affine open neighbourhoods of their
distinguished points; these are quasi-compact, hence of size bounded by that of the base, hence
objects of the site.

## References

* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 055V](https://stacks.math.columbia.edu/tag/055V)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u v w

/-- **Stacks 055V with affine members.** A smooth surjective morphism `m : T ⟶ U` of the
underlying category of a big fppf site is refined by a jointly surjective family `e i : W i ⟶ U`
of étale morphisms whose sources are affine and each of which factors through `m`. -/
theorem exists_affine_etaleRefinement_of_smooth_surjective
    (B : BigFppfSite.{u}) {U T : B.Schemes} (m : T ⟶ U)
    (hsm : Smooth (B.inclusion.map m)) (hsurj : Surjective (B.inclusion.map m)) :
    ∃ (I : Type (u + 1)) (W : I → B.Schemes) (e : ∀ i, W i ⟶ U),
      (∀ i, Etale (B.inclusion.map (e i))) ∧ (∀ i, IsAffine (B.inclusion.obj (W i))) ∧
      (∀ x : B.inclusion.obj U, ∃ i, x ∈ Set.range (B.inclusion.map (e i))) ∧
      ∀ i, ∃ c : W i ⟶ T, c ≫ m = e i := by
  classical
  have := hsm
  have hdata (x : B.inclusion.obj U) :
      ∃ (X : Scheme.{u}) (_ : B.Contains X) (_ : IsAffine X) (e : X ⟶ B.inclusion.obj U),
        Etale e ∧ x ∈ Set.range e ∧ ∃ c : X ⟶ B.inclusion.obj T, c ≫ B.inclusion.map m = e := by
    obtain ⟨N, g, hg⟩ := exists_etaleNeighborhood_lift_of_smooth (B.inclusion.map m) x
      ((B.inclusion.map m).surjective x)
    obtain ⟨V, hV, hpV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := N.scheme) (x := N.point) (U := ⊤) trivial
    have : IsAffine V.toScheme := hV
    have hcontains : B.Contains V.toScheme :=
      (Scheme.size_le_of_locallyOfFiniteType (V.ι ≫ N.toBase)).trans_lt U.property
    exact ⟨V.toScheme, hcontains, hV, V.ι ≫ N.toBase, inferInstance,
      ⟨⟨N.point, hpV⟩, N.map_point⟩, V.ι ≫ g, by rw [Category.assoc, hg]⟩
  choose X hX hXa e he hmem c hc using hdata
  refine ⟨ULift.{u + 1} (B.inclusion.obj U), fun i => B.obj (hX i.down),
    fun i => ObjectProperty.homMk (e i.down), fun i => he i.down, fun i => hXa i.down,
    fun x => ⟨ULift.up x, hmem x⟩, fun i => ⟨ObjectProperty.homMk (c i.down), ?_⟩⟩
  exact ObjectProperty.hom_ext _ (hc i.down)

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 06XH, part (2), family form with affine members.** Along a 1-morphism
`f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S` which is representable
by algebraic spaces and whose base change along every scheme-valued point is surjective and smooth,
every object `y` of `𝒴` over `U` admits a jointly surjective family `e k : W k ⟶ U` of étale
morphisms of the site with affine sources, together with, for each member, an object of `𝒳` and a
morphism from its image to `y` lying over that member. -/
theorem exists_affine_etale_family_lift_of_representable
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U) :
    ∃ (I : Type (u + 1)) (W : I → BigFppfOver B S hS) (e : ∀ k, W k ⟶ U),
      (∀ k, Etale ((BigFppfOver.toScheme B S hS).map (e k))) ∧
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (W k))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj U,
        ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (e k))) ∧
      ∀ k, ∃ (x : 𝒳.val.obj) (α : (CatFiberedInGroupoids.homFunctor f).obj x ⟶ y.1),
        𝒴.val.p.IsHomLift (e k) α := by
  obtain ⟨T, m, hmsm, hmsurj, z, φ, hφ⟩ :=
    exists_scheme_lift_of_representable_isSurjective_isSmooth B S hS f hf hprop U y
  obtain ⟨I, W, e, hetale, haff, hjs, hfacs⟩ :=
    exists_affine_etaleRefinement_of_smooth_surjective B m hmsm hmsurj
  refine ⟨I, fun k => Over.mk (e k ≫ U.hom), fun k => Over.homMk (e k), hetale, haff, hjs, ?_⟩
  intro k
  obtain ⟨c, hc⟩ := hfacs k
  let b : (Over.mk (e k ≫ U.hom) : BigFppfOver B S hS) ⟶ Over.mk (m ≫ U.hom) :=
    Over.homMk c (by simp [← hc])
  have hb : b ≫ (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U)
      = (Over.homMk (e k) : (Over.mk (e k ≫ U.hom) : BigFppfOver B S hS) ⟶ U) :=
    Over.OverMorphism.ext (by simp [b, hc])
  have hw : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p := f.hom.w
  have hzbase : 𝒳.val.p.obj z = Over.mk (m ≫ U.hom) := by
    rw [← hw]
    exact IsHomLift.domain_eq 𝒴.val.p
      (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) φ
  obtain ⟨z', ρ, hρ⟩ := 𝒳.isFiberedInGroupoids.exists_lift b z hzbase
  refine ⟨z', (CatFiberedInGroupoids.homFunctor f).map ρ ≫ φ, ?_⟩
  show 𝒴.val.p.IsHomLift
    (Over.homMk (e k) : (Over.mk (e k ≫ U.hom) : BigFppfOver B S hS) ⟶ U) _
  rw [← hb]
  have h₁ : 𝒴.val.p.IsHomLift b ((CatFiberedInGroupoids.homFunctor f).map ρ) :=
    PresheafOfCategories.isHomLift_map_of_comp hw b ρ hρ
  exact IsHomLift.comp 𝒴.val.p b
    (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U)
    ((CatFiberedInGroupoids.homFunctor f).map ρ) φ

end Stack

end AlgebraicGeometry

end
