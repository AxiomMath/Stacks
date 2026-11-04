module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesLocalChart
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesLocalCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteSpecAlgebra

/-!
# Set-up for the local step of Stacks 0CJV

Three inputs to the local step of Stacks 0CJV:

* a smooth surjective chart `b : U' ⟶ 𝒳'` has a base change `U = U' ×_{𝒳'} 𝒳` along a thickening
  which is at once smooth and surjective over `𝒳` and a monomorphism into `U'`;
* a point of a scheme of the site mapping to `U'` has an affine open neighbourhood mapping into
  an affine open of `U'`;
* a point of an algebraic space lies in the image of an étale morphism from an affine scheme of
  the site.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.BigFppfOver

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An open subscheme of an object of the site, as an object of the site. -/
noncomputable def openObj (T : BigFppfOver B S hS) (V : ((toScheme B S hS).obj T).Opens) :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (Scheme.size_lt_of_isOpenImmersion V.ι T.left.property)
    (V.ι ≫ B.inclusion.map T.hom)

/-- The inclusion of an open subscheme, as a morphism of the site. -/
noncomputable def openObjι (T : BigFppfOver B S hS) (V : ((toScheme B S hS).obj T).Opens) :
    openObj T V ⟶ T :=
  homOfCompEq B S hS V.ι rfl

/-- The underlying scheme morphism of `openObjι T V` is the open immersion `V.ι`. -/
theorem toScheme_map_openObjι (T : BigFppfOver B S hS) (V : ((toScheme B S hS).obj T).Opens) :
    (toScheme B S hS).map (openObjι T V) = V.ι :=
  toScheme_map_homOfCompEq B S hS _ _

/-- A point of an open subscheme lies in the range of the inclusion of that open subscheme. -/
private theorem mem_range_toScheme_map_openObjι (T : BigFppfOver B S hS)
    (V : ((toScheme B S hS).obj T).Opens) {y : (toScheme B S hS).obj T} (hy : y ∈ V) :
    y ∈ Set.range ((toScheme B S hS).map (openObjι T V)) := by
  refine ⟨(⟨y, hy⟩ : V.toScheme), ?_⟩
  rw [toScheme_map_openObjι]
  rfl

/-- The inclusion of an open subscheme is an open immersion of schemes. -/
private theorem isOpenImmersion_toScheme_map_openObjι (T : BigFppfOver B S hS)
    (V : ((toScheme B S hS).obj T).Opens) :
    IsOpenImmersion ((toScheme B S hS).map (openObjι T V)) := by
  rw [toScheme_map_openObjι]
  exact (inferInstance : IsOpenImmersion V.ι)

/-- **An affine neighbourhood of a point mapping into an affine open.** For a morphism
`ε : T ⟶ U'` of the site and a point `y` of `T`, there are affine opens `T₀ ⊆ T` around `y` and
`V ⊆ U'` with `ε (T₀) ⊆ V`. -/
theorem exists_affine_shrink {T U' : BigFppfOver B S hS} (ε : T ⟶ U')
    (y : (toScheme B S hS).obj T) :
    ∃ (V : BigFppfOver B S hS) (ιV : V ⟶ U') (T₀ : BigFppfOver B S hS) (m : T₀ ⟶ T)
      (ε₀ : T₀ ⟶ V),
      IsAffine ((toScheme B S hS).obj V) ∧ IsAffine ((toScheme B S hS).obj T₀) ∧
      IsOpenImmersion ((toScheme B S hS).map ιV) ∧ IsOpenImmersion ((toScheme B S hS).map m) ∧
      ε₀ ≫ ιV = m ≫ ε ∧ y ∈ Set.range ((toScheme B S hS).map m) := by
  set ε' := (toScheme B S hS).map ε
  obtain ⟨Vo, hVo, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (toScheme B S hS).obj U') (x := ε' y) (U := ⊤) trivial
  have hyW : y ∈ ε' ⁻¹ᵁ Vo := hyV
  obtain ⟨T₀o, hT₀o, hyT₀, hsub⟩ := exists_isAffineOpen_mem_and_subset hyW
  have hrange : Set.range (T₀o.ι ≫ ε') ⊆ Set.range Vo.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hsub (Scheme.Opens.range_ι T₀o ▸ ⟨z, rfl⟩ : T₀o.ι z ∈ (T₀o : Set _))
  let l : T₀o.toScheme ⟶ Vo.toScheme := IsOpenImmersion.lift Vo.ι (T₀o.ι ≫ ε') hrange
  have hl : l ≫ Vo.ι = T₀o.ι ≫ ε' := IsOpenImmersion.lift_fac _ _ _
  have hw : l ≫ B.inclusion.map (openObj U' Vo).hom = B.inclusion.map (openObj T T₀o).hom := by
    show l ≫ Vo.ι ≫ B.inclusion.map U'.hom = T₀o.ι ≫ B.inclusion.map T.hom
    rw [← Category.assoc, hl, Category.assoc, ← Over.w ε]
    rfl
  refine ⟨openObj U' Vo, openObjι U' Vo, openObj T T₀o, openObjι T T₀o,
    homOfCompEq B S hS (T := openObj T T₀o) (W := openObj U' Vo) l hw, hVo, hT₀o,
    isOpenImmersion_toScheme_map_openObjι _ _, isOpenImmersion_toScheme_map_openObjι _ _, ?_,
    mem_range_toScheme_map_openObjι _ _ hyT₀⟩
  have e1 : (toScheme B S hS).map
        (homOfCompEq B S hS (T := openObj T T₀o) (W := openObj U' Vo) l hw) = l :=
    toScheme_map_homOfCompEq B S hS _ _
  apply (toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, e1, toScheme_map_openObjι, toScheme_map_openObjι]
  exact hl

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A point of an algebraic space is hit by an affine étale chart.** -/
theorem exists_affine_etale_mem_range {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hR : IsAlgebraicSpace B S hS R) (r : points B S hS R) :
    ∃ (E : BigFppfOver B S hS) (eE : yoneda.obj E ⟶ R),
      IsAffine ((BigFppfOver.toScheme B S hS).obj E) ∧ IsEtale B S hS eE ∧
        r ∈ Set.range (pointsMap B S hS (yoneda.obj E) eE) := by
  classical
  have hcov : IsSmoothCovering B S hS (fun _ : Unit => R) (fun _ => 𝟙 R) := by
    refine ⟨hR, fun _ => hR, fun _ => isSmooth_id B S hS hR, ?_⟩
    rw [Set.iUnion_const, pointsMap_id]
    exact Set.range_id
  obtain ⟨J, T, t, hcovE, -⟩ :=
    exists_isEtaleCovering_representable_refining_isSmoothCovering B S hS hcov
  obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcovE.jointly_surjective r)
  set y := pointsToScheme B S hS (T j) z with hy
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (BigFppfOver.toScheme B S hS).obj (T j)) (x := y) (U := ⊤) trivial
  have hVaff : IsAffine V.toScheme := hV
  let A := BigFppfOver.openObj (T j) V
  let m := BigFppfOver.openObjι (T j) V
  have hm : (BigFppfOver.toScheme B S hS).map m = V.ι := BigFppfOver.toScheme_map_openObjι _ _
  have hAet : IsEtale B S hS (yoneda.map m) := by
    refine (isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS _).2 ?_)
    rw [hm]; exact (inferInstance : Etale V.ι)
  obtain ⟨s, hs⟩ := BigFppfOver.mem_range_toScheme_map_openObjι (T j) V hyV
  obtain ⟨r', hr'⟩ := (bijective_pointsToScheme B S hS A).surjective s
  have hzr : pointsMap B S hS (yoneda.obj A) (yoneda.map m) r' = z :=
    (bijective_pointsToScheme B S hS (T j)).injective
      (by rw [pointsToScheme_pointsMap_yoneda, hr', hs, hy])
  refine ⟨A, yoneda.map m ≫ t j, hVaff, isEtale_comp B S hS hAet (hcovE.etale j), r', ?_⟩
  rw [pointsMap_comp B S hS _ (yoneda.map m) (t j), Function.comp_apply, hzr, hz]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The base change of a smooth surjective chart along a thickening, with all its
properties.** For a thickening `ι : 𝒳 ⟶ 𝒳'` and a smooth 1-morphism `b` out of the stack of an
algebraic space `U'` which is surjective, the 2-fibre product `U = U' ×_{𝒳'} 𝒳` is an algebraic
space with a monomorphism to `U'`, and its projection to `𝒳` is smooth and surjective in the
relative sense. -/
theorem exists_thickeningChart_mono {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (ι : 𝒳 ⟶ 𝒳')
    (hι : IsThickening ι) {U' : AlgebraicSpaces B S hS}
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U' ⟶ 𝒳')
    (hb : AlgebraicStacks.IsSmooth B S hS b) (hbs : IsSurjective B S hS b) :
    ∃ (U : AlgebraicSpaces B S hS) (iU : U ⟶ U')
      (a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
      (γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map iU ≫ b ≅ a ≫ ι),
      Nonempty (Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq b ι)) ∧
      IsRelativelySmooth.{u, u, u + 1} B S hS a.hom ∧
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS) a.hom
        (isRepresentableByAlgebraicSpaces_of_space_source a) ∧ Mono iU.hom := by
  have hrep : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom ι.hom).pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _ ι.hom b.hom _
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        b.hom ι.hom) hι.1.1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U'.obj U'.property)
  obtain ⟨U, c, a, γ, ⟨hγ⟩⟩ := exists_isTwoFibreProduct_algebraicSpaceStackFunctor_obj b ι hrep
  obtain ⟨iU, rfl⟩ : ∃ iU : U ⟶ U', (algebraicSpaceStackFunctor.{u, w} B S hS).map iU = c :=
    ⟨_, algebraicSpaceStackFunctor_map_homMk_representingMap c⟩
  have hsw' := isTwoFibreProduct_underlying_algebraicStacks B S hS _
    (Bicategory.isTwoFibreProduct_swap hγ)
  let Q := (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq b ι).underlying
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_underlying_algebraicStacks B S hS _ hγ
  have hth := mono_and_isThickening_range_representingMap_fst B S hS ι.hom b.hom
    (isRelativeThickening_of_isThickening B S hS hι) Q hQ U.obj U'.obj U.property U'.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  have he : representingMap B S hS Q.pt ((algebraicSpaceStackFunctor.{u, w} B S hS).obj U').val
      U.obj U'.obj (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst = iU.hom :=
    representingMap_associatedMap B S hS U.obj U'.obj iU.hom
  refine ⟨U, iU, a, γ, ⟨hγ⟩, ?_, ?_, ?_⟩
  · exact isRelativelySmooth_baseChange.{u, u, u + 1} B S hS _ _ _ b.hom ι.hom _ hsw'
      (isRelativelySmooth_of_isSmooth_space_source b hb)
  · exact hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) _ _ _ b.hom ι.hom _ hsw'
      (isRepresentableByAlgebraicSpaces_of_space_source b)
      (hasRelativeProperty_surjective_of_space_source b hbs)
  · have := hth.1; rwa [he] at this

end AlgebraicGeometry.Stack

end
