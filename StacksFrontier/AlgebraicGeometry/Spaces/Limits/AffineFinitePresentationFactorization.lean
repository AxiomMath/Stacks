module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.UniversallyClosedSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingOnObjectsCriteria

/-!
# Factoring a morphism to an algebraic space through an affine scheme of finite presentation

Let `Y` be an algebraic space over a scheme `S` and let `g : Z → Y` be a morphism from a
scheme. We study when `g` factors, Zariski locally on `Z`, through an affine scheme which is
locally of finite presentation over `Y`. This is exactly what the refinement of Stacks 0CM8
for `Z` a scheme asks for, by
`AlgebraicGeometry.Space.exists_affine_isLocallyOfFinitePresentation_factorization_of_separation`.

Two statements are proved.

The first is a descent statement. If `π : P → Q` is a surjective étale morphism of schemes
and `φ : P → Y` is a morphism which agrees on the two projections of `P ×_Q P`, then `φ`
descends to a morphism `Q → Y`, because a surjective étale morphism of schemes is an
effective epimorphism of fppf sheaves; and the descended morphism is locally of finite
presentation over `Y` as soon as `φ` is, because local finite presentation descends along a
morphism which is surjective as a map of fppf sheaves.

The second is the factorization itself when `Y` is locally of finite presentation over `S`.
Take an affine open `V` of `Z` around the given point lying over an affine open `Spec R` of
`S`. Then `V = Spec A` is the cofiltered limit of the spectra of finitely presented
`R`-algebras, the functor of points of `Y` is limit preserving by Stacks 04AK, so the
morphism `V → Y` factors through one of these spectra, and that spectrum is locally of finite
presentation over `Y` because both it and `Y` are locally of finite presentation over `S`.

## Main results

* `AlgebraicGeometry.Space.exists_desc_of_surjective_etale`: descent of a morphism to an
  algebraic space along a surjective étale morphism of schemes, together with the descent of
  local finite presentation.
* `AlgebraicGeometry.Space.exists_affine_isLocallyOfFinitePresentation_factorization_of_terminal`:
  a morphism from a scheme to an algebraic space locally of finite presentation over `S`
  factors, on an affine open neighbourhood of any given point, through an affine scheme
  locally of finite presentation over the algebraic space.

## References

* [Stacks Project, Tag 0CM8](https://stacks.math.columbia.edu/tag/0CM8)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent of a morphism to an algebraic space along a surjective étale morphism of
schemes.** Let `π : P ⟶ Q` be a morphism of the big fppf site of `S` whose underlying morphism
of schemes is surjective and étale, let `s, t : R ⟶ P` be its kernel pair, and let
`φ : P ⟶ Y` be a morphism to an algebraic space with `s ≫ φ = t ≫ φ`. Then `φ` factors as
`π ≫ ψ` for a morphism `ψ : Q ⟶ Y`, and `ψ` is locally of finite presentation whenever `φ` is.

The factorization is Stacks 0262, part (3), for the representable algebraic space `Q`: the
surjective étale atlas `π` is the coequalizer of its kernel pair in fppf sheaves. Local finite
presentation descends to `ψ` by Stacks 06NR, since `π` is surjective as a map of sheaves. -/
theorem exists_desc_of_surjective_etale
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {P Q R : BigFppfOver B S hS} (π : P ⟶ Q)
    (hπs : Surjective ((BigFppfOver.toScheme B S hS).map π))
    (hπe : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map π))
    (s t : R ⟶ P) (hR : IsPullback (yoneda.map s) (yoneda.map t) (yoneda.map π) (yoneda.map π))
    (φ : yoneda.obj P ⟶ Y) (hφ : yoneda.map s ≫ φ = yoneda.map t ≫ φ) :
    ∃ ψ : yoneda.obj Q ⟶ Y, yoneda.map π ≫ ψ = φ ∧
      (IsLocallyOfFinitePresentation B S hS φ → IsLocallyOfFinitePresentation B S hS ψ) := by
  have hQ := isAlgebraicSpace_yoneda B S hS Q
  have hπs' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map π) :=
    (presheaf_yoneda_map_iff B S hS inferInstance π).2 hπs
  have hπe' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map π) :=
    (presheaf_yoneda_map_etale_iff B S hS π).2 hπe
  obtain ⟨hRsh, hUsh, ⟨hc⟩⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS (yoneda.map π) s t hR hQ hπs' hπe'
  let J := BigFppfOver.topology B S hS
  let YF : Sheaf J (Type u) := ⟨Y, hY.isSheaf⟩
  let φF : (⟨yoneda.obj P, hUsh⟩ : Sheaf J (Type u)) ⟶ YF := ⟨φ⟩
  have hw : (⟨yoneda.map s⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶ ⟨yoneda.obj P, hUsh⟩)
      ≫ φF = (⟨yoneda.map t⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶
        ⟨yoneda.obj P, hUsh⟩) ≫ φF :=
    Sheaf.hom_ext hφ
  let ψF := hc.desc (Cofork.ofπ φF hw)
  have hcomp : yoneda.map π ≫ ψF.hom = φ :=
    congrArg (fun k : (⟨yoneda.obj P, hUsh⟩ : Sheaf J (Type u)) ⟶ YF => k.hom)
      (hc.fac (Cofork.ofπ φF hw) WalkingParallelPair.one)
  exact ⟨ψF.hom, hcomp, fun hφlfp => isLocallyOfFinitePresentation_of_comp_of_locallySurjective
    B S hS (isAlgebraicSpace_yoneda B S hS P) hQ hY (yoneda.map π) ψF.hom (by rwa [hcomp])
    (isLocallySurjective_of_surjective_etale B S hS (yoneda.map π) hπs' hπe')⟩

/-- The structural morphism of an object of the big fppf site of `S` whose underlying morphism
to `S` is locally of finite presentation is locally of finite presentation as a morphism of
algebraic spaces to the terminal presheaf. -/
theorem isLocallyOfFinitePresentation_terminal_from_yoneda (U : BigFppfOver B S hS)
    (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom)) :
    IsLocallyOfFinitePresentation B S hS (terminal.from (yoneda.obj U)) := by
  have hmap : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (terminal.from U)) := by
    rw [← Category.comp_id ((BigFppfOver.toScheme B S hS).map (terminal.from U)),
      ← Iso.hom_inv_id (toSchemeTerminalIso B S hS), ← Category.assoc,
      toScheme_map_terminal_from B S hS U]
    infer_instance
  exact holdsOnEveryEtaleChart_of_isTerminal B S hS (isTerminal_yoneda_obj_terminal B S hS)
    terminalIsTerminal _ _ (isLocallyOfFinitePresentation_yoneda_map B S hS _ hmap)

/-- A section of a presheaf over `W` which restricts along `π : X ⟶ W` to the section of a
morphism `f` from the Yoneda presheaf of `X` gives, as a morphism from the Yoneda presheaf of
`W`, a factorization of `f` through `π`. -/
theorem yoneda_map_comp_yonedaEquiv_symm_eq {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*}
    {X W : C} (π : X ⟶ W) (y : F.obj (Opposite.op W)) (f : yoneda.obj X ⟶ F)
    (h : F.map π.op y = yonedaEquiv f) : yoneda.map π ≫ yonedaEquiv.symm y = f := by
  apply yonedaEquiv.injective
  rwa [← yonedaEquiv_naturality, Equiv.apply_symm_apply]

/-- Transport of a factorization along an isomorphism of the source: if `π ≫ ι` agrees with
`(e.hom ≫ p) ≫ g` on Yoneda presheaves, then `p ≫ g` factors through `e.inv ≫ π`. -/
theorem yoneda_map_comp_eq_of_iso {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*}
    {U' V W Z : C} (e : U' ≅ V) (π : U' ⟶ W) (ι : yoneda.obj W ⟶ F) (p : V ⟶ Z)
    (g : yoneda.obj Z ⟶ F) (h : yoneda.map π ≫ ι = yoneda.map (e.hom ≫ p) ≫ g) :
    yoneda.map p ≫ g = yoneda.map (e.inv ≫ π) ≫ ι := by
  rw [yoneda.map_comp, Category.assoc, h, ← Category.assoc, ← yoneda.map_comp,
    Iso.inv_hom_id_assoc]

/-- A morphism from the Yoneda presheaf of an object locally of finite presentation over `S`
to an algebraic space locally of finite presentation over `S` is locally of finite
presentation. -/
private theorem isLocallyOfFinitePresentation_of_yoneda_of_terminal
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYlfp : IsLocallyOfFinitePresentation B S hS (terminal.from Y))
    (U : BigFppfOver B S hS) (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom))
    (ι : yoneda.obj U ⟶ Y) : IsLocallyOfFinitePresentation B S hS ι := by
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B S hS (yonedaTerminalIso B S hS)
      (isAlgebraicSpace_yoneda B S hS (⊤_ (BigFppfOver B S hS)))
  refine isLocallyOfFinitePresentation_of_comp B S hS
    (isAlgebraicSpace_yoneda B S hS U) hY hT ι (terminal.from Y) ?_
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hYlfp)
  rw [terminal.hom_ext (ι ≫ terminal.from Y) (terminal.from (yoneda.obj U))]
  exact isLocallyOfFinitePresentation_terminal_from_yoneda B S hS U hU

/-- Given a morphism of schemes `f : X ⟶ T` and a point `x` of `X`, there are an affine open
`T₀` of `T` containing `f x` and an affine open `X₀` of `X` containing `x` with
`X₀ ≤ f ⁻¹ᵁ T₀`. -/
private theorem exists_isAffine_opens_le_preimage {X T : Scheme.{u}} (f : X ⟶ T) (x : X) :
    ∃ (T₀ : T.Opens) (X₀ : X.Opens), IsAffine T₀.toScheme ∧ IsAffine X₀.toScheme ∧
      f x ∈ T₀ ∧ x ∈ X₀ ∧ X₀ ≤ f ⁻¹ᵁ T₀ := by
  obtain ⟨-, ⟨T₀, hT₀, rfl⟩, hxT₀, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨-, ⟨X₀, hX₀, rfl⟩, hxX₀, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (f ⁻¹ᵁ T₀ : Set _) from hxT₀) (f ⁻¹ᵁ T₀).2
  exact ⟨T₀, X₀, hT₀, hX₀, hxT₀, hxX₀, hle⟩

/-- **A morphism from a scheme to an algebraic space locally of finite presentation over `S`
factors Zariski locally through an affine scheme locally of finite presentation over the
space.** Let `Y` be an algebraic space over `S` which is locally of finite presentation over
`S`, let `g : Z₀ ⟶ Y` be a morphism from an object of the big fppf site, and let `z` be a
point of `|Z₀|`. Then there are an affine open neighbourhood `V` of `z` in `Z₀`, an affine
object `U` of the site with a morphism `ι : U ⟶ Y` locally of finite presentation, and a
factorization `V ⟶ U ⟶ Y` of the restriction of `g` to `V`.

Choose an affine open `Spec R` of `S` containing the image of `z` and an affine open
`V = Spec A` of `Z₀` around `z` mapping into it. Writing `A` as a directed colimit of finitely
presented `R`-algebras exhibits `V` as a cofiltered limit of affine objects of the site locally
of finite presentation over `S`; the functor of points of `Y` is limit preserving by Stacks
04AK, so the morphism `V ⟶ Y` factors through one of them, which is `U`. Since `U` and `Y` are
both locally of finite presentation over `S`, the morphism `U ⟶ Y` is locally of finite
presentation, by Stacks 05WT. -/
theorem exists_affine_isLocallyOfFinitePresentation_factorization_of_terminal
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z₀ : BigFppfOver B S hS}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYlfp : IsLocallyOfFinitePresentation B S hS (terminal.from Y))
    (g : yoneda.obj Z₀ ⟶ Y) (z : points B S hS (yoneda.obj Z₀)) :
    ∃ (U V : BigFppfOver B S hS) (ι : yoneda.obj U ⟶ Y) (pV : V ⟶ Z₀)
      (v : points B S hS (yoneda.obj V)) (α₀ : V ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsLocallyOfFinitePresentation B S hS ι ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
      pointsMap B S hS (yoneda.obj V) (yoneda.map pV) v = z ∧
      yoneda.map pV ≫ g = yoneda.map α₀ ≫ ι := by
  classical
  set πZ : (BigFppfOver.toScheme B S hS).obj Z₀ ⟶ S := B.inclusion.map Z₀.hom
  set x := pointsToScheme B S hS Z₀ z
  -- an affine open of `Z₀` around `z` inside the preimage of an affine open of `S`
  obtain ⟨S₀, VO, hS₀, hVO, -, hxV, hle⟩ := exists_isAffine_opens_le_preimage πZ x
  let V := openSiteObject B S hS Z₀ VO
  let pV : V ⟶ Z₀ := openSiteObjectHom B S hS Z₀ VO
  have hpV : (BigFppfOver.toScheme B S hS).map pV = VO.ι := map_openSiteObjectHom B S hS Z₀ VO
  obtain ⟨v, hv⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS pV z (by
    rw [hpV]
    exact ⟨⟨x, hxV⟩, rfl⟩)
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVO
  -- the affine open of `S` as a spectrum
  let R : CommRingCat.{u} := Γ(S₀.toScheme, ⊤)
  have hR : B.Contains (Spec R) := by
    show (Spec R).size < B.cutoff
    rw [← Scheme.size_congr S₀.toScheme.isoSpec]
    exact Scheme.size_lt_of_isOpenImmersion S₀.ι hS
  let r : Spec R ⟶ S := S₀.toScheme.isoSpec.inv ≫ S₀.ι
  have : LocallyOfFinitePresentation r := by
    dsimp only [r]
    infer_instance
  let q : VO.toScheme ⟶ Spec R := πZ.resLE S₀ VO hle ≫ S₀.toScheme.isoSpec.hom
  have hq : q ≫ r = B.inclusion.map V.hom := show q ≫ r = VO.ι ≫ πZ by
    simp only [q, r, Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]
  -- `V` as a cofiltered limit of affine objects locally of finite presentation over `S`
  have : IsAffine V.left.1 := hVaff
  obtain ⟨I, hI, hco, D, c', e, ⟨hc'⟩, hfp⟩ :=
    Stack.exists_isLimit_affine_locallyOfFinitePresentation B S hS V R hR r q hq
  let D' : I ⥤ BigFppfOver B S hS := D ⋙ BigAffineFppf.inclusion B S hS
  obtain ⟨hcol⟩ := limitPreserving_of_isLocallyOfFinitePresentation B S hS hY hYlfp
    I D' c' hc' (fun i => (D.obj i).property)
    (.of_isIso ((BigFppfOver.toScheme B S hS).map e.hom))
  let y₀ : Y.obj (Opposite.op c'.pt) := yonedaEquiv (yoneda.map (e.hom ≫ pV) ≫ g)
  obtain ⟨j, yj, hyj⟩ := Types.jointly_surjective_of_isColimit hcol y₀
  let ι : yoneda.obj (D'.obj j.unop) ⟶ Y := yonedaEquiv.symm yj
  refine ⟨D'.obj j.unop, V, ι, pV, v, e.inv ≫ c'.π.app j.unop,
    (D.obj j.unop).property, ?_, hVaff, ?_, hv, ?_⟩
  · -- `U ⟶ Y` is locally of finite presentation, by cancellation over `S`
    exact isLocallyOfFinitePresentation_of_yoneda_of_terminal B S hS hY hYlfp
      (D'.obj j.unop) (hfp j.unop) ι
  · rw [hpV]
    exact (inferInstance : AlgebraicGeometry.IsOpenImmersion VO.ι)
  · -- the factorization, read on the sections of `Y` over `V`
    exact yoneda_map_comp_eq_of_iso e (c'.π.app j.unop) ι pV g
      (yoneda_map_comp_yonedaEquiv_symm_eq (F := Y) (c'.π.app j.unop) yj
        (yoneda.map (e.hom ≫ pV) ≫ g) hyj)

end AlgebraicGeometry.Space

end
