module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OpenImmersionDerivedSections
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackCupProductDerived
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ClassMorphismPushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageComparisonSections

/-!
# The canonical map of de Rham complexes along an open immersion

Let `ι : X' ⟶ X` and `h₀ : S' ⟶ S` be open immersions of schemes with `ι ≫ p = p' ≫ h₀`. Then the
morphism `(X', p'⁻¹𝒪_{S'}) ⟶ (X, p⁻¹𝒪_S)` of inverse-image ringed spaces is an open immersion
of ringed spaces, and the canonical map `c : Ω^•_{X/S} ⟶ Rh_*Ω^•_{X'/S'}` induces isomorphisms on
derived sections over every open `U ⊆ ι(X')`
(`isIso_derivedSectionsOverOpen_map_deRhamComparisonQ`): the restriction of the de Rham complex
of `X/S` to `X'` is the de Rham complex of `X'/S'` ([Stacks, Tag 0FLV]), and derived sections
over `U` may be computed on `X'` ([Stacks, Tag 0D5V]).

## Main results

* `Scheme.Hom.bijective_relativeDifferentialFormsPullback_of_isOpenImmersion_of_etale`:
  pulling back forms along an open immersion over an étale change of base is bijective over
  every open inside its image.
* `DeRhamLerayHirsch.isOpenImmersion_inverseImageBaseMap`: the morphism of inverse-image ringed
  spaces of a square of open immersions is an open immersion.
* `DeRhamLerayHirsch.isIso_derivedSectionsOverOpen_map_deRhamComparisonQ`: the canonical map
  `Ω^•_{X/S} ⟶ Rh_*Ω^•_{X'/S'}` induces isomorphisms on derived sections over every open
  `U ⊆ ι(X')`.

## References

* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S S' : Scheme.{u}}

/-- **Pulling back forms along an open immersion over an étale change of base is bijective over
every open inside its image** ([Stacks, Tag 0FLV]). -/
theorem bijective_relativeDifferentialFormsPullback_of_isOpenImmersion_of_etale (ι : Y ⟶ X)
    [IsOpenImmersion ι] (π : X ⟶ S) (π' : Y ⟶ S') (t : S' ⟶ S) [Etale t]
    (h : ι ≫ π = π' ≫ t) (d : ℤ) (W : X.Opens) (hW : W ≤ ι.opensRange) :
    Function.Bijective (relativeDifferentialFormsPullback ι π π' t h d W) := by
  have hmap : IsIso (relativeDifferentialFormsMap ι π π' t h d) :=
    isIso_relativeDifferentialFormsMap_of_etale ι π π' t h d
  have h1 : Function.Bijective (Scheme.Modules.Hom.app
      (relativeDifferentialFormsMap ι π π' t h d) (ι ⁻¹ᵁ W)) :=
    ConcreteCategory.bijective_of_isIso _
  have himg : ι ''ᵁ ι ⁻¹ᵁ W = W := by
    rw [ι.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr hW
  have hres : Function.Bijective ((relativeDifferentialForms π d).presheaf.map
      (homOfLE (ι.image_preimage_le W)).op) := by
    have : homOfLE (ι.image_preimage_le W) = eqToHom himg := Subsingleton.elim _ _
    rw [this, eqToHom_op]
    exact ConcreteCategory.bijective_of_isIso _
  have he : Function.Bijective (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback ι).inv.app
        (relativeDifferentialForms π d)) (ι ⁻¹ᵁ W)) :=
    ConcreteCategory.bijective_of_isIso _
  have hunit : Function.Bijective
      (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ι (relativeDifferentialForms π d) W) := by
    have hcomp : (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback ι).inv.app
        (relativeDifferentialForms π d)) (ι ⁻¹ᵁ W)) ∘
          Stacks.Tag01VSPullbackTensor.modulesPullbackUnit ι (relativeDifferentialForms π d) W =
        (relativeDifferentialForms π d).presheaf.map (homOfLE (ι.image_preimage_le W)).op := by
      funext a
      exact Scheme.Modules.restrictFunctorIsoPullback_inv_unit ι _ W a
    exact (Function.Bijective.of_comp_iff' he _).mp (hcomp ▸ hres)
  exact h1.comp hunit

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X X' S S' : Scheme.{u}} (ι : X' ⟶ X) (p' : X' ⟶ S') (p : X ⟶ S) (h₀ : S' ⟶ S)
  (w : ι ≫ p = p' ≫ h₀)

/-- The underlying continuous map of the morphism of inverse-image ringed spaces of a square is
that of `ι`. -/
theorem inverseImageBaseMap_base : (inverseImageBaseMap ι p' p h₀ w).hom.base = ι.base :=
  Category.id_comp _

/-- **The morphism of inverse-image ringed spaces of a square of open immersions is an open
immersion of ringed spaces**: its stalk maps are those of `h₀`, read through the identifications
of the stalks of inverse images. -/
theorem isOpenImmersion_inverseImageBaseMap [IsOpenImmersion ι] [IsOpenImmersion h₀] :
    SheafedSpace.IsOpenImmersion (inverseImageBaseMap ι p' p h₀ w) := by
  have hemb : Topology.IsOpenEmbedding (inverseImageBaseMap ι p' p h₀ w).hom.base := by
    rw [inverseImageBaseMap_base]
    exact ι.isOpenEmbedding
  have H : ∀ x, IsIso ((inverseImageBaseMap ι p' p h₀ w).hom.stalkMap x) := by
    intro x
    have e := congrArg (fun φ => φ.hom)
      (inverseImageBaseMap_comp_inverseImageBaseProjection ι p' p h₀ w)
    have e₁ := PresheafedSpace.stalkMap.comp (inverseImageBaseMap ι p' p h₀ w).hom
      (inverseImageBaseProjection p).hom x
    have e₂ := PresheafedSpace.stalkMap.congr_hom _ _ e x
    have e₃ := PresheafedSpace.stalkMap.comp (inverseImageBaseProjection p').hom
      h₀.toLRSHom.toShHom.hom x
    have i₁ := AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection
      S.toRingedSpace p.base ((inverseImageBaseMap ι p' p h₀ w).hom.base x)
    have i₂ := AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection
      S'.toRingedSpace p'.base x
    have i₃ : IsIso (h₀.stalkMap (p'.base x)) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
    have h₄ : IsIso (PresheafedSpace.Hom.stalkMap
        (inverseImageBaseMap ι p' p h₀ w ≫ inverseImageBaseProjection p).hom x) := by
      rw [e₂]
      refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
      refine (congrArg IsIso e₃).mpr ?_
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ i₃ i₂
    have h₅ := (congrArg IsIso e₁).mp h₄
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ i₁ h₅
  exact SheafedSpace.IsOpenImmersion.of_stalk_iso _ hemb (H := H)

/-- Bijectivity transported along equalities of types and a heterogeneous equality of maps. -/
theorem bijective_of_heq {α β α' β' : Type u} (hα : α = α') (hβ : β = β') (f : α → β)
    (g : α' → β') (h : ∀ x x', HEq x x' → HEq (f x) (g x')) (hg : Function.Bijective g) :
    Function.Bijective f := by
  subst hα hβ
  have : f = g := funext fun x => eq_of_heq (h x x HEq.rfl)
  rwa [this]

/-- **On sections over an open inside the image of `ι`, the canonical map of de Rham complexes
of a square of open immersions is bijective** in every degree. -/
theorem isIso_deRhamPushforwardInt_f_app [IsOpenImmersion ι] [IsOpenImmersion h₀] (n : ℤ)
    (V : X.Opens) (hV : V ≤ ι.opensRange) :
    IsIso (((deRhamPushforwardInt ι p' p h₀ w).f n).val.app (op V)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  by_cases hn : 0 ≤ n
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine bijective_of_heq
      (congrArg (fun M : _root_.SheafOfModules.{u}
        (SheafOfModules.underlyingRingSheaf.{u, u} (DeRhamKatzOdaCech.baseSheaf p)) =>
          (M.val.obj (op V) : Type u))
        (SheafOfModules.deRhamComplexInt_X_of_nonneg (Scheme.Hom.deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) (q : ℤ)
          (Int.natCast_nonneg q)))
      (congrArg (fun M : _root_.SheafOfModules.{u}
        (SheafOfModules.underlyingRingSheaf.{u, u} (DeRhamKatzOdaCech.baseSheaf p')) =>
          (M.val.obj (op (ι ⁻¹ᵁ V)) : Type u))
        (SheafOfModules.deRhamComplexInt_X_of_nonneg (Scheme.Hom.deRhamAlgebras p')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p')) (q : ℤ)
          (Int.natCast_nonneg q))) _
      (Scheme.Hom.relativeDifferentialFormsPullback ι p p' h₀ w (q : ℤ) V)
      (fun x x' hx => dgaPushforward_f_app_heq ι p' p h₀ w q q rfl (op V) x x' hx) ?_
    exact Scheme.Hom.bijective_relativeDifferentialFormsPullback_of_isOpenImmersion_of_etale
      ι p p' h₀ w q V hV
  · refine ⟨fun x y _ => (dga_section_eq_zero p n (by omega) (op V) x).trans
      (dga_section_eq_zero p n (by omega) (op V) y).symm, fun y => ⟨0, ?_⟩⟩
    exact (dga_section_eq_zero p' n (by omega) _ _).trans
      (dga_section_eq_zero p' n (by omega) _ y).symm

/-- The image of an open of `X'` lies in the image of `ι`. -/
theorem functor_obj_le_opensRange [IsOpenImmersion ι] [IsOpenImmersion h₀] (W : X'.Opens) :
    (isOpenImmersion_inverseImageBaseMap ι p' p h₀ w).base_open.functor.obj W ≤ ι.opensRange := by
  rintro x ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

/-- **The canonical map `h^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` of a square of open immersions is an
isomorphism** ([Stacks, Tag 0FLV]). -/
theorem isIso_deRhamPullbackInt [IsOpenImmersion ι] [IsOpenImmersion h₀] :
    IsIso (ProperSmoothDeRham.deRhamPullbackInt ι p' p h₀ w) := by
  have := isOpenImmersion_inverseImageBaseMap ι p' p h₀ w
  have : ∀ n, IsIso ((ProperSmoothDeRham.deRhamPullbackInt ι p' p h₀ w).f n) := by
    intro n
    have e : (ProperSmoothDeRham.deRhamPullbackInt ι p' p h₀ w).f n =
        (modulePullback (inverseImageBaseMap ι p' p h₀ w)).map
          ((deRhamPushforwardInt ι p' p h₀ w).f n) ≫
        (modulePullbackPushforwardAdjunction (inverseImageBaseMap ι p' p h₀ w)).counit.app _ := by
      have e₀ := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
        ((((modulePullbackPushforwardAdjunction
          (inverseImageBaseMap ι p' p h₀ w)).mapHomologicalComplex
          (ComplexShape.up ℤ)).homEquiv _ _).symm_apply_apply
            (ProperSmoothDeRham.deRhamPullbackInt ι p' p h₀ w))
      refine e₀.symm.trans ?_
      rw [Adjunction.homEquiv_counit]
      rfl
    rw [e]
    have h₁ := Stacks.Cohomology.openImmersionPullback_map_isIso (inverseImageBaseMap ι p' p h₀ w)
      ((deRhamPushforwardInt ι p' p h₀ w).f n) fun W =>
        isIso_deRhamPushforwardInt_f_app ι p' p h₀ w n _ (functor_obj_le_opensRange ι p' p h₀ w W)
    have h₂ := Stacks.Cohomology.openImmersionPullback_counit_isIso
      (inverseImageBaseMap ι p' p h₀ w)
      ((ProperSmoothDeRham.deRhamComplexInt p').X n)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The canonical map of a square is the unit of `h^* ⊣ h_*` followed by `h_* ⟶ Rh_*` and the
direct image of `h^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`. -/
theorem deRhamComparisonQ_eq_pullbackUnitQ :
    deRhamComparisonQ ι p' p h₀ w =
      Stacks.Cohomology.OpenImmersionSections.pullbackUnitQ (inverseImageBaseMap ι p' p h₀ w)
          (ProperSmoothDeRham.deRhamComplexInt p) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          (inverseImageBaseMap ι p' p h₀ w)).map
          (DerivedCategory.Q.map (ProperSmoothDeRham.deRhamPullbackInt ι p' p h₀ w)) := by
  have h₁ := congrArg (fun φ => DerivedCategory.Q.map φ ≫
      Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
        (inverseImageBaseMap ι p' p h₀ w) (deRhamComplexModules p'))
    (deRhamPushforwardInt_eq_unit_comp ι p' p h₀ w)
  have h₂ :=
    open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces in
    pushforwardComparisonQ_naturality
      (inverseImageBaseMap ι p' p h₀ w) (ProperSmoothDeRham.deRhamPullbackInt ι p' p h₀ w)
  refine h₁.trans ((congrArg (· ≫ _) (DerivedCategory.Q.map_comp _ _)).trans
    ((Category.assoc _ _ _).trans ((congrArg (DerivedCategory.Q.map
      (Stacks.Cohomology.OpenImmersionSections.pullbackUnitComplex (inverseImageBaseMap ι p' p h₀ w)
        (ProperSmoothDeRham.deRhamComplexInt p)) ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

/-- **The canonical map of a square of open immersions induces isomorphisms on derived sections
over every open inside the image of `ι`**: `RΓ(U, Ω^•_{X/S}) ≅ RΓ(U, Rh_*Ω^•_{X'/S'})` for
`U ⊆ ι(X')` ([Stacks, Tags 0FLV and 0D5V]). -/
theorem isIso_derivedSectionsOverOpen_map_deRhamComparisonQ [IsOpenImmersion ι]
    [IsOpenImmersion h₀] (U : X.Opens) (hU : U ≤ ι.opensRange) :
    IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
        (inverseImageBase p) U).map
      (deRhamComparisonQ ι p' p h₀ w)) := by
  have := isOpenImmersion_inverseImageBaseMap ι p' p h₀ w
  have hκ := isIso_deRhamPullbackInt ι p' p h₀ w
  have hU' : (U : Set X) ⊆ Set.range (inverseImageBaseMap ι p' p h₀ w).hom.base := by
    rw [inverseImageBaseMap_base]
    exact hU
  have h₁ := Stacks.Cohomology.OpenImmersionSections.isIso_derivedSectionsOverOpen_map_pullbackUnitQ
    (inverseImageBaseMap ι p' p h₀ w) U hU' (ProperSmoothDeRham.deRhamComplexInt p)
  rw [deRhamComparisonQ_eq_pullbackUnitQ]
  refine (congrArg IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
    (inverseImageBase p) U).map_comp _ _)).mpr ?_
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (Functor.map_isIso _ _)

end AlgebraicGeometry.DeRhamLerayHirsch
