module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalPointReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFactorizationCovering

/-!
# Base change of the conormal isomorphism of Stacks 0B4I: the target side

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `σ` a section of `𝐏(ℰ) ⟶ X` and `σ'` a
section of `𝐏(g^*ℰ) ⟶ X'` lying over `σ` along `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`.  Let `v : T' ⟶ X'` and
`u : T ⟶ X` be scheme points with `v ≫ g = u ∘ h` for a morphism `h : T' ⟶ T` of test objects.

* The fibres `𝐏(g^*ℰ)_{T'}` (over `v`) and `𝐏(ℰ)_T` (over `u`) are compared by
  `AlgebraicGeometry.Space.sectionFibreBaseChangeComparison`, which lies over `h` and over
  `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`, and carries the section `k'_v` of the first fibre to `h` followed by the
  section `k_u` of the second.
* The paste of the target maps
  (`AlgebraicGeometry.Space.sectionConormalTargetBaseChangeHom_paste`): `v^*` of the base-change
  map `g^*𝒞_σ ⟶ 𝒞_{σ'}` followed by the target map at `v` is, through the composition comparisons
  of Stacks 03LU, `h^*` of the chart isomorphism at the étale point `u` followed by the map of
  conormal algebras of the square of sections `k'_v`, `k_u` over `h`.  Both halves
  (`AlgebraicGeometry.Space.sectionConormalTargetBaseChangeHom_paste_left`,
  `AlgebraicGeometry.Space.sectionConormalTargetBaseChangeHom_paste_right`) are the map of
  conormal algebras of the outer square `k'_v`, `σ` over `v ≫ g`.
* The generic glue `CategoryTheory.Functor.conormalGlue_baseChange` for the base change of the
  glued conormal isomorphism at a chart of the source.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))
  {T T' : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1) (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T)
  (hvh : v ≫ g.hom = yoneda.map h ≫ u)

/-! ### The comparison of fibres -/

/-- The base-change morphism `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)` lies over `g`. -/
theorem projectiveBundleBaseChange_hom_comp_projectiveBundleπ_hom :
    (projectiveBundleBaseChange X E hE hb g hb').hom ≫ (projectiveBundleπ X E hE hb).hom =
      (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom ≫ g.hom :=
  congrArg InducedCategory.Hom.hom (baseChangeHomOfPointsEquiv_comp g E _ _ _ _ _ _)

/-- **The comparison `𝐏(g^*ℰ)_{T'} ⟶ 𝐏(ℰ)_T` of the fibres over `v` and over `u`**, for
`v ≫ g = u ∘ h`: the morphism the cartesian square of the fibre over `u` produces from
`𝐏(g^*ℰ)_{T'} ⟶ 𝐏(g^*ℰ) ⟶ 𝐏(ℰ)` and from `𝐏(g^*ℰ)_{T'} ⟶ T' ⟶ T`. -/
def sectionFibreBaseChangeComparison :
    (projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibre T' v ⟶ (projectiveBundleSituation X E hE
      hb).relativeProjPoints.fibre T u :=
  Yoneda.fullyFaithful.preimage
    (((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback T u).lift
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v ≫
        (projectiveBundleBaseChange X E hE hb g hb').hom)
      (yoneda.map ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreHom T' v) ≫ yoneda.map h)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (projectiveBundleBaseChange_hom_comp_projectiveBundleπ_hom X E hE hb g hb')).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g.hom)
          ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.isPullback T' v).w).trans ((Category.assoc _ _ _).trans
            ((congrArg (_ ≫ ·) hvh).trans (Category.assoc _ _ _).symm)))))))

/-- The comparison of fibres lies over `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`. -/
theorem map_sectionFibreBaseChangeComparison_comp_fibreToSpace :
    yoneda.map (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh) ≫
      (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T u =
      (projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        hb').relativeProjPoints.fibreToSpace T' v ≫
        (projectiveBundleBaseChange X E hE hb g hb').hom :=
  (congrArg (· ≫ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T u)
    (Yoneda.fullyFaithful.map_preimage _)).trans
    (((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback T u).lift_fst _ _ _)

/-- The comparison of fibres lies over `h`. -/
theorem sectionFibreBaseChangeComparison_comp_fibreHom :
    (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh) ≫
      (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T u =
      (projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreHom T' v ≫ h :=
  Yoneda.fullyFaithful.map_injective (((yoneda.map_comp _ _).trans
    ((congrArg (· ≫ yoneda.map ((projectiveBundleSituation X E hE
      hb).relativeProjPoints.fibreHom T u)) (Yoneda.fullyFaithful.map_preimage _)).trans
      (((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback T u).lift_snd _ _
        _))).trans (yoneda.map_comp _ _).symm)

/-- A functor carries an equation between two composites to the equation of the images. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Y} {f' : W ⟶ Z} {g' : Z ⟶ Y} (h : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' :=
  (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))

/-- The comparison of fibres lies over `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`, as morphisms of algebraic spaces. -/
theorem yonedaSpaceMap_sectionFibreBaseChangeComparison_comp_pointHom :
    yonedaSpaceMap (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh) ≫
      (pointHom (X := relativeProjSymmetricAlgebra X E hE hb)
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T u)) =
      (pointHom (X := relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreToSpace T' v)) ≫ (projectiveBundleBaseChange X E hE hb g hb') :=
  ObjectProperty.hom_ext _ (map_sectionFibreBaseChangeComparison_comp_fibreToSpace X E hE hb g hb'
    u v h hvh)

variable (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb)
    (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
  (σ' : X' ⟶ relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
  (hσ' : σ' ≫ projectiveBundleπ X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' = 𝟙 X')
  (comm : σ' ≫ (projectiveBundleBaseChange X E hE hb g hb') = g ≫ σ)

include comm in
/-- The comparison of fibres carries the section `k'_v` to `h` followed by the section `k_u`. -/
theorem sectionFibreLift_comp_sectionFibreBaseChangeComparison :
    (sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) ≫
      (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh) = h ≫
      (sectionFibreLift X E hE hb σ hσ T u) := by
  apply Yoneda.fullyFaithful.map_injective
  refine ((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback T u).hom_ext ?_ ?_
  · have a₁ := map_sectionFibreBaseChangeComparison_comp_fibreToSpace X E hE hb g hb' u v h hvh
    have a₂ := yoneda_map_sectionFibreLift_comp X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
    have a₃ := yoneda_map_sectionFibreLift_comp X E hE hb σ hσ T u
    have a₄ : σ'.hom ≫ (projectiveBundleBaseChange X E hE hb g hb').hom = g.hom ≫ σ.hom := congrArg
        InducedCategory.Hom.hom comm
    exact (congrArg (· ≫ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T u)
        (yoneda.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg
        (yoneda.map (sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) ≫ ·)
        a₁).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg
        (· ≫ (projectiveBundleBaseChange X E hE hb g hb').hom) a₂).trans
      ((Category.assoc _ _ _).trans ((congrArg (v ≫ ·) a₄).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ σ.hom) hvh).trans
      ((Category.assoc _ _ _).trans ((congrArg (yoneda.map h ≫ ·) a₃.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T u)
          (yoneda.map_comp _ _).symm))))))))))))
  · have e₁ : ((sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) ≫
        (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh)) ≫
        (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T u = h :=
      (Category.assoc _ _ _).trans ((congrArg
        ((sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) ≫ ·)
        (sectionFibreBaseChangeComparison_comp_fibreHom X E hE hb g hb' u v h hvh)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h)
          (sectionFibreLift_comp_fibreHom X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)).trans
          (Category.id_comp h))))
    have e₂ : (h ≫ (sectionFibreLift X E hE hb σ hσ T u)) ≫
        (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T u = h :=
      (Category.assoc _ _ _).trans ((congrArg (h ≫ ·)
        (sectionFibreLift_comp_fibreHom X E hE hb σ hσ T u)).trans (Category.comp_id h))
    exact map_comp_eq_map_comp yoneda (e₁.trans e₂.symm)

include comm in
/-- The square of sections `k'_v`, `k_u` over `h`, as morphisms of algebraic spaces. -/
theorem yonedaSpaceMap_sectionFibreLift_comp_sectionFibreBaseChangeComparison :
    yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) ≫
      yonedaSpaceMap (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh) =
      yonedaSpaceMap h ≫ yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T u) :=
  ObjectProperty.hom_ext _ (map_comp_eq_map_comp yoneda
    (sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh σ hσ σ' hσ'
      comm))

include comm in
/-- The square of sections `k'_v`, `k_u` over `h`, on the underlying schemes. -/
theorem toScheme_map_sectionFibreLift_comp_sectionFibreBaseChangeComparison :
    (BigFppfOver.toScheme B S hS).map (sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) ≫
      (BigFppfOver.toScheme B S hS).map (sectionFibreBaseChangeComparison X E hE hb g hb' u v h
      hvh) =
      (BigFppfOver.toScheme B S hS).map h ≫ (BigFppfOver.toScheme B S hS).map
        (sectionFibreLift X E hE hb σ hσ T u) :=
  map_comp_eq_map_comp _ (sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u
    v h hvh σ hσ σ' hσ' comm)

include comm in
/-- The outer square `k'_v`, `σ` over `v ≫ g` of the paste. -/
theorem sectionFibreLift_baseChange_outer_w :
    yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) ≫
      ((pointHom (X := relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreToSpace T' v)) ≫ (projectiveBundleBaseChange X E hE hb g hb')) =
      (pointHom v ≫ g) ≫ σ :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (projectiveBundleBaseChange X E hE hb g hb'))
    (isPullback_sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T'
      v).w.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (pointHom v ≫ ·) comm).trans
      (Category.assoc _ _ _).symm)))

/-- A morphism into a piece of a conormal algebra, read through an identification `κ` of that
piece, followed by the map of conormal algebras through `κ`, is the map of conormal algebras. -/
theorem modulePullback_map_comp_inv_conormalAlgebraPieceSquareMapOfIso
    {U₀ X₀ Z₀ ZU₀ : AlgebraicSpaces B S hS} (p : ZU₀ ⟶ Z₀) (iU : ZU₀ ⟶ U₀) (i : Z₀ ⟶ X₀)
    (φ : U₀ ⟶ X₀) (hsq : iU ≫ φ = p ≫ i) (n : ℤ) {M N : Modules.{u, u} B S hS Z₀.1 Z₀.2}
    (κ : M ≅ (conormalAlgebra B S hS i).piece n) (a : N ⟶ (conormalAlgebra B S hS i).piece n) :
    (modulePullback B S hS p).map (a ≫ κ.inv) ≫
        conormalAlgebraPieceSquareMapOfIso B S hS p iU i φ hsq n κ =
      (modulePullback B S hS p).map a ≫ conormalAlgebraPieceSquareMap B S hS p iU i φ hsq n :=
  (congrArg (· ≫ conormalAlgebraPieceSquareMapOfIso B S hS p iU i φ hsq n κ)
    ((modulePullback B S hS p).map_comp a κ.inv)).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Iso.map_inv_hom_id_assoc κ (modulePullback B S hS p) _)))

/-- **Two stacked squares through identifications of the pieces**: `p₂^*` of the map of conormal
algebras of the first square read through `κ` and `κ'`, followed by the map of the second square
through `κ'`, is the composition comparison followed by the map of the outer square through `κ`. -/
theorem modulePullback_map_conormalAlgebraPieceSquareMapOfIsos_comp
    {X₀ Z₀ U₁ U₂ Z₁ Z₂ : AlgebraicSpaces B S hS} (i : Z₀ ⟶ X₀) (p₁ : Z₁ ⟶ Z₀)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X₀) (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁)
    (h₁ : iU₁ ≫ φ₁ = p₁ ≫ i) (h₂ : iU₂ ≫ φ₂ = p₂ ≫ iU₁)
    (h₁₂ : iU₂ ≫ (φ₂ ≫ φ₁) = (p₂ ≫ p₁) ≫ i) (n : ℤ)
    {M : Modules.{u, u} B S hS Z₀.1 Z₀.2} (κ : M ≅ (conormalAlgebra B S hS i).piece n)
    {M' : Modules.{u, u} B S hS Z₁.1 Z₁.2} (κ' : M' ≅ (conormalAlgebra B S hS iU₁).piece n) :
    (modulePullback B S hS p₂).map
        (conormalAlgebraPieceSquareMapOfIsos B S hS p₁ iU₁ i φ₁ h₁ n κ κ') ≫
      conormalAlgebraPieceSquareMapOfIso B S hS p₂ iU₂ iU₁ φ₂ h₂ n κ' =
    (modulePullbackCompIso B S hS p₂ p₁).hom.app M ≫
      conormalAlgebraPieceSquareMapOfIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n κ :=
  (modulePullback_map_comp_inv_conormalAlgebraPieceSquareMapOfIso p₂ iU₂ iU₁ φ₂ h₂ n κ'
    (conormalAlgebraPieceSquareMapOfIso B S hS p₁ iU₁ i φ₁ h₁ n κ)).trans
    ((conormalAlgebraPieceSquareMapOfIso_comp_of_eq B S hS i p₁ iU₁ φ₁ p₂ iU₂ φ₂ h₁ h₂
      (p₂ ≫ p₁) rfl (φ₂ ≫ φ₁) rfl h₁₂ n κ).symm.trans (congrArg (_ ≫ ·) (Category.id_comp _)))

/-- Bookkeeping for pasting two descriptions of a map through a common outer map `O`, in a bare
category. -/
theorem _root_.CategoryTheory.conormalTargetPaste_right {𝒟 : Type*} [Category 𝒟]
    {A B B' D Z : 𝒟} (L : A ⟶ Z) (a : A ⟶ B) (e₁ : B ⟶ B') (e₂ : B' ⟶ B) (i : B' ⟶ D)
    (j : D ⟶ B') (O : B ⟶ Z) (R : D ⟶ Z) (hA : L = a ≫ O) (hB : j ≫ e₂ ≫ O = R)
    (hij : i ≫ j = 𝟙 _) (he : e₁ ≫ e₂ = 𝟙 _) :
    L = a ≫ e₁ ≫ i ≫ R := by
  rw [← hB, reassoc_of% hij, reassoc_of% he, hA]

/-- **The right half of the paste of the target maps**, `u` étale: the composition comparison
along `h` and `u` followed by the map of conormal algebras of the outer square is `h^*` of the
chart isomorphism at `u` followed by the map of the square of sections `k'_v`, `k_u`. -/
theorem sectionConormalTargetBaseChangeHom_paste_right (hu : IsEtale B S hS u) :
    (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u)).hom.app
      (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
      eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
        (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u).symm) ≫
          (conormalAlgebraPieceSquareMapOfIso B S hS (pointHom v ≫ g)
          (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)) σ
          ((pointHom (X := relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
          ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibreToSpace T' v)) ≫
          (projectiveBundleBaseChange X E hE hb g hb'))
          (sectionFibreLift_baseChange_outer_w X E hE hb g hb' v σ σ' hσ' comm) 1
          (sectionConormalTargetPieceIso X E hE hb σ hσ)) =
    (modulePullback B S hS (yonedaSpaceMap h)).map
        (sectionConormalChartIso X E hE hb σ hσ T u hu).hom ≫
          (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap h)
          (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v))
          (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T u))
          (yonedaSpaceMap (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh))
          (yonedaSpaceMap_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v
          h hvh σ hσ σ' hσ' comm) 1) := by
  have hB := conormalAlgebraPieceSquareMapOfIso_comp_of_eq B S hS σ (pointHom u) _ _ _ _ _
    (isPullback_sectionFibreLift X E hE hb σ hσ T u).w.symm
    (yonedaSpaceMap_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v h
      hvh σ hσ σ' hσ' comm) _
    (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u).symm _
    (yonedaSpaceMap_sectionFibreBaseChangeComparison_comp_pointHom X E hE hb g hb' u v h hvh)
    (sectionFibreLift_baseChange_outer_w X E hE hb g hb' v σ σ' hσ' comm) 1
    (sectionConormalTargetPieceIso X E hE hb σ hσ)
  exact hB.trans (congrArg (fun a => (modulePullback B S hS (yonedaSpaceMap h)).map a ≫ _)
    (sectionConormalTargetPointHom_eq_chartIso X E hE hb σ hσ T u hu))

/-- The target map at the scheme point `v` of `X'`, as the map of conormal algebras of the fibre
square through `sectionConormalTargetPieceIso`. -/
theorem sectionConormalTargetPointHom_baseChange_eq :
    sectionConormalTargetPointHom X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v =
      conormalAlgebraPieceSquareMapOfIso B S hS (pointHom v)
      (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)) σ'
      (pointHom (X := relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
      ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      hb').relativeProjPoints.fibreToSpace T' v))
      (isPullback_sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v).w.symm 1
      (M := (sectionConormalTarget X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))
      (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ') := rfl

/-- The base-change map of the target as the map of conormal algebras of the square of `σ'`,
`g`, `σ` and `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`, through the identifications of both conormal modules. -/
theorem sectionConormalTargetBaseChangeHom_eq :
    sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm =
      conormalAlgebraPieceSquareMapOfIsos B S hS g σ' σ (projectiveBundleBaseChange X E hE hb g hb')
      comm 1 (M := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2
      σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
            (sectionConormalTargetPieceIso X E hE hb σ hσ)
            (M' := (sectionConormalTarget X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))
            (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ') := rfl

/-- The left side of the paste of the target maps, with both maps written out as maps of
conormal algebras. -/
theorem sectionConormalTargetBaseChangeHom_comp_pointHom_eq :
    (modulePullback B S hS (pointHom v)).map
        (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm) ≫
      sectionConormalTargetPointHom X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v =
    (modulePullback B S hS (pointHom v)).map
      (conormalAlgebraPieceSquareMapOfIsos B S hS g σ' σ
      (projectiveBundleBaseChange X E hE hb g hb') comm 1
      (M := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
            (sectionConormalTargetPieceIso X E hE hb σ hσ)
            (M' := (sectionConormalTarget X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))
            (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')) ≫
            conormalAlgebraPieceSquareMapOfIso B S hS (pointHom v)
            (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)) σ'
            (pointHom (X := relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
            ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibreToSpace T' v))
            (isPullback_sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T'
            v).w.symm 1 (M := (sectionConormalTarget X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))
            (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ') := by
  rw [sectionConormalTargetBaseChangeHom_eq X E hE hb g hb' σ hσ σ' hσ' comm,
    sectionConormalTargetPointHom_baseChange_eq X E hE g hb' v σ' hσ']

/-- The left side of the paste of the target maps, written out, is the map of conormal algebras
of the outer square `k'_v`, `σ` over `v ≫ g` after the composition comparison of Stacks 03LU. -/
theorem conormalAlgebraPieceSquareMapOfIsos_baseChange_paste_left :
    (modulePullback B S hS (pointHom v)).map
      (conormalAlgebraPieceSquareMapOfIsos B S hS g σ' σ
      (projectiveBundleBaseChange X E hE hb g hb') comm 1
      (M := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
            (sectionConormalTargetPieceIso X E hE hb σ hσ)
            (M' := (sectionConormalTarget X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))
            (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')) ≫
            conormalAlgebraPieceSquareMapOfIso B S hS (pointHom v)
            (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)) σ'
            (pointHom (X := relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
            ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibreToSpace T' v))
            (isPullback_sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T'
            v).w.symm 1 (M := (sectionConormalTarget X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))
            (sectionConormalTargetPieceIso X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ') =
    (modulePullbackCompIso B S hS (pointHom v) g).hom.app
      (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
            (conormalAlgebraPieceSquareMapOfIso B S hS (pointHom v ≫ g)
            (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)) σ
            ((pointHom (X := relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
            ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibreToSpace T' v)) ≫
            (projectiveBundleBaseChange X E hE hb g hb'))
            (sectionFibreLift_baseChange_outer_w X E hE hb g hb' v σ σ' hσ' comm) 1
            (sectionConormalTargetPieceIso X E hE hb σ hσ)) :=
  modulePullback_map_conormalAlgebraPieceSquareMapOfIsos_comp _ _ _ _ _ _ _ comm _ _ _ _ _

/-- **The left half of the paste of the target maps**: `v^*` of the base-change map followed by
the target map at `v` is, through the composition comparison of Stacks 03LU, the map of conormal
algebras of the outer square `k'_v`, `σ` over `v ≫ g`. -/
theorem sectionConormalTargetBaseChangeHom_paste_left :
    (modulePullback B S hS (pointHom v)).map
        (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm) ≫
      sectionConormalTargetPointHom X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v =
    (modulePullbackCompIso B S hS (pointHom v) g).hom.app
      (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
            (conormalAlgebraPieceSquareMapOfIso B S hS (pointHom v ≫ g)
            (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)) σ
            ((pointHom (X := relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
            ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').relativeProjPoints.fibreToSpace T' v)) ≫
            (projectiveBundleBaseChange X E hE hb g hb'))
            (sectionFibreLift_baseChange_outer_w X E hE hb g hb' v σ σ' hσ' comm) 1
            (sectionConormalTargetPieceIso X E hE hb σ hσ)) :=
  (sectionConormalTargetBaseChangeHom_comp_pointHom_eq X E hE hb g hb' v σ hσ σ' hσ' comm).trans
    (conormalAlgebraPieceSquareMapOfIsos_baseChange_paste_left X E hE hb g hb' v σ hσ σ' hσ' comm)

/-- **The paste of the target maps along `v ≫ g = u ∘ h`**, `u` étale: `v^*` of the base-change
map `g^*𝒞_σ ⟶ 𝒞_{σ'}` followed by the target map at `v` is, through the composition comparisons
of Stacks 03LU, `h^*` of the chart isomorphism at `u` followed by the map of conormal algebras of
the square of sections `k'_v`, `k_u` over `h`.  Both are the map of conormal algebras of the outer
square `k'_v`, `σ` over `v ≫ g`. -/
theorem sectionConormalTargetBaseChangeHom_paste (hu : IsEtale B S hS u) :
    (modulePullback B S hS (pointHom v)).map
        (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm) ≫
      sectionConormalTargetPointHom X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v =
    (modulePullbackCompIso B S hS (pointHom v) g).hom.app
      (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
      eqToHom (congrArg (fun k : yonedaSpace B S hS T' ⟶ X => (modulePullback B S hS k).obj
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
        (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g = yonedaSpaceMap h ≫ pointHom u)) ≫
      (modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u)).inv.app
        (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))) ≫
      (modulePullback B S hS (yonedaSpaceMap h)).map
        (sectionConormalChartIso X E hE hb σ hσ T u hu).hom ≫
          (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap h)
          (yonedaSpaceMap (sectionFibreLift X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v))
          (yonedaSpaceMap (sectionFibreLift X E hE hb σ hσ T u))
          (yonedaSpaceMap (sectionFibreBaseChangeComparison X E hE hb g hb' u v h hvh))
          (yonedaSpaceMap_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v
          h hvh σ hσ σ' hσ' comm) 1) :=
  CategoryTheory.conormalTargetPaste_right _ _ _ _ _ _ _ _
    (sectionConormalTargetBaseChangeHom_paste_left X E hE hb g hb' v σ hσ σ' hσ' comm)
    (sectionConormalTargetBaseChangeHom_paste_right X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm hu)
    (Iso.inv_hom_id_app _ _) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))

/-- **The base change of a glued isomorphism read at a chart of the source** (generic): with the
reading `hφu` of `φu` at the chart `u` and the reading `hφv` of `φv` at the chart `v`, the base
change data of `AlgebraicGeometry.Space` style (`cK`, the base changes `pK`, `pC`, `pN` of the
reading, the comparisons `mK`, `mC`), the combined source square `hpt`, the naturality `hnat`, the
paste `hpaste` of the target maps and the naturality `hz` of the reading of conormal modules,
`R'` reads `φx ≫ tB` as `sB ≫ φv`. -/
theorem _root_.CategoryTheory.Functor.conormalGlue_baseChange {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [Category ℬ] [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ 𝒟) (R : ℬ ⥤ 𝒞) (R' : 𝒜 ⥤ 𝒟)
    (Φ : ℬ ⥤ 𝒜) {Ku Cu Nk : ℬ} {Kx Cx Cv Nk' Kv : 𝒜} {a₁ a₂ a₃ : 𝒞} {b₁ b₂ b₃ : 𝒟}
    (φu : Ku ⟶ Cu) (φx : Kx ⟶ Cx) (Ch : Cu ≅ Nk) (tB : Cx ⟶ Cv) (Ch' : Cv ≅ Nk')
    (Z : R.obj Nk ≅ a₃) (Z' : R'.obj Nk' ≅ b₃)
    (s : R.obj Ku ⟶ a₁) (hs : IsIso s) (θ : a₁ ≅ a₂) (F : a₂ ≅ a₃)
    (sB : Kx ⟶ Kv) (φv : Kv ⟶ Cv) (s' : R'.obj Kv ⟶ b₁) (hs' : IsIso s') (θ' : b₁ ≅ b₂)
    (F' : b₂ ≅ b₃)
    (cK : R'.obj Kx ⟶ P.obj (R.obj Ku)) (pK : P.obj (R.obj Ku) ⟶ R'.obj (Φ.obj Ku))
    (mK : Φ.obj Ku ⟶ Kx) (pC : P.obj (R.obj Cu) ⟶ R'.obj (Φ.obj Cu))
    (pN : P.obj (R.obj Nk) ⟶ R'.obj (Φ.obj Nk)) (mC : Φ.obj Cu ⟶ Cx) (sq : Φ.obj Nk ⟶ Nk')
    (cbk : P.obj a₃ ⟶ b₃)
    (hφu : R.map φu = (@asIso _ _ _ _ s hs ≪≫ θ ≪≫ F ≪≫ Z.symm ≪≫ (R.mapIso Ch).symm).hom)
    (hφv : R'.map φv = (@asIso _ _ _ _ s' hs' ≪≫ θ' ≪≫ F' ≪≫ Z'.symm ≪≫ (R'.mapIso Ch').symm).hom)
    (hcK : cK ≫ pK ≫ R'.map mK = 𝟙 _)
    (hpt : cK ≫ P.map s ≫ P.map θ.hom ≫ P.map F.hom ≫ cbk = R'.map sB ≫ s' ≫ θ'.hom ≫ F'.hom)
    (nK : P.map (R.map φu) ≫ pC = pK ≫ R'.map (Φ.map φu))
    (nC : P.map (R.map Ch.hom) ≫ pN = pC ≫ R'.map (Φ.map Ch.hom))
    (hnat : Φ.map φu ≫ mC = mK ≫ φx) (hpaste : mC ≫ tB ≫ Ch'.hom = Φ.map Ch.hom ≫ sq)
    (hz : pN ≫ R'.map sq ≫ Z'.hom = P.map Z.hom ≫ cbk) :
    R'.map φx ≫ R'.map tB = R'.map sB ≫ R'.map φv := by
  have k₁ := CategoryTheory.Functor.conormalGlue_point P R R' Φ φu φx Ch (tB ≫ Ch'.hom) Z Z'.hom
    s hs θ F (cK ≫ P.map s ≫ P.map θ.hom ≫ P.map F.hom ≫ cbk) (𝟙 b₃) (𝟙 b₃) cK pK mK pC pN mC sq
    (P.map θ.hom ≫ P.map F.hom ≫ cbk) (P.map F.hom ≫ cbk) cbk hφu hcK rfl
    (Category.comp_id _) (Category.comp_id _) nK nC hnat hpaste hz
  have k₂ : R'.map φv ≫ R'.map Ch'.hom ≫ Z'.hom = s' ≫ θ'.hom ≫ F'.hom := by
    rw [hφv]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_inv, Category.assoc]
    rw [← R'.map_comp_assoc, Iso.inv_hom_id, R'.map_id, Category.id_comp, Iso.inv_hom_id,
      Category.comp_id]
  rw [Category.comp_id, Category.comp_id, hpt, ← k₂, R'.map_comp] at k₁
  have k₃ := k₁.trans (Category.assoc _ _ _).symm
  simp only [← Category.assoc] at k₃
  simpa only [Category.assoc] using (cancel_mono (R'.map Ch'.hom)).1 ((cancel_mono Z'.hom).1 k₃)

end AlgebraicGeometry.Space

end
