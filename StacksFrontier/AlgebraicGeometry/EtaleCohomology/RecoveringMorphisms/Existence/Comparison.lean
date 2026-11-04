module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.ComparisonPresentations

/-!
# The comparison `g⁻¹h_{V'} ⟶ h_{X ×_Y V'}`

Let `g` be a morphism of locally ringed topoi between the small étale ringed topoi of `X` and `Y`
and `f : X ⟶ Y` the morphism of schemes glued from it
(`AlgebraicGeometry.glueHom`).  For an object `V'` of the small étale site of `Y`, a morphism
`c : g⁻¹h_{V'} ⟶ h_{X ×_Y V'}` is a *comparison* (`AlgebraicGeometry.IsComparison`) when for every
section `b` of `𝒪_Y` over `V'`,
`c ≫ (pr₂^* b) = g⁻¹(b) ≫ g^♯` as generalized elements `g⁻¹h_{V'} ⟶ 𝒪_X`.

For `V'` affine and lying over an affine open `V` of `Y`, a comparison exists
(`AlgebraicGeometry.exists_isComparison`) and is unique
(`AlgebraicGeometry.IsComparison.eq`).  This is step (3) of the proof of Stacks 04I6, in the
relative form needed for Stacks 04I7: the comparison is the "unique dotted arrow" of the source's
diagram, produced from a standard presentation of `Γ(V', ⊤)` over `Γ(V, ⊤)`, and its defining
property is stated for all sections so that it no longer depends on the presentation.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry

/-! ### Evaluation of generalized elements on sections -/

section Eval

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Evaluation of generalized elements of shape `Z` on a section of `Z` over `U`, as a ring
homomorphism to `Γ(U, ⊤)`. -/
def evalRingHom {Z : Sheaf (SmallEtale.topology B S hS) (Type u)} (U : SmallEtale B S hS)
    (t : Z.obj.obj (op U)) :
    (Z ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) →+*
      ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) :=
  (smallEtaleSectionRingEquiv B S hS U).toRingHom.comp
    (Sheaf.compRingHom ((SmallEtale.topology B S hS).yonedaEquiv.symm t))

/-- The evaluation ring homomorphism sends `a` to the component of `a` at `U` applied to `t`. -/
theorem evalRingHom_apply {Z : Sheaf (SmallEtale.topology B S hS) (Type u)}
    (U : SmallEtale B S hS) (t : Z.obj.obj (op U))
    (a : Z ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) :
    evalRingHom B S hS U t a = a.hom.app (op U) t :=
  (hom_app_eq_smallEtaleSectionRingEquiv B S hS a U t).symm

end Eval

/-- The projection `X ×_Y V' ⟶ V'` of the base change, on global functions. -/
abbrev baseChangeRingHom {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)
    (V' : SmallEtale B Y.obj Y.property) :
    ↥Γ((SmallEtale.toScheme B Y.obj Y.property).obj V', ⊤) →+*
      ↥Γ((SmallEtale.toScheme B X.obj X.property).obj ((smallEtaleBaseChange B f).obj V'), ⊤) :=
  ((structureSharp B f).hom.app (op V')).hom

/-- The morphism of schemes attached to `z : U ⟶ X ×_Y V'` is the morphism underlying `z`
followed by the projection `X ×_Y V' ⟶ V'`. -/
theorem baseChangeSchemeHom_eq {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)
    (V' : SmallEtale B Y.obj Y.property) (U : SmallEtale B X.obj X.property)
    (z : U ⟶ (smallEtaleBaseChange B f).obj V') :
    baseChangeSchemeHom f U V' z = (SmallEtale.toScheme B X.obj X.property).map z ≫
      B.inclusion.map (pullback.fst V'.obj.hom f) := by
  have := smallEtaleBaseChangeSchemeHomEquiv_naturality f z V' (𝟙 _)
  simp only [Category.comp_id, smallEtaleBaseChangeSchemeHomEquiv_apply_coe] at this
  rw [this]
  rfl

section Comparison

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme}
  (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))

/-- **A comparison `g⁻¹h_{V'} ⟶ h_{X ×_Y V'}`**: a morphism carrying, for every section `b` of
`𝒪_Y` over `V'`, the pullback `pr₂^* b` to `g⁻¹(b)` followed by the structure map of `g`. -/
def IsComparison (V' : SmallEtale B Y.obj Y.property)
    (c : g.toToposHom.inverseImage.obj ((smallEtaleYoneda B Y.obj Y.property).obj V') ⟶
      (smallEtaleYoneda B X.obj X.property).obj ((smallEtaleBaseChange B (glueHom g)).obj V')) :
    Prop :=
  ∀ b : ↥Γ((SmallEtale.toScheme B Y.obj Y.property).obj V', ⊤),
    c ≫ (smallEtaleSectionRingEquiv B X.obj X.property _).symm
        (baseChangeRingHom (glueHom g) V' b) =
      g.toToposHom.inverseImage.map ((smallEtaleSectionRingEquiv B Y.obj Y.property V').symm b) ≫
        g.fSharpSet

variable (hg : g.IsLocallyRinged) (V : Y.obj.affineOpens)
  {V' : SmallEtale B Y.obj Y.property} [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V')]
  (k : V' ⟶ openObj B Y.obj Y.property V) {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n)
    Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤))
  (pres : Stacks.EtaleCohomology.StandardPresentationOver
    ((SmallEtale.toScheme B Y.obj Y.property).obj V')
    ((SmallEtale.toScheme B Y.obj Y.property).map k) P)

/-- The `i`-th coordinate of the target row is the section `xᵢ` of `𝒪_Y` over `V'`. -/
theorem targetRelPresentation_coord (i : Fin n) :
    (targetRelPresentation V k P pres).coord i =
      (smallEtaleSectionRingEquiv B Y.obj Y.property V').symm
        (pres.iso.inv.hom (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i))) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U =>
    TypeCat.homEquiv.injective (funext fun z => ?_)))
  exact (smallEtaleSectionRingEquiv_symm_hom_app B Y.obj Y.property V' _ U z).symm

/-- The `i`-th coordinate of the source row is the pullback `pr₂^* xᵢ`. -/
theorem sourceRelPresentation_coord (i : Fin n) :
    (sourceRelPresentation g V k P pres hg).coord i =
      (smallEtaleSectionRingEquiv B X.obj X.property _).symm
        (baseChangeRingHom (glueHom g) V'
          (pres.iso.inv.hom
            (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)))) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => TypeCat.homEquiv.injective
    (funext fun (z : U.unop ⟶ (smallEtaleBaseChange B (glueHom g)).obj V') => ?_)))
  refine Eq.trans ?_ (smallEtaleSectionRingEquiv_symm_hom_app B X.obj X.property _ _ U z).symm
  show (pres.iso.inv ≫ (baseChangeSchemeHom (glueHom g) U.unop V' z).appTop).hom
    (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)) = _
  rw [baseChangeSchemeHom_eq, Scheme.Hom.comp_appTop]
  rfl

/-- On `X ×_Y V'`, the pullback of a section of `𝒪_Y` over `V` along `X ×_Y V' ⟶ V' ⟶ V` is the
pullback of its image under `φ_V` along `X ×_Y V' ⟶ W_V`. -/
theorem baseChangeRingHom_appTop
    (b : Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤)) :
    baseChangeRingHom (glueHom g) V' (((SmallEtale.toScheme B Y.obj Y.property).map k).appTop b) =
      smallEtaleRestrict B X.obj X.property (sourceRelPresentation g V k P pres hg).over
        (openRingHomObj g V b) := by
  let U := (smallEtaleBaseChange B (glueHom g)).obj V'
  let over := (sourceRelPresentation g V k P pres hg).over
  have hsq : (SmallEtale.toScheme B X.obj X.property).map over ≫ openSchemeHom g V =
      B.inclusion.map (pullback.fst V'.obj.hom (glueHom g)) ≫
        (SmallEtale.toScheme B Y.obj Y.property).map k := by
    refine (cancel_mono (V : Y.obj.Opens).ι).1 ?_
    refine (smallEtaleMap_comp_glueHom g V over).symm.trans ?_
    refine (baseChangeSchemeHom_comp (glueHom g) U V' (𝟙 U)).symm.trans ?_
    exact (congrArg (_ ≫ ·) (smallEtaleMap_eq_comp k)).trans (Category.assoc _ _ _).symm
  have h1 := congrArg (fun φ => φ b) (appTop_comp_openSchemeHom g V
    ((SmallEtale.toScheme B X.obj X.property).map over))
  have h2 := congrArg (fun m => m.hom b) (Scheme.Hom.comp_appTop
    (B.inclusion.map (pullback.fst V'.obj.hom (glueHom g)))
      ((SmallEtale.toScheme B Y.obj Y.property).map k))
  exact h2.symm.trans ((congrArg (fun m => m.appTop.hom b) hsq).symm.trans h1)

/-- The presentation carries the constants to the pullbacks of global functions of `V`. -/
theorem pres_inv_C (b) :
    pres.iso.inv.hom (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.C b)) =
      ((SmallEtale.toScheme B Y.obj Y.property).map k).appTop.hom b := by
  have hc := congrArg (fun m => m.hom b) pres.comp_iso_hom
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    MvPolynomial.quotientSpanRangeStructureMap_apply] at hc
  rw [← hc, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

/-- The coefficients of the target row, as generalized elements of shape `h_{V'}`. -/
def targetCoeff :
    ↥Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤) →+*
      ((smallEtaleYoneda B Y.obj Y.property).obj V' ⟶
        Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B Y.obj Y.property)) :=
  (Sheaf.compRingHom ((smallEtaleYoneda B Y.obj Y.property).map k)).comp
    (smallEtaleSectionRingEquiv B Y.obj Y.property (openObj B Y.obj Y.property V)).symm.toRingHom

/-- The coefficients of the source row, as generalized elements of shape `h_{X ×_Y V'}`. -/
def sourceCoeff :
    ↥Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤) →+*
      ((smallEtaleYoneda B X.obj X.property).obj ((smallEtaleBaseChange B (glueHom g)).obj V') ⟶
        Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B X.obj X.property)) :=
  (Sheaf.compRingHom ((smallEtaleYoneda B X.obj X.property).map
      (sourceRelPresentation g V k P pres hg).over)).comp
    ((smallEtaleSectionRingEquiv B X.obj X.property
      (openObj B X.obj X.property (inverseImageOpen B X Y g V))).symm.toRingHom.comp
      (openRingHomObj g V))

/-- The coordinates of the target row, as generalized elements. -/
def targetCoord (i : Fin n) :
    (smallEtaleYoneda B Y.obj Y.property).obj V' ⟶
      Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B Y.obj Y.property) :=
  (targetRelPresentation V k P pres).coord i

/-- The coordinates of the source row, as generalized elements. -/
def sourceCoord (i : Fin n) :
    (smallEtaleYoneda B X.obj X.property).obj ((smallEtaleBaseChange B (glueHom g)).obj V') ⟶
      Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B X.obj X.property) :=
  (sourceRelPresentation g V k P pres hg).coord i

/-- A ring homomorphism out of a polynomial ring is the evaluation at its values on the
constants and the variables. -/
private theorem ringHom_apply_eq_eval₂ {A R : Type*} [CommRing A] [CommRing R] {σ : Type*}
    (φ : MvPolynomial σ A →+* R) (c : A →+* R) (v : σ → R)
    (hC : ∀ b, φ (MvPolynomial.C b) = c b) (hX : ∀ i, φ (MvPolynomial.X i) = v i)
    (Q : MvPolynomial σ A) : φ Q = MvPolynomial.eval₂ c v Q :=
  DFunLike.congr_fun (MvPolynomial.ringHom_ext (g := MvPolynomial.eval₂Hom c v)
    (fun b => (hC b).trans (MvPolynomial.eval₂_C c v b).symm)
    (fun i => (hX i).trans (MvPolynomial.eval₂_X c v i).symm)) Q

/-- **Every section of `𝒪_Y` over `V'`, as a generalized element, is a polynomial in the
coordinates.** -/
theorem targetSection_eq_eval₂
    (Q : MvPolynomial (Fin n)
      Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤)) :
    (smallEtaleSectionRingEquiv B Y.obj Y.property V').symm
        (pres.iso.inv.hom (Ideal.Quotient.mk (Ideal.span (Set.range P)) Q)) =
      MvPolynomial.eval₂ (targetCoeff V k) (targetCoord V k P pres)
        Q := by
  refine ringHom_apply_eq_eval₂
    ((smallEtaleSectionRingEquiv B Y.obj Y.property V').symm.toRingHom.comp
      (pres.iso.inv.hom.comp (Ideal.Quotient.mk (Ideal.span (Set.range P)))))
    _ _ (fun b => ?_) (fun i => ?_) Q
  · exact (congrArg (smallEtaleSectionRingEquiv B Y.obj Y.property V').symm
      (pres_inv_C V k P pres b)).trans
      (yoneda_map_comp_smallEtaleSectionRingEquiv_symm B Y.obj Y.property k b).symm
  · exact (targetRelPresentation_coord V k P pres i).symm

/-- **Every pullback `pr₂^* b` is the same polynomial in the coordinates of the source row.** -/
theorem sourceSection_eq_eval₂
    (Q : MvPolynomial (Fin n)
      Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤)) :
    (smallEtaleSectionRingEquiv B X.obj X.property _).symm
        (baseChangeRingHom (glueHom g) V'
          (pres.iso.inv.hom (Ideal.Quotient.mk (Ideal.span (Set.range P)) Q))) =
      MvPolynomial.eval₂ (sourceCoeff g hg V k P pres)
        (sourceCoord g hg V k P pres) Q := by
  refine ringHom_apply_eq_eval₂
    ((smallEtaleSectionRingEquiv B X.obj X.property _).symm.toRingHom.comp
      ((baseChangeRingHom (glueHom g) V').comp
        (pres.iso.inv.hom.comp (Ideal.Quotient.mk (Ideal.span (Set.range P))))))
    _ _ (fun b => ?_) (fun i => ?_) Q
  · exact (congrArg (fun x => (smallEtaleSectionRingEquiv B X.obj X.property _).symm
      (baseChangeRingHom (glueHom g) V' x)) (pres_inv_C V k P pres b)).trans
      ((congrArg (smallEtaleSectionRingEquiv B X.obj X.property _).symm
        (baseChangeRingHom_appTop g hg V k P pres b)).trans
      (yoneda_map_comp_smallEtaleSectionRingEquiv_symm B X.obj X.property _ _).symm)
  · exact (sourceRelPresentation_coord g hg V k P pres i).symm

/-- The coordinates of the target row solve the system, as generalized elements. -/
theorem isSolution_targetCoord :
    MvPolynomial.IsSolution P (targetCoeff V k) (targetCoord V k P pres) := by
  rw [MvPolynomial.isSolution_iff_forall_eval₂]
  intro j
  rw [← targetSection_eq_eval₂, MvPolynomial.quotientSpanRange_mk_eq_zero, map_zero, map_zero]

/-- The morphism `g⁻¹h_{V'} ⟶ g⁻¹h_V ≅ h_{W_V}`. -/
def comparisonOver :
    g.toToposHom.inverseImage.obj ((smallEtaleYoneda B Y.obj Y.property).obj V') ⟶
      openSheaf B X.obj X.property (inverseImageOpen B X Y g V) :=
  g.toToposHom.inverseImage.map ((smallEtaleYoneda B Y.obj Y.property).map k) ≫
    (inverseImageOpenIso g V).hom

/-- **The coefficients move along `g` as they should**: transporting the coefficient `b` of the
target row gives the coefficient `φ_V b` of the source row, read on `g⁻¹h_{V'}`. -/
theorem comparisonOver_comp_openRingHomObj (b) :
    comparisonOver g V k ≫ (smallEtaleSectionRingEquiv B X.obj X.property
        (openObj B X.obj X.property (inverseImageOpen B X Y g V))).symm (openRingHomObj g V b) =
      transportRingHom g (𝟙 _) (targetCoeff V k b) := by
  rw [smallEtaleSectionRingEquiv_symm_openRingHomObj, transportRingHom_apply]
  show (g.toToposHom.inverseImage.map ((smallEtaleYoneda B Y.obj Y.property).map k) ≫
    (inverseImageOpenIso g V).hom) ≫ _ = 𝟙 _ ≫ g.toToposHom.inverseImage.map
      ((smallEtaleYoneda B Y.obj Y.property).map k ≫ _) ≫ _
  rw [Functor.map_comp]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((inverseImageOpenIso g V).hom_inv_id_assoc _)).trans ?_)
  exact (Category.id_comp _).symm.trans (congrArg (𝟙 _ ≫ ·) (Category.assoc _ _ _).symm)

/-- The coordinates of the comparison: the inverse images of the coordinates of the target row,
followed by the structure map. -/
abbrev comparisonCoordinate (i : Fin n) :
    g.toToposHom.inverseImage.obj ((smallEtaleYoneda B Y.obj Y.property).obj V') ⟶
      Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B X.obj X.property) :=
  transportRingHom g (𝟙 _) (targetCoord V k P pres i)

/-- The comparison coordinates evaluated at a section `t` solve the relations `P`, with
coefficients the image of `t` under the comparison over the inverse image of `V`. -/
theorem isSolution_comparisonCoordinate (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (t : (g.toToposHom.inverseImage.obj
      ((smallEtaleYoneda B Y.obj Y.property).obj V')).obj.obj U) :
    MvPolynomial.IsSolution P (relCoeff B X.obj X.property (inverseImageOpen B X Y g V)
      (openRingHomObj g V) ((comparisonOver g V k).hom.app U t))
      (fun i => (comparisonCoordinate g V k P pres i).hom.app U t) := by
  have h1 := MvPolynomial.isSolution_comp (targetCoeff V k) (transportRingHom g (𝟙 _))
    (isSolution_targetCoord V k P pres)
  have h2 := MvPolynomial.isSolution_comp _ (evalRingHom B X.obj X.property U.unop t) h1
  have hcoef : (evalRingHom B X.obj X.property U.unop t).comp
      ((transportRingHom g (𝟙 _)).comp (targetCoeff V k)) =
      relCoeff B X.obj X.property (inverseImageOpen B X Y g V) (openRingHomObj g V)
        ((comparisonOver g V k).hom.app U t) := by
    ext b
    simp only [RingHom.comp_apply]
    rw [evalRingHom_apply, ← comparisonOver_comp_openRingHomObj g V k b]
    exact smallEtaleSectionRingEquiv_symm_hom_app B X.obj X.property _ _ U _
  have hv : (fun i => evalRingHom B X.obj X.property U.unop t
      (transportRingHom g (𝟙 _) (targetCoord V k P pres i))) =
      fun i => (comparisonCoordinate g V k P pres i).hom.app U t :=
    funext fun i => evalRingHom_apply B X.obj X.property U.unop t _
  rwa [hcoef, hv] at h2

/-- **The comparison `g⁻¹h_{V'} ⟶ h_{X ×_Y V'}`** of step (3) of the proof of Stacks 04I6, for a
chart `V'` over an affine open `V` with a standard presentation. -/
def comparison :
    g.toToposHom.inverseImage.obj ((smallEtaleYoneda B Y.obj Y.property).obj V') ⟶
      (smallEtaleYoneda B X.obj X.property).obj ((smallEtaleBaseChange B (glueHom g)).obj V') :=
  (sourceRelPresentation g V k P pres hg).homOfIsSolution _ (comparisonOver g V k)
    (fun i => comparisonCoordinate g V k P pres i) (isSolution_comparisonCoordinate g V k P pres)

/-- The comparison followed by the `i`-th coordinate of the source row is the `i`-th comparison
coordinate. -/
theorem comparison_comp_sourceCoord (i : Fin n) :
    comparison g hg V k P pres ≫ sourceCoord g hg V k P pres i =
      comparisonCoordinate g V k P pres i :=
  (sourceRelPresentation g V k P pres hg).homOfIsSolution_comp_coord _ _ _ _ i

/-- **The comparison is a comparison**: it carries `pr₂^* b` to `g⁻¹(b)` followed by `g^♯`, for
every section `b` of `𝒪_Y` over `V'`. -/
theorem isComparison_comparison : IsComparison g V' (comparison g hg V k P pres) := by
  intro b'
  obtain ⟨Q, hQ⟩ := Ideal.Quotient.mk_surjective (pres.iso.hom.hom b')
  obtain rfl : pres.iso.inv.hom (Ideal.Quotient.mk (Ideal.span (Set.range P)) Q) = b' := by
    rw [hQ, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [sourceSection_eq_eval₂ g hg V k P pres Q, targetSection_eq_eval₂ V k P pres Q]
  have hco : (Sheaf.compRingHom (comparison g hg V k P pres)).comp (sourceCoeff g hg V k P pres) =
      (transportRingHom g (𝟙 _)).comp (targetCoeff V k) := by
    refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply, Sheaf.compRingHom_apply]
    rw [← comparisonOver_comp_openRingHomObj g V k b]
    show comparison g hg V k P pres ≫ ((smallEtaleYoneda B X.obj X.property).map
      (sourceRelPresentation g V k P pres hg).over ≫ _) = _
    rw [← Category.assoc]
    exact congrArg (· ≫ _) (isSubterminal_openSheaf B X.obj X.property _ _ _)
  have h1 := MvPolynomial.eval₂_comp_left (Sheaf.compRingHom (comparison g hg V k P pres))
    (sourceCoeff g hg V k P pres) (sourceCoord g hg V k P pres) Q
  have h2 := MvPolynomial.eval₂_comp_left (transportRingHom g (𝟙 _))
    (targetCoeff V k) (targetCoord V k P pres) Q
  have hv : (Sheaf.compRingHom (comparison g hg V k P pres)) ∘ sourceCoord g hg V k P pres =
      (transportRingHom g (𝟙 _)) ∘ targetCoord V k P pres :=
    funext fun i => comparison_comp_sourceCoord g hg V k P pres i
  rw [hco, hv, ← h2] at h1
  refine h1.trans ?_
  rw [transportRingHom_apply]
  exact Category.id_comp _

include hg pres in
/-- **A comparison is unique.** -/
theorem IsComparison.eq {c₁ c₂ : g.toToposHom.inverseImage.obj
      ((smallEtaleYoneda B Y.obj Y.property).obj V') ⟶
      (smallEtaleYoneda B X.obj X.property).obj ((smallEtaleBaseChange B (glueHom g)).obj V')}
    (h₁ : IsComparison g V' c₁) (h₂ : IsComparison g V' c₂) : c₁ = c₂ := by
  refine (sourceRelPresentation g V k P pres hg).hom_ext c₁ c₂ fun i => ?_
  show c₁ ≫ sourceCoord g hg V k P pres i = c₂ ≫ sourceCoord g hg V k P pres i
  rw [sourceCoord, sourceRelPresentation_coord g hg V k P pres i, h₁, h₂]

end Comparison

end AlgebraicGeometry

end
