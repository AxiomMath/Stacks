module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftNatural

/-!
# Isomorphic lifts of `E₀` come from morphisms of `Complexes_{X/Y}`

Let `x₀` be a field point of `Complexes_{X/Y}` over `Spec k`, and `m : x₀ ⟶ A`, `m' : x₀ ⟶ A'`
two morphisms of `Complexes_{X/Y}` onto objects over the same test scheme `T = Spec k[V]`, with
the same base map `b : T₀ ⟶ T` and a retraction `t`. If the attached lifts of `E₀` to
`𝒪_{X₀}[𝒪_{X₀} ⊗_k V]` (`AlgebraicGeometry.Space.ComplexesSituation.fibreDataDerivedLift`) are
isomorphic, then `m'` is `m` followed by a morphism `A ⟶ A'` over the identity of `T`
(`AlgebraicGeometry.Space.ComplexesSituation.exists_comp_eq_of_fibreDataDerivedLift_isomorphic`):
the derived equivalence `D(𝒪_{X₀}[𝒪_{X₀} ⊗_k V]) ≌ D(𝒪_{X_T})` carries the isomorphism of lifts
to an isomorphism `E ≅ E'` compatible with the comparisons of `m` and `m'`. This is the converse
of the naturality `c3 (a)` and the core of the separation property `c3 (d)` of the proof of
Stacks 0DLL.

More generally a morphism `g : A.T ⟶ A'.T` of test schemes which is an identity of the underlying
objects of the site, compatible with the base maps and the retractions, lifts to a morphism
`A ⟶ A'` as soon as the lifts are isomorphic
(`AlgebraicGeometry.Space.ComplexesSituation.exists_hom_of_fibreDataDerivedLift_isomorphic`).
With the second component of the 2-fibre product this gives `c3 (d)`: two lifts of the base point
`w₀` of the fibre over `k[V]` with isomorphic images in `(Sch/V)` and isomorphic lifts of `E₀` are
isomorphic (`AlgebraicGeometry.Space.ComplexesSituation.fibreLift_nonempty_iso_of_isomorphic`),
so the classes of lifts of `E₀⟦m⟧` separate the classes of lifts of `w₀` with the same image in
`(Sch/V)` (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass_separates`): the
`separates` field of `Deformation.Artin.CoefficientLiftComparison`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe d u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 10000] HasDerivedCategory.standard

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS}

attribute [local instance] complexesCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : ComplexesObject D}
  {hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {hk : B.Contains (Spec (.of k))} {V : FGModuleCat.{u} k}
  [hDer : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]

/-- An isomorphism of the lifts of `E₀` attached to `m : x₀ ⟶ (T, E)` and `m' : x₀ ⟶ (T, E')`
with the same base map gives an isomorphism `E ≅ E'` carrying the comparison of `m'` to that of
`m`. -/
theorem exists_iso_of_fibreDataDerivedLift_isomorphic {T : SchemesOver D.Y}
    {E E' : derivedModules B S hS (D.space T)} {rp : D.IsRelativelyPerfect T E}
    {nn : D.HasNoNegativeFibreExt T E} {rp' : D.IsRelativelyPerfect T E'}
    {nn' : D.HasNoNegativeFibreExt T E'} (m : x₀ ⟶ ⟨T, E, rp, nn⟩)
    (φ' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj E' ⟶ x₀.E)
    [IsIso φ'] {t : T ⟶ x₀.T} (hbt : m.base ≫ t = 𝟙 x₀.T)
    (hb : IsSquareZeroClosedImmersion B S hS m.base.left)
    (hT : T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).obj V))
    (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m.base.left ≫
        eqToHom hT =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (h : DerivedLift.Isomorphic
      (fibreDataDerivedLift (hDer := hDer) ⟨T, E, rp, nn⟩ m t hbt hb hT hβ hK)
      (fibreDataDerivedLift (hDer := hDer) ⟨T, E', rp', nn'⟩
        (⟨m.base, φ', inferInstance⟩ : ComplexesHom x₀ ⟨T, E', rp', nn'⟩) t hbt hb hT hβ hK)) :
    ∃ ε : E ≅ E', ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map
      ε.hom ≫ φ' = m.fibre := by
  obtain ⟨e, he⟩ := h
  let eD := fibreDataDerivedEquivalence (hx₀ := hx₀) (hDer := hDer) T m.base t hbt hb hT hβ
  let P := (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)
  let e' : eD.inverse.obj E ≅ eD.inverse.obj E' := e
  change _ ≫ ((fibreDataDerivedPullbackIso (hx₀ := hx₀) T m.base t hbt hb hT hβ _).hom.app _ ≫
      P.map (eD.counitIso.hom.app E') ≫ φ') =
    (fibreDataDerivedPullbackIso (hx₀ := hx₀) T m.base t hbt hb hT hβ _).hom.app _ ≫
      P.map (eD.counitIso.hom.app E) ≫ m.fibre at he
  have he' := ((fibreDataDerivedPullbackIso (hx₀ := hx₀) T m.base t hbt hb hT hβ
      _).hom.naturality_assoc e'.hom (P.map (eD.counitIso.hom.app E') ≫ φ')).symm.trans he
  have he'' : P.map (eD.functor.map e'.hom) ≫ P.map (eD.counitIso.hom.app E') ≫ φ' =
      P.map (eD.counitIso.hom.app E) ≫ m.fibre :=
    (Iso.cancel_iso_hom_left ((fibreDataDerivedPullbackIso (hx₀ := hx₀) T m.base t hbt hb hT hβ
      _).app _) _ _).1 he'
  refine ⟨eD.counitIso.symm.app E ≪≫ eD.functor.mapIso e' ≪≫ eD.counitIso.app E', ?_⟩
  calc
    _ = P.map (eD.counitIso.inv.app E) ≫
          (P.map (eD.functor.map e'.hom) ≫ P.map (eD.counitIso.hom.app E') ≫ φ') := by
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
        Functor.map_comp, Category.assoc]
      rfl
    _ = P.map (eD.counitIso.inv.app E) ≫ (P.map (eD.counitIso.hom.app E) ≫ m.fibre) := by
      rw [he'']
    _ = m.fibre := by
      rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
        Category.id_comp]

/-- **Isomorphic lifts of `E₀` come from morphisms over the identity.** If the lifts of `E₀`
attached to `m : x₀ ⟶ (T, E)` and `m' : x₀ ⟶ (T, E')` with the same base map and retraction are
isomorphic, then `m'` is `m` followed by a morphism `(T, E) ⟶ (T, E')` of `Complexes_{X/Y}`
over `𝟙 T`. The converse of
`AlgebraicGeometry.Space.ComplexesSituation.fibreDataDerivedLift_isomorphic_of_id`. -/
theorem exists_comp_eq_of_fibreDataDerivedLift_isomorphic {T : SchemesOver D.Y}
    {E E' : derivedModules B S hS (D.space T)} {rp : D.IsRelativelyPerfect T E}
    {nn : D.HasNoNegativeFibreExt T E} {rp' : D.IsRelativelyPerfect T E'}
    {nn' : D.HasNoNegativeFibreExt T E'} (m : x₀ ⟶ ⟨T, E, rp, nn⟩)
    (φ' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj E' ⟶ x₀.E)
    [hφ' : IsIso φ'] {t : T ⟶ x₀.T} (hbt : m.base ≫ t = 𝟙 x₀.T)
    (hb : IsSquareZeroClosedImmersion B S hS m.base.left)
    (hT : T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).obj V))
    (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m.base.left ≫
        eqToHom hT =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (h : DerivedLift.Isomorphic
      (fibreDataDerivedLift (hDer := hDer) ⟨T, E, rp, nn⟩ m t hbt hb hT hβ hK)
      (fibreDataDerivedLift (hDer := hDer) ⟨T, E', rp', nn'⟩
        (⟨m.base, φ', inferInstance⟩ : ComplexesHom x₀ ⟨T, E', rp', nn'⟩) t hbt hb hT hβ hK)) :
    ∃ n : ComplexesHom ⟨T, E, rp, nn⟩ ⟨T, E', rp', nn'⟩, n.base = 𝟙 T ∧
      m.comp n = (⟨m.base, φ', inferInstance⟩ : ComplexesHom x₀ ⟨T, E', rp', nn'⟩) := by
  obtain ⟨ε, hε⟩ := exists_iso_of_fibreDataDerivedLift_isomorphic m φ' hbt hb hT hβ hK h
  obtain ⟨nf, hnfd⟩ : ∃ nf : ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (𝟙 T))).obj E' ⟶ E, nf = (D.idComparison T).hom.app E' ≫ ε.inv := ⟨_, rfl⟩
  have hnf : IsIso nf := hnfd ▸ @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance inferInstance
  refine ⟨⟨𝟙 T, nf, hnf⟩, rfl, ?_⟩
  let χ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj E' ⟶ x₀.E :=
    (D.relativeMapComparison (Category.comp_id m.base)).inv.app E' ≫
      (m.comp (A'' := ⟨T, E', rp', nn'⟩) ⟨𝟙 T, nf, hnf⟩).fibre
  have hχi : IsIso χ := @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
    (m.comp (A'' := ⟨T, E', rp', nn'⟩) ⟨𝟙 T, nf, hnf⟩).isIso_fibre
  have hχ : (⟨m.base, χ, hχi⟩ : ComplexesHom x₀ ⟨T, E', rp', nn'⟩) =
      m.comp (A'' := ⟨T, E', rp', nn'⟩) ⟨𝟙 T, nf, hnf⟩ :=
    ComplexesHom.ext (Category.comp_id m.base).symm
      (Functor.eqToHom_comp_eqToIso_inv_app _ E' _ _)
  have key : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map
      ((@asIso _ _ _ _ nf hnf).symm ≪≫ (D.idComparison T).app E').hom ≫ χ = m.fibre :=
    D.fibreComp_id_fibre_cancel m.base m.fibre nf hnf _ (ComplexesHom.comp_fibre _ _)
  have hεε : ((@asIso _ _ _ _ nf hnf).symm ≪≫ (D.idComparison T).app E').hom = ε.hom := by
    rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.app_hom, IsIso.inv_comp_eq, hnfd]
    simp
  rw [hεε] at key
  obtain rfl : φ' = χ := (Iso.cancel_iso_hom_left
    (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).mapIso ε) _ _).1
    (hε.trans key.symm)
  exact hχ.symm

/-- **The converse of the naturality of the lift of `E₀`.** Two morphisms `m : x₀ ⟶ A`,
`m' : x₀ ⟶ A'` of `Complexes_{X/Y}` with retractions, related by a morphism `g : A.T ⟶ A'.T` of
test schemes which is an identity of the underlying objects of the site, and with isomorphic
lifts of `E₀`, come from a morphism `n : A ⟶ A'` over `g` with `m ≫ n = m'`. -/
theorem exists_hom_of_fibreDataDerivedLift_isomorphic {A A' : ComplexesObject D} (m : x₀ ⟶ A)
    (m' : x₀ ⟶ A') (g : A.T ⟶ A'.T) (hg : m.base ≫ g = m'.base) {t : A.T ⟶ x₀.T}
    {t' : A'.T ⟶ x₀.T} (htg : t = g ≫ t') (h : A.T.left = A'.T.left)
    (hgl : g.left = eqToHom h)
    (hbt : m.base ≫ t = 𝟙 x₀.T) (hb : IsSquareZeroClosedImmersion B S hS m.base.left)
    (hT : A.T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).obj V))
    (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m.base.left ≫
        eqToHom hT =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hbt' : m'.base ≫ t' = 𝟙 x₀.T) (hb' : IsSquareZeroClosedImmersion B S hS m'.base.left)
    (hT' : A'.T.left =
      squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).obj V))
    (hβ' : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m'.base.left ≫
        eqToHom hT' =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (hiso : DerivedLift.Isomorphic (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK)
      (fibreDataDerivedLift (hDer := hDer) A' m' t' hbt' hb' hT' hβ' hK)) :
    ∃ n : A ⟶ A', n.base = g ∧ m ≫ n = m' := by
  obtain ⟨⟨Tl, ⟨⟨⟩⟩, Th⟩, E, rp, nn⟩ := A
  obtain ⟨⟨Tl', ⟨⟨⟩⟩, Th'⟩, E', rp', nn'⟩ := A'
  change Tl = Tl' at h
  subst h
  have hTh : Th = Th' := by
    have hw := CostructuredArrow.w g
    change _ = eqToHom rfl at hgl
    rw [hgl, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp] at hw
    exact hw.symm
  subst hTh
  have hg1 : g = 𝟙 _ := CostructuredArrow.hom_ext _ _ (by simpa using hgl)
  subst hg1
  rw [Category.id_comp] at htg
  subst htg
  obtain ⟨b', φ', hφ'⟩ := m'
  change m.base ≫ 𝟙 _ = b' at hg
  rw [Category.comp_id] at hg
  subst hg
  exact exists_comp_eq_of_fibreDataDerivedLift_isomorphic m φ' hbt hb hT hβ hK hiso

/-- The retraction of a lift of `w₀` factors through a morphism of test schemes induced by a
morphism of the `(Sch/V)`-components compatible with the comparisons. -/
theorem fibreLiftRetraction_eq_comp_of_snd {M : SiteModule k B}
    {y y' : FibreLift D iΛ x₀ hx₀ hk M} (ψ : y.1.right.y ⟶ y'.1.right.y)
    (g : fibreLiftScheme y ⟶ fibreLiftScheme y')
    (hg : g ≫ y'.1.right.iso.hom.down = y.1.right.iso.hom.down ≫
      ((schemePointToBase D.Y x₀.T.left x₀.T.hom).map ψ).down) :
    fibreLiftRetraction y = g ≫ fibreLiftRetraction y' := by
  have hb : ((schemePointToBase D.Y x₀.T.left x₀.T.hom).map ψ).down ≫
      CostructuredArrow.homMk (overMapHom x₀.T.left y'.1.right.y) rfl =
        CostructuredArrow.homMk (overMapHom x₀.T.left y.1.right.y) rfl := by
    apply CostructuredArrow.hom_ext
    show (Over.map x₀.T.left.hom).map ψ ≫ overMapHom x₀.T.left y'.1.right.y =
      overMapHom x₀.T.left y.1.right.y
    apply Over.OverMorphism.ext
    exact Over.w ψ
  unfold fibreLiftRetraction
  exact ((congrArg (y.1.right.iso.hom.down ≫ ·) hb.symm).trans
    (Category.assoc _ _ _).symm).trans
    ((congrArg (· ≫ CostructuredArrow.homMk (overMapHom x₀.T.left y'.1.right.y) rfl)
      hg.symm).trans (Category.assoc _ _ _))

/-- The fibre of lifts of `w₀` over `k[M]` is a groupoid. -/
theorem fibreLift_isGroupoid (M : SiteModule k B) :
    IsGroupoid (FibreLift D iΛ x₀ hx₀ hk M) :=
  (underPost_isFiberedInGroupoids _ (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (complexesFunctor_isFiberedInGroupoids D)
    (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
    (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
    (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom)) (fibreBasePoint D x₀)).fiber_isGroupoid _

/-- **Lifts of `w₀` with isomorphic `(Sch/V)`-components and isomorphic lifts of `E₀` are
isomorphic.** A morphism `ψ` of the `(Sch/V)`-components of two lifts `y, y'` of `w₀` over
`k[V]`, vertical and compatible with the maps from `w₀`, together with an isomorphism of the
lifts `AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedLift` of `E₀`, gives an
isomorphism `y ≅ y'`: the comparisons of the two components give a morphism `g` of test schemes,
an identity of the underlying objects of the site, and the isomorphism of lifts of `E₀` a
morphism of `Complexes_{X/Y}` over it
(`AlgebraicGeometry.Space.ComplexesSituation.exists_hom_of_fibreDataDerivedLift_isomorphic`). -/
theorem fibreLift_nonempty_iso_of_isomorphic
    {y y' : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V)}
    (ψ : y.1.right.y ⟶ y'.1.right.y)
    (hψ : (Over.map x₀.T.left.hom).IsHomLift
      (𝟙 (squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).obj V))) ψ)
    (hψb : y.1.hom.b ≫ ψ = y'.1.hom.b)
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (h : DerivedLift.Isomorphic (fibreLiftDerivedLift (hDer := hDer) y hK)
      (fibreLiftDerivedLift (hDer := hDer) y' hK)) :
    Nonempty (y ≅ y') := by
  obtain ⟨Γ, hΓd⟩ : ∃ Γ : (complexesToBaseObjects D).obj y.1.right.x ⟶
      (complexesToBaseObjects D).obj y'.1.right.x,
      Γ = y.1.right.iso.hom ≫ (schemePointToBase D.Y x₀.T.left x₀.T.hom).map ψ ≫
        y'.1.right.iso.inv := ⟨_, rfl⟩
  have hΓw : Γ ≫ y'.1.right.iso.hom =
      y.1.right.iso.hom ≫ (schemePointToBase D.Y x₀.T.left x₀.T.hom).map ψ := by
    rw [hΓd, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hFΓ : (complexesToBaseObjects D).map y.1.hom.a ≫ Γ =
      (complexesToBaseObjects D).map y'.1.hom.a := by
    rw [hΓd, y.1.hom.w_assoc, ← Functor.map_comp_assoc, hψb, ← y'.1.hom.w_assoc,
      Iso.hom_inv_id, Category.comp_id]
  let g : fibreLiftScheme y ⟶ fibreLiftScheme y' := Γ.down
  have hg : y.1.hom.a.base ≫ g = y'.1.hom.a.base := congrArg ULift.down hFΓ
  have htg : fibreLiftRetraction y = g ≫ fibreLiftRetraction y' :=
    fibreLiftRetraction_eq_comp_of_snd ψ g (congrArg ULift.down hΓw)
  have hl : (fibreLiftScheme y).left = (fibreLiftScheme y').left :=
    (fibreLiftScheme_left_eq y).trans (fibreLiftScheme_left_eq y').symm
  have e3 := IsHomLift.fac' (Over.map x₀.T.left.hom)
    (𝟙 (squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).obj V))) ψ
  have hgl : g.left = eqToHom hl := by
    have := y.1.right.vertical
    have := y'.1.right.vertical
    have e1 := IsHomLift.fac' (baseProj D.Y) (𝟙 y.1.right.base) y.1.right.iso.hom
    have e2 := IsHomLift.fac' (baseProj D.Y) (𝟙 y'.1.right.base) y'.1.right.iso.inv
    show (baseProj D.Y).map Γ = _
    rw [hΓd, Functor.map_comp, Functor.map_comp, e1, e2]
    show _ ≫ (Over.map x₀.T.left.hom).map ψ ≫ _ = _
    rw [e3]
    simp only [Category.id_comp, eqToHom_trans]
    exact eqToHom_comp_comp_eqToHom_of_eq _ _ _ _ _ rfl
  rw [fibreLiftDerivedLift_eq, fibreLiftDerivedLift_eq] at h
  obtain ⟨n, hn, hmn⟩ := exists_hom_of_fibreDataDerivedLift_isomorphic (hDer := hDer)
    y.1.hom.a y'.1.hom.a g hg htg hl hgl _ _ _ _ _ _ _ _ hK h
  have hbase : y.1.right.base = y'.1.right.base :=
    (congrArg Under.right y.2).trans (congrArg Under.right y'.2).symm
  have hFn : (complexesToBaseObjects D).map n = Γ := ULift.ext hn
  have hna : (complexesFunctor D).IsHomLift (eqToHom hbase) n := by
    refine IsHomLift.of_fac' _ _ _ y.1.right.hx y'.1.right.hx ?_
    show n.base.left = _
    rw [hn, hgl]
    simp only [eqToHom_trans]
    rfl
  have hψb' : (Over.map x₀.T.left.hom).IsHomLift (eqToHom hbase) ψ := by
    refine IsHomLift.of_fac' _ _ _ y.1.right.hy y'.1.right.hy ?_
    rw [e3]
    simp
  let R : y.1.right ⟶ y'.1.right :=
    { hbase := eqToHom hbase
      a := n
      b := ψ
      ha := hna
      hb := hψb'
      w := by rw [hFn, hΓw] }
  have hR : y.1.hom ≫ R = y'.1.hom := TwoFibreProductOver.Hom.ext' hmn hψb
  have hRl : (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
      (baseProj D.Y) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom)).IsHomLift
      (𝟙 (squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).obj V))) R := by
    refine IsHomLift.of_fac' _ _ _ (congrArg Under.right y.2) (congrArg Under.right y'.2) ?_
    show eqToHom hbase = _
    rw [Category.id_comp]
    exact (eqToHom_trans _ _).symm
  have hgpd := fibreLift_isGroupoid (D := D) (iΛ := iΛ) (x₀ := x₀) (hx₀ := hx₀) (hk := hk)
    ((fgSiteModule B hk).obj V)
  let θ : y ⟶ y' := underFiberHomMk _ (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
    (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      ((fgSiteModule B hk).obj V)) (s := y) (t := y') R hRl hR
  have : IsIso θ := IsGroupoid.all_isIso θ
  exact ⟨asIso θ⟩

/-- **Stacks 0DLL, `c3 (d)`: the classes of lifts of `E₀⟦m⟧` separate the lifts of `w₀` with
the same image in `(Sch/V)`.** Two classes `a, b` of lifts of `w₀` over `k[V]` with the same
class of `(Sch/V)`-components (`Deformation.Artin.sndLiftClass`) and the same class of lifts of
`E₀⟦m⟧` (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass`) are equal. -/
theorem fibreLiftClass_separates (hK : DerivedCategory.TStructure.t.minus x₀.E) (m : ℤ)
    (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧))
    (a b : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      hk (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
      (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
      ((fgSiteModule B hk).obj V))
    (h𝒵 : sndLiftClass B S hS iΛ hk (complexesFunctor D) (baseProj D.Y)
        (Over.map x₀.T.left.hom) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom) (fibreBasePoint D x₀)
        (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) _ a =
      sndLiftClass B S hS iΛ hk (complexesFunctor D) (baseProj D.Y)
        (Over.map x₀.T.left.hom) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom) (fibreBasePoint D x₀)
        (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) _ b)
    (h : fibreLiftClass (hDer := hDer) hK m hKm a = fibreLiftClass (hDer := hDer) hK m hKm b) :
    a = b := by
  unfold fibreLiftClass at h
  have h1 : DerivedLift.Isomorphic (fibreLiftDerivedLift (hDer := hDer) a.out hK)
      (fibreLiftDerivedLift (hDer := hDer) b.out hK) :=
    Quotient.exact (DerivedLift.classShift_injective
      (T := derivedExtensionOfScalarsData.{d, u + 1}
        (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)))
      (K₀ := ⟨x₀.E, hK⟩) (K₀' := ⟨x₀.E⟦m⟧, hKm⟩) m (Iso.refl _) h)
  rw [← Quotient.out_eq a, ← Quotient.out_eq b] at h𝒵
  obtain ⟨e⟩ := Quotient.exact h𝒵
  have hψ := underPost_isHomLift_right _ _ e.hom.1 e.hom.2
  have hw := Under.w e.hom.1
  change (Over.map x₀.T.left.hom).IsHomLift
    (𝟙 (squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).obj V))) (e.hom.1.right : a.out.1.right.y ⟶ b.out.1.right.y) at hψ
  change (𝟙 _ ≫ a.out.1.hom.b) ≫ (e.hom.1.right : a.out.1.right.y ⟶ b.out.1.right.y) =
    𝟙 _ ≫ b.out.1.hom.b at hw
  rw [Category.id_comp, Category.id_comp] at hw
  obtain ⟨ι⟩ := fibreLift_nonempty_iso_of_isomorphic (hDer := hDer) _ hψ hw hK h1
  exact (Quotient.out_eq a).symm.trans
    ((Quotient.sound (s := isIsomorphicSetoid _) ⟨ι⟩).trans (Quotient.out_eq b))

end ComplexesSituation

end AlgebraicGeometry.Space

end
