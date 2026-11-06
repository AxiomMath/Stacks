module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftSeparates

/-!
# Automorphisms of lifts of `E₀` give infinitesimal automorphisms of lifts of `w₀`

Let `x₀` be a field point of `Complexes_{X/Y}` over `Spec k`, `w₀` the base point of the fibre
of `Complexes_{X/Y}` over the point `Spec k ⟶ Y`, and `y` a lift of `w₀` over `k[V]`, with lift
`L_y` of `E₀` to `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedLift`). An automorphism `α` of the
complex of `L_y` with trivial derived base change (Stacks 0DIZ) is carried by the derived
equivalence to an automorphism of the complex `E_y` of `y`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataComplexAut`) whose derived pullback to `X₀`
is compatible with the comparison of `y`, hence to an endomorphism of `y` in the fibre over
`k[V]` with identity `(Sch/V)`-component
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftEndOfAut`): an infinitesimal automorphism
of `y` in the sense of Stacks 07Y9. This is the map `φ ↦ 1 + φ` of the proof of Stacks 0DLL.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
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

section Single

variable [hDer : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]

section Data

variable (A : ComplexesObject D) (m : x₀ ⟶ A) (t : A.T ⟶ x₀.T)
  (hbt : m.base ≫ t = 𝟙 x₀.T) (hb : IsSquareZeroClosedImmersion B S hS m.base.left)
  (hT : A.T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
    ((fgSiteModule B hk).obj V))
  (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m.base.left ≫
      eqToHom hT =
    squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      ((fgSiteModule B hk).obj V))
  (hK : DerivedCategory.TStructure.t.minus x₀.E)

/-- The automorphism of the complex `E` of `A` carried by the derived equivalence from an
automorphism of the complex of the lift of `E₀` attached to `m : x₀ ⟶ A`. -/
def fibreDataComplexAut
    (α : Aut (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).K.obj) : A.E ≅ A.E :=
  (fibreDataDerivedEquivalence (hx₀ := hx₀) A.T m.base t hbt hb hT hβ).counitIso.symm.app A.E ≪≫
    (fibreDataDerivedEquivalence (hx₀ := hx₀) A.T m.base t hbt hb hT hβ).functor.mapIso
      α.asIso ≪≫
    (fibreDataDerivedEquivalence (hx₀ := hx₀) A.T m.base t hbt hb hT hβ).counitIso.app A.E

/-- An automorphism of the lift of `E₀` fixes the identification with the base change of `E₀`
iff the corresponding automorphism of `E` is compatible with the comparison of `m`. -/
private theorem baseChange_map_comp_identification_iff
    (α : Aut (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).K.obj) :
    (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
          α.asIso.hom ≫
        (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).identification.hom =
      (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).identification.hom ↔
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map
      (fibreDataComplexAut A m t hbt hb hT hβ hK α).hom ≫ m.fibre = m.fibre := by
  let eD := fibreDataDerivedEquivalence (hx₀ := hx₀) (hDer := hDer) A.T m.base t hbt hb hT hβ
  let P := (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)
  let e' : eD.inverse.obj A.E ≅ eD.inverse.obj A.E := α.asIso
  change _ ≫ ((fibreDataDerivedPullbackIso (hx₀ := hx₀) A.T m.base t hbt hb hT hβ _).hom.app _ ≫
      P.map (eD.counitIso.hom.app A.E) ≫ m.fibre) =
    (fibreDataDerivedPullbackIso (hx₀ := hx₀) A.T m.base t hbt hb hT hβ _).hom.app _ ≫
      P.map (eD.counitIso.hom.app A.E) ≫ m.fibre ↔
    P.map (eD.counitIso.inv.app A.E ≫ eD.functor.map e'.hom ≫ eD.counitIso.hom.app A.E) ≫
      m.fibre = m.fibre
  refine (Eq.congr_left ((fibreDataDerivedPullbackIso (hx₀ := hx₀) A.T m.base t hbt hb hT hβ
    _).hom.naturality_assoc e'.hom (P.map (eD.counitIso.hom.app A.E) ≫ m.fibre))).trans ?_
  rw [cancel_epi ((fibreDataDerivedPullbackIso (hx₀ := hx₀) A.T m.base t hbt hb hT hβ _).hom.app _)]
  refine (Iso.cancel_iso_hom_left (Functor.mapIso P (eD.counitIso.app A.E).symm) _ _).symm.trans ?_
  have h1 : P.map (eD.counitIso.inv.app A.E) ≫ P.map (eD.counitIso.hom.app A.E) ≫ m.fibre =
      m.fibre := by
    rw [← Category.assoc, ← P.map_comp, Iso.inv_hom_id_app, P.map_id, Category.id_comp]
  rw [Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
  erw [h1]
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  rfl

/-- An automorphism of the lift of `E₀` with trivial derived base change gives an automorphism of
`E` whose derived pullback along the base map of `m` is compatible with the comparison of `m`. -/
theorem fibreDataComplexAut_fibre
    (α : Aut (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).K.obj)
    (hα : (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
          α.asIso.hom = 𝟙 _) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map
      (fibreDataComplexAut A m t hbt hb hT hβ hK α).hom ≫ m.fibre = m.fibre :=
  (baseChange_map_comp_identification_iff A m t hbt hb hT hβ hK α).1 (by rw [hα, Category.id_comp])

/-- The endomorphism of `A` over the identity of its test scheme attached to an automorphism of
the lift of `E₀`: its comparison is the unit law followed by the inverse of
`AlgebraicGeometry.Space.ComplexesSituation.fibreDataComplexAut`. -/
def fibreDataComplexEnd
    (α : Aut (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).K.obj) :
    ComplexesHom A A where
  base := 𝟙 A.T
  fibre := (D.idComparison A.T).hom.app A.E ≫ (fibreDataComplexAut A m t hbt hb hT hβ hK α).inv
  isIso_fibre := @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance inferInstance

/-- Composing `m` with an endomorphism of `A` over the identity gives a morphism whose comparison
`χ` satisfies the cancellation law against the comparison of `m`. -/
private theorem exists_comparison_comp_end (nf : ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (𝟙 A.T))).obj A.E ⟶ A.E) (hnf : IsIso nf) :
    ∃ (χ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj A.E ⟶ x₀.E)
      (hχi : IsIso χ), (⟨m.base, χ, hχi⟩ : ComplexesHom x₀ A) =
        m.comp (A'' := A) ⟨𝟙 A.T, nf, hnf⟩ ∧
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map
        ((@asIso _ _ _ _ nf hnf).symm ≪≫ (D.idComparison A.T).app A.E).hom ≫ χ = m.fibre := by
  let χ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj A.E ⟶
      x₀.E :=
    (D.relativeMapComparison (Category.comp_id m.base)).inv.app A.E ≫
      (m.comp (A'' := A) ⟨𝟙 A.T, nf, hnf⟩).fibre
  have hχi : IsIso χ := @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
    (m.comp (A'' := A) ⟨𝟙 A.T, nf, hnf⟩).isIso_fibre
  have hχ : (⟨m.base, χ, hχi⟩ : ComplexesHom x₀ A) = m.comp (A'' := A) ⟨𝟙 A.T, nf, hnf⟩ :=
    ComplexesHom.ext (Category.comp_id m.base).symm
      (Functor.eqToHom_comp_eqToIso_inv_app _ A.E _ _)
  exact ⟨χ, hχi, hχ,
    D.fibreComp_id_fibre_cancel m.base m.fibre nf hnf _ (ComplexesHom.comp_fibre _ _)⟩

/-- **The endomorphism attached to an automorphism of the lift with trivial derived base change
fixes `m`.** -/
theorem comp_fibreDataComplexEnd
    (α : Aut (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).K.obj)
    (hα : (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
          α.asIso.hom = 𝟙 _) :
    m ≫ fibreDataComplexEnd A m t hbt hb hT hβ hK α = m := by
  obtain ⟨nf, hnfd⟩ : ∃ nf : ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (𝟙 A.T))).obj A.E ⟶ A.E,
      nf = (D.idComparison A.T).hom.app A.E ≫
        (fibreDataComplexAut A m t hbt hb hT hβ hK α).inv := ⟨_, rfl⟩
  have hnf : IsIso nf := hnfd ▸ @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance inferInstance
  have hn : fibreDataComplexEnd A m t hbt hb hT hβ hK α = ⟨𝟙 A.T, nf, hnf⟩ := by
    subst hnfd
    rfl
  rw [hn]
  obtain ⟨χ, hχi, hχ, key⟩ := exists_comparison_comp_end A m nf hnf
  have hεε : ((@asIso _ _ _ _ nf hnf).symm ≪≫ (D.idComparison A.T).app A.E).hom =
      (fibreDataComplexAut A m t hbt hb hT hβ hK α).hom := by
    rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.app_hom, IsIso.inv_comp_eq, hnfd]
    simp
  rw [hεε] at key
  have hφχ : m.fibre = χ := (Iso.cancel_iso_hom_left
    (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).mapIso
      (fibreDataComplexAut A m t hbt hb hT hβ hK α)) _ _).1
    ((fibreDataComplexAut_fibre A m t hbt hb hT hβ hK α hα).trans key.symm)
  change m.comp ⟨𝟙 A.T, nf, hnf⟩ = m
  rw [← hχ]
  have key' : ∀ (f : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj A.E ⟶
      x₀.E) (hf : m.fibre = f) (hi : IsIso f), (⟨m.base, f, hi⟩ : ComplexesHom x₀ A) = m := by
    rintro f rfl hi
    rfl
  exact key' χ hφχ hχi

/-- A morphism of `Complexes_{X/Y}` out of `x₀` is determined by its base map and comparison. -/
theorem fibre_eq_of_mk_eq {A : ComplexesObject D} (c : x₀ ⟶ A)
    (f : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c.base)).obj A.E ⟶ x₀.E)
    (hf : IsIso f) (h : (⟨c.base, f, hf⟩ : ComplexesHom x₀ A) = c) : f = c.fibre := by
  obtain ⟨cb, cf, ci⟩ := c
  cases h
  rfl

/-- The automorphism of `A.E` attached to the image of `ε` under the inverse of the derived
equivalence is `ε`. -/
theorem fibreDataComplexAut_inverse_mapIso (ε : A.E ≅ A.E) :
    fibreDataComplexAut A m t hbt hb hT hβ hK
      (.of ((fibreDataDerivedEquivalence (hx₀ := hx₀) (hDer := hDer) A.T m.base t hbt hb hT
        hβ).inverse.mapIso ε)) = ε := by
  let eD := fibreDataDerivedEquivalence (hx₀ := hx₀) (hDer := hDer) A.T m.base t hbt hb hT hβ
  ext
  change eD.counitIso.inv.app A.E ≫ eD.functor.map (eD.inverse.map ε.hom) ≫
    eD.counitIso.hom.app A.E = ε.hom
  rw [show eD.functor.map (eD.inverse.map ε.hom) ≫ eD.counitIso.hom.app A.E =
    eD.counitIso.hom.app A.E ≫ ε.hom from eD.counitIso.hom.naturality ε.hom,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- An automorphism `ε` of `A.E` compatible with the comparison of `m` gives an automorphism of the
lift of `E₀` with trivial derived base change. -/
theorem baseChange_map_inverse_mapIso_eq_id (ε : A.E ≅ A.E)
    (hε : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map ε.hom ≫
      m.fibre = m.fibre) :
    let α : Aut (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).K.obj :=
      .of ((fibreDataDerivedEquivalence (hx₀ := hx₀) (hDer := hDer) A.T m.base t hbt hb hT
        hβ).inverse.mapIso ε)
    (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
          α.asIso.hom = 𝟙 _ := by
  intro α
  refine (Iso.cancel_iso_hom_right _ _
    (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).identification).1
      (((baseChange_map_comp_identification_iff A m t hbt hb hT hβ hK α).2 ?_).trans
        (Category.id_comp _).symm)
  rw [fibreDataComplexAut_inverse_mapIso]
  exact hε

/-- **Every endomorphism of `A` over the identity of its test scheme fixing `m` comes from an
automorphism of the lift of `E₀` with trivial derived base change**, through
`AlgebraicGeometry.Space.ComplexesSituation.fibreDataComplexEnd`. -/
theorem exists_aut_of_fibreDataComplexEnd (n : ComplexesHom A A) (hn : n.base = 𝟙 A.T)
    (hmn : m ≫ n = m) :
    ∃ α : Aut (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).K.obj,
      (derivedExtensionOfScalarsData.{d, u + 1}
        (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
            α.asIso.hom = 𝟙 _ ∧
      fibreDataComplexEnd A m t hbt hb hT hβ hK α = n := by
  obtain ⟨nb, nf, hnf⟩ := n
  change nb = 𝟙 _ at hn
  subst hn
  let eD := fibreDataDerivedEquivalence (hx₀ := hx₀) (hDer := hDer) A.T m.base t hbt hb hT hβ
  let P := (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)
  let ε : A.E ≅ A.E := (@asIso _ _ _ _ nf hnf).symm ≪≫ (D.idComparison A.T).app A.E
  obtain ⟨χ, hχi, hχ, key⟩ := exists_comparison_comp_end A m nf hnf
  have hχm : χ = m.fibre := fibre_eq_of_mk_eq m χ hχi (hχ.trans hmn)
  have hε : P.map ε.hom ≫ m.fibre = m.fibre :=
    (congrArg (P.map ε.hom ≫ ·) hχm).symm.trans key
  let α : Aut (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK).K.obj :=
    .of (eD.inverse.mapIso ε)
  refine ⟨α, baseChange_map_inverse_mapIso_eq_id A m t hbt hb hT hβ hK ε hε, ?_⟩
  have hαε : fibreDataComplexAut A m t hbt hb hT hβ hK α = ε :=
    fibreDataComplexAut_inverse_mapIso A m t hbt hb hT hβ hK ε
  have hf : (D.idComparison A.T).hom.app A.E ≫
      (fibreDataComplexAut A m t hbt hb hT hβ hK α).inv = nf := by
    rw [hαε]
    change (D.idComparison A.T).hom.app A.E ≫ ((D.idComparison A.T).inv.app A.E ≫ nf) = nf
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have key' : ∀ (f : ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (𝟙 A.T))).obj A.E ⟶ A.E) (_ : f = nf) (hi : IsIso f),
      (⟨𝟙 A.T, f, hi⟩ : ComplexesHom A A) = ⟨𝟙 A.T, nf, hnf⟩ := by
    rintro f rfl hi
    rfl
  exact key' _ hf _

end Data

/-- **An automorphism of the lift of `E₀` of a lift `y` of `w₀` with trivial derived base change
gives an infinitesimal automorphism of `y`**: the endomorphism of `y` in the fibre over `k[V]`
with `Complexes`-component `AlgebraicGeometry.Space.ComplexesSituation.fibreDataComplexEnd` and
identity `(Sch/V)`-component. This is `φ ↦ 1 + φ` of the proof of Stacks 0DLL. -/
def fibreLiftEndOfAut (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (α : Aut (fibreLiftDerivedLift (hDer := hDer) y hK).K.obj)
    (hα : (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
          α.asIso.hom = 𝟙 _) : y ⟶ y :=
  let n : y.1.right.x ⟶ y.1.right.x := fibreDataComplexEnd (hDer := hDer) y.1.right.x y.1.hom.a
    (fibreLiftRetraction y) (fibreLiftSection_comp_retraction y)
    (isSquareZeroClosedImmersion_fibreLiftSection y) (fibreLiftScheme_left_eq y)
    (fibreLiftSection_conj y) hK α
  let R : y.1.right ⟶ y.1.right :=
    { hbase := 𝟙 _
      a := n
      b := 𝟙 _
      ha := IsHomLift.of_fac' _ _ _ y.1.right.hx y.1.right.hx
        ((show (complexesFunctor D).map n = 𝟙 _ from rfl).trans (by simp))
      hb := IsHomLift.of_fac' _ _ _ y.1.right.hy y.1.right.hy (by simp)
      w := by
        rw [CategoryTheory.Functor.map_id, Category.comp_id,
          show (complexesToBaseObjects D).map n = 𝟙 _ from rfl, Category.id_comp] }
  underFiberHomMk _ (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
    (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      ((fgSiteModule B hk).obj V)) (s := y) (t := y) R
    (IsHomLift.of_fac' _ _ _ (congrArg Under.right y.2) (congrArg Under.right y.2) (by
      change 𝟙 _ = _
      rw [Category.id_comp]
      exact (eqToHom_refl _ _).symm.trans (eqToHom_trans _ _).symm))
    (TwoFibreProductOver.Hom.ext'
      (comp_fibreDataComplexEnd (hDer := hDer) y.1.right.x y.1.hom.a _ _ _ _ _ hK α hα)
      (Category.comp_id _))

/-- Equal automorphisms of the lift of `E₀` give equal infinitesimal automorphisms. -/
theorem fibreLiftEndOfAut_congr (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    {α α' : Aut (fibreLiftDerivedLift (hDer := hDer) y hK).K.obj} (h : α = α')
    (hα : (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
          α.asIso.hom = 𝟙 _)
    (hα' : (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
          α'.asIso.hom = 𝟙 _) :
    fibreLiftEndOfAut y hK α hα = fibreLiftEndOfAut y hK α' hα' := by
  subst h
  rfl

/-- **Every infinitesimal automorphism of a lift `y` of `w₀` comes from an automorphism of the
lift of `E₀` of `y` with trivial derived base change** (through
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftEndOfAut`): its `(Sch/V)`-component is the
identity, its `Complexes`-component lies over the identity of the test scheme and fixes the
structure map of `y`. -/
theorem exists_fibreLiftEndOfAut_eq (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E) (τ : y ⟶ y) :
    ∃ (α : Aut (fibreLiftDerivedLift (hDer := hDer) y hK).K.obj)
      (hα : (derivedExtensionOfScalarsData.{d, u + 1}
        (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
            α.asIso.hom = 𝟙 _),
      fibreLiftEndOfAut y hK α hα = τ := by
  have hR : (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
      (baseProj D.Y) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom)).IsHomLift
      (𝟙 (squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).obj V))) τ.1.right :=
    underPost_isHomLift_right _ _ τ.1 τ.2
  have hb0 : τ.1.right.hbase = 𝟙 _ := by
    have e := IsHomLift.fac' (TwoFibreProductOver.structureFunctor (complexesFunctor D)
      (Over.map x₀.T.left.hom) (baseProj D.Y) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom))
      (𝟙 (squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).obj V))) τ.1.right
    change τ.1.right.hbase = _ at e
    rw [e, Category.id_comp]
    exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)
  have ha : (complexesFunctor D).IsHomLift (𝟙 _) τ.1.right.a := hb0 ▸ τ.1.right.ha
  have hb : (Over.map x₀.T.left.hom).IsHomLift (𝟙 _) τ.1.right.b := hb0 ▸ τ.1.right.hb
  have hab : τ.1.right.a.base = 𝟙 _ := by
    apply CostructuredArrow.hom_ext
    have e := IsHomLift.fac' (complexesFunctor D) (𝟙 y.1.right.base) τ.1.right.a
    change τ.1.right.a.base.left = _ at e
    rw [e, Category.id_comp]
    exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)
  have hbb : τ.1.right.b = 𝟙 _ := by
    have e := IsHomLift.fac' (Over.map x₀.T.left.hom) (𝟙 y.1.right.base) τ.1.right.b
    rw [Category.id_comp, eqToHom_trans, eqToHom_refl] at e
    have e2 := congrArg (fun z => CommaMorphism.left z) e
    exact Over.OverMorphism.ext e2
  have hm : y.1.hom.a ≫ τ.1.right.a = y.1.hom.a :=
    congrArg TwoFibreProductOver.Hom.a (Under.w τ.1)
  obtain ⟨α, hα, hαn⟩ := exists_aut_of_fibreDataComplexEnd (hDer := hDer) y.1.right.x y.1.hom.a
    (fibreLiftRetraction y) (fibreLiftSection_comp_retraction y)
    (isSquareZeroClosedImmersion_fibreLiftSection y) (fibreLiftScheme_left_eq y)
    (fibreLiftSection_conj y) hK τ.1.right.a hab hm
  exact ⟨α, hα, Functor.Fiber.hom_ext (Under.UnderMorphism.ext
    (TwoFibreProductOver.Hom.ext' hαn hbb.symm))⟩

end Single

/-- A value of a group homomorphism lies in a subgroup equal to its range. -/
theorem mem_of_range_eq {G H : Type*} [Group G] [Group H] (φ : G →* H) {K : Subgroup H}
    (h : φ.range = K) (x : G) : φ x ∈ K :=
  h ▸ ⟨x, rfl⟩

/-- An element of a subgroup equal to the range of a group homomorphism is a value of it. -/
theorem exists_apply_eq_of_range_eq {G H : Type*} [Group G] [Group H] (φ : G →* H)
    {K : Subgroup H} (h : φ.range = K) (y : H) (hy : y ∈ K) : ∃ x, φ x = y :=
  (h ▸ hy : y ∈ φ.range)

section Unipotent

variable [hDer' : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]

/-- **The infinitesimal automorphism `1 + g` of a lift `y` of `w₀`** attached to
`g : E₀ ⟶ E₀ ⊗^L (𝒪_{X₀} ⊗_k V)`: the comparison homomorphism of Stacks 0DIZ (1)
(`Deformation.ComplexLift.comparisonHom`) on the lift of `E₀` of `y`, followed by
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftEndOfAut`. This is the map `θ_V` of the
proof of Stacks 0DLL. -/
def fibreLiftUnipotentAut (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (g : x₀.E ⟶ (derivedTensorRight.{u + 1}
      ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)).obj x₀.E) :
    y ⟶ y :=
  fibreLiftEndOfAut (hDer := hDer' V) y hK
    (comparisonHom (coefficientReduction.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)
      (fibreLiftDerivedLift (hDer := hDer' V) y hK) (Multiplicative.ofAdd g))
    ((mem_automorphismsOfLift_iff (comparisonHom
      (coefficientReduction.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)
      (fibreLiftDerivedLift (hDer := hDer' V) y hK) (Multiplicative.ofAdd g))).1
      (mem_of_range_eq (comparisonHom
        (coefficientReduction.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)
        (fibreLiftDerivedLift (hDer := hDer' V) y hK)) (comparisonHom_range
        (coefficientReduction.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)
        (fibreLiftDerivedLift (hDer := hDer' V) y hK)) (Multiplicative.ofAdd g)))

/-- **Stacks 0DLL: every infinitesimal automorphism of a lift of `w₀` is `1 + g`**, by Stacks
0DIZ (1) (`Deformation.ComplexLift.comparisonHom_range`) and
`AlgebraicGeometry.Space.ComplexesSituation.exists_fibreLiftEndOfAut_eq`. -/
theorem fibreLiftUnipotentAut_surjective
    (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    Function.Surjective (fibreLiftUnipotentAut y hK) := by
  intro τ
  obtain ⟨α, hα, hτ⟩ := exists_fibreLiftEndOfAut_eq (hDer := hDer' V) y hK τ
  have hmem : α ∈ automorphismsOfLift _ (fibreLiftDerivedLift (hDer := hDer' V) y hK) :=
    (mem_automorphismsOfLift_iff α).2 hα
  obtain ⟨t, ht⟩ := exists_apply_eq_of_range_eq (comparisonHom
      (coefficientReduction.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)
      (fibreLiftDerivedLift (hDer := hDer' V) y hK)) (comparisonHom_range
      (coefficientReduction.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)
      (fibreLiftDerivedLift (hDer := hDer' V) y hK)) α hmem
  refine ⟨Multiplicative.toAdd t, ?_⟩
  have h3 : comparisonHom
      (coefficientReduction.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)
      (fibreLiftDerivedLift (hDer := hDer' V) y hK)
      (Multiplicative.ofAdd (Multiplicative.toAdd t)) = α := ht
  exact (fibreLiftEndOfAut_congr (hDer := hDer' V) y hK h3 _ hα).trans hτ

/-- **The naturality of `g ↦ 1 + g` on the trivial deformations of `w₀`**: for a linear map
`f : V ⟶ W`, the infinitesimal automorphism `1 + (𝒪 ⊗ f)_* g` of the trivial deformation over
`k[W]` is the pullback (`Deformation.Artin.infinitesimalAutomorphismSetFunctor`) of the
infinitesimal automorphism `1 + g` of the trivial deformation over `k[V]`. It is the `haut`
hypothesis of the fibre consumer
`AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_coefficientHom_fieldPoint` for
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftUnipotentAut`; it is **internal, pending**: it
needs the comparison of the lifts of `E₀` of a lift of `w₀` and of its pullback with derived base
change along `𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]`, natural in automorphisms (the comparison `chi` of
0DLL-G23 / 0DLL-G4-2, the same input as
`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftClassPullback`). -/
def FibreTrivialAutNatural (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (hK : DerivedCategory.TStructure.t.minus x₀.E) : Prop :=
  ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (g : (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
      x₀.E).obj V),
    fibreLiftUnipotentAut
        (trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
          ((fgSiteModule B hk).obj W)) hK
        ((coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
          x₀.E).map f g) =
      (infinitesimalAutomorphismSetFunctor k B S hS
          (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))).map
          ((fgSiteModule B hk).map f)
        (fibreLiftUnipotentAut
          (trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
            (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
              (baseProj D.Y) (complexesToBaseObjects D)
              (schemePointToBase D.Y x₀.T.left x₀.T.hom))
            (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
            (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
              (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
              (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
              (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
            ((fgSiteModule B hk).obj V)) hK g)

end Unipotent

end ComplexesSituation

end AlgebraicGeometry.Space

end
