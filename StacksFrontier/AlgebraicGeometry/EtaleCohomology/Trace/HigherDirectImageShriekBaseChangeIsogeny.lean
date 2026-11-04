module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageShriekBaseChangeHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageCoefficient

/-!
# The base change maps of the towers of `R^r g_!` are inverse up to an isogeny

The base change morphisms of ℓ-adic sheaves `χ : (R^r g_! K)|_V ⟶ R^r g'_!(K|_{U'})` and
`χ' : R^r g'_!(K|_{U'}) ⟶ (R^r g_! K)|_V`
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekBaseChangeHom`,
`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekBaseChangeInv`) are built from the base
change maps of the towers `n ↦ R^r g_! K'ₙ`: proper base change
([Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)) on the levels, read through the single
isomorphism `Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTowerBaseChangeIso` in both directions,
followed by the isogeny between the torsion-free models `ℓᴺ K` and `ℓ^{N'} (K|_{U'})` through
`K|_{U'}`. The two isogenies compose to `ℓ ^ (N + N')` in both orders
(`Stacks.EtaleCohomology.LAdicSheaf.flatModelBaseChange_comp_inv`,
`Stacks.EtaleCohomology.LAdicSheaf.flatModelBaseChange_inv_comp`), hence so do the base change
maps of the towers (`Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTowerBaseChange_comp_inv`,
`Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTowerBaseChangeInv_comp`) and, a morphism of ℓ-adic
sheaves being determined by its map of towers of levels
(`Stacks.EtaleCohomology.LAdicSheaf.padicTowerMap_injective`), the morphisms `χ` and `χ'`.
The base change morphism `χ` commutes with the endomorphisms induced by endomorphisms of `K`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekBaseChangeHom_comp_inv`:
  `χ ≫ χ' = ℓ ^ (N + N')`.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekBaseChangeInv_comp`:
  `χ' ≫ χ = ℓ ^ (N + N')`.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekBaseChangeHom_naturality`:
  `(R^r g_! φ)|_V ≫ χ = χ ≫ R^r g'_!(φ|_{U'})`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-! ### Morphisms of ℓ-adic sheaves through their towers of levels -/

section PadicTower

attribute [local instance] moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- The tower map of the morphism of ℓ-adic sheaves of a map of towers is that map of towers. -/
theorem LAdicSheaf.padicTowerMap_homOfPadicTower {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (γ : LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G) :
    LAdicSheaf.padicTowerMap (LAdicSheaf.homOfPadicTower γ) = γ := by
  ext n : 2
  induction n using Opposite.rec with
  | op n => exact LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower γ n

/-- A morphism of ℓ-adic sheaves is determined by its map of towers of levels. -/
theorem LAdicSheaf.padicTowerMap_injective {F G : LAdicSheaf.{u, u + 1} B X ℓ} {φ ψ : F ⟶ G}
    (h : LAdicSheaf.padicTowerMap φ = LAdicSheaf.padicTowerMap ψ) : φ = ψ :=
  LAdicSheaf.hom_ext_of_padicLevelMap fun n =>
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map_injective
      (congrArg (fun t => NatTrans.app t (op n)) h)

/-- The map of towers of levels of the zero morphism of ℓ-adic sheaves is zero. -/
theorem LAdicSheaf.padicTowerMap_zero (F G : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.padicTowerMap (0 : F ⟶ G) = 0 := by
  have h := LAdicSheaf.padicTowerMap_add (0 : F ⟶ G) 0
  rw [add_zero] at h
  simpa using h

/-- Taking the map of towers of levels commutes with multiplication by a natural number. -/
theorem LAdicSheaf.padicTowerMap_nsmul {F G : LAdicSheaf.{u, u + 1} B X ℓ} (k : ℕ) (φ : F ⟶ G) :
    LAdicSheaf.padicTowerMap (k • φ) = k • LAdicSheaf.padicTowerMap φ := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, LAdicSheaf.padicTowerMap_zero]
  | succ k ih => rw [succ_nsmul, LAdicSheaf.padicTowerMap_add, ih, succ_nsmul]

/-- `F ⟶ ℓᴺ F` is natural: `toTorsionFreeModel F N ≫ torsionFreeModelMap φ N =
φ ≫ toTorsionFreeModel G N`. -/
theorem LAdicSheaf.toTorsionFreeModel_comp_torsionFreeModelMap {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (φ : F ⟶ G) (N : ℕ) :
    LAdicSheaf.toTorsionFreeModel F N ≫ LAdicSheaf.torsionFreeModelMap φ N =
      φ ≫ LAdicSheaf.toTorsionFreeModel G N := by
  refine LAdicSheaf.Hom.ext _ _ _ fun n => ?_
  apply (underlyingLevelFunctor B X ℓ n).map_injective
  have := LAdicSheaf.underlyingTransitionLE_epi B X ℓ F (Nat.le_add_left n N)
  refine (cancel_epi (LAdicSheaf.underlyingTransitionLE B X ℓ F (Nat.le_add_left n N))).1 ?_
  have hnat : (underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n)) ≫
      LAdicSheaf.underlyingTransitionLE B X ℓ G (Nat.le_add_left n N) =
      LAdicSheaf.underlyingTransitionLE B X ℓ F (Nat.le_add_left n N) ≫
        (underlyingLevelFunctor B X ℓ n).map (φ.app n) :=
    ((LAdicSheaf.underlyingLAdicTowerMap B X ℓ φ).naturality
      (homOfLE (Nat.le_add_left n N)).op).symm
  have hF : LAdicSheaf.underlyingTransitionLE B X ℓ F (Nat.le_add_left n N) ≫
      (underlyingLevelFunctor B X ℓ n).map ((LAdicSheaf.toTorsionFreeModel F N).app n) =
        LAdicSheaf.torsionFreeModelπ F N n :=
    (congrArg (LAdicSheaf.underlyingTransitionLE B X ℓ F (Nat.le_add_left n N) ≫ ·)
      (LAdicSheaf.underlyingLevelFunctor_map_toTorsionFreeModelApp F N n)).trans
      (LAdicSheaf.transitionLE_toTorsionFreeModelUnderlying F N n)
  have hG : LAdicSheaf.underlyingTransitionLE B X ℓ G (Nat.le_add_left n N) ≫
      (underlyingLevelFunctor B X ℓ n).map ((LAdicSheaf.toTorsionFreeModel G N).app n) =
        LAdicSheaf.torsionFreeModelπ G N n :=
    (congrArg (LAdicSheaf.underlyingTransitionLE B X ℓ G (Nat.le_add_left n N) ≫ ·)
      (LAdicSheaf.underlyingLevelFunctor_map_toTorsionFreeModelApp G N n)).trans
      (LAdicSheaf.transitionLE_toTorsionFreeModelUnderlying G N n)
  have h1 := (underlyingLevelFunctor B X ℓ n).map_comp ((LAdicSheaf.toTorsionFreeModel F N).app n)
    ((LAdicSheaf.torsionFreeModelMap φ N).app n)
  have h2 := (underlyingLevelFunctor B X ℓ n).map_comp (φ.app n)
    ((LAdicSheaf.toTorsionFreeModel G N).app n)
  refine (congrArg (_ ≫ ·) h1).trans (Eq.trans ?_ (congrArg (_ ≫ ·) h2).symm)
  exact ((reassoc_of% hF) _).trans ((LAdicSheaf.torsionFreeModelπ_map_app φ N n).trans
    ((congrArg (_ ≫ ·) hG).symm.trans ((reassoc_of% hnat) _)))

end PadicTower

/-- Whiskering on the right by an additive functor commutes with multiplication by a natural
number: `whiskerRight (k • α) Φ = k • whiskerRight α Φ`. -/
theorem _root_.CategoryTheory.Functor.whiskerRight_nsmul_of_additive {J C D : Type*}
    [Category* J] [Category* C] [Category* D] [Preadditive C] [Preadditive D] {F G : J ⥤ C}
    (α : F ⟶ G) (Φ : C ⥤ D) [Φ.Additive] (k : ℕ) :
    Functor.whiskerRight (k • α) Φ = k • Functor.whiskerRight α Φ := by
  ext j
  simp only [Functor.whiskerRight_app, NatTrans.app_nsmul, Functor.map_nsmul]

/-- Conjugating `k • 𝟙` by an isomorphism: the shape of the composite of the base change maps of
the towers. -/
theorem _root_.CategoryTheory.Iso.inv_comp_comp_hom_eq_nsmul {𝒞 : Type*} [Category* 𝒞]
    [Preadditive 𝒞] {X Y P Q : 𝒞} (e : X ≅ Y) (h : X ⟶ P) (p : P ⟶ Q) (q : Q ⟶ P) (h' : P ⟶ X)
    (k : ℕ) (H : h ≫ p ≫ q ≫ h' = k • 𝟙 X) :
    (e.inv ≫ h ≫ p) ≫ (q ≫ h' ≫ e.hom) = k • 𝟙 Y := by
  simp only [Category.assoc]
  rw [reassoc_of% H, Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
    Iso.inv_hom_id]

/-- Cancelling an isomorphism and an inverse pair in the middle of a composite: the shape of the
composite of the base change maps of the towers in the other order. -/
theorem _root_.CategoryTheory.Iso.comp_hom_comp_inv_eq_nsmul {𝒞 : Type*} [Category* 𝒞]
    [Preadditive 𝒞] {X Y P Q : 𝒞} (e : X ≅ Y) (h : X ⟶ P) (p : P ⟶ Q) (q : Q ⟶ P) (h' : P ⟶ X)
    (k : ℕ) (H' : h' ≫ h = 𝟙 P) (H : q ≫ p = k • 𝟙 Q) :
    (q ≫ h' ≫ e.hom) ≫ (e.inv ≫ h ≫ p) = k • 𝟙 Q := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% H', H]

/-- Right whiskering of a composite of four natural transformations is the composite of their
right whiskerings. -/
theorem _root_.CategoryTheory.Functor.whiskerRight_comp₄ {J C D : Type*} [Category* J]
    [Category* C] [Category* D] {F₀ F₁ F₂ F₃ F₄ : J ⥤ C} (a : F₀ ⟶ F₁) (b : F₁ ⟶ F₂)
    (c : F₂ ⟶ F₃) (d : F₃ ⟶ F₄) (Φ : C ⥤ D) :
    Functor.whiskerRight a Φ ≫ Functor.whiskerRight b Φ ≫ Functor.whiskerRight c Φ ≫
      Functor.whiskerRight d Φ = Functor.whiskerRight (a ≫ b ≫ c ≫ d) Φ := by
  simp only [Functor.whiskerRight_comp]

/-- The shape of the composite `χ ≫ χ'` of the base change morphisms on the towers of levels:
factorisations through monomorphisms of two maps `bc`, `bci` with `bc ≫ bci = k • 𝟙` compose to
`k • 𝟙`. -/
theorem _root_.CategoryTheory.comp_eq_nsmul_of_factorizations {𝒞 : Type*} [Category* 𝒞]
    [Preadditive 𝒞] {A A' T₀ T₁ T' S' S₂ : 𝒞} (eP : T₀ ≅ A) (w : T₀ ⟶ T₁) [Mono w]
    (bc : T₁ ⟶ T') (bci : T' ⟶ T₁) (k : ℕ) (hbb : bc ≫ bci = k • 𝟙 T₁) (ι' : S' ⟶ T')
    (lf : A ⟶ S') (hlf : lf ≫ ι' = eP.inv ≫ w ≫ bc) (eI : A' ≅ S') (ιS : S₂ ⟶ T₁)
    (σ : A' ⟶ S₂) (hσ : σ ≫ ιS = eI.hom ≫ ι' ≫ bci) (ρ₀ : S₂ ⟶ T₀) (hρ₀ : ρ₀ ≫ w = ιS) :
    (lf ≫ eI.inv) ≫ (σ ≫ ρ₀ ≫ eP.hom) = k • 𝟙 A := by
  rw [← cancel_mono (eP.inv ≫ w)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, hρ₀, hσ, Iso.inv_hom_id_assoc,
    reassoc_of% hlf, hbb, Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
    Category.id_comp]

/-- The shape of the composite `χ' ≫ χ` of the base change morphisms on the towers of levels. -/
theorem _root_.CategoryTheory.comp_eq_nsmul_of_factorizations' {𝒞 : Type*} [Category* 𝒞]
    [Preadditive 𝒞] {A A' T₀ T₁ T' S' S₂ : 𝒞} (eP : T₀ ≅ A) (w : T₀ ⟶ T₁)
    (bc : T₁ ⟶ T') (bci : T' ⟶ T₁) (k : ℕ) (hbb : bci ≫ bc = k • 𝟙 T') (ι' : S' ⟶ T') [Mono ι']
    (lf : A ⟶ S') (hlf : lf ≫ ι' = eP.inv ≫ w ≫ bc) (eI : A' ≅ S') (ιS : S₂ ⟶ T₁)
    (σ : A' ⟶ S₂) (hσ : σ ≫ ιS = eI.hom ≫ ι' ≫ bci) (ρ₀ : S₂ ⟶ T₀) (hρ₀ : ρ₀ ≫ w = ιS) :
    (σ ≫ ρ₀ ≫ eP.hom) ≫ (lf ≫ eI.inv) = k • 𝟙 A' := by
  rw [← cancel_mono (eI.hom ≫ ι')]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hlf, Iso.hom_inv_id_assoc, reassoc_of% hρ₀,
    reassoc_of% hσ, hbb, Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
    Category.id_comp]

/-- The isomorphism `CategoryTheory.ObjectProperty.liftWhiskerIso` commutes with the
endomorphisms induced by an endomorphism of the tower. -/
theorem _root_.CategoryTheory.ObjectProperty.liftWhiskerIso_inv_naturality {C C₁ C₂ D J : Type*}
    [Category* C] [Category* C₁] [Category* C₂] [Category* D] [Category* J] (P : ObjectProperty C)
    (T : J ⥤ C) (hT : ∀ j, P (T.obj j)) (α : T ⟶ T) {F₁ : C ⥤ C₁} {F₂ : C₁ ⥤ D} {G₁ : C ⥤ C₂}
    {G₂ : C₂ ⥤ D} (β : P.ι ⋙ F₁ ⋙ F₂ ≅ P.ι ⋙ G₁ ⋙ G₂) :
    Functor.whiskerRight (Functor.whiskerRight α G₁) G₂ ≫ (P.liftWhiskerIso T hT β).inv =
      (P.liftWhiskerIso T hT β).inv ≫ Functor.whiskerRight (Functor.whiskerRight α F₁) F₂ := by
  ext j
  simp only [Functor.comp_obj, Functor.whiskerRight_twice, ObjectProperty.liftWhiskerIso,
    ObjectProperty.liftCompιIso, Iso.refl_symm, Functor.isoWhiskerRight_refl, Iso.refl_trans,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Category.assoc,
    Functor.isoWhiskerRight_inv, Iso.refl_inv, Functor.whiskerRight_id', Category.comp_id,
    Iso.inv_hom_id_assoc, NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerRight_app,
    Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp]
  exact β.inv.naturality (ObjectProperty.homMk (X := (P.lift T hT).obj j)
    (Y := (P.lift T hT).obj j) (α.app j))

/-- The shape of the compatibility of the base change morphism with endomorphisms, on the towers
of levels: a factorisation `lf` of `eP.inv ≫ w ≫ bc` through a monomorphism `ι'` commutes with
endomorphisms compatible with `eP`, `w`, `bc` and `ι'`. -/
theorem _root_.CategoryTheory.comp_eq_comp_of_factorizations {𝒞 : Type*} [Category* 𝒞]
    {A A₀ T₁ T' S' A' : 𝒞} (eP : A₀ ≅ A) (w : A₀ ⟶ T₁) (bc : T₁ ⟶ T') (ι' : S' ⟶ T') [Mono ι']
    (lf : A ⟶ S') (hlf : lf ≫ ι' = eP.inv ≫ w ≫ bc) (eI : A' ≅ S') (p : A ⟶ A) (p₀ : A₀ ⟶ A₀)
    (hp : p₀ ≫ eP.hom = eP.hom ≫ p) (E : T₁ ⟶ T₁) (hw : p₀ ≫ w = w ≫ E) (E' : T' ⟶ T')
    (hbc : E ≫ bc = bc ≫ E') (s' : S' ⟶ S') (hs' : s' ≫ ι' = ι' ≫ E') :
    p ≫ (lf ≫ eI.inv) = (lf ≫ eI.inv) ≫ (eI.hom ≫ s' ≫ eI.inv) := by
  have hp' : p ≫ eP.inv = eP.inv ≫ p₀ := by
    rw [Iso.comp_inv_eq, Category.assoc, hp, Iso.inv_hom_id_assoc]
  rw [← cancel_mono (eI.hom ≫ ι')]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hp', reassoc_of% hw,
    hbc, hs', hlf, reassoc_of% hlf]

/-! ### The composites of the base change morphisms -/

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {U W U' V : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] [IsNoetherian U'.1]
  [IsNoetherian V.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  (g' : U' ⟶ V) [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
  [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
  (jU : U' ⟶ U) (jV : V ⟶ W)
  (hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
    (B.inclusion.map jV))
  (K : LAdicSheaf.{u, u + 1} B U ℓ)

/-- `f⁻¹ (k • φ) = k • f⁻¹ φ` for ℓ-adic sheaves. -/
theorem LAdicSheaf.inverseImageMap_nsmul {F G : LAdicSheaf.{u, u + 1} B U ℓ} (k : ℕ) (φ : F ⟶ G) :
    LAdicSheaf.inverseImageMap jU (k • φ) = k • LAdicSheaf.inverseImageMap jU φ := by
  show (LAdicSheaf.inverseImageFunctor jU).map (k • φ) = k • (LAdicSheaf.inverseImageFunctor
      jU).map φ
  exact (LAdicSheaf.inverseImageFunctor jU).map_nsmul

/-- `f⁻¹` is compatible with composition, for ℓ-adic sheaves. -/
private theorem inverseImageMap_comp {F₁ F₂ F₃ : LAdicSheaf.{u, u + 1} B U ℓ}
    (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃) :
    LAdicSheaf.inverseImageMap jU a ≫ LAdicSheaf.inverseImageMap jU b =
      LAdicSheaf.inverseImageMap jU (a ≫ b) :=
  ((LAdicSheaf.inverseImageFunctor jU).map_comp a b).symm

/-- `f⁻¹ 𝟙 = 𝟙` for ℓ-adic sheaves. -/
private theorem inverseImageMap_id (F₁ : LAdicSheaf.{u, u + 1} B U ℓ) :
    LAdicSheaf.inverseImageMap jU (𝟙 F₁) = 𝟙 _ :=
  (LAdicSheaf.inverseImageFunctor jU).map_id F₁

/-- The isogeny `(ℓᴺ K)|_{U'} ⟶ ℓ^{N'} (K|_{U'}) ⟶ (ℓᴺ K)|_{U'}` is `ℓ ^ (N + N')`. -/
theorem LAdicSheaf.flatModelBaseChange_comp_inv :
    (LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
      LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
        (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) ≫
      (LAdicSheaf.fromTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K))) =
      (ℓ ^ (LAdicSheaf.torsionBound K + LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) •
        𝟙 _ := by
  rw [Category.assoc, ← Category.assoc (LAdicSheaf.toTorsionFreeModel _ _),
    LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel, Preadditive.nsmul_comp,
    Category.id_comp, Preadditive.comp_nsmul, inverseImageMap_comp,
    LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel, LAdicSheaf.inverseImageMap_nsmul,
    inverseImageMap_id, smul_smul, ← pow_add, add_comm]

/-- The isogeny `ℓ^{N'} (K|_{U'}) ⟶ (ℓᴺ K)|_{U'} ⟶ ℓ^{N'} (K|_{U'})` is `ℓ ^ (N + N')`. -/
theorem LAdicSheaf.flatModelBaseChange_inv_comp :
    (LAdicSheaf.fromTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K))) ≫
      (LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
        LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) =
      (ℓ ^ (LAdicSheaf.torsionBound K + LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) •
        𝟙 _ := by
  rw [Category.assoc, ← Category.assoc (LAdicSheaf.inverseImageMap jU _), inverseImageMap_comp,
    LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel, LAdicSheaf.inverseImageMap_nsmul,
    inverseImageMap_id, Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
    LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel, smul_smul, ← pow_add]

omit [AlgebraicGeometry.IsNoetherian V.obj] [LocallyOfFiniteType (B.inclusion.map g')]
  [QuasiCompact (B.inclusion.map g')] [IsSeparated (B.inclusion.map g')] in
/-- The four whiskered maps of towers of the base change, composed: `ℓ ^ (N + N')`. -/
theorem LAdicSheaf.lowerShriekTowerBaseChange_whiskered_comp (r : ℤ) :
    Functor.whiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ
        K)).hom
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
        LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)))) (lowerShriekHomology ℤ_[ℓ]
              (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.fromTorsionFreeModel
          (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K)))) (lowerShriekHomology
              ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ
          K)).inv
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) =
      (ℓ ^ (LAdicSheaf.torsionBound K + LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) •
          𝟙 _ := by
  refine (Functor.whiskerRight_comp₄ _ _ _ _ _).trans ?_
  rw [← Category.assoc (LAdicSheaf.padicTowerMap _), ← LAdicSheaf.padicTowerMap_comp,
    LAdicSheaf.flatModelBaseChange_comp_inv, LAdicSheaf.padicTowerMap_nsmul,
    LAdicSheaf.padicTowerMap_id, Preadditive.nsmul_comp, Category.id_comp,
    Preadditive.comp_nsmul, Iso.hom_inv_id, Functor.whiskerRight_nsmul_of_additive,
    Functor.whiskerRight_id']

omit [AlgebraicGeometry.IsNoetherian V.obj] [LocallyOfFiniteType (B.inclusion.map g')]
  [QuasiCompact (B.inclusion.map g')] [IsSeparated (B.inclusion.map g')] in
/-- The inverse pair of whiskered isomorphisms of towers in the base change. -/
theorem LAdicSheaf.lowerShriekTowerBaseChange_whiskered_inv_hom (r : ℤ) :
    Functor.whiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ
        K)).inv
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ
          K)).hom
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) = 𝟙 _ :=
  (Functor.whiskerRight_comp _ _ _).symm.trans
    ((congrArg (fun t => Functor.whiskerRight t _) (Iso.inv_hom_id _)).trans
      (Functor.whiskerRight_id' _))

omit [AlgebraicGeometry.IsNoetherian V.obj] [LocallyOfFiniteType (B.inclusion.map g')]
  [QuasiCompact (B.inclusion.map g')] [IsSeparated (B.inclusion.map g')] in
/-- The two whiskered isogenies of towers in the other order: `ℓ ^ (N + N')`. -/
theorem LAdicSheaf.lowerShriekTowerBaseChange_whiskered_inv_comp (r : ℤ) :
    Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.fromTorsionFreeModel
        (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K)))) (lowerShriekHomology
              ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
        LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)))) (lowerShriekHomology ℤ_[ℓ]
              (B.inclusion.map g') jg' r) =
      (ℓ ^ (LAdicSheaf.torsionBound K + LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) •
          𝟙 _ := by
  refine (Functor.whiskerRight_comp _ _ _).symm.trans ?_
  rw [← LAdicSheaf.padicTowerMap_comp, LAdicSheaf.flatModelBaseChange_inv_comp,
    LAdicSheaf.padicTowerMap_nsmul, LAdicSheaf.padicTowerMap_id,
    Functor.whiskerRight_nsmul_of_additive, Functor.whiskerRight_id']

omit [AlgebraicGeometry.IsNoetherian W.obj] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- **The base change maps of the towers are inverse up to `ℓ ^ (N + N')`**, one way. -/
theorem LAdicSheaf.lowerShriekTowerBaseChange_comp_inv (r : ℤ) :
    LAdicSheaf.lowerShriekTowerBaseChange B ℓ g jg g' jg' jU jV hpb K r ≫
        LAdicSheaf.lowerShriekTowerBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r =
      (ℓ ^ (LAdicSheaf.torsionBound K + LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) •
        𝟙 _ := by
  rw [LAdicSheaf.lowerShriekTowerBaseChange, LAdicSheaf.lowerShriekTowerBaseChangeInv]
  exact Iso.inv_comp_comp_hom_eq_nsmul _ _ _ _ _ _
    (LAdicSheaf.lowerShriekTowerBaseChange_whiskered_comp B ℓ g' jg' jU K r)

omit [AlgebraicGeometry.IsNoetherian W.obj] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- **The base change maps of the towers are inverse up to `ℓ ^ (N + N')`**, the other way. -/
theorem LAdicSheaf.lowerShriekTowerBaseChangeInv_comp (r : ℤ) :
    LAdicSheaf.lowerShriekTowerBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r ≫
        LAdicSheaf.lowerShriekTowerBaseChange B ℓ g jg g' jg' jU jV hpb K r =
      (ℓ ^ (LAdicSheaf.torsionBound K + LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) •
        𝟙 _ := by
  rw [LAdicSheaf.lowerShriekTowerBaseChange, LAdicSheaf.lowerShriekTowerBaseChangeInv]
  exact Iso.comp_hom_comp_inv_eq_nsmul _ _ _ _ _ _
    (LAdicSheaf.lowerShriekTowerBaseChange_whiskered_inv_hom B ℓ g' jg' jU K r)
    (LAdicSheaf.lowerShriekTowerBaseChange_whiskered_inv_comp B ℓ g' jg' jU K r)

omit [AlgebraicGeometry.IsNoetherian W.obj] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- **The base change map of the towers commutes with the endomorphisms induced by `K ⟶ K`.** -/
theorem LAdicSheaf.lowerShriekTowerBaseChange_naturality (φ : K ⟶ K) (r : ℤ) :
    Functor.whiskerRight (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg K r φ)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      LAdicSheaf.lowerShriekTowerBaseChange B ℓ g jg g' jg' jU jV hpb K r =
    LAdicSheaf.lowerShriekTowerBaseChange B ℓ g jg g' jg' jU jV hpb K r ≫
      LAdicSheaf.lowerShriekTowerEnd B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r
        (LAdicSheaf.inverseImageMap jU φ) := by
  have hsheaf : LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)) ≫
      LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
      LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
        (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) =
    (LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
      LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
        (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) ≫
      LAdicSheaf.torsionFreeModelMap (LAdicSheaf.inverseImageMap jU φ)
        (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) := by
    rw [← Category.assoc, inverseImageMap_comp,
      LAdicSheaf.torsionFreeModelMap_comp_fromTorsionFreeModel, ← inverseImageMap_comp]
    simp only [Category.assoc]
    rw [LAdicSheaf.toTorsionFreeModel_comp_torsionFreeModelMap]
  have htower : Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)) ≫
      (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ K)).hom ≫
      LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
        LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) =
    (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ K)).hom ≫
      LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
        LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) ≫
      LAdicSheaf.padicTowerMap (LAdicSheaf.torsionFreeModelMap (LAdicSheaf.inverseImageMap jU φ)
        (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) := by
    rw [reassoc_of% (LAdicSheaf.padicTowerInverseImageIso_hom_naturality B ℓ jU
      (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K))),
      ← LAdicSheaf.padicTowerMap_comp, hsheaf, LAdicSheaf.padicTowerMap_comp]
  have he : Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      (LAdicSheaf.lowerShriekTowerBaseChangeIso B ℓ g jg g' jg' jU jV hpb K r).inv =
    (LAdicSheaf.lowerShriekTowerBaseChangeIso B ℓ g jg g' jg' jU jV hpb K r).inv ≫
      Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) :=
    ObjectProperty.liftWhiskerIso_inv_naturality (IsLPowerTorsion ℓ U.1)
      (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ K))
      (fun m => ⟨m.unop + 1, LAdicSheaf.padicTower_annihilated B U ℓ _ m.unop⟩)
      (LAdicSheaf.padicTowerMap (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
      (lowerShriekHomologyTorsionBaseChangeIso B ℓ g jg g' jg' jU jV hpb r)
  have hw : Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ jU
        (LAdicSheaf.flatModel B ℓ K)).hom (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
        LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) =
    Functor.whiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ jU
        (LAdicSheaf.flatModel B ℓ K)).hom (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
        LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.torsionFreeModelMap
        (LAdicSheaf.inverseImageMap jU φ) (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) :=
    have w3 : ∀ {F₀ F₁ F₂ F₃ : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] U'.1} (a : F₀ ⟶ F₁) (b : F₁ ⟶ F₂)
        (c : F₂ ⟶ F₃),
        Functor.whiskerRight a (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
          Functor.whiskerRight b (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
          Functor.whiskerRight c (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) =
        Functor.whiskerRight (a ≫ b ≫ c) (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) :=
      fun a b c => by simp only [Functor.whiskerRight_comp]
    (w3 _ _ _).trans ((congrArg (fun t => Functor.whiskerRight t
      (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r)) htower).trans (w3 _ _ _).symm)
  have shape : ∀ {P Q R S : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] V.1} (a : P ⟶ P) (einv : P ⟶ Q)
      (b : Q ⟶ Q) (x : Q ⟶ R) (y : R ⟶ S) (c : S ⟶ S), a ≫ einv = einv ≫ b →
        b ≫ x ≫ y = x ≫ y ≫ c → a ≫ einv ≫ x ≫ y = (einv ≫ x ≫ y) ≫ c := by
    intro P Q R S a einv b x y c h₁ h₂
    rw [reassoc_of% h₁, h₂]
    simp only [Category.assoc]
  exact shape _ _ _ _ _ _ he hw

/-! ### The composites of the base change morphisms of ℓ-adic sheaves -/

section Sheaf

variable (r : ℕ) (hcond : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg K r)
  (hcond' : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r)

include hcond in
omit [AlgebraicGeometry.IsNoetherian V.obj] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- The inverse image along `jV` of the composite of `padicTowerHigherDirectImageShriekIso` with
the inclusion `stableImageι` of the stable image of the tower `lowerShriekTowerLES` is a
monomorphism of towers. -/
theorem LAdicSheaf.mono_whiskerRight_padicTowerHigherDirectImageShriekIso_stableImageι :
    haveI := hcond.fst
    Mono (Functor.whiskerRight
      ((LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg K r hcond).hom ≫
        (LAdicSheaf.lowerShriekTowerLES B ℓ g jg K r).stableImageι)
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV))) := by
  have := hcond.fst
  have : ∀ n, Mono ((Functor.whiskerRight
      ((LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg K r hcond).hom ≫
        (LAdicSheaf.lowerShriekTowerLES B ℓ g jg K r).stableImageι)
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV))).app n) := fun n => by
    induction n using Opposite.rec with
    | op n =>
      rw [Functor.whiskerRight_app, NatTrans.comp_app]
      infer_instance
  exact NatTrans.mono_of_mono_app _

include hcond' in
omit [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
  [IsSeparated (B.inclusion.map g')] in
/-- The inclusion `stableImageι` of the stable image of the tower `lowerShriekTowerLES` for
`g'` and the restriction of `K` along `jU` is a monomorphism of towers. -/
theorem LAdicSheaf.mono_lowerShriekTowerLES_stableImageι :
    haveI := hcond'.fst
    Mono (LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K)
      r).stableImageι := by
  have := hcond'.fst
  have : ∀ n, Mono ((LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K)
      r).stableImageι.app n) := fun n => by
    induction n using Opposite.rec with
    | op n => infer_instance
  exact NatTrans.mono_of_mono_app _

omit [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] in
/-- **The base change morphisms of `R^r g_!` are inverse up to `ℓ ^ (N + N')`**, one way:
`χ ≫ χ' = ℓ ^ (N + N')` on `(R^r g_! K)|_V`, `N`, `N'` the torsion bounds of `K` and `K|_{U'}`. -/
theorem LAdicSheaf.higherDirectImageShriekBaseChangeHom_comp_inv :
    LAdicSheaf.higherDirectImageShriekBaseChangeHom B ℓ g jg g' jg' jU jV hpb K r hcond hcond' ≫
        LAdicSheaf.higherDirectImageShriekBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r hcond
          hcond' =
      (ℓ ^ (LAdicSheaf.torsionBound K + LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) •
        𝟙 _ := by
  have := hcond.fst
  have := hcond'.fst
  have := LAdicSheaf.mono_whiskerRight_padicTowerHigherDirectImageShriekIso_stableImageι B ℓ g jg
    jV K r hcond
  refine LAdicSheaf.padicTowerMap_injective ?_
  rw [LAdicSheaf.padicTowerMap_comp, LAdicSheaf.padicTowerMap_nsmul, LAdicSheaf.padicTowerMap_id,
    LAdicSheaf.higherDirectImageShriekBaseChangeHom, LAdicSheaf.higherDirectImageShriekHom,
    LAdicSheaf.padicTowerMap_homOfPadicTower, LAdicSheaf.higherDirectImageShriekBaseChangeInv,
    LAdicSheaf.padicTowerMap_homOfPadicTower]
  exact comp_eq_nsmul_of_factorizations
    (LAdicSheaf.padicTowerInverseImageIso B ℓ jV (LAdicSheaf.higherDirectImageShriek B ℓ g jg K r))
    _ _ _ _ (LAdicSheaf.lowerShriekTowerBaseChange_comp_inv B ℓ g jg g' jg' jU jV hpb K r)
    (LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r).stableImageι _
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r).liftStableImage_ι
      _ _)
    (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r
      hcond') _ _
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg K r).liftStableImageComp_ι _ _ _)
    (Functor.whiskerRight (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg K r hcond).inv
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)))
    (by rw [← Functor.whiskerRight_comp, Iso.inv_hom_id_assoc])

omit [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] in
/-- **The base change morphisms of `R^r g_!` are inverse up to `ℓ ^ (N + N')`**, the other way:
`χ' ≫ χ = ℓ ^ (N + N')` on `R^r g'_!(K|_{U'})`. -/
theorem LAdicSheaf.higherDirectImageShriekBaseChangeInv_comp :
    LAdicSheaf.higherDirectImageShriekBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r hcond hcond' ≫
        LAdicSheaf.higherDirectImageShriekBaseChangeHom B ℓ g jg g' jg' jU jV hpb K r hcond
          hcond' =
      (ℓ ^ (LAdicSheaf.torsionBound K + LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) •
        𝟙 _ := by
  have := hcond.fst
  have := hcond'.fst
  have := LAdicSheaf.mono_lowerShriekTowerLES_stableImageι B ℓ g' jg' jU K r
    hcond'
  refine LAdicSheaf.padicTowerMap_injective ?_
  rw [LAdicSheaf.padicTowerMap_comp, LAdicSheaf.padicTowerMap_nsmul, LAdicSheaf.padicTowerMap_id,
    LAdicSheaf.higherDirectImageShriekBaseChangeHom, LAdicSheaf.higherDirectImageShriekHom,
    LAdicSheaf.padicTowerMap_homOfPadicTower, LAdicSheaf.higherDirectImageShriekBaseChangeInv,
    LAdicSheaf.padicTowerMap_homOfPadicTower]
  exact comp_eq_nsmul_of_factorizations'
    (LAdicSheaf.padicTowerInverseImageIso B ℓ jV (LAdicSheaf.higherDirectImageShriek B ℓ g jg K r))
    _ _ _ _ (LAdicSheaf.lowerShriekTowerBaseChangeInv_comp B ℓ g jg g' jg' jU jV hpb K r)
    (LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r).stableImageι _
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r).liftStableImage_ι
      _ _)
    (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r
      hcond') _ _
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg K r).liftStableImageComp_ι _ _ _)
    (Functor.whiskerRight (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg K r hcond).inv
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)))
    (by rw [← Functor.whiskerRight_comp, Iso.inv_hom_id_assoc]; rfl)

omit [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] in
/-- **The base change morphism `χ` commutes with the endomorphisms induced by `K ⟶ K`**: for
`φ : K ⟶ K`, `(R^r g_! φ)|_V ≫ χ = χ ≫ R^r g'_!(φ|_{U'})`. In particular `χ` is compatible with
an action of coefficients on `K`. -/
theorem LAdicSheaf.higherDirectImageShriekBaseChangeHom_naturality (φ : K ⟶ K) :
    LAdicSheaf.inverseImageMap jV (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg K r φ) ≫
        LAdicSheaf.higherDirectImageShriekBaseChangeHom B ℓ g jg g' jg' jU jV hpb K r hcond
          hcond' =
      LAdicSheaf.higherDirectImageShriekBaseChangeHom B ℓ g jg g' jg' jU jV hpb K r hcond hcond' ≫
        LAdicSheaf.higherDirectImageShriekEnd B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r
          (LAdicSheaf.inverseImageMap jU φ) := by
  have := hcond.fst
  have := hcond'.fst
  have := LAdicSheaf.mono_lowerShriekTowerLES_stableImageι B ℓ g' jg' jU K r hcond'
  have hw : Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg K r φ))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      Functor.whiskerRight
        ((LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg K r hcond).hom ≫
          (LAdicSheaf.lowerShriekTowerLES B ℓ g jg K r).stableImageι)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) =
    Functor.whiskerRight ((LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg K r hcond).hom ≫
        (LAdicSheaf.lowerShriekTowerLES B ℓ g jg K r).stableImageι)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      Functor.whiskerRight (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg K r φ)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) := by
    rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp,
      LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg K r hcond φ,
      LAdicSheaf.padicTowerMap_homOfPadicTower]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      LESData.stableImageMap_ι]
  refine LAdicSheaf.padicTowerMap_injective ?_
  rw [LAdicSheaf.padicTowerMap_comp, LAdicSheaf.padicTowerMap_comp,
    LAdicSheaf.higherDirectImageShriekBaseChangeHom, LAdicSheaf.higherDirectImageShriekHom,
    LAdicSheaf.padicTowerMap_homOfPadicTower,
    LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r
      hcond' (LAdicSheaf.inverseImageMap jU φ),
    LAdicSheaf.padicTowerMap_homOfPadicTower]
  exact comp_eq_comp_of_factorizations
    (LAdicSheaf.padicTowerInverseImageIso B ℓ jV (LAdicSheaf.higherDirectImageShriek B ℓ g jg K r))
    _ _ (LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r).stableImageι _
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r).liftStableImage_ι
      _ _)
    (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r
      hcond') _ _
    (LAdicSheaf.padicTowerInverseImageIso_hom_naturality B ℓ jV
      (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg K r φ)) _ hw _
    (LAdicSheaf.lowerShriekTowerBaseChange_naturality B ℓ g jg g' jg' jU jV hpb K φ r) _
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r).stableImageMap_ι
      _)

end Sheaf

end Stacks.EtaleCohomology

end
