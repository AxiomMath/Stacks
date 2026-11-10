module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TransposeLocallyBijectiveOfBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleTerminalBaseChange

/-!
# The flat base change property of Stacks 0762 from cartesianness on flat affine arrows

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` a presheaf of modules over
its structure sheaf, with sections in any universe. This file proves that `F` has the flat base
change property of **Stacks 0762**, read with the pullback of sheaves of Stacks 06WC, as soon as
it is *cartesian on flat arrows between affine objects*: for every arrow `ψ : x' ⟶ y'` of `𝒳`
lying over a flat morphism of affine schemes, the base change map
`𝒪(x') ⊗_{𝒪(y')} F(y') ⟶ F(x')` is bijective.

For an arrow `φ : x ⟶ y` over a flat morphism `f : U ⟶ V`, the comparison
`c_φ : f^*_{psh}(F|_{V_ét}) ⟶ F|_{U_ét}` is the transpose of the comparison
`F|_{V_ét} ⟶ f_*F|_{U_ét}` of Stacks 06W2, and
`PresheafOfModules.TransposeLocalization.isLocallyInjective_transpose` and
`…isLocallySurjective_transpose` reduce its local bijectivity to the bijectivity of the base change
maps along the arrows `a : W ⟶ W' ×_V U` from affine objects of `U_ét` to base changes of affine
objects of `V_ét`. Such a base change map is the base change map of `F` along the arrow of `𝒳`
between the cartesian lifts of `W` and `W'`, which lies over the flat morphism
`W ⟶ W' ×_V U ⟶ W'` of affine schemes.

No quasi-coherence and no description of the pullback of presheaves of modules is used, and the
module universe is free.

## Main definitions

* `AlgebraicGeometry.Stack.IsCartesianOnFlatAffineArrows`: the base change maps of `F` along the
  arrows of `𝒳` lying over flat morphisms of affine schemes are bijective.

## Main results

* `AlgebraicGeometry.SmallEtale.generate_affinePairs_mem`: on small étale sites, arrows from
  affine objects to base changes of affine objects dominate any two arrows to base changes,
  locally.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangePropertyUnivLE_of_isCartesianOnFlatAffineArrows`:
  **cartesianness on flat affine arrows implies Stacks 0762**.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m

namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u})

/-- **Domination of two arrows to base changes by affine pairs.** Let `f : T' ⟶ T` be a
morphism of the big étale site, `W` an object of the small étale site of `T'` and
`a₁ : W ⟶ W₁ ×_T T'`, `a₂ : W ⟶ W₂ ×_T T'` two arrows to base changes of objects of the small étale
site of `T`. The arrows `t : W₀ ⟶ W` from affine objects for which some arrow
`a₀ : W₀ ⟶ W' ×_T T'` with `W'` affine and arrows `b₁ : W' ⟶ W₁`, `b₂ : W' ⟶ W₂` satisfy
`a₀ ≫ b_i ×_T T' = t ≫ a_i` generate a covering sieve of `W`. -/
theorem generate_affinePairs_mem {T T' : E.Scheme} (f : T' ⟶ T)
    {W : SmallEtale E T'.obj T'.property} {W₁ W₂ : SmallEtale E T.obj T.property}
    (a₁ : W ⟶ (smallEtaleBaseChange E f).obj W₁) (a₂ : W ⟶ (smallEtaleBaseChange E f).obj W₂) :
    Sieve.generate (fun (W₀ : SmallEtale E T'.obj T'.property) (t : W₀ ⟶ W) =>
      ∃ (V₀ : SmallEtale E T.obj T.property) (a₀ : W₀ ⟶ (smallEtaleBaseChange E f).obj V₀)
        (b₁ : V₀ ⟶ W₁) (b₂ : V₀ ⟶ W₂),
        (AlgebraicGeometry.IsAffine ((toScheme E _ _).obj W₀) ∧
          AlgebraicGeometry.IsAffine ((toScheme E _ _).obj V₀)) ∧
        a₀ ≫ (smallEtaleBaseChange E f).map b₁ = t ≫ a₁ ∧
        a₀ ≫ (smallEtaleBaseChange E f).map b₂ = t ≫ a₂) ∈
      topology E T'.obj T'.property W := by
  let G := smallEtaleBaseChange E f
  let a : W ⟶ G.obj (W₁ ⨯ W₂) := prod.lift a₁ a₂ ≫ (PreservesLimitPair.iso G W₁ W₂).inv
  have ha₁ : a ≫ G.map prod.fst = a₁ := by
    simp only [a, Category.assoc, PreservesLimitPair.iso_inv_fst]
    exact prod.lift_fst _ _
  have ha₂ : a ≫ G.map prod.snd = a₂ := by
    simp only [a, Category.assoc, PreservesLimitPair.iso_inv_snd]
    exact prod.lift_snd _ _
  have hcp : CoverPreserving (topology E T.obj T.property) (topology E T'.obj T'.property) G :=
    (Functor.isContinuous_iff_coverPreserving (F := G)).1 inferInstance
  have hS := (topology E T'.obj T'.property).pullback_stable a
    (hcp.cover_preserve (generate_isAffine_mem_topology E _ _ (W₁ ⨯ W₂)))
  refine (topology E T'.obj T'.property).superset_covering ?_
    (PresheafOfModules.TransposeLocalization.generate_aff_mem _
      (generate_isAffine_mem_topology E _ _) hS)
  rintro W₀ _ ⟨Z, e, t, ⟨hZ, ⟨V₁, g, k, ⟨V₀, e', g', hV₀, rfl⟩, hk⟩⟩, rfl⟩
  have key : ∀ {X} (π : W₁ ⨯ W₂ ⟶ X),
      (k ≫ G.map e') ≫ G.map (g' ≫ π) = t ≫ a ≫ G.map π := fun π => by
    rw [← Category.assoc t a, hk]
    simp
  refine ⟨Z, e, t, ⟨V₀, k ≫ G.map e', g' ≫ prod.fst, g' ≫ prod.snd, ⟨hZ, hV₀⟩, ?_, ?_⟩, rfl⟩
  · rw [key, ha₁]
  · rw [key, ha₂]

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

open Stacks.PresheafOfModules PresheafOfModules.TransposeLocalization

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **Cartesianness on flat arrows between affine objects.** A presheaf of modules over the
structure sheaf of `𝒳` is cartesian on flat affine arrows when, for every arrow `φ : x ⟶ y` of
`𝒳` lying over a flat morphism of affine schemes, the base change map
`𝒪(x) ⊗_{𝒪(y)} F(y) ⟶ F(x)` of the restriction map along `φ` is bijective. -/
def IsCartesianOnFlatAffineArrows
    (F : PresheafOfModules.{max (u + 1) v w m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    Prop :=
  ∀ ⦃x y : 𝒳⦄ (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) →
    Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp τ hτ).obj) F φ.op)

variable {B E h S hS p hp τ hτ}

/-- The base change map of the comparison of Stacks 06W2 along an arrow `a : W ⟶ W' ×_V U` is the
base change map of `F` along the arrow `ℓ ≫ φ'` of `𝒳` between the cartesian lifts of `W` and
`W'`, where `φ'` computes the comparison at `W'`
(`AlgebraicGeometry.Stack.exists_restrictionComparisonLift`), transported along the
identifications of structure sheaves of Stacks 06W9; so it is bijective when that base change map
is. -/
private theorem bijective_pairBaseChange_of_lift
    (F : PresheafOfModules.{max (u + 1) v w m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    {x y : 𝒳} (φ : x ⟶ y)
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    {V' : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj V')
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj V') ⟶
      (etaleIndex B E h S hS p hp y).obj V')
    (hmod : (restrictionPushforwardComparison B E h S hS p hp φ F.presheaf).app (op V') =
      F.presheaf.map φ'.op)
    (hring : (restrictionPushforwardComparison B E h S hS p hp φ
      (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op V') =
        (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op)
    (hbij : Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp τ hτ).obj) F
        ((etaleIndex B E h S hS p hp x).map a ≫ φ').op)) :
    Function.Bijective (pairBaseChange.{max (u + 1) v w m, u, u, u + 1, u + 1, u}
      (S := SmallEtale.commStructurePresheaf E (p.obj y).left.1 (contains_base B E h S hS p y))
      (R := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
      (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F) a).hom := by
  let f := smallEtaleBaseMorphism B E h S hS p φ
  let ℓ := (etaleIndex B E h S hS p hp x).map a
  let ψa : (etaleIndex B E h S hS p hp x).obj W ⟶ (etaleIndex B E h S hS p hp y).obj V' :=
    ℓ ≫ φ'
  let ψy := localStructurePresheafIso B E h S hS p hp y τ hτ
  let ψx := localStructurePresheafIso B E h S hS p hp x τ hτ
  let O := (structureSheaf B S hS p hp τ hτ).obj
  let ρ := smallEtaleStructureComparison B E h S hS p hp φ τ hτ
  let SV := SmallEtale.commStructurePresheaf E (p.obj y).left.1 (contains_base B E h S hS p y)
  let RU := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x)
  let yl := (etaleIndex B E h S hS p hp y).obj V'
  let xl := (etaleIndex B E h S hS p hp x).obj W
  let α : SV.obj (op V') ≃+* O.obj (op yl) := (ψy.app (op V')).ringCatIsoToRingEquiv
  let β : RU.obj (op W) ≃+* O.obj (op xl) := (ψx.app (op W)).ringCatIsoToRingEquiv
  let rA : SV.obj (op V') →+* RU.obj (op W) := pairRingHom (S := SV) (R := RU) ρ a
  have hsq : ∀ t, β (rA t) = (O.map ψa.op).hom (α t) := by
    intro t
    let t' : (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y)).obj.obj (op V') := t
    let z := (ρ.app (op V')).hom t'
    have e₁ : z = (ψx.inv.app (op ((smallEtaleBaseChange E f).obj V'))).hom
        (((restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op V')).hom
            ((ψy.hom.app (op V')).hom t')) := rfl
    rw [hring] at e₁
    have e₂ := ConcreteCategory.congr_hom (ψx.hom.naturality a.op) z
    simp only [ConcreteCategory.comp_apply] at e₂
    change (ψx.hom.app (op W)).hom ((RU.map a.op).hom z) = _
    refine e₂.trans ?_
    rw [e₁]
    have hcancel := ConcreteCategory.congr_hom
      (ψx.inv_hom_id_app (op ((smallEtaleBaseChange E f).obj V')))
      (((ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op).hom ((ψy.hom.app (op V')).hom t'))
    simp only [ConcreteCategory.comp_apply] at hcancel
    refine (congrArg (fun r => (ConcreteCategory.hom ((restrictToSmallEtale B E h S hS p hp x
      (ringStructureSheafCore B S hS p hp τ hτ).obj).map a.op)) r) hcancel).trans ?_
    change (O.map ℓ.op).hom ((O.map φ'.op).hom (α t)) = (O.map ψa.op).hom (α t)
    rw [← ConcreteCategory.comp_apply, ← O.map_comp]
    rfl
  have hg : ∀ m : F.obj (op yl), ((pairGenerator.{max (u + 1) v w m, u, u, u + 1, u + 1, u}
      (S := SV) (R := RU) ρ (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F) a) m :
        F.obj (op xl)) = (F.map ψa.op m : F.obj (op xl)) := by
    intro m
    have hgm : ((restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F).app (op V')).hom m =
        F.map φ'.op m := ConcreteCategory.congr_hom hmod m
    change F.map ℓ.op (((restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F).app
      (op V')).hom m) = _
    rw [hgm]
    exact (PresheafOfModules.map_comp_apply F φ'.op ℓ.op m).symm
  exact bijective_homEquiv_symm_of_ringEquiv.{max (u + 1) v w m, u} rA (O.map ψa.op).hom
    α β hsq (ψy.hom.app (op V')).hom (ψx.hom.app (op W)).hom (fun _ => rfl) (fun _ => rfl)
    (M := F.obj (op yl)) (N := F.obj (op xl)) (F.map ψa.op)
    (pairGenerator.{max (u + 1) v w m, u, u, u + 1, u + 1, u} (S := SV) (R := RU) ρ
      (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F) a) hg hbij

/-- **The base change maps of the comparison of Stacks 06W2 along affine pairs.** Let
`φ : x ⟶ y` lie over a flat morphism of schemes `U ⟶ V`, and let `a : W ⟶ W' ×_V U` be an arrow
of the small étale site of `U` from an affine object to the base change of an affine object `W'`
of the small étale site of `V`. If `F` is cartesian on flat affine arrows, the base change map
`Γ(W) ⊗_{Γ(W')} F|_{V_ét}(W') ⟶ F|_{U_ét}(W)` of the comparison along `a` is bijective: it is the
base change map of `F` along the arrow of `𝒳` between the cartesian lifts of `W` and `W'`, which
lies over the flat morphism `W ⟶ W' ×_V U ⟶ W'` of affine schemes, transported along the
identifications of structure sheaves of Stacks 06W9. -/
theorem bijective_pairBaseChange_of_isCartesianOnFlatAffineArrows
    (F : PresheafOfModules.{max (u + 1) v w m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hF : IsCartesianOnFlatAffineArrows.{u, v, w, m} B S hS p hp τ hτ F) {x y : 𝒳} (φ : x ⟶ y)
    (hφ : Flat (B.inclusion.map (p.map φ).left))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    {V' : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj V')
    (hW : IsAffine ((SmallEtale.toScheme E _ _).obj W))
    (hV' : IsAffine ((SmallEtale.toScheme E _ _).obj V')) :
    Function.Bijective (pairBaseChange.{max (u + 1) v w m, u, u, u + 1, u + 1, u}
      (S := SmallEtale.commStructurePresheaf E (p.obj y).left.1 (contains_base B E h S hS p y))
      (R := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
      (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F) a).hom := by
  classical
  have := isEquivalence_overPost B S hS p hp x
  have := isEquivalence_overPost B S hS p hp y
  let f := smallEtaleBaseMorphism B E h S hS p φ
  obtain ⟨φ', hfac, hbase⟩ := exists_restrictionComparisonLift B E h S hS p hp φ V'
  have hmod := restrictionPushforwardComparison_app B E h S hS p hp φ F.presheaf V' φ' hfac hbase
  have hring := restrictionPushforwardComparison_app B E h S hS p hp φ
    (ringStructureSheafCore B S hS p hp τ hτ).obj V' φ' hfac hbase
  let ℓ := (etaleIndex B E h S hS p hp x).map a
  let ψa : (etaleIndex B E h S hS p hp x).obj W ⟶ (etaleIndex B E h S hS p hp y).obj V' :=
    ℓ ≫ φ'
  have hφ' : Flat (B.inclusion.map (p.map φ').left) := by
    have : MorphismProperty.RespectsIso @Flat :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hfst : Flat (E.inclusion.map (pullback.fst V'.obj.hom f)) :=
      MorphismProperty.of_isPullback ((IsPullback.of_hasPullback V'.obj.hom f).flip.map
        E.inclusion) hφ
    have h1 : Flat ((etaleIndexIso B E h S hS p hp x
        ((smallEtaleBaseChange E f).obj V')).hom ≫ E.inclusion.map (pullback.fst V'.obj.hom f)) :=
      (MorphismProperty.cancel_left_of_respectsIso @Flat _ _).mpr hfst
    have h2 : B.inclusion.map (p.map φ').left ≫ (etaleIndexIso B E h S hS p hp y V').hom =
        (etaleIndexIso B E h S hS p hp x ((smallEtaleBaseChange E f).obj V')).hom ≫
          E.inclusion.map (pullback.fst V'.obj.hom f) := hbase
    rw [← h2] at h1
    exact (MorphismProperty.cancel_right_of_respectsIso @Flat _ _).mp h1
  have hflat : Flat (B.inclusion.map (p.map ψa).left) := by
    have hℓ := etale_etaleIndex_map B E h S hS p hp x a
    have hc : B.inclusion.map (p.map ψa).left =
        (BigFppfOver.toScheme B S hS).map (p.map ℓ) ≫ B.inclusion.map (p.map φ').left := by
      simp only [ψa, Functor.map_comp, Over.comp_left]
      rfl
    rw [hc]
    infer_instance
  exact bijective_pairBaseChange_of_lift.{u, v, w, m} F φ a φ' hmod hring
    (hF ψa hflat (isAffine_etaleIndex_obj B E h S hS p hp x W hW)
      (isAffine_etaleIndex_obj B E h S hS p hp y V' hV'))

/-- **Cartesianness on flat affine arrows implies the flat base change property of Stacks 0762**,
with the pullback of sheaves of Stacks 06WC, at any module universe from `u + 1` on. For every
arrow `φ` of `𝒳` lying over a flat morphism, the comparison `c_φ` is locally injective and
locally surjective: by `PresheafOfModules.TransposeLocalization.isLocallyInjective_transpose` and
`…isLocallySurjective_transpose` it suffices that the base change maps of the comparison of
Stacks 06W2 along arrows from affine objects to base changes of affine objects be bijective, which
is `AlgebraicGeometry.Stack.bijective_pairBaseChange_of_isCartesianOnFlatAffineArrows`, and that
such arrows cover and dominate each other, which is
`AlgebraicGeometry.SmallEtale.generate_affinePairs_mem`. -/
theorem hasSheafFlatBaseChangePropertyUnivLE_of_isCartesianOnFlatAffineArrows
    (F : PresheafOfModules.{max (u + 1) v w m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hF : IsCartesianOnFlatAffineArrows.{u, v, w, m} B S hS p hp τ hτ F) :
    HasSheafFlatBaseChangeProperty.{u, v, w, max (u + 1) v w m} B E h S hS p hp τ hτ F := by
  intro x y φ hφ
  have : (PresheafOfModules.pushforward.{max (u + 1) v w m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (R := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
        forget₂ CommRingCat RingCat)
      (S := SmallEtale.commStructurePresheaf E (p.obj y).left.1 (contains_base B E h S hS p y) ⋙
        forget₂ CommRingCat RingCat)
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).IsRightAdjoint :=
    isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE.{u, v, w,
      max (u + 1) v w m} B E h S hS p hp φ τ hτ
  let f := smallEtaleBaseMorphism B E h S hS p φ
  let G := smallEtaleBaseChange E f
  let J := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  let Aff : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) → Prop := fun W =>
    IsAffine ((SmallEtale.toScheme E _ _).obj W)
  let Good : ∀ {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
      {V' : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)},
      (W ⟶ G.obj V') → Prop := fun {W V'} _ =>
    IsAffine ((SmallEtale.toScheme E _ _).obj W) ∧ IsAffine ((SmallEtale.toScheme E _ _).obj V')
  have hterm : IsTerminal (G.obj (SmallEtale.final E (p.obj y).left.1
      (contains_base B E h S hS p y))) :=
    (SmallEtale.finalIsTerminal E _ _).isTerminalObj G
  have hG : GoodArrows J Aff Good :=
    { aff_cover := fun W => SmallEtale.generate_isAffine_mem_topology E _ _ W
      aff_of_good := fun _ h => h.1
      good_comp := fun _ _ h hW' => ⟨hW', h.2⟩
      cover := fun W => by
        refine J.superset_covering ?_ (SmallEtale.generate_affinePairs_mem E f
          (hterm.from W) (hterm.from W))
        rintro _ _ ⟨Z, e, t, ⟨V₀, a₀, b₁, b₂, hg, -, -⟩, rfl⟩
        exact ⟨Z, e, t, ⟨V₀, a₀, hg⟩, rfl⟩
      gen := fun V' => by
        refine J.superset_covering ?_ (SmallEtale.generate_affinePairs_mem E f
          (𝟙 (G.obj V')) (𝟙 (G.obj V')))
        rintro _ _ ⟨Z, e, t, ⟨V₀, a₀, b₁, b₂, hg, hb, -⟩, rfl⟩
        exact ⟨Z, e, t, ⟨V₀, a₀, b₁, hg, hb.trans (Category.comp_id t)⟩, rfl⟩
      pair := fun a₁ a₂ _ _ => SmallEtale.generate_affinePairs_mem E f a₁ a₂ }
  have hbij : ∀ {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
      {V' : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)} (a : W ⟶ G.obj V'),
      Good a → Function.Bijective (pairBaseChange.{max (u + 1) v w m, u, u, u + 1, u + 1, u}
        (S := SmallEtale.commStructurePresheaf E (p.obj y).left.1 (contains_base B E h S hS p y))
        (R := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
        (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F) a).hom :=
    fun a ha => bijective_pairBaseChange_of_isCartesianOnFlatAffineArrows F hF φ hφ a ha.1 ha.2
  exact ⟨isLocallyInjective_transpose.{max (u + 1) v w m, u, u, u + 1, u + 1, u}
      (S := SmallEtale.commStructurePresheaf E (p.obj y).left.1 (contains_base B E h S hS p y))
      (R := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
      (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F) hG
      (fun a ha => (hbij a ha).1),
    isLocallySurjective_transpose.{max (u + 1) v w m, u, u, u + 1, u + 1, u}
      (S := SmallEtale.commStructurePresheaf E (p.obj y).left.1 (contains_base B E h S hS p y))
      (R := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
      (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F)
      (fun a ha => (hbij a ha).2) hG.cover⟩

end AlgebraicGeometry.Stack

end
