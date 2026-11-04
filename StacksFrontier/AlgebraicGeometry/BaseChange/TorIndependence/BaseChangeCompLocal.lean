module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompIsoLeftApp
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineBaseInduction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeLocalOnTheBase

/-!
# The base-change composition is invertible locally on the base

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes, `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`.  The
composition `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is invertible as soon as, for all affine opens
`V ⊆ S` and `V' ⊆ g^{-1}(V)`, the composition over the restricted square

```
f'^{-1}(V') ---> f^{-1}(V)
     |               |
     v               v
    V'  ------->     V
```

attached to the restricted datum is invertible.

## Main results

* `Stacks.Cohomology.BaseChangeCover.isIso_comp_of_affineCharts`: the localization.

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChangeCover

/-- The chase behind localizing the base for the composition. -/
theorem chase_localize {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ Q₂ Q₃ : C}
    (a : P₀ ⟶ P₁) (Lβ : P₁ ⟶ P₂) (b₂ : P₂ ⟶ P₃) (Rc : P₃ ⟶ P₄) (R : P₀ ⟶ P₄)
    (E : a ≫ Lβ ≫ b₂ ≫ Rc = R) (LRφ : P₂ ⟶ Q₂) (β' : Q₂ ⟶ Q₃) (RLφ : P₃ ⟶ Q₃)
    (nat : LRφ ≫ β' = b₂ ≫ RLφ) (Rψ : P₄ ⟶ Q₃) (hc : Rc ≫ Rψ = RLφ) :
    a ≫ (Lβ ≫ LRφ) ≫ β' = R ≫ Rψ := by
  rw [← E]
  simp only [Category.assoc, nat, hc]

/-- The chase behind shrinking the base for the composition. -/
theorem isIso_iff_of_chase_shrink {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ Q : C}
    (a : P₀ ⟶ P₁) (Lβ : P₁ ⟶ P₂) (b₂ : P₂ ⟶ P₃) (Rc : P₃ ⟶ P₄) (R : P₀ ⟶ P₄)
    (E : a ≫ Lβ ≫ b₂ ≫ Rc = R) (Rφ : P₄ ⟶ Q) (Rcφ : P₃ ⟶ Q) (hcφ : Rc ≫ Rφ = Rcφ)
    [IsIso a] [IsIso Lβ] : IsIso (b₂ ≫ Rcφ) ↔ IsIso (R ≫ Rφ) := by
  have : R ≫ Rφ = (a ≫ Lβ) ≫ b₂ ≫ Rcφ := by
    rw [← E, ← hcφ]
    simp only [Category.assoc]
  rw [this, isIso_comp_left_iff (a ≫ Lβ)]

/-- Invertibility of `x` and of `u ≫ x ≫ v` agree for isomorphisms `u`, `v`. -/
theorem isIso_iff_of_comp_comp {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ : C} (u : P₀ ⟶ P₁)
    (x : P₁ ⟶ P₂) (v : P₂ ⟶ P₃) (y : P₀ ⟶ P₃) [IsIso u] [IsIso v] (h : u ≫ x ≫ v = y) :
    IsIso x ↔ IsIso y := by
  rw [← h, isIso_comp_left_iff u, isIso_comp_right_iff x v]

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

attribute [local instance] HasDerivedCategory.standard

section Pasting

variable {X'' X' X Y'' Y' Y : RingedSpace.{u, u}} (g' : X'' ⟶ X') (g : X' ⟶ X)
  (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)

/-- **Localizing the base, for the composition.** -/
theorem isIso_derivedPullback_map_comp_iff (sq₁ : g ≫ f = f' ≫ h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g).obj K ⟶ K') [IsIso (derivedBaseChangeMap g' f'' f' h' sq₂ K')] :
    IsIso ((derivedPullback h').map
        (derivedBaseChangeMap g f' f h sq₁ K ≫ (derivedPushforward f').map φ)) ↔
      IsIso (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
          (hcomp_square g' g f'' f' f h' h sq₁ sq₂) K ≫
        (derivedPushforward f'').map
          ((derivedPullbackCompIsoCanonical g' g).inv.app K ≫ (derivedPullback g').map φ)) := by
  rw [CategoryTheory.Functor.map_comp]
  exact isIso_iff_of_comp_comp _ _ _ _ (chase_localize _ _ _ _ _
    (derivedBaseChangeMap_comp_horizontal g' g f'' f' f h' h sq₁ sq₂ K) _ _ _
    (derivedBaseChangeMap_naturality g' f'' f' h' sq₂ φ) _
    (by rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc]))

/-- **Shrinking the base, for the composition.** -/
theorem isIso_comp_hcomp_iff (sq₁ : g ≫ f = f' ≫ h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'')))
    (φ : (derivedPullback (g' ≫ g)).obj K ⟶ K'')
    [IsIso (derivedBaseChangeMap g f' f h sq₁ K)] :
    IsIso (derivedBaseChangeMap g' f'' f' h' sq₂ ((derivedPullback g).obj K) ≫
        (derivedPushforward f'').map ((derivedPullbackCompIsoCanonical g' g).hom.app K ≫ φ)) ↔
      IsIso (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
          (hcomp_square g' g f'' f' f h' h sq₁ sq₂) K ≫ (derivedPushforward f'').map φ) :=
  isIso_iff_of_chase_shrink _ _ _ _ _
    (derivedBaseChangeMap_comp_horizontal g' g f'' f' f h' h sq₁ sq₂ K) _ _
    ((derivedPushforward f'').map_comp _ _).symm

end Pasting

/-- The composition depends on the horizontal arrows only up to equality, the datum being
transported along the equality. -/
theorem isIso_comp_congr' {X' X Y' Y : RingedSpace.{u, u}} {g₁ g₂ : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {h₁ h₂ : Y' ⟶ Y} (hg : g₁ = g₂) (hh : h₁ = h₂) (sq₁ : g₁ ≫ f = f' ≫ h₁)
    (sq₂ : g₂ ≫ f = f' ≫ h₂) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (φ₂ : (derivedPullback g₂).obj K ⟶ K') :
    IsIso (derivedBaseChangeMap g₁ f' f h₁ sq₁ K ≫ (derivedPushforward f').map
        (eqToHom (congrArg (fun r : X' ⟶ X => (derivedPullback r).obj K) hg) ≫ φ₂)) ↔
      IsIso (derivedBaseChangeMap g₂ f' f h₂ sq₂ K ≫ (derivedPushforward f').map φ₂) := by
  subst hg hh
  simp only [eqToHom_refl, Category.id_comp]

/-- The composition depends on the horizontal arrows only up to equality, the datum being
transported along the equality. -/
theorem isIso_comp_congr {X' X Y' Y : RingedSpace.{u, u}} {g₁ g₂ : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {h₁ h₂ : Y' ⟶ Y} (hg : g₁ = g₂) (hh : h₁ = h₂) (sq₁ : g₁ ≫ f = f' ≫ h₁)
    (sq₂ : g₂ ≫ f = f' ≫ h₂) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (φ₁ : (derivedPullback g₁).obj K ⟶ K') (φ₂ : (derivedPullback g₂).obj K ⟶ K')
    (hφ : HEq φ₁ φ₂) :
    IsIso (derivedBaseChangeMap g₁ f' f h₁ sq₁ K ≫ (derivedPushforward f').map φ₁) ↔
      IsIso (derivedBaseChangeMap g₂ f' f h₂ sq₂ K ≫ (derivedPushforward f').map φ₂) := by
  subst hg hh
  obtain rfl := eq_of_heq hφ
  exact Iff.rfl

/-- `bcNatTrans_app`, read for invertibility of a composite. -/
theorem isIso_bcNatTrans_comp_iff {X' X T' T : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ T')
    (f : X ⟶ T) (h : T' ⟶ T) (sq : g' ≫ f = f' ≫ h)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing T'))}
    (x : (derivedPushforward f').obj ((derivedPullback g').obj K) ⟶ E) :
    IsIso ((bcNatTrans g' f' f h sq).app K ≫ x) ↔
      IsIso (derivedBaseChangeMap g' f' f h sq K ≫ x) := by
  rw [bcNatTrans_app]

/-! ### Locality on the base -/

section Cover

variable {X' X Y' Y : RingedSpace.{u, u}} (g : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (h : Y' ⟶ Y)

/-- **Invertibility of the composition is local on the base.** -/
theorem isIso_comp_of_isIso_on_open_cover (sq₁ : g ≫ f = f' ≫ h)
    {ι : Type*} (U : ι → TopologicalSpace.Opens Y') (hU : iSup U = ⊤)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g).obj K ⟶ K')
    (hloc : ∀ t, IsIso ((derivedPullback (Y'.ofRestrict (U t).isOpenEmbedding)).map
      (derivedBaseChangeMap g f' f h sq₁ K ≫ (derivedPushforward f').map φ))) :
    IsIso (derivedBaseChangeMap g f' f h sq₁ K ≫ (derivedPushforward f').map φ) := by
  refine Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map (structureSheafRing Y') U
    hU _ fun t => ?_
  exact (NatIso.isIso_map_iff
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso Y' (U t)) _).mp
    (hloc t)

end Cover

section Chart

variable {X' X S' S Z' Z T' T : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S)
  (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g) (j : Z ⟶ X) (j' : Z' ⟶ X') (fZ : Z ⟶ T) (fZ' : Z' ⟶ T')
  (gZ : Z' ⟶ Z) (gT : T' ⟶ T) (iT : T ⟶ S) (iT' : T' ⟶ S')
  (hg : gZ ≫ j = j' ≫ g') (hq : gZ ≫ fZ = fZ' ≫ gT) (hsq₁ : j ≫ f = fZ ≫ iT)
  (hsq₂ : j' ≫ f' = fZ' ≫ iT') (hT : gT ≫ iT = iT' ≫ g)

/-- Step one: shrinking the base of the chart. -/
theorem isIso_rect_of_chart (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g').obj K ⟶ K')
    [IsIso (derivedBaseChangeMap j fZ f iT hsq₁ K)]
    (h : IsIso (derivedBaseChangeMap gZ fZ' fZ gT hq ((derivedPullback j).obj K) ≫
      (derivedPushforward fZ').map (pullDatum gZ j' j g' hg K K' φ))) :
    IsIso (derivedBaseChangeMap (gZ ≫ j) fZ' f (gT ≫ iT) (hcomp_square _ _ _ _ _ _ _ hsq₁ hq) K ≫
      (derivedPushforward fZ').map
        ((derivedPullbackCompIsoLeft gZ j' j g' hg).inv.app K ≫ (derivedPullback j').map φ)) := by
  rw [pullDatum_eq] at h
  exact (isIso_comp_hcomp_iff gZ j fZ' fZ f gT iT hsq₁ hq K _ _).1 h

include hT in
/-- **One chart of the base.** The derived pullback to a chart of the composition is invertible
as soon as the composition over the chart, attached to the pulled-back datum, is, and the two
base-change maps of the chart's squares are invertible. -/
theorem isIso_derivedPullback_map_comp_of_chart
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g').obj K ⟶ K')
    [IsIso (derivedBaseChangeMap j fZ f iT hsq₁ K)]
    [IsIso (derivedBaseChangeMap j' fZ' f' iT' hsq₂ K')]
    (h : IsIso (derivedBaseChangeMap gZ fZ' fZ gT hq ((derivedPullback j).obj K) ≫
      (derivedPushforward fZ').map (pullDatum gZ j' j g' hg K K' φ))) :
    IsIso ((derivedPullback iT').map
      (derivedBaseChangeMap g' f' f g sq K ≫ (derivedPushforward f').map φ)) := by
  have h₁ := isIso_rect_of_chart g' f j j' fZ fZ' gZ gT iT hg hq hsq₁ K K' φ h
  rw [derivedPullbackCompIsoLeft_inv_app_comp g' j j' gZ hg K K' φ] at h₁
  exact (isIso_derivedPullback_map_comp_iff j' g' fZ' f' f iT' g sq hsq₂ K K' φ).2
    ((isIso_comp_congr' hg hT _ (hcomp_square _ _ _ _ _ _ _ sq hsq₂) K _).1 h₁)

end Chart

section Schemes

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- Invertibility of the composition is local on an open cover of the base of schemes. -/
theorem isIso_comp_of_isIso_on_open_cover_scheme (w : g' ≫ f = f' ≫ g) {ι : Type*}
    (V : ι → S'.Opens) (hV : iSup V = ⊤)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (hloc : ∀ t, IsIso ((derivedPullback (V t).ι.toLRSHom.toShHom).map
      (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm w) K ≫
        (derivedPushforward f'.toLRSHom.toShHom).map φ))) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm w) K ≫
      (derivedPushforward f'.toLRSHom.toShHom).map φ) :=
  isIso_comp_of_isIso_on_open_cover _ _ _ _ _ V hV K K' φ hloc

/-- For an open `V` of the base, the base change map of the restricted square is invertible. -/
private theorem exists_isIso_derivedBaseChangeMap_restrict {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))) :
    ∃ w : (f ⁻¹ᵁ V).ι.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
        (f ∣_ V).toLRSHom.toShHom ≫ V.ι.toLRSHom.toShHom,
      IsIso (derivedBaseChangeMap (f ⁻¹ᵁ V).ι.toLRSHom.toShHom
        (f ∣_ V).toLRSHom.toShHom f.toLRSHom.toShHom V.ι.toLRSHom.toShHom w K) :=
  have hsq := isPullback_toShHom_of_isOpenImmersion ((f ⁻¹ᵁ V).ι) (f ∣_ V) f (V.ι)
    (AlgebraicGeometry.isPullback_morphismRestrict f V).flip
  ⟨hsq.w, isIso_derivedBaseChangeMap_of_isOpenImmersions _ _ _ _ hsq K⟩

/-- **The composition is invertible as soon as it is over every pair of affine opens of the
bases**, the restricted datum being the pulled-back one. -/
theorem isIso_comp_of_affineCharts (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (haff : ∀ (V : S.Opens) (V' : S'.Opens), IsAffineOpen V → IsAffineOpen V' →
      ∀ hle : V' ≤ g ⁻¹ᵁ V,
      repGood% f f' g' V.ι V'.ι (g.resLE V V' hle) K K' φ (f ⁻¹ᵁ V)) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w) K ≫
      (derivedPushforward f'.toLRSHom.toShHom).map φ) := by
  have hex : ∀ x : S', ∃ (V : S.Opens) (V' : S'.Opens), IsAffineOpen V ∧ IsAffineOpen V' ∧
      V' ≤ g ⁻¹ᵁ V ∧ x ∈ V' := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := S) (x := g.base x)
        (U := ⊤) (TopologicalSpace.Opens.mem_top _)
    obtain ⟨V', hV', hxV', hsub⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := S') (x := x)
        (U := g ⁻¹ᵁ V) hxV
    exact ⟨V, V', hV, hV', hsub, hxV'⟩
  choose Vb Vp hVb hVp hlep hmemp using hex
  refine isIso_comp_of_isIso_on_open_cover_scheme sq.w Vp
    (eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmemp y⟩) K K' φ
    fun x => ?_
  obtain ⟨w₁, _⟩ := exists_isIso_derivedBaseChangeMap_restrict f (Vb x) K
  obtain ⟨w₂, _⟩ := exists_isIso_derivedBaseChangeMap_restrict f' (Vp x) K'
  have key := isIso_derivedPullback_map_comp_of_chart g'.toLRSHom.toShHom f'.toLRSHom.toShHom
    f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)
    (f ⁻¹ᵁ Vb x).ι.toLRSHom.toShHom (f' ⁻¹ᵁ Vp x).ι.toLRSHom.toShHom
    (f ∣_ Vb x).toLRSHom.toShHom (f' ∣_ Vp x).toLRSHom.toShHom
    (g'.resLE (f ⁻¹ᵁ Vb x) (f' ⁻¹ᵁ Vp x)
      (preimage_le_preimage_of_comm g' f' f g sq.w (hlep x))).toLRSHom.toShHom
    (g.resLE (Vb x) (Vp x) (hlep x)).toLRSHom.toShHom (Vb x).ι.toLRSHom.toShHom
    (Vp x).ι.toLRSHom.toShHom
    (comp_toShHom_of_comm (Scheme.Hom.resLE_comp_ι g' _))
    (comp_toShHom_of_comm (isPullback_resLE_morphismRestrict sq (hlep x)).w) w₁ w₂
    (comp_toShHom_of_comm (Scheme.Hom.resLE_comp_ι g (hlep x))) K K' φ
  have h2 := haff (Vb x) (Vp x) (hVb x) (hVp x) (hlep x) (f ⁻¹ᵁ Vb x).ι (f' ⁻¹ᵁ Vp x).ι
    (f ∣_ Vb x) (f' ∣_ Vp x)
    (g'.resLE (f ⁻¹ᵁ Vb x) (f' ⁻¹ᵁ Vp x) (preimage_le_preimage_of_comm g' f' f g sq.w (hlep x)))
    (Scheme.Opens.opensRange_ι _) (morphismRestrict_ι f (Vb x))
    (morphismRestrict_ι f' (Vp x)) (Scheme.Hom.resLE_comp_ι g' _)
    (isPullback_resLE_morphismRestrict sq (hlep x))
  have h3 := (isIso_bcNatTrans_comp_iff _ _ _ _ _ _ _).1 h2
  exact key h3

end Schemes

end Stacks.Cohomology.BaseChangeCover
