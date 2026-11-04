module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleFunctorLaws
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# Restriction of the sections of the powers of `O(0)` along a composite

Let `(E, f, 0)` be a pointed family over `S`, separated and smooth of relative dimension one, and
let `g : T ⟶ S`, `g' : T' ⟶ T` with `g' ≫ g = g''`. Restricting a section of `O(0)^{⊗ n}` along
`g` and then along `g'` agrees with restricting it along `g''`, up to multiplicative maps between
the sections of the powers of `O(0)` on the two models `(E ×_S T) ×_T T'` and `E ×_S T'` of the
base change, which preserve the canonical section. In particular, whether the restriction is a
multiple of the canonical section does not depend on the model. Over affine bases restriction is
semilinear for the structure of module over the base ring.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartRatioPullback.transportSection`: the pullback of a global
  section of `L^{⊗ n}` along `j`, read in `L'^{⊗ n}` through an isomorphism `j^*L ≅ L'`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.exists_restrictSection_comp`: the maps
  comparing the two restrictions, in both directions.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.restrictSection_comp_notMem_range`: the
  restriction along `g''` is a multiple of the canonical section exactly when the restriction
  along `g` and then `g'` is.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.restrictSection_smul`: restriction along
  `Spec B ⟶ Spec A` is semilinear.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Divisors
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections)
open Stacks.AmplePullbackPart1 (natTensorPowCongr natTensorPowCongr_trans natTensorPowCongr_symm)
open Stacks.TensorSheafSpellingIso (pullbackCompIso)

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace Stacks.AlgebraicGeometry.ProjChartRatioPullback

variable {Y Y' Y'' : Scheme.{u}} (j : Y' ⟶ Y) {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]
  {L' : Y'.Modules}

/-- **The transport of a global section of `L^{⊗ n}` along `j`**: its pullback, read in
`L'^{⊗ n}` through an isomorphism `e : j^*L ≅ L'`. -/
def transportSection (e : (Scheme.Modules.pullback j).obj L ≅ L') (n : ℕ)
    (x : Γ(natTensorPow L n, ⊤)) : Γ(natTensorPow L' n, ⊤) :=
  (natTensorPowCongr e n).hom.app ⊤ (pullSection j L n x)

/-- **Transport is multiplicative.** -/
theorem transportSection_mulSections (e : (Scheme.Modules.pullback j).obj L ≅ L') {n m : ℕ}
    (x : Γ(natTensorPow L n, ⊤)) (y : Γ(natTensorPow L m, ⊤)) :
    transportSection j e (n + m) (mulSections L x y) =
      mulSections L' (transportSection j e n x) (transportSection j e m y) := by
  rw [transportSection,
    Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullSection_mulSections,
    Stacks.AlgebraicGeometry.ProjTripleClassifying.mulSections_natTensorPowCongr]
  rfl

/-- **Transport along a composite is the composite of the transports**, through the composite
isomorphism. -/
theorem transportSection_comp (e : (Scheme.Modules.pullback j).obj L ≅ L')
    [Stacks.Ample.IsInvertibleModule Y' L'] (j' : Y'' ⟶ Y') {L'' : Y''.Modules}
    (e' : (Scheme.Modules.pullback j').obj L' ≅ L'') (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) :
    transportSection j' e' n (transportSection j e n x) =
      transportSection (j' ≫ j) (((pullbackCompIso j' j).app L).symm ≪≫
        (Scheme.Modules.pullback j').mapIso e ≪≫ e') n x := by
  unfold transportSection
  rw [Stacks.AlgebraicGeometry.ProjTriplePullbackEquiv.pullSection_natTensorPowCongr,
    ← Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.congr_hom_app_pullSection_comp,
    natTensorPowCongr_trans, natTensorPowCongr_trans, natTensorPowCongr_symm]
  simp only [Iso.trans_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  congr 2
  exact (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤)
    (natTensorPowCongr ((pullbackCompIso j' j).app L) n).hom_inv_id) _).symm

/-- **Transport along `φ` intertwines two transports to `Y` related by `φ`.** For transports
along `ha : A ⟶ Y` and `hb : B ⟶ Y` with `φ ≫ hb = ha`, some transport along `φ` carries the
second to the first. -/
theorem exists_transportSection_comp_eq {A B : Scheme.{u}} {LA : A.Modules} {LB : B.Modules}
    [Stacks.Ample.IsInvertibleModule B LB] (ha : A ⟶ Y)
    (ea : (Scheme.Modules.pullback ha).obj L ≅ LA) (hb : B ⟶ Y)
    (eb : (Scheme.Modules.pullback hb).obj L ≅ LB) (φ : A ⟶ B) (hφ : φ ≫ hb = ha) :
    ∃ β : (Scheme.Modules.pullback φ).obj LB ≅ LA, ∀ n (x : Γ(natTensorPow L n, ⊤)),
      transportSection φ β n (transportSection hb eb n x) = transportSection ha ea n x := by
  subst hφ
  refine ⟨(Scheme.Modules.pullback φ).mapIso eb.symm ≪≫
    (pullbackCompIso φ hb).app L ≪≫ ea, fun n x => ?_⟩
  rw [transportSection_comp]
  congr 1
  ext1
  simp

end Stacks.AlgebraicGeometry.ProjChartRatioPullback

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

open Stacks.AlgebraicGeometry.ProjChartRatioPullback

variable {S T T' : Scheme.{u}} (E : PointedFamily S) [IsSeparated E.map]
  [SmoothOfRelativeDimension 1 E.map]

/-- Restriction is the transport along the projection through `zeroSheafPullbackIso`. -/
theorem restrictSection_eq_transportSection (g : T ⟶ S) (n : ℕ)
    (x : Γ(natTensorPow E.zeroSheaf n, ⊤)) :
    E.restrictSection g n x =
      transportSection (Limits.pullback.fst E.map g) (E.zeroSheafPullbackIso g) n x :=
  rfl

/-- Restriction along `g` and then `g'` is a transport along the composite of the projections. -/
theorem exists_restrictSection_restrictSection_eq (g : T ⟶ S) (g' : T' ⟶ T) :
    ∃ α : (Scheme.Modules.pullback (Limits.pullback.fst (E.pullback g).map g' ≫
        Limits.pullback.fst E.map g)).obj E.zeroSheaf ≅ ((E.pullback g).pullback g').zeroSheaf,
      ∀ n (t : Γ(natTensorPow E.zeroSheaf n, ⊤)),
        (E.pullback g).restrictSection g' n (E.restrictSection g n t) =
          transportSection _ α n t :=
  have := isInvertibleModule_zeroSheaf (E.pullback g)
  ⟨_, fun n t => transportSection_comp _ _ _ _ n t⟩

/-- **Comparing the two restrictions along a composite, towards `E ×_S T'`.** For
`g' ≫ g = g''` there are multiplicative maps from the sections of the powers of `O(0)` on
`(E ×_S T) ×_T T'` to those on `E ×_S T'` carrying the restriction along `g` and then `g'` to the
restriction along `g''`. -/
theorem exists_restrictSection_comp (g : T ⟶ S) (g' : T' ⟶ T) (g'' : T' ⟶ S)
    (hg : g' ≫ g = g'') :
    ∃ ε : ∀ n, Γ(natTensorPow ((E.pullback g).pullback g').zeroSheaf n, ⊤) →
        Γ(natTensorPow (E.pullback g'').zeroSheaf n, ⊤),
      (∀ {n m : ℕ} (a : Γ(natTensorPow ((E.pullback g).pullback g').zeroSheaf n, ⊤))
          (b : Γ(natTensorPow ((E.pullback g).pullback g').zeroSheaf m, ⊤)),
        ε (n + m) (mulSections _ a b) = mulSections _ (ε n a) (ε m b)) ∧
      ∀ n (t : Γ(natTensorPow E.zeroSheaf n, ⊤)),
        ε n ((E.pullback g).restrictSection g' n (E.restrictSection g n t)) =
          E.restrictSection g'' n t := by
  subst hg
  have : SmoothOfRelativeDimension 1 (E.pullback g).map := inferInstance
  have : SmoothOfRelativeDimension 1 ((E.pullback g).pullback g').map :=
    smoothOfRelativeDimension_pullback_map (E.pullback g) g'
  have := isInvertibleModule_zeroSheaf ((E.pullback g).pullback g')
  have := isInvertibleModule_zeroSheaf (E.pullback (g' ≫ g))
  obtain ⟨α, hα⟩ := E.exists_restrictSection_restrictSection_eq g g'
  have hφ : (Limits.pullbackLeftPullbackSndIso E.map g g').inv ≫
      (Limits.pullback.fst (E.pullback g).map g' ≫ Limits.pullback.fst E.map g) =
        Limits.pullback.fst E.map (g' ≫ g) := by
    rw [Iso.inv_comp_eq, Limits.pullbackLeftPullbackSndIso_hom_fst]
  obtain ⟨β, hβ⟩ := exists_transportSection_comp_eq _ (E.zeroSheafPullbackIso (g' ≫ g)) _ α _ hφ
  exact ⟨fun n => transportSection _ β n, fun a b => transportSection_mulSections _ β a b,
    fun n t => by
      beta_reduce
      rw [hα, hβ]
      rfl⟩

/-- **Comparing the two restrictions along a composite, towards `(E ×_S T) ×_T T'`.** -/
theorem exists_restrictSection_comp_symm (g : T ⟶ S) (g' : T' ⟶ T) (g'' : T' ⟶ S)
    (hg : g' ≫ g = g'') :
    ∃ ε : ∀ n, Γ(natTensorPow (E.pullback g'').zeroSheaf n, ⊤) →
        Γ(natTensorPow ((E.pullback g).pullback g').zeroSheaf n, ⊤),
      (∀ {n m : ℕ} (a : Γ(natTensorPow (E.pullback g'').zeroSheaf n, ⊤))
          (b : Γ(natTensorPow (E.pullback g'').zeroSheaf m, ⊤)),
        ε (n + m) (mulSections _ a b) = mulSections _ (ε n a) (ε m b)) ∧
      ∀ n (t : Γ(natTensorPow E.zeroSheaf n, ⊤)),
        ε n (E.restrictSection g'' n t) =
          (E.pullback g).restrictSection g' n (E.restrictSection g n t) := by
  subst hg
  have : SmoothOfRelativeDimension 1 (E.pullback g).map := inferInstance
  have : SmoothOfRelativeDimension 1 ((E.pullback g).pullback g').map :=
    smoothOfRelativeDimension_pullback_map (E.pullback g) g'
  have := isInvertibleModule_zeroSheaf ((E.pullback g).pullback g')
  have := isInvertibleModule_zeroSheaf (E.pullback (g' ≫ g))
  obtain ⟨α, hα⟩ := E.exists_restrictSection_restrictSection_eq g g'
  obtain ⟨β, hβ⟩ := exists_transportSection_comp_eq _ α _ (E.zeroSheafPullbackIso (g' ≫ g))
    (Limits.pullbackLeftPullbackSndIso E.map g g').hom
    (Limits.pullbackLeftPullbackSndIso_hom_fst E.map g g')
  exact ⟨fun n => transportSection _ β n, fun a b => transportSection_mulSections _ β a b,
    fun n t => by
      beta_reduce
      rw [hα, ← hβ]
      rfl⟩

/-- The canonical section is the restriction of the canonical section along `g` and then `g'`. -/
theorem restrictSection_restrictSection_zeroSection (g : T ⟶ S) (g' : T' ⟶ T) :
    (E.pullback g).restrictSection g' 1 (E.restrictSection g 1 E.zeroSection) =
      ((E.pullback g).pullback g').zeroSection := by
  rw [restrictSection_zeroSection, restrictSection_zeroSection]

/-- **Being a multiple of the canonical section does not depend on the model of the base
change**: for `g' ≫ g = g''`, the restriction of a section of `O(0)^{⊗ (1 + m)}` along `g''` is
not a multiple of the canonical section exactly when its restriction along `g` and then `g'` is
not. -/
theorem restrictSection_comp_notMem_range (g : T ⟶ S) (g' : T' ⟶ T) (g'' : T' ⟶ S)
    (hg : g' ≫ g = g'') {m : ℕ} (t : Γ(natTensorPow E.zeroSheaf (1 + m), ⊤)) :
    E.restrictSection g'' (1 + m) t ∉ Set.range (mulSections (E.pullback g'').zeroSheaf (m := m)
        (E.pullback g'').zeroSection) ↔
      (E.pullback g).restrictSection g' (1 + m) (E.restrictSection g (1 + m) t) ∉
        Set.range (mulSections ((E.pullback g).pullback g').zeroSheaf (m := m)
          ((E.pullback g).pullback g').zeroSection) := by
  obtain ⟨ε, hεm, hε⟩ := E.exists_restrictSection_comp g g' g'' hg
  obtain ⟨ε', hεm', hε'⟩ := E.exists_restrictSection_comp_symm g g' g'' hg
  have hσ : ε 1 ((E.pullback g).pullback g').zeroSection = (E.pullback g'').zeroSection := by
    rw [← restrictSection_restrictSection_zeroSection, hε, restrictSection_zeroSection]
  have hσ' : ε' 1 (E.pullback g'').zeroSection = ((E.pullback g).pullback g').zeroSection := by
    rw [← restrictSection_zeroSection, hε', restrictSection_restrictSection_zeroSection]
  refine not_congr ⟨fun ⟨u, hu⟩ => ⟨ε' m u, ?_⟩, fun ⟨u, hu⟩ => ⟨ε m u, ?_⟩⟩
  · rw [← hσ', ← hεm', hu, hε']
  · rw [← hσ, ← hεm, hu, hε]

/-! ### Restriction over affine bases is semilinear -/

section Affine

variable {A B : Type u} [CommRing A] [CommRing B] (E : PointedFamily (Spec (.of A)))
  [IsSeparated E.map] [SmoothOfRelativeDimension 1 E.map] (φ : A →+* B)

omit [IsSeparated E.map] [SmoothOfRelativeDimension 1 E.map] in
/-- The structure ring map of `E ×_A B` over `B` is that of `E` over `A`, followed by the
projection. -/
theorem appTop_fst_baseRingHom :
    Stacks.Cech.baseRingHom E.map ⊤ ≫
        (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ))).appLE ⊤ ⊤ (by simp) =
      CommRingCat.ofHom φ ≫
        Stacks.Cech.baseRingHom (E.pullback (Spec.map (CommRingCat.ofHom φ))).map ⊤ := by
  have hid : ∀ (X : Scheme.{u}), X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ :=
    fun X => by rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
      X.presheaf.map_id]
  rw [Stacks.Cech.baseRingHom, Stacks.Cech.baseRingHom, Stacks.Cech.globalRingHom,
    Stacks.Cech.globalRingHom, hid, hid, Category.comp_id, Category.comp_id,
    AlgebraicGeometry.appLE_top_top_eq_appTop]
  have h1 := congrArg Scheme.Hom.appTop
    (Limits.pullback.condition (f := E.map) (g := Spec.map (CommRingCat.ofHom φ)))
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h1
  have h2 : toSpecΓ (CommRingCat.of A) ≫ (Spec.map (CommRingCat.ofHom φ)).appTop =
      CommRingCat.ofHom φ ≫ toSpecΓ (CommRingCat.of B) :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  calc _ = toSpecΓ (CommRingCat.of A) ≫ (E.map.appTop ≫
        (Limits.pullback.fst E.map (Spec.map (CommRingCat.ofHom φ))).appTop) :=
          Category.assoc _ _ _
    _ = toSpecΓ (CommRingCat.of A) ≫ ((Spec.map (CommRingCat.ofHom φ)).appTop ≫
        (Limits.pullback.snd E.map (Spec.map (CommRingCat.ofHom φ))).appTop) :=
          congrArg (toSpecΓ (CommRingCat.of A) ≫ ·) h1
    _ = (toSpecΓ (CommRingCat.of A) ≫ (Spec.map (CommRingCat.ofHom φ)).appTop) ≫
        (Limits.pullback.snd E.map (Spec.map (CommRingCat.ofHom φ))).appTop :=
          (Category.assoc _ _ _).symm
    _ = _ := (congrArg (· ≫ (Limits.pullback.snd E.map (Spec.map (CommRingCat.ofHom φ))).appTop)
          h2).trans (Category.assoc _ _ _)

/-- **Restriction along `Spec B ⟶ Spec A` is semilinear**: for the module structures over `A` and
`B` through the structure morphisms, restricting `a • t` gives `φ a •` the restriction of `t`. -/
theorem restrictSection_smul (n : ℕ) (a : A) (t : Γ(natTensorPow E.zeroSheaf n, ⊤)) :
    letI := Stacks.Cech.sectionsModule E.map (natTensorPow E.zeroSheaf n) ⊤
    letI := Stacks.Cech.sectionsModule (E.pullback (Spec.map (CommRingCat.ofHom φ))).map
      (natTensorPow (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSheaf n) ⊤
    E.restrictSection (Spec.map (CommRingCat.ofHom φ)) n (a • t) =
      φ a • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) n t := by
  have key := congrArg (fun f => f.hom a) (appTop_fst_baseRingHom E φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  show transportSection _ (E.zeroSheafPullbackIso (Spec.map (CommRingCat.ofHom φ))) n
      ((Stacks.Cech.baseRingHom E.map ⊤).hom a • t) =
    (Stacks.Cech.baseRingHom (E.pullback (Spec.map (CommRingCat.ofHom φ))).map ⊤).hom (φ a) •
      transportSection _ (E.zeroSheafPullbackIso (Spec.map (CommRingCat.ofHom φ))) n t
  rw [← key]
  unfold transportSection pullSection
  rw [pullbackSectionHom_smul, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]

end Affine

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

end
