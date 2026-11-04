module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ComparisonComposite
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ClassMorphismSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.AffineBaseMorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.IsoOnABasis

/-!
# The morphism `ξ̃` of the Leray--Hirsch theorem over an open of the base

Let `f : X ⟶ Y` be a morphism over `S` and `ξ̃ : ⨁ Ω^•_{Y/S}[-n_i] ⟶ Rf_*Ω^•_{X/S}` the morphism of
Proposition 0FMR. For an open `V ⊆ Y` mapping into an open `W ⊆ S`, the map that `ξ̃` induces on
`H^k(V, -)` is identified, through the canonical maps of the squares of open immersions
`(f⁻¹V ⟶ X, W ⟶ S)` and `(V ⟶ Y, W ⟶ S)` (which induce isomorphisms on derived sections over
`f⁻¹V` and `V`), with the map induced on `H^k(V, -)` by the morphism `ξ̃` of `f⁻¹V ⟶ V` over `W`
for the restricted classes (`bijective_homology_lerayHirschMorphism_of_restrict`). This is how the
proof of Proposition 0FMR reduces to the case of affine `Y` and `S`.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.bijective_homology_lerayHirschMorphism_of_restrict`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace CategoryTheory

section Shift

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]

/-- Moving a morphism `φ : B ⟶ B[n]` across a natural transformation compatible with the shift. -/
theorem comp_map_commShiftIso_hom_app_shift_eq {G₁ G₂ : C ⥤ D} [G₁.CommShift ℤ] [G₂.CommShift ℤ]
    (τ : G₁ ⟶ G₂) [NatTrans.CommShift τ ℤ] {A : D} {B : C} (c₁ : A ⟶ G₁.obj B)
    (c₂ : A ⟶ G₂.obj B) (hc : c₁ ≫ τ.app B = c₂) (n : ℤ) (φ : B ⟶ B⟦n⟧) :
    c₁ ≫ G₁.map φ ≫ (G₁.commShiftIso n).hom.app B ≫ (τ.app B)⟦n⟧' =
      c₂ ≫ G₂.map φ ≫ (G₂.commShiftIso n).hom.app B := by
  rw [NatTrans.shift_app_comm τ n B, ← hc, τ.naturality_assoc]
  simp only [Category.assoc]

/-- A morphism after `a[-n] ≫ (X[n][-n] ≅ X)` is the translate of the morphism shifted back. -/
theorem shift_map_comp_shiftFunctorCompIsoId_hom_app_comp {X Y Z : C} (n : ℤ) (a : X ⟶ Y⟦n⟧)
    (b : Y ⟶ Z) :
    a⟦-n⟧' ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app Y ≫ b =
      (a ≫ b⟦n⟧')⟦-n⟧' ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app Z := by
  rw [Functor.map_comp, Category.assoc]
  exact congrArg (a⟦-n⟧' ≫ ·)
    ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.naturality b).symm

/-- A functor commuting with the shift carries `φ[-n] ≫ (B[n][-n] ≅ B)` to the translate of
`G(φ)` read through the commutation isomorphisms. -/
theorem shift_comp_shiftFunctorCompIsoId_hom_app_eq_map (G : C ⥤ D) [G.CommShift ℤ] {A B : C}
    (n : ℤ) (φ : A ⟶ B⟦n⟧) :
    (G.map φ ≫ (G.commShiftIso n).hom.app B)⟦-n⟧' ≫
        (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app (G.obj B) =
      (G.commShiftIso (-n)).inv.app A ≫
        G.map (φ⟦-n⟧' ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app B) := by
  rw [← cancel_epi ((G.commShiftIso (-n)).hom.app A), Iso.hom_inv_id_app_assoc, G.map_comp,
    G.map_shiftFunctorCompIsoId_hom_app, Functor.commShiftIso_hom_naturality_assoc,
    Functor.map_comp, Category.assoc]

end Shift

/-- **An additive functor into modules carries a map of finite biproducts with bijective
components to a bijection.** -/
theorem bijective_map_biproduct_map {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {R : Type u} [Ring R] (H : C ⥤ ModuleCat.{u} R) [H.Additive] {N : ℕ}
    {A B : Fin N → C} (φ : ∀ i, A i ⟶ B i) (h : ∀ i, Function.Bijective (H.map (φ i))) :
    Function.Bijective (H.map (biproduct.map φ)) := by
  have hi : ∀ i, IsIso (H.map (φ i)) := fun i => (ConcreteCategory.isIso_iff_bijective _).2 (h i)
  have e : H.map (biproduct.map φ) = (H.mapBiproduct A).hom ≫
      (biproduct.mapIso fun i => asIso (H.map (φ i))).hom ≫ (H.mapBiproduct B).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    refine biproduct.hom_ext _ _ fun j => ?_
    simp only [Functor.mapBiproduct_hom, Category.assoc, biproduct.lift_π, biproduct.map_π,
      ← H.map_comp]
    simp
  rw [← ConcreteCategory.isIso_iff_bijective, e]
  infer_instance

/-- Applying a functor to `c ≫ y = x₁ ≫ x₂ ≫ e⁻¹`. -/
theorem map_comp_eq_of_eq_comp_inv {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {P Q R S₁ S' : C} (c : P ⟶ Q) (y : Q ⟶ R) (x₁ : P ⟶ S₁) (x₂ : S₁ ⟶ S') (e : R ≅ S')
    (h : c ≫ y = x₁ ≫ x₂ ≫ e.inv) : F.map x₁ ≫ F.map x₂ = F.map c ≫ F.map y ≫ F.map e.hom := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← Category.assoc, h]
  simp

/-- The bookkeeping behind `classDirectImageMorphism_comp_restrictComparisonX`, with every object
and morphism a variable. -/
theorem restrict_paste {D : Type*} [Category* D] {A F₀ F₁ F₀s G₀ G₁ G₀s G₂ H₀ K₀ H₂ Hs Ks K₂ : D}
    (dd : A ⟶ F₀) (xi : F₀ ⟶ F₁) (cs : F₁ ⟶ F₀s) (rc : F₀ ⟶ G₀) (rcm : F₁ ⟶ G₁)
    (rcs : G₁ ⟶ G₀s) (rcsh : F₀s ⟶ G₀s) (rxi : G₀ ⟶ G₂) (rics : G₂ ⟶ G₁) (compCs : G₂ ⟶ G₀s)
    (compS : G₀s ⟶ Hs) (eqS : Hs ⟶ Ks) (ct : G₀ ⟶ H₀) (eqq : H₀ ⟶ K₀) (rk : H₀ ⟶ H₂)
    (rkcs : H₂ ⟶ Hs) (rkC : K₀ ⟶ K₂) (rkCcs : K₂ ⟶ Ks) (cC : A ⟶ K₀) (sh : F₀s ⟶ Ks)
    (hsh : sh = rcsh ≫ compS ≫ eqS) (n₁ : rcm ≫ rcs = cs ≫ rcsh) (hs : xi ≫ rcm = rc ≫ rxi ≫ rics)
    (hcs : compCs = rics ≫ rcs)
    (e₁ : (dd ≫ rc) ≫ rxi ≫ compCs ≫ compS = ((dd ≫ rc) ≫ ct) ≫ rk ≫ rkcs)
    (e₂ : ((dd ≫ rc) ≫ ct) ≫ rk ≫ rkcs ≫ eqS = (((dd ≫ rc) ≫ ct) ≫ eqq) ≫ rkC ≫ rkCcs)
    (hDC : dd ≫ rc ≫ ct ≫ eqq = cC) :
    (dd ≫ xi ≫ cs) ≫ sh = cC ≫ rkC ≫ rkCcs := by
  subst hsh hcs hDC
  simp only [Category.assoc] at e₁ e₂ ⊢
  rw [← reassoc_of% n₁, reassoc_of% hs, reassoc_of% e₁, e₂]

/-- The bookkeeping behind `restrictComparisonY_comp_classDirectImageMorphism`, with every object
and morphism a variable. -/
theorem restrict_paste₂ {D : Type*} [Category* D] {A B₀ C₀ C₁ C₂ C₃ Hs Ks H₀ H₂ K₀ K₂ : D}
    (cY : A ⟶ B₀) (rcf : B₀ ⟶ C₀) (rxi : C₀ ⟶ C₁) (rcs₁ : C₁ ⟶ C₂) (rcs₂ : C₂ ⟶ C₃)
    (compCs : C₁ ⟶ C₃) (compS : C₃ ⟶ Hs) (eqS : Hs ⟶ Ks) (ct : C₀ ⟶ H₀) (eqq : H₀ ⟶ K₀)
    (rk : H₀ ⟶ H₂) (rkcs : H₂ ⟶ Hs) (rkC : K₀ ⟶ K₂) (rkCcs : K₂ ⟶ Ks) (cC : A ⟶ K₀)
    (Mmap : B₀ ⟶ C₂) (sh : C₃ ⟶ Ks) (hM : Mmap = rcf ≫ rxi ≫ rcs₁)
    (hcs : compCs = rcs₁ ≫ rcs₂) (hsh : sh = compS ≫ eqS)
    (e₁ : (cY ≫ rcf) ≫ rxi ≫ compCs ≫ compS = ((cY ≫ rcf) ≫ ct) ≫ rk ≫ rkcs)
    (e₂ : ((cY ≫ rcf) ≫ ct) ≫ rk ≫ rkcs ≫ eqS = (((cY ≫ rcf) ≫ ct) ≫ eqq) ≫ rkC ≫ rkCcs)
    (hDC : cY ≫ rcf ≫ ct ≫ eqq = cC) :
    cY ≫ Mmap ≫ rcs₂ ≫ sh = cC ≫ rkC ≫ rkCcs := by
  subst hM hcs hsh hDC
  simp only [Category.assoc] at e₁ e₂ ⊢
  rw [reassoc_of% e₁, e₂]

/-- The bookkeeping behind `classDirectImageSummand_comp_restrict`, with every object and morphism
a variable. -/
theorem summand_paste {D : Type*} [Category* D] (F : D ⥤ D) {A B C₁ C E G H : D} (cY : A ⟶ B)
    (M₁ : B ⟶ C₁) (M₂ : C₁ ⟶ C) (T2s : C ⟶ E) (sci₁ : F.obj C ⟶ G) (sci₂ : F.obj E ⟶ H) (T₂ : G ⟶ H)
    {G' : D} (L₁ : F.obj B ⟶ G') (L₂ : G' ⟶ G) (h3 : F.map (M₁ ≫ M₂) ≫ sci₁ = L₁ ≫ L₂)
    (h2b : F.map (M₁ ≫ M₂) ≫ sci₁ ≫ T₂ = F.map ((M₁ ≫ M₂) ≫ T2s) ≫ sci₂) :
    F.map (cY ≫ M₁ ≫ M₂ ≫ T2s) ≫ sci₂ = F.map cY ≫ L₁ ≫ L₂ ≫ T₂ := by
  rw [← Category.assoc L₁, ← h3, Category.assoc, h2b, ← F.map_comp_assoc]
  simp only [Category.assoc]

section Biproduct

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasShift C ℤ] [HasShift D ℤ]
  (G : C ⥤ D) [G.CommShift ℤ] {N : ℕ} (a : Fin N → ℤ)

/-- The comparison `⨁ (G X)[a_i] ⟶ G(⨁ X[a_i])` of a functor with finite biproducts and shifts. -/
abbrev biproductShiftComparison (X : C) :
    (⨁ fun i => (G.obj X)⟦a i⟧) ⟶ G.obj (⨁ fun i => X⟦a i⟧) :=
  biproduct.desc fun i => (G.commShiftIso (a i)).inv.app X ≫
    G.map (biproduct.ι (fun i => X⟦a i⟧) i)

/-- For an additive functor `G`, the comparison `⨁ (G X)[a_i] ⟶ G(⨁ X[a_i])` is an isomorphism. -/
instance [G.Additive] (X : C) : IsIso (biproductShiftComparison G a X) := by
  have e : biproductShiftComparison G a X =
      (biproduct.mapIso fun i => ((G.commShiftIso (a i)).app X).symm).hom ≫
        (G.mapBiproduct (fun i => X⟦a i⟧)).inv := by
    refine biproduct.hom_ext' _ _ fun i => ?_
    simp only [biproductShiftComparison, Functor.mapBiproduct_inv, biproduct.mapIso_hom,
      Iso.symm_hom, Iso.app_inv, biproduct.ι_desc, biproduct.ι_map_assoc]
  rw [e]
  infer_instance

/-- A morphism out of a biproduct, compared summand by summand with the image of one. -/
theorem biproduct_desc_comp_eq {A : Fin N → D} {Xb : C} {T E : D} {U : C}
    (s : ∀ i, A i ⟶ T) (R : T ⟶ E) (c : ∀ i, A i ⟶ (G.obj Xb)⟦a i⟧) (t : ∀ i, Xb⟦a i⟧ ⟶ U)
    (T₂ : G.obj U ⟶ E)
    (h : ∀ i, s i ≫ R = c i ≫ (G.commShiftIso (a i)).inv.app Xb ≫ G.map (t i) ≫ T₂) :
    biproduct.desc s ≫ R = biproduct.map c ≫ biproductShiftComparison G a Xb ≫
      G.map (biproduct.desc t) ≫ T₂ := by
  refine biproduct.hom_ext' _ _ fun i => ?_
  simp only [biproduct.ι_desc_assoc, biproduct.ι_map_assoc, biproductShiftComparison,
    Category.assoc, ← G.map_comp_assoc, biproduct.ι_desc]
  exact h i

end Biproduct

/-- Bijectivity on a functor into modules, read off an equation `a ≫ b ≫ c = d₁ ≫ d₂ ≫ d₃ ≫ d₄`. -/
theorem bijective_map_of_comp_eq {C : Type*} [Category* C] {R : Type u} [Ring R]
    (H : C ⥤ ModuleCat.{u} R) {A B B' E₀ D₁ D₂ D₃ : C} (a : A ⟶ B) (b : B ⟶ B') (c : B' ⟶ E₀)
    (d₁ : A ⟶ D₁) (d₂ : D₁ ⟶ D₂) (d₃ : D₂ ⟶ D₃) (d₄ : D₃ ⟶ E₀)
    (h : a ≫ b ≫ c = d₁ ≫ d₂ ≫ d₃ ≫ d₄) (hb : Function.Bijective (H.map b))
    (hc : Function.Bijective (H.map c)) (h₁ : Function.Bijective (H.map d₁))
    (h₂ : Function.Bijective (H.map d₂)) (h₃ : Function.Bijective (H.map d₃))
    (h₄ : Function.Bijective (H.map d₄)) : Function.Bijective (H.map a) := by
  have e := congrArg H.map h
  simp only [H.map_comp] at e
  have hr : Function.Bijective (H.map d₁ ≫ H.map d₂ ≫ H.map d₃ ≫ H.map d₄) :=
    h₄.comp (h₃.comp (h₂.comp h₁))
  rw [← e] at hr
  exact (Function.Bijective.of_comp_iff' (hc.comp hb) _).mp hr

end CategoryTheory

namespace AlgebraicGeometry.DeRhamLerayHirsch

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardCompIso)

/-- The transport between the derived direct images along two equal morphisms commutes with the
shift. -/
theorem derivedPushforward_eqToHom_shift {A B : RingedSpace.{u, u}} {k k' : A ⟶ B} (h : k = k')
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing B))}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing A))}
    (c : M ⟶ (derivedPushforward k).obj K) (n : ℤ) (φ : K ⟶ K⟦n⟧) :
    Eq (c ≫ (derivedPushforward k).map φ ≫ ((derivedPushforward k).commShiftIso n).hom.app K ≫
        (eqToHom (congrArg (fun k => (derivedPushforward k).obj K) h))⟦n⟧' :
          M ⟶ ((derivedPushforward k').obj K)⟦n⟧)
      ((c ≫ eqToHom (congrArg (fun k => (derivedPushforward k).obj K) h)) ≫
        (derivedPushforward k').map φ ≫ ((derivedPushforward k').commShiftIso n).hom.app K :
          M ⟶ ((derivedPushforward k').obj K)⟦n⟧) := by
  subst h
  simp

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (V : Y.Opens) (W : S.Opens)
  (hVW : V ≤ g ⁻¹ᵁ W)

/-- The square `(V ⟶ Y, W ⟶ S)`. -/
theorem restrictBase_w : V.ι ≫ g = g.resLE W V hVW ≫ W.ι :=
  (Scheme.Hom.resLE_comp_ι g hVW).symm

/-- The square `(f⁻¹V ⟶ X, W ⟶ S)`. -/
theorem restrict_w : (f ⁻¹ᵁ V).ι ≫ (f ≫ g) = (f ∣_ V ≫ g.resLE W V hVW) ≫ W.ι := by
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc, restrictBase_w g V W hVW]
  simp only [Category.assoc]

/-- The outer square `(f⁻¹V ⟶ Y, W ⟶ S)`. -/
theorem restrictOuter_w :
    ((f ⁻¹ᵁ V).ι ≫ f) ≫ g = (f ∣_ V ≫ g.resLE W V hVW) ≫ W.ι :=
  (Category.assoc _ _ _).trans (restrict_w f g V W hVW)

/-- The restriction of a class of `H^m_{dR}(X/S)` to `H^m_{dR}(f⁻¹V/W)`. -/
abbrev restrictClass (m : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :=
  deRhamPullbackSquare (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW) (f ≫ g) W.ι
    (restrict_w f g V W hVW) m ξ

/-- The morphism of inverse-image ringed spaces of the square `(f⁻¹V ⟶ X, W ⟶ S)`. -/
abbrev restrictMapX := inverseImageBaseMap (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW) (f ≫ g) W.ι
  (restrict_w f g V W hVW)

/-- The morphism of inverse-image ringed spaces of the square `(V ⟶ Y, W ⟶ S)`. -/
abbrev restrictMapY := inverseImageBaseMap V.ι (g.resLE W V hVW) g W.ι (restrictBase_w g V W hVW)

/-- The morphism of inverse-image ringed spaces of the outer square `(f⁻¹V ⟶ Y, W ⟶ S)`. -/
abbrev restrictMapOuter := inverseImageBaseMap ((f ⁻¹ᵁ V).ι ≫ f) (f ∣_ V ≫ g.resLE W V hVW) g W.ι
  (restrictOuter_w f g V W hVW)

/-- The morphisms of inverse-image ringed spaces along `f⁻¹V ⟶ X ⟶ Y` compose to that of the outer
square. -/
theorem restrictMapX_comp :
    restrictMapX f g V W hVW ≫ baseMap f g = restrictMapOuter f g V W hVW :=
  inverseImageBaseMap_comp f g (f ≫ g) (𝟙 S) (Category.comp_id _).symm (f ⁻¹ᵁ V).ι
    (f ∣_ V ≫ g.resLE W V hVW) W.ι (restrict_w f g V W hVW) ((f ⁻¹ᵁ V).ι ≫ f) W.ι
    (restrictOuter_w f g V W hVW) rfl (Category.comp_id _)

/-- The morphisms of inverse-image ringed spaces along `f⁻¹V ⟶ V ⟶ Y` compose to that of the outer
square. -/
theorem baseMap_comp_restrictMapY :
    baseMap (f ∣_ V) (g.resLE W V hVW) ≫ restrictMapY g V W hVW = restrictMapOuter f g V W hVW :=
  inverseImageBaseMap_comp V.ι g (g.resLE W V hVW) W.ι (restrictBase_w g V W hVW) (f ∣_ V)
    (f ∣_ V ≫ g.resLE W V hVW) (𝟙 W.toScheme) (Category.comp_id _).symm ((f ⁻¹ᵁ V).ι ≫ f) W.ι
    (restrictOuter_w f g V W hVW) (morphismRestrict_ι f V) (Category.id_comp _)

/-- The canonical map of the square `(f⁻¹V ⟶ X, W ⟶ S)`. -/
abbrev restrictComparisonX := deRhamComparisonQ (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW) (f ≫ g) W.ι
  (restrict_w f g V W hVW)

/-- The canonical map of the square `(V ⟶ Y, W ⟶ S)`. -/
abbrev restrictComparisonY := deRhamComparisonQ V.ι (g.resLE W V hVW) g W.ι
  (restrictBase_w g V W hVW)

/-- The canonical map of the outer square `(f⁻¹V ⟶ Y, W ⟶ S)`. -/
abbrev restrictComparisonOuter := deRhamComparisonQ ((f ⁻¹ᵁ V).ι ≫ f) (f ∣_ V ≫ g.resLE W V hVW) g
  W.ι (restrictOuter_w f g V W hVW)

/-- The composition isomorphism along `f⁻¹V ⟶ X ⟶ Y`, at `Ω^•_{f⁻¹V/W}`, landing in the direct
image along the outer square. -/
abbrev restrictCompX :=
  (derivedPushforwardCompIso (restrictMapX f g V W hVW) (baseMap f g)).hom.app
      (deRhamObject (f ∣_ V ≫ g.resLE W V hVW)) ≫
    eqToHom (congrArg (fun k => (derivedPushforward k).obj
      (deRhamObject (f ∣_ V ≫ g.resLE W V hVW))) (restrictMapX_comp f g V W hVW))

/-- The composition isomorphism along `f⁻¹V ⟶ V ⟶ Y`, at `Ω^•_{f⁻¹V/W}`, landing in the direct
image along the outer square. -/
abbrev restrictCompY :=
  (derivedPushforwardCompIso (baseMap (f ∣_ V) (g.resLE W V hVW)) (restrictMapY g V W hVW)).hom.app
      (deRhamObject (f ∣_ V ≫ g.resLE W V hVW)) ≫
    eqToHom (congrArg (fun k => (derivedPushforward k).obj
      (deRhamObject (f ∣_ V ≫ g.resLE W V hVW))) (baseMap_comp_restrictMapY f g V W hVW))

/-- The canonical maps of `f` and of `(f⁻¹V ⟶ X, W ⟶ S)` compose to that of the outer square. -/
theorem deRhamDirectImageMap_comp_restrictComparisonX :
    deRhamDirectImageMap f g ≫ (relativeDirectImage f g).map (restrictComparisonX f g V W hVW) ≫
      restrictCompX f g V W hVW = restrictComparisonOuter f g V W hVW :=
  deRhamComparisonQ_comp f g (f ≫ g) (𝟙 S) (Category.comp_id _).symm (f ⁻¹ᵁ V).ι
    (f ∣_ V ≫ g.resLE W V hVW) W.ι (restrict_w f g V W hVW) ((f ⁻¹ᵁ V).ι ≫ f) W.ι
    (restrictOuter_w f g V W hVW) rfl (Category.comp_id _)

/-- The canonical maps of `(V ⟶ Y, W ⟶ S)` and of `f ∣_ V` compose to that of the outer square. -/
theorem restrictComparisonY_comp_deRhamDirectImageMap :
    restrictComparisonY g V W hVW ≫ (derivedPushforward (restrictMapY g V W hVW)).map
      (deRhamDirectImageMap (f ∣_ V) (g.resLE W V hVW)) ≫ restrictCompY f g V W hVW =
      restrictComparisonOuter f g V W hVW :=
  deRhamComparisonQ_comp V.ι g (g.resLE W V hVW) W.ι (restrictBase_w g V W hVW) (f ∣_ V)
    (f ∣_ V ≫ g.resLE W V hVW) (𝟙 W.toScheme) (Category.comp_id _).symm ((f ⁻¹ᵁ V).ι ≫ f) W.ι
    (restrictOuter_w f g V W hVW) (morphismRestrict_ι f V) (Category.id_comp _)

/-- **`ξ̃` followed by the canonical map of `(f⁻¹V ⟶ X, W ⟶ S)`** is the canonical map of the
outer square followed by `(ξ|_{f⁻¹V})'`, by Remark 0FU7 for the square. -/
theorem classDirectImageMorphism_comp_restrictComparisonX (m : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    Eq (classDirectImageMorphism f g m ξ ≫
        ((relativeDirectImage f g).map (restrictComparisonX f g V W hVW) ≫
          restrictCompX f g V W hVW)⟦m⟧' :
        deRhamObject g ⟶ ((derivedPushforward (restrictMapOuter f g V W hVW)).obj
          (deRhamObject (f ∣_ V ≫ g.resLE W V hVW)))⟦m⟧)
      (restrictComparisonOuter f g V W hVW ≫
        (derivedPushforward (restrictMapOuter f g V W hVW)).map
          (classMorphism (f ∣_ V ≫ g.resLE W V hVW) m (restrictClass f g V W hVW m ξ)) ≫
        ((derivedPushforward (restrictMapOuter f g V W hVW)).commShiftIso m).hom.app _) := by
  have hstar := deRhamComparisonQ_comp_classMorphism (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW)
    (f ≫ g) W.ι (restrict_w f g V W hVW) m ξ
  have e₁ := comp_map_commShiftIso_hom_app_shift_eq
    (derivedPushforwardCompIso (restrictMapX f g V W hVW) (baseMap f g)).hom
    (deRhamDirectImageMap f g ≫ (relativeDirectImage f g).map (restrictComparisonX f g V W hVW)) _
    rfl m (classMorphism (f ∣_ V ≫ g.resLE W V hVW) m (restrictClass f g V W hVW m ξ))
  have e₂ := derivedPushforward_eqToHom_shift (restrictMapX_comp f g V W hVW)
    ((deRhamDirectImageMap f g ≫ (relativeDirectImage f g).map (restrictComparisonX f g V W hVW)) ≫
      (derivedPushforwardCompIso (restrictMapX f g V W hVW) (baseMap f g)).hom.app _) m
    (classMorphism (f ∣_ V ≫ g.resLE W V hVW) m (restrictClass f g V W hVW m ξ))
  have hDC := deRhamDirectImageMap_comp_restrictComparisonX f g V W hVW
  have hs := map_comp_eq_of_eq_comp_inv (relativeDirectImage f g) _ _ _ _
    (((derivedPushforward (restrictMapX f g V W hVW)).commShiftIso m).app
      (deRhamObject (f ∣_ V ≫ g.resLE W V hVW))) hstar
  have h'' := Functor.commShiftIso_comp_hom_app (derivedPushforward (restrictMapX f g V W hVW))
    (relativeDirectImage f g) m (deRhamObject (f ∣_ V ≫ g.resLE W V hVW))
  exact restrict_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by simp only [Functor.map_comp]) (Functor.commShiftIso_hom_naturality _ _ _) hs h'' e₁ e₂ hDC

/-- **The canonical map of `(V ⟶ Y, W ⟶ S)` followed by the direct image of the morphism `ξ̃` of
`f ∣_ V`** is the canonical map of the outer square followed by `(ξ|_{f⁻¹V})'`. -/
theorem restrictComparisonY_comp_classDirectImageMorphism (m : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    Eq (restrictComparisonY g V W hVW ≫ (derivedPushforward (restrictMapY g V W hVW)).map
          (classDirectImageMorphism (f ∣_ V) (g.resLE W V hVW) m (restrictClass f g V W hVW m ξ)) ≫
        ((derivedPushforward (restrictMapY g V W hVW)).commShiftIso m).hom.app _ ≫
        (restrictCompY f g V W hVW)⟦m⟧' :
        deRhamObject g ⟶ ((derivedPushforward (restrictMapOuter f g V W hVW)).obj
          (deRhamObject (f ∣_ V ≫ g.resLE W V hVW)))⟦m⟧)
      (restrictComparisonOuter f g V W hVW ≫
        (derivedPushforward (restrictMapOuter f g V W hVW)).map
          (classMorphism (f ∣_ V ≫ g.resLE W V hVW) m (restrictClass f g V W hVW m ξ)) ≫
        ((derivedPushforward (restrictMapOuter f g V W hVW)).commShiftIso m).hom.app _) := by
  have e₁ := comp_map_commShiftIso_hom_app_shift_eq
    (derivedPushforwardCompIso (baseMap (f ∣_ V) (g.resLE W V hVW)) (restrictMapY g V W hVW)).hom
    (restrictComparisonY g V W hVW ≫ (derivedPushforward (restrictMapY g V W hVW)).map
      (deRhamDirectImageMap (f ∣_ V) (g.resLE W V hVW))) _ rfl m
    (classMorphism (f ∣_ V ≫ g.resLE W V hVW) m (restrictClass f g V W hVW m ξ))
  have e₂ := derivedPushforward_eqToHom_shift (baseMap_comp_restrictMapY f g V W hVW)
    ((restrictComparisonY g V W hVW ≫ (derivedPushforward (restrictMapY g V W hVW)).map
      (deRhamDirectImageMap (f ∣_ V) (g.resLE W V hVW))) ≫
      (derivedPushforwardCompIso (baseMap (f ∣_ V) (g.resLE W V hVW))
        (restrictMapY g V W hVW)).hom.app _) m
    (classMorphism (f ∣_ V ≫ g.resLE W V hVW) m (restrictClass f g V W hVW m ξ))
  have hDC := restrictComparisonY_comp_deRhamDirectImageMap f g V W hVW
  have h'' := Functor.commShiftIso_comp_hom_app (derivedPushforward (baseMap (f ∣_ V)
    (g.resLE W V hVW))) (derivedPushforward (restrictMapY g V W hVW)) m
    (deRhamObject (f ∣_ V ≫ g.resLE W V hVW))
  exact restrict_paste₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by simp only [classDirectImageMorphism, Functor.map_comp, Functor.comp_map]; rfl) h''
    (Functor.map_comp _ _ _) e₁ e₂ hDC

/-- **A summand of `ξ̃`, followed by the canonical map of `(f⁻¹V ⟶ X, W ⟶ S)`**, is the shifted
canonical map of `(V ⟶ Y, W ⟶ S)` followed by the direct image of the corresponding summand of the
morphism `ξ̃` of `f ∣_ V` for the restricted class. -/
theorem classDirectImageSummand_comp_restrict (m : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m) :
    classDirectImageSummand f g m ξ ≫
        (relativeDirectImage f g).map (restrictComparisonX f g V W hVW) ≫
          restrictCompX f g V W hVW =
      (restrictComparisonY g V W hVW)⟦-m⟧' ≫
        ((derivedPushforward (restrictMapY g V W hVW)).commShiftIso (-m)).inv.app _ ≫
        (derivedPushforward (restrictMapY g V W hVW)).map
          (classDirectImageSummand (f ∣_ V) (g.resLE W V hVW) m (restrictClass f g V W hVW m ξ)) ≫
        restrictCompY f g V W hVW := by
  have l2a := shift_map_comp_shiftFunctorCompIsoId_hom_app_comp m (classDirectImageMorphism f g m ξ)
    ((relativeDirectImage f g).map (restrictComparisonX f g V W hVW) ≫ restrictCompX f g V W hVW)
  have l3 := shift_comp_shiftFunctorCompIsoId_hom_app_eq_map
    (derivedPushforward (restrictMapY g V W hVW)) m
    (classDirectImageMorphism (f ∣_ V) (g.resLE W V hVW) m (restrictClass f g V W hVW m ξ))
  have l2b := shift_map_comp_shiftFunctorCompIsoId_hom_app_comp m
    ((derivedPushforward (restrictMapY g V W hVW)).map
      (classDirectImageMorphism (f ∣_ V) (g.resLE W V hVW) m (restrictClass f g V W hVW m ξ)) ≫
      ((derivedPushforward (restrictMapY g V W hVW)).commShiftIso m).hom.app _)
    (restrictCompY f g V W hVW)
  have hT := classDirectImageMorphism_comp_restrictComparisonX f g V W hVW m ξ
  have hB := restrictComparisonY_comp_classDirectImageMorphism f g V W hVW m ξ
  refine (Category.assoc _ _ _).trans (l2a.trans ((congrArg (fun z => z⟦-m⟧' ≫
    (shiftFunctorCompIsoId _ m (-m) (add_neg_cancel m)).hom.app _) (hT.trans hB.symm)).trans ?_))
  exact summand_paste (shiftFunctor _ (-m)) _ _ _ _ _ _ _ _ _ l3 l2b

variable {N : ℕ} (n : Fin N → ℕ)
  (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))

/-- **The morphism `ξ̃` of `f`, followed by the canonical map of `(f⁻¹V ⟶ X, W ⟶ S)`**, is the
canonical map of `(V ⟶ Y, W ⟶ S)` followed by the direct image of the morphism `ξ̃` of `f ∣_ V` for
the restricted classes. -/
theorem lerayHirschMorphism_comp_restrict :
    lerayHirschMorphism f g n ξ ≫
        (relativeDirectImage f g).map (restrictComparisonX f g V W hVW) ≫
          restrictCompX f g V W hVW =
      biproduct.map (fun i => (restrictComparisonY g V W hVW)⟦-(n i : ℤ)⟧') ≫
        biproductShiftComparison (derivedPushforward (restrictMapY g V W hVW))
          (fun i => -(n i : ℤ)) (deRhamObject (g.resLE W V hVW)) ≫
        (derivedPushforward (restrictMapY g V W hVW)).map
          (lerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n
            fun i => restrictClass f g V W hVW (n i) (ξ i)) ≫
        restrictCompY f g V W hVW :=
  biproduct_desc_comp_eq (derivedPushforward (restrictMapY g V W hVW)) (fun i => -(n i : ℤ)) _ _ _ _
    _ fun i => classDirectImageSummand_comp_restrict f g V W hVW (n i) (ξ i)

/-- A morphism whose image under derived sections over `V` is an isomorphism keeps this property
after a shift. -/
theorem isIso_derivedSectionsOverOpen_map_shift {Z : RingedSpace.{u, u}}
    (U : TopologicalSpace.Opens Z.carrier)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))} (c : K ⟶ L)
    (hc : IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen Z U).map c))
    (a : ℤ) :
    IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen Z U).map (c⟦a⟧')) := by
  have : IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen Z U).map (c⟦a⟧') ≫
      ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
        Z U).commShiftIso a).hom.app L) := by
    rw [Functor.commShiftIso_hom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      Z U).commShiftIso a).hom.app L)

include hVW in
/-- The derived sections over `V` of the canonical map of `(V ⟶ Y, W ⟶ S)` are an isomorphism. -/
theorem isIso_derivedSectionsOverOpen_map_restrictComparisonY :
    IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
        (inverseImageBase g) V).map
      (restrictComparisonY g V W hVW)) :=
  isIso_derivedSectionsOverOpen_map_deRhamComparisonQ V.ι (g.resLE W V hVW) g W.ι
    (restrictBase_w g V W hVW) V (Scheme.Opens.opensRange_ι V).ge

/-- The derived sections over `f⁻¹V` of the canonical map of `(f⁻¹V ⟶ X, W ⟶ S)` are an
isomorphism. -/
theorem isIso_derivedSectionsOverOpen_map_restrictComparisonX :
    IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
        (inverseImageBase (f ≫ g))
        ((RingedSpaceModuleAdjunction.opensMap (baseMap f g)).obj V)).map
      (restrictComparisonX f g V W hVW)) :=
  isIso_derivedSectionsOverOpen_map_deRhamComparisonQ (f ⁻¹ᵁ V).ι (f ∣_ V ≫ g.resLE W V hVW) (f ≫ g)
    W.ι (restrict_w f g V W hVW) _ fun x hx => by rwa [Scheme.Opens.opensRange_ι]

/-- **Over an open `V ⊆ g⁻¹W`, the map induced by `ξ̃` on `H^k(V, -)` is bijective as soon as
the morphism `ξ̃` of `f ∣_ V` over `W`, for the restricted classes, induces bijections on
cohomology.** -/
theorem bijective_homology_lerayHirschMorphism_of_restrict
    (h : ∀ k, Function.Bijective ((cohomologyFunctor (g.resLE W V hVW) k).map
      (lerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n
        fun i => restrictClass f g V W hVW (n i) (ξ i))).hom) (k : ℤ) :
    Function.Bijective ((DerivedCategory.homologyFunctor _ k).map
      ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (inverseImageBase g) V).map
        (lerayHirschMorphism f g n ξ))) := by
  let H := Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (inverseImageBase g) V ⋙
    DerivedCategory.homologyFunctor _ k
  have hX := isIso_derivedSectionsOverOpen_map_restrictComparisonX f g V W hVW
  have h₁ : Function.Bijective (H.map (biproduct.map fun i =>
      (restrictComparisonY g V W hVW)⟦-(n i : ℤ)⟧')) := by
    refine bijective_map_biproduct_map H _ fun i => ?_
    have := isIso_derivedSectionsOverOpen_map_shift (Z := inverseImageBase g) V _
      (isIso_derivedSectionsOverOpen_map_restrictComparisonY g V W hVW) (-(n i : ℤ))
    exact (ConcreteCategory.isIso_iff_bijective _).1 <| Functor.map_isIso
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing (inverseImageBase g)).obj.obj (op V))) k)
      ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (inverseImageBase g) V).map
        ((restrictComparisonY g V W hVW)⟦-(n i : ℤ)⟧'))
  have h₃ : Function.Bijective (H.map ((derivedPushforward (restrictMapY g V W hVW)).map
      (lerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n
        fun i => restrictClass f g V W hVW (n i) (ξ i)))) := by
    refine (Stacks.Cohomology.OpenImmersionSections.bijective_homology_map_derivedPushforward_iff
      (restrictMapY g V W hVW) V _ k).2 ?_
    have key : ∀ (U' : TopologicalSpace.Opens (inverseImageBase (g.resLE W V hVW)).carrier),
        U' = ⊤ → Function.Bijective ((DerivedCategory.homologyFunctor _ k).map
          ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen _ U').map
            (lerayHirschMorphism (f ∣_ V) (g.resLE W V hVW) n
              fun i => restrictClass f g V W hVW (n i) (ξ i)))) := by
      rintro _ rfl
      exact h k
    exact key _ (Scheme.Opens.ι_preimage_self V)
  have h₅ : Function.Bijective (H.map ((relativeDirectImage f g).map
      (restrictComparisonX f g V W hVW))) :=
    (Stacks.Cohomology.OpenImmersionSections.bijective_homology_map_derivedPushforward_iff
      (baseMap f g) V _ k).2 (ConcreteCategory.bijective_of_isIso _)
  have h₂ : Function.Bijective (H.map (biproductShiftComparison
      (derivedPushforward (restrictMapY g V W hVW)) (fun i => -(n i : ℤ))
        (deRhamObject (g.resLE W V hVW)))) :=
    ConcreteCategory.bijective_of_isIso _
  exact bijective_map_of_comp_eq H _ _ _ _ _ _ _
    (lerayHirschMorphism_comp_restrict f g V W hVW n ξ) h₅
    (ConcreteCategory.bijective_of_isIso _) h₁ h₂ h₃ (ConcreteCategory.bijective_of_isIso _)

end AlgebraicGeometry.DeRhamLerayHirsch
