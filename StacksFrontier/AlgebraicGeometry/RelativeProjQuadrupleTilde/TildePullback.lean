module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.LocalHom
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.PullbackCover
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Global

/-!
# Property (2) of Tag 01O7: compatibility with pullback

For a quadruple `P = (f : T → S, d, L, ψ)` classifying `h : T ⟶ Proj_S(𝒜)` and `g : T' ⟶ T`, the
pulled-back quadruple classifies `g ≫ h`, and its isomorphism `ℳ̃_{T'} ≅ (g ≫ h)^*ℳ̃` of property
(1) is the pullback along `g` of the isomorphism `ℳ̃_T ≅ h^*ℳ̃` of `P`, read through
`ℳ̃_{T'} ≅ g^*ℳ̃_T` and `g^*h^*ℳ̃ ≅ (g ≫ h)^*ℳ̃`.

Both sides are determined by their chart formulas on a covering of `T'` by chart data; the chart
formula of the pulled-back isomorphism along `a : Z ⟶ T'` is the chart formula of the
isomorphism of `P` along `a ≫ g`, with the chart datum transported along `a^*g^*L ≅ (a ≫ g)^*L`
(`pullback_map_pullbackHom_eq`).

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.Quadruple.tildeComparison_pullback`:
  property (2).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr (congrIso)
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

private theorem pullback_square {C : Type*} [Category C] {X0 X1 X2 X3 Y1 Y2 S S' W : C}
    (m1 : X0 ⟶ X1) (m1i : X1 ⟶ X0) (m2 : X1 ⟶ X2) (m3 : X2 ⟶ X3)
    (pag : X1 ⟶ Y1) (pagi : Y1 ⟶ X1) (Φag : Y1 ⟶ Y2) (pag' : Y2 ⟶ X2)
    (A'' : Y1 ⟶ S') (D'' : S' ⟶ W) (pcagh : W ⟶ Y2) (Aψ : X0 ⟶ S) (cong : S ⟶ S')
    (D' : S ⟶ W) (q : W ⟶ X3)
    (hm1 : m1 ≫ m1i = 𝟙 _) (hpag : pag ≫ pagi = 𝟙 _)
    (hm2 : m2 = pag ≫ Φag ≫ pag') (hΦ : Φag = A'' ≫ D'' ≫ pcagh)
    (haux : pagi ≫ m1i ≫ Aψ ≫ cong = A'') (hcong : D' = cong ≫ D'')
    (hq : pcagh ≫ pag' ≫ m3 = q) :
    m1 ≫ m2 ≫ m3 = Aψ ≫ D' ≫ q := by
  subst hm2 hΦ hcong hq haux
  simp only [Category.assoc]
  rw [reassoc_of% hpag, reassoc_of% hm1]

private theorem inv_of_comp_eq_id {C : Type*} [Category C] {X0 X1 X2 X3 : C}
    (x : X0 ⟶ X1) (y : X1 ⟶ X2) (z : X2 ⟶ X3) (w : X3 ⟶ X0) (yi : X2 ⟶ X1) (zi : X3 ⟶ X2)
    (wi : X0 ⟶ X3) (h : x ≫ y ≫ z ≫ w = 𝟙 _) (hy : y ≫ yi = 𝟙 _) (hz : z ≫ zi = 𝟙 _)
    (hw : w ≫ wi = 𝟙 _) : wi ≫ zi ≫ yi = x := by
  calc wi ≫ zi ≫ yi = (x ≫ y ≫ z ≫ w) ≫ wi ≫ zi ≫ yi := by rw [h, Category.id_comp]
    _ = x := by
      simp only [Category.assoc]
      rw [reassoc_of% hw, reassoc_of% hz, hy, Category.comp_id]

section Pullback

variable {s : Stacks.RelativeProj.Situation.{u}} {T : Scheme.{u}} {f : T ⟶ s.base} {d : ℕ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {ψ : Twisting f s.algebra (d : ℤ) L} {h : T ⟶ relativeProj s}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] (hd : 0 < d)

/-- The associativity coherence of the composition law for pullback, read as the composition
law along `g ≫ h` pulled back along `a`. -/
theorem pullbackComp_comp_inv_app {Z T' : Scheme.{u}} {X : Scheme.{u}} (a : Z ⟶ T') (g : T' ⟶ T)
    (h' : T ⟶ X) (N : X.Modules) :
    (Scheme.Modules.pullbackComp (a ≫ g) h').inv.app N ≫
        (Scheme.Modules.pullbackComp a g).inv.app ((Scheme.Modules.pullback h').obj N) ≫
          (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp g h').hom.app N) =
      (Scheme.Modules.pullbackComp a (g ≫ h')).inv.app N :=
  inv_of_comp_eq_id (C := Z.Modules) _ _ _ _ _ _ _ (pullbackComp_assoc_app a g h' N)
    (((Scheme.Modules.pullback a).mapIso
      ((Scheme.Modules.pullbackComp g h').app N)).inv_hom_id)
    (Iso.hom_inv_id_app _ _) (Iso.hom_inv_id_app _ _)

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The comparison `ℳ̃` of a composite pullback, `(a ≫ g)^*ℳ̃_T ≅ ℳ̃_Z`, through `g`. -/
theorem associatedSheafPullbackIso_comp' {Z T' : Scheme.{u}} (g : T' ⟶ T) (a : Z ⟶ T') :
    (Scheme.Modules.pullbackComp a g).inv.app (src ℳ f ψ) ≫
        (Scheme.Modules.pullback a).map
          (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L g ψ).hom ≫
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ)
          ((pullbackFunctor (ringedSpaceHom g)).obj L) a (ψ.pullback g)).hom ≫
        (associatedSheafCongrIso (ℳ.toGradedModule s.mul_comm) ((ψ.pullback g).pullback a)
          (ψ.pullback (a ≫ g)) (LaurentComposition.compCmp a g L)
          (fun n => ψ.pullbackApp_comp g a n)).hom =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L (a ≫ g) ψ).hom :=
  (congrArg (· ≫ _) (compComparison_eq_pullbackComp_inv a g (src ℳ f ψ))).symm.trans
    (associatedSheafPullbackIso_comp (ℳ.toGradedModule s.mul_comm) (d : ℤ) L g a ψ)

/-- The comparison of the transported chart datum, read at the composite `a ≫ g`. -/
private theorem iso_congr_reassoc {T' : Scheme.{u}} (g : T' ⟶ T) {Z : Scheme.{u}} (a : Z ⟶ T')
    (D : ChartDatum (a ≫ g ≫ f) ((ψ.pullback g).pullback a) (a ≫ g ≫ h)) :
    (ChartDatum.iso ℳ (f := (a ≫ g) ≫ f) (ψ := ψ.pullback (a ≫ g)) (h := (a ≫ g) ≫ h)
        (D.congr (LaurentComposition.compCmp a g L) (ψ.pullback (a ≫ g))
          (fun n => ψ.pullbackApp_comp g a n)) hd).hom =
      ((D.congr (LaurentComposition.compCmp a g L) (ψ.pullback (a ≫ g))
        (fun n => ψ.pullbackApp_comp g a n)).iso ℳ hd).hom :=
  rfl

/-- The chart formula along `a ≫ g`, at the chart datum transported from the pulled-back
twisting. -/
private theorem chart_comp (Φ : src ℳ f ψ ≅ (Scheme.Modules.pullback h).obj (moduleSheaf ℳ))
    (hΦ : ∀ {Z : Scheme.{u}} (a : Z ⟶ T) (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)),
      (Scheme.Modules.pullback a).map Φ.hom =
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ).hom ≫
          (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp a h).inv.app (moduleSheaf ℳ))
    {T' : Scheme.{u}} (g : T' ⟶ T) {Z : Scheme.{u}} (a : Z ⟶ T')
    (D : ChartDatum (a ≫ g ≫ f) ((ψ.pullback g).pullback a) (a ≫ g ≫ h)) :
    (Scheme.Modules.pullback (a ≫ g)).map Φ.hom =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L (a ≫ g) ψ).hom ≫
        ((D.congr (LaurentComposition.compCmp a g L) (ψ.pullback (a ≫ g))
          (fun n => ψ.pullbackApp_comp g a n)).iso ℳ hd).hom ≫
        (Scheme.Modules.pullbackComp (a ≫ g) h).inv.app (moduleSheaf ℳ) :=
  (hΦ (a ≫ g) (D.congr (LaurentComposition.compCmp a g L) (ψ.pullback (a ≫ g))
    (fun n => ψ.pullbackApp_comp g a n))).trans
    (congrArg (fun i =>
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L (a ≫ g) ψ).hom ≫ i ≫
        (Scheme.Modules.pullbackComp (a ≫ g) h).inv.app (moduleSheaf ℳ))
      (iso_congr_reassoc ℳ hd g a D))

/-- **The chart formula for the pulled-back comparison.** If `Φ : ℳ̃_T ≅ h^*ℳ̃` satisfies the chart
formula along every morphism carrying a chart datum, then for `g : T' ⟶ T` the composite
`ℳ̃_{T'} ≅ g^*ℳ̃_T ⟶ g^*h^*ℳ̃ ≅ (g ≫ h)^*ℳ̃` satisfies the chart formula of `(g ≫ f, g^*ψ)` and
`g ≫ h` along every morphism `a : Z ⟶ T'` carrying a chart datum `D` of them. -/
theorem pullback_map_pullbackHom_eq
    (Φ : src ℳ f ψ ≅ (Scheme.Modules.pullback h).obj (moduleSheaf ℳ))
    (hΦ : ∀ {Z : Scheme.{u}} (a : Z ⟶ T) (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)),
      (Scheme.Modules.pullback a).map Φ.hom =
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ).hom ≫
          (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp a h).inv.app (moduleSheaf ℳ))
    {T' : Scheme.{u}} (g : T' ⟶ T) {Z : Scheme.{u}} (a : Z ⟶ T')
    (D : ChartDatum (a ≫ g ≫ f) ((ψ.pullback g).pullback a) (a ≫ g ≫ h)) :
    (Scheme.Modules.pullback a).map
        ((associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L g ψ).inv ≫
          (Scheme.Modules.pullback g).map Φ.hom ≫
            (Scheme.Modules.pullbackComp g h).hom.app (moduleSheaf ℳ)) =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ)
          ((pullbackFunctor (ringedSpaceHom g)).obj L) a (ψ.pullback g)).hom ≫
        (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp a (g ≫ h)).inv.app (moduleSheaf ℳ) := by
  have hΦag := chart_comp ℳ hd Φ hΦ g a D
  have hcong := ChartDatum.iso_congr ℳ hd D (LaurentComposition.compCmp a g L)
    (ψ.pullback (a ≫ g)) (fun n => ψ.pullbackApp_comp g a n)
  have haux := associatedSheafPullbackIso_comp' (f := f) (L := L) (ψ := ψ) ℳ g a
  have hq := pullbackComp_comp_inv_app a g h (moduleSheaf ℳ)
  refine ((Functor.map_comp _ _ _).trans (congrArg _ (Functor.map_comp _ _ _))).trans ?_
  exact pullback_square (C := Z.Modules)
    ((Scheme.Modules.pullback a).map
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L g ψ).inv)
    ((Scheme.Modules.pullback a).map
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L g ψ).hom)
    ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullback g).map Φ.hom))
    ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp g h).hom.app (moduleSheaf ℳ)))
    ((Scheme.Modules.pullbackComp a g).hom.app (src ℳ f ψ))
    ((Scheme.Modules.pullbackComp a g).inv.app (src ℳ f ψ))
    ((Scheme.Modules.pullback (a ≫ g)).map Φ.hom)
    ((Scheme.Modules.pullbackComp a g).inv.app ((Scheme.Modules.pullback h).obj (moduleSheaf ℳ)))
    (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L (a ≫ g) ψ).hom
    ((D.congr (LaurentComposition.compCmp a g L) (ψ.pullback (a ≫ g))
        (fun n => ψ.pullbackApp_comp g a n)).iso ℳ hd).hom
    ((Scheme.Modules.pullbackComp (a ≫ g) h).inv.app (moduleSheaf ℳ))
    (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ)
      ((pullbackFunctor (ringedSpaceHom g)).obj L) a (ψ.pullback g)).hom
    (associatedSheafCongrIso (ℳ.toGradedModule s.mul_comm) ((ψ.pullback g).pullback a)
      (ψ.pullback (a ≫ g)) (LaurentComposition.compCmp a g L)
      (fun n => ψ.pullbackApp_comp g a n)).hom
    (D.iso ℳ hd).hom
    ((Scheme.Modules.pullbackComp a (g ≫ h)).inv.app (moduleSheaf ℳ))
    (((Scheme.Modules.pullback a).mapIso
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L g ψ)).inv_hom_id)
    (Iso.hom_inv_id_app _ _)
    (NatIso.naturality_2 (Scheme.Modules.pullbackComp a g) Φ.hom).symm
    hΦag haux hcong hq

/-- **Compatibility with pullback, from the chart formulas.** Let `Φ : ℳ̃_T ≅ h^*ℳ̃` satisfy the
chart formula along every morphism carrying a chart datum, `g : T' ⟶ T`, and `Φ'` an isomorphism
`ℳ̃_{T'} ≅ h'^*ℳ̃` for a morphism `h' = g ≫ h`, satisfying the chart formula of `(g ≫ f, g^*ψ, h')`
along the opens of a covering of `T'` by chart data. Then `Φ'` is `g^*Φ` read through
`ℳ̃_{T'} ≅ g^*ℳ̃_T`, `g^*h^*ℳ̃ ≅ (g ≫ h)^*ℳ̃` and `(g ≫ h)^*ℳ̃ = h'^*ℳ̃`. -/
theorem hom_eq_pullback_of_chart
    (Φ : src ℳ f ψ ≅ (Scheme.Modules.pullback h).obj (moduleSheaf ℳ))
    (hΦ : ∀ {Z : Scheme.{u}} (a : Z ⟶ T) (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)),
      (Scheme.Modules.pullback a).map Φ.hom =
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ).hom ≫
          (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp a h).inv.app (moduleSheaf ℳ))
    {T' : Scheme.{u}} (g : T' ⟶ T) {h' : T' ⟶ relativeProj s} (e : h' = g ≫ h)
    (Φ' : src ℳ (g ≫ f) (ψ.pullback g) ≅ (Scheme.Modules.pullback h').obj (moduleSheaf ℳ))
    (hex' : ∀ t : T', ∃ V : T'.Opens, t ∈ V ∧
      Nonempty (ChartDatum (V.ι ≫ g ≫ f) ((ψ.pullback g).pullback V.ι) (V.ι ≫ h')))
    (hΦ' : ∀ (V : T'.Opens) (D : ChartDatum (V.ι ≫ g ≫ f) ((ψ.pullback g).pullback V.ι) (V.ι ≫ h')),
      (Scheme.Modules.pullback V.ι).map Φ'.hom =
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ)
            ((pullbackFunctor (ringedSpaceHom g)).obj L) V.ι (ψ.pullback g)).hom ≫
          (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp V.ι h').inv.app (moduleSheaf ℳ)) :
    Φ'.hom = (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L g ψ).inv ≫
      (Scheme.Modules.pullback g).map Φ.hom ≫
        (Scheme.Modules.pullbackComp g h).hom.app (moduleSheaf ℳ) ≫
          (Scheme.Modules.pullbackCongr e.symm).hom.app (moduleSheaf ℳ) := by
  subst e
  refine Eq.trans ?_ (congrArg (fun x => _ ≫ _ ≫ _ ≫ x)
    (show (Scheme.Modules.pullbackCongr (rfl : g ≫ h = g ≫ h)).hom.app (moduleSheaf ℳ) = 𝟙 _ by
      simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app])).symm
  refine Eq.trans ?_ (congrArg (fun x => _ ≫ _ ≫ x) (Category.comp_id _)).symm
  refine ModuleHomGlue.hom_ext_of_pullbackCover (fun t : T' => (hex' t).choose)
    (fun t => ⟨t, (hex' t).choose_spec.1⟩) fun t => ?_
  exact (hΦ' _ (hex' t).choose_spec.2.some).trans
    (pullback_map_pullbackHom_eq ℳ hd Φ hΦ g _ (hex' t).choose_spec.2.some).symm

/-- `hom_eq_pullback_of_chart` for any invertible module `L'` and twisting `ψ'` that are the
pullbacks of `L` and `ψ`, and any isomorphism `A` that is `ℳ̃_{T'} ≅ g^*ℳ̃_T`. -/
theorem hom_eq_pullback_of_chart'
    (Φ : src ℳ f ψ ≅ (Scheme.Modules.pullback h).obj (moduleSheaf ℳ))
    (hΦ : ∀ {Z : Scheme.{u}} (a : Z ⟶ T) (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)),
      (Scheme.Modules.pullback a).map Φ.hom =
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ).hom ≫
          (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp a h).inv.app (moduleSheaf ℳ))
    {T' : Scheme.{u}} (g : T' ⟶ T) {h' : T' ⟶ relativeProj s} (e : h' = g ≫ h)
    {L' : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)}
    {inst' : Stacks.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf (isSheafStruct T') L'}
    (ψ' : Twisting (g ≫ f) s.algebra (d : ℤ) L')
    (hL : (pullbackFunctor (ringedSpaceHom g)).obj L = L') (hψ : HEq (ψ.pullback g) ψ')
    (Φ' : src ℳ (g ≫ f) ψ' ≅ (Scheme.Modules.pullback h').obj (moduleSheaf ℳ))
    (hex' : ∀ t : T', ∃ V : T'.Opens, t ∈ V ∧
      Nonempty (ChartDatum (V.ι ≫ g ≫ f) (ψ'.pullback V.ι) (V.ι ≫ h')))
    (hΦ' : ∀ (V : T'.Opens) (D : ChartDatum (V.ι ≫ g ≫ f) (ψ'.pullback V.ι) (V.ι ≫ h')),
      (Scheme.Modules.pullback V.ι).map Φ'.hom =
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L' V.ι ψ').hom ≫
          (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp V.ι h').inv.app (moduleSheaf ℳ))
    (A : (pullbackFunctor (ringedSpaceHom g)).obj
        (Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) ψ) ≅
      Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) ψ')
    (hA : HEq (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L g ψ) A) :
    Φ'.hom = A.inv ≫ (Scheme.Modules.pullback g).map Φ.hom ≫
        (Scheme.Modules.pullbackComp g h).hom.app (moduleSheaf ℳ) ≫
          (Scheme.Modules.pullbackCongr e.symm).hom.app (moduleSheaf ℳ) := by
  subst hL
  obtain rfl : inst' =
      PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj (ringedSpaceHom g) L :=
    Subsingleton.elim _ _
  subst hψ
  subst hA
  exact hom_eq_pullback_of_chart ℳ hd Φ hΦ g e Φ' hex' hΦ'

end Pullback

section Quadruple

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] {d : ℕ} (hd : 0 < d)

/-- `hom_eq_pullback_of_chart'` for a quadruple `P` and a quadruple `P'` over `T'` whose module
and twisting are those of `P` pulled back along `g`. -/
theorem hom_eq_pullback_quadruple {T : Scheme.{u}} {f : T ⟶ s.base}
    (P : Quadruple f s.algebra (d : ℤ)) {h : T ⟶ relativeProj s} {T' : Scheme.{u}} (g : T' ⟶ T)
    (P' : Quadruple (g ≫ f) s.algebra (d : ℤ)) {h' : T' ⟶ relativeProj s} :
    letI := P.isInvertible
    letI := P'.isInvertible
    ∀ (Φ : src ℳ f P.twisting ≅ (Scheme.Modules.pullback h).obj (moduleSheaf ℳ))
    (_ : ∀ {Z : Scheme.{u}} (a : Z ⟶ T) (D : ChartDatum (a ≫ f) (P.twisting.pullback a) (a ≫ h)),
      (Scheme.Modules.pullback a).map Φ.hom =
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) P.L a P.twisting).hom ≫
          (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp a h).inv.app (moduleSheaf ℳ))
    (Φ' : src ℳ (g ≫ f) P'.twisting ≅ (Scheme.Modules.pullback h').obj (moduleSheaf ℳ))
    (_ : ∀ (V : T'.Opens) (D : ChartDatum (V.ι ≫ g ≫ f) (P'.twisting.pullback V.ι) (V.ι ≫ h')),
      (Scheme.Modules.pullback V.ι).map Φ'.hom =
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ)
            P'.L V.ι P'.twisting).hom ≫
          (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp V.ι h').inv.app (moduleSheaf ℳ))
    (_ : ∀ t : T', ∃ V : T'.Opens, t ∈ V ∧
      Nonempty (ChartDatum (V.ι ≫ g ≫ f) (P'.twisting.pullback V.ι) (V.ι ≫ h')))
    (e : h' = g ≫ h) (_ : (pullbackFunctor (ringedSpaceHom g)).obj P.L = P'.L)
    (_ : HEq (P.twisting.pullback g) P'.twisting)
    (A : (pullbackFunctor (ringedSpaceHom g)).obj
        (Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) P.twisting) ≅
      Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) P'.twisting)
    (_ : HEq (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) P.L g P.twisting)
      A),
    Φ'.hom = A.inv ≫ (Scheme.Modules.pullback g).map Φ.hom ≫
        (Scheme.Modules.pullbackComp g h).hom.app (moduleSheaf ℳ) ≫
          (Scheme.Modules.pullbackCongr e.symm).hom.app (moduleSheaf ℳ) :=
  let := P.isInvertible
  let := P'.isInvertible
  fun Φ hΦ Φ' hΦ' hex e hL hψ A hA =>
    hom_eq_pullback_of_chart' ℳ hd Φ hΦ g e P'.twisting hL hψ Φ' hex hΦ' A hA

/-- **Property (2) of [Stacks, Tag 01O7]: the isomorphisms of property (1) are compatible with
pullbacks.** For a quadruple `P = (f : T → S, d, L, ψ)` classifying `h : T ⟶ Proj_S(𝒜)` and a
morphism `g : T' ⟶ T`, the pulled-back quadruple `P.pullback g` classifies `g ≫ h`, and its
isomorphism `ℳ̃_{T'} ≅ (g ≫ h)^*ℳ̃` of property (1) is the pullback along `g` of the isomorphism
`ℳ̃_T ≅ h^*ℳ̃` of `P`, read through the canonical comparisons `ℳ̃_{T'} ≅ g^*ℳ̃_T` and
`g^*h^*ℳ̃ ≅ (g ≫ h)^*ℳ̃`. -/
@[stacks 01O7 "property (2): the isomorphisms of property (1) are compatible with pullback along
every morphism of test schemes"]
theorem Quadruple.tildeComparison_pullback {T : Scheme.{u}} {f : T ⟶ s.base}
    (P : Quadruple f s.algebra (d : ℤ)) {T' : Scheme.{u}} (g : T' ⟶ T) :
    letI := P.isInvertible
    (Quadruple.tildeComparison ℳ hd (P.pullback g)).hom =
      (Quadruple.associatedSheafPullbackIso (M := ℳ.toGradedModule s.mul_comm) (P := P)
          (g := g)).inv ≫
        (Scheme.Modules.pullback g).map (Quadruple.tildeComparison ℳ hd P).hom ≫
          (Scheme.Modules.pullbackComp g (classifyingHom s (by exact_mod_cast hd) P)).hom.app
            (moduleSheaf ℳ) ≫
            (Scheme.Modules.pullbackCongr
              (classifyingHom_pullback s (by exact_mod_cast hd) P g).symm).hom.app
                (moduleSheaf ℳ) :=
  let := P.isInvertible
  hom_eq_pullback_quadruple ℳ hd P g (P.pullback g) (Quadruple.tildeComparison ℳ hd P)
    (fun a D => (Quadruple.tildeComparison_chart ℳ hd P a D).trans (localHom_eq ℳ hd a D))
    (Quadruple.tildeComparison ℳ hd (P.pullback g))
    (fun V D => (Quadruple.tildeComparison_chart ℳ hd (P.pullback g) V.ι D).trans
      (localHom_eq ℳ hd V.ι D))
    (exists_chartDatum s hd (g ≫ f) (P.pullback g))
    (classifyingHom_pullback s (by exact_mod_cast hd) P g) rfl HEq.rfl
    (Quadruple.associatedSheafPullbackIso (M := ℳ.toGradedModule s.mul_comm) (P := P) (g := g))
    HEq.rfl

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
