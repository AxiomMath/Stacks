module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.DatumPullback

/-!
# The local comparisons of Tag 01O7 (1) and their restrictions

For a quadruple `(f : T → S, d, L, ψ)` with classifying morphism `h` and a morphism `a : V ⟶ T`
carrying a chart datum `D` of `(a ≫ f, a^*ψ, a ≫ h)`, the chart datum's comparison
`ℳ̃_V ≅ (a ≫ h)^*ℳ̃` read along `a` is a morphism `a^*ℳ̃_T ⟶ a^*h^*ℳ̃`, `localHom`. This file
proves two compatibilities of these local morphisms: **restriction along a further `k : W ⟶ V`**
(`localHom_restrict`) and **transport along an equality of morphisms** (`localHom_congr`).

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.congr`: a chart datum
  transported along an isomorphism of the invertible modules carrying one twisting to another.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.conjMor`: `a ≫ X ≫ c⁻¹` for isomorphisms
  `a`, `c`, in one category.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.localHom`: the local comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr (congrIso)
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

private theorem restrict_alg {C : Type*} [Category C] {X0 X1 X2 X3 X4 X5 Y Y' Z : C}
    (cKi : X0 ⟶ X1) (kL : X1 ⟶ X4) (kA : X1 ⟶ X2) (kD : X2 ⟶ X3) (kC : X3 ⟶ X4)
    (cKh : X4 ⟶ X5) (A' : X2 ⟶ Y) (Cg : Y ⟶ Y') (Dp : Y ⟶ Z) (D'' : Y' ⟶ Z) (Pinv : Z ⟶ X3)
    (Aka : X0 ⟶ Y') (Ckahom : X5 ⟶ Z) (Ckainv : Z ⟶ X5)
    (hF : kL = kA ≫ kD ≫ kC) (hi : cKi ≫ kA ≫ A' ≫ Cg = Aka) (hii : kD = A' ≫ Dp ≫ Pinv)
    (hiii : Dp = Cg ≫ D'') (hiv : Pinv ≫ kC ≫ cKh ≫ Ckahom = 𝟙 Z)
    (hC : Ckahom ≫ Ckainv = 𝟙 X5) :
    cKi ≫ kL ≫ cKh = Aka ≫ D'' ≫ Ckainv := by
  subst hF hi hii hiii
  have e : Pinv ≫ kC ≫ cKh = Ckainv := by
    calc Pinv ≫ kC ≫ cKh = (Pinv ≫ kC ≫ cKh ≫ Ckahom) ≫ Ckainv := by
          simp only [Category.assoc, hC, Category.comp_id]
      _ = Ckainv := by rw [hiv, Category.id_comp]
  simp only [Category.assoc, e]

theorem solve_conj {C : Type*} [Category C] {P Q R S : C} (a : Q ≅ P) (m : Q ⟶ R)
    (c : R ≅ S) (X : P ⟶ S) (hX : X = a.inv ≫ m ≫ c.hom) : m = a.hom ≫ X ≫ c.inv := by
  subst hX
  simp

/-- **`a ≫ X ≫ c⁻¹`** for isomorphisms `a : P ≅ Q`, `c : S ≅ R` and a morphism `X : Q ⟶ R` of one
category. -/
def conjMor {C : Type*} [Category C] {P Q R S : C} (a : P ≅ Q) (X : Q ⟶ R) (c : S ≅ R) :
    P ⟶ S :=
  a.hom ≫ X ≫ c.inv

/-- `conjMor a X c` unfolds to `a.hom ≫ X ≫ c.inv`. -/
theorem conjMor_eq {C : Type*} [Category C] {P Q R S : C} (a : P ≅ Q) (X : Q ⟶ R)
    (c : S ≅ R) : conjMor a X c = a.hom ≫ X ≫ c.inv :=
  rfl

/-- `conjMor a b.hom c` is an isomorphism when `b` is an isomorphism. -/
theorem isIso_conjMor_iso {C : Type*} [Category C] {P Q R S : C} (a : P ≅ Q) (b : Q ≅ R)
    (c : S ≅ R) : IsIso (conjMor a b.hom c) := by
  rw [conjMor_eq]
  infer_instance

namespace ChartDatum

variable {s : Stacks.RelativeProj.Situation.{u}} {T : Scheme.{u}} {f : T ⟶ s.base} {d : ℕ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {ψ : Twisting f s.algebra (d : ℤ) L} {h : T ⟶ relativeProj s}

/-- **A chart datum transported along an isomorphism `e : L ≅ L'` carrying `ψ` to `ψ'`**: the
same chart, and the unit transported along `e`. -/
def congr (D : ChartDatum f ψ h) {L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
    (e : L ≅ L') (ψ' : Twisting f s.algebra (d : ℤ) L')
    (hψ : ∀ n : ℤ, ψ.app n ≫ (congrIso e n).hom = ψ'.app n) : ChartDatum f ψ' h where
  U := D.U
  c := D.c
  hf := D.hf
  g := D.g
  hg := D.hg
  hgf := D.hgf
  w := LaurentSections.congrUnit e D.w
  hCP := hCP_congr D.U D.c D.hf D.hg ψ D.w e ψ' hψ D.hCP D.hw D.hw'
  hw := LaurentSections.congrUnit_homogeneous e D.w D.hw
  hw' := LaurentSections.congrUnit_inv_homogeneous e D.w D.hw'
  fac := D.fac

variable (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] (hd : 0 < d)

/-- The comparison of a transported chart datum is the comparison of the datum, read through the
induced isomorphism of the modules of Tag 01O6. -/
theorem iso_congr (D : ChartDatum f ψ h)
    {L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
    (e : L ≅ L') (ψ' : Twisting f s.algebra (d : ℤ) L')
    (hψ : ∀ n : ℤ, ψ.app n ≫ (congrIso e n).hom = ψ'.app n) :
    (D.iso ℳ hd).hom =
      (associatedSheafCongrIso (ℳ.toGradedModule s.mul_comm) ψ ψ' e hψ).hom ≫
        ((D.congr e ψ' hψ).iso ℳ hd).hom := by
  have h1 : (chartIso ℳ D.U D.c f D.hf D.g D.hg D.hgf ψ D.w D.hCP D.hw D.hw' hd).hom =
      (associatedSheafCongrIso (ℳ.toGradedModule s.mul_comm) ψ ψ' e hψ).hom ≫
        (chartIso ℳ (D.congr e ψ' hψ).U (D.congr e ψ' hψ).c f (D.congr e ψ' hψ).hf
          (D.congr e ψ' hψ).g (D.congr e ψ' hψ).hg (D.congr e ψ' hψ).hgf ψ'
          (D.congr e ψ' hψ).w (D.congr e ψ' hψ).hCP (D.congr e ψ' hψ).hw
          (D.congr e ψ' hψ).hw' hd).hom :=
    chartIso_congr ℳ D.U D.c f D.hf D.g D.hg D.hgf ψ D.w D.hCP D.hw D.hw' hd e ψ' hψ
  have h2 : (moduleSheafPullbackChartIso ℳ D.U D.g D.fac).inv =
      (moduleSheafPullbackChartIso ℳ (D.congr e ψ' hψ).U (D.congr e ψ' hψ).g
        (D.congr e ψ' hψ).fac).inv := rfl
  refine (Iso.trans_hom _ _).trans ?_
  refine (congrArg₂ (· ≫ ·) h1 ((Iso.symm_hom _).trans h2)).trans ?_
  exact Category.assoc _ _ _

end ChartDatum

section Local

variable {s : Stacks.RelativeProj.Situation.{u}} {T : Scheme.{u}} {f : T ⟶ s.base} {d : ℕ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {ψ : Twisting f s.algebra (d : ℤ) L} {h : T ⟶ relativeProj s}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] (hd : 0 < d)

/-- **The local comparison** attached to a chart datum along `a : V ⟶ T`: the comparison
`ℳ̃_V ≅ (a ≫ h)^*ℳ̃` of the datum, read as a morphism `a^*ℳ̃_T ⟶ a^*h^*ℳ̃` through
`a^*ℳ̃_T ≅ ℳ̃_V` and the composition law for pullback. -/
def localHom {V : Scheme.{u}} (a : V ⟶ T) (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) :
    (Scheme.Modules.pullback a).obj (src ℳ f ψ) ⟶
      (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback h).obj (moduleSheaf ℳ)) :=
  conjMor (C := V.Modules) (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ)
    (D.iso ℳ hd).hom ((Scheme.Modules.pullbackComp a h).app (moduleSheaf ℳ))

/-- The local comparison, as `conjMor`. -/
theorem localHom_eq_conjMor {V : Scheme.{u}} (a : V ⟶ T)
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) :
    localHom ℳ hd a D =
      conjMor (C := V.Modules)
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ)
        (D.iso ℳ hd).hom ((Scheme.Modules.pullbackComp a h).app (moduleSheaf ℳ)) :=
  rfl

/-- **The local comparison, unfolded.** -/
theorem localHom_eq {V : Scheme.{u}} (a : V ⟶ T) (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) :
    localHom ℳ hd a D =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ).hom ≫
        (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp a h).inv.app (moduleSheaf ℳ) :=
  (localHom_eq_conjMor ℳ hd a D).trans (conjMor_eq (C := V.Modules) _ _ _)

/-- Chart data with the same comparison give the same local comparison. -/
theorem localHom_eq_of_iso_hom_eq {V : Scheme.{u}} (a : V ⟶ T)
    (D D' : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h))
    (e : (D.iso ℳ hd).hom = (D'.iso ℳ hd).hom) : localHom ℳ hd a D = localHom ℳ hd a D' :=
  (localHom_eq_conjMor ℳ hd a D).trans
    ((congrArg (fun x => conjMor (C := V.Modules)
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ) x
        ((Scheme.Modules.pullbackComp a h).app (moduleSheaf ℳ))) e).trans
      (localHom_eq_conjMor ℳ hd a D').symm)

/-- The local comparison is an isomorphism. -/
instance isIso_localHom {V : Scheme.{u}} (a : V ⟶ T)
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) : IsIso (localHom ℳ hd a D) :=
  isIso_conjMor_iso (C := V.Modules)
    (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ) (D.iso ℳ hd)
    ((Scheme.Modules.pullbackComp a h).app (moduleSheaf ℳ))

/-- **The local comparison along an equal morphism** is the transport of the local comparison. -/
theorem localHom_congr {V : Scheme.{u}} (a a' : V ⟶ T) (e : a = a')
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) :
    (Scheme.Modules.pullbackCongr e).inv.app _ ≫ localHom ℳ hd a D ≫
        (Scheme.Modules.pullbackCongr e).hom.app _ =
      localHom ℳ hd a' (e ▸ D) := by
  subst e
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id]
  exact Category.id_comp _

/-- The associativity coherence of the composition law for pullback, at one module. -/
theorem pullbackComp_assoc_app {V W : Scheme.{u}} {X : Scheme.{u}} (k : W ⟶ V) (a : V ⟶ T)
    (h' : T ⟶ X) (N : X.Modules) :
    (Scheme.Modules.pullbackComp k (a ≫ h')).inv.app N ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullbackComp a h').inv.app N) ≫
          (Scheme.Modules.pullbackComp k a).hom.app ((Scheme.Modules.pullback h').obj N) ≫
            (Scheme.Modules.pullbackComp (k ≫ a) h').hom.app N = 𝟙 _ := by
  have hassoc := congrArg (fun φ => φ.app N) (Scheme.Modules.pseudofunctor_associativity k a h')
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at hassoc
  exact hassoc.trans rfl

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The comparison `ℳ̃` of a composite pullback, `(k ≫ a)^*ℳ̃_T ≅ ℳ̃_W`, through `a`. -/
theorem associatedSheafPullbackIso_comp_pullbackComp {V : Scheme.{u}} (a : V ⟶ T)
    {W : Scheme.{u}} (k : W ⟶ V) :
    (Scheme.Modules.pullbackComp k a).inv.app (src ℳ f ψ) ≫
        (Scheme.Modules.pullback k).map
          (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ).hom ≫
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ)
          ((pullbackFunctor (ringedSpaceHom a)).obj L) k (ψ.pullback a)).hom ≫
        (associatedSheafCongrIso (ℳ.toGradedModule s.mul_comm) ((ψ.pullback a).pullback k)
          (ψ.pullback (k ≫ a)) (LaurentComposition.compCmp k a L)
          (fun n => ψ.pullbackApp_comp a k n)).hom =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L (k ≫ a) ψ).hom :=
  (congrArg (· ≫ _) (compComparison_eq_pullbackComp_inv k a (src ℳ f ψ))).symm.trans
    (associatedSheafPullbackIso_comp (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a k ψ)

/-- The pullback of the comparison of a chart datum along `k`, through the comparison of the
pulled-back datum. -/
private theorem pullback_map_iso_hom' {V : Scheme.{u}} {a : V ⟶ T}
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) {W : Scheme.{u}} (k : W ⟶ V) :
    (Scheme.Modules.pullback k).map (D.iso ℳ hd).hom =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ)
          ((pullbackFunctor (ringedSpaceHom a)).obj L) k (ψ.pullback a)).hom ≫
        ((D.pullback k).iso ℳ hd).hom ≫
          (Scheme.Modules.pullbackComp k (a ≫ h)).inv.app (moduleSheaf ℳ) :=
  solve_conj (C := W.Modules) _ _ ((Scheme.Modules.pullbackComp k (a ≫ h)).app (moduleSheaf ℳ)) _
    (ChartDatum.iso_pullback ℳ D hd k)

/-- The comparison of the transported pulled-back datum, read at the composite `k ≫ a`. -/
private theorem iso_congr_reassoc {V : Scheme.{u}} {a : V ⟶ T}
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) {W : Scheme.{u}} (k : W ⟶ V) :
    (ChartDatum.iso ℳ (f := (k ≫ a) ≫ f) (ψ := ψ.pullback (k ≫ a)) (h := (k ≫ a) ≫ h)
      ((D.pullback k).congr (LaurentComposition.compCmp k a L) (ψ.pullback (k ≫ a))
        (fun n => ψ.pullbackApp_comp a k n)) hd).hom =
      (((D.pullback k).congr (LaurentComposition.compCmp k a L) (ψ.pullback (k ≫ a))
        (fun n => ψ.pullbackApp_comp a k n)).iso ℳ hd).hom :=
  rfl

/-- **The local comparison restricted along `k : W ⟶ V`** is the local comparison along `k ≫ a`
of the pulled-back chart datum transported along `k^*a^*L ≅ (k ≫ a)^*L`. -/
theorem localHom_restrict {V : Scheme.{u}} (a : V ⟶ T)
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) {W : Scheme.{u}} (k : W ⟶ V) :
    (Scheme.Modules.pullbackComp k a).inv.app _ ≫
        (Scheme.Modules.pullback k).map (localHom ℳ hd a D) ≫
          (Scheme.Modules.pullbackComp k a).hom.app _ =
      localHom ℳ hd (k ≫ a) ((D.pullback k).congr (LaurentComposition.compCmp k a L)
        (ψ.pullback (k ≫ a)) (fun n => ψ.pullbackApp_comp a k n)) := by
  have hF : (Scheme.Modules.pullback k).map (localHom ℳ hd a D) =
      (Scheme.Modules.pullback k).map
          (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ).hom ≫
        (Scheme.Modules.pullback k).map (D.iso ℳ hd).hom ≫
          (Scheme.Modules.pullback k).map
            ((Scheme.Modules.pullbackComp a h).inv.app (moduleSheaf ℳ)) :=
    (congrArg (Scheme.Modules.pullback k).map (localHom_eq ℳ hd a D)).trans
      ((Functor.map_comp _ _ _).trans (congrArg _ (Functor.map_comp _ _ _)))
  have hi := associatedSheafPullbackIso_comp_pullbackComp (f := f) (L := L) (ψ := ψ) ℳ a k
  have hii := pullback_map_iso_hom' ℳ hd D k
  have hiii := (ChartDatum.iso_congr ℳ hd (D.pullback k) (LaurentComposition.compCmp k a L)
    (ψ.pullback (k ≫ a)) (fun n => ψ.pullbackApp_comp a k n)).trans
      (congrArg (_ ≫ ·) (iso_congr_reassoc ℳ hd D k).symm)
  have hiv := pullbackComp_assoc_app k a h (moduleSheaf ℳ)
  refine Eq.trans ?_ (localHom_eq ℳ hd (k ≫ a) _).symm
  exact restrict_alg (C := W.Modules) _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF hi hii hiii hiv
    (Iso.hom_inv_id_app _ _)

end Local

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
