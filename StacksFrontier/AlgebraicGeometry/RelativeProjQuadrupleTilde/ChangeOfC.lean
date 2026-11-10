module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Datum
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentGlue

/-!
# The comparison on a chart does not depend on the section `c`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

section Coherence

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Changing the coordinate of the twisting factor by a scalar `s` is changing the comparison of
the module factor by `s`. -/
theorem tensor_scale {X Lm G : C} (β β' : X ⟶ G) (t : 𝟙_ C ⟶ Lm) (co co' : Lm ⟶ 𝟙_ C)
    (sc : 𝟙_ C ⟶ 𝟙_ C) (hct : co ≫ t = 𝟙 _) (hts : t ≫ co' = sc)
    (hβ : β = β' ≫ (ρ_ G).inv ≫ (G ◁ sc) ≫ (ρ_ G).hom) :
    (β ⊗ₘ co) ≫ (ρ_ G).hom = (β' ⊗ₘ co') ≫ (ρ_ G).hom := by
  have hco : co' = co ≫ sc := by rw [← hts, ← Category.assoc, hct, Category.id_comp]
  rw [hco, hβ, tensorHom_def', tensorHom_def', Category.assoc, Category.assoc,
    rightUnitor_naturality, rightUnitor_naturality, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  congr 1
  rw [← rightUnitor_naturality_assoc, Iso.hom_inv_id_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]

end Coherence

section Fibre

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  (U : s.base.affineOpens) {d : ℕ} (c c' : s.sectionPieces U.1 d)

/-- The overlap `D₊(c) ∩ D₊(c')`. -/
abbrev ovl : (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).Opens :=
  Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) ⊓
    Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c')

/-- The fraction `c' / c` of degree zero. -/
abbrev ratio : HomogeneousLocalization.Away (s.sectionRingGrading U.1) (cHom U.1 c) :=
  HomogeneousLocalization.Away.mk (s.sectionRingGrading U.1) (cHom_mem U.1 c) 1 (cHom U.1 c')
    (by simpa using cHom_mem U.1 c')

/-- The fraction `c'^k / c^k` of degree zero. -/
abbrev ratioPow (k : ℕ) : HomogeneousLocalization.Away (s.sectionRingGrading U.1) (cHom U.1 c) :=
  HomogeneousLocalization.Away.mk (s.sectionRingGrading U.1) (cHom_mem U.1 c) k (cHom U.1 c' ^ k)
    (SetLike.pow_mem_graded k (cHom_mem U.1 c'))

/-- The fraction `c'^k / c^k` is the `k`-th power of `c' / c`. -/
theorem ratioPow_eq (k : ℕ) : ratioPow U c c' k = ratio U c c' ^ k := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_pow, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow]
  congr 1
  exact Subtype.ext (by simp)

/-- **On the overlap, `x / c^k = (c' / c)^k · x / c'^k`**, in the fibre at a point. -/
theorem fibre_pos (k : ℕ) (x : sectionModulePieces ℳ U.1 ((k : ℤ) * d))
    (p : ProjectiveSpectrum (s.sectionRingGrading U.1))
    (hp : p ∈ ProjectiveSpectrum.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
    (hp' : p ∈ ProjectiveSpectrum.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c')) :
    moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1) (cHom U.1 c) ⟨p, hp⟩
        (fracElt ℳ U.1 c k x).1 =
      HomogeneousLocalization.val
          (HomogeneousLocalization.mapId _ (Q := p.asHomogeneousIdeal.toIdeal.primeCompl)
            (Submonoid.powers_le.mpr hp) (ratioPow U c c' k)) •
        moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1) (cHom U.1 c') ⟨p, hp'⟩
          (fracElt ℳ U.1 c' k x).1 := by
  have e1 := fracElt_val_eq ℳ U.1 c k x k 0 (by simp)
  have e2 := fracElt_val_eq ℳ U.1 c' k x k 0 (by simp)
  refine (congrArg (moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1)
    (cHom U.1 c) ⟨p, hp⟩) e1).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => HomogeneousLocalization.val
          (HomogeneousLocalization.mapId _ (Q := p.asHomogeneousIdeal.toIdeal.primeCompl)
            (Submonoid.powers_le.mpr hp) (ratioPow U c c' k)) •
        moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1) (cHom U.1 c') ⟨p, hp'⟩
          z) e2).symm
  rw [moduleToFiber_mk, moduleToFiber_mk]
  have hv : HomogeneousLocalization.val (HomogeneousLocalization.mapId _
      (Q := p.asHomogeneousIdeal.toIdeal.primeCompl) (Submonoid.powers_le.mpr hp)
        (ratioPow U c c' k)) =
      Localization.mk (cHom U.1 c' ^ k) ⟨(cHom U.1 c) ^ k, (Submonoid.powers_le.mpr hp) ⟨k, rfl⟩⟩ :=
    rfl
  refine Eq.trans ?_ (congrArg (· • _) hv).symm
  refine Eq.trans ?_ (LocalizedModule.mk_smul_mk _ _ _ _).symm
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, pow_zero, smul_smul]

/-- **On the overlap, `c^k x = (c^k / c'^k) · c'^k x`**, in the fibre at a point. -/
theorem fibre_neg (k : ℕ) (x : sectionModulePieces ℳ U.1 (-(k : ℤ) * d))
    (p : ProjectiveSpectrum (s.sectionRingGrading U.1))
    (hp : p ∈ ProjectiveSpectrum.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
    (hp' : p ∈ ProjectiveSpectrum.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c')) :
    moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1) (cHom U.1 c) ⟨p, hp⟩
        (fracElt ℳ U.1 c (-(k : ℤ)) x).1 =
      HomogeneousLocalization.val
          (HomogeneousLocalization.mapId _ (Q := p.asHomogeneousIdeal.toIdeal.primeCompl)
            (Submonoid.powers_le.mpr hp') (ratioPow U c' c k)) •
        moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1) (cHom U.1 c') ⟨p, hp'⟩
          (fracElt ℳ U.1 c' (-(k : ℤ)) x).1 := by
  have e1 := fracElt_val_eq ℳ U.1 c (-(k : ℤ)) x 0 k (by simp)
  have e2 := fracElt_val_eq ℳ U.1 c' (-(k : ℤ)) x 0 k (by simp)
  refine (congrArg (moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1)
    (cHom U.1 c) ⟨p, hp⟩) e1).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => HomogeneousLocalization.val
          (HomogeneousLocalization.mapId _ (Q := p.asHomogeneousIdeal.toIdeal.primeCompl)
            (Submonoid.powers_le.mpr hp') (ratioPow U c' c k)) •
        moduleToFiber (M := sectionModule ℳ U.1) (s.sectionRingGrading U.1) (cHom U.1 c') ⟨p, hp'⟩
          z) e2).symm
  rw [moduleToFiber_mk, moduleToFiber_mk]
  have hv : HomogeneousLocalization.val (HomogeneousLocalization.mapId _
      (Q := p.asHomogeneousIdeal.toIdeal.primeCompl) (Submonoid.powers_le.mpr hp')
        (ratioPow U c' c k)) =
      Localization.mk (cHom U.1 c ^ k)
        ⟨(cHom U.1 c') ^ k, (Submonoid.powers_le.mpr hp') ⟨k, rfl⟩⟩ :=
    rfl
  refine Eq.trans ?_ (congrArg (· • _) hv).symm
  refine Eq.trans ?_ (LocalizedModule.mk_smul_mk _ _ _ _).symm
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, pow_zero, smul_smul]
  congr 1
  ring

/-- **On the overlap, `x / c^k = (c'^k / c^k) · x / c'^k`**, as sections of `ℳ̃(U)`. -/
theorem fracChart_ovl (k : ℕ) (x : sectionModulePieces ℳ U.1 ((k : ℤ) * d)) :
    (moduleChart ℳ U).val.map (homOfLE (inf_le_left : ovl U c c' ≤ _)).op
        (toChart ℳ U c (fracElt ℳ U.1 c k x)) =
      (show (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).ringCatSheaf.obj.obj
          (op (ovl U c c')) from
        (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).presheaf.map
          (homOfLE (inf_le_left : ovl U c c' ≤ _)).op
          (Proj.awayToSection _ _ (ratioPow U c c' k))) •
        (show (moduleChart ℳ U).val.obj (op (ovl U c c')) from
          (moduleChart ℳ U).val.map (homOfLE (inf_le_right : ovl U c c' ≤ _)).op
            (toChart ℳ U c' (fracElt ℳ U.1 c' k x))) :=
  Subtype.ext <| funext fun p => fibre_pos ℳ U c c' k x p.1 p.2.1 p.2.2

/-- **On the overlap, `c^k x = (c^k / c'^k) · c'^k x`**, as sections of `ℳ̃(U)`. -/
theorem fracChart_ovl_neg (k : ℕ) (x : sectionModulePieces ℳ U.1 (-(k : ℤ) * d)) :
    (moduleChart ℳ U).val.map (homOfLE (inf_le_left : ovl U c c' ≤ _)).op
        (toChart ℳ U c (fracElt ℳ U.1 c (-(k : ℤ)) x)) =
      (show (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).ringCatSheaf.obj.obj
          (op (ovl U c c')) from
        (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).presheaf.map
          (homOfLE (inf_le_right : ovl U c c' ≤ _)).op
          (Proj.awayToSection _ _ (ratioPow U c' c k))) •
        (show (moduleChart ℳ U).val.obj (op (ovl U c c')) from
          (moduleChart ℳ U).val.map (homOfLE (inf_le_right : ovl U c c' ≤ _)).op
            (toChart ℳ U c' (fracElt ℳ U.1 c' (-(k : ℤ)) x))) :=
  Subtype.ext <| funext fun p => fibre_neg ℳ U c c' k x p.1 p.2.1 p.2.2

end Fibre

section Pull

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  (U : s.base.affineOpens) {d : ℕ} (c c' : s.sectionPieces U.1 d)
  {T : Scheme.{u}} (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
  (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
  (hg' : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c'))

include hg hg' in
/-- If `g` maps `T` into `D₊(c)` and into `D₊(c')`, then it maps `T` into their overlap. -/
theorem le_ovl : (⊤ : T.Opens) ≤ g ⁻¹ᵁ ovl U c c' := fun _ ht => ⟨hg ht, hg' ht⟩

/-- If `x / c^n` equals `r · x / c'^n` on the overlap, the same holds after pulling back by `g`,
with `r` replaced by `g^♯ r`. -/
private theorem fracPull_change_of_ovl (n : ℤ) (x : sectionModulePieces ℳ U.1 (n * d))
    {V : (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).Opens} (j : ovl U c c' ≤ V)
    (hj : (⊤ : T.Opens) ≤ g ⁻¹ᵁ V)
    (r : (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).presheaf.obj (op V))
    (h : (moduleChart ℳ U).val.map (homOfLE (inf_le_left : ovl U c c' ≤ _)).op
        (toChart ℳ U c (fracElt ℳ U.1 c n x)) =
      (show (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).ringCatSheaf.obj.obj
          (op (ovl U c c')) from
        (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).presheaf.map (homOfLE j).op r) •
        (show (moduleChart ℳ U).val.obj (op (ovl U c c')) from
          (moduleChart ℳ U).val.map (homOfLE (inf_le_right : ovl U c c' ≤ _)).op
            (toChart ℳ U c' (fracElt ℳ U.1 c' n x)))) :
    fracPull ℳ U c g hg n x =
      (show T.ringCatSheaf.obj.obj (op ⊤) from g.appLE V ⊤ hj r) • fracPull ℳ U c' g hg' n x := by
  have _ := ‹∀ n : ℤ, (ℳ.piece n).IsQuasicoherent›
  have hV := le_ovl U c c' g hg hg'
  have e1 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_target_le g (moduleChart ℳ U)
    (inf_le_left : ovl U c c' ≤ _) ⊤ hg hV (toChart ℳ U c (fracElt ℳ U.1 c n x))
  have e2 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_target_le g (moduleChart ℳ U)
    (inf_le_right : ovl U c c' ≤ _) ⊤ hg' hV (toChart ℳ U c' (fracElt ℳ U.1 c' n x))
  have e3 := congrArg (Scheme.Modules.pullbackSection g (moduleChart ℳ U) (ovl U c c') ⊤ hV) h
  have e4 := AffineOpenHomRecovery.pullbackSection_smul g (moduleChart ℳ U) (ovl U c c') ⊤ hV
    ((AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).presheaf.map (homOfLE j).op r)
    ((moduleChart ℳ U).val.map (homOfLE (inf_le_right : ovl U c c' ≤ _)).op
      (toChart ℳ U c' (fracElt ℳ U.1 c' n x)))
  have e5 : g.appLE (ovl U c c') ⊤ hV
      ((AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).presheaf.map (homOfLE j).op r) =
      g.appLE V ⊤ hj r :=
    congrArg (fun φ => φ r) (Scheme.Hom.map_appLE g hV (homOfLE j).op)
  refine (fracPull_apply ℳ U c g hg n x).trans ?_
  refine (congrArg (Scheme.Modules.pullbackSection g (moduleChart ℳ U) _ ⊤ hg)
    (fracChart_eq ℳ U c n x)).trans ?_
  refine e1.symm.trans (e3.trans (e4.trans ?_))
  refine Eq.trans ?_ (congrArg (fun z => (show T.ringCatSheaf.obj.obj (op ⊤) from
        g.appLE V ⊤ hj r) • z)
    ((fracPull_apply ℳ U c' g hg' n x).trans (congrArg
      (Scheme.Modules.pullbackSection g (moduleChart ℳ U) _ ⊤ hg') (fracChart_eq ℳ U c' n x)))).symm
  exact congrArg₂ (· • ·) e5 e2

/-- **`g^*(x / c^k) = g^♯(c'^k / c^k) · g^*(x / c'^k)`.** -/
theorem fracPull_change_pos (k : ℕ) (x : sectionModulePieces ℳ U.1 ((k : ℤ) * d)) :
    fracPull ℳ U c g hg k x =
      (show T.ringCatSheaf.obj.obj (op ⊤) from
        g.appLE _ ⊤ hg (Proj.awayToSection _ _ (ratioPow U c c' k))) •
        fracPull ℳ U c' g hg' k x :=
  fracPull_change_of_ovl ℳ U c c' g hg hg' k x inf_le_left hg _ (fracChart_ovl ℳ U c c' k x)

/-- **`g^*(c^k x) = g^♯(c^k / c'^k) · g^*(c'^k x)`.** -/
theorem fracPull_change_neg (k : ℕ) (x : sectionModulePieces ℳ U.1 (-(k : ℤ) * d)) :
    fracPull ℳ U c g hg (-(k : ℤ)) x =
      (show T.ringCatSheaf.obj.obj (op ⊤) from
        g.appLE _ ⊤ hg' (Proj.awayToSection _ _ (ratioPow U c' c k))) •
        fracPull ℳ U c' g hg' (-(k : ℤ)) x :=
  fracPull_change_of_ovl ℳ U c c' g hg hg' (-(k : ℤ)) x inf_le_right hg' _
    (fracChart_ovl_neg ℳ U c c' k x)

end Pull

section Laurent

open LaurentSections

variable {T : Scheme.{u}} {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The functions on `T`, as the degree-zero part of the ring of Laurent sections. -/
def degZero : (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) →+* Ring L (op ⊤) where
  toFun r := DirectSum.of ((laurent L).sectionsPiece (op ⊤)) 0 (r • (laurent L).one.eval (op ⊤))
  map_one' := by rw [one_smul, one_eq]
  map_mul' r r' := by
    rw [mul_smul, smul_of (op ⊤) r 0 (r' • (laurent L).one.eval (op ⊤))]
  map_zero' := by rw [zero_smul, map_zero]
  map_add' r r' := by rw [add_smul, map_add]

/-- Multiplying a homogeneous Laurent section by `degZero r` is the scalar action of `r`. -/
theorem degZero_mul_of (r : (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤)) (i : ℤ)
    (y : (laurent L).sectionsPiece (op ⊤) i) :
    degZero r * DirectSum.of ((laurent L).sectionsPiece (op ⊤)) i y =
      DirectSum.of ((laurent L).sectionsPiece (op ⊤)) i (r • y) :=
  (smul_of (op ⊤) r i y).symm

variable (w w' : (Ring L (op ⊤))ˣ)
  (hw : ∃ σ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hw' : ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ)
  (hv : ∃ σ, (w' : Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hv' : ∃ τ, ((w'⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ)
  (u : ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ)

variable (L) in
/-- The inclusion `degZero` of the functions on `T` into the Laurent sections is injective. -/
theorem degZero_injective : Function.Injective (degZero (L := L)) := by
  intro r r' h
  have h' := DirectSum.of_injective (β := (laurent L).sectionsPiece (op ⊤)) 0 h
  have e1 : r • (laurent L).one.eval (op ⊤) = r := smul_one_eval (L := L) (op ⊤) r
  have e2 : r' • (laurent L).one.eval (op ⊤) = r' := smul_one_eval (L := L) (op ⊤) r'
  exact e1.symm.trans (h'.trans e2)

include hw hw' hv hv' in
/-- If `w' = r · w` in degree one, then `w' = degZero r * w` as Laurent sections. -/
theorem val_eq_degZero_mul (r : (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))
    (h : pw w' 1 = r • pw w 1) : (w' : Ring L (op ⊤)) = degZero r * (w : Ring L (op ⊤)) := by
  have e1 := of_pw w hw hw' 1
  have e2 := of_pw w' hv hv' 1
  rw [zpow_one] at e1 e2
  rw [← e1, ← e2, h]
  exact (degZero_mul_of _ 1 _).symm

include hw hw' hv hv' in
/-- **If `w' = r · w` and `w = r' · w'` in degree one, then `r r' = 1`.** -/
theorem mul_eq_one_of_pw (r r' : (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))
    (h : pw w' 1 = r • pw w 1) (h' : pw w 1 = r' • pw w' 1) : r' * r = 1 := by
  have e := val_eq_degZero_mul w w' hw hw' hv hv' r h
  have e' := val_eq_degZero_mul w' w hv hv' hw hw' r' h'
  apply degZero_injective (L := L)
  have h2 : degZero (L := L) (r' * r) * (w : Ring L (op ⊤)) = 1 * w := by
    rw [map_mul, mul_assoc, ← e, ← e', one_mul]
  have h3 := congrArg (· * ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤))) h2
  simp only [mul_assoc, Units.mul_inv, _root_.mul_one] at h3
  rw [h3, map_one]

include hw hw' hv hv' in
/-- **If `w' = u · w` in degree one, then `w'^n = u^n · w^n` in every degree.** -/
theorem pw_eq_smul (h : pw w' 1 = (u : (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤)) •
    pw w 1) (n : ℤ) :
    pw w' n = ((u ^ n : ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ) :
      (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤)) • pw w n := by
  have h1 : w' = Units.map degZero.toMonoidHom u * w := by
    apply Units.ext
    rw [Units.val_mul, Units.coe_map]
    exact val_eq_degZero_mul w w' hw hw' hv hv' _ h
  apply DirectSum.of_injective (β := (laurent L).sectionsPiece (op ⊤)) n
  rw [of_pw w' hv hv' n, ← degZero_mul_of, of_pw w hw hw' n, h1, mul_zpow, Units.val_mul,
    ← map_zpow, Units.coe_map]
  rfl

/-- **Multiplication by a function on `T`**, as an endomorphism of a sheaf of modules. -/
def smulMor (X : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    (r : T.ringCatSheaf.obj.obj (op ⊤)) : X ⟶ X :=
  (ρ_ X).inv ≫ (X ◁ secHom (𝟙_ _)
    (show (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))).val.obj (op ⊤) from r)) ≫
      (ρ_ X).hom

omit [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] in
/-- On global sections, `smulMor X r` is the scalar action of `r`. -/
theorem smulMor_app_top (X : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    (r : T.ringCatSheaf.obj.obj (op ⊤)) (y : X.val.obj (op ⊤)) :
    (smulMor X r).val.app (op ⊤) y =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from r) • y := by
  change (ρ_ X).hom.val.app (op ⊤) ((X ◁ secHom (𝟙_ _) (show (𝟙_ (SheafOfModules.{u}
    (structureRingSheaf T.toRingedSpace))).val.obj (op ⊤) from r)).val.app (op ⊤)
    ((ρ_ X).inv.val.app (op ⊤) y)) = _
  rw [rightUnitor_inv_app, whiskerLeft_tmul]
  have etop : (secHom (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)))
      (show (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))).val.obj (op ⊤)
        from r)).val.app (op ⊤) (oneSec T.toRingedSpace (op ⊤)) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from r) := by
    refine (secHom_app _ _ _ _).trans ((one_smul _ _).trans ?_)
    have h1 : topRes T (op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    change (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))).val.map
      (topRes T (op ⊤)) r = r
    rw [h1, PresheafOfModules.map_id]
    rfl
  rw [etop]
  exact rightUnitor_hom_tmul (op ⊤) y _

include hw hw' in
/-- **The trivialization by `w` followed by the coordinate of `w'`** is multiplication by `u^n`,
when `w'^n = u^n · w^n`. -/
theorem triv_coord_scale (n : ℤ) (r : T.ringCatSheaf.obj.obj (op ⊤))
    (hpw : pw w' n = (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from r) • pw w n) :
    triv w n ≫ coord w' n = secHom (𝟙_ _) (show (𝟙_ (SheafOfModules.{u}
      (structureRingSheaf T.toRingedSpace))).val.obj (op ⊤) from r) := by
  apply (SheafOfModules.unitHomEquiv _).injective
  ext V
  change (coord w' n).val.app V ((triv w n).val.app V (oneSec T.toRingedSpace V)) =
    (secHom (𝟙_ _) (show (𝟙_ (SheafOfModules.{u}
      (structureRingSheaf T.toRingedSpace))).val.obj (op ⊤) from r)).val.app V
        (oneSec T.toRingedSpace V)
  have e1 : (triv w n).val.app V (oneSec T.toRingedSpace V) =
      ((laurent L).piece (-n)).val.restrictₛₗ (topRes T V) (pw w (-n)) :=
    (triv_app w n V 1).trans (one_smul _ _)
  rw [e1, coord_app]
  refine Eq.trans ?_ ((secHom_app _ _ V 1).trans (one_smul _ _)).symm
  apply DirectSum.of_injective (β := (laurent L).sectionsPiece V) (0 : ℤ)
  rw [of_eqToHom (add_neg_cancel n), ← of_mul_of, hpw]
  have e2 : ((laurent L).piece n).val.restrictₛₗ (topRes T V)
        ((show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from r) • pw w n) =
      (structureRingSheaf T.toRingedSpace).obj.map (topRes T V) r •
        ((laurent L).piece n).val.restrictₛₗ (topRes T V) (pw w n) :=
    ((laurent L).piece n).val.map_smul (topRes T V) r (pw w n)
  rw [e2, smul_of, mul_assoc, res_pw_mul_pw w hw hw' V _ n, _root_.mul_one]
  exact congrArg _ (smul_one_eval V _)

end Laurent

section Units

/-- For a unit `u`, the value of `u ^ (-k)` is `(u⁻¹) ^ k`. -/
theorem units_zpow_neg {R : Type*} [Monoid R] (u : Rˣ) (k : ℕ) :
    ((u ^ (-(k : ℤ)) : Rˣ) : R) = ((u⁻¹ : Rˣ) : R) ^ k := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]

end Units

section Change

open LaurentSections

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  (U : s.base.affineOpens) {d : ℕ} (c c' : s.sectionPieces U.1 d)
  {T : Scheme.{u}} (f : T ⟶ s.base) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U.1)
  (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
  (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
  (hg' : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c'))

/-- A section of `𝒜_d`, read in the degree `1 · d`. -/
def oneMul (a : s.sectionPieces U.1 d) : s.sectionPieces U.1 (1 * d) :=
  cast (congrArg (s.sectionPieces U.1) (one_mul d).symm) a

/-- The section `oneMul a`, placed in degree `1 * d`, is the element `cHom a` of the graded
ring. -/
theorem of_oneMul (a : s.sectionPieces U.1 d) :
    DirectSum.of (s.sectionPieces U.1) (1 * d) (oneMul U a) = cHom U.1 a :=
  DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (one_mul d) (cast_heq _ _))

/-- The fraction `c' / c` formed from `oneMul c'` in degree one is `ratio c c'`. -/
theorem algFrac_oneMul : algFrac U c 1 (oneMul U c') = ratio U c c' := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  change (Localization.mk (DirectSum.of (s.sectionPieces U.1) (1 * d) (oneMul U c'))
    (⟨(cHom U.1 c) ^ 1, 1, rfl⟩ : Submonoid.powers (cHom U.1 c)) : Localization.Away _) = _
  rw [of_oneMul]

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The function `kappaSec` of `oneMul c'` in degree one is `g^♯(c' / c)`. -/
theorem kappaSec_oneMul :
    kappaSec U c g hg 1 (oneMul U c') = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (ratio U c c')) :=
  congrArg (fun z => g.appLE _ ⊤ hg (Proj.awayToSection _ _ z)) (algFrac_oneMul U c c')

variable (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))
  (hgf' : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg' (Proj.awayToSection _ _ (baseFrac U c' r)))
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f s.algebra (d : ℤ) L) (w w' : (Ring L (op ⊤))ˣ)
  (hCP : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
    ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        pw w i)
  (hCP' : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
    ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c' g hg' i a) •
        pw w' i)
  (hw : ∃ σ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hw' : ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ)
  (hv : ∃ σ, (w' : Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hv' : ∃ τ, ((w'⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ)
  (hd : 0 < d)

include hCP hCP' in
omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **In degree one, `w' = g^♯(c' / c) · w`.** -/
theorem pw_one_change :
    pw w' 1 = (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from
      kappaSec U c g hg 1 (oneMul U c')) • pw w 1 := by
  have h := (hCP' 1 (oneMul U c')).symm.trans (hCP 1 (oneMul U c'))
  have h1 : kappaSec U c' g hg' 1 (oneMul U c') = 1 :=
    kappaSec_pow U c' g hg' 1 (oneMul U c') (by rw [of_oneMul, pow_one])
  rw [h1] at h
  exact (one_smul _ _).symm.trans h

/-- The unit `g^♯(c' / c)` of the functions on `T`. -/
def ratioUnit : ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ where
  val := kappaSec U c g hg 1 (oneMul U c')
  inv := kappaSec U c' g hg' 1 (oneMul U c)
  val_inv := mul_eq_one_of_pw w' w hv hv' hw hw' _ _
      (pw_one_change U c' c f hf g hg' hg ψ w' w hCP' hCP)
      (pw_one_change U c c' f hf g hg hg' ψ w w' hCP hCP')
  inv_val := mul_eq_one_of_pw w w' hw hw' hv hv' _ _
      (pw_one_change U c c' f hf g hg hg' ψ w w' hCP hCP')
      (pw_one_change U c' c f hf g hg' hg ψ w' w hCP' hCP)

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The value of `ratioUnit` is `g^♯(c' / c)`. -/
theorem ratioUnit_val :
    ((ratioUnit U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv hv' :
      ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ) :
        (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤)) =
      g.appLE _ ⊤ hg (Proj.awayToSection _ _ (ratio U c c')) :=
  kappaSec_oneMul U c c' g hg

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The inverse of `ratioUnit` is `g^♯(c / c')`. -/
theorem ratioUnit_inv :
    (((ratioUnit U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv hv')⁻¹ :
      ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ) :
        (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤)) =
      g.appLE _ ⊤ hg' (Proj.awayToSection _ _ (ratio U c' c)) :=
  kappaSec_oneMul U c' c g hg'

/-- **`g^*(x / c^n) = u^n · g^*(x / c'^n)`** with `u = g^♯(c' / c)`, for every integer `n`. -/
theorem fracPull_unit (n : ℤ) (x : sectionModulePieces ℳ U.1 (n * d)) :
    fracPull ℳ U c g hg n x =
      (show T.ringCatSheaf.obj.obj (op ⊤) from
        (((ratioUnit U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv hv') ^ n :
          ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ) :
            (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))) •
        fracPull ℳ U c' g hg' n x := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · refine (fracPull_change_pos ℳ U c c' g hg hg' k x).trans (congrArg (· • _) ?_)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, ratioUnit_val, ratioPow_eq, map_pow, map_pow]
    rfl
  · refine (fracPull_change_neg ℳ U c c' g hg hg' k x).trans (congrArg (· • _) ?_)
    have e1 : g.appLE _ ⊤ hg' (Proj.awayToSection _ _ (ratioPow U c' c k)) =
        (g.appLE _ ⊤ hg' (Proj.awayToSection _ _ (ratio U c' c))) ^ k := by
      rw [ratioPow_eq, map_pow, map_pow]
    refine e1.trans ((congrArg (· ^ k) (ratioUnit_inv U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv
      hv').symm).trans (units_zpow_neg _ k).symm)

include hgf hgf' in
/-- **The comparisons `β` for `c` and `c'` differ by `u^n`.** -/
theorem betaS_change (n : ℤ) :
    betaS ℳ U c f hf g hg hgf n = betaS ℳ U c' f hf g hg' hgf' n ≫
      smulMor (tgt ℳ U g) (show T.ringCatSheaf.obj.obj (op ⊤) from
        (((ratioUnit U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv hv') ^ n :
          ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ) :
            (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))) := by
  refine AffineOpenHomRecovery.hom_ext f U.1 hf (ℳ.piece (n * d)) U.2 (tgt ℳ U g) fun x => ?_
  have e1 := beta_pullbackSection ℳ U c f hf g hg hgf n x
  have e2 := beta_pullbackSection ℳ U c' f hf g hg' hgf' n x
  have e3 := fracPull_unit ℳ U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv hv' n x
  have e4 := smulMor_app_top (tgt ℳ U g) (show T.ringCatSheaf.obj.obj (op ⊤) from
        (((ratioUnit U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv hv') ^ n :
          ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ) :
            (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))) (fracPull ℳ U c' g hg' n x)
  have h1 : (smulMor (tgt ℳ U g) (show T.ringCatSheaf.obj.obj (op ⊤) from
        (((ratioUnit U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv hv') ^ n :
          ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ) :
            (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤)))).val.app (op ⊤)
      ((beta ℳ U c' f hf g hg' hgf' n).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f (ℳ.piece (n * d)) U.1 ⊤ hf x)) =
      (smulMor (tgt ℳ U g) (show T.ringCatSheaf.obj.obj (op ⊤) from
        (((ratioUnit U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv hv') ^ n :
          ((structureRingSheaf T.toRingedSpace).obj.obj (op ⊤))ˣ) :
            (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤)))).val.app (op ⊤)
        (fracPull ℳ U c' g hg' n x) := congrArg _ e2
  exact e1.trans (e3.trans (e4.symm.trans h1.symm))

include hgf hgf' hCP hCP' hw hw' hv hv' in
/-- **The degreewise comparisons for `(c, w)` and `(c', w')` agree.** -/
theorem bmap_change (n : ℤ) :
    bmap ℳ U c f hf g hg hgf w n = bmap ℳ U c' f hf g hg' hgf' w' n :=
  tensor_scale _ _ (triv w n) (coord w n) (coord w' n) _ (coord_triv w hw hw' n)
    (triv_coord_scale w w' hw hw' n _ (pw_eq_smul w w' hw hw' hv hv'
      (ratioUnit U c c' f hf g hg hg' ψ w w' hCP hCP' hw hw' hv hv')
      (pw_one_change U c c' f hf g hg hg' ψ w w' hCP hCP') n))
    (betaS_change ℳ U c c' f hf g hg hg' hgf hgf' ψ w w' hCP hCP' hw hw' hv hv' n)

include hgf hgf' in
/-- **Property (1) on a chart does not depend on the section `c`.** -/
theorem chartIso_change :
    (chartIso ℳ U c f hf g hg hgf ψ w hCP hw hw' hd).hom =
      (chartIso ℳ U c' f hf g hg' hgf' ψ w' hCP' hv hv' hd).hom :=
  (Twisting.existsUnique_hom (ℳ.toGradedModule s.mul_comm) ψ (tgt ℳ U g)
    (bmap ℳ U c f hf g hg hgf w)
    (bmap_balanced ℳ U c f hf g hg hgf ψ w hCP hw hw' hd)).unique
    (pureTensor_chartIso_hom ℳ U c f hf g hg hgf ψ w hCP hw hw' hd)
    (fun n => (pureTensor_chartIso_hom ℳ U c' f hf g hg' hgf' ψ w' hCP' hv hv' hd n).trans
      (bmap_change ℳ U c c' f hf g hg hg' hgf hgf' ψ w w' hCP hCP' hw hw' hv hv' n).symm)

end Change



namespace ChartDatum

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] {T : Scheme.{u}} {f : T ⟶ s.base} {d : ℕ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {ψ : Twisting f s.algebra (d : ℤ) L} {h : T ⟶ relativeProj s} (hd : 0 < d)

/-- The morphism of `D.iso` is the comparison `chartIso` on the chart of `D`, followed by the
inverse of `moduleSheafPullbackChartIso`. -/
theorem iso_hom (D : ChartDatum f ψ h) :
    (D.iso ℳ hd).hom = (chartIso ℳ D.U D.c f D.hf D.g D.hg D.hgf ψ D.w D.hCP D.hw D.hw' hd).hom ≫
      (moduleSheafPullbackChartIso ℳ D.U D.g D.fac).inv :=
  Iso.trans_hom _ _

end ChartDatum

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
