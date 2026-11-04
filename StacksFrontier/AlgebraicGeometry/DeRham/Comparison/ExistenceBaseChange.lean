module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Existence
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsChartSquares
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Rule
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DiagonalConormal
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.PullbackIso

/-!
# The maps of Section 0FL7 are compatible with base change; Stacks Tag 0FLA

For a commutative square `b ≫ f = f' ≫ a` of locally quasi-finite syntomic morphisms which
induces an open immersion of `Y'` into `X' ×_X Y`, the glued maps
`AlgebraicGeometry.Scheme.Hom.chartGarelMaps` of `f` and of `f'` satisfy condition (0H9E) of
Section 0FL7, through the identification `b^*det(NL_{Y/X}) ≅ det(NL_{Y'/X'})`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.chartGarelMaps_isCompatible`: condition (0H9E).
* `AlgebraicGeometry.GarelRule.existsUnique_isNormalized_isMultiplicative_isCompatible`:
  Stacks Tag 0FLA, the existence and uniqueness of the rule of maps of Section 0FL7.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Syntomic f)

attribute [local instance] isQuasicoherent_relativeDifferentialForms

/-- A morphism of sheaves of modules on sections over an open, in the two spellings. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.app_eq_val_app {Z : Scheme.{u}}
    {M N : Z.Modules} (φ : M ⟶ N) (U : Z.Opens) (x : Γ(M, U)) :
    φ.app U x = φ.val.app (op U) x :=
  rfl

section BaseChange

variable {X' Y' : Scheme.{u}} {f' : Y' ⟶ X'} {a : X' ⟶ X} {b : Y' ⟶ Y} (w : b ≫ f = f' ≫ a)
  [IsOpenImmersion (pullback.lift b f' w)] (hf' : Syntomic f')

/-- **`detNLPullbackIso` on the pullback of a section over a chart**: over a chart `(U', V')` of
`f'` lying over a chart `(U, V)` of `f`, the pullback of a section of `det(NL_{Y/X})` over `V`,
carried by `detNLPullbackIso`, is the base change map of determinants. -/
theorem detNLSectionsEquiv_detNLPullbackIso_hom_pullbackSection (c : f.chartIndex.ι)
    (c' : f'.chartIndex.ι) (hU : c'.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1) (hV : c'.1.2.1 ≤ b ⁻¹ᵁ c.1.2.1)
    (hsq : f.IsGoodChartSquare w c.2 c'.2 hU hV) (l : Γ(f.detNL hf, c.1.2.1)) :
    f'.detNLSectionsEquiv hf' c' ((detNLPullbackIso w hf hf').hom.val.app (op c'.1.2.1)
        (Scheme.Modules.pullbackSection b (f.detNL hf) c.1.2.1 c'.1.2.1 hV l)) =
      detNLSquareMap w hf hf' c c' hU hV hsq (f.detNLSectionsEquiv hf c l) := by
  refine Eq.trans ?_ (detNLSectionsEquiv_homEquiv_detNLPullbackIso_hom w hf hf'
    (c' := c') (c := c) ⟨hU, hV, hsq⟩ l)
  refine congrArg (f'.detNLSectionsEquiv hf' c') ?_
  refine (PresheafOfModules.naturality_apply (detNLPullbackIso w hf hf').hom.val
    (homOfLE hV).op _).trans ?_
  rw [Adjunction.homEquiv_unit]
  rfl

open Stacks.PullbackTensorCoherence in
/-- **The base change arrow of Lemma 0H9G on a square of presented charts**, on the pullback of a
local pure tensor. -/
theorem chartTwistedEquiv_twistedPullbackFormsBaseChange_tmul
    (c : {c : f.chartIndex.ι // f.ChartPresented c})
    (c' : {c' : f'.chartIndex.ι // f'.ChartPresented c'}) (hU : c'.1.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1.1)
    (hV : c'.1.1.2.1 ≤ b ⁻¹ᵁ c.1.1.2.1) (hsq : f.IsGoodChartSquare w c.1.2 c'.1.2 hU hV) (p : ℕ)
    (s : Γ(f.pullbackForms p, c.1.1.2.1)) (l : Γ(f.detNL hf, c.1.1.2.1)) :
    letI := f.chartAlgebra c.1.2
    letI := f'.chartAlgebra c'.1.2
    letI := a.chartAlgebra hU
    letI := b.chartAlgebra hV
    letI := squareAlgebra f' a hU c'.1.2
    haveI := isScalarTower_squareAlgebra_left hU c'.1.2
    haveI := f.isScalarTower_squareAlgebra_right w c.1.2 hU hV c'.1.2
    f'.chartTwistedEquiv hf' c' p
        ((twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val.app
          (op c'.1.1.2.1) (Scheme.Modules.pullbackSection b (f.twistedPullbackForms (f.detNL hf) p)
            c.1.1.2.1 c'.1.1.2.1 hV (f.twistedPullbackFormsTmul (f.detNL hf) p c.1.1.2.1 s l))) =
      TensorProduct.map (ExteriorAlgebra.powMapₛₗ p
          (algebraMap Γ(Y, c.1.1.2.1) Γ(Y', c'.1.1.2.1))
          (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1.1) Γ(Y, c.1.1.2.1) Γ(X', c'.1.1.1.1)
            Γ(Y', c'.1.1.2.1)))
        (detNLSquareMap w hf hf' c.1 c'.1 hU hV hsq)
        (f.chartTwistedEquiv hf c p (f.twistedPullbackFormsTmul (f.detNL hf) p c.1.1.2.1 s l)) := by
  let := f.chartAlgebra c.1.2
  let := f'.chartAlgebra c'.1.2
  let := a.chartAlgebra hU
  let := b.chartAlgebra hV
  let := squareAlgebra f' a hU c'.1.2
  have := isScalarTower_squareAlgebra_left hU c'.1.2
  have := f.isScalarTower_squareAlgebra_right w c.1.2 hU hV c'.1.2
  refine (congrArg (f'.chartTwistedEquiv hf' c' p) (PresheafOfModules.naturality_apply
    (twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val
    (homOfLE hV).op _)).trans ?_
  refine (congrArg (fun z => f'.chartTwistedEquiv hf' c' p
    ((f'.twistedPullbackForms (f'.detNL hf') p).val.map (homOfLE hV).op z))
    (twistedPullbackFormsBaseChange_pullbackUnit_tmul (f.detNL hf) w
      (detNLPullbackIso w hf hf').hom p c.1.1.2.1 s l)).trans ?_
  refine (congrArg (f'.chartTwistedEquiv hf' c' p) (tmul_restrict (homOfLE hV).op _ _)).trans ?_
  refine (congrArg (fun z => f'.chartTwistedEquiv hf' c' p
    (f'.twistedPullbackFormsTmul (f'.detNL hf') p c'.1.1.2.1 z
      ((f'.detNL hf').val.map (homOfLE hV).op ((detNLPullbackIso w hf hf').hom.val.app
        (op (b ⁻¹ᵁ c.1.1.2.1)) (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom (f.detNL hf)
          (op c.1.1.2.1) l)))))
    (PresheafOfModules.naturality_apply (pullbackFormsBaseChange w p).val
      (homOfLE hV).op _).symm).trans ?_
  refine (congrArg (fun z => f'.chartTwistedEquiv hf' c' p
    (f'.twistedPullbackFormsTmul (f'.detNL hf') p c'.1.1.2.1
      ((pullbackFormsBaseChange w p).val.app (op c'.1.1.2.1)
        (Scheme.Modules.pullbackSection b (f.pullbackForms p) c.1.1.2.1 c'.1.1.2.1 hV s)) z))
    (PresheafOfModules.naturality_apply (detNLPullbackIso w hf hf').hom.val
      (homOfLE hV).op _).symm).trans ?_
  refine (f'.chartTwistedEquiv_tmul hf' c' p _ _).trans ?_
  refine Eq.trans ?_ (congrArg _ (f.chartTwistedEquiv_tmul hf c p s l)).symm
  refine Eq.trans ?_ (TensorProduct.map_tmul _ _ _ _).symm
  refine congrArg₂ (· ⊗ₜ ·) ?_ ?_
  · refine (congrArg (Scheme.pullbackFormsSectionsEquiv c'.1.1.2.2 f' c'.1.1.1.2 c'.1.2 p)
      (Scheme.Modules.Hom.app_eq_val_app (pullbackFormsBaseChange w p) c'.1.1.2.1 _).symm).trans ?_
    exact Scheme.pullbackFormsSectionsEquiv_pullbackFormsBaseChange_formsBaseChangeMapₛₗ
      c.1.1.2.2 f c.1.1.1.2 c.1.2 b c'.1.1.2.2 w c'.1.1.1.2 c'.1.2 hU hV p s
  · exact detNLSectionsEquiv_detNLPullbackIso_hom_pullbackSection f hf w hf' c.1 c'.1 hU hV hsq l

/-- **The base change arrow of Lemma 0H9G on a square of presented charts** is the base change
map of pulled back forms tensored with the base change map of determinants. -/
theorem chartTwistedEquiv_twistedPullbackFormsBaseChange
    (c : {c : f.chartIndex.ι // f.ChartPresented c})
    (c' : {c' : f'.chartIndex.ι // f'.ChartPresented c'}) (hU : c'.1.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1.1)
    (hV : c'.1.1.2.1 ≤ b ⁻¹ᵁ c.1.1.2.1) (hsq : f.IsGoodChartSquare w c.1.2 c'.1.2 hU hV) (p : ℕ)
    (x : Γ(f.twistedPullbackForms (f.detNL hf) p, c.1.1.2.1)) :
    letI := f.chartAlgebra c.1.2
    letI := f'.chartAlgebra c'.1.2
    letI := a.chartAlgebra hU
    letI := b.chartAlgebra hV
    letI := squareAlgebra f' a hU c'.1.2
    haveI := isScalarTower_squareAlgebra_left hU c'.1.2
    haveI := f.isScalarTower_squareAlgebra_right w c.1.2 hU hV c'.1.2
    f'.chartTwistedEquiv hf' c' p
        ((twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val.app
          (op c'.1.1.2.1) (Scheme.Modules.pullbackSection b (f.twistedPullbackForms (f.detNL hf) p)
            c.1.1.2.1 c'.1.1.2.1 hV x)) =
      TensorProduct.map (ExteriorAlgebra.powMapₛₗ p
          (algebraMap Γ(Y, c.1.1.2.1) Γ(Y', c'.1.1.2.1))
          (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1.1) Γ(Y, c.1.1.2.1) Γ(X', c'.1.1.1.1)
            Γ(Y', c'.1.1.2.1)))
        (detNLSquareMap w hf hf' c.1 c'.1 hU hV hsq)
        (f.chartTwistedEquiv hf c p x) := by
  let := f.chartAlgebra c.1.2
  let := f'.chartAlgebra c'.1.2
  let := a.chartAlgebra hU
  let := b.chartAlgebra hV
  let := squareAlgebra f' a hU c'.1.2
  have := isScalarTower_squareAlgebra_left hU c'.1.2
  have := f.isScalarTower_squareAlgebra_right w c.1.2 hU hV c'.1.2
  suffices H : ∀ z, f'.chartTwistedEquiv hf' c' p
        ((twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val.app
          (op c'.1.1.2.1) (Scheme.Modules.pullbackSection b (f.twistedPullbackForms (f.detNL hf) p)
            c.1.1.2.1 c'.1.1.2.1 hV ((f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p).symm z))) =
      TensorProduct.map (ExteriorAlgebra.powMapₛₗ p
          (algebraMap Γ(Y, c.1.1.2.1) Γ(Y', c'.1.1.2.1))
          (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1.1) Γ(Y, c.1.1.2.1) Γ(X', c'.1.1.1.1)
            Γ(Y', c'.1.1.2.1)))
        (detNLSquareMap w hf hf' c.1 c'.1 hU hV hsq)
        (f.chartTwistedEquiv hf c p ((f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p).symm z)) by
    have hx := H (f.twistedSectionsEquiv c.1.1.2.2 (f.detNL hf) p x)
    simpa only [LinearEquiv.symm_apply_apply] using hx
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
    refine (congrArg (fun y => f'.chartTwistedEquiv hf' c' p
        ((twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val.app
          (op c'.1.1.2.1) (Scheme.Modules.pullbackSection b (f.twistedPullbackForms (f.detNL hf) p)
            c.1.1.2.1 c'.1.1.2.1 hV y))) (map_zero _)).trans ?_
    refine (congrArg (fun y => f'.chartTwistedEquiv hf' c' p
        ((twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val.app
          (op c'.1.1.2.1) y))
      (Stacks.Conormal.pullbackSection_zero b _ _ _ hV)).trans ?_
    refine (congrArg (f'.chartTwistedEquiv hf' c' p) (map_zero _)).trans ?_
    refine (map_zero _).trans ?_
    simp only [map_zero]
  | add z z' hz hz' =>
    refine (congrArg (fun y => f'.chartTwistedEquiv hf' c' p
        ((twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val.app
          (op c'.1.1.2.1) (Scheme.Modules.pullbackSection b (f.twistedPullbackForms (f.detNL hf) p)
            c.1.1.2.1 c'.1.1.2.1 hV y))) (map_add _ _ _)).trans ?_
    refine (congrArg (fun y => f'.chartTwistedEquiv hf' c' p
        ((twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val.app
          (op c'.1.1.2.1) y))
      (Stacks.Conormal.pullbackSection_add b _ _ _ hV _ _)).trans ?_
    refine (congrArg (f'.chartTwistedEquiv hf' c' p) (map_add _ _ _)).trans ?_
    refine (map_add _ _ _).trans ?_
    refine (congrArg₂ (· + ·) hz hz').trans ?_
    simp only [map_add]
  | tmul s l =>
    refine (congrArg (fun y => f'.chartTwistedEquiv hf' c' p
        ((twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val.app
          (op c'.1.1.2.1) (Scheme.Modules.pullbackSection b (f.twistedPullbackForms (f.detNL hf) p)
            c.1.1.2.1 c'.1.1.2.1 hV y)))
      (f.twistedSectionsEquiv_symm_tmul c.1.1.2.2 (f.detNL hf) p s l)).trans ?_
    refine (chartTwistedEquiv_twistedPullbackFormsBaseChange_tmul f hf w hf' c c' hU hV hsq p s
      l).trans ?_
    exact congrArg (fun y => TensorProduct.map (ExteriorAlgebra.powMapₛₗ p
          (algebraMap Γ(Y, c.1.1.2.1) Γ(Y', c'.1.1.2.1))
          (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1.1) Γ(Y, c.1.1.2.1) Γ(X', c'.1.1.1.1)
            Γ(Y', c'.1.1.2.1)))
        (detNLSquareMap w hf hf' c.1 c'.1 hU hV hsq)
        (f.chartTwistedEquiv hf c p y))
      (f.twistedSectionsEquiv_symm_tmul c.1.1.2.2 (f.detNL hf) p s l).symm

/-- A restriction map of a sheaf of modules on sections, in the two spellings. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.presheaf_map_eq_val_map {Z : Scheme.{u}}
    (M : Z.Modules) {U V : Z.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    M.presheaf.map i.op x = M.val.map i.op x :=
  rfl

variable [LocallyQuasiFinite f] [LocallyQuasiFinite f']

omit [LocallyQuasiFinite f] in
/-- **Presented charts of `f'` over a presented chart of `f`, near each point**: on them the maps
of Remark 0FL9 are compatible with the base change maps of forms and of determinants. -/
theorem exists_chartOver_chartGarelMap (c : {c : f.chartIndex.ι // f.ChartPresented c}) (p : ℕ)
    (z : {z : Y' // z ∈ b ⁻¹ᵁ c.1.1.2.1}) :
    ∃ (c' : {c' : f'.chartIndex.ι // f'.ChartPresented c'})
      (hU : c'.1.1.1.1 ≤ a ⁻¹ᵁ c.1.1.1.1) (hV : c'.1.1.2.1 ≤ b ⁻¹ᵁ c.1.1.2.1)
      (hsq : f.IsGoodChartSquare w c.1.2 c'.1.2 hU hV),
      z.1 ∈ c'.1.1.2.1 ∧ c'.1.1.2.1 ≤ b ⁻¹ᵁ c.1.1.2.1 ∧
      letI := f.chartAlgebra c.1.2
      letI := f'.chartAlgebra c'.1.2
      letI := a.chartAlgebra hU
      letI := b.chartAlgebra hV
      letI := squareAlgebra f' a hU c'.1.2
      haveI := isScalarTower_squareAlgebra_left hU c'.1.2
      haveI := f.isScalarTower_squareAlgebra_right w c.1.2 hU hV c'.1.2
      ∀ ω : ⋀[Γ(Y, c.1.1.2.1)]^p Ω[Γ(Y, c.1.1.2.1)⁄ℤ],
        f'.chartGarelMap hf' c' p (ExteriorAlgebra.powMapₛₗ p
            (algebraMap Γ(Y, c.1.1.2.1) Γ(Y', c'.1.1.2.1))
            (Stacks.DeRham.kaehlerMapₛₗ _ _) ω) =
          TensorProduct.map (ExteriorAlgebra.powMapₛₗ p
              (algebraMap Γ(Y, c.1.1.2.1) Γ(Y', c'.1.1.2.1))
              (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, c.1.1.1.1) Γ(Y, c.1.1.2.1)
                Γ(X', c'.1.1.1.1) Γ(Y', c'.1.1.2.1)))
            (detNLSquareMap w hf hf' c.1 c'.1 hU hV hsq) (f.chartGarelMap hf c p ω) := by
  have h := exists_chartOver_presentationDetNLMap w hf hf' c.1 c.2 z.2 z.2
  obtain ⟨c', hU, hV, hsq, hm, hl, hP, hid⟩ := h
  have := f'.isRelativeGlobalCompleteIntersection_chartPresentation ⟨c', hP⟩
  exact ⟨⟨c', hP⟩, hU, hV, hsq, hm, hl,
    fun ω => hid (f.chartPresentation c).2 (f'.chartPresentation ⟨c', hP⟩).2 p ω⟩

/-- **The glued maps satisfy condition (0H9E)**: for a commutative square `b ≫ f = f' ≫ a` of
locally quasi-finite syntomic morphisms which induces an open immersion of `Y'` into
`X' ×_X Y`, the maps of `f` and of `f'` are compatible as in Lemma 0H9G through the
identification `b^*det(NL_{Y/X}) ≅ det(NL_{Y'/X'})` of Discriminants, Section 0FKB. -/
theorem chartGarelMaps_isCompatible :
    GarelMaps.IsCompatible w (detNLPullbackIso w hf hf').hom (f.chartGarelMaps hf)
      (f'.chartGarelMaps hf') := by
  refine GarelMaps.isCompatible_of_isBasis w _ _ _
    (f.chartIndex.isBasis_of_refines f.ChartPresented
      (fun c _ hy => f.exists_refines_chartPresented hf c hy) (fun c => c.1.1.2.1) (fun _ => rfl))
    (fun _ _ => Set.univ) (fun _ _ _ => Submodule.span_univ) ?_
  rintro p _ ⟨c, rfl⟩ η -
  beta_reduce
  have hex := f.exists_chartOver_chartGarelMap hf w hf' c p
  choose κ hU hV hsq hmem hle hid using hex
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover _ (fun z => (κ z).1.1.2.1) hle
    (fun y hy => ⟨⟨y, hy⟩, hmem ⟨y, hy⟩⟩) _ _ fun z => ?_
  refine (f'.chartTwistedEquiv hf' (κ z) p).injective ?_
  refine (congrArg (f'.chartTwistedEquiv hf' (κ z) p) (PresheafOfModules.naturality_apply
    (twistedPullbackFormsBaseChange (f.detNL hf) w (detNLPullbackIso w hf hf').hom p).val
    (homOfLE (hle z)).op _).symm).trans ?_
  refine (chartTwistedEquiv_twistedPullbackFormsBaseChange f hf w hf' c (κ z) (hU z) (hV z)
    (hsq z) p _).trans ?_
  refine (congrArg _ (f.chartTwistedEquiv_chartGarelMaps_app hf p c η)).trans ?_
  refine Eq.trans ?_ (congrArg (f'.chartTwistedEquiv hf' (κ z) p)
    (PresheafOfModules.naturality_apply (f'.chartGarelMaps hf' p).val (homOfLE (hle z)).op _))
  refine Eq.trans ?_ (congrArg (fun y => f'.chartTwistedEquiv hf' (κ z) p
    ((f'.chartGarelMaps hf' p).val.app (op (κ z).1.1.2.1) y))
    ((Scheme.absoluteFormsMap_app_pullbackSection (b := b) (hb := hV z) p η).trans
      (Scheme.Modules.presheaf_map_eq_val_map _ (homOfLE (hle z)) _)))
  refine Eq.trans ?_ (f'.chartTwistedEquiv_chartGarelMaps_app hf' p (κ z) _).symm
  refine Eq.trans ?_ (congrArg (f'.chartGarelMap hf' (κ z) p)
    (?e : _ = (let := b.chartAlgebra (hV z)
      ExteriorAlgebra.powMapₛₗ p (algebraMap Γ(Y, c.1.1.2.1) Γ(Y', (κ z).1.1.2.1))
        (Stacks.DeRham.kaehlerMapₛₗ Γ(Y, c.1.1.2.1) Γ(Y', (κ z).1.1.2.1))
        (Scheme.absoluteFormsSectionsEquiv Y c.1.1.2.2 p η)))).symm
  case e =>
    exact Scheme.absoluteFormsSectionsEquiv_absoluteFormsMap_pullbackSection_kaehlerMapₛₗ
      c.1.1.2.2 b (κ z).1.1.2.2 (hV z) p η
  exact (hid z _).symm

end BaseChange

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.GarelRule

open MonoidalCategory Scheme.Hom

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict

/-- **The rule of Stacks Tag 0FLA**: to a locally quasi-finite syntomic morphism it assigns the
maps glued from the maps of Remark 0FL9 on presented charts. -/
def chartRule : GarelRule.{u} := fun _ _ f hf hq =>
  haveI := hq
  f.chartGarelMaps hf

/-- The rule `chartRule` satisfies (0H9C). -/
theorem chartRule_isNormalized : chartRule.{u}.IsNormalized := fun _ _ f hf hq =>
  have := hq
  f.chartGarelMaps_isNormalized hf

/-- The rule `chartRule` satisfies (0H9D). -/
theorem chartRule_isMultiplicative : chartRule.{u}.IsMultiplicative := fun _ _ f hf hq =>
  have := hq
  f.chartGarelMaps_isMultiplicative hf

/-- The rule `chartRule` satisfies (0H9E). -/
theorem chartRule_isCompatible : chartRule.{u}.IsCompatible :=
  fun _ _ _ _ f _ _ _ w _ hf hq hf' hq' =>
    have := hq
    have := hq'
    f.chartGarelMaps_isCompatible hf w hf'

/-- There exists a unique rule that to every locally quasi-finite syntomic morphism of schemes
`f : Y ⟶ X` assigns `𝒪_Y`-module maps
`c^p_{Y/X} : Ω^p_{Y/ℤ} ⟶ f^*Ω^p_{X/ℤ} ⊗_{𝒪_Y} det(NL_{Y/X})` for `p ≥ 0` satisfying (0H9C),
(0H9D) and (0H9E). In particular, the composition of `c^p_{Y/X}` with
`f^*Ω^p_{X/ℤ} ⟶ Ω^p_{Y/ℤ}` is multiplication by `δ(NL_{Y/X})`. -/
@[stacks 0FLA "the unique rule c^p_{Y/X} satisfying 0H9C, 0H9D and 0H9E, and its composition \
with f^*Ω^p_{X/Z} → Ω^p_{Y/Z} is multiplication by δ(NL_{Y/X})"]
theorem existsUnique_isNormalized_isMultiplicative_isCompatible :
    (∃! c : GarelRule.{u}, c.IsNormalized ∧ c.IsMultiplicative ∧ c.IsCompatible) ∧
      ∀ c : GarelRule.{u}, c.IsNormalized → c.IsMultiplicative → c.IsCompatible →
        ∀ ⦃X Y : Scheme.{u}⦄ (f : Y ⟶ X) (hf : Syntomic f) (hq : LocallyQuasiFinite f) (p : ℕ),
          f.absoluteFormsMap p ≫ c f hf hq p =
            (ρ_ (f.pullbackForms p)).inv ≫ (f.pullbackForms p ◁
              Scheme.Modules.globalSectionHom (f.detNL hf) (haveI := hq; f.deltaNL hf)) :=
  ⟨⟨chartRule, ⟨chartRule_isNormalized, chartRule_isMultiplicative, chartRule_isCompatible⟩,
      fun _ ⟨h₁, h₂, h₃⟩ => eq_of_isNormalized_of_isMultiplicative_of_isCompatible h₁ h₂ h₃
        chartRule_isNormalized chartRule_isMultiplicative chartRule_isCompatible⟩,
    fun _ h₁ h₂ _ _ _ f hf hq p => GarelMaps.absoluteFormsMap_comp (h₁ f hf hq) (h₂ f hf hq) p⟩

end AlgebraicGeometry.GarelRule

end
