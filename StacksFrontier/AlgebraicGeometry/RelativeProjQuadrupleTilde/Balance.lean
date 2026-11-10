module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartData
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The comparison `ℳ̃_T ⟶ h^*ℳ̃` on one chart: the balancing relations

In the local situation of
`StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartData` the degree-`m` member of the
comparison of property (1) of [Stacks, Tag 01O7] is

`b_m : f^*ℳ_{md} ⊗ L^{⊗ (-m)} ⟶ g^*ℳ̃(U)`,  `x ⊗ l ↦ (w^m · l) · g^*(x / c^m)`,

the comparison `β_m` of the module factor tensored with the coordinate of `L^{⊗ (-m)}` in the
trivialization by `w`. This file proves that the family is balanced over `f^*𝒜^{(d)}`, which by
the universal property of the module of [Stacks, Tag 01O6] is what produces the comparison out of
`ℳ̃_T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation
open Stacks.AlgebraicGeometry.AffineOpenHomRecovery (pullbackSection_add pullbackSection_smul)

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing
attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

/-! ### A coherence identity -/

section Coherence

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- The two ways of multiplying `X ⊗ Y ⊗ Z ⟶ G ⊗ 𝟙 ⊗ 𝟙` down to `G` agree. -/
theorem tensor_unit_assoc {X Y Z G : C} (β : X ⟶ G) (κ : Y ⟶ 𝟙_ C) (γ : Z ⟶ 𝟙_ C) :
    (((β ⊗ₘ κ) ≫ (ρ_ G).hom) ⊗ₘ γ) ≫ (ρ_ G).hom =
      (α_ X Y Z).hom ≫ (β ⊗ₘ ((κ ▷ Z) ≫ (λ_ Z).hom ≫ γ)) ≫ (ρ_ G).hom := by
  rw [← leftUnitor_naturality, ← Category.assoc (κ ▷ Z), ← tensorHom_def]
  monoidal

end Coherence

/-! ### Local pure tensors -/

section Generic

variable {Z : RingedSpace.{u, u}}

/-- The inverse right unitor on a local section: `x ↦ x ⊗ 1`. -/
theorem rightUnitor_inv_app (X : SheafOfModules.{u} (structureRingSheaf Z))
    (V : (TopologicalSpace.Opens Z.carrier)ᵒᵖ) (x : X.val.obj V) :
    (ρ_ X).inv.val.app V x = tmul Z X (𝟙_ _) V x (oneSec Z V) := by
  have h := rightUnitor_hom_tmul (Z := Z) (A := X) V x
    (1 : (structureRingSheaf Z).obj.obj V)
  rw [one_smul] at h
  have h2 : ((ρ_ X).hom ≫ (ρ_ X).inv).val.app V (tmul Z X (𝟙_ _) V x (oneSec Z V)) =
      tmul Z X (𝟙_ _) V x (oneSec Z V) := by
    rw [Iso.hom_inv_id]
    rfl
  exact (congrArg (fun z => (ρ_ X).inv.val.app V z) h.symm).trans h2

/-- A pure tensor of local sections commutes with restriction. -/
theorem tmul_restrict (A B : SheafOfModules.{u} (structureRingSheaf Z))
    {V V' : (TopologicalSpace.Opens Z.carrier)ᵒᵖ} (e : V ⟶ V') (a : A.val.obj V)
    (b : B.val.obj V) :
    (A ⊗ B).val.map e (tmul Z A B V a b) = tmul Z A B V' (A.val.map e a) (B.val.map e b) :=
  (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf (Z))
      (𝟙 (Stacks.RingedSpace.structureRingSheaf (Z)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (Z).presheaf) (A).val (B).val)) e (a ⊗ₜ b)).symm.trans
    (congrArg (fun w => ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf (Z))
        (𝟙 (Stacks.RingedSpace.structureRingSheaf (Z)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (Z).presheaf) (A).val (B).val)).app V' w)
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul e a b))

/-- **The comparison of Tag 01CD on the pullbacks of a pure tensor of sections over an open**,
read on the sections over the whole of the source. -/
theorem pullbackTensorComparison_pullbackSection {S T : Scheme.{u}} (f : T ⟶ S)
    (A B : S.Modules) (U : S.Opens)
    (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U) (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    (pullbackTensorComparison (ringedSpaceHom f) A B).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f (AffineOpenTensorSections.tensorMod A B) U ⊤ hf
          (AffineOpenTensorSections.gammaTmul A B U a b)) =
      tmul T.toRingedSpace ((pullbackFunctor (ringedSpaceHom f)).obj A)
        ((pullbackFunctor (ringedSpaceHom f)).obj B) (op ⊤)
        (Scheme.Modules.pullbackSection f A U ⊤ hf a)
        (Scheme.Modules.pullbackSection f B U ⊤ hf b) := by
  unfold Scheme.Modules.pullbackSection
  refine (PresheafOfModules.naturality_apply
    (pullbackTensorComparison (ringedSpaceHom f) A B).val (homOfLE hf).op _).trans ?_
  refine (congrArg (fun z => (((pullbackFunctor (ringedSpaceHom f)).obj A) ⊗
    ((pullbackFunctor (ringedSpaceHom f)).obj B)).val.map (homOfLE hf).op z)
    (pullbackTensorComparison_pullbackUnit (ringedSpaceHom f) A B (op U) a b)).trans ?_
  exact tmul_restrict _ _ (homOfLE hf).op _ _

end Generic

section Chart

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  (U : s.base.affineOpens) {d : ℕ} (c : s.sectionPieces U.1 d)
  {T : Scheme.{u}} (f : T ⟶ s.base) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U.1)
  (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
  (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
  (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))

/-- The product of the image of a function on `U` with a homogeneous section of the algebra is the
homogeneous section of the module action. -/
theorem sectionRingBaseMap_mul_of (r : s.base.ringCatSheaf.obj.obj (op U.1)) (n : ℕ)
    (a : s.sectionPieces U.1 n) :
    s.sectionRingBaseMap U.1 r * DirectSum.of (s.sectionPieces U.1) n a =
      DirectSum.of (s.sectionPieces U.1) n (r • a) := by
  rw [show s.sectionRingBaseMap U.1 r = _ from (sectionRingStructure s).baseMap_apply U.1 r,
    DirectSum.of_mul_of]
  refine DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (zero_add n) ?_)
  rw [sectionPieces_mul_eq]
  have hleft : (s.algebra.mul ((0 : ℕ) : ℤ) (n : ℤ)).app (op U.1)
        (r • s.algebra.one.eval (op U.1)) a
      = r • (s.algebra.mul ((0 : ℕ) : ℤ) (n : ℤ)).app (op U.1) (s.algebra.one.eval (op U.1)) a :=
    (s.algebra.mul _ _).map_smul_left _ r _ a
  refine (heq_of_eq hleft).trans ?_
  have key : ∀ (k : ℤ) (_ : k = (n : ℤ)) (y : (s.algebra.piece k).val.obj (op U.1)),
      HEq y a → HEq (r • y) (r • a) := by
    rintro k rfl y hy
    rw [eq_of_heq hy]
  exact key _ (zero_add _) _ (s.algebra.one_mul (n : ℤ) (op U.1) a)

/-- The fraction `a / c^i` of a section `a` of `𝒜_{id}` over `U`. -/
abbrev algFrac (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    HomogeneousLocalization.Away (s.sectionRingGrading U.1) (cHom U.1 c) :=
  HomogeneousLocalization.Away.mk (s.sectionRingGrading U.1) (cHom_mem U.1 c) i
    (DirectSum.of (s.sectionPieces U.1) (i * d) a) ⟨a, rfl⟩

/-- The fraction `a / c^i` is additive in `a`. -/
theorem algFrac_add (i : ℕ) (a b : s.sectionPieces U.1 (i * d)) :
    algFrac U c i (a + b) = algFrac U c i a + algFrac U c i b := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_add]
  change (Localization.mk (DirectSum.of (s.sectionPieces U.1) (i * d) (a + b))
      (⟨(cHom U.1 c) ^ i, i, rfl⟩ : Submonoid.powers (cHom U.1 c)) : Localization.Away _) =
    Localization.mk (DirectSum.of (s.sectionPieces U.1) (i * d) a)
        (⟨(cHom U.1 c) ^ i, i, rfl⟩ : Submonoid.powers (cHom U.1 c)) +
      Localization.mk (DirectSum.of (s.sectionPieces U.1) (i * d) b)
        (⟨(cHom U.1 c) ^ i, i, rfl⟩ : Submonoid.powers (cHom U.1 c))
  rw [map_add, Localization.add_mk_self]

/-- The fraction `(r • a) / c^i` is the product of `r / 1` and `a / c^i`. -/
theorem algFrac_smul (i : ℕ) (r : s.base.ringCatSheaf.obj.obj (op U.1))
    (a : s.sectionPieces U.1 (i * d)) :
    algFrac U c i (r • a) = baseFrac U c r * algFrac U c i a := by
  apply HomogeneousLocalization.val_injective
  simp only [algFrac, baseFrac, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_mul, ← sectionRingBaseMap_mul_of]
  congr 1
  exact Subtype.ext (by simp)

/-- The function `g^♯(a / c^i)` on `T`, additive in `a`. -/
def kappaSec (i : ℕ) : s.sectionPieces U.1 (i * d) →+ T.ringCatSheaf.obj.obj (op ⊤) where
  toFun a := g.appLE _ ⊤ hg (Proj.awayToSection _ _ (algFrac U c i a))
  map_zero' := by
    rw [show algFrac U c i 0 = 0 by simpa using algFrac_add U c i 0 0, map_zero, map_zero]
    rfl
  map_add' a b := by
    rw [algFrac_add, map_add, map_add]
    rfl

include hgf in
/-- The function `g^♯((r • a) / c^i)` is `f^♯(r)` times `g^♯(a / c^i)`. -/
theorem kappaSec_smul (i : ℕ) (r : s.base.ringCatSheaf.obj.obj (op U.1))
    (a : s.sectionPieces U.1 (i * d)) :
    kappaSec U c g hg i (r • a) =
      (show T.ringCatSheaf.obj.obj (op ⊤) from f.appLE U.1 ⊤ hf r) • kappaSec U c g hg i a := by
  change g.appLE _ ⊤ hg (Proj.awayToSection _ _ (algFrac U c i (r • a))) =
    f.appLE U.1 ⊤ hf r * g.appLE _ ⊤ hg (Proj.awayToSection _ _ (algFrac U c i a))
  rw [algFrac_smul, map_mul, map_mul, hgf r]

/-- **The morphism `κ_i : f^*𝒜_{id} ⟶ 𝒪_T`, `a ↦ g^♯(a / c^i)`.** -/
def kappa (i : ℕ) :
    (Scheme.Modules.pullback f).obj (s.algebra.piece ((i * d : ℕ) : ℤ)) ⟶
      (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) : T.Modules) :=
  AffineOpenHomRecovery.homOfSections f U.1 hf (s.algebra.piece ((i * d : ℕ) : ℤ)) U.2
    (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) : T.Modules)
    (kappaSec U c g hg i) (kappaSec_smul U c f hf g hg hgf i)

/-- The morphism `κ_i` sends the pullback of a section `a` of `𝒜_{id}` over `U` to
`g^♯(a / c^i)`. -/
theorem kappa_pullbackSection (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    (kappa U c f hf g hg hgf i).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf a) = kappaSec U c g hg i a :=
  AffineOpenHomRecovery.homOfSections_pullbackSection f U.1 hf
    (s.algebra.piece ((i * d : ℕ) : ℤ)) U.2
    (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) : T.Modules)
    (kappaSec U c g hg i) (kappaSec_smul U c f hf g hg hgf i) a

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **The pulled-back fraction carries the action of `a` to multiplication by `g^♯(a / c^i)`.** -/
theorem fracPull_smul (m : ℤ) (i : ℕ) (a : s.sectionPieces U.1 (i * d))
    (x : sectionModulePieces ℳ U.1 (m * d)) (y : sectionModulePieces ℳ U.1 ((m + i) * d))
    (hy : DirectSum.of (sectionModulePieces ℳ U.1) ((m + i) * d) y =
      DirectSum.of (s.sectionPieces U.1) (i * d) a •
        DirectSum.of (sectionModulePieces ℳ U.1) (m * d) x) :
    fracPull ℳ U c g hg (m + i) y =
      (show T.ringCatSheaf.obj.obj (op ⊤) from kappaSec U c g hg i a) •
        fracPull ℳ U c g hg m x := by
  have h1 : fracChart ℳ U c (m + i) y =
      (show (AlgebraicGeometry.Proj (s.sectionRingGrading U.1)).ringCatSheaf.obj.obj
          (op (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))) from
        Proj.awayToSection _ _ (algFrac U c i a)) • fracChart ℳ U c m x :=
    (congrArg (degreeZeroToSection (s.sectionRingGrading U.1) (sectionModuleGrading ℳ U.1)
      (cHom U.1 c)) (fracElt_smul ℳ U.1 c m i a x y hy)).trans (map_smul _ _ _)
  exact (congrArg (Scheme.Modules.pullbackSection g (moduleChart ℳ U) _ ⊤ hg) h1).trans
    (pullbackSection_smul g _ _ ⊤ hg _ _)

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The homogeneous product presented by the right action of the right graded module read off
`ℳ`, transported to the degree `(m + i)d`. -/
theorem of_act (m : ℤ) (i : ℕ) (x : sectionModulePieces ℳ U.1 (m * d))
    (a : s.sectionPieces U.1 (i * d)) :
    DirectSum.of (sectionModulePieces ℳ U.1) ((m + i) * d)
        ((eqToHom (congrArg ℳ.piece (by ring : m * d + (i : ℤ) * d = (m + i) * d))).val.app
          (op U.1) ((ℳ.toGradedModule s.mul_comm).smul (m * d) ((i : ℤ) * d) (op U.1) x a)) =
      DirectSum.of (s.sectionPieces U.1) (i * d) a •
        DirectSum.of (sectionModulePieces ℳ U.1) (m * d) x := by
  rw [sectionModule_of_smul_of]
  have key : ∀ (k k' : ℤ) (hk : k = k') (z : sectionModulePieces ℳ U.1 k),
      DirectSum.of (sectionModulePieces ℳ U.1) k'
          ((eqToHom (congrArg ℳ.piece hk)).val.app (op U.1) z) =
        DirectSum.of (sectionModulePieces ℳ U.1) k z := by
    rintro k k' rfl z
    rfl
  refine (key _ _ (by ring) _).trans ?_
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext
    (show m * (d : ℤ) + (i : ℤ) * d = ((i * d : ℕ) : ℤ) + m * d by push_cast; ring)
    (SheafOfModules.LeftGradedModule.toGradedModule_smul_heq ℳ s.mul_comm _ _ (op U.1) x a))

/-- The target `g^*ℳ̃(U)` of the comparison, in the spelling of the monoidal structure. -/
abbrev tgt : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace) :=
  (Scheme.Modules.pullback g).obj (moduleChart ℳ U)

/-- `β_m`, in the spelling of the monoidal structure. -/
abbrev betaS (m : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (ℳ.piece (m * d)) ⟶ tgt ℳ U g :=
  beta ℳ U c f hf g hg hgf m

/-- `κ_i`, in the spelling of the monoidal structure. -/
abbrev kappaS (i : ℕ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (s.algebra.piece ((i : ℤ) * d)) ⟶
      𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :=
  kappa U c f hf g hg hgf i

/-- **The comparisons `β` carry the action of `f^*𝒜_{id}` on `f^*ℳ_{md}` to multiplication by
`κ_i`.** -/
theorem act_beta (m : ℤ) (i : ℕ) :
    act f (ℳ.toGradedModule s.mul_comm) (d : ℤ) m i ≫ betaS ℳ U c f hf g hg hgf (m + i) =
      (betaS ℳ U c f hf g hg hgf m ⊗ₘ kappaS U c f hf g hg hgf i) ≫ (ρ_ _).hom := by
  let φ := (ℳ.toGradedModule s.mul_comm).smulSheaf (m * d) ((i : ℤ) * d) ≫
    eqToHom (congrArg (ℳ.toGradedModule s.mul_comm).piece
      (by ring : m * (d : ℤ) + (i : ℤ) * d = (m + i) * d))
  suffices h : (pullbackFunctor (ringedSpaceHom f)).map φ ≫
        betaS ℳ U c f hf g hg hgf (m + i) =
        pullbackTensorComparison (ringedSpaceHom f) ((ℳ.toGradedModule s.mul_comm).piece (m * d))
            (s.algebra.piece ((i : ℤ) * d)) ≫
          (betaS ℳ U c f hf g hg hgf m ⊗ₘ kappaS U c f hf g hg hgf i) ≫ (ρ_ _).hom by
    exact (Category.assoc _ _ _).trans ((congrArg (fun z => inv (pullbackTensorComparison
      (ringedSpaceHom f) ((ℳ.toGradedModule s.mul_comm).piece (m * d))
        (s.algebra.piece ((i : ℤ) * d))) ≫ z) h).trans (IsIso.inv_hom_id_assoc _ _))
  refine AffineOpenHomRecovery.hom_ext_tensor f U.1 hf U.2 _ (ℳ.piece (m * d))
    (s.algebra.piece ((i : ℤ) * d)) fun x a => ?_
  let t := AffineOpenTensorSections.gammaTmul (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d))
    U.1 x a
  have hL : ((pullbackFunctor (ringedSpaceHom f)).map φ ≫
          betaS ℳ U c f hf g hg hgf (m + i)).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf t) =
      fracPull ℳ U c g hg (m + i)
        ((eqToHom (congrArg ℳ.piece (by ring : m * d + (i : ℤ) * d = (m + i) * d))).val.app
          (op U.1) ((ℳ.toGradedModule s.mul_comm).smul (m * d) ((i : ℤ) * d) (op U.1) x a)) := by
    change (betaS ℳ U c f hf g hg hgf (m + i)).val.app (op ⊤)
      (((Scheme.Modules.pullback f).map φ).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf t)) = _
    have e1 := Scheme.Modules.pullbackSection_naturality f
      (F := AffineOpenTensorSections.tensorMod (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d)))
      (G := ℳ.piece ((m + i) * d)) φ U.1 ⊤ hf t
    refine (congrArg (fun z => (betaS ℳ U c f hf g hg hgf (m + i)).val.app (op ⊤) z) e1).trans ?_
    have e2 : φ.val.app (op U.1) t =
        (eqToHom (congrArg ℳ.piece (by ring : m * d + (i : ℤ) * d = (m + i) * d))).val.app
          (op U.1) ((ℳ.toGradedModule s.mul_comm).smul (m * d) ((i : ℤ) * d) (op U.1) x a) :=
      congrArg (fun z => (eqToHom (congrArg ℳ.piece
          (by ring : m * d + (i : ℤ) * d = (m + i) * d))).val.app (op U.1) z)
        (SheafOfModules.GradedModule.smulSheaf_unit (ℳ.toGradedModule s.mul_comm) _ _ (op U.1) x a)
    refine (congrArg (fun z => (betaS ℳ U c f hf g hg hgf (m + i)).val.app (op ⊤)
      (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf z)) e2).trans ?_
    exact beta_pullbackSection ℳ U c f hf g hg hgf (m + i) _
  have hR : (pullbackTensorComparison (ringedSpaceHom f)
        ((ℳ.toGradedModule s.mul_comm).piece (m * d)) (s.algebra.piece ((i : ℤ) * d)) ≫
          (betaS ℳ U c f hf g hg hgf m ⊗ₘ kappaS U c f hf g hg hgf i) ≫ (ρ_ _).hom).val.app
        (op ⊤) (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf t) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        fracPull ℳ U c g hg m x := by
    change (ρ_ (tgt ℳ U g)).hom.val.app (op ⊤)
      ((betaS ℳ U c f hf g hg hgf m ⊗ₘ kappaS U c f hf g hg hgf i).val.app (op ⊤)
        ((pullbackTensorComparison (ringedSpaceHom f) (ℳ.piece (m * d))
          (s.algebra.piece ((i : ℤ) * d))).val.app (op ⊤)
          (Scheme.Modules.pullbackSection f
            (AffineOpenTensorSections.tensorMod (ℳ.piece (m * d)) (s.algebra.piece ((i : ℤ) * d)))
            U.1 ⊤ hf t))) = _
    have e1 := pullbackTensorComparison_pullbackSection f (ℳ.piece (m * d))
      (s.algebra.piece ((i : ℤ) * d)) U.1 hf x a
    refine (congrArg (fun z => (ρ_ (tgt ℳ U g)).hom.val.app (op ⊤)
      ((betaS ℳ U c f hf g hg hgf m ⊗ₘ kappaS U c f hf g hg hgf i).val.app (op ⊤) z)) e1).trans ?_
    refine (congrArg (fun z => (ρ_ (tgt ℳ U g)).hom.val.app (op ⊤) z)
      (tensorHom_tmul _ _ (op ⊤) _ _)).trans ?_
    refine (rightUnitor_hom_tmul (op ⊤) _ _).trans ?_
    exact congrArg₂ (· • ·) (kappa_pullbackSection U c f hf g hg hgf i a)
      (beta_pullbackSection ℳ U c f hf g hg hgf m x)
  refine hL.trans (Eq.trans ?_ hR.symm)
  exact fracPull_smul ℳ U c g hg m i a x _ (of_act ℳ U m i x a)

variable {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f s.algebra (d : ℤ) L) (w : (LaurentSections.Ring L (op ⊤))ˣ)
  (hCP : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
    ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        LaurentSections.pw w i)

include hCP in
/-- **The chart identity, as an identity of morphisms**: `ψ_i = κ_i · w^i`. -/
theorem twisting_app_eq (i : ℕ) :
    ψ.app i = kappa U c f hf g hg hgf i ≫
      LaurentSections.secHom ((laurent L).piece i) (LaurentSections.pw w i) := by
  refine AffineOpenHomRecovery.hom_ext f U.1 hf (s.algebra.piece ((i * d : ℕ) : ℤ)) U.2
    ((laurent L).piece i) fun a => ?_
  have e1 : (ψ.app i).val.app (op ⊤) (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf a) =
      ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) :=
    PresheafOfModules.naturality_apply (ψ.app i).val (homOfLE hf).op _
  have etop : ∀ x : ((laurent L).piece i).val.obj (op ⊤),
      ((laurent L).piece i).val.restrictₛₗ (LaurentSections.topRes T (op ⊤)) x = x := by
    intro x
    have h1 : LaurentSections.topRes T (op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    change ((laurent L).piece i).val.map (LaurentSections.topRes T (op ⊤)) x = x
    rw [h1, PresheafOfModules.map_id]
    rfl
  have e2 : (kappa U c f hf g hg hgf i ≫
      LaurentSections.secHom ((laurent L).piece i) (LaurentSections.pw w i)).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        LaurentSections.pw w i := by
    change (LaurentSections.secHom ((laurent L).piece i) (LaurentSections.pw w i)).val.app (op ⊤)
      ((kappa U c f hf g hg hgf i).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ U.1 ⊤ hf a)) = _
    rw [kappa_pullbackSection]
    exact (LaurentSections.secHom_app _ _ _ _).trans (congrArg _ (etop _))
  exact e1.trans ((hCP i a).trans e2.symm)

variable (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
    DirectSum.of _ (-1) τ)

/-- **The degree-`n` member of the comparison**, `x ⊗ l ↦ (w^n · l) · g^*(x / c^n)`. -/
def bmap (n : ℤ) : summand f (ℳ.toGradedModule s.mul_comm) (d : ℤ) L n ⟶ tgt ℳ U g :=
  (betaS ℳ U c f hf g hg hgf n ⊗ₘ LaurentSections.coord w n) ≫ (ρ_ _).hom

include hCP hw hw' in
/-- **The family is balanced in a bidegree `(m, i)` with `i ≥ 0`.** -/
theorem bmap_balanced_nat (m : ℤ) (i : ℕ) :
    relationLeft f (ℳ.toGradedModule s.mul_comm) (d : ℤ) L (m, (i : ℤ)) ≫
        bmap ℳ U c f hf g hg hgf w (m + i) =
      Twisting.relationRight (ℳ.toGradedModule s.mul_comm) ψ (m, (i : ℤ)) ≫
        bmap ℳ U c f hf g hg hgf w m := by
  have h1 := act_beta ℳ U c f hf g hg hgf m i
  have h2 : ψ.app (i : ℤ) = kappaS U c f hf g hg hgf i ≫
      LaurentSections.secHom ((laurent L).piece i) (LaurentSections.pw w i) :=
    twisting_app_eq U c f hf g hg hgf ψ w hCP i
  have h3 := LaurentSections.secHom_mul_coord w hw hw' m i
  have hL : relationLeft f (ℳ.toGradedModule s.mul_comm) (d : ℤ) L (m, (i : ℤ)) ≫
        bmap ℳ U c f hf g hg hgf w (m + i) =
      (((betaS ℳ U c f hf g hg hgf m ⊗ₘ kappaS U c f hf g hg hgf i) ≫ (ρ_ _).hom) ⊗ₘ
        LaurentSections.coord w (m + i)) ≫ (ρ_ _).hom := by
    rw [← h1]
    exact (whiskerRight_comp_tensorHom_assoc _ _ _ _)
  have hR : Twisting.relationRight (ℳ.toGradedModule s.mul_comm) ψ (m, (i : ℤ)) ≫
        bmap ℳ U c f hf g hg hgf w m =
      (α_ _ _ _).hom ≫ (betaS ℳ U c f hf g hg hgf m ⊗ₘ
        ((kappaS U c f hf g hg hgf i ▷ (laurent L).piece (-(m + i))) ≫ (λ_ _).hom ≫
          LaurentSections.coord w (m + i))) ≫ (ρ_ _).hom := by
    rw [← h3]
    change ((α_ _ _ _).hom ≫ _ ◁ ((ψ.app (i : ℤ) ▷ (laurent L).piece (-(m + i))) ≫
        mulHom (laurent L) i (-(m + i)) ≫ eqToHom (congrArg (laurent L).piece
          (by ring : (i : ℤ) + -(m + i) = -m)))) ≫
      (betaS ℳ U c f hf g hg hgf m ⊗ₘ LaurentSections.coord w m) ≫ (ρ_ _).hom = _
    rw [Category.assoc, whiskerLeft_comp_tensorHom_assoc, h2, comp_whiskerRight]
    simp only [Category.assoc]
  rw [hL, hR]
  exact tensor_unit_assoc _ _ _

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **Any two morphisms out of a balancing source in a negative degree of `𝒜` agree**: the
pulled-back piece `f^*𝒜_{id}`, `i < 0`, is zero. -/
theorem relationSummand_hom_ext (hd : 0 < d) (p : ℤ × ℤ) (hp : p.2 < 0) {N : T.Modules}
    (φ₁ φ₂ : relationSummand f (ℳ.toGradedModule s.mul_comm) (d : ℤ) L p ⟶ N) : φ₁ = φ₂ := by
  have hz : IsZero ((pullbackFunctor (ringedSpaceHom f)).obj (s.algebra.piece (p.2 * d))) :=
    IsZero.of_iso (isZero_zero _)
      ((Scheme.Modules.pullback f).mapIso (s.negative_isZero _ (by nlinarith)).isoZero ≪≫
        (Scheme.Modules.pullback f).mapZeroObject)
  have h0 : ∀ (V : (Opens T.carrier)ᵒᵖ)
      (a : ((pullbackFunctor (ringedSpaceHom f)).obj (s.algebra.piece (p.2 * d))).val.obj V),
      a = 0 := fun V a => by
    have := congrArg (fun φ : (pullbackFunctor (ringedSpaceHom f)).obj
        (s.algebra.piece (p.2 * d)) ⟶ _ => φ.val.app V a) (hz.eq_of_src (𝟙 _) 0)
    exact this
  refine tensor_hom_ext₂ fun V x a l => ?_
  rw [h0 V a]
  have e1 : tmul T.toRingedSpace _ _ V x
      (0 : ((pullbackFunctor (ringedSpaceHom f)).obj (s.algebra.piece (p.2 * d))).val.obj V) = 0 :=
    by unfold tmul; rw [TensorProduct.tmul_zero]; exact map_zero _
  rw [e1]
  have e2 : tmul T.toRingedSpace _ _ V (0 : ((pullbackFunctor (ringedSpaceHom f)).obj
      ((ℳ.toGradedModule s.mul_comm).piece (p.1 * d)) ⊗ (pullbackFunctor (ringedSpaceHom f)).obj
        (s.algebra.piece (p.2 * d))).val.obj V) l = 0 :=
    by unfold tmul; rw [TensorProduct.zero_tmul]; exact map_zero _
  rw [e2, map_zero, map_zero]

include hCP hw hw' in
/-- **The family `b` is balanced over `f^*𝒜^{(d)}` in every bidegree.** -/
theorem bmap_balanced (hd : 0 < d) (p : ℤ × ℤ) :
    relationLeft f (ℳ.toGradedModule s.mul_comm) (d : ℤ) L p ≫
        bmap ℳ U c f hf g hg hgf w (p.1 + p.2) =
      Twisting.relationRight (ℳ.toGradedModule s.mul_comm) ψ p ≫
        bmap ℳ U c f hf g hg hgf w p.1 := by
  obtain ⟨m, k⟩ := p
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact bmap_balanced_nat ℳ U c f hf g hg hgf ψ w hCP hw hw' m i
  · exact relationSummand_hom_ext ℳ f hd (m, k) hk _ _

end Chart

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
