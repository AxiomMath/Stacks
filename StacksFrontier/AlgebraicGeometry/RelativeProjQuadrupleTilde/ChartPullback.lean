module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Balance
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.LaurentSectionsPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AssociatedSheafPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.AssociatedSheafCompose

/-!
# The local situation of Tag 01O7 (1) along a pullback

In the local situation of
`StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartData` — an affine open `U` of the
base, a section `c` of `𝒜_d` over `U`, a test scheme `T` over `U`, a morphism
`g : T ⟶ D₊(c) ⊆ Proj 𝒜(U)` lying over `f`, and a homogeneous unit `w` of degree one of the ring
of global Laurent sections with `ψ(a) = g^♯(a / c^i) · w^i` — this file shows that **pulling
everything back along a morphism `k : T' ⟶ T` gives the same local situation for the pulled-back
quadruple**: `k ≫ f`, `k ≫ g`, the pullback `ψ.pullback k` and the pulled-back unit
`LaurentSections.pullbackUnit' k L w` satisfy the two chart identities again.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.hgf_pullback`: the base identity along the
  pullback.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.sectionHom_pullback`: the sections of the
  pulled-back `ψ` are the pulled-back sections of `ψ`.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.hCP_pullback`: the chart identity along the
  pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation
open RingedSpaceModuleAdjunction

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

/-! ### A rearrangement in a monoidal category -/

section Monoidal

variable {C : Type*} [Category C] [MonoidalCategory C]

private theorem bmap_square {P A B A₂ B₂ G G' I Q : C} {ptc : P ⟶ A ⊗ B} {cinv : A ⟶ A₂}
    {lp : B ⟶ B₂} {β' : A₂ ⟶ G'} {co' : B₂ ⟶ 𝟙_ C} {kβ : A ⟶ G} {pc : G ⟶ G'} {kco : B ⟶ I}
    {puc : I ⟶ 𝟙_ C} {kbm : P ⟶ Q} {ptc' : Q ⟶ G ⊗ I} {kρ : Q ⟶ G} {kbmρ : P ⟶ G}
    (hm : kbmρ = kbm ≫ kρ) (hnat : kbm ≫ ptc' = ptc ≫ (kβ ⊗ₘ kco))
    (hρ : kρ = ptc' ≫ (G ◁ puc) ≫ (ρ_ G).hom) (hβ : cinv ≫ β' = kβ ≫ pc)
    (hco : lp ≫ co' = kco ≫ puc) :
    ptc ≫ (cinv ⊗ₘ lp) ≫ (β' ⊗ₘ co') ≫ (ρ_ G').hom = kbmρ ≫ pc := by
  subst hm hρ
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, hβ, hco]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, ← MonoidalCategory.rightUnitor_naturality]
  simp only [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

private theorem whisker_tensor_square {X B B' G : C} {a : B ⟶ B'} {β : X ⟶ G}
    {co' : B' ⟶ 𝟙_ C} {co : B ⟶ 𝟙_ C} (h : a ≫ co' = co) :
    (X ◁ a) ≫ (β ⊗ₘ co') ≫ (ρ_ G).hom = (β ⊗ₘ co) ≫ (ρ_ G).hom := by
  rw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc, h]

end Monoidal

/-! ### Sections of a pulled-back `ψ` -/

section Twisting

variable {T' T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The sections of the pulled-back `ψ` are the pulled-back sections of `ψ`.** -/
theorem sectionHom_pullback (ψ : Twisting f A d L) (k : T' ⟶ T) (i : ℤ)
    (U : (Opens S.toRingedSpace.carrier)ᵒᵖ) (a : (A.piece (i * d)).val.obj U) :
    (ψ.pullback k).sectionHom i U a =
      LaurentSections.pullbackSec k L i ((opensMap (ringedSpaceHom f)).op.obj U)
        (ψ.sectionHom i U a) :=
  (congrArg (fun z => (laurentPullback k L i).val.app
      ((opensMap (ringedSpaceHom k)).op.obj ((opensMap (ringedSpaceHom f)).op.obj U))
      ((((pullbackFunctor (ringedSpaceHom k)).map (ψ.app i)).val.app
        ((opensMap (ringedSpaceHom k)).op.obj ((opensMap (ringedSpaceHom f)).op.obj U))) z))
    (Stacks.PullbackCompMonoidal.comparison_pullbackUnit (ringedSpaceHom f) (ringedSpaceHom k)
      (A.piece (i * d)) U a)).trans
    (congrArg (fun z => (laurentPullback k L i).val.app
      ((opensMap (ringedSpaceHom k)).op.obj ((opensMap (ringedSpaceHom f)).op.obj U)) z)
      (pullbackUnit_naturality (ringedSpaceHom k) (ψ.app i)
        ((opensMap (ringedSpaceHom f)).op.obj U)
        (pullbackUnit (ringedSpaceHom f) (A.piece (i * d)) U a)))

end Twisting

/-! ### The contraction of an iterated pullback on pulled-back sections -/

section Sections

variable {T' T S : Scheme.{u}}

/-- **The contraction `(k ≫ f)^*M ⟶ k^*f^*M` carries the pullback of a section to its iterated
pullback.** -/
theorem compComparison_pullbackSection (k : T' ⟶ T) (f : T ⟶ S) (M : S.Modules) (V : S.Opens)
    (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ V) (h : (⊤ : T'.Opens) ≤ (k ≫ f) ⁻¹ᵁ V) (x : M.val.obj (op V)) :
    (compComparison k f M).val.app (op ⊤) (Scheme.Modules.pullbackSection (k ≫ f) M V ⊤ h x) =
      Scheme.Modules.pullbackSection k ((Scheme.Modules.pullback f).obj M) ⊤ ⊤ le_top
        (Scheme.Modules.pullbackSection f M V ⊤ hf x) := by
  unfold Scheme.Modules.pullbackSection
  refine (PresheafOfModules.naturality_apply (compComparison k f M).val (homOfLE h).op _).trans ?_
  refine (congrArg (fun z => ((pullbackFunctor (ringedSpaceHom k)).obj
      ((pullbackFunctor (ringedSpaceHom f)).obj M)).val.map (homOfLE h).op z)
    (Stacks.PullbackCompMonoidal.comparison_pullbackUnit (ringedSpaceHom f) (ringedSpaceHom k)
      M (op V) x)).trans ?_
  have hr := pullbackUnit_restrict (ringedSpaceHom k) ((pullbackFunctor (ringedSpaceHom f)).obj M)
    (homOfLE hf).op (pullbackUnit (ringedSpaceHom f) M (op V) x)
  refine Eq.trans ?_ (congrArg (fun z => ((pullbackFunctor (ringedSpaceHom k)).obj
      ((pullbackFunctor (ringedSpaceHom f)).obj M)).val.map (homOfLE le_top).op z) hr)
  refine Eq.trans ?_ (PresheafOfModules.map_comp_apply _ _ _ _)
  exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _

/-- **The contraction of an iterated pullback is the inverse of Mathlib's composition law for the
pullback of sheaves of modules on schemes.** Both are morphisms out of a pullback, and both carry
the image of a local section under the unit to its iterated image. -/
theorem compComparison_eq_pullbackComp_inv (k : T' ⟶ T) (f : T ⟶ S) (M : S.Modules) :
    compComparison k f M = (Scheme.Modules.pullbackComp k f).inv.app M := by
  refine pullback_hom_ext (ringedSpaceHom (k ≫ f)) fun U m => ?_
  refine (Stacks.PullbackCompMonoidal.comparison_pullbackUnit (ringedSpaceHom f)
    (ringedSpaceHom k) M U m).trans ?_
  exact (Scheme.Modules.pullbackComp_inv_unit k f M U.unop m).symm

end Sections

/-! ### The local situation along a pullback -/

section Chart

variable {s : Stacks.RelativeProj.Situation.{u}}
  (U : s.base.affineOpens) {d : ℕ} (c : s.sectionPieces U.1 d)
  {T : Scheme.{u}} (f : T ⟶ s.base) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U.1)
  (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
  (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
  {T' : Scheme.{u}} (k : T' ⟶ T)

include hf in
/-- If `T` maps into the open `U` under `f`, then so does `T'` under `k ≫ f`. -/
theorem hf_pullback : (⊤ : T'.Opens) ≤ (k ≫ f) ⁻¹ᵁ U.1 := fun _ _ => hf trivial

include hg in
/-- If `T` maps into the basic open `D₊(c)` under `g`, then so does `T'` under `k ≫ g`. -/
theorem hg_pullback :
    (⊤ : T'.Opens) ≤ (k ≫ g) ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) :=
  fun _ _ => hg trivial

/-- The function `k^♯ : Γ(T, ⊤) ⟶ Γ(T', ⊤)` precomposed with a restriction is the restriction
along the composite. -/
theorem appLE_comp_appTop {X : Scheme.{u}} (h : T ⟶ X) (V : X.Opens)
    (hV : (⊤ : T.Opens) ≤ h ⁻¹ᵁ V) (hV' : (⊤ : T'.Opens) ≤ (k ≫ h) ⁻¹ᵁ V) (r : Γ(X, V)) :
    (k ≫ h).appLE V ⊤ hV' r = k.appTop (h.appLE V ⊤ hV r) := by
  have h1 := Scheme.Hom.appLE_comp_appLE k h V ⊤ ⊤ hV le_top
  have h2 : k.appLE ⊤ ⊤ le_top = k.appTop := Scheme.Hom.appLE_preimage_self k ⊤
  rw [h2] at h1
  exact (congrArg (fun φ => φ r) h1).symm

variable {g} in
include hg in
/-- **The function `g^♯(a / c^i)` along the pullback** is the pullback of the function. -/
theorem kappaSec_pullback (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    kappaSec U c (k ≫ g) (hg_pullback U c g hg k) i a = k.appTop (kappaSec U c g hg i a) :=
  appLE_comp_appTop k g _ hg _ _

variable {f g} in
/-- **The base identity along the pullback.** -/
theorem hgf_pullback
    (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
      f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))
    (r : s.base.ringCatSheaf.obj.obj (op U.1)) :
    (k ≫ f).appLE U.1 ⊤ (hf_pullback U f hf k) r =
      (k ≫ g).appLE _ ⊤ (hg_pullback U c g hg k) (Proj.awayToSection _ _ (baseFrac U c r)) :=
  (appLE_comp_appTop k f U.1 hf _ r).trans
    ((congrArg k.appTop (hgf r)).trans (appLE_comp_appTop k g _ hg _ _).symm)

variable {f g}

section Beta

variable (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))

/-- **The comparison `β_m : f^*ℳ_{md} ⟶ g^*ℳ̃(U)` along a pullback** is the pullback of `β_m`,
read through the contraction `(k ≫ f)^* ⟶ k^*f^*` and the composition law
`k^*g^* ≅ (k ≫ g)^*`. -/
theorem beta_pullback (m : ℤ) :
    beta ℳ U c (k ≫ f) (hf_pullback U f hf k) (k ≫ g) (hg_pullback U c g hg k)
        (hgf_pullback U c hf hg k hgf) m =
      compComparison k f (ℳ.piece (m * d)) ≫
        (Scheme.Modules.pullback k).map (beta ℳ U c f hf g hg hgf m) ≫
          (Scheme.Modules.pullbackComp k g).hom.app (moduleChart ℳ U) := by
  refine AffineOpenHomRecovery.hom_ext (k ≫ f) U.1 (hf_pullback U f hf k) (ℳ.piece (m * d)) U.2
    _ fun x => ?_
  refine (beta_pullbackSection ℳ U c (k ≫ f) (hf_pullback U f hf k) (k ≫ g)
    (hg_pullback U c g hg k) (hgf_pullback U c hf hg k hgf) m x).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => ((Scheme.Modules.pullbackComp k g).hom.app
      (moduleChart ℳ U)).val.app (op ⊤) (((Scheme.Modules.pullback k).map
        (beta ℳ U c f hf g hg hgf m)).val.app (op ⊤) z))
    (compComparison_pullbackSection k f (ℳ.piece (m * d)) U.1 hf (hf_pullback U f hf k) x)).symm
  refine Eq.trans ?_ (congrArg (fun z => ((Scheme.Modules.pullbackComp k g).hom.app
      (moduleChart ℳ U)).val.app (op ⊤) z)
    (Scheme.Modules.pullbackSection_naturality k (beta ℳ U c f hf g hg hgf m) ⊤ ⊤ le_top
      (Scheme.Modules.pullbackSection f (ℳ.piece (m * d)) U.1 ⊤ hf x))).symm
  refine Eq.trans ?_ (congrArg (fun z => ((Scheme.Modules.pullbackComp k g).hom.app
      (moduleChart ℳ U)).val.app (op ⊤) (Scheme.Modules.pullbackSection k _ ⊤ ⊤ le_top z))
    (beta_pullbackSection ℳ U c f hf g hg hgf m x)).symm
  exact (Scheme.Modules.pullbackSection_comp k g (moduleChart ℳ U) _ ⊤ ⊤ hg le_top
    (hg_pullback U c g hg k) (fracChart ℳ U c m x)).symm

end Beta

variable {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f s.algebra (d : ℤ) L) (w : (LaurentSections.Ring L (op ⊤))ˣ)

/-- **The chart identity along the pullback**: if `ψ_i(a) = g^♯(a / c^i) · w^i` on `T`, then
`(k^*ψ)_i(a) = (k ≫ g)^♯(a / c^i) · (k^*w)^i` on `T'`. -/
theorem hCP_pullback
    (hCP : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
      ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
        (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
          LaurentSections.pw w i)
    (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
      DirectSum.of _ (-1) τ)
    (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    ((laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).piece i).val.map
        (homOfLE (hf_pullback U f hf k)).op ((ψ.pullback k).sectionHom i (op U.1) a) =
      (show (structureRingSheaf T'.toRingedSpace).obj.obj (op ⊤) from
        kappaSec U c (k ≫ g) (hg_pullback U c g hg k) i a) •
          LaurentSections.pw (LaurentSections.pullbackUnit' k L w) i := by
  have e1 := sectionHom_pullback ψ k (i : ℤ) (op U.1) a
  have e2 := LaurentSections.pullbackSec_restrict k L (i : ℤ) (homOfLE hf).op
    (ψ.sectionHom i (op U.1) a)
  have e3 := LaurentSections.pullbackSec_smul k L (i : ℤ) (op ⊤) (kappaSec U c g hg i a)
    (LaurentSections.pw w i)
  have e4 := LaurentSections.pw_pullbackUnit' k L w hw hw' (i : ℤ)
  have e5 := kappaSec_pullback U c hg k i a
  refine (congrArg _ e1).trans (e2.trans ((congrArg _ (hCP i a)).trans (e3.trans ?_)))
  rw [e4, e5]
  rfl

variable (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))

/-- **The degree-`n` member `b_n` of the local comparison along a pullback**: the comparison of
the summands of Tag 01O6 followed by `b_n` for the pulled-back datum is the pullback of `b_n`
followed by the composition law `k^*g^* ≅ (k ≫ g)^*`. -/
theorem bmap_pullback (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
      DirectSum.of _ (-1) τ) (n : ℤ) :
    summandPullback (ℳ.toGradedModule s.mul_comm) (d : ℤ) L k n ≫
        bmap ℳ U c (k ≫ f) (hf_pullback U f hf k) (k ≫ g) (hg_pullback U c g hg k)
          (hgf_pullback U c hf hg k hgf) (LaurentSections.pullbackUnit' k L w) n =
      (pullbackFunctor (ringedSpaceHom k)).map (bmap ℳ U c f hf g hg hgf w n) ≫
        (Scheme.Modules.pullbackComp k g).hom.app (moduleChart ℳ U) := by
  have hβ : inv (compComparison k f (ℳ.piece (n * d))) ≫
      betaS ℳ U c (k ≫ f) (hf_pullback U f hf k) (k ≫ g) (hg_pullback U c g hg k)
        (hgf_pullback U c hf hg k hgf) n =
      (pullbackFunctor (ringedSpaceHom k)).map (betaS ℳ U c f hf g hg hgf n) ≫
        (Scheme.Modules.pullbackComp k g).hom.app (moduleChart ℳ U) :=
    (IsIso.inv_comp_eq (compComparison k f (ℳ.piece (n * d)))).mpr
      (beta_pullback U c hf hg k ℳ hgf n)
  have hco := LaurentSections.coord_pullback k L w hw hw' n
  have hnat := pullbackTensorComparison_naturality_tensorHom (ringedSpaceHom k)
      (betaS ℳ U c f hf g hg hgf n) (LaurentSections.coord w n)
  have hρ := pullbackTensorComparison_rightUnitor (ringedSpaceHom k) (tgt ℳ U g)
  have hm := (pullbackFunctor (ringedSpaceHom k)).map_comp
    (betaS ℳ U c f hf g hg hgf n ⊗ₘ LaurentSections.coord w n) (ρ_ (tgt ℳ U g)).hom
  have key := bmap_square hm hnat hρ hβ hco
  exact key

/-- **A local comparison along a pullback.** If `φ : ℳ̃_T ⟶ g^*ℳ̃(U)` is `b_n` on the degreewise
pure tensors, then a morphism `χ : ℳ̃_{T'} ⟶ (k ≫ g)^*ℳ̃(U)` which is `b_n` for the pulled-back
datum on the pure tensors is the pullback of `φ`, read through `k^*ℳ̃_T ≅ ℳ̃_{T'}` and
`k^*g^* ≅ (k ≫ g)^*`. -/
theorem eq_of_pureTensor_bmap_pullback
    (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
      DirectSum.of _ (-1) τ)
    (φ : Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) ψ ⟶ tgt ℳ U g)
    (hφ : ∀ n : ℤ, Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ n ≫ φ =
      bmap ℳ U c f hf g hg hgf w n)
    (χ : Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) (ψ.pullback k) ⟶
      tgt ℳ U (k ≫ g))
    (hχ : ∀ n : ℤ, Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) (ψ.pullback k) n ≫ χ =
      bmap ℳ U c (k ≫ f) (hf_pullback U f hf k) (k ≫ g) (hg_pullback U c g hg k)
        (hgf_pullback U c hf hg k hgf) (LaurentSections.pullbackUnit' k L w) n) :
    χ = (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L k ψ).inv ≫
      (pullbackFunctor (ringedSpaceHom k)).map φ ≫
        (Scheme.Modules.pullbackComp k g).hom.app (moduleChart ℳ U) := by
  rw [Iso.eq_inv_comp]
  refine pullback_associatedSheaf_hom_ext (ℳ.toGradedModule s.mul_comm) (d : ℤ) L k ψ fun n => ?_
  rw [← Category.assoc, associatedSheafPullbackIso_pureTensor, Category.assoc, hχ,
    bmap_pullback U c hf hg k w ℳ hgf hw hw' n]
  exact congrArg (· ≫ (Scheme.Modules.pullbackComp k g).hom.app (moduleChart ℳ U))
    ((congrArg (pullbackFunctor (ringedSpaceHom k)).map (hφ n)).symm.trans
      ((pullbackFunctor (ringedSpaceHom k)).map_comp _ _)) |>.trans (Category.assoc _ _ _)

/-! ### The local situation along an isomorphism of invertible modules -/

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr (congrIso) in
/-- **The chart identity along an isomorphism `e : L ≅ L'` carrying `ψ` to `ψ'`**, with the unit
transported along `e`. -/
theorem hCP_congr {L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
    (e : L ≅ L') (ψ' : Twisting f s.algebra (d : ℤ) L')
    (hψ : ∀ n : ℤ, ψ.app n ≫ (congrIso e n).hom = ψ'.app n)
    (hCP : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
      ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
        (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
          LaurentSections.pw w i)
    (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
      DirectSum.of _ (-1) τ)
    (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    ((laurent L').piece i).val.map (homOfLE hf).op (ψ'.sectionHom i (op U.1) a) =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
        LaurentSections.pw (LaurentSections.congrUnit e w) i := by
  have e1 : ψ'.sectionHom i (op U.1) a =
      (congrIso e i).hom.val.app _ (ψ.sectionHom i (op U.1) a) :=
    (congrArg (fun φ => φ.val.app ((opensMap (ringedSpaceHom f)).op.obj (op U.1))
      (pullbackUnit (ringedSpaceHom f) _ (op U.1) a)) (hψ i)).symm
  have e2 := PresheafOfModules.naturality_apply (congrIso e (i : ℤ)).hom.val (homOfLE hf).op
    (ψ.sectionHom i (op U.1) a)
  have e4 := LaurentSections.pw_congrUnit e w hw hw' (i : ℤ)
  refine (congrArg (fun z => ((laurent L').piece i).val.map (homOfLE hf).op z) e1).trans ?_
  refine e2.symm.trans ?_
  refine (congrArg (fun z => (congrIso e (i : ℤ)).hom.val.app (op ⊤) z) (hCP i a)).trans ?_
  refine (map_smul _ _ _).trans ?_
  exact congrArg (fun z => (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from
    kappaSec U c g hg i a) • z) e4.symm

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr (congrIso) in
/-- **The degree-`n` member `b_n` along an isomorphism `e : L ≅ L'`**: precomposed with
`x ⊗ l ↦ x ⊗ e(l)`, the member for the transported unit is the member for `w`. -/
theorem bmap_congr {L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
    (e : L ≅ L')
    (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
      DirectSum.of _ (-1) τ) (n : ℤ) :
    summandMap (ℳ.toGradedModule s.mul_comm) (fun m => (congrIso e m).hom) n ≫
        bmap ℳ U c f hf g hg hgf (LaurentSections.congrUnit e w) n =
      bmap ℳ U c f hf g hg hgf w n :=
  whisker_tensor_square (LaurentSections.coord_congr e w hw hw' n)

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr (congrIso) in
/-- **A local comparison along an isomorphism `e : L ≅ L'` carrying `ψ` to `ψ'`.** If `φ` is `b_n`
on the pure tensors for `w`, and `χ` is `b_n` on the pure tensors of `ψ'` for the transported
unit, then `χ` is `φ` read through the induced isomorphism `ℳ̃_T(ψ) ≅ ℳ̃_T(ψ')`. -/
theorem eq_of_pureTensor_bmap_congr {L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
    (e : L ≅ L') (ψ' : Twisting f s.algebra (d : ℤ) L')
    (hψ : ∀ n : ℤ, ψ.app n ≫ (congrIso e n).hom = ψ'.app n)
    (hw : ∃ σ, (w : LaurentSections.Ring L (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (LaurentSections.Ring L (op ⊤))ˣ) : LaurentSections.Ring L (op ⊤)) =
      DirectSum.of _ (-1) τ)
    (φ : Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) ψ ⟶ tgt ℳ U g)
    (hφ : ∀ n : ℤ, Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ n ≫ φ =
      bmap ℳ U c f hf g hg hgf w n)
    (χ : Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) ψ' ⟶ tgt ℳ U g)
    (hχ : ∀ n : ℤ, Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) ψ' n ≫ χ =
      bmap ℳ U c f hf g hg hgf (LaurentSections.congrUnit e w) n) :
    φ = (associatedSheafCongrIso (ℳ.toGradedModule s.mul_comm) ψ ψ' e hψ).hom ≫ χ :=
  Twisting.associatedSheaf_hom_ext (ℳ.toGradedModule s.mul_comm) ψ fun n =>
    (hφ n).trans ((bmap_congr U c hf hg w ℳ hgf e hw hw' n).symm.trans
      ((congrArg (summandMap (ℳ.toGradedModule s.mul_comm) (fun m => (congrIso e m).hom) n ≫ ·)
        (hχ n).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ χ) (pureTensor_associatedSheafCongrIso_hom (ℳ.toGradedModule s.mul_comm)
          ψ ψ' e hψ n).symm).trans (Category.assoc _ _ _)))))

end Chart

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
