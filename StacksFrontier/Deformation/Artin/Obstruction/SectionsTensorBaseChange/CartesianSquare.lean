module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsBaseChangeData
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsThickeningSequence

/-!
# The direct image to `W` of `𝓕_A ⊗_A M`: the identification at a cartesian square

Two abstract lemmas on chains of tensor isomorphisms (`tensorChain_change`,
`tensorChain_thickening`), the identification `tensorBaseChangeIsoGen` of
`p_*(𝓕_A ⊗_A M)` with `𝓕 ⊗_Λ M` at an arbitrary cartesian square over `Spec φ`, and the
change of the base ring `restrictScalarsHomOfComp`.

See `StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange` for the overview.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Prod TensorProduct

universe u

namespace Deformation.Artin.SectionsSheaf

/-! ### Two abstract lemmas -/

section Abstract

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]

/-- A functor on a product category preserves composition in the first factor. -/
private theorem map_comp_prod_id (L : 𝒞 × 𝒞 ⥤ 𝒞) (Q : 𝒞) {Y₁ Y₂ Y₃ : 𝒞} (x : Y₁ ⟶ Y₂)
    (y : Y₂ ⟶ Y₃) : L.map ((x ≫ y) ×ₘ 𝟙 Q) = L.map (x ×ₘ 𝟙 Q) ≫ L.map (y ×ₘ 𝟙 Q) := by
  rw [← L.map_comp]
  congr 1
  exact Prod.hom_ext rfl (by simp)

/-- **Naturality of a chain `L(u × 1) ≫ P`, in the abstract**: a first-factor arrow `u` natural
along `a` and `v`, followed by a map `P` natural in the first factor, is natural. The arrows
`e₁`, `e₁'`, `e₂`, `e₂'` are transports between two spellings of one object, constrained to be
identities, so that each spelling comparison is made once, where the lemma is applied. -/
theorem tensorChain_comp_naturality (L : 𝒞 × 𝒞 ⥤ 𝒞) (L' : 𝒟 × 𝒟 ⥤ 𝒟) (G : 𝒟 ⥤ 𝒞)
    {U U₁ Q : 𝒞} {V V₁ Q₁ : 𝒟}
    (a : U ⟶ U₁) (v : V ⟶ V₁) (u : U ⟶ G.obj V) (u₁ : U₁ ⟶ G.obj V₁)
    (P : L.obj (G.obj V, Q) ⟶ G.obj (L'.obj (V, Q₁)))
    (P₁ : L.obj (G.obj V₁, Q) ⟶ G.obj (L'.obj (V₁, Q₁)))
    (e₁ : L.obj (U, Q) ⟶ L.obj (U, Q)) (e₁' : L.obj (U₁, Q) ⟶ L.obj (U₁, Q))
    (e₂ : L'.obj (V, Q₁) ⟶ L'.obj (V, Q₁)) (e₂' : L'.obj (V₁, Q₁) ⟶ L'.obj (V₁, Q₁))
    (he₁ : e₁ = 𝟙 _) (he₁' : e₁' = 𝟙 _) (he₂ : e₂ = 𝟙 _) (he₂' : e₂' = 𝟙 _)
    (hu : a ≫ u₁ = u ≫ G.map v)
    (hP : L.map (G.map v ×ₘ 𝟙 Q) ≫ P₁ = P ≫ G.map (L'.map (v ×ₘ 𝟙 Q₁))) :
    L.map (a ×ₘ 𝟙 Q) ≫ (e₁' ≫ L.map (u₁ ×ₘ 𝟙 Q) ≫ P₁ ≫ G.map e₂') =
      (e₁ ≫ L.map (u ×ₘ 𝟙 Q) ≫ P ≫ G.map e₂) ≫ G.map (L'.map (v ×ₘ 𝟙 Q₁)) := by
  subst he₁ he₁' he₂ he₂'
  have h₁ : L.map (a ×ₘ 𝟙 Q) ≫ L.map (u₁ ×ₘ 𝟙 Q) =
      L.map (u ×ₘ 𝟙 Q) ≫ L.map (G.map v ×ₘ 𝟙 Q) := by
    rw [← map_comp_prod_id, ← map_comp_prod_id, hu]
  simp only [Category.id_comp, G.map_id, Category.comp_id]
  rw [← Category.assoc, h₁, Category.assoc, hP, Category.assoc]

/-- Naturality of the forward maps of a family of isomorphisms, from naturality of the inverse
maps. -/
theorem hom_naturality_of_inv_naturality {X Y X' Y' : 𝒞} (e : X ≅ Y) (e' : X' ≅ Y')
    (f : X ⟶ X') (f' : Y ⟶ Y') (h : f' ≫ e'.inv = e.inv ≫ f) :
    f ≫ e'.hom = e.hom ≫ f' := by
  rw [← cancel_epi e.inv, ← Category.assoc, ← h, Category.assoc, e'.inv_hom_id, e.inv_hom_id_assoc,
    Category.comp_id]

/-- **A chain `L(f × 1) ≫ P ≫ G(M(ν × 1) ≫ lam)`, contracted**: by naturality `hn` of the
projection-formula maps along `ν`, it is `L((f ≫ G ν) × 1) ≫ PO ≫ G lam`. The arrows `e₁`, `e₂`
stand for transports between two spellings of one object and are constrained to be identities. -/
theorem tensorChain_contract (L : 𝒞 × 𝒞 ⥤ 𝒞) (M : 𝒟 × 𝒟 ⥤ 𝒟) (G : 𝒟 ⥤ 𝒞)
    {U Q : 𝒞} {V O QX : 𝒟} (f : U ⟶ G.obj V) (ν : V ⟶ O)
    (P : L.obj (G.obj V, Q) ⟶ G.obj (M.obj (V, QX)))
    (PO : L.obj (G.obj O, Q) ⟶ G.obj (M.obj (O, QX))) (lam : M.obj (O, QX) ⟶ QX)
    (e₁ : L.obj (U, Q) ⟶ L.obj (U, Q)) (e₂ : M.obj (V, QX) ⟶ M.obj (V, QX))
    (he₁ : e₁ = 𝟙 _) (he₂ : e₂ = 𝟙 _)
    (θ : L.obj (U, Q) ⟶ G.obj QX) (uh : M.obj (V, QX) ⟶ QX)
    (hθ : θ = (e₁ ≫ L.map (f ×ₘ 𝟙 Q) ≫ P ≫ G.map e₂) ≫ G.map uh)
    (huh : uh = M.map (ν ×ₘ 𝟙 QX) ≫ lam)
    (hn : L.map (G.map ν ×ₘ 𝟙 Q) ≫ PO = P ≫ G.map (M.map (ν ×ₘ 𝟙 QX))) :
    θ = L.map ((f ≫ G.map ν) ×ₘ 𝟙 Q) ≫ PO ≫ G.map lam := by
  subst he₁ he₂ hθ huh
  simp only [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [map_comp_prod_id, Category.assoc, reassoc_of% hn]

/-- **The degree-zero change of base, in the abstract**: two contracted chains whose first
factors are related by `hU` and projection formulas by `hK` satisfy `L(a × 1) ≫ θ' = θ ≫ r`. -/
theorem tensorChain_change {ℰ : Type*} [Category ℰ]
    (L : 𝒞 × 𝒞 ⥤ 𝒞) (N : ℰ × ℰ ⥤ ℰ) (G : 𝒟 ⥤ 𝒞) (G' : ℰ ⥤ 𝒞)
    {U U' Q : 𝒞} {O QX : 𝒟} {O' QX' : ℰ} (M : 𝒟 × 𝒟 ⥤ 𝒟)
    (a : U ⟶ U') (ρ : U ⟶ G.obj O) (ρ' : U' ⟶ G'.obj O')
    (PO : L.obj (G.obj O, Q) ⟶ G.obj (M.obj (O, QX)))
    (PO' : L.obj (G'.obj O', Q) ⟶ G'.obj (N.obj (O', QX')))
    (lam : M.obj (O, QX) ⟶ QX) (lam' : N.obj (O', QX') ⟶ QX')
    (b : G.obj O ⟶ G'.obj O') (r : G.obj QX ⟶ G'.obj QX')
    (θ : L.obj (U, Q) ⟶ G.obj QX) (θ' : L.obj (U', Q) ⟶ G'.obj QX')
    (hθ : θ = L.map (ρ ×ₘ 𝟙 Q) ≫ PO ≫ G.map lam)
    (hθ' : θ' = L.map (ρ' ×ₘ 𝟙 Q) ≫ PO' ≫ G'.map lam')
    (hU : a ≫ ρ' = ρ ≫ b)
    (hK : L.map (b ×ₘ 𝟙 Q) ≫ PO' ≫ G'.map lam' = PO ≫ G.map lam ≫ r) :
    L.map (a ×ₘ 𝟙 Q) ≫ θ' = θ ≫ r := by
  subst hθ hθ'
  rw [← Category.assoc, ← map_comp_prod_id, hU, map_comp_prod_id, Category.assoc, hK,
    Category.assoc, Category.assoc]

/-- **The thickening coherence, in the abstract**, for `tensorBaseChangeIsoGen_comp_inv`: two
chains `θ₀`, `θ'` and a chain `β` whose first-factor arrows are related by `hU`, whose
projection formulas are related by `hK` and `hn`, with `κ : H ⋙ G ⟶ G'` comparing the direct
images and `e₁`, `e₁'`, `E`, `E'`, `e₂ ≫ e₃` transports between two spellings of one object. -/
theorem tensorChain_thickening {ℰ : Type*} [Category ℰ]
    (L : 𝒞 × 𝒞 ⥤ 𝒞) (M' : 𝒟 × 𝒟 ⥤ 𝒟) (N : ℰ × ℰ ⥤ ℰ) (G : 𝒟 ⥤ 𝒞) (H : ℰ ⥤ 𝒟)
    (G' : ℰ ⥤ 𝒞) (κ : H ⋙ G ⟶ G')
    {U₀ U₀' Q : 𝒞} {V₀ QX' Y₀ : 𝒟} {G₀ I' QX Z : ℰ}
    (a : U₀ ⟶ U₀') (f₀ : U₀ ⟶ G.obj V₀) (f' : U₀' ⟶ G'.obj G₀) (w : V₀ ⟶ H.obj G₀)
    (P₀ : L.obj (G.obj V₀, Q) ⟶ G.obj (M'.obj (V₀, QX')))
    (PO : L.obj (G.obj (H.obj G₀), Q) ⟶ G.obj (M'.obj (H.obj G₀, QX')))
    (Pi Pi' : M'.obj (H.obj G₀, QX') ⟶ H.obj (N.obj (G₀, I')))
    (P' : L.obj (G'.obj G₀, Q) ⟶ G'.obj (N.obj (G₀, QX)))
    (eF : I' ⟶ QX)
    (e₁ E : L.obj (U₀, Q) ⟶ L.obj (U₀, Q)) (e₁' E' : L.obj (U₀', Q) ⟶ L.obj (U₀', Q))
    (e₂ : M'.obj (V₀, QX') ⟶ Y₀) (e₃ : Y₀ ⟶ M'.obj (V₀, QX')) (e₄ : N.obj (G₀, QX) ⟶ Z)
    (he₁ : e₁ = 𝟙 _) (he₁' : e₁' = 𝟙 _) (hE : E = 𝟙 _) (hE' : E' = 𝟙 _)
    (he₂₃ : e₂ ≫ e₃ = 𝟙 _)
    (c : L.obj (U₀, Q) ⟶ L.obj (U₀', Q)) (θ₀ : L.obj (U₀, Q) ⟶ G.obj Y₀)
    (θ' : L.obj (U₀', Q) ⟶ G'.obj Z) (β : Y₀ ⟶ H.obj Z)
    (hc : c = E ≫ L.map (a ×ₘ 𝟙 Q) ≫ E')
    (hθ₀ : θ₀ = e₁ ≫ L.map (f₀ ×ₘ 𝟙 Q) ≫ P₀ ≫ G.map e₂)
    (hθ' : θ' = e₁' ≫ L.map (f' ×ₘ 𝟙 Q) ≫ P' ≫ G'.map e₄)
    (hβ : β = e₃ ≫ M'.map (w ×ₘ 𝟙 QX') ≫ Pi' ≫ H.map (N.map (𝟙 G₀ ×ₘ eF)) ≫ H.map e₄)
    (hPi : Pi' = Pi)
    (hn : L.map (G.map w ×ₘ 𝟙 Q) ≫ PO = P₀ ≫ G.map (M'.map (w ×ₘ 𝟙 QX')))
    (hU : a ≫ f' = f₀ ≫ G.map w ≫ κ.app G₀)
    (hK : L.map (κ.app G₀ ×ₘ 𝟙 Q) ≫ P' =
      PO ≫ G.map Pi ≫ G.map (H.map (N.map (𝟙 G₀ ×ₘ eF))) ≫ κ.app (N.obj (G₀, QX))) :
    c ≫ θ' = θ₀ ≫ G.map β ≫ κ.app Z := by
  subst he₁ he₁' hE hE' hc hθ₀ hθ' hβ hPi
  have h1 : L.map (a ×ₘ 𝟙 Q) ≫ L.map (f' ×ₘ 𝟙 Q) =
      L.map (f₀ ×ₘ 𝟙 Q) ≫ L.map (G.map w ×ₘ 𝟙 Q) ≫ L.map (κ.app G₀ ×ₘ 𝟙 Q) := by
    rw [← map_comp_prod_id, hU, map_comp_prod_id, map_comp_prod_id]
  have h2 : G.map e₂ ≫ G.map e₃ = 𝟙 _ := by
    rw [← G.map_comp, he₂₃, CategoryTheory.Functor.map_id]
  have h3 : G.map (H.map e₄) ≫ κ.app Z = κ.app (N.obj (G₀, QX)) ≫ G'.map e₄ :=
    κ.naturality e₄
  simp only [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% h1, reassoc_of% hK, reassoc_of% h2, ← reassoc_of% hn, h3]

/-- The forward map of an isomorphism, from an equation of inverse maps; `e` is a transport
between two spellings of one object, constrained to be the identity. -/
theorem hom_eq_of_comp_inv_eq {X₀ Y₀ X₁ X₂ Y₁ : 𝒞} (γ₀ : X₀ ≅ Y₀) (γ' : X₂ ≅ Y₁)
    (c : Y₀ ⟶ Y₁) (k₁ : X₀ ≅ X₁) (k₂ : X₁ ≅ X₂) (e : X₂ ⟶ X₂) (he : e = 𝟙 _)
    (h : c ≫ γ'.inv = γ₀.inv ≫ k₁.hom ≫ k₂.hom) :
    γ'.hom = (e ≫ k₂.inv) ≫ k₁.inv ≫ γ₀.hom ≫ c := by
  subst he
  have e' : k₂.inv ≫ k₁.inv ≫ γ₀.hom ≫ c ≫ γ'.inv = 𝟙 _ := by
    rw [h, γ₀.hom_inv_id_assoc, k₁.inv_hom_id_assoc, k₂.inv_hom_id]
  calc γ'.hom = (k₂.inv ≫ k₁.inv ≫ γ₀.hom ≫ c ≫ γ'.inv) ≫ γ'.hom := by
        rw [e', Category.id_comp]
    _ = (𝟙 _ ≫ k₂.inv) ≫ k₁.inv ≫ γ₀.hom ≫ c := by simp

end Abstract

/-! ### The identification at a cartesian square -/

section Gen

variable {Λ A : CommRingCat.{u}} (φ : Λ ⟶ A) {W X : Scheme.{u}} {g : W ⟶ Spec Λ}
  {π : X ⟶ Spec A} {p : X ⟶ W} (h : IsPullback π p (Spec.map φ) g)

include h in
/-- The projection `p` of a cartesian square over `Spec φ` is affine, being a base change of a
morphism of affine schemes. -/
theorem isAffineHom_of_isPullback : IsAffineHom p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback h inferInstance

/-- **The first tensor factor**, `g^*(M|_Λ)~ ≅ p_* π^* M̃`: [Stacks, Tag 01I9] followed by affine
base change. -/
def tensorBaseChangeFirstIso (M : ModuleCat.{u} A) :
    (Scheme.Modules.pullback g).obj
        ((tilde.functor Λ).obj ((ModuleCat.restrictScalars φ.hom).obj M)) ≅
      (Scheme.Modules.pushforward p).obj
        ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M)) :=
  (Scheme.Modules.pullback g).mapIso (tildePushforwardIso φ M).symm ≪≫
    affineBaseChangeIsoGen φ g π p h ((tilde.functor A).obj M)

/-- `tensorBaseChangeFirstIso` on `hom`. -/
theorem tensorBaseChangeFirstIso_hom (M : ModuleCat.{u} A) :
    (tensorBaseChangeFirstIso φ h M).hom =
      (Scheme.Modules.pullback g).map (tildePushforwardIso φ M).inv ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans h.w).app
          ((tilde.functor A).obj M) :=
  rfl

/-- `tensorBaseChangeFirstIso` is natural in the module. -/
theorem tensorBaseChangeFirstIso_hom_naturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (Scheme.Modules.pullback g).map
        ((tilde.functor Λ).map ((ModuleCat.restrictScalars φ.hom).map f)) ≫
        (tensorBaseChangeFirstIso φ h N).hom =
      (tensorBaseChangeFirstIso φ h M).hom ≫
        (Scheme.Modules.pushforward p).map
          ((Scheme.Modules.pullback π).map ((tilde.functor A).map f)) := by
  have hnat : (tilde.functor Λ).map ((ModuleCat.restrictScalars φ.hom).map f) ≫
      (tildePushforwardIso φ N).inv =
      (tildePushforwardIso φ M).inv ≫
        (Scheme.Modules.pushforward (Spec.map φ)).map ((tilde.functor A).map f) :=
    (pushforwardTildeIso Λ A φ).inv.naturality f
  rw [tensorBaseChangeFirstIso_hom, tensorBaseChangeFirstIso_hom, ← Category.assoc,
    ← Functor.map_comp, hnat, Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans h.w).naturality
    ((tilde.functor A).map f)

variable (F : W.Modules) [F.IsQuasicoherent]

/-- **The projection formula along `p`**, `p_* G ⊗ 𝓕 ≅ p_*(G ⊗ p^* 𝓕)` for quasi-coherent `G`
and `𝓕`. This is [Stacks, Tag 0FZE] for the affine morphism `p`. -/
def projectionFormulaIsoOfIsPullback (G : X.Modules) (hG : G.IsQuasicoherent) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))).obj
        ((Scheme.Modules.pushforward p).obj G, F) ≅
      (Scheme.Modules.pushforward p).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))).obj
          (G, (Scheme.Modules.pullback p).obj F)) :=
  haveI := isAffineHom_of_isPullback φ h
  Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent p G F hG
    inferInstance

/-- `projectionFormulaIsoOfIsPullback` is the canonical projection-formula morphism, the
abstract `CategoryTheory.adjunctionTensorMap` of the adjunction `p^* ⊣ p_*` and the comparison
of [Stacks, Tag 01CD]. -/
theorem projectionFormulaIsoOfIsPullback_hom (G : X.Modules) (hG : G.IsQuasicoherent) :
    (projectionFormulaIsoOfIsPullback φ h F G hG).hom =
      adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)))
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)))
        (Stacks.RingedSpace.comparisonNatTrans p.toLRSHom.toShHom) G F :=
  (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq p G F).trans rfl

/-- `projectionFormulaIsoOfIsPullback` is natural in the first factor. -/
theorem projectionFormulaIsoOfIsPullback_hom_naturality {G G' : X.Modules}
    (hG : G.IsQuasicoherent) (hG' : G'.IsQuasicoherent) (k : G ⟶ G') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))).map
          ((Scheme.Modules.pushforward p).map k ×ₘ 𝟙 F) ≫
        (projectionFormulaIsoOfIsPullback φ h F G' hG').hom =
      (projectionFormulaIsoOfIsPullback φ h F G hG).hom ≫
        (Scheme.Modules.pushforward p).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))).map
            (k ×ₘ 𝟙 ((Scheme.Modules.pullback p).obj F))) := by
  rw [projectionFormulaIsoOfIsPullback_hom, projectionFormulaIsoOfIsPullback_hom]
  have e := adjunctionTensorMap_natural (Scheme.Modules.pullbackPushforwardAdjunction p)
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)))
    (Stacks.RingedSpace.comparisonNatTrans p.toLRSHom.toShHom) k (𝟙 F)
  rw [CategoryTheory.Functor.map_id] at e
  exact e

/-- **`p_*(𝓕_A ⊗_A M) ≅ 𝓕 ⊗_Λ M` at a cartesian square over `Spec φ`**, for `𝓕_A = p^* 𝓕`: the
inverse of the projection formula along `p`, followed by the inverse of
`tensorBaseChangeFirstIso` in the first tensor factor. -/
def tensorBaseChangeIsoGen (M : ModuleCat.{u} A) :
    (Scheme.Modules.pushforward p).obj
        ((tensorSheafFunctor π ((Scheme.Modules.pullback p).obj F)).obj M) ≅
      (tensorSheafFunctor g F).obj ((ModuleCat.restrictScalars φ.hom).obj M) :=
  (Scheme.Modules.pushforward p).mapIso (eqToIso (tensorSheafFunctor_obj_eq π _ M)) ≪≫
    (projectionFormulaIsoOfIsPullback φ h F
      ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M))
      (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback π _)).symm ≪≫
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))).mapIso
      (Iso.prod (tensorBaseChangeFirstIso φ h M).symm (Iso.refl F)) ≪≫
    eqToIso (tensorSheafFunctor_obj_eq g F _).symm

/-- `tensorBaseChangeIsoGen` on `inv`, as the composite of the arrows it is built from: the first
tensor factor, the projection formula, and the two transports between the spellings of the
tensor product, which are identities. -/
theorem tensorBaseChangeIsoGen_inv (M : ModuleCat.{u} A) :
    (tensorBaseChangeIsoGen φ h F M).inv =
      eqToHom (tensorSheafFunctor_obj_eq g F ((ModuleCat.restrictScalars φ.hom).obj M)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))).map
          ((tensorBaseChangeFirstIso φ h M).hom ×ₘ 𝟙 F) ≫
        (projectionFormulaIsoOfIsPullback φ h F
          ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M))
          (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback π _)).hom ≫
        (Scheme.Modules.pushforward p).map
          (eqToHom (tensorSheafFunctor_obj_eq π ((Scheme.Modules.pullback p).obj F) M).symm) :=
  rfl

/-- **`tensorBaseChangeIsoGen` is natural in the module**, read on `inv`. -/
theorem tensorBaseChangeIsoGen_inv_naturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (tensorSheafFunctor g F).map ((ModuleCat.restrictScalars φ.hom).map f) ≫
        (tensorBaseChangeIsoGen φ h F N).inv =
      (tensorBaseChangeIsoGen φ h F M).inv ≫
        (Scheme.Modules.pushforward p).map
          ((tensorSheafFunctor π ((Scheme.Modules.pullback p).obj F)).map f) := by
  have hbase : (tensorSheafFunctor g F).map ((ModuleCat.restrictScalars φ.hom).map f) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((Scheme.Modules.pullback g).map
          ((tilde.functor Λ).map ((ModuleCat.restrictScalars φ.hom).map f)) ×ₘ 𝟙 F) :=
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩
      ((Scheme.Modules.pullback g).map
        ((tilde.functor Λ).map ((ModuleCat.restrictScalars φ.hom).map f))) (𝟙 F)).symm
  have hfibre : (tensorSheafFunctor π ((Scheme.Modules.pullback p).obj F)).map f =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        ((Scheme.Modules.pullback π).map ((tilde.functor A).map f) ×ₘ
          𝟙 ((Scheme.Modules.pullback p).obj F)) :=
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩
      ((Scheme.Modules.pullback π).map ((tilde.functor A).map f))
      (𝟙 ((Scheme.Modules.pullback p).obj F))).symm
  rw [tensorBaseChangeIsoGen_inv, tensorBaseChangeIsoGen_inv, hbase, hfibre]
  exact tensorChain_comp_naturality
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))) (Scheme.Modules.pushforward p)
    ((Scheme.Modules.pullback g).map
      ((tilde.functor Λ).map ((ModuleCat.restrictScalars φ.hom).map f)))
    ((Scheme.Modules.pullback π).map ((tilde.functor A).map f)) _ _ _ _ _ _ _ _
    (eqToHom_refl _ _) (eqToHom_refl _ _) (eqToHom_refl _ _) (eqToHom_refl _ _)
    (tensorBaseChangeFirstIso_hom_naturality φ h f)
    (projectionFormulaIsoOfIsPullback_hom_naturality φ h F _ _ _)

/-- **`tensorBaseChangeIsoGen` is natural in the module.** -/
theorem tensorBaseChangeIsoGen_hom_naturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (Scheme.Modules.pushforward p).map
        ((tensorSheafFunctor π ((Scheme.Modules.pullback p).obj F)).map f) ≫
        (tensorBaseChangeIsoGen φ h F N).hom =
      (tensorBaseChangeIsoGen φ h F M).hom ≫
        (tensorSheafFunctor g F).map ((ModuleCat.restrictScalars φ.hom).map f) :=
  hom_naturality_of_inv_naturality _ _ _ _ (tensorBaseChangeIsoGen_inv_naturality φ h F f)

end Gen

/-! ### Change of the base ring -/

section RestrictScalars

variable {Λ A A' : CommRingCat.{u}} {φ : Λ ⟶ A} {φ' : Λ ⟶ A'}

/-- **A ring map under `Λ`, as a map of `Λ`-modules.** For `ψ : A ⟶ A'` with `φ ≫ ψ = φ'`, the
map `ψ : A → A'` is `Λ`-linear when `A` and `A'` are regarded as `Λ`-modules along `φ` and
`φ'`. -/
def restrictScalarsHomOfComp (ψ : A ⟶ A') (hψ : φ ≫ ψ = φ') :
    (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A) ⟶
      (ModuleCat.restrictScalars φ'.hom).obj (ModuleCat.of A' A') :=
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A))
    (Y := (ModuleCat.restrictScalars φ'.hom).obj (ModuleCat.of A' A'))
    { toFun := ψ.hom
      map_add' := map_add _
      map_smul' := fun r x => by
        subst hψ
        exact map_mul ψ.hom (φ.hom r) x }

/-- `restrictScalarsHomOfComp` is `ψ` on elements. -/
@[simp]
theorem restrictScalarsHomOfComp_apply (ψ : A ⟶ A') (hψ : φ ≫ ψ = φ') (a : A) :
    (restrictScalarsHomOfComp ψ hψ).hom a = ψ a :=
  rfl

end RestrictScalars

/-- For a morphism `Spec A' → Spec A` of schemes over `Spec Λ` which is `Spec ψ`, the ring map
of the composite is the composite of the ring maps. -/
theorem preimage_comp_eq_of_over {Λ A A' : CommRingCat.{u}} {t : Spec A ⟶ Spec Λ}
    {t' : Spec A' ⟶ Spec Λ} (α : Over.mk t' ⟶ Over.mk t) (ψ : A ⟶ A')
    (hα : α.left = Spec.map ψ) : Spec.preimage t ≫ ψ = Spec.preimage t' :=
  Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← hα]
    exact Over.w α)

/-- `preimage_comp_eq_of_over`, read on underlying ring homomorphisms. -/
theorem preimage_hom_eq_comp {Λ A A₁ : CommRingCat.{u}} {t : Spec A ⟶ Spec Λ}
    {t₁ : Spec A₁ ⟶ Spec Λ} (α : Over.mk t₁ ⟶ Over.mk t) (φ : A ⟶ A₁)
    (hα : α.left = Spec.map φ) :
    (Spec.preimage t₁).hom = φ.hom.comp (Spec.preimage t).hom :=
  (congrArg CommRingCat.Hom.hom (preimage_comp_eq_of_over α φ hα)).symm

end Deformation.Artin.SectionsSheaf

end
