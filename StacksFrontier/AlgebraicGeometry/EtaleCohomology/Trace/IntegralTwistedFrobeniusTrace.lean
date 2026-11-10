module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistIsoTransferTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralDirectImage

/-!
# The Frobenius trace along an integral morphism, twisted by an automorphism

Let `i : Z ⟶ Y` be an integral morphism of schemes over a finite field `k`, `σ : Z ⟶ Z` a
morphism over `Y` (so `σ ≫ i = i`), `M` a bounded below complex of sheaves of `Λ`-modules on
`Z_étale` and `ε : M ⟶ σ_* M`.  Then `i_*(ε)`, followed by `i_* σ_* = i_*`, is an endomorphism of
`i_* M`, and the canonical Frobenius of `RΓ(Y_k̄, i_* M)` composed with it has the same trace as
the endomorphism `φ^*` of `RΓ(Z_k̄, M)` for the twisted Frobenius `φ = σ̄ ≫ π̄` of `Z_k̄`:

`Tr(π_Y^* ∘ i_*(ε) | RΓ(Y_k̄, i_* M)) = Tr((σ̄ π̄)^* | RΓ(Z_k̄, M))`.

This is Step 8 of the proof of [Stacks, Tag 03UG]: with `i = f̄ : V̄ ⟶ Ū` the normalization of the
compactification of `U` in the Galois cover `V`, `M = j'_! A` and `ε` the action of a deck
transformation, it identifies the trace of `(g, π_U^*)` on `RΓ_c(U_k̄, f_* A)` with the trace of
`(g π_V)^*` on `RΓ_c(V_k̄, A)` ("the Leray spectral sequence, using the finiteness of `f`").

The base change map `(i_* M)|_{Y_k̄} ⟶ (i_k̄)_*(M|_{Z_k̄})` of the integral morphism `i` is an
isomorphism; it carries the Frobenius twists to each other, it is compatible with `i_* σ_* = i_*`
and the base change map of `σ`, and the comparisons of direct images along `σ̄ ≫ π̄` and `i_k̄`
are coherent.  The abstract statement
`CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_twistedBaseChange_eq` then applies.

## Main results

* `Stacks.EtaleCohomology.etaleModuleBaseChange_comp_directImageComp`.
* `Stacks.EtaleCohomology.directImageTwistTransfer_comp_directImageComp`.
* `Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusTwist_directImage_eq_twistedFrobenius`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

section Coherence

variable (Λ : Type r) [Ring Λ]

private lemma opChain₅₃ {C D : Type*} [Category* C] [Category* D] (G : Cᵒᵖ ⥤ D)
    {O₀ O₁ O₂ O₃ O₄ O₅ P₁ P₂ : C} {x₁ : O₁ ⟶ O₀} {x₂ : O₂ ⟶ O₁} {x₃ : O₃ ⟶ O₂}
    {x₄ : O₄ ⟶ O₃} {x₅ : O₅ ⟶ O₄} {y₁ : P₁ ⟶ O₀} {y₂ : P₂ ⟶ P₁} {y₃ : O₅ ⟶ P₂}
    (h : x₅ ≫ x₄ ≫ x₃ ≫ x₂ ≫ x₁ = y₃ ≫ y₂ ≫ y₁) :
    G.map x₁.op ≫ G.map x₂.op ≫ G.map x₃.op ≫ G.map x₄.op ≫ G.map x₅.op =
      G.map y₁.op ≫ G.map y₂.op ≫ G.map y₃.op := by
  simp only [← Functor.map_comp, ← op_comp, Category.assoc, h]

private lemma opChain₃₃ {C D : Type*} [Category* C] [Category* D] (G : Cᵒᵖ ⥤ D)
    {O₀ O₁ O₂ O₃ P₁ P₂ : C} {x₁ : O₁ ⟶ O₀} {x₂ : O₂ ⟶ O₁} {x₃ : O₃ ⟶ O₂}
    {y₁ : P₁ ⟶ O₀} {y₂ : P₂ ⟶ P₁} {y₃ : O₃ ⟶ P₂} (h : x₃ ≫ x₂ ≫ x₁ = y₃ ≫ y₂ ≫ y₁) :
    G.map x₁.op ≫ G.map x₂.op ≫ G.map x₃.op = G.map y₁.op ≫ G.map y₂.op ≫ G.map y₃.op := by
  simp only [← Functor.map_comp, ← op_comp, Category.assoc, h]

private lemma projChain₅ {D : Type*} [Category* D] {O₀ O₁ O₂ O₃ O₄ O₅ V : D}
    {l₁ : O₁ ⟶ O₀} {l₂ : O₂ ⟶ O₁} {l₃ : O₃ ⟶ O₂} {l₄ : O₄ ⟶ O₃} {l₅ : O₅ ⟶ O₄}
    {φ₀ : O₀ ⟶ V} {φ₁ : O₁ ⟶ V} {φ₂ : O₂ ⟶ V} {φ₃ : O₃ ⟶ V} {φ₄ : O₄ ⟶ V} {φ₅ : O₅ ⟶ V}
    (h₁ : l₁ ≫ φ₀ = φ₁) (h₂ : l₂ ≫ φ₁ = φ₂) (h₃ : l₃ ≫ φ₂ = φ₃) (h₄ : l₄ ≫ φ₃ = φ₄)
    (h₅ : l₅ ≫ φ₄ = φ₅) :
    (l₅ ≫ l₄ ≫ l₃ ≫ l₂ ≫ l₁) ≫ φ₀ = φ₅ := by
  simp only [Category.assoc, h₁, h₂, h₃, h₄, h₅]

private lemma projChain₃ {D : Type*} [Category* D] {O₀ O₁ O₂ O₃ V : D}
    {l₁ : O₁ ⟶ O₀} {l₂ : O₂ ⟶ O₁} {l₃ : O₃ ⟶ O₂}
    {φ₀ : O₀ ⟶ V} {φ₁ : O₁ ⟶ V} {φ₂ : O₂ ⟶ V} {φ₃ : O₃ ⟶ V}
    (h₁ : l₁ ≫ φ₀ = φ₁) (h₂ : l₂ ≫ φ₁ = φ₂) (h₃ : l₃ ≫ φ₂ = φ₃) :
    (l₃ ≫ l₂ ≫ l₁) ≫ φ₀ = φ₃ := by
  simp only [Category.assoc, h₁, h₂, h₃]

section Paste

variable {Z Z' Y Y' : Scheme.{u}} (i : Z ⟶ Y) (i' : Z' ⟶ Y') (g : Y' ⟶ Y) (g' : Z' ⟶ Z)
  (s : Z ⟶ Z) (s' : Z' ⟶ Z') (hi : i' ≫ g = g' ≫ i) (hs : s' ≫ g' = g' ≫ s)
  (hsi : i = s ≫ i) (hsi' : i' = s' ≫ i')

/-- The coherence of the comparisons of direct images behind
`Stacks.EtaleCohomology.etaleModuleBaseChange_comp_directImageComp`. -/
theorem directImageComp_paste_coherence (N : EtaleModules.{u, r} Λ Z') :
    (etaleModuleDirectImage.{u, r} Λ i).map
        ((etaleModuleDirectImageComp.{u, r} Λ g' s (s' ≫ g') hs).hom.app N ≫
          (etaleModuleDirectImageComp.{u, r} Λ s' g' (s' ≫ g') rfl).inv.app N) ≫
      (etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) hi).hom.app
          ((etaleModuleDirectImage.{u, r} Λ s').obj N) ≫
      (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl).inv.app
          ((etaleModuleDirectImage.{u, r} Λ s').obj N) ≫
      (etaleModuleDirectImage.{u, r} Λ g).map
        ((etaleModuleDirectImageComp.{u, r} Λ s' i' i' hsi').hom.app N) =
    (etaleModuleDirectImageComp.{u, r} Λ s i i hsi).hom.app
        ((etaleModuleDirectImage.{u, r} Λ g').obj N) ≫
      (etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) hi).hom.app N ≫
      (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl).inv.app N := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Functor.map_comp,
    directImage_map_hom_app, etaleModuleDirectImageComp_hom_app_hom_app,
    etaleModuleDirectImageComp_inv_app_hom_app, directImage_obj_map, Category.assoc]
  refine opChain₅₃ N.obj (smallEtaleBaseChange_hom_ext₃ g' s i ?_)
  exact Eq.trans
    (projChain₅ (stepHom _ (smallEtaleBaseChangeComp'_fst_fst g' s (s' ≫ g') hs _))
      (stepInv _ (smallEtaleBaseChangeComp'_inv_fst s' g' (s' ≫ g') rfl _))
      (stepMapHom (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_fst_fst g' i (i' ≫ g) hi _))
      (stepMapInv (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_inv_fst i' g (i' ≫ g) rfl _))
      (stepHom _ (smallEtaleBaseChangeComp'_fst_fst s' i' i' hsi' _)))
    (projChain₃ (stepMapHom (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_fst_fst s i i hsi _))
      (smallEtaleBaseChangeComp'_fst_fst g' i (i' ≫ g) hi _)
      (smallEtaleBaseChangeComp'_inv_fst i' g (i' ≫ g) rfl _)).symm

/-- **The base change map of `i` is compatible with `i_* s_* = i_*`.**  For a base change square
`i' ≫ g = g' ≫ i`, endomorphisms `s` of `Z` and `s'` of `Z'` over `Y` and `Y'` with
`s' ≫ g' = g' ≫ s`, and a sheaf `N` on `Z_étale`, the base change map of `i` at `s_* N`, followed
by `i'_*` of the base change map of `s` and `i'_* s'_* = i'_*`, is `g^{-1}(i_* s_* N = i_* N)`
followed by the base change map of `i` at `N`. -/
theorem etaleModuleBaseChange_comp_directImageComp (N : EtaleModules.{u, r} Λ Z) :
    (etaleModuleBaseChange Λ i i' g g' hi).app ((etaleModuleDirectImage.{u, r} Λ s).obj N) ≫
        (etaleModuleDirectImage.{u, r} Λ i').map ((etaleModuleBaseChange Λ s s' g' g' hs).app N) ≫
        (etaleModuleDirectImageComp.{u, r} Λ s' i' i' hsi').hom.app
          ((etaleModuleInverseImage.{u, r} Λ g').obj N) =
      (etaleModuleInverseImage.{u, r} Λ g).map
          ((etaleModuleDirectImageComp.{u, r} Λ s i i hsi).hom.app N) ≫
        (etaleModuleBaseChange Λ i i' g g' hi).app N := by
  apply ((etaleModuleInverseImageAdj.{u, r} Λ g).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.comp_obj, Functor.map_comp]
  have hU₁ := unit_comp_map_etaleModuleBaseChange Λ i i' g g' hi
    ((etaleModuleDirectImage.{u, r} Λ s).obj N)
  have hU₂ := unit_comp_map_etaleModuleBaseChange Λ s s' g' g' hs N
  have hU₃ := unit_comp_map_etaleModuleBaseChange Λ i i' g g' hi N
  have hu := (etaleModuleInverseImageAdj.{u, r} Λ g).unit.naturality
    ((etaleModuleDirectImageComp.{u, r} Λ s i i hsi).hom.app N)
  have hI := (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl).inv.naturality
    ((etaleModuleBaseChange Λ s s' g' g' hs).app N)
  have hH := (etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) hi).hom.naturality
    ((etaleModuleBaseChange Λ s s' g' g' hs).app N)
  have hc := (etaleModuleDirectImageComp.{u, r} Λ s i i hsi).hom.naturality
    ((etaleModuleInverseImageAdj.{u, r} Λ g').unit.app N)
  have hcoh := directImageComp_paste_coherence Λ i i' g g' s s' hi hs hsi hsi'
    ((etaleModuleInverseImage.{u, r} Λ g').obj N)
  rw [← Category.assoc, hU₁]
  simp only [Category.assoc]
  rw [reassoc_of% hI.symm, reassoc_of% hH.symm, ← Functor.map_comp_assoc, hU₂]
  rw [← reassoc_of% hu, hU₃, ← reassoc_of% hc]
  simp only [Functor.map_comp, Category.assoc] at hcoh ⊢
  rw [hcoh]

end Paste

section Transfer

variable {Z' Y' : Scheme.{u}} (i' : Z' ⟶ Y') (s' πZ φ : Z' ⟶ Z') (πY : Y' ⟶ Y')
  (hφ : φ = s' ≫ πZ) (e₁ : πZ ≫ i' = i' ≫ πY) (eφ : φ ≫ i' = i' ≫ πY) (hsi' : i' = s' ≫ i')

/-- **Coherence of the comparisons of direct images along `φ = s' ≫ π_Z` and `i'`**, with
`s' ≫ i' = i'`: the comparison `i'_* φ_* ⟶ π_{Y,*} i'_*` is the comparison
`i'_* π_{Z,*} ⟶ π_{Y,*} i'_*` at `s'_*` followed by `i'_* s'_* = i'_*`. -/
theorem directImageTwistTransfer_comp_directImageComp (N : EtaleModules.{u, r} Λ Z') :
    (etaleModuleDirectImage.{u, r} Λ i').map
        ((etaleModuleDirectImageComp.{u, r} Λ s' πZ φ hφ).hom.app N) ≫
      (directImageTwistTransfer Λ i' φ πY eφ).app N =
    (directImageTwistTransfer Λ i' πZ πY e₁).app ((etaleModuleDirectImage.{u, r} Λ s').obj N) ≫
      (etaleModuleDirectImage.{u, r} Λ πY).map
        ((etaleModuleDirectImageComp.{u, r} Λ s' i' i' hsi').hom.app N) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  simp only [directImageTwistTransfer, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, directImage_map_hom_app,
    etaleModuleDirectImageComp_hom_app_hom_app, etaleModuleDirectImageComp_inv_app_hom_app,
    directImage_obj_map, Category.assoc]
  refine opChain₃₃ N.obj (smallEtaleBaseChange_hom_ext₃ s' πZ i' ?_)
  exact Eq.trans
    (projChain₃ (stepHom _ (smallEtaleBaseChangeComp'_fst_fst s' πZ φ hφ _))
      (smallEtaleBaseChangeComp'_fst_fst φ i' (φ ≫ i') rfl _)
      (smallEtaleBaseChangeComp'_inv_fst i' πY (φ ≫ i') eφ _))
    (projChain₃ (stepMapHom (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_fst_fst πZ i' (πZ ≫ i') rfl _))
      (stepMapInv (smallEtaleBaseChange_map_left_fst _ _)
        (smallEtaleBaseChangeComp'_inv_fst i' πY (πZ ≫ i') e₁ _))
      (stepHom _ (smallEtaleBaseChangeComp'_fst_fst s' i' i' hsi' _))).symm

end Transfer

end Coherence

section Frobenius

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))}
  (i : Z ⟶ Y) (σ : Z ⟶ Z) (hσ : σ ≫ i = i) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [Fintype k] in
include hσ in
/-- `σ̄ ≫ i_k̄ = i_k̄` for `σ` over `Y`. -/
lemma fieldBaseChangeMap_comp_of_comp_eq :
    fieldBaseChangeMap σ kbar ≫ fieldBaseChangeMap i kbar = fieldBaseChangeMap i kbar := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, fieldBaseChangeMap_comp_fst,
      reassoc_of% (fieldBaseChangeMap_comp_fst σ kbar), ← Over.comp_left, hσ]
  · rw [Category.assoc, fieldBaseChangeMap_comp_snd, fieldBaseChangeMap_comp_snd]

include hσ in
/-- `i_k̄` intertwines the twisted Frobenius `σ̄ ≫ π̄` of `Z_k̄` with the Frobenius of `Y_k̄`. -/
lemma twistedGeometricFrobenius_comp_fieldBaseChangeMap :
    twistedGeometricFrobenius Z σ kbar p q hcard ≫ fieldBaseChangeMap i kbar =
      fieldBaseChangeMap i kbar ≫ geometricFrobeniusBaseChange Y kbar p q hcard := by
  rw [Category.assoc, geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar,
    ← Category.assoc, fieldBaseChangeMap_comp_of_comp_eq i σ hσ kbar]

include hσ in
/-- **Step 8 of [Stacks, Tag 03UG]: the Frobenius trace along an integral morphism, twisted by
an automorphism.**  Let `i : Z ⟶ Y` be an integral morphism over `k` (with base change map to
`k̄` an isomorphism, which holds by [Tag 0EYP],
`Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isIntegralHom`),
`σ : Z ⟶ Z` a morphism with `σ ≫ i = i`, `M` a bounded below complex on `Z_étale` with maps
`ε : M^n ⟶ σ_* M^n` commuting with the differentials, and `L` a bounded below complex on `Y_étale`
with an endomorphism `δ` and an isomorphism `e : L ≅ i_* M` carrying `δ` to `i_*(ε)` followed by
`i_* σ_* = i_*`.  Then the trace of the canonical Frobenius of `RΓ(Y_k̄, L)` composed with `δ`
(the derived endomorphism of the twist `τ ≫ π̄_*(δ|_{Y_k̄})`) is the trace of `(σ̄ π̄)^*` on
`RΓ(Z_k̄, M)`: the derived endomorphism of the twist `τ ≫ π̄_*(ε| ≫ (σ_* M)| ⟶ σ̄_*(M|))` of
`M|_{Z_k̄}` followed by `π̄_* σ̄_* = (σ̄ π̄)_*`. -/
theorem perfectDerivedTrace_frobeniusTwist_directImage_eq_twistedFrobenius [IsIntegralHom i.left]
    [IsIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
      (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar))]
    (L : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) (δ : L ⟶ L)
    (M : CochainComplex.Plus (EtaleModules.{u, r} Λ Z.left))
    (ε : ∀ n, M.obj.X n ⟶ (etaleModuleDirectImage.{u, r} Λ σ.left).obj (M.obj.X n))
    (hε : ∀ a b, M.obj.d a b ≫ ε b =
      ε a ≫ (etaleModuleDirectImage.{u, r} Λ σ.left).map (M.obj.d a b))
    (e : L ≅ (etaleModuleDirectImage.{u, r} Λ i.left).mapCochainComplexPlus.obj M)
    (he : ∀ n, δ.hom.f n ≫ e.hom.hom.f n = e.hom.hom.f n ≫
      (etaleModuleDirectImage.{u, r} Λ i.left).map (ε n) ≫
        (etaleModuleDirectImageComp.{u, r} Λ σ.left i.left i.left
          (by rw [← Over.comp_left, hσ])).hom.app (M.obj.X n))
    (hY : StacksDraft.Perfect.IsPerfect.{r, max r (u + 1), max r ((max r (u + 1)) + 1)}
      (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, r} Λ
          (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              L))))))
    (hZ : StacksDraft.Perfect.IsPerfect.{r, max r (u + 1), max r ((max r (u + 1)) + 1)}
      (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, r} Λ
          (pullback.snd Z.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
              M)))))) :
    perfectDerivedTrace Λ ⟨_, hY⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj L)
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, r} Λ
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj L)
          (Y := (etaleModuleDirectImage.{u, r} Λ
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj L))
          ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard) (ComplexShape.up ℤ)).app L.obj) ≫
          (etaleModuleDirectImage.{u, r} Λ
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
              δ)))) =
      perfectDerivedTrace Λ ⟨_, hZ⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Z σ kbar p q hcard))
        (etaleModuleDirectImage.{u, r} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, r} Λ (twistedGeometricFrobenius Z σ kbar p q hcard)
          (pullback.snd Z.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius_comp_toBase Z σ kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj M)
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, r} Λ
            (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj M)
          (Y := (etaleModuleDirectImage.{u, r} Λ
            (twistedGeometricFrobenius Z σ kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj M))
          (Functor.twistedBaseChangeTwistHC
            (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Z σ kbar p q hcard))
            (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar))
            (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Z kbar p q hcard))
            (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap σ kbar))
            (etaleModuleDirectImage.{u, r} Λ σ.left)
            (frobeniusBaseChangeTwist.{u, r} Λ Z kbar p q hcard)
            (automorphismBaseChange Λ Z σ kbar)
            (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap σ kbar)
              (geometricFrobeniusBaseChange Z kbar p q hcard)
              (twistedGeometricFrobenius Z σ kbar p q hcard) rfl)
            M.obj ε hε)))) := by
  have hint : IsIntegralHom (fieldBaseChangeMap i kbar) :=
    MorphismProperty.of_isPullback (isPullback_fieldBaseChangeMap i kbar).flip ‹_›
  have hex := etaleModuleDirectImage_exact_of_isIntegralHom Λ (fieldBaseChangeMap i kbar)
  have : PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar)) :=
    ((exactFunctor_iff _).1 hex).1
  have : PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar)) :=
    ((exactFunctor_iff _).1 hex).2
  have hσ' : i.left = σ.left ≫ i.left := by rw [← Over.comp_left, hσ]
  have hσk := (fieldBaseChangeMap_comp_of_comp_eq i σ hσ kbar).symm
  exact Functor.perfectDerivedTrace_derivedTwistEndo_twistedBaseChange_eq
    (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleDirectImage.{u, r} Λ (twistedGeometricFrobenius Z σ kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)))
    (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap i kbar))
    (etaleModuleDirectImage.{u, r} Λ i.left)
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Z kbar))
    (etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Z kbar p q hcard))
    (etaleModuleDirectImage.{u, r} Λ (fieldBaseChangeMap σ kbar))
    (etaleModuleDirectImage.{u, r} Λ σ.left)
    (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (etaleModuleDirectImageComp.{u, r} Λ (twistedGeometricFrobenius Z σ kbar p q hcard)
      (pullback.snd Z.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (twistedGeometricFrobenius_comp_toBase Z σ kbar p q hcard).symm)
    (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    (directImageTwistTransfer Λ (fieldBaseChangeMap i kbar)
      (twistedGeometricFrobenius Z σ kbar p q hcard) (geometricFrobeniusBaseChange Y kbar p q hcard)
      (twistedGeometricFrobenius_comp_fieldBaseChangeMap i σ hσ kbar p q hcard))
    (directImageTwistTransfer_compat Λ (fieldBaseChangeMap i kbar)
      (twistedGeometricFrobenius Z σ kbar p q hcard) (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (twistedGeometricFrobenius_comp_fieldBaseChangeMap i σ hσ kbar p q hcard)
      (fieldBaseChangeMap_comp_snd i kbar).symm
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm
      (twistedGeometricFrobenius_comp_toBase Z σ kbar p q hcard).symm)
    (asIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar)
      (fieldBaseChangeMap_comp_fst i kbar)))
    (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)
    (frobeniusBaseChangeTwist.{u, r} Λ Z kbar p q hcard)
    (directImageTwistTransfer Λ (fieldBaseChangeMap i kbar)
      (geometricFrobeniusBaseChange Z kbar p q hcard)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar))
    (automorphismBaseChange Λ Z σ kbar)
    (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap σ kbar)
      (geometricFrobeniusBaseChange Z kbar p q hcard)
      (twistedGeometricFrobenius Z σ kbar p q hcard) rfl)
    (etaleModuleDirectImageComp.{u, r} Λ (fieldBaseChangeMap σ kbar) (fieldBaseChangeMap i kbar)
      (fieldBaseChangeMap i kbar) hσk)
    (etaleModuleDirectImageComp.{u, r} Λ σ.left i.left i.left hσ')
    (etaleModuleBaseChange_comp_frobeniusBaseChangeTwist Λ i p q hcard kbar)
    (etaleModuleBaseChange_comp_directImageComp Λ i.left (fieldBaseChangeMap i kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Z kbar) σ.left (fieldBaseChangeMap σ kbar)
      (fieldBaseChangeMap_comp_fst i kbar) (fieldBaseChangeMap_comp_fst σ kbar) hσ' hσk)
    (directImageTwistTransfer_comp_directImageComp Λ (fieldBaseChangeMap i kbar)
      (fieldBaseChangeMap σ kbar) (geometricFrobeniusBaseChange Z kbar p q hcard)
      (twistedGeometricFrobenius Z σ kbar p q hcard) (geometricFrobeniusBaseChange Y kbar p q hcard)
      rfl (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)
      (twistedGeometricFrobenius_comp_fieldBaseChangeMap i σ hσ kbar p q hcard) hσk)
    L δ M ε e he _ (fun _ => rfl) hε hY hZ


section CommRing

variable (Λ : Type) [CommRing Λ]

include hσ in
/-- `Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusTwist_directImage_eq_twistedFrobenius` for
a commutative coefficient ring in `Type`, where the base change isomorphism of the integral
morphism `i` is [Tag 0EYP]. -/
theorem perfectDerivedTrace_frobeniusTwist_directImage_eq_twistedFrobenius_of_commRing
    [IsIntegralHom i.left]
    (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) (δ : L ⟶ L)
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left))
    (ε : ∀ n, M.obj.X n ⟶ (etaleModuleDirectImage.{u, 0} Λ σ.left).obj (M.obj.X n))
    (hε : ∀ a b, M.obj.d a b ≫ ε b =
      ε a ≫ (etaleModuleDirectImage.{u, 0} Λ σ.left).map (M.obj.d a b))
    (e : L ≅ (etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj M)
    (he : ∀ n, δ.hom.f n ≫ e.hom.hom.f n = e.hom.hom.f n ≫
      (etaleModuleDirectImage.{u, 0} Λ i.left).map (ε n) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ σ.left i.left i.left
          (by rw [← Over.comp_left, hσ])).hom.app (M.obj.X n))
    (hY : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              L))))))
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd Z.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
              M)))))) :
    perfectDerivedTrace Λ ⟨_, hY⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj L)
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj L)
          (Y := (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj L))
          ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard) (ComplexShape.up ℤ)).app L.obj) ≫
          (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
              δ)))) =
      perfectDerivedTrace Λ ⟨_, hZ⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Z σ kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ (twistedGeometricFrobenius Z σ kbar p q hcard)
          (pullback.snd Z.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius_comp_toBase Z σ kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj M)
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj M)
          (Y := (etaleModuleDirectImage.{u, 0} Λ
            (twistedGeometricFrobenius Z σ kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj M))
          (Functor.twistedBaseChangeTwistHC
            (etaleModuleDirectImage.{u, 0} Λ (twistedGeometricFrobenius Z σ kbar p q hcard))
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar))
            (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard))
            (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap σ kbar))
            (etaleModuleDirectImage.{u, 0} Λ σ.left)
            (frobeniusBaseChangeTwist.{u, 0} Λ Z kbar p q hcard)
            (automorphismBaseChange Λ Z σ kbar)
            (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap σ kbar)
              (geometricFrobeniusBaseChange Z kbar p q hcard)
              (twistedGeometricFrobenius Z σ kbar p q hcard) rfl)
            M.obj ε hε)))) := by
  have := isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isIntegralHom Λ i kbar
  exact perfectDerivedTrace_frobeniusTwist_directImage_eq_twistedFrobenius Λ i σ hσ kbar p q hcard
    L δ M ε hε e he hY hZ

end CommRing

end Frobenius

end Stacks.EtaleCohomology

end
