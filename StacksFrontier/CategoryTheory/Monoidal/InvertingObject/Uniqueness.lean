module

public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Existence
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Transport

/-!
# Uniqueness of the braided extension

We prove (U) of `StacksFrontier.CategoryTheory.Monoidal.InvertingObject`. Every braided extension
`G'` of `F` along `K` is monoidally isomorphic to the extension `Pairs.ext` constructed in
`StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Existence`, compatibly with the
identifications on `𝒜`: transporting the presentations of `Pairs` along the second projection
and along `G'` composed with the first projection gives morphisms of `𝒞` presented by the same
morphisms of `𝒜`, hence equal. Two monoidal isomorphisms of extensions which agree on `𝒜` agree
on `T` (cancel the invertible `G(K(L))` in `G(K(L) ⊗ T) ≅ G(𝟙)`) and hence everywhere.

## Main results

* `CategoryTheory.InvertingObject.uniqueness`: (U).
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.InvertingObject

open MonoidalCategory BraidedCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open Expr

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [SymmetricCategory 𝒜]
  {ℳ : Type u₂} [Category.{v₂} ℳ] [MonoidalCategory ℳ] [SymmetricCategory ℳ]
  {𝒞 : Type u₃} [Category.{v₃} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  (K : 𝒜 ⥤ ℳ) [K.Braided] (F : 𝒜 ⥤ 𝒞) [F.Braided] {L : 𝒜} {T : ℳ}
  (ℓ : K.obj L ⊗ T ≅ 𝟙_ ℳ) (hL : HasInverse (F.obj L))

namespace Pairs

/-- The second component of `K.prod' F` is `F`. -/
def sndIso : K.prod' F ⋙ Prod.snd ℳ 𝒞 ≅ F :=
  NatIso.ofComponents (fun A => Iso.refl (F.obj A))
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The isomorphism `sndIso K F` is a monoidal natural transformation. -/
instance : NatTrans.IsMonoidal (sndIso K F).hom where
  unit := by
    change ((𝟙 _ ≫ (ε (K.prod' F)).2)) ≫ 𝟙 _ = ε F
    rw [Category.comp_id, Category.id_comp, Functor.prod'_ε_snd]
  tensor A B := by
    change ((𝟙 _ ≫ (μ (K.prod' F) A B).2)) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ F A B
    rw [Category.comp_id, Category.id_comp, id_tensorHom_id, Category.id_comp,
      Functor.prod'_μ_snd]

/-- Under the second projection, the pairing of `(T, V)` with `(K.prod' F).obj L` corresponds, via
`sndIso K F`, to the identification `V ⊗ F(L) ≅ 𝟙_ 𝒞` of the inverse `V` of `F(L)`. -/
theorem sndIso_compat :
    μ (Prod.snd ℳ 𝒞) ((T, hL.inv) : ℳ × 𝒞) ((K.prod' F).obj L) ≫
      (Prod.snd ℳ 𝒞).map (β_ ((T, hL.inv) : ℳ × 𝒞) ((K.prod' F).obj L) ≪≫ pairing K F ℓ hL ≪≫
        εIso (K.prod' F)).hom ≫ (sndIso K F).hom.app (𝟙_ 𝒜) =
      ((Iso.refl hL.inv).hom ⊗ₘ (sndIso K F).hom.app L) ≫
        (β_ hL.inv (F.obj L) ≪≫ hL.isoLeft ≪≫ εIso F).hom := by
  change 𝟙 _ ≫ ((β_ hL.inv (F.obj L)).hom ≫ hL.isoLeft.hom ≫ (ε (K.prod' F)).2) ≫ 𝟙 _ =
    (𝟙 _ ⊗ₘ 𝟙 _) ≫ ((β_ hL.inv (F.obj L)).hom ≫ hL.isoLeft.hom ≫ ε F)
  rw [Functor.prod'_ε_snd, id_tensorHom_id, Category.id_comp, Category.id_comp,
    Category.comp_id]

variable {K F} (G' : ℳ ⥤ 𝒞) [G'.Braided] (φ' : K ⋙ G' ≅ F) [NatTrans.IsMonoidal φ'.hom]

/-- `G'` after the first component of `K.prod' F` is `F`. -/
def fstIso : K.prod' F ⋙ (Prod.fst ℳ 𝒞 ⋙ G') ≅ F :=
  NatIso.ofComponents (fun A => φ'.app A) (fun f => φ'.hom.naturality f)

/-- The isomorphism `fstIso G' φ'` is a monoidal natural transformation. -/
instance : NatTrans.IsMonoidal (fstIso G' φ').hom where
  unit := by
    have h := NatTrans.IsMonoidal.unit (τ := φ'.hom)
    rw [Functor.LaxMonoidal.comp_ε] at h
    change ((ε G' ≫ G'.map (𝟙 _)) ≫ G'.map (ε (K.prod' F)).1) ≫ φ'.hom.app _ = ε F
    rw [G'.map_id, Category.comp_id, Functor.prod'_ε_fst]
    exact h
  tensor A B := by
    have h := NatTrans.IsMonoidal.tensor (τ := φ'.hom) A B
    rw [Functor.LaxMonoidal.comp_μ] at h
    change ((μ G' _ _ ≫ G'.map (𝟙 _)) ≫ G'.map (μ (K.prod' F) A B).1) ≫ φ'.hom.app _ =
      (φ'.hom.app A ⊗ₘ φ'.hom.app B) ≫ μ F A B
    rw [G'.map_id, Category.comp_id, Functor.prod'_μ_fst]
    exact h

variable {ℓ hL} in
/-- The isomorphism `G'(T) ≅ V` compatible with `ℓ`, `φ'` and the pairing of `V` with `F(L)`. -/
def tateIso : G'.obj T ≅ hL.inv :=
  hL.tensorRightEquivalence.fullyFaithfulFunctor.preimageIso
    (whiskerLeftIso (G'.obj T) (φ'.app L).symm ≪≫ μIso G' T (K.obj L) ≪≫
      G'.mapIso (β_ T (K.obj L) ≪≫ ℓ ≪≫ εIso K) ≪≫ φ'.app (𝟙_ 𝒜) ≪≫
        (β_ hL.inv (F.obj L) ≪≫ hL.isoLeft ≪≫ εIso F).symm)

omit [NatTrans.IsMonoidal φ'.hom] in
/-- Under `G'` after the first projection, the pairing of `(T, V)` with `(K.prod' F).obj L`
corresponds, via `tateIso G' φ'` and `fstIso G' φ'`, to the identification `V ⊗ F(L) ≅ 𝟙_ 𝒞` of
the inverse `V` of `F(L)`. -/
theorem fstIso_compat :
    μ (Prod.fst ℳ 𝒞 ⋙ G') ((T, hL.inv) : ℳ × 𝒞) ((K.prod' F).obj L) ≫
      (Prod.fst ℳ 𝒞 ⋙ G').map (β_ ((T, hL.inv) : ℳ × 𝒞) ((K.prod' F).obj L) ≪≫
        pairing K F ℓ hL ≪≫ εIso (K.prod' F)).hom ≫ (fstIso G' φ').hom.app (𝟙_ 𝒜) =
      ((tateIso G' φ' (ℓ := ℓ) (hL := hL)).hom ⊗ₘ (fstIso G' φ').hom.app L) ≫
        (β_ hL.inv (F.obj L) ≪≫ hL.isoLeft ≪≫ εIso F).hom := by
  have h : (tateIso G' φ' (ℓ := ℓ) (hL := hL)).hom ▷ F.obj L =
      G'.obj T ◁ (φ'.app L).inv ≫ μ G' T (K.obj L) ≫
        G'.map ((β_ T (K.obj L)).hom ≫ ℓ.hom ≫ ε K) ≫ φ'.hom.app (𝟙_ 𝒜) ≫
          (β_ hL.inv (F.obj L) ≪≫ hL.isoLeft ≪≫ εIso F).inv :=
    hL.tensorRightEquivalence.fullyFaithfulFunctor.map_preimage _
  change ((μ G' T (K.obj L) ≫ G'.map (𝟙 _)) ≫ G'.map ((β_ T (K.obj L)).hom ≫ ℓ.hom ≫
      (ε (K.prod' F)).1) ≫ φ'.hom.app (𝟙_ 𝒜)) =
    ((tateIso G' φ' (ℓ := ℓ) (hL := hL)).hom ⊗ₘ φ'.hom.app L) ≫
      (β_ hL.inv (F.obj L) ≪≫ hL.isoLeft ≪≫ εIso F).hom
  rw [G'.map_id, Category.comp_id, Functor.prod'_ε_fst, tensorHom_def', h]
  simp

/-- The comparison of the evaluations, through `G'` after the first component. -/
abbrev evFst : ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) ⋙ (Prod.fst ℳ 𝒞 ⋙ G') ≅ ev F hL.inv :=
  evTransport (𝕋 := ((T, hL.inv) : ℳ × 𝒞)) (Prod.fst ℳ 𝒞 ⋙ G') (fstIso G' φ')
    (tateIso G' φ' (ℓ := ℓ) (hL := hL))

variable (K F) in
/-- The comparison of the evaluations, through the second component. -/
abbrev evSnd : ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) ⋙ Prod.snd ℳ 𝒞 ≅ ev F hL.inv :=
  evTransport (𝕋 := ((T, hL.inv) : ℳ × 𝒞)) (Prod.snd ℳ 𝒞) (sndIso K F) (Iso.refl hL.inv)

/-- The isomorphism `G'(pr₁ X) ≅ pr₂ X` on the objects of `Pairs`. -/
abbrev compIso (e : Expr 𝒜) :
    G'.obj ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e).1 ≅
      ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e).2 :=
  ((evFst ℓ hL G' φ') ≪≫ (evSnd K F hL).symm).app e

variable [K.Full] [K.Faithful]

omit [K.Full] [K.Faithful] in
/-- **`G'` agrees with the second projection on the morphisms of `Pairs`.** -/
theorem compIso_naturality {X Y : Pairs K F ℓ hL} (f : X ⟶ Y) :
    G'.map f.1.1 ≫ (compIso ℓ hL G' φ' Y.expr).hom = (compIso ℓ hL G' φ' X.expr).hom ≫ f.1.2 := by
  obtain ⟨X', Y', φ, c, hX', -, h⟩ := f.2
  have a := h.transport (𝕋 := ((T, hL.inv) : ℳ × 𝒞)) (Prod.fst ℳ 𝒞 ⋙ G') (fstIso G' φ')
    (tateIso G' φ' (ℓ := ℓ) (hL := hL)) (fstIso_compat ℓ hL G' φ')
  have b := h.transport (𝕋 := ((T, hL.inv) : ℳ × 𝒞)) (Prod.snd ℳ 𝒞) (sndIso K F)
    (Iso.refl hL.inv) (sndIso_compat K F ℓ hL)
  have hc := IsInvertible.rightCancel (isInvertible_prod_snd (IsInvertible.map_tensor
    (K.prod' F) X.isInvertible hX'))
  have e := hc.1 (a.whiskerRight_eq b)
  change ((evFst ℓ hL G' φ').app X.expr).inv ≫ G'.map f.1.1 ≫ ((evFst ℓ hL G' φ').app Y.expr).hom =
    ((evSnd K F hL).app X.expr).inv ≫ f.1.2 ≫ ((evSnd K F hL).app Y.expr).hom at e
  simp only [compIso, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [← cancel_epi ((evFst ℓ hL G' φ').app X.expr).inv]
  simp only [Iso.app_hom, Iso.app_inv] at e ⊢
  rw [Iso.inv_hom_id_app_assoc, reassoc_of% e, Iso.hom_inv_id_app]
  exact congrArg (_ ≫ ·) (Category.comp_id f.1.2)

/-- **A braided extension agrees with the second projection on `Pairs`.** -/
def compNatIso : pr₁ K F ℓ hL ⋙ G' ≅ pr₂ K F ℓ hL :=
  NatIso.ofComponents (fun X => compIso ℓ hL G' φ' X.expr)
    (fun f => compIso_naturality ℓ hL G' φ' f)

/-- The isomorphism `compNatIso ℓ hL G' φ'` is a monoidal natural transformation. -/
instance : NatTrans.IsMonoidal (compNatIso ℓ hL G' φ').hom where
  unit := by
    have h := NatTrans.IsMonoidal.unit (τ := (evFst ℓ hL G' φ').hom ≫ (evSnd K F (T := T) hL).inv)
    simp only [Functor.LaxMonoidal.comp_ε, fst_ε, snd_ε, Functor.map_id,
      Category.comp_id, Category.id_comp, NatTrans.comp_app, FreeMonoidalCategory.project_ε] at h
    simp only [compNatIso, Functor.LaxMonoidal.comp_ε, Graph.incl_ε, fst_ε, snd_ε,
      Category.id_comp]
    exact h
  tensor X Y := by
    have h := NatTrans.IsMonoidal.tensor (τ := (evFst ℓ hL G' φ').hom ≫ (evSnd K F (T := T) hL).inv)
      X.expr Y.expr
    have h₁ : μ (ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) ⋙ (Prod.fst ℳ 𝒞 ⋙ G')) X.expr Y.expr =
        μ G' ((pr₁ K F ℓ hL).obj X) ((pr₁ K F ℓ hL).obj Y) := by
      change (μ G' _ _ ≫ G'.map (𝟙 ((pr₁ K F ℓ hL).obj X ⊗ (pr₁ K F ℓ hL).obj Y))) ≫
        G'.map (𝟙 ((pr₁ K F ℓ hL).obj X ⊗ (pr₁ K F ℓ hL).obj Y)) = _
      rw [G'.map_id, Category.comp_id, Category.comp_id]
    have h₂ : μ (ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) ⋙ Prod.snd ℳ 𝒞) X.expr Y.expr =
        𝟙 ((pr₂ K F ℓ hL).obj X ⊗ (pr₂ K F ℓ hL).obj Y) := by
      change 𝟙 ((pr₂ K F ℓ hL).obj X ⊗ (pr₂ K F ℓ hL).obj Y) ≫
        𝟙 ((pr₂ K F ℓ hL).obj X ⊗ (pr₂ K F ℓ hL).obj Y) = _
      rw [Category.comp_id]
    have h₃ : μ (pr₁ K F ℓ hL ⋙ G') X Y = μ G' ((pr₁ K F ℓ hL).obj X) ((pr₁ K F ℓ hL).obj Y) := by
      change μ G' _ _ ≫ G'.map (𝟙 ((pr₁ K F ℓ hL).obj X ⊗ (pr₁ K F ℓ hL).obj Y) ≫
        𝟙 ((pr₁ K F ℓ hL).obj X ⊗ (pr₁ K F ℓ hL).obj Y)) = _
      rw [Category.comp_id, G'.map_id, Category.comp_id]
    have h₄ : μ (pr₂ K F ℓ hL) X Y = 𝟙 ((pr₂ K F ℓ hL).obj X ⊗ (pr₂ K F ℓ hL).obj Y) := by
      change 𝟙 ((pr₂ K F ℓ hL).obj X ⊗ (pr₂ K F ℓ hL).obj Y) ≫
        𝟙 ((pr₂ K F ℓ hL).obj X ⊗ (pr₂ K F ℓ hL).obj Y) = _
      rw [Category.comp_id]
    exact (congrArg (· ≫ _) (h₃.trans h₁.symm)).trans (h.trans ((congrArg (_ ≫ ·)
      (h₂.trans h₄.symm))))

variable (hess : ∀ M : ℳ, ∃ (A : 𝒜) (n : ℕ), Nonempty (M ≅ K.obj A ⊗ tensorPow T n))

attribute [local instance] Equivalence.inverseMonoidal Equivalence.inverseBraided

/-- `compNatIso`, with the first projection seen as the functor of the equivalence. -/
def compNatIso' : (pr₁Equiv K F ℓ hL hess).functor ⋙ G' ≅ pr₂ K F ℓ hL := compNatIso ℓ hL G' φ'

/-- The isomorphism `compNatIso' ℓ hL G' φ' hess` is a monoidal natural transformation. -/
instance : NatTrans.IsMonoidal (compNatIso' ℓ hL G' φ' hess).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (compNatIso ℓ hL G' φ').hom)

/-- **A braided extension is isomorphic to `ext`.** -/
def isoExt : G' ≅ ext K F ℓ hL hess :=
  (Functor.leftUnitor G').symm ≪≫
    Functor.isoWhiskerRight (pr₁Equiv K F ℓ hL hess).counitIso.symm G' ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (compNatIso' ℓ hL G' φ' hess)

/-- The isomorphism `isoExt ℓ hL G' φ' hess` is a monoidal natural transformation. -/
instance : NatTrans.IsMonoidal (isoExt ℓ hL G' φ' hess).hom := by
  have h : (isoExt ℓ hL G' φ' hess).hom = (Functor.leftUnitor G').inv ≫
      Functor.whiskerRight (pr₁Equiv K F ℓ hL hess).counitIso.inv G' ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (compNatIso' ℓ hL G' φ' hess).hom := rfl
  rw [h]
  infer_instance

/-- The isomorphism `isoExt ℓ hL G' φ' hess : G' ≅ ext K F ℓ hL hess`, restricted along `K` and
composed with `extIso K F ℓ hL hess`, is `φ'`. -/
theorem isoExt_compat :
    Functor.whiskerLeft K (isoExt ℓ hL G' φ' hess).hom ≫ (extIso K F ℓ hL hess).hom = φ'.hom := by
  ext A
  have hn := (compNatIso' ℓ hL G' φ' hess).hom.naturality
    ((pr₁Equiv K F ℓ hL hess).unitIso.inv.app ((ι K F ℓ hL).obj A))
  simp only [isoExt, extIso, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
    Functor.leftUnitor_hom_app, Functor.associator_inv_app, Category.id_comp] at hn ⊢
  have e₃ : (compNatIso' ℓ hL G' φ' hess).hom.app ((ι K F ℓ hL).obj A) = φ'.hom.app A :=
    Category.comp_id _
  have key : G'.map ((pr₁Equiv K F ℓ hL hess).counitInv.app
      ((pr₁Equiv K F ℓ hL hess).functor.obj ((ι K F ℓ hL).obj A))) ≫
        (compNatIso' ℓ hL G' φ' hess).hom.app (((pr₁Equiv K F ℓ hL hess).functor ⋙
          (pr₁Equiv K F ℓ hL hess).inverse).obj ((ι K F ℓ hL).obj A)) ≫
        (pr₂ K F ℓ hL).map ((pr₁Equiv K F ℓ hL hess).unitIso.inv.app ((ι K F ℓ hL).obj A)) =
      φ'.hom.app A := by
    rw [← hn, Functor.comp_map, ← G'.map_comp_assoc]
    rw [show (pr₁Equiv K F ℓ hL hess).unitIso.inv = (pr₁Equiv K F ℓ hL hess).unitInv from rfl,
      Equivalence.counitInv_functor_comp]
    exact ((congrArg (· ≫ _) (G'.map_id _)).trans (Category.id_comp _)).trans e₃
  have hc : (ext K F ℓ hL hess).map ((ιPr₁' K F ℓ hL hess).inv.app A) = 𝟙 _ :=
    (ext K F ℓ hL hess).map_id _
  refine Eq.trans ?_ key
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ _ ≫ ·) ((congrArg (· ≫ _) hc).trans
    ((Category.id_comp _).trans ((Category.comp_id _).trans (Category.comp_id _)))))

end Pairs

section Ext

variable {K} {G₁ G₂ : ℳ ⥤ 𝒞} [G₁.Monoidal] [G₂.Monoidal] (θ θ' : G₁ ⟶ G₂) [NatTrans.IsMonoidal θ]
  [NatTrans.IsMonoidal θ']

omit [SymmetricCategory ℳ] [SymmetricCategory 𝒞] in
/-- Two monoidal natural transformations `G₁ ⟶ G₂` agree on the unit `𝟙_ ℳ`. -/
theorem app_unit_eq : θ.app (𝟙_ ℳ) = θ'.app (𝟙_ ℳ) := by
  rw [← cancel_epi (ε G₁), NatTrans.IsMonoidal.unit, NatTrans.IsMonoidal.unit]

variable {θ θ'}

omit [SymmetricCategory ℳ] [SymmetricCategory 𝒞] in
/-- If two monoidal natural transformations agree on `X` and on `Y`, they agree on `X ⊗ Y`. -/
theorem app_tensor_eq {X Y : ℳ} (hX : θ.app X = θ'.app X) (hY : θ.app Y = θ'.app Y) :
    θ.app (X ⊗ Y) = θ'.app (X ⊗ Y) := by
  rw [← cancel_epi (μ G₁ X Y), NatTrans.IsMonoidal.tensor, NatTrans.IsMonoidal.tensor, hX, hY]

omit [SymmetricCategory ℳ] [SymmetricCategory 𝒞] in
/-- If two monoidal natural transformations agree on `X`, they agree on every tensor power
`tensorPow X n`. -/
theorem app_tensorPow_eq {X : ℳ} (hX : θ.app X = θ'.app X) (n : ℕ) :
    θ.app (tensorPow X n) = θ'.app (tensorPow X n) := by
  induction n with
  | zero => exact app_unit_eq θ θ'
  | succ n ih => exact app_tensor_eq ih hX

omit [MonoidalCategory 𝒜] [SymmetricCategory 𝒜] [SymmetricCategory ℳ] [SymmetricCategory 𝒞]
  [K.Braided] in
/-- **Monoidal transformations out of `ℳ` are determined on `𝒜`.** Two monoidal natural
isomorphisms `G₁ ≅ G₂` agreeing on the image of `K` agree, provided `G₂(K(L))` is invertible. -/
theorem iso_ext_of_app_obj {φ ψ : G₁ ≅ G₂} [NatTrans.IsMonoidal φ.hom] [NatTrans.IsMonoidal ψ.hom]
    (ℓ : K.obj L ⊗ T ≅ 𝟙_ ℳ)
    (hess : ∀ M : ℳ, ∃ (A : 𝒜) (n : ℕ), Nonempty (M ≅ K.obj A ⊗ tensorPow T n))
    (hinv : IsInvertible (G₂.obj (K.obj L))) (hK : ∀ A, φ.hom.app (K.obj A) = ψ.hom.app (K.obj A)) :
    φ = ψ := by
  have hLT : φ.hom.app (K.obj L ⊗ T) = ψ.hom.app (K.obj L ⊗ T) := by
    rw [← cancel_mono (G₂.map ℓ.hom), ← φ.hom.naturality, ← ψ.hom.naturality,
      app_unit_eq φ.hom ψ.hom]
  have hT : φ.hom.app T = ψ.hom.app T := by
    have h := hLT
    rw [← cancel_epi (μ G₁ (K.obj L) T), NatTrans.IsMonoidal.tensor, NatTrans.IsMonoidal.tensor,
      cancel_mono, tensorHom_def, tensorHom_def, hK L, cancel_epi] at h
    exact (IsInvertible.leftCancel hinv).1 h
  ext M
  obtain ⟨A, n, ⟨i⟩⟩ := hess M
  have h := app_tensor_eq (hK A) (app_tensorPow_eq hT n)
  rw [← cancel_mono (G₂.map i.hom), ← φ.hom.naturality, ← ψ.hom.naturality, h]

end Ext

/-- The inverse `G(T)` of `F(L) ≅ G(K(L))`, for an extension `G` of `F`. -/
def hasInverseOfExtension {K} {F} (ℓ : K.obj L ⊗ T ≅ 𝟙_ ℳ) (G : ℳ ⥤ 𝒞) [G.Monoidal]
    (φ : K ⋙ G ≅ F) : HasInverse (F.obj L) where
  inv := G.obj T
  isoLeft := whiskerRightIso (φ.app L).symm _ ≪≫ μIso G _ _ ≪≫ G.mapIso ℓ ≪≫ (εIso G).symm
  isoRight := β_ _ _ ≪≫ whiskerRightIso (φ.app L).symm _ ≪≫ μIso G _ _ ≪≫ G.mapIso ℓ ≪≫
    (εIso G).symm

section

variable (𝒞 : Type u₃) [Category.{v₃} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  (K : 𝒜 ⥤ ℳ) [K.Braided] [K.Full] [K.Faithful] (L : 𝒜) (T : ℳ)

attribute [local instance] Equivalence.inverseMonoidal Equivalence.inverseBraided

/-- **(U)**, see `CategoryTheory.InvertingObject.Uniqueness`. -/
theorem uniqueness : Uniqueness 𝒞 K L T := by
  intro ℓ hess F _ G₁ G₂ _ _ φ₁ φ₂ _ _
  let hL := hasInverseOfExtension ℓ G₁ φ₁
  let θ₁ := Pairs.isoExt ℓ hL G₁ φ₁ hess
  let θ₂ := Pairs.isoExt ℓ hL G₂ φ₂ hess
  have c₁ := Pairs.isoExt_compat ℓ hL G₁ φ₁ hess
  have c₂ := Pairs.isoExt_compat ℓ hL G₂ φ₂ hess
  have key : ∀ A, (θ₁ ≪≫ θ₂.symm).hom.app (K.obj A) ≫ φ₂.hom.app A = φ₁.hom.app A := by
    intro A
    have h₂ := congrArg (fun t => t.app A) c₁
    have h₃ := congrArg (fun t => t.app A) c₂
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₂ h₃
    rw [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc, ← h₃,
      Iso.inv_hom_id_app_assoc, h₂]
  have hm : NatTrans.IsMonoidal (θ₁ ≪≫ θ₂.symm).hom := by
    rw [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  refine ⟨θ₁ ≪≫ θ₂.symm, ⟨hm, ?_⟩, ?_⟩
  · ext A
    exact key A
  · rintro θ ⟨hθm, hθ⟩
    refine iso_ext_of_app_obj ℓ hess (isInvertible_of_iso (φ₂.app L).symm ⟨hL⟩) fun A => ?_
    have h₁ := congrArg (fun t => t.app A) hθ
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁
    exact (cancel_mono (φ₂.hom.app A)).1 (h₁.trans (key A).symm)

end

end CategoryTheory.InvertingObject
