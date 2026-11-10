module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralTwistedFrobeniusTrace

/-!
# Extension by zero along an integral direct image, with a twist

Let `f : V ⟶ U` be the restriction over an open `j : U ⟶ Ū` of an integral morphism
`f̄ : V̄ ⟶ Ū` (`V = V̄ ×_Ū U`, `j' : V ⟶ V̄`), let `σ : V̄ ⟶ V̄` be integral with `σ ≫ f̄ = f̄` and
`a : V ⟶ V` its restriction (`V = σ^{-1}(V)`). For a sheaf `G` on `V` with a map
`ε : G ⟶ a_* G`, the canonical isomorphism `E : j_!(f_* G) ≅ f̄_*(j'_! G)` carries the endomorphism
`j_!(f_* ε ≫ f_* a_* = f_*)` of `j_!(f_* G)` to `f̄_*` of the extension by zero of `ε`, followed by
`f̄_* σ_* = f̄_*`. This is how the deck action on the cover in Step 8 of the proof of
[Stacks, Tag 03UG] becomes, on the compactification, the twist used in Step 9.

## Main results

* `Stacks.EtaleCohomology.restrictionDirectImageIso_inv_app_comp`,
  `Stacks.EtaleCohomology.restrictionDirectImageIso_hom_app_comp`: the pasting of the
  isomorphisms `f_* j'^{-1} ≅ j^{-1} f̄_*` along `σ`.
* `Stacks.EtaleCohomology.extensionByZeroDirectImageMap_comp_twist`, and its form
  `Stacks.EtaleCohomology.extensionByZeroDirectImageMap_comp_extensionByZeroTwist` for the
  restriction `Stacks.EtaleCohomology.restrictionTwist` of a map on `V̄`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [Etale j] [Mono j]
  (j' : V ⟶ Vb) [Etale j'] [Mono j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb) (a : V ⟶ V) (σ : Vb ⟶ Vb) [IsIntegralHom σ]
  (sqσ : IsPullback a j' j' σ) (hσ : σ ≫ fb = fb) (ha : a ≫ f = f)

/-- The category chase behind `Stacks.EtaleCohomology.restrictionDirectImageIso_inv_app_comp`. -/
private lemma pasteChase {C C' : Type*} [Category* C] [Category* C'] (F : C' ⥤ C)
    {P Q Q' : C} {S S' T T' AS AS' : C'} (i₁ : P ⟶ Q) (c' : Q ⟶ Q') (b : Q' ⟶ F.obj S)
    (t₁ : S ⟶ S') (b₂ : Q ⟶ F.obj T) (v : T ⟶ T') (v' : T' ⟶ T) (b' : T ⟶ AS) (At₁ : AS ⟶ AS')
    (κS : F.obj AS ⟶ F.obj S) (κS' : F.obj AS' ⟶ F.obj S') (hv : v ≫ v' = 𝟙 T)
    (hc : F.map At₁ ≫ κS' = κS ≫ F.map t₁) (key : b₂ ≫ F.map b' ≫ κS = c' ≫ b) :
    i₁ ≫ c' ≫ b ≫ F.map t₁ = i₁ ≫ b₂ ≫ F.map v ≫ F.map (v' ≫ b' ≫ At₁) ≫ κS' := by
  rw [← F.map_comp_assoc, ← Category.assoc v, hv, Category.id_comp, Functor.map_comp_assoc, hc,
    reassoc_of% key]

omit [Etale j] [Mono j] [Etale j'] [Mono j'] [IsIntegralHom fb] [IsIntegralHom σ] in
include hσ ha in
/-- `Stacks.EtaleCohomology.etaleModuleBaseChange_comp_directImageComp` for a commutative
coefficient ring in `Type`, proved afresh in this universe: instantiating the polymorphic
statement at `Λ : Type` produces universe levels `max 1 (u + 2)` where statements written in
`Type` have `u + 2`, and the kernel cannot compare the two forms of the sheaf categories. -/
theorem etaleModuleBaseChange_comp_directImageComp_of_commRing (X : EtaleModules.{u, 0} Λ Vb) :
    (etaleModuleBaseChange Λ fb f j j' sq.w).app ((etaleModuleDirectImage.{u, 0} Λ σ).obj X) ≫
        (etaleModuleDirectImage.{u, 0} Λ f).map ((etaleModuleBaseChange Λ σ a j' j' sqσ.w).app X) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.app
          ((etaleModuleInverseImage.{u, 0} Λ j').obj X) =
      (etaleModuleInverseImage.{u, 0} Λ j).map
          ((etaleModuleDirectImageComp.{u, 0} Λ σ fb fb hσ.symm).hom.app X) ≫
        (etaleModuleBaseChange Λ fb f j j' sq.w).app X := by
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ j).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.comp_obj, Functor.map_comp]
  have hU₁ := unit_comp_map_etaleModuleBaseChange Λ fb f j j' sq.w
    ((etaleModuleDirectImage.{u, 0} Λ σ).obj X)
  have hU₂ := unit_comp_map_etaleModuleBaseChange Λ σ a j' j' sqσ.w X
  have hU₃ := unit_comp_map_etaleModuleBaseChange Λ fb f j j' sq.w X
  have hu := (etaleModuleInverseImageAdj.{u, 0} Λ j).unit.naturality
    ((etaleModuleDirectImageComp.{u, 0} Λ σ fb fb hσ.symm).hom.app X)
  have hI := (etaleModuleDirectImageComp.{u, 0} Λ f j (f ≫ j) rfl).inv.naturality
    ((etaleModuleBaseChange Λ σ a j' j' sqσ.w).app X)
  have hH := (etaleModuleDirectImageComp.{u, 0} Λ j' fb (f ≫ j) sq.w).hom.naturality
    ((etaleModuleBaseChange Λ σ a j' j' sqσ.w).app X)
  have hc := (etaleModuleDirectImageComp.{u, 0} Λ σ fb fb hσ.symm).hom.naturality
    ((etaleModuleInverseImageAdj.{u, 0} Λ j').unit.app X)
  have hcoh := directImageComp_paste_coherence Λ fb f j j' σ a sq.w sqσ.w hσ.symm ha.symm
    ((etaleModuleInverseImage.{u, 0} Λ j').obj X)
  rw [← Category.assoc, hU₁]
  simp only [Category.assoc]
  rw [reassoc_of% hI.symm, reassoc_of% hH.symm, ← Functor.map_comp_assoc, hU₂, ← reassoc_of% hu,
    hU₃, ← reassoc_of% hc]
  simp only [Functor.map_comp, Category.assoc] at hcoh ⊢
  rw [hcoh]

include hσ ha in
/-- **The pasting of the isomorphisms `j'^{-1} f̄_* ≅ f_* j^{-1}` along `σ`**: through
`f̄_* σ_* = f̄_*` and `f_* a_* = f_*`, the isomorphism at `σ_* X` followed by `f_*` of the one of
`σ` is the one at `X`. -/
theorem restrictionDirectImageIso_inv_app_comp (X : EtaleModules.{u, 0} Λ Vb) :
    (etaleModuleRestriction.{u, 0} Λ j).map
        ((etaleModuleDirectImageComp.{u, 0} Λ σ fb fb hσ.symm).hom.app X) ≫
      (restrictionDirectImageIso Λ j j' f fb sq).inv.app X =
    (restrictionDirectImageIso Λ j j' f fb sq).inv.app ((etaleModuleDirectImage.{u, 0} Λ σ).obj X) ≫
      (etaleModuleDirectImage.{u, 0} Λ f).map
        ((restrictionDirectImageIso Λ j' j' a σ sqσ).inv.app X) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.app
        ((etaleModuleRestriction.{u, 0} Λ j').obj X) := by
  have key := etaleModuleBaseChange_comp_directImageComp_of_commRing Λ j j' f fb sq a σ sqσ hσ ha X
  have hn := (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).inv.naturality
    ((etaleModuleDirectImageComp.{u, 0} Λ σ fb fb hσ.symm).hom.app X)
  have hc := (etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.naturality
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j').hom.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn hc
  rw [restrictionDirectImageIso_inv_app, restrictionDirectImageIso_inv_app,
    restrictionDirectImageIso_inv_app, reassoc_of% hn]
  simp only [Category.assoc]
  exact pasteChase (etaleModuleDirectImage.{u, 0} Λ f)
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).inv.app
      ((etaleModuleDirectImage.{u, 0} Λ fb).obj ((etaleModuleDirectImage.{u, 0} Λ σ).obj X)))
    ((etaleModuleInverseImage.{u, 0} Λ j).map
      ((etaleModuleDirectImageComp.{u, 0} Λ σ fb fb hσ.symm).hom.app X))
    ((etaleModuleBaseChange Λ fb f j j' sq.w).app X)
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j').hom.app X)
    ((etaleModuleBaseChange Λ fb f j j' sq.w).app ((etaleModuleDirectImage.{u, 0} Λ σ).obj X))
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j').hom.app
      ((etaleModuleDirectImage.{u, 0} Λ σ).obj X))
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j').inv.app
      ((etaleModuleDirectImage.{u, 0} Λ σ).obj X))
    ((etaleModuleBaseChange Λ σ a j' j' sqσ.w).app X)
    ((etaleModuleDirectImage.{u, 0} Λ a).map
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j').hom.app X))
    ((etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.app
      ((etaleModuleInverseImage.{u, 0} Λ j').obj X))
    ((etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.app
      ((etaleModuleRestriction.{u, 0} Λ j').obj X))
    (Iso.hom_inv_id_app _ _) hc key

/-- Inverting the isomorphisms in a commutative square. -/
private lemma invChase {C : Type*} [Category* C] {P Q P' Q' S : C} (rX : P ≅ Q) (rσ : P' ≅ Q')
    (t : S ≅ P') (A : Q' ⟶ Q) (B : S ⟶ P) (h : A ≫ rX.inv = rσ.inv ≫ t.inv ≫ B) :
    t.hom ≫ rσ.hom ≫ A = B ≫ rX.hom := by
  rw [← cancel_mono rX.inv, Category.assoc, Category.assoc, h, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

include hσ ha in
/-- `Stacks.EtaleCohomology.restrictionDirectImageIso_inv_app_comp` for the isomorphisms
themselves. -/
theorem restrictionDirectImageIso_hom_app_comp (X : EtaleModules.{u, 0} Λ Vb) :
    (etaleModuleDirectImage.{u, 0} Λ f).map
        ((restrictionDirectImageIso Λ j' j' a σ sqσ).hom.app X) ≫
      (restrictionDirectImageIso Λ j j' f fb sq).hom.app
        ((etaleModuleDirectImage.{u, 0} Λ σ).obj X) ≫
      (etaleModuleRestriction.{u, 0} Λ j).map
        ((etaleModuleDirectImageComp.{u, 0} Λ σ fb fb hσ.symm).hom.app X) =
    (etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.app
        ((etaleModuleRestriction.{u, 0} Λ j').obj X) ≫
      (restrictionDirectImageIso Λ j j' f fb sq).hom.app X := by
  have h := restrictionDirectImageIso_inv_app_comp Λ j j' f fb sq a σ sqσ hσ ha X
  exact invChase ((restrictionDirectImageIso Λ j j' f fb sq).app X)
    ((restrictionDirectImageIso Λ j j' f fb sq).app ((etaleModuleDirectImage.{u, 0} Λ σ).obj X))
    ((etaleModuleDirectImage.{u, 0} Λ f).mapIso ((restrictionDirectImageIso Λ j' j' a σ sqσ).app X))
    _ _ h

/-- The category chase behind `Stacks.EtaleCohomology.extensionByZeroDirectImageMap_comp_twist`. -/
private lemma twistChase {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {G A T₁ T₂ T₃ A' : C} {Z Z₂ Z₃ : D} (e : G ⟶ A) (uG : G ⟶ T₁) (uA : A ⟶ T₂) (w₁ : T₁ ⟶ T₂)
    (w₂ : T₂ ⟶ T₃) (aU : A ⟶ A') (r' : A' ⟶ T₃) (k : F.obj A ⟶ F.obj G)
    (k' : F.obj A' ⟶ F.obj T₁) (R : F.obj T₁ ⟶ Z) (RA : F.obj T₂ ⟶ Z₂) (Rσ : F.obj T₃ ⟶ Z₃)
    (m₁ : Z ⟶ Z₂) (m₂ : Z₂ ⟶ Z₃) (c : Z₃ ⟶ Z)
    (hn₁ : F.map w₁ ≫ RA = R ≫ m₁) (hn₂ : F.map w₂ ≫ Rσ = RA ≫ m₂) (hu : e ≫ uA = uG ≫ w₁)
    (hext : uA ≫ w₂ = aU ≫ r') (hP : F.map r' ≫ Rσ ≫ c = k' ≫ R)
    (hk : F.map aU ≫ k' = k ≫ F.map uG) :
    F.map e ≫ k ≫ F.map uG ≫ R = F.map uG ≫ R ≫ m₁ ≫ m₂ ≫ c := by
  rw [← reassoc_of% hn₁, ← reassoc_of% hn₂, ← F.map_comp_assoc, ← F.map_comp_assoc, ← hu,
    Category.assoc, hext, F.map_comp_assoc, F.map_comp_assoc, hP, reassoc_of% hk]

include hσ ha in
/-- **The canonical map `j_!(f_* G) ⟶ f̄_*(j'_! G)` carries a twist through `f` to the extension
by zero of the twist, through `f̄`.**  For `ε : G ⟶ a_* G`, `j_!` of `f_* ε` followed by
`f_* a_* = f_*`, then the canonical map, is the canonical map followed by `f̄_*` of
`j'_!(ε)` and the canonical map `j'_! a_* ⟶ σ_* j'_!`, then `f̄_* σ_* = f̄_*`. -/
theorem extensionByZeroDirectImageMap_comp_twist (G : EtaleModules.{u, 0} Λ V)
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ a).obj G) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).map ((etaleModuleDirectImage.{u, 0} Λ f).map ε ≫
        (etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.app G) ≫
      extensionByZeroDirectImageMap Λ j j' f fb sq G =
    extensionByZeroDirectImageMap Λ j j' f fb sq G ≫
      (etaleModuleDirectImage.{u, 0} Λ fb).map ((etaleModuleExtensionByZero.{u, 0} Λ j').map ε ≫
        extensionByZeroDirectImageMap Λ j' j' a σ sqσ G) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ σ fb fb hσ.symm).hom.app
        ((etaleModuleExtensionByZero.{u, 0} Λ j').obj G) := by
  apply ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).injective
  have hext : ∀ N : EtaleModules.{u, 0} Λ V,
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _)
        (extensionByZeroDirectImageMap Λ j j' f fb sq N) =
      (etaleModuleDirectImage.{u, 0} Λ f).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app N) ≫
        (restrictionDirectImageIso Λ j j' f fb sq).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ j').obj N) := fun N => Equiv.apply_symm_apply _ _
  have hext' : (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app
        ((etaleModuleDirectImage.{u, 0} Λ a).obj G) ≫
      (etaleModuleRestriction.{u, 0} Λ j').map (extensionByZeroDirectImageMap Λ j' j' a σ sqσ G) =
      (etaleModuleDirectImage.{u, 0} Λ a).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app G) ≫
        (restrictionDirectImageIso Λ j' j' a σ sqσ).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ j').obj G) :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hu := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.naturality ε
  have hn₁ := (restrictionDirectImageIso Λ j j' f fb sq).hom.naturality
    ((etaleModuleExtensionByZero.{u, 0} Λ j').map ε)
  have hn₂ := (restrictionDirectImageIso Λ j j' f fb sq).hom.naturality
    (extensionByZeroDirectImageMap Λ j' j' a σ sqσ G)
  have hk := (etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.naturality
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app G)
  have hP := restrictionDirectImageIso_hom_app_comp Λ j j' f fb sq a σ sqσ hσ ha
    ((etaleModuleExtensionByZero.{u, 0} Λ j').obj G)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hu hn₁ hn₂ hk
  rw [Adjunction.homEquiv_naturality_left, hext, Adjunction.homEquiv_naturality_right, hext]
  simp only [Functor.map_comp, Category.assoc]
  exact twistChase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn₁ hn₂ hu hext' hP hk

/-- **The restriction to `V` of a map `ε₀ : G₀ ⟶ σ_* G₀` on `V̄`**:
`j'^{-1} G₀ ⟶ j'^{-1} σ_* G₀ ≅ a_* j'^{-1} G₀`. -/
def restrictionTwist (G₀ : EtaleModules.{u, 0} Λ Vb)
    (ε₀ : G₀ ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G₀) :
    (etaleModuleRestriction.{u, 0} Λ j').obj G₀ ⟶
      (etaleModuleDirectImage.{u, 0} Λ a).obj ((etaleModuleRestriction.{u, 0} Λ j').obj G₀) :=
  (etaleModuleRestriction.{u, 0} Λ j').map ε₀ ≫
    (restrictionDirectImageIso Λ j' j' a σ sqσ).inv.app G₀

/-- **The endomorphism of `f_* G` given by a map `ε : G ⟶ a_* G`**: `f_* ε` followed by
`f_* a_* = f_*`. -/
def directImageTwist (G : EtaleModules.{u, 0} Λ V)
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ a).obj G) :
    (etaleModuleDirectImage.{u, 0} Λ f).obj G ⟶ (etaleModuleDirectImage.{u, 0} Λ f).obj G :=
  (etaleModuleDirectImage.{u, 0} Λ f).map ε ≫
    (etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.app G

omit [Mono j'] in
/-- **`Stacks.EtaleCohomology.restrictionTwist` is natural** in the pair `(G₀, ε₀)`. -/
lemma restrictionTwist_naturality {G₀ G₀' : EtaleModules.{u, 0} Λ Vb}
    (ε₀ : G₀ ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G₀)
    (ε₀' : G₀' ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G₀') (x : G₀ ⟶ G₀')
    (hx : x ≫ ε₀' = ε₀ ≫ (etaleModuleDirectImage.{u, 0} Λ σ).map x) :
    (etaleModuleRestriction.{u, 0} Λ j').map x ≫ restrictionTwist Λ j' a σ sqσ G₀' ε₀' =
      restrictionTwist Λ j' a σ sqσ G₀ ε₀ ≫
        (etaleModuleDirectImage.{u, 0} Λ a).map ((etaleModuleRestriction.{u, 0} Λ j').map x) := by
  have h := (restrictionDirectImageIso Λ j' j' a σ sqσ).inv.naturality x
  dsimp only [Functor.comp_obj, Functor.comp_map] at h
  rw [restrictionTwist, restrictionTwist, ← Functor.map_comp_assoc, hx, Functor.map_comp_assoc, h,
    Category.assoc]

/-- **`Stacks.EtaleCohomology.directImageTwist` is natural** in the pair `(G, ε)`. -/
lemma directImageTwist_naturality {G G' : EtaleModules.{u, 0} Λ V}
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ a).obj G)
    (ε' : G' ⟶ (etaleModuleDirectImage.{u, 0} Λ a).obj G') (y : G ⟶ G')
    (hy : y ≫ ε' = ε ≫ (etaleModuleDirectImage.{u, 0} Λ a).map y) :
    (etaleModuleDirectImage.{u, 0} Λ f).map y ≫ directImageTwist Λ f a ha G' ε' =
      directImageTwist Λ f a ha G ε ≫ (etaleModuleDirectImage.{u, 0} Λ f).map y := by
  have h := (etaleModuleDirectImageComp.{u, 0} Λ a f f ha.symm).hom.naturality y
  dsimp only [Functor.comp_obj, Functor.comp_map] at h
  rw [directImageTwist, directImageTwist, ← Functor.map_comp_assoc, hy, Functor.map_comp_assoc, h,
    Category.assoc]

include hσ in
/-- `Stacks.EtaleCohomology.extensionByZeroDirectImageMap_comp_twist` for the restriction to `V`
of a map `ε₀ : G₀ ⟶ σ_* G₀` on `V̄`: the canonical map carries `j_!` of the induced endomorphism
of `f_* j'^{-1} G₀` to `f̄_*` of the extension by zero of `ε₀`, followed by `f̄_* σ_* = f̄_*`. -/
theorem extensionByZeroDirectImageMap_comp_extensionByZeroTwist (G₀ : EtaleModules.{u, 0} Λ Vb)
    (ε₀ : G₀ ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G₀) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).map (directImageTwist Λ f a ha
        ((etaleModuleRestriction.{u, 0} Λ j').obj G₀) (restrictionTwist Λ j' a σ sqσ G₀ ε₀)) ≫
      extensionByZeroDirectImageMap Λ j j' f fb sq ((etaleModuleRestriction.{u, 0} Λ j').obj G₀) =
    extensionByZeroDirectImageMap Λ j j' f fb sq ((etaleModuleRestriction.{u, 0} Λ j').obj G₀) ≫
      (etaleModuleDirectImage.{u, 0} Λ fb).map (extensionByZeroTwist Λ j' a σ sqσ G₀ ε₀) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ σ fb fb hσ.symm).hom.app
        ((etaleModuleExtensionByZero.{u, 0} Λ j').obj
          ((etaleModuleRestriction.{u, 0} Λ j').obj G₀)) := by
  rw [directImageTwist, restrictionTwist, extensionByZeroTwist]
  exact extensionByZeroDirectImageMap_comp_twist Λ j j' f fb sq a σ sqσ hσ ha _ _

end Stacks.EtaleCohomology

end
