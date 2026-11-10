module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CechKunneth.SchemeCech
public import StacksFrontier.AlgebraicGeometry.DeRham.StructureSheafConnection
public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.ChartBoxSectionRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductFunctor

/-!
# The sections of a box product over products of opens

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `ψ : k ⟶ Γ(S, 𝒪_S)` a ring map, `ℱ` an
`𝒪_X`-module and `𝒢` an `𝒪_Y`-module. Opens `A ⊆ X` and `B ⊆ Y` give the open
`A × B = pr₁⁻¹A ∩ pr₂⁻¹B` of `X ×_S Y`, and sections `s` of `ℱ` over `A` and `t` of `𝒢` over `B`
give the section `s ⊠ t` of `ℱ ⊠ 𝒢 = pr₁^*ℱ ⊗ pr₂^*𝒢` over `A × B`. This file packages this as a
morphism of presheaves of `k`-modules on pairs of opens `Γ(A, ℱ) ⊗_k Γ(B, 𝒢) ⟶ Γ(A × B, ℱ ⊠ 𝒢)`,
`s ⊗ t ↦ s ⊠ t`.

## Main definitions

* `Stacks.CechKunneth.baseRingHom`: the ring map `k ⟶ Γ(W, 𝒪_W)` of a scheme over `S`.
* `Stacks.CechKunneth.boxOpen`: the open `pr₁⁻¹A ∩ pr₂⁻¹B`, as a functor on pairs of opens.
* `Stacks.CechKunneth.boxPresheaf`: the presheaf `(A, B) ↦ Γ(A × B, ℱ ⊠ 𝒢)` of `k`-modules.
* `Stacks.CechKunneth.boxMap`: the morphism `Γ(A, ℱ) ⊗_k Γ(B, 𝒢) ⟶ Γ(A × B, ℱ ⊠ 𝒢)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry TensorProduct
open Stacks.Tag01VSPullbackTensor Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.CechKunneth

variable {k : Type u} [CommRing k] {S : Scheme.{u}} (ψ : k →+* Γ(S, ⊤))

/-- **The ring map `k ⟶ Γ(W, 𝒪_W)` of a scheme `π : W ⟶ S` over `S`**, through `ψ`. -/
def baseRingHom {W : Scheme.{u}} (π : W ⟶ S) : k →+* Γ(W, ⊤) :=
  (π.appLE ⊤ ⊤ (show ⊤ ≤ π ⁻¹ᵁ ⊤ from le_top)).hom.comp ψ

/-- The image of a scalar of `k` in `Γ(V, 𝒪_W)` is the image along `π.appLE`. -/
theorem map_baseRingHom {W : Scheme.{u}} (π : W ⟶ S) (V : W.Opens) (x : k) :
    (W.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (baseRingHom ψ π x) =
      (π.appLE ⊤ V (show V ≤ π ⁻¹ᵁ ⊤ from le_top)).hom (ψ x) := by
  rw [baseRingHom, RingHom.comp_apply, ← CommRingCat.comp_apply]
  simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]
  rfl

/-- **Scalars of `k` are compatible with the comap along a morphism over `S`.** -/
theorem app_map_baseRingHom {Z W : Scheme.{u}} (g : Z ⟶ W) (π : W ⟶ S) (V : W.Opens)
    (V' : Z.Opens) (hV : V' ≤ g ⁻¹ᵁ V) (x : k) :
    (Z.presheaf.map (homOfLE hV).op).hom ((g.app V).hom
      ((W.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (baseRingHom ψ π x))) =
      (Z.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op).hom (baseRingHom ψ (g ≫ π) x) := by
  rw [map_baseRingHom, map_baseRingHom]
  change (π.appLE ⊤ V (show V ≤ π ⁻¹ᵁ ⊤ from le_top) ≫ g.appLE V V' hV).hom (ψ x) = _
  rw [Scheme.Hom.appLE_comp_appLE]

variable {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The open `pr₁⁻¹A ∩ pr₂⁻¹B` of `X ×_S Y`**, as a functor on pairs of opens. -/
def boxOpen : LatProd X.Opens Y.Opens ⥤ (pullback a b).Opens :=
  Monotone.functor (f := fun Z => pullback.fst a b ⁻¹ᵁ Z.fst ⊓ pullback.snd a b ⁻¹ᵁ Z.snd)
    fun _ _ h => inf_le_inf (Scheme.Hom.preimage_mono _ (LatProd.fst_mono h))
      (Scheme.Hom.preimage_mono _ (LatProd.snd_mono h))

/-- The open `(boxOpen a b).obj Z` is `pr₁⁻¹ Z.fst ⊓ pr₂⁻¹ Z.snd`. -/
theorem boxOpen_obj (Z : LatProd X.Opens Y.Opens) :
    (boxOpen a b).obj Z = pullback.fst a b ⁻¹ᵁ Z.fst ⊓ pullback.snd a b ⁻¹ᵁ Z.snd :=
  rfl

/-- The open `pr₁⁻¹A ∩ pr₂⁻¹B` is contained in `pr₁⁻¹A`. -/
theorem boxOpen_le_fst (Z : LatProd X.Opens Y.Opens) :
    (boxOpen a b).obj Z ≤ pullback.fst a b ⁻¹ᵁ Z.fst :=
  inf_le_left

/-- The open `pr₁⁻¹A ∩ pr₂⁻¹B` is contained in `pr₂⁻¹B`. -/
theorem boxOpen_le_snd (Z : LatProd X.Opens Y.Opens) :
    (boxOpen a b).obj Z ≤ pullback.snd a b ⁻¹ᵁ Z.snd :=
  inf_le_right

variable (F : X.Modules) (G : Y.Modules)

/-- **The presheaf `(A, B) ↦ Γ(pr₁⁻¹A ∩ pr₂⁻¹B, ℱ ⊠ 𝒢)` of `k`-modules.** -/
def boxPresheaf : (LatProd X.Opens Y.Opens)ᵒᵖ ⥤ ModuleCat.{u} k :=
  (boxOpen a b).op ⋙ sectionsK (pullback a b) (baseRingHom ψ (pullback.fst a b ≫ a))
    (externalTensorProduct a b F G)

/-- The section `s ⊠ t` of `ℱ ⊠ 𝒢` over `pr₁⁻¹A ∩ pr₂⁻¹B`. -/
def boxSection (Z : LatProd X.Opens Y.Opens) (s : Γ(F, Z.fst)) (t : Γ(G, Z.snd)) :
    Γ(externalTensorProduct a b F G, (boxOpen a b).obj Z) :=
  externalTensorSection a b F G s t ((boxOpen a b).obj Z) (boxOpen_le_fst a b Z)
    (boxOpen_le_snd a b Z)

/-- The section `s ⊠ t` is additive in `s`. -/
theorem boxSection_add_left (Z : LatProd X.Opens Y.Opens) (s s' : Γ(F, Z.fst))
    (t : Γ(G, Z.snd)) :
    boxSection a b F G Z (s + s') t = boxSection a b F G Z s t + boxSection a b F G Z s' t :=
  externalTensorSection_add_left a b F G s s' t _ _ _

/-- The section `s ⊠ t` is additive in `t`. -/
theorem boxSection_add_right (Z : LatProd X.Opens Y.Opens) (s : Γ(F, Z.fst))
    (t t' : Γ(G, Z.snd)) :
    boxSection a b F G Z s (t + t') = boxSection a b F G Z s t + boxSection a b F G Z s t' :=
  externalTensorSection_add_right a b F G s t t' _ _ _

/-- Restricting the unit image of `r • s` gives the pullback of `r` times that of `s`. -/
private theorem restrict_modulesPullbackUnit_smul {W Z : Scheme.{u}} (f : W ⟶ Z) (M : Z.Modules)
    {U : Z.Opens} {V : W.Opens} (h : V ≤ f ⁻¹ᵁ U) (r : Γ(Z, U)) (s : Γ(M, U)) :
    (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op)
        (modulesPullbackUnit f M U (r • s)) =
      (W.presheaf.map (homOfLE h).op).hom ((f.app U) r) •
        (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op)
          (modulesPullbackUnit f M U s) :=
  (congrArg _ (Scheme.Modules.Hom.app_smul _ r s)).trans (Scheme.Modules.map_smul _ _ _ _)

/-- For a function `r` on `A`, `(r • s) ⊠ t = pr₁^*r • (s ⊠ t)`. -/
theorem boxSection_smul_left (Z : LatProd X.Opens Y.Opens) (r : Γ(X, Z.fst)) (s : Γ(F, Z.fst))
    (t : Γ(G, Z.snd)) :
    boxSection a b F G Z (r • s) t =
      ((pullback a b).presheaf.map (homOfLE (boxOpen_le_fst a b Z)).op).hom
        ((pullback.fst a b).app Z.fst r) • boxSection a b F G Z s t := by
  refine (congrArg (fun z ↦ toTensorSheafSection (pullback a b).toRingedSpace
      ((Scheme.Modules.pullback (pullback.fst a b)).obj F)
      ((Scheme.Modules.pullback (pullback.snd a b)).obj G) (op ((boxOpen a b).obj Z))
      (z ⊗ₜ (((Scheme.Modules.pullback (pullback.snd a b)).obj G).presheaf.map
        (homOfLE (boxOpen_le_snd a b Z)).op)
        (modulesPullbackUnit (pullback.snd a b) G Z.snd t)))
    (restrict_modulesPullbackUnit_smul _ _ _ r s)).trans ?_
  exact AlgebraicGeometry.Scheme.Hom.toTensorSheafSection_smul_tmul (pullback a b).toRingedSpace
    _ _ (op ((boxOpen a b).obj Z)) _ _ _

/-- For a function `r` on `B`, `s ⊠ (r • t) = pr₂^*r • (s ⊠ t)`. -/
theorem boxSection_smul_right (Z : LatProd X.Opens Y.Opens) (s : Γ(F, Z.fst)) (r : Γ(Y, Z.snd))
    (t : Γ(G, Z.snd)) :
    boxSection a b F G Z s (r • t) =
      ((pullback a b).presheaf.map (homOfLE (boxOpen_le_snd a b Z)).op).hom
        ((pullback.snd a b).app Z.snd r) • boxSection a b F G Z s t := by
  refine (congrArg (fun z ↦ toTensorSheafSection (pullback a b).toRingedSpace
      ((Scheme.Modules.pullback (pullback.fst a b)).obj F)
      ((Scheme.Modules.pullback (pullback.snd a b)).obj G) (op ((boxOpen a b).obj Z))
      ((((Scheme.Modules.pullback (pullback.fst a b)).obj F).presheaf.map
        (homOfLE (boxOpen_le_fst a b Z)).op)
        (modulesPullbackUnit (pullback.fst a b) F Z.fst s) ⊗ₜ z))
    (restrict_modulesPullbackUnit_smul _ _ _ r t)).trans ?_
  exact AlgebraicGeometry.Scheme.Hom.toTensorSheafSection_tmul_smul (pullback a b).toRingedSpace
    _ _ (op ((boxOpen a b).obj Z)) _ _ _

/-- The section of `ℱ ⊠ 𝒢` attached to restrictions of two local sections is the one attached to
the two sections. -/
theorem externalTensorSection_res {U U' : X.Opens} {V V' : Y.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (s : Γ(F, U)) (t : Γ(G, V)) (W : (pullback a b).Opens) (h₁ : W ≤ pullback.fst a b ⁻¹ᵁ U')
    (h₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    externalTensorSection a b F G (F.presheaf.map (homOfLE hU).op s)
        (G.presheaf.map (homOfLE hV).op t) W h₁ h₂ =
      externalTensorSection a b F G s t W (h₁.trans (Scheme.Hom.preimage_mono _ hU))
        (h₂.trans (Scheme.Hom.preimage_mono _ hV)) := by
  simp only [externalTensorSection]
  rw [modulesPullbackUnit_map, modulesPullbackUnit_map, presheaf_map_map, presheaf_map_map]

/-- The section `s ⊠ t` is compatible with restriction of the two sections. -/
theorem boxSection_map {Z Z' : LatProd X.Opens Y.Opens} (h : Z' ≤ Z) (s : Γ(F, Z.fst))
    (t : Γ(G, Z.snd)) :
    (externalTensorProduct a b F G).presheaf.map (homOfLE ((boxOpen a b).monotone h)).op
        (boxSection a b F G Z s t) =
      boxSection a b F G Z' (F.presheaf.map (homOfLE (LatProd.fst_mono h)).op s)
        (G.presheaf.map (homOfLE (LatProd.snd_mono h)).op t) :=
  (externalTensorSection_presheaf_map a b F G s t _ _
    ((boxOpen_le_fst a b Z').trans (Scheme.Hom.preimage_mono _ (LatProd.fst_mono h)))
    ((boxOpen_le_snd a b Z').trans (Scheme.Hom.preimage_mono _ (LatProd.snd_mono h))) _).trans
    (externalTensorSection_res a b F G _ _ s t _ _ _).symm

/-- **The section `s ⊠ t`, as a `k`-bilinear map.** -/
def boxBilin (Z : LatProd X.Opens Y.Opens) :
    (sectionsK X (baseRingHom ψ a) F).obj (op Z.fst) →ₗ[k]
      (sectionsK Y (baseRingHom ψ b) G).obj (op Z.snd) →ₗ[k] (boxPresheaf ψ a b F G).obj (op Z) :=
  LinearMap.mk₂ k (fun s t => boxSection a b F G Z s t)
    (fun s s' t => boxSection_add_left a b F G Z s s' t)
    (fun x s t => (boxSection_smul_left a b F G Z _ s t).trans (congrArg (· • _)
      (app_map_baseRingHom ψ (pullback.fst a b) a Z.fst _ (boxOpen_le_fst a b Z) x)))
    (fun s t t' => boxSection_add_right a b F G Z s t t')
    (fun x s t => (boxSection_smul_right a b F G Z s _ t).trans (congrArg (· • _)
      ((app_map_baseRingHom ψ (pullback.snd a b) b Z.snd _ (boxOpen_le_snd a b Z) x).trans
        (by rw [pullback.condition]; rfl))))

/-- The bilinear map `boxBilin` sends `(s, t)` to `s ⊠ t`. -/
theorem boxBilin_apply (Z : LatProd X.Opens Y.Opens) (s : Γ(F, Z.fst)) (t : Γ(G, Z.snd)) :
    boxBilin ψ a b F G Z s t = boxSection a b F G Z s t :=
  rfl

/-- **The morphism `Γ(A, ℱ) ⊗_k Γ(B, 𝒢) ⟶ Γ(pr₁⁻¹A ∩ pr₂⁻¹B, ℱ ⊠ 𝒢)` of presheaves of
`k`-modules on pairs of opens**, `s ⊗ t ↦ s ⊠ t`. -/
def boxMap : extTensor (sectionsK X (baseRingHom ψ a) F) (sectionsK Y (baseRingHom ψ b) G) ⟶
    boxPresheaf ψ a b F G where
  app Z := ModuleCat.homEquiv.symm (TensorProduct.lift (boxBilin ψ a b F G Z.unop))
  naturality _ _ f := ModuleCat.hom_ext (TensorProduct.ext' fun s t =>
    (boxSection_map a b F G (leOfHom f.unop) s t).symm)

/-- The morphism `boxMap` sends `s ⊗ t` to `s ⊠ t`. -/
theorem boxMap_app_tmul (Z : LatProd X.Opens Y.Opens) (s : Γ(F, Z.fst)) (t : Γ(G, Z.snd)) :
    ((boxMap ψ a b F G).app (op Z)).hom (s ⊗ₜ t) = boxSection a b F G Z s t :=
  rfl

end Stacks.CechKunneth

end
