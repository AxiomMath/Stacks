module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.Det

/-!
# The local determinants along a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes and `K` a perfect object of `D(𝒪_Y)` of Tor amplitude in
`[-1, 0]`. For affine opens `V ⊆ Y` and `W ⊆ X` with `f(W) ⊆ V`, the local avatar of `Lf^*K` on
`W` is the derived base change of the local avatar of `K` on `V` along `Γ(Y, V) → Γ(X, W)`, so
the determinant of the latter base-changes to the determinant of the former. These maps are
compatible with restriction on both sides, exhibit their targets as base changes, and preserve
the canonical elements of rank-zero objects.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.pullbackDetMap`: the map `det(M_V) → det(M'_W)`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite TwoTermDeterminant
open AlgebraicGeometry.StandardModel

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (K : PerfectTwoTermAmplitude Y)

/-- The identification `Γ(X, W) ⊗ᴸ M_V ≅ M'_W` of the local avatar of `Lf^*K` on `W` with the
derived base change of the local avatar of `K` on `V`, along a ring map `g` with
`Spec(g) ≫ (V ↪ Y) = (W ↪ X) ≫ f`. -/
def pullbackTransitionIso (V : Y.affineOpens) (W : X.affineOpens) (g : Γ(Y, V) ⟶ Γ(X, W))
    (hg : Spec.map g ≫ V.2.fromSpec = W.2.fromSpec ≫ f) :
    (Lext g.hom).obj (localComplex K V.2.fromSpec).obj ≅
      (localComplex (pullbackObj f K) W.2.fromSpec).obj :=
  transitionIso K g V.2.fromSpec (W.2.fromSpec ≫ f) hg ≪≫ (pullbackLocalIso f K W.2.fromSpec).symm

/-- The map of local determinants along `g`, semilinear over `g`. -/
def pullbackDetMapAt (V : Y.affineOpens) (W : X.affineOpens) (g : Γ(Y, V) ⟶ Γ(X, W))
    (hg : Spec.map g ≫ V.2.fromSpec = W.2.fromSpec ≫ f) :
    localDet K V.2.fromSpec →ₛₗ[g.hom] localDet (pullbackObj f K) W.2.fromSpec :=
  baseChangeMap g.hom _ _ (pullbackTransitionIso f K V W g hg)

/-- The map `pullbackDetMapAt` depends only on the ring map `g`, not on the proof of the
compatibility `Spec(g) ≫ (V ↪ Y) = (W ↪ X) ≫ f`. -/
theorem pullbackDetMapAt_congr (V : Y.affineOpens) (W : X.affineOpens) {g g' : Γ(Y, V) ⟶ Γ(X, W)}
    (he : g = g') (hg : Spec.map g ≫ V.2.fromSpec = W.2.fromSpec ≫ f)
    (hg' : Spec.map g' ≫ V.2.fromSpec = W.2.fromSpec ≫ f) (x : localDet K V.2.fromSpec) :
    pullbackDetMapAt f K V W g hg x = pullbackDetMapAt f K V W g' hg' x := by
  subst he
  rfl

/-- **The map of local determinants along `f`**, for affine opens `W ≤ f⁻¹V`. -/
def pullbackDetMap (V : Y.affineOpens) (W : X.affineOpens) (h : (W : X.Opens) ≤ f ⁻¹ᵁ V) :
    localDet K V.2.fromSpec →ₛₗ[(f.appLE V W h).hom] localDet (pullbackObj f K) W.2.fromSpec :=
  pullbackDetMapAt f K V W (f.appLE V W h) (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 W.2 h)

/-- The map `pullbackDetMap f K V W h` exhibits `det(M'_W)` as the base change of `det(M_V)`
along `Γ(Y, V) → Γ(X, W)`. -/
theorem isBaseChangeAlong_pullbackDetMap (V : Y.affineOpens) (W : X.affineOpens)
    (h : (W : X.Opens) ≤ f ⁻¹ᵁ V) :
    IsBaseChangeAlong (f.appLE V W h).hom (pullbackDetMap f K V W h) :=
  isBaseChangeAlong_baseChangeMap _ _

/-- The transition isomorphisms of `Lf^*K` and of `K` are compatible with the identifications. -/
theorem pullbackTransitionIso_comp_left (V : Y.affineOpens) {W W' : X.affineOpens}
    (g : Γ(Y, V) ⟶ Γ(X, W)) (hg : Spec.map g ≫ V.2.fromSpec = W.2.fromSpec ≫ f)
    (hWW : (W' : X.Opens) ≤ W)
    (hg' : Spec.map (g ≫ X.presheaf.map (homOfLE hWW).op) ≫ V.2.fromSpec = W'.2.fromSpec ≫ f) :
    (compIso g.hom (X.presheaf.map (homOfLE hWW).op).hom (localComplex K V.2.fromSpec).obj).symm ≪≫
        (Lext (X.presheaf.map (homOfLE hWW).op).hom).mapIso (pullbackTransitionIso f K V W g hg) ≪≫
        transitionIso (pullbackObj f K) (X.presheaf.map (homOfLE hWW).op) W.2.fromSpec
          W'.2.fromSpec (IsAffineOpen.map_fromSpec _ _ _) =
      pullbackTransitionIso f K V W' (g ≫ X.presheaf.map (homOfLE hWW).op) hg' := by
  have hf : Spec.map (X.presheaf.map (homOfLE hWW).op) ≫ W.2.fromSpec ≫ f =
      W'.2.fromSpec ≫ f := by
    rw [← Category.assoc]
    exact congrArg (· ≫ f) (IsAffineOpen.map_fromSpec _ _ _)
  have hc := transitionIso_comp K g (X.presheaf.map (homOfLE hWW).op) V.2.fromSpec
    (W.2.fromSpec ≫ f) (W'.2.fromSpec ≫ f) hg hf hg'
  have hp := pullbackLocalIso_transitionIso f K (X.presheaf.map (homOfLE hWW).op) W.2.fromSpec
    W'.2.fromSpec (IsAffineOpen.map_fromSpec _ _ _) hf
  ext
  simp only [pullbackTransitionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, hc]
  congr 2
  rw [Iso.eq_comp_inv, Category.assoc, ← hp, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Compatibility with restriction on `X`.** -/
theorem detSystem_map_pullbackDetMapAt (V : Y.affineOpens) {W W' : X.affineOpens}
    (g : Γ(Y, V) ⟶ Γ(X, W)) (hg : Spec.map g ≫ V.2.fromSpec = W.2.fromSpec ≫ f)
    (hWW : (W' : X.Opens) ≤ W)
    (hg' : Spec.map (g ≫ X.presheaf.map (homOfLE hWW).op) ≫ V.2.fromSpec = W'.2.fromSpec ≫ f)
    (x : localDet K V.2.fromSpec) :
    (detSystem (pullbackObj f K)).map hWW (pullbackDetMapAt f K V W g hg x) =
      pullbackDetMapAt f K V W' (g ≫ X.presheaf.map (homOfLE hWW).op) hg' x := by
  change baseChangeMap _ _ _ _ (baseChangeMap _ _ _ _ x) = baseChangeMap _ _ _ _ x
  rw [← baseChangeMap_comp, pullbackTransitionIso_comp_left f K V g hg hWW hg']
  rfl

/-- The transition isomorphisms of `K` compose with the identifications. -/
theorem pullbackTransitionIso_comp_right {V V' : Y.affineOpens} (W : X.affineOpens)
    (hVV : (V' : Y.Opens) ≤ V) (g : Γ(Y, V') ⟶ Γ(X, W))
    (hg : Spec.map g ≫ V'.2.fromSpec = W.2.fromSpec ≫ f)
    (hg' : Spec.map (Y.presheaf.map (homOfLE hVV).op ≫ g) ≫ V.2.fromSpec = W.2.fromSpec ≫ f) :
    (compIso (Y.presheaf.map (homOfLE hVV).op).hom g.hom (localComplex K V.2.fromSpec).obj).symm ≪≫
        (Lext g.hom).mapIso (transitionIso K (Y.presheaf.map (homOfLE hVV).op) V.2.fromSpec
          V'.2.fromSpec (IsAffineOpen.map_fromSpec _ _ _)) ≪≫ pullbackTransitionIso f K V' W g hg =
      pullbackTransitionIso f K V W (Y.presheaf.map (homOfLE hVV).op ≫ g) hg' := by
  have hc := transitionIso_comp K (Y.presheaf.map (homOfLE hVV).op) g V.2.fromSpec V'.2.fromSpec
    (W.2.fromSpec ≫ f) (IsAffineOpen.map_fromSpec _ _ _) hg hg'
  ext
  simp only [pullbackTransitionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, hc]

/-- **Compatibility with restriction on `Y`.** -/
theorem pullbackDetMapAt_detSystem_map {V V' : Y.affineOpens} (W : X.affineOpens)
    (hVV : (V' : Y.Opens) ≤ V) (g : Γ(Y, V') ⟶ Γ(X, W))
    (hg : Spec.map g ≫ V'.2.fromSpec = W.2.fromSpec ≫ f)
    (hg' : Spec.map (Y.presheaf.map (homOfLE hVV).op ≫ g) ≫ V.2.fromSpec = W.2.fromSpec ≫ f)
    (x : localDet K V.2.fromSpec) :
    pullbackDetMapAt f K V' W g hg ((detSystem K).map hVV x) =
      pullbackDetMapAt f K V W (Y.presheaf.map (homOfLE hVV).op ≫ g) hg' x := by
  change baseChangeMap _ _ _ _ (baseChangeMap _ _ _ _ x) = baseChangeMap _ _ _ _ x
  rw [← baseChangeMap_comp, pullbackTransitionIso_comp_right f K W hVV g hg hg']
  rfl

/-- **Rank zero is preserved by derived pullback.** -/
theorem isRankZero_pullbackObj (hK : IsRankZero K) : IsRankZero (pullbackObj f K) := fun A u =>
  DeterminantTwoTerm.isRankZero_of_iso (pullbackLocalIso f K u).symm (hK A (u ≫ f))

/-- **The maps of local determinants along `f` preserve the canonical elements.** -/
theorem pullbackDetMapAt_delta (V : Y.affineOpens) (W : X.affineOpens) (g : Γ(Y, V) ⟶ Γ(X, W))
    (hg : Spec.map g ≫ V.2.fromSpec = W.2.fromSpec ≫ f) (hK : IsRankZero K) :
    pullbackDetMapAt f K V W g hg (delta (localComplex K V.2.fromSpec) (hK _ _)) =
      delta (localComplex (pullbackObj f K) W.2.fromSpec) (isRankZero_pullbackObj f K hK _ _) :=
  baseChangeMap_delta _ _ _ _

end AlgebraicGeometry.DeterminantTwoTerm

end
