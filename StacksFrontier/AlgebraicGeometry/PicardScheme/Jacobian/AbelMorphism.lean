module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.HilbertChartFull

/-!
# The Abel morphism `γ_d : Hilb^d_{X/S} ⟶ Pic⁰` (Stacks 0BA0 (4))

Let `f : X ⟶ S` be a proper smooth relative curve with a section `σ`, let `θ` be a Picard class
of `X` of degree `d` on every fibre, let `H` represent the degree-`d` Hilbert functor and let `A`
be a group object over `S` representing `Pic⁰_{X/S,σ}`. The rigidified class of
`𝒪_{X_T}(D) ⊗ pr_X^*θ^{-1}`, for `D` a degree-`d` family over `T`, has degree zero on every
fibre, so by the Yoneda lemma it defines a morphism `γ : H ⟶ A` over `S`, the Abel morphism of
[Stacks, Tag 0BA0] (4) followed by translation by `θ^{-1}` (which identifies `Pic^d` with
`Pic⁰`).

## Main definitions

* `Stacks.RigidifiedPicard.abelElement` — the element of `Pic⁰_{X/S,σ}(T)` attached to a morphism
  `T ⟶ H`.
* `Stacks.RigidifiedPicard.abelMorphism` — the morphism `γ : H ⟶ A`.
* `Stacks.RigidifiedPicard.abelMorphismFull` — the morphism `γ_d : H ⟶ P` into a group object `P`
  representing `Pic_{X/S,σ}`, classifying the rigidified class of `𝒪_{X_T}(D)`.

## Main results

* `Stacks.RigidifiedPicard.abelMorphism_spec` — `γ` classifies the classes `abelElement`:
  `e (m ≫ γ) = abelElement m`.
* `Stacks.RigidifiedPicard.abelMorphismFull_spec` — `γ_d` classifies the classes
  `abelElementFull`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsProper f]
  [SmoothOfRelativeDimension 1 f] [LocallyOfFiniteType f]
  (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
  (θ : Stacks.Picard.ofScheme X) {d : ℕ}
  (hθ : ∀ s : S, relativeInvertibleDegreeHomAt f hdim s θ = d)
  {H : Over S} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)

/-- **The element of `Pic⁰_{X/S,σ}(T)` attached to `m : T ⟶ H`**: the rigidified class of
`𝒪_{X_T}(D_m) ⊗ pr_X^*θ^{-1}`, for `D_m` the family classified by `m`. -/
def abelElement {T : Over S} (m : T ⟶ H) : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T) :=
  mkZero f hdim σ hσ (chartClass f σ hσ θ hH m)
    (schemePullbackClass_bcSection_chartClass f σ hσ θ hH m)
    (relativeInvertibleDegreeHomAt_chartClass f hdim σ hσ θ hH hθ m)

/-- The class in `Pic(X_T)` of `abelElement m` is the normalised Abel class of `D_m` translated by
`θ^{-1}`. -/
theorem smallEquiv_abelElement {T : Over S} (m : T ⟶ H) :
    smallEquiv _ ((((Multiplicative.toAdd (abelElement f hdim σ hσ θ hθ hH m) :
      groupZero f hdim σ hσ T) : group f σ hσ T)) : Stacks.Picard.smallOfScheme (bc f T)) =
      abelNormalized f σ hσ θ (hH.family m) :=
  smallEquiv_mkZero _ _ _ _ _ _ _

/-- The elements `abelElement` are compatible with base change: `abelElement (a ≫ m)` is the
pullback along `a` of `abelElement m`. -/
theorem abelElement_comp {T T' : Over S} (a : T' ⟶ T) (m : T ⟶ H) :
    abelElement f hdim σ hσ θ hθ hH (a ≫ m) =
      (functorZero f hdim σ hσ ⋙ forget GrpCat).map a.op (abelElement f hdim σ hσ θ hθ hH m) := by
  refine ext_functorZero f hdim σ hσ ?_
  rw [functorZero_map_val, smallEquiv_abelElement, smallEquiv_abelElement]
  exact chartClass_comp f σ hσ θ hH a m

variable (A : Grp (Over S)) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)

/-- **The Abel morphism** `γ : H ⟶ A` over `S`: the morphism classifying the universal
`abelElement`, through the representing isomorphism `e`. -/
def abelMorphism : H ⟶ A.X :=
  (e.inv.app (op H)).hom (abelElement f hdim σ hσ θ hθ hH (𝟙 H))

/-- **`γ` classifies the Abel classes**: for every `m : T ⟶ H`, the element of
`Pic⁰_{X/S,σ}(T)` corresponding under `e` to `m ≫ γ` is `abelElement m`, the rigidified class of
`𝒪_{X_T}(D_m) ⊗ pr_X^*θ^{-1}`. -/
theorem abelMorphism_spec {T : Over S} (m : T ⟶ H) :
    (e.hom.app (op T)).hom (m ≫ abelMorphism f hdim σ hσ θ hθ hH A e) =
      abelElement f hdim σ hσ θ hθ hH m := by
  have hn : (e.hom.app (op T)).hom ((yonedaGrp.obj A).map m.op
      (abelMorphism f hdim σ hσ θ hθ hH A e)) =
      (functorZero f hdim σ hσ).map m.op ((e.hom.app (op H)).hom
        (abelMorphism f hdim σ hσ θ hθ hH A e)) :=
    congrArg (fun φ => GrpCat.Hom.hom φ (abelMorphism f hdim σ hσ θ hθ hH A e))
      (e.hom.naturality m.op)
  have hinv : (e.hom.app (op H)).hom (abelMorphism f hdim σ hσ θ hθ hH A e) =
      abelElement f hdim σ hσ θ hθ hH (𝟙 H) := by
    show ((e.inv ≫ e.hom).app (op H)).hom _ = _
    rw [e.inv_hom_id]; rfl
  refine hn.trans ?_
  rw [hinv]
  exact (abelElement_comp f hdim σ hσ θ hθ hH m (𝟙 H)).symm.trans (by rw [Category.comp_id])

/-! ### The Abel morphism into the whole Picard scheme -/

section Full

variable (P : Grp (Over S)) (eP : yonedaGrp.obj P ≅ functor f σ hσ)

/-- The element of `Pic_{X/S,σ}(T)` attached to `m : T ⟶ H`: the rigidified class of
`𝒪_{X_T}(D_m)`. -/
def abelElementFull {T : Over S} (m : T ⟶ H) : (functor f σ hσ ⋙ forget GrpCat).obj (op T) :=
  Multiplicative.ofAdd (mkGroup f σ hσ (chartClass f σ hσ 0 hH m)
    (schemePullbackClass_bcSection_chartClass f σ hσ 0 hH m))

/-- The class in `Pic(X_T)` of `abelElementFull m` is the normalised Abel class of `D_m`. -/
theorem smallEquiv_abelElementFull {T : Over S} (m : T ⟶ H) :
    smallEquiv _ ((Multiplicative.toAdd (abelElementFull f σ hσ hH m) : group f σ hσ T) :
      Stacks.Picard.smallOfScheme (bc f T)) = abelNormalized f σ hσ 0 (hH.family m) :=
  smallEquiv_mkGroup f σ hσ _ (schemePullbackClass_bcSection_chartClass f σ hσ 0 hH m)

/-- The elements `abelElementFull` are compatible with base change: `abelElementFull (a ≫ m)`
is the pullback along `a` of `abelElementFull m`. -/
theorem abelElementFull_comp {T T' : Over S} (a : T' ⟶ T) (m : T ⟶ H) :
    abelElementFull f σ hσ hH (a ≫ m) =
      (functor f σ hσ ⋙ forget GrpCat).map a.op (abelElementFull f σ hσ hH m) := by
  refine ext_functor f σ hσ ?_
  rw [functor_map_val, smallEquiv_abelElementFull, smallEquiv_abelElementFull]
  exact chartClass_comp f σ hσ 0 hH a m

/-- **The Abel morphism** `γ_d : Hilb^d_{X/S} ⟶ Pic_{X/S,σ}` of [Stacks, Tag 0BA0] (4): the
morphism classifying the rigidified class of `𝒪(D_univ)`. -/
def abelMorphismFull : H ⟶ P.X :=
  (eP.inv.app (op H)).hom (abelElementFull f σ hσ hH (𝟙 H))

/-- **`γ_d` classifies the Abel classes**: `m ≫ γ_d` corresponds to the rigidified class of
`𝒪_{X_T}(D_m)`. -/
theorem abelMorphismFull_spec {T : Over S} (m : T ⟶ H) :
    (eP.hom.app (op T)).hom (m ≫ abelMorphismFull f σ hσ hH P eP) =
      abelElementFull f σ hσ hH m := by
  have hn : (eP.hom.app (op T)).hom ((yonedaGrp.obj P).map m.op
      (abelMorphismFull f σ hσ hH P eP)) =
      (functor f σ hσ).map m.op ((eP.hom.app (op H)).hom (abelMorphismFull f σ hσ hH P eP)) :=
    congrArg (fun φ => GrpCat.Hom.hom φ (abelMorphismFull f σ hσ hH P eP)) (eP.hom.naturality m.op)
  have hinv : (eP.hom.app (op H)).hom (abelMorphismFull f σ hσ hH P eP) =
      abelElementFull f σ hσ hH (𝟙 H) := by
    show ((eP.inv ≫ eP.hom).app (op H)).hom _ = _
    rw [eP.inv_hom_id]; rfl
  refine hn.trans ?_
  rw [hinv]
  exact (abelElementFull_comp f σ hσ hH m (𝟙 H)).symm.trans (by rw [Category.comp_id])

end Full

end Stacks.RigidifiedPicard

end
