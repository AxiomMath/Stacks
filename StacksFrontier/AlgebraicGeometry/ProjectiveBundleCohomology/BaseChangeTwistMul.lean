module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeRows
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoKoszul
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiEssSurj
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCanonical
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The identification of the twists along the base change of a projective bundle is
multiplicative

Let `b : 𝐏(E') ⟶ 𝐏(E)` be the morphism of projective bundles over `g : S' ⟶ S`, `E' ≅ g^*E`. The
identification `θ♯ : b^* 𝒪_{𝐏(E)}(d) ⟶ 𝒪_{𝐏(E')}(d)` of the twists carries the multiplication
`𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)` to the multiplication of the twists of `𝐏(E')`, through the comparison
`b^*(M ⊗ N) ≅ b^*M ⊗ b^*N` of [Stacks, Tag 01CD].

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaSharp_pbUnit`: `θ♯` on the pullback of
  a section is `θ♭` of the section.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaSharp_twistMul`: `θ♯` is
  multiplicative.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (E' : S'.Modules) [E'.IsQuasicoherent]
  (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc'))

/-- **`θ♯` on the pullback of a section is `θ♭` of the section.** -/
public theorem thetaSharp_pbUnit (d : ℤ)
    (V : (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (s : (D.algebra.piece d).val.obj (op V)) :
    (thetaSharp g E hqc E' hqc' hE D D' d).val.app (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V))
        (pbUnit (bundleBaseChange g E hqc E' hqc' hE) (D.algebra.piece d) V s) =
      (thetaFlat g E hqc E' hqc' hE D D' d).val.app (op V) s := by
  have := congrArg (fun φ => φ.val.app (op V) s)
    (((Scheme.Modules.pullbackPushforwardAdjunction (bundleBaseChange g E hqc E' hqc' hE)).homEquiv
      _ _).apply_symm_apply (thetaFlat g E hqc E' hqc' hE D D' d))
  simp only [Adjunction.homEquiv_unit] at this
  exact this

/-- **`θ♯` is multiplicative**: `b^*(𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j))` followed by `θ♯` is the comparison
`b^*(𝒪(i) ⊗ 𝒪(j)) ≅ b^*𝒪(i) ⊗ b^*𝒪(j)`, then `θ♯ ⊗ θ♯`, then the multiplication of the twists
of `𝐏(E')`. -/
public theorem thetaSharp_twistMul (i j : ℤ) :
    (pullbackFunctor (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom).map (twistMul D i j) ≫
        thetaSharp g E hqc E' hqc' hE D D' (i + j) =
      Stacks.RingedSpace.comparison (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom
          (twistPiece D i) (twistPiece D j) ≫
        tensorMap (thetaSharp g E hqc E' hqc' hE D D' i) (thetaSharp g E hqc E' hqc' hE D D' j) ≫
          twistMul D' i j :=
  pullback_mulSheaf (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom (A := D.algebra)
    (B := D'.algebra) (fun d => thetaSharp g E hqc E' hqc' hE D D' d) i j
    (fun U x y => (thetaSharp_pbUnit g E hqc E' hqc' hE D D' (i + j) (Opposite.unop U) _).trans
      ((thetaFlat_mul g E hqc E' hqc' hE D D' i j (Opposite.unop U) x y).trans
        (congrArg₂ (fun a b => (D'.algebra.mul i j).app _ a b)
          (thetaSharp_pbUnit g E hqc E' hqc' hE D D' i (Opposite.unop U) x).symm
          (thetaSharp_pbUnit g E hqc E' hqc' hE D D' j (Opposite.unop U) y).symm)))

/-- **The identification `g^* Sym(E) ≅ Sym(E')` on the degree-one generator**: it is `E' ≅ g^*E`
followed by the generator of `Sym(E')`. -/
public theorem symmetricSituationPullbackHom_gen :
    (Scheme.Modules.pullback g).map (Scheme.Modules.symmetricAlgebraGenIso S E).hom ≫
        (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app 1 =
      hE.inv ≫ (Scheme.Modules.symmetricAlgebraGenIso S' E').hom :=
  Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator g E E' hE

/-- Transposing along a composite `(p ≫ g)^* ⊣ (p ≫ g)_*` a map that factors through the unit of
`g^* ⊣ g_*`. -/
public theorem homEquiv_symm_comp_pushforward {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules) {M' : Y.Modules} (e : (Scheme.Modules.pullback q).obj M ⟶ M')
    (k : M' ⟶ (Scheme.Modules.pushforward p).obj N) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)).homEquiv M N).symm
        ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M ≫
          (Scheme.Modules.pushforward q).map (e ≫ k) ≫
            (Scheme.Modules.pushforwardComp p q).hom.app N) =
      (Scheme.Modules.pullbackComp p q).inv.app M ≫ (Scheme.Modules.pullback p).map e ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M' N).symm k := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
    Stacks.Descent.unit_pullbackPushforwardAdjunction_comp]
  have h1 := (Scheme.Modules.pushforwardComp p q).hom.naturality
    ((Scheme.Modules.pullback p).map e ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M' N).symm k)
  have h2 := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality e
  have h3 : (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M' ≫
      (Scheme.Modules.pushforward p).map
        (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M' N).symm k) = k :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  simp only [Functor.comp_map, Functor.id_map] at h1 h2
  rw [Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc,
    ← h1, ← Functor.map_comp_assoc]
  refine congrArg (fun φ => _ ≫ (Scheme.Modules.pushforward q).map φ ≫ _) ?_
  rw [Functor.map_comp, ← Category.assoc, ← h2, Category.assoc, h3]

/-- **`b^* π^* E ≅ π'^* E'`**: `b ≫ π = π' ≫ g`, then `E' ≅ g^* E`. -/
public def bundlePullbackBaseChange :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).obj
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj E) ≅
      (Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).obj E' :=
  pullbackPullbackIso (bundleBaseChange g E hqc E' hqc' hE) _ _
      (bundleBaseChange_toBase g E hqc E' hqc' hE) E ≪≫
    ((Scheme.Modules.pullbackComp _ g).app E).symm ≪≫
    (Scheme.Modules.pullback
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).mapIso hE.symm

/-- **The tautological surjections correspond under base change**: `b^*(π^* E ⟶ 𝒪(1))` followed
by `θ♯` is `b^* π^* E ≅ π'^* E'` followed by `π'^* E' ⟶ 𝒪'(1)`. -/
public theorem tautologicalMap_baseChange :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map (tautologicalMap E hqc D) ≫
        thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ) =
      (bundlePullbackBaseChange g E hqc E' hqc' hE).hom ≫ tautologicalMap E' hqc' D' := by
  have key := pullback_homEquiv_symm (bundleBaseChange g E hqc E' hqc' hE) _ _
    (bundleBaseChange_toBase g E hqc E' hqc' hE) (thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ))
    ((Scheme.Modules.symmetricAlgebraGenIso S E).hom ≫ D.ψ 1)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app E ≫
      (Scheme.Modules.pushforward g).map
        (hE.inv ≫ (Scheme.Modules.symmetricAlgebraGenIso S' E').hom ≫ D'.ψ 1) ≫
      (Scheme.Modules.pushforwardComp
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase g).hom.app
          (D'.algebra.piece ((1 : ℕ) : ℤ))) ?_
  · refine key.trans ?_
    have hc := homEquiv_symm_comp_pushforward
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase g E
      (D'.algebra.piece ((1 : ℕ) : ℤ)) hE.inv
      ((Scheme.Modules.symmetricAlgebraGenIso S' E').hom ≫ D'.ψ 1)
    refine (congrArg (_ ≫ ·) hc).trans ?_
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm
  · intro U s
    have hθ := thetaSharp_pbUnit g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ)
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
      (((Scheme.Modules.symmetricAlgebraGenIso S E).hom ≫ D.ψ 1).val.app (op U) s)
    have hψ := congrArg (fun φ => φ.val.app (op U)
      ((Scheme.Modules.symmetricAlgebraGenIso S E).hom.val.app (op U) s))
      (psi_comp_thetaFlat g E hqc E' hqc' hE D D' 1)
    have hη := congrArg (fun φ => φ.val.app (op U) s)
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality
        (Scheme.Modules.symmetricAlgebraGenIso S E).hom)
    have hgen := congrArg (fun φ => φ.val.app (op (g ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app E).val.app (op U) s))
      (symmetricSituationPullbackHom_gen g E E' hE)
    have hsq :=
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso_hom_app_app
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
      (D'.algebra.piece ((1 : ℕ) : ℤ)) U
    have hr : ∀ (h : (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ
          (g ⁻¹ᵁ U) ≤ bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ
            ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
        (t : (D'.algebra.piece ((1 : ℕ) : ℤ)).val.obj (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ
          ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)))),
        (D'.algebra.piece ((1 : ℕ) : ℤ)).val.presheaf.map (homOfLE h).op t =
          (((Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
            (bundleBaseChange g E hqc E' hqc' hE)
            (bundleBaseChange_toBase g E hqc E' hqc' hE)).hom.app
              (D'.algebra.piece ((1 : ℕ) : ℤ))).app U) t := fun h t => by
      rw [hsq]
      exact congrArg (fun f => (D'.algebra.piece ((1 : ℕ) : ℤ)).val.presheaf.map f t)
        (Subsingleton.elim _ _)
    refine (hr _ _).trans ?_
    refine (congrArg _ hθ).trans ?_
    refine hψ.trans ?_
    exact congrArg ((D'.ψ 1).val.app (op (g ⁻¹ᵁ U)))
      ((congrArg (((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app 1).val.app
        (op (g ⁻¹ᵁ U))) hη).trans hgen)

/-- `θ♯` is an epimorphism in degree one: the tautological surjection of `𝐏(E')` factors through
it. -/
public theorem epi_thetaSharp_one : Epi (thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ)) := by
  have := epi_tautologicalMap E' hqc' D'
  have : Epi ((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
      (tautologicalMap E hqc D) ≫ thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ)) := by
    rw [tautologicalMap_baseChange]
    exact epi_comp _ _
  exact epi_of_epi ((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
      (tautologicalMap E hqc D)) _

/-- The pullback along `b` of the degree-one twist of `𝐏(E)` is invertible. -/
private theorem isInvertibleModule_pullback_piece_one :
    Stacks.Ample.IsInvertibleModule _
      ((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).obj
        (D.algebra.piece ((1 : ℕ) : ℤ))) :=
  have := isInvertible_piece E hqc D ((1 : ℕ) : ℤ)
  Stacks.InvertiblePullback.isInvertibleModule_pullback (bundleBaseChange g E hqc E' hqc' hE)
    (D.algebra.piece ((1 : ℕ) : ℤ))

/-- **`θ♯` is an isomorphism in degree one**: an epimorphism between invertible modules. -/
public theorem isIso_thetaSharp_one :
    IsIso (thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ)) := by
  have := isInvertible_piece E hqc D ((1 : ℕ) : ℤ)
  have := isInvertible_piece E' hqc' D' ((1 : ℕ) : ℤ)
  have := isInvertibleModule_pullback_piece_one g E hqc E' hqc' hE D
  exact Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible _
    (epi_thetaSharp_one g E hqc E' hqc' hE D D')

/-- In a commutative square whose other three sides are isomorphisms after composing, one side is
an isomorphism exactly when the other is. -/
public theorem iso_chain_iff {C : Type*} [Category C] {X Y Z W V V' : C} (a : X ⟶ Y)
    (θ : Y ⟶ Z) (c : X ⟶ W) (t : W ⟶ V) (s : V ⟶ V') (m : V' ⟶ Z) (ha : IsIso a) (hc : IsIso c)
    (hs : IsIso s) (hm : IsIso m) (key : a ≫ θ = c ≫ (t ≫ s) ≫ m) : IsIso θ ↔ IsIso t := by
  rw [← isIso_comp_left_iff a, key, isIso_comp_left_iff, isIso_comp_right_iff, isIso_comp_right_iff]

/-- `θ♯` in degree `d + 1` is an isomorphism exactly when it is one in degree `d`: they are
related by the multiplication with the degree-one twists, on which `θ♯` is an isomorphism. -/
public theorem isIso_thetaSharp_iff_succ (d e : ℤ) (h : d + ((1 : ℕ) : ℤ) = e) :
    IsIso (thetaSharp g E hqc E' hqc' hE D D' e) ↔
      IsIso (thetaSharp g E hqc E' hqc' hE D D' d) := by
  subst h
  have := isIso_twistMul D'
    (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E' hqc') d ((1 : ℕ) : ℤ)
  have := isInvertible_piece E' hqc' D' ((1 : ℕ) : ℤ)
  have key := thetaSharp_twistMul g E hqc E' hqc' hE D D' d ((1 : ℕ) : ℤ)
  have hsplit : tensorMap (thetaSharp g E hqc E' hqc' hE D D' d) (𝟙 _) ≫
        tensorMap (𝟙 _) (thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ)) =
      tensorMap (thetaSharp g E hqc E' hqc' hE D D' d)
        (thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ)) :=
    (tensorMap_comp _ _ _ _).trans (congrArg₂ tensorMap (Category.comp_id _) (Category.id_comp _))
  have hs : IsIso (tensorMap (𝟙 (D'.algebra.piece d))
      (thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ))) :=
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(bundle E' hqc').toRingedSpace.presheaf, (bundle E' hqc').toRingedSpace.IsSheaf⟩)).mapIso
      (X := (D'.algebra.piece d, (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).obj
        (D.algebra.piece ((1 : ℕ) : ℤ))))
      (Y := (D'.algebra.piece d, D'.algebra.piece ((1 : ℕ) : ℤ)))
      (Iso.prod (Iso.refl _) (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ))
        (isIso_thetaSharp_one g E hqc E' hqc' hE D D')))).isIso_hom
  refine (iso_chain_iff _ _ _ _ _ _
    ((pullbackFunctor (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom).mapIso
      (@asIso _ _ _ _ (twistMul D d ((1 : ℕ) : ℤ))
        (isIso_twistMul D (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E hqc)
          d ((1 : ℕ) : ℤ)))).isIso_hom
    (Stacks.PullbackTensor.isIso_comparison _ _ _) hs
    (isIso_twistMul D' (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E' hqc')
      d ((1 : ℕ) : ℤ)) (key.trans (congrArg (fun t => _ ≫ t ≫ _) hsplit.symm))).trans ?_
  have := isInvertibleModule_pullback_piece_one g E hqc E' hqc' hE D
  exact isIso_iff_of_reflects_iso (thetaSharp g E hqc E' hqc' hE D D' d)
    (Stacks.ProjectionFormula.tensorRightInvertible _
      ((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).obj
        (D.algebra.piece ((1 : ℕ) : ℤ))))

/-- **The identification `b^* 𝒪_{𝐏(E)}(d) ⟶ 𝒪_{𝐏(E')}(d)` of the twists is an isomorphism**, in
every degree. -/
public instance isIso_thetaSharp (d : ℤ) : IsIso (thetaSharp g E hqc E' hqc' hE D D' d) := by
  induction d using Int.inductionOn' (b := ((1 : ℕ) : ℤ)) with
  | zero => exact isIso_thetaSharp_one g E hqc E' hqc' hE D D'
  | succ k _ ih => exact (isIso_thetaSharp_iff_succ g E hqc E' hqc' hE D D' k (k + 1) rfl).mpr ih
  | pred k _ ih =>
    exact (isIso_thetaSharp_iff_succ g E hqc E' hqc' hE D D' (k - 1) k (by omega)).mp ih

/-- The pullback along `b` of the kernel inclusion of the tautological surjection is a
monomorphism: the surjection is split on stalks, its target being invertible. -/
public theorem mono_pullback_kernel_ι_tautologicalMap :
    Mono ((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
      (kernel.ι (tautologicalMap E hqc D))) :=
  Stacks.RingedSpace.mono_modulePullback_map_kernel_ι_of_isSplitEpi_stalk
    (bundleBaseChange g E hqc E' hqc' hE).toLRSHom.toShHom (tautologicalMap E hqc D)
    fun y => @Stacks.SheafOfModules.isSplitEpi_stalkFunctor_map_of_isInvertible _ _ _
      (tautologicalMap E hqc D) (epi_tautologicalMap E hqc D)
      (isInvertible_piece E hqc D ((1 : ℕ) : ℤ)) _

/-- The kernel sequence of the tautological surjection of `𝐏(E')`, presented through the pullback
of that of `𝐏(E)`. -/
public abbrev tautologicalPullbackSequence : ShortComplex
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).scheme.Modules :=
  ShortComplex.mk
    ((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
      (kernel.ι (tautologicalMap E hqc D)) ≫ (bundlePullbackBaseChange g E hqc E' hqc' hE).hom)
    (tautologicalMap E' hqc' D')
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (tautologicalMap_baseChange g E hqc E' hqc' hE D D').symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (((Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map_comp _ _).symm.trans
          ((congrArg _ (kernel.condition _)).trans (Functor.map_zero _ _ _)))).trans zero_comp))))

/-- That sequence is short exact. -/
@[sga "6 VI 5.1" "partial"]
public theorem shortExact_tautologicalPullbackSequence :
    (tautologicalPullbackSequence g E hqc E' hqc' hE D D').ShortExact := by
  have := mono_pullback_kernel_ι_tautologicalMap g E hqc E' hqc' hE D
  have := epi_tautologicalMap E' hqc' D'
  have hpres : PreservesColimit (parallelPair (tautologicalSequence E hqc D).f 0)
      (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)) :=
    have := (Scheme.Modules.pullbackPushforwardAdjunction
      (bundleBaseChange g E hqc E' hqc' hE)).leftAdjoint_preservesColimits
    inferInstance
  have hex := (exact_tautological E hqc D).map_of_epi_of_preservesCokernel
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)) (epi_tautologicalMap E hqc D)
    hpres
  have e : (tautologicalSequence E hqc D).map (Scheme.Modules.pullback
      (bundleBaseChange g E hqc E' hqc' hE)) ≅
        tautologicalPullbackSequence g E hqc E' hqc' hE D D' :=
    ShortComplex.isoMk (Iso.refl _) (bundlePullbackBaseChange g E hqc E' hqc' hE)
      (@asIso _ _ _ _ (thetaSharp g E hqc E' hqc' hE D D' ((1 : ℕ) : ℤ))
        (isIso_thetaSharp g E hqc E' hqc' hE D D' _)) (Category.id_comp _)
      (tautologicalMap_baseChange g E hqc E' hqc' hE D D').symm
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_iso e hex) (mono_comp _ _) inferInstance

/-- **`b^* K ≅ K'`**: the kernels of the tautological surjections correspond under base change. -/
public def tautKernelBaseChange :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).obj
        (tautologicalKernel E hqc D) ≅
      tautologicalKernel E' hqc' D' :=
  (shortExact_tautologicalPullbackSequence g E hqc E' hqc' hE D D').fIsKernel.conePointUniqueUpToIso
    (limit.isLimit _)

/-- The kernel inclusions correspond. -/
public theorem tautKernelBaseChange_ι :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).map
        (kernel.ι (tautologicalMap E hqc D)) ≫ (bundlePullbackBaseChange g E hqc E' hqc' hE).hom =
      (tautKernelBaseChange g E hqc E' hqc' hE D D').hom ≫ kernel.ι (tautologicalMap E' hqc' D') :=
  (IsLimit.conePointUniqueUpToIso_hom_comp
    (shortExact_tautologicalPullbackSequence g E hqc E' hqc' hE D D').fIsKernel
    (limit.isLimit _) WalkingParallelPair.zero).symm

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
