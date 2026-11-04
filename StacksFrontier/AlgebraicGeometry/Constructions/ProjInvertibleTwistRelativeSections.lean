module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeGluing
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineOpenTensorSections
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence

/-!
# Tag 02NC over a base scheme: the two sides of clause (2) on sections

Clause (2) of Tag 02NC is a commutative square of maps of sections over an open `V` of the
base. This file names its two composites for an arbitrary comparison `θ : g^*𝒪_{P'}(n) ⟶ F` and
proves that both commute with restriction to a smaller open of the base, so that the square holds
over every open as soon as it holds over the members of a basis.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeTwistSections.thetaSections`: a comparison
  `θ : g^*F' ⟶ F` on sections over the inverse image of an open of the base.
* `Stacks.AlgebraicGeometry.RelativeTwistSections.SquareAt`: the square of clause (2) over an
  open `V` of the base, on pure tensors.
* `Stacks.AlgebraicGeometry.RelativeTwistSections.lowerRoute`: its lower route on the whole tensor
  product `A_n(V) ⊗ L_n(V)`.
* `Stacks.AlgebraicGeometry.RelativeTwistSections.multiplyHom`: the lower route as a morphism of
  sheaves `A_n ⊗ L_n ⟶ π_*(F_A ⊗ π^*L_n)`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeTwistSections.squareAt_of_isBasis`: the square over every
  open from the square over the members of a basis.
* `Stacks.AlgebraicGeometry.RelativeTwistSections.squareAt_of_generator`: over an open where
  `L_n` has a generator, the square from the square at the generator.
* `Stacks.AlgebraicGeometry.RelativeTwistSections.upperRoute_eq_lowerRoute`: the square on pure
  tensors is the square on the whole tensor product.
* `Stacks.AlgebraicGeometry.RelativeTwistSections.multiplyHom_app_gammaTmul` and
  `squareAt_of_multiplyHom`: the multiply map on pure tensors, and the square from it.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.RelativeTwistSections

variable {S P P' : Scheme.{u}}

/-- A section of a sheaf of modules on `P` over the inverse image of an open of the base is
determined by its restrictions to the inverse images of the members of a basis of the base
inside that open. -/
theorem eq_of_isBasis (π : P ⟶ S) {B : Set S.Opens} (hB : Opens.IsBasis B) (F : P.Modules)
    {V : S.Opens} {s t : F.val.obj (op (π ⁻¹ᵁ V))}
    (h : ∀ W : {W : S.Opens // W ∈ B ∧ W ≤ V},
      F.val.map (homOfLE (π.preimage_mono W.2.2)).op s =
        F.val.map (homOfLE (π.preimage_mono W.2.2)).op t) : s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf F.isSheaf
    (fun W : {W : S.Opens // W ∈ B ∧ W ≤ V} => π ⁻¹ᵁ W.1)
    (fun W => π.preimage_mono W.2.2) ?_ h
  intro p hp
  obtain ⟨W, hWB, hpW, hWV⟩ := Opens.isBasis_iff_nbhd.mp hB (show π p ∈ V from hp)
  exact Opens.mem_iSup.mpr ⟨⟨W, hWB, hWV⟩, hpW⟩

section Theta

variable (π : P ⟶ S) (π' : P' ⟶ S) (g : P ⟶ P') (hg : g ≫ π' = π)

include hg in
/-- The inverse image along `g` of the inverse image of an open of the base in `P'` is its
inverse image in `P`, as `g` is a morphism over the base. -/
theorem preimage_preimage_eq (V : S.Opens) : g ⁻¹ᵁ (π' ⁻¹ᵁ V) = π ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, hg]

/-- **A comparison `θ : g^*F' ⟶ F` on sections over the inverse image of an open of the base.**
A section of `F'` over `π'^{-1}V` is pulled back along `g` by the unit of the
pullback--pushforward adjunction, to a section of `g^*F'` over `g^{-1}π'^{-1}V = π^{-1}V`, and
then mapped by `θ`. -/
def thetaSections {F' : P'.Modules} {F : P.Modules} (θ : (Scheme.Modules.pullback g).obj F' ⟶ F)
    (V : S.Opens) (s : F'.val.obj (op (π' ⁻¹ᵁ V))) : F.val.obj (op (π ⁻¹ᵁ V)) :=
  F.val.map (homOfLE (preimage_preimage_eq π π' g hg V).ge).op
    (θ.val.app (op (g ⁻¹ᵁ (π' ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F').val.app
        (op (π' ⁻¹ᵁ V)) s))

/-- `thetaSections` commutes with restriction to a smaller open of the base. -/
theorem thetaSections_res {F' : P'.Modules} {F : P.Modules}
    (θ : (Scheme.Modules.pullback g).obj F' ⟶ F) {W V : S.Opens} (h : W ≤ V)
    (s : F'.val.obj (op (π' ⁻¹ᵁ V))) :
    F.val.map (homOfLE (π.preimage_mono h)).op (thetaSections π π' g hg θ V s) =
      thetaSections π π' g hg θ W (F'.val.map (homOfLE (π'.preimage_mono h)).op s) := by
  have hu := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F').val
    (homOfLE (π'.preimage_mono h)).op s
  have hθ := PresheafOfModules.naturality_apply θ.val
    (homOfLE (g.preimage_mono (π'.preimage_mono h))).op
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F').val.app
        (op (π' ⁻¹ᵁ V)) s)
  have hc := PresheafOfModules.map_comp_apply F.val
    (homOfLE (preimage_preimage_eq π π' g hg V).ge).op (homOfLE (π.preimage_mono h)).op
    (θ.val.app (op (g ⁻¹ᵁ (π' ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F').val.app
        (op (π' ⁻¹ᵁ V)) s))
  have hc' := PresheafOfModules.map_comp_apply F.val
    (homOfLE (g.preimage_mono (π'.preimage_mono h))).op
    (homOfLE (preimage_preimage_eq π π' g hg W).ge).op
    (θ.val.app (op (g ⁻¹ᵁ (π' ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F').val.app
        (op (π' ⁻¹ᵁ V)) s))
  refine hc.symm.trans ((PresheafOfModules.congr_map_apply F.val (Subsingleton.elim _ _) _).trans
    (hc'.trans ?_))
  refine congrArg (F.val.map (homOfLE (preimage_preimage_eq π π' g hg W).ge).op)
    (hθ.symm.trans ?_)
  exact congrArg (θ.val.app (op (g ⁻¹ᵁ (π' ⁻¹ᵁ W)))) hu.symm

/-- `thetaSections` is additive. -/
theorem thetaSections_add {F' : P'.Modules} {F : P.Modules}
    (θ : (Scheme.Modules.pullback g).obj F' ⟶ F) (V : S.Opens)
    (s t : F'.val.obj (op (π' ⁻¹ᵁ V))) :
    thetaSections π π' g hg θ V (s + t) =
      thetaSections π π' g hg θ V s + thetaSections π π' g hg θ V t :=
  (congrArg (F.val.map (homOfLE (preimage_preimage_eq π π' g hg V).ge).op)
    ((congrArg (θ.val.app (op (g ⁻¹ᵁ (π' ⁻¹ᵁ V))))
      ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F').val.app
        (op (π' ⁻¹ᵁ V))).hom.map_add s t)).trans
      ((θ.val.app (op (g ⁻¹ᵁ (π' ⁻¹ᵁ V)))).hom.map_add _ _))).trans
  ((F.val.map (homOfLE (preimage_preimage_eq π π' g hg V).ge).op).hom.map_add _ _)

/-- `thetaSections` carries zero to zero. -/
theorem thetaSections_zero {F' : P'.Modules} {F : P.Modules}
    (θ : (Scheme.Modules.pullback g).obj F' ⟶ F) (V : S.Opens) :
    thetaSections π π' g hg θ V 0 = 0 :=
  (congrArg (F.val.map (homOfLE (preimage_preimage_eq π π' g hg V).ge).op)
    ((congrArg (θ.val.app (op (g ⁻¹ᵁ (π' ⁻¹ᵁ V))))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F').val.app
        (op (π' ⁻¹ᵁ V))).hom.map_zero).trans
      (θ.val.app (op (g ⁻¹ᵁ (π' ⁻¹ᵁ V)))).hom.map_zero)).trans
  (F.val.map (homOfLE (preimage_preimage_eq π π' g hg V).ge).op).hom.map_zero

end Theta

section Tensor

open Stacks.AlgebraicGeometry.AffineOpenTensorSections

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- The pure tensor of two sections commutes with restriction. -/
theorem gammaTmul_res (F G : P.Modules) {W V : P.Opens} (h : W ≤ V)
    (s : F.val.obj (op V)) (t : G.val.obj (op V)) :
    (tensorMod F G).val.map (homOfLE h).op (gammaTmul F G V s t) =
      gammaTmul F G W (F.val.map (homOfLE h).op s) (G.val.map (homOfLE h).op t) :=
  (PresheafOfModules.naturality_apply
    (PresheafOfModules.tensorSheafUnit (ofScheme F) (ofScheme G)) (homOfLE h).op
    (s ⊗ₜ t)).symm

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

/-- The pure tensor of sections is balanced: a scalar moves from one factor to the other. -/
theorem gammaTmul_smul_left (F G : S.Modules) (V : S.Opens) (c : Γ(S, V))
    (s : Γ(F, V)) (t : Γ(G, V)) :
    gammaTmul F G V (c • s) t = gammaTmul F G V s (c • t) :=
  congrArg (gammaTensorMap F G V)
    (TensorProduct.smul_tmul (R := Γ(S, V)) (M := Γ(F, V)) (N := Γ(G, V)) c s t)

/-- The value of a morphism into a direct image on a multiple of a section. -/
theorem app_smul_pushforward (π : P ⟶ S) {F : S.Modules} {G : P.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward π).obj G) (V : S.Opens) (c : Γ(S, V)) (s : Γ(F, V)) :
    φ.val.app (op V) (c • s) =
      π.app V c • (show Γ(G, π ⁻¹ᵁ V) from φ.val.app (op V) s) :=
  (φ.val.app (op V)).hom.map_smul c s

/-- The pure tensor of sections is additive in its first factor. -/
theorem gammaTmul_add_left' (F G : S.Modules) (V : S.Opens) (s s' : Γ(F, V)) (t : Γ(G, V)) :
    gammaTmul F G V (s + s') t = gammaTmul F G V s t + gammaTmul F G V s' t :=
  (congrArg (gammaTensorMap F G V) (TensorProduct.add_tmul s s' t)).trans
    (map_add (gammaTensorMap F G V) _ _)

/-- The pure tensor of sections is additive in its second factor. -/
theorem gammaTmul_add_right' (F G : S.Modules) (V : S.Opens) (s : Γ(F, V)) (t t' : Γ(G, V)) :
    gammaTmul F G V s (t + t') = gammaTmul F G V s t + gammaTmul F G V s t' :=
  (congrArg (gammaTensorMap F G V) (TensorProduct.tmul_add s t t')).trans
    (map_add (gammaTensorMap F G V) _ _)

end Tensor

/-! ### The square of clause (2), and its reduction to a basis of the base -/

section Square

open Stacks.AlgebraicGeometry.AffineOpenTensorSections

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable (π : P ⟶ S) (π' : P' ⟶ S) (g : P ⟶ P') (hg : g ≫ π' = π)
  {An Ln : S.Modules} {FA : P.Modules} {FB : P'.Modules}
  (ψA : An ⟶ (Scheme.Modules.pushforward π).obj FA)
  (ψB : tensorMod An Ln ⟶ (Scheme.Modules.pushforward π').obj FB)
  (θ : (Scheme.Modules.pullback g).obj FB ⟶ tensorMod FA ((Scheme.Modules.pullback π).obj Ln))

/-- **The square of clause (2) of Tag 02NC over an open `V` of the base**, for a comparison
`θ : g^*F_B ⟶ F_A ⊗ π^*L_n`: for every `a ∈ A_n(V)` and `l ∈ L_n(V)`, sending `a ⊗ l` along the
multiplication to `B_n(V)`, then by `ψ_B` to `Γ(π'^{-1}V, F_B)` and by `θ` to
`Γ(π^{-1}V, F_A ⊗ π^*L_n)`, is the same as sending `a` by `ψ_A` and `l` by `π^*` and multiplying.
-/
def SquareAt (V : S.Opens) : Prop :=
  ∀ (a : Γ(An, V)) (l : Γ(Ln, V)),
    thetaSections π π' g hg θ V (ψB.val.app (op V) (gammaTmul An Ln V a l)) =
      gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ V) (ψA.val.app (op V) a)
        (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op V) l)

/-- **The square of clause (2) holds over every open of the base once it holds over the members
of a basis.** Both composites commute with restriction to a smaller open of the base, and a
section over `π^{-1}V` is determined by its restrictions to the inverse images of the members of
the basis inside `V`. -/
theorem squareAt_of_isBasis {B : Set S.Opens} (hB : Opens.IsBasis B)
    (hsq : ∀ W ∈ B, SquareAt π π' g hg ψA ψB θ W) (V : S.Opens) :
    SquareAt π π' g hg ψA ψB θ V := by
  intro a l
  refine eq_of_isBasis π hB _ fun W => ?_
  have h := W.2.2
  refine (thetaSections_res π π' g hg θ h _).trans ?_
  refine Eq.trans ?_ (gammaTmul_res FA ((Scheme.Modules.pullback π).obj Ln)
    (π.preimage_mono h) _ _).symm
  have hB' := PresheafOfModules.naturality_apply ψB.val (homOfLE h).op (gammaTmul An Ln V a l)
  have hA := PresheafOfModules.naturality_apply ψA.val (homOfLE h).op a
  have hL := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val (homOfLE h).op l
  refine (congrArg (thetaSections π π' g hg θ W.1) hB'.symm).trans ?_
  refine (congrArg (fun z => thetaSections π π' g hg θ W.1 (ψB.val.app (op W.1) z))
    (gammaTmul_res An Ln h a l)).trans ?_
  refine (hsq W.1 W.2.1 _ _).trans ?_
  exact congrArg₂ (gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ W.1)) hA hL

/-- **Over an open where `L_n` has a generator, the square of clause (2) reduces to the
generator.** If every section of `L_n` over `W` is a multiple of `t₀`, the square holds at every
`a ⊗ l` as soon as it holds at every `a ⊗ t₀`: the multiplication is balanced, and `ψ_A`, `π^*`
and the multiplication on `P` are linear over the functions on `W`. -/
theorem squareAt_of_generator {W : S.Opens} (t₀ : Γ(Ln, W))
    (hgen : ∀ l : Γ(Ln, W), ∃ c : Γ(S, W), l = c • t₀)
    (h : ∀ a : Γ(An, W),
      thetaSections π π' g hg θ W (ψB.val.app (op W) (gammaTmul An Ln W a t₀)) =
        gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ W) (ψA.val.app (op W) a)
          (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op W) t₀)) :
    SquareAt π π' g hg ψA ψB θ W := by
  intro a l
  obtain ⟨c, rfl⟩ := hgen l
  refine (congrArg (fun z => thetaSections π π' g hg θ W (ψB.val.app (op W) z))
    (gammaTmul_smul_left An Ln W c a t₀).symm).trans ((h (c • a)).trans ?_)
  refine Eq.trans ?_ (congrArg (gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ W)
    (ψA.val.app (op W) a))
    (app_smul_pushforward π ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln) W c
      t₀)).symm
  refine (congrArg (fun z => gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ W) z
    (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op W) t₀))
    (app_smul_pushforward π ψA W c a)).trans ?_
  exact gammaTmul_smul_left FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ W) (π.app W c) _ _

/-- The lower route of the square of clause (2) on a pure tensor, as a biadditive map:
`(a, l) ↦ ψ_A(a) · π^*l`. -/
def lowerRouteBiadd (V : S.Opens) :
    Γ(An, V) →+ Γ(Ln, V) →+
      Γ(tensorMod FA ((Scheme.Modules.pullback π).obj Ln), π ⁻¹ᵁ V) :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun l =>
      gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ V) (ψA.val.app (op V) a)
        (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op V) l))
      fun l l' =>
        (congrArg (gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ V)
          (ψA.val.app (op V) a))
          ((((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app
            (op V)).hom.map_add l l')).trans
        (gammaTmul_add_right' _ _ _ _ _ _))
    fun a a' => AddMonoidHom.ext fun l =>
      (congrArg (fun z => gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ V) z
        (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op V) l))
        ((ψA.val.app (op V)).hom.map_add a a')).trans
      (gammaTmul_add_left' _ _ _ _ _ _)

/-- **The lower route of the square of clause (2)**, on the tensor product
`A_n(V) ⊗_{Γ(S, V)} L_n(V)`: `ψ_A ⊗ π^*` followed by the multiplication
`Γ(π^{-1}V, F_A) × Γ(π^{-1}V, π^*L_n) → Γ(π^{-1}V, F_A ⊗ π^*L_n)`. -/
def lowerRoute (V : S.Opens) :
    Γ(An, V) ⊗[Γ(S, V)] Γ(Ln, V) →+
      Γ(tensorMod FA ((Scheme.Modules.pullback π).obj Ln), π ⁻¹ᵁ V) :=
  TensorProduct.liftAddHom (lowerRouteBiadd π ψA V) fun c a l => by
    simp only [lowerRouteBiadd, AddMonoidHom.mk'_apply]
    refine (congrArg (fun z => gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ V) z
      (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op V) l))
      (app_smul_pushforward π ψA V c a)).trans ?_
    refine (gammaTmul_smul_left FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ V)
      (π.app V c) _ _).trans ?_
    exact congrArg (gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ V)
      (ψA.val.app (op V) a))
      (app_smul_pushforward π ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln) V c
        l).symm

/-- The lower route on a pure tensor. -/
theorem lowerRoute_tmul (V : S.Opens) (a : Γ(An, V)) (l : Γ(Ln, V)) :
    lowerRoute π ψA V (a ⊗ₜ l) =
      gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ V) (ψA.val.app (op V) a)
        (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op V) l) :=
  rfl

/-- **The square of clause (2), on the whole tensor product.** Once it holds on pure tensors, the
upper route `θ ∘ ψ_B ∘ multiply` and the lower route `multiply ∘ (ψ_A ⊗ π^*)` agree as maps out of
`A_n(V) ⊗_{Γ(S, V)} L_n(V)`, both being additive. -/
theorem upperRoute_eq_lowerRoute {V : S.Opens} (h : SquareAt π π' g hg ψA ψB θ V)
    (z : Γ(An, V) ⊗[Γ(S, V)] Γ(Ln, V)) :
    thetaSections π π' g hg θ V (ψB.val.app (op V) (gammaTensorMap An Ln V z)) =
      lowerRoute π ψA V z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    refine (congrArg (fun w => thetaSections π π' g hg θ V (ψB.val.app (op V) w))
      (map_zero (gammaTensorMap An Ln V))).trans ?_
    refine (congrArg (thetaSections π π' g hg θ V) (ψB.val.app (op V)).hom.map_zero).trans ?_
    exact (thetaSections_zero π π' g hg θ V).trans (map_zero (lowerRoute π ψA V)).symm
  | tmul a l => exact h a l
  | add z z' hz hz' =>
    refine (congrArg (fun w => thetaSections π π' g hg θ V (ψB.val.app (op V) w))
      (map_add (gammaTensorMap An Ln V) z z')).trans ?_
    refine (congrArg (thetaSections π π' g hg θ V)
      ((ψB.val.app (op V)).hom.map_add _ _)).trans ?_
    refine (thetaSections_add π π' g hg θ V _ _).trans ?_
    exact (congrArg₂ (· + ·) hz hz').trans (map_add (lowerRoute π ψA V) z z').symm

end Square

/-! ### The lower route as a morphism of sheaves: the multiply map `ψ^C` -/

section Multiply

open MonoidalCategory
open Stacks.AlgebraicGeometry.AffineOpenTensorSections

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable (π : P ⟶ S) {An Ln : S.Modules} {FA : P.Modules}
  (ψA : An ⟶ (Scheme.Modules.pushforward π).obj FA)

/-- The adjoint transpose `π^*A_n ⟶ F_A` of `ψ_A`. -/
def psiTranspose : (Scheme.Modules.pullback π).obj An ⟶ FA :=
  ((Scheme.Modules.pullbackPushforwardAdjunction π).homEquiv _ _).symm ψA

/-- `psiTranspose`, as a morphism over the ringed-space spelling of the structure sheaf. -/
def psiTransposeR :
    ofScheme ((Scheme.Modules.pullback π).obj An) ⟶ ofScheme FA :=
  psiTranspose π ψA

/-- **The multiply map `ψ^C : A_n ⊗ L_n ⟶ π_*(F_A ⊗ π^*L_n)`**, the lower route of the square of
clause (2) of Tag 02NC as a morphism of sheaves: adjoint to the comparison
`π^*(A_n ⊗ L_n) ≅ π^*A_n ⊗ π^*L_n` of Tag 01CD followed by the transpose of `ψ_A` on the first
factor. On pure tensors it is `a ⊗ l ↦ ψ_A(a) · π^*l` (`multiplyHom_app_gammaTmul`). -/
def multiplyHom :
    tensorMod An Ln ⟶
      (Scheme.Modules.pushforward π).obj (tensorMod FA ((Scheme.Modules.pullback π).obj Ln)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction π).homEquiv _ _
    (Stacks.RingedSpace.comparison π.toLRSHom.toShHom An Ln ≫
      (psiTransposeR π ψA ▷ ofScheme ((Scheme.Modules.pullback π).obj Ln)))

/-- `psiTranspose` recovers `ψ_A` through the unit: over every open `V` of the base, the transpose
of `ψ_A` applied to the image of `a ∈ A_n(V)` under the unit `A_n ⟶ π_*π^*A_n` is `ψ_A(a)`. -/
theorem psiTranspose_unit (V : S.Opens) (a : Γ(An, V)) :
    (psiTranspose π ψA).val.app (op (π ⁻¹ᵁ V))
        (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app An).val.app (op V) a) =
      ψA.val.app (op V) a := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction π).homEquiv An FA).apply_symm_apply ψA
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun φ : An ⟶ (Scheme.Modules.pushforward π).obj FA => φ.val.app (op V) a) h

/-- **The multiply map on pure tensors**: over every open `V` of the base,
`ψ^C(a ⊗ l) = ψ_A(a) · π^*l`. -/
theorem multiplyHom_app_gammaTmul (V : S.Opens) (a : Γ(An, V)) (l : Γ(Ln, V)) :
    (multiplyHom π ψA).val.app (op V) (gammaTmul An Ln V a l) =
      gammaTmul FA ((Scheme.Modules.pullback π).obj Ln) (π ⁻¹ᵁ V) (ψA.val.app (op V) a)
        (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op V) l) := by
  have h1 := (Scheme.Modules.pullbackPushforwardAdjunction π).homEquiv_unit (tensorMod An Ln)
    (tensorMod FA ((Scheme.Modules.pullback π).obj Ln))
    (Stacks.RingedSpace.comparison π.toLRSHom.toShHom An Ln ≫
      (psiTransposeR π ψA ▷ ofScheme ((Scheme.Modules.pullback π).obj Ln)))
  have e2 := Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul π.toLRSHom.toShHom
    (A := An) (B := Ln) (op V) a l
  have e3 := Stacks.PullbackTensorCoherence.whiskerRight_tmul (Z := P.toRingedSpace)
    (B := ofScheme ((Scheme.Modules.pullback π).obj Ln))
    (psiTransposeR π ψA) (op (π ⁻¹ᵁ V))
    (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app An).val.app (op V) a)
    (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op V) l)
  refine (congrArg (fun φ : tensorMod An Ln ⟶ (Scheme.Modules.pushforward π).obj
      (tensorMod FA ((Scheme.Modules.pullback π).obj Ln)) =>
    φ.val.app (op V) (gammaTmul An Ln V a l)) h1).trans ?_
  refine (congrArg ((psiTransposeR π ψA ▷ ofScheme ((Scheme.Modules.pullback π).obj Ln)).val.app
    (op (π ⁻¹ᵁ V))) e2).trans ?_
  refine e3.trans ?_
  exact congrArg (fun z => Stacks.PullbackTensorCoherence.tmul P.toRingedSpace (ofScheme FA)
      (ofScheme ((Scheme.Modules.pullback π).obj Ln)) (op (π ⁻¹ᵁ V)) z
      (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app Ln).val.app (op V) l))
    (psiTranspose_unit π ψA V a)

/-- **The square of clause (2) from the multiply map.** If `θ` carries `ψ_B(b)` to `ψ^C(b)` for
every section `b` of `B_n = A_n ⊗ L_n` over every open of the base, the square holds over every
open of the base. -/
theorem squareAt_of_multiplyHom {P' : Scheme.{u}} (π' : P' ⟶ S) (g : P ⟶ P') (hg : g ≫ π' = π)
    {FB : P'.Modules} (ψB : tensorMod An Ln ⟶ (Scheme.Modules.pushforward π').obj FB)
    (θ : (Scheme.Modules.pullback g).obj FB ⟶
      tensorMod FA ((Scheme.Modules.pullback π).obj Ln))
    (h : ∀ (V : S.Opens) (b : Γ(tensorMod An Ln, V)),
      thetaSections π π' g hg θ V (ψB.val.app (op V) b) = (multiplyHom π ψA).val.app (op V) b)
    (V : S.Opens) : SquareAt π π' g hg ψA ψB θ V :=
  fun a l => (h V (gammaTmul An Ln V a l)).trans (multiplyHom_app_gammaTmul π ψA V a l)

end Multiply

end Stacks.AlgebraicGeometry.RelativeTwistSections

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

open Stacks.AlgebraicGeometry.AffineOpenTensorSections

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- **Where the `n`-th power of `x` trivializes `ℒ^{⊗ n}`, every section of `ℒ^{⊗ n}` is a
multiple of it.** -/
theorem exists_smul_powSecAt_of_trivializesPower {V : S.Opens} {x : (tp L 1).val.obj (op V)}
    {n : ℕ} (h : TrivializesPower L V x n) (l : Γ(tpMod L n, V)) :
    ∃ c : Γ(S, V), l = c • powSecAtMod L V x n := by
  obtain ⟨e, he⟩ := h
  refine ⟨Stacks.SheafOfModules.TensorGenerator.coord S.sheaf.obj S.ringCatSheaf.property V
    (tp L (n : ℤ)) e l, ?_⟩
  refine (Stacks.SheafOfModules.TensorGenerator.smul_generator S.sheaf.obj
    S.ringCatSheaf.property V (tp L (n : ℤ)) e l).symm.trans ?_
  exact congrArg (fun z => Stacks.SheafOfModules.TensorGenerator.coord S.sheaf.obj
    S.ringCatSheaf.property V (tp L (n : ℤ)) e l • z) he

/-- In degree zero every section of `ℒ^{⊗ 0} = 𝒪_S` is a multiple of the zeroth power of any
section, which is the unit. -/
theorem exists_smul_powSecAt_zero {V : S.Opens} (x : (tp L 1).val.obj (op V))
    (l : Γ(tpMod L 0, V)) :
    ∃ c : Γ(S, V), l = c • powSecAtMod L V x 0 :=
  ⟨(show Γ(S, V) from l), (mul_one (show Γ(S, V) from l)).symm⟩

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
