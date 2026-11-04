module

public import StacksFrontier.Deformation.ToposThickening.ExtensionProblem

/-!
# Moving a square-zero extension problem to another base along an isomorphism of lower rows

A square-zero extension problem `S` of ringed topoi ([Stacks Project, Tag 08UF]) over
`f₁ : X ⟶ B₁` sees its base only through the lower row of its diagram on `X`: the sheaves of rings
`f₁⁻¹𝒪_{B'₁} ⟶ f₁⁻¹𝒪_{B₁} ⟶ 𝒪_X`, the ideal `f₁⁻¹𝒥` and the prescribed map `c`. Given a second
morphism `f₂ : X ⟶ B₂`, a first-order thickening `r : 𝒪_{B'₂} ⟶ 𝒪_{B₂}` of `B₂`, and isomorphisms
`θ : f₁⁻¹𝒪_{B'₁} ≅ f₂⁻¹𝒪_{B'₂}`, `μ : f₁⁻¹𝒪_{B₁} ≅ f₂⁻¹𝒪_{B₂}` compatible with the reductions and
with the structure maps, together with an isomorphism `β : 𝒢 ≅ 𝒢'` of target modules, the problem
`S` becomes a problem over `B₂` with the same ideal (read over `f₂⁻¹𝒪_{B₂}` through `μ`), target
`𝒢'` and prescribed map `β ∘ c`. Its solutions are those of `S`: the same thickened structure
sheaf, with the base map read through `θ` and the kernel through `β`.

This is how the problem of a deformation of `X → Spec A` along `Spec A ⊂ Spec A'`, posed over the
closed subspace of `Spec A'` that `Spec A` cuts out, is read over `Spec A` itself, so that its
base ring `f⁻¹𝒪_{Spec A}` is the same for every thickening (the `07YZ` route of
[Stacks, Remark 0D1P]).

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.rebase`: the problem over `B₂`.
* `Deformation.ToposThickening.RingedToposExtensionProblem.rebaseSolution` and
  `rebaseSolutionInv`: the solutions of `S` and of its rebase, in both directions.
* `Deformation.ToposThickening.RingedToposExtensionProblem.rebaseIsomorphismClassesEquiv`: the
  bijection of isomorphism classes of solutions.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v₁ u₁ w₁ v₂ u₂ w₂

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}} {B₁ : RingedTopos.{v₁, u₁, w₁}}
  {B₂ : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B₁.J.HasSheafCompose (forget RingCat.{w₁})]
  [B₂.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  (S : RingedToposExtensionProblem X B₁) (f : RingedToposHom X B₂)
  {E : Sheaf B₂.J CommRingCat.{w₂}} (r : E ⟶ B₂.O)
  (θ : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ≅
    (inverseImageCommRingFunctor f.toToposHom).obj E)
  (μ : (inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O ≅
    (inverseImageCommRingFunctor f.toToposHom).obj B₂.O)
  (hθ : θ.hom ≫ (inverseImageCommRingFunctor f.toToposHom).map r =
    (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫ μ.hom)
  (hμ : μ.hom ≫ f.fSharpInverseImage = S.f.fSharpInverseImage)
  {G : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
  (β : S.G ≅ G)

include hθ in
/-- The inverse form of the compatibility of `θ` and `μ` with the reductions, on sections. -/
theorem rebase_reduction_inv_apply (U : X.Cᵒᵖ)
    (y : ((inverseImageCommRingFunctor f.toToposHom).obj E).obj.obj U) :
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U
        (θ.inv.hom.app U y) =
      μ.inv.hom.app U (((inverseImageCommRingFunctor f.toToposHom).map r).hom.app U y) := by
  have h : θ.inv ≫ (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction =
      (inverseImageCommRingFunctor f.toToposHom).map r ≫ μ.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hθ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact congrArg (fun k => k.hom.app U y) h

include hμ in
/-- The inverse form of the compatibility of `μ` with the structure maps, on sections. -/
theorem rebase_fSharp_inv_apply (U : X.Cᵒᵖ)
    (y : ((inverseImageCommRingFunctor f.toToposHom).obj B₂.O).obj.obj U) :
    S.f.fSharpInverseImage.hom.app U (μ.inv.hom.app U y) = f.fSharpInverseImage.hom.app U y := by
  have h : μ.inv ≫ S.f.fSharpInverseImage = f.fSharpInverseImage := by
    rw [Iso.inv_comp_eq, hμ]
  exact congrArg (fun k => k.hom.app U y) h

/-- **The ideal of the rebased problem**: the ideal `f₁⁻¹𝒥` of `S`, read as a module over
`f₂⁻¹𝒪_{B₂}` through `μ`. -/
abbrev rebaseIdeal :
    SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor f.toToposHom).obj B₂.O)) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map μ.inv)).obj S.I

/-- **The inclusion of the ideal of the rebased problem**: the inclusion of `S` followed by `θ`. -/
def rebaseIdealInclusion :
    (SheafOfModules.restrictScalars ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        ((inverseImageCommRingFunctor f.toToposHom).map r))).obj (S.rebaseIdeal f μ) ⟶
      SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((inverseImageCommRingFunctor f.toToposHom).obj E)) where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map
            ((inverseImageCommRingFunctor f.toToposHom).map r))).obj
              (S.rebaseIdeal f μ)).val.obj U)
        (Y := (SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((inverseImageCommRingFunctor f.toToposHom).obj E))).val.obj U)
        { toFun := fun x => θ.hom.hom.app U (S.idealInclusion.val.app U x)
          map_add' := fun x y =>
            (congrArg _ (map_add (ConcreteCategory.hom (S.idealInclusion.val.app U)) x y)).trans
              (map_add _ _ _)
          map_smul' := fun s x => by
            have hs := rebase_reduction_inv_apply S f r θ μ hθ U s
            have hθs : θ.hom.hom.app U (θ.inv.hom.app U s) = s :=
              congrArg (fun k => k.hom.app U s) θ.inv_hom_id
            change θ.hom.hom.app U (S.idealInclusion.val.app U
                (show S.I.val.obj U from
                  (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
                    ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)).obj.obj U from
                    μ.inv.hom.app U (((inverseImageCommRingFunctor f.toToposHom).map r).hom.app
                      U s)) • (show S.I.val.obj U from x))) =
              (show ((inverseImageCommRingFunctor f.toToposHom).obj E).obj.obj U from s) *
                θ.hom.hom.app U (S.idealInclusion.val.app U x)
            rw [← hs]
            refine (congrArg (θ.hom.hom.app U) ((ConcreteCategory.hom
              (S.idealInclusion.val.app U)).map_smul (θ.inv.hom.app U s) x)).trans ?_
            exact ((θ.hom.hom.app U).hom.map_mul _ _).trans
              (congrArg (· * θ.hom.hom.app U (S.idealInclusion.val.app U x)) hθs) }
      naturality := fun {U V} g => by
        ext x
        exact (congrArg (θ.hom.hom.app V)
          (PresheafOfModules.naturality_apply S.idealInclusion.val g x)).trans
            (NatTrans.naturality_apply θ.hom.hom g _) }

/-- On sections, the inclusion of the ideal of the rebased problem is the inclusion of `S`
followed by `θ`. -/
theorem rebaseIdealInclusion_val_app (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    (S.rebaseIdealInclusion f r θ μ hθ).val.app U x =
      θ.hom.hom.app U (S.idealInclusion.val.app U x) :=
  rfl

/-- **The prescribed map of the rebased problem**: that of `S` followed by `β`. -/
def rebaseC :
    S.rebaseIdeal f μ ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map f.fSharpInverseImage)).obj G where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := (S.rebaseIdeal f μ).val.obj U)
        (Y := ((SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map f.fSharpInverseImage)).obj G).val.obj U)
        { toFun := fun x => β.hom.val.app U (S.c.val.app U x)
          map_add' := fun x y =>
            (congrArg _ (map_add (ConcreteCategory.hom (S.c.val.app U)) x y)).trans
              (map_add _ _ _)
          map_smul' := fun s x => by
            have hs := rebase_fSharp_inv_apply S f μ hμ U s
            change β.hom.val.app U (S.c.val.app U
                (show S.I.val.obj U from
                  (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
                    ((inverseImageCommRingFunctor S.f.toToposHom).obj B₁.O)).obj.obj U from
                    μ.inv.hom.app U s) • (show S.I.val.obj U from x))) =
              (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O).obj.obj U
                from f.fSharpInverseImage.hom.app U s) •
                β.hom.val.app U (S.c.val.app U x)
            rw [← hs]
            refine (congrArg (β.hom.val.app U) ((ConcreteCategory.hom
              (S.c.val.app U)).map_smul (μ.inv.hom.app U s) x)).trans ?_
            exact (ConcreteCategory.hom (β.hom.val.app U)).map_smul _ _ }
      naturality := fun {U V} g => by
        ext x
        exact (congrArg (β.hom.val.app V)
          (PresheafOfModules.naturality_apply S.c.val g x)).trans
            (PresheafOfModules.naturality_apply β.hom.val g _) }

/-- On sections, the prescribed map of the rebased problem is `c` of `S` followed by `β`. -/
theorem rebaseC_val_app (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    (S.rebaseC f μ hμ β).val.app U x = β.hom.val.app U (S.c.val.app U x) :=
  rfl

/-- **`S` moved to the base `B₂`** along the identifications `θ`, `μ` of the lower rows and the
identification `β` of target modules: the morphism `f₂`, the thickening `r` of `B₂`, the ideal of
`S` read over `f₂⁻¹𝒪_{B₂}`, target `𝒢'`, and prescribed map `β ∘ c`. -/
def rebase (hr : Presheaf.IsLocallySurjective B₂.J r.hom)
    (hsq : ∀ U : B₂.Cᵒᵖ, (RingHom.ker (r.hom.app U).hom) ^ 2 = ⊥) :
    RingedToposExtensionProblem X B₂ where
  f := f
  baseExtension := E
  baseReduction := r
  baseLocallySurjective := hr
  baseSquareZero := hsq
  I := S.rebaseIdeal f μ
  G := G
  idealInclusion := S.rebaseIdealInclusion f r θ μ hθ
  c := S.rebaseC f μ hμ β
  idealZero U a := by
    change ((inverseImageCommRingFunctor f.toToposHom).map r).hom.app U
      (θ.hom.hom.app U (S.idealInclusion.val.app U a)) = 0
    have h := congrArg (fun k => k.hom.app U (S.idealInclusion.val.app U a)) hθ
    refine h.trans ?_
    change μ.hom.hom.app U (((inverseImageCommRingFunctor S.f.toToposHom).map
      S.baseReduction).hom.app U (S.idealInclusion.val.app U a)) = 0
    rw [S.idealZero U a, map_zero]
  idealUniversal U y hy := by
    have h0 : ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U
        (θ.inv.hom.app U y) = 0 := by
      rw [rebase_reduction_inv_apply S f r θ μ hθ U y, hy, map_zero]
    obtain ⟨x, hx, hu⟩ := S.idealUniversal U _ h0
    have hθ₁ : ∀ z, θ.hom.hom.app U (θ.inv.hom.app U z) = z := fun z =>
      congrArg (fun k => k.hom.app U z) θ.inv_hom_id
    have hθ₂ : ∀ z, θ.inv.hom.app U (θ.hom.hom.app U z) = z := fun z =>
      congrArg (fun k => k.hom.app U z) θ.hom_inv_id
    refine ⟨x, ?_, fun x' hx' => hu x' ?_⟩
    · change θ.hom.hom.app U (S.idealInclusion.val.app U x) = y
      rw [show (S.idealInclusion.val.app U x : _) = θ.inv.hom.app U y from hx, hθ₁]
    · change θ.hom.hom.app U (S.idealInclusion.val.app U x') = y at hx'
      rw [← hx']
      exact (hθ₂ _).symm

variable (hr : Presheaf.IsLocallySurjective B₂.J r.hom)
  (hsq : ∀ U : B₂.Cᵒᵖ, (RingHom.ker (r.hom.app U).hom) ^ 2 = ⊥)

/-- The morphism of the rebased problem is `f`. -/
theorem rebase_f : (S.rebase f r θ μ hθ hμ β hr hsq).f = f := rfl

/-- The target module of the rebased problem is `G`. -/
theorem rebase_G : (S.rebase f r θ μ hθ hμ β hr hsq).G = G := rfl

/-! ### Solutions -/

omit [X.J.HasSheafCompose (forget RingCat)] [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `β⁻¹ (β x) = x`, on sections. -/
private theorem iso_inv_hom_apply {R : Sheaf X.J RingCat.{w}} {M N : SheafOfModules.{w} R}
    (e : M ≅ N) (U : X.Cᵒᵖ) (x : M.val.obj U) : e.inv.val.app U (e.hom.val.app U x) = x :=
  congrArg (fun k : M ⟶ M => k.val.app U x) e.hom_inv_id

omit [X.J.HasSheafCompose (forget RingCat)] [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private theorem iso_hom_inv_apply {R : Sheaf X.J RingCat.{w}} {M N : SheafOfModules.{w} R}
    (e : M ≅ N) (U : X.Cᵒᵖ) (x : N.val.obj U) : e.hom.val.app U (e.inv.val.app U x) = x :=
  iso_inv_hom_apply e.symm U x

/-- **A solution of `S` is a solution of its rebase**: the same thickened structure sheaf and
reduction, the base map read through `θ`, the kernel through `β`. -/
def rebaseSolution (P : S.CompatibleFirstOrderThickening) :
    (S.rebase f r θ μ hθ hμ β hr hsq).CompatibleFirstOrderThickening where
  extension := P.extension
  reduction := P.reduction
  locallySurjective := P.locallySurjective
  squareZero := P.squareZero
  baseMap := θ.inv ≫ P.baseMap
  baseMap_reduction := by
    change θ.inv ≫ P.baseMap ≫ P.reduction = (inverseImageCommRingFunctor f.toToposHom).map r ≫
      f.fSharpInverseImage
    rw [P.baseMap_reduction, ← hμ, ← Category.assoc
      ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction), ← hθ,
      Category.assoc, Iso.inv_hom_id_assoc]
  kernelInclusion := (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map P.reduction)).map β.inv ≫ P.kernelInclusion
  kernelZero U a := P.kernelZero U (β.inv.val.app U a)
  kernelUniversal U a ha := by
    obtain ⟨g, hg, hu⟩ := P.kernelUniversal U a ha
    refine ⟨β.hom.val.app U g, ?_, fun g' hg' => ?_⟩
    · change P.kernelInclusion.val.app U (β.inv.val.app U (β.hom.val.app U g)) = a
      exact (congrArg (P.kernelInclusion.val.app U) (iso_inv_hom_apply β U g)).trans hg
    · rw [← hu (β.inv.val.app U g') hg']
      exact (iso_hom_inv_apply β U g').symm
  baseMap_ideal U a := by
    change P.baseMap.hom.app U (θ.inv.hom.app U (θ.hom.hom.app U (S.idealInclusion.val.app U a))) =
      P.kernelInclusion.val.app U (β.inv.val.app U (β.hom.val.app U (S.c.val.app U a)))
    refine (congrArg (P.baseMap.hom.app U)
      (congrArg (fun k => k.hom.app U (S.idealInclusion.val.app U a)) θ.hom_inv_id)).trans ?_
    refine (P.baseMap_ideal U a).trans ?_
    exact congrArg (P.kernelInclusion.val.app U) (iso_inv_hom_apply β U _).symm

/-- **A solution of the rebase is a solution of `S`**: the base map read through `θ⁻¹`, the kernel
through `β⁻¹`. -/
def rebaseSolutionInv (Q : (S.rebase f r θ μ hθ hμ β hr hsq).CompatibleFirstOrderThickening) :
    S.CompatibleFirstOrderThickening where
  extension := Q.extension
  reduction := Q.reduction
  locallySurjective := Q.locallySurjective
  squareZero := Q.squareZero
  baseMap := θ.hom ≫ Q.baseMap
  baseMap_reduction := by
    have hQ : Q.baseMap ≫ Q.reduction =
        (inverseImageCommRingFunctor f.toToposHom).map r ≫ f.fSharpInverseImage :=
      Q.baseMap_reduction
    calc (θ.hom ≫ Q.baseMap) ≫ Q.reduction = θ.hom ≫ (Q.baseMap ≫ Q.reduction) :=
          Category.assoc _ _ _
      _ = θ.hom ≫ ((inverseImageCommRingFunctor f.toToposHom).map r ≫
            f.fSharpInverseImage) := congrArg (θ.hom ≫ ·) hQ
      _ = (θ.hom ≫ (inverseImageCommRingFunctor f.toToposHom).map r) ≫
            f.fSharpInverseImage := (Category.assoc _ _ _).symm
      _ = ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫ μ.hom) ≫
            f.fSharpInverseImage := congrArg (· ≫ f.fSharpInverseImage) hθ
      _ = _ := (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hμ)
  kernelInclusion := (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map Q.reduction)).map β.hom ≫ Q.kernelInclusion
  kernelZero U a := Q.kernelZero U (β.hom.val.app U a)
  kernelUniversal U a ha := by
    obtain ⟨g, hg, hu⟩ := Q.kernelUniversal U a ha
    refine ⟨β.inv.val.app U g, ?_, fun g' hg' => ?_⟩
    · change Q.kernelInclusion.val.app U (β.hom.val.app U (β.inv.val.app U g)) = a
      exact (congrArg (Q.kernelInclusion.val.app U) (iso_hom_inv_apply β U g)).trans hg
    · rw [← hu (β.hom.val.app U g') hg']
      exact (iso_inv_hom_apply β U g').symm
  baseMap_ideal U a := Q.baseMap_ideal U a

/-- An isomorphism of solutions of `S` is one of their rebases. -/
def rebaseSolutionIso {P P' : S.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso P P') :
    CompatibleFirstOrderThickening.Iso (S.rebaseSolution f r θ μ hθ hμ β hr hsq P)
      (S.rebaseSolution f r θ μ hθ hμ β hr hsq P') where
  hom := e.hom
  reduction_comm := e.reduction_comm
  baseMap_comm := by
    change (θ.inv ≫ P.baseMap) ≫ e.hom.hom = θ.inv ≫ P'.baseMap
    rw [Category.assoc, e.baseMap_comm]
  kernel_comm U g := e.kernel_comm U (β.inv.val.app U g)

/-- An isomorphism of solutions of the rebase is one of the corresponding solutions of `S`. -/
def rebaseSolutionInvIso {Q Q' : (S.rebase f r θ μ hθ hμ β hr hsq).CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso Q Q') :
    CompatibleFirstOrderThickening.Iso (S.rebaseSolutionInv f r θ μ hθ hμ β hr hsq Q)
      (S.rebaseSolutionInv f r θ μ hθ hμ β hr hsq Q') where
  hom := e.hom
  reduction_comm := e.reduction_comm
  baseMap_comm := (Category.assoc _ _ _).trans (congrArg (θ.hom ≫ ·) e.baseMap_comm)
  kernel_comm U g := e.kernel_comm U (β.hom.val.app U g)

/-- A solution of `S` is isomorphic to the solution of `S` attached to its rebase. -/
def rebaseSolutionInvSolutionIso (P : S.CompatibleFirstOrderThickening) :
    CompatibleFirstOrderThickening.Iso
      (S.rebaseSolutionInv f r θ μ hθ hμ β hr hsq (S.rebaseSolution f r θ μ hθ hμ β hr hsq P)) P
    where
  hom := Iso.refl _
  reduction_comm := Category.id_comp _
  baseMap_comm := by
    change (θ.hom ≫ θ.inv ≫ P.baseMap) ≫ 𝟙 _ = P.baseMap
    rw [Category.comp_id, Iso.hom_inv_id_assoc]
  kernel_comm U g := by
    change P.kernelInclusion.val.app U (β.inv.val.app U (β.hom.val.app U g)) =
      P.kernelInclusion.val.app U g
    exact congrArg (P.kernelInclusion.val.app U) (iso_inv_hom_apply β U g)

/-- A solution of the rebase is isomorphic to the rebase of the solution of `S` attached to it. -/
def rebaseSolutionSolutionInvIso
    (Q : (S.rebase f r θ μ hθ hμ β hr hsq).CompatibleFirstOrderThickening) :
    CompatibleFirstOrderThickening.Iso
      (S.rebaseSolution f r θ μ hθ hμ β hr hsq (S.rebaseSolutionInv f r θ μ hθ hμ β hr hsq Q)) Q
    where
  hom := Iso.refl _
  reduction_comm := Category.id_comp _
  baseMap_comm := (Category.comp_id _).trans (Iso.inv_hom_id_assoc θ Q.baseMap)
  kernel_comm U g := by
    change Q.kernelInclusion.val.app U (β.hom.val.app U (β.inv.val.app U g)) =
      Q.kernelInclusion.val.app U g
    exact congrArg (Q.kernelInclusion.val.app U) (iso_hom_inv_apply β U g)

/-- **The isomorphism classes of solutions of `S` and of its rebase correspond.** -/
def rebaseIsomorphismClassesEquiv :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      CompatibleFirstOrderThickening.IsomorphismClasses (S.rebase f r θ μ hθ hμ β hr hsq) where
  toFun := Quotient.map (S.rebaseSolution f r θ μ hθ hμ β hr hsq)
    fun _ _ ⟨e⟩ => ⟨S.rebaseSolutionIso f r θ μ hθ hμ β hr hsq e⟩
  invFun := Quotient.map (S.rebaseSolutionInv f r θ μ hθ hμ β hr hsq)
    fun _ _ ⟨e⟩ => ⟨S.rebaseSolutionInvIso f r θ μ hθ hμ β hr hsq e⟩
  left_inv p := Quotient.inductionOn p fun P =>
    Quotient.sound ⟨S.rebaseSolutionInvSolutionIso f r θ μ hθ hμ β hr hsq P⟩
  right_inv q := Quotient.inductionOn q fun Q =>
    Quotient.sound ⟨S.rebaseSolutionSolutionInvIso f r θ μ hθ hμ β hr hsq Q⟩

/-- **`S` has a solution exactly when its rebase has one.** -/
theorem nonempty_rebase_iff :
    Nonempty (S.rebase f r θ μ hθ hμ β hr hsq).CompatibleFirstOrderThickening ↔
      Nonempty S.CompatibleFirstOrderThickening :=
  ⟨fun ⟨Q⟩ => ⟨S.rebaseSolutionInv f r θ μ hθ hμ β hr hsq Q⟩,
    fun ⟨P⟩ => ⟨S.rebaseSolution f r θ μ hθ hμ β hr hsq P⟩⟩

end Deformation.ToposThickening.RingedToposExtensionProblem

end
