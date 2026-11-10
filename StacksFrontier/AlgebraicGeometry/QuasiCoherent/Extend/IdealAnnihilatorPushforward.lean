module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.IdealAnnihilator
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pushforward of the sections annihilated by an ideal sheaf

Let `f : X ⟶ Y` be a morphism of schemes, let `I` be an ideal sheaf on `Y` and let `F` be a
module on `X`. Extending `I` along `f` gives an ideal sheaf on `X`, namely the image of the
canonical map `f^*I ⟶ 𝒪_X`, and the subsheaf of `F` annihilated by that extended ideal pushes
forward to the subsheaf of `f_*F` annihilated by `I`. This file proves that, as an equality of
the two subsheaves inside `f_*F`. It is Stacks Tag 07ZN, and it needs no quasi-compactness,
quasi-separatedness or quasi-coherence.

## Main definitions

* `AlgebraicGeometry.extendedIdealSheafMap` is the canonical map `f^*I ⟶ 𝒪_X`.
* `AlgebraicGeometry.extendedIdealSheaf` is its image, the extended ideal sheaf, and
  `AlgebraicGeometry.extendedIdealSheafι` is the inclusion of that image in `𝒪_X`.

## Main results

* `AlgebraicGeometry.pushforward_annihilatorSubsheaf_range_eq` identifies the two subsheaves
  inside `f_*F` on every open of `Y`.

## Implementation notes

The extended ideal has to be taken as an image rather than as `f^*I` itself, because inverse
image need not preserve the injection `I ⟶ 𝒪_Y`.

Annihilation of a section `s` of `F` over `U` is recast as the vanishing of a composite of
maps of sheaves of modules: `AlgebraicGeometry.sectionAction` turns `s` into a map out of
`𝒪_X`, and `AlgebraicGeometry.comp_sectionAction_eq_zero_iff` says that `I` kills `s` exactly
when `I ⟶ 𝒪_X ⟶ ⋯` is zero. In that form the statement about the extended ideal transfers
across the `f^* ⊣ f_*` adjunction, which is the content of
`AlgebraicGeometry.extendedIdealSheafι_comp_eq_zero_iff`.

The coefficient of a scalar action here is a section of `X.ringCatSheaf`, whose head
`TopCat.Sheaf` is a non-reducible definition in Mathlib; so `rw`'s motive check, which runs at
`implicit` transparency, fails on goals mentioning `SheafOfModules.unit X.ringCatSheaf` even
when the pattern is displayed in the goal. Every step of this file is therefore composed from
explicitly-typed `have`s with `congrArg`, `calc` and `Iff.trans`, which are checked at default
transparency, rather than driven by `rw` or `simp` through the coercion. The three restriction
identities that recur are isolated as `presheafMap_comp_apply_subsingleton`,
`schemeMap_comp_apply_subsingleton` and `schemeMap_comp_apply_eq_self`; they hold because the
opens of a scheme form a poset, so any two morphisms between the same two opens agree.

## References

* [Stacks Project, Tag 07ZN](https://stacks.math.columbia.edu/tag/07ZN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Opposite TopologicalSpace

section Restriction

variable {X : Scheme.{u}}

/-- Two successive restrictions of a section of a module agree with any single restriction
between the same two opens: the category of opens is a poset, so the composite is forced. -/
private lemma presheafMap_comp_apply_subsingleton (M : X.Modules)
    {A B C : X.Opens} (p : A ⟶ B) (q : B ⟶ C) (pq : A ⟶ C) (x : Γ(M, C)) :
    M.presheaf.map p.op (M.presheaf.map q.op x) = M.presheaf.map pq.op x := by
  rw [← M.presheaf.map_comp_apply, ← op_comp, Subsingleton.elim (p ≫ q) pq]

/-- The structure-sheaf version of `presheafMap_comp_apply_subsingleton`. -/
private lemma schemeMap_comp_apply_subsingleton
    {A B C : X.Opens} (p : A ⟶ B) (q : B ⟶ C) (pq : A ⟶ C) (x : Γ(X, C)) :
    X.presheaf.map p.op (X.presheaf.map q.op x) = X.presheaf.map pq.op x := by
  rw [← X.presheaf.map_comp_apply, ← op_comp, Subsingleton.elim (p ≫ q) pq]

/-- Restricting a section of the structure sheaf out to a larger open and back is the
identity. -/
private lemma schemeMap_comp_apply_eq_self {A B : X.Opens} (p : A ⟶ B) (q : B ⟶ A)
    (x : Γ(X, A)) : X.presheaf.map p.op (X.presheaf.map q.op x) = x := by
  rw [← X.presheaf.map_comp_apply, ← op_comp, Subsingleton.elim (p ≫ q) (𝟙 A), op_id,
    X.presheaf.map_id]
  rfl

/-- If the scalar action of a section pulled back along `snd` kills the restriction of `s` along
`fst`, and `l` is a section of `snd`, then the action already kills the restriction along `g`. -/
private lemma smul_map_eq_zero_of_smul_map_eq_zero {X : Scheme.{u}} (F : X.Modules)
    {U V P : X.Opens} (fst : P ⟶ U) (snd : P ⟶ V) (l : V ⟶ P) (g : V ⟶ U) (a : Γ(X, V))
    (s : Γ(F, U)) (h : X.presheaf.map snd.op a • F.presheaf.map fst.op s = 0) :
    a • F.presheaf.map g.op s = 0 :=
  calc a • F.presheaf.map g.op s
      = X.presheaf.map l.op (X.presheaf.map snd.op a) • F.presheaf.map l.op
          (F.presheaf.map fst.op s) := by
        rw [schemeMap_comp_apply_eq_self l snd,
          presheafMap_comp_apply_subsingleton F l fst g s]
    _ = F.presheaf.map l.op (X.presheaf.map snd.op a • F.presheaf.map fst.op s) :=
        (Scheme.Modules.map_smul (M := F) l _ _).symm
    _ = F.presheaf.map l.op 0 := congrArg _ h
    _ = 0 := map_zero _

end Restriction

/-- The canonical map from the inverse image of an ideal sheaf to the structure
sheaf of the source. -/
@[ega "0 4.3.5"]
noncomputable def extendedIdealSheafMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.Modules) (i : I ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback f).obj I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    Scheme.Modules.instIsRightAdjointPushforward f
  (Scheme.Modules.pullback f).map i ≫
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

/-- The ideal sheaf obtained by extending `I` along `f`, i.e. the image of
`extendedIdealSheafMap`. -/
@[ega "0 4.3.5"]
noncomputable def extendedIdealSheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.Modules) (i : I ⟶ SheafOfModules.unit Y.ringCatSheaf) :=
  Abelian.image (extendedIdealSheafMap f I i)

/-- The inclusion of the extended ideal sheaf in the structure sheaf. -/
noncomputable def extendedIdealSheafι {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.Modules) (i : I ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    extendedIdealSheaf f I i ⟶ SheafOfModules.unit X.ringCatSheaf :=
  Abelian.image.ι (extendedIdealSheafMap f I i)

/-- The inclusion of the extended ideal sheaf in the structure sheaf is a monomorphism. -/
instance extendedIdealSheafι_mono {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.Modules) (i : I ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    Mono (extendedIdealSheafι f I i) := by
  unfold extendedIdealSheafι
  exact Fork.IsLimit.mono
    (s := Fork.ofι (kernel.ι (cokernel.π (extendedIdealSheafMap f I i)))
      ((kernel.condition _).trans comp_zero.symm))
    (kernelIsKernel (cokernel.π (extendedIdealSheafMap f I i)))

/-- The target of `sectionAction`: the pushforward along `U ⟶ X` of the slice of `F` over `U`. -/
private noncomputable abbrev sectionTarget {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) :
    X.Modules :=
  (SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := X.ringCatSheaf) U)).obj
    (F.over U)

/-- Scalar multiplication by a fixed section `s` of `F` over `U`, as a map of sheaves of
modules out of the structure sheaf. -/
private noncomputable def sectionAction {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (s : Γ(F, U)) : SheafOfModules.unit X.ringCatSheaf ⟶ sectionTarget F U where
  val.app V := @ModuleCat.ofHom _ _
    ((SheafOfModules.unit X.ringCatSheaf).val.obj V) ((sectionTarget F U).val.obj V)
    _ ((SheafOfModules.unit X.ringCatSheaf).val.obj V).isModule
    _ ((sectionTarget F U).val.obj V).isModule
    { toFun r := (X.presheaf.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op r) •
        F.presheaf.map (prod.fst : U ⨯ V.unop ⟶ U).op s
      map_add' r t :=
        (congrArg (fun c => c • F.presheaf.map (prod.fst : U ⨯ V.unop ⟶ U).op s)
          (map_add (ConcreteCategory.hom
              (X.presheaf.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op))
            (show Γ(X, V.unop) from r) (show Γ(X, V.unop) from t))).trans
          (add_smul _ _ _)
      map_smul' r t :=
        (congrArg (fun c => c • F.presheaf.map (prod.fst : U ⨯ V.unop ⟶ U).op s)
          (map_mul (ConcreteCategory.hom
              (X.presheaf.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op))
            (show Γ(X, V.unop) from r) (show Γ(X, V.unop) from t))).trans
          (mul_smul _ _ _) }
  val.naturality {V W} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (X.presheaf.map (prod.snd : U ⨯ W.unop ⟶ W.unop).op
        (X.presheaf.map g.unop.op (show Γ(X, V.unop) from r))) •
        F.presheaf.map (prod.fst : U ⨯ W.unop ⟶ U).op s =
      F.presheaf.map (prod.map (𝟙 U) g.unop).op
        ((X.presheaf.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op (show Γ(X, V.unop) from r)) •
          F.presheaf.map (prod.fst : U ⨯ V.unop ⟶ U).op s)
    rw [Scheme.Modules.map_smul,
      presheafMap_comp_apply_subsingleton F (prod.map (𝟙 U) g.unop)
        (prod.fst : U ⨯ V.unop ⟶ U) (prod.fst : U ⨯ W.unop ⟶ U) s,
      schemeMap_comp_apply_subsingleton (prod.map (𝟙 U) g.unop)
        (prod.snd : U ⨯ V.unop ⟶ V.unop)
        ((prod.snd : U ⨯ W.unop ⟶ W.unop) ≫ g.unop) (show Γ(X, V.unop) from r),
      schemeMap_comp_apply_subsingleton (prod.snd : U ⨯ W.unop ⟶ W.unop) g.unop
        ((prod.snd : U ⨯ W.unop ⟶ W.unop) ≫ g.unop) (show Γ(X, V.unop) from r)]

/-- A section is annihilated by the ideal exactly when the ideal composed with the section's
scalar action is zero. -/
private lemma comp_sectionAction_eq_zero_iff {X : Scheme.{u}} (I F : X.Modules)
    (i : I ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) (s : Γ(F, U)) :
    i ≫ sectionAction F U s = 0 ↔
      ∀ (V : X.Opens) (g : V ⟶ U) (r : Γ(I, V)),
        (show Γ(X, V) from i.app V r) • F.presheaf.map g.op s = 0 := by
  constructor
  · intro h V g r
    have h' := congrArg (fun k => k.app V r) h
    change (X.presheaf.map (prod.snd : U ⨯ V ⟶ V).op (i.app V r)) •
      F.presheaf.map (prod.fst : U ⨯ V ⟶ U).op s = 0 at h'
    exact smul_map_eq_zero_of_smul_map_eq_zero F (prod.fst : U ⨯ V ⟶ U) prod.snd
      (prod.lift g (𝟙 V)) g _ _ h'
  · intro h
    ext V r
    change (X.presheaf.map (prod.snd : U ⨯ V ⟶ V).op (i.app V r)) •
      F.presheaf.map (prod.fst : U ⨯ V ⟶ U).op s = 0
    have hn := PresheafOfModules.naturality_apply i.val
      (prod.snd : U ⨯ V ⟶ V).op r
    change i.app (U ⨯ V) (I.presheaf.map prod.snd.op r) =
      X.presheaf.map prod.snd.op (i.app V r) at hn
    rw [← hn]
    exact h (U ⨯ V) prod.fst (I.presheaf.map prod.snd.op r)

/-- Precomposition with the extended ideal's inclusion vanishes exactly when the original
ideal's composite with the pushforward does. -/
private lemma extendedIdealSheafι_comp_eq_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.Modules) (i : I ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (G : X.Modules) (a : SheafOfModules.unit X.ringCatSheaf ⟶ G) :
    extendedIdealSheafι f I i ≫ a = 0 ↔
      i ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map a = 0 := by
  have hra : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    Scheme.Modules.instIsRightAdjointPushforward f
  have him : extendedIdealSheafι f I i ≫ a = 0 ↔
      extendedIdealSheafMap f I i ≫ a = 0 := by
    refine ⟨fun h => ?_, Abelian.image_ι_comp_eq_zero⟩
    calc extendedIdealSheafMap f I i ≫ a
        = (Abelian.factorThruImage (extendedIdealSheafMap f I i) ≫
            Abelian.image.ι (extendedIdealSheafMap f I i)) ≫ a :=
          congrArg (fun k => k ≫ a) (Abelian.image.fac (extendedIdealSheafMap f I i)).symm
      _ = Abelian.factorThruImage (extendedIdealSheafMap f I i) ≫
            (extendedIdealSheafι f I i ≫ a) := Category.assoc _ _ _
      _ = Abelian.factorThruImage (extendedIdealSheafMap f I i) ≫ 0 := congrArg _ h
      _ = 0 := comp_zero
  have key : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv I G
        (extendedIdealSheafMap f I i ≫ a) =
      i ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map a :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left i
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫ a)).trans
      (congrArg (fun k => i ≫ k)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
            (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) a).trans
          (congrArg (fun k => k ≫ (Scheme.Modules.pushforward f).map a)
            (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _))))
  have hzero : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv I G 0 = 0 := by
    simp [Adjunction.homEquiv_apply]
  exact him.trans
    ((((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv I G).apply_eq_iff_eq
        (x := extendedIdealSheafMap f I i ≫ a) (y := 0)).symm.trans
      (iff_of_eq (congrArg₂ Eq key hzero)))

/-- The same vanishing criterion for the pushed-forward scalar action. -/
private lemma comp_pushforward_sectionAction_eq_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.Modules) (F : X.Modules)
    (j : I ⟶ (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
    (U : Y.Opens) (s : Γ(F, f ⁻¹ᵁ U)) :
    j ≫ (Scheme.Modules.pushforward f).map (sectionAction F (f ⁻¹ᵁ U) s) = 0 ↔
      ∀ (V : Y.Opens) (g : V ⟶ U) (r : Γ(I, V)),
        (show Γ(X, f ⁻¹ᵁ V) from j.app V r) •
          F.presheaf.map ((Opens.map f.base).map g).op s = 0 := by
  constructor
  · intro h V g r
    have h' := congrArg (fun k => k.app V r) h
    change (X.presheaf.map (prod.snd : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ V).op (j.app V r)) •
      F.presheaf.map (prod.fst : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ U).op s = 0 at h'
    exact smul_map_eq_zero_of_smul_map_eq_zero F (prod.fst : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ U)
      prod.snd (prod.lift ((Opens.map f.base).map g) (𝟙 (f ⁻¹ᵁ V))) _ _ _ h'
  · intro h
    ext V r
    have hn := PresheafOfModules.naturality_apply j.val
      (homOfLE (inf_le_right : U ⊓ V ≤ V)).op r
    change j.app (U ⊓ V) (I.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op r) =
      X.presheaf.map ((Opens.map f.base).map
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).op (j.app V r) at hn
    have h' := h (U ⊓ V) (homOfLE inf_le_left)
      (I.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op r)
    rw [hn] at h'
    change (X.presheaf.map (prod.snd : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ V).op (j.app V r)) •
      F.presheaf.map (prod.fst : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ U).op s = 0
    have hc : ((f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) : X.Opens) ⟶ f ⁻¹ᵁ (U ⊓ V) :=
      homOfLE (le_inf (leOfHom (prod.fst : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ U))
        (leOfHom (prod.snd : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ V)))
    calc (X.presheaf.map (prod.snd : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ V).op (j.app V r)) •
            F.presheaf.map (prod.fst : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ U).op s
        = X.presheaf.map hc.op
              (X.presheaf.map ((Opens.map f.base).map
                (homOfLE (inf_le_right : U ⊓ V ≤ V))).op
                  (show Γ(X, f ⁻¹ᵁ V) from j.app V r)) •
            F.presheaf.map hc.op
              (F.presheaf.map ((Opens.map f.base).map
                (homOfLE (inf_le_left : U ⊓ V ≤ U))).op s) := by
          rw [schemeMap_comp_apply_subsingleton hc
              ((Opens.map f.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
              (prod.snd : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ V)
              (show Γ(X, f ⁻¹ᵁ V) from j.app V r),
            presheafMap_comp_apply_subsingleton F hc
              ((Opens.map f.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
              (prod.fst : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V) ⟶ f ⁻¹ᵁ U) s]
      _ = F.presheaf.map hc.op
            (X.presheaf.map ((Opens.map f.base).map
                (homOfLE (inf_le_right : U ⊓ V ≤ V))).op
                (show Γ(X, f ⁻¹ᵁ V) from j.app V r) •
              F.presheaf.map ((Opens.map f.base).map
                (homOfLE (inf_le_left : U ⊓ V ≤ U))).op s) :=
          (Scheme.Modules.map_smul (M := F) hc _ _).symm
      _ = F.presheaf.map hc.op 0 := congrArg _ h'
      _ = 0 := map_zero _

private lemma range_submoduleInclusion_iff {X : Scheme.{u}} (M : X.Modules)
    (N : M.Submodule) (U : X.Opens) (s : Γ(M, U)) :
    s ∈ Set.range (N.ι.val.app (op U)) ↔ s ∈ N.toSubmodule.obj (op U) := by
  refine ⟨?_, fun hs => ⟨⟨s, hs⟩, rfl⟩⟩
  rintro ⟨x, rfl⟩
  exact x.property

/-- **Stacks Project, Tag 07ZN.** Pushing forward the annihilator of the extended ideal gives
the annihilator of the original ideal, as subobjects of the pushed-forward module. -/
@[stacks 07ZN]
theorem pushforward_annihilatorSubsheaf_range_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.Modules)
    (i : I ⟶ SheafOfModules.unit Y.ringCatSheaf) [Mono i]
    (F : X.Modules) (U : Y.Opens) :
    Set.range (((Scheme.Modules.pushforward f).map
      (annihilatorSubsheaf
        (extendedIdealSheaf f I i) F
        (extendedIdealSheafι f I i)).ι).app U) =
    Set.range (((annihilatorSubsheaf I
      ((Scheme.Modules.pushforward f).obj F) i).ι).val.app (op U)) := by
  ext s
  refine Iff.trans (range_submoduleInclusion_iff F
      (annihilatorSubsheaf (extendedIdealSheaf f I i) F (extendedIdealSheafι f I i))
      (f ⁻¹ᵁ U) (show Γ(F, f ⁻¹ᵁ U) from s))
    (Iff.trans ?_ (range_submoduleInclusion_iff ((Scheme.Modules.pushforward f).obj F)
      (annihilatorSubsheaf I ((Scheme.Modules.pushforward f).obj F) i) U
      (show Γ((Scheme.Modules.pushforward f).obj F, U) from s)).symm)
  refine Iff.trans (mem_annihilatorSubsheaf_iff (extendedIdealSheaf f I i) F
      (extendedIdealSheafι f I i) (f ⁻¹ᵁ U) (show Γ(F, f ⁻¹ᵁ U) from s)) ?_
  refine Iff.trans ?_ (mem_annihilatorSubsheaf_iff I
      ((Scheme.Modules.pushforward f).obj F) i U
      (show Γ((Scheme.Modules.pushforward f).obj F, U) from s)).symm
  refine Iff.trans (comp_sectionAction_eq_zero_iff (extendedIdealSheaf f I i) F
      (extendedIdealSheafι f I i) (f ⁻¹ᵁ U) (show Γ(F, f ⁻¹ᵁ U) from s)).symm ?_
  refine Iff.trans (extendedIdealSheafι_comp_eq_zero_iff f I i _
      (sectionAction F (f ⁻¹ᵁ U) (show Γ(F, f ⁻¹ᵁ U) from s))) ?_
  refine Iff.trans (iff_of_eq (congrArg (fun k => k = 0) (Category.assoc
      i (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      ((Scheme.Modules.pushforward f).map
        (sectionAction F (f ⁻¹ᵁ U) (show Γ(F, f ⁻¹ᵁ U) from s)))).symm)) ?_
  exact comp_pushforward_sectionAction_eq_zero_iff f I F
    (i ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) U
    (show Γ(F, f ⁻¹ᵁ U) from s)

end AlgebraicGeometry

end
