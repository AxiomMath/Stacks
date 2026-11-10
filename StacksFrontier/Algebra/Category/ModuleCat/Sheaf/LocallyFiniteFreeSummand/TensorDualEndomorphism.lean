module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDual
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# The rank-one-operator description of the endomorphism sheaf

Let `(X, O_X)` be a ringed space and let `F` be a sheaf of `O_X`-modules. There is a
canonical morphism `F ⊗ F^∨ ⟶ SheafHom(F, F)` sending a local pure tensor `f ⊗ λ` to the
rank-one endomorphism `g ↦ λ(g) • f`. Stacks 0FNV asserts that it is an isomorphism as soon
as `F` is locally a direct summand of a finite free module, and that is what this file proves.

## Main definitions

* `Stacks.SheafOfModules.OnSpace.sheafHom`, `.dualSheaf` and `.evaluation` are the sheaf-hom,
  the dual and the evaluation pairing of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHom.lean`, read on a ringed space rather
  than on a general ringed site.
* `Stacks.SheafOfModules.OnSpace.rankOne` is the rank-one endomorphism `g ↦ λ(g) • f`
  attached to a section `f` of `F` over `U` and a local functional `λ`, and
  `Stacks.SheafOfModules.OnSpace.tensorEndPresheafMap` is the resulting morphism out of the
  presheaf tensor product.
* `Stacks.SheafOfModules.OnSpace.tensorDualToEndomorphism` is the induced morphism of
  sheaves `F ⊗ F^∨ ⟶ SheafHom(F, F)`.

## Main results

* `Stacks.SheafOfModules.OnSpace.tensorDualToEndomorphism_tmul_apply` evaluates the morphism
  on a local pure tensor, on every object of the slice site, which determines the resulting
  section of the internal hom.
* `Stacks.SheafOfModules.OnSpace.tensorDualToEndomorphism_isIso`: the morphism is an
  isomorphism when `F` is locally a direct summand of a finite free module.

## Implementation notes

Nothing here redefines the internal hom: `sheafHom` and `dualSheaf` are abbreviations for the
library's `Stacks.SheafOfModules.sheafHom` and `Stacks.SheafOfModules.dualSheaf` with the site
taken to be the opens of `X` and the structure presheaf taken to be `X.presheaf`. With those
choices the ring universe and the module universe both collapse to `u`, and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf _` is
`structureSheafRing X` on the nose,
so the abbreviations are transports of spelling and not new constructions. The same holds for
the tensor product: `Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf _`
and `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X`
are definitionally equal, and the latter spelling is used throughout because the monoidal
material of Stacks 01CA is phrased with it.

The proof that the morphism is an isomorphism is local: a retract of `O_U^{⊕n}` gives a finite
dual basis over `U` (`exists_dualBasis`), a dual basis makes the presheaf-level map bijective
on sections over `U` (`tensorEnd_bijective_of_dualBasis`), and a cover by such opens makes it
locally bijective, hence an isomorphism after sheafification.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The sheaf-hom `SheafHom(F, G)` of two sheaves of modules on a ringed space: the
internal-hom presheaf of Tag 03EM, which is a sheaf as soon as `G` is. This is the library's
`Stacks.SheafOfModules.sheafHom` with the site taken to be the opens of `X`, recorded as a
reducible abbreviation so that a section of it is visibly a morphism on the slice site. -/
noncomputable abbrev sheafHom (F G : SheafOfModules.{u} (structureSheafRing X)) :
    SheafOfModules.{u} (structureSheafRing X) :=
  ⟨internalHom X.presheaf F.val G.val,
    internalHom_isSheaf X.presheaf F.val G.val G.isSheaf⟩

/-- `sheafHom` is the library's sheaf-hom, read on a ringed space. -/
theorem sheafHom_eq (F G : SheafOfModules.{u} (structureSheafRing X)) :
    sheafHom X F G =
      Stacks.SheafOfModules.sheafHom X.presheaf (structureSheafRing X).property F G := rfl

/-- The dual `F^∨ = SheafHom(F, O_X)` of a sheaf of modules on a ringed space. -/
@[sga "3 I 4.6.5.1" "more general"]
noncomputable abbrev dualSheaf (F : SheafOfModules.{u} (structureSheafRing X)) :
    SheafOfModules.{u} (structureSheafRing X) :=
  sheafHom X F (SheafOfModules.unit (structureSheafRing X))

/-- The evaluation pairing `F^∨ ⊗ F ⟶ O_X` of a sheaf of modules on a ringed space. -/
noncomputable abbrev evaluation (F : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((dualSheaf X F))).obj (F)) ⟶ SheafOfModules.unit (structureSheafRing X) :=
  Stacks.SheafOfModules.evaluation X.presheaf (structureSheafRing X).property F

attribute [local implicit_reducible] restrFun ORestr PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ ModuleCat.restrictScalars internalHom

/-- The component at an object `V` of the slice site over `U` of a local functional on `F`,
applied to a section of `F` over `V.left`, with its value spelled as a section of the
structure presheaf. Naming it fixes one spelling of the ring, which instance search cannot
otherwise connect to the `ModuleCat` index of `F.val.obj (op V.left)`. -/
noncomputable abbrev dualValue (F : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier} (lam : (dualSheaf X F).val.obj (op U))
    (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)) :
    X.presheaf.obj (op V.unop.left) :=
  (lam.app V).hom g

/-- The restriction of a section of `F` from `U` to an object `V` of the slice site over `U`,
with its type pinned to the sections of `F` over `V.left`. -/
noncomputable abbrev resSection (F : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier} (V : (Over U)ᵒᵖ) (x : F.val.obj (op U)) :
    F.val.obj (op V.unop.left) :=
  (F.val.map V.unop.hom.op).hom x

/-- The value at `V` of a morphism from the structure sheaf of the slice site over `U` to
`F|_U`, with both its argument and its value pinned to sections over `V.left`. -/
noncomputable abbrev unitMapValue (F : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier}
    (a : SheafOfModules.unit ((structureSheafRing X).over U) ⟶ F.over U)
    (V : (Over U)ᵒᵖ) (r : X.presheaf.obj (op V.unop.left)) :
    F.val.obj (op V.unop.left) :=
  (a.val.app V).hom r

/-- The component at an object `V` of the slice site over `U` of a section of
`SheafHom(F, G)` over `U`, applied to a section of `F` over `V.left`. -/
noncomputable abbrev homApp (F G : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier} (a : (sheafHom X F G).val.obj (op U))
    (V : (Over U)ᵒᵖ) (y : F.val.obj (op V.unop.left)) : G.val.obj (op V.unop.left) :=
  (a.app V).hom y

/-- The value of a section of the dual `F^∨` over `U` on a section of `F` over `U`, with its
value spelled as a section of the structure presheaf. -/
noncomputable abbrev dualEval (F : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier} (lam : (dualSheaf X F).val.obj (op U))
    (x : F.val.obj (op U)) : X.presheaf.obj (op U) :=
  (lam.app (op (Over.mk (𝟙 U)))).hom x

/-- The value of a section of `SheafHom(F, G)` over `U` on a section of `F` over `U`, read at
the terminal object of the slice site over `U`. -/
noncomputable abbrev homValue (F G : SheafOfModules.{u} (structureSheafRing X))
    {U : TopologicalSpace.Opens X.carrier} (a : (sheafHom X F G).val.obj (op U))
    (x : F.val.obj (op U)) : G.val.obj (op U) :=
  (a.app (op (Over.mk (𝟙 U)))).hom x

/-- The rank-one endomorphism `g ↦ λ(g) • f` of `F|_U` attached to a section `f` of `F`
over `U` and a local functional `λ` on `F|_U`. -/
noncomputable def rankOne
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) (f : F.val.obj (op U))
    (lam : (dualSheaf X F).val.obj (op U)) :
    (sheafHom X F F).val.obj (op U) where
  app V := ModuleCat.ofHom
    { toFun := fun g => dualValue X F lam V g • (F.val.map V.unop.hom.op).hom f
      map_add' := fun x y =>
        (congrArg (fun r : X.presheaf.obj (op V.unop.left) =>
            r • (F.val.map V.unop.hom.op).hom f)
          (map_add (lam.app V).hom x y)).trans (add_smul _ _ _)
      map_smul' := fun r x =>
        (congrArg (fun c : X.presheaf.obj (op V.unop.left) =>
            c • (F.val.map V.unop.hom.op).hom f)
          ((lam.app V).hom.map_smul r x)).trans (mul_smul _ _ _) }
  naturality {V W} k := by
    ext g
    have hval : dualValue X F lam W ((F.val.map k.unop.left.op).hom g) =
        (X.presheaf.map k.unop.left.op).hom (dualValue X F lam V g) :=
      congrArg (fun q => q.hom g) (lam.naturality k)
    have hres : (F.val.map W.unop.hom.op).hom f =
        (F.val.map k.unop.left.op).hom ((F.val.map V.unop.hom.op).hom f) := by
      rw [← Over.w k.unop, op_comp, PresheafOfModules.map_comp]
      rfl
    have hsmul := PresheafOfModules.map_smul F.val k.unop.left.op
      (dualValue X F lam V g) ((F.val.map V.unop.hom.op).hom f)
    change dualValue X F lam W ((F.val.map k.unop.left.op).hom g) •
        (F.val.map W.unop.hom.op).hom f =
      (F.val.map k.unop.left.op).hom
        (dualValue X F lam V g • (F.val.map V.unop.hom.op).hom f)
    refine Eq.trans ?_ hsmul.symm
    exact congrArg₂ (fun (r : X.presheaf.obj (op W.unop.left))
      (y : F.val.obj (op W.unop.left)) => r • y) hval hres

/-- The rank-one operator is bilinear in the section and the functional. -/
noncomputable def rankOneBilinear
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) :
    F.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      (dualSheaf X F).val.obj (op U) →ₗ[X.presheaf.obj (op U)]
        (sheafHom X F F).val.obj (op U) where
  toFun f :=
    { toFun := rankOne X F U f
      map_add' := by
        intro a b
        apply PresheafOfModules.hom_ext
        intro V
        ext g
        let av : X.presheaf.obj (op V.unop.left) := (a.app V).hom g
        let bv : X.presheaf.obj (op V.unop.left) := (b.app V).hom g
        change (av + bv) • (F.val.map V.unop.hom.op).hom f =
          av • (F.val.map V.unop.hom.op).hom f + bv • (F.val.map V.unop.hom.op).hom f
        exact add_smul _ _ _
      map_smul' := by
        intro r a
        apply PresheafOfModules.hom_ext
        intro V
        ext g
        let av : X.presheaf.obj (op V.unop.left) := (a.app V).hom g
        let rv : X.presheaf.obj (op V.unop.left) := (X.presheaf.map V.unop.hom.op).hom r
        change (rv * av) • (F.val.map V.unop.hom.op).hom f =
          rv • (av • (F.val.map V.unop.hom.op).hom f)
        exact mul_smul _ _ _ }
  map_add' a b := by
    apply LinearMap.ext
    intro lam
    apply PresheafOfModules.hom_ext
    intro V
    ext g
    refine Eq.trans (congrArg (fun y : F.val.obj (op V.unop.left) =>
      dualValue X F lam V g • y) (map_add (F.val.map V.unop.hom.op).hom a b)) ?_
    exact smul_add _ _ _
  map_smul' r a := by
    apply LinearMap.ext
    intro lam
    apply PresheafOfModules.hom_ext
    intro V
    ext g
    refine Eq.trans (congrArg (fun y : F.val.obj (op V.unop.left) =>
      dualValue X F lam V g • y)
        (PresheafOfModules.map_smul F.val V.unop.hom.op r a)) ?_
    have hcomm : ∀ (c d : X.presheaf.obj (op V.unop.left))
        (y : F.val.obj (op V.unop.left)), c • d • y = d • c • y := by
      intro c d y
      rw [smul_smul, smul_smul, mul_comm]
    exact hcomm _ _ _

/-- The rank-one operators assembled into a morphism out of the presheaf tensor product
`F ⊗^{pre} F^∨ ⟶ SheafHom(F, F)`. -/
noncomputable def tensorEndPresheafMap
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    (PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) ((dualSheaf X F).val)) ⟶
      (sheafHom X F F).val where
  app U := by
    letI := homModule X.presheaf F.val F.val U.unop
    exact ModuleCat.ofHom (TensorProduct.lift (rankOneBilinear X F U.unop))
  naturality {U W} k := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro lam
    apply PresheafOfModules.hom_ext
    intro V
    ext g
    refine congrArg (fun y : F.val.obj (op V.unop.left) =>
      dualValue X F lam ((Over.map k.unop).op.obj V) g • y) ?_
    change (F.val.map V.unop.hom.op).hom ((F.val.map k).hom f) =
      (F.val.map (V.unop.hom ≫ k.unop).op).hom f
    rw [op_comp, PresheafOfModules.map_comp]
    rfl

/-- A finite sum of sections of the sheaf-hom is evaluated componentwise. -/
theorem sheafHom_sum_apply
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) {I : Type*} (s : Finset I)
    (a : I → (sheafHom X F G).val.obj (op U))
    (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)) :
    ((∑ i ∈ s, a i : (sheafHom X F G).val.obj (op U)).app V).hom g =
      ∑ i ∈ s, ((a i).app V).hom g := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    change ((a i).app V).hom g + ((∑ i ∈ s, a i).app V).hom g = _
    rw [ih]

/-- A scalar multiple of a section of the sheaf-hom is evaluated componentwise. -/
theorem sheafHom_smul_apply
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) (r : X.presheaf.obj (op U))
    (a : (sheafHom X F G).val.obj (op U))
    (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)) :
    ((r • a : (sheafHom X F G).val.obj (op U)).app V).hom g =
      (X.presheaf.map V.unop.hom.op).hom r • (a.app V).hom g := rfl

/-- On a free sheaf of modules over `U`, the coordinate projections followed by the inclusions
sum to the identity. -/
theorem sum_desc_comp_ιFree (U : TopologicalSpace.Opens X.carrier) {I : Type u} [Fintype I]
    [DecidableEq I] :
    ∑ i, (Limits.Sigma.desc (fun j : I =>
        if j = i then 𝟙 (SheafOfModules.unit ((structureSheafRing X).over U)) else 0) :
          SheafOfModules.free (R := (structureSheafRing X).over U) I ⟶ _) ≫
        SheafOfModules.ιFree i =
      𝟙 (SheafOfModules.free (R := (structureSheafRing X).over U) I) := by
  let R := (structureSheafRing X).over U
  let p (i : I) : SheafOfModules.free (R := R) I ⟶ SheafOfModules.unit R :=
    Limits.Sigma.desc (fun j => if j = i then 𝟙 _ else 0)
  have hp (i j : I) : SheafOfModules.ιFree j ≫ p i = if j = i then 𝟙 _ else 0 :=
    Limits.Sigma.ι_comp_desc _ _
  change ∑ i, p i ≫ SheafOfModules.ιFree i = 𝟙 (SheafOfModules.free (R := R) I)
  apply Limits.Sigma.hom_ext
  intro j
  change SheafOfModules.ιFree (R := R) j ≫ (∑ i, p i ≫ SheafOfModules.ιFree i) =
    SheafOfModules.ιFree (R := R) j ≫ 𝟙 (SheafOfModules.free (R := R) I)
  rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single j]
  · rw [← Category.assoc, hp j j]
    simp
  · intro i _ hij
    rw [← Category.assoc, hp i j]
    simp [Ne.symm hij]
  · simp

/-- A retract of a finite free module over `U` gives a finite dual basis for `F` over `U`:
sections `e i` of `F` and local functionals `lam i` with `∑ i, lam i (g) • e i = g` on every
object of the slice site over `U`. -/
theorem exists_dualBasis
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) (n : ℕ)
    (r : Retract (F.over U)
      (SheafOfModules.free (R := (structureSheafRing X).over U) (ULift.{u} (Fin n)))) :
    ∃ (e : ULift.{u} (Fin n) → F.val.obj (op U))
      (lam : ULift.{u} (Fin n) → (dualSheaf X F).val.obj (op U)),
      ∀ (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)),
        ∑ i, dualValue X F (lam i) V g • resSection X F V (e i) = g := by
  classical
  let I := ULift.{u} (Fin n)
  let R := (structureSheafRing X).over U
  let p (i : I) : SheafOfModules.free (R := R) I ⟶ SheafOfModules.unit R :=
    Limits.Sigma.desc (fun j => if j = i then 𝟙 _ else 0)
  have hsum : ∑ i, p i ≫ SheafOfModules.ιFree i = 𝟙 (SheafOfModules.free (R := R) I) :=
    sum_desc_comp_ιFree X U
  let a (i : I) : SheafOfModules.unit R ⟶ F.over U := SheafOfModules.ιFree i ≫ r.r
  let b (i : I) : F.over U ⟶ SheafOfModules.unit R := r.i ≫ p i
  have hab : ∑ i, b i ≫ a i = 𝟙 (F.over U) := by
    dsimp [a, b]
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum]
    simp_rw [← Category.assoc]
    rw [← Preadditive.sum_comp, hsum, Category.id_comp, r.retract]
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  refine ⟨fun i => (a i).val.app T (1 : X.presheaf.obj (op U)), fun i => (b i).val, ?_⟩
  intro V g
  have ha (i : I) :
      resSection X F V ((a i).val.app T (1 : X.presheaf.obj (op U))) =
      unitMapValue X F (a i) V (1 : X.presheaf.obj (op V.unop.left)) := by
    have h := PresheafOfModules.naturality_apply (a i).val
      (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op (1 : X.presheaf.obj (op U))
    change unitMapValue X F (a i) V ((X.presheaf.map V.unop.hom.op).hom 1) =
      resSection X F V ((a i).val.app T (1 : X.presheaf.obj (op U))) at h
    rw [map_one] at h
    exact h.symm
  have hlin (i : I) (c : X.presheaf.obj (op V.unop.left)) :
      unitMapValue X F (a i) V c = c • unitMapValue X F (a i) V 1 := by
    refine Eq.trans (congrArg (unitMapValue X F (a i) V)
      (mul_one (M := X.presheaf.obj (op V.unop.left)) c).symm) ?_
    exact ((a i).val.app V).hom.map_smul c (1 : X.presheaf.obj (op V.unop.left))
  have h (i : I) : dualValue X F (b i).val V g •
      resSection X F V ((a i).val.app T (1 : X.presheaf.obj (op U))) =
      ((b i ≫ a i).val.app V).hom g :=
    (congrArg (fun z : F.val.obj (op V.unop.left) =>
      dualValue X F (b i).val V g • z) (ha i)).trans
        (hlin i (dualValue X F (b i).val V g)).symm
  change (∑ i, dualValue X F (b i).val V g •
    resSection X F V ((a i).val.app T (1 : X.presheaf.obj (op U)))) = g
  simp_rw [h]
  exact (_root_.SheafOfModules.sum_val_app_apply Finset.univ (fun i => b i ≫ a i) V g).symm.trans
    (congrArg (fun q : F.over U ⟶ F.over U => (q.val.app V).hom g) hab)

/-- A dual basis restricts along any inclusion of opens. -/
theorem dualBasis_restrict
    (F : SheafOfModules.{u} (structureSheafRing X))
    {U W : TopologicalSpace.Opens X.carrier} (k : W ⟶ U)
    {I : Type u} [Fintype I]
    (e : I → F.val.obj (op U))
    (lam : I → (dualSheaf X F).val.obj (op U))
    (h : ∀ (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)),
      ∑ i, dualValue X F (lam i) V g • resSection X F V (e i) = g) :
    ∀ (V : (Over W)ᵒᵖ) (g : F.val.obj (op V.unop.left)),
      ∑ i, dualValue X F (((dualSheaf X F).val.map k.op).hom (lam i)) V g •
        resSection X F V ((F.val.map k.op).hom (e i)) = g := by
  intro V g
  refine Eq.trans ?_ (h ((Over.map k).op.obj V) g)
  apply Finset.sum_congr rfl
  intro i _
  change _ • _ = _ • (F.val.map (V.unop.hom ≫ k).op).hom (e i)
  rw [op_comp, PresheafOfModules.map_comp]
  rfl

/-- A dual basis expands the value of a section of the sheaf-hom on `g` through its values on
the basis. -/
private theorem sum_dualValue_smul_homApp
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) {I : Type u} [Fintype I]
    (e : I → F.val.obj (op U))
    (lam : I → (dualSheaf X F).val.obj (op U))
    (hb : ∀ (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)),
      ∑ i, dualValue X F (lam i) V g • resSection X F V (e i) = g)
    (a : (sheafHom X F G).val.obj (op U)) (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)) :
    ∑ i, dualValue X F (lam i) V g • homApp X F G a V (resSection X F V (e i)) =
      homApp X F G a V g :=
  (Finset.sum_congr rfl fun _ _ => ((a.app V).hom.map_smul _ _).symm).trans
    ((map_sum (a.app V).hom _ _).symm.trans (congrArg (homApp X F G a V) (hb V g)))

/-- A finite dual basis over `U` expands every local functional over `U` in the dual basis. -/
theorem dualBasis_sum_dualEval_smul
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) {I : Type u} [Fintype I]
    (e : I → F.val.obj (op U))
    (lam : I → (dualSheaf X F).val.obj (op U))
    (hb : ∀ (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)),
      ∑ i, dualValue X F (lam i) V g • resSection X F V (e i) = g)
    (l : (dualSheaf X F).val.obj (op U)) :
    ∑ i, dualEval X F l (e i) • lam i = l := by
  apply PresheafOfModules.hom_ext
  intro V
  ext g
  have hn (i : I) : dualValue X F l V (resSection X F V (e i)) =
      (X.presheaf.map V.unop.hom.op).hom (dualEval X F l (e i)) :=
    PresheafOfModules.naturality_apply l
      (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op (e i)
  change dualValue X F (∑ i, dualEval X F l (e i) • lam i) V g = dualValue X F l V g
  refine (sheafHom_sum_apply X F _ U Finset.univ _ V g).trans (Eq.trans ?_
    (sum_dualValue_smul_homApp X F (SheafOfModules.unit (structureSheafRing X)) U e lam hb l V g))
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans (sheafHom_smul_apply X F _ U (dualEval X F l (e i)) (lam i) V g) ?_
  exact (mul_comm _ _).trans (congrArg
    (fun z : X.presheaf.obj (op V.unop.left) => dualValue X F (lam i) V g * z) (hn i).symm)

/-- Given a finite dual basis over `U`, the rank-one map sends `∑ i, a (e i) ⊗ lam i` back
to the endomorphism `a`. -/
theorem tensorEndPresheafMap_app_sum_homValue_tmul
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) {I : Type u} [Fintype I]
    (e : I → F.val.obj (op U))
    (lam : I → (dualSheaf X F).val.obj (op U))
    (hb : ∀ (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)),
      ∑ i, dualValue X F (lam i) V g • resSection X F V (e i) = g)
    (a : (sheafHom X F F).val.obj (op U)) :
    ((tensorEndPresheafMap X F).app (op U)).hom
      (∑ i, homValue X F F a (e i) ⊗ₜ[X.presheaf.obj (op U)] lam i) = a := by
  let B := ((tensorEndPresheafMap X F).app (op U)).hom
  have hres (V : (Over U)ᵒᵖ) (x : F.val.obj (op U)) :
      resSection X F V (homValue X F F a x) = homApp X F F a V (resSection X F V x) :=
    (PresheafOfModules.naturality_apply a
      (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op x).symm
  refine Eq.trans (map_sum B
    (fun i => homValue X F F a (e i) ⊗ₜ[X.presheaf.obj (op U)] lam i) Finset.univ) ?_
  apply PresheafOfModules.hom_ext
  intro V
  ext g
  refine Eq.trans (sheafHom_sum_apply X F F U Finset.univ
    (fun i => B (homValue X F F a (e i) ⊗ₜ[X.presheaf.obj (op U)] lam i)) V g) ?_
  have hterm (i : I) :
      homApp X F F (B (homValue X F F a (e i) ⊗ₜ[X.presheaf.obj (op U)] lam i)) V g =
        dualValue X F (lam i) V g • resSection X F V (homValue X F F a (e i)) :=
    congrArg (fun q => homApp X F F q V g) (TensorProduct.lift.tmul _ _)
  change (∑ i, homApp X F F
    (B (homValue X F F a (e i) ⊗ₜ[X.presheaf.obj (op U)] lam i)) V g) =
      homApp X F F a V g
  calc
    _ = ∑ i, dualValue X F (lam i) V g • homApp X F F a V (resSection X F V (e i)) :=
      Finset.sum_congr rfl fun i _ => (hterm i).trans
        (congrArg (fun z : F.val.obj (op V.unop.left) =>
          dualValue X F (lam i) V g • z) (hres V (e i)))
    _ = _ := sum_dualValue_smul_homApp X F F U e lam hb a V g

/-- Given a finite dual basis over `U`, every section `t` of `F ⊗^{pre} F^∨` over `U` is
recovered from its rank-one image `B t` as `∑ i, B t (e i) ⊗ lam i`. -/
theorem sum_homValue_tmul_tensorEndPresheafMap_app
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) {I : Type u} [Fintype I]
    (e : I → F.val.obj (op U))
    (lam : I → (dualSheaf X F).val.obj (op U))
    (hb : ∀ (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)),
      ∑ i, dualValue X F (lam i) V g • resSection X F V (e i) = g)
    (t : (PresheafOfModules.tensorObj (O := X.presheaf) F.val (dualSheaf X F).val).obj
      (op U)) :
    (∑ i, homValue X F F (((tensorEndPresheafMap X F).app (op U)).hom t) (e i) ⊗ₜ[
        X.presheaf.obj (op U)] lam i :
      (PresheafOfModules.tensorObj (O := X.presheaf) F.val (dualSheaf X F).val).obj
        (op U)) = t := by
  let B := ((tensorEndPresheafMap X F).app (op U)).hom
  induction t using TensorProduct.inductionOn with
  | tmul f l =>
    have hf' : resSection X F (op (Over.mk (𝟙 U))) f = f := by
      change (F.val.map (𝟙 U).op).hom f = f
      rw [op_id, PresheafOfModules.map_id]
      rfl
    have hval (i : I) : homValue X F F (B (f ⊗ₜ[X.presheaf.obj (op U)] l)) (e i) =
        dualEval X F l (e i) • f :=
      congrArg (fun z : F.val.obj (op U) => dualEval X F l (e i) • z) hf'
    refine Eq.trans (Finset.sum_congr rfl fun i _ =>
      congrArg (fun z : F.val.obj (op U) => z ⊗ₜ[X.presheaf.obj (op U)] lam i)
        (hval i)) ?_
    refine Eq.trans (Finset.sum_congr rfl fun i _ =>
      TensorProduct.smul_tmul (dualEval X F l (e i)) f (lam i)) ?_
    refine Eq.trans (TensorProduct.tmul_sum f Finset.univ
      (fun i => dualEval X F l (e i) • lam i)).symm ?_
    exact congrArg (fun z : (dualSheaf X F).val.obj (op U) =>
      f ⊗ₜ[X.presheaf.obj (op U)] z) (dualBasis_sum_dualEval_smul X F U e lam hb l)
  | add t s ht hs =>
    refine Eq.trans (Finset.sum_congr rfl fun i _ =>
      (congrArg (fun z : F.val.obj (op U) => z ⊗ₜ[X.presheaf.obj (op U)] lam i)
        (show homValue X F F (B (t + s)) (e i) =
          homValue X F F (B t) (e i) + homValue X F F (B s) (e i) from
            congrArg (fun q => homValue X F F q (e i))
              (LinearMap.map_add B t s))).trans
          (add_tmul _ _ _)) ?_
    exact Finset.sum_add_distrib.trans (congrArg₂ (· + ·) ht hs)

/-- A finite dual basis over `U` makes the rank-one map bijective on sections over `U`. -/
theorem tensorEnd_bijective_of_dualBasis
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) {I : Type u} [Fintype I]
    (e : I → F.val.obj (op U))
    (lam : I → (dualSheaf X F).val.obj (op U))
    (hb : ∀ (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)),
      ∑ i, dualValue X F (lam i) V g • resSection X F V (e i) = g) :
    Function.Bijective ((tensorEndPresheafMap X F).app (op U)).hom := by
  let Q (a : (sheafHom X F F).val.obj (op U)) :
      (PresheafOfModules.tensorObj (O := X.presheaf) F.val (dualSheaf X F).val).obj (op U) :=
    ∑ i, homValue X F F a (e i) ⊗ₜ[X.presheaf.obj (op U)] lam i
  exact ⟨Function.LeftInverse.injective (g := Q)
      (sum_homValue_tmul_tensorEndPresheafMap_app X F U e lam hb),
    Function.RightInverse.surjective (g := Q)
      (tensorEndPresheafMap_app_sum_homValue_tmul X F U e lam hb)⟩

/-- If `F` is locally a direct summand of a finite free module, the rank-one map is locally
injective and locally surjective. -/
theorem tensorEnd_locallyBijective
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) :
    Presheaf.IsLocallyInjective (JX X)
        ((PresheafOfModules.toPresheaf (O X)).map (tensorEndPresheafMap X F)) ∧
      Presheaf.IsLocallySurjective (JX X)
        ((PresheafOfModules.toPresheaf (O X)).map (tensorEndPresheafMap X F)) := by
  let phi := (PresheafOfModules.toPresheaf (O X)).map (tensorEndPresheafMap X F)
  have hlocal (U : TopologicalSpace.Opens X.carrier) (x : X.carrier) (hx : x ∈ U) :
      ∃ V : TopologicalSpace.Opens X.carrier, ∃ _ : V ⟶ U,
        Function.Bijective (phi.app (op V)) ∧ x ∈ V := by
    obtain ⟨W, hxW, n, ⟨r⟩⟩ := hF x
    obtain ⟨e, lam, hb⟩ := exists_dualBasis X F W n r
    let V := W ⊓ U
    let k : V ⟶ W := homOfLE inf_le_left
    refine ⟨V, homOfLE inf_le_right, ?_, ⟨hxW, hx⟩⟩
    exact tensorEnd_bijective_of_dualBasis X F V
      (fun i => (F.val.map k.op).hom (e i))
      (fun i => ((dualSheaf X F).val.map k.op).hom (lam i))
      (dualBasis_restrict X F k e lam hb)
  constructor
  · constructor
    intro U t s h
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, k, hbij, hxV⟩ := hlocal U.unop x hx
    refine ⟨V, k, ?_, hxV⟩
    apply hbij.injective
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]
  · constructor
    intro U a
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, k, hbij, hxV⟩ := hlocal U x hx
    exact ⟨V, k, hbij.surjective _, hxV⟩

/-- **The canonical morphism `F ⊗ F^∨ ⟶ SheafHom(F, F)`**, which sends a local pure tensor
`f ⊗ λ` to the rank-one endomorphism `g ↦ λ(g) • f`. -/
noncomputable def tensorDualToEndomorphism
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
      ((dualSheaf X F))) ⟶ sheafHom X F F :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheafRing X).obj)).homEquiv _ _).symm (tensorEndPresheafMap X F)

/-- On a local pure tensor of a section `f` and a local functional `lam`, the canonical
morphism is the rank-one endomorphism `g ↦ lam(g) • f`. The formula is recorded on every
object `V` of the slice site over `U`, so it determines the resulting section of the
internal hom. -/
@[stacks 0FNV "tensor_dual_endomorphism_iso"]
theorem tensorDualToEndomorphism_tmul_apply
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier)
    (f : F.val.obj (op U)) (lam : (dualSheaf X F).val.obj (op U))
    (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)) :
    ((((tensorDualToEndomorphism X F).val.app (op U)).hom
      (toTensorSheafSection X F (dualSheaf X F) (op U)
        (f ⊗ₜ[X.presheaf.obj (op U)] lam))).app V).hom g =
      dualValue X F lam V g • (F.val.map V.unop.hom.op).hom f := by
  have h := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheafRing X).obj)).homEquiv _ (sheafHom X F F)).apply_symm_apply
      (tensorEndPresheafMap X F)
  exact congrArg (fun q => ((q.app (op U)).hom
    (f ⊗ₜ[X.presheaf.obj (op U)] lam)).app V |>.hom g) h

/-- **Stacks 0FNV.** If `F` is locally a direct summand of a finite free module, the
canonical rank-one-operator morphism `F ⊗ F^∨ ⟶ SheafHom(F, F)` is an isomorphism. -/
@[stacks 0FNV "tensor_dual_endomorphism_iso"]
theorem tensorDualToEndomorphism_isIso
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) :
    IsIso (tensorDualToEndomorphism X F) := by
  obtain ⟨_, _⟩ := tensorEnd_locallyBijective X F hF
  have hmap : IsIso ((PresheafOfModules.sheafification
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).map
        (tensorEndPresheafMap X F)) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (structureSheafRing X))]
    exact ((JX X).W_iff _).mp ((JX X).W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf (O X)).map (tensorEndPresheafMap X F)))
  rw [show tensorDualToEndomorphism X F =
      (PresheafOfModules.sheafification (R := structureSheafRing X)
          (𝟙 (structureSheafRing X).obj)).map (tensorEndPresheafMap X F) ≫
        (PresheafOfModules.sheafificationAdjunction
          (𝟙 (structureSheafRing X).obj)).counit.app (sheafHom X F F) from rfl]
  have hcounit : IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafRing X).obj)).counit.app (sheafHom X F F)) :=
    NatIso.isIso_app_of_isIso _ _
  exact IsIso.comp_isIso' hmap hcounit

end Stacks.SheafOfModules.OnSpace
