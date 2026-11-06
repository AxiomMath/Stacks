module


public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.Topology.Sheaves.Skyscraper.Modules
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import Std.Tactic.BVDecide.Normalize.Prop
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks.Basic

/-!
# The stalk of the tensor product of `O_X`-modules, and stalk maps (Tags 01CB, 05NE)

This file builds the inverse map `OXModule.presheafTensorStalkInv` of the forward map
`OXModule.presheafTensorStalkFwd` from `FlatModuleSheavesAndStalks.Basic`, and assembles the
presheaf-tensor stalk isomorphism `OXModule.presheafTensor_stalk_iso` and the correctness lemma
`OXModule.stalk_tensor_iso` (Tag 01CB): the stalk of the sheaf tensor product is the tensor
product of the stalks.  It then relates monomorphisms of `O_X`-modules to stalkwise injectivity
(`OXModule.stalkMapAdd`, `OXModule.mono_of_stalkMapAdd_injective`,
`OXModule.stalkMapAdd_injective_of_mono`), and proves the two stalk-local leaf lemmas for
Tag 05NE (`OXModule.tensorBy_stalk_injective_of_flat`,
`OXModule.rTensor_stalkLinearMap_injective_of_tensorBy_stalk_injective`), together with the
unfolding `OXModule.tor1IsZero_iff_stalk`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopCat

universe u

namespace OXModule

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

attribute [local instance] sectionModule sectionPresheafModule stalkModule

/-! ### Helpers for the inverse map `Ψ` (informal proof §2). -/

/-- The germ map of the presheaf tensor `P = M.val ⊗ N.val` at `x` over an open
`W ∋ x`, as an `AddMonoidHom` `P(W) →+ P_x`. -/
noncomputable def ptsInv_germP (M N : OXModule X) (x : X.carrier)
    (W : TopologicalSpace.Opens X.carrier) (hxW : x ∈ W) :
    ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        N).presheaf.obj (Opposite.op W)
      →+ presheafTensorStalkCarrier M N x :=
  ConcreteCategory.hom (TopCat.Presheaf.germ
    ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        N).presheaf W x hxW)

/-- The inner cocone leg `N(V) →+ P_x` for fixed `U, m`:
`n ↦ germ_{U⊓V}^P (m|_{U⊓V} ⊗ n|_{U⊓V})`. -/
noncomputable def ptsInv_legV (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : M.val.obj (Opposite.op U))
    (V : TopologicalSpace.Opens X.carrier) (hxV : x ∈ V) :
    N.val.obj (Opposite.op V) →+ presheafTensorStalkCarrier M N x :=
  (ptsInv_germP M N x (U ⊓ V) ⟨hxU, hxV⟩).comp
    (((TensorProduct.mk (X.presheaf.obj (Opposite.op (U ⊓ V)))
        (M.val.obj (Opposite.op (U ⊓ V))) (N.val.obj (Opposite.op (U ⊓ V)))
        ((ConcreteCategory.hom (M.val.presheaf.map (CategoryTheory.homOfLE inf_le_left).op))
            m)).toAddMonoidHom).comp
      (ConcreteCategory.hom (N.val.presheaf.map (CategoryTheory.homOfLE inf_le_right).op)))

/-- Defining equation for `ptsInv_legV`: it sends `n` to
`germ_{U⊓V}^P (m|_{U⊓V} ⊗ n|_{U⊓V})`. -/
theorem ptsInv_legV_apply (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : M.val.obj (Opposite.op U))
    (V : TopologicalSpace.Opens X.carrier) (hxV : x ∈ V) (n : N.val.obj (Opposite.op V)) :
    ptsInv_legV M N x U hxU m V hxV n
      = ptsInv_germP M N x (U ⊓ V) ⟨hxU, hxV⟩
          (((ConcreteCategory.hom (M.val.presheaf.map (CategoryTheory.homOfLE inf_le_left).op)) m)
            ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ V))]
            ((ConcreteCategory.hom (N.val.presheaf.map (CategoryTheory.homOfLE inf_le_right).op))
                n)) :=
  rfl

/-- Inner cocone compatibility: for `V' ≤ V`, restricting `n` along `N(V) → N(V')`
does not change the leg value. -/
theorem ptsInv_legV_compat (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : M.val.obj (Opposite.op U))
    (V V' : TopologicalSpace.Opens X.carrier) (hxV : x ∈ V) (hxV' : x ∈ V') (hV'V : V' ≤ V)
    (n : N.val.obj (Opposite.op V)) :
    ptsInv_legV M N x U hxU m V' hxV'
        ((ConcreteCategory.hom (N.val.presheaf.map (CategoryTheory.homOfLE hV'V).op)) n)
      = ptsInv_legV M N x U hxU m V hxV n := by
  have hle : U ⊓ V' ≤ U ⊓ V := inf_le_inf_left U hV'V
  let leftSection : M.val.obj (Opposite.op (U ⊓ V)) :=
    (ConcreteCategory.hom (M.val.presheaf.map (homOfLE inf_le_left).op)) m
  let rightSection : N.val.obj (Opposite.op (U ⊓ V)) :=
    (ConcreteCategory.hom (N.val.presheaf.map (homOfLE inf_le_right).op)) n
  have leftRestriction :
      (ConcreteCategory.hom (M.val.presheaf.map
        (homOfLE (inf_le_left : U ⊓ V' ≤ U)).op)) m =
      (ConcreteCategory.hom (M.val.presheaf.map (homOfLE hle).op)) leftSection :=
    ConcreteCategory.congr_hom (M.val.presheaf.map_comp
      (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (homOfLE hle).op) m
  have rightRestriction :
      (ConcreteCategory.hom (N.val.presheaf.map
        (homOfLE (inf_le_right : U ⊓ V' ≤ V')).op))
          ((ConcreteCategory.hom (N.val.presheaf.map (homOfLE hV'V).op)) n) =
      (ConcreteCategory.hom (N.val.presheaf.map (homOfLE hle).op)) rightSection :=
    (ConcreteCategory.congr_hom (N.val.presheaf.map_comp (homOfLE hV'V).op
      (homOfLE (inf_le_right : U ⊓ V' ≤ V')).op) n).symm.trans
        (ConcreteCategory.congr_hom (N.val.presheaf.map_comp
          (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (homOfLE hle).op) n)
  have tensorRestriction :=
    (congrArg₂ (fun (leftValue : M.val.obj (Opposite.op (U ⊓ V')))
        (rightValue : N.val.obj (Opposite.op (U ⊓ V'))) =>
      leftValue ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ V'))] rightValue)
      leftRestriction rightRestriction).trans
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul (R := X.presheaf)
          (M₁ := M.val) (M₂ := N.val) (homOfLE hle).op leftSection rightSection).symm
  exact (ptsInv_legV_apply M N x U hxU m V' hxV'
    ((ConcreteCategory.hom (N.val.presheaf.map (homOfLE hV'V).op)) n)).trans
      ((congrArg (ptsInv_germP M N x (U ⊓ V') ⟨hxU, hxV'⟩) tensorRestriction).trans
        ((TopCat.Presheaf.germ_res_apply (M.val ⊗ N.val).presheaf (homOfLE hle) x
          ⟨hxU, hxV'⟩ (leftSection ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ V))] rightSection)).trans
            (ptsInv_legV_apply M N x U hxU m V hxV n).symm))

/-- The inner cocone (for fixed `U, m`) over the `OpenNhds x` diagram for `N`,
with point `P_x` and legs `ptsInv_legV`. -/
noncomputable def ptsInv_innerCocone (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : M.val.obj (Opposite.op U)) :
    CategoryTheory.Limits.Cocone
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ N.val.presheaf) where
  pt := AddCommGrpCat.of (presheafTensorStalkCarrier M N x)
  ι :=
    { app := fun V => AddCommGrpCat.ofHom (ptsInv_legV M N x U hxU m V.unop.1 V.unop.2)
      naturality := by
        intro V V' i
        ext n
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
          Functor.const_obj_map]
        exact ptsInv_legV_compat M N x U hxU m V.unop.1 V'.unop.1 V.unop.2 V'.unop.2
          (CategoryTheory.leOfHom i.unop) n }

/-- The inner descent `γ_{U,m} : N_x →+ P_x`, for fixed `U` and `m ∈ M(U)`. -/
noncomputable def ptsInv_gamma (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : M.val.obj (Opposite.op U)) :
    ↑(N.stalk x) →+ presheafTensorStalkCarrier M N x :=
  AddCommGrpCat.Hom.hom (CategoryTheory.Limits.colimit.desc _ (ptsInv_innerCocone M N x U hxU m))

/-- Germ action of `γ_{U,m}`: `γ_{U,m}(germ_V n) = germ_{U⊓V}^P(m|_{U⊓V} ⊗ n|_{U⊓V})`. -/
theorem ptsInv_gamma_germ (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : M.val.obj (Opposite.op U))
    (V : TopologicalSpace.Opens X.carrier) (hxV : x ∈ V) (n : N.val.obj (Opposite.op V)) :
    ptsInv_gamma M N x U hxU m
        ((ConcreteCategory.hom (TopCat.Presheaf.germ N.val.presheaf V x hxV)) n)
      = ptsInv_legV M N x U hxU m V hxV n := by
  have key := CategoryTheory.Limits.colimit.ι_desc (ptsInv_innerCocone M N x U hxU m)
    (Opposite.op ⟨V, hxV⟩)
  have happ := ConcreteCategory.congr_hom key n
  exact happ

/-- The outer cocone leg `M(U) →+ (N_x →+ P_x)`, `m ↦ γ_{U,m}`.  Additivity in
`m` reduces, on germs of `N_x`, to biadditivity of the simple tensor. -/
noncomputable def ptsInv_legU (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) :
    M.val.obj (Opposite.op U) →+ (↑(N.stalk x) →+ presheafTensorStalkCarrier M N x) where
  toFun m := ptsInv_gamma M N x U hxU m
  map_zero' := by
    refine AddMonoidHom.ext fun germValue => ?_
    obtain ⟨V, hxV, value, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) N.val.presheaf germValue
    let rightSection : N.val.obj (Opposite.op (U ⊓ V)) :=
      N.val.restrictₛₗ (homOfLE inf_le_right).op value
    let leftLeg : M.val.obj (Opposite.op U) →+ presheafTensorStalkCarrier M N x :=
      (ptsInv_germP M N x (U ⊓ V) ⟨hxU, hxV⟩).comp
        (((TensorProduct.mk (X.presheaf.obj (Opposite.op (U ⊓ V)))
          (M.val.obj (Opposite.op (U ⊓ V))) (N.val.obj (Opposite.op (U ⊓ V)))).flip
            rightSection).toAddMonoidHom.comp
          (M.val.restrictₛₗ (homOfLE inf_le_left).op).toAddMonoidHom)
    exact (ptsInv_gamma_germ M N x U hxU 0 V hxV value).trans (map_zero leftLeg)
  map_add' left right := by
    refine AddMonoidHom.ext fun germValue => ?_
    obtain ⟨V, hxV, value, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) N.val.presheaf germValue
    let rightSection : N.val.obj (Opposite.op (U ⊓ V)) :=
      N.val.restrictₛₗ (homOfLE inf_le_right).op value
    let leftLeg : M.val.obj (Opposite.op U) →+ presheafTensorStalkCarrier M N x :=
      (ptsInv_germP M N x (U ⊓ V) ⟨hxU, hxV⟩).comp
        (((TensorProduct.mk (X.presheaf.obj (Opposite.op (U ⊓ V)))
          (M.val.obj (Opposite.op (U ⊓ V))) (N.val.obj (Opposite.op (U ⊓ V)))).flip
            rightSection).toAddMonoidHom.comp
          (M.val.restrictₛₗ (homOfLE inf_le_left).op).toAddMonoidHom)
    exact (ptsInv_gamma_germ M N x U hxU (left + right) V hxV value).trans
      ((map_add leftLeg left right).trans
        (congrArg₂ (· + ·) (ptsInv_gamma_germ M N x U hxU left V hxV value).symm
          (ptsInv_gamma_germ M N x U hxU right V hxV value).symm))

/-- Outer cocone compatibility: for `U' ≤ U`, restricting `m` along `M(U) → M(U')`
does not change the outer leg `γ`. -/
theorem ptsInv_legU_compat (M N : OXModule X) (x : X.carrier)
    (U U' : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (hxU' : x ∈ U') (hU'U : U' ≤ U)
    (m : M.val.obj (Opposite.op U)) :
    ptsInv_legU M N x U' hxU'
        ((ConcreteCategory.hom (M.val.presheaf.map (CategoryTheory.homOfLE hU'U).op)) m)
      = ptsInv_legU M N x U hxU m := by
  refine AddMonoidHom.ext fun germValue => ?_
  obtain ⟨V, hxV, value, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) N.val.presheaf germValue
  have hle : U' ⊓ V ≤ U ⊓ V := inf_le_inf_right V hU'U
  let restrictedLeft : M.val.obj (Opposite.op U') := M.val.restrictₛₗ (homOfLE hU'U).op m
  let leftSection : M.val.obj (Opposite.op (U ⊓ V)) :=
    M.val.restrictₛₗ (homOfLE inf_le_left).op m
  let rightSection : N.val.obj (Opposite.op (U ⊓ V)) :=
    N.val.restrictₛₗ (homOfLE inf_le_right).op value
  have leftRestriction :
      (ConcreteCategory.hom (M.val.presheaf.map
        (homOfLE (inf_le_left : U' ⊓ V ≤ U')).op)) restrictedLeft =
      (ConcreteCategory.hom (M.val.presheaf.map (homOfLE hle).op)) leftSection :=
    (ConcreteCategory.congr_hom (M.val.presheaf.map_comp (homOfLE hU'U).op
      (homOfLE (inf_le_left : U' ⊓ V ≤ U')).op) m).symm.trans
        (ConcreteCategory.congr_hom (M.val.presheaf.map_comp
          (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (homOfLE hle).op) m)
  have rightRestriction :
      (ConcreteCategory.hom (N.val.presheaf.map
        (homOfLE (inf_le_right : U' ⊓ V ≤ V)).op)) value =
      (ConcreteCategory.hom (N.val.presheaf.map (homOfLE hle).op)) rightSection :=
    ConcreteCategory.congr_hom (N.val.presheaf.map_comp
      (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (homOfLE hle).op) value
  have tensorRestriction :=
    (congrArg₂ (fun (leftValue : M.val.obj (Opposite.op (U' ⊓ V)))
        (rightValue : N.val.obj (Opposite.op (U' ⊓ V))) =>
      leftValue ⊗ₜ[X.presheaf.obj (Opposite.op (U' ⊓ V))] rightValue)
      leftRestriction rightRestriction).trans
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul (R := X.presheaf)
          (M₁ := M.val) (M₂ := N.val) (homOfLE hle).op leftSection rightSection).symm
  exact (ptsInv_gamma_germ M N x U' hxU' restrictedLeft V hxV value).trans
    ((ptsInv_legV_apply M N x U' hxU' restrictedLeft V hxV value).trans
      ((congrArg (ptsInv_germP M N x (U' ⊓ V) ⟨hxU', hxV⟩) tensorRestriction).trans
        ((TopCat.Presheaf.germ_res_apply (M.val ⊗ N.val).presheaf (homOfLE hle) x
          ⟨hxU', hxV⟩ (leftSection ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ V))] rightSection)).trans
            ((ptsInv_legV_apply M N x U hxU m V hxV value).symm.trans
              (ptsInv_gamma_germ M N x U hxU m V hxV value).symm))))

/-- The outer cocone over the `OpenNhds x` diagram for `M`, with point
`N_x →+ P_x` and legs `ptsInv_legU`. -/
noncomputable def ptsInv_outerCocone (M N : OXModule X) (x : X.carrier) :
    CategoryTheory.Limits.Cocone
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ M.val.presheaf) where
  pt := AddCommGrpCat.of (↑(N.stalk x) →+ presheafTensorStalkCarrier M N x)
  ι :=
    { app := fun U => AddCommGrpCat.ofHom (ptsInv_legU M N x U.unop.1 U.unop.2)
      naturality := by
        intro U U' i
        ext m
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
          Functor.const_obj_map]
        exact ptsInv_legU_compat M N x U.unop.1 U'.unop.1 U.unop.2 U'.unop.2
          (CategoryTheory.leOfHom i.unop) m }

/-- The bilinear-type map `β : M_x →+ (N_x →+ P_x)`, by descending the outer
cocone over `M`. -/
noncomputable def ptsInv_beta (M N : OXModule X) (x : X.carrier) :
    ↑(M.stalk x) →+ (↑(N.stalk x) →+ presheafTensorStalkCarrier M N x) :=
  AddCommGrpCat.Hom.hom (CategoryTheory.Limits.colimit.desc _ (ptsInv_outerCocone M N x))

/-- Germ action of `β` in the first variable: `β(germ_U m) = γ_{U,m}`. -/
theorem ptsInv_beta_germ (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : M.val.obj (Opposite.op U)) :
    ptsInv_beta M N x ((ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf U x hxU)) m)
      = ptsInv_legU M N x U hxU m := by
  have key := CategoryTheory.Limits.colimit.ι_desc (ptsInv_outerCocone M N x)
    (Opposite.op ⟨U, hxU⟩)
  have happ := ConcreteCategory.congr_hom key m
  exact happ

/-- Full germ action of `β`: `β(germ_U m)(germ_V n) = germ_{U⊓V}^P(m|_{U⊓V} ⊗ n|_{U⊓V})`. -/
theorem ptsInv_beta_germ_germ (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : M.val.obj (Opposite.op U))
    (V : TopologicalSpace.Opens X.carrier) (hxV : x ∈ V) (n : N.val.obj (Opposite.op V)) :
    ptsInv_beta M N x ((ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf U x hxU)) m)
        ((ConcreteCategory.hom (TopCat.Presheaf.germ N.val.presheaf V x hxV)) n)
      = ptsInv_legV M N x U hxU m V hxV n := by
  exact (congrArg
    (fun morphism : N.stalk x →+ presheafTensorStalkCarrier M N x =>
      morphism ((ConcreteCategory.hom (TopCat.Presheaf.germ N.val.presheaf V x hxV)) n))
    (ptsInv_beta_germ M N x U hxU m)).trans (ptsInv_gamma_germ M N x U hxU m V hxV n)

/-- At a common open set, the inverse pairing sends sections to the germ of their tensor. -/
theorem ptsInv_legV_self (leftModule rightModule : OXModule X) (point : X.carrier)
    (openSet : TopologicalSpace.Opens X.carrier) (containsPoint : point ∈ openSet)
    (left : leftModule.val.obj (Opposite.op openSet))
    (right : rightModule.val.obj (Opposite.op openSet)) :
    ptsInv_legV leftModule rightModule point openSet containsPoint left openSet containsPoint
        right =
      ptsInv_germP leftModule rightModule point openSet containsPoint
        (left ⊗ₜ[X.presheaf.obj (Opposite.op openSet)] right) :=
  (ptsInv_legV_apply leftModule rightModule point openSet containsPoint left openSet
      containsPoint right).trans
    ((congrArg
      (ptsInv_germP leftModule rightModule point (openSet ⊓ openSet) ⟨containsPoint, containsPoint⟩)
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul (R := X.presheaf)
        (M₁ := leftModule.val) (M₂ := rightModule.val)
        (homOfLE (inf_le_left : openSet ⊓ openSet ≤ openSet)).op
          left right).symm).trans
      (TopCat.Presheaf.germ_res_apply (leftModule.val ⊗ rightModule.val).presheaf
        (homOfLE (inf_le_left : openSet ⊓ openSet ≤ openSet)) point ⟨containsPoint, containsPoint⟩
          (left ⊗ₜ[X.presheaf.obj (Opposite.op openSet)] right)))

/-- Scalar action of `legV` in the first variable at a common open `A` (`U=V=A`):
`legV(A, s•m, A, n) = (germ_A s) • legV(A, m, A, n)`. -/
theorem ptsInv_legV_smul_left (M N : OXModule X) (x : X.carrier)
    (A : TopologicalSpace.Opens X.carrier) (hxA : x ∈ A) (s : X.presheaf.obj (Opposite.op A))
    (m : M.val.obj (Opposite.op A)) (n : N.val.obj (Opposite.op A)) :
    ptsInv_legV M N x A hxA (s • m) A hxA n
      = (ConcreteCategory.hom (X.presheaf.germ A x hxA)) s • ptsInv_legV M N x A hxA m A hxA n := by
  exact (ptsInv_legV_self M N x A hxA (s • m) n).trans
    ((congrArg (ptsInv_germP M N x A hxA)
      (TensorProduct.smul_tmul' (R := ↑(X.presheaf.obj (Opposite.op A))) s m n).symm).trans
        ((PresheafOfModules.germ_smul (M.val ⊗ N.val) x A hxA s
          (m ⊗ₜ[X.presheaf.obj (Opposite.op A)] n)).trans
          (congrArg (fun value : presheafTensorStalkCarrier M N x =>
            X.presheaf.germ A x hxA s • value) (ptsInv_legV_self M N x A hxA m n).symm)))

/-- Scalar action of `legV` in the second variable at a common open `A`:
`legV(A, m, A, s•n) = (germ_A s) • legV(A, m, A, n)`. -/
theorem ptsInv_legV_smul_right (M N : OXModule X) (x : X.carrier)
    (A : TopologicalSpace.Opens X.carrier) (hxA : x ∈ A) (s : X.presheaf.obj (Opposite.op A))
    (m : M.val.obj (Opposite.op A)) (n : N.val.obj (Opposite.op A)) :
    ptsInv_legV M N x A hxA m A hxA (s • n)
      = (ConcreteCategory.hom (X.presheaf.germ A x hxA)) s • ptsInv_legV M N x A hxA m A hxA n := by
  exact (ptsInv_legV_self M N x A hxA m (s • n)).trans
    ((congrArg (ptsInv_germP M N x A hxA)
      (TensorProduct.tmul_smul (R := ↑(X.presheaf.obj (Opposite.op A))) s m n)).trans
        ((PresheafOfModules.germ_smul (M.val ⊗ N.val) x A hxA s
          (m ⊗ₜ[X.presheaf.obj (Opposite.op A)] n)).trans
          (congrArg (fun value : presheafTensorStalkCarrier M N x =>
            X.presheaf.germ A x hxA s • value) (ptsInv_legV_self M N x A hxA m n).symm)))

/-- A scalar germ and germs of `M` and `N` at `x` are all germs over one common open. -/
private theorem exists_common_germ (M N : OXModule X) (x : X.carrier)
    (r : X.presheaf.stalk x) (μ : ↑(M.stalk x)) (ν : ↑(N.stalk x)) :
    ∃ (A : TopologicalSpace.Opens X.carrier) (hxA : x ∈ A) (s : X.presheaf.obj (Opposite.op A))
      (m : M.val.obj (Opposite.op A)) (n : N.val.obj (Opposite.op A)),
      r = (ConcreteCategory.hom (X.presheaf.germ A x hxA)) s ∧
      μ = (ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf A x hxA)) m ∧
      ν = (ConcreteCategory.hom (TopCat.Presheaf.germ N.val.presheaf A x hxA)) n := by
  obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) X.presheaf r
  obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) M.val.presheaf μ
  obtain ⟨V, hxV, n, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) N.val.presheaf ν
  refine ⟨U ⊓ V ⊓ W, ⟨⟨hxU, hxV⟩, hxW⟩,
    (ConcreteCategory.hom (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ⊓ W ≤ W)).op)) s,
    (ConcreteCategory.hom (M.val.presheaf.map
      (homOfLE (le_trans inf_le_left inf_le_left : U ⊓ V ⊓ W ≤ U)).op)) m,
    (ConcreteCategory.hom (N.val.presheaf.map
      (homOfLE (le_trans inf_le_left inf_le_right : U ⊓ V ⊓ W ≤ V)).op)) n,
    ?_, ?_, ?_⟩ <;> exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

/-- `R`-balancing of `β`: `β(r•μ)(ν) = β(μ)(r•ν)` for `r ∈ O_{X,x}`.  Reduce all
germs to a common open `A` and use the fixed-ring `legV` smul lemmas. -/
theorem ptsInv_beta_balanced (M N : OXModule X) (x : X.carrier)
    (r : X.presheaf.stalk x) (μ : ↑(M.stalk x)) (ν : ↑(N.stalk x)) :
    ptsInv_beta M N x (r • μ) ν = ptsInv_beta M N x μ (r • ν) := by
  obtain ⟨A, hxA, s', m', n', rfl, rfl, rfl⟩ := exists_common_germ M N x r μ ν
  have leftUnit := congrArg
    (fun element : M.stalk x => ptsInv_beta M N x element (ptsFwd_germM N x A hxA n'))
    (PresheafOfModules.germ_smul M.val x A hxA s' m').symm
  have rightUnit := congrArg
    (fun element : N.stalk x => ptsInv_beta M N x (ptsFwd_germM M x A hxA m') element)
    (PresheafOfModules.germ_smul N.val x A hxA s' n')
  exact leftUnit.trans
    ((ptsInv_beta_germ_germ M N x A hxA (s' • m') A hxA n').trans
      ((ptsInv_legV_smul_left M N x A hxA s' m' n').trans
        ((ptsInv_legV_smul_right M N x A hxA s' m' n').symm.trans
          ((ptsInv_beta_germ_germ M N x A hxA m' A hxA (s' • n')).symm.trans rightUnit))))

/-- `R`-linearity datum for `β`: `β(r•μ)(ν) = r • β(μ)(ν)`. -/
theorem ptsInv_beta_smul (M N : OXModule X) (x : X.carrier)
    (r : X.presheaf.stalk x) (μ : ↑(M.stalk x)) (ν : ↑(N.stalk x)) :
    ptsInv_beta M N x (r • μ) ν = r • ptsInv_beta M N x μ ν := by
  obtain ⟨A, hxA, s', m', n', rfl, rfl, rfl⟩ := exists_common_germ M N x r μ ν
  have leftUnit := congrArg
    (fun element : M.stalk x => ptsInv_beta M N x element (ptsFwd_germM N x A hxA n'))
    (PresheafOfModules.germ_smul M.val x A hxA s' m').symm
  exact leftUnit.trans
    ((ptsInv_beta_germ_germ M N x A hxA (s' • m') A hxA n').trans
      ((ptsInv_legV_smul_left M N x A hxA s' m' n').trans
        (congrArg (fun element : presheafTensorStalkCarrier M N x =>
          X.presheaf.germ A x hxA s' • element)
          (ptsInv_beta_germ_germ M N x A hxA m' A hxA n').symm)))

/-- **Leaf (2b) — inverse map `Ψ`.**  The `O_{X,x}`-linear map
`M_x ⊗_{O_{X,x}} N_x → colim_{U∋x}(M(U) ⊗_{O(U)} N(U))` defined on a simple
tensor of germs by `germ_U(m) ⊗ germ_V(n) ↦ germ_{U⊓V}(m|_{U⊓V} ⊗ n|_{U⊓V})`.

Construction (informal proof §2): `TensorProduct.lift` of the biadditive
`O_{X,x}`-balanced map `β(germ_U m, germ_V n) = germ_{U⊓V}(m|_{U⊓V} ⊗ n|_{U⊓V})`;
well-definedness and balancing reduce to a common refinement via the filtered
colimit identification `TopCat.Presheaf.germ_eq` and `germ_smul`. -/
noncomputable def presheafTensorStalkInv (M N : OXModule X) (x : X.carrier) :
    (M.stalk x ⊗ N.stalk x : ModuleCat.{u} (X.presheaf.stalk x)) →ₗ[X.presheaf.stalk x]
      presheafTensorStalkCarrier M N x where
  toFun := TensorProduct.liftAddHom (ptsInv_beta M N x) (ptsInv_beta_balanced M N x)
  map_add' a b := by rw [map_add]
  map_smul' := by
    intro r z
    simp only [RingHom.id_apply]
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
    | tmul μ ν =>
        rw [TensorProduct.smul_tmul']
        change TensorProduct.liftAddHom (ptsInv_beta M N x) (ptsInv_beta_balanced M N x) ((r • μ)
            ⊗ₜ ν)
          = r • TensorProduct.liftAddHom (ptsInv_beta M N x) (ptsInv_beta_balanced M N x) (μ ⊗ₜ ν)
        rw [TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
        exact ptsInv_beta_smul M N x r μ ν

/-- **Defining equation for the inverse map `Ψ` on simple tensors of germs.**
`Ψ(germ_U m ⊗ germ_V n) = germ^P_{U⊓V}(m|_{U⊓V} ⊗ n|_{U⊓V})`, where the right-hand
side is the stalk germ of the presheaf-tensor `P = M.val ⊗ N.val`.  This is the
clean characterization required by the round-trip leaves. -/
theorem presheafTensorStalkInv_tmul_germ (M N : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : M.val.obj (Opposite.op U))
    (V : TopologicalSpace.Opens X.carrier) (hxV : x ∈ V) (n : N.val.obj (Opposite.op V)) :
    presheafTensorStalkInv M N x
        ((ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf U x hxU)) m
          ⊗ₜ[X.presheaf.stalk x]
          (ConcreteCategory.hom (TopCat.Presheaf.germ N.val.presheaf V x hxV)) n)
      = (ConcreteCategory.hom (TopCat.Presheaf.germ
            ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                X)).obj N).presheaf
            (U ⊓ V) x ⟨hxU, hxV⟩))
          (((ConcreteCategory.hom (M.val.presheaf.map (CategoryTheory.homOfLE inf_le_left).op)) m)
            ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ V))]
            ((ConcreteCategory.hom (N.val.presheaf.map (CategoryTheory.homOfLE inf_le_right).op))
              n)) := by
  exact (ptsInv_beta_germ_germ M N x U hxU m V hxV n).trans
    (ptsInv_legV_apply M N x U hxU m V hxV n)

/-- **Leaf (2c) — `Φ ∘ Ψ = id`** on `M_x ⊗_{O_{X,x}} N_x`.  Check on simple
tensors `germ_U m ⊗ germ_V n` (informal proof §3.1): both maps are linear, and
`Φ(Ψ(germ_U m ⊗ germ_V n)) = germ_{U⊓V}(m|_{U⊓V}) ⊗ germ_{U⊓V}(n|_{U⊓V})
= germ_U m ⊗ germ_V n` by the cocone identity `germ_W (a|_W) = germ_U a`
(`TopCat.Presheaf.germ_res`). -/
theorem presheafTensorStalk_fwd_inv (M N : OXModule X) (x : X.carrier) :
    (presheafTensorStalkFwd M N x).comp (presheafTensorStalkInv M N x) = LinearMap.id := by
  refine TensorProduct.ext' (R := ↑(X.presheaf.stalk x)) (M := M.stalk x)
    (N := N.stalk x) fun left right => ?_
  obtain ⟨U, hxU, leftValue, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) M.val.presheaf left
  obtain ⟨V, hxV, rightValue, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) N.val.presheaf right
  let leftSection : M.val.obj (Opposite.op (U ⊓ V)) :=
    M.val.restrictₛₗ (homOfLE inf_le_left).op leftValue
  let rightSection : N.val.obj (Opposite.op (U ⊓ V)) :=
    N.val.restrictₛₗ (homOfLE inf_le_right).op rightValue
  exact (congrArg (presheafTensorStalkFwd M N x)
    (presheafTensorStalkInv_tmul_germ M N x U hxU leftValue V hxV rightValue)).trans
      ((ptsFwd_fwdAdd_germ M N x (U ⊓ V) ⟨hxU, hxV⟩
        (leftSection ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ V))] rightSection)).trans
          (congrArg₂ (fun (leftGerm : M.stalk x) (rightGerm : N.stalk x) =>
            leftGerm ⊗ₜ[X.presheaf.stalk x] rightGerm)
            (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE inf_le_left) x
              ⟨hxU, hxV⟩ leftValue)
            (TopCat.Presheaf.germ_res_apply N.val.presheaf (homOfLE inf_le_right) x
              ⟨hxU, hxV⟩ rightValue)))

/-- **Leaf (2d) — `Ψ ∘ Φ = id`** on `colim_{U∋x}(M(U) ⊗_{O(U)} N(U))`.  Every
element is a germ `germ_U t` (`germ_exist`); reduce to a simple tensor `t = m ⊗ n`
(`TensorProduct.span_tmul_eq_top`); then
`Ψ(Φ(germ_U(m ⊗ n))) = Ψ(germ_U m ⊗ germ_U n) = germ_U(m|_U ⊗ n|_U) = germ_U(m ⊗ n)`
(informal proof §3.2; `W = U` since both germs share `U`). -/
theorem presheafTensorStalk_inv_fwd (M N : OXModule X) (x : X.carrier) :
    (presheafTensorStalkInv M N x).comp (presheafTensorStalkFwd M N x) = LinearMap.id := by
  refine LinearMap.ext fun element => ?_
  obtain ⟨U, hxU, value, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x)
    (M.val ⊗ N.val).presheaf element
  let germMap : TensorProduct (X.presheaf.obj (Opposite.op U))
      (M.val.obj (Opposite.op U)) (N.val.obj (Opposite.op U)) →+
        presheafTensorStalkCarrier M N x := ptsInv_germP M N x U hxU
  let composite := (presheafTensorStalkInv M N x).toAddMonoidHom.comp
    ((presheafTensorStalkFwd M N x).toAddMonoidHom.comp germMap)
  show composite value = germMap value
  induction value using TensorProduct.induction_on with
  | zero => exact (map_zero composite).trans (map_zero germMap).symm
  | add left right left_eq right_eq =>
      exact (map_add composite left right).trans
        ((congrArg₂ (· + ·) left_eq right_eq).trans (map_add germMap left right).symm)
  | tmul left right =>
      exact (congrArg (presheafTensorStalkInv M N x)
        (ptsFwd_fwdAdd_germ M N x U hxU (left ⊗ₜ[X.presheaf.obj (Opposite.op U)] right))).trans
          ((ptsInv_beta_germ_germ M N x U hxU left U hxU right).trans
            (ptsInv_legV_self M N x U hxU left right))

/-- **Assembly (proof-complete).**  The presheaf-tensor stalk iso, from the forward
and inverse maps and the two round-trip identities, as an `O_{X,x}`-`ModuleCat`
isomorphism. -/
@[ega "0 4.1.5" "partial"]
noncomputable def presheafTensor_stalk_iso (M N : OXModule X) (x : X.carrier) :
    ModuleCat.of (X.presheaf.stalk x) (presheafTensorStalkCarrier M N x) ≅
      (M.stalk x ⊗ N.stalk x : ModuleCat.{u} (X.presheaf.stalk x)) :=
  (LinearEquiv.ofLinearMap (presheafTensorStalkFwd M N x) (presheafTensorStalkInv M N x)
    (presheafTensorStalk_fwd_inv M N x) (presheafTensorStalk_inv_fwd M N x)).toModuleIso

/-- **Correctness for Definition 1 (Tag 01CB).**
The formation of the sheaf tensor product commutes with stalks: the stalk of
`M ⊗_{O_X} N` at `x` is (canonically isomorphic to) the tensor product of the
stalks `M_x ⊗_{O_{X,x}} N_x`.  This is exactly the stalk-compatibility asserted
in Tag 01CB and justifies the stalk-wise treatment of `Tor` below.  The
existence of the canonical isomorphism is recorded as `Nonempty (... ≅ ...)`
(a proposition), which is the mathematical content. -/
@[ega "0 4.1.5" "partial",
  ega "0 4.3.3" "partial",
  ega "0 6.7.2" "special case",
  ega "I 9.1.12" "special case",
  sga "4 IV 13.5" "Ringed-space case",
  sga "4 V 1.6.2" "special case"]
theorem stalk_tensor_iso (M N : OXModule X) (x : X.carrier) :
    Nonempty ((tensor M N).stalk x ≅ M.stalk x ⊗ N.stalk x) := by
  -- Part (1) [CLOSED]: sheafification preserves stalks, via the generic
  -- `sheafify_stalk_iso`.  This reduces the goal to the presheaf-level statement.
  -- Part (2) [via `presheafTensor_stalk_iso`]: presheaf-tensor stalk = tensor of stalks.
  exact ⟨sheafify_stalk_iso x ((SheafOfModules.forget _).obj M ⊗ (SheafOfModules.forget _).obj N)
    ≪≫ presheafTensor_stalk_iso M N x⟩

/-! ### The stalk map of a morphism, and the mono ↔ stalkwise-injective bridge

For a morphism `f : M ⟶ N` of `O_X`-modules, `stalkMapAdd M N f x` is the induced
map on the underlying `AddCommGrp`-valued stalks at `x` (it is the genuine
`O_{X,x}`-linear stalk map `M_x ⟶ N_x`, here recorded at the `AddCommGrp` level).
A morphism of sheaves of modules is a monomorphism **iff** it is injective on every
stalk; this is Stacks' standard "monomorphisms are detected on stalks" fact, and is
proven below with no open goals from Mathlib's
`TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective` together with the
faithfulness of the forgetful functors `SheafOfModules.forget` and
`PresheafOfModules.toPresheaf`. -/

/-- The induced map on `AddCommGrp`-valued stalks of a morphism of `O_X`-modules. -/
@[ega "0 4.4.3" "partial"]
noncomputable def stalkMapAdd (M N : OXModule X) (f : M ⟶ N) (x : X.carrier) :
    TopCat.Presheaf.stalk M.val.presheaf x ⟶ TopCat.Presheaf.stalk N.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor _ x).map ((PresheafOfModules.toPresheaf _).map f.val)

/-- If every stalk map of `f` is injective, then `f` is a monomorphism.  (Stalkwise
injectivity ⇒ componentwise injectivity ⇒ componentwise mono ⇒ mono of the underlying
`AddCommGrp` presheaf morphism, then reflected back along the faithful composite
`forget ⋙ toPresheaf`.) -/
theorem mono_of_stalkMapAdd_injective (M N : OXModule X) (f : M ⟶ N)
    (h : ∀ x, Function.Injective (stalkMapAdd M N f x)) : Mono f := by
  set g : M.val.presheaf ⟶ N.val.presheaf := (PresheafOfModules.toPresheaf _).map f.val with hg
  have hcomp : ∀ U, Function.Injective (ConcreteCategory.hom (g.app (Opposite.op U))) := fun U =>
    (TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective
      (F := (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X.carrier))
      (G := N.val.presheaf) g).1 (fun x => h x) U
  have : Mono g := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    obtain ⟨U⟩ := U
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback (g.app (Opposite.op U))).2
      (hcomp U)
  have : (SheafOfModules.forget (ringSheaf X) ⋙ PresheafOfModules.toPresheaf _ :
      type_of% M ⥤ _).Faithful :=
    CategoryTheory.Functor.Faithful.comp _ _
  have hmono : Mono ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map f) := by
    show Mono g; infer_instance
  exact Functor.mono_of_mono_map (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _) hmono

/-- The underlying `AddCommGrp` presheaf morphism of a monomorphism of `O_X`-modules
is again a monomorphism (the forgetful functors preserve monos). -/
theorem mono_val_of_mono (M N : OXModule X) (f : M ⟶ N) [Mono f] :
    Mono ((PresheafOfModules.toPresheaf _).map f.val) := by
  have hf : Mono ((SheafOfModules.forget (ringSheaf X)).map f) := Functor.map_mono _ f
  exact Functor.map_mono (PresheafOfModules.toPresheaf _) ((SheafOfModules.forget _).map f)

/-- If the underlying presheaf morphism of `f` is a monomorphism, then every stalk map
of `f` is injective (componentwise mono ⇒ componentwise injective ⇒ stalkwise
injective via the Mathlib stalk iff). -/
theorem inj_of_mono_val (M N : OXModule X) (f : M ⟶ N)
    (hmg : Mono ((PresheafOfModules.toPresheaf _).map f.val)) (x : X.carrier) :
    Function.Injective (stalkMapAdd M N f x) := by
  have hcomp : ∀ U, Function.Injective (ConcreteCategory.hom
      (((PresheafOfModules.toPresheaf _).map f.val).app (Opposite.op U))) := by
    intro U
    have hmU : Mono (((PresheafOfModules.toPresheaf _).map f.val).app (Opposite.op U)) :=
      (NatTrans.mono_iff_mono_app _).1 hmg (Opposite.op U)
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1 hmU
  exact (TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective
    (F := (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X.carrier))
    (G := N.val.presheaf) ((PresheafOfModules.toPresheaf _).map f.val)).2 hcomp x

/-- If `f` is a monomorphism, then every stalk map of `f` is injective. -/
theorem stalkMapAdd_injective_of_mono (M N : OXModule X) (f : M ⟶ N) [Mono f]
    (x : X.carrier) : Function.Injective (stalkMapAdd M N f x) :=
  inj_of_mono_val M N f (mono_val_of_mono M N f) x

/-! ### The two remaining stalk-local leaf lemmas (Tag 05NE)

With the mono ↔ stalkwise-injective bridge above (`mono_of_stalkMapAdd_injective`,
`stalkMapAdd_injective_of_mono`) the equivalence `Flat ↔ FlatStalkwise` is reduced to
two purely *stalk-local* facts, isolated as the leaf lemmas below.  Both are exactly
the content of Stacks Tag 05NE once monomorphisms have been transferred to stalks; they
rest on the stalk-tensor compatibility `stalk_tensor_iso` (Tag 01CB) being *natural* in
the first variable and on the module-theoretic characterization of flatness
(`Module.Flat.iff_lTensor_preserves_injective_linearMap`), together with the
realization lemma `exists_oxModule_stalk_iso` for the forward direction.

* `tensorBy_stalk_injective_of_flat` (used for `FlatStalkwise ⇒ Flat`): if `f` is
  stalkwise injective and every `F_x` is flat, then `(f ⊗ F)` is stalkwise injective
  — because on the stalk at `x`, `(f ⊗ F)_x` is identified (via `stalk_tensor_iso`,
  naturally in `f`) with `f_x ⊗_{O_{X,x}} F_x`, which is injective by flatness of `F_x`.
* `flat_stalk_of_flat` (used for `Flat ⇒ FlatStalkwise`): if `F` is flat then each
  stalk `F_x` is a flat `O_{X,x}`-module — given an injection `g : N' ↪ N` of
  `O_{X,x}`-modules, realize it (via `exists_oxModule_stalk_iso`) as the stalk of a
  monomorphism of `O_X`-modules, tensor by `F` (a mono by flatness), and read off
  injectivity of `g ⊗ F_x` on the stalk at `x`. -/

/-- Germ action of `stalkMapAdd`: on `germ_U s` it gives `germ_U (f.val.app U s)`. -/
theorem stalkMapAdd_germ (M N : OXModule X) (f : M ⟶ N) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (s : M.val.obj (Opposite.op U)) :
    stalkMapAdd M N f x ((ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf U x hxU)) s)
      = (ConcreteCategory.hom (TopCat.Presheaf.germ N.val.presheaf U x hxU))
          ((ConcreteCategory.hom (((PresheafOfModules.toPresheaf _).map f.val).app (Opposite.op U)))
            s) := by
  rw [stalkMapAdd]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    ((PresheafOfModules.toPresheaf _).map f.val) s

/-- **Sheafify naturality at the stalk (germ form).**  For `g : P ⟶ Q` in
`PresheafOfModules`, the `AddCommGrp` stalk map of `sheafify.map g` intertwines the
forward stalk maps of the sheafification unit. -/
theorem sheafifyStalkFwd_naturality (x : X.carrier)
    {P Q : PresheafOfModules.{u} ((ringSheaf X).obj)} (g : P ⟶ Q)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (s : P.obj (Opposite.op U)) :
    stalkMapAdd (sheafify.obj P) (sheafify.obj Q) (sheafify.map g) x
        (sheafifyStalkFwd x P
          ((ConcreteCategory.hom (TopCat.Presheaf.germ P.presheaf U x hxU)) s))
      = sheafifyStalkFwd x Q
          ((ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map
            ((PresheafOfModules.toPresheaf _).map g)))
            ((ConcreteCategory.hom (TopCat.Presheaf.germ P.presheaf U x hxU)) s)) := by
  exact ConcreteCategory.congr_hom
    ((Functor.whiskerRight
      (PresheafOfModules.sheafificationAdjunction (R := ringSheaf X)
        (𝟙 (ringSheaf X).obj)).unit
      (PresheafOfModules.toPresheaf (ringSheaf X).obj ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).naturality g).symm
    ((TopCat.Presheaf.germ P.presheaf U x hxU).hom s)

section ProbeWhisker
theorem tensorBy_map_app_tmul (F M N : OXModule X) (f : M ⟶ N)
    (U : TopologicalSpace.Opens X.carrier)
    (m : M.val.obj (Opposite.op U)) (n : F.val.obj (Opposite.op U)) :
    (ConcreteCategory.hom
      ((((MonoidalCategory.tensorRight ((SheafOfModules.forget (ringSheaf X)).obj F)).map
        ((SheafOfModules.forget (ringSheaf X)).map f)).app (Opposite.op U)))
        (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n))
      = (ConcreteCategory.hom (f.val.app (Opposite.op U)) m)
        ⊗ₜ[X.presheaf.obj (Opposite.op U)] n := by
  exact ModuleCat.MonoidalCategory.whiskerRight_apply
    (R := ↑(X.presheaf.obj (Opposite.op U))) (f.val.app (Opposite.op U))
    (F.val.obj (Opposite.op U)) m n

end ProbeWhisker

/-- The `O_{X,x}`-linear stalk map of `f : M ⟶ N`, whose underlying function is
`stalkMapAdd M N f x`.  Linearity is `germ_smul` plus component linearity of `f.val`. -/
@[ega "0 4.4.3" "special case"]
noncomputable def stalkLinearMap (M N : OXModule X) (f : M ⟶ N) (x : X.carrier) :
    M.stalk x →ₗ[X.presheaf.stalk x] N.stalk x where
  toFun := stalkMapAdd M N f x
  map_add' left right := map_add (ConcreteCategory.hom (stalkMapAdd M N f x)) left right
  map_smul' scalar element := by
    let linearMap : M.stalk x →ₗ[X.presheaf.stalk x] N.stalk x :=
      Stacks.Modules.stalkLinearMap (O := X.presheaf) (z := x) f.val
    exact linearMap.map_smul scalar element

@[simp] theorem stalkLinearMap_apply (M N : OXModule X) (f : M ⟶ N) (x : X.carrier)
    (z : M.stalk x) : stalkLinearMap M N f x z = stalkMapAdd M N f x z := rfl

/-- `presheafTensorStalkFwd` on a germ of a general element `t` is `ptsFwd_phiU`. -/
theorem presheafTensorStalkFwd_germ (M F : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
    (t : ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        F).presheaf.obj (Opposite.op U)) :
    presheafTensorStalkFwd M F x
        ((ConcreteCategory.hom (TopCat.Presheaf.germ
          ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
              F).presheaf U x hxU) t))
      = ptsFwd_phiU M F x U hxU t := by
  exact ptsFwd_fwdAdd_germ M F x U hxU t

/-- `presheafTensorStalkFwd` on a germ of a simple tensor `m ⊗ₜ n`:
`germ_U m ⊗ germ_U n`. -/
theorem presheafTensorStalkFwd_germ_tmul (M F : OXModule X) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
    (m : M.val.obj (Opposite.op U)) (n : F.val.obj (Opposite.op U)) :
    presheafTensorStalkFwd M F x
        ((ConcreteCategory.hom (TopCat.Presheaf.germ
          ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
              F).presheaf U x hxU)
          (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n)))
      = (ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf U x hxU)) m
          ⊗ₜ[X.presheaf.stalk x]
          (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf U x hxU)) n := by
  exact ptsFwd_fwdAdd_germ M F x U hxU (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n)

/-- **Naturality of `presheafTensorStalkFwd` in the first variable.**  The presheaf
stalk map of `(tensorRight F.val).map f.val = f.val ▷ F.val` corresponds, under
`presheafTensorStalkFwd`, to `rTensor (F.stalk x) (stalkLinearMap M N f x)`. -/
theorem presheafTensorStalkFwd_naturality (F M N : OXModule X) (f : M ⟶ N) (x : X.carrier)
    (z : presheafTensorStalkCarrier M F x) :
    presheafTensorStalkFwd N F x
        ((ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map
          ((PresheafOfModules.toPresheaf _).map
            ((MonoidalCategory.tensorRight ((SheafOfModules.forget (ringSheaf X)).obj F)).map
              ((SheafOfModules.forget (ringSheaf X)).map f))))) z)
      = LinearMap.rTensor (F.stalk x) (stalkLinearMap M N f x)
          (presheafTensorStalkFwd M F x z) := by
  obtain ⟨U, hxU, value, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x)
    (M.val ⊗ F.val).presheaf z
  let sourceGerm : TensorProduct (X.presheaf.obj (Opposite.op U))
      (M.val.obj (Opposite.op U)) (F.val.obj (Opposite.op U)) →+
        presheafTensorStalkCarrier M F x := ptsInv_germP M F x U hxU
  let stalkHom : presheafTensorStalkCarrier M F x →+ presheafTensorStalkCarrier N F x :=
    ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map ((MonoidalCategory.tensorRight F.val).map f.val)))
  let leftComposite := (presheafTensorStalkFwd N F x).toAddMonoidHom.comp
    (stalkHom.comp sourceGerm)
  let rightComposite := (LinearMap.rTensor (F.stalk x) (stalkLinearMap M N f x)).toAddMonoidHom.comp
    ((presheafTensorStalkFwd M F x).toAddMonoidHom.comp sourceGerm)
  show leftComposite value = rightComposite value
  induction value using TensorProduct.induction_on with
  | zero => exact (map_zero leftComposite).trans (map_zero rightComposite).symm
  | add left right left_eq right_eq =>
      exact (map_add leftComposite left right).trans
        ((congrArg₂ (· + ·) left_eq right_eq).trans (map_add rightComposite left right).symm)
  | tmul left right =>
      have mappedGerm := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
        ((PresheafOfModules.toPresheaf _).map ((MonoidalCategory.tensorRight F.val).map f.val))
        (left ⊗ₜ[X.presheaf.obj (Opposite.op U)] right)
      have mappedTensor := congrArg
        (fun sectionValue : TensorProduct (X.presheaf.obj (Opposite.op U))
            (N.val.obj (Opposite.op U)) (F.val.obj (Opposite.op U)) =>
          presheafTensorStalkFwd N F x (ptsInv_germP N F x U hxU sectionValue))
        (tensorBy_map_app_tmul F M N f U left right)
      have leftComputation := (congrArg (presheafTensorStalkFwd N F x) mappedGerm).trans
        (mappedTensor.trans (presheafTensorStalkFwd_germ_tmul N F x U hxU
          ((f.val.app (Opposite.op U)).hom left) right))
      have rightComputation := (congrArg (LinearMap.rTensor (F.stalk x) (stalkLinearMap M N f x))
        (presheafTensorStalkFwd_germ_tmul M F x U hxU left right)).trans
          ((LinearMap.rTensor_tmul (F.stalk x) (stalkLinearMap M N f x)
            (ptsFwd_germM F x U hxU right) (ptsFwd_germM M x U hxU left)).trans
              (congrArg (fun element : N.stalk x =>
                element ⊗ₜ[X.presheaf.stalk x] ptsFwd_germM F x U hxU right)
                (stalkMapAdd_germ M N f x U hxU left)))
      exact leftComputation.trans rightComputation.symm

/-- `presheafTensorStalkFwd` is injective: it has the left inverse `presheafTensorStalkInv`. -/
private theorem presheafTensorStalkFwd_injective (M N : OXModule X) (x : X.carrier) :
    Function.Injective (presheafTensorStalkFwd M N x) :=
  Function.LeftInverse.injective (g := presheafTensorStalkInv M N x) fun z => by
    simpa using LinearMap.congr_fun (presheafTensorStalk_inv_fwd M N x) z

/-- **Leaf (Tag 05NE, ⇐ stalk-local core).**  Stalkwise injectivity is preserved by
`- ⊗_{O_X} F` when every stalk `F_x` is flat.  This is the stalk-tensor compatibility
(`stalk_tensor_iso`, natural in the first variable) combined with flatness of `F_x`. -/
@[ega "0 6.7.2" "partial",
  ega "IV 2.2.7" "partial",
  ega "IV 2.2.9" "partial",
  ega "IV 21.5.3" "partial", sga "3 VIB 11.7" "more general"]
theorem tensorBy_stalk_injective_of_flat (F M N : OXModule X) (f : M ⟶ N)
    (hf : ∀ x, Function.Injective (stalkMapAdd M N f x)) (hF : F.FlatStalkwise)
    (x : X.carrier) :
    Function.Injective
      (stalkMapAdd ((tensorBy F).obj M) ((tensorBy F).obj N) ((tensorBy F).map f) x) := by
  -- Abbreviations: the presheaf-module map `g = f.val ▷ F.val` and its presheaf stalk map.
  set g : ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
      F)
      ⟶ ((SheafOfModules.forget (ringSheaf X)).obj N ⊗ (SheafOfModules.forget (ringSheaf X)).obj F)
          :=
    (MonoidalCategory.tensorRight ((SheafOfModules.forget (ringSheaf X)).obj F)).map
      ((SheafOfModules.forget (ringSheaf X)).map f) with hg
  set gMap := (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map
    ((PresheafOfModules.toPresheaf _).map g))) with hgMap
  -- `F.stalk x` is flat, so `rTensor (F.stalk x) (stalkLinearMap M N f x)` is injective.
  have : Module.Flat (X.presheaf.stalk x) (stalk F x) := hF x
  have hfx : Function.Injective (stalkLinearMap M N f x) := hf x
  have hrT : Function.Injective
      (LinearMap.rTensor (F.stalk x) (stalkLinearMap M N f x)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (stalkLinearMap M N f x) hfx
  -- `presheafTensorStalkFwd M F x` is injective (it has a left inverse).
  have hFwdM := presheafTensorStalkFwd_injective M F x
  -- Hence `gMap` is injective, via the presheaf-tensor naturality square (B).
  have hgMap_inj : Function.Injective gMap := by
    have hcomp : Function.Injective
        (fun z => presheafTensorStalkFwd N F x (gMap z)) := by
      have heq : (fun z => presheafTensorStalkFwd N F x (gMap z))
          = fun z => LinearMap.rTensor (F.stalk x) (stalkLinearMap M N f x)
              (presheafTensorStalkFwd M F x z) := by
        funext z
        exact presheafTensorStalkFwd_naturality F M N f x z
      rw [heq]
      exact hrT.comp hFwdM
    exact fun a b hab => hcomp (by simp only []; rw [hab])
  -- `sheafifyStalkFwd` is bijective at both ends.
  have hbijM := (sheafifyStalkLinearEquiv x
    ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        F)).bijective
  have hbijN := (sheafifyStalkLinearEquiv x
    ((SheafOfModules.forget (ringSheaf X)).obj N ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        F)).bijective
  -- The target stalk map is, by construction, the sheafify stalk map of `g`.
  show Function.Injective
    (ConcreteCategory.hom (stalkMapAdd
      (sheafify.obj ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget
          (ringSheaf X)).obj F))
      (sheafify.obj ((SheafOfModules.forget (ringSheaf X)).obj N ⊗ (SheafOfModules.forget
          (ringSheaf X)).obj F))
      (sheafify.map g) x))
  -- Conclude injectivity of the sheaf stalk map `S` via the sheafify naturality square (A).
  intro s t hst
  -- write s, t as images of germs under the bijective `sheafifyStalkFwd`
  obtain ⟨s', hs'⟩ := hbijM.2 s
  obtain ⟨t', ht'⟩ := hbijM.2 t
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x)
    ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        F).presheaf s'
  obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x)
    ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        F).presheaf t'
  -- `sheafifyStalkLinearEquiv` applied is `sheafifyStalkFwd`
  have hsF : (sheafifyStalkLinearEquiv x
        ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj F))
        ((ConcreteCategory.hom (TopCat.Presheaf.germ
          ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
              F).presheaf U x hxU)) a)
      = sheafifyStalkFwd x _
          ((ConcreteCategory.hom (TopCat.Presheaf.germ
            ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                X)).obj F).presheaf U x hxU)) a) := rfl
  have htF : (sheafifyStalkLinearEquiv x
        ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj F))
        ((ConcreteCategory.hom (TopCat.Presheaf.germ
          ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
              F).presheaf V x hxV)) b)
      = sheafifyStalkFwd x _
          ((ConcreteCategory.hom (TopCat.Presheaf.germ
            ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                X)).obj F).presheaf V x hxV)) b) := rfl
  rw [← hs', ← ht', hsF, htF] at hst
  rw [sheafifyStalkFwd_naturality x g U hxU a, sheafifyStalkFwd_naturality x g V hxV b] at hst
  -- the outer `sheafifyStalkFwd x (sheafify-target)` is injective; strip it
  have hst2 := hbijN.1 hst
  -- now hst2 : gMap (germ a) = gMap (germ b); use injectivity of gMap
  have hst3 := hgMap_inj hst2
  -- finally apply `sheafifyStalkFwd x P_M` to germ a = germ b
  rw [← hs', ← ht', hsF, htF, hst3]

/-- **Converse transport (Tag 05NE, ⇒ direction).**  If the sheaf stalk map of
`(tensorBy F).map f` is injective, then `rTensor (F.stalk x) (stalkLinearMap M N f x)`
is injective.  This is the reverse of the conjugation used in
`tensorBy_stalk_injective_of_flat`: we strip the bijective sheafify-stalk transport
(square A) and the bijective presheaf-tensor-stalk transport (square B). -/
theorem rTensor_stalkLinearMap_injective_of_tensorBy_stalk_injective
    (F M N : OXModule X) (f : M ⟶ N) (x : X.carrier)
    (hS : Function.Injective
      (stalkMapAdd ((tensorBy F).obj M) ((tensorBy F).obj N) ((tensorBy F).map f) x)) :
    Function.Injective (LinearMap.rTensor (F.stalk x) (stalkLinearMap M N f x)) := by
  -- The presheaf-module map `g = f.val ▷ F.val` and its presheaf stalk map.
  set g : ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
      F)
      ⟶ ((SheafOfModules.forget (ringSheaf X)).obj N ⊗ (SheafOfModules.forget (ringSheaf X)).obj F)
          :=
    (MonoidalCategory.tensorRight ((SheafOfModules.forget (ringSheaf X)).obj F)).map
      ((SheafOfModules.forget (ringSheaf X)).map f) with hg
  set gMap := (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map
    ((PresheafOfModules.toPresheaf _).map g))) with hgMap
  -- `presheafTensorStalkFwd` is bijective at both ends.
  have hFwdM := presheafTensorStalkFwd_injective M F x
  have hFwdN_inj := presheafTensorStalkFwd_injective N F x
  have hFwdM_surj : Function.Surjective (presheafTensorStalkFwd M F x) := by
    intro y
    refine ⟨presheafTensorStalkInv M F x y, ?_⟩
    have := LinearMap.congr_fun (presheafTensorStalk_fwd_inv M F x) y
    simpa using this
  -- `sheafifyStalkFwd` is bijective at both ends.
  have hbijM := (sheafifyStalkLinearEquiv x
    ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        F)).bijective
  have hbijN := (sheafifyStalkLinearEquiv x
    ((SheafOfModules.forget (ringSheaf X)).obj N ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        F)).bijective
  -- Reframe `hS` as injectivity of the sheafify stalk map of `g`.
  have hS' : Function.Injective
      (ConcreteCategory.hom (stalkMapAdd
        (sheafify.obj ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget
            (ringSheaf X)).obj F))
        (sheafify.obj ((SheafOfModules.forget (ringSheaf X)).obj N ⊗ (SheafOfModules.forget
            (ringSheaf X)).obj F))
        (sheafify.map g) x)) := hS
  -- Step 1: `gMap` is injective (strip square A).
  have hgMap_inj : Function.Injective gMap := by
    intro u v huv
    -- write `u`, `v` as germs of the presheaf stalk
    obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x)
      ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
          F).presheaf u
    obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x)
      ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
          F).presheaf v
    -- apply the bijective `sheafifyStalkFwd x (N⊗F)` to both sides of `huv`
    have huv2 := congrArg (sheafifyStalkFwd x
      ((SheafOfModules.forget (ringSheaf X)).obj N ⊗ (SheafOfModules.forget (ringSheaf X)).obj F))
          huv
    -- rewrite via square A
    rw [show sheafifyStalkFwd x
            ((SheafOfModules.forget (ringSheaf X)).obj N ⊗ (SheafOfModules.forget (ringSheaf
                X)).obj F)
            (gMap ((ConcreteCategory.hom (TopCat.Presheaf.germ
              ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                  X)).obj F).presheaf U x hxU)) a))
          = stalkMapAdd (sheafify.obj _) (sheafify.obj _) (sheafify.map g) x
              (sheafifyStalkFwd x _
                ((ConcreteCategory.hom (TopCat.Presheaf.germ
                  ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                      X)).obj F).presheaf U x hxU)) a))
        from (sheafifyStalkFwd_naturality x g U hxU a).symm,
      show sheafifyStalkFwd x
            ((SheafOfModules.forget (ringSheaf X)).obj N ⊗ (SheafOfModules.forget (ringSheaf
                X)).obj F)
            (gMap ((ConcreteCategory.hom (TopCat.Presheaf.germ
              ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                  X)).obj F).presheaf V x hxV)) b))
          = stalkMapAdd (sheafify.obj _) (sheafify.obj _) (sheafify.map g) x
              (sheafifyStalkFwd x _
                ((ConcreteCategory.hom (TopCat.Presheaf.germ
                  ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                      X)).obj F).presheaf V x hxV)) b))
        from (sheafifyStalkFwd_naturality x g V hxV b).symm] at huv2
    -- strip `S` (injective) then strip `sheafifyStalkFwd x (M⊗F)` (injective)
    exact hbijM.1 (hS' huv2)
  -- Step 2: `rTensor` is injective (strip square B).
  intro u v huv
  obtain ⟨z₁, rfl⟩ := hFwdM_surj u
  obtain ⟨z₂, rfl⟩ := hFwdM_surj v
  rw [← presheafTensorStalkFwd_naturality F M N f x z₁,
      ← presheafTensorStalkFwd_naturality F M N f x z₂] at huv
  -- `huv : presheafTensorStalkFwd N F x (gMap z₁) = presheafTensorStalkFwd N F x (gMap z₂)`
  have := hgMap_inj (hFwdN_inj huv)
  rw [this]

/-- `Tor1IsZero F G` unfolded: it says exactly that the module-theoretic
`Tor_1^{O_{X,x}}(F_x, G_x)` vanishes at every point `x`.

This is `Iff.rfl` — `Tor1IsZero` is *defined* as the right-hand side, so this
lemma has no mathematical content and in particular does **not** relate
`Tor1IsZero` to the sheaf-level `Tor_1` of Tag 08BP
(`Stacks.Cohomology.tor`).  It is kept only as a readable restatement of the
definition; do not cite it as a correctness lemma. -/
theorem tor1IsZero_iff_stalk (F G : OXModule X) :
    F.Tor1IsZero G ↔ ∀ x : X.carrier, IsZero (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) 1).obj
      (F.stalk x)).obj (G.stalk x)) := Iff.rfl

end OXModule
