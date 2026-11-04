module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.ModuleGeneration
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.GradedAlgebra
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.AffineLimitProjection

import all StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.ModuleGeneration
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.GradedAlgebra
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.AffineLimitProjection

/-!
# The graded module of transition kernels and its finite type

An affine-local bilinear pairing is extended to the whole scheme, giving the graded module over
the associated graded algebra whose homogeneous pieces are `F_0` and the transition kernels; it
is of finite type ([Stacks, Tag 087Z]).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

attribute [local instance] ringHomInvPairOfRingEquiv ringHomInvPairOfRingEquivSymm

/-! ### Extending an affine-local bilinear pairing to the whole scheme -/

section BasisExtension

attribute [local instance] moduleOfSectionsBE

private lemma sections_ext_affine {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (s t : M.val.obj (op U))
    (h : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U),
      M.val.map (homOfLE hVU).op s = M.val.map (homOfLE hVU).op t) : s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf _).obj M)
    (fun V : {V : X.affineOpens // V.1 ≤ U} => V.1.1) U (fun V => homOfLE V.2) ?_ s t ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact (TopologicalSpace.Opens.mem_iSup).mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
  · exact fun V => h V.1 V.2

private def sectionPairs {X : Scheme.{u}} (M N : X.Modules) : X.Opensᵒᵖ ⥤ Type u where
  obj U := M.val.obj U × N.val.obj U
  map f := ↾fun x => (M.val.map f x.1, N.val.map f x.2)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (ConcreteCategory.congr_hom (M.presheaf.map_id U) x.1)
      (ConcreteCategory.congr_hom (N.presheaf.map_id U) x.2)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (M.val.map_comp_apply f g x.1) (N.val.map_comp_apply f g x.2)

private def basisBinaryExtension {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens, M.val.obj (op U.1) → N.val.obj (op U.1) → P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y)) :
    sectionPairs M N ⟶ P.presheaf ⋙ forget AddCommGrpCat :=
  TopCat.Sheaf.restrictHomEquivHom (sectionPairs M N)
    ((sheafForget _).obj ((SheafOfModules.toSheaf _).obj P))
    (B := fun U : X.affineOpens => U.1)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens)
    { app U := ↾fun x => b U.unop x.1 x.2
      naturality U V f := by
        ext x
        exact (hb U.unop V.unop f.unop.hom.le x.1 x.2).symm }

private lemma basisBinaryExtension_affine {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens, M.val.obj (op U.1) → N.val.obj (op U.1) → P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    (U : X.affineOpens) (x) (y) :
    (basisBinaryExtension M N P b hb).app (op U.1) (x, y) = b U x y := by
  have happ : (basisBinaryExtension M N P b hb).app (op U.1) = ↾fun z => b U z.1 z.2 :=
    TopCat.Sheaf.extend_hom_app (B := fun V : X.affineOpens => V.1) _ _ _ _ U
  rw [happ]
  rfl

private lemma basisBinaryExtension_restrict {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens, M.val.obj (op U.1) → N.val.obj (op U.1) → P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) (x) (y) :
    P.val.map f ((basisBinaryExtension M N P b hb).app U (x, y)) =
      (basisBinaryExtension M N P b hb).app V (M.val.map f x, N.val.map f y) :=
  (congrArg (fun k => k.hom (x, y)) ((basisBinaryExtension M N P b hb).naturality f)).symm

/-- A pairing specified on affine opens and compatible with restriction, glued to a pairing
of sections over every open. -/
private abbrev bilinearPairing {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y)) :
    sectionPairs M N ⟶ P.presheaf ⋙ forget AddCommGrpCat :=
  basisBinaryExtension M N P (fun U x y => b U x y) hb

/-- The value of the glued pairing on a pair of sections, read as a section of `P`. -/
private abbrev bilinearPairingVal {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    (U : X.Opensᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) : P.val.obj U :=
  (bilinearPairing M N P b hb).app U (x, y)

private lemma bilinearPairingVal_restrict {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) (x) (y) :
    P.val.map f (bilinearPairingVal M N P b hb U x y) =
      bilinearPairingVal M N P b hb V (M.val.map f x) (N.val.map f y) :=
  basisBinaryExtension_restrict M N P _ hb f x y

private lemma bilinearPairingVal_affine {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    (U : X.affineOpens) (x) (y) :
    bilinearPairingVal M N P b hb (op U.1) x y = b U x y :=
  basisBinaryExtension_affine M N P _ hb U x y

/-- The glued pairing, restricted to an affine open, is the pairing there. -/
private lemma bilinearPairingVal_map_affine {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    {U : X.Opensᵒᵖ} (V : X.affineOpens) (h : V.1 ≤ U.unop) (x) (y) :
    P.val.map (homOfLE h).op (bilinearPairingVal M N P b hb U x y) =
      b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y) :=
  (bilinearPairingVal_restrict M N P b hb (homOfLE h).op x y).trans
    (bilinearPairingVal_affine M N P b hb V _ _)

/-- The glued pairing is additive in its second variable. -/
private lemma bilinearPairingVal_add_right {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    (U : X.Opensᵒᵖ) (x : M.val.obj U) (y z : N.val.obj U) :
    bilinearPairingVal M N P b hb U x (y + z) =
      bilinearPairingVal M N P b hb U x y + bilinearPairingVal M N P b hb U x z := by
  apply sections_ext_affine P U.unop
  intro V h
  rw [bilinearPairingVal_map_affine, map_add, map_add, bilinearPairingVal_map_affine,
    bilinearPairingVal_map_affine]
  exact map_add _ _ _

/-- The glued pairing is additive in its first variable. -/
private lemma bilinearPairingVal_add_left {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    (U : X.Opensᵒᵖ) (x z : M.val.obj U) (y : N.val.obj U) :
    bilinearPairingVal M N P b hb U (x + z) y =
      bilinearPairingVal M N P b hb U x y + bilinearPairingVal M N P b hb U z y := by
  apply sections_ext_affine P U.unop
  intro V h
  rw [bilinearPairingVal_map_affine, map_add, map_add, bilinearPairingVal_map_affine,
    bilinearPairingVal_map_affine]
  exact (DFunLike.congr_fun (map_add (b V) _ _) _).trans (AddMonoidHom.add_apply _ _ _)

/-- The glued pairing is linear in its first variable. -/
private lemma bilinearPairingVal_smul_left {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    (hl : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (x) (y), b U (r • x) y = r • b U x y)
    (U : X.Opensᵒᵖ) (r : X.ringCatSheaf.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    bilinearPairingVal M N P b hb U (r • x) y =
      r • bilinearPairingVal M N P b hb U x y := by
  apply sections_ext_affine P U.unop
  intro V h
  rw [bilinearPairingVal_map_affine, P.val.map_smul, bilinearPairingVal_map_affine,
    M.val.map_smul]
  exact hl V _ _ _

/-- The glued pairing is linear in its second variable. -/
private lemma bilinearPairingVal_smul_right {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    (hr : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (x) (y), b U x (r • y) = r • b U x y)
    (U : X.Opensᵒᵖ) (r : X.ringCatSheaf.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    bilinearPairingVal M N P b hb U x (r • y) =
      r • bilinearPairingVal M N P b hb U x y := by
  apply sections_ext_affine P U.unop
  intro V h
  rw [bilinearPairingVal_map_affine, P.val.map_smul, bilinearPairingVal_map_affine,
    N.val.map_smul]
  exact hr V _ _ _

/-- A pairing specified on affine opens, compatible with restriction and bilinear there,
extends to a bilinear map of sheaves of modules. -/
private def extendBilinear {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    (hl : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (x) (y), b U (r • x) y = r • b U x y)
    (hr : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (x) (y), b U x (r • y) = r • b U x y) :
    SheafOfModules.BilinearMap M N P where
  app U := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => bilinearPairingVal M N P b hb U x y)
      (bilinearPairingVal_add_right M N P b hb U x))
    (fun x z => AddMonoidHom.ext fun y =>
      bilinearPairingVal_add_left M N P b hb U x z y)
  map_smul_left U r x y := bilinearPairingVal_smul_left M N P b hb hl U r x y
  map_smul_right U r x y := bilinearPairingVal_smul_right M N P b hb hr U r x y
  naturality f x y := bilinearPairingVal_restrict M N P b hb f x y

private lemma extendBilinear_affine {X : Scheme.{u}} (M N P : X.Modules)
    (b : ∀ U : X.affineOpens,
      M.val.obj (op U.1) →+ N.val.obj (op U.1) →+ P.val.obj (op U.1))
    (hb : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x) (y),
      P.val.map (homOfLE h).op (b U x y) =
        b V (M.val.map (homOfLE h).op x) (N.val.map (homOfLE h).op y))
    (hl : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (x) (y), b U (r • x) y = r • b U x y)
    (hr : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (x) (y), b U x (r • y) = r • b U x y)
    (U : X.affineOpens) (x) (y) :
    (extendBilinear M N P b hb hl hr).app (op U.1) x y = b U x y :=
  bilinearPairingVal_affine M N P b hb U x y

end BasisExtension

/-! ### The graded module of transition kernels -/

section GradedModuleConstruction

attribute [local instance] moduleOfSectionsGM

private def zeroBilinear {X : Scheme.{u}} (M N P : X.Modules) :
    SheafOfModules.BilinearMap M N P where
  app _ := 0
  map_smul_left _ _ _ _ := by simp
  map_smul_right _ _ _ _ := by simp
  naturality f _ _ := (P.val.map f).hom.map_zero

private def natTransitionBilinear {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n m : ℕ) :
    SheafOfModules.BilinearMap
      (transitionKernelPiece F n) ((conormalPushforward I).piece m)
      (transitionKernelPiece F (n + m : ℕ)) :=
  extendBilinear _ _ _ (fun U => affineOpenTransitionAction I F U n m)
    (fun U V h => affineOpenTransitionAction_restrict I F U V h n m)
    (fun U => affineOpenTransitionAction_smul_left I F U n m)
    (fun U => affineOpenTransitionAction_smul_right I F U n m)

private lemma natTransitionBilinear_affine {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n m : ℕ)
    (U : X.affineOpens) (x) (a) :
    (natTransitionBilinear I F n m).app (op U.1) x a =
      affineOpenTransitionAction I F U n m x a :=
  extendBilinear_affine _ _ _ _ _ _ _ U x a

/-- On an affine open the action of the associated graded algebra on the transition kernels
is associative. -/
private lemma natTransitionBilinear_assoc {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n i j : ℕ) (V : X.affineOpens)
    (x : (transitionKernelPiece F (n : ℤ)).val.obj (op V.1))
    (a : ((conormalPushforward I).piece (i : ℤ)).val.obj (op V.1))
    (b : ((conormalPushforward I).piece (j : ℤ)).val.obj (op V.1)) :
    HEq ((natTransitionBilinear I F (n + i) j).app (op V.1)
        ((natTransitionBilinear I F n i).app (op V.1) x a) b)
      ((natTransitionBilinear I F n (i + j)).app (op V.1) x
        (((conormalPushforward I).mul (i : ℤ) (j : ℤ)).app (op V.1) a b)) := by
  rw [natTransitionBilinear_affine, natTransitionBilinear_affine,
    natTransitionBilinear_affine]
  exact affineOpenTransitionAction_assoc I F V n i j x a b

/-- On an affine open the unit of the associated graded algebra acts as the identity on the
transition kernels. -/
private lemma natTransitionBilinear_one {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n : ℕ) (V : X.affineOpens)
    (x : (transitionKernelPiece F (n : ℤ)).val.obj (op V.1)) :
    HEq ((natTransitionBilinear I F n 0).app (op V.1) x
      ((conormalPushforward I).one.eval (op V.1))) x := by
  rw [natTransitionBilinear_affine, affineOpenTransitionAction_one]

private def transitionBilinear {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n m : ℤ) :
    SheafOfModules.BilinearMap
      (transitionKernelPiece F n) ((conormalPushforward I).piece m)
      (transitionKernelPiece F (n + m)) :=
  match n, m with
  | .ofNat n, .ofNat m => natTransitionBilinear I F n m
  | .negSucc _, _ => zeroBilinear _ _ _
  | .ofNat _, .negSucc _ => zeroBilinear _ _ _

private abbrev transitionAction {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n m : ℤ)
    (U : X.Opensᵒᵖ) := (transitionBilinear I F n m).app U

private lemma sections_eq_zero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M)
    (U : X.Opensᵒᵖ) (x : M.val.obj U) : x = 0 := by
  have hid := (IsZero.iff_id_eq_zero M).mp hM
  have happ := congrArg (fun f : M ⟶ M => f.val.app U x) hid
  rw [show ((𝟙 M : M ⟶ M).val.app U) = 𝟙 _ from rfl,
    show ((0 : M ⟶ M).val.app U) = 0 from rfl] at happ
  simpa using happ

private lemma graded_zero_heq {X : Scheme.{u}} (M : ℤ → X.Modules) {n m : ℤ}
    (h : n = m) (U : X.Opensᵒᵖ) :
    HEq (0 : (M n).val.obj U) (0 : (M m).val.obj U) := by subst m; rfl

private lemma sections_heq_affine {X : Scheme.{u}} (M : ℤ → X.Modules) {n m : ℤ}
    (hnm : n = m) (U : X.Opens) (s : (M n).val.obj (op U)) (t : (M m).val.obj (op U))
    (h : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U),
      HEq ((M n).val.map (homOfLE hVU).op s) ((M m).val.map (homOfLE hVU).op t)) :
    HEq s t := by
  subst m
  exact heq_of_eq (sections_ext_affine _ U s t fun V hVU => eq_of_heq (h V hVU))

private lemma transitionAction_assoc {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n i j : ℤ)
    (U : X.Opensᵒᵖ) (x : (transitionKernelPiece F n).val.obj U)
    (a : ((conormalPushforward I).piece i).val.obj U)
    (b : ((conormalPushforward I).piece j).val.obj U) :
    HEq (transitionAction I F (n + i) j U (transitionAction I F n i U x a) b)
      (transitionAction I F n (i + j) U x (((conormalPushforward I).mul i j).app U a b)) := by
  by_cases hn : n < 0
  · rw [sections_eq_zero _ (transitionKernelPiece_negative F n hn) U x]
    simp only [map_zero, AddMonoidHom.zero_apply]
    exact graded_zero_heq (transitionKernelPiece F) (add_assoc n i j) U
  by_cases hi : i < 0
  · rw [sections_eq_zero _ (conormalPushforward_negative I i hi) U a]
    simp only [map_zero, AddMonoidHom.zero_apply]
    exact graded_zero_heq (transitionKernelPiece F) (add_assoc n i j) U
  by_cases hj : j < 0
  · rw [sections_eq_zero _ (conormalPushforward_negative I j hj) U b]
    simp only [map_zero]
    exact graded_zero_heq (transitionKernelPiece F) (add_assoc n i j) U
  lift n to ℕ using le_of_not_gt hn
  lift i to ℕ using le_of_not_gt hi
  lift j to ℕ using le_of_not_gt hj
  apply sections_heq_affine (transitionKernelPiece F) (add_assoc _ _ _) U.unop
  intro V h
  have hgoal : HEq
      ((transitionKernelPiece F ((n + i + j : ℕ) : ℤ)).val.map (homOfLE h).op
        ((natTransitionBilinear I F (n + i) j).app U
          ((natTransitionBilinear I F n i).app U x a) b))
      ((transitionKernelPiece F ((n + (i + j) : ℕ) : ℤ)).val.map (homOfLE h).op
        ((natTransitionBilinear I F n (i + j)).app U x
          (((conormalPushforward I).mul i j).app U a b))) := by
    have hmul : ((conormalPushforward I).piece ((i + j : ℕ) : ℤ)).val.map (homOfLE h).op
          (((conormalPushforward I).mul (i : ℤ) (j : ℤ)).app U a b) =
        ((conormalPushforward I).mul (i : ℤ) (j : ℤ)).app (op V.1)
          (((conormalPushforward I).piece (i : ℤ)).val.map (homOfLE h).op a)
          (((conormalPushforward I).piece (j : ℤ)).val.map (homOfLE h).op b) :=
      ((conormalPushforward I).mul i j).naturality (homOfLE h).op a b
    rw [(natTransitionBilinear I F (n + i) j).naturality,
      (natTransitionBilinear I F n i).naturality,
      (natTransitionBilinear I F n (i + j)).naturality, hmul]
    exact natTransitionBilinear_assoc I F n i j V _ _ _
  exact hgoal

private lemma transitionAction_one {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n : ℤ)
    (U : X.Opensᵒᵖ) (x : (transitionKernelPiece F n).val.obj U) :
    HEq (transitionAction I F n 0 U x ((conormalPushforward I).one.eval U)) x := by
  by_cases hn : n < 0
  · rw [sections_eq_zero _ (transitionKernelPiece_negative F n hn) U x]
    simp only [map_zero, AddMonoidHom.zero_apply]
    exact graded_zero_heq (transitionKernelPiece F) (add_zero n) U
  lift n to ℕ using le_of_not_gt hn
  apply sections_heq_affine (transitionKernelPiece F) (add_zero _) U.unop
  intro V h
  have hgoal : HEq
      ((transitionKernelPiece F ((n + 0 : ℕ) : ℤ)).val.map (homOfLE h).op
        ((natTransitionBilinear I F n 0).app U x ((conormalPushforward I).one.eval U)))
      ((transitionKernelPiece F (n : ℤ)).val.map (homOfLE h).op x) := by
    have hone : ((conormalPushforward I).piece ((0 : ℕ) : ℤ)).val.map (homOfLE h).op
          ((conormalPushforward I).one.eval U) =
        (conormalPushforward I).one.eval (op V.1) :=
      (conormalPushforward I).one.property (homOfLE h).op
    rw [(natTransitionBilinear I F n 0).naturality, hone]
    exact natTransitionBilinear_one I F n V _
  exact hgoal

/-- The transition kernels of a coherent adic system, as a graded module over the
associated graded algebra of the ideal. -/
private def transitionGradedModule {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) :
    SheafOfModules.GradedModule (conormalPushforward I) where
  piece n := transitionKernelPiece F n
  smul := transitionAction I F
  smul_smul_left n m := (transitionBilinear I F n m).map_smul_left
  smul_smul_right n m := (transitionBilinear I F n m).map_smul_right
  smul_naturality n m := (transitionBilinear I F n m).naturality
  smul_mul := transitionAction_assoc I F
  smul_one := transitionAction_one I F

private lemma transitionGradedModule_affineAction {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n m : ℕ)
    (U : X.affineOpens) (x) (a) :
    HEq (affineOpenTransitionSectionsEquiv I F U (n + m)
      ((transitionGradedModule I F).smul n m (op U.1) x a))
      (AssociatedGraded.homogeneousSMul (I.ideal U)
        (conormalPieceAddEquiv I U m a) (affineOpenTransitionSectionsEquiv I F U n x)) := by
  have h1 : (transitionGradedModule I F).smul (n : ℤ) (m : ℤ) (op U.1) x a =
      affineOpenTransitionAction I F U n m x a :=
    natTransitionBilinear_affine I F n m U x a
  rw [h1]
  exact (heq_of_eq ((affineOpenTransitionSectionsEquiv I F U (n + m)).apply_symm_apply _)).trans
    (gradedPieceCast_heq _ _ _)

end GradedModuleConstruction

/-! ### Finite generation -/

private lemma affine_limit_finite_generators {X : Scheme.{u}} [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) :
    ∃ G : Finset (sectionsLimit F ⊤), ∀ n : ℕ,
      AddSubgroup.closure
        {x : AssociatedGraded.piece (M := sectionsLimit F ⊤)
            (I.ideal ⟨⊤, isAffineOpen_top X⟩) n |
          ∃ s ∈ G, ∃ a : AssociatedGraded.power (M := Γ(X, ⊤))
            (I.ideal ⟨⊤, isAffineOpen_top X⟩) n,
            x = gradedScale (I.ideal ⟨⊤, isAffineOpen_top X⟩) n a s} = ⊤ := by
  obtain ⟨J, rfl⟩ := Scheme.IdealSheafData.equivOfIsAffine.symm.surjective I
  let e := (globalSectionsComparison X J F).toLinearEquiv
  let _ : IsScalarTower Γ(X, ⊤) (AdicCompletion J Γ(X, ⊤)) (completedModuleAsBase X J F) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let _ : Module.Finite (AdicCompletion J Γ(X, ⊤)) (completedModuleAsBase X J F) :=
    ((coherentAdicSystemsEquivFGModuleCat X J).functor.obj F).property
  have h := adicCompletion_associatedGraded_piece_closure_smul_fg
    (R := Γ(X, ⊤)) (M := completedModuleAsBase X J F) (I := J)
  exact finite_generators_transport (RingEquiv.refl Γ(X, ⊤)) J
    ((Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top X⟩) (by simp) e h

private lemma affineOpen_limit_finite_generators {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (U : X.affineOpens) :
    ∃ G : Finset (sectionsLimit F U.1), ∀ n : ℕ,
      AddSubgroup.closure
        {x : AssociatedGraded.piece (M := sectionsLimit F U.1) (I.ideal U) n |
          ∃ s ∈ G, ∃ a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n,
            x = gradedScale (I.ideal U) n a s} = ⊤ := by
  let _ : IsAffine U.1.toScheme := U.2
  let _ : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  exact finite_generators_transport U.1.topIso.commRingCatIsoToRingEquiv
    ((I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1⟩) (I.ideal U)
    (ideal_map_affineOpen I U) (affineOpenLimitSemilinearEquiv I F U)
    (affine_limit_finite_generators (I.comap U.1.ι) (restrictSystem I F U.1))

private lemma equiv_symm_heq {ι : Type*} {A B : ι → Type*}
    (e : ∀ i, A i ≃ B i) {i j : ι} (h : i = j) (x : A i) (y : B j)
    (hxy : HEq (e i x) y) : HEq ((e j).symm y) x := by
  subst j
  exact heq_of_eq ((e i).symm_apply_eq.mpr (eq_of_heq hxy).symm)

private lemma homogeneousSMul_degreeZero_heq {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) (n : ℕ) (a : AssociatedGraded.power (M := A) I n) (s : M) :
    HEq (AssociatedGraded.homogeneousSMul I (AssociatedGraded.mk I n a)
      (AssociatedGraded.mk I 0 (associatedGradedDegreeZero I s)))
      (gradedScale I n a s) := HEq.refl _

/-! ### The statement of Tag 087Z -/

/-- Local finite generation of a graded module by homogeneous sections. -/
public def IsFiniteTypeOnAffine {X : Scheme.{u}}
    {A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (M : SheafOfModules.GradedModule A) : Prop :=
  ∀ U : X.affineOpens,
    ∃ generators : Finset (Σ n : ℤ, (M.piece n).val.obj (op U.1)),
      ∀ n : ℤ,
        AddSubgroup.closure
          { t : (M.piece n).val.obj (op U.1) |
            ∃ s : Σ d : ℤ, (M.piece d).val.obj (op U.1),
              s ∈ generators ∧
                ∃ (m : ℤ) (a : (A.piece m).val.obj (op U.1))
                  (h : s.1 + m = n),
                  t = h ▸ M.smul s.1 m (op U.1) s.2 a } = ⊤

/-- The associated graded algebra of an ideal sheaf, with the affine identifications of its
homogeneous pieces.  The identifications specify the ordinary associated graded algebra,
not merely an algebra with abstractly isomorphic homogeneous pieces: the identification of
each homogeneous piece is linear over the sections of the structure sheaf, not merely
additive, so it cannot be a twist of the canonical one by a ring automorphism. -/
public structure AssociatedGradedAlgebraData {X : Scheme.{u}} (I : X.IdealSheafData) where
  /-- The graded algebra `⨁ ℐ ⁿ / ℐ ⁿ⁺¹`. -/
  algebra : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf
  /-- Each homogeneous piece of the algebra is `I ⁿ / I ⁿ⁺¹` on an affine open. -/
  algebraPiece (n : ℕ) (U : X.affineOpens) :
    (algebra.piece (n : ℤ)).val.obj (op U.1) ≃+
      AssociatedGraded.piece (M := Γ(X, U.1)) (I.ideal U) n
  /-- That identification is linear over the sections of the structure sheaf. -/
  algebraPiece_smul (n : ℕ) (U : X.affineOpens)
      (r : X.ringCatSheaf.obj.obj (op U.1))
      (a : (algebra.piece (n : ℤ)).val.obj (op U.1)) :
    algebraPiece n U (r • a) = (show Γ(X, U.1) from r) • algebraPiece n U a
  /-- It carries the graded multiplication to the associated graded multiplication. -/
  algebraMul (n m : ℕ) (U : X.affineOpens)
      (a : (algebra.piece (n : ℤ)).val.obj (op U.1))
      (b : (algebra.piece (m : ℤ)).val.obj (op U.1)) :
    HEq (algebraPiece (n + m) U
      ((algebra.mul (n : ℤ) (m : ℤ)).app (op U.1) a b))
      (AssociatedGraded.homogeneousSMul (I.ideal U)
        (algebraPiece n U a) (algebraPiece m U b))
  /-- Restriction of an element of `I ⁿ` to a smaller affine open stays in `I ⁿ`. -/
  algebraRestrictionPower (n : ℕ) (U V : X.affineOpens)
      (h : V.1 ≤ U.1) (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n) :
    X.presheaf.map (homOfLE h).op (a : Γ(X, U.1)) ∈
      AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n
  /-- The induced restriction on associated graded pieces. -/
  algebraRestriction (n : ℕ) (U V : X.affineOpens)
      (h : V.1 ≤ U.1) :
    AssociatedGraded.piece (M := Γ(X, U.1)) (I.ideal U) n →+
      AssociatedGraded.piece (M := Γ(X, V.1)) (I.ideal V) n
  /-- It is computed on classes by restricting representatives. -/
  algebraRestriction_mk (n : ℕ) (U V : X.affineOpens)
      (h : V.1 ≤ U.1)
      (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n) :
    algebraRestriction n U V h (AssociatedGraded.mk (I.ideal U) n a) =
      AssociatedGraded.mk (I.ideal V) n
        ⟨X.presheaf.map (homOfLE h).op (a : Γ(X, U.1)),
          algebraRestrictionPower n U V h a⟩
  /-- The affine identifications commute with restriction. -/
  algebraPiece_naturality (n : ℕ) (U V : X.affineOpens)
      (h : V.1 ≤ U.1) (a : (algebra.piece (n : ℤ)).val.obj (op U.1)) :
    algebraPiece n V ((algebra.piece (n : ℤ)).val.map (homOfLE h).op a) =
      algebraRestriction n U V h (algebraPiece n U a)
  /-- The algebra is concentrated in nonnegative degrees. -/
  algebraNegative (n : ℤ) (hn : n < 0) : IsZero (algebra.piece n)
  /-- Every homogeneous piece of the algebra is quasi-coherent. -/
  algebraQuasicoherent (n : ℤ) : (algebra.piece n).IsQuasicoherent

/-- The graded module of transition kernels over the associated graded algebra of the ideal,
with the affine identifications of its homogeneous pieces. -/
public structure AssociatedGradedData {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    extends AssociatedGradedAlgebraData I where
  /-- The graded module over the associated graded algebra. -/
  module : SheafOfModules.GradedModule algebra
  /-- In degree zero the module is the zeroth term of the system. -/
  modulePieceZero : module.piece 0 ≅ F.obj.obj (op 0)
  /-- In degree `n + 1` the module is the `n`-th transition kernel. -/
  modulePieceSucc (n : ℕ) : module.piece ((n + 1 : ℕ) : ℤ) ≅
    kernel (F.obj.map (homOfLE (Nat.le_succ n)).op)
  /-- On an affine open the module piece is the associated graded piece of the inverse limit
  of sections. -/
  moduleAffinePiece (n : ℕ) (U : X.affineOpens) :
    (module.piece (n : ℤ)).val.obj (op U.1) ≃+
      AssociatedGraded.piece (M := sectionsLimit F U.1) (I.ideal U) n
  /-- In degree zero that identification is the projection out of the inverse limit. -/
  moduleAffineZero (U : X.affineOpens)
      (a : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) 0)
      (x : (module.piece 0).val.obj (op U.1))
      (h : moduleAffinePiece 0 U x = AssociatedGraded.mk (I.ideal U) 0 a) :
    (modulePieceZero.hom.val.app (op U.1)) x =
      (sectionsProjection F U.1 0).hom a.1
  /-- In positive degrees it is the projection out of the inverse limit, read in the kernel. -/
  moduleAffineSucc (n : ℕ) (U : X.affineOpens)
      (a : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) (n + 1))
      (x : (module.piece ((n + 1 : ℕ) : ℤ)).val.obj (op U.1))
      (h : moduleAffinePiece (n + 1) U x =
        AssociatedGraded.mk (I.ideal U) (n + 1) a) :
    ((kernel.ι (F.obj.map (homOfLE (Nat.le_succ n)).op)).val.app (op U.1))
      ((modulePieceSucc n).hom.val.app (op U.1) x) =
        (sectionsProjection F U.1 (n + 1)).hom a.1
  /-- The action is the associated graded action of the inverse limit. -/
  moduleAffineAction (n m : ℕ) (U : X.affineOpens)
      (x : (module.piece (n : ℤ)).val.obj (op U.1))
      (a : (algebra.piece (m : ℤ)).val.obj (op U.1)) :
    HEq (moduleAffinePiece (n + m) U
      (module.smul (n : ℤ) (m : ℤ) (op U.1) x a))
      (AssociatedGraded.homogeneousSMul (I.ideal U)
        (algebraPiece m U a) (moduleAffinePiece n U x))
  /-- The module is concentrated in nonnegative degrees. -/
  moduleNegative (n : ℤ) (hn : n < 0) : IsZero (module.piece n)
  /-- Every homogeneous piece of the module is quasi-coherent. -/
  moduleQuasicoherent (n : ℤ) : (module.piece n).IsQuasicoherent
  /-- The module is of finite type. -/
  finiteType : IsFiniteTypeOnAffine module

private lemma transitionGradedModule_finiteType {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) :
    IsFiniteTypeOnAffine (transitionGradedModule I F) := by
  classical
  intro U
  obtain ⟨G, hG⟩ := affineOpen_limit_finite_generators I F U
  let g (s : sectionsLimit F U.1) :
      Σ n : ℤ, ((transitionGradedModule I F).piece n).val.obj (op U.1) :=
    ⟨0, transitionMk I F U 0 (associatedGradedDegreeZero (I.ideal U) s)⟩
  refine ⟨G.image g, fun n => ?_⟩
  by_cases hn : n < 0
  · refine top_unique fun x _ => ?_
    rw [sections_eq_zero _ (transitionKernelPiece_negative F n hn) _ x]
    exact AddSubgroup.zero_mem _
  lift n to ℕ using le_of_not_gt hn
  let H := AddSubgroup.closure
    { t : ((transitionGradedModule I F).piece (n : ℤ)).val.obj (op U.1) |
      ∃ s : Σ d : ℤ, ((transitionGradedModule I F).piece d).val.obj (op U.1),
        s ∈ G.image g ∧ ∃ (m : ℤ) (a : ((conormalPushforward I).piece m).val.obj (op U.1))
          (h : s.1 + m = (n : ℤ)),
          t = h ▸ (transitionGradedModule I F).smul s.1 m (op U.1) s.2 a }
  let e := (affineOpenTransitionSectionsEquiv I F U n).symm
  have hle : AddSubgroup.closure
        {x : AssociatedGraded.piece (M := sectionsLimit F U.1) (I.ideal U) n |
          ∃ s ∈ G, ∃ a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n,
            x = gradedScale (I.ideal U) n a s} ≤
      H.comap e.toAddMonoidHom := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨s, hs, a, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨g s, Finset.mem_image.mpr ⟨s, hs, rfl⟩,
      (n : ℤ), conormalLocalMap I U n a, zero_add _, ?_⟩
    have hh := transitionGradedModule_affineAction I F 0 n U (g s).2
      (conormalLocalMap I U n a)
    have hm : (affineOpenTransitionSectionsEquiv I F U 0) (g s).2 =
        AssociatedGraded.mk (I.ideal U) 0 (associatedGradedDegreeZero (I.ideal U) s) :=
      (affineOpenTransitionSectionsEquiv I F U 0).apply_symm_apply _
    rw [hm, conormalPieceAddEquiv_localMap] at hh
    have hh' : HEq ((affineOpenTransitionSectionsEquiv I F U (0 + n))
        ((transitionGradedModule I F).smul 0 (n : ℤ) (op U.1) (g s).2
          (conormalLocalMap I U n a)))
        (gradedScale (I.ideal U) n a s) :=
      hh.trans (homogeneousSMul_degreeZero_heq (I.ideal U) n a s)
    refine eq_of_heq (heq_eqRec_iff.mpr ?_)
    exact equiv_symm_heq (fun k => (affineOpenTransitionSectionsEquiv I F U k).toEquiv)
      (Nat.zero_add n) _ _ hh'
  rw [hG n] at hle
  refine top_unique fun x _ => ?_
  have hx : e (e.symm x) ∈ H := hle (show e.symm x ∈ (⊤ : AddSubgroup _) from trivial)
  exact Eq.subst (motive := fun z => z ∈ H) (e.apply_symm_apply x) hx

/-- **Stacks Project, Tag 087Z.** For a Noetherian scheme `X` and a quasi-coherent sheaf of
ideals `ℐ`, the transition kernels of an object of `Coh(X, ℐ)` form a finite type, graded,
quasi-coherent module over the associated graded algebra `⨁ ℐ ⁿ / ℐ ⁿ⁺¹`. -/
@[stacks 087Z]
public theorem finiteTypeAssociatedGradedData {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) :
    Nonempty (AssociatedGradedData I F) :=
  ⟨{ algebra := conormalPushforward I
     module := transitionGradedModule I F
     algebraPiece n U := conormalPieceAddEquiv I U n
     algebraPiece_smul n U r a := (conormalPieceEquiv I U n).map_smul r a
     algebraMul n m U a b := conormalPieceEquiv_mul I U n m a b
     algebraRestrictionPower n U V h a := idealPower_restrict_mem I n U V h a
     algebraRestriction n U V h := conormalRestriction I n U V h
     algebraRestriction_mk n U V h a := conormalRestriction_mk I n U V h a
     algebraPiece_naturality n U V h a := conormalPieceEquiv_naturality I n U V h a
     algebraNegative n hn := conormalPushforward_negative I n hn
     algebraQuasicoherent n := conormalPushforward_quasicoherent I n
     modulePieceZero := Iso.refl _
     modulePieceSucc _ := Iso.refl _
     moduleAffinePiece n U := affineOpenTransitionSectionsEquiv I F U n
     moduleAffineZero U a x h := affineOpenTransitionZero_mk I F U a x h
     moduleAffineSucc n U a x h := affineOpenTransitionSucc_mk I F U n a x h
     moduleAffineAction n m U x a := transitionGradedModule_affineAction I F n m U x a
     moduleNegative n hn := transitionKernelPiece_negative F n hn
     moduleQuasicoherent n := transitionKernelPiece_isQuasicoherent F n
     finiteType := transitionGradedModule_finiteType I F }⟩

end Stacks.Coherent

end
