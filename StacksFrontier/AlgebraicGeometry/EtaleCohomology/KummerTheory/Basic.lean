module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.RootsOfUnity
public import StacksCore.Tactic.StacksAttribute

/-!
# Isomorphisms of trivialized powers of invertible sheaves

An isomorphism between two invertible sheaves with trivialized `n`th powers is an isomorphism of
sheaves compatible with the trivializations. If one exists, their isomorphisms form a torsor
under the global `n`th roots of unity.

## Main definitions

* `AlgebraicGeometry.TrivializedPower` is an invertible sheaf with a trivialization of its `n`th
  tensor power.
* `AlgebraicGeometry.PairIso` is an isomorphism respecting these trivializations.
* `AlgebraicGeometry.IsScalarTranslate` says that one pair isomorphism is a given scalar multiple
  of another.
* `AlgebraicGeometry.tensorPowerMap` is the tensor power of an isomorphism of sheaves, and
  `AlgebraicGeometry.scalarEnd` and `AlgebraicGeometry.scalarIso` are the endomorphism and the
  automorphism given by a global section and a global unit.
* `AlgebraicGeometry.structureSheafTensorPowerIso` trivializes every natural tensor power of the
  structure sheaf, and `AlgebraicGeometry.unitPair` is the pair given by the structure sheaf
  together with multiplication by a global unit.

## Main results

* `AlgebraicGeometry.pairIso_torsor` says each pair isomorphism is uniquely a scalar multiple of
  a chosen one.
* `AlgebraicGeometry.scalarTranslate_pairIso` says every global root of unity gives exactly one
  such scalar multiple, which is an isomorphism of pairs.
* `AlgebraicGeometry.pairIso_unitPair_iff` says two pairs whose invertible sheaf is the structure
  sheaf are isomorphic exactly when their trivializing units differ by the `n`th power of a
  global unit.

## Implementation notes

Tensor powers are those of Stacks Project Tag 01CU. Their successor comparisons define the power
of an isomorphism recursively. Scalar multiplication is fixed sectionwise by the natural
endomorphism arising from a global section, rather than by an unspecified torsor action. The two
results make scalar translation a bijection once a pair isomorphism is chosen. Without one, the
type of pair isomorphisms is empty.

## References

* [Stacks Project, Tag 040P](https://stacks.math.columbia.edu/tag/040P)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules (terminalSectionToEnd terminalSectionToEnd_apply)

namespace AlgebraicGeometry

universe u

/-- The structure presheaf of rings of a scheme is a sheaf, at the spelling the
tensor-power and invertible-sheaf API asks for. Naming this proof keeps the projection
`S.ringCatSheaf.property` out of proof goals, where it cannot be type-checked without
unfolding `TopCat.Sheaf`. -/
public theorem ringSheafCond (S : Scheme.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥S)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf S.presheaf) :=
  S.ringCatSheaf.2

/-- The structure sheaf of rings of a scheme, at the spelling the sheaf-of-modules and
tensor-power API is stated over. It is `S.ringCatSheaf`, but presented as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of the structure presheaf, so that a
  sheaf of modules over it
is accepted by that API without unfolding `TopCat.Sheaf`. -/
public abbrev ringSheaf (S : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology ↥S) RingCat.{u} :=
  Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf (ringSheafCond S)

/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- The tensor power of an isomorphism of sheaves. -/
public noncomputable def tensorPowerMap (S : Scheme.{u})
    {L M : SheafOfModules.{u} (ringSheaf S)}
    [IsInvertible S.presheaf (ringSheafCond S) L]
    [IsInvertible S.presheaf (ringSheafCond S) M]
    (e : L ≅ M) :
    (n : ℕ) →
      tensorPower S.presheaf (ringSheafCond S) L (n : ℤ) ≅
        tensorPower S.presheaf (ringSheafCond S) M (n : ℤ)
  | 0 => Iso.refl _
  | n + 1 =>
      (tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)).symm ≪≫
        tensorProductIso S.presheaf (ringSheafCond S)
          (tensorPowerMap S e n) e ≪≫
        tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ)

/-- An invertible sheaf together with a trivialization of its `n`th tensor power. -/
public structure TrivializedPower (S : Scheme.{u}) (n : ℕ) where
  /-- The underlying sheaf of modules. -/
  sheaf : SheafOfModules.{u} (ringSheaf S)
  /-- The underlying sheaf is invertible. -/
  invertible : IsInvertible S.presheaf (ringSheafCond S) sheaf
  /-- An isomorphism from the `n`th tensor power of `sheaf` to the structure sheaf. -/
  trivialization : tensorPower S.presheaf (ringSheafCond S)
      sheaf (n : ℤ) ≅ SheafOfModules.unit (ringSheaf S)

/-- Isomorphisms of pairs are isomorphisms of sheaves whose tensor powers
commute with the chosen trivializations. -/
public structure PairIso {S : Scheme.{u}} {n : ℕ}
    (P Q : TrivializedPower S n) where
  /-- The isomorphism of the underlying sheaves. -/
  sheafIso : P.sheaf ≅ Q.sheaf
  /-- The `n`th tensor power of `sheafIso` carries the trivialization of `P` to that of `Q`. -/
  compatible : letI := P.invertible
    letI := Q.invertible
    tensorPowerMap S sheafIso n ≪≫ Q.trivialization = P.trivialization

/-- A pair isomorphism is the scalar translate of another when its underlying
sheaf map is obtained by multiplication by the specified global root of unity. -/
public def IsScalarTranslate {S : Scheme.{u}} {n : ℕ}
    {P Q : TrivializedPower S n} (a :
      (AlgebraicGeometry.rootsOfUnitySections n).obj (Opposite.op S))
    (φ ψ : PairIso P Q) : Prop :=
  ψ.sheafIso.hom =
    (terminalSectionToEnd (ringSheaf S) ⊤
      Limits.isTerminalTop a.1.val).asHom.app P.sheaf ≫ φ.sheafIso.hom

/-- Multiplication by a global section of the structure sheaf, as an endomorphism of a sheaf of
modules. -/
public noncomputable def scalarEnd (S : Scheme.{u})
    (s : Scheme.Γ.obj (Opposite.op S))
    (M : SheafOfModules (ringSheaf S)) : M ⟶ M :=
  (terminalSectionToEnd (ringSheaf S) ⊤
    Limits.isTerminalTop s).asHom.app M

/-- Multiplication by a global section commutes with every morphism of sheaves of modules. -/
private theorem scalarEnd_comp_comm (S : Scheme.{u}) (s : Scheme.Γ.obj (Opposite.op S))
    {M N : SheafOfModules (ringSheaf S)} (e : M ⟶ N) :
    e ≫ scalarEnd S s N = scalarEnd S s M ≫ e :=
  (terminalSectionToEnd (ringSheaf S) ⊤ Limits.isTerminalTop s).asHom.naturality e

private theorem scalarEnd_mul (S : Scheme.{u}) (s t : Scheme.Γ.obj (Opposite.op S))
    (M : SheafOfModules (ringSheaf S)) :
    scalarEnd S s M ≫ scalarEnd S t M = scalarEnd S (s * t) M := by
  ext U x
  let ρ := ((ringSheaf S).obj.map (Limits.isTerminalTop.from U.unop).op).hom
  change ρ t • (ρ s • x) = ρ (s * t) • x
  exact (smul_smul (ρ t) (ρ s) x).trans
    (congrArg (fun r => r • x)
      ((map_mul ρ t s).symm.trans (congrArg ρ (mul_comm t s))))

/-- Multiplication by a global unit of the structure sheaf, as an automorphism of a sheaf of
modules. -/
public noncomputable def scalarIso (S : Scheme.{u}) (a : (Scheme.Γ.obj (Opposite.op S))ˣ)
    (M : SheafOfModules (ringSheaf S)) : M ≅ M where
  hom := scalarEnd S a.val M
  inv := scalarEnd S a⁻¹.val M
  hom_inv_id := by
    rw [scalarEnd_mul]
    have h : a.val * a⁻¹.val = (1 : Scheme.Γ.obj (Opposite.op S)) := by
      exact Units.mul_inv a
    rw [h]
    ext U x
    change ((ringSheaf S).obj.map
      (Limits.isTerminalTop.from U.unop).op).hom 1 • x = x
    rw [map_one, one_smul]
  inv_hom_id := by
    rw [scalarEnd_mul]
    have h : a⁻¹.val * a.val = (1 : Scheme.Γ.obj (Opposite.op S)) := by
      exact Units.inv_mul a
    rw [h]
    ext U x
    change ((ringSheaf S).obj.map
      (Limits.isTerminalTop.from U.unop).op).hom 1 • x = x
    rw [map_one, one_smul]

private theorem scalarEnd_one (S : Scheme.{u}) (M : SheafOfModules (ringSheaf S)) :
    scalarEnd S 1 M = 𝟙 M := by
  change (terminalSectionToEnd (ringSheaf S) ⊤
    Limits.isTerminalTop 1).asHom.app M = 𝟙 M
  ext U x
  change ((ringSheaf S).obj.map
    (Limits.isTerminalTop.from U.unop).op).hom 1 • x = x
  rw [map_one, one_smul]

private theorem scalarIso_one (S : Scheme.{u}) (M : SheafOfModules (ringSheaf S)) :
    scalarIso S 1 M = Iso.refl M :=
  Iso.ext (scalarEnd_one S M)

private noncomputable def scalarOfUnitEnd (S : Scheme.{u})
    (g : SheafOfModules.unit (ringSheaf S) ⟶
      SheafOfModules.unit (ringSheaf S)) :
    Scheme.Γ.obj (Opposite.op S) :=
  (SheafOfModules.unitHomEquiv (SheafOfModules.unit (ringSheaf S)) g).val
    (Opposite.op (⊤ : TopologicalSpace.Opens S))

private theorem unitEnd_eq_scalar (S : Scheme.{u})
    (g : SheafOfModules.unit (ringSheaf S) ⟶
      SheafOfModules.unit (ringSheaf S)) :
    g = scalarEnd S (scalarOfUnitEnd S g) (SheafOfModules.unit (ringSheaf S)) := by
  apply (SheafOfModules.unitHomEquiv (SheafOfModules.unit (ringSheaf S))).injective
  ext U
  change (SheafOfModules.unitHomEquiv
    (SheafOfModules.unit (ringSheaf S)) g).val U =
    ((((terminalSectionToEnd (ringSheaf S) ⊤
      Limits.isTerminalTop (scalarOfUnitEnd S g)).asHom.app
      (SheafOfModules.unit (ringSheaf S))).val.app U).hom
      (1 : (ringSheaf S).obj.obj U))
  rw [← (SheafOfModules.unitHomEquiv
    (SheafOfModules.unit (ringSheaf S)) g).property
      (Limits.isTerminalTop.from U.unop).op]
  change ((ringSheaf S).obj.map
      (Limits.isTerminalTop.from U.unop).op).hom
        ((g.val.app (Opposite.op ⊤)).hom
          (1 : (ringSheaf S).obj.obj (Opposite.op ⊤))) =
    ((ringSheaf S).obj.map
      (Limits.isTerminalTop.from U.unop).op).hom
        ((g.val.app (Opposite.op ⊤)).hom
          (1 : (ringSheaf S).obj.obj (Opposite.op ⊤))) •
          (1 : (ringSheaf S).obj.obj U)
  rw [smul_eq_mul, mul_one]

private theorem scalarOfUnitEnd_scalarEnd (S : Scheme.{u})
    (s : Scheme.Γ.obj (Opposite.op S)) :
    scalarOfUnitEnd S (scalarEnd S s (SheafOfModules.unit (ringSheaf S))) = s := by
  simp only [scalarOfUnitEnd]
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  let U : (TopologicalSpace.Opens S)ᵒᵖ := Opposite.op ⊤
  let R := (S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U
  let sR : ↑R := s
  let : CommRing ↑(S.presheaf.obj U) := inferInstance
  let : CommRing ↑R := inferInstance
  let : Module ↑R ((SheafOfModules.unit (ringSheaf S)).val.obj U) := by
    change Module ↑((ringSheaf S).obj.obj U)
      ((SheafOfModules.unit (ringSheaf S)).val.obj U)
    infer_instance
  let rho : ↑(S.presheaf.obj U) →+* ↑R :=
    { toFun := id
      map_one' := rfl
      map_mul' := by intro x y; simp
      map_zero' := rfl
      map_add' := by intro x y; simp }
  let : Module ↑(S.presheaf.obj U) ↑R :=
    Module.compHom (M := ↑R) rho
  change (S.presheaf.map (Limits.isTerminalTop.from ⊤).op).hom s •
    (1 : ↑R) = s
  have hfrom : Limits.isTerminalTop.from (⊤ : TopologicalSpace.Opens S) = 𝟙 _ := by
    apply Limits.isTerminalTop.hom_ext
  have hres : (S.presheaf.map (Limits.isTerminalTop.from ⊤).op).hom sR = sR := by
    rw [hfrom]
    simp
  rw [hres]
  change rho sR * (1 : ↑R) = sR
  simp [rho]

private theorem tensorLeft_map_scalar_unit (S : Scheme.{u})
    (L : SheafOfModules (ringSheaf S))
    (N : SheafOfModules (ringSheaf S))
    (s : Scheme.Γ.obj (Opposite.op S)) :
    let F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
        (ringSheafCond S)⟩).obj L
    F.map (scalarEnd S s N) =
      scalarEnd S s (F.obj N) := by
  classical
  let : MonoidalCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf S.presheaf)) := by
    infer_instance
  let : MonoidalCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf (ringSheafCond S)).obj)
        :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := S.presheaf)
  let : MonoidalCategory (PresheafOfModules.{u} (ringSheaf S).obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := S.presheaf)
  let : MonoidalCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf S.presheaf)) :=
        inferInstance
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
      (ringSheafCond S)⟩).obj L
  let a := tensorLeftFunctorUniversal S.presheaf (ringSheafCond S) L
  apply (a.bijective (N)
    (F.obj (N))).injective
  have hn := a.ι.naturality (scalarEnd S s (N))
  change (SheafOfModules.forget (ringSheaf S) ⋙ tensorLeft L.val).map
        (scalarEnd S s (N)) ≫
      a.ι.app (N) =
      a.ι.app (N) ≫
      (F ⋙ SheafOfModules.forget (ringSheaf S)).map
        (scalarEnd S s (N)) at hn
  change (SheafOfModules.forget (ringSheaf S) ⋙ tensorLeft L.val).map
        (scalarEnd S s (N)) ≫
      a.ι.app (N) =
    a.ι.app (N) ≫
      (SheafOfModules.forget (ringSheaf S)).map
        (F.map (scalarEnd S s (N))) at hn
  change a.ι.app (N) ≫
      (SheafOfModules.forget (ringSheaf S)).map
        (F.map (scalarEnd S s (N))) =
    a.ι.app (N) ≫
      (SheafOfModules.forget (ringSheaf S)).map
        (scalarEnd S s (F.obj (N)))
  rw [← hn]
  apply PresheafOfModules.Hom.ext
  funext U
  let : IsMulCommutative ↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) :=
    inferInstanceAs (IsMulCommutative ↑((ringSheaf S).obj.obj U))
  let : CommRing ↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) := inferInstance
  let : Module ↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) (L.val.obj U) :=
    inferInstanceAs (Module ↑((ringSheaf S).obj.obj U) (L.val.obj U))
  let : Module ↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) (N.val.obj U) :=
    inferInstanceAs (Module ↑((ringSheaf S).obj.obj U) (N.val.obj U))
  let : Module ↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
      ((F.obj N).val.obj U) :=
    ((F.obj N).val.obj U).isModule
  let : Module ↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
      (((F ⋙ SheafOfModules.forget (ringSheaf S)).obj N).obj U) :=
    ((F.obj N).val.obj U).isModule
  let : Module ↑(S.presheaf.obj U) (L.val.obj U) :=
    inferInstanceAs (Module ↑((ringSheaf S).obj.obj U) (L.val.obj U))
  let : Module ↑(S.presheaf.obj U) (N.val.obj U) :=
    inferInstanceAs (Module ↑((ringSheaf S).obj.obj U) (N.val.obj U))
  let tmap := ((tensorLeft L.val).map
    ((SheafOfModules.forget (ringSheaf S)).map (scalarEnd S s (N)))).app U
  let iota := (a.ι.app (N)).app U
  let zmap := (scalarEnd S s (F.obj (N))).val.app U
  let σ : ↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) :=
    ((S.presheaf ⋙ forget₂ CommRingCat RingCat).map
      (Limits.isTerminalTop.from U.unop).op).hom s
  have hs (r : (N).val.obj U) :
      ((scalarEnd S s (N)).val.app U) r = σ • r :=
    rfl
  have hsF (z : (F.obj (N)).val.obj U) : zmap z = σ • z :=
    rfl
  have hmul (m : L.val.obj U) (r : (N).val.obj U) :
      tmap (m ⊗ₜ r) = m ⊗ₜ ((scalarEnd S s (N)).val.app U) r :=
    rfl
  have htmul (m : L.val.obj U) (r : (N).val.obj U) :
      m ⊗ₜ[↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)] (σ • r) =
        σ • (m ⊗ₜ[↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)] r) :=
    map_smul (TensorProduct.mk _ ↑(L.val.obj U) ↑((N).val.obj U) m) σ r
  apply ModuleCat.hom_ext
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m r =>
      change iota (tmap (m ⊗ₜ r)) = zmap (iota (m ⊗ₜ r))
      rw [hmul m r, hs r]
      exact (congrArg (fun w => iota w) (htmul m r)).trans
        ((map_smul (ConcreteCategory.hom iota) σ
            (m ⊗ₜ[↑((S.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)] r)).trans
          (hsF _).symm)
  | add x y hx hy =>
      change iota (tmap (x + y)) = zmap (iota (x + y))
      change iota (tmap x) = zmap (iota x) at hx
      change iota (tmap y) = zmap (iota y) at hy
      have e1 : iota (tmap (x + y)) = iota (tmap x) + iota (tmap y) :=
        (congrArg (fun w => iota w)
            (map_add (ConcreteCategory.hom tmap) x y)).trans
          (map_add (ConcreteCategory.hom iota) (tmap x) (tmap y))
      have e2 : zmap (iota (x + y)) = zmap (iota x) + zmap (iota y) :=
        (congrArg (fun w => zmap w)
            (map_add (ConcreteCategory.hom iota) x y)).trans
          (map_add (ConcreteCategory.hom zmap) (iota x) (iota y))
      exact e1.trans
        (((congrArg (fun w => w + iota (tmap y)) hx).trans
          (congrArg (fun w => zmap (iota x) + w) hy)).trans e2.symm)

private theorem tensorProductIso_scalar_second (S : Scheme.{u})
    (M N : SheafOfModules (ringSheaf S))
    (a : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    (tensorProductIso S.presheaf (ringSheafCond S)
      (Iso.refl M) (scalarIso S a N)).hom =
        scalarEnd S a.val ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.presheaf) (forget₂ CommRingCat RingCat)
              ((ringSheafCond S))⟩).obj (M)).obj (N))) := by
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
      (ringSheafCond S)⟩).obj M
  change F.map (scalarEnd S a.val N) = scalarEnd S a.val (F.obj N)
  exact tensorLeft_map_scalar_unit S M N a.val

private theorem tensorProductIso_scalar_first (S : Scheme.{u})
    (M N : SheafOfModules (ringSheaf S))
    (a : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    (tensorProductIso S.presheaf (ringSheafCond S)
      (scalarIso S a M) (Iso.refl N)).hom =
        scalarEnd S a.val ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.presheaf) (forget₂ CommRingCat RingCat)
              ((ringSheafCond S))⟩).obj (M)).obj (N))) := by
  let : MonoidalCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf (ringSheafCond S)).obj)
        :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := S.presheaf)
  let : MonoidalCategory (PresheafOfModules.{u} (ringSheaf S).obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := S.presheaf)
  let : SymmetricCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf (ringSheafCond S)).obj)
        :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := S.presheaf)
  let : SymmetricCategory (PresheafOfModules.{u} (ringSheaf S).obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := S.presheaf)
  let β := tensorProductBraiding S.presheaf (ringSheafCond S) M N
  let e := tensorProductIso S.presheaf (ringSheafCond S)
    (scalarIso S a M) (Iso.refl N)
  let f := tensorProductIso S.presheaf (ringSheafCond S)
    (Iso.refl N) (scalarIso S a M)
  have hmove : e.hom ≫ β.hom = β.hom ≫ f.hom := by
    let MV : PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf (ringSheafCond S)).obj
        := M.val
    let NV : PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf (ringSheafCond S)).obj
        := N.val
    let g : MV ⟶ MV := (SheafOfModules.forget
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf (ringSheafCond S))).map
        (scalarEnd S a.val M)
    change (Stacks.SheafOfModules.TensorSheafification.sheafify S.presheaf (ringSheafCond S)).map
        (g ⊗ₘ (𝟙 NV)) ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify S.presheaf (ringSheafCond S)).map (β_
          MV NV).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify S.presheaf (ringSheafCond S)).map (β_ MV
        NV).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify S.presheaf (ringSheafCond S)).map ((𝟙
          NV) ⊗ₘ g)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Stacks.SheafOfModules.TensorSheafification.sheafify S.presheaf (ringSheafCond
      S)).map
      (BraidedCategory.braiding_naturality
        (C := PresheafOfModules (ringSheaf S).obj)
        (scalarEnd S a.val M).val (𝟙 N.val))
  have hsecond := tensorProductIso_scalar_second S N M a
  have hnat' := scalarEnd_comp_comm S a.val β.hom
  have hmove' := hmove
  rw [hsecond] at hmove'
  exact (cancel_mono β.hom).mp (hmove'.trans hnat')

private theorem tensorProductIso_trans (S : Scheme.{u})
    {L M N L' M' N' : SheafOfModules (ringSheaf S)}
    (e : L ≅ M) (f : M ≅ N) (e' : L' ≅ M') (f' : M' ≅ N') :
    tensorProductIso S.presheaf (ringSheafCond S) (e ≪≫ f) (e' ≪≫ f') =
      tensorProductIso S.presheaf (ringSheafCond S) e e' ≪≫
        tensorProductIso S.presheaf (ringSheafCond S) f f' := by
  let B := tensorProductBifunctor S.presheaf (ringSheafCond S)
  have hp : (e ≪≫ f).prod (e' ≪≫ f') = e.prod e' ≪≫ f.prod f' := by
    ext <;> simp
  change B.mapIso ((e ≪≫ f).prod (e' ≪≫ f')) =
    B.mapIso (e.prod e') ≪≫ B.mapIso (f.prod f')
  exact (congrArg B.mapIso hp).trans (Functor.mapIso_trans B _ _)

private theorem tensorProductIso_scalar_both (S : Scheme.{u})
    (M N : SheafOfModules (ringSheaf S))
    (a b : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    (tensorProductIso S.presheaf (ringSheafCond S)
      (scalarIso S a M) (scalarIso S b N)).hom =
        scalarEnd S (a.val * b.val)
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ (S.presheaf) (forget₂ CommRingCat RingCat)
                ((ringSheafCond S))⟩).obj (M)).obj (N)))
            := by
  have hdecomp := congrArg Iso.hom (tensorProductIso_trans S (scalarIso S a M) (Iso.refl M)
    (Iso.refl N) (scalarIso S b N))
  simp only [Iso.trans_refl, Iso.refl_trans, Iso.trans_hom] at hdecomp
  have hfac :
      (tensorProductIso S.presheaf (ringSheafCond S)
        (scalarIso S a M) (Iso.refl N)).hom ≫
      (tensorProductIso S.presheaf (ringSheafCond S)
        (Iso.refl M) (scalarIso S b N)).hom =
      scalarEnd S a.val ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (S.presheaf) (forget₂ CommRingCat RingCat)
            ((ringSheafCond S))⟩).obj (M)).obj (N))) ≫
        scalarEnd S b.val ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ (S.presheaf) (forget₂ CommRingCat RingCat)
              ((ringSheafCond S))⟩).obj (M)).obj (N))) :=
    congrArg₂ (fun firstMap secondMap => firstMap ≫ secondMap)
      (tensorProductIso_scalar_first S M N a)
      (tensorProductIso_scalar_second S M N b)
  exact hdecomp.trans (hfac.trans (scalarEnd_mul S a.val b.val _))

private theorem tensorPowerMap_scalar (S : Scheme.{u})
    (L : SheafOfModules (ringSheaf S))
    [IsInvertible S.presheaf (ringSheafCond S) L]
    (a : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    ∀ n : ℕ,
      tensorPowerMap S (scalarIso S a L) n =
        scalarIso S (a ^ n)
          (tensorPower S.presheaf (ringSheafCond S) L (n : ℤ)) := by
  intro n
  induction n with
  | zero =>
      rw [tensorPowerMap, pow_zero]
      exact (scalarIso_one S
        (tensorPower S.presheaf (ringSheafCond S) L (0 : ℤ))).symm
  | succ n ih =>
      let E := tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)
      have hp : (a ^ n).val * a.val = (a ^ (n + 1)).val := by
        rw [pow_succ, Units.val_mul]
      have hboth := tensorProductIso_scalar_both S
        (tensorPower S.presheaf (ringSheafCond S) L (n : ℤ)) L (a ^ n) a
      have hnat' := (scalarEnd_comp_comm S (a ^ (n + 1)).val E.hom).symm
      apply Iso.ext
      change E.inv ≫
          (tensorProductIso S.presheaf (ringSheafCond S)
            (tensorPowerMap S (scalarIso S a L) n) (scalarIso S a L)).hom ≫ E.hom =
        scalarEnd S (a ^ (n + 1)).val
          (tensorPower S.presheaf (ringSheafCond S) L ((n + 1 : ℕ) : ℤ))
      rw [ih, hboth, hp]
      exact (congrArg (fun f => E.inv ≫ f) hnat').trans (E.inv_hom_id_assoc _)

private noncomputable def tensorLeftUnitIso (S : Scheme.{u})
    (L : SheafOfModules (ringSheaf S)) :
    let F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
        (ringSheafCond S)⟩).obj L
    F.obj (SheafOfModules.unit (ringSheaf S)) ≅ L := by
  exact tensorProductRightUnitor S.presheaf (ringSheafCond S) L

private theorem existsUnique_scalarEnd (S : Scheme.{u})
    (P : SheafOfModules (ringSheaf S))
    [IsInvertible S.presheaf (ringSheafCond S) P]
    (f : P ⟶ P) :
    ∃! s : Scheme.Γ.obj (Opposite.op S), scalarEnd S s P = f := by
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
      (ringSheafCond S)⟩).obj P
  let : F.IsEquivalence :=
    tensorLeftFunctor_isEquivalence S.presheaf (ringSheafCond S) P
  let e := tensorLeftUnitIso S P
  let gP := e.hom ≫ f ≫ e.inv
  let g : SheafOfModules.unit (ringSheaf S) ⟶
      SheafOfModules.unit (ringSheaf S) := F.preimage gP
  let s := scalarOfUnitEnd S g
  have hmap : F.map (scalarEnd S s (SheafOfModules.unit (ringSheaf S))) =
      e.hom ≫ f ≫ e.inv :=
    (congrArg F.map (unitEnd_eq_scalar S g).symm).trans (F.map_preimage gP)
  have htensor : F.map (scalarEnd S s (SheafOfModules.unit (ringSheaf S))) =
      scalarEnd S s (F.obj (SheafOfModules.unit (ringSheaf S))) :=
    tensorLeft_map_scalar_unit S P (SheafOfModules.unit (ringSheaf S)) s
  have hn := scalarEnd_comp_comm S s e.hom
  have hs : scalarEnd S s P = f := by
    have hcomp : e.hom ≫ scalarEnd S s P = e.hom ≫ f := by
      refine hn.trans ((congrArg (fun k => k ≫ e.hom) htensor.symm).trans ?_)
      rw [hmap]
      exact (Category.assoc _ _ _).trans (congrArg (fun k => e.hom ≫ k)
        ((Category.assoc _ _ _).trans ((congrArg (fun k => f ≫ k) e.inv_hom_id).trans
          (Category.comp_id f))))
    exact (e.cancel_iso_hom_left _ _).1 hcomp
  refine ⟨s, hs, ?_⟩
  intro t ht
  have hnat := scalarEnd_comp_comm S t e.hom
  have heq : scalarEnd S s (F.obj (SheafOfModules.unit (ringSheaf S))) =
      scalarEnd S t (F.obj (SheafOfModules.unit (ringSheaf S))) := by
    have h : scalarEnd S s (F.obj (SheafOfModules.unit (ringSheaf S))) ≫ e.hom =
        scalarEnd S t (F.obj (SheafOfModules.unit (ringSheaf S))) ≫ e.hom :=
      hn.symm.trans ((congrArg (fun k => e.hom ≫ k) (hs.trans ht.symm)).trans hnat)
    exact (Iso.cancel_iso_hom_right _ _ e).1 h
  have hunit : scalarEnd S s (SheafOfModules.unit (ringSheaf S)) =
      scalarEnd S t (SheafOfModules.unit (ringSheaf S)) := by
    apply F.map_injective
    rw [tensorLeft_map_scalar_unit, tensorLeft_map_scalar_unit]
    exact heq
  symm
  calc
    s = scalarOfUnitEnd S (scalarEnd S s (SheafOfModules.unit (ringSheaf S))) :=
      (scalarOfUnitEnd_scalarEnd S s).symm
    _ = scalarOfUnitEnd S (scalarEnd S t (SheafOfModules.unit (ringSheaf S))) :=
      congrArg (scalarOfUnitEnd S) hunit
    _ = t := scalarOfUnitEnd_scalarEnd S t

private theorem scalarEnd_injective (S : Scheme.{u})
    (L : SheafOfModules (ringSheaf S))
    [IsInvertible S.presheaf (ringSheafCond S) L] :
    Function.Injective (fun s => scalarEnd S s L) := by
  intro s t h
  obtain ⟨r, hr, hu⟩ := existsUnique_scalarEnd S L (scalarEnd S t L)
  exact (hu s h).trans (hu t rfl).symm

private theorem exists_scalarIso (S : Scheme.{u})
    (L : SheafOfModules (ringSheaf S))
    [IsInvertible S.presheaf (ringSheafCond S) L]
    (e : L ≅ L) :
    ∃ a : (Scheme.Γ.obj (Opposite.op S))ˣ, scalarIso S a L = e := by
  obtain ⟨s, hs, _⟩ := existsUnique_scalarEnd S L e.hom
  obtain ⟨t, ht, _⟩ := existsUnique_scalarEnd S L e.inv
  have hst : s * t = 1 := scalarEnd_injective S L (by
    calc
      scalarEnd S (s * t) L = scalarEnd S s L ≫ scalarEnd S t L :=
        (scalarEnd_mul S s t L).symm
      _ = e.hom ≫ e.inv := congrArg₂ (fun f g : L ⟶ L => f ≫ g) hs ht
      _ = scalarEnd S 1 L := e.hom_inv_id.trans (scalarEnd_one S L).symm)
  exact ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, Iso.ext hs⟩

private theorem tensorPowerMap_trans (S : Scheme.{u})
    {L M N : SheafOfModules (ringSheaf S)}
    [IsInvertible S.presheaf (ringSheafCond S) L]
    [IsInvertible S.presheaf (ringSheafCond S) M]
    [IsInvertible S.presheaf (ringSheafCond S) N]
    (e : L ≅ M) (f : M ≅ N) (n : ℕ) :
    tensorPowerMap S (e ≪≫ f) n =
      tensorPowerMap S e n ≪≫ tensorPowerMap S f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht := tensorProductIso_trans S (tensorPowerMap S e n)
      (tensorPowerMap S f n) e f
    simp only [tensorPowerMap, ih]
    refine Eq.trans (congrArg (fun z =>
      (tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)).symm ≪≫
        z ≪≫ tensorPowerSuccIso S.presheaf (ringSheafCond S) N (n : ℤ)) ht) ?_
    have leftAssoc := congrArg
      (fun middle =>
        (tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)).symm ≪≫ middle)
      (Iso.trans_assoc
        (tensorProductIso S.presheaf (ringSheafCond S) (tensorPowerMap S e n) e)
        (tensorProductIso S.presheaf (ringSheafCond S) (tensorPowerMap S f n) f)
        (tensorPowerSuccIso S.presheaf (ringSheafCond S) N (n : ℤ)))
    have rightAssoc :=
      (Iso.trans_assoc
        (tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)).symm
        (tensorProductIso S.presheaf (ringSheafCond S) (tensorPowerMap S e n) e ≪≫
          tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ))
        ((tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ)).symm ≪≫
          tensorProductIso S.presheaf (ringSheafCond S) (tensorPowerMap S f n) f ≪≫
            tensorPowerSuccIso S.presheaf (ringSheafCond S) N (n : ℤ))).trans
        (congrArg
          (fun middle =>
            (tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)).symm ≪≫ middle)
          ((Iso.trans_assoc
            (tensorProductIso S.presheaf (ringSheafCond S) (tensorPowerMap S e n) e)
            (tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ))
            ((tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ)).symm ≪≫
              tensorProductIso S.presheaf (ringSheafCond S) (tensorPowerMap S f n) f ≪≫
                tensorPowerSuccIso S.presheaf (ringSheafCond S) N (n : ℤ))).trans
            (congrArg
              (fun tailIso =>
                tensorProductIso S.presheaf (ringSheafCond S)
                  (tensorPowerMap S e n) e ≪≫ tailIso)
              (Iso.self_symm_id_assoc
                (tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ))
                (tensorProductIso S.presheaf (ringSheafCond S) (tensorPowerMap S f n) f ≪≫
                  tensorPowerSuccIso S.presheaf (ringSheafCond S) N (n : ℤ))))))
    exact leftAssoc.trans rightAssoc.symm

private theorem pairIso_ext {S : Scheme.{u}} {n : ℕ}
    {P Q : TrivializedPower S n} {φ ψ : PairIso P Q}
    (h : φ.sheafIso.hom = ψ.sheafIso.hom) : φ = ψ := by
  have he := Iso.ext h
  cases φ
  cases ψ
  cases he
  rfl

private theorem scalar_eq_one_of_comp (S : Scheme.{u})
    (L : SheafOfModules (ringSheaf S))
    (e : L ≅ SheafOfModules.unit (ringSheaf S))
    (s : Scheme.Γ.obj (Opposite.op S))
    (h : scalarEnd S s L ≫ e.hom = e.hom) : s = 1 := by
  have hn := scalarEnd_comp_comm S s e.hom
  have hu : scalarEnd S s (SheafOfModules.unit (ringSheaf S)) =
      scalarEnd S 1 (SheafOfModules.unit (ringSheaf S)) := by
    apply (cancel_epi e.hom).mp
    calc
      _ = scalarEnd S s L ≫ e.hom := hn
      _ = e.hom := h
      _ = _ := by rw [scalarEnd_one, Category.comp_id]
  exact (scalarOfUnitEnd_scalarEnd S s).symm.trans
    ((congrArg (scalarOfUnitEnd S) hu).trans (scalarOfUnitEnd_scalarEnd S 1))

/-- Once an isomorphism of pairs has been chosen, every other isomorphism is uniquely its scalar
translate by a global `n`th root of unity. -/
@[stacks 040P "every pair isomorphism is uniquely a scalar translate"]
public theorem pairIso_torsor (S : Scheme.{u}) (n : ℕ)
    (P Q : TrivializedPower S n) (φ : PairIso P Q) :
    ∀ ψ : PairIso P Q, ∃! a :
      (AlgebraicGeometry.rootsOfUnitySections n).obj (Opposite.op S),
      IsScalarTranslate a φ ψ := by
  let := P.invertible
  let := Q.invertible
  intro ψ
  obtain ⟨a, ha⟩ := exists_scalarIso S P.sheaf (ψ.sheafIso ≪≫ φ.sheafIso.symm)
  have he : scalarIso S a P.sheaf ≪≫ φ.sheafIso = ψ.sheafIso := by
    rw [ha]
    apply Iso.ext
    simp
  have hc : tensorPowerMap S (scalarIso S a P.sheaf) n ≪≫
      P.trivialization = P.trivialization := by
    calc
      _ = tensorPowerMap S (scalarIso S a P.sheaf) n ≪≫
          (tensorPowerMap S φ.sheafIso n ≪≫ Q.trivialization) := by
            rw [φ.compatible]
      _ = tensorPowerMap S ψ.sheafIso n ≪≫ Q.trivialization := by
        rw [← he, tensorPowerMap_trans, Iso.trans_assoc]
      _ = P.trivialization := ψ.compatible
  have hap : a ^ n = 1 := by
    apply Units.ext
    apply scalar_eq_one_of_comp S _ P.trivialization
    rw [tensorPowerMap_scalar S P.sheaf a n] at hc
    exact congrArg Iso.hom hc
  refine ⟨⟨a, hap⟩, (congrArg Iso.hom he).symm, fun b hb => ?_⟩
  apply Subtype.ext
  apply Units.ext
  apply scalarEnd_injective S P.sheaf
  apply (cancel_mono φ.sheafIso.hom).mp
  exact hb.symm.trans (congrArg Iso.hom he).symm

/-- Every global `n`th root of unity acts on a chosen isomorphism of pairs,
giving a unique isomorphism whose sheaf map is its specified scalar translate. -/
@[stacks 040P "every global root gives a unique pair isomorphism"]
public theorem scalarTranslate_pairIso (S : Scheme.{u}) (n : ℕ)
    (P Q : TrivializedPower S n) (φ : PairIso P Q) :
    ∀ a : (AlgebraicGeometry.rootsOfUnitySections n).obj (Opposite.op S),
      ∃! ψ : PairIso P Q, IsScalarTranslate a φ ψ := by
  let := P.invertible
  let := Q.invertible
  intro a
  let ψ : PairIso P Q :=
    { sheafIso := scalarIso S a.1 P.sheaf ≪≫ φ.sheafIso
      compatible := by
        rw [tensorPowerMap_trans, tensorPowerMap_scalar, a.2, scalarIso_one S]
        simpa using φ.compatible }
  exact ⟨ψ, rfl, fun _ hχ => pairIso_ext hχ⟩

/-- The structure sheaf of a scheme is invertible as a module over itself, in the spelling the
tensor-power API is stated over. -/
public instance isInvertible_unit (S : Scheme.{u}) :
    IsInvertible S.presheaf (ringSheafCond S) (SheafOfModules.unit (ringSheaf S)) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

/-- The canonical trivialization of every natural tensor power of the structure sheaf: start
from the identification of the zeroth power with the structure sheaf and iterate the successor
and right-unit constraints. -/
public noncomputable def structureSheafTensorPowerIso (S : Scheme.{u}) :
    (k : ℕ) →
      tensorPower S.presheaf (ringSheafCond S) (SheafOfModules.unit (ringSheaf S)) (k : ℤ) ≅
        SheafOfModules.unit (ringSheaf S)
  | 0 => Iso.refl _
  | k + 1 =>
      tensorPowerReindex S.presheaf (ringSheafCond S)
          (SheafOfModules.unit (ringSheaf S)) (by push_cast; ring) ≪≫
        (tensorPowerSuccIso S.presheaf (ringSheafCond S)
            (SheafOfModules.unit (ringSheaf S)) (k : ℤ)).symm ≪≫
        tensorProductIso S.presheaf (ringSheafCond S)
          (structureSheafTensorPowerIso S k) (Iso.refl (SheafOfModules.unit (ringSheaf S))) ≪≫
        tensorProductRightUnitor S.presheaf (ringSheafCond S)
          (SheafOfModules.unit (ringSheaf S))

/-- The pair consisting of the structure sheaf and the trivialization of its `n`th tensor power
given by multiplication by a global unit. -/
public noncomputable def unitPair (S : Scheme.{u}) (n : ℕ)
    (f : (Scheme.Γ.obj (Opposite.op S))ˣ) : TrivializedPower S n where
  sheaf := SheafOfModules.unit (ringSheaf S)
  invertible := isInvertible_unit S
  trivialization :=
    structureSheafTensorPowerIso S n ≪≫ scalarIso S f (SheafOfModules.unit (ringSheaf S))

/-- The invertible sheaf of a unit pair is the structure sheaf. -/
public theorem unitPair_sheaf (S : Scheme.{u}) (n : ℕ)
    (f : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    (unitPair S n f).sheaf = SheafOfModules.unit (ringSheaf S) :=
  rfl

/-- The trivialization of a unit pair is the canonical one followed by multiplication by the
chosen unit. -/
public theorem unitPair_trivialization (S : Scheme.{u}) (n : ℕ)
    (f : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    (unitPair S n f).trivialization =
      structureSheafTensorPowerIso S n ≪≫ scalarIso S f (SheafOfModules.unit (ringSheaf S)) :=
  rfl

/-- Multiplication by a unit is multiplication by its underlying section. -/
public theorem scalarIso_hom (S : Scheme.{u}) (a : (Scheme.Γ.obj (Opposite.op S))ˣ)
    (M : SheafOfModules (ringSheaf S)) :
    (scalarIso S a M).hom = scalarEnd S a.val M :=
  rfl

/-- Multiplication by a global section is natural in the sheaf of modules. -/
public theorem scalarEnd_naturality (S : Scheme.{u}) (s : Scheme.Γ.obj (Opposite.op S))
    {M N : SheafOfModules (ringSheaf S)} (e : M ⟶ N) :
    e ≫ scalarEnd S s N = scalarEnd S s M ≫ e :=
  scalarEnd_comp_comm S s e

private theorem unitPair_compatible_hom (S : Scheme.{u}) (n : ℕ)
    (g u : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    (tensorPowerMap S (scalarIso S u (SheafOfModules.unit (ringSheaf S))) n ≪≫
        (unitPair S n g).trivialization).hom =
      (structureSheafTensorPowerIso S n).hom ≫
        scalarEnd S ((u ^ n).val * g.val) (SheafOfModules.unit (ringSheaf S)) := by
  rw [tensorPowerMap_scalar S (SheafOfModules.unit (ringSheaf S)) u n,
    unitPair_trivialization, Iso.trans_hom, Iso.trans_hom, scalarIso_hom, scalarIso_hom,
    ← Category.assoc, ← scalarEnd_naturality S (u ^ n).val (structureSheafTensorPowerIso S n).hom,
    Category.assoc, scalarEnd_mul]

private theorem unitPair_compatible_iff (S : Scheme.{u}) (n : ℕ)
    (f g u : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    tensorPowerMap S (scalarIso S u (SheafOfModules.unit (ringSheaf S))) n ≪≫
        (unitPair S n g).trivialization = (unitPair S n f).trivialization ↔
      f = u ^ n * g := by
  have hR : (unitPair S n f).trivialization.hom =
      (structureSheafTensorPowerIso S n).hom ≫
        scalarEnd S f.val (SheafOfModules.unit (ringSheaf S)) := by
    rw [unitPair_trivialization, Iso.trans_hom, scalarIso_hom]
  constructor
  · intro h
    have h' := (unitPair_compatible_hom S n g u).symm.trans ((congrArg Iso.hom h).trans hR)
    have h'' := (cancel_epi (structureSheafTensorPowerIso S n).hom).mp h'
    apply Units.ext
    exact (scalarEnd_injective S (SheafOfModules.unit (ringSheaf S)) h'').symm
  · intro h
    apply Iso.ext
    refine (unitPair_compatible_hom S n g u).trans (hR.symm.trans ?_).symm
    exact congrArg (fun z => (structureSheafTensorPowerIso S n).hom ≫
      scalarEnd S z (SheafOfModules.unit (ringSheaf S)))
      (congrArg (fun z : (Scheme.Γ.obj (Opposite.op S))ˣ =>
        (z : Scheme.Γ.obj (Opposite.op S))) h)

/-- Two pairs whose invertible sheaf is the structure sheaf are isomorphic exactly when their
trivializing units differ by the `n`th power of a global unit; so the isomorphism classes of such
pairs are the global units modulo `n`th powers. -/
@[stacks 040Q "the pair side of the identification for pairs whose invertible sheaf is the \
structure sheaf: two such pairs are isomorphic exactly when their trivializing units agree \
modulo nth powers of global units, so the isomorphism classes of such pairs are the global \
units modulo nth powers; the cohomological side is \
AlgebraicGeometry.pairIso_iff_kummerBoundary_eq"]
public theorem pairIso_unitPair_iff (S : Scheme.{u}) (n : ℕ)
    (f g : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    Nonempty (PairIso (unitPair S n f) (unitPair S n g)) ↔
      ∃ u : (Scheme.Γ.obj (Opposite.op S))ˣ, f = u ^ n * g := by
  constructor
  · rintro ⟨φ⟩
    obtain ⟨u, hu⟩ := exists_scalarIso S (SheafOfModules.unit (ringSheaf S)) φ.sheafIso
    refine ⟨u, (unitPair_compatible_iff S n f g u).mp ?_⟩
    rw [hu]
    exact φ.compatible
  · rintro ⟨u, hu⟩
    exact ⟨{ sheafIso := scalarIso S u (SheafOfModules.unit (ringSheaf S))
             compatible := (unitPair_compatible_iff S n f g u).mpr hu }⟩

end AlgebraicGeometry

/-! ### Kummer theory: further declarations -/

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules (terminalSectionToEnd terminalSectionToEnd_apply)
namespace AlgebraicGeometry
universe u
/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- An invertible sheaf carries a trivialization of its `n`th tensor power exactly when that
power is trivial; so the invertible sheaves of pairs are exactly those whose class in the Picard
group is `n`-torsion. -/
@[stacks 040Q "the invertible sheaves occurring in a pair are exactly those whose nth tensor \
power is trivial, with no restriction to the structure sheaf"]
public theorem exists_trivializedPower_sheaf_iff (S : Scheme.{u}) (n : ℕ)
    (L : SheafOfModules.{u} (ringSheaf S))
    (hL : IsInvertible S.presheaf (ringSheafCond S) L) :
    (∃ P : TrivializedPower S n, P.sheaf = L) ↔
      Nonempty (tensorPower S.presheaf (ringSheafCond S) L (n : ℤ) ≅
        SheafOfModules.unit (ringSheaf S)) := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.trivialization⟩
  · rintro ⟨α⟩
    exact ⟨⟨L, hL, α⟩, rfl⟩

end AlgebraicGeometry
end

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules (terminalSectionToEnd terminalSectionToEnd_apply)
namespace AlgebraicGeometry
universe u
/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- Two trivializations of the `n`th tensor power of an invertible sheaf differ by multiplication
by a global unit, because the automorphisms of the structure sheaf are the global units. -/
public theorem exists_scalarIso_trivialization (S : Scheme.{u}) (n : ℕ)
    {L : SheafOfModules.{u} (ringSheaf S)}
    [IsInvertible S.presheaf (ringSheafCond S) L]
    (α β : tensorPower S.presheaf (ringSheafCond S) L (n : ℤ) ≅
      SheafOfModules.unit (ringSheaf S)) :
    ∃ v : (Scheme.Γ.obj (Opposite.op S))ˣ,
      scalarIso S v (SheafOfModules.unit (ringSheaf S)) = β.symm ≪≫ α :=
  exists_scalarIso S (SheafOfModules.unit (ringSheaf S)) (β.symm ≪≫ α)

end AlgebraicGeometry
end

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules (terminalSectionToEnd terminalSectionToEnd_apply)
namespace AlgebraicGeometry
universe u
/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- The global unit by which two trivializations of the `n`th tensor power of an invertible sheaf
differ: multiplication by it is the automorphism `β⁻¹ ∘ α` of the structure sheaf. -/
public noncomputable def trivializationRatio (S : Scheme.{u}) (n : ℕ)
    {L : SheafOfModules.{u} (ringSheaf S)}
    [IsInvertible S.presheaf (ringSheafCond S) L]
    (α β : tensorPower S.presheaf (ringSheafCond S) L (n : ℤ) ≅
      SheafOfModules.unit (ringSheaf S)) :
    (Scheme.Γ.obj (Opposite.op S))ˣ :=
  (exists_scalarIso_trivialization S n α β).choose

end AlgebraicGeometry
end

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules (terminalSectionToEnd terminalSectionToEnd_apply)
namespace AlgebraicGeometry
universe u
/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- Multiplication by the ratio of two trivializations is the automorphism comparing them. -/
public theorem scalarIso_trivializationRatio (S : Scheme.{u}) (n : ℕ)
    {L : SheafOfModules.{u} (ringSheaf S)}
    [IsInvertible S.presheaf (ringSheafCond S) L]
    (α β : tensorPower S.presheaf (ringSheafCond S) L (n : ℤ) ≅
      SheafOfModules.unit (ringSheaf S)) :
    scalarIso S (trivializationRatio S n α β) (SheafOfModules.unit (ringSheaf S)) =
      β.symm ≪≫ α :=
  (exists_scalarIso_trivialization S n α β).choose_spec

end AlgebraicGeometry
end

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules (terminalSectionToEnd terminalSectionToEnd_apply)
namespace AlgebraicGeometry
universe u
/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

private theorem scalarIso_trans_eq_trans_scalarIso (S : Scheme.{u})
    {M N : SheafOfModules (ringSheaf S)} (a : (Scheme.Γ.obj (Opposite.op S))ˣ) (e : M ≅ N) :
    scalarIso S a M ≪≫ e = e ≪≫ scalarIso S a N :=
  Iso.ext (scalarEnd_naturality S a.val e.hom).symm

end AlgebraicGeometry
end

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules (terminalSectionToEnd terminalSectionToEnd_apply)
namespace AlgebraicGeometry
universe u
/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

private theorem pairIso_sameSheaf_iff_pow (S : Scheme.{u}) (n : ℕ)
    (L : SheafOfModules.{u} (ringSheaf S))
    [IsInvertible S.presheaf (ringSheafCond S) L]
    (α β : tensorPower S.presheaf (ringSheafCond S) L (n : ℤ) ≅
      SheafOfModules.unit (ringSheaf S))
    (u : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    tensorPowerMap S (scalarIso S u L) n ≪≫ β = α ↔
      trivializationRatio S n α β = u ^ n := by
  rw [tensorPowerMap_scalar S L u n, scalarIso_trans_eq_trans_scalarIso]
  constructor
  · intro h
    have h' : scalarIso S (u ^ n) (SheafOfModules.unit (ringSheaf S)) = β.symm ≪≫ α := by
      apply Iso.ext
      rw [Iso.trans_hom, Iso.symm_hom, ← h, Iso.trans_hom, Iso.inv_hom_id_assoc]
    apply Units.ext
    exact scalarEnd_injective S (SheafOfModules.unit (ringSheaf S))
      (congrArg Iso.hom ((scalarIso_trivializationRatio S n α β).trans h'.symm))
  · intro h
    apply Iso.ext
    rw [Iso.trans_hom, ← h, scalarIso_trivializationRatio, Iso.trans_hom, Iso.symm_hom,
      Iso.hom_inv_id_assoc]

end AlgebraicGeometry
end

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules (terminalSectionToEnd terminalSectionToEnd_apply)
namespace AlgebraicGeometry
universe u
/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- Two pairs with the same, possibly nontrivial, invertible sheaf are isomorphic exactly when
their trivializations differ by the `n`th power of a global unit. -/
@[stacks 040Q "the pair side for an arbitrary, possibly nontrivial, invertible sheaf: two pairs \
with the same invertible sheaf are isomorphic exactly when their trivializations differ by the \
nth power of a global unit, so the pairs with a given invertible sheaf form one coset of the nth \
powers in the global units"]
public theorem pairIso_iff_trivializationRatio_eq_pow (S : Scheme.{u}) (n : ℕ)
    (L : SheafOfModules.{u} (ringSheaf S))
    [hL : IsInvertible S.presheaf (ringSheafCond S) L]
    (α β : tensorPower S.presheaf (ringSheafCond S) L (n : ℤ) ≅
      SheafOfModules.unit (ringSheaf S)) :
    Nonempty (PairIso ⟨L, hL, α⟩ ⟨L, hL, β⟩) ↔
      ∃ u : (Scheme.Γ.obj (Opposite.op S))ˣ, trivializationRatio S n α β = u ^ n := by
  constructor
  · rintro ⟨φ⟩
    obtain ⟨u, hu⟩ := exists_scalarIso S L φ.sheafIso
    refine ⟨u, (pairIso_sameSheaf_iff_pow S n L α β u).1 ?_⟩
    rw [hu]
    exact φ.compatible
  · rintro ⟨u, hu⟩
    exact ⟨{ sheafIso := scalarIso S u L
             compatible := (pairIso_sameSheaf_iff_pow S n L α β u).2 hu }⟩

end AlgebraicGeometry
end

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules (terminalSectionToEnd terminalSectionToEnd_apply)
namespace AlgebraicGeometry
universe u
/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- A pair whose invertible sheaf is isomorphic to the structure sheaf — not only equal to it —
is isomorphic to the pair given by the structure sheaf and a global unit. -/
@[stacks 040Q "every pair whose invertible sheaf is isomorphic to the structure sheaf is \
isomorphic to a unit pair, so the trivial-invertible-sheaf case is not a restriction to the \
literal structure sheaf"]
public theorem exists_pairIso_unitPair (S : Scheme.{u}) (n : ℕ) (P : TrivializedPower S n)
    (e : P.sheaf ≅ SheafOfModules.unit (ringSheaf S)) :
    ∃ f : (Scheme.Γ.obj (Opposite.op S))ˣ, Nonempty (PairIso P (unitPair S n f)) := by
  let := P.invertible
  obtain ⟨f, hf⟩ := exists_scalarIso S (SheafOfModules.unit (ringSheaf S))
    ((structureSheafTensorPowerIso S n).symm ≪≫
      ((tensorPowerMap S e n).symm ≪≫ P.trivialization))
  have key : structureSheafTensorPowerIso S n ≪≫
      scalarIso S f (SheafOfModules.unit (ringSheaf S)) =
      (tensorPowerMap S e n).symm ≪≫ P.trivialization := by
    rw [hf, ← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  have key' : tensorPowerMap S e n ≪≫
      ((tensorPowerMap S e n).symm ≪≫ P.trivialization) = P.trivialization := by
    rw [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  exact ⟨f, ⟨{ sheafIso := e
               compatible := (congrArg (fun z => tensorPowerMap S e n ≪≫ z) key).trans key' }⟩⟩

end AlgebraicGeometry
end

@[expose] public section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  tensorLeftFunctorUniversal tensorLeftFunctor_isEquivalence)
open Stacks.SheafOfModules.Invertible
namespace AlgebraicGeometry
universe u
/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. -/
local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- A global section of the structure sheaf is determined by multiplication by it on the
structure sheaf. -/
public theorem scalarEnd_unit_injective (S : Scheme.{u}) :
    Function.Injective (fun s : Scheme.Γ.obj (Opposite.op S) =>
      scalarEnd S s (SheafOfModules.unit (ringSheaf S))) :=
  scalarEnd_injective S (SheafOfModules.unit (ringSheaf S))

/-- The tensor power of a composite of isomorphisms of invertible sheaves is the composite of
the tensor powers. -/
public theorem tensorPowerMap_trans_eq {S : Scheme.{u}}
    {L M N : SheafOfModules (ringSheaf S)}
    [IsInvertible S.presheaf (ringSheafCond S) L]
    [IsInvertible S.presheaf (ringSheafCond S) M]
    [IsInvertible S.presheaf (ringSheafCond S) N]
    (e : L ≅ M) (f : M ≅ N) (n : ℕ) :
    tensorPowerMap S (e ≪≫ f) n =
      tensorPowerMap S e n ≪≫ tensorPowerMap S f n :=
  tensorPowerMap_trans S e f n

end AlgebraicGeometry
end
