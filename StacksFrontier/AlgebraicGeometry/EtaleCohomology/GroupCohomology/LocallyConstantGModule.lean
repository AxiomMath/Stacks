module

public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.GroupTheory.Torsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeOneCocycles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteCochains

/-!
# The module of locally constant functions on a profinite group

Let `G` be a profinite group and `B` an abelian group. The locally constant functions `G → B`
form a subgroup of all functions `G → B`, and `G` acts on it by right translation,
`(g • f) x = f (x * g)`. On a profinite group a locally constant function is right invariant
under an open subgroup, so every stabilizer for this action is open and the result is a discrete
`G`-module in the sense of Stacks 04JP.

This module is the standard source of injective objects in the category of discrete
`G`-modules: when `B` is divisible it is injective, an injective additive map `M →+ B` induces a
monomorphism from any discrete `G`-module `M` into it, and it is torsion as soon as `B` is.

## Main definitions

* `Stacks.GroupCohomology.lcAddSubgroup`: the locally constant functions `G → B`, as a subgroup
  of `G → B`; `Stacks.GroupCohomology.lcFun` abbreviates its carrier type.
* `Stacks.GroupCohomology.locallyConstantGModule`: the same group as a discrete `G`-module, with
  `G` acting by right translation.
* `Stacks.GroupCohomology.orbitHom` and `Stacks.GroupCohomology.orbitMap`: the additive map and
  the morphism of discrete `G`-modules `z ↦ (g ↦ ψ (g • z))` attached to an additive map
  `ψ : M →+ B`.
* `Stacks.GroupCohomology.charDual`, `Stacks.GroupCohomology.torsionHull`: the divisible group
  `M⋆ → ℚ/ℤ` into which an abelian group `M` embeds, and its torsion subgroup.

## Main results

* `Stacks.GroupCohomology.isOpen_stabilizer_lcFun`: the stabilizer of a locally constant
  function is open, which is what makes the right translation action continuous.
* `Stacks.GroupCohomology.injective_locallyConstantGModule`: **for divisible `B` the discrete
  `G`-module of locally constant functions `G → B` is an injective object.**
* `Stacks.GroupCohomology.mono_orbitMap`: an injective `ψ : M →+ B` gives a monomorphism of
  discrete `G`-modules into the locally constant functions.
* `Stacks.GroupCohomology.exists_nsmul_eq_zero_lcFun` and
  `Stacks.GroupCohomology.isAddTorsion_lcFun`: the locally constant functions are torsion when
  `B` is.
* `Stacks.GroupCohomology.injective_toTorsionHull`,
  `Stacks.GroupCohomology.isAddTorsion_torsionHull`: a torsion abelian group embeds into a
  torsion divisible one.

## Implementation notes

The carrier is an `AddSubgroup` of `G → B` rather than a structure of its own, so that the
abelian group structure, the `ℤ`-module structure and the lemmas about them come for free. The
action is a bare `DistribMulAction`; the object of Stacks 04JP is then obtained through
`Stacks.GroupCohomology.ofDistribMulAction`.

Injectivity is Baer's criterion transported along the evaluation at `1`. A morphism
`X ⟶ locallyConstantGModule G B` is the same thing as an additive map `X →+ B`, namely its
composite with evaluation at `1`; the inverse construction sends `ψ` to the orbit map
`z ↦ (g ↦ ψ (g • z))`, which is locally constant because the stabilizer of `z` is open. So an
extension problem in the category of discrete `G`-modules becomes an extension problem for
additive maps into `B`, which divisibility of `B` solves.

The torsion divisible hull is the injective object used by Mathlib's
`AddCommGrpCat.enoughInjectives`, cut down to its torsion subgroup. The torsion subgroup of a
divisible group is again divisible: a division of a torsion element is killed by the product of
its own order and the integer divided by.

## References

* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP): discrete `G`-modules.
* [Stacks Project, Tag 0DV3](https://stacks.math.columbia.edu/tag/0DV3): the dévissage these
  objects serve.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.ContinuousCohomology

universe u v

namespace Stacks.GroupCohomology

open scoped Stacks.DiscreteModuleTopology

/-! ### The group of locally constant functions -/

section Carrier

/-- The locally constant functions `G → B`, as a subgroup of all functions `G → B`. -/
def lcAddSubgroup (G : Type u) [TopologicalSpace G] (B : Type v) [AddCommGroup B] :
    AddSubgroup (G → B) where
  carrier := {f | IsLocallyConstant f}
  add_mem' hf hg := hf.add hg
  zero_mem' := IsLocallyConstant.zero
  neg_mem' hf := hf.neg

/-- The group of locally constant functions `G → B`. -/
abbrev lcFun (G : Type u) [TopologicalSpace G] (B : Type v) [AddCommGroup B] : Type max u v :=
  ↥(lcAddSubgroup G B)

variable {G : Type u} [TopologicalSpace G] {B : Type v} [AddCommGroup B]

/-- A function `G → B` lies in `Stacks.GroupCohomology.lcAddSubgroup` iff it is locally
constant. -/
@[simp] lemma mem_lcAddSubgroup {f : G → B} :
    f ∈ lcAddSubgroup G B ↔ IsLocallyConstant f := Iff.rfl

/-- The function underlying an element of `Stacks.GroupCohomology.lcFun` is locally constant. -/
lemma isLocallyConstant_coe (f : lcFun G B) : IsLocallyConstant (f : G → B) := f.2

end Carrier

/-! ### The action by right translation -/

/-- The identity of `G` acts trivially on a discrete `G`-module. -/
private lemma ρ_one_apply {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : ContinuousGModule.{u, max u v} G) (z : X.obj.obj.V) :
    (X.obj.obj.ρ (1 : G)).asHom.hom z = z := by
  rw [map_one]
  rfl

section Action

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {B : Type v} [AddCommGroup B]

/-- `G` acts on the locally constant functions `G → B` by right translation,
`(g • f) x = f (x * g)`. -/
instance : SMul G (lcFun G B) where
  smul g f := ⟨fun x ↦ (f : G → B) (x * g),
    (isLocallyConstant_coe f).comp_continuous (by fun_prop)⟩

/-- The function underlying `g • f` sends `x` to `f (x * g)`. -/
@[simp] lemma lcFun_smul_coe (g : G) (f : lcFun G B) (x : G) :
    ((g • f : lcFun G B) : G → B) x = (f : G → B) (x * g) := rfl

/-- Right translation is a left action of `G`: `(g₁ * g₂) • f` sends `x` to `f (x * g₁ * g₂)`,
which is `(g₁ • (g₂ • f)) x`. It is additive in `f`. -/
instance : DistribMulAction G (lcFun G B) where
  one_smul f := Subtype.ext (funext fun x ↦ by simp)
  mul_smul g₁ g₂ f := Subtype.ext (funext fun x ↦ by simp [mul_assoc])
  smul_zero g := Subtype.ext rfl
  smul_add g f₁ f₂ := Subtype.ext rfl

end Action

/-! ### The discrete `G`-module of locally constant functions -/

section Module

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (B : Type v) [AddCommGroup B]

variable {G B} in
/-- **The stabilizer of a locally constant function is open.** -/
theorem isOpen_stabilizer_lcFun (f : lcFun G B) : IsOpen {g : G | g • f = f} := by
  obtain ⟨N, hN⟩ := exists_openSubgroup_forall_mul_right_eq f.2
  have hle : N.toSubgroup ≤ MulAction.stabilizer G f := by
    intro n hn
    exact Subtype.ext (funext fun x ↦ hN x n hn)
  exact Subgroup.isOpen_mono hle N.isOpen'

/-- The action by right translation on the locally constant functions is continuous for the
discrete topology. -/
theorem isContinuous_lcFun :
    (actionOfDistribMulAction G (lcFun G B)).IsContinuous :=
  isContinuous_ofDistribMulAction_iff.2 isOpen_stabilizer_lcFun

/-- The discrete `G`-module of locally constant functions `G → B`, with `G` acting by right
translation. -/
def locallyConstantGModule : ContinuousGModule.{u, max u v} G :=
  ofDistribMulAction (isContinuous_lcFun G B)

/-- The abelian group underlying `Stacks.GroupCohomology.locallyConstantGModule` is the group of
locally constant functions. -/
@[simp] lemma locallyConstantGModule_V :
    (locallyConstantGModule G B).obj.obj.V = ModuleCat.of ℤ (lcFun G B) := rfl

variable {G B}

/-- The action on `Stacks.GroupCohomology.locallyConstantGModule` is right translation. -/
@[simp] lemma locallyConstantGModule_ρ_hom (g : G) (f : lcFun G B) :
    (((locallyConstantGModule G B).obj.obj.ρ g).asHom.hom f : lcFun G B) = g • f := rfl

end Module

/-! ### The orbit map of an additive map to the coefficients -/

section Orbit

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {B : Type v} [AddCommGroup B]

/-- The orbit map of an additive map `ψ : X →+ B` out of a discrete `G`-module: it sends `z` to
the locally constant function `g ↦ ψ (g • z)`. -/
def orbitHom (X : ContinuousGModule.{u, max u v} G) (ψ : X.obj.obj.V →+ B) :
    X.obj.obj.V →+ lcFun G B where
  toFun z := ⟨fun g ↦ ψ ((X.obj.obj.ρ g).asHom.hom z),
    isLocallyConstant_of_stabilizer G X z _ fun g₁ g₂ h ↦ by rw [h]⟩
  map_zero' := Subtype.ext (funext fun g ↦ by simp)
  map_add' z₁ z₂ := Subtype.ext (funext fun g ↦ by simp)

variable (X : ContinuousGModule.{u, max u v} G) (ψ : X.obj.obj.V →+ B)

/-- The orbit map sends `z` to the function `g ↦ ψ (g • z)`. -/
@[simp] lemma orbitHom_apply_coe (z : X.obj.obj.V) (g : G) :
    ((orbitHom X ψ z : lcFun G B) : G → B) g = ψ ((X.obj.obj.ρ g).asHom.hom z) := rfl

/-- The orbit map is `G`-equivariant for the action by right translation. -/
lemma orbitHom_smul (g : G) (z : X.obj.obj.V) :
    orbitHom X ψ ((X.obj.obj.ρ g).asHom.hom z) = g • orbitHom X ψ z := by
  refine Subtype.ext (funext fun x ↦ ?_)
  simp only [orbitHom_apply_coe, lcFun_smul_coe]
  rw [map_mul]
  rfl

/-- **The morphism of discrete `G`-modules attached to an additive map `ψ : X →+ B`**, sending
`z` to the locally constant function `g ↦ ψ (g • z)`. -/
def orbitMap : X ⟶ locallyConstantGModule G B :=
  (gModuleHomEquiv G X (locallyConstantGModule G B)).symm
    ⟨orbitHom X ψ, fun g z ↦ (orbitHom_smul X ψ g z).trans
      (locallyConstantGModule_ρ_hom g (orbitHom X ψ z)).symm⟩

/-- The underlying additive map of `Stacks.GroupCohomology.orbitMap X ψ` is
`Stacks.GroupCohomology.orbitHom X ψ`. -/
@[simp] lemma orbitMap_underlying_apply (z : X.obj.obj.V) :
    ((continuousGModuleUnderlying.{u, max u v} G).map (orbitMap X ψ)).hom z =
      orbitHom X ψ z := rfl

/-- **The orbit map of an injective `ψ` is a monomorphism of discrete `G`-modules.** -/
theorem mono_orbitMap (hψ : Function.Injective ψ) : Mono (orbitMap X ψ) := by
  refine (continuousGModuleUnderlying.{u, max u v} G).mono_of_mono_map ?_
  rw [ModuleCat.mono_iff_injective]
  intro z₁ z₂ h
  have h' : orbitHom X ψ z₁ = orbitHom X ψ z₂ := h
  have h1 : ψ ((X.obj.obj.ρ (1 : G)).asHom.hom z₁) = ψ ((X.obj.obj.ρ (1 : G)).asHom.hom z₂) :=
    congrFun (congrArg Subtype.val h') 1
  exact (ρ_one_apply X z₁).symm.trans ((hψ h1).trans (ρ_one_apply X z₂))

end Orbit

/-! ### Injectivity -/

section Injective

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (B : Type v) [AddCommGroup B]

/-- **For divisible `B` the discrete `G`-module of locally constant functions `G → B` is an
injective object.** -/
instance injective_locallyConstantGModule [DivisibleBy B ℤ] :
    Injective (locallyConstantGModule G B) := by
  constructor
  intro X Y gm fm hfm
  have : Mono fm := hfm
  let G₀ : X.obj.obj.V →+ lcFun G B :=
    (gModuleHomEquiv G X (locallyConstantGModule G B) gm).1
  have hG₀ : ∀ (g : G) (x : X.obj.obj.V), G₀ ((X.obj.obj.ρ g).asHom.hom x) = g • G₀ x :=
    fun g x ↦ ((gModuleHomEquiv G X (locallyConstantGModule G B) gm).2 g x).trans
      (locallyConstantGModule_ρ_hom g (G₀ x))
  let ψ : X.obj.obj.V →+ B :=
    { toFun := fun x ↦ (G₀ x : G → B) 1
      map_zero' := by simp
      map_add' := fun a b ↦ by simp }
  let fl : X.obj.obj.V →+ Y.obj.obj.V :=
    ((continuousGModuleUnderlying.{u, max u v} G).map fm).hom.toAddMonoidHom
  have hflinj : Function.Injective fl :=
    (ModuleCat.mono_iff_injective ((continuousGModuleUnderlying.{u, max u v} G).map fm)).mp
      (Functor.map_mono _ fm)
  have hfleq : ∀ (g : G) (x : X.obj.obj.V),
      fl ((X.obj.obj.ρ g).asHom.hom x) = (Y.obj.obj.ρ g).asHom.hom (fl x) :=
    fun g x ↦ ConcreteCategory.congr_hom (fm.hom.hom.comm g) x
  obtain ⟨ψ', hψ'⟩ := (Module.Baer.of_divisible B).extension_property_addMonoidHom fl hflinj ψ
  refine ⟨orbitMap Y ψ', (gModuleHomEquiv G X (locallyConstantGModule G B)).injective
    (Subtype.ext (AddMonoidHom.ext fun x ↦ ?_))⟩
  change orbitHom Y ψ' (fl x) = G₀ x
  refine Subtype.ext (funext fun g ↦ ?_)
  change ψ' ((Y.obj.obj.ρ g).asHom.hom (fl x)) = (G₀ x : G → B) g
  calc ψ' ((Y.obj.obj.ρ g).asHom.hom (fl x))
      = ψ' (fl ((X.obj.obj.ρ g).asHom.hom x)) := by rw [hfleq]
    _ = ψ ((X.obj.obj.ρ g).asHom.hom x) := DFunLike.congr_fun hψ' _
    _ = (G₀ x : G → B) g :=
      (congrArg (fun f : lcFun G B ↦ (f : G → B) 1) (hG₀ g x)).trans (by simp)

end Injective

/-! ### Torsion -/

section Torsion

variable {G : Type u} [TopologicalSpace G] [CompactSpace G] {B : Type v} [AddCommGroup B]

/-- **The locally constant functions `G → B` are torsion when `B` is**: if every element of `B`
is killed by a positive integer, so is every locally constant function `G → B`. -/
theorem exists_nsmul_eq_zero_lcFun (hB : ∀ b : B, ∃ n : ℕ, 0 < n ∧ n • b = 0)
    (f : lcFun G B) : ∃ n : ℕ, 0 < n ∧ n • f = 0 := by
  choose ord hord hord' using hB
  classical
  obtain ⟨s, hs⟩ := (isLocallyConstant_coe f).range_finite.exists_finset
  refine ⟨∏ b ∈ s, ord b, Finset.prod_pos fun b _ ↦ hord b, ?_⟩
  refine Subtype.ext (funext fun x ↦ ?_)
  have hmem : (f : G → B) x ∈ s := (hs _).2 ⟨x, rfl⟩
  have hprod : (∏ b ∈ s, ord b) =
      ord ((f : G → B) x) * ∏ b ∈ s.erase ((f : G → B) x), ord b :=
    (Finset.mul_prod_erase s ord hmem).symm
  simp [hprod, mul_nsmul, hord']

/-- **The locally constant functions `G → B` are torsion when `B` is.** -/
theorem isAddTorsion_lcFun (hB : IsAddTorsion B) : IsAddTorsion (lcFun G B) := by
  intro f
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 (exists_nsmul_eq_zero_lcFun ?_ f)
  exact fun b ↦ isOfFinAddOrder_iff_nsmul_eq_zero.1 (hB b)

end Torsion

/-! ### A torsion divisible hull -/

section TorsionHull

variable (M : Type v) [AddCommGroup M]

/-- The divisible abelian group `M⋆ → ℚ/ℤ` into which `M` embeds, where `M⋆` is the character
module of `M`. -/
abbrev charDual : Type v := CharacterModule M → ULift.{v} (AddCircle (1 : ℚ))

/-- The embedding of `M` into `Stacks.GroupCohomology.charDual`, sending `a` to evaluation at
`a`. -/
def toCharDual : M →+ charDual M where
  toFun a i := ULift.up (i a)
  map_zero' := by aesop
  map_add' := by aesop

/-- **An abelian group embeds into its character dual.** -/
lemma injective_toCharDual : Function.Injective (toCharDual M) :=
  (injective_iff_map_eq_zero _).2 fun _ h ↦
    CharacterModule.eq_zero_of_character_apply (congrArg ULift.down <| congrFun h ·)

/-- The torsion subgroup of `Stacks.GroupCohomology.charDual`: a divisible torsion group into
which every torsion abelian group embeds. -/
def torsionHull : AddSubgroup (charDual M) := AddCommGroup.torsion (charDual M)

/-- An element lies in `Stacks.GroupCohomology.torsionHull M` iff it has finite additive
order. -/
lemma mem_torsionHull {x : charDual M} : x ∈ torsionHull M ↔ IsOfFinAddOrder x := Iff.rfl

/-- **The torsion hull is divisible**: the division of a torsion element of
`Stacks.GroupCohomology.charDual M` is again torsion. -/
instance divisibleBy_torsionHull : DivisibleBy ↥(torsionHull M) ℤ where
  div x n := ⟨DivisibleBy.div (x : charDual M) n, by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [DivisibleBy.div_zero]
      exact (mem_torsionHull M).2 IsOfFinAddOrder.zero
    · obtain ⟨m, hm, hmx⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.1 ((mem_torsionHull M).1 x.2)
      refine (mem_torsionHull M).2 (isOfFinAddOrder_iff_zsmul_eq_zero.2
        ⟨m * n, mul_ne_zero hm hn, ?_⟩)
      rw [mul_smul, DivisibleBy.div_cancel _ hn, hmx]⟩
  div_zero x := Subtype.ext (DivisibleBy.div_zero _)
  div_cancel x hn := Subtype.ext (by simpa using DivisibleBy.div_cancel (x : charDual M) hn)

/-- **The torsion hull is torsion.** -/
theorem isAddTorsion_torsionHull : IsAddTorsion ↥(torsionHull M) := by
  intro x
  obtain ⟨n, hn, hx⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.1 ((mem_torsionHull M).1 x.2)
  exact isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨n, hn, Subtype.ext (by simpa using hx)⟩

/-- The embedding of a torsion abelian group into its torsion divisible hull. -/
def toTorsionHull (hM : IsAddTorsion M) : M →+ ↥(torsionHull M) where
  toFun a := ⟨toCharDual M a, by
    obtain ⟨n, hn, hna⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.1 (hM a)
    exact (mem_torsionHull M).2 (isOfFinAddOrder_iff_zsmul_eq_zero.2
      ⟨n, hn, by rw [← map_zsmul, hna, map_zero]⟩)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

/-- **A torsion abelian group embeds into a torsion divisible one.** -/
theorem injective_toTorsionHull (hM : IsAddTorsion M) :
    Function.Injective (toTorsionHull M hM) :=
  fun _ _ h ↦ injective_toCharDual M (Subtype.ext_iff.1 h)

end TorsionHull

end Stacks.GroupCohomology

end
