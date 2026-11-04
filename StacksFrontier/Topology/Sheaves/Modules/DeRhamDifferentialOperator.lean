module

public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperators
public import StacksFrontier.RingTheory.DifferentialOperator.OrderOne
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamExistence
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham differentials are differential operators of order one

Let `φ : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space, with `B`
the structure sheaf of a ringed space, and let `⋀ᵖ Ω` be the terms of the relative de Rham
complex of `φ`. This file proves that the de Rham differential `d : ⋀ᵖ Ω ⟶ ⋀ᵖ⁺¹ Ω`, regarded as
an additive operator on local sections of sheaves of `B`-modules, is a differential operator of
order at most one relative to `φ`.

The proof is the proof of the source. The order-one condition is `A`-linearity together with
`B`-linearity of every commutator `s ↦ d (g · s) - g · d s`; the first is immediate because the
differential is a morphism of sheaves of `A`-modules, and the second is a local identity, so it
may be checked on the sections that come from the presheaf of sectionwise exterior powers of the
sectionwise Kähler differentials — which they do on a covering of every object. There the
differential is the sectionwise one, and the identity is the ring-level statement that the de
Rham differential of a ring map is a differential operator of order one.

## Main results

* `PresheafOfModules.sectionwiseDeRhamDifferentialApp_commutator_smul`: the commutator of the
  sectionwise de Rham differential with a section of the target ring is linear over the target
  ring.
* `AlgebraicGeometry.SheafOfModules.deRhamDifferentialHom_isGlobalDiffOpOfOrder_one`: **the de
  Rham differential is a differential operator of order one.**

## Implementation notes

`DiffOp.IsGlobalDiffOpOfOrder` localizes the commutator condition at every object of the site,
over the slice category there. Since the de Rham differential is a morphism of sheaves and its
commutators are given by one and the same formula over every object,
`DiffOp.isGlobalDiffOpOfOrder_one_of_commutator_smul` reduces the whole predicate to three
statements about an operator on the sections of the sheaves themselves — restriction
compatibility, linearity for the scalars coming from the source ring sheaf, and target-ring
linearity of the commutator — with no slices left in them.

The differential is a morphism of sheaves of `A`-modules between the restrictions of scalars of
`⋀ᵖ Ω` and `⋀ᵖ⁺¹ Ω`, whereas the differential-operator predicate wants an operator between the
sheaves of `B`-modules themselves. Restriction of scalars does not change the underlying
sections, so `AlgebraicGeometry.SheafOfModules.deRhamGlobalOp` is the differential read as such
an operator with no transport at all.

The sectionwise statement is proved at the `CommRingCat` spelling `(R.obj U)`, `(R'.obj U)` of
the two rings, which is the spelling `CommRingCat.KaehlerDifferential` itself uses; this is the
same discipline as `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DeRhamSectionwise`, and for the
same reason.

## References

* [Stacks Project, Tag 0G3Y](https://stacks.math.columbia.edu/tag/0G3Y)
* [Stacks Project, Tag 0G34](https://stacks.math.columbia.edu/tag/0G34)
* [Stacks Project, Tag 09CR](https://stacks.math.columbia.edu/tag/09CR)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe v u w

namespace DiffOp

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {O₁ O₂ : Sheaf J RingCat}

/-- Restriction of a scalar multiple, when the restricted scalar is known. -/
private theorem map_smul_of_restrict_eq {H : SheafOfModules O₂} {Y Y' : Cᵒᵖ} (h : Y ⟶ Y')
    {a : O₂.obj.obj Y} {b : O₂.obj.obj Y'} (hab : O₂.obj.map h a = b) (x : H.val.obj Y) :
    H.val.map h (a • x) = b • H.val.map h x := by
  rw [H.val.map_smul, hab]

/-- **A criterion for order one.** An operator on the local sections of two sheaves of
`O₂`-modules which is compatible with restriction, linear for the scalars coming from `O₁`, and
whose commutator with every local section of `O₂` is `O₂`-linear, is a differential operator of
order at most one.

The three hypotheses are statements about the sheaves themselves; the predicate
`DiffOp.IsGlobalDiffOpOfOrder` asks for the commutator condition over every slice of the site,
and this lemma discharges the slices once and for all. -/
theorem isGlobalDiffOpOfOrder_one_of_commutator_smul (φ : O₁ ⟶ O₂)
    {F G : SheafOfModules O₂} (D : GlobalOp F G)
    (hnat : ∀ {Y Y' : Cᵒᵖ} (h : Y ⟶ Y') (s : F.val.obj Y),
      D Y' (F.val.map h s) = G.val.map h (D Y s))
    (hlin : ∀ (Y : Cᵒᵖ) (a : O₁.obj.obj Y) (s : F.val.obj Y),
      D Y (sectionRingHom φ Y a • s) = sectionRingHom φ Y a • D Y s)
    (hcomm : ∀ (Y : Cᵒᵖ) (g r : O₂.obj.obj Y) (s : F.val.obj Y),
      D Y (g • r • s) - g • D Y (r • s) = r • (D Y (g • s) - g • D Y s)) :
    IsGlobalDiffOpOfOrder φ 1 D := by
  intro U
  refine ⟨fun Y Y' h s => hnat h.left.op s, fun Y a s => hlin _ a s, fun Y g => ⟨?_, ?_⟩⟩
  · intro Z Z' h s
    -- the restriction of `g` to `Z` is the restriction along `h` of its restriction to `Z'`
    have hop : Z.hom.op = Z'.hom.op ≫ h.left.op := by rw [← Over.w h]; rfl
    have hg : (O₂.obj.map h.left.op) ((O₂.obj.map Z'.hom.op) g) =
        (O₂.obj.map Z.hom.op) g := by rw [hop, O₂.obj.map_comp]; rfl
    have a₁ := (congrArg (D (op Z.left)) (map_smul_of_restrict_eq h.left.op hg s).symm).trans
      (hnat h.left.op ((O₂.obj.map Z'.hom.op) g • s))
    have a₂ := (congrArg ((O₂.obj.map Z.hom.op) g • ·) (hnat h.left.op s)).trans
      (map_smul_of_restrict_eq h.left.op hg (D (op Z'.left) s)).symm
    exact (congrArg₂ (· - ·) a₁ a₂).trans (map_sub (G.val.restrictₛₗ h.left.op) _ _).symm
  · intro Z r s
    exact hcomm _ _ r s

end DiffOp

namespace PresheafOfModules

open DifferentialsConstruction

variable {C : Type u} [Category.{v} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : R ⟶ R')

/-- **The sectionwise de Rham differential is a differential operator of order one.** Its
commutator with multiplication by a section of `R'` is linear over `R'`.

This is the ring-level statement of Tag 0G34, read on the sections of the presheaves of
sectionwise exterior powers of the sectionwise Kähler differentials. -/
theorem sectionwiseDeRhamDifferentialApp_commutator_smul (p : ℕ) (U : Cᵒᵖ)
    (g r : (R' ⋙ forget₂ CommRingCat RingCat).obj U)
    (z : (extPow.{v, u, w, w} p (relativeDifferentials' φ)).obj U) :
    sectionwiseDeRhamDifferentialApp φ p U (g • r • z) -
        g • sectionwiseDeRhamDifferentialApp φ p U (r • z) =
      r • (sectionwiseDeRhamDifferentialApp φ p U (g • z) -
        g • sectionwiseDeRhamDifferentialApp φ p U z) := by
  let : Algebra (R.obj U) (R'.obj U) := (φ.app U).hom.toAlgebra
  have hd : IsDiffOpLE (R.obj U) (R'.obj U) 1
      (KaehlerDifferential.deRhamDifferential
        (A := R.obj U) (B := R'.obj U) p).toAddMonoidHom :=
    deRham_isDiffOpOfOrder_one p _
      (fun a x => KaehlerDifferential.deRhamDifferential_algebraMap_smul p a x)
      (fun b => KaehlerDifferential.deRhamDifferential_smul_ιMulti_D p b)
  exact hd.2 g r (extPowSections.{v, u, w, w} p (relativeDifferentials' φ) U z)

end PresheafOfModules

namespace AlgebraicGeometry.SheafOfModules

open PresheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- **The degree-`p` de Rham differential, read as an operator on the local sections of the
sheaves of `B`-modules `⋀ᵖ Ω` and `⋀ᵖ⁺¹ Ω`.** The differential is a morphism of sheaves of
`A`-modules between the restrictions of scalars of those two sheaves, and restriction of scalars
does not change the sections, so no transport is involved. -/
noncomputable abbrev deRhamGlobalOp (p : ℕ) :
    DiffOp.GlobalOp (B.exteriorPower p) (B.exteriorPower (p + 1)) :=
  fun U => ((deRhamDifferentialHom B p).val.app U).hom.toAddMonoidHom

/-- The de Rham differential commutes with restriction: it is a morphism of sheaves. -/
theorem deRhamGlobalOp_map (p : ℕ) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (s : (B.exteriorPower p).val.obj U) :
    deRhamGlobalOp B p V ((B.exteriorPower p).val.map f s) =
      (B.exteriorPower (p + 1)).val.map f (deRhamGlobalOp B p U s) :=
  PresheafOfModules.naturality_apply (deRhamDifferentialHom B p).val f s

/-- **The order-one commutator identity, as pure module algebra.** If an additive operator `D`
factors through an additive `C₁` on the sections coming from `C₀` — compatibly with the scalar
action — then the commutator identity for `D` on such a section is the commutator identity for
the factor `sw`.

This is the algebraic skeleton of the two steps below, separated out so that the rewriting is
done on abstract terms rather than on the sheafification `AlgebraicGeometry.SheafOfModules
.deRhamDifferentialHom` is built from. -/
private theorem commutator_smul_of_factorization {R₀ : Type*} [CommRing R₀]
    {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M']
    [AddCommGroup N'] [Module R₀ M] [Module R₀ N] [Module R₀ M'] [Module R₀ N']
    (D : M →+ N) (C₀ : M' → M) (C₁ : N' →+ N) (sw : M' →+ N')
    (hC₁ : ∀ (c : R₀) (x : N'), C₁ (c • x) = c • C₁ x)
    (key : ∀ (c : R₀) (w : M'), D (c • C₀ w) = C₁ (sw (c • w)))
    (key0 : ∀ w : M', D (C₀ w) = C₁ (sw w))
    (g r : R₀) (z : M')
    (hsw : sw (g • r • z) - g • sw (r • z) = r • (sw (g • z) - g • sw z)) :
    D (g • r • C₀ z) - g • D (r • C₀ z) = r • (D (g • C₀ z) - g • D (C₀ z)) := by
  rw [show g • r • C₀ z = (g * r) • C₀ z from (mul_smul g r _).symm, key, key, key, key0,
    mul_smul g r z, ← hC₁ g (sw (r • z)), ← hC₁ g (sw z), ← map_sub, ← map_sub, ← hC₁ r, hsw]

/-- **Descending the order-one commutator identity along a restriction map, as pure module
algebra.** If the restriction `resN` carries the values of `D` on the multiples of `s` to the
values of `D₁` on the multiples of `s₁`, then the commutator identity for `D₁` at `s₁` restricts
to the commutator identity for `D` at `s`. -/
private theorem commutator_smul_restrict {R₀ R₁ : Type*} [CommRing R₀] [CommRing R₁]
    {M N M₁ N₁ : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M₁] [AddCommGroup N₁]
    [Module R₀ M] [Module R₀ N] [Module R₁ M₁] [Module R₁ N₁]
    (ρ : R₀ →+* R₁) (D : M →+ N) (D₁ : M₁ →+ N₁) (resN : N →+ N₁)
    (g r : R₀) (s : M) (s₁ : M₁)
    (hresN : ∀ (c : R₀) (y : N), resN (c • y) = ρ c • resN y)
    (hD : ∀ c : R₀, resN (D (c • s)) = D₁ (ρ c • s₁))
    (hloc : D₁ (ρ g • ρ r • s₁) - ρ g • D₁ (ρ r • s₁) =
      ρ r • (D₁ (ρ g • s₁) - ρ g • D₁ s₁)) :
    resN (D (g • r • s) - g • D (r • s)) = resN (r • (D (g • s) - g • D s)) := by
  rw [show g • r • s = (g * r) • s from (mul_smul g r s).symm, map_sub, hresN, hresN, map_sub,
    hresN, hD, hD, hD, show resN (D s) = D₁ s₁ by simpa using hD 1, map_mul, mul_smul]
  exact hloc

/-- **The commutator identity on a section that comes from the sectionwise exterior powers.** On
such a section the differential is the sectionwise one, so the identity is the ring-level
statement of Tag 0G34. -/
theorem deRhamGlobalOp_commutator_smul_comparison (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (g r : X.sheaf.obj.obj U)
    (z : (PresheafOfModules.extPow.{u, u, u, u} p
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)).obj U) :
    deRhamGlobalOp B p U (g • r • (exactWedgeComparison B p).app U z) -
        g • deRhamGlobalOp B p U (r • (exactWedgeComparison B p).app U z) =
      r • (deRhamGlobalOp B p U (g • (exactWedgeComparison B p).app U z) -
        g • deRhamGlobalOp B p U ((exactWedgeComparison B p).app U z)) :=
  commutator_smul_of_factorization (R₀ := X.sheaf.obj.obj U) (deRhamGlobalOp B p U)
    (fun w => (exactWedgeComparison B p).app U w)
    ((exactWedgeComparison B (p + 1)).app U).hom.toAddMonoidHom
    (PresheafOfModules.sectionwiseDeRhamDifferentialApp φ.hom p U)
    (fun c x => PresheafOfModules.app_smul (exactWedgeComparison B (p + 1)) c x)
    (fun c w => (congrArg (fun y => deRhamGlobalOp B p U y)
        (PresheafOfModules.app_smul (exactWedgeComparison B p) c w).symm).trans
      (deRhamDifferentialHom_app_exactWedgeComparison B p U (c • w)))
    (fun w => deRhamDifferentialHom_app_exactWedgeComparison B p U w) g r z
    (PresheafOfModules.sectionwiseDeRhamDifferentialApp_commutator_smul φ.hom p U g r z)

/-- **The commutator identity on every local section.** Both sides are sections of a sheaf and
agree on the covering on which the section comes from the sectionwise exterior powers. -/
theorem deRhamGlobalOp_commutator_smul (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (g r : X.sheaf.obj.obj U) (s : (B.exteriorPower p).val.obj U) :
    deRhamGlobalOp B p U (g • r • s) - g • deRhamGlobalOp B p U (r • s) =
      r • (deRhamGlobalOp B p U (g • s) - g • deRhamGlobalOp B p U s) := by
  refine (B.exteriorPower (p + 1)).isSheaf.isSeparated (unop U)
    (Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map (exactWedgeComparison B p)) s)
    (mem_imageSieve_exactWedgeComparison B p U s) _ _ fun V f hf => ?_
  obtain ⟨z, hz⟩ := PresheafOfModules.exists_app_eq_of_mem_imageSieve
    (exactWedgeComparison B p) s f hf
  have hD : ∀ c : X.sheaf.obj.obj U, (B.exteriorPower (p + 1)).val.map f.op
      (deRhamGlobalOp B p U (c • s)) = deRhamGlobalOp B p (op V)
        (X.sheaf.obj.map f.op c • (exactWedgeComparison B p).app (op V) z) := fun c =>
    (deRhamGlobalOp_map B p f.op (c • s)).symm.trans
      (congrArg (fun y => deRhamGlobalOp B p (op V) y)
        (((B.exteriorPower p).val.map_smul f.op c s).trans
          (congrArg (fun y => X.sheaf.obj.map f.op c • y) hz.symm)))
  exact commutator_smul_restrict (X.sheaf.obj.map f.op).hom (deRhamGlobalOp B p U)
    (deRhamGlobalOp B p (op V))
    ((B.exteriorPower (p + 1)).val.restrictₛₗ f.op).toAddMonoidHom g r s
    ((exactWedgeComparison B p).app (op V) z)
    (fun c y => (B.exteriorPower (p + 1)).val.map_smul f.op c y) hD
    (deRhamGlobalOp_commutator_smul_comparison B p (op V)
      (X.sheaf.obj.map f.op g) (X.sheaf.obj.map f.op r) z)

/-- **Stacks Project, Tag 0G3Y.** For a morphism `φ : A ⟶ B` of sheaves of commutative rings on
a topological space, every differential `d : ⋀ᵖ Ω ⟶ ⋀ᵖ⁺¹ Ω` of the relative de Rham complex is a
differential operator of order at most one relative to `φ`. -/
@[stacks 0G3Y,
  stacks 0G3Z "the case of a morphism of ringed spaces f : X -> Y, at phi : f^{-1} O_Y -> O_X"]
theorem deRhamDifferentialHom_isGlobalDiffOpOfOrder_one (p : ℕ) :
    DiffOp.IsGlobalDiffOpOfOrder (underlyingRingHom (φ := φ)) 1 (deRhamGlobalOp B p) :=
  DiffOp.isGlobalDiffOpOfOrder_one_of_commutator_smul _ _
    (fun {_ _} f s => deRhamGlobalOp_map B p f s)
    (fun U a s => ((deRhamDifferentialHom B p).val.app U).hom.map_smul a s)
    (fun U g r s => deRhamGlobalOp_commutator_smul B p U g r s)

end AlgebraicGeometry.SheafOfModules

end
