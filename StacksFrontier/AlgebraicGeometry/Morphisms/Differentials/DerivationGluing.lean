module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorGluing
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsFunctorial
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamDifferentialOperator
public import StacksFrontier.Topology.Sheaves.Modules.Differentials

/-!
# Relative derivations are the differential operators of order one that kill the constants

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a topological space. A
relative `φ`-derivation of `O₂` into itself is, by definition, an additive operator on the local
sections of `O₂` over every open which obeys the Leibniz rule, commutes with restriction and
annihilates the image of `φ`. This file identifies that data with a *differential operator of
order at most one* on the unit sheaf of modules which annihilates the unit section, and uses the
identification to glue a compatible family of local relative derivations into a global one.

The gluing is the point. Differential operators of order at most `k` glue along an arbitrary
open cover (`DiffOp.existsUnique_globalOp_of_cover`), because the order condition is local on the
base; derivations have no such gluing statement of their own, because the Leibniz rule and the
vanishing on `φ` are conditions on sections rather than on an order. Reading a derivation as an
order-one operator transports the gluing across, which is what produces a relative derivation
from local data.

## Main definitions

* `DiffOp.unitOp` and `DiffOp.RawOp.unitOp` — an operator on the unit sheaf of modules, read as a
  family of maps on the ring sections themselves.
* `AlgebraicGeometry.SheafOfModules.sheafDerivationOfOrderOne` — the relative derivation
  underlying an order-one operator which annihilates the unit section.
* `AlgebraicGeometry.SheafOfModules.globalOpOfSheafDerivation` — a relative derivation, read as a
  global differential operator.

## Main results

* `DiffOp.leibniz_of_isGlobalDiffOpOfOrder_one` and
  `DiffOp.apply_sectionRingHom_eq_zero_of_isGlobalDiffOpOfOrder_one` — an order-one operator on
  the unit sheaf which kills the unit section obeys the Leibniz rule and kills the scalars coming
  from `O₁`.
* `DiffOp.isGlobalDiffOpOfOrder_one_of_leibniz` and `DiffOp.isDiffOpOfOrder_one_of_leibniz` — the
  converse, globally and over a base object.
* `AlgebraicGeometry.SheafOfModules.existsUnique_sheafDerivation_of_cover` — **a compatible
  family of relative derivations on the members of an open cover glues to a unique relative
  derivation.**

## Implementation notes

The mathematical content of the identification is one line of ring algebra. Order at most one
says that the commutator `s ↦ D (g · s) - g · D s` is `O₂`-linear for every local section `g`;
evaluating that linearity at `s = 1` turns it into `D (g · r) - g · D r = r · (D g - g · D 1)`,
which with `D 1 = 0` is the Leibniz rule, and evaluating the `O₁`-linearity of `D` itself at
`s = 1` gives `D (φ a) = φ a · D 1 = 0`. No commutativity of the sections is used in either
direction, so both statements are proved for sheaves of rings.

What costs the work is that the sections of `SheafOfModules.unit O₂` over an open and the
sections of `O₂` there are the same type presented differently: the scalar action of the first is
the multiplication of the second, but the two are written at types the elaborator does not
identify, so a product of a ring section and a value of the operator picks up whichever of the
two instances the arguments happen to carry. `DiffOp.unitOp` is the operator read at the ring
sections, where the Leibniz rule is a statement about `*` alone; every algebraic step is taken
there, and the passage to the module spelling is by definitional equality only.

The order-one criterion over a base object is the global criterion
`DiffOp.isGlobalDiffOpOfOrder_one_of_commutator_smul` with the slices discharged by the
naturality of commutators and slices already available for a topological space, which is why it
is stated for `TopCat` rather than for a general site.

In the gluing, the glued operator annihilates the unit section because each of the given local
operators does — the Leibniz rule at `1 = 1 · 1` forces it — and a section of `𝒪` annihilated
in a neighbourhood of each of its points is zero. That is the only place the sheaf condition is
used; the Leibniz rule and the vanishing on `φ` of the glued operator are then supplied by the
order-one identification rather than proved again by gluing.

## References

* [Stacks Project, Tag 09CR](https://stacks.math.columbia.edu/tag/09CR)
* [Stacks Project, Tag 09CM](https://stacks.math.columbia.edu/tag/09CM)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace DiffOp

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {O₁ O₂ : Sheaf J RingCat}

section Order

/-- **Naturality of a differential operator at an arbitrary morphism of the site.** -/
theorem map_apply_of_isGlobalDiffOpOfOrder (φ : O₁ ⟶ O₂) (k : ℕ) {F G : SheafOfModules O₂}
    (D : GlobalOp F G) (hD : IsGlobalDiffOpOfOrder φ k D) {Y Y' : Cᵒᵖ} (f : Y ⟶ Y')
    (s : F.val.obj Y) :
    D Y' (F.val.map f s) = G.val.map f (D Y s) :=
  RawOp.isNatural_of_isDiffOpOfOrder φ k _ (hD Y.unop)
    (Over.mk f.unop) (Over.mk (CategoryStruct.id Y.unop))
    (Over.homMk f.unop (by simp)) s

/-- **The scalars coming from `O₁` pass through a differential operator of positive order.** -/
theorem smul_apply_of_isGlobalDiffOpOfOrder_succ (φ : O₁ ⟶ O₂) (k : ℕ)
    {F G : SheafOfModules O₂} (D : GlobalOp F G) (hD : IsGlobalDiffOpOfOrder φ (k + 1) D)
    (Y : Cᵒᵖ) (a : O₁.obj.obj Y) (s : F.val.obj Y) :
    D Y (sectionRingHom φ Y a • s) = sectionRingHom φ Y a • D Y s :=
  (hD Y.unop).2.1 (Over.mk (CategoryStruct.id Y.unop)) a s

/-- **The order-one commutator identity, with the slices discharged.** This is the converse of
`DiffOp.isGlobalDiffOpOfOrder_one_of_commutator_smul`. -/
theorem commutator_smul_of_isGlobalDiffOpOfOrder_one (φ : O₁ ⟶ O₂) {F G : SheafOfModules O₂}
    (D : GlobalOp F G) (hD : IsGlobalDiffOpOfOrder φ 1 D) (Y : Cᵒᵖ) (g r : O₂.obj.obj Y)
    (s : F.val.obj Y) :
    D Y (g • r • s) - g • D Y (r • s) = r • (D Y (g • s) - g • D Y s) := by
  have h := ((hD Y.unop).2.2 (Over.mk (CategoryStruct.id Y.unop)) g).2
    (Over.mk (CategoryStruct.id Y.unop)) r s
  simpa [RawOp.commutator, GlobalOp.restrict] using h

end Order

section Unit

/-- **An operator on the unit sheaf of modules, read on the ring sections themselves.** The
sections of `SheafOfModules.unit O₂` over an object are the sections of `O₂` there and the
scalar action is the multiplication, so this is the same function; naming it lets the
Leibniz rule be stated and manipulated inside the ring of sections. -/
noncomputable def unitOp (D : GlobalOp (SheafOfModules.unit O₂) (SheafOfModules.unit O₂))
    (Y : Cᵒᵖ) (s : O₂.obj.obj Y) : O₂.obj.obj Y :=
  D Y s

variable (φ : O₁ ⟶ O₂) (D : GlobalOp (SheafOfModules.unit O₂) (SheafOfModules.unit O₂))

/-- A Leibniz map makes the commutator with left multiplication linear. -/
private theorem leibniz_commutator_mul {R : Type*} [NonUnitalRing R] (f : R → R)
    (hleib : ∀ a b, f (a * b) = a * f b + b * f a) (g r s : R) :
    f (g * (r * s)) - g * f (r * s) = r * (f (g * s) - g * f s) := by
  rw [hleib g (r * s), hleib g s, add_sub_cancel_left, add_sub_cancel_left]
  exact mul_assoc r s (f g)

/-- A Leibniz map is linear over the elements on which it vanishes. -/
private theorem leibniz_mul_of_apply_eq_zero {R : Type*} [NonUnitalNonAssocSemiring R] (f : R → R)
    (hleib : ∀ a b, f (a * b) = a * f b + b * f a) {x : R} (hx : f x = 0) (s : R) :
    f (x * s) = x * f s := by
  rw [hleib x s, hx, mul_zero, add_zero]

/-- **Order one plus annihilating the unit section gives the Leibniz rule.** -/
theorem leibniz_of_isGlobalDiffOpOfOrder_one (hD : IsGlobalDiffOpOfOrder φ 1 D)
    (hone : ∀ Y : Cᵒᵖ, unitOp D Y 1 = 0) (Y : Cᵒᵖ) (a b : O₂.obj.obj Y) :
    unitOp D Y (a * b) = a * unitOp D Y b + b * unitOp D Y a := by
  have h : unitOp D Y (a * (b * 1)) - a * unitOp D Y (b * 1) =
      b * (unitOp D Y (a * 1) - a * unitOp D Y 1) :=
    commutator_smul_of_isGlobalDiffOpOfOrder_one φ D hD Y a b (1 : O₂.obj.obj Y)
  rw [mul_one, mul_one, hone Y, mul_zero, sub_zero] at h
  rw [← sub_eq_iff_eq_add', h]

/-- **An order-one operator on the unit sheaf annihilating the unit section annihilates every
scalar coming from `O₁`.** -/
theorem apply_sectionRingHom_eq_zero_of_isGlobalDiffOpOfOrder_one
    (hD : IsGlobalDiffOpOfOrder φ 1 D) (hone : ∀ Y : Cᵒᵖ, unitOp D Y 1 = 0)
    (Y : Cᵒᵖ) (a : O₁.obj.obj Y) :
    unitOp D Y (sectionRingHom φ Y a) = 0 := by
  have h : unitOp D Y (sectionRingHom φ Y a * 1) =
      sectionRingHom φ Y a * unitOp D Y 1 :=
    smul_apply_of_isGlobalDiffOpOfOrder_succ φ 0 D hD Y a (1 : O₂.obj.obj Y)
  rw [mul_one] at h
  rw [h, hone Y, mul_zero]

/-- **The Leibniz rule, with the vanishing on the scalars from `O₁`, makes an operator on the
unit sheaf one of order at most one.** -/
theorem isGlobalDiffOpOfOrder_one_of_leibniz
    (hnat : ∀ {Y Y' : Cᵒᵖ} (f : Y ⟶ Y') (s : (SheafOfModules.unit O₂).val.obj Y),
      D Y' ((SheafOfModules.unit O₂).val.map f s) =
        (SheafOfModules.unit O₂).val.map f (D Y s))
    (hleib : ∀ (Y : Cᵒᵖ) (a b : O₂.obj.obj Y),
      unitOp D Y (a * b) = a * unitOp D Y b + b * unitOp D Y a)
    (hker : ∀ (Y : Cᵒᵖ) (a : O₁.obj.obj Y), unitOp D Y (sectionRingHom φ Y a) = 0) :
    IsGlobalDiffOpOfOrder φ 1 D := by
  exact isGlobalDiffOpOfOrder_one_of_commutator_smul φ D (fun f s => hnat f s)
    (fun Y a s => leibniz_mul_of_apply_eq_zero (unitOp D Y) (hleib Y) (hker Y a) s)
    (fun Y g r s => leibniz_commutator_mul (unitOp D Y) (hleib Y) g r s)

/-- **An operator over a base object on the unit sheaf of modules, read on the ring sections.**
This is `DiffOp.unitOp` for an operator defined only over a base object. -/
noncomputable def RawOp.unitOp {U : C}
    (D : RawOp (SheafOfModules.unit O₂) (SheafOfModules.unit O₂) U) (Y : Over U)
    (s : O₂.obj.obj (op Y.left)) : O₂.obj.obj (op Y.left) :=
  D Y s

/-- **An operator over a base object which obeys the Leibniz rule and annihilates the scalars
from `O₁` has order at most one.** -/
theorem isDiffOpOfOrder_one_of_leibniz {T : TopCat.{u}} {R₁ R₂ : TopCat.Sheaf RingCat.{u} T}
    (ψ : R₁ ⟶ R₂) {V : Opens T}
    (E : RawOp (SheafOfModules.unit R₂) (SheafOfModules.unit R₂) V) (hnat : E.IsNatural)
    (hleib : ∀ (Y : Over V) (a b : R₂.obj.obj (op Y.left)),
      E.unitOp Y (a * b) = a * E.unitOp Y b + b * E.unitOp Y a)
    (hker : ∀ (Y : Over V) (a : R₁.obj.obj (op Y.left)),
      E.unitOp Y (sectionRingHom ψ (op Y.left) a) = 0) :
    IsDiffOpOfOrder ψ 1 E := by
  exact ⟨hnat, fun Y a s => leibniz_mul_of_apply_eq_zero (E.unitOp Y) (hleib Y) (hker Y a) s,
    fun Y g =>
    ⟨AlgebraicGeometry.AffineDiffOp.raw_commutator_natural
      (AlgebraicGeometry.AffineDiffOp.raw_slice_natural hnat Y) g,
      fun Z r s =>
      leibniz_commutator_mul (E.unitOp (Over.mk (Z.hom ≫ Y.hom))) (hleib _) _ r s⟩⟩

/-- **An operator obeying the Leibniz rule annihilates the unit section.** -/
theorem RawOp.unitOp_one_eq_zero {U : C}
    (D : RawOp (SheafOfModules.unit O₂) (SheafOfModules.unit O₂) U) (Y : Over U)
    (hleib : ∀ (a b : O₂.obj.obj (op Y.left)),
      D.unitOp Y (a * b) = a * D.unitOp Y b + b * D.unitOp Y a) :
    D.unitOp Y 1 = 0 := by
  have h := hleib 1 1
  rw [one_mul, one_mul] at h
  exact left_eq_add.mp h

end Unit

end DiffOp

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} (φ : A ⟶ X.sheaf)
  (D : DiffOp.GlobalOp (SheafOfModules.unit (underlyingRingSheaf X.sheaf))
    (SheafOfModules.unit (underlyingRingSheaf X.sheaf)))

/-- **A differential operator of order at most one on the structure sheaf which annihilates the
unit section is a relative derivation.** -/
noncomputable def sheafDerivationOfOrderOne
    (hD : DiffOp.IsGlobalDiffOpOfOrder (underlyingRingHom (φ := φ)) 1 D)
    (hone : ∀ W : (Opens X.carrier)ᵒᵖ, DiffOp.unitOp D W 1 = 0) :
    SheafDerivation φ (SheafOfModules.unit (underlyingRingSheaf X.sheaf)) where
  d {W} := D W
  d_mul a b :=
    DiffOp.leibniz_of_isGlobalDiffOpOfOrder_one (underlyingRingHom (φ := φ)) D hD hone _ a b
  d_map f x := DiffOp.map_apply_of_isGlobalDiffOpOfOrder (underlyingRingHom (φ := φ)) 1 D hD f x
  d_app a :=
    DiffOp.apply_sectionRingHom_eq_zero_of_isGlobalDiffOpOfOrder_one
      (underlyingRingHom (φ := φ)) D hD hone _ a

/-- **A relative derivation, read as a global differential operator.** -/
noncomputable def globalOpOfSheafDerivation
    (E : SheafDerivation φ (SheafOfModules.unit (underlyingRingSheaf X.sheaf))) :
    DiffOp.GlobalOp (SheafOfModules.unit (underlyingRingSheaf X.sheaf))
      (SheafOfModules.unit (underlyingRingSheaf X.sheaf)) :=
  fun W => E.d (X := W)

/-- **A relative derivation is a differential operator of order at most one.** -/
theorem isGlobalDiffOpOfOrder_one_globalOpOfSheafDerivation
    (E : SheafDerivation φ (SheafOfModules.unit (underlyingRingSheaf X.sheaf))) :
    DiffOp.IsGlobalDiffOpOfOrder (underlyingRingHom (φ := φ)) 1
      (globalOpOfSheafDerivation φ E) :=
  DiffOp.isGlobalDiffOpOfOrder_one_of_leibniz _ _ (fun f s => E.d_map f s)
    (fun _ a b => E.d_mul a b) (fun _ a => E.d_app a)

/-- **Gluing relative derivations along an open cover.** A family of derivations of the structure
sheaf relative to `φ`, each defined on the opens contained in one member of an open cover and
agreeing on the opens contained in two members, glues to a unique relative derivation on the
whole space. -/
theorem existsUnique_sheafDerivation_of_cover {ι : Type*} (U : ι → Opens X.carrier)
    (hU : ∀ p : X.carrier, ∃ i, p ∈ U i)
    (d : ∀ i, DiffOp.RawOp (SheafOfModules.unit (underlyingRingSheaf X.sheaf))
      (SheafOfModules.unit (underlyingRingSheaf X.sheaf)) (U i))
    (hnat : ∀ i, (d i).IsNatural)
    (hleib : ∀ (i : ι) (Y : Over (U i))
      (a b : (underlyingRingSheaf X.sheaf).obj.obj (op Y.left)),
      (d i).unitOp Y (a * b) = a * (d i).unitOp Y b + b * (d i).unitOp Y a)
    (hker : ∀ (i : ι) (Y : Over (U i)) (a : (underlyingRingSheaf A).obj.obj (op Y.left)),
      (d i).unitOp Y
        (DiffOp.sectionRingHom (underlyingRingHom (φ := φ)) (op Y.left) a) = 0)
    (hagree : DiffOp.AgreeOnCover U d) :
    ∃! E : SheafDerivation φ (SheafOfModules.unit (underlyingRingSheaf X.sheaf)),
      ∀ i, (globalOpOfSheafDerivation φ E).restrict (U i) = d i := by
  have hd : ∀ i, DiffOp.IsDiffOpOfOrder (underlyingRingHom (φ := φ)) 1 (d i) :=
    fun i => DiffOp.isDiffOpOfOrder_one_of_leibniz _ (d i) (hnat i) (hleib i) (hker i)
  obtain ⟨E, ⟨hEord, hEres⟩, huniq⟩ :=
    DiffOp.existsUnique_globalOp_of_cover (underlyingRingHom (φ := φ))
      (fun V r s => mul_comm (G := X.sheaf.obj.obj V) r s) U hU d hd hagree
  have honed : ∀ (i : ι) (Y : Over (U i)), (d i).unitOp Y 1 = 0 :=
    fun i Y => DiffOp.RawOp.unitOp_one_eq_zero (d i) Y (hleib i Y)
  have hone : ∀ W : (Opens X.carrier)ᵒᵖ, DiffOp.unitOp E W 1 = 0 := by
    intro W
    obtain ⟨V⟩ := W
    refine TopCat.Presheaf.IsSheaf.section_ext
      (SheafOfModules.unit (underlyingRingSheaf X.sheaf)).isSheaf ?_
    intro p hp
    obtain ⟨i, hi⟩ := hU p
    refine ⟨V ⊓ U i, inf_le_left, ⟨hp, hi⟩, ?_⟩
    have hE2 : E (op (V ⊓ U i)) = d i (Over.mk (homOfLE (inf_le_right : V ⊓ U i ≤ U i))) :=
      congrFun (hEres i) (Over.mk (homOfLE (inf_le_right : V ⊓ U i ≤ U i)))
    have hres1 : (SheafOfModules.unit (underlyingRingSheaf X.sheaf)).val.map
        (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op
        (1 : (underlyingRingSheaf X.sheaf).obj.obj (op V)) =
        (1 : (underlyingRingSheaf X.sheaf).obj.obj (op (V ⊓ U i))) :=
      PresheafOfModules.unit_map_one _ _
    have hone1 : E (op (V ⊓ U i))
        ((SheafOfModules.unit (underlyingRingSheaf X.sheaf)).val.map
          (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op
          (1 : (underlyingRingSheaf X.sheaf).obj.obj (op V))) = 0 :=
      (DFunLike.congr_arg (E (op (V ⊓ U i))) hres1).trans
        ((DFunLike.congr_fun hE2
          (1 : (underlyingRingSheaf X.sheaf).obj.obj (op (V ⊓ U i)))).trans (honed i _))
    have key : (SheafOfModules.unit (underlyingRingSheaf X.sheaf)).val.map
        (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op
        (E (op V) (1 : (underlyingRingSheaf X.sheaf).obj.obj (op V))) = 0 :=
      (DiffOp.map_apply_of_isGlobalDiffOpOfOrder (underlyingRingHom (φ := φ)) 1 E hEord
        (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op
        (1 : (underlyingRingSheaf X.sheaf).obj.obj (op V))).symm.trans hone1
    exact key.trans (map_zero _).symm
  refine ⟨sheafDerivationOfOrderOne φ E hEord hone, hEres, ?_⟩
  intro E' hE'
  refine PresheafOfModulesOfCommRing.Derivation.ext ?_
  funext W
  exact congrFun (huniq (globalOpOfSheafDerivation φ E')
    ⟨isGlobalDiffOpOfOrder_one_globalOpOfSheafDerivation φ E', hE'⟩) W

end AlgebraicGeometry.SheafOfModules

end
