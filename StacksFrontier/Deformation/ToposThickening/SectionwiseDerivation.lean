module

public import StacksFrontier.Deformation.ToposThickening.LiftingBetweenThickenings

/-!
# Section-wise derivations of sheaves of rings, and the group of derivations of a diagram

A *section-wise derivation* of a sheaf of commutative rings `R` with values in a sheaf of
modules `G` over another sheaf of commutative rings `O`, the scalars acting through a
homomorphism `c : R ⟶ O`, is a natural family of additive maps `R(U) ⟶ G(U)` satisfying the
Leibniz rule with the scalars read through `c`. It is the substrate of the derivations the
lemmas of [Stacks Project, Tag 08UG] and [Stacks Project, Tag 08U8] need: the derivations into
the ideal of a layer along a homomorphism, which twist that homomorphism
(`StacksFrontier/Deformation/ToposThickening/SquareZeroTwist.lean`), and the derivations of a
`Deformation.ToposThickening.DerivationSituation`, the group acting on the lifts of a diagram.

## Main definitions

* `Deformation.ToposThickening.SectionwiseDerivation`: a section-wise derivation, with its
  additive group.
* The additive group structure on `Deformation.ToposThickening.Derivation`, the group of
  clause (2) of the two lemmas in its concrete form, extending the zero and the sum that
  `StacksFrontier/Deformation/ToposThickening/LiftingBetweenThickenings.lean` defines.

## Implementation notes

The object is a bare section-wise family with its three laws and not a morphism in a category:
its source is a sheaf of rings and its target a module over a possibly different sheaf of
rings, so there is no one category in which it is a morphism. `map_one` and `map_zero` are not
fields: a derivation kills `1` because the Leibniz rule gives `δ 1 = δ 1 + δ 1`, and it kills
`0` by additivity.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Deformation.ToposThickening

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A composite of morphisms of sheaves of commutative rings, on sections. -/
public theorem sheafHom_comp_apply {F G H : Sheaf J CommRingCat.{w}} (f : F ⟶ G) (g : G ⟶ H)
    (U : Cᵒᵖ) (x : F.obj.obj U) :
    (f ≫ g).hom.app U x = g.hom.app U (f.hom.app U x) :=
  rfl

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

section

variable {J}

/-- A *section-wise derivation* of a sheaf of commutative rings `R` with values in a sheaf of
modules `G` over another sheaf of commutative rings `O`, the scalars acting through a
homomorphism `c : R ⟶ O`: a natural family of additive maps `R(U) ⟶ G(U)` satisfying the
Leibniz rule with the scalars read through `c`. -/
@[ext]
public structure SectionwiseDerivation (R : Sheaf J CommRingCat.{w})
    {O : Sheaf J CommRingCat.{w}}
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (c : R ⟶ O) where
  /-- The underlying section-wise map. -/
  toFun : ∀ U : Cᵒᵖ, R.obj.obj U → G.val.obj U
  /-- The map is additive on sections. -/
  map_add' : ∀ (U : Cᵒᵖ) (x y : R.obj.obj U), toFun U (x + y) = toFun U x + toFun U y
  /-- The map commutes with the restriction maps of the site. -/
  naturality : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) (x : R.obj.obj U),
    toFun V (R.obj.map h x) = show G.val.obj V from G.val.map h (toFun U x)
  /-- The Leibniz rule, the scalars acting through `c`. -/
  leibniz : ∀ (U : Cᵒᵖ) (x y : R.obj.obj U),
    toFun U (x * y) =
      toRingSection J (c.hom.app U x) • toFun U y +
        toRingSection J (c.hom.app U y) • toFun U x

namespace SectionwiseDerivation

variable {R O : Sheaf J CommRingCat.{w}}
  {G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {c : R ⟶ O}

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two section-wise derivations agreeing on every section are equal. -/
public theorem ext_apply {δ ε : SectionwiseDerivation R G c}
    (h : ∀ (U : Cᵒᵖ) (x : R.obj.obj U), δ.toFun U x = ε.toFun U x) : δ = ε :=
  SectionwiseDerivation.ext (funext₂ h)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A derivation kills the zero section. -/
public theorem map_zero (δ : SectionwiseDerivation R G c) (U : Cᵒᵖ) : δ.toFun U 0 = 0 :=
  _root_.map_zero (AddMonoidHom.mk' (δ.toFun U) (δ.map_add' U))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A derivation kills the unit section: the Leibniz rule at `1 * 1` gives
`δ 1 = δ 1 + δ 1`. -/
public theorem map_one (δ : SectionwiseDerivation R G c) (U : Cᵒᵖ) : δ.toFun U 1 = 0 := by
  have h := δ.leibniz U 1 1
  rw [mul_one] at h
  have h1 : toRingSection J (c.hom.app U (1 : R.obj.obj U)) =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U) := by
    show c.hom.app U (1 : R.obj.obj U) = 1
    simp
  rw [h1, one_smul] at h
  exact left_eq_add.mp h

/-- The zero derivation. -/
public instance : Zero (SectionwiseDerivation R G c) where
  zero :=
    { toFun := fun _ _ => 0
      map_add' := fun _ _ _ => (add_zero (0 : _)).symm
      naturality := fun h _ => ((G.val.map h).hom.map_zero).symm
      leibniz := fun _ _ _ => by simp }

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The value of the zero derivation. -/
@[simp]
public theorem zero_toFun (U : Cᵒᵖ) (x : R.obj.obj U) :
    (0 : SectionwiseDerivation R G c).toFun U x = 0 := rfl

/-- The sum of two derivations. -/
public instance : Add (SectionwiseDerivation R G c) where
  add δ ε :=
    { toFun := fun U x => δ.toFun U x + ε.toFun U x
      map_add' := fun U x y => by simp only [δ.map_add', ε.map_add']; abel
      naturality := fun h x => by
        simp only [δ.naturality, ε.naturality]
        exact (_root_.map_add _ _ _).symm
      leibniz := fun U x y => by simp only [δ.leibniz, ε.leibniz, smul_add]; abel }

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The value of a sum of derivations. -/
@[simp]
public theorem add_toFun (δ ε : SectionwiseDerivation R G c) (U : Cᵒᵖ) (x : R.obj.obj U) :
    (δ + ε).toFun U x = δ.toFun U x + ε.toFun U x := rfl

/-- The negative of a derivation. -/
public instance : Neg (SectionwiseDerivation R G c) where
  neg δ :=
    { toFun := fun U x => -δ.toFun U x
      map_add' := fun U x y => by rw [δ.map_add']; abel
      naturality := fun h x => by
        rw [δ.naturality]
        exact (map_neg _ _).symm
      leibniz := fun U x y => by rw [δ.leibniz, smul_neg, smul_neg]; abel }

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The value of the negative of a derivation. -/
@[simp]
public theorem neg_toFun (δ : SectionwiseDerivation R G c) (U : Cᵒᵖ) (x : R.obj.obj U) :
    (-δ).toFun U x = -δ.toFun U x := rfl

/-- The section-wise derivations of `R` into `G` along `c` form an additive commutative group
under pointwise addition. -/
public instance : AddCommGroup (SectionwiseDerivation R G c) :=
  { nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc := fun δ ε ζ => ext_apply fun _ _ => add_assoc _ _ _
    zero_add := fun δ => ext_apply fun _ _ => zero_add _
    add_zero := fun δ => ext_apply fun _ _ => add_zero _
    neg_add_cancel := fun δ => ext_apply fun _ _ => neg_add_cancel _
    add_comm := fun δ ε => ext_apply fun _ _ => add_comm _ _ }

end SectionwiseDerivation

namespace Derivation

variable {T : DerivationSituation J}

/-- The negative of a derivation of a situation. -/
public instance : Neg (Derivation T) where
  neg δ :=
    { toFun := fun U x => -δ.toFun U x
      map_add' := fun U x y => by rw [δ.map_add']; abel
      naturality := fun h x => by
        rw [δ.naturality]
        exact (map_neg _ _).symm
      leibniz := fun U x y => by rw [δ.leibniz, smul_neg, smul_neg]; abel
      map_kernel := fun U m => by rw [δ.map_kernel, neg_zero]
      map_base := fun U a => by rw [δ.map_base, neg_zero] }

/-- The value of the negative of a derivation. -/
@[simp]
public theorem neg_toFun (δ : Derivation T) (U : Cᵒᵖ) (x : T.O'.obj.obj U) :
    (-δ).toFun U x = -δ.toFun U x := rfl

/-- The derivations of a situation form an additive commutative group under pointwise
addition, extending the zero and the sum of
`StacksFrontier/Deformation/ToposThickening/LiftingBetweenThickenings.lean`. This is the group of
clause (2) of [Stacks Project, Tag 08UG] in its concrete form. -/
public instance : AddCommGroup (Derivation T) :=
  { nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc := fun δ ε ζ => ext_apply fun _ _ => add_assoc _ _ _
    zero_add := fun δ => ext_apply fun _ _ => zero_add _
    add_zero := fun δ => ext_apply fun _ _ => add_zero _
    neg_add_cancel := fun δ => ext_apply fun _ _ => neg_add_cancel _
    add_comm := fun δ ε => ext_apply fun _ _ => add_comm _ _ }

end Derivation

end

end Deformation.ToposThickening

end
