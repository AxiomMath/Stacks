module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardTransport
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower

/-!
# Transporting tensor powers along a functor with object-level comparisons

Let `O₁` and `O₂` be sheaves of commutative rings on two sites and let

`F : Mod(O₁) ⥤ Mod(O₂)`

be a functor carrying the structure sheaf to the structure sheaf and the tensor product sheaf of
Tag 01CA to the tensor product sheaf, *on objects only*: the data
`Stacks.SheafOfModules.Picard.UnitIso` and `Stacks.SheafOfModules.Picard.TensorIso`. Such an `F`
carries the tensor powers of Tag 01CU at a natural exponent to tensor powers:

`F(L^{⊗ k}) ≅ (F L)^{⊗ k}`.

This comparison is natural in `L` once the tensor comparison is itself natural in both arguments,
`TensorIsoNatural`. The object-level data alone does not give this: replacing the tensor
comparison at each pair `(L, N)` by its composite with an arbitrary automorphism of `F L ⊗ F N`
leaves the data intact and destroys every naturality square.

## Main definitions

* `Stacks.SheafOfModules.TensorPowerTransport.powerMapOf`: **the `k`-th tensor power of an
  isomorphism of invertible sheaves of modules**, at a natural exponent and over an arbitrary
  sheaf of commutative rings on an arbitrary site.
* `Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural`: naturality of an object-level
  tensor comparison in both arguments.
* `Stacks.SheafOfModules.TensorPowerTransport.powerTransport`: the comparison
  `F(L^{⊗ k}) ≅ (F L)^{⊗ k}`, with the invertibility of `F L` as an instance argument.
* `Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso`: **the same comparison, with the
  invertibility of `F L` discharged** from the two object-level comparisons.

## Main results

* `Stacks.SheafOfModules.TensorPowerTransport.tensorProductIso_trans`: two tensor products of
  isomorphisms compose into the tensor product of the composites.
* `Stacks.SheafOfModules.TensorPowerTransport.powerMapOf_succ_comm`: the square relating the two
  successor comparisons along the `k`-th power of an isomorphism and the isomorphism itself.
* `Stacks.SheafOfModules.TensorPowerTransport.powerTransport_succ_comm`: the same square for the
  transport.
* `Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_naturality`: **the comparison is
  natural in `L`**, given the naturality of the tensor comparison.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u v₁ u₁ v₂ u₂ w

namespace Stacks.SheafOfModules.TensorPowerTransport

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)
open Stacks.SheafOfModules.Invertible
  (tensorPower tensorPowerSuccIso tensorProductIso tensorProductBifunctor)

/- `Stacks.SheafOfModules.Tensor.ringSheaf` and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` are the same sheaf of rings after
unfolding both definitions. -/
attribute [local implicit_reducible] TensorSheafification.structureSheaf Tensor.ringSheaf

/-! ### Tensor powers of an isomorphism, over one sheaf of rings -/

section OneSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w}) (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Two tensor products of isomorphisms compose into the tensor product of the composites.**
This is functoriality of `Stacks.SheafOfModules.Invertible.tensorProductBifunctor`. -/
theorem tensorProductIso_trans {A A' A'' B B' B'' : SheafOfModules.{w} (structureSheaf O hO)}
    (a : A ≅ A') (a' : A' ≅ A'') (b : B ≅ B') (b' : B' ≅ B'') :
    tensorProductIso O hO a b ≪≫ tensorProductIso O hO a' b' =
      tensorProductIso O hO (a ≪≫ a') (b ≪≫ b') :=
  Iso.ext (((tensorProductBifunctor O hO).map_comp (X := (A, B)) (Y := (A', B'))
    (Z := (A'', B'')) (Iso.prod a b).hom (Iso.prod a' b').hom).symm)

/-- **The `k`-th tensor power of an isomorphism of invertible sheaves of modules**, at a natural
exponent: the successor comparison conjugates the tensor product of the `k`-th power
of the isomorphism with the isomorphism itself. -/
noncomputable def powerMapOf {L M : SheafOfModules.{w} (structureSheaf O hO)}
    [IsInvertible O hO L] [IsInvertible O hO M] (e : L ≅ M) :
    (k : ℕ) → tensorPower O hO L (k : ℤ) ≅ tensorPower O hO M (k : ℤ)
  | 0 => Iso.refl _
  | k + 1 => ((tensorPowerSuccIso O hO L (k : ℤ)).symm ≪≫
      tensorProductIso O hO (powerMapOf e k) e) ≪≫ tensorPowerSuccIso O hO M (k : ℤ)

/-- The tensor power of an isomorphism at a successor exponent. -/
theorem powerMapOf_succ {L M : SheafOfModules.{w} (structureSheaf O hO)}
    [IsInvertible O hO L] [IsInvertible O hO M] (e : L ≅ M) (k : ℕ) :
    powerMapOf O hO e (k + 1) = ((tensorPowerSuccIso O hO L (k : ℤ)).symm ≪≫
      tensorProductIso O hO (powerMapOf O hO e k) e) ≪≫ tensorPowerSuccIso O hO M (k : ℤ) := rfl

/-- **The successor square for tensor powers of an isomorphism**: the two successor comparisons
are related along the `k`-th power of `e` tensored with `e` and the `(k+1)`-st power of `e`. This
is naturality of `Stacks.SheafOfModules.Invertible.tensorPowerSuccIso` in the invertible module,
at a natural exponent. -/
theorem powerMapOf_succ_comm {L M : SheafOfModules.{w} (structureSheaf O hO)}
    [IsInvertible O hO L] [IsInvertible O hO M] (e : L ≅ M) (k : ℕ) :
    (tensorProductIso O hO (powerMapOf O hO e k) e).hom ≫
        (tensorPowerSuccIso O hO M (k : ℤ)).hom =
      (tensorPowerSuccIso O hO L (k : ℤ)).hom ≫ (powerMapOf O hO e (k + 1)).hom := by
  rw [powerMapOf_succ]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

end OneSite

/-! ### Transporting a tensor power along a functor -/

section TwoSites

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  (O₁ : C₁ᵒᵖ ⥤ CommRingCat.{w}) (hO₁ : Presheaf.IsSheaf J₁ (structureRingPresheaf O₁))
  [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₁ AddCommGrpCat.{w}]
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  (O₂ : C₂ᵒᵖ ⥤ CommRingCat.{w}) (hO₂ : Presheaf.IsSheaf J₂ (structureRingPresheaf O₂))
  [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₂ AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (structureSheaf O₁ hO₁) ⥤ SheafOfModules.{w} (structureSheaf O₂ hO₂))

/-- **Naturality of an object-level tensor comparison** `hten` in both arguments: for
isomorphisms `e : L ≅ L'` and `f : N ≅ N'`, the image under `F` of `e ⊗ f` followed by
`hten L' N'` is `hten L N` followed by `F e ⊗ F f`. -/
def TensorIsoNatural (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F) : Prop :=
  ∀ (L N L' N' : SheafOfModules.{w} (structureSheaf O₁ hO₁)) (e : L ≅ L') (f : N ≅ N'),
    F.map (tensorProductIso O₁ hO₁ e f).hom ≫ (hten L' N').hom =
      (hten L N).hom ≫ (tensorProductIso O₂ hO₂ (F.mapIso e) (F.mapIso f)).hom

/-- **The image of an invertible sheaf of modules is invertible**: this is
`Stacks.SheafOfModules.Picard.isInvertible_map_obj`, with the invertibility of the source taken
as an instance argument. -/
theorem isInvertible_obj (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F)
    (L : SheafOfModules.{w} (structureSheaf O₁ hO₁)) [hL : IsInvertible O₁ hO₁ L] :
    IsInvertible O₂ hO₂ (F.obj L) :=
  Picard.isInvertible_map_obj O₁ hO₁ O₂ hO₂ F hunit hten L hL

/-- The comparison `F(L^{⊗ k}) ≅ (F L)^{⊗ k}`, with the invertibility of `F L` as an instance
argument. At a successor exponent the composite is

`F(L^{⊗(k+1)}) ≅ F(L^{⊗ k} ⊗ L) ≅ F(L^{⊗ k}) ⊗ F L ≅ (F L)^{⊗ k} ⊗ F L ≅ (F L)^{⊗(k+1)}`:

the successor comparison, the object-level tensor comparison, the induction
hypothesis, and the successor comparison again.  At the zero exponent both powers are the
structure sheaf by `Stacks.SheafOfModules.Invertible.tensorPower_zero`, so the base case is the
unit comparison itself. -/
noncomputable def powerTransport (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F)
    (L : SheafOfModules.{w} (structureSheaf O₁ hO₁))
    [IsInvertible O₁ hO₁ L] [IsInvertible O₂ hO₂ (F.obj L)] :
    (k : ℕ) → F.obj (tensorPower O₁ hO₁ L (k : ℤ)) ≅ tensorPower O₂ hO₂ (F.obj L) (k : ℤ)
  | 0 => hunit
  | k + 1 =>
      ((F.mapIso (tensorPowerSuccIso O₁ hO₁ L (k : ℤ)).symm ≪≫
            hten (tensorPower O₁ hO₁ L (k : ℤ)) L) ≪≫
          tensorProductIso O₂ hO₂ (powerTransport hunit hten L k) (Iso.refl (F.obj L))) ≪≫
        tensorPowerSuccIso O₂ hO₂ (F.obj L) (k : ℤ)

/-- The transport of a tensor power at a successor exponent. -/
theorem powerTransport_succ (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F)
    (L : SheafOfModules.{w} (structureSheaf O₁ hO₁))
    [IsInvertible O₁ hO₁ L] [IsInvertible O₂ hO₂ (F.obj L)] (k : ℕ) :
    powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L (k + 1) =
      ((F.mapIso (tensorPowerSuccIso O₁ hO₁ L (k : ℤ)).symm ≪≫
            hten (tensorPower O₁ hO₁ L (k : ℤ)) L) ≪≫
          tensorProductIso O₂ hO₂ (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L k)
            (Iso.refl (F.obj L))) ≪≫
        tensorPowerSuccIso O₂ hO₂ (F.obj L) (k : ℤ) := rfl

/-- **The successor square for the transport**: the image under `F` of the successor comparison,
followed by the transport at `k + 1`, is the tensor comparison followed by the tensor product of
the transport at `k` with the identity and the successor comparison on the other site. -/
theorem powerTransport_succ_comm (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F)
    (L : SheafOfModules.{w} (structureSheaf O₁ hO₁))
    [IsInvertible O₁ hO₁ L] [IsInvertible O₂ hO₂ (F.obj L)] (k : ℕ) :
    (hten (tensorPower O₁ hO₁ L (k : ℤ)) L).hom ≫
        (tensorProductIso O₂ hO₂ (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L k)
          (Iso.refl (F.obj L))).hom ≫ (tensorPowerSuccIso O₂ hO₂ (F.obj L) (k : ℤ)).hom =
      F.map (tensorPowerSuccIso O₁ hO₁ L (k : ℤ)).hom ≫
        (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L (k + 1)).hom := by
  rw [powerTransport_succ]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  conv_rhs => rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]

/-- If the transport at `k` is natural along `e`, as an equality `ih` of isomorphisms, then the
image under `F` of the tensor product of the `k`-th power of `e` with `e`, followed by the tensor
comparison and the tensor product of the transport at `k` with the identity, equals the tensor
comparison followed by the tensor product of the transport at `k` with the identity and the
tensor product of the `k`-th power of `F e` with `F e`; both sides are then composed with `h`. -/
theorem powerTransport_naturality_step (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F) (hnat : TensorIsoNatural O₁ hO₁ O₂ hO₂ F hten)
    {L M : SheafOfModules.{w} (structureSheaf O₁ hO₁)}
    [IsInvertible O₁ hO₁ L] [IsInvertible O₁ hO₁ M]
    [IsInvertible O₂ hO₂ (F.obj L)] [IsInvertible O₂ hO₂ (F.obj M)] (e : L ≅ M) (k : ℕ)
    {W : SheafOfModules.{w} (structureSheaf O₂ hO₂)}
    (h : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O₂, Presheaf.isSheaf_of_isSheaf_comp _ O₂ (forget₂ CommRingCat RingCat) hO₂⟩).obj
      (tensorPower O₂ hO₂ (F.obj M) (k : ℤ))).obj (F.obj M) ⟶ W)
    (ih : F.mapIso (powerMapOf O₁ hO₁ e k) ≪≫ powerTransport O₁ hO₁ O₂ hO₂ F hunit hten M k =
      powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L k ≪≫ powerMapOf O₂ hO₂ (F.mapIso e) k) :
    F.map (tensorProductIso O₁ hO₁ (powerMapOf O₁ hO₁ e k) e).hom ≫
        (hten (tensorPower O₁ hO₁ M (k : ℤ)) M).hom ≫
        (tensorProductIso O₂ hO₂ (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten M k)
          (Iso.refl (F.obj M))).hom ≫ h =
      (hten (tensorPower O₁ hO₁ L (k : ℤ)) L).hom ≫
        (tensorProductIso O₂ hO₂ (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L k)
          (Iso.refl (F.obj L))).hom ≫
        (tensorProductIso O₂ hO₂ (powerMapOf O₂ hO₂ (F.mapIso e) k) (F.mapIso e)).hom ≫ h := by
  have key : (tensorProductIso O₂ hO₂ (F.mapIso (powerMapOf O₁ hO₁ e k)) (F.mapIso e)).hom ≫
        (tensorProductIso O₂ hO₂ (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten M k)
          (Iso.refl (F.obj M))).hom =
      (tensorProductIso O₂ hO₂ (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L k)
          (Iso.refl (F.obj L))).hom ≫
        (tensorProductIso O₂ hO₂ (powerMapOf O₂ hO₂ (F.mapIso e) k) (F.mapIso e)).hom := by
    rw [← Iso.trans_hom, ← Iso.trans_hom, tensorProductIso_trans, tensorProductIso_trans, ih,
      Iso.trans_refl, Iso.refl_trans]
  have mid : (F.map (tensorProductIso O₁ hO₁ (powerMapOf O₁ hO₁ e k) e).hom ≫
        (hten (tensorPower O₁ hO₁ M (k : ℤ)) M).hom) ≫
      (tensorProductIso O₂ hO₂ (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten M k)
        (Iso.refl (F.obj M))).hom =
      ((hten (tensorPower O₁ hO₁ L (k : ℤ)) L).hom ≫
        (tensorProductIso O₂ hO₂ (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L k)
          (Iso.refl (F.obj L))).hom) ≫
        (tensorProductIso O₂ hO₂ (powerMapOf O₂ hO₂ (F.mapIso e) k) (F.mapIso e)).hom := by
    rw [hnat (tensorPower O₁ hO₁ L (k : ℤ)) L (tensorPower O₁ hO₁ M (k : ℤ)) M
      (powerMapOf O₁ hO₁ e k) e, Category.assoc, Category.assoc, key]
  simp only [← Category.assoc]
  exact congrArg (fun z => z ≫ h) mid

/-- **The transport of tensor powers is natural in the invertible module**, given the naturality
of the object-level tensor comparison. -/
theorem powerTransport_naturality (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F) (hnat : TensorIsoNatural O₁ hO₁ O₂ hO₂ F hten)
    {L M : SheafOfModules.{w} (structureSheaf O₁ hO₁)}
    [IsInvertible O₁ hO₁ L] [IsInvertible O₁ hO₁ M]
    [IsInvertible O₂ hO₂ (F.obj L)] [IsInvertible O₂ hO₂ (F.obj M)] (e : L ≅ M) :
    (k : ℕ) → F.map (powerMapOf O₁ hO₁ e k).hom ≫
          (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten M k).hom =
        (powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L k).hom ≫
          (powerMapOf O₂ hO₂ (F.mapIso e) k).hom
  | 0 => by
      show F.map (𝟙 (SheafOfModules.unit (structureSheaf O₁ hO₁))) ≫ hunit.hom =
        hunit.hom ≫ 𝟙 (SheafOfModules.unit (structureSheaf O₂ hO₂))
      rw [F.map_id, Category.id_comp, Category.comp_id]
  | k + 1 => by
      refine (Iso.cancel_iso_hom_left
        (F.mapIso (tensorPowerSuccIso O₁ hO₁ L (k : ℤ))) _ _).1 ?_
      rw [Functor.mapIso_hom]
      conv_lhs => rw [← Category.assoc, ← F.map_comp, ← powerMapOf_succ_comm, F.map_comp,
        Category.assoc, ← powerTransport_succ_comm]
      conv_rhs => rw [← Category.assoc, ← powerTransport_succ_comm, Category.assoc,
        Category.assoc, ← powerMapOf_succ_comm]
      exact powerTransport_naturality_step O₁ hO₁ O₂ hO₂ F hunit hten hnat e k _
        (Iso.ext (powerTransport_naturality hunit hten hnat e k))

/-- **`F(L^{⊗ k}) ≅ (F L)^{⊗ k}`, at a natural exponent, from the object-level unit and tensor
comparisons of `F`.**  This is
`Stacks.SheafOfModules.TensorPowerTransport.powerTransport` with the invertibility of `F L`
supplied by `Stacks.SheafOfModules.TensorPowerTransport.isInvertible_obj`. -/
noncomputable def powerTransportIso (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F)
    (L : SheafOfModules.{w} (structureSheaf O₁ hO₁)) [IsInvertible O₁ hO₁ L] (k : ℕ) :
    F.obj (tensorPower O₁ hO₁ L (k : ℤ)) ≅
      letI := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten L
      tensorPower O₂ hO₂ (F.obj L) (k : ℤ) :=
  letI := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten L
  powerTransport O₁ hO₁ O₂ hO₂ F hunit hten L k

/-- **The comparison is natural in `L`**, given the naturality `hnat` of the object-level tensor
comparison. -/
theorem powerTransportIso_naturality (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F) (hnat : TensorIsoNatural O₁ hO₁ O₂ hO₂ F hten)
    {L M : SheafOfModules.{w} (structureSheaf O₁ hO₁)}
    [IsInvertible O₁ hO₁ L] [IsInvertible O₁ hO₁ M] (e : L ≅ M) (k : ℕ) :
    letI := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten L
    letI := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten M
    F.map (powerMapOf O₁ hO₁ e k).hom ≫
        (powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten M k).hom =
      (powerTransportIso O₁ hO₁ O₂ hO₂ F hunit hten L k).hom ≫
        (powerMapOf O₂ hO₂ (F.mapIso e) k).hom :=
  let _ := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten L
  let _ := isInvertible_obj O₁ hO₁ O₂ hO₂ F hunit hten M
  powerTransport_naturality O₁ hO₁ O₂ hO₂ F hunit hten hnat e k

end TwoSites

end Stacks.SheafOfModules.TensorPowerTransport

end
