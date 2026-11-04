module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleBraidingSelf
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Comparison
public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The self-braiding of an invertible sheaf of modules is the identity

Let `O` be a sheaf of commutative rings on a site and `L` an invertible sheaf of `O`-modules in
the sense of [Stacks, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS). This file proves

  `β_{L, L} = 𝟙`,

the braiding of `L` with itself being the identity, with no hypothesis on `L` or on the site
beyond invertibility. This is the commutativity constraint of
[Stacks, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) in its decisive degree: it is the
one input of the coherence of the multiplication isomorphisms of the tensor powers which is not
a formal consequence of the symmetric monoidal axioms — an invertible object of a general
symmetric monoidal category satisfies only `β ≫ β = 𝟙`, and the odd line in super vector spaces
has `β = -𝟙`.

## Main results

* `Stacks.SheafOfModules.Invertible.tensor_unit_end_eq_id_of_squares`: an endomorphism of the
  structure sheaf which fixes the squares of all pure-pair values of a locally surjective
  pairing `A ⊗ B ⟶ O` is the identity.
* `Stacks.SheafOfModules.Invertible.tensorProductBraiding_self`: **the braiding of an invertible
  sheaf of modules with itself is the identity**, in the tensor-product-sheaf spelling of Tag
  01CU.
* `Stacks.SheafOfModules.Invertible.braiding_self_hom_eq_id`: the same in the spelling of the
  monoidal structure on sheaves of modules, `β_ L L = 𝟙 (L ⊗ L)`.

## Implementation notes

**The argument.** Choose a tensor inverse: by Tag 0B8K there are `N` and an isomorphism
`(L ⊗ N)^# ≅ O`, so a pairing `E : L.val ⊗ N.val ⟶ O` which is *locally surjective*. Multiplying
two values of `E` gives `r : (A ⊗ B) ⊗ (A ⊗ B) ⟶ O`, where `A = L.val`, `B = N.val`, and `r`
sheafifies to an isomorphism. Transport the automorphism `s` of `(A ⊗ B) ⊗ (A ⊗ B)` which swaps
the two `A` slots — the braiding `β_{A,A}` conjugated by the shuffle `pairShuffle` — through that
isomorphism, to get a scalar `d : O ⟶ O`. On a diagonal pure tensor `(a ⊗ b) ⊗ (a ⊗ b)` the swap
`s` is the identity, so `d` fixes `E(a ⊗ b)²` for all `a`, `b`. Local surjectivity makes `1` a
sum of values `E(a ⊗ b)` after refinement, and in a commutative ring an element annihilating the
squares of a generating family annihilates `1`: that is `eq_zero_of_tensor_squares`, by the
radical of the annihilator ideal. Hence `d = 𝟙`, hence the sheafification of `s` is the identity,
hence so is the sheafification of `β_{A,A} ▷ (B ⊗ B)`, and cancelling the tensor factor
`(B ⊗ B)^#` — invertible because `B ⊗ B` has `A ⊗ A` as a tensor inverse — leaves `β_{A,A}`.

**What this adds over what was already in the repository.**
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BraidingScalar/Basic.lean` proves `β_ M M = 𝟙` for a
*locally cyclic* `M` (`braiding_self_hom_eq_id_of_locally_span_singleton`), and says that local
cyclicity is not implied by invertibility on a general site, the scalar identity being true
there only "by the classical rank argument for invertible modules, which localizes `R` at its
primes — an operation with no counterpart in the Grothendieck topology". The argument above is
unconditional and uses no localization and no rank theory: the radical of an annihilator ideal
replaces them. So the conclusion of that file is available for every invertible sheaf of
modules, and `Stacks.Monoidal.PowerSystem.sectionMul_comm`'s hypothesis `hβ` — and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerCoherence.lean`'s
`braidingScalar = 𝟙`, through
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` — are no longer conditional on local
triviality.

**Which `IsInvertible`.** `AlgebraicGeometry.SheafOfModules.IsInvertible`, written out in full
because inside `namespace Stacks.SheafOfModules.Invertible` the bare name `IsInvertible` is
captured by the enclosing namespace and resolves to `Stacks.SheafOfModules.IsInvertible`, a
different class, whatever `open` is in force.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization
open AlgebraicGeometry.SheafOfModules (IsInvertible)
open scoped TensorProduct
universe v u w
namespace Stacks.SheafOfModules.Invertible

/-- An endomorphism of the tensor unit which can be cancelled against an invertible tensor
factor is determined by that cancellation. -/
theorem cancel_tensor_right
    {D : Type*} [Category.{v} D] [MonoidalCategory D]
    {X Y A B : D} (e : A ⊗ B ≅ 𝟙_ D) (f g : X ⟶ Y)
    (h : f ▷ A = g ▷ A) : f = g := by
  have h' : (f ▷ A) ▷ B = (g ▷ A) ▷ B := congrArg (fun k => k ▷ B) h
  have hh (k : X ⟶ Y) :
      (k ▷ A) ▷ B ≫ (α_ Y A B).hom ≫ Y ◁ e.hom ≫ (ρ_ Y).hom =
        (α_ X A B).hom ≫ X ◁ e.hom ≫ (ρ_ X).hom ≫ k := by
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]
  apply (cancel_epi ((α_ X A B).hom ≫ X ◁ e.hom ≫ (ρ_ X).hom)).mp
  simpa only [← hh, Category.assoc] using
    congrArg (fun k => k ≫ (α_ Y A B).hom ≫ Y ◁ e.hom ≫ (ρ_ Y).hom) h'

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafOfModules.monoidalCategory Stacks.SheafOfModules.braidedCategory
  Stacks.SheafOfModules.symmetricCategory
  Stacks.SheafOfModules.Invertible.sheafifyMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The sections `A(U)` of a presheaf of modules over the structure sheaf, as a module over the
ring of sections of the structure ring presheaf. -/
local instance moduleStructureRingPresheafSections (U : Cᵒᵖ)
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    Module ((Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O).obj U) (A.obj U) :=
  inferInstanceAs (Module ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj.obj
    U) (A.obj U))

/-- The shuffle `(A ⊗ B) ⊗ (A ⊗ B) ≅ (A ⊗ A) ⊗ (B ⊗ B)` of a braided monoidal category. -/
noncomputable def pairShuffle
    {D : Type*} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A B : D) :
    (A ⊗ B) ⊗ (A ⊗ B) ≅ (A ⊗ A) ⊗ (B ⊗ B) :=
  (α_ A B (A ⊗ B)) ≪≫ whiskerLeftIso A (α_ B A B).symm ≪≫
    whiskerLeftIso A (whiskerRightIso (β_ B A) B) ≪≫
    whiskerLeftIso A (α_ A B B) ≪≫ (α_ A A (B ⊗ B)).symm

/-- The automorphism of `(A ⊗ B) ⊗ (A ⊗ B)` which swaps the two `A` slots. -/
noncomputable def pairSwap
    (A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj) :
    (A ⊗ B) ⊗ (A ⊗ B) ≅ (A ⊗ B) ⊗ (A ⊗ B) :=
  pairShuffle A B ≪≫ whiskerRightIso (β_ A A) (B ⊗ B) ≪≫ (pairShuffle A B).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- The swap of the two `A` slots fixes the diagonal pure tensors. -/
theorem pairSwap_diagonal
    (A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj)
    (U : Cᵒᵖ) (a : A.obj U) (b : B.obj U) :
    (pairSwap O hO A B).hom.app U ((a ⊗ₜ b) ⊗ₜ (a ⊗ₜ b)) =
      (a ⊗ₜ b) ⊗ₜ (a ⊗ₜ b) :=
  rfl

/-- The commutative ring structure on the sections over `U` of the unit sheaf of modules, those of
`O`. -/
noncomputable local instance unitSectionCommRing (U : Cᵒᵖ) :
    CommRing ((SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)).val.obj U) :=
  inferInstanceAs (CommRing (O.obj U))

/-- The commutative ring structure on the sections over `U` of the structure sheaf, those of
`O`. -/
local instance structureSectionCommRing (U : Cᵒᵖ) :
    CommRing ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj.obj U) :=
  inferInstanceAs (CommRing (O.obj U))

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- An endomorphism of the structure sheaf which fixes the squares of all pure-pair values of a
locally surjective pairing `A ⊗ B ⟶ O` is the identity. -/
theorem tensor_unit_end_eq_id_of_squares
    (A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj)
    (E : A ⊗ B ⟶ (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)).val)
    [PresheafOfModules.IsLocallySurjective J E]
    (d : SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hd : ∀ (U : Cᵒᵖ) (a : A.obj U) (b : B.obj U),
      d.val.app U (E.app U (a ⊗ₜ b) ^ 2) = E.app U (a ⊗ₜ b) ^ 2) : d = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show d.val.app U x = x
  suffices h1 : d.val.app U 1 = 1 by
    have h := (d.val.app U).hom.map_smul x
      (1 : (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO)).val.obj U)
    change d.val.app U (x * 1) = x * d.val.app U 1 at h
    rwa [mul_one, h1, mul_one] at h
  apply (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
    hO)).isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map E) (1 : O.obj U))
  rintro V f ⟨t, ht⟩
  show (O.map f.op) (d.val.app U (1 : O.obj U)) = (O.map f.op) 1
  have hn := PresheafOfModules.naturality_apply d.val f.op (1 : O.obj U) |>.symm
  change (O.map f.op) (d.val.app U (1 : O.obj U)) =
    d.val.app (Opposite.op V) ((O.map f.op) 1) at hn
  rw [hn, map_one]
  apply sub_eq_zero.mp
  apply eq_zero_of_tensor_squares (R := O.obj (Opposite.op V)) (E.app (Opposite.op V)).hom t
    (by change (E.app _).hom t = (O.map f.op).hom 1 at ht; rwa [map_one] at ht)
  intro a b
  let a0 : O.obj (Opposite.op V) :=
    (E.app (Opposite.op V)).hom (a ⊗ₜ[O.obj (Opposite.op V)] b)
  let d0 : O.obj (Opposite.op V) := d.val.app (Opposite.op V) (1 : O.obj (Opposite.op V))
  let dl : O.obj (Opposite.op V) →ₗ[O.obj (Opposite.op V)] O.obj (Opposite.op V) :=
    (d.val.app (Opposite.op V)).hom
  have h := hd (Opposite.op V) a b
  change dl (a0 ^ 2) = a0 ^ 2 at h
  have hs := dl.map_smul (a0 ^ 2) 1
  change dl (a0 ^ 2 * 1) = a0 ^ 2 * d0 at hs
  rw [mul_one] at hs
  have hz : a0 ^ 2 * d0 = a0 ^ 2 := hs.symm.trans h
  show (d0 - 1) * a0 ^ 2 = 0
  rw [sub_mul, one_mul, mul_comm d0 (a0 ^ 2), hz, sub_self]

/-- An endomorphism which is the identity after conjugation by an isomorphism is the identity. -/
private theorem eq_id_of_conj_eq_id {D : Type*} [Category D] {X Y : D} (i : X ≅ Y) (f : Y ⟶ Y)
    (h : i.hom ≫ f ≫ i.inv = 𝟙 X) : f = 𝟙 Y := by
  rw [← cancel_epi i.hom, ← cancel_mono i.inv]
  simpa using h

/-- **The self-braiding of an invertible sheaf of modules is the identity.** A tensor inverse
`N` of `L` makes the double tensor product of `L ⊗ N` isomorphic to the structure sheaf, and the
transported swap of the two `L` slots fixes the square of every pure-pair value of the pairing.
Local surjectivity of that pairing and the unit-ideal criterion
`eq_zero_of_tensor_squares` then identify the transported swap with the identity, and cancelling
the invertible factor `(N ⊗ N)^#` leaves the braiding of `L` with itself. -/
theorem tensorProductBraiding_self
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    tensorProductBraiding O hO L L = Iso.refl _ := by
  obtain ⟨N, ⟨e⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit O hO L).mp inferInstance
  let F := Stacks.SheafOfModules.TensorSheafification.sheafify O hO
  let A := L.val
  let B := N.val
  let I := SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
  let e' : F.obj (A ⊗ B) ≅ I := e
  let E : A ⊗ B ⟶ I.val := toSheafifyVal O hO (A ⊗ B) ≫ e'.hom.val
  have : IsIso (F.map E) := by
    have h1 : IsIso (F.map (toSheafifyVal O hO (A ⊗ B))) :=
      Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO (A ⊗ B)
    have h2 : IsIso e'.hom.val := (SheafOfModules.forget _).map_isIso e'.hom
    have h3 : F.map E = F.map (toSheafifyVal O hO (A ⊗ B)) ≫ F.map e'.hom.val :=
      F.map_comp _ _
    rw [h3]
    infer_instance
  have hW : J.W ((PresheafOfModules.toPresheaf _).map E) := by
    show (J.W.inverseImage (PresheafOfModules.toPresheaf _)) E
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)]
    exact inferInstanceAs (IsIso (F.map E))
  let _ : PresheafOfModules.IsLocallySurjective J E := hW.isLocallySurjective
  let r : (A ⊗ B) ⊗ (A ⊗ B) ⟶ I.val := (E ⊗ₘ E) ≫ (λ_ I.val).hom
  have : IsIso (F.map r) := by
    have h4 : F.map r = F.map (E ⊗ₘ E) ≫ F.map (λ_ I.val).hom := F.map_comp _ _
    have h5 : IsIso (F.map (E ⊗ₘ E)) := by
      rw [Functor.Monoidal.map_tensor]
      infer_instance
    have h6 : IsIso (F.map (λ_ I.val).hom) := (F.mapIso (λ_ I.val)).isIso_hom
    rw [h4]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h5 h6
  let b : F.obj ((A ⊗ B) ⊗ (A ⊗ B)) ≅ I := asIso (F.map r) ≪≫ valIso O hO I
  let s := pairSwap O hO A B
  let d : I ⟶ I := b.inv ≫ F.map s.hom ≫ b.hom
  have hb : toSheafifyVal O hO ((A ⊗ B) ⊗ (A ⊗ B)) ≫ b.hom.val = r :=
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).unit_comp_map_eq_iff b.hom
      r).mpr rfl
  have hr : r ≫ d.val = s.hom ≫ r := by
    rw [← hb, Category.assoc, ← SheafOfModules.comp_val]
    have hbd : b.hom ≫ d = F.map s.hom ≫ b.hom := by
      simp only [d, Iso.hom_inv_id_assoc]
    rw [hbd, SheafOfModules.comp_val, ← Category.assoc, toSheafifyVal_naturality,
      Category.assoc]
  have hd : d = 𝟙 I := by
    apply tensor_unit_end_eq_id_of_squares O hO A B E d
    intro U a c
    have h := congrArg (fun f => f.app U ((a ⊗ₜ c) ⊗ₜ (a ⊗ₜ c))) hr
    change d.val.app U (r.app U ((a ⊗ₜ c) ⊗ₜ (a ⊗ₜ c))) =
      r.app U (s.hom.app U ((a ⊗ₜ c) ⊗ₜ (a ⊗ₜ c))) at h
    rw [pairSwap_diagonal] at h
    change d.val.app U (E.app U (a ⊗ₜ c) * E.app U (a ⊗ₜ c)) =
      E.app U (a ⊗ₜ c) * E.app U (a ⊗ₜ c) at h
    simpa only [pow_two] using h
  have hs : F.map s.hom = 𝟙 _ := eq_id_of_conj_eq_id b.symm _ hd
  have hw : F.map ((β_ A A).hom ▷ (B ⊗ B)) = 𝟙 _ :=
    eq_id_of_conj_eq_id (F.mapIso (pairShuffle A B)) _ 
      (by
        rw [Functor.mapIso_hom, Functor.mapIso_inv, ← Functor.map_comp, ← Functor.map_comp]
        exact hs)
  have hw' : F.map (β_ A A).hom ▷ F.obj (B ⊗ B) = (𝟙 _) ▷ F.obj (B ⊗ B) := by
    apply (cancel_mono (Functor.Monoidal.μIso F (A ⊗ A) (B ⊗ B)).hom).mp
    rw [Functor.Monoidal.μIso_hom, Functor.LaxMonoidal.μ_natural_left,
      hw, Category.comp_id, id_whiskerRight, Category.id_comp]
  let i : F.obj (B ⊗ B) ⊗ F.obj (A ⊗ A) ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ Functor.Monoidal.μIso F _ _ ≪≫ (F.mapIso (pairShuffle A B)).symm ≪≫ b
  exact Iso.ext (cancel_tensor_right i _ _ hw')

/-- **The braiding of an invertible sheaf of modules with itself is the identity**, in the
spelling of the monoidal structure on sheaves of modules. This is the form the commutativity
constraint of Tag 01CU is consumed in. -/
theorem braiding_self_hom_eq_id
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    (β_ L L).hom = 𝟙 (L ⊗ L) := by
  rw [Stacks.SheafOfModules.braiding_hom_eq_tensorSheafBraiding O hO L L,
    show Stacks.SheafOfModules.tensorSheafBraiding O hO L L = tensorProductBraiding O hO L L from
      rfl,
    tensorProductBraiding_self O hO L]
  exact (congrArg (fun morphism => (Stacks.SheafOfModules.tensorObjIso O hO L L).hom ≫ morphism)
    (Category.id_comp (Stacks.SheafOfModules.tensorObjIso O hO L L).inv)).trans
      (Stacks.SheafOfModules.tensorObjIso O hO L L).hom_inv_id
end Stacks.SheafOfModules.Invertible

end
