module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMapMultiplication
public import StacksCore.Tactic.StacksAttribute

/-!
# Multiplication by a global section on the integral tensor powers

Let `L` be an invertible sheaf of modules on a ringed site and let `σ : 𝒪 ⟶ L` be a global
section of it, read as a morphism out of the structure sheaf. For every integer `n` the section
multiplies the `n`-th integral tensor power of Tag 01CU into the `(n + 1)`-st,

`L^{⊗ n} ≅ L^{⊗ n} ⊗ 𝒪 --(1 ⊗ σ)--> L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`,

and this file records that morphism together with the two compatibilities a consumer needs: it
is carried to multiplication by the corresponding section by the comparison of tensor powers
along a functor, and by the comparison of the tensor powers of two isomorphic invertible
modules.

The first compatibility is the one that
[Stacks, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27) needs. There the section is
multiplied into the twists of a *coherent triple*, whose two members live on different schemes
and are identified, over a third, through the inverse images of their tensor powers; so the
"multiply by `σ`" maps of the two members form a morphism of triples exactly when multiplication
commutes with that identification, which is built from the comparison of Tag 01CD in every
integer degree.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.mulSectionPow`: multiplication by a global section,
  `L^{⊗ n} ⟶ L^{⊗ (n + 1)}`.

## Main results

* `Stacks.SheafOfModules.TensorPower.map_mulSectionPow_tensorPowerComparison`: **the comparison
  of integral tensor powers along a functor carries multiplication by a section to
  multiplication by the image of that section.** The inputs are compatibility of the tensorator
  with the right unit constraints of Tag 01CA and its naturality in the second slot, both of
  which are available for the inverse image along a morphism of ringed spaces.
* `Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso_tensorPowerCongr`: the comparison of the
  tensor powers of two isomorphic invertible modules commutes with the successor comparison.
* `Stacks.SheafOfModules.TensorPower.mulSectionPow_tensorPowerCongr`: **that comparison carries
  multiplication by a section to multiplication by the corresponding section.**

## Implementation notes

The definition is written with the unitor and the whiskering of the strict monoidal structure of
Tag 01CA rather than with `Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso` and
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso`, because the two hypotheses it is combined
with — `Stacks.SheafOfModules.TensorPower.IsNaturalRight` and the successor square
`map_tensorPowerSuccIso_tensorPowerComparison` — are stated in the monoidal vocabulary, and
because the section is not an isomorphism, so `tensorSheafMapIso` does not apply to it. The one
input stated against the tensor product sheaf, `IsRightUnital`, is crossed over by
`Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor`.

No naturality of the tensorator in its *first* slot is needed, and neither is the associator:
multiplication by a section only ever changes the outer factor, so the whole chase is the
right unit constraint, one exchange of whiskerings, and the degree-`(n, 1)` normalisation.

The statement for `Stacks.SheafOfModules.TensorPower.tensorPowerCongr` is not an instance of the
one for a functor — a functor comparison has the *same* invertible module in both slots, while
here the module changes — but both comparisons are
`Stacks.Equivalence.powIntertwineObj`, so both successor squares are
`Stacks.Equivalence.powIntertwineObj_succIso`, here with the identity functor. The congruence
statement needs no unital hypothesis at all: naturality of the right unit constraint does the
work that `IsRightUnital` does in the other.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the integral tensor
  powers of an invertible sheaf of modules.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe v u v' u' w

namespace Stacks.SheafOfModules.TensorPower

attribute [local implicit_reducible] TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  Stacks.SheafOfModules.Strict.braidedCategory

/-! ### Bookkeeping in a monoidal category -/

section Transfer

variable {M : Type*} [Category M] [MonoidalCategory M]

/-- The right unit constraint read through a comparison `p` and an identification `u` of the
unit: if `i ≫ p` factors as `b ≫ (p ⊗ u) ≫ ρ`, then `i⁻¹ ≫ b ≫ (p ▷ U)` is `p ≫ ρ⁻¹ ≫ u⁻¹`. -/
private theorem rightUnitor_transfer {S A A' U : M} (i : S ≅ A) {b : S ⟶ A ⊗ U} {p : A ⟶ A'}
    (u : U ≅ 𝟙_ M) (h : i.hom ≫ p = b ≫ (p ⊗ₘ u.hom) ≫ (ρ_ A').hom) :
    i.inv ≫ b ≫ (p ▷ U) = p ≫ (ρ_ A').inv ≫ (A' ◁ u.inv) := by
  rw [MonoidalCategory.tensorHom_def] at h
  simp only [Category.assoc] at h
  rw [← cancel_mono ((A' ◁ u.hom) ≫ (ρ_ A').hom)]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Iso.inv_hom_id, Category.comp_id, ← h, Iso.inv_hom_id_assoc]

/-- The chase of multiplication by a section through a comparison: the image of the
multiplication factors through the successor square, naturality of the tensorator in its
second slot, one exchange of whiskerings and the right unit constraint. -/
private theorem mulSection_transfer {A S₁ S₂ Q Q' A' U L : M} {m : A ⟶ Q} {x₁ : A ⟶ S₁}
    {x₂ : S₁ ⟶ S₂} {x₃ : S₂ ⟶ Q} {q : Q ⟶ Q'} {b : S₂ ⟶ A ⊗ L} {p : A ⟶ A'}
    {s : A' ⊗ L ⟶ Q'} {bᵤ : S₁ ⟶ A ⊗ U} {r : U ⟶ L} {v : 𝟙_ M ⟶ U}
    (hm : m = x₁ ≫ x₂ ≫ x₃) (hsucc : x₃ ≫ q = b ≫ (p ▷ L) ≫ s) (hnat : x₂ ≫ b = bᵤ ≫ (A ◁ r))
    (hunit : x₁ ≫ bᵤ ≫ (p ▷ U) = p ≫ (ρ_ A').inv ≫ (A' ◁ v)) :
    m ≫ q = p ≫ (ρ_ A').inv ≫ (A' ◁ (v ≫ r)) ≫ s := by
  rw [hm]
  simp only [Category.assoc]
  rw [hsucc, reassoc_of% hnat, MonoidalCategory.whisker_exchange_assoc, reassoc_of% hunit,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- The chase of multiplication by a section through the comparison of the powers of two
isomorphic modules: the successor square, then naturality of the right unit constraint. -/
private theorem mulSectionCongr_transfer {A A' L L' Q Q' : M} {σ : 𝟙_ M ⟶ L} {e : L ⟶ L'}
    {c : A ⟶ A'} {s : A ⊗ L ⟶ Q} {c₁ : Q ⟶ Q'} {s' : A' ⊗ L' ⟶ Q'}
    (hsucc : s ≫ c₁ = (A ◁ e) ≫ (c ▷ L') ≫ s') :
    ((ρ_ A).inv ≫ (A ◁ σ) ≫ s) ≫ c₁ = c ≫ (ρ_ A').inv ≫ (A' ◁ (σ ≫ e)) ≫ s' := by
  simp only [Category.assoc]
  rw [hsucc, ← MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.rightUnitor_inv_naturality_assoc]

end Transfer

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-! ### Multiplication by a global section -/

/-- **Multiplication by a global section of `L` on the integral tensor powers of Tag 01CU.** A
global section is a morphism `σ : 𝒪 ⟶ L` out of the structure sheaf, and it carries the `n`-th
tensor power to the `(n + 1)`-st by writing `L^{⊗ n}` as `L^{⊗ n} ⊗ 𝒪`, tensoring `σ` into the
outer factor, and comparing `L^{⊗ n} ⊗ L` with `L^{⊗ (n + 1)}`. -/
public def mulSectionPow
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L]
    (σ : _root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⟶ L) (n : ℤ) :
    tensorPower O hO L n ⟶ tensorPower O hO L (n + 1) :=
  (ρ_ (tensorPower O hO L n)).inv ≫ (tensorPower O hO L n ◁ σ) ≫
    (tensorPowerSuccIso O hO L n).hom

/-! ### The comparison along a functor -/

section Functorial

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (O' : Dᵒᵖ ⥤ CommRingCat.{w})
  (hO' : Presheaf.IsSheaf K (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O'))
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}]
  (R : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
    _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [IsInvertible O hO L] [IsInvertible O' hO' (R.obj L)]
  (β : ∀ M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
    R.obj ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
        Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat)
          (hO)⟩).obj (M)).obj (N))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O',
        Presheaf.isSheaf_of_isSheaf_comp _ (O') (forget₂ CommRingCat RingCat)
          (hO')⟩).obj ((R.obj M))).obj ((R.obj N))))
  (hunit : R.obj (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≅
    _root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))

/-- The right unit constraint of the `n`-th power, read through the comparison of tensor powers
and the comparison of the structure sheaves. This is
`Stacks.SheafOfModules.TensorPower.map_tensorSheafRightUnitor_tensorPowerComparison` with both
unit constraints and the tensor product of the two comparisons written in the monoidal
vocabulary. -/
public theorem map_rightUnitor_tensorPowerComparison
    (hright : IsRightUnital O hO O' hO' R β hunit) (n : ℤ) :
    R.map (ρ_ (tensorPower O hO L n)).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit n).hom =
      (β (tensorPower O hO L n) (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).hom ≫
        ((tensorPowerComparison O hO O' hO' R L β hunit n).hom ⊗ₘ hunit.hom) ≫
          (ρ_ (tensorPower O' hO' (R.obj L) n)).hom := by
  rw [Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor,
    Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor, ← tensorSheafMapIso_hom_eq]
  exact map_tensorSheafRightUnitor_tensorPowerComparison O hO O' hO' R L β hunit hright n

/-- **The comparison of integral tensor powers along a functor carries multiplication by a
global section to multiplication by the image of that section.** The image of `σ : 𝒪 ⟶ L` is
`hunit.inv ≫ R.map σ`, a global section of `R L`.

The two inputs are compatibility of the tensorator with the right unit constraints of Tag 01CA
and its naturality in the second slot. For the inverse image along a morphism of ringed spaces
they are `Stacks.TensorPowerPullback.isRightUnital_pullback` and
`Stacks.TensorPowerPullback.isNaturalRight_pullback`. -/
@[reassoc]
public theorem map_mulSectionPow_tensorPowerComparison
    (hright : IsRightUnital O hO O' hO' R β hunit)
    (hnatR : IsNaturalRight O hO O' hO' R β)
    (σ : _root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⟶ L) (n : ℤ) :
    R.map (mulSectionPow O hO L σ n) ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + 1)).hom =
      (tensorPowerComparison O hO O' hO' R L β hunit n).hom ≫
        mulSectionPow O' hO' (R.obj L) (hunit.inv ≫ R.map σ) n := by
  exact mulSection_transfer ((R.map_comp _ _).trans (whisker_eq _ (R.map_comp _ _)))
    (map_tensorPowerSuccIso_tensorPowerComparison O hO O' hO' R L β hunit n) (hnatR σ)
    (rightUnitor_transfer (R.mapIso (ρ_ (tensorPower O hO L n))) hunit
      (map_rightUnitor_tensorPowerComparison O hO O' hO' R L β hunit hright n))

end Functorial

/-! ### The comparison of the powers of two isomorphic modules -/

section Congr

variable (L L' : _root_.SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [IsInvertible O hO L] [IsInvertible O hO L']

/-- **The comparison of the tensor powers of two isomorphic invertible modules commutes with the
successor comparison**, in every integer degree. Both comparisons are
`Stacks.Equivalence.powIntertwineObj`, so this is
`Stacks.Equivalence.powIntertwineObj_succIso` for the identity functor. -/
public theorem tensorPowerSuccIso_tensorPowerCongr (e : L ≅ L') (n : ℤ) :
    (tensorPowerSuccIso O hO L n).hom ≫ (tensorPowerCongr O hO e (n + 1)).hom =
      (tensorPower O hO L n ◁ e.hom) ≫ ((tensorPowerCongr O hO e n).hom ▷ L') ≫
        (tensorPowerSuccIso O hO L' n).hom := by
  have hsq := Stacks.Equivalence.powIntertwineObj_succIso
    ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
        (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).asEquivalence
    ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
        (forget₂ CommRingCat RingCat) hO⟩).flip.obj L').asEquivalence
    (𝟭 _) (fun M => ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).mapIso e) n
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  have hα : (((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj
        (tensorPower O hO L n)).mapIso e).hom = tensorPower O hO L n ◁ e.hom :=
    (Stacks.SheafOfModules.whiskerLeft_eq_sheafify_map O hO (tensorPower O hO L n) e.hom).symm
  have hmap : ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L').map
        (tensorPowerCongr O hO e n).hom =
      (tensorPowerCongr O hO e n).hom ▷ L' :=
    (Stacks.SheafOfModules.whiskerRight_eq_sheafify_map O hO
      (tensorPowerCongr O hO e n).hom L').symm
  rw [← hα, ← hmap]
  exact hsq

/-- **The comparison of the tensor powers of two isomorphic invertible modules carries
multiplication by a global section to multiplication by the corresponding section.** -/
@[reassoc]
public theorem mulSectionPow_tensorPowerCongr (e : L ≅ L')
    (σ : _root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⟶ L) (n : ℤ) :
    mulSectionPow O hO L σ n ≫ (tensorPowerCongr O hO e (n + 1)).hom =
      (tensorPowerCongr O hO e n).hom ≫ mulSectionPow O hO L' (σ ≫ e.hom) n := by
  exact mulSectionCongr_transfer (tensorPowerSuccIso_tensorPowerCongr O hO L L' e n)

end Congr

end Stacks.SheafOfModules.TensorPower

end
