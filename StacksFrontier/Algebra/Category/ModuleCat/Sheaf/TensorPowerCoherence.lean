module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of the tensor powers of an invertible sheaf of modules

Let `O` be a sheaf of commutative rings on a site and let `L` be an invertible sheaf of
`O`-modules, in the sense of Tag 01CS. `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower`
defines the integer tensor powers `L^{⊗ n}` and the successor comparison
`L^{⊗ n} ⊗_O L ≅ L^{⊗ (n + 1)}`. This file proves that every tensor power is again invertible,
and analyses the commutativity constraint which Tag 01CU asserts for the canonical multiplication
isomorphisms `L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}`.

## Main definitions

* `tensorSheafBraiding`: the braiding `M ⊗_O N ≅ N ⊗_O M` of the tensor product sheaf, namely
  the sheafification of the braiding of the underlying presheaves of modules.
* `tensorPowerSquareEquivalence`: the autoequivalence of sheaves of `O`-modules taking the
  structure sheaf to `L^{⊗ n} ⊗_O L^{⊗ n}`.
* `endUnitEquiv`: the identification, got from that equivalence, of the endomorphisms of
  `L^{⊗ n} ⊗_O L^{⊗ n}` with the endomorphisms of the structure sheaf — the scalars.
* `braidingScalar`: the scalar by which the braiding acts on `L^{⊗ n} ⊗_O L^{⊗ n}`.

## Main results

* `isInvertible_of_iso` and `isInvertible_of_tensor_isInvertible`: invertibility is an
  isomorphism invariant, and an invertible tensor factor may be cancelled.
* `isInvertible_tensorPower`: every integer tensor power of an invertible sheaf of modules is
  invertible.
* `tensorSheafBraiding_self_eq_refl_of_commutativity`: the commutativity constraint of Tag 01CU,
  in degrees `(n, n)`, forces the braiding of `L^{⊗ n}` with itself to be the identity, whichever
  multiplication isomorphism is chosen. By `tensorSheafBraiding_self_eq_refl_iff` that is exactly
  the scalar identity `braidingScalar = 𝟙`.
* `braidingScalar_comp_self`: the braiding scalar squares to the identity.
* `braidingScalar_zero`: in degree zero the braiding scalar is the identity.

## Implementation notes

Tag 01CU asserts that the multiplication isomorphisms satisfy "a commutativity and an
associativity constraint (formulation omitted)". The commutativity constraint is not a property
of the chosen multiplication: `tensorSheafBraiding_self_eq_refl_of_commutativity` shows that it
forces the braiding of `L^{⊗ n}` with itself to be the identity, so it is a property of `L`
alone. That property is true, but it is not a formal consequence of the symmetric monoidal
axioms — an invertible object of a general symmetric monoidal category satisfies only
`β ≫ β = 𝟙`, which is `braidingScalar_comp_self`, and the odd line in super vector spaces has
`β = -𝟙`. This file therefore isolates what is left as a single scalar identity: `braidingScalar`
is a square root of the identity in the endomorphism ring of the structure sheaf, and it is the
identity exactly when the commutativity constraint holds in degree `n`.

The input which proves `braidingScalar = 𝟙` is the rank-one local structure of an invertible
sheaf of modules, in trace form. On a covering where `L` admits a dual basis — sections
`x_i` of `L` and `y_i` of its inverse `N` with `∑ ψ(x_i ⊗ y_i) = 1`, which is Tag 0B8N (b) —
put `m_{ij} = ψ(x_j ⊗ y_i)`. The dual basis expansion `x = ∑ ψ(x ⊗ y_i) x_i` makes the matrix
`M = (m_{ij})` idempotent with trace `1`, and pairing `β = ε · 𝟙` against `φ_k = ψ(- ⊗ y_k)` in
both variables gives `m_{kj} m_{li} = ε · m_{ki} m_{lj}`; summing that over `k = i` and `l = j`
gives `ε = tr(M²) = tr(M) = 1`. The argument uses no localization, so it is available over an
arbitrary site, but it is not formalized here. The route through local triviality is not
available: an invertible sheaf of modules on a general site need not be locally trivial.

Invertibility is taken in the form of this repository's `Stacks.SheafOfModules.IsInvertible`
(Tag 01CS). The hypothesis `(tensorRightFunctor O hO L).IsEquivalence` under which the tensor
powers are defined is supplied from it by the instance `isEquivalence_tensorRightFunctor`, so the
two spellings of invertibility need not be reconciled by hand at each use.

The universes are those of `TensorPower`, and for the same reasons: the site `C : Type u` with
`Category.{v} C` is arbitrary, while the ring sheaf and the modules share the single universe
`w`, because Mathlib's monoidal structure on presheaves of modules is stated only in that form.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Invertibility only depends on the isomorphism class of a sheaf of modules. -/
theorem isInvertible_of_iso {L L' : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (e : L ≅ L') [IsInvertible O hO L] : IsInvertible O hO L' := by
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        L).IsEquivalence :=
    tensorLeftFunctor_isEquivalence O hO L
  refine (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO L').mpr ?_
  exact Functor.isEquivalence_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).mapIso e)

/-- Cancellation of an invertible factor: if `M ⊗ L` is invertible and `L` is invertible, then
so is `M`. -/
theorem isInvertible_of_tensor_isInvertible
    {M L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
      [IsInvertible O hO L]
    (h : IsInvertible O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M)).obj L)) :
    IsInvertible O hO M := by
  have h1 : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M)).obj
          L))).IsEquivalence :=
    (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO _).mp h
  have h2 : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        L)).asEquivalence.functor ⋙
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        M)).IsEquivalence :=
    Functor.isEquivalence_of_iso (tensorLeftFunctorObjIso O hO M L)
  refine (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO M).mpr ?_
  exact Functor.isEquivalence_of_iso
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        L)).asEquivalence.invFunIdAssoc
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M)))

/-- The tensor product sheaf of two invertible sheaves of modules is invertible. This is Tag
01CT (1), restated for `Stacks.SheafOfModules.Tensor.sheafTensor`; the tensor functor and the
tensor product sheaf agree by construction. -/
theorem isInvertible_tensorSheaf
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO M] [IsInvertible O hO N] :
    IsInvertible O hO (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N) :=
  tensorProduct_isInvertible O hO M N

/-- Cancellation of an invertible factor from a tensor product sheaf. -/
theorem isInvertible_of_tensorSheaf_isInvertible
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      [IsInvertible O hO N]
    (h : IsInvertible O hO (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N)) :
      IsInvertible O hO M :=
  isInvertible_of_tensor_isInvertible O hO h

/-- The braiding of the tensor product sheaf: the sheafification of the braiding of the
underlying presheaves of modules. -/
noncomputable def tensorSheafBraiding
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj M :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (braidingVal O hO N M)

/-- The underlying morphism of the braiding of the tensor product sheaf. -/
private theorem tensorSheafBraiding_hom
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafBraiding O hO M N).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (braidingVal O hO N M).hom :=
  rfl

/-- The braiding of the tensor product sheaf is a symmetry: braiding twice is the identity. -/
theorem tensorSheafBraiding_trans_self
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    tensorSheafBraiding O hO M N ≪≫ tensorSheafBraiding O hO N M = Iso.refl _ := by
  refine Iso.ext ?_
  rw [Iso.trans_hom, tensorSheafBraiding_hom, tensorSheafBraiding_hom]
  exact (CategoryTheory.Functor.map_comp _ _ _).symm.trans
    ((congrArg _ (SymmetricCategory.symmetry M.val N.val)).trans
      (CategoryTheory.Functor.map_id _ _))

namespace TensorPower

variable (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- An invertible sheaf of modules in the sense of Tag 01CS satisfies the hypothesis under which
the tensor powers of Tag 01CU are defined: tensoring on the right by it is an equivalence. -/
instance isEquivalence_tensorRightFunctor [IsInvertible O hO L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L)).IsEquivalence :=
  (isEquivalence_tensorRightFunctor_iff O hO L).mpr
    (Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence O hO L)

/-- **Every integer tensor power of an invertible sheaf of modules is invertible.** For
non-negative exponents this is Tag 01CT (1) and the successor comparison; for negative exponents
it is the same two inputs read backwards, cancelling the invertible factor `L`. -/
@[stacks 01CU "tensor powers are invertible", instance]
theorem isInvertible_tensorPower [IsInvertible O hO L] (n : ℤ) :
    IsInvertible O hO (tensorPower O hO L n) := by
  induction n using Int.induction_on with
  | zero => exact isInvertible_unit O hO
  | succ i ih =>
      have := ih
      have : IsInvertible O hO (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (tensorPower O hO L i)).obj L) :=
        isInvertible_tensorSheaf O hO _ L
      exact isInvertible_of_iso O hO (tensorPowerSuccIso O hO L i)
  | pred i ih =>
      have := ih
      refine isInvertible_of_tensorSheaf_isInvertible O hO _ L
        (isInvertible_of_iso O hO
          (tensorPowerSuccIso O hO L (-(i : ℤ) - 1) ≪≫
            tensorPowerReindex O hO L (by ring : -(i : ℤ) - 1 + 1 = -(i : ℤ))).symm)

variable [IsInvertible O hO L] (n : ℤ)

/-- The autoequivalence of sheaves of `O`-modules whose value at the structure sheaf is
`L^{⊗ n} ⊗_O L^{⊗ n}`: the `n`th power of tensoring by `L`, followed by tensoring by `L^{⊗ n}`.
Both factors are equivalences because `L` and `L^{⊗ n}` are invertible. -/
noncomputable def tensorPowerSquareEquivalence :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  (tensorPowerEquivalence O hO L n).trans
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        (tensorPower O hO L n))).asEquivalence

/-- **Every endomorphism of `L^{⊗ n} ⊗_O L^{⊗ n}` is a scalar**, i.e. is the image of a unique
endomorphism of the structure sheaf under `tensorPowerSquareEquivalence`. This is where
invertibility of the tensor powers is used: the equivalence is fully faithful, and it takes the
structure sheaf to `L^{⊗ n} ⊗_O L^{⊗ n}`. -/
noncomputable def endUnitEquiv :
    End (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≃
      End (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (tensorPower O hO L n)).obj (tensorPower O hO L n)) :=
  (tensorPowerSquareEquivalence O hO L n).fullyFaithfulFunctor.homEquiv

/-- `endUnitEquiv` sends the identity to the identity. -/
@[simp]
theorem endUnitEquiv_id : endUnitEquiv O hO L n (𝟙 _) = 𝟙 _ :=
  (tensorPowerSquareEquivalence O hO L n).functor.map_id _

/-- `endUnitEquiv` is compatible with composition. -/
theorem endUnitEquiv_comp
    (f g : End (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))) :
    endUnitEquiv O hO L n (f ≫ g) =
      endUnitEquiv O hO L n f ≫ endUnitEquiv O hO L n g :=
  (tensorPowerSquareEquivalence O hO L n).functor.map_comp f g

/-- The scalar by which the braiding acts on `L^{⊗ n} ⊗_O L^{⊗ n}`: the unique endomorphism of
the structure sheaf whose image under `tensorPowerSquareEquivalence` is that braiding. -/
noncomputable def braidingScalar : End (SheafOfModules.unit
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :=
  (endUnitEquiv O hO L n).symm
    (tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n)).hom

/-- The image of `braidingScalar` under `endUnitEquiv` is the braiding of `L^{⊗ n}` with
itself. -/
@[simp]
theorem endUnitEquiv_braidingScalar :
    endUnitEquiv O hO L n (braidingScalar O hO L n) =
      (tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n)).hom :=
  (endUnitEquiv O hO L n).apply_symm_apply _

/-- The braiding scalar squares to one: this is the symmetry of the braiding, read through the
identification of endomorphisms of `L^{⊗ n} ⊗_O L^{⊗ n}` with scalars. -/
theorem braidingScalar_comp_self :
    braidingScalar O hO L n ≫ braidingScalar O hO L n = 𝟙 _ := by
  refine (endUnitEquiv O hO L n).injective ?_
  rw [endUnitEquiv_comp, endUnitEquiv_id, endUnitEquiv_braidingScalar]
  simpa using congrArg Iso.hom (tensorSheafBraiding_trans_self O hO
    (tensorPower O hO L n) (tensorPower O hO L n))

/-- **The commutativity constraint on tensor powers is equivalent to a single scalar identity.**
The braiding of `L^{⊗ n}` with itself is the identity exactly when its braiding scalar is the
identity of the structure sheaf. -/
theorem tensorSheafBraiding_self_eq_refl_iff :
    tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n) = Iso.refl _ ↔
      braidingScalar O hO L n = 𝟙 _ := by
  refine ⟨fun h => (endUnitEquiv O hO L n).injective ?_, fun h => Iso.ext ?_⟩
  · rw [endUnitEquiv_braidingScalar, endUnitEquiv_id, h, Iso.refl_hom]
  · rw [← endUnitEquiv_braidingScalar, h, endUnitEquiv_id, Iso.refl_hom]

/-- **The commutativity constraint of Tag 01CU forces the braiding to be the identity.** A
multiplication isomorphism `L^{⊗ n} ⊗_O L^{⊗ n} ≅ L^{⊗ 2n}` which is unchanged by precomposing
with the braiding — the commutativity constraint at `n = m` — exists only if that braiding is
the identity. So the commutativity constraint is not a property of a chosen multiplication: it
is a property of `L`, and by `tensorSheafBraiding_self_eq_refl_iff` it is the single scalar
identity `braidingScalar = 𝟙`. -/
theorem tensorSheafBraiding_self_eq_refl_of_commutativity
    (μ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        (tensorPower O hO L n)).obj (tensorPower O hO L n) ≅
      tensorPower O hO L (n + n))
    (hμ : μ = tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n) ≪≫ μ ≪≫
      tensorPowerReindex O hO L (Int.add_comm n n)) :
    tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n) = Iso.refl _ := by
  have reindexIdentity := tensorPowerReindex_rfl O hO L (Int.add_comm n n)
  have multiplicationInvariant :
      μ = tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n) ≪≫ μ :=
    hμ.trans (congrArg (fun comparison ↦
      tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n) ≪≫ comparison)
        ((congrArg (fun comparison ↦ μ ≪≫ comparison) reindexIdentity).trans (Iso.trans_refl μ)))
  refine Iso.ext ?_
  let braidingHom :=
    (tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n)).hom
  exact (Category.comp_id braidingHom).symm.trans
    ((congrArg (fun morphism ↦ braidingHom ≫ morphism) μ.hom_inv_id.symm).trans
      ((Category.assoc braidingHom μ.hom μ.inv).symm.trans
        ((congrArg (fun morphism ↦ morphism ≫ μ.inv)
          (congrArg Iso.hom multiplicationInvariant).symm).trans μ.hom_inv_id)))

/-- The braiding scalar in degree zero is the identity: the zeroth tensor power is the structure
sheaf, and the braiding of the tensor unit with itself is the identity in any braided category.
This is the degree-zero case of the commutativity constraint, and it shows that the scalar
identity isolated above is not vacuously unprovable. -/
theorem braidingScalar_zero : braidingScalar O hO L 0 = 𝟙 _ := by
  have hβ : (braidingVal O hO (tensorPower O hO L 0) (tensorPower O hO L 0)).hom = 𝟙 _ := by
    change (β_ (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO).obj))
      (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO).obj))).hom = 𝟙 _
    rw [braiding_tensorUnit_left, MonoidalCategory.unitors_equal, Iso.hom_inv_id]
  rw [← tensorSheafBraiding_self_eq_refl_iff]
  refine Iso.ext ?_
  rw [tensorSheafBraiding_hom, hβ, CategoryTheory.Functor.map_id]
  rfl

end TensorPower

end Stacks.SheafOfModules

end
