module

public import StacksFrontier.CategoryTheory.Monoidal.IntPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced

/-!
# The self-symmetry of an invertible sheaf of modules is trivial

Let `O` be a sheaf of commutative rings on a site and let `L` be an invertible sheaf of
`O`-modules in the sense of Tag 01CS. This file proves that the symmetry constraint
`Invertible.tensorProductBraiding O hO L L : L ⊗_O L ≅ L ⊗_O L` of the sheaf tensor product is
the identity.

This is the commutativity half of the coherence asserted by Tag 01CU for the multiplication of
tensor powers: an invertible object of a general symmetric monoidal category satisfies only
`β ≫ β = 𝟙`, and the odd line in super vector spaces has `β = -𝟙`, so the triviality is a fact
about sheaves of modules and not a formal consequence of the monoidal axioms.

## Main results

* `Stacks.SheafOfModules.tensorProductBraiding_self`: the symmetry constraint of an invertible
  sheaf of modules with itself is the identity.
* `Stacks.SheafOfModules.eq_zero_of_tensor_squares`: the commutative-algebra core of that
  argument. If an `R`-linear functional `E` on `M ⊗[R] N` takes the value `1` somewhere and
  `d * E (x ⊗ₜ y) ^ 2 = 0` for every pure pair, then `d = 0`.
* `Stacks.SheafOfModules.tensor_unit_end_eq_id_of_squares`: its sheaf-theoretic form. An
  endomorphism of the structure sheaf which fixes the squares of the pure values of a locally
  surjective pairing is the identity.

## Implementation notes

The argument is a unit-ideal argument rather than a local trivialization, which is unavailable:
an invertible sheaf of modules on a general site need not be locally trivial. Tag 0B8K provides a
tensor inverse `N` and hence a pairing `E : L.val ⊗ N.val ⟶ O` which sheafification inverts, so
`E` is locally surjective. Transporting the symmetry along the regrouping `pairShuffle` and the
pairing turns it into an endomorphism `d` of the structure sheaf which, by `pairSwap_diagonal`,
fixes the square of every pure-pair evaluation `E(a ⊗ b)`. Those evaluations generate the unit
ideal locally, and `eq_zero_of_tensor_squares` concludes `d = 𝟙`; cancelling the tensor factor
`N ⊗ N` returns the symmetry itself.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules
  monoidalCategory braidedCategory symmetricCategory sheafifyMonoidal sheafifyBraided

attribute [local implicit_reducible] TensorSheafification.structureSheaf
  Tensor.sheafTensor PresheafOfModules.tensorObj
  _root_.SheafOfModules.forget _root_.PresheafOfModules.restrictScalars

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Squares of pure-pair evaluations generate the unit ideal when their span contains one. -/
theorem eq_zero_of_tensor_squares
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (E : M ⊗[R] N →ₗ[R] R)
    (t : M ⊗[R] N) (ht : E t = 1) (d : R)
    (hd : ∀ x y, d * E (x ⊗ₜ[R] y) ^ 2 = 0) : d = 0 := by
  let I : Ideal R := (LinearMap.mul R R d).ker
  have hmem : ∀ x y, E (x ⊗ₜ[R] y) ∈ I.radical := fun x y =>
    ⟨2, hd x y⟩
  have ht' : E t ∈ I.radical := by
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => exact hmem x y
    | add x y hx hy => simpa only [map_add] using I.radical.add_mem hx hy
  have htop : I = ⊤ := Ideal.radical_eq_top.mp (Ideal.eq_top_of_isUnit_mem _
    (by rwa [ht] at ht') isUnit_one)
  have h1 : (1 : R) ∈ I := htop ▸ Submodule.mem_top
  simpa [I] using h1

/-- The swap of the two factors of `(A ⊗ B) ⊗ (A ⊗ B)`, conjugated through `pairShuffle` so
that it is carried out by braiding the two copies of `A` with each other. On a pure diagonal
element `(a ⊗ b) ⊗ (a ⊗ b)` it is therefore the identity. -/
noncomputable def pairSwap
    (A B : PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj) :
    (A ⊗ B) ⊗ (A ⊗ B) ≅ (A ⊗ B) ⊗ (A ⊗ B) :=
  Stacks.IntPower.pairShuffle A B ≪≫ whiskerRightIso (β_ A A) (B ⊗ B) ≪≫
    (Stacks.IntPower.pairShuffle A B).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- `pairSwap` fixes every pure diagonal element. -/
theorem pairSwap_diagonal
    (A B : PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj)
    (U : Cᵒᵖ) (a : A.obj U) (b : B.obj U) :
    (pairSwap O hO A B).hom.app U ((a ⊗ₜ b) ⊗ₜ (a ⊗ₜ b)) =
      (a ⊗ₜ b) ⊗ₜ (a ⊗ₜ b) := by
  rfl

/-- The multiplication of the unit sheaf of modules, with its source written as a tensor square
of `.val`s. It is the left unitor of presheaves of modules, but the identification of the
underlying presheaf of the unit sheaf with the tensor unit of presheaves holds only by unfolding,
so recording it in the result type keeps a composite ending in this map a composite of morphisms
of one category at instance transparency. -/
noncomputable def unitTensorVal :
    (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)).val ⊗
        (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)).val ⟶
      (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)).val :=
  (λ_ _).hom

/-- The multiplication `unitTensorVal` of the unit sheaf of modules is an isomorphism. -/
instance isIso_unitTensorVal : IsIso (unitTensorVal O hO) :=
  inferInstanceAs
    (IsIso (λ_ (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)).val).hom)

/-- The sections of the unit sheaf of modules over an object of the site form a commutative
ring: they are the sections of the structure sheaf. -/
noncomputable local instance unitSectionCommRing (U : Cᵒᵖ) :
    CommRing ((SheafOfModules.unit (TensorSheafification.structureSheaf O hO)).val.obj U) :=
  inferInstanceAs (CommRing (O.obj U))

/-- The sections of the structure sheaf over an object of the site form a commutative ring. -/
local instance structureSectionCommRing (U : Cᵒᵖ) :
    CommRing ((TensorSheafification.structureSheaf O hO).obj.obj U) :=
  inferInstanceAs (CommRing (O.obj U))

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- An endomorphism of the unit sheaf of modules which fixes the square of every pure-pair
evaluation of a locally surjective pairing `E : A ⊗ B ⟶ O` is the identity. Locally the
evaluations of `E` span the unit ideal, and `eq_zero_of_tensor_squares` turns that into the
vanishing of `d - 1`. -/
theorem tensor_unit_end_eq_id_of_squares
    (A B : PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj)
    (E : A ⊗ B ⟶ (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)).val)
    [PresheafOfModules.IsLocallySurjective J E]
    (d : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      SheafOfModules.unit (TensorSheafification.structureSheaf O hO))
    (hd : ∀ (U : Cᵒᵖ) (a : A.obj U) (b : B.obj U),
      d.val.app U (E.app U (a ⊗ₜ b) ^ 2) = E.app U (a ⊗ₜ b) ^ 2) : d = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show d.val.app U x = x
  suffices h1 : d.val.app U (1 : O.obj U) = (1 : O.obj U) by
    have h := (d.val.app U).hom.map_smul x (1 : O.obj U)
    change d.val.app U (x * 1) = x * d.val.app U (1 : O.obj U) at h
    rw [h1] at h
    change d.val.app U (x * 1) = x * 1 at h
    rwa [mul_one] at h
  apply (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)).isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map E) (1 : O.obj U))
  rintro V f ⟨t, ht⟩
  show (O.map f.op) (d.val.app U (1 : O.obj U)) = (O.map f.op) 1
  have hn := PresheafOfModules.naturality_apply d.val f.op (1 : O.obj U) |>.symm
  change (O.map f.op) (d.val.app U (1 : O.obj U)) =
    d.val.app (Opposite.op V) ((O.map f.op) 1) at hn
  rw [hn, map_one]
  apply sub_eq_zero.mp
  apply eq_zero_of_tensor_squares (R := O.obj (Opposite.op V)) (E.app (Opposite.op V)).hom t
    (by change (E.app _).hom t = (O.map f.op).hom 1 at ht; rw [map_one] at ht; exact ht)
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
  show (d0 - 1) * a0 ^ 2 = 0
  rw [sub_mul, one_mul, mul_comm d0 (a0 ^ 2), hs.symm.trans h]
  exact sub_self _

/-- The self-braiding of an invertible sheaf is trivial. A tensor inverse transports
its double tensor to the unit, where the transported swap fixes the squares of all
pure-pair evaluations. Local surjectivity and the unit ideal criterion detect the identity. -/
theorem tensorProductBraiding_self
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    Invertible.tensorProductBraiding O hO L L = Iso.refl _ := by
  obtain ⟨N, ⟨e⟩⟩ :=
    (isInvertible_iff_exists_tensor_iso_unit L).mp inferInstance
  let F := sheafifyFunctor O hO
  let A := L.val
  let B := N.val
  let I := SheafOfModules.unit (TensorSheafification.structureSheaf O hO)
  let e' : F.obj (A ⊗ B) ≅ I := e
  let η : A ⊗ B ⟶ (F.obj (A ⊗ B)).val := TensorSheafification.toSheafify O hO (A ⊗ B)
  let E : A ⊗ B ⟶ I.val := η ≫ e'.hom.val
  have : IsIso (F.map E) := by
    have : IsIso (F.map η) :=
      TensorSheafification.isIso_sheafify_map_toSheafify O hO (A ⊗ B)
    have : IsIso e'.hom.val := (SheafOfModules.forget _).map_isIso e'.hom
    dsimp only [E]
    rw [Functor.map_comp]
    infer_instance
  have hW : J.W ((PresheafOfModules.toPresheaf _).map E) := by
    show (J.W.inverseImage (PresheafOfModules.toPresheaf _)) E
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (TensorSheafification.structureSheaf O hO).obj)]
    exact inferInstanceAs (IsIso (F.map E))
  let : PresheafOfModules.IsLocallySurjective J E := hW.isLocallySurjective
  let r : (A ⊗ B) ⊗ (A ⊗ B) ⟶ I.val := (E ⊗ₘ E) ≫ unitTensorVal O hO
  have : IsIso (F.map r) := by
    dsimp only [r]
    rw [Functor.map_comp, Functor.Monoidal.map_tensor]
    -- `unitTensorVal` is a morphism of presheaves of modules over `(structureSheaf O hO).obj`
    -- while `sheafifyFunctor` has its source over `structureRingPresheaf O`; the two categories
    -- are definitionally equal but instance search does not cross the identification, so the
    -- invertibility of its sheafification is named here once.
    have hu : IsIso (F.map (unitTensorVal O hO)) :=
      inferInstanceAs (IsIso ((TensorSheafification.sheafify O hO).map (unitTensorVal O hO)))
    infer_instance
  let b : F.obj ((A ⊗ B) ⊗ (A ⊗ B)) ≅ I :=
    asIso (F.map r) ≪≫ sheafifyValIso O hO I
  let s := pairSwap O hO A B
  let d : I ⟶ I := b.inv ≫ F.map s.hom ≫ b.hom
  let η₂ : (A ⊗ B) ⊗ (A ⊗ B) ⟶ (F.obj ((A ⊗ B) ⊗ (A ⊗ B))).val :=
    TensorSheafification.toSheafify O hO ((A ⊗ B) ⊗ (A ⊗ B))
  have hb : η₂ ≫ b.hom.val = r :=
    ((TensorSheafification.sheafifyAdjunction O hO).unit_comp_map_eq_iff b.hom r).mpr rfl
  have hr : r ≫ d.val = s.hom ≫ r := by
    rw [← hb, Category.assoc, ← SheafOfModules.comp_val]
    have hbd : b.hom ≫ d = F.map s.hom ≫ b.hom := by simp [d]
    rw [hbd, SheafOfModules.comp_val, ← Category.assoc]
    have hn : η₂ ≫ (F.map s.hom).val = s.hom ≫ η₂ := toSheafifyVal_naturality O hO s.hom
    rw [hn, Category.assoc]
  have hd : d = 𝟙 I := by
    apply tensor_unit_end_eq_id_of_squares O hO A B E d
    intro U a c
    have h := congrArg (fun f => f.app U ((a ⊗ₜ c) ⊗ₜ (a ⊗ₜ c))) hr
    change d.val.app U (r.app U ((a ⊗ₜ c) ⊗ₜ (a ⊗ₜ c))) =
      r.app U (s.hom.app U ((a ⊗ₜ c) ⊗ₜ (a ⊗ₜ c))) at h
    rw [pairSwap_diagonal] at h
    change d.val.app U (E.app U (a ⊗ₜ c) * E.app U (a ⊗ₜ c) : O.obj U) =
      (E.app U (a ⊗ₜ c) : O.obj U) * E.app U (a ⊗ₜ c) at h
    simpa only [pow_two] using h
  have hs : F.map s.hom = 𝟙 _ := by
    simpa [d] using congrArg (fun f => b.hom ≫ f ≫ b.inv) hd
  have hw : F.map ((β_ A A).hom ▷ (B ⊗ B)) = 𝟙 _ := by
    simpa [s, pairSwap, ← Functor.map_comp] using congrArg (fun f =>
      F.map (Stacks.IntPower.pairShuffle A B).inv ≫ f ≫
        F.map (Stacks.IntPower.pairShuffle A B).hom) hs
  have hw' : F.map (β_ A A).hom ▷ F.obj (B ⊗ B) = (𝟙 _) ▷ F.obj (B ⊗ B) := by
    apply (cancel_mono (Functor.Monoidal.μIso F (A ⊗ A) (B ⊗ B)).hom).mp
    rw [Functor.Monoidal.μIso_hom, Functor.LaxMonoidal.μ_natural_left,
      hw, Category.comp_id, id_whiskerRight, Category.id_comp]
  let i : F.obj (B ⊗ B) ⊗ F.obj (A ⊗ A) ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ Functor.Monoidal.μIso F _ _ ≪≫
      (F.mapIso (Stacks.IntPower.pairShuffle A B)).symm ≪≫ b
  have hβ : F.map (β_ A A).hom = 𝟙 _ := Stacks.IntPower.cancel_tensor_right i _ _ hw'
  exact Iso.ext hβ

end Stacks.SheafOfModules

end
