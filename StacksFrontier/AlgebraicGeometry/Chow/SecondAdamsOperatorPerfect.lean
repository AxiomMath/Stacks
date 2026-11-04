module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Ring
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom

/-!
# The switching action on a derived tensor square and its invariants

Let `C` be a symmetric monoidal category and let `L` be an object of `C`. Switching the two
factors of `L ⊗ L` is an involution, so the group `{±1}` acts on `L ⊗ L`; this is
`Stacks.SecondAdamsPerfect.swapSquareAction`. If moreover `C` is `R`-linear for a ring `R` in
which `2` is invertible, the two elements

`(𝟙 + σ)/2`  and  `(𝟙 - σ)/2`

of the endomorphism group of `L ⊗ L`, where `σ` is the switch, are complementary orthogonal
idempotents. The *invariants* `(L ⊗ L)^+` and the *anti-invariants* `(L ⊗ L)^-` of the switch
are by definition the objects splitting them. When `C` is in addition pretriangulated, such a
pair of splittings exhibits `L ⊗ L` as the biproduct of the two, so that

`[L ⊗ L] = [(L ⊗ L)^+] + [(L ⊗ L)^-]`

in the `K`-group `CategoryTheory.Pretriangulated.K0` of [Stacks, Tag 0FCN], and the difference
`[(L ⊗ L)^+] - [(L ⊗ L)^-]` — the value the second Adams operator of [Stacks, Tag 0FEK] is to
take on `L` — does not depend on the chosen splittings.

For the derived category `D(O_X)` of a ringed space the symmetric monoidal structure is
`Stacks.SheafOfModules.derivedSymmetricStructure`, whose tensor product is the derived tensor
product `- ⊗^L_{O_X} -` of `Stacks.SheafOfModules.derivedTensor` on the nose and whose
commutativity constraint is the Koszul symmetry; the switching action on `L ⊗^L L` is read off
there as `Stacks.SecondAdamsPerfect.derivedSwapSquareAction`.

## Main definitions

* `Stacks.SecondAdamsPerfect.swapSquare`: the switch `σ : L ⊗ L ⟶ L ⊗ L` of the two factors,
  the commutativity constraint of the symmetric monoidal structure at `(L, L)`.
* `Stacks.SecondAdamsPerfect.swapSquareAction`: the action of the group `{±1}` on `L ⊗ L` by
  switching the factors, as a monoid homomorphism from `ℤˣ` to the endomorphism monoid.
* `Stacks.SecondAdamsPerfect.invariantProjector` and `antiInvariantProjector`: the endomorphisms
  `(𝟙 + σ)/2` and `(𝟙 - σ)/2` of `L ⊗ L`.
* `Stacks.SecondAdamsPerfect.IdempotentSplitting`: a splitting of an idempotent endomorphism,
  the datum which defines the invariants and the anti-invariants of the switch.
* `Stacks.SecondAdamsPerfect.derivedSwapSquareAction`: the switching action on `L ⊗^L_{O_X} L`
  in the derived category of a ringed space.

## Main results

* `Stacks.SecondAdamsPerfect.swapSquare_comp_swapSquare`: the switch is an involution, which is
  what makes the group `{±1}` act.
* `Stacks.SecondAdamsPerfect.invariantProjector_add_antiInvariantProjector`,
  `invariantProjector_comp_self`, `antiInvariantProjector_comp_self`,
  `invariantProjector_comp_antiInvariantProjector`,
  `antiInvariantProjector_comp_invariantProjector`: the two endomorphisms are complementary
  orthogonal idempotents.
* `Stacks.SecondAdamsPerfect.swapSquare_comp_invariantProjector` and
  `swapSquare_comp_antiInvariantProjector`: the switch acts as `+1` on the first and as `-1` on
  the second, which is what makes them the invariant and the anti-invariant part.
* `Stacks.SecondAdamsPerfect.IdempotentSplitting.iso`: two splittings of one idempotent have
  isomorphic objects, so the invariants and the anti-invariants are determined up to
  isomorphism by `L`.
* `Stacks.SecondAdamsPerfect.IdempotentSplitting.ι_comp_self`,
  `IdempotentSplitting.self_comp_π` and `IdempotentSplitting.ι_comp_π_eq_zero`: the inclusion
  and the projection of a splitting absorb the idempotent, and splittings of two orthogonal
  idempotents are orthogonal.
* `Stacks.SecondAdamsPerfect.cls_tensorObj_eq_add`: **`[L ⊗ L] = [(L ⊗ L)^+] + [(L ⊗ L)^-]`** in
  the `K`-group.
* `Stacks.SecondAdamsPerfect.cls_sub_cls_eq`: **the difference `[(L ⊗ L)^+] - [(L ⊗ L)^-]` is
  independent of the chosen invariants and anti-invariants**, hence a well-defined element of
  the `K`-group attached to `L`.
* `Stacks.SecondAdamsPerfect.derivedSwapSquare_comp_self`: the switch of the two factors of
  `L ⊗^L_{O_X} L` is an involution.

## Implementation notes

**What `(-)^+` and `(-)^-` mean.** The source writes "(suitably defined)" and supplies no
definition. The definition taken here is the one that `2` being invertible makes available:
`σ` is an involution, so `(𝟙 + σ)/2` and `(𝟙 - σ)/2` are complementary orthogonal idempotents,
and the invariants and the anti-invariants are the objects splitting them, which is the datum
`IdempotentSplitting`. Nothing weaker would do: an object with a `{±1}`-action has an
invariant part in this sense exactly when that idempotent splits.

**Why the splittings are data.** That the two idempotents split is not proved here, and
splitting idempotents is not available in the library for a derived category. Accordingly the
splittings are arguments of the statements rather than constructed, and every conclusion below
is about whatever splittings are supplied. Their *objects* are nevertheless pinned down: by
`IdempotentSplitting.iso` any two splittings of one idempotent have isomorphic objects, so the
two classes appearing in the formulas, and hence their sum and their difference, depend only on
`L`.

**The hypothesis that `2` is invertible.** The source assumes `2` invertible on the scheme `X`.
What the argument uses is that `2` is invertible on the morphism groups of the category, which
is recorded here as `R`-linearity for a ring `R` with `Invertible (2 : R)` rather than by a new
class. That the derived category of a scheme on which `2` is invertible is `ℤ[1/2]`-linear is
not proved here; it is the one step between the source's hypothesis and the hypothesis used.

**What is not proved.** The source asserts further that `L ↦ [(L ⊗ L)^+] - [(L ⊗ L)^-]`
descends to the `K`-group, i.e. that it is additive along distinguished triangles, and refers
for this to the argument of [Stacks, Tag 0FEJ]. That argument filters the tensor square of a
distinguished triangle in three steps and uses that the switch exchanges the two middle graded
pieces. Neither that filtration of a derived tensor square nor the exactness of taking
invariants is in the library, and no such descent is proved here: the results below are about a
single object `L` and its tensor square.

**The geometric reading.** The symmetric monoidal structure on `D(O_X)` is transported onto the
derived tensor product on the nose by
`Stacks.SheafOfModules.curriedTensor_derivedMonoidalStructure`, so `L ⊗ L` *is*
`((Stacks.SheafOfModules.derivedTensor Rc).obj L).obj L` and the switch needs no comparison
isomorphism. The source reads the construction inside the subcategory `D_perf(O_X)` of perfect
objects, whose `K`-group is `K₀(X)` of [Stacks, Tag 0FDG]; perfect objects are closed under the
derived tensor product by [Stacks, Tag 09JB]
(`AlgebraicGeometry.RingedSite.isPerfect_derivedTensorProduct`). The statements below are made
for an arbitrary symmetric monoidal pretriangulated category and so apply to that subcategory
once it is equipped with the restricted structure, which is not done here.

## References

* [Stacks Project, Tag 0FEK](https://stacks.math.columbia.edu/tag/0FEK)
* [Stacks Project, Tag 0FDG](https://stacks.math.columbia.edu/tag/0FDG)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FCN](https://stacks.math.columbia.edu/tag/0FCN)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated

universe v u

namespace Stacks.SecondAdamsPerfect

/-! ### The switching action -/

section Swap

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- **The switch of the two factors of `L ⊗ L`**: the commutativity constraint of the symmetric
monoidal structure at `(L, L)`. -/
def swapSquare (L : C) : L ⊗ L ⟶ L ⊗ L := (β_ L L).hom

/-- **The switch is an involution.** This is the symmetry of the commutativity constraint, read
at `(L, L)`, and it is what makes the group `{±1}` act on `L ⊗ L`. -/
@[simp, stacks 0FEK "the switch of the two factors of a tensor square is an involution"]
theorem swapSquare_comp_swapSquare (L : C) : swapSquare L ≫ swapSquare L = 𝟙 (L ⊗ L) :=
  SymmetricCategory.symmetry L L

/-- **The action of the group `{±1}` on `L ⊗ L` by switching the factors**: the unit `1` acts by
the identity and the unit `-1` by the switch, which is an involution. -/
@[stacks 0FEK "the action of the group of units {±1} on the tensor square by switching the two \
  factors"]
def swapSquareAction (L : C) : ℤˣ →* End (L ⊗ L) where
  toFun u := if (u : ℤ) = 1 then 𝟙 (L ⊗ L) else swapSquare L
  map_one' := by norm_num; rfl
  map_mul' x y := by
    rcases Int.units_eq_one_or x with hx | hx <;> rcases Int.units_eq_one_or y with hy | hy <;>
      subst hx <;> subst hy <;> norm_num [End.mul_def, End.one_def]

/-- The unit `1` acts on `L ⊗ L` by the identity. -/
@[simp] theorem swapSquareAction_one (L : C) : swapSquareAction L 1 = 𝟙 (L ⊗ L) := by
  simp [swapSquareAction]

/-- The unit `-1` acts on `L ⊗ L` by the switch of the two factors. -/
@[simp] theorem swapSquareAction_neg_one (L : C) : swapSquareAction L (-1) = swapSquare L := by
  norm_num [swapSquareAction]

end Swap

/-! ### Invariants and anti-invariants -/

section Projectors

variable (R : Type*) [Ring R] [Invertible (2 : R)] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [MonoidalCategory C] [SymmetricCategory C]

private theorem half_smul_add_self {M : Type*} [AddCommGroup M] [Module R M] (x : M) :
    ⅟(2 : R) • (x + x) = x := by
  rw [← two_smul R x, smul_smul, invOf_mul_self, one_smul]

/-- **The invariant projector `(𝟙 + σ)/2` of the switch `σ` on `L ⊗ L`.** It is an idempotent,
and the switch acts on it as `+1`. -/
def invariantProjector (L : C) : L ⊗ L ⟶ L ⊗ L := ⅟(2 : R) • (𝟙 (L ⊗ L) + swapSquare L)

/-- **The anti-invariant projector `(𝟙 - σ)/2` of the switch `σ` on `L ⊗ L`.** It is an
idempotent, and the switch acts on it as `-1`. -/
def antiInvariantProjector (L : C) : L ⊗ L ⟶ L ⊗ L := ⅟(2 : R) • (𝟙 (L ⊗ L) - swapSquare L)

variable (L : C)

/-- The two projectors are complementary: their sum is the identity of `L ⊗ L`. -/
@[stacks 0FEK "the invariant and anti-invariant projectors of the switch are complementary"]
theorem invariantProjector_add_antiInvariantProjector :
    invariantProjector R L + antiInvariantProjector R L = 𝟙 (L ⊗ L) := by
  rw [invariantProjector, antiInvariantProjector, ← smul_add]
  rw [show 𝟙 (L ⊗ L) + swapSquare L + (𝟙 (L ⊗ L) - swapSquare L) = 𝟙 (L ⊗ L) + 𝟙 (L ⊗ L) by abel]
  exact half_smul_add_self R _

/-- The switch acts as `+1` on the invariant projector. -/
@[simp] theorem swapSquare_comp_invariantProjector :
    swapSquare L ≫ invariantProjector R L = invariantProjector R L := by
  rw [invariantProjector, Linear.comp_smul, Preadditive.comp_add, Category.comp_id,
    swapSquare_comp_swapSquare, add_comm]

/-- The switch acts as `-1` on the anti-invariant projector. -/
@[simp] theorem swapSquare_comp_antiInvariantProjector :
    swapSquare L ≫ antiInvariantProjector R L = -antiInvariantProjector R L := by
  rw [antiInvariantProjector, Linear.comp_smul, Preadditive.comp_sub, Category.comp_id,
    swapSquare_comp_swapSquare, ← neg_sub, smul_neg]

/-- Precomposing with the invariant projector averages over the switch. -/
private theorem invariantProjector_comp {Y : C} (f : L ⊗ L ⟶ Y) :
    invariantProjector R L ≫ f = ⅟(2 : R) • (f + swapSquare L ≫ f) := by
  rw [invariantProjector, Linear.smul_comp, Preadditive.add_comp, Category.id_comp]

/-- Precomposing with the anti-invariant projector anti-averages over the switch. -/
private theorem antiInvariantProjector_comp {Y : C} (f : L ⊗ L ⟶ Y) :
    antiInvariantProjector R L ≫ f = ⅟(2 : R) • (f - swapSquare L ≫ f) := by
  rw [antiInvariantProjector, Linear.smul_comp, Preadditive.sub_comp, Category.id_comp]

/-- The invariant projector is an idempotent. -/
theorem invariantProjector_comp_self :
    invariantProjector R L ≫ invariantProjector R L = invariantProjector R L := by
  rw [invariantProjector_comp, swapSquare_comp_invariantProjector, half_smul_add_self]

/-- The anti-invariant projector is an idempotent. -/
theorem antiInvariantProjector_comp_self :
    antiInvariantProjector R L ≫ antiInvariantProjector R L = antiInvariantProjector R L := by
  rw [antiInvariantProjector_comp, swapSquare_comp_antiInvariantProjector, sub_neg_eq_add,
    half_smul_add_self]

/-- The two projectors are orthogonal. -/
theorem invariantProjector_comp_antiInvariantProjector :
    invariantProjector R L ≫ antiInvariantProjector R L = 0 := by
  rw [invariantProjector_comp, swapSquare_comp_antiInvariantProjector, add_neg_cancel, smul_zero]

/-- The two projectors are orthogonal. -/
theorem antiInvariantProjector_comp_invariantProjector :
    antiInvariantProjector R L ≫ invariantProjector R L = 0 := by
  rw [antiInvariantProjector_comp, swapSquare_comp_invariantProjector, sub_self, smul_zero]

end Projectors

/-! ### Splitting an idempotent -/

/-- **A splitting of an idempotent endomorphism `e` of `M`**: an object together with a section
and a retraction of `M` composing to the identity one way round and to `e` the other. The
invariants and the anti-invariants of the switch on `L ⊗ L` are, by definition, the objects of
such splittings of `invariantProjector` and of `antiInvariantProjector`. -/
structure IdempotentSplitting {C : Type u} [Category.{v} C] {M : C} (e : M ⟶ M) where
  /-- The object cut out by the idempotent. -/
  obj : C
  /-- The inclusion of the object cut out by the idempotent. -/
  ι : obj ⟶ M
  /-- The projection onto the object cut out by the idempotent. -/
  π : M ⟶ obj
  /-- The inclusion followed by the projection is the identity. -/
  ι_π : ι ≫ π = 𝟙 obj
  /-- The projection followed by the inclusion is the idempotent. -/
  π_ι : π ≫ ι = e

namespace IdempotentSplitting

variable {C : Type u} [Category.{v} C] {M : C} {e : M ⟶ M}

/-- The inclusion of the object cut out by an idempotent is absorbed by the idempotent. -/
theorem ι_comp_self (s : IdempotentSplitting e) : s.ι ≫ e = s.ι :=
  calc s.ι ≫ e = s.ι ≫ s.π ≫ s.ι := by rw [s.π_ι]
    _ = (s.ι ≫ s.π) ≫ s.ι := (Category.assoc _ _ _).symm
    _ = s.ι := by rw [s.ι_π, Category.id_comp]

/-- The projection onto the object cut out by an idempotent absorbs the idempotent. -/
theorem self_comp_π (s : IdempotentSplitting e) : e ≫ s.π = s.π :=
  calc e ≫ s.π = (s.π ≫ s.ι) ≫ s.π := by rw [s.π_ι]
    _ = s.π ≫ s.ι ≫ s.π := Category.assoc _ _ _
    _ = s.π := by rw [s.ι_π, Category.comp_id]

/-- **Two splittings of one idempotent have isomorphic objects.** Hence the invariants and the
anti-invariants of the switch are determined up to isomorphism by the object `L`. -/
def iso (s t : IdempotentSplitting e) : s.obj ≅ t.obj where
  hom := s.ι ≫ t.π
  inv := t.ι ≫ s.π
  hom_inv_id := by
    rw [Category.assoc, reassoc_of% t.π_ι, reassoc_of% s.ι_comp_self, s.ι_π]
  inv_hom_id := by
    rw [Category.assoc, reassoc_of% s.π_ι, reassoc_of% t.ι_comp_self, t.ι_π]

/-- Splittings of two orthogonal idempotents are orthogonal: the inclusion of the object cut out
by one composes to zero with the projection onto the object cut out by the other. -/
theorem ι_comp_π_eq_zero [Limits.HasZeroMorphisms C] {f : M ⟶ M} (s : IdempotentSplitting e)
    (t : IdempotentSplitting f) (h : e ≫ f = 0) : s.ι ≫ t.π = 0 := by
  rw [← s.ι_comp_self, ← t.self_comp_π, Category.assoc, reassoc_of% h, zero_comp, comp_zero]

end IdempotentSplitting

/-! ### The tensor square as the sum of its invariants and anti-invariants -/

section Bicone

variable (R : Type*) [Ring R] [Invertible (2 : R)] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [MonoidalCategory C] [SymmetricCategory C] (L : C)

/-- The invariants and the anti-invariants of the switch, with their inclusions into and
projections from `L ⊗ L`, assembled as a binary bicone on `L ⊗ L`. -/
private def bicone (P : IdempotentSplitting (invariantProjector R L))
    (N : IdempotentSplitting (antiInvariantProjector R L)) : BinaryBicone P.obj N.obj where
  pt := L ⊗ L
  fst := P.π
  snd := N.π
  inl := P.ι
  inr := N.ι
  inl_fst := P.ι_π
  inl_snd := P.ι_comp_π_eq_zero N (invariantProjector_comp_antiInvariantProjector R L)
  inr_fst := N.ι_comp_π_eq_zero P (antiInvariantProjector_comp_invariantProjector R L)
  inr_snd := N.ι_π

private theorem bicone_total (P : IdempotentSplitting (invariantProjector R L))
    (N : IdempotentSplitting (antiInvariantProjector R L)) :
    (bicone R L P N).fst ≫ (bicone R L P N).inl + (bicone R L P N).snd ≫ (bicone R L P N).inr =
      𝟙 (bicone R L P N).pt :=
  (by rw [P.π_ι, N.π_ι]; exact invariantProjector_add_antiInvariantProjector R L :
    P.π ≫ P.ι + N.π ≫ N.ι = 𝟙 (L ⊗ L))

end Bicone

section KGroup

variable (R : Type*) [Ring R] [Invertible (2 : R)] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [MonoidalCategory C] [SymmetricCategory C] (L : C)

/-- **`[L ⊗ L] = [(L ⊗ L)^+] + [(L ⊗ L)^-]` in the `K`-group**: the invariants and the
anti-invariants of the switch exhibit the tensor square as their biproduct, and the split
triangle on a biproduct is distinguished. -/
@[stacks 0FEK "the class of the tensor square is the sum of the classes of the invariants and \
  of the anti-invariants of the switch"]
theorem cls_tensorObj_eq_add (P : IdempotentSplitting (invariantProjector R L))
    (N : IdempotentSplitting (antiInvariantProjector R L)) :
    K0.cls (L ⊗ L) = K0.cls P.obj + K0.cls N.obj := by
  have htot := bicone_total R L P N
  have : HasBinaryBiproduct P.obj N.obj := hasBinaryBiproduct_of_total _ htot
  have e : (L ⊗ L) ≅ P.obj ⊞ N.obj :=
    biprod.uniqueUpToIso P.obj N.obj (isBinaryBilimitOfTotal _ htot)
  rw [K0.cls_eq_of_iso e]
  exact K0.cls_eq_add_of_distinguished (binaryBiproductTriangle_distinguished P.obj N.obj)

/-- The class of the invariants of the switch depends only on `L`. -/
theorem cls_invariants_eq (P P' : IdempotentSplitting (invariantProjector R L)) :
    K0.cls P.obj = K0.cls P'.obj :=
  K0.cls_eq_of_iso (P.iso P')

/-- The class of the anti-invariants of the switch depends only on `L`. -/
theorem cls_antiInvariants_eq (N N' : IdempotentSplitting (antiInvariantProjector R L)) :
    K0.cls N.obj = K0.cls N'.obj :=
  K0.cls_eq_of_iso (N.iso N')

/-- **The difference `[(L ⊗ L)^+] - [(L ⊗ L)^-]` is independent of the chosen invariants and
anti-invariants**, hence a well-defined element of the `K`-group attached to `L`. This is the
value the second Adams operator of the source is to take on `L`. -/
@[stacks 0FEK "the difference of the classes of the invariants and of the anti-invariants of \
  the switch on the tensor square is a well-defined element of the K-group attached to the \
  object; its additivity along distinguished triangles is not proved"]
theorem cls_sub_cls_eq (P P' : IdempotentSplitting (invariantProjector R L))
    (N N' : IdempotentSplitting (antiInvariantProjector R L)) :
    K0.cls P.obj - K0.cls N.obj = K0.cls P'.obj - K0.cls N'.obj := by
  rw [cls_invariants_eq R L P P', cls_antiInvariants_eq R L N N']

end KGroup

/-! ### The switching action on a derived tensor square -/

section Derived

open TopologicalSpace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.derivedMonoidalStructure
  Stacks.SheafOfModules.derivedSymmetricStructure

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **The switch of the two factors of `L ⊗^L_{O_X} L`** in the derived category of a ringed
space: the Koszul commutativity constraint of
`Stacks.SheafOfModules.derivedSymmetricStructure`, whose tensor product is the derived tensor
product of `Stacks.SheafOfModules.derivedTensor` on the nose. -/
def derivedSwapSquare (L : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj L).obj L ⟶ ((derivedTensor Rc).obj L).obj L :=
  swapSquare L

/-- **The switch of the two factors of `L ⊗^L_{O_X} L` is an involution.** -/
@[stacks 0FEK "the switch of the two factors of the derived tensor square on a ringed space is \
  an involution"]
theorem derivedSwapSquare_comp_self (L : DerivedCategory (StructureSheafModules Rc)) :
    derivedSwapSquare Rc L ≫ derivedSwapSquare Rc L = 𝟙 (((derivedTensor Rc).obj L).obj L) :=
  swapSquare_comp_swapSquare L

/-- **The action of the group `{±1}` on `L ⊗^L_{O_X} L` by switching the factors**, in the
derived category of a ringed space. -/
@[stacks 0FEK "the action of the group {±1} on the derived tensor square of an object of D(O_X) \
  by switching the two factors"]
def derivedSwapSquareAction (L : DerivedCategory (StructureSheafModules Rc)) :
    ℤˣ →* End (((derivedTensor Rc).obj L).obj L) :=
  swapSquareAction L

/-- The unit `-1` acts on `L ⊗^L_{O_X} L` by the switch of the two factors. -/
@[simp] theorem derivedSwapSquareAction_neg_one
    (L : DerivedCategory (StructureSheafModules Rc)) :
    derivedSwapSquareAction Rc L (-1) = derivedSwapSquare Rc L :=
  swapSquareAction_neg_one L

end Derived

end Stacks.SecondAdamsPerfect

end
