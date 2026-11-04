module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseExteriorSymmetricAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# The universal properties of the sectionwise tensor, exterior and symmetric algebras

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseTensorAlgebra` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseExteriorSymmetricAlgebra` build the
three sectionwise graded algebras of a presheaf of modules `F` over a presheaf of commutative
rings `O` — `U ↦ T_{O(U)}(F(U))`, `U ↦ ⋀_{O(U)}(F(U))` and `U ↦ Sym_{O(U)}(F(U))` — as
`Stacks.GradedAlgebra`s, with their degree-one generators. This file proves their universal
properties: a degree-one morphism of presheaves of modules into any graded algebra of presheaves
of modules extends to a *unique* unital homomorphism out of the sectionwise tensor algebra, and
likewise out of its exterior and symmetric quotients once the degree-one morphism satisfies the
corresponding side condition.

This is the input that `Stacks.GradedAlgebra.isTensorAlgebra_sheafify`,
`isExteriorAlgebra_sheafify` and `isSymmetricAlgebra_sheafify` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction`) consume, and which the
implementation notes of that file record as missing: with it, the three `IsTensorAlgebra`,
`IsExteriorAlgebra` and `IsSymmetricAlgebra` fields of
`SheafOfModules.TensorExteriorSymmetricAlgebras` are available for the sheafification of the
sectionwise algebras. See the implementation notes for what is still missing for an inhabitant
of that bundle.

## Main definitions

* `PresheafOfModules.tensorAlgebraTotalLift`, `exteriorAlgebraTotalLift` and
  `symmetricAlgebraTotalLift`: the ring homomorphism from the tensor, exterior respectively
  symmetric algebra of the sections of `F` over an object of the site into the ungraded
  realization `Stacks.GradedAlgebra.Total` of the target graded algebra, determined by the
  degree-one morphism.
* `PresheafOfModules.tensorAlgebraDesc`, `exteriorAlgebraDesc` and `symmetricAlgebraDesc`: the
  unital homomorphism of graded algebras of presheaves of modules those lifts assemble into,
  degreewise the degree-`n` component of the lift.
* `PresheafOfModules.tensorAlgebraPieceMk`, `exteriorAlgebraPieceMk` and
  `symmetricAlgebraPieceMk`: an element of the algebra of sections, read as a local section of
  the homogeneous piece it lies in. These exist only because the sections of a homogeneous piece
  are a `ModuleCat` object rather than syntactically a subtype, so the anonymous constructor
  does not elaborate at that type.
* `PresheafOfModules.restrictGen`: a degree-one generator of a sheaf of graded algebras, read
  along the sheafification unit as a degree-one morphism into the restriction of scalars. This is
  the translation between the shape `Stacks.GradedAlgebra.isUniversal_sheafify` asks for and the
  shape the three universal properties below are stated in.

## Main results

* `Stacks.GradedAlgebra.incl_injective`: a homogeneous local section is determined by its image
  in the ungraded realization. Every proof below is an application of this: an equation between
  local sections of one homogeneous piece is proved by comparing the two ungraded images, where
  the graded transports disappear and the laws are ring laws.
* `PresheafOfModules.existsUnique_unitalHom_tensorAlgebra`: **the universal property of the
  sectionwise tensor algebra.** For every graded algebra `D` of presheaves of `O`-modules and
  every `lam : F ⟶ Q 1` there is a unique unital homomorphism out of
  `tensorAlgebraGradedAlgebra F` whose degree-one component carries the degree-one generator
  to `lam`.
* `PresheafOfModules.existsUnique_unitalHom_exteriorAlgebra` and
  `existsUnique_unitalHom_symmetricAlgebra`: the same for the exterior and symmetric algebras,
  under the hypothesis that the image of `lam` squares to zero, respectively commutes pairwise.
  Those are exactly the side conditions `SheafOfModules.GradedAlgebra.SquareZero` and
  `PairwiseCommutes` impose on a degree-one generator.
* `PresheafOfModules.isTensorAlgebra_sheafify_tensorAlgebra`,
  `isExteriorAlgebra_sheafify_exteriorAlgebra` and `isSymmetricAlgebra_sheafify_symmetricAlgebra`:
  **the three universal properties of the sheafified sectionwise algebras**, which are the
  `tensor_isTensorAlgebra`, `exterior_isExteriorAlgebra` and `symmetric_isSymmetricAlgebra` fields
  of `SheafOfModules.TensorExteriorSymmetricAlgebras` for those algebras. These are the three
  results `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction` reduces to
  sectionwise data and leaves open.

## Implementation notes

**Why the ungraded realization.** A unital homomorphism out of one of these algebras is a family
of morphisms of presheaves of modules, one in each degree, multiplicative on homogeneous local
sections. Constructing it degree by degree would mean lifting out of each homogeneous piece
separately, and the multiplicativity law relates three different degrees. Instead everything is
done at once in `Stacks.GradedAlgebra.Total`, the direct sum of the homogeneous pieces over a
fixed object of the site: there the target is a single *ring* with a compatible module
structure, which is precisely what `TensorAlgebra.liftRing`, `ExteriorAlgebra.liftRing` and
`SymmetricAlgebra.liftComm` map into, and the degreewise morphism is recovered as the
degree-`n` component `Stacks.GradedAlgebra.proj` of the lift. The only thing to prove is that
the lift of a degree-`n` element is *concentrated* in degree `n`
(`PresheafOfModules.exists_incl_tensorAlgebraTotalLift` and its two analogues), which is an
induction over `Submodule.pow_induction_on_right'` on the homogeneous piece.

**Why the induction multiplies on the right.** The homogeneous pieces are the submodules
`LinearMap.range ι ^ n` of a single algebra, with `n : ℕ`, while the graded algebra is indexed by
`ℤ`. `Submodule.pow_induction_on_right'` produces the degree-`n + 1` case as `x * m` with
`x` of degree `n`, so the degree of the product is `(n : ℤ) + 1`, which is *definitionally*
`((n + 1 : ℕ) : ℤ)`. The left-handed induction gives `1 + (n : ℤ)`, which is not, and would force
a transport along `Int.add_comm` into every step. This is the same reason
`Stacks.GradedAlgebra.homogeneousProd` multiplies on the right.

**The degree spellings.** `((n : ℕ) : ℤ)` and `Int.ofNat n` are definitionally equal but not
syntactically so, and `rw` works at reducible transparency, so a rewrite stated at one spelling
does not fire at the other. The two places where this bites — splitting an integer degree into
the nonnegative and the negative case, and the inductive step — are handled by
`Int.eq_ofNat_of_zero_le`, which produces the `((n : ℕ) : ℤ)` spelling in the goal, and by
stating the inductive step as its own lemma at a free integer degree
(`PresheafOfModules.incl_unitalHom_tensorAlgebra_app_mul_gen` and its two analogues) and
`exact`ing it, which checks at default transparency. No transparency option and no `erw` is
used.

**One proof is written in tactic mode for a reason.**
`PresheafOfModules.isSymmetricAlgebra_sheafify_symmetricAlgebra` is `refine ... ?_ ?_` followed
by two `exact`s rather than a single application, because as one term the elaborator unifies the
two arguments against the expected type at once and exhausts its budget at `whnf`: the written-out
commutation condition of `Stacks.GradedAlgebra.isSymmetricAlgebra_sheafify` mentions the
degree-`1 + 1` symmetric piece, and unfolding `SymPow.symmetricPower` there is the same cost that
the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseExteriorSymmetricAlgebra` record for
`symPowIntGradedAlgebra_genCommutes`. Splitting the application postpones each unification until its
own goal is fixed, and both then check cheaply.

**What is still missing for an inhabitant of the bundle.** The bundle
`SheafOfModules.TensorExteriorSymmetricAlgebras` has twenty-three fields. For the
sheafifications of the three sectionwise algebras, `Stacks.GradedAlgebra.sheafify` and
`sheafifyGen` supply the three algebras and their three generators;
`sheafify_piece_eq_zero` together with
`PresheafOfModules.tensorAlgebraPiece_eq_zero_of_neg` and its two analogues supplies the three
vanishing fields; this file supplies the three universal properties, and the two quotient maps and
their two compatibilities then follow from the tensor algebra's universal property
(`SheafOfModules.GradedAlgebra.IsTensorAlgebra.descAny`). That is fifteen. The eight that remain
are the ones about the *tensor powers* and about degree zero:

* `tensorGenerator` is a morphism out of the sheaf `F`, while `sheafifyGen` produces one out of
  `(sheafification α).obj F.val`; the two agree through the sheafification unit, which is an
  isomorphism because `F` is a sheaf, and `IsTensorAlgebra` has to be transported along it.
* `tensorPieceIso`, `tensorPieceIso_one` and `tensorPieceIso_mul_left`:
  `SheafOfModules.tensorPowerSheafifyIso` reduces these to the *sectionwise* recursion
  `Tⁿ⁺²(F(U)) ≅ Tⁿ⁺¹⁻ᵒⁿᵉ · T¹`, i.e. to the assertion that multiplication
  `range ι ^ 1 ⊗_{O(U)} range ι ^ (n + 1) ⟶ range ι ^ (n + 2)` is bijective. Taking the
  comparison to *be* the multiplication map makes its naturality in `U` free — ring
  multiplication commutes with `TensorAlgebra.mapₛₗ` — and leaves only bijectivity, which is
  pointwise algebra. The pieces Mathlib has for that are `TensorPower.mulEquiv`
  (`⨂[R]^i M ⊗ ⨂[R]^j M ≃ ⨂[R]^(i + j) M`), `TensorPower.toTensorAlgebra` with
  `toTensorAlgebra_tprod` and `toTensorAlgebra_gMul`, and `TensorAlgebra.toDirectSum` with
  `toDirectSum_tensorPower_tprod`. What Mathlib does *not* have is the bridge between the
  external tensor powers and the internal grading: no statement that `toTensorAlgebra` is
  injective with range `LinearMap.range (ι R) ^ n`. Both halves of that are available here —
  surjectivity onto the piece is `TensorAlgebra.pow_range_ι_eq_span_prod_ι`, and injectivity
  follows from `toDirectSum (toTensorAlgebra x) = DirectSum.lof n x`, proved on `tprod`s. This is
  the one missing mathematical input, and it is a module-level statement about
  `TensorAlgebra`, with no sheaf theory in it.
* `tensorPieceIso_zero`, `exteriorPieceIso_zero` and `exteriorPieceIso_zero_one`: the degree-zero
  pieces are free of rank one on the unit, by `Submodule.mem_one` and the injectivity of
  `algebraMap`, which for the tensor algebra is
  `TensorAlgebra.algebraMap_algebraMapInv_of_mem_intPiece_zero`.
* `tensorDirectSumIso` and `tensorDirectSumIso_ι`: formal consequences of `tensorPieceIso`, by
  `Limits.Sigma.mapIso`; `TensorExteriorSymmetricAlgebras.tensorDirectSumIso_unique` shows the
  field is determined by the one below it.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace Stacks.GradedAlgebra

/-! ### A homogeneous section is determined by its ungraded image -/

section Incl

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
  {Q : ℤ → PresheafOfModules.{a} R} (D : Stacks.GradedAlgebra Q)

/-- A homogeneous local section is determined by its image in the ungraded realization. This is
`DirectSum.of_injective`, and it is what every law below is proved through: an equation between
sections of a single homogeneous piece becomes an equation in a ring, where the graded degrees
no longer appear. -/
theorem incl_injective (i : ℤ) (X : Cᵒᵖ) : Function.Injective (D.incl (X := X) i) :=
  DirectSum.of_injective (β := fun j => ((Q j).obj X : Type a)) i

end Incl

end Stacks.GradedAlgebra

namespace PresheafOfModules

/-! ### The tensor algebra -/

section Tensor

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- An element of the tensor algebra of the sections, read as a local section of the homogeneous
piece it lies in. The sections of `tensorAlgebraPiece n F` are a `ModuleCat` object rather than
syntactically a subtype, so the anonymous constructor does not elaborate at that type. -/
noncomputable def tensorAlgebraPieceMk (n : ℤ) (X : Cᵒᵖ)
    (v : TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
    (hv : v ∈ TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n) :
    (tensorAlgebraPiece n F).obj X :=
  (⟨v, hv⟩ : ↥(TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n))

/-- Reading `tensorAlgebraPieceMk` back in the tensor algebra of the sections returns the
element it was built from. -/
@[simp]
theorem tensorAlgebraPieceVal_mk (n : ℤ) (X : Cᵒᵖ)
    (v : TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
    (hv : v ∈ TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n) :
    tensorAlgebraPieceVal n F X (tensorAlgebraPieceMk F n X v hv) = v := rfl

variable {Q : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (D : Stacks.GradedAlgebra Q) (lam : F ⟶ Q 1)

/-- **The ring homomorphism out of the sectionwise tensor algebra.** The tensor algebra of the
sections of `F` over `X` maps to the ungraded realization of `D` over `X`, sending a degree-one
generator to the degree-one section `lam` names. -/
noncomputable def tensorAlgebraTotalLift (X : Cᵒᵖ) :
    TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →+* D.Total X :=
  TensorAlgebra.liftRing (fun r x y => D.smul_mul_eq (X := X) r x y)
    (fun r x y => D.mul_smul_eq (X := X) r x y) (D.genLin lam X)

/-- The lift sends a degree-one generator to the degree-one section that `lam` names. -/
@[simp]
theorem tensorAlgebraTotalLift_ι (X : Cᵒᵖ) (m : F.obj X) :
    tensorAlgebraTotalLift F D lam X (TensorAlgebra.ι _ m) = D.incl 1 (lam.app X m) :=
  TensorAlgebra.liftRing_ι m

/-- The lift is linear over the ring of sections. -/
theorem tensorAlgebraTotalLift_smul (X : Cᵒᵖ) (r : (O ⋙ forget₂ _ RingCat).obj X)
    (x : TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    tensorAlgebraTotalLift F D lam X (r • x) = r • tensorAlgebraTotalLift F D lam X x :=
  TensorAlgebra.liftRing_smul r x

/-- The lift sends a scalar to its image under the structure map of `D`. -/
theorem tensorAlgebraTotalLift_algebraMap (X : Cᵒᵖ) (r : (O ⋙ forget₂ _ RingCat).obj X) :
    tensorAlgebraTotalLift F D lam X (algebraMap _ _ r) = D.structureMap X r := by
  rw [Algebra.algebraMap_eq_smul_one, tensorAlgebraTotalLift_smul, map_one]
  rfl

/-- The lift sends a scalar `r` to the degree-zero section `r • 1`. -/
theorem tensorAlgebraTotalLift_algebraMap_incl (X : Cᵒᵖ)
    (r : (O ⋙ forget₂ _ RingCat).obj X) :
    tensorAlgebraTotalLift F D lam X (algebraMap _ _ r) = D.incl 0 (r • D.one.eval X) := by
  rw [tensorAlgebraTotalLift_algebraMap, D.incl_smul, ← D.one_eq_incl]
  rfl

/-- A ring homomorphism `φ` into the ungraded realization that sends scalars to degree zero and the
generators `ι m` to the degree-one section `lam m` sends the `n`-th power of the range of `ι` to
degree `n`. The induction multiplies on the right, so that the degree of the inductive step is
`(i : ℤ) + 1`, which is definitionally the cast of `i + 1`. -/
private theorem exists_incl_of_mem_pow_range (X : Cᵒᵖ) {A : Type*} [Semiring A]
    [Algebra ((O ⋙ forget₂ _ RingCat).obj X) A]
    (ι : F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] A) (φ : A →+* D.Total X)
    (h₀ : ∀ r, φ (algebraMap ((O ⋙ forget₂ _ RingCat).obj X) A r) =
      D.incl 0 (r • D.one.eval X))
    (h₁ : ∀ m, φ (ι m) = D.incl 1 (lam.app X m)) (n : ℕ) {x : A}
    (hx : x ∈ LinearMap.range ι ^ n) : ∃ y : (Q (n : ℤ)).obj X, φ x = D.incl (n : ℤ) y := by
  induction hx using Submodule.pow_induction_on_right' with
  | algebraMap r => exact ⟨r • D.one.eval X, h₀ r⟩
  | add x y i hx hy ihx ihy =>
      obtain ⟨p, hp⟩ := ihx
      obtain ⟨q, hq⟩ := ihy
      exact ⟨p + q, by rw [map_add, hp, hq, D.incl_add]⟩
  | mul_mem i x hx ih m hm =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨m₀, rfl⟩ := hm
      refine ⟨(D.mul (i : ℤ) 1).app X p (lam.app X m₀), ?_⟩
      rw [map_mul, hp, h₁, D.incl_mul_incl]
      rfl

/-- **The lift is concentrated in a single degree on each homogeneous piece.** -/
theorem exists_incl_tensorAlgebraTotalLift (X : Cᵒᵖ) (n : ℕ)
    {x : TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)}
    (hx : x ∈ LinearMap.range (TensorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) :
      F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] _) ^ n) :
    ∃ y : (Q (n : ℤ)).obj X, tensorAlgebraTotalLift F D lam X x = D.incl (n : ℤ) y :=
  exists_incl_of_mem_pow_range F D lam X _ _ (tensorAlgebraTotalLift_algebraMap_incl F D lam X)
    (tensorAlgebraTotalLift_ι F D lam X) n hx

/-- The lift commutes with restriction along a morphism of the site. -/
theorem tensorAlgebraTotalLift_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    D.totalRestrict f (tensorAlgebraTotalLift F D lam X x) =
      tensorAlgebraTotalLift F D lam Y
        (TensorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x) := by
  have key : (D.totalRestrictRingHom f).comp (tensorAlgebraTotalLift F D lam X) =
      (tensorAlgebraTotalLift F D lam Y).comp
        (TensorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)) := by
    refine TensorAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · show D.totalRestrict f (tensorAlgebraTotalLift F D lam X (algebraMap _ _ r)) =
        tensorAlgebraTotalLift F D lam Y (TensorAlgebra.mapₛₗ _ (F.restrictₛₗ f)
          (algebraMap _ _ r))
      rw [tensorAlgebraTotalLift_algebraMap, TensorAlgebra.mapₛₗ_algebraMap,
        tensorAlgebraTotalLift_algebraMap, D.structureMap_naturality]
    · show D.totalRestrict f (tensorAlgebraTotalLift F D lam X (TensorAlgebra.ι _ m)) =
        tensorAlgebraTotalLift F D lam Y (TensorAlgebra.mapₛₗ _ (F.restrictₛₗ f)
          (TensorAlgebra.ι _ m))
      rw [tensorAlgebraTotalLift_ι, TensorAlgebra.mapₛₗ_ι, tensorAlgebraTotalLift_ι,
        D.totalRestrict_incl]
      refine congrArg (D.incl 1) ?_
      rw [Stacks.sectionRestrict_apply]
      exact (PresheafOfModules.naturality_apply lam f m).symm
  exact congrFun (congrArg (fun g : TensorAlgebra _ _ →+* D.Total Y => g.toFun) key) x

/-- The lift, read on a local section of a homogeneous piece. -/
noncomputable def tensorAlgebraDescLin (n : ℤ) (X : Cᵒᵖ) :
    (tensorAlgebraPiece n F).obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] D.Total X where
  toFun x := tensorAlgebraTotalLift F D lam X (tensorAlgebraPieceVal n F X x)
  map_add' _ _ := map_add (tensorAlgebraTotalLift F D lam X) _ _
  map_smul' r _ := tensorAlgebraTotalLift_smul F D lam X r _

/-- The degree-`n` component of the lift. -/
noncomputable def tensorAlgebraDescAppLin (n : ℤ) (X : Cᵒᵖ) :
    (tensorAlgebraPiece n F).obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] (Q n).obj X :=
  (D.proj X n).comp (tensorAlgebraDescLin F D lam n X)

/-- The degree-`n` component `proj` of a ring homomorphism `φ` into the ungraded realization loses
nothing on the image of `val`, provided `φ` is concentrated in degree `k` on degree-`k` elements
and the negative degrees are trivial. -/
private theorem incl_proj_of_exists_incl (X : Cᵒᵖ) {A : Type*} [Semiring A] (φ : A →+* D.Total X)
    {P : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (val : ∀ n, (P n).obj X → A)
    (hval₀ : ∀ n, val n 0 = 0) (hneg : ∀ n, n < 0 → ∀ y : (P n).obj X, y = 0)
    (hex : ∀ (k : ℕ) (y : (P k).obj X), ∃ z : (Q (k : ℤ)).obj X, φ (val k y) = D.incl (k : ℤ) z)
    (n : ℤ) (y : (P n).obj X) : D.incl n (D.proj X n (φ (val n y))) = φ (val n y) := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    obtain ⟨z, hz⟩ := hex k y
    rw [hz, D.proj_incl]
  · rw [hneg n hn y, hval₀, map_zero, map_zero, D.incl_zero]

/-- The degree-`n` component of the lift loses nothing: its ungraded image is the lift itself,
because the lift of a degree-`n` element is concentrated in degree `n`. -/
theorem incl_tensorAlgebraDescAppLin (n : ℤ) (X : Cᵒᵖ) (x : (tensorAlgebraPiece n F).obj X) :
    D.incl n (tensorAlgebraDescAppLin F D lam n X x) =
      tensorAlgebraTotalLift F D lam X (tensorAlgebraPieceVal n F X x) :=
  incl_proj_of_exists_incl D X _ (fun n => tensorAlgebraPieceVal n F X) (fun _ => rfl)
    (fun _ hn y => tensorAlgebraPiece_eq_zero_of_neg hn F X y)
    (fun k y => exists_incl_tensorAlgebraTotalLift F D lam X k
      (y : ↥(TensorAlgebra.intPiece _ _ (k : ℤ))).2) n x

/-- The degree-`n` component of the lift commutes with restriction along a morphism of the site. -/
theorem tensorAlgebraDescAppLin_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (tensorAlgebraPiece n F).obj X) :
    Stacks.sectionRestrict (Q n) f (tensorAlgebraDescAppLin F D lam n X x) =
      tensorAlgebraDescAppLin F D lam n Y
        (Stacks.sectionRestrict (tensorAlgebraPiece n F) f x) := by
  refine D.incl_injective n Y ?_
  rw [← D.totalRestrict_incl f n (tensorAlgebraDescAppLin F D lam n X x),
    incl_tensorAlgebraDescAppLin, incl_tensorAlgebraDescAppLin,
    tensorAlgebraTotalLift_naturality]
  rfl

/-- The degreewise morphism out of the sectionwise tensor algebra determined by `lam`. -/
noncomputable def tensorAlgebraDescApp (n : ℤ) : tensorAlgebraPiece n F ⟶ Q n where
  app X := ModuleCat.ofHom (tensorAlgebraDescAppLin F D lam n X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (tensorAlgebraDescAppLin_naturality F D lam _ f x).symm)

/-- The ungraded image of `tensorAlgebraDescApp` is the lift. -/
@[simp]
theorem incl_tensorAlgebraDescApp (n : ℤ) (X : Cᵒᵖ) (x : (tensorAlgebraPiece n F).obj X) :
    D.incl n (PresheafOfModules.Hom.app (tensorAlgebraDescApp F D lam n) X x) =
      tensorAlgebraTotalLift F D lam X (tensorAlgebraPieceVal n F X x) :=
  incl_tensorAlgebraDescAppLin F D lam n X x

/-- **The unital homomorphism out of the sectionwise tensor algebra determined by a degree-one
morphism.** -/
noncomputable def tensorAlgebraDesc :
    Stacks.GradedAlgebra.UnitalHom (tensorAlgebraGradedAlgebra F) D where
  app := tensorAlgebraDescApp F D lam
  map_mul i j X x y := by
    refine D.incl_injective (i + j) X ?_
    rw [incl_tensorAlgebraDescApp, ← D.incl_mul_incl, incl_tensorAlgebraDescApp,
      incl_tensorAlgebraDescApp, ← map_mul]
    rfl
  map_one X := by
    refine D.incl_injective 0 X ?_
    rw [incl_tensorAlgebraDescApp, ← D.one_eq_incl]
    exact map_one _

/-- `tensorAlgebraDesc` carries the degree-one generator to `lam`. -/
theorem tensorAlgebraDesc_gen (X : Cᵒᵖ) (m : F.obj X) :
    PresheafOfModules.Hom.app ((tensorAlgebraDesc F D lam).app 1) X
        (PresheafOfModules.Hom.app (tensorAlgebraGen F) X m) =
      PresheafOfModules.Hom.app lam X m := by
  refine D.incl_injective 1 X ?_
  show D.incl 1 (PresheafOfModules.Hom.app (tensorAlgebraDescApp F D lam 1) X _) = _
  rw [incl_tensorAlgebraDescApp, tensorAlgebraPieceVal_gen, tensorAlgebraTotalLift_ι]

/-- Degree-zero case of the uniqueness argument shared by the three sectionwise algebras: degree
zero sections are scalar multiples of the unit, which a unital homomorphism preserves. -/
private theorem incl_unitalHom_app_zero_of_pow_range (X : Cᵒᵖ) {A : Type*} [Semiring A]
    [Algebra ((O ⋙ forget₂ _ RingCat).obj X) A]
    (ι : F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] A) (φ : A →+* D.Total X)
    {P : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} {G : Stacks.GradedAlgebra P}
    (g : Stacks.GradedAlgebra.UnitalHom G D) (val : (P 0).obj X → A) (hinj : Function.Injective val)
    (hmem : ∀ y, val y ∈ LinearMap.range ι ^ 0)
    (hone : ∀ r, val (r • G.one.eval X) = algebraMap ((O ⋙ forget₂ _ RingCat).obj X) A r)
    (h₀ : ∀ r, φ (algebraMap ((O ⋙ forget₂ _ RingCat).obj X) A r) =
      D.incl 0 (r • D.one.eval X))
    (y : (P 0).obj X) : D.incl 0 (PresheafOfModules.Hom.app (g.app 0) X y) = φ (val y) := by
  have hy := hmem y
  rw [pow_zero] at hy
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 hy
  obtain rfl : y = r • G.one.eval X := hinj (by rw [hone, hr])
  rw [map_smul, g.map_one X, hone, h₀]

/-- Uniqueness argument shared by the three sectionwise algebras: a unital homomorphism `g` out of
a graded algebra `G` whose pieces are identified (through `val`) with the powers of the range of
`ι` in an algebra `A` agrees in every degree with `φ ∘ val`, once it does so in degree zero and in
the inductive step `y ↦ y * ι m`. -/
private theorem incl_unitalHom_app_of_pow_range (X : Cᵒᵖ) {A : Type*} [Semiring A]
    [Algebra ((O ⋙ forget₂ _ RingCat).obj X) A]
    (ι : F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] A) (φ : A →+* D.Total X)
    {P : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} {G : Stacks.GradedAlgebra P}
    (gen : F ⟶ P 1) (g : Stacks.GradedAlgebra.UnitalHom G D) (val : ∀ n, (P n).obj X → A)
    (hinj : ∀ n, Function.Injective (val n))
    (hrange : ∀ (k : ℕ) (v : A), v ∈ LinearMap.range ι ^ k ↔ ∃ y, val k y = v)
    (hadd : ∀ n y y', val n (y + y') = val n y + val n y') (hval₀ : ∀ n, val n 0 = 0)
    (hmul : ∀ i y m, val (i + 1) ((G.mul i 1).app X y (PresheafOfModules.Hom.app gen X m)) =
      val i y * ι m)
    (hneg : ∀ n, n < 0 → ∀ y : (P n).obj X, y = 0)
    (hzero : ∀ y, D.incl 0 (PresheafOfModules.Hom.app (g.app 0) X y) = φ (val 0 y))
    (hstep : ∀ i y m, D.incl i (PresheafOfModules.Hom.app (g.app i) X y) = φ (val i y) →
      D.incl (i + 1) (PresheafOfModules.Hom.app (g.app (i + 1)) X
        ((G.mul i 1).app X y (PresheafOfModules.Hom.app gen X m))) = φ (val i y * ι m))
    (n : ℤ) (y : (P n).obj X) :
    D.incl n (PresheafOfModules.Hom.app (g.app n) X y) = φ (val n y) := by
  have key : ∀ (k : ℕ) (v : A), v ∈ LinearMap.range ι ^ k → ∀ y : (P k).obj X, val k y = v →
      D.incl (k : ℤ) (PresheafOfModules.Hom.app (g.app (k : ℤ)) X y) = φ v := by
    intro k v hv
    induction hv using Submodule.pow_induction_on_right' with
    | algebraMap r =>
        intro y hy
        exact hy ▸ hzero y
    | add v v' i hv hv' ihv ihv' =>
        intro y hy
        obtain ⟨y₁, rfl⟩ := (hrange i v).1 hv
        obtain ⟨y₂, rfl⟩ := (hrange i v').1 hv'
        obtain rfl : y = y₁ + y₂ := hinj _ (hy.trans (hadd _ _ _).symm)
        rw [map_add, D.incl_add, ihv _ rfl, ihv' _ rfl, map_add]
    | mul_mem i v hv ih m hm =>
        intro y hy
        obtain ⟨m₀, rfl⟩ := hm
        obtain ⟨y₁, rfl⟩ := (hrange i v).1 hv
        obtain rfl : y = (G.mul (i : ℤ) 1).app X y₁ (PresheafOfModules.Hom.app gen X m₀) :=
          hinj _ (hy.trans (hmul _ _ _).symm)
        exact hstep (i : ℤ) y₁ m₀ (ih _ rfl)
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact key k _ ((hrange k _).2 ⟨y, rfl⟩) y rfl
  · rw [hneg n hn y, map_zero, D.incl_zero, hval₀, map_zero]

variable (g : Stacks.GradedAlgebra.UnitalHom (tensorAlgebraGradedAlgebra F) D)

/-- A degree-zero local section of the sectionwise tensor algebra is a scalar multiple of the
unit, so a unital homomorphism has no freedom there. -/
theorem incl_unitalHom_tensorAlgebra_app_zero (X : Cᵒᵖ)
    (y : (tensorAlgebraPiece (0 : ℤ) F).obj X) :
    D.incl 0 (PresheafOfModules.Hom.app (g.app 0) X y) =
      tensorAlgebraTotalLift F D lam X (tensorAlgebraPieceVal 0 F X y) :=
  incl_unitalHom_app_zero_of_pow_range F D X _ _ g (tensorAlgebraPieceVal 0 F X)
    (tensorAlgebraPieceVal_injective _ F X) (fun y => (y : ↥(TensorAlgebra.intPiece _ _ 0)).2)
    (fun r => by
      change r • tensorAlgebraPieceVal 0 F X ((tensorAlgebraOne F).eval X) = _
      rw [tensorAlgebraPieceVal_one, Algebra.algebraMap_eq_smul_one])
    (tensorAlgebraTotalLift_algebraMap_incl F D lam X) y

/-- The inductive step of the uniqueness argument, at a free integer degree so that no transport
along `Int.add_comm` or along the cast of `n + 1` appears. -/
theorem incl_unitalHom_tensorAlgebra_app_mul_gen
    (hg : ∀ (X : Cᵒᵖ) (m : F.obj X),
      PresheafOfModules.Hom.app (g.app 1) X
          (PresheafOfModules.Hom.app (tensorAlgebraGen F) X m) =
        PresheafOfModules.Hom.app lam X m)
    (i : ℤ) (X : Cᵒᵖ) (y : (tensorAlgebraPiece i F).obj X) (m₀ : F.obj X)
    (h : D.incl i (PresheafOfModules.Hom.app (g.app i) X y) =
      tensorAlgebraTotalLift F D lam X (tensorAlgebraPieceVal i F X y)) :
    D.incl (i + 1) (PresheafOfModules.Hom.app (g.app (i + 1)) X
        (((tensorAlgebraGradedAlgebra F).mul i 1).app X y
          (PresheafOfModules.Hom.app (tensorAlgebraGen F) X m₀))) =
      tensorAlgebraTotalLift F D lam X
        (tensorAlgebraPieceVal i F X y * TensorAlgebra.ι _ m₀) := by
  rw [g.map_mul i 1 X y (PresheafOfModules.Hom.app (tensorAlgebraGen F) X m₀),
    ← D.incl_mul_incl, h, hg X m₀, ← tensorAlgebraTotalLift_ι F D lam X m₀, ← map_mul]

/-- **A unital homomorphism out of the sectionwise tensor algebra is determined by its
degree-one component**, because the ungraded image of a local section of a homogeneous piece is
forced by the lift. -/
theorem incl_unitalHom_tensorAlgebra_app
    (hg : ∀ (X : Cᵒᵖ) (m : F.obj X),
      PresheafOfModules.Hom.app (g.app 1) X
          (PresheafOfModules.Hom.app (tensorAlgebraGen F) X m) =
        PresheafOfModules.Hom.app lam X m)
    (n : ℤ) (X : Cᵒᵖ) (x : (tensorAlgebraPiece n F).obj X) :
    D.incl n (PresheafOfModules.Hom.app (g.app n) X x) =
      tensorAlgebraTotalLift F D lam X (tensorAlgebraPieceVal n F X x) :=
  incl_unitalHom_app_of_pow_range F D X _ _ (tensorAlgebraGen F) g
    (fun n => tensorAlgebraPieceVal n F X) (fun n => tensorAlgebraPieceVal_injective n F X)
    (fun k v => ⟨fun hv => ⟨tensorAlgebraPieceMk F k X v hv, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ (y : ↥(TensorAlgebra.intPiece _ _ (k : ℤ))).2⟩)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)
    (fun _ hn y => tensorAlgebraPiece_eq_zero_of_neg hn F X y)
    (incl_unitalHom_tensorAlgebra_app_zero F D lam g X)
    (fun i y m h => incl_unitalHom_tensorAlgebra_app_mul_gen F D lam g hg i X y m h) n x

/-- **The universal property of the sectionwise tensor algebra.** A degree-one morphism of
presheaves of modules into a graded algebra of presheaves of modules extends to a unique unital
homomorphism out of the sectionwise tensor algebra.

This is the hypothesis of `Stacks.GradedAlgebra.isTensorAlgebra_sheafify`, hence the
`tensor_isTensorAlgebra` field of `SheafOfModules.TensorExteriorSymmetricAlgebras` for the
sheafification of `tensorAlgebraGradedAlgebra`. -/
theorem existsUnique_unitalHom_tensorAlgebra :
    ∃! g : Stacks.GradedAlgebra.UnitalHom (tensorAlgebraGradedAlgebra F) D,
      ∀ (X : Cᵒᵖ) (m : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X
            (PresheafOfModules.Hom.app (tensorAlgebraGen F) X m) =
          PresheafOfModules.Hom.app lam X m := by
  refine ⟨tensorAlgebraDesc F D lam, tensorAlgebraDesc_gen F D lam, fun h hh => ?_⟩
  refine Stacks.GradedAlgebra.UnitalHom.ext fun n => ?_
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine D.incl_injective n X ?_
  rw [incl_unitalHom_tensorAlgebra_app F D lam h hh n X x]
  exact (incl_tensorAlgebraDescApp F D lam n X x).symm

end Tensor

end PresheafOfModules

namespace PresheafOfModules

/-! ### The exterior algebra -/

section Exterior

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- An element of the exterior algebra of the sections, read as a local section of the
homogeneous piece it lies in. -/
noncomputable def exteriorAlgebraPieceMk (n : ℤ) (X : Cᵒᵖ)
    (v : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
    (hv : v ∈ ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n) :
    (exteriorAlgebraPiece n F).obj X :=
  (⟨v, hv⟩ : ↥(ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n))

/-- Reading `exteriorAlgebraPieceMk` back in the exterior algebra of the sections returns the
element it was built from. -/
@[simp]
theorem exteriorAlgebraPieceVal_mk (n : ℤ) (X : Cᵒᵖ)
    (v : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
    (hv : v ∈ ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n) :
    exteriorAlgebraPieceVal n F X (exteriorAlgebraPieceMk F n X v hv) = v := rfl

variable {Q : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (D : Stacks.GradedAlgebra Q) (lam : F ⟶ Q 1)
  (hsq : ∀ (X : Cᵒᵖ) (m : F.obj X),
    (D.mul 1 1).app X (lam.app X m) (lam.app X m) = 0)

include hsq in
/-- The degree-one sections `lam` names square to zero in the ungraded realization. This is the
hypothesis `ExteriorAlgebra.liftRing` needs. -/
theorem genLin_mul_self (X : Cᵒᵖ) (m : F.obj X) :
    D.genLin lam X m * D.genLin lam X m = 0 := by
  rw [Stacks.GradedAlgebra.genLin_apply, D.incl_mul_incl, hsq X m, D.incl_zero]

/-- **The ring homomorphism out of the sectionwise exterior algebra.** -/
noncomputable def exteriorAlgebraTotalLift (X : Cᵒᵖ) :
    ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →+* D.Total X :=
  ExteriorAlgebra.liftRing (fun r x y => D.smul_mul_eq (X := X) r x y)
    (fun r x y => D.mul_smul_eq (X := X) r x y) (D.genLin lam X)
    (genLin_mul_self F D lam hsq X)

/-- The lift sends a degree-one generator to the degree-one section that `lam` names. -/
@[simp]
theorem exteriorAlgebraTotalLift_ι (X : Cᵒᵖ) (m : F.obj X) :
    exteriorAlgebraTotalLift F D lam hsq X (ExteriorAlgebra.ι _ m) = D.incl 1 (lam.app X m) :=
  ExteriorAlgebra.liftRing_ι m

/-- The lift is linear over the ring of sections. -/
theorem exteriorAlgebraTotalLift_smul (X : Cᵒᵖ) (r : (O ⋙ forget₂ _ RingCat).obj X)
    (x : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    exteriorAlgebraTotalLift F D lam hsq X (r • x) =
      r • exteriorAlgebraTotalLift F D lam hsq X x :=
  ExteriorAlgebra.liftRing_smul r x

/-- The lift sends a scalar to its image under the structure map of `D`. -/
theorem exteriorAlgebraTotalLift_algebraMap (X : Cᵒᵖ)
    (r : (O ⋙ forget₂ _ RingCat).obj X) :
    exteriorAlgebraTotalLift F D lam hsq X (algebraMap _ _ r) = D.structureMap X r := by
  rw [Algebra.algebraMap_eq_smul_one, exteriorAlgebraTotalLift_smul, map_one]
  rfl

/-- The lift sends a scalar `r` to the degree-zero section `r • 1`. -/
theorem exteriorAlgebraTotalLift_algebraMap_incl (X : Cᵒᵖ)
    (r : (O ⋙ forget₂ _ RingCat).obj X) :
    exteriorAlgebraTotalLift F D lam hsq X (algebraMap _ _ r) =
      D.incl 0 (r • D.one.eval X) := by
  rw [exteriorAlgebraTotalLift_algebraMap, D.incl_smul, ← D.one_eq_incl]
  rfl

/-- **The lift is concentrated in a single degree on each exterior power.** -/
theorem exists_incl_exteriorAlgebraTotalLift (X : Cᵒᵖ) (n : ℕ)
    {x : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)}
    (hx : x ∈ LinearMap.range (ExteriorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) :
      F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] _) ^ n) :
    ∃ y : (Q (n : ℤ)).obj X, exteriorAlgebraTotalLift F D lam hsq X x = D.incl (n : ℤ) y :=
  exists_incl_of_mem_pow_range F D lam X _ _
    (exteriorAlgebraTotalLift_algebraMap_incl F D lam hsq X)
    (exteriorAlgebraTotalLift_ι F D lam hsq X) n hx

/-- The lift commutes with restriction along a morphism of the site. -/
theorem exteriorAlgebraTotalLift_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    D.totalRestrict f (exteriorAlgebraTotalLift F D lam hsq X x) =
      exteriorAlgebraTotalLift F D lam hsq Y
        (ExteriorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x) := by
  have key : (D.totalRestrictRingHom f).comp (exteriorAlgebraTotalLift F D lam hsq X) =
      (exteriorAlgebraTotalLift F D lam hsq Y).comp
        (ExteriorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)) := by
    refine ExteriorAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · show D.totalRestrict f (exteriorAlgebraTotalLift F D lam hsq X (algebraMap _ _ r)) =
        exteriorAlgebraTotalLift F D lam hsq Y (ExteriorAlgebra.mapₛₗ _ (F.restrictₛₗ f)
          (algebraMap _ _ r))
      rw [exteriorAlgebraTotalLift_algebraMap, ExteriorAlgebra.mapₛₗ_algebraMap,
        exteriorAlgebraTotalLift_algebraMap, D.structureMap_naturality]
    · show D.totalRestrict f (exteriorAlgebraTotalLift F D lam hsq X (ExteriorAlgebra.ι _ m)) =
        exteriorAlgebraTotalLift F D lam hsq Y (ExteriorAlgebra.mapₛₗ _ (F.restrictₛₗ f)
          (ExteriorAlgebra.ι _ m))
      rw [exteriorAlgebraTotalLift_ι, ExteriorAlgebra.mapₛₗ_ι, exteriorAlgebraTotalLift_ι,
        D.totalRestrict_incl]
      refine congrArg (D.incl 1) ?_
      rw [Stacks.sectionRestrict_apply]
      exact (PresheafOfModules.naturality_apply lam f m).symm
  exact congrFun (congrArg (fun g : ExteriorAlgebra _ _ →+* D.Total Y => g.toFun) key) x

/-- The lift, read on a local section of an exterior power. -/
noncomputable def exteriorAlgebraDescLin (n : ℤ) (X : Cᵒᵖ) :
    (exteriorAlgebraPiece n F).obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] D.Total X where
  toFun x := exteriorAlgebraTotalLift F D lam hsq X (exteriorAlgebraPieceVal n F X x)
  map_add' _ _ := map_add (exteriorAlgebraTotalLift F D lam hsq X) _ _
  map_smul' r _ := exteriorAlgebraTotalLift_smul F D lam hsq X r _

/-- The degree-`n` component of the lift. -/
noncomputable def exteriorAlgebraDescAppLin (n : ℤ) (X : Cᵒᵖ) :
    (exteriorAlgebraPiece n F).obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] (Q n).obj X :=
  (D.proj X n).comp (exteriorAlgebraDescLin F D lam hsq n X)

/-- The degree-`n` component of the lift loses nothing: its ungraded image is the lift itself,
because the lift of a degree-`n` element is concentrated in degree `n`. -/
theorem incl_exteriorAlgebraDescAppLin (n : ℤ) (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece n F).obj X) :
    D.incl n (exteriorAlgebraDescAppLin F D lam hsq n X x) =
      exteriorAlgebraTotalLift F D lam hsq X (exteriorAlgebraPieceVal n F X x) :=
  incl_proj_of_exists_incl D X _ (fun n => exteriorAlgebraPieceVal n F X) (fun _ => rfl)
    (fun _ hn y => exteriorAlgebraPiece_eq_zero_of_neg hn F X y)
    (fun k y => exists_incl_exteriorAlgebraTotalLift F D lam hsq X k
      (y : ↥(ExteriorAlgebra.intPiece _ _ (k : ℤ))).2) n x

/-- The degree-`n` component of the lift commutes with restriction along a morphism of the site. -/
theorem exteriorAlgebraDescAppLin_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (exteriorAlgebraPiece n F).obj X) :
    Stacks.sectionRestrict (Q n) f (exteriorAlgebraDescAppLin F D lam hsq n X x) =
      exteriorAlgebraDescAppLin F D lam hsq n Y
        (Stacks.sectionRestrict (exteriorAlgebraPiece n F) f x) := by
  refine D.incl_injective n Y ?_
  rw [← D.totalRestrict_incl f n (exteriorAlgebraDescAppLin F D lam hsq n X x),
    incl_exteriorAlgebraDescAppLin, incl_exteriorAlgebraDescAppLin,
    exteriorAlgebraTotalLift_naturality]
  rfl

/-- The degreewise morphism out of the sectionwise exterior algebra determined by `lam`. -/
noncomputable def exteriorAlgebraDescApp (n : ℤ) : exteriorAlgebraPiece n F ⟶ Q n where
  app X := ModuleCat.ofHom (exteriorAlgebraDescAppLin F D lam hsq n X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (exteriorAlgebraDescAppLin_naturality F D lam hsq _ f x).symm)

/-- The ungraded image of `exteriorAlgebraDescApp` is the lift. -/
@[simp]
theorem incl_exteriorAlgebraDescApp (n : ℤ) (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece n F).obj X) :
    D.incl n (PresheafOfModules.Hom.app (exteriorAlgebraDescApp F D lam hsq n) X x) =
      exteriorAlgebraTotalLift F D lam hsq X (exteriorAlgebraPieceVal n F X x) :=
  incl_exteriorAlgebraDescAppLin F D lam hsq n X x

/-- **The unital homomorphism out of the sectionwise exterior algebra determined by a degree-one
morphism with square-zero image.** -/
noncomputable def exteriorAlgebraDesc :
    Stacks.GradedAlgebra.UnitalHom (exteriorAlgebraGradedAlgebra F) D where
  app := exteriorAlgebraDescApp F D lam hsq
  map_mul i j X x y := by
    refine D.incl_injective (i + j) X ?_
    rw [incl_exteriorAlgebraDescApp, ← D.incl_mul_incl, incl_exteriorAlgebraDescApp,
      incl_exteriorAlgebraDescApp, ← map_mul]
    rfl
  map_one X := by
    refine D.incl_injective 0 X ?_
    rw [incl_exteriorAlgebraDescApp, ← D.one_eq_incl]
    exact map_one _

/-- `exteriorAlgebraDesc` carries the degree-one generator to `lam`. -/
theorem exteriorAlgebraDesc_gen (X : Cᵒᵖ) (m : F.obj X) :
    PresheafOfModules.Hom.app ((exteriorAlgebraDesc F D lam hsq).app 1) X
        (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X m) =
      PresheafOfModules.Hom.app lam X m := by
  refine D.incl_injective 1 X ?_
  show D.incl 1 (PresheafOfModules.Hom.app (exteriorAlgebraDescApp F D lam hsq 1) X _) = _
  rw [incl_exteriorAlgebraDescApp, exteriorAlgebraPieceVal_gen, exteriorAlgebraTotalLift_ι]

variable (g : Stacks.GradedAlgebra.UnitalHom (exteriorAlgebraGradedAlgebra F) D)

/-- A degree-zero local section of the sectionwise exterior algebra is a scalar multiple of the
unit, so a unital homomorphism has no freedom there. -/
theorem incl_unitalHom_exteriorAlgebra_app_zero (X : Cᵒᵖ)
    (y : (exteriorAlgebraPiece (0 : ℤ) F).obj X) :
    D.incl 0 (PresheafOfModules.Hom.app (g.app 0) X y) =
      exteriorAlgebraTotalLift F D lam hsq X (exteriorAlgebraPieceVal 0 F X y) :=
  incl_unitalHom_app_zero_of_pow_range F D X _ _ g (exteriorAlgebraPieceVal 0 F X)
    (exteriorAlgebraPieceVal_injective _ F X)
    (fun y => (y : ↥(ExteriorAlgebra.intPiece _ _ 0)).2)
    (fun r => by
      change r • exteriorAlgebraPieceVal 0 F X ((exteriorAlgebraOne F).eval X) = _
      rw [exteriorAlgebraPieceVal_one, Algebra.algebraMap_eq_smul_one])
    (exteriorAlgebraTotalLift_algebraMap_incl F D lam hsq X) y

/-- The inductive step of the uniqueness argument for the exterior algebra, at a free integer
degree so that no transport along the cast of `n + 1` appears. -/
theorem incl_unitalHom_exteriorAlgebra_app_mul_gen
    (hg : ∀ (X : Cᵒᵖ) (m : F.obj X),
      PresheafOfModules.Hom.app (g.app 1) X
          (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X m) =
        PresheafOfModules.Hom.app lam X m)
    (i : ℤ) (X : Cᵒᵖ) (y : (exteriorAlgebraPiece i F).obj X) (m₀ : F.obj X)
    (h : D.incl i (PresheafOfModules.Hom.app (g.app i) X y) =
      exteriorAlgebraTotalLift F D lam hsq X (exteriorAlgebraPieceVal i F X y)) :
    D.incl (i + 1) (PresheafOfModules.Hom.app (g.app (i + 1)) X
        (((exteriorAlgebraGradedAlgebra F).mul i 1).app X y
          (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X m₀))) =
      exteriorAlgebraTotalLift F D lam hsq X
        (exteriorAlgebraPieceVal i F X y * ExteriorAlgebra.ι _ m₀) := by
  rw [g.map_mul i 1 X y (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X m₀),
    ← D.incl_mul_incl, h, hg X m₀, ← exteriorAlgebraTotalLift_ι F D lam hsq X m₀, ← map_mul]

/-- **A unital homomorphism out of the sectionwise exterior algebra is determined by its
degree-one component**, because the ungraded image of a local section of a homogeneous piece is
forced by the lift. -/
theorem incl_unitalHom_exteriorAlgebra_app
    (hg : ∀ (X : Cᵒᵖ) (m : F.obj X),
      PresheafOfModules.Hom.app (g.app 1) X
          (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X m) =
        PresheafOfModules.Hom.app lam X m)
    (n : ℤ) (X : Cᵒᵖ) (x : (exteriorAlgebraPiece n F).obj X) :
    D.incl n (PresheafOfModules.Hom.app (g.app n) X x) =
      exteriorAlgebraTotalLift F D lam hsq X (exteriorAlgebraPieceVal n F X x) :=
  incl_unitalHom_app_of_pow_range F D X _ _ (exteriorAlgebraGen F) g
    (fun n => exteriorAlgebraPieceVal n F X) (fun n => exteriorAlgebraPieceVal_injective n F X)
    (fun k v => ⟨fun hv => ⟨exteriorAlgebraPieceMk F k X v hv, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ (y : ↥(ExteriorAlgebra.intPiece _ _ (k : ℤ))).2⟩)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)
    (fun _ hn y => exteriorAlgebraPiece_eq_zero_of_neg hn F X y)
    (incl_unitalHom_exteriorAlgebra_app_zero F D lam hsq g X)
    (fun i y m h => incl_unitalHom_exteriorAlgebra_app_mul_gen F D lam hsq g hg i X y m h) n x

include hsq in
/-- **The universal property of the sectionwise exterior algebra.** A degree-one morphism of
presheaves of modules whose image squares to zero extends to a unique unital homomorphism out of
the sectionwise exterior algebra.

This is the second hypothesis of `Stacks.GradedAlgebra.isExteriorAlgebra_sheafify`, hence the
`exterior_isExteriorAlgebra` field of `SheafOfModules.TensorExteriorSymmetricAlgebras` for the
sheafification of `exteriorAlgebraGradedAlgebra`. -/
theorem existsUnique_unitalHom_exteriorAlgebra :
    ∃! g : Stacks.GradedAlgebra.UnitalHom (exteriorAlgebraGradedAlgebra F) D,
      ∀ (X : Cᵒᵖ) (m : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X
            (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X m) =
          PresheafOfModules.Hom.app lam X m := by
  refine ⟨exteriorAlgebraDesc F D lam hsq, exteriorAlgebraDesc_gen F D lam hsq, fun h hh => ?_⟩
  refine Stacks.GradedAlgebra.UnitalHom.ext fun n => ?_
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine D.incl_injective n X ?_
  rw [incl_unitalHom_exteriorAlgebra_app F D lam hsq h hh n X x]
  exact (incl_exteriorAlgebraDescApp F D lam hsq n X x).symm

end Exterior

end PresheafOfModules

namespace PresheafOfModules

/-! ### The symmetric algebra -/

section Symmetric

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- An element of the symmetric algebra of the sections, read as a local section of the
homogeneous piece it lies in. -/
noncomputable def symmetricAlgebraPieceMk (n : ℤ) (X : Cᵒᵖ)
    (v : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
    (hv : v ∈ SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    (symPowInt n F).obj X :=
  (⟨v, hv⟩ : ↥(SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)))

/-- Reading `symmetricAlgebraPieceMk` back in the symmetric algebra of the sections returns the
element it was built from. -/
@[simp]
theorem symPowIntVal_mk (n : ℤ) (X : Cᵒᵖ)
    (v : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
    (hv : v ∈ SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    symPowIntVal (symmetricAlgebraPieceMk F n X v hv) = v := rfl

variable {Q : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (D : Stacks.GradedAlgebra Q) (lam : F ⟶ Q 1) (hcomm : D.GenCommutes lam)

/-- **The ring homomorphism out of the sectionwise symmetric algebra.** -/
noncomputable def symmetricAlgebraTotalLift (X : Cᵒᵖ) :
    SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →+* D.Total X :=
  SymmetricAlgebra.liftComm (fun r x y => D.smul_mul_eq (X := X) r x y)
    (fun r x y => D.mul_smul_eq (X := X) r x y) (D.genLin lam X)
    (D.genLin_mul_comm lam hcomm X)

/-- The lift sends a degree-one generator to the degree-one section that `lam` names. -/
@[simp]
theorem symmetricAlgebraTotalLift_ι (X : Cᵒᵖ) (m : F.obj X) :
    symmetricAlgebraTotalLift F D lam hcomm X (SymmetricAlgebra.ι _ _ m) =
      D.incl 1 (lam.app X m) :=
  SymmetricAlgebra.liftComm_ι m

/-- The lift is linear over the ring of sections. -/
theorem symmetricAlgebraTotalLift_smul (X : Cᵒᵖ) (r : (O ⋙ forget₂ _ RingCat).obj X)
    (x : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    symmetricAlgebraTotalLift F D lam hcomm X (r • x) =
      r • symmetricAlgebraTotalLift F D lam hcomm X x :=
  SymmetricAlgebra.liftComm_smul r x

/-- The lift sends a scalar to its image under the structure map of `D`. -/
theorem symmetricAlgebraTotalLift_algebraMap (X : Cᵒᵖ)
    (r : (O ⋙ forget₂ _ RingCat).obj X) :
    symmetricAlgebraTotalLift F D lam hcomm X (algebraMap _ _ r) = D.structureMap X r := by
  rw [Algebra.algebraMap_eq_smul_one, symmetricAlgebraTotalLift_smul, map_one]
  rfl

/-- The lift sends a scalar `r` to the degree-zero section `r • 1`. -/
theorem symmetricAlgebraTotalLift_algebraMap_incl (X : Cᵒᵖ)
    (r : (O ⋙ forget₂ _ RingCat).obj X) :
    symmetricAlgebraTotalLift F D lam hcomm X (algebraMap _ _ r) =
      D.incl 0 (r • D.one.eval X) := by
  rw [symmetricAlgebraTotalLift_algebraMap, D.incl_smul, ← D.one_eq_incl]
  rfl

/-- **The lift is concentrated in a single degree on each symmetric power.** -/
theorem exists_incl_symmetricAlgebraTotalLift (X : Cᵒᵖ) (n : ℕ)
    {x : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)}
    (hx : x ∈ LinearMap.range (SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X)
      (F.obj X)) ^ n) :
    ∃ y : (Q (n : ℤ)).obj X,
      symmetricAlgebraTotalLift F D lam hcomm X x = D.incl (n : ℤ) y :=
  exists_incl_of_mem_pow_range F D lam X _ _
    (symmetricAlgebraTotalLift_algebraMap_incl F D lam hcomm X)
    (symmetricAlgebraTotalLift_ι F D lam hcomm X) n hx

/-- The lift commutes with restriction along a morphism of the site. -/
theorem symmetricAlgebraTotalLift_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    D.totalRestrict f (symmetricAlgebraTotalLift F D lam hcomm X x) =
      symmetricAlgebraTotalLift F D lam hcomm Y
        (SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x) := by
  have key : (D.totalRestrictRingHom f).comp (symmetricAlgebraTotalLift F D lam hcomm X) =
      (symmetricAlgebraTotalLift F D lam hcomm Y).comp
        (SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)) := by
    refine SymmetricAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · show D.totalRestrict f (symmetricAlgebraTotalLift F D lam hcomm X (algebraMap _ _ r)) =
        symmetricAlgebraTotalLift F D lam hcomm Y (SymmetricAlgebra.mapₛₗ _ (F.restrictₛₗ f)
          (algebraMap _ _ r))
      rw [symmetricAlgebraTotalLift_algebraMap, SymmetricAlgebra.mapₛₗ_algebraMap,
        symmetricAlgebraTotalLift_algebraMap, D.structureMap_naturality]
    · show D.totalRestrict f
          (symmetricAlgebraTotalLift F D lam hcomm X (SymmetricAlgebra.ι _ _ m)) =
        symmetricAlgebraTotalLift F D lam hcomm Y (SymmetricAlgebra.mapₛₗ _ (F.restrictₛₗ f)
          (SymmetricAlgebra.ι _ _ m))
      rw [symmetricAlgebraTotalLift_ι, SymmetricAlgebra.mapₛₗ_ι,
        symmetricAlgebraTotalLift_ι, D.totalRestrict_incl]
      refine congrArg (D.incl 1) ?_
      rw [Stacks.sectionRestrict_apply]
      exact (PresheafOfModules.naturality_apply lam f m).symm
  exact congrFun (congrArg (fun g : SymmetricAlgebra _ _ →+* D.Total Y => g.toFun) key) x

/-- The lift, read on a local section of a symmetric power. -/
noncomputable def symmetricAlgebraDescLin (n : ℤ) (X : Cᵒᵖ) :
    (symPowInt n F).obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] D.Total X where
  toFun x := symmetricAlgebraTotalLift F D lam hcomm X (symPowIntVal x)
  map_add' _ _ := map_add (symmetricAlgebraTotalLift F D lam hcomm X) _ _
  map_smul' r _ := symmetricAlgebraTotalLift_smul F D lam hcomm X r _

/-- The degree-`n` component of the lift. -/
noncomputable def symmetricAlgebraDescAppLin (n : ℤ) (X : Cᵒᵖ) :
    (symPowInt n F).obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] (Q n).obj X :=
  (D.proj X n).comp (symmetricAlgebraDescLin F D lam hcomm n X)

/-- The degree-`n` component of the lift loses nothing: its ungraded image is the lift itself,
because the lift of a degree-`n` element is concentrated in degree `n`. -/
theorem incl_symmetricAlgebraDescAppLin (n : ℤ) (X : Cᵒᵖ)
    (x : (symPowInt n F).obj X) :
    D.incl n (symmetricAlgebraDescAppLin F D lam hcomm n X x) =
      symmetricAlgebraTotalLift F D lam hcomm X (symPowIntVal x) :=
  incl_proj_of_exists_incl D X _ (fun _ y => symPowIntVal y) (fun _ => rfl)
    (fun n hn y => symPowInt_eq_zero_of_neg n F hn X y)
    (fun k y => exists_incl_symmetricAlgebraTotalLift F D lam hcomm X k
      (y : ↥(SymPow.symmetricPowerInt (k : ℤ) _ _)).2) n x

/-- The degree-`n` component of the lift commutes with restriction along a morphism of the site. -/
theorem symmetricAlgebraDescAppLin_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (symPowInt n F).obj X) :
    Stacks.sectionRestrict (Q n) f (symmetricAlgebraDescAppLin F D lam hcomm n X x) =
      symmetricAlgebraDescAppLin F D lam hcomm n Y
        (Stacks.sectionRestrict (symPowInt n F) f x) := by
  refine D.incl_injective n Y ?_
  rw [← D.totalRestrict_incl f n (symmetricAlgebraDescAppLin F D lam hcomm n X x),
    incl_symmetricAlgebraDescAppLin, incl_symmetricAlgebraDescAppLin,
    symmetricAlgebraTotalLift_naturality]
  rfl

/-- The degreewise morphism out of the sectionwise symmetric algebra determined by `lam`. -/
noncomputable def symmetricAlgebraDescApp (n : ℤ) : symPowInt n F ⟶ Q n where
  app X := ModuleCat.ofHom (symmetricAlgebraDescAppLin F D lam hcomm n X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (symmetricAlgebraDescAppLin_naturality F D lam hcomm _ f x).symm)

/-- The ungraded image of `symmetricAlgebraDescApp` is the lift. -/
@[simp]
theorem incl_symmetricAlgebraDescApp (n : ℤ) (X : Cᵒᵖ)
    (x : (symPowInt n F).obj X) :
    D.incl n (PresheafOfModules.Hom.app (symmetricAlgebraDescApp F D lam hcomm n) X x) =
      symmetricAlgebraTotalLift F D lam hcomm X (symPowIntVal x) :=
  incl_symmetricAlgebraDescAppLin F D lam hcomm n X x

/-- **The unital homomorphism out of the sectionwise symmetric algebra determined by a degree-one
morphism with pairwise commuting image.** -/
noncomputable def symmetricAlgebraDesc :
    Stacks.GradedAlgebra.UnitalHom (symPowIntGradedAlgebra F) D where
  app := symmetricAlgebraDescApp F D lam hcomm
  map_mul i j X x y := by
    refine D.incl_injective (i + j) X ?_
    rw [incl_symmetricAlgebraDescApp, ← D.incl_mul_incl, incl_symmetricAlgebraDescApp,
      incl_symmetricAlgebraDescApp, ← map_mul]
    rfl
  map_one X := by
    refine D.incl_injective 0 X ?_
    rw [incl_symmetricAlgebraDescApp, ← D.one_eq_incl]
    exact map_one _

/-- `symmetricAlgebraDesc` carries the degree-one generator to `lam`. -/
theorem symmetricAlgebraDesc_gen (X : Cᵒᵖ) (m : F.obj X) :
    PresheafOfModules.Hom.app ((symmetricAlgebraDesc F D lam hcomm).app 1) X
        (PresheafOfModules.Hom.app (symPowIntGen F) X m) =
      PresheafOfModules.Hom.app lam X m := by
  refine D.incl_injective 1 X ?_
  show D.incl 1
    (PresheafOfModules.Hom.app (symmetricAlgebraDescApp F D lam hcomm 1) X _) = _
  rw [incl_symmetricAlgebraDescApp, symPowIntVal_gen,
    symmetricAlgebraTotalLift_ι]

variable (g : Stacks.GradedAlgebra.UnitalHom (symPowIntGradedAlgebra F) D)

/-- A degree-zero local section of the sectionwise symmetric algebra is a scalar multiple of the
unit, so a unital homomorphism has no freedom there. -/
theorem incl_unitalHom_symmetricAlgebra_app_zero (X : Cᵒᵖ)
    (y : (symPowInt (0 : ℤ) F).obj X) :
    D.incl 0 (PresheafOfModules.Hom.app (g.app 0) X y) =
      symmetricAlgebraTotalLift F D lam hcomm X (symPowIntVal y) :=
  incl_unitalHom_app_zero_of_pow_range F D X _ _ g symPowIntVal
    (fun _ _ h => symPowIntVal_injective _ F h)
    (fun y => (y : ↥(SymPow.symmetricPowerInt 0 _ _)).2)
    (fun r => by
      change r • symPowIntVal ((symPowIntOne F).eval X) = _
      rw [symPowIntVal_one, Algebra.algebraMap_eq_smul_one])
    (symmetricAlgebraTotalLift_algebraMap_incl F D lam hcomm X) y

/-- The inductive step of the uniqueness argument for the symmetric algebra, at a free integer
degree so that no transport along the cast of `n + 1` appears. -/
theorem incl_unitalHom_symmetricAlgebra_app_mul_gen
    (hg : ∀ (X : Cᵒᵖ) (m : F.obj X),
      PresheafOfModules.Hom.app (g.app 1) X
          (PresheafOfModules.Hom.app (symPowIntGen F) X m) =
        PresheafOfModules.Hom.app lam X m)
    (i : ℤ) (X : Cᵒᵖ) (y : (symPowInt i F).obj X) (m₀ : F.obj X)
    (h : D.incl i (PresheafOfModules.Hom.app (g.app i) X y) =
      symmetricAlgebraTotalLift F D lam hcomm X (symPowIntVal y)) :
    D.incl (i + 1) (PresheafOfModules.Hom.app (g.app (i + 1)) X
        (((symPowIntGradedAlgebra F).mul i 1).app X y
          (PresheafOfModules.Hom.app (symPowIntGen F) X m₀))) =
      symmetricAlgebraTotalLift F D lam hcomm X
        (symPowIntVal y * SymmetricAlgebra.ι _ _ m₀) := by
  rw [g.map_mul i 1 X y (PresheafOfModules.Hom.app (symPowIntGen F) X m₀),
    ← D.incl_mul_incl, h, hg X m₀, ← symmetricAlgebraTotalLift_ι F D lam hcomm X m₀, ← map_mul]

/-- **A unital homomorphism out of the sectionwise symmetric algebra is determined by its
degree-one component**, because the ungraded image of a local section of a homogeneous piece is
forced by the lift. -/
theorem incl_unitalHom_symmetricAlgebra_app
    (hg : ∀ (X : Cᵒᵖ) (m : F.obj X),
      PresheafOfModules.Hom.app (g.app 1) X
          (PresheafOfModules.Hom.app (symPowIntGen F) X m) =
        PresheafOfModules.Hom.app lam X m)
    (n : ℤ) (X : Cᵒᵖ) (x : (symPowInt n F).obj X) :
    D.incl n (PresheafOfModules.Hom.app (g.app n) X x) =
      symmetricAlgebraTotalLift F D lam hcomm X (symPowIntVal x) :=
  incl_unitalHom_app_of_pow_range F D X _ _ (symPowIntGen F) g (fun _ y => symPowIntVal y)
    (fun n _ _ h => symPowIntVal_injective n F h)
    (fun k v => ⟨fun hv => ⟨symmetricAlgebraPieceMk F k X v hv, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ (y : ↥(SymPow.symmetricPowerInt (k : ℤ) _ _)).2⟩)
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)
    (fun n hn y => symPowInt_eq_zero_of_neg n F hn X y)
    (incl_unitalHom_symmetricAlgebra_app_zero F D lam hcomm g X)
    (fun i y m h => incl_unitalHom_symmetricAlgebra_app_mul_gen F D lam hcomm g hg i X y m h) n x

include hcomm in
/-- **The universal property of the sectionwise symmetric algebra.** A degree-one morphism of
presheaves of modules whose image commutes pairwise extends to a unique unital homomorphism out
of the sectionwise symmetric algebra.

This is the second hypothesis of `Stacks.GradedAlgebra.isSymmetricAlgebra_sheafify`, hence the
`symmetric_isSymmetricAlgebra` field of `SheafOfModules.TensorExteriorSymmetricAlgebras` for the
sheafification of `symPowIntGradedAlgebra`. -/
theorem existsUnique_unitalHom_symmetricAlgebra :
    ∃! g : Stacks.GradedAlgebra.UnitalHom (symPowIntGradedAlgebra F) D,
      ∀ (X : Cᵒᵖ) (m : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X
            (PresheafOfModules.Hom.app (symPowIntGen F) X m) =
          PresheafOfModules.Hom.app lam X m := by
  refine ⟨symmetricAlgebraDesc F D lam hcomm, symmetricAlgebraDesc_gen F D lam hcomm,
    fun h hh => ?_⟩
  refine Stacks.GradedAlgebra.UnitalHom.ext fun n => ?_
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine D.incl_injective n X ?_
  rw [incl_unitalHom_symmetricAlgebra_app F D lam hcomm h hh n X x]
  exact (incl_symmetricAlgebraDescApp F D lam hcomm n X x).symm

end Symmetric

end PresheafOfModules

namespace PresheafOfModules

/-! ### The three universal properties of the sheafified sectionwise algebras -/

section Sheafify

open Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {R : Sheaf J RingCat.{w}}
  (α : (O ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  [HasWeakSheafify J AddCommGrpCat.{max w a}]
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- The degree-one morphism into the restriction of scalars of a sheaf of graded algebras that a
degree-one generator of the sheafification determines. -/
noncomputable def restrictGen {B : SheafOfModules.GradedAlgebra.{w, max w a} R}
    (κ : (sheafification α).obj F ⟶ B.piece 1) :
    F ⟶ (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).obj (B.piece 1) :=
  sheafifyUnit α F ≫ (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).map κ

/-- `restrictGen` on a local section: the sheafification unit followed by `κ`. -/
theorem restrictGen_app {B : SheafOfModules.GradedAlgebra.{w, max w a} R}
    (κ : (sheafification α).obj F ⟶ B.piece 1) (X : Cᵒᵖ) (s : F.obj X) :
    PresheafOfModules.Hom.app (restrictGen α F κ) X s =
      κ.val.app X (PresheafOfModules.Hom.app (sheafifyUnit α F) X s) := rfl

/-- **The sheafification of the sectionwise tensor algebra is the tensor algebra of the
sheafification.** This is the `tensor_isTensorAlgebra` field of
`SheafOfModules.TensorExteriorSymmetricAlgebras`. -/
theorem isTensorAlgebra_sheafify_tensorAlgebra :
    SheafOfModules.GradedAlgebra.IsTensorAlgebra
      ((tensorAlgebraGradedAlgebra F).sheafify α)
      ((tensorAlgebraGradedAlgebra F).sheafifyGen α (tensorAlgebraGen F)) :=
  (tensorAlgebraGradedAlgebra F).isTensorAlgebra_sheafify α (tensorAlgebraGen F)
    fun B κ => existsUnique_unitalHom_tensorAlgebra F (B.restrictScalars α)
      (restrictGen α F κ)

/-- **The sheafification of the sectionwise exterior algebra is the exterior algebra of the
sheafification.** This is the `exterior_isExteriorAlgebra` field of
`SheafOfModules.TensorExteriorSymmetricAlgebras`. -/
theorem isExteriorAlgebra_sheafify_exteriorAlgebra :
    SheafOfModules.GradedAlgebra.IsExteriorAlgebra
      ((exteriorAlgebraGradedAlgebra F).sheafify α)
      ((exteriorAlgebraGradedAlgebra F).sheafifyGen α (exteriorAlgebraGen F)) :=
  (exteriorAlgebraGradedAlgebra F).isExteriorAlgebra_sheafify α (exteriorAlgebraGen F)
    (exteriorAlgebraGen_squareZero F)
    fun B κ hκ => existsUnique_unitalHom_exteriorAlgebra F (B.restrictScalars α)
      (restrictGen α F κ) fun X _ => hκ X _

/-- **The sheafification of the sectionwise symmetric algebra is the symmetric algebra of the
sheafification.** This is the `symmetric_isSymmetricAlgebra` field of
`SheafOfModules.TensorExteriorSymmetricAlgebras`. -/
theorem isSymmetricAlgebra_sheafify_symmetricAlgebra :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra
      ((symPowIntGradedAlgebra F).sheafify α)
      ((symPowIntGradedAlgebra F).sheafifyGen α (symPowIntGen F)) :=
  by
  refine (symPowIntGradedAlgebra F).isSymmetricAlgebra_sheafify α
    (symPowIntGen F) ?_ ?_
  · exact symPowIntGradedAlgebra_genCommutes F
  · exact fun B κ hκ => existsUnique_unitalHom_symmetricAlgebra F (B.restrictScalars α)
      (restrictGen α F κ) fun X _ _ => hκ X _ _

end Sheafify

end PresheafOfModules
