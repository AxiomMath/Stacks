module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraOnBasis
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplitting
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxPresentation
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.Basic

/-!
# The polynomial cover of the associated graded algebra of `I · 𝒪_X`

Let `A` be a commutative ring, `I` an ideal of `A`, `X` a scheme over `Spec A` along
`f : X ⟶ Spec A`, and let `ℐ = I · 𝒪_X` be the extension of `I` to `X`. Let `D` present the
associated graded algebra `𝓑 = ⨁ ℐ ⁿ / ℐ ⁿ⁺¹`, so that over an affine open `U` the degree-`n`
piece of `D.algebra` is identified, `Γ(X, U)`-linearly, with `J ⁿ / J ⁿ⁺¹` for `J = ℐ(U)`.

Choose a family `a : ι → A` spanning `I`. Each `a i` gives a degree-one section of `𝓑` over
every affine open, namely the class of its image in `J / J ²`, and these assemble into a
morphism `𝒪_X ⟶ 𝓑₁`. The resulting morphism out of the free module `𝒪_X ^ ι` extends, by the
universal property of the symmetric algebra, to a unital homomorphism of sheaves of graded
algebras `𝓟 = 𝒪_X[x_i] ⟶ 𝓑`, and that homomorphism is surjective on the sections over every
affine open: `J ⁿ` is generated over `Γ(X, U)` by the images of the degree-`n` monomials in the
`a i`, and each such image is the value of the homomorphism on the corresponding monomial.

Surjectivity on affine sections is the hypothesis `hφ` of
`Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_epi_over`, and is stated here in
exactly that shape.

## Main definitions

* `Stacks.Coherent.pieceClass`: the section of the degree-`n` piece of `D.algebra` over an
  affine open attached to an element of `ℐ ⁿ`.
* `Stacks.Coherent.genSectionHom` and `Stacks.Coherent.genHom`: the degree-one generator
  `𝒪_X ⟶ 𝓑₁` attached to `a i`, built from its values on the sections over affine opens.
* `Stacks.Coherent.genFree`: the induced morphism `𝒪_X ^ ι ⟶ 𝓑₁` out of the free module.
* `Stacks.Coherent.polyAlgebra`: the polynomial algebra `𝒪_X[x_i]`, the symmetric algebra of
  the free module on `ι`.
* `Stacks.Coherent.polyHom`: the unital homomorphism `𝓟 ⟶ 𝓑` extending `genFree`.
* `Stacks.Coherent.IsPolyImage`: the property of a section of a homogeneous piece of `𝓑` over
  an affine open of being in the image of `polyHom`.

## Main results

* `Stacks.Coherent.algebra_mul_comm`: the associated graded algebra of an ideal is commutative
  on the sections over an affine open, whence `Stacks.Coherent.pairwiseCommutes_genFree`, the
  hypothesis of the universal property of the symmetric algebra.
* `Stacks.Coherent.algebraPiece_one`: over an affine open the algebra unit is the class of `1`.
* `Stacks.Coherent.surjective_polyHom_app`: **the polynomial algebra covers the associated
  graded algebra on the sections over every affine open, in every degree.** This is the
  hypothesis `hφ` of
  `Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_epi_over`.

## Implementation notes

**Why the generator is built on a basis.** The formula for the degree-one generator only makes
sense over an affine open, where `D.algebraPiece` identifies the sections of `𝓑₁` with
`J / J ²`. The affine opens form a basis of `X`, so
`Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis` turns the family of these formulas
into an honest morphism of sheaves of modules; the compatibility it requires is
`D.algebraPiece_naturality` together with `D.algebraRestriction_mk` and
`Stacks.Coherent.baseSectionHom_restrict`, the functoriality of the base sections. The same
basis is used again for commutativity: `Stacks.Coherent.pairwiseCommutes_genFree` is an
identity between two sections of `𝓑₂` over an *arbitrary* open while the hypothesis is
available only over affine ones, so it is the separatedness statement
`Stacks.BasisRestriction.moduleSheafSection_ext_onBasis` applied after pushing both sides down
to a chart, where the restriction maps pass through the multiplication by bilinearity.

**Where the spanning hypothesis is spent.** `Ideal.span (Set.range a) = I` enters exactly twice:
once to know that each `a i` has a class in `J / J ²`, and once in
`Stacks.Coherent.isPolyImage_pieceClass_one`, a span induction showing that every element of `I`
has its class covered. Noetherianity of `A` is never used — the family and the spanning equation
are hypotheses, not conclusions.

**The shape of the surjectivity argument.** The negative degrees are handled by
`D.algebraNegative`: the target is a zero object, so the zero section works. In degree `n ≥ 0`
the target is `J ⁿ / J ⁿ⁺¹`, every class is `AssociatedGraded.mk` of an element of
`J ⁿ = Ideal.map (baseSectionHom A f U) (I ⁿ)`, and a span induction reduces to the classes of
the images of elements of `I ⁿ`. Those are covered by induction on `n`: the degree-zero case is
`Stacks.Coherent.algebraPiece_one` together with the unitality of the homomorphism, and the
inductive step writes an element of `I ⁿ⁺¹ = I ⁿ · I` as a sum of products and uses the
multiplicativity of the homomorphism together with `D.algebraMul`, which identifies the graded
product with `AssociatedGraded.homogeneousSMul`.

**Membership proofs are carried explicitly.** `Stacks.Coherent.pieceClass` takes the proof that
its argument lies in `ℐ ⁿ`, so rewriting its argument needs
`Stacks.Coherent.pieceClass_congr`; the proofs themselves are irrelevant, which is why that
lemma asks for no compatibility between them. The inductions over products carry the membership
inside an existential, because `Submodule.mul_induction_on` supplies no membership in its
additivity clause.

No Stacks attribute is attached: the construction is an input to part (2) of
[Stacks, Tag 0897], not a statement of a tag.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Cohomology.FormalFunctions

universe u

namespace Stacks.Coherent

attribute [local instance_reducible] TopCat.Sheaf
attribute [local implicit_reducible] TopCat.Sheaf PresheafOfModules.presheaf
  SheafOfModules.toSheaf ModuleCat.restrictScalars

/-! ### Restriction of the base sections, and the polynomial algebra -/

/-- **The base sections are compatible with restriction.** The ring map `A ⟶ Γ(X, U)` is the
global one followed by restriction to `U`, so restricting further to `V ≤ U` gives the ring map
of `V`; this is the functoriality of the structure presheaf. -/
public lemma baseSectionHom_restrict (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) {U V : X.Opens} (h : V ≤ U) (g : A) :
    X.presheaf.map (homOfLE h).op (baseSectionHom A f U g) = baseSectionHom A f V g := by
  show (X.presheaf.map (homOfLE (le_top (a := U))).op ≫ X.presheaf.map (homOfLE h).op)
    (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom g) = _
  rw [← Functor.map_comp]
  rfl

/-- The polynomial algebra `𝒪_Y[x_k]` on a family of generators indexed by `κ`: the symmetric
algebra of the free sheaf of modules on `κ`. -/
public abbrev polyAlgebra (Y : Scheme.{u}) (κ : Type u) :
    SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf :=
  SheafOfModules.sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y)
    (SheafOfModules.free (R := Y.ringCatSheaf) κ)

/-! ### Classes of sections of the ideal -/

variable {X : Scheme.{u}} (A : Type u) [CommRing A] (I : Ideal A) (f : X ⟶ Spec (.of A))
  (D : AssociatedGradedAlgebraData (baseIdealSheaf A I f))

/-- The image of an element of `I ⁿ` lies in `ℐ ⁿ` over every affine open: over an affine open
`ℐ ⁿ` is the ideal generated by the image of `I ⁿ`. -/
public lemma baseSectionHom_mem_power (U : X.affineOpens) (n : ℕ) (g : A) (hg : g ∈ I ^ n) :
    baseSectionHom A f U.1 g ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n := by
  rw [AssociatedGraded.ring_power_eq, baseIdealSheaf_ideal_pow_eq_map]
  exact Ideal.mem_map_of_mem _ hg

/-- The section of the degree-`n` piece of the associated graded algebra over an affine open
attached to an element of `ℐ ⁿ`: its class in `ℐ ⁿ / ℐ ⁿ⁺¹`, read back through
`D.algebraPiece`. -/
public def pieceClass (U : X.affineOpens) (n : ℕ) (x : Γ(X, U.1))
    (hx : x ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n) :
    (D.algebra.piece (n : ℤ)).val.obj (op U.1) :=
  (D.algebraPiece n U).symm (AssociatedGraded.mk _ n ⟨x, hx⟩)

/-- The affine identification carries `pieceClass` back to the class it was built from. -/
public lemma algebraPiece_pieceClass (U : X.affineOpens) (n : ℕ) (x : Γ(X, U.1))
    (hx : x ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n) :
    D.algebraPiece n U (pieceClass A I f D U n x hx) =
      AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) n ⟨x, hx⟩ :=
  (D.algebraPiece n U).apply_symm_apply _

/-- The class attached to an element of `ℐ ⁿ` depends only on the element: the membership proof
is irrelevant, so an equality of elements transports the class. -/
public lemma pieceClass_congr (U : X.affineOpens) (n : ℕ) (x y : Γ(X, U.1))
    (hx : x ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n)
    (hy : y ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n)
    (hxy : x = y) :
    pieceClass A I f D U n x hx = pieceClass A I f D U n y hy := by
  subst hxy
  rfl

/-- The inverse of the affine identification is linear over the sections of the structure
sheaf, the identification itself being so by `D.algebraPiece_smul`. -/
public lemma algebraPiece_symm_smul (U : X.affineOpens) (n : ℕ)
    (r : X.ringCatSheaf.obj.obj (op U.1))
    (z : AssociatedGraded.piece (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n) :
    (D.algebraPiece n U).symm (Stacks.Blowup.ringSectionToGamma r • z) =
      r • (D.algebraPiece n U).symm z := by
  apply (D.algebraPiece n U).injective
  rw [AddEquiv.apply_symm_apply,
    D.algebraPiece_smul n U r ((D.algebraPiece n U).symm z), AddEquiv.apply_symm_apply]
  rfl

/-- The class of `0` is `0`. -/
public lemma pieceClass_zero (U : X.affineOpens) (n : ℕ)
    (h : (0 : Γ(X, U.1)) ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n) :
    pieceClass A I f D U n 0 h = 0 :=
  map_zero (D.algebraPiece n U).symm

/-- The class of a sum is the sum of the classes. -/
public lemma pieceClass_add (U : X.affineOpens) (n : ℕ) (x y : Γ(X, U.1))
    (hx : x ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n)
    (hy : y ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n)
    (hxy : x + y ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n) :
    pieceClass A I f D U n (x + y) hxy =
      pieceClass A I f D U n x hx + pieceClass A I f D U n y hy :=
  map_add (D.algebraPiece n U).symm (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) n ⟨x, hx⟩)
    (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) n ⟨y, hy⟩)

/-- The class of a multiple is the multiple of the class. -/
public lemma pieceClass_smul (U : X.affineOpens) (n : ℕ)
    (c : X.ringCatSheaf.obj.obj (op U.1)) (x : Γ(X, U.1))
    (hx : x ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n)
    (hcx : Stacks.Blowup.ringSectionToGamma c * x ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n) :
    pieceClass A I f D U n (Stacks.Blowup.ringSectionToGamma c * x) hcx =
      c • pieceClass A I f D U n x hx :=
  algebraPiece_symm_smul A I f D U n c (AssociatedGraded.mk _ n ⟨x, hx⟩)

/-! ### Commutativity and the unit -/

/-- Over an affine open the graded product is the associated graded product. -/
private theorem algebraPiece_mul (U : X.affineOpens) (n m : ℕ)
    (x : (D.algebra.piece (n : ℤ)).val.obj (op U.1))
    (y : (D.algebra.piece (m : ℤ)).val.obj (op U.1)) :
    D.algebraPiece (n + m) U ((D.algebra.mul (n : ℤ) (m : ℤ)).app (op U.1) x y) =
      AssociatedGraded.homogeneousSMul ((baseIdealSheaf A I f).ideal U)
        (D.algebraPiece n U x) (D.algebraPiece m U y) :=
  eq_of_heq (D.algebraMul n m U x y)

/-- **The associated graded algebra of an ideal is commutative on the sections over an affine
open.** There `D.algebraMul` identifies the graded product with
`AssociatedGraded.homogeneousSMul`, which is commutative because the sections of the structure
sheaf form a commutative ring. -/
public lemma algebra_mul_comm (U : X.affineOpens)
    (x y : (D.algebra.piece (1 : ℤ)).val.obj (op U.1)) :
    (D.algebra.mul 1 1).app (op U.1) x y = (D.algebra.mul 1 1).app (op U.1) y x := by
  apply (D.algebraPiece (1 + 1) U).injective
  refine (algebraPiece_mul A I f D U 1 1 x y).trans
    (Eq.trans ?_ (algebraPiece_mul A I f D U 1 1 y x).symm)
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (D.algebraPiece 1 U x)
  obtain ⟨q, hq⟩ := Submodule.Quotient.mk_surjective _ (D.algebraPiece 1 U y)
  rw [← hp, ← hq]
  exact congrArg (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) (1 + 1))
    (Subtype.ext (mul_comm (p : Γ(X, U.1)) q))

/-- **Over an affine open the unit of the associated graded algebra is the class of `1`.** The
unit acts as the identity in degree zero, so its class `c` satisfies `c · z = z` for every
degree-zero class `z`; taking `z` to be the class of `1` identifies `c` with it. -/
public lemma algebraPiece_one (U : X.affineOpens) :
    D.algebraPiece 0 U (D.algebra.one.eval (op U.1)) =
      AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) 0
        ⟨1, by rw [AssociatedGraded.power_zero]; trivial⟩ := by
  have hone1 : (1 : Γ(X, U.1)) ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) 0 := by
    rw [AssociatedGraded.power_zero]; trivial
  have h1 : (D.algebra.mul ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ)).app (op U.1)
      (D.algebra.one.eval (op U.1))
      ((D.algebraPiece 0 U).symm
        (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) 0 ⟨1, hone1⟩)) =
      (D.algebraPiece 0 U).symm
        (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) 0 ⟨1, hone1⟩) :=
    eq_of_heq (D.algebra.one_mul _ (op U.1) _)
  have h2 := algebraPiece_mul A I f D U 0 0 (D.algebra.one.eval (op U.1))
    ((D.algebraPiece 0 U).symm
      (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) 0 ⟨1, hone1⟩))
  rw [h1, AddEquiv.apply_symm_apply] at h2
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    (D.algebraPiece 0 U (D.algebra.one.eval (op U.1)))
  rw [← hc] at h2 ⊢
  refine Eq.trans ?_ h2.symm
  exact congrArg (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) (0 + 0))
    (Subtype.ext (by simp))

/-! ### The degree-one generators -/

variable {ι : Type u} (a : ι → A) (ha : Ideal.span (Set.range a) = I)

include ha

/-- The image of a chosen generator `a i` lies in `ℐ` over every affine open. -/
public lemma baseSectionHom_gen_mem (i : ι) (U : X.affineOpens) :
    baseSectionHom A f U.1 (a i) ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) 1 :=
  baseSectionHom_mem_power A I f U 1 (a i)
    (by rw [pow_one]; exact ha ▸ Ideal.subset_span ⟨i, rfl⟩)

/-- The degree-one generator attached to `a i`, on the sections over an affine open: a section
`r` of the structure sheaf goes to `r` times the class of `a i` in `ℐ / ℐ ²`. -/
public def genSectionHom (i : ι) (U : X.affineOpens) :
    (SheafOfModules.unit X.ringCatSheaf).val.obj (op U.1) ⟶
      (D.algebra.piece 1).val.obj (op U.1) :=
  ModuleCat.ofHom
    { toFun := fun r => r • pieceClass A I f D U 1 (baseSectionHom A f U.1 (a i))
        (baseSectionHom_gen_mem A I f a ha i U)
      map_add' := fun r s => by exact add_smul r s _
      map_smul' := fun c r => by exact mul_smul c r _ }

/-- The value of the degree-one generator on a section over an affine open is the class of the
product. The section is given twice, once in each of the two spellings of the sections of the
structure sheaf, so that the statement can be used with the second spelling already in the
shape the surrounding argument needs. -/
public lemma genSectionHom_apply (i : ι) (U : X.affineOpens)
    (r : X.ringCatSheaf.obj.obj (op U.1)) (s : Γ(X, U.1))
    (hrs : Stacks.Blowup.ringSectionToGamma r = s)
    (hmem : s * baseSectionHom A f U.1 (a i) ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) 1) :
    genSectionHom A I f D a ha i U r =
      pieceClass A I f D U 1 (s * baseSectionHom A f U.1 (a i)) hmem := by
  subst hrs
  exact (pieceClass_smul A I f D U 1 r (baseSectionHom A f U.1 (a i))
    (baseSectionHom_gen_mem A I f a ha i U) hmem).symm

/-- The product of a section of the structure sheaf with the image of `a i` lies in `ℐ`. -/
public lemma mul_baseSectionHom_gen_mem (i : ι) (U : X.affineOpens) (r : Γ(X, U.1)) :
    r * baseSectionHom A f U.1 (a i) ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) 1 := by
  rw [← smul_eq_mul]
  exact Submodule.smul_mem _ _ (baseSectionHom_gen_mem A I f a ha i U)

/-- The degree-one generators over the affine opens are compatible with the restriction maps
between them: `D.algebraPiece_naturality` and `D.algebraRestriction_mk` compute the restriction
of a class as the class of the restriction, and `Stacks.Coherent.baseSectionHom_restrict`
restricts the image of `a i`. -/
public lemma genSectionHom_compatible (i : ι) :
    Stacks.BasisRestriction.IsCompatibleOnBasis (SheafOfModules.unit X.ringCatSheaf)
      (D.algebra.piece 1) (fun U : X.affineOpens => U.1)
      (genSectionHom A I f D a ha i) := by
  intro U V h r
  apply (D.algebraPiece 1 V).injective
  have hUmem := mul_baseSectionHom_gen_mem A I f a ha i U (Stacks.Blowup.ringSectionToGamma r)
  have hVmem := mul_baseSectionHom_gen_mem A I f a ha i V
    (X.presheaf.map (homOfLE h).op (Stacks.Blowup.ringSectionToGamma r))
  have hsub : (⟨X.presheaf.map (homOfLE h).op (Stacks.Blowup.ringSectionToGamma r) *
        baseSectionHom A f V.1 (a i), hVmem⟩ :
      AssociatedGraded.power (M := Γ(X, V.1)) ((baseIdealSheaf A I f).ideal V) 1) =
      ⟨X.presheaf.map (homOfLE h).op
          (Stacks.Blowup.ringSectionToGamma r * baseSectionHom A f U.1 (a i)),
        D.algebraRestrictionPower 1 U V h ⟨_, hUmem⟩⟩ := by
    refine Subtype.ext ?_
    show X.presheaf.map (homOfLE h).op (Stacks.Blowup.ringSectionToGamma r) *
        baseSectionHom A f V.1 (a i) =
      X.presheaf.map (homOfLE h).op
        (Stacks.Blowup.ringSectionToGamma r * baseSectionHom A f U.1 (a i))
    rw [map_mul, baseSectionHom_restrict]
  calc D.algebraPiece 1 V (genSectionHom A I f D a ha i V
          ((SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE h).op r))
      = D.algebraPiece 1 V (pieceClass A I f D V 1
          (X.presheaf.map (homOfLE h).op (Stacks.Blowup.ringSectionToGamma r) *
            baseSectionHom A f V.1 (a i)) hVmem) :=
        congrArg (fun y => D.algebraPiece 1 V y)
          (genSectionHom_apply A I f D a ha i V
            ((SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE h).op r)
            (X.presheaf.map (homOfLE h).op (Stacks.Blowup.ringSectionToGamma r)) rfl hVmem)
    _ = AssociatedGraded.mk ((baseIdealSheaf A I f).ideal V) 1 ⟨_, hVmem⟩ :=
        algebraPiece_pieceClass A I f D V 1 _ hVmem
    _ = AssociatedGraded.mk ((baseIdealSheaf A I f).ideal V) 1
          ⟨X.presheaf.map (homOfLE h).op
              (Stacks.Blowup.ringSectionToGamma r * baseSectionHom A f U.1 (a i)),
            D.algebraRestrictionPower 1 U V h ⟨_, hUmem⟩⟩ :=
        congrArg (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal V) 1) hsub
    _ = D.algebraRestriction 1 U V h
          (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) 1 ⟨_, hUmem⟩) :=
        (D.algebraRestriction_mk 1 U V h ⟨_, hUmem⟩).symm
    _ = D.algebraRestriction 1 U V h
          (D.algebraPiece 1 U (genSectionHom A I f D a ha i U r)) :=
        congrArg (fun y => D.algebraRestriction 1 U V h y)
          ((algebraPiece_pieceClass A I f D U 1 _ hUmem).symm.trans
            (congrArg (fun y => D.algebraPiece 1 U y)
              (genSectionHom_apply A I f D a ha i U r (Stacks.Blowup.ringSectionToGamma r) rfl
                hUmem).symm))
    _ = D.algebraPiece 1 V ((D.algebra.piece 1).val.map (homOfLE h).op
          (genSectionHom A I f D a ha i U r)) :=
        (D.algebraPiece_naturality 1 U V h (genSectionHom A I f D a ha i U r)).symm

/-- **The degree-one generator attached to `a i`**: the morphism `𝒪_X ⟶ 𝓑₁` whose value on a
section `r` over an affine open `U` is the class of `r · a i` in `ℐ(U) / ℐ(U) ²`. The affine
opens form a basis, so `Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis` assembles
the chartwise formulas into a morphism of sheaves of modules. -/
public def genHom (i : ι) : SheafOfModules.unit X.ringCatSheaf ⟶ D.algebra.piece 1 :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis
    (SheafOfModules.unit X.ringCatSheaf) (D.algebra.piece 1) (fun U : X.affineOpens => U.1)
    (genSectionHom A I f D a ha i) (by simpa using X.isBasis_affineOpens)
    (genSectionHom_compatible A I f D a ha i)

/-- The degree-one generator has the chartwise formula as its component on an affine open. -/
public lemma genHom_app (i : ι) (U : X.affineOpens) :
    (genHom A I f D a ha i).val.app (op U.1) = genSectionHom A I f D a ha i U :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app
    (SheafOfModules.unit X.ringCatSheaf) (D.algebra.piece 1) (fun U : X.affineOpens => U.1)
    (genSectionHom A I f D a ha i) _ _ U

/-- **The morphism out of the free module determined by the degree-one generators.** The free
sheaf of modules on `ι` is the coproduct of copies of the structure sheaf, so the family of
generators descends to it. -/
public def genFree : SheafOfModules.free (R := X.ringCatSheaf) ι ⟶ D.algebra.piece 1 :=
  Limits.Sigma.desc fun i => genHom A I f D a ha i

/-- The `i`-th coprojection into the free module followed by `genFree` is the `i`-th
generator. -/
public lemma sigmaι_comp_genFree (i : ι) :
    Limits.Sigma.ι (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) i ≫
        genFree A I f D a ha = genHom A I f D a ha i := by
  simp [genFree]

/-- **The degree-one generators commute pairwise.** The identity is between two sections of
`𝓑₂` over an arbitrary open; the affine opens contained in it cover it, so it suffices to
compare the restrictions, where `Stacks.Coherent.algebra_mul_comm` applies. -/
public lemma pairwiseCommutes_genFree :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (genFree A I f D a ha) := by
  rintro ⟨W⟩ s u
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis (D.algebra.piece (1 + 1))
    (fun V : X.affineOpens => V.1) (by simpa using X.isBasis_affineOpens) _ _ fun V hle => ?_
  rw [(D.algebra.mul 1 1).naturality (homOfLE hle).op _ _,
    (D.algebra.mul 1 1).naturality (homOfLE hle).op _ _]
  exact algebra_mul_comm A I f D V _ _

/-! ### The unital homomorphism out of the polynomial algebra -/

/-- **The unital homomorphism `𝒪_X[x_i] ⟶ 𝓑`** extending the degree-one generators, by the
universal property of the symmetric algebra. -/
public def polyHom :
    SheafOfModules.GradedAlgebra.UnitalHom (polyAlgebra X ι) D.algebra :=
  (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X)
      (SheafOfModules.free (R := X.ringCatSheaf) ι)).isUniversal.desc D.algebra
    (genFree A I f D a ha) (pairwiseCommutes_genFree A I f D a ha)

/-- The unital homomorphism extends the degree-one generators. -/
public lemma polyHom_extends :
    SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X)
        (SheafOfModules.free (R := X.ringCatSheaf) ι) ≫
      (polyHom A I f D a ha).app 1 = genFree A I f D a ha :=
  (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X)
      (SheafOfModules.free (R := X.ringCatSheaf) ι)).isUniversal.desc_extends D.algebra
    (genFree A I f D a ha) (pairwiseCommutes_genFree A I f D a ha)

/-! ### Covering the sections over an affine open -/

/-- A section of a homogeneous piece of the associated graded algebra over an affine open is
*covered* when it is the image of a section of the polynomial algebra. -/
public def IsPolyImage (U : X.affineOpens) (m : ℤ)
    (b : (D.algebra.piece m).val.obj (op U.1)) : Prop :=
  ∃ c : ((polyAlgebra X ι).piece m).val.obj (op U.1),
    ((polyHom A I f D a ha).app m).val.app (op U.1) c = b

/-- The zero section is covered. -/
public lemma isPolyImage_zero (U : X.affineOpens) (m : ℤ) :
    IsPolyImage A I f D a ha U m 0 :=
  ⟨0, map_zero _⟩

/-- A sum of covered sections is covered. -/
public lemma isPolyImage_add (U : X.affineOpens) (m : ℤ)
    {b b' : (D.algebra.piece m).val.obj (op U.1)}
    (hb : IsPolyImage A I f D a ha U m b) (hb' : IsPolyImage A I f D a ha U m b') :
    IsPolyImage A I f D a ha U m (b + b') := by
  obtain ⟨c, hc⟩ := hb
  obtain ⟨c', hc'⟩ := hb'
  exact ⟨c + c', by rw [map_add, hc, hc']⟩

/-- A multiple of a covered section is covered. -/
public lemma isPolyImage_smul (U : X.affineOpens) (m : ℤ)
    (r : X.ringCatSheaf.obj.obj (op U.1))
    {b : (D.algebra.piece m).val.obj (op U.1)} (hb : IsPolyImage A I f D a ha U m b) :
    IsPolyImage A I f D a ha U m (r • b) := by
  obtain ⟨c, hc⟩ := hb
  exact ⟨r • c, by rw [map_smul, hc]⟩

/-- The class of an element equal to `0` is covered. -/
private theorem isPolyImage_pieceClass_zero (U : X.affineOpens) (n : ℕ) {x : Γ(X, U.1)}
    {hx : x ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n}
    (h0 : x = 0) : IsPolyImage A I f D a ha U (n : ℤ) (pieceClass A I f D U n x hx) := by
  subst h0
  rw [pieceClass_zero]
  exact isPolyImage_zero A I f D a ha U _

/-- The class of an element equal to a sum of elements with covered classes is covered. -/
private theorem isPolyImage_pieceClass_add (U : X.affineOpens) (n : ℕ) {x y z : Γ(X, U.1)}
    {hx : x ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n}
    {hy : y ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n}
    {hz : z ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n}
    (hzxy : z = x + y) (hcx : IsPolyImage A I f D a ha U (n : ℤ) (pieceClass A I f D U n x hx))
    (hcy : IsPolyImage A I f D a ha U (n : ℤ) (pieceClass A I f D U n y hy)) :
    IsPolyImage A I f D a ha U (n : ℤ) (pieceClass A I f D U n z hz) := by
  subst hzxy
  rw [pieceClass_add A I f D U n x y hx hy hz]
  exact isPolyImage_add A I f D a ha U _ hcx hcy

/-- The class of a multiple of an element with covered class is covered. -/
private theorem isPolyImage_pieceClass_smul (U : X.affineOpens) (n : ℕ)
    (c : X.ringCatSheaf.obj.obj (op U.1)) {x z : Γ(X, U.1)}
    {hx : x ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n}
    {hz : z ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n}
    (hzx : z = Stacks.Blowup.ringSectionToGamma c * x)
    (hcx : IsPolyImage A I f D a ha U (n : ℤ) (pieceClass A I f D U n x hx)) :
    IsPolyImage A I f D a ha U (n : ℤ) (pieceClass A I f D U n z hz) := by
  subst hzx
  rw [pieceClass_smul A I f D U n c x hx hz]
  exact isPolyImage_smul A I f D a ha U _ c hcx

/-- The product of two covered sections is covered: the homomorphism is multiplicative. -/
public lemma isPolyImage_mul (U : X.affineOpens) (m m' : ℤ)
    {b : (D.algebra.piece m).val.obj (op U.1)}
    {b' : (D.algebra.piece m').val.obj (op U.1)}
    (hb : IsPolyImage A I f D a ha U m b) (hb' : IsPolyImage A I f D a ha U m' b') :
    IsPolyImage A I f D a ha U (m + m') ((D.algebra.mul m m').app (op U.1) b b') := by
  obtain ⟨c, hc⟩ := hb
  obtain ⟨c', hc'⟩ := hb'
  refine ⟨((polyAlgebra X ι).mul m m').app (op U.1) c c', ?_⟩
  rw [(polyHom A I f D a ha).map_mul m m' (op U.1) c c', hc, hc']

/-- The unit of the associated graded algebra is covered: the homomorphism is unital. -/
public lemma isPolyImage_one (U : X.affineOpens) :
    IsPolyImage A I f D a ha U 0 (D.algebra.one.eval (op U.1)) :=
  ⟨(polyAlgebra X ι).one.eval (op U.1), (polyHom A I f D a ha).map_one (op U.1)⟩

/-- The value of a degree-one generator on a section over an affine open is covered: it is the
image of the corresponding section of the degree-one piece of the polynomial algebra. -/
public lemma isPolyImage_genSectionHom (U : X.affineOpens) (i : ι)
    (r : X.ringCatSheaf.obj.obj (op U.1)) :
    IsPolyImage A I f D a ha U 1 (genSectionHom A I f D a ha i U r) := by
  have hcomp : (Limits.Sigma.ι (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) i ≫
        SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X)
          (SheafOfModules.free (R := X.ringCatSheaf) ι)) ≫ (polyHom A I f D a ha).app 1 =
      genHom A I f D a ha i :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g : SheafOfModules.free (R := X.ringCatSheaf) ι ⟶ D.algebra.piece 1 =>
            Limits.Sigma.ι (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) i ≫ g)
          (polyHom_extends A I f D a ha)).trans (sigmaι_comp_genFree A I f D a ha i))
  refine ⟨(Limits.Sigma.ι (fun _ : ι => SheafOfModules.unit X.ringCatSheaf) i ≫
      SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X)
        (SheafOfModules.free (R := X.ringCatSheaf) ι)).val.app (op U.1) r, ?_⟩
  refine Eq.trans ?_ (congrArg (fun φ => φ r) (genHom_app A I f D a ha i U))
  exact congrArg (fun g : SheafOfModules.unit X.ringCatSheaf ⟶ D.algebra.piece 1 =>
    g.val.app (op U.1) r) hcomp

/-- **The class of the image of an element of `I` is covered in degree one.** The elements of
`I` whose class is covered form a submodule containing the `a i`, which span `I`. -/
public lemma isPolyImage_pieceClass_one (U : X.affineOpens) (z : A) (hz : z ∈ I)
    (h : baseSectionHom A f U.1 z ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) 1) :
    IsPolyImage A I f D a ha U 1 (pieceClass A I f D U 1 (baseSectionHom A f U.1 z) h) := by
  have main : ∀ t ∈ Ideal.span (Set.range a), ∃ ht : baseSectionHom A f U.1 t ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) 1,
      IsPolyImage A I f D a ha U 1
        (pieceClass A I f D U 1 (baseSectionHom A f U.1 t) ht) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      refine ⟨baseSectionHom_gen_mem A I f a ha i U, ?_⟩
      obtain ⟨c, hcc⟩ := isPolyImage_genSectionHom A I f D a ha U i 1
      exact ⟨c, hcc.trans (one_smul _ _)⟩
    | zero =>
      refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, ?_⟩
      exact isPolyImage_pieceClass_zero A I f D a ha U 1 (map_zero _)
    | add w w' _ _ ihw ihw' =>
      obtain ⟨hm, Pw⟩ := ihw
      obtain ⟨hm', Pw'⟩ := ihw'
      refine ⟨by rw [map_add]; exact Submodule.add_mem _ hm hm', ?_⟩
      exact isPolyImage_pieceClass_add A I f D a ha U 1 (map_add _ _ _) Pw Pw'
    | smul c w _ ihw =>
      obtain ⟨hm, Pw⟩ := ihw
      have hcw : baseSectionHom A f U.1 (c • w) =
          Stacks.Blowup.ringSectionToGamma (baseSectionHom A f U.1 c) *
            baseSectionHom A f U.1 w := by
        rw [smul_eq_mul, map_mul]
        rfl
      refine ⟨by rw [hcw]; exact Submodule.smul_mem _ _ hm, ?_⟩
      exact isPolyImage_pieceClass_smul A I f D a ha U 1 (baseSectionHom A f U.1 c) hcw Pw
  obtain ⟨_, P⟩ := main z (ha ▸ hz)
  exact P

/-- **The class of the image of an element of `I ⁿ` is covered in degree `n`.** Induction on
`n`: in degree zero the class is a multiple of the algebra unit, and an element of `I ⁿ⁺¹` is a
sum of products of an element of `I ⁿ` with an element of `I`, whose classes multiply to the
class of the product by `D.algebraMul`. -/
public lemma isPolyImage_pieceClass (U : X.affineOpens) (n : ℕ) (x : A) (hx : x ∈ I ^ n)
    (h : baseSectionHom A f U.1 x ∈
      AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n) :
    IsPolyImage A I f D a ha U (n : ℤ)
      (pieceClass A I f D U n (baseSectionHom A f U.1 x) h) := by
  induction n generalizing x with
  | zero =>
    have hmem0 : ∀ y : Γ(X, U.1),
        y ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) 0 := by
      intro y
      rw [AssociatedGraded.power_zero]; trivial
    have hone1 := hmem0 1
    have hmem1 := hmem0 (Stacks.Blowup.ringSectionToGamma (baseSectionHom A f U.1 x) * 1)
    have hone : D.algebra.one.eval (op U.1) = pieceClass A I f D U 0 1 hone1 := by
      apply (D.algebraPiece 0 U).injective
      rw [algebraPiece_pieceClass, algebraPiece_one]
    have hcov := isPolyImage_smul A I f D a ha U 0 (baseSectionHom A f U.1 x)
      (isPolyImage_one A I f D a ha U)
    rw [hone, ← pieceClass_smul A I f D U 0 (baseSectionHom A f U.1 x) 1 hone1 hmem1,
      pieceClass_congr A I f D U 0 _ (baseSectionHom A f U.1 x) hmem1 h (mul_one _)] at hcov
    exact hcov
  | succ n ih =>
    have main : ∀ z ∈ (I ^ n * I : Ideal A),
        ∃ hz : baseSectionHom A f U.1 z ∈ AssociatedGraded.power (M := Γ(X, U.1))
          ((baseIdealSheaf A I f).ideal U) (n + 1),
        IsPolyImage A I f D a ha U ((n + 1 : ℕ) : ℤ)
          (pieceClass A I f D U (n + 1) (baseSectionHom A f U.1 z) hz) := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro y hy w hw
        have hy' := baseSectionHom_mem_power A I f U n y hy
        have hwm : baseSectionHom A f U.1 w ∈
            AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) 1 :=
          baseSectionHom_mem_power A I f U 1 w (by rwa [pow_one])
        have hprod : baseSectionHom A f U.1 (y * w) ∈
            AssociatedGraded.power (M := Γ(X, U.1))
              ((baseIdealSheaf A I f).ideal U) (n + 1) :=
          baseSectionHom_mem_power A I f U (n + 1) (y * w)
            (by rw [pow_succ]; exact Submodule.mul_mem_mul hy hw)
        refine ⟨hprod, ?_⟩
        have hmulcov := isPolyImage_mul A I f D a ha U (n : ℤ) 1
          (ih y hy hy') (isPolyImage_pieceClass_one A I f D a ha U w hw hwm)
        have hkey : (D.algebra.mul (n : ℤ) 1).app (op U.1)
              (pieceClass A I f D U n (baseSectionHom A f U.1 y) hy')
              (pieceClass A I f D U 1 (baseSectionHom A f U.1 w) hwm) =
            pieceClass A I f D U (n + 1) (baseSectionHom A f U.1 (y * w)) hprod := by
          apply (D.algebraPiece (n + 1) U).injective
          refine (algebraPiece_mul A I f D U n 1 _ _).trans ?_
          rw [algebraPiece_pieceClass, algebraPiece_pieceClass, algebraPiece_pieceClass]
          refine congrArg (AssociatedGraded.mk ((baseIdealSheaf A I f).ideal U) (n + 1))
            (Subtype.ext ?_)
          show (baseSectionHom A f U.1 y : Γ(X, U.1)) • (baseSectionHom A f U.1 w) = _
          rw [smul_eq_mul, ← map_mul]
        rw [hkey] at hmulcov
        exact hmulcov
      · rintro y w ⟨hy, Py⟩ ⟨hw, Pw⟩
        refine ⟨by rw [map_add]; exact Submodule.add_mem _ hy hw, ?_⟩
        exact isPolyImage_pieceClass_add A I f D a ha U (n + 1) (map_add _ _ _) Py Pw
    obtain ⟨_, P⟩ := main x (by rwa [← pow_succ])
    exact P

/-- **Every section of a nonnegative homogeneous piece over an affine open is covered.** The
section is the class of an element of `ℐ(U) ⁿ = Ideal.map (baseSectionHom A f U) (I ⁿ)`, and a
span induction reduces to the classes of the images of elements of `I ⁿ`. -/
public lemma isPolyImage_of_nat (U : X.affineOpens) (n : ℕ)
    (b : (D.algebra.piece (n : ℤ)).val.obj (op U.1)) :
    IsPolyImage A I f D a ha U (n : ℤ) b := by
  have hpow : AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n =
      Ideal.span (⇑(baseSectionHom A f U.1) '' ((I ^ n : Ideal A) : Set A)) := by
    rw [AssociatedGraded.ring_power_eq, baseIdealSheaf_ideal_pow_eq_map]
    rfl
  have hmemOf : ∀ s ∈ Ideal.span (⇑(baseSectionHom A f U.1) '' ((I ^ n : Ideal A) : Set A)),
      s ∈ AssociatedGraded.power (M := Γ(X, U.1)) ((baseIdealSheaf A I f).ideal U) n := by
    intro s hs
    rw [hpow]
    exact hs
  have key : ∀ v ∈ Ideal.span (⇑(baseSectionHom A f U.1) '' ((I ^ n : Ideal A) : Set A)),
      ∀ hv : v ∈ AssociatedGraded.power (M := Γ(X, U.1))
        ((baseIdealSheaf A I f).ideal U) n,
      IsPolyImage A I f D a ha U (n : ℤ) (pieceClass A I f D U n v hv) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨y, hy, rfl⟩ := ht
      exact fun hvv => isPolyImage_pieceClass A I f D a ha U n y hy hvv
    | zero => exact fun _ => isPolyImage_pieceClass_zero A I f D a ha U n rfl
    | add s t hs ht hs' ht' =>
      exact fun _ => isPolyImage_pieceClass_add A I f D a ha U n rfl (hs' (hmemOf s hs))
        (ht' (hmemOf t ht))
    | smul c s hs hs' =>
      exact fun _ => isPolyImage_pieceClass_smul A I f D a ha U n c rfl (hs' (hmemOf s hs))
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (D.algebraPiece n U b)
  have hb : b = pieceClass A I f D U n (w : Γ(X, U.1)) w.2 := by
    apply (D.algebraPiece n U).injective
    rw [algebraPiece_pieceClass, ← hw]
    rfl
  rw [hb]
  exact key (w : Γ(X, U.1)) (by rw [← hpow]; exact w.2) w.2

/-- **The polynomial algebra covers the associated graded algebra on the sections over every
affine open, in every degree.** In a negative degree the target is a zero object; in degree
`n ≥ 0` this is `Stacks.Coherent.isPolyImage_of_nat`.

This is the hypothesis `hφ` of
`Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_epi_over`. -/
public theorem surjective_polyHom_app (U : X.affineOpens) (m : ℤ)
    (b : (D.algebra.piece m).val.obj (op U.1)) :
    ∃ c : ((polyAlgebra X ι).piece m).val.obj (op U.1),
      ((polyHom A I f D a ha).app m).val.app (op U.1) c = b := by
  rcases lt_or_ge m 0 with hm | hm
  · have hid := (Limits.IsZero.iff_id_eq_zero (D.algebra.piece m)).mp (D.algebraNegative m hm)
    have happ := congrArg
      (fun g : D.algebra.piece m ⟶ D.algebra.piece m => g.val.app (op U.1) b) hid
    rw [show ((𝟙 (D.algebra.piece m) : D.algebra.piece m ⟶ D.algebra.piece m).val.app
        (op U.1)) = 𝟙 _ from rfl,
      show ((0 : D.algebra.piece m ⟶ D.algebra.piece m).val.app (op U.1)) = 0 from rfl] at happ
    have hb : b = 0 := by simpa using happ
    exact ⟨0, by rw [hb, map_zero]⟩
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact isPolyImage_of_nat A I f D a ha U n b

end Stacks.Coherent

end
