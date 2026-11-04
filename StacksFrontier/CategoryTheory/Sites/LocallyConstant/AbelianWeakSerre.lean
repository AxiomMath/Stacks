module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.Glueing.MapsOfSheavesGlue
import StacksCore.Tactic.StacksAttribute

/-!
# Finite locally constant abelian sheaves form a weak Serre subcategory

Let `(C, J)` be a site. Stacks Tag 093U (2) asserts that the finite locally constant sheaves of
abelian groups form a weak Serre subcategory of the category of all abelian sheaves on `C`. This
file proves that.

## Main definitions

* `Stacks.ConstantSheaf.isFiniteLocallyConstantAbelianSheaf`: the property of objects of
  `Sh(C, Ab)` that the tag is about.

## Main results

* **Tag 093U (2)** itself, carried by
  `Stacks.ConstantSheaf.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf`.

## Implementation notes

The proof does not redo the Serre-class bookkeeping. It *reduces to part (3)*, the
`Stacks.ConstantSheaf.isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf`, taken over
the coefficient ring `ℤ`, which is Noetherian. The reduction has two halves, and both are needed
because neither condition alone is the one of part (2):

* a finite locally constant abelian sheaf is, read as a sheaf of `ℤ`-modules, locally constant of
  finite type — a finite abelian group is a finitely generated `ℤ`-module;
* conversely a locally constant sheaf of `ℤ`-modules of finite type whose local values are
  moreover *locally annihilated* by some positive integer is finite locally constant, because the
  cokernel of multiplication by `n ≠ 0` on a finitely generated abelian group is finite.

Local annihilation is the extra invariant carried through the five term exact sequence: it is
visibly inherited by the middle term, with the product of the two exponents as a new exponent,
and `|E| = |M| * |N|` never has to be computed.

Reading an abelian sheaf as a sheaf of `ℤ`-modules is `sheafCompose` along the inverse of
`forget₂ (ModuleCat ℤ) AddCommGrpCat`, which is an equivalence. The three sheaf-theoretic side
conditions this needs — `HasSheafCompose`, `PreservesSheafification` and the compatibility
`constantCommuteCompose` of the constant sheaf functor with postcomposition — are all available
for an equivalence of value categories, but none of them is found by instance search inside its
budget, so each is isolated as a named theorem below and supplied by name.

The value universe is `AddCommGrpCat.{max u v w}` for a free `w`, which is the same recipe as the
set universe of Tag 093U (1) and the module universe of Tag 093U (3), and for the same reason: at
that universe every sheafification hypothesis, and the pointwise Kan extension hypothesis of
`Stacks.ConstantSheaf.mapPullbackConstantSheafApp`, is dischargeable, and the universe is stable
under slicing the site. `HasSheafify` for abelian groups is not an instance in Mathlib at this
shape; it is recorded here from
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall`.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace Stacks.ConstantSheaf

/-! ### Multiplication by an integer on an object of an additive category -/

section Nsmul

variable {D : Type*} [Category* D] [Preadditive D]

/-- If `n` annihilates the identity of `A` and `A ⟶ B` is epi, then `n` annihilates the identity
of `B`. -/
theorem nsmul_id_zero_of_epi {A B : D} (f : A ⟶ B) [Epi f] (n : ℕ) (h : n • 𝟙 A = 0) :
    n • 𝟙 B = 0 := by
  apply (cancel_epi f).1
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
    Category.id_comp, comp_zero, zero_comp] using congrArg (fun g => g ≫ f) h

/-- Annihilation of the identity by `n` is invariant under isomorphism. -/
theorem nsmul_id_zero_of_iso {A B : D} (e : A ≅ B) (n : ℕ) (h : n • 𝟙 A = 0) : n • 𝟙 B = 0 :=
  nsmul_id_zero_of_epi e.hom n h

/-- An additive functor carries an object whose identity is killed by `n` to such an object. -/
private theorem nsmul_id_zero_map {E : Type*} [Category* E] [Preadditive E] (T : D ⥤ E)
    [T.Additive] {A : D} (n : ℕ) (h : n • 𝟙 A = 0) : n • 𝟙 (T.obj A) = 0 := by
  simpa only [Functor.map_nsmul, T.map_id, Functor.map_zero] using congrArg T.map h

end Nsmul

/-- **The exponent is multiplicative along a short exact sequence.** If `m` annihilates the
identity of the sub and `n` annihilates the identity of the quotient, then `m * n` annihilates the
identity of the middle term. -/
theorem nsmul_id_zero_of_exact {D : Type*} [Category* D] [Abelian D]
    (S : ShortComplex D) (hS : S.Exact) (m n : ℕ)
    (hm : m • 𝟙 S.X₁ = 0) (hn : n • 𝟙 S.X₃ = 0) : (m * n) • 𝟙 S.X₂ = 0 := by
  have : Epi (kernel.lift S.g S.f S.zero) := hS.epi_kernelLift
  have hK := nsmul_id_zero_of_epi (kernel.lift S.g S.f S.zero) m hm
  have hz : (n • 𝟙 S.X₂) ≫ S.g = 0 := by
    simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
      Category.id_comp, comp_zero] using congrArg (fun g => S.g ≫ g) hn
  have h := congrArg (fun g => kernel.lift S.g (n • 𝟙 S.X₂) hz ≫ g ≫ kernel.ι S.g) hK
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
    kernel.lift_ι, comp_zero, zero_comp, ← mul_smul] using h

/-- A functor between abelian categories which is additive and exact carries exact composable
arrows to exact composable arrows. -/
theorem mapComposableArrows_exact {D E : Type*} [Category* D] [Category* E]
    [Abelian D] [Abelian E] (T : D ⥤ E) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {n : ℕ} (S : ComposableArrows D n) (hS : S.Exact) :
    ((T.mapComposableArrows n).obj S).Exact where
  zero i hi := by
    show T.map (S.map' i (i + 1)) ≫ T.map (S.map' (i + 1) (i + 2)) = 0
    simpa only [CategoryTheory.Functor.map_comp, Functor.map_zero] using
      congrArg T.map (hS.toIsComplex.zero i hi)
  exact i hi := (hS.exact i hi).map T

/-! ### Finitely generated abelian groups killed by a positive integer -/

section FG

universe x

/-- For a finitely generated abelian group `A` and `n ≠ 0`, the cokernel of `n • 𝟙 A` in
`AddCommGrpCat` is finite: it is the quotient of `A` by the image of multiplication by `n`, which
has finite index. -/
theorem finite_cokernel_nsmul (A : AddCommGrpCat.{x}) [AddGroup.FG A]
    (n : ℕ) (hn : n ≠ 0) : Finite ((cokernel (n • 𝟙 A) : AddCommGrpCat.{x}) : Type x) := by
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A hn
  have : Finite (A ⧸ (nsmulAddMonoidHom (α := A) n).range) := inferInstance
  have heq : (n • 𝟙 A).hom = nsmulAddMonoidHom (α := A) n := by ext; rfl
  have : Finite (A ⧸ (n • 𝟙 A).hom.range) := by rwa [heq]
  exact Finite.of_injective (AddCommGrpCat.cokernelIsoQuotient (n • 𝟙 A)).hom
    (ConcreteCategory.bijective_of_isIso (AddCommGrpCat.cokernelIsoQuotient (n • 𝟙 A)).hom).1

end FG

/-! ### Integer coefficients -/

section Coefficients

universe x

/-- An abelian group read as a `ℤ`-module: the inverse of the forgetful equivalence
`ModuleCat ℤ ⥤ AddCommGrpCat`. -/
abbrev intCoefficients : AddCommGrpCat.{x} ⥤ ModuleCat.{x} ℤ :=
  (forget₂ (ModuleCat.{x} ℤ) AddCommGrpCat.{x}).inv

variable {D : Type*} [Category* D] (K : GrothendieckTopology D)

/-- Postcomposition with `intCoefficients` carries sheaves to sheaves. Instance search does not
find this inside its budget, so it is recorded and applied by name. -/
theorem hasSheafCompose_intCoefficients : K.HasSheafCompose intCoefficients.{x} :=
  hasSheafCompose_of_preservesLimitsOfSize (J := K) (F := intCoefficients.{x})

/-- Postcomposition with `intCoefficients` commutes with sheafification: it is a left adjoint,
being half of an equivalence. -/
theorem preservesSheafification_intCoefficients :
    K.PreservesSheafification intCoefficients.{x} :=
  Sheaf.preservesSheafification_of_adjunction K (Adjunction.ofIsLeftAdjoint intCoefficients.{x})

/-- Postcomposition with the forgetful functor `ModuleCat ℤ ⥤ AddCommGrpCat` carries sheaves to
sheaves. -/
theorem hasSheafCompose_forget₂_int :
    K.HasSheafCompose (forget₂ (ModuleCat.{x} ℤ) AddCommGrpCat.{x}) :=
  hasSheafCompose_of_preservesLimitsOfSize (J := K)
    (F := forget₂ (ModuleCat.{x} ℤ) AddCommGrpCat.{x})

/-- Postcomposition with the forgetful functor `ModuleCat ℤ ⥤ AddCommGrpCat` commutes with
sheafification. -/
theorem preservesSheafification_forget₂_int :
    K.PreservesSheafification (forget₂ (ModuleCat.{x} ℤ) AddCommGrpCat.{x}) :=
  Sheaf.preservesSheafification_of_adjunction K
    (Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{x} ℤ) AddCommGrpCat.{x}))

attribute [local instance] hasSheafCompose_intCoefficients preservesSheafification_intCoefficients
  hasSheafCompose_forget₂_int preservesSheafification_forget₂_int

/-- Postcomposition with `T.inv` and then `T` is isomorphic to the identity on sheaves. -/
private def sheafCompose_inv_iso {A B : Type*} [Category* A] [Category* B]
    (T : A ⥤ B) [T.IsEquivalence] [K.HasSheafCompose T] [K.HasSheafCompose T.inv]
    (G : Sheaf K B) : (sheafCompose K T).obj ((sheafCompose K T.inv).obj G) ≅ G :=
  ObjectProperty.isoMk _ ((Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft G.obj T.asEquivalence.counitIso ≪≫ Functor.rightUnitor G.obj)

/-- Postcomposition with an equivalence of value categories is an equivalence of sheaf
categories. -/
theorem sheafCompose_isEquivalence {A B : Type*} [Category* A] [Category* B]
    (T : A ⥤ B) [T.IsEquivalence] [K.HasSheafCompose T] [K.HasSheafCompose T.inv] :
    (sheafCompose K T).IsEquivalence := by
  have : (sheafCompose K T).EssSurj :=
    ⟨fun G => ⟨(sheafCompose K T.inv).obj G, ⟨sheafCompose_inv_iso K T G⟩⟩⟩
  exact {}

end Coefficients

/-! ### Tag 093U (2) -/

section Main

universe v u w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sheafification of presheaves of abelian groups in a universe containing the site, together
with its left exactness: the site is essentially small in that universe. -/
theorem hasSheafify_addCommGrp : HasSheafify J AddCommGrpCat.{max u v w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max u v w, v, u} J

attribute [local instance] hasSheafify_addCommGrp hasSheafCompose_intCoefficients
  preservesSheafification_intCoefficients hasSheafCompose_forget₂_int
  preservesSheafification_forget₂_int

/-- Reading an abelian sheaf as a sheaf of `ℤ`-modules. -/
abbrev intSheaf :
    Sheaf J AddCommGrpCat.{max u v w} ⥤ Sheaf J (ModuleCat.{max u v w} ℤ) :=
  sheafCompose J intCoefficients.{max u v w}

/-- Reading an abelian sheaf as a sheaf of `ℤ`-modules is an equivalence of categories. -/
theorem intSheaf_isEquivalence : (intSheaf.{v, u, w} J).IsEquivalence :=
  sheafCompose_isEquivalence J _

/-- A finite abelian group is a finitely generated `ℤ`-module, so a finite locally constant
abelian sheaf is locally constant of finite type as a sheaf of `ℤ`-modules. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_intSheaf
    (F : Sheaf J AddCommGrpCat.{max u v w}) (hF : IsFiniteLocallyConstant J F) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J ℤ ((intSheaf.{v, u, w} J).obj F) := by
  intro U
  obtain ⟨I, X, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, X, f, hf, fun i => ?_⟩
  obtain ⟨A, hA, ⟨e⟩⟩ := h i
  let E := intCoefficients.{max u v w}.obj A
  have : Finite (A : Type (max u v w)) := hA
  have : Finite (((𝟭 AddCommGrpCat.{max u v w}).obj A) : Type (max u v w)) := hA
  have : Finite (E : Type (max u v w)) :=
    Finite.of_injective
      (fun y : E =>
        (((forget₂ (ModuleCat.{max u v w} ℤ)
          AddCommGrpCat.{max u v w}).asEquivalence.counitIso.app A).hom y : A))
      (ConcreteCategory.bijective_of_isIso
        ((forget₂ (ModuleCat.{max u v w} ℤ)
          AddCommGrpCat.{max u v w}).asEquivalence.counitIso.app A).hom).1
  refine ⟨E, (ModuleCat.isFG_iff E).2 inferInstance, ⟨?_⟩⟩
  exact ((constantCommuteCompose (J.over (X i)) intCoefficients.{max u v w}).app A).symm ≪≫
    (sheafCompose (J.over (X i)) intCoefficients.{max u v w}).mapIso e

/-- The converse reading: a trivializing cover for `F` as a sheaf of `ℤ`-modules of finite type is
a trivializing cover for `F` by *finitely generated* abelian groups. -/
theorem exists_cover_fg_of_isFiniteTypeLocallyConstantModuleSheaf
    (F : Sheaf J AddCommGrpCat.{max u v w})
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J ℤ ((intSheaf.{v, u, w} J).obj F))
    (U : C) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ i, ∃ A : AddCommGrpCat.{max u v w}, AddGroup.FG A ∧
        Nonempty ((constantSheaf (J.over (X i)) AddCommGrpCat.{max u v w}).obj A ≅
          (J.overPullback AddCommGrpCat.{max u v w} (X i)).obj F) := by
  obtain ⟨I, X, f, hf, h⟩ := hF U
  refine ⟨I, X, f, hf, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  let T := forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}
  have hfinite : Module.Finite ℤ E := (ModuleCat.isFG_iff E).1 hE
  have : AddGroup.FG E := Module.Finite.iff_addGroup_fg.mp (by
    convert hfinite using 1
    exact Subsingleton.elim _ _)
  refine ⟨T.obj E, inferInstance, ⟨?_⟩⟩
  exact ((constantCommuteCompose (J.over (X i)) T).app E).symm ≪≫
    (sheafCompose (J.over (X i)) T).mapIso e ≪≫
    sheafCompose_inv_iso (J.over (X i)) T ((J.overPullback AddCommGrpCat.{max u v w} (X i)).obj F)

/-- If a constant sheaf on a finitely generated abelian group `A` is isomorphic to `F`, and `F` is
annihilated by `n ≠ 0`, then `F` is the constant sheaf on a *finite* abelian group, namely the
cokernel of `n • 𝟙 A`. -/
theorem exists_finite_constant_of_fg_of_nsmul_id_zero
    (F : Sheaf J AddCommGrpCat.{max u v w}) (A : AddCommGrpCat.{max u v w}) [AddGroup.FG A]
    (e : (constantSheaf J AddCommGrpCat.{max u v w}).obj A ≅ F)
    (n : ℕ) (hn : n ≠ 0) (hF : n • 𝟙 F = 0) :
    ∃ B : AddCommGrpCat.{max u v w}, Finite (B : Type (max u v w)) ∧
      Nonempty ((constantSheaf J AddCommGrpCat.{max u v w}).obj B ≅ F) := by
  let T := constantSheaf J AddCommGrpCat.{max u v w}
  have : PreservesFiniteColimits T := by
    dsimp [T, constantSheaf]
    exact comp_preservesFiniteColimits _ _
  have : T.Additive := inferInstance
  have hT : T.map (n • 𝟙 A) = 0 := by
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using
      nsmul_id_zero_of_iso e.symm n hF
  exact ⟨cokernel (n • 𝟙 A), finite_cokernel_nsmul A n hn,
    ⟨PreservesCokernel.iso T (n • 𝟙 A) ≪≫ cokernelIsoOfEq hT ≪≫ cokernelZeroIsoTarget ≪≫ e⟩⟩

/-- Two covering families of the same object admit a common refinement by a single covering
family, each member of which factors through a member of each. -/
theorem exists_cover_factors_through_both
    {U : C} {I K : Type (max u v)} (X : I → C) (f : ∀ i, X i ⟶ U)
    (Y : K → C) (g : ∀ k, Y k ⟶ U)
    (hX : Sieve.ofArrows X f ∈ J U) (hY : Sieve.ofArrows Y g ∈ J U) :
    ∃ (L : Type (max u v)) (Z : L → C) (q : ∀ l, Z l ⟶ U),
      Sieve.ofArrows Z q ∈ J U ∧
        ∀ l, (∃ i, ∃ a : Z l ⟶ X i, q l = a ≫ f i) ∧
          (∃ k, ∃ b : Z l ⟶ Y k, q l = b ≫ g k) := by
  let S : Sieve U := Sieve.ofArrows X f ⊓ Sieve.ofArrows Y g
  obtain ⟨L, Z, q, hq⟩ := S.exists_eq_ofArrows
  refine ⟨L, Z, q, hq ▸ J.intersection_covering hX hY, fun l => ?_⟩
  have hmem : S.arrows (q l) := hq ▸ Sieve.ofArrows_mk Z q l
  exact ⟨Sieve.ofArrows.exists hmem.1, Sieve.ofArrows.exists hmem.2⟩

/-- **Local annihilation.** Every object of the site has a covering on each member of which the
restriction of `F` is annihilated by some positive integer. This is the extra invariant, beyond
finite type over `ℤ`, that pins down finiteness of the local values. -/
def IsLocallyAnnihilated (F : Sheaf J AddCommGrpCat.{max u v w}) : Prop :=
  ∀ U : C, ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
    Sieve.ofArrows X f ∈ J U ∧ ∀ i, ∃ n : ℕ, n ≠ 0 ∧
      n • 𝟙 ((J.overPullback AddCommGrpCat.{max u v w} (X i)).obj F) = 0

/-- Annihilation of a restriction by `n` passes to a finer slice. -/
theorem nsmul_id_zero_overPullback_of_hom (F : Sheaf J AddCommGrpCat.{max u v w})
    {X Y : C} (f : X ⟶ Y) (n : ℕ)
    (h : n • 𝟙 ((J.overPullback AddCommGrpCat.{max u v w} Y).obj F) = 0) :
    n • 𝟙 ((J.overPullback AddCommGrpCat.{max u v w} X).obj F) = 0 := by
  have : (J.overMapPullback AddCommGrpCat.{max u v w} f).Additive :=
    Functor.additive_of_preserves_binary_products _
  apply nsmul_id_zero_of_iso ((Stacks.SheafMapGluing.overPullbackOverMapPullbackIso J f).app F) n
  show n • 𝟙 ((J.overMapPullback AddCommGrpCat.{max u v w} f).obj
    ((J.overPullback AddCommGrpCat.{max u v w} Y).obj F)) = 0
  exact nsmul_id_zero_map (J.overMapPullback AddCommGrpCat.{max u v w} f) n h

/-- A finite locally constant abelian sheaf is locally annihilated: the exponent of a finite
abelian group is its cardinality. -/
theorem isLocallyAnnihilated_of_isFiniteLocallyConstant
    (F : Sheaf J AddCommGrpCat.{max u v w}) (hF : IsFiniteLocallyConstant J F) :
    IsLocallyAnnihilated.{v, u, w} J F := by
  intro U
  obtain ⟨I, X, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, X, f, hf, fun i => ?_⟩
  obtain ⟨A, hA, ⟨e⟩⟩ := h i
  have : Finite (A : Type (max u v w)) := hA
  let _ := Fintype.ofFinite A
  refine ⟨Fintype.card A, Fintype.card_ne_zero, ?_⟩
  apply nsmul_id_zero_of_iso e
  have hzero : Fintype.card A • 𝟙 A = 0 := by
    ext x
    exact card_nsmul_eq_zero
  exact nsmul_id_zero_map (constantSheaf (J.over (X i)) AddCommGrpCat.{max u v w}) _ hzero

/-- Local annihilation is inherited by the middle term of a short exact sequence, with the product
of the two exponents. -/
theorem isLocallyAnnihilated_of_exact (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v w}))
    (hS : S.Exact) (h₁ : IsLocallyAnnihilated.{v, u, w} J S.X₁)
    (h₃ : IsLocallyAnnihilated.{v, u, w} J S.X₃) :
    IsLocallyAnnihilated.{v, u, w} J S.X₂ := by
  intro U
  obtain ⟨I, X, f, hf, hX⟩ := h₁ U
  obtain ⟨K, Y, g, hg, hY⟩ := h₃ U
  obtain ⟨L, Z, q, hq, hZ⟩ := exists_cover_factors_through_both J X f Y g hf hg
  refine ⟨L, Z, q, hq, fun l => ?_⟩
  obtain ⟨⟨i, a, _⟩, ⟨k, b, _⟩⟩ := hZ l
  obtain ⟨m, hm, hmi⟩ := hX i
  obtain ⟨n, hn, hnk⟩ := hY k
  have hcolim : PreservesFiniteColimits
      (J.overPullback AddCommGrpCat.{max u v w} (Z l)) := by
    have : (J.overPullback AddCommGrpCat.{max u v w} (Z l)).IsLeftAdjoint :=
      ((Over.forget (Z l)).sheafAdjunctionCocontinuous AddCommGrpCat.{max u v w}
        (J.over (Z l)) J).isLeftAdjoint
    infer_instance
  exact ⟨m * n, Nat.mul_ne_zero hm hn,
    nsmul_id_zero_of_exact (S.map (J.overPullback AddCommGrpCat.{max u v w} (Z l))) (hS.map _) m n
      (nsmul_id_zero_overPullback_of_hom J S.X₁ a m hmi)
      (nsmul_id_zero_overPullback_of_hom J S.X₃ b n hnk)⟩

/-- The converse half of the reduction: finite type over `ℤ` together with local annihilation
gives finite local constancy. -/
theorem isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf
    (F : Sheaf J AddCommGrpCat.{max u v w})
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J ℤ ((intSheaf.{v, u, w} J).obj F))
    (hB : IsLocallyAnnihilated.{v, u, w} J F) : IsFiniteLocallyConstant J F := by
  constructor
  intro U
  obtain ⟨I, X, f, hf, hX⟩ := exists_cover_fg_of_isFiniteTypeLocallyConstantModuleSheaf J F hF U
  obtain ⟨K, Y, g, hg, hY⟩ := hB U
  obtain ⟨L, Z, q, hq, hZ⟩ := exists_cover_factors_through_both J X f Y g hf hg
  refine ⟨L, Z, q, hq, fun l => ?_⟩
  obtain ⟨⟨i, a, _⟩, ⟨k, b, _⟩⟩ := hZ l
  obtain ⟨A, hA, ⟨e⟩⟩ := hX i
  obtain ⟨n, hn, hnk⟩ := hY k
  have := hA
  exact exists_finite_constant_of_fg_of_nsmul_id_zero (J.over (Z l))
    ((J.overPullback AddCommGrpCat.{max u v w} (Z l)).obj F) A
    (mapPullbackConstantSheafApp J AddCommGrpCat.{max u v w} a A ≪≫
      (J.overMapPullback AddCommGrpCat.{max u v w} a).mapIso e ≪≫
      (Stacks.SheafMapGluing.overPullbackOverMapPullbackIso J a).app F)
    n hn (nsmul_id_zero_overPullback_of_hom J F b n hnk)

/-- The zero abelian sheaf is finite locally constant. -/
theorem isFiniteLocallyConstant_zero :
    IsFiniteLocallyConstant J (0 : Sheaf J AddCommGrpCat.{max u v w}) := by
  constructor
  intro U
  refine ⟨PUnit, (fun _ : PUnit => U), (fun _ => 𝟙 U), ?_, fun _ => ?_⟩
  · show Sieve.generate (Presieve.ofArrows (fun _ : PUnit => U)
      (fun _ => 𝟙 U)) ∈ J U
    rw [Presieve.ofArrows_of_unique, Sieve.generate_of_singleton_isSplitEpi]
    exact J.top_mem U
  · let E : AddCommGrpCat.{max u v w} := AddCommGrpCat.of (ULift.{max u v w} PUnit)
    refine ⟨E, inferInstance, ⟨?_⟩⟩
    exact (Functor.map_isZero (constantSheaf (J.over U) AddCommGrpCat.{max u v w})
        (AddCommGrpCat.isZero_of_subsingleton E)).iso
      (Functor.map_isZero (J.overPullback AddCommGrpCat.{max u v w} U)
        (isZero_zero (Sheaf J AddCommGrpCat.{max u v w})))

/-- Being a finite locally constant sheaf of abelian groups, as a property of objects of
`Sh(C, Ab)`. -/
def isFiniteLocallyConstantAbelianSheaf :
    ObjectProperty (Sheaf J AddCommGrpCat.{max u v w}) :=
  fun F ↦ IsFiniteLocallyConstant J F

/-- **Stacks Tag 093U (2).** On a site, the finite locally constant sheaves of abelian groups form
a weak Serre subcategory of the category of all abelian sheaves.

The clause proved here is part (2). It is not an instance of part (3),
`Stacks.ConstantSheaf.isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf`: there the
finiteness is finiteness of type over a Noetherian coefficient ring, here it is finiteness of the
local value itself. Part (3) over `ℤ` is however what the proof reduces to, together with the
local annihilation invariant `Stacks.ConstantSheaf.IsLocallyAnnihilated`. -/
@[stacks 093U "finite_abelian", sga "4 IX 2.1" "(ii) ker/coker, (iii)"]
theorem isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf :
    (isFiniteLocallyConstantAbelianSheaf.{v, u, w} J).IsWeakSerreClass := by
  apply (ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact _).2
  refine ⟨⟨0, isFiniteLocallyConstant_zero J⟩, ?_⟩
  intro S hS h₀ h₁ h₃ h₄
  have := intSheaf_isEquivalence.{v, u, w} J
  have : (intSheaf.{v, u, w} J).Additive := Functor.additive_of_preserves_binary_products _
  apply isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf J (S.obj' 2)
  · let P : ObjectProperty (Sheaf J (ModuleCat.{max u v w} ℤ)) :=
      IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J ℤ
    have : P.IsWeakSerreClass :=
      isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J ℤ
    exact P.prop_obj₂_of_exact ((intSheaf.{v, u, w} J).mapComposableArrows 4 |>.obj S)
      (mapComposableArrows_exact (intSheaf.{v, u, w} J) S hS)
      (isFiniteTypeLocallyConstantModuleSheaf_intSheaf J _ h₀)
      (isFiniteTypeLocallyConstantModuleSheaf_intSheaf J _ h₁)
      (isFiniteTypeLocallyConstantModuleSheaf_intSheaf J _ h₃)
      (isFiniteTypeLocallyConstantModuleSheaf_intSheaf J _ h₄)
  · exact isLocallyAnnihilated_of_exact J (hS.sc' 1 2 3) (hS.exact' 1 2 3)
      (isLocallyAnnihilated_of_isFiniteLocallyConstant J _ h₁)
      (isLocallyAnnihilated_of_isFiniteLocallyConstant J _ h₃)

end Main

end Stacks.ConstantSheaf

end
