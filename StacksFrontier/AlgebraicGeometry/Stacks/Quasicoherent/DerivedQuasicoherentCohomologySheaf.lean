module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomologyPrimed
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatGroupoidPresentationCoherator

/-!
# The cohomology functors of Stacks 07B7 on the faithful `D_QCoh(𝒪_𝒳)`

This file first proves the formal part of **Stacks 07B7** for an arbitrary Verdier quotient of
the shape of **Stacks 07B6**: for a weak Serre subcategory `L` of an abelian category `𝒜` whose
derived category `D_L(𝒜)` is triangulated, a weak Serre subcategory `P` of `𝒜`, and a functor
`Q : L ⥤ 𝒞` to an abelian category whose kernel is `P ∩ L` and with `Q ∘ H^i` homological, the
functor `Q ∘ H^i` descends to the Verdier quotient `D_L(𝒜) / D_{P ∩ L}(𝒜)`; the descended functor
is cohomological, and an object of the quotient is zero exactly when all its `H^i` vanish.

## Main definitions

* `DerivedCategoryB.quotientW`: the morphisms of `D_L(𝒜)` whose cone lies in `D_{P ∩ L}(𝒜)`.
* `DerivedCategoryB.quotientCohomology`: the descended functor `H^i`.
* `DerivedCategoryB.quotientCohomologyFac`: its defining identity `H^i ∘ (quotient) ≅ Q ∘ H^i`.

## Main results

* `DerivedCategoryB.quotientW_eq_trW`: the inverted class is the one attached to the subcategory
  of `D_L(𝒜)` of complexes with cohomology in `P`.
* `DerivedCategoryB.isHomological_quotientCohomology`: the descended functor is cohomological.
* `DerivedCategoryB.isZero_iff_forall_isZero_quotientCohomology`: an object of the quotient is
  zero exactly when all its `H^i` vanish.

## For an algebraic stack

With `𝒜 = Mod(𝒪_𝒳)` the modules on the fppf site of an algebraic stack `𝒳`,
`L = LQCoh^fbc(𝒪_𝒳)` read on sheaves of modules as in the source (a weak Serre subcategory,
Stacks 0771), `P` the parasitic modules and `Q` the coherator of Stacks 0778
(`AlgebraicGeometry.Stack.FlatGroupoidPresentation.flatBaseChangeCoherator`, exact with kernel
`Parasitic ∩ LQCoh^fbc` by Stacks 0779), this gives:

* `AlgebraicGeometry.Stack.derivedCategoryQuasicoherentSheaf`: **Stacks 07B6**,
  `D_QCoh(𝒪_𝒳) = D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.cohomologyDerivedCategoryQuasicoherentSheaf`,
  `…Fac`, `AlgebraicGeometry.Stack.isHomological_cohomologyDerivedCategoryQuasicoherentSheaf` and
  `AlgebraicGeometry.Stack.isZero_iff_forall_isZero_cohomologyDerivedCategoryQuasicoherentSheaf`:
  **Stacks 07B7**, the cohomological functor `H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` and the vanishing
  criterion `E = 0 ↔ ∀ i, H^i(E) = 0`.

The only binder is `HasDerivedCategory.{t} Mod(𝒪_𝒳)`, the choice of a universe for the
derived category, as for the other derived categories of the library.

## References

* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07B7](https://stacks.math.columbia.edu/tag/07B7)
* [Stacks Project, Tag 05RJ](https://stacks.math.columbia.edu/tag/05RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe t u w

namespace DerivedCategoryB

section Quotient

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory.{t} 𝒜]
  (L P : ObjectProperty 𝒜) [L.IsWeakSerreClass] [P.IsWeakSerreClass]

/-- The subcategory of `D_L(𝒜)` of the complexes whose cohomology lies in `P`, which is
`D_{P ∩ L}(𝒜)` read inside `D_L(𝒜)`. -/
abbrev quotientSubcategory : ObjectProperty (derivedCategoryB L).FullSubcategory :=
  (derivedCategoryB P).inverseImage (derivedCategoryB L).ι

/-- **The morphisms the Verdier quotient `D_L(𝒜) / D_{P ∩ L}(𝒜)` inverts**: those whose cone,
taken in `D(𝒜)`, lies in `D_{P ∩ L}(𝒜)`. -/
abbrev quotientW : MorphismProperty (derivedCategoryB L).FullSubcategory :=
  MorphismProperty.inverseImage (derivedCategoryB (P ⊓ L)).trW (derivedCategoryB L).ι

/-- The subcategory `D_{P ∩ L}(𝒜)` of `D(𝒜)` is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_derivedCategoryB_inf :
    (derivedCategoryB (P ⊓ L)).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_derivedCategoryB _

/-- The subcategory `D_P(𝒜)` of `D(𝒜)` is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_derivedCategoryB_weakSerre :
    (derivedCategoryB P).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_derivedCategoryB _

/-- For a weak Serre subcategory `P`, the subcategory `D_P(𝒜)` of `D(𝒜)` is triangulated. -/
instance isTriangulated_derivedCategoryB_weakSerre :
    (derivedCategoryB P).IsTriangulated :=
  derivedCategoryB_isTriangulated _ (WeakSerre.isWeakSerre_of_isWeakSerreClass _)

/-- **The inverted class is the class attached to a triangulated subcategory of `D_L(𝒜)`.**
`D_L(𝒜)` is a triangulated subcategory of `D(𝒜)` by **Stacks 06UQ**, `L` being a weak Serre
subcategory. A cone in `D(𝒜)` of a morphism of the triangulated subcategory `D_L(𝒜)` is a cone in
`D_L(𝒜)`, and inside `D_L(𝒜)` having cohomology in `P ∩ L` is having cohomology in `P`. -/
theorem quotientW_eq_trW : quotientW L P = (quotientSubcategory L P).trW := by
  have hinv : (derivedCategoryB (P ⊓ L)).inverseImage (derivedCategoryB L).ι =
      quotientSubcategory L P := by
    ext X
    simp only [ObjectProperty.prop_inverseImage_iff]
    exact ⟨fun hX n => (hX n).1, fun hX n => ⟨hX n, X.property n⟩⟩
  ext X Y f
  rw [← hinv]
  exact ((derivedCategoryB (P ⊓ L)).inverseImage_trW_iff (derivedCategoryB L).ι f).symm

/-- The class `quotientW L P` is compatible with the triangulation of `D_L(𝒜)`. -/
instance isCompatibleWithTriangulation_quotientW :
    (quotientW L P).IsCompatibleWithTriangulation := by
  rw [quotientW_eq_trW]
  infer_instance

/-- The class `quotientW L P` admits a left calculus of fractions. -/
instance hasLeftCalculusOfFractions_quotientW :
    (quotientW L P).HasLeftCalculusOfFractions := by
  rw [quotientW_eq_trW]
  infer_instance

/-- The localization functor of `quotientW L P` is a localization with respect to the class
`(quotientSubcategory L P).trW`. -/
instance isLocalization_quotientW_Q :
    (quotientW L P).Q.IsLocalization (quotientSubcategory L P).trW := by
  rw [← quotientW_eq_trW]
  infer_instance

section Cohomology

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] (Q : L.FullSubcategory ⥤ 𝒞)

/-- **`Q ∘ H^i : D_L(𝒜) ⟶ 𝒞`**, the functor the Verdier quotient descends. -/
abbrev cohomologyComp (i : ℤ) : (derivedCategoryB L).FullSubcategory ⥤ 𝒞 :=
  homologyFunctorB L i ⋙ Q

/-- **`Q ∘ H^i` is homological when `Q` is exact**: `H^i : D_L(𝒜) ⟶ L` is homological and an
exact functor of abelian categories preserves exact sequences (**Stacks 05QZ** (2)). -/
theorem isHomological_cohomologyComp [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (i : ℤ) : (cohomologyComp L Q i).IsHomological :=
  have : Q.Additive := Q.additive_of_preserves_binary_products
  main_statement_comp_homological_exact (homologyFunctorB L i) Q

/-- The subcategory divided by lies in the homological kernel of `Q ∘ H^i`. -/
private theorem quotientSubcategory_le_homologicalKernel (i : ℤ)
    [(cohomologyComp L Q i).IsHomological]
    (hQker : ∀ F : L.FullSubcategory, IsZero (Q.obj F) ↔ P F.obj) :
    quotientSubcategory L P ≤ (cohomologyComp L Q i).homologicalKernel :=
  fun X hX n => (hQker _).mpr (((quotientSubcategory L P).le_shift n X hX) i)

/-- **`Q ∘ H^i` inverts the morphisms the Verdier quotient inverts**, when it is homological and
`Q` kills exactly the objects of `P`: the subcategory divided by lies in its homological kernel,
so the universal property of the Verdier quotient for homological functors (**Stacks 05RJ**)
applies. -/
theorem isInvertedBy_cohomologyComp (i : ℤ) [(cohomologyComp L Q i).IsHomological]
    (hQker : ∀ F : L.FullSubcategory, IsZero (Q.obj F) ↔ P F.obj) :
    (quotientW L P).IsInvertedBy (cohomologyComp L Q i) := by
  obtain ⟨H, fac, -, -⟩ := VerdierQuotientUniversalProperty.homological_universal_property
    (quotientSubcategory L P) (cohomologyComp L Q i)
    (quotientSubcategory_le_homologicalKernel L P Q i hQker)
  rw [quotientW_eq_trW]
  refine (MorphismProperty.IsInvertedBy.iff_of_iso _ fac).mp (fun X Y f hf => ?_)
  have : IsIso ((quotientSubcategory L P).trW.Q.map f) := Localization.inverts _ _ f hf
  show IsIso (H.map ((quotientSubcategory L P).trW.Q.map f))
  infer_instance

/-- **The descended functor `H^i : D_L(𝒜) / D_{P ∩ L}(𝒜) ⟶ 𝒞`.** -/
def quotientCohomology (i : ℤ) [(cohomologyComp L Q i).IsHomological]
    (hQker : ∀ F : L.FullSubcategory, IsZero (Q.obj F) ↔ P F.obj) :
    (quotientW L P).Localization ⥤ 𝒞 :=
  Localization.lift (cohomologyComp L Q i) (isInvertedBy_cohomologyComp L P Q i hQker)
    (quotientW L P).Q

/-- **The defining identity `H^i ∘ (quotient functor) ≅ Q ∘ H^i`.** -/
def quotientCohomologyFac (i : ℤ) [(cohomologyComp L Q i).IsHomological]
    (hQker : ∀ F : L.FullSubcategory, IsZero (Q.obj F) ↔ P F.obj) :
    (quotientW L P).Q ⋙ quotientCohomology L P Q i hQker ≅ cohomologyComp L Q i :=
  Localization.fac _ _ _

/-- **The descended `H^i` is cohomological**: the quotient functor is a triangulated
localization, essentially surjective on arrows, and its composite with `H^i` is `Q ∘ H^i`. -/
theorem isHomological_quotientCohomology (i : ℤ) [(cohomologyComp L Q i).IsHomological]
    (hQker : ∀ F : L.FullSubcategory, IsZero (Q.obj F) ↔ P F.obj) :
    (quotientCohomology L P Q i hQker).IsHomological :=
  have : (quotientW L P).Q.mapArrow.EssSurj := Localization.essSurj_mapArrow _ (quotientW L P)
  Functor.isHomological_of_localization (quotientW L P).Q (quotientCohomology L P Q i hQker)
    (cohomologyComp L Q i) (quotientCohomologyFac L P Q i hQker)

/-- The descended functor is unique up to a unique isomorphism compatible with the defining
identity. -/
theorem quotientCohomology_uniq (i : ℤ) [(cohomologyComp L Q i).IsHomological]
    (hQker : ∀ F : L.FullSubcategory, IsZero (Q.obj F) ↔ P F.obj)
    (G : (quotientW L P).Localization ⥤ 𝒞) (α : (quotientW L P).Q ⋙ G ≅ cohomologyComp L Q i) :
    ∃! e : G ≅ quotientCohomology L P Q i hQker,
      Functor.whiskerLeft (quotientW L P).Q e.hom ≫
        (quotientCohomologyFac L P Q i hQker).hom = α.hom :=
  Localization.existsUnique_isoLift _ _ _ _ G α

/-- **An object of the quotient is zero exactly when all its `H^i` vanish.**  Choose a lift `Y`
to `D_L(𝒜)`; the vanishing of all `Q(H^i(Y))` is `Y` having cohomology in `P`, which is `Y`
lying in the subcategory divided by, and the kernel of the quotient functor is the least strictly
full saturated triangulated subcategory containing it (**Stacks 05RK**). -/
theorem isZero_iff_forall_isZero_quotientCohomology
    [∀ i, (cohomologyComp L Q i).IsHomological]
    (hQker : ∀ F : L.FullSubcategory, IsZero (Q.obj F) ↔ P F.obj)
    (X : (quotientW L P).Localization) :
    IsZero X ↔ ∀ i : ℤ, IsZero ((quotientCohomology L P Q i hQker).obj X) := by
  obtain ⟨-, hleast⟩ :=
    (quotientSubcategory L P).kernel_iff_exists_isoClosure_biprod_and_isLeast_kernel
      (quotientW L P).Q
  obtain ⟨Y, ⟨e⟩⟩ : ∃ Y, Nonempty ((quotientW L P).Q.obj Y ≅ X) :=
    ⟨_, ⟨(quotientW L P).Q.objObjPreimageIso X⟩⟩
  have hzero : IsZero X ↔ IsZero ((quotientW L P).Q.obj Y) :=
    ⟨fun hz => hz.of_iso e, fun hz => hz.of_iso e.symm⟩
  have hdeg : ∀ i : ℤ, IsZero ((quotientCohomology L P Q i hQker).obj X) ↔
      IsZero ((cohomologyComp L Q i).obj Y) := by
    intro i
    have ei := ((quotientCohomology L P Q i hQker).mapIso e.symm).trans
      ((quotientCohomologyFac L P Q i hQker).app Y)
    exact ⟨fun hz => hz.of_iso ei.symm, fun hz => hz.of_iso ei⟩
  rw [hzero]
  constructor
  · intro hz i
    rw [hdeg i]
    obtain ⟨htri, hsat⟩ := Functor.isTriangulated_and_isSaturated_homologicalKernel
      (cohomologyComp L Q i)
    have hsub : (cohomologyComp L Q i).homologicalKernel ∈
        {P' : ObjectProperty (derivedCategoryB L).FullSubcategory |
          P'.IsClosedUnderIsomorphisms ∧ P'.IsTriangulated ∧ P'.IsSaturated ∧
            quotientSubcategory L P ≤ P'} :=
      ⟨inferInstance, htri, hsat, quotientSubcategory_le_homologicalKernel L P Q i hQker⟩
    have hmem := hleast.2 hsub Y hz
    exact (hmem 0).of_iso ((cohomologyComp L Q i).mapIso ((shiftFunctorZero _ ℤ).app Y).symm)
  · intro hz
    exact hleast.1.2.2.2 Y fun i => (hQker _).mp ((hdeg i).mp (hz i))

end Cohomology

end Quotient

end DerivedCategoryB

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]

/-- **Stacks 07B6**, at the source's `LQCoh^fbc(𝒪_𝒳)`: the derived category with
quasi-coherent cohomology `D_QCoh(𝒪_𝒳) = D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`,
the Verdier quotient of the triangulated subcategory of complexes of `𝒪_𝒳`-modules with
cohomology in `LQCoh^fbc(𝒪_𝒳)` (a weak Serre subcategory, Stacks 0771) by the one with
cohomology in the parasitic modules of `LQCoh^fbc(𝒪_𝒳)`. -/
@[stacks 07B6 "the Verdier quotient D_QCoh(𝒪_𝒳) = D_LQCoh^fbc(𝒪_𝒳) / D_(Parasitic ∩ \
  LQCoh^fbc)(𝒪_𝒳), with the flat base change property of LQCoh^fbc read on sheaves of modules \
  as in the source"]
abbrev derivedCategoryQuasicoherentSheaf :=
  (DerivedCategoryB.quotientW (lqcFbcFppf B S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)).Localization

/-- **Stacks 07B6**, at the source's `LQCoh^fbc(𝒪_𝒳)`: the quotient functor. -/
@[stacks 07B6 "the quotient functor D_LQCoh^fbc(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳), with the flat base change \
  property read on sheaves of modules as in the source"]
abbrev toDerivedCategoryQuasicoherentSheaf :
    (DerivedCategoryB.derivedCategoryB (lqcFbcFppf B S hS 𝒳)).FullSubcategory ⥤
      derivedCategoryQuasicoherentSheaf B S hS 𝒳 :=
  (DerivedCategoryB.quotientW (lqcFbcFppf B S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)).Q

section Cohomology

/-- The coherator `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of Stacks 0778 is left exact, being a right
adjoint. -/
instance preservesFiniteLimits_flatBaseChangeCoherator :
    PreservesFiniteLimits (flatGroupoidPresentation 𝒳).flatBaseChangeCoherator :=
  have := (flatGroupoidPresentation 𝒳).flatBaseChangeCoheratorAdjunction.isRightAdjoint
  inferInstance

/-- The coherator of Stacks 0778 is right exact (Stacks 0779 (3)). -/
instance preservesFiniteColimits_flatBaseChangeCoherator :
    PreservesFiniteColimits (flatGroupoidPresentation 𝒳).flatBaseChangeCoherator :=
  (flatGroupoidPresentation 𝒳).preservesFiniteColimits_flatBaseChangeCoherator

/-- The composite `Q ∘ H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)`, with `Q` the coherator, is a
homological functor. -/
instance isHomological_cohomologyComp_flatBaseChangeCoherator (i : ℤ) :
    (DerivedCategoryB.cohomologyComp (lqcFbcFppf B S hS 𝒳)
      (flatGroupoidPresentation 𝒳).flatBaseChangeCoherator i).IsHomological :=
  DerivedCategoryB.isHomological_cohomologyComp _ _ i

/-- **Stacks 07B7**: the cohomological functor `H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)`, the functor
`Q ∘ H^i : D_{LQCoh^fbc}(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` descended to the Verdier quotient (Stacks 05RJ),
`Q` being the coherator of Stacks 0778, which annihilates
`Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` (Stacks 0779). -/
@[stacks 07B7 "the cohomology functor H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳), descended from Q ∘ H^i \
  with Q the coherator of 0778"]
def cohomologyDerivedCategoryQuasicoherentSheaf (i : ℤ) :
    derivedCategoryQuasicoherentSheaf B S hS 𝒳 ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  DerivedCategoryB.quotientCohomology _ _ _ i
    FlatGroupoidPresentation.isZero_flatBaseChangeCoherator_obj_iff_parasitic

/-- **Stacks 07B7**: the defining identity `H^i ∘ (quotient functor) ≅ Q ∘ H^i`. -/
@[stacks 07B7 "the identity H^i ∘ (quotient functor) = Q ∘ H^i defining the cohomology functor"]
def cohomologyDerivedCategoryQuasicoherentSheafFac (i : ℤ) :
    toDerivedCategoryQuasicoherentSheaf B S hS 𝒳 ⋙
        cohomologyDerivedCategoryQuasicoherentSheaf B S hS 𝒳 i ≅
      DerivedCategoryB.cohomologyComp (lqcFbcFppf B S hS 𝒳)
        (flatGroupoidPresentation 𝒳).flatBaseChangeCoherator i :=
  DerivedCategoryB.quotientCohomologyFac _ _ _ i
    FlatGroupoidPresentation.isZero_flatBaseChangeCoherator_obj_iff_parasitic

/-- **Stacks 07B7**: `H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` is a cohomological functor. -/
@[stacks 07B7 "the descended H^i : D_QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳) is a cohomological functor"]
theorem isHomological_cohomologyDerivedCategoryQuasicoherentSheaf (i : ℤ) :
    (cohomologyDerivedCategoryQuasicoherentSheaf B S hS 𝒳 i).IsHomological :=
  DerivedCategoryB.isHomological_quotientCohomology _ _ _ i
    FlatGroupoidPresentation.isZero_flatBaseChangeCoherator_obj_iff_parasitic

/-- **Stacks 07B7**: an object `E` of `D_QCoh(𝒪_𝒳)` is zero exactly when `H^i(E) = 0` for all
`i`, the kernel of `Q` being exactly `Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` (Stacks 0779 (1)). -/
@[stacks 07B7 "E is zero in D_QCoh(𝒪_𝒳) if and only if H^i(E) = 0 for every i"]
theorem isZero_iff_forall_isZero_cohomologyDerivedCategoryQuasicoherentSheaf
    (X : derivedCategoryQuasicoherentSheaf B S hS 𝒳) :
    IsZero X ↔ ∀ i : ℤ,
      IsZero ((cohomologyDerivedCategoryQuasicoherentSheaf B S hS 𝒳 i).obj X) :=
  DerivedCategoryB.isZero_iff_forall_isZero_quotientCohomology _ _ _
    FlatGroupoidPresentation.isZero_flatBaseChangeCoherator_obj_iff_parasitic X

end Cohomology

end AlgebraicGeometry.Stack
