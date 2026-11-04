module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoCancellations
public import StacksFrontier.CategoryTheory.Shift.Mates
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitForgetModuleStructure

/-!
# The comparison of derived lower shriek at module and at abelian coefficients

Let `C` be a small category carrying the chaotic topology and let `B` be a ring, so that lower
shriek is the colimit over `Cᵒᵖ` (Tag 08PF) and its total left derived functor is
`Stacks.CategoryHomology.totalDerivedColimit`, available both at module coefficients
`ModuleCat B` and at abelian coefficients. Write `Ψ` for the functor applying `Mod(B) ⥤ Ab` to
the values of a diagram (`Stacks.ChaoticSite.forgetModuleDiagrams`) and `Φ` for `Mod(B) ⥤ Ab`
itself. This file builds the canonical comparison

`Lπ_!(Ψ K) ⟶ Φ(Lπ_!(K))`,

natural in `K ∈ D(Cᵒᵖ ⥤ Mod(B))`, with no hypothesis on `C` whatsoever, and pins it against the
*underived* comparison `colim(Ψ F) ⟶ Φ(colim F)` of `CategoryTheory.Limits.colimit.post`.

Its invertibility, which needs a cosimplicial point resolution, is
`Stacks.ChaoticSite.isIso_derivedColimitForgetComparison` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedColimitForgetNatIso.lean`.

## Main definitions

* `Stacks.ChaoticSite.diagramColimitForgetPost`: the underived comparison
  `Ψ ⋙ colim ⟶ colim ⋙ Φ`, degreewise `CategoryTheory.Limits.colimit.post`.
* `Stacks.ChaoticSite.derivedConstForgetIso`: the identification
  `π^{-1} ⋙ Ψ ≅ Φ ⋙ π^{-1}` of the two derived inverse images of the constant diagram.
* `Stacks.ChaoticSite.derivedColimitForgetComparison`: the comparison
  `Lπ_!(Ψ K) ⟶ Φ(Lπ_!(K))` on the unbounded derived category, as the mate of that
  identification.

## Main results

* `Stacks.ChaoticSite.commShift_derivedColimitForgetComparison`: the comparison is compatible
  with the shift, the first of the inputs a dévissage along compact generators needs.
* `Stacks.ChaoticSite.colimitPost_colimConstAdj_unit` and its two degreewise forms: `Ψ` carries
  the unit of `colim ⊣ const` to the unit of `colim ⊣ const`, corrected by the underived
  comparison. This is the only thing the pinning uses about the underived comparison.
* `Stacks.ChaoticSite.derivedColimitForgetComparison_app_comp_counit`: the comparison at an
  object coming from the homotopy category, followed by the comparison of `Lπ_!` with `π_!` at
  module coefficients, is the underived comparison read after the comparison of `Lπ_!` with
  `π_!` at abelian coefficients. This is what turns the invertibility of the comparison into the
  invertibility of those three.

## Implementation notes

`π^{-1} ⋙ Ψ = Φ ⋙ π^{-1}` holds **on the nose** — a constant diagram with `Mod(B) ⥤ Ab`
applied to its values is the constant diagram at the underlying abelian group, with the same
identity morphisms — which is what
`Stacks.ChaoticSite.const_comp_diagramForget` records. The identification of the derived functors
is therefore two applications of `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`
across that equality, and the comparison is the mate of it across the two derived adjunctions
`Lπ_! ⊣ π^{-1}` of `Stacks.CategoryHomology.totalDerivedColimitAdjunction`. Being a mate it is
shift-compatible by `CategoryTheory.NatTrans.commShift_mateEquiv_symm`.

The two spellings of the middle functor — `π^{-1} ⋙ Ψ` and `Φ ⋙ π^{-1}` — are definitionally
equal and syntactically distinct, so a composite whose consecutive factors use different ones is
well typed and yet invisible to the keyed matching of `rw` and `simp`, which also refuse to build
one. The two transposes of the pinning identity are therefore assembled by
`Stacks.ChaoticSite.shuffleA` and `Stacks.ChaoticSite.shuffleB`, which state the bookkeeping at
variables, where no spelling survives; the same device is
`Stacks.DerivedCategoryComparisons.pinning_aux` for the value of the identification at a complex.
`Stacks.ChaoticSite.forgetConstCompIso` is the second composition comparison stated at the first
spelling of its source, which is what lets instance search find the shift-compatibility of the
composite.

## References

* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ChaoticSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

open Stacks.CategoryHomology

variable (C : Type u) [SmallCategory C] (B : Type u) [Ring B]

/-- **The underived comparison `colim(Ψ F) ⟶ Φ(colim F)`**, as a natural transformation
`Ψ ⋙ colim ⟶ colim ⋙ Φ`. Degreewise it is `CategoryTheory.Limits.colimit.post`, whose
naturality is `CategoryTheory.Limits.colimit.map_post`. It is invertible exactly when the
forgetful functor preserves the colimit over `Cᵒᵖ`, which it does, being a right adjoint. -/
def diagramColimitForgetPost :
    forgetModuleDiagrams (C := C) (B := B) ⋙
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) ⟶
      (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B) ⋙
        forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u} where
  app F := colimit.post F (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})
  naturality _ _ α := (colimit.map_post α (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})).symm

/-- **The constant diagram of the underlying abelian group of a `B`-module is the underlying
abelian diagram of the constant diagram**, on the nose: both send an object of `Cᵒᵖ` to the
underlying abelian group and every morphism to the identity. This is the datum of Tag 08PH
saying that `Ψ ∘ π^{-1} = π^{-1} ∘ Φ`. -/
lemma const_comp_diagramForget :
    (Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _) ⋙ forgetModuleDiagrams (C := C) (B := B) =
      forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u} ⋙ (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _) :=
  rfl

/-- The composition comparison for `forget₂` then the constant diagram, read at the source
spelling `(const ⋙ forgetModuleDiagrams)`: the two underived composites are equal by
`Stacks.ChaoticSite.const_comp_diagramForget`. -/
def forgetConstCompIso :
    ((Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _) ⋙
        forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory ≅
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory ⋙
        (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}) (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _)

/-- The isomorphism `Stacks.ChaoticSite.forgetConstCompIso` commutes with the shift by `ℤ`. -/
instance commShift_forgetConstCompIso :
    NatTrans.CommShift (forgetConstCompIso C B).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})
      (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _)).hom ℤ)

/-- **The identification `π^{-1} ⋙ Ψ ≅ Φ ⋙ π^{-1}` of the derived inverse images of the constant
diagram.** The two underived functors are equal by
`Stacks.ChaoticSite.const_comp_diagramForget`, and all four are exact, so the only thing to spend
is the comparison of the degreewise action of a composite with the composite of the degreewise
actions, twice. -/
def derivedConstForgetIso :
    (Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _).mapDerivedCategory ⋙
        (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory ≅
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory ⋙
        (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _) (forgetModuleDiagrams (C := C) (B := B))).symm ≪≫
    forgetConstCompIso C B

/-- The identification of the derived constant diagrams is compatible with the shift, each of
its two factors being. -/
instance commShift_derivedConstForgetIso :
    NatTrans.CommShift (derivedConstForgetIso C B).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _) (forgetModuleDiagrams (C := C) (B := B))).inv ≫
      (forgetConstCompIso C B).hom) ℤ)

/-- **The comparison `Lπ_!(Ψ K) ⟶ Φ(Lπ_!(K))` on the unbounded derived category.** Both derived
lower shrieks are left adjoints, with the derived constant diagrams as right adjoints
(`Stacks.CategoryHomology.totalDerivedColimitAdjunction`); this is the mate of the identification
`Stacks.ChaoticSite.derivedConstForgetIso` of those right adjoints. No hypothesis on `C` is
used: the comparison exists always, and it is its invertibility that needs a cosimplicial point
resolution. -/
def derivedColimitForgetComparison :
    (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory ⋙
        totalDerivedColimit C AddCommGrpCat.{u} ⟶
      totalDerivedColimit C (ModuleCat.{u} B) ⋙
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory :=
  ((mateEquiv (totalDerivedColimitAdjunction C (ModuleCat.{u} B))
      (totalDerivedColimitAdjunction C AddCommGrpCat.{u})).symm
    (TwoSquare.mk _ _ _ _ (derivedConstForgetIso C B).hom)).natTrans

/-- **The comparison is compatible with the shift.** Both derived adjunctions are, being
adjunctions whose right adjoint commutes with the shift, and the identification of the derived
constant diagrams is by `Stacks.ChaoticSite.commShift_derivedConstForgetIso`; so
`CategoryTheory.NatTrans.commShift_mateEquiv_symm` applies to the mate. -/
instance commShift_derivedColimitForgetComparison :
    NatTrans.CommShift (derivedColimitForgetComparison C B) ℤ := by
  let : (totalDerivedColimitAdjunction C (ModuleCat.{u} B)).CommShift ℤ :=
    (totalDerivedColimitAdjunction C (ModuleCat.{u} B)).commShift_of_rightAdjoint ℤ
  let : (totalDerivedColimitAdjunction C AddCommGrpCat.{u}).CommShift ℤ :=
    (totalDerivedColimitAdjunction C AddCommGrpCat.{u}).commShift_of_rightAdjoint ℤ
  rw [derivedColimitForgetComparison]
  infer_instance

/-- **The identity that pins the comparison down.** Its transpose along `Lπ_! ⊣ π^{-1}` at
abelian coefficients is `Ψ` applied to the unit of `Lπ_! ⊣ π^{-1}` at module coefficients,
followed by the identification of the derived constant diagrams. Being a mate, it is the unique
morphism with that property. -/
lemma unit_comp_derivedConstForgetIso (K : DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{u} B)) :
    (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.map
          ((totalDerivedColimitAdjunction C (ModuleCat.{u} B)).unit.app K) ≫
        (derivedConstForgetIso C B).hom.app ((totalDerivedColimit C (ModuleCat.{u} B)).obj K) =
      (totalDerivedColimitAdjunction C AddCommGrpCat.{u}).unit.app
          ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.obj K) ≫
        (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategory.map
          ((derivedColimitForgetComparison C B).app K) := by
  simp [derivedColimitForgetComparison]

/-! ### The underived input -/

/-- **`Ψ` carries the unit of `colim ⊣ const` to the unit of `colim ⊣ const`, corrected by the
underived comparison.** At an object `V` of `Cᵒᵖ` the left side is the forgetful functor applied
to the colimit injection and the right side is the colimit injection of the underlying abelian
diagram followed by `CategoryTheory.Limits.colimit.post`, so this is
`CategoryTheory.Limits.colimit.ι_post`. -/
theorem colimitPost_colimConstAdj_unit (F : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    (forgetModuleDiagrams (C := C) (B := B)).map
        ((colimConstAdj : (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ _) ⊣
          Functor.const Cᵒᵖ).unit.app F) =
      (colimConstAdj : (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ _) ⊣
            Functor.const Cᵒᵖ).unit.app ((forgetModuleDiagrams (C := C) (B := B)).obj F) ≫
        (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).map
          ((diagramColimitForgetPost C B).app F) :=
  NatTrans.ext (funext fun V ↦
    (colimit.ι_post F (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}) V).symm)

/-- **`Stacks.ChaoticSite.colimitPost_colimConstAdj_unit` read degreewise on cochain
complexes.** Both sides are degreewise, so this is the statement at a single diagram applied in
each degree. -/
theorem colimitPost_colimConstAdj_unit_mapHomologicalComplex
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) :
    ((forgetModuleDiagrams (C := C) (B := B)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (colimConstAdj : (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ _) ⊣
            Functor.const Cᵒᵖ).unit (ComplexShape.up ℤ)).app K) =
      (NatTrans.mapHomologicalComplex
            (colimConstAdj : (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ _) ⊣
              Functor.const Cᵒᵖ).unit (ComplexShape.up ℤ)).app
          (((forgetModuleDiagrams (C := C) (B := B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
        ((Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (diagramColimitForgetPost C B)
            (ComplexShape.up ℤ)).app K) :=
  HomologicalComplex.hom_ext _ _ fun i ↦ colimitPost_colimConstAdj_unit C B (K.X i)

/-- **`Stacks.ChaoticSite.colimitPost_colimConstAdj_unit` read on homotopy categories.** The
unit of `CategoryTheory.Adjunction.mapHomotopyCategory` is the quotient of the degreewise unit,
and so is the action of `Ψ` on a quotient, so this is the previous statement under
`HomotopyCategory.quotient`. -/
theorem colimitPost_colimConstAdj_unit_mapHomotopyCategory
    (X : HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ)) :
    ((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((colimConstAdj : (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ _) ⊣
          Functor.const Cᵒᵖ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X) =
      ((colimConstAdj : (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ _) ⊣
              Functor.const Cᵒᵖ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
          (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X) ≫
        ((Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapHomotopyCategory
            (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (diagramColimitForgetPost C B)
              (ComplexShape.up ℤ)).app X.as)) :=
  (congrArg (HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ)).map
      (colimitPost_colimConstAdj_unit_mapHomologicalComplex C B X.as)).trans
    ((HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ)).map_comp _ _)

/-! ### The value of the identification at a complex -/

/-- **The value of the identification of the derived constant diagrams at a complex.** Preceded
by `Ψ` applied to the inverse of the comparison of `π^{-1}` with `DerivedCategory.Qh` at module
coefficients and followed by `π^{-1}` of the comparison for `Φ`, the identification is the
comparison of `Ψ` with `DerivedCategory.Qh` followed by the inverse of the comparison of
`π^{-1}` with it at abelian coefficients: the two factors coming from the middle functor cancel,
being the two directions of one isomorphism read at its two spellings. -/
theorem derivedConstForgetIso_hom_app_Qh
    (Z : HomotopyCategory (ModuleCat.{u} B) (ComplexShape.up ℤ)) :
    (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.map
          ((Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _).mapDerivedCategoryFactorsh.inv.app Z) ≫
        (derivedConstForgetIso C B).hom.app (DerivedCategory.Qh.obj Z) ≫
          (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategory.map
            ((forget₂ (ModuleCat.{u} B)
              AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.hom.app Z) =
      (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.hom.app
          (((Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj Z) ≫
        (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategoryFactorsh.inv.app
          (((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj Z) :=
  Stacks.DerivedCategoryComparisons.pinning_aux
    (a := (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.map
      ((Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _).mapDerivedCategoryFactorsh.inv.app Z))
    (ei := (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _)
      (forgetModuleDiagrams (C := C) (B := B))).inv.app (DerivedCategory.Qh.obj Z))
    (fh := (forgetConstCompIso C B).hom.app (DerivedCategory.Qh.obj Z))
    (ef := (derivedConstForgetIso C B).hom.app (DerivedCategory.Qh.obj Z))
    (p := (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategory.map
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.hom.app Z))
    (q := (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategoryFactorsh.hom.app
      (((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj Z))
    (qi := (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategoryFactorsh.inv.app
      (((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj Z))
    (b := (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.hom.app
      (((Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj Z))
    (r := ((Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _) ⋙
      forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.inv.app Z)
    (r' := (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u} ⋙
      (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _)).mapDerivedCategoryFactorsh.hom.app Z)
    rfl
    (Stacks.DerivedCategoryComparisons.map_factorsh_inv_comp_compIso_inv_app_Qh
      (Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _) (forgetModuleDiagrams (C := C) (B := B)) Z)
    (Stacks.DerivedCategoryComparisons.compIso_hom_comp_factorsh_app_Qh
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})
      (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _) Z)
    (((Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _) ⋙
      forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.inv_hom_id_app Z)
    (Iso.hom_inv_id_app _ _)

/-! ### The two transposes, as bookkeeping at variables -/

section Shuffle

variable {D : Type*} [Category D]

/-- The chain of five identities that computes the transpose of the comparison, followed by the
two derived-functor comparisons. Stated at variables: in the application the endpoints of some
consecutive factors are definitionally equal but syntactically distinct spellings of one object,
which makes the composites invisible to `rw` and `simp`. -/
private theorem shuffleA {A X Y Z W T V N M M₂ : D}
    (u : A ⟶ X) (s : X ⟶ Y) (c : Y ⟶ Z) (f : Z ⟶ W)
    (pe : A ⟶ T) (al : T ⟶ Y) (pc : T ⟶ V) (al' : V ⟶ Z)
    (pq : A ⟶ N) (pk : N ⟶ V) (b : N ⟶ M) (qi : M ⟶ W) (bb : A ⟶ M₂) (g : M₂ ⟶ M)
    (n1 : u ≫ s = pe ≫ al) (n2 : al ≫ c = pc ≫ al') (n3 : pe ≫ pc = pq ≫ pk)
    (n4 : pk ≫ al' ≫ f = b ≫ qi) (n5 : pq ≫ b = bb ≫ g) :
    u ≫ s ≫ c ≫ f = bb ≫ g ≫ qi := by
  rw [reassoc_of% n1, reassoc_of% n2, reassoc_of% n3, n4, reassoc_of% n5]

/-- The chain of four identities that computes the transpose of the underived comparison, read
after the two derived-functor comparisons. Stated at variables, for the reason given at
`shuffleA`. -/
private theorem shuffleB {A X Y Z W M N P : D}
    (u : A ⟶ X) (a1 : X ⟶ Y) (a2 : Y ⟶ Z) (a3 : Z ⟶ W)
    (bb : A ⟶ M) (u2 : M ⟶ Y) (q1 : M ⟶ N) (ki : N ⟶ Z) (q2 : N ⟶ P) (qi : P ⟶ W) (g : M ⟶ P)
    (m1 : u ≫ a1 = bb ≫ u2) (m2 : u2 ≫ a2 = q1 ≫ ki) (m3 : ki ≫ a3 = q2 ≫ qi)
    (m4 : q1 ≫ q2 = g) :
    u ≫ a1 ≫ a2 ≫ a3 = bb ≫ g ≫ qi := by
  rw [reassoc_of% m1, reassoc_of% m2, m3, reassoc_of% m4]

end Shuffle

/-! ### The comparison, pinned against the underived comparison -/

private theorem unit_comp_map_derivedColimitForgetComparison_comp_counit
    (X : HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ)) :
    (totalDerivedColimitAdjunction C AddCommGrpCat.{u}).unit.app
          ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.obj
              (DerivedCategory.Qh.obj X)) ≫
        (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategory.map
          ((derivedColimitForgetComparison C B).app (DerivedCategory.Qh.obj X) ≫
            (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.map
                ((totalDerivedColimitCounit C (ModuleCat.{u} B)).app X) ≫
              (forget₂ (ModuleCat.{u} B)
                  AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.hom.app
                (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj X)) =
      (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map
            (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory (ComplexShape.up ℤ)).map
              (((colimConstAdj : (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ _) ⊣
                Functor.const Cᵒᵖ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X)) ≫
          (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategoryFactorsh.inv.app
            (((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj
              (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj X)) := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  refine shuffleA _ _ _ _
    ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.map
      ((totalDerivedColimitAdjunction C (ModuleCat.{u} B)).unit.app
        (DerivedCategory.Qh.obj X)))
    ((derivedConstForgetIso C B).hom.app
      ((totalDerivedColimit C (ModuleCat.{u} B)).obj (DerivedCategory.Qh.obj X)))
    ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.map
      ((Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _).mapDerivedCategory.map
        ((totalDerivedColimitCounit C (ModuleCat.{u} B)).app X)))
    ((derivedConstForgetIso C B).hom.app
      (DerivedCategory.Qh.obj
        (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj X)))
    ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.map
      (DerivedCategory.Qh.map
        (((colimConstAdj : (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ _) ⊣
          Functor.const Cᵒᵖ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X)))
    ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.map
      ((Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _).mapDerivedCategoryFactorsh.inv.app
        (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj X)))
    _ _ _ _
    (unit_comp_derivedConstForgetIso C B (DerivedCategory.Qh.obj X)).symm
    (((derivedConstForgetIso C B).hom.naturality
      ((totalDerivedColimitCounit C (ModuleCat.{u} B)).app X)).symm)
    (by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        totalDerivedColimitAdjunction_unit_app_comp_counit])
    (derivedConstForgetIso_hom_app_Qh C B
      (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj X))
    ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.hom.naturality
      (((colimConstAdj : (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ _) ⊣
        Functor.const Cᵒᵖ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X))

private theorem unit_comp_map_colimitForgetPost_counit
    (X : HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ)) :
    (totalDerivedColimitAdjunction C AddCommGrpCat.{u}).unit.app
          ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory.obj
              (DerivedCategory.Qh.obj X)) ≫
        (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategory.map
          ((totalDerivedColimit C AddCommGrpCat.{u}).map
              ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.hom.app X) ≫
            (totalDerivedColimitCounit C AddCommGrpCat.{u}).app
                (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory
                    (ComplexShape.up ℤ)).obj X) ≫
              DerivedCategory.Qh.map
                ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
                  ((NatTrans.mapHomologicalComplex (diagramColimitForgetPost C B)
                    (ComplexShape.up ℤ)).app X.as))) =
      (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map
            (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory (ComplexShape.up ℤ)).map
              (((colimConstAdj : (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ _) ⊣
                Functor.const Cᵒᵖ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X)) ≫
          (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategoryFactorsh.inv.app
            (((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj
              (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj X)) := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  refine shuffleB _ _ _ _ _
    ((totalDerivedColimitAdjunction C AddCommGrpCat.{u}).unit.app
      (DerivedCategory.Qh.obj
        (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj X)))
    (DerivedCategory.Qh.map
      (((colimConstAdj : (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ _) ⊣
          Functor.const Cᵒᵖ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj X)))
    ((Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategoryFactorsh.inv.app
      (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj
        (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj X)))
    (DerivedCategory.Qh.map
      (((Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapHomotopyCategory
        (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (diagramColimitForgetPost C B)
            (ComplexShape.up ℤ)).app X.as))))
    _ _
    (((totalDerivedColimitAdjunction C AddCommGrpCat.{u}).unit.naturality
      ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.hom.app X)).symm)
    (totalDerivedColimitAdjunction_unit_app_comp_counit C AddCommGrpCat.{u}
      (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory (ComplexShape.up ℤ)).obj X))
    (((Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _).mapDerivedCategoryFactorsh.inv.naturality
      ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (diagramColimitForgetPost C B)
          (ComplexShape.up ℤ)).app X.as))).symm)
    (by
      rw [← CategoryTheory.Functor.map_comp,
        ← colimitPost_colimConstAdj_unit_mapHomotopyCategory]
      rfl)

/-- **The comparison composed with the two derived-functor comparisons is the underived
comparison.** Both sides have the same transpose along `Lπ_! ⊣ π^{-1}` at abelian coefficients,
and the transpose is a bijection. -/
theorem derivedColimitForgetComparison_app_comp_counit
    (X : HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ)) :
    (derivedColimitForgetComparison C B).app (DerivedCategory.Qh.obj X) ≫
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.map
            ((totalDerivedColimitCounit C (ModuleCat.{u} B)).app X) ≫
          (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.hom.app
            (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X) =
      (totalDerivedColimit C AddCommGrpCat.{u}).map
          ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategoryFactorsh.hom.app X) ≫
        (totalDerivedColimitCounit C AddCommGrpCat.{u}).app
            (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
              ((NatTrans.mapHomologicalComplex (diagramColimitForgetPost C B)
                (ComplexShape.up ℤ)).app X.as)) :=
  ((totalDerivedColimitAdjunction C AddCommGrpCat.{u}).homEquiv _ _).injective
    ((unit_comp_map_derivedColimitForgetComparison_comp_counit C B X).trans
      (unit_comp_map_colimitForgetPost_counit C B X).symm)

end Stacks.ChaoticSite

end
