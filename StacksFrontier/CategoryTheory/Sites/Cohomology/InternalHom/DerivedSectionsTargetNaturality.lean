module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing
import StacksCore.Tactic.StacksAttribute

/-! # Naturality of Stacks 08JA in its covariant variable

Let `(C, O)` be a ringed site. Stacks 08JA identifies the degree-zero global hypercohomology of
the derived internal Hom `RSheafHom(L, M)` with the group of morphisms `L ⟶ M` of `D(O)`,
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`. The companion file
`…InternalHom.DerivedSectionsSourceNaturality` proves that identification natural in `L`. This
file proves it natural in `M`, for an **arbitrary** morphism of `D(O)`: a morphism `φ : M ⟶ M'`
acts on the left-hand side through the covariant functoriality of the derived internal Hom and
on the right-hand side by postcomposition.

The consequence the rest of the development asks for is the corollary: the identification
`H⁰(C, Z) = Hom_{D(O)}(O, Z)` of
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv` is natural in `Z`. That
is the statement needed to pass between a global hypercohomology class and the morphism out of
the structure sheaf naming it while a diagram is transported, as in Stacks 0FVB.

## Main results

* `RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality_target`:
  the naturality at the classes of complexes, for the class of a morphism of complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target`:
  **Stacks 08JA, naturality in the target variable**, for arbitrary objects and an arbitrary
  morphism of `D(O)`.
* `AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality`: morphisms
  out of the structure sheaf are global hypercohomology classes **naturally in the object**.
* `AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap_naturality`: the map of
  Stacks 08JD on degree-zero global hypercohomology is **functorial in its covariant variable**.
  This one needs no new work beyond the above: the naturality in `M` of the canonical map
  `M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)` is
  `derivedTensorDualSectionsMap_naturality`, and Stacks 08JA's naturality in the target is the
  only other factor of the composite.

## Implementation notes

The identification of Stacks 08JA is the composite of four comparisons: the choice of a K-flat
representative of the source and of a K-injective representative of the target, the K-injective
target computing the derived internal Hom (Stacks 0A97), global sections computing derived global
sections on the K-injective complex `SheafHom(A, I)` (Stacks 07A5), and Stacks 0A94. Each of the
last three is natural for morphisms of *complexes* in both variables — the comparison by
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality`, which is already stated in
the source and the K-injective target at once, the third by
`Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso_naturality_complexMap`, and the
fourth by `AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality`,
which is likewise already stated in both variables. So the clause at the classes of complexes is
the mirror image of the source clause, obtained by specialising those two both-variable statements
to `homMap X (𝟙 A) d` instead of to `homMap X c (𝟙 I)`.

Where the two directions differ is the passage from the class of a morphism of complexes to an
arbitrary morphism of `D(O)`, and this is the cheap direction. In the contravariant variable a
morphism between the classes of two K-flat complexes need not be the class of a morphism of
complexes, so the source clause is extended by the calculus of fractions — the clause is shown
closed under composition and under inverting an isomorphism and then applied to a right fraction
whose apex is replaced by a K-flat resolution. Here no such argument is needed: the representative
of the target is K-injective, and every morphism of `D(O)` into the class of a K-injective complex
is the class of a morphism of complexes, by
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective`. So the general clause is the
complex-level clause applied to one chosen representative, with no closure properties and no
localization-calculus argument.

For arbitrary objects the comparison `derivedSheafHomObjectsModelIso` with the chosen
representatives is dinatural in the target — `derivedSheafHomObjectsModelIso_natural_target`
below — carrying a morphism `φ : M ⟶ M'` to the morphism of the classes of the chosen K-injective
representatives that `φ` conjugates to, which is again a morphism into the class of a K-injective
complex. So the general clause follows with no clause for the comparison isomorphisms themselves,
exactly as in the source direction.

The corollary needs one further input, which is available: the identification
`RSheafHom(O, Z) ≅ Z` of `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` is natural in
`Z`, as `derivedStructureSheafHomIso_naturality`. Since
`derivedStructureSheafGlobalSectionsEquiv` is that identification followed by Stacks 08JA at
source the structure sheaf, the naturality proved here is the only remaining piece.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-! ### Naturality at the classes of complexes -/

/-- **Stacks 08JA on a K-injective internal Hom complex is natural in the target**, for the
class of a morphism of complexes. -/
theorem derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality_target
    {A I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A I').obj).IsKInjective] (d : I ⟶ I')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
              (DerivedCategory.Q.map d))) x) =
      derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I x ≫
        DerivedCategory.Q.map d := by
  have hcomp : (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
        (DerivedCategory.Q.map d)) ≫ (derivedSheafHomComparison X A I').hom =
      (derivedSheafHomComparison X A I).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 A) d) := by
    simpa using derivedSheafHomComparison_naturality X (𝟙 A) d
  have s1 : (derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
            (DerivedCategory.Q.map d)) ≫
        (derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I').hom =
      (derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
        (derivedModuleGlobalSections X).map
          (DerivedCategory.Q.map (homMap X (𝟙 A) d)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomp]
  have s2 : (derivedModuleGlobalSections X).map
          (DerivedCategory.Q.map (homMap X (𝟙 A) d)) ≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A I').obj)).inv =
      (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv ≫
        DerivedCategory.Q.map
          (globalSectionsComplexMap X (homMap X (𝟙 A) d)) := by
    rw [Iso.comp_inv_eq, Category.assoc, globalSectionsKInjectiveIso_naturality_complexMap,
      Iso.inv_hom_id_assoc]
  have hfac := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
    (globalSectionsComplexMap X (homMap X (𝟙 A) d))
  have s3 : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
              (DerivedCategory.Q.map d))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I').hom ≫
            (globalSectionsKInjectiveIso X ((sheafHomComplex X A I').obj)).inv) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
            (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          (DerivedCategory.Q.map (globalSectionsComplexMap X (homMap X (𝟙 A) d))) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      (CategoryTheory.square_comp s1 s2)
  -- As in the source clause, `key` is the two glued squares read on `x` rather than a
  -- hand-written equation: its instance arguments are the ones instance search picks there, and
  -- the two normalizations do not commute — rewriting the homology functor to `homologyMap`
  -- first respells the object the composite passes through.
  have key := ConcreteCategory.congr_hom (CategoryTheory.square_comp s3 hfac) x
  simp only [Category.assoc, ConcreteCategory.comp_apply] at key
  simp only [HomologicalComplex.homologyFunctor_map] at key
  have h94 := sheafHomGlobalHomologyEquivDerivedCategoryHom_naturality X (𝟙 A) d
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
        (globalSectionsComplex X (sheafHomComplex X A I).obj)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
            (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) x))
  rw [derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply_comparisons,
    derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_apply_comparisons]
  simp only [Iso.app_hom]
  rw [key]
  -- `rw [h94]` cannot be used, for the reason recorded on the source clause: Stacks 0A94 is
  -- stated for an element of `C.homology 0` and the element here is typed at
  -- `(homologyFunctor _ _ 0).obj C`.
  refine h94.trans ?_
  simp

/-- **Stacks 08JA at a K-flat source is natural in the target**, for an arbitrary morphism of
`D(O)` between the classes of two K-injective complexes. No calculus of fractions is needed: the
morphism is the class of a morphism of complexes because its target is the class of a K-injective
complex. -/
theorem derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_target
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    {I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    (ψ : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsEquivOfKFlat X A I' hA
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map ψ)) x) =
      derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA x ≫ ψ := by
  obtain ⟨d, rfl⟩ := exists_Q_map_eq_of_isKInjective X ψ
  have : ((sheafHomComplex X A I).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X A I hA
  have : ((sheafHomComplex X A I').obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X A I' hA
  exact derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality_target X d x

/-! ### Naturality for arbitrary objects -/

/-- **The comparison of the derived internal Hom with the chosen representatives is dinatural in
the target.** A morphism `φ : M ⟶ M'` of `D(O)` is carried to the morphism of the classes of the
chosen K-injective representatives that `φ` conjugates to. -/
private lemma derivedSheafHomObjectsModelIso_natural_target
    {L M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : M ⟶ M') :
    ((derivedSheafHomBifunctor X).obj (op L)).map φ ≫
        (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
          (kInjectiveModelIso X M')).hom =
      (derivedSheafHomObjectsModelIso X (kFlatModelIso X L) (kInjectiveModelIso X M)).hom ≫
        ((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kFlatModel X L)))).map
          ((kInjectiveModelIso X M).hom ≫ φ ≫ (kInjectiveModelIso X M').inv) := by
  have s1 : ((derivedSheafHomBifunctor X).obj (op L)).map φ ≫
        ((derivedSheafHomBifunctor X).map (kFlatModelIso X L).hom.op).app M' =
      ((derivedSheafHomBifunctor X).map (kFlatModelIso X L).hom.op).app M ≫
        ((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (kFlatModel X L)))).map φ :=
    ((derivedSheafHomBifunctor X).map (kFlatModelIso X L).hom.op).naturality φ
  have hconj : φ ≫ (kInjectiveModelIso X M').inv =
      (kInjectiveModelIso X M).inv ≫
        ((kInjectiveModelIso X M).hom ≫ φ ≫ (kInjectiveModelIso X M').inv) := by
    simp
  have s2 : ((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kFlatModel X L)))).map φ ≫
        ((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (kFlatModel X L)))).map
            (kInjectiveModelIso X M').inv =
      ((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (kFlatModel X L)))).map
            (kInjectiveModelIso X M).inv ≫
        ((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (kFlatModel X L)))).map
            ((kInjectiveModelIso X M).hom ≫ φ ≫ (kInjectiveModelIso X M').inv) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    -- `rw [hconj]` would rewrite the right-hand side too, the pattern
    -- `φ ≫ (kInjectiveModelIso X M').inv` occurring inside it.
    exact congrArg ((derivedSheafHomBifunctor X).obj
      (op (DerivedCategory.Q.obj (kFlatModel X L)))).map hconj
  exact CategoryTheory.square_comp s1 s2

/-- **A commuting square of `D(O)` read on a degree-zero global hypercohomology class.** Stated
with all four objects and all four morphisms variables and applied by `exact`: at the objects of
the clauses below, carrying a class of that size through a natural square by `rw` spends a
declaration's whole heartbeat budget, whereas one `isDefEq` against this statement costs
nothing. -/
private lemma homologyGlobalSections_apply_sq
    {Z₁ Z₂ Z₃ Z₄ :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {b : Z₁ ⟶ Z₂} {a : Z₂ ⟶ Z₄} {d : Z₁ ⟶ Z₃} {c : Z₃ ⟶ Z₄} (hsq : b ≫ a = d ≫ c)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj Z₁) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map a)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map b) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map c)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map d) x) := by
  have h2 := congrArg (fun m => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
    ((derivedModuleGlobalSections X).map m)) hsq
  simp only [Functor.map_comp] at h2
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h2 x

/-- The transport of a global hypercohomology class of `RSheafHom(L, M)` through the comparison
with the chosen representatives, for the covariant functoriality of the derived internal Hom:
`derivedSheafHomObjectsModelIso_natural_target` read on a class. -/
private lemma derivedSheafHomObjectsModelIso_apply_target
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : M ⟶ M')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
            (kInjectiveModelIso X M')).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op L)).map φ)) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kFlatModel X L)))).map
              ((kInjectiveModelIso X M).hom ≫ φ ≫ (kInjectiveModelIso X M').inv)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
              (kInjectiveModelIso X M)).hom) x) :=
  homologyGlobalSections_apply_sq X (derivedSheafHomObjectsModelIso_natural_target X φ) x

/-- The rearrangement that turns the K-flat clause at the conjugated morphism into the clause
for `φ`, with every object and morphism a variable. Stated separately and applied by `exact`:
at the objects of the clause itself the associativity normalization alone exhausts the
heartbeat budget. -/
private lemma assembleTarget {D : Type*} [Category D] {P A B N N' B' : D}
    (f : P ⟶ A) (g : A ⟶ B) (h : B ⟶ N) (φ : N ⟶ N') (k : N' ⟶ B') (l : B' ⟶ N')
    (hkl : k ≫ l = 𝟙 N') :
    f ≫ (g ≫ h ≫ φ ≫ k) ≫ l = (f ≫ g ≫ h) ≫ φ := by
  simp only [Category.assoc, hkl, Category.comp_id]

/-- **Stacks 08JA, naturality in the target variable.** For objects `L`, `M`, `M'` of `D(O)` and
an arbitrary morphism `φ : M ⟶ M'`, the identification of the degree-zero global
hypercohomology of `RSheafHom(L, M)` with `Hom_{D(O)}(L, M)` carries the covariant
functoriality of the derived internal Hom to postcomposition with `φ`. -/
@[stacks 08JA "global sections, naturality in the target"]
theorem derivedSheafHomGlobalSectionsEquiv_naturality_target
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : M ⟶ M')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op L)).map φ)) x) =
      derivedSheafHomGlobalSectionsEquiv X L M x ≫ φ := by
  have hx := derivedSheafHomObjectsModelIso_apply_target X L φ x
  have hnat := derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_target X
    (isKFlat_kFlatModel X L)
    ((kInjectiveModelIso X M).hom ≫ φ ≫ (kInjectiveModelIso X M').inv)
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
          (kInjectiveModelIso X M)).hom) x)
  -- The two instances of `derivedSheafHomGlobalSectionsEquiv_apply_assoc` are supplied with their
  -- arguments, and `hx` is carried into the K-flat clause by `congrArg` rather than by `rw`,
  -- for the reason recorded on the source clause: a rewrite whose pattern is one of these
  -- hypercohomology classes exhausts the elaborator's budget.
  have e' := derivedSheafHomGlobalSectionsEquiv_apply_assoc X L M'
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        (((derivedSheafHomBifunctor X).obj (op L)).map φ)) x)
  have e := derivedSheafHomGlobalSectionsEquiv_apply_assoc X L M x
  have step := (congrArg (fun z => derivedSheafHomGlobalSectionsEquivOfKFlat X (kFlatModel X L)
    (kInjectiveModel X M') (isKFlat_kFlatModel X L) z) hx).trans hnat
  have h1 := congrArg
    (fun g => (kFlatModelIso X L).inv ≫ g ≫ (kInjectiveModelIso X M').hom) step
  have h2 := congrArg (fun g => g ≫ φ) e
  exact e'.trans (h1.trans ((assembleTarget _ _ _ _ _ _ (Iso.inv_hom_id _)).trans h2.symm))

/-! ### Global hypercohomology classes are morphisms out of the structure sheaf, naturally -/

/-- **Morphisms out of the structure sheaf are global hypercohomology classes, naturally in the
object.** For a morphism `φ : Z ⟶ W` of `D(O)` the identification
`H⁰(C, Z) = Hom_{D(O)}(O, Z)` of
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv` carries the map induced
by `φ` on global hypercohomology to postcomposition with `φ`.

This is Stacks 08JA at source the structure sheaf, read through the naturality in `Z` of the
identification `RSheafHom(O, Z) ≅ Z` (`derivedStructureSheafHomIso_naturality`). -/
theorem derivedStructureSheafGlobalSectionsEquiv_naturality
    {Z W : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : Z ⟶ W)
    (y : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj Z) : Type u)) :
    derivedStructureSheafGlobalSectionsEquiv X W
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map φ) y) =
      derivedStructureSheafGlobalSectionsEquiv X Z y ≫ φ := by
  -- `derivedStructureSheafGlobalSectionsEquiv X Z` is `H⁰(Γ(-))` of the inverse of
  -- `derivedStructureSheafHomIso X Z` followed by Stacks 08JA at source the structure sheaf.
  have hy := homologyGlobalSections_apply_sq X
    (b := φ) (a := (derivedStructureSheafHomIso X W).inv)
    (d := (derivedStructureSheafHomIso X Z).inv)
    (c := ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map φ)
    (by rw [Iso.comp_inv_eq, Category.assoc, derivedStructureSheafHomIso_naturality,
      Iso.inv_hom_id_assoc]) y
  have hnat := derivedSheafHomGlobalSectionsEquiv_naturality_target X
    (derivedStructureSheaf X) φ
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map (derivedStructureSheafHomIso X Z).inv) y)
  exact (congrArg
    (derivedSheafHomGlobalSectionsEquiv X (derivedStructureSheaf X) W) hy).trans hnat

/-! ### The map of Stacks 08JD is functorial in its covariant variable -/

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **The map of Stacks 08JD on degree-zero global hypercohomology is natural in `M`.** For
`m : M ⟶ M'` the map `H⁰(C, M ⊗^L_O L^∨) ⟶ Hom_{D(O)}(L, M)` of
`AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap` carries the map induced by `m`
on the left to postcomposition with `m` on the right.

That map is the degree-zero global hypercohomology of the canonical map
`M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)` followed by Stacks 08JA, so this is the naturality in `M` of
those two pieces: `derivedTensorDualSectionsMap_naturality` for the first, and
`derivedSheafHomGlobalSectionsEquiv_naturality_target` above for the second. No bijectivity of the map, hence no perfectness of `L`, is
involved: this is functoriality of the comparison of Stacks 08JD, not Stacks 08DQ. -/
@[stacks 08JD "functoriality in M of the map on degree-zero derived global sections"]
theorem derivedTensorDualGlobalSectionsMap_naturality
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M')
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        ((T.tensor.obj M).obj (derivedDual X L))) : Type u)) :
    derivedTensorDualGlobalSectionsMap X T L M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            ((T.tensor.map m).app (derivedDual X L))) z) =
      derivedTensorDualGlobalSectionsMap X T L M z ≫ m := by
  have hsec := derivedTensorDualSectionsMap_naturality X T L m z
  have htgt := derivedSheafHomGlobalSectionsEquiv_naturality_target X L m
    (derivedTensorDualSectionsMap X T L M z)
  exact (congrArg (derivedSheafHomGlobalSectionsEquiv X L M') hsec).trans htgt

end AlgebraicGeometry.RingedSite

end
