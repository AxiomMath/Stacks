module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Pushforward
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceOverBase
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-!
# The base ring acts through the derived internal Hom and through derived global sections

Let `A` be a commutative ring and let `X` be a scheme over `Spec A`. The canonical `A`-linear
structure on `𝒪_X`-modules, `AlgebraicGeometry.modulesLinear`, is multiplication by the image of a
scalar under `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`, read on sections over every open. Two functors carry
that action to the corresponding action on their values:

* the derived internal Hom `R𝓗om_{𝒪_X}(K, -)` out of a fixed object;
* `A`-linear global sections `Γ(X, -)` and its derived functor `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`.

## Main results

* `AlgebraicGeometry.smul_eq_of_toCatCenter_eq`: two scalar actions whose central
  endomorphisms agree on an abelian category agree on its derived category.
* `AlgebraicGeometry.baseSectionFamily` and
  `AlgebraicGeometry.toCatCenter_eq_globalSectionToEnd`: the base scalar of a scheme over
  `Spec A` is multiplication by a compatible family of local sections of the structure sheaf,
  as a central endomorphism `Stacks.SheafOfModules.globalSectionToEnd`.
* `AlgebraicGeometry.derivedSheafHomFunctor_map_smul_id`: `R𝓗om_{𝒪_X}(K, -)` carries
  multiplication by a base scalar to multiplication by that scalar.
* `AlgebraicGeometry.globalSectionsOver_linear` and
  `AlgebraicGeometry.derivedGlobalSectionsOver_map_smul_id`: `Γ(X, -)` and `RΓ(X, -)` are
  `A`-linear.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Two scalar actions agreeing on a derived category -/

/-- Two scalar actions with the same central endomorphism agree on every morphism. -/
private theorem smul_eq_of_toCatCenter_eq_of_cat {R S : Type*} [Ring R] [Ring S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] [Linear S C] {a : R} {b : S}
    (h : Linear.toCatCenter R C a = Linear.toCatCenter S C b) {Y Z : C} (g : Y ⟶ Z) :
    a • g = b • g := by
  rw [← Category.id_comp g, ← Linear.smul_comp, ← Linear.smul_comp,
    Linear.smul_id_eq_toCatCenter_app, Linear.smul_id_eq_toCatCenter_app, h]

/-- Two scalar actions whose central endomorphisms agree on an abelian category agree on its
derived category. -/
theorem smul_eq_of_toCatCenter_eq {R S : Type*} [Ring R] [Ring S]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Linear R C] [Linear S C]
    (a : R) (b : S) (h : Linear.toCatCenter R C a = Linear.toCatCenter S C b)
    {Y Z : DerivedCategory C} (g : Y ⟶ Z) : a • g = b • g := by
  have hcenter : Linear.toCatCenter R (DerivedCategory C) a =
      Linear.toCatCenter S (DerivedCategory C) b := by
    apply CatCenter.ext_of_localization DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    intro L
    change a • 𝟙 (DerivedCategory.Q.obj L) = b • 𝟙 (DerivedCategory.Q.obj L)
    calc a • 𝟙 (DerivedCategory.Q.obj L)
        = DerivedCategory.Q.map (a • 𝟙 L) := by
          rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
      _ = DerivedCategory.Q.map (b • 𝟙 L) :=
          congrArg DerivedCategory.Q.map
            (HomologicalComplex.hom_ext _ _ fun _ ↦ smul_eq_of_toCatCenter_eq_of_cat h _)
      _ = b • 𝟙 (DerivedCategory.Q.obj L) := by
          rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  exact smul_eq_of_toCatCenter_eq_of_cat hcenter g

/-! ### The base scalar as a global section of the structure sheaf -/

variable {A : Type u} [CommRing A] (X : Over (Spec (CommRingCat.of A)))

/-- The image of a base scalar in the functions on every open, as a compatible family of sections
of the structure sheaf. -/
def baseSectionFamily (a : A) : (X.left.ringCatSheaf.obj ⋙ forget RingCat).sections where
  val U := baseRingToSections A X U a
  property {U V} i := by
    have h : X.left.ringCatSheaf.obj.map U.unop.leTop.op ≫
        X.left.ringCatSheaf.obj.map i = X.left.ringCatSheaf.obj.map V.unop.leTop.op :=
      (X.left.ringCatSheaf.obj.map_comp _ _).symm
    exact congrArg (fun r ↦ (RingCat.Hom.hom r)
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ X.hom.appTop).hom a)) h

/-- The central endomorphism of the category of `𝒪_X`-modules given by a base scalar. -/
abbrev baseCatCenter (a : A) : CatCenter X.left.Modules :=
  Stacks.SheafOfModules.globalSectionToEnd X.left.ringCatSheaf (baseSectionFamily X a)

/-- The centre of the category of `𝒪_X`-modules acting on itself. -/
@[instance_reducible]
def linearCatCenterModules : Linear (CatCenter X.left.Modules) X.left.Modules :=
  Linear.ofRingMorphism (RingHom.id _)

/-- The base scalar is multiplication by the compatible family `baseSectionFamily` of local
sections of the structure sheaf. -/
theorem toCatCenter_eq_globalSectionToEnd (a : A) :
    letI : Linear A X.left.Modules := modulesLinear A X
    letI := linearCatCenterModules X
    Linear.toCatCenter A X.left.Modules a =
      Linear.toCatCenter (CatCenter X.left.Modules) X.left.Modules (baseCatCenter X a) := by
  let : Linear A X.left.Modules := modulesLinear A X
  let := linearCatCenterModules X
  refine CatCenter.ext _ _ fun M ↦ ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  rfl

/-! ### The derived internal Hom is linear over the base ring -/

/-- The derived internal Hom `R𝓗om_{𝒪_X}(K, -)` as an endofunctor of `D(𝒪_X)`. -/
def derivedSheafHomFunctor (K : DerivedCategory X.left.Modules) :
    DerivedCategory X.left.Modules ⥤ DerivedCategory X.left.Modules :=
  (Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj (op K)

/-- The derived internal Hom out of a fixed object carries multiplication by a base scalar to
multiplication by that scalar. -/
theorem derivedSheafHomFunctor_map_smul_id (K M : DerivedCategory X.left.Modules) (a : A) :
    letI : Linear A X.left.Modules := modulesLinear A X
    (derivedSheafHomFunctor X K).map (a • 𝟙 M) =
      a • 𝟙 ((derivedSheafHomFunctor X K).obj M) := by
  let : Linear A X.left.Modules := modulesLinear A X
  let := linearCatCenterModules X
  have hD : ∀ {Y Z : DerivedCategory X.left.Modules} (g : Y ⟶ Z),
      a • g = baseCatCenter X a • g := fun {_ _} g ↦
    smul_eq_of_toCatCenter_eq a (baseCatCenter X a) (toCatCenter_eq_globalSectionToEnd X a) g
  calc (derivedSheafHomFunctor X K).map (a • 𝟙 M)
      = (derivedSheafHomFunctor X K).map (baseCatCenter X a • 𝟙 M) := congrArg _ (hD (𝟙 M))
    _ = baseCatCenter X a • 𝟙 ((derivedSheafHomFunctor X K).obj M) :=
        AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd
          (Stacks.SheafOfModules.ringedSite X.left.sheaf) (baseSectionFamily X a) K M
    _ = a • 𝟙 ((derivedSheafHomFunctor X K).obj M) := (hD (𝟙 _)).symm

/-! ### Global sections over the base ring are linear -/

/-- `A`-linear global sections of a scheme over `Spec A` is an `A`-linear functor. -/
theorem globalSectionsOver_linear :
    letI : Linear A X.left.Modules := modulesLinear A X
    (globalSectionsOver X.hom).Linear A := by
  let : Linear A X.left.Modules := modulesLinear A X
  constructor
  intro M N g a
  apply ModuleCat.hom_ext
  ext x
  change (g.val.app (op ⊤)).hom
      (baseRingToSections A X (op ⊤) a • (show M.val.obj (op ⊤) from x)) = _
  rw [map_smul, AlgebraicGeometry.CoherentModuleFunctors.baseRingToSections_top]
  rfl

/-- `A`-linear derived global sections carries multiplication by a base scalar to multiplication by
that scalar. -/
theorem derivedGlobalSectionsOver_map_smul_id (a : A) (E : DerivedCategory X.left.Modules) :
    letI : Linear A X.left.Modules := modulesLinear A X
    (derivedGlobalSectionsOver X.hom).map (a • 𝟙 E) =
      a • 𝟙 ((derivedGlobalSectionsOver X.hom).obj E) := by
  let : Linear A X.left.Modules := modulesLinear A X
  let := globalSectionsOver_linear X
  have hunder : ∀ N : X.left.Modules, (globalSectionsOver X.hom).map (a • 𝟙 N) =
      a • 𝟙 ((globalSectionsOver X.hom).obj N) := fun N ↦ by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  exact Stacks.SemilinearFunctor.map_smul_id_rightDerived (R := A) (S := A)
    (H₁ := HomotopyCategory X.left.Modules (ComplexShape.up ℤ))
    (D₁ := DerivedCategory X.left.Modules) (D₂ := DerivedCategory (ModuleCat.{u} A))
    (G := homotopyGlobalSectionsOver X.hom) (L := DerivedCategory.Qh)
    (derivedGlobalSectionsOver X.hom) (derivedGlobalSectionsOverUnit X.hom)
    (HomotopyCategory.quasiIso X.left.Modules (ComplexShape.up ℤ)) a a
    (fun M ↦ Stacks.SemilinearFunctor.map_smul_id_comp (R := A) (S := A)
      ((globalSectionsOver X.hom).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh a a
      (fun N ↦ Stacks.SemilinearFunctor.map_smul_id_mapHomotopyCategory (R := A) (S := A)
        (globalSectionsOver X.hom) a a hunder (ComplexShape.up ℤ) N) M) E

end AlgebraicGeometry

end
