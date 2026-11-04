module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreGlobalSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IntegralRefinementFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchLocallyIrreducible
public import StacksCore.CategoryTheory.Filtration.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricPointStalkCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves

/-!
# Geometric points detect isomorphisms in the derived category of abelian étale sheaves

Let `Y` be a scheme. A morphism `φ` of the unbounded derived category `D(Y_étale)` of abelian
sheaves on the small étale site of `Y` is an isomorphism if and only if its inverse image
`y⁻¹ φ` along every geometric point `y : Spec Ω ⟶ Y`, `Ω` a separably closed field, is an
isomorphism of `D((Spec Ω)_étale)`.

Over the spectrum of a separably closed field `Ω` the question is then a question about abelian
groups: global sections `Γ(Spec Ω, -)` is an equivalence from abelian sheaves to abelian groups,
and so is the stalk at the canonical point, so a morphism of `D((Spec Ω)_étale)` is an
isomorphism if and only if its image under either functor, applied degreewise, is an isomorphism
of `D(Ab)`. Combined with the identification `(Rf'_* L)_{can} ≅ RΓ(X', L)` for
`f' : X' ⟶ Spec Ω`, this says that `Rf'_*` inverts a morphism exactly when `RΓ(X', -)` does.

## Main results

* `Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleAbelianInverseImage_map` — a morphism of
  abelian sheaves on `Y_étale` is an isomorphism as soon as its inverse image along every
  geometric point of `Y` is one.
* `Stacks.EtaleCohomology.isIso_iff_forall_isIso_etaleAbelianDerivedInverseImage_map` — a
  morphism of `D(Y_étale)` is an isomorphism if and only if its derived inverse image along every
  geometric point is one.
* `Stacks.EtaleCohomology.isIso_iff_isIso_sheafFiber_mapDerivedCategory_map_of_isSepClosed` and
  `Stacks.EtaleCohomology.isIso_iff_isIso_globalSections_mapDerivedCategory_map_of_isSepClosed` —
  over `Spec Ω`, `Ω` separably closed, a morphism of the derived category is an isomorphism if
  and only if the stalk at the canonical point, respectively global sections, carries it to one.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImage_map_iff_of_isSepClosed` — for
  `f' : X' ⟶ Spec Ω`, `Rf'_*` inverts a morphism of `D(X'_étale)` if and only if `RΓ(X', -)`
  does.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 0F0F](https://stacks.math.columbia.edu/tag/0F0F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] additive_globalSections_smallEtale additive_sheafFiber_smallEtale

/-! ### Conservativity of the geometric points -/

section Conservativity

variable {Y : Scheme.{u}}

/-- **Geometric points detect isomorphisms of abelian étale sheaves through inverse images.** A
morphism `γ` of abelian sheaves on the small étale site of `Y` is an isomorphism as soon as its
inverse image `y⁻¹ γ` is one for every geometric point `y : Spec Ω ⟶ Y`, `Ω` a separably closed
field. -/
theorem isIso_of_forall_isIso_etaleAbelianInverseImage_map
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (γ : F ⟶ G)
    (hγ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      IsIso ((etaleAbelianInverseImage.{u, v} y).map γ)) :
    IsIso γ :=
  isIso_of_isIso_etaleAbelianInverseImage_family (residueGeometricPoint Y)
    (Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2
      ⟨y, default, residueGeometricPoint_apply Y y default⟩) γ
    fun y ↦ hγ _ (residueGeometricPoint Y y)

/-- **Geometric points are conservative on the unbounded derived category of abelian étale
sheaves.** A morphism `φ` of `D(Y_étale)` is an isomorphism if and only if, for every geometric
point `y : Spec Ω ⟶ Y` with `Ω` a separably closed field, its derived inverse image `y⁻¹ φ` is an
isomorphism of `D((Spec Ω)_étale)`. -/
theorem isIso_iff_forall_isIso_etaleAbelianDerivedInverseImage_map
    {K L : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (φ : K ⟶ L) :
    IsIso φ ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      IsIso ((etaleAbelianDerivedInverseImage.{u, v} y).map φ) := by
  refine ⟨fun _ _ _ _ _ ↦ inferInstance, fun h ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  exact isIso_of_forall_isIso_etaleAbelianInverseImage_map _ fun Ω _ _ y ↦
    ((etaleAbelianInverseImage.{u, v} y).isIso_mapDerivedCategory_map_iff φ).1 (h Ω y) n

/-- An exact additive functor from abelian sheaves on `Y_étale` to abelian groups that reflects
isomorphisms detects isomorphisms of the derived category degreewise. -/
private theorem isIso_iff_isIso_mapDerivedCategory_map_of_reflectsIsomorphisms
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      AddCommGrpCat.{max (u + 1) v}) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F.ReflectsIsomorphisms]
    {K L : DerivedCategory (Sheaf Y.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})} (φ : K ⟶ L) :
    IsIso φ ↔ IsIso (F.mapDerivedCategory.map φ) := by
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have := (Functor.isIso_mapDerivedCategory_map_iff _ φ).1 h n
  exact isIso_of_reflects_iso _ F

end Conservativity

/-! ### The spectrum of a separably closed field -/

section SeparablyClosedField

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- Over the spectrum of a separably closed field, global sections of abelian étale sheaves is
right exact. -/
instance preservesFiniteColimits_globalSections_of_isSepClosed :
    PreservesFiniteColimits
      (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) := by
  have := isEquivalence_globalSections_of_isSepClosed Ω AddCommGrpCat.{max (u + 1) v}
  infer_instance

/-- Over the spectrum of a separably closed field, the stalk at the canonical point reflects
isomorphisms of abelian étale sheaves. -/
theorem reflectsIsomorphisms_sheafFiber_pointSmallEtale_id_ulift :
    (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).ReflectsIsomorphisms := by
  have := isEquivalence_globalSections_of_isSepClosed Ω AddCommGrpCat.{max (u + 1) v}
  exact CategoryTheory.reflectsIsomorphisms_of_iso (sheafFiberUliftIdIsoGamma.{u, v} Ω).symm

/-- **Over a separably closed field the stalk at the canonical point detects isomorphisms of the
derived category.** A morphism `φ` of `D((Spec Ω)_étale)`, `Ω` separably closed, is an
isomorphism if and only if the stalk at the canonical point of `Spec Ω`, applied degreewise,
carries it to an isomorphism of `D(Ab)`. -/
theorem isIso_iff_isIso_sheafFiber_mapDerivedCategory_map_of_isSepClosed
    {K L : DerivedCategory (Sheaf (Spec (.of Ω)).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})} (φ : K ⟶ L) :
    IsIso φ ↔ IsIso ((((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).mapDerivedCategory.map φ) := by
  have := reflectsIsomorphisms_sheafFiber_pointSmallEtale_id_ulift.{u, v} Ω
  exact isIso_iff_isIso_mapDerivedCategory_map_of_reflectsIsomorphisms.{u, v} _ φ

/-- **Over a separably closed field global sections detect isomorphisms of the derived
category.** A morphism `φ` of `D((Spec Ω)_étale)`, `Ω` separably closed, is an isomorphism if and
only if global sections `Γ(Spec Ω, -)`, an exact functor here, applied degreewise, carries it to
an isomorphism of `D(Ab)`. -/
theorem isIso_iff_isIso_globalSections_mapDerivedCategory_map_of_isSepClosed
    {K L : DerivedCategory (Sheaf (Spec (.of Ω)).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})} (φ : K ⟶ L) :
    IsIso φ ↔ IsIso ((Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).mapDerivedCategory.map φ) := by
  have := isEquivalence_globalSections_of_isSepClosed Ω AddCommGrpCat.{max (u + 1) v}
  exact isIso_iff_isIso_mapDerivedCategory_map_of_reflectsIsomorphisms.{u, v} _ φ

/-- **`Rf'_*` to a separably closed point inverts exactly what `RΓ(X', -)` inverts.** For
`f' : X' ⟶ Spec Ω`, `Ω` separably closed, a morphism `ψ` of `D(X'_étale)` is carried to an
isomorphism by the derived direct image `Rf'_*` if and only if it is carried to one by the derived
global sections `RΓ(X', -)`. -/
theorem isIso_etaleAbelianDerivedDirectImage_map_iff_of_isSepClosed {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (.of Ω))
    {K L : DerivedCategory (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (ψ : K ⟶ L) :
    IsIso ((etaleAbelianDerivedDirectImage.{u, v} f').map ψ) ↔
      IsIso ((Stacks.DerivedFunctor.totalRightDerived
        (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})).map ψ) := by
  rw [isIso_iff_isIso_sheafFiber_mapDerivedCategory_map_of_isSepClosed.{u, v} Ω]
  exact NatIso.isIso_map_iff
    (etaleAbelianSheafFiberMapDerivedCategoryDerivedDirectImageIso.{u, v} f') ψ

end SeparablyClosedField

end Stacks.EtaleCohomology

end
