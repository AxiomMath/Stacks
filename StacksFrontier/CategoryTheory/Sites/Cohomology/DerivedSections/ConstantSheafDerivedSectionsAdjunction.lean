module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.GlobalSectionsAtTerminal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived constant sheaf is left adjoint to the unbounded derived global sections of a site

Let `(C, J)` be a site whose underlying category has a terminal object `T`, and let `A` be an
abelian category of coefficients for which sheafification exists and for which the sheaves
`Sheaf J A` form a Grothendieck abelian category. This file constructs the two functors

`Lπ^{-1} : D(A) ⥤ D(Sheaf J A)` and `RΓ(T, -) : D(Sheaf J A) ⥤ D(A)`

on the *unbounded* derived categories and proves that the first is left adjoint to the second.
The left adjoint is the constant sheaf functor promoted by
`CategoryTheory.Functor.mapDerivedCategory`, which applies because the constant sheaf functor —
the constant presheaf functor followed by sheafification — is exact. The right adjoint is the
total right derived functor of the sections over an object, which exists because `Sheaf J A` is
Grothendieck abelian and therefore admits K-injective resolutions of unbounded complexes
([Stacks, Tag 079P], available here with no hypotheses left standing as
`Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective`).

Nothing here requires the sections functor to be exact, which it is not — that is what sheaf
cohomology measures, and it is why `CategoryTheory.Functor.mapDerivedCategory` cannot be applied
to it and why `CategoryTheory.Adjunction.mapDerivedCategory` is unavailable. Only the *left*
adjoint is exact, and `CategoryTheory.Adjunction.derived` asks exactness of neither: it asks that
the two functors be derived functors of the two composites with the localizations, and that the
two composites `Lπ^{-1} ⋙ RΓ` and `RΓ ⋙ Lπ^{-1}` be derived functors as well. Of those four,
three hold because the comparison map is invertible — the constant sheaf functor being exact —
and the fourth is the K-injective criterion
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`
applied to `RΓ` followed by an arbitrary functor.

## Main definitions

* `Stacks.Cohomology.SiteConstantSheaf.derivedSections`: **`RΓ(U, -)` on the unbounded derived
  category of sheaves on a site**, the total right derived functor of the sections over an
  object `U` followed by the localization, together with its unit
  `Stacks.Cohomology.SiteConstantSheaf.derivedSectionsUnit`.
* `Stacks.Cohomology.SiteConstantSheaf.derivedConstantSheaf`: **`Lπ^{-1}` on the unbounded
  derived categories**, the constant sheaf functor promoted to derived categories, with the
  factorization `Stacks.Cohomology.SiteConstantSheaf.derivedConstantSheafFactors` through the
  degreewise functor.

## Main results

* `Stacks.Cohomology.SiteConstantSheaf.derivedConstantSheafAdjunction`: **the derived adjunction
  `Lπ^{-1} ⊣ RΓ(T, -)`** on the unbounded derived categories, for a terminal object `T` of the
  site.
* `Stacks.Cohomology.SiteConstantSheaf.derivedConstantSheafAdjunction_unit_fac`: the unit of the
  derived adjunction at the class of a complex `K` of coefficients is the class of the degreewise
  unit `K ⟶ Γ(T, π^{-1}K)` followed by the comparison map of the derived sections.
* `Stacks.Cohomology.SiteConstantSheaf.smallEtaleDerivedConstantSheafAdjunction`: **the same
  adjunction on the small étale site of a scheme**, `Lπ^{-1} ⊣ RΓ(X, -)` on
  `D(Ab) ⇄ D(X_étale)`. Its two hypotheses are discharged by
  `Stacks.Cohomology.SiteConstantSheaf.isGrothendieckAbelian_smallEtaleAbelianSheaf`, the small
  étale site being essentially small, and
  `Stacks.Cohomology.SiteConstantSheaf.smallEtaleTerminalObjIsTerminal`, which exhibits
  `X ──𝟙──> X` as a terminal object of it.

## Implementation notes

*Why a general site, and why these hypotheses.* The repository already has this adjunction for
the open-cover site of a topological space with coefficients in abelian groups,
`Stacks.Cohomology.Leray.derivedConstantAbelianSheafAdjunction`. That instance is of no use away
from `TopCat`: its left adjoint is the constant sheaf on `Opens X` and its right adjoint the
sections over `⊤ : Opens X`. The content of this file is the same construction with the space
replaced by an arbitrary site and the coefficients by an arbitrary abelian category, which is
what a statement about the étale site of a scheme, or about sheaves of modules over a ring, can
quote. Every input is available at unconstrained universes: the existence of K-injective
resolutions is
`Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q`,
stated for any `C : Type u` with `Category.{v} C`, `Abelian C` and `IsGrothendieckAbelian.{w} C`;
so the Grothendieck abelian condition is an instance binder on `Sheaf J A` rather than deduced from
a smallness assumption on `C`, which would exclude the étale site.

*The site of the application.* The last section instantiates the adjunction at the small étale
site of an arbitrary scheme with coefficients in `AddCommGrpCat.{u + 1}`, which is the site and
the coefficient category of [Stacks, Tag 0F0E] and of the special case
`Stacks.EtaleCohomology.isIso_etaleTensorConstComparison`. The three hypotheses the general
construction asks for are made local instances there rather than global ones, which keeps
`IsGrothendieckAbelian` on étale abelian sheaves out of global instance search.

*The sections are taken over an arbitrary object.* Nothing in the construction of the right
adjoint uses that the object is terminal; only the adjunction does, through
`CategoryTheory.constantSheafAdj`. So `derivedSections` is defined at an arbitrary `U : Cᵒᵖ`
and the adjunction is its value at `op T`.

*Exactness of the constant sheaf functor* is `Functor.const Cᵒᵖ ⋙ presheafToSheaf J A` being a
composite of a functor preserving all limits and colimits with sheafification, which preserves
finite limits by `CategoryTheory.instPreservesFiniteLimitsPresheafToSheaf` and all colimits
because it is a left adjoint. Both are found by instance search, so neither is restated.

*What this does not do.* The adjunction is the first of the three inputs to [Stacks, Tag 0F0E],
`RΓ(X, E ⊗_𝐙^𝐋 K̲) = RΓ(X, E) ⊗_𝐙^𝐋 K` for a quasi-compact quasi-separated scheme `X`: fed to
`CategoryTheory.adjunctionTensorMap` together with an oplax monoidal structure on `Lπ^{-1}` for
the two derived tensor products, it produces the comparison map
`RΓ(E) ⊗_𝐙^𝐋 K ⟶ RΓ(E ⊗_𝐙^𝐋 K̲)` whose invertibility is that lemma. That oplax structure is
not built here and is not available: the derived tensor product of sheaves of modules
(`Stacks.ModuleSheaf.derivedMonoidal`) is computed by K-flat resolutions, and the canonical
comparison `Q(M) ⊗^𝐋 Q(N) ⟶ Q(M ⊗ N)` runs in the direction opposite to the one an oplax
structure on `Lπ^{-1}` needs, so producing it requires knowing that the constant sheaf functor
carries K-flat complexes to K-flat complexes. Nor are the two nested stupid-truncation
dévissages of steps 3 to 5 of that proof done here.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 0F0E](https://stacks.math.columbia.edu/tag/0F0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₀ w₁ w₂ v₂ u₂ v u

namespace Stacks.Cohomology.SiteConstantSheaf

open Stacks.Injectives.KInjectiveResolution

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A] [Abelian A] [HasSheafify J A]
  [PreservesFiniteLimits (constantSheaf J A)] [PreservesFiniteColimits (constantSheaf J A)]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} (Sheaf J A)]
  [IsGrothendieckAbelian.{w₀} (Sheaf J A)]

/-! ### The unbounded derived sections -/

/-- **The sections over an object on cochain complexes, followed by the localization to `D(A)`,
has a right derived functor** on the whole unbounded derived category of sheaves. The sheaves on
the site form a Grothendieck abelian category, so every cochain complex of them receives a
quasi-isomorphism into a K-injective one, and that is all the criterion
`Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q`
needs. -/
instance hasRightDerivedFunctor_sheafSections_comp_Q (U : Cᵒᵖ) :
    (((sheafSections J A).obj U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf J A) (ComplexShape.up ℤ)) :=
  hasRightDerivedFunctor_mapHomologicalComplex_comp_Q ((sheafSections J A).obj U)

/-- **`RΓ(U, -) : D(Sheaf J A) ⥤ D(A)` on the unbounded derived category.** This is the total
right derived functor of the sections over `U` on cochain complexes followed by the localization,
along the localization `DerivedCategory.Q` of the sheaves.

It is not the restriction of a functor defined by applying `Γ(U, -)` degreewise: sections are
left exact and not exact, so `CategoryTheory.Functor.mapDerivedCategory` does not apply to them.
The bounded below derived sections `CategoryTheory.Functor.rightDerivedFunctorPlus` of
`(sheafSections J A).obj U` is the restriction of this one in the sense that both are right
derived functors of the same functor; no such comparison is proved here. -/
@[sga "4 XVII 1.2.3" "(i), special case", sga "4½ Etat_0 4.1.3" "special case"]
def derivedSections (U : Cᵒᵖ) : DerivedCategory (Sheaf J A) ⥤ DerivedCategory A :=
  (((sheafSections J A).obj U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf J A) (ComplexShape.up ℤ))

/-- **The unit of the unbounded derived sections**: the comparison map `Γ(U, K) ⟶ RΓ(U, K)` in
`D(A)`, natural in the cochain complex `K` of sheaves. It is invertible at every K-injective
complex, by `Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective`. -/
def derivedSectionsUnit (U : Cᵒᵖ) :
    ((sheafSections J A).obj U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedSections J A U :=
  (((sheafSections J A).obj U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf J A) (ComplexShape.up ℤ))

/-- `derivedSections J A U` is a right derived functor of the sections over `U` on cochain
complexes followed by the localization, with unit `derivedSectionsUnit J A U`. -/
instance isRightDerivedFunctor_derivedSections (U : Cᵒᵖ) :
    (derivedSections J A U).IsRightDerivedFunctor (derivedSectionsUnit J A U)
      (HomologicalComplex.quasiIso (Sheaf J A) (ComplexShape.up ℤ)) :=
  inferInstanceAs (Functor.IsRightDerivedFunctor _
    (Functor.totalRightDerivedUnit _ _ _) _)

/-! ### The derived constant sheaf -/

/-- **`Lπ^{-1} : D(A) ⥤ D(Sheaf J A)`**, the constant sheaf functor promoted to the unbounded
derived categories. The constant sheaf functor is exact — it is the constant presheaf functor,
which preserves all limits and colimits, followed by sheafification, which preserves finite
limits and, being a left adjoint, all colimits — so
`CategoryTheory.Functor.mapDerivedCategory` applies to it, and no derivation is needed: it is
its own left and right derived functor. -/
def derivedConstantSheaf : DerivedCategory A ⥤ DerivedCategory (Sheaf J A) :=
  (constantSheaf J A).mapDerivedCategory

/-- **The derived constant sheaf is induced by the degreewise one**: the comparison between
applying the constant sheaf functor degreewise and then localizing, and localizing and then
applying the derived functor, is invertible. -/
def derivedConstantSheafFactors :
    DerivedCategory.Q ⋙ derivedConstantSheaf J A ≅
      (constantSheaf J A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (constantSheaf J A).mapDerivedCategoryFactors

/-- `derivedConstantSheaf J A` is a left derived functor of the degreewise constant sheaf functor
followed by the localization, with comparison map `derivedConstantSheafFactors J A`. -/
instance isLeftDerivedFunctor_derivedConstantSheaf :
    (derivedConstantSheaf J A).IsLeftDerivedFunctor
      (derivedConstantSheafFactors J A).hom
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (derivedConstantSheafFactors J A)

/-! ### The two composites are derived functors -/

omit [PreservesFiniteLimits (constantSheaf J A)] [PreservesFiniteColimits (constantSheaf J A)]
  [HasDerivedCategory.{w₂} (Sheaf J A)] [IsGrothendieckAbelian.{w₀} (Sheaf J A)] in
/-- The sections on cochain complexes followed by the localization and then by any functor
inverts the quasi-isomorphisms between K-injective complexes, because the first two steps
already do. -/
private lemma invertsQuasiIso_sections_comp_Q_comp {D : Type*} [Category D] (U : Cᵒᵖ)
    (T : DerivedCategory A ⥤ D) :
    InvertsQuasiIsoOfIsKInjective
      (((sheafSections J A).obj U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⋙ T) := by
  intro K L f hK hL hf
  have := invertsQuasiIso_mapHomologicalComplex_comp_Q
    ((sheafSections J A).obj U) f hK hL hf
  exact inferInstanceAs (IsIso (T.map
    ((((sheafSections J A).obj U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).map f)))

/-- **The composite `Lπ^{-1} ⋙ RΓ` is a left derived functor**, with the comparison map induced
by the one of `Lπ^{-1}`: that comparison is invertible, so there is nothing to derive. -/
instance isLeftDerivedFunctor_derivedConstantSheaf_comp (U : Cᵒᵖ) :
    (derivedConstantSheaf J A ⋙ derivedSections J A U).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        (derivedConstantSheafFactors J A).hom (derivedSections J A U))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    (asIso ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
      (derivedConstantSheafFactors J A).hom (derivedSections J A U)))

/-- **The composite `RΓ ⋙ Lπ^{-1}` is a right derived functor**, with the comparison map induced
by the unit of `RΓ`. By the K-injective criterion it suffices that the comparison be invertible
at every K-injective complex, and there it is the image under `Lπ^{-1}` of the unit of `RΓ`,
which is invertible. -/
instance isRightDerivedFunctor_derivedSections_comp (U : Cᵒᵖ) :
    (derivedSections J A U ⋙ derivedConstantSheaf J A).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedSectionsUnit J A U) (derivedConstantSheaf J A) ≫
        (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso (Sheaf J A) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective (L := DerivedCategory.Q) _ _
    (invertsQuasiIso_sections_comp_Q_comp J A U (derivedConstantSheaf J A))]
  intro K hK
  have := isIso_app_of_isKInjective DerivedCategory.Q (derivedSections J A U)
    (derivedSectionsUnit J A U)
    (invertsQuasiIso_mapHomologicalComplex_comp_Q ((sheafSections J A).obj U)) K hK
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id]
  exact Functor.map_isIso _ _

/-! ### The derived adjunction -/

variable {T : C} (hT : IsTerminal T)

/-- **The derived constant sheaf is left adjoint to the unbounded derived sections over a
terminal object**,

`Lπ^{-1} ⊣ RΓ(T, -)` on `D(A) ⇄ D(Sheaf J A)`,

obtained by deriving the degreewise adjunction of `CategoryTheory.constantSheafAdj`. The right
adjoint is not exact and is not claimed to be; only the left one is, and
`CategoryTheory.Adjunction.derived` asks exactness of neither. -/
def derivedConstantSheafAdjunction :
    derivedConstantSheaf J A ⊣ derivedSections J A (op T) :=
  (Adjunction.mapHomologicalComplexAdjunction (constantSheafAdj J A hT)
      (ComplexShape.up ℤ)).derived
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso (Sheaf J A) (ComplexShape.up ℤ))
    (derivedConstantSheafFactors J A).hom (derivedSectionsUnit J A (op T))

/-- **The unit of the derived adjunction on the class of a complex** `K` of coefficients is the
class of the degreewise unit `K ⟶ Γ(T, π^{-1}K)` followed by the comparison map of the derived
sections, read through the factorization of the derived constant sheaf. -/
theorem derivedConstantSheafAdjunction_unit_fac (K : CochainComplex A ℤ) :
    (derivedConstantSheafAdjunction J A hT).unit.app (DerivedCategory.Q.obj K) ≫
        (derivedSections J A (op T)).map ((derivedConstantSheafFactors J A).hom.app K) =
      DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
          (constantSheafAdj J A hT) (ComplexShape.up ℤ)).unit.app K) ≫
        (derivedSectionsUnit J A (op T)).app
          (((constantSheaf J A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Adjunction.derivedη_fac_app _
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (derivedConstantSheafFactors J A).hom (derivedSectionsUnit J A (op T)) K

/-! ### The small étale site of a scheme -/

section SmallEtale

open AlgebraicGeometry

variable (X : Scheme.{u})

/-- **The identity of `X`, as a terminal object of the small étale site of `X`.** -/
def smallEtaleTerminalObj : X.Etale :=
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)

/-- The identity of `X` is indeed a terminal object of the small étale site: any étale `U → X`
factors through it uniquely. -/
def smallEtaleTerminalObjIsTerminal : IsTerminal (smallEtaleTerminalObj X) :=
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mkIdTerminal _ _

/-- **Abelian sheaves on the small étale site of a scheme form a Grothendieck abelian
category**: the site is essentially small, so this is
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`. -/
theorem isGrothendieckAbelian_smallEtaleAbelianSheaf :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  let : EssentiallySmall.{u + 1} X.Etale := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} X.smallEtaleTopology
    AddCommGrpCat.{u + 1}

/-- The constant abelian sheaf functor on the small étale site is left exact. -/
theorem preservesFiniteLimits_constantSheaf_smallEtale :
    PreservesFiniteLimits (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstanceAs (PreservesFiniteLimits
    (Functor.const _ ⋙ presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))

/-- The constant abelian sheaf functor on the small étale site is right exact. -/
theorem preservesFiniteColimits_constantSheaf_smallEtale :
    PreservesFiniteColimits (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstanceAs (PreservesFiniteColimits
    (Functor.const _ ⋙ presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))

attribute [local instance] isGrothendieckAbelian_smallEtaleAbelianSheaf
  preservesFiniteLimits_constantSheaf_smallEtale
  preservesFiniteColimits_constantSheaf_smallEtale

variable [HasDerivedCategory.{w₁} AddCommGrpCat.{u + 1}]
  [HasDerivedCategory.{w₂} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The derived constant sheaf is left adjoint to the unbounded derived global sections on the
small étale site of a scheme**,

`Lπ^{-1} ⊣ RΓ(X, -)` on `D(Ab) ⇄ D(X_étale)`.

This is the instance of `derivedConstantSheafAdjunction` at the site of [Stacks, Tag 0F0E]: the
hypotheses of that construction hold here because the small étale site is essentially small,
hence its abelian sheaves are Grothendieck abelian, and because `X ──𝟙──> X` is a terminal
object of it. -/
def smallEtaleDerivedConstantSheafAdjunction :
    derivedConstantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⊣
      derivedSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (op (smallEtaleTerminalObj X)) :=
  derivedConstantSheafAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (smallEtaleTerminalObjIsTerminal X)

end SmallEtale

end Stacks.Cohomology.SiteConstantSheaf

end
