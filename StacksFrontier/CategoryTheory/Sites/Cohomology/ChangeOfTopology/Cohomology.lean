module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImages
public import StacksFrontier.CategoryTheory.Abelian.InjectiveResolution.DescHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonClass
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.CategoryTheory.Sites.AbelianSheavesAbelian

/-! # Cohomology under a change of topology

In the situation of Stacks 0EZ3 write `ε : C_τ → C_τ'` for the change-of-topology morphism
from the finer site to the coarser one. Pulling back cohomology classes along `ε` gives, for
every object `X` and every degree `i`, a natural map
`H^i_{τ'}(X, ε_{X,*} F) ⟶ H^i_τ(X, F)`.

This file constructs that map and, assuming the vanishing condition `(V_n)` for the higher
change-of-topology direct images, proves the two assertions of Stacks 0EZC about it in degree
`n + 1`: it is injective, and its image consists exactly of the classes which become zero
after restriction to the members of some covering for the coarser topology.

## Main definitions

* `Stacks.sheafCohomology` and `Stacks.sheafCohomologyRestriction`: cohomology of an abelian
  sheaf over an object of a site, as the right derived functors of sections, and the
  restriction maps between them.
* `Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition`: the condition `(V_n)`
  that the higher change-of-topology direct images of the sheaves in `𝒜_X` vanish in degrees
  `1, …, n`, for every object `X` of the site.
* `Stacks.ComparingTopologies.cohomologyComparison`: the natural change-of-topology map on
  cohomology.

## Main results

* `Stacks.ComparingTopologies.cohomologyComparison_eq_injectiveResolution`: the comparison map
  is computed, in every degree, by any augmentation-preserving comparison of an injective
  resolution of `ε_{X,*} F` with the direct image of an injective resolution of `F`. This pins
  the map down independently of any choice of resolution.
* `Stacks.ComparingTopologies.exists_injectiveResolutionComparison`: such a comparison of
  resolutions exists.
* `Stacks.ComparingTopologies.mono_cohomologyComparison`: under `(V_n)` the comparison map is
  injective in degree `n + 1`.
* `Stacks.ComparingTopologies.mem_range_cohomologyComparison_iff`: under `(V_n)` a class in
  degree `n + 1` lies in the image of the comparison map exactly when it restricts to zero on
  the members of a covering for the coarser topology.

## Implementation notes

The change-of-topology morphism is represented by `abelianComparisonPushforward`, the
inclusion of the sheaves for the finer localized topology among the sheaves for the coarser
one; it has an exact left adjoint, namely sheafification, hence preserves injective objects.
Cohomology over `X` is cohomology over the terminal object `Over.mk (𝟙 X)` of the localized
site, which is how the derived functors of sections see it.

The comparison map is the edge map of the Grothendieck spectral sequence, but it is built here
without any spectral sequence: an injective resolution of `ε_{X,*} F` admits an
augmentation-preserving map to the direct image of an injective resolution of `F` — the latter
is a complex of injectives, though not a resolution — and the induced map on the homology of
the complexes of sections is the comparison. Any two such maps of resolutions are homotopic,
which is what makes the construction natural and independent of the choice.

Both halves of the tag are proved by the same elementary mechanism, a *partial* comparison in
the other direction. Under `(V_n)` the direct image of the resolution of `F` is exact in
degrees `1, …, n`, so a map back to it from the resolution of `ε_{X,*} F` can be constructed
degree by degree up to degree `n + 1` using injectivity, and the two composites differ from the
identity by a partial homotopy. That is enough to invert the comparison on homology in degree
`n + 1` up to a boundary, which gives injectivity, and to identify its image with the classes
whose representing cocycle is locally a boundary, which is the covering condition. The
translation between "locally in the image of a map of sheaves" and "zero after a covering" uses
that a short exact sequence of sheaves is exact on sections up to refinement.

## References

* [Stacks Project, Tag 0EZC](https://stacks.math.columbia.edu/tag/0EZC)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks

/-- Evaluation of abelian sheaves at an object of the site is additive. -/
instance sheafSections_obj_additive {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology D) (U : D) :
    ((sheafSections J Ab.{max u v}).obj (op U)).Additive := ⟨rfl⟩

/-- Cohomology of an abelian sheaf over an object of a site, defined as the right derived
functors of the sections over that object. -/
@[sga "4 V 2.4.1" "H^q(X, special case"]
abbrev sheafCohomology {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
    (F : Sheaf J Ab.{max u v}) (U : D) (n : ℕ) : Ab.{max u v} :=
  (((sheafSections J Ab.{max u v}).obj (op U)).rightDerived n).obj F

/-- The restriction map on cohomology induced by a morphism `f : U ⟶ V` of the site: it goes
from cohomology over `V` to cohomology over `U`. -/
def sheafCohomologyRestriction {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
    {U V : D} (f : U ⟶ V) (n : ℕ) (F : Sheaf J Ab.{max u v}) :
    sheafCohomology J F V n ⟶ sheafCohomology J F U n :=
  (NatTrans.rightDerived ((sheafSections J Ab.{max u v}).map f.op) n).app F

/-- Sections over the terminal object `Over.mk (𝟙 X)` of a localized site; these are the global
sections of a sheaf on the site localized at `X`. -/
abbrev globalSectionsOver {D : Type u} [Category.{v} D] (J : GrothendieckTopology D) (X : D) :
    Sheaf (J.over X) Ab.{max u v} ⥤ Ab.{max u v} :=
  (sheafSections (J.over X) Ab.{max u v}).obj (op (Over.mk (𝟙 X)))

/-- The degree-zero augmentation of an injective resolution of `F` is a monomorphism, stated
with its source spelled `F` rather than as the degree-zero term of the complex `F[0]`.

The two spellings are equal only by unfolding at default transparency, so Mathlib's instance,
which is indexed by the second, is invisible to instance search whenever the use site has
already fixed the source to be `F` — which it does as soon as the augmentation is composed with
anything typed in terms of `F`. -/
private instance mono_resolution_ι_f_zero {A : Type*} [Category* A] [Abelian A] {F : A}
    (I : InjectiveResolution F) : @Mono A _ F (I.cocomplex.X 0) (I.ι.f 0) := by
  have h : Mono (I.ι.f 0) := inferInstance
  exact h

namespace ComparingTopologies

variable {C : Type u} [Category.{v} C]

/-- The condition `(Vₙ)` of Stacks 0EZ3: for every object `X` of the site, the higher
change-of-topology direct images of the sheaves in `𝒜_X` vanish in the degrees `1, …, n`. -/
def CohomologyComparison.vanishingCondition (S : CohomologyComparison C) (n : ℕ) : Prop :=
  ∀ (X : C) (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}),
    S.fineWeakSerre X F →
      ∀ i : ℕ, 1 ≤ i → i ≤ n →
        IsZero (((abelianComparisonPushforward S.fineCoverage
          S.coarseCoverage S.coarse_le_fine X).rightDerived i).obj F)

/-- The change-of-topology direct image preserves injective objects, having an exact left
adjoint. -/
private lemma changePreservesInjectives (K K' : Precoverage C) (h : K' ≤ K) (X : C) :
    (abelianComparisonPushforward K K' h X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (abelianComparisonAdjunction K K' h X)

section

variable {A : Type*} [Category* A] [Abelian A]
    {F : A} (J : InjectiveResolution F) (K : CochainComplex A ℕ)
    [∀ i, Injective (K.X i)]

/-- An augmentation-compatible map from an injective resolution of `F` into any complex of
injectives receiving `F` in degree zero. Only injectivity of the terms of the target is used,
not exactness. -/
private def resolutionDesc (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0) :
    J.cocomplex ⟶ K := by
  let g₀ : J.cocomplex.X 0 ⟶ K.X 0 := Injective.factorThru a (J.ι.f 0)
  have hg₀ : J.ι.f 0 ≫ g₀ = a := Injective.comp_factorThru _ _
  let g₁ : J.cocomplex.X 1 ⟶ K.X 1 := J.exact₀.descToInjective
    (g₀ ≫ K.d 0 1) (by
      dsimp
      rw (transparency := .default) [← Category.assoc, hg₀, ha]
      rfl)
  have hg₁ : J.cocomplex.d 0 1 ≫ g₁ = g₀ ≫ K.d 0 1 :=
    J.exact₀.comp_descToInjective _ _
  refine CochainComplex.mkHom _ _ g₀ g₁ hg₁.symm ?_
  rintro n ⟨g, g', hg⟩
  refine ⟨(J.exact_succ n).descToInjective (g' ≫ K.d (n + 1) (n + 2)) ?_, ?_⟩
  · dsimp
    rw [← Category.assoc, ← hg, Category.assoc, K.d_comp_d, comp_zero]
  · exact ((J.exact_succ n).comp_descToInjective _ _).symm

/-- The map produced by `resolutionDesc` is compatible with the augmentations. -/
private lemma resolutionDesc_zero (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0) :
    J.ι.f 0 ≫ (resolutionDesc J K a ha).f 0 = a := by
  change J.ι.f 0 ≫ Injective.factorThru a (J.ι.f 0) = a
  exact Injective.comp_factorThru _ _

end

section

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [Abelian A] [Abelian B] [Abelian D] [HasInjectiveResolutions A]
    [HasInjectiveResolutions B]
    (T : A ⥤ B) [T.Additive] [T.PreservesInjectiveObjects]
    (G : B ⥤ D) [G.Additive]

/-- An augmentation-compatible comparison from an injective resolution of `T.obj F` to the
image under `T` of an injective resolution of `F`. The target is a complex of injectives
because `T` preserves injective objects, but it is not a resolution. -/
private def resolutionComparison {F : A} (I : InjectiveResolution F)
    (J : InjectiveResolution (T.obj F)) :
    J.cocomplex ⟶ (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex := by
  have : ∀ i, Injective (((T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).X i) :=
    fun i => T.injective_obj _
  exact resolutionDesc J _ (T.map (I.ι.f 0))
    (by
      rw (transparency := .default) [Functor.mapHomologicalComplex_obj_d, ← T.map_comp,
        I.ι_f_zero_comp_complex_d, T.map_zero])

omit [HasInjectiveResolutions A] [HasInjectiveResolutions B] in
/-- The comparison of resolutions is compatible with the augmentations. -/
private lemma resolutionComparison_zero {F : A} (I : InjectiveResolution F)
    (J : InjectiveResolution (T.obj F)) :
    J.ι.f 0 ≫ (resolutionComparison T I J).f 0 = T.map (I.ι.f 0) := by
  have : ∀ i, Injective (((T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).X i) :=
    fun i => T.injective_obj _
  unfold resolutionComparison
  apply resolutionDesc_zero

/-- The value at `F` of the comparison between the derived functors of `G` at `T.obj F` and
the derived functors of `T ⋙ G` at `F`, computed from a choice of resolutions and of an
augmentation-compatible map between them. -/
private abbrev comparisonValue (i : ℕ) {F : A} (I : InjectiveResolution F)
    (J : InjectiveResolution (T.obj F))
    (φ : J.cocomplex ⟶ (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex) :
    (G.rightDerived i).obj (T.obj F) ⟶ ((T ⋙ G).rightDerived i).obj F :=
  (J.isoRightDerivedObj G i).hom ≫
    (G.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ i).map φ ≫
    (I.isoRightDerivedObj (T ⋙ G) i).inv

/-- The comparison values are natural in the object: two of them, for arbitrary resolutions
and arbitrary augmentation-compatible maps, fit into the naturality square of a morphism. -/
private lemma comparisonValue_naturality (i : ℕ) {F F' : A} (f : F ⟶ F')
    (I : InjectiveResolution F) (I' : InjectiveResolution F')
    (J : InjectiveResolution (T.obj F)) (J' : InjectiveResolution (T.obj F'))
    (φ : J.cocomplex ⟶ (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (φ' : J'.cocomplex ⟶ (T.mapHomologicalComplex (.up ℕ)).obj I'.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = T.map (I.ι.f 0))
    (hφ' : J'.ι.f 0 ≫ φ'.f 0 = T.map (I'.ι.f 0)) :
    (G.rightDerived i).map (T.map f) ≫ comparisonValue T G i I' J' φ' =
      comparisonValue T G i I J φ ≫ ((T ⋙ G).rightDerived i).map f := by
  let a := InjectiveResolution.desc f I' I
  let b := InjectiveResolution.desc (T.map f) J' J
  have hb : J.ι.f 0 ≫ b.f 0 = T.map f ≫ J'.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero _ _ _
  have ha : I.ι.f 0 ≫ a.f 0 = f ≫ I'.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero _ _ _
  have : ∀ i, Injective (((T.mapHomologicalComplex (.up ℕ)).obj I'.cocomplex).X i) :=
    fun i => T.injective_obj _
  have h : Homotopy (b ≫ φ') (φ ≫ (T.mapHomologicalComplex _).map a) := by
    refine InjectiveResolution.descHomotopy' _ _ (InjectiveResolution.ι_comp_ext _ _ ?_)
    dsimp
    rw (transparency := .default) [← Category.assoc, hb, Category.assoc, hφ',
      ← Category.assoc, hφ, ← T.map_comp, ← T.map_comp, ha]
    rfl
  have hh := (G.mapHomotopy h).homologyMap_eq i
  dsimp [comparisonValue]
  rw [← Category.assoc, ← Category.assoc,
    J.isoRightDerivedObj_hom_naturality (T.map f) J' b hb G i]
  simp only [Category.assoc]
  rw [I.isoRightDerivedObj_inv_naturality f I' a ha (T ⋙ G) i]
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map,
    Functor.map_comp, HomologicalComplex.homologyMap_comp] at hh ⊢
  convert (congrArg
    (fun k => (J.isoRightDerivedObj G i).hom ≫ k ≫
      (I'.isoRightDerivedObj (T ⋙ G) i).inv) hh) using 1 <;>
    exact congrArg (fun k => (J.isoRightDerivedObj G i).hom ≫ k) (Category.assoc _ _ _).symm

end

section

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [Abelian A] [Abelian B] [Abelian D] [HasInjectiveResolutions A]
    [HasInjectiveResolutions B]
    (T : A ⥤ B) [T.Additive] [T.PreservesInjectiveObjects]
    (G : B ⥤ D) [G.Additive]

/-- The canonical comparison `T ⋙ Rⁱ G ⟶ Rⁱ (T ⋙ G)` for a functor `T` preserving injective
objects. It is the edge map of the Grothendieck spectral sequence, obtained here directly from
the chosen injective resolutions. -/
private def derivedComparison (i : ℕ) : T ⋙ G.rightDerived i ⟶ (T ⋙ G).rightDerived i where
  app F := comparisonValue T G i (injectiveResolution F) (injectiveResolution (T.obj F))
    (resolutionComparison T _ _)
  naturality _ _ f := comparisonValue_naturality T G i f _ _ _ _ _ _
    (resolutionComparison_zero T _ _) (resolutionComparison_zero T _ _)

/-- The components of `derivedComparison` are computed by *any* pair of injective resolutions
together with any augmentation-compatible map between them. -/
private lemma derivedComparison_eq (i : ℕ) {F : A} (I : InjectiveResolution F)
    (J : InjectiveResolution (T.obj F))
    (φ : J.cocomplex ⟶ (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = T.map (I.ι.f 0)) :
    (derivedComparison T G i).app F = comparisonValue T G i I J φ := by
  have h := comparisonValue_naturality T G i (𝟙 F) (injectiveResolution F) I
    (injectiveResolution (T.obj F)) J (resolutionComparison T _ _) φ
    (resolutionComparison_zero T _ _) hφ
  change (derivedComparison T G i).app F = _
  simpa [derivedComparison, Functor.map_id] using h.symm

end

/-- The natural change-of-topology map `H^i_{τ'}(U, ε_{X,*} F) ⟶ H^i_τ(U, F)` over an object `U`
of the localized site: the edge morphism of the pair `(ε_{X,*}, Γ_{τ'}(U, -))`, whose composite is
`Γ_τ(U, -)`. Over the terminal object it is `cohomologyComparison`. -/
@[no_expose]
def cohomologyComparisonAt (S : CohomologyComparison C) (X : C) (U : Over X) (i : ℕ) :
    abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X ⋙
        ((sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj
            (op U)).rightDerived i ⟶ ((sheafSections
                (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U)).rightDerived i :=
  letI : (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).PreservesInjectiveObjects :=
    changePreservesInjectives S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  derivedComparison
    (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
    ((sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U)) i

/-- The natural change-of-topology map `H^i_{τ'}(X, ε_{X,*} F) ⟶ H^i_τ(X, F)`, given by
pulling back cohomology classes along `ε_X`. -/
@[stacks 0EZC "canonical cohomology map", no_expose]
def cohomologyComparison (S : CohomologyComparison C) (X : C) (i : ℕ) :
    abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X ⋙
        (globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerived i ⟶
      (globalSectionsOver S.fineCoverage.toGrothendieck X).rightDerived i :=
  letI : (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).PreservesInjectiveObjects :=
    changePreservesInjectives S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  derivedComparison
    (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
    (globalSectionsOver S.coarseCoverage.toGrothendieck X) i

/-- A comparison of an injective resolution of the change-of-topology direct image with the
direct image of an injective resolution, compatible with the augmentations, exists. -/
theorem exists_injectiveResolutionComparison (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((abelianComparisonPushforward S.fineCoverage
      S.coarseCoverage S.coarse_le_fine X).obj F)) :
    ∃ φ : J.cocomplex ⟶
      ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex,
      J.ι.f 0 ≫ φ.f 0 =
        (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).map (I.ι.f 0) := by
  have : (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).PreservesInjectiveObjects :=
    changePreservesInjectives S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  exact ⟨resolutionComparison (abelianComparisonPushforward S.fineCoverage
    S.coarseCoverage S.coarse_le_fine X) I J, resolutionComparison_zero _ _ _⟩

/-- An augmentation-preserving comparison from an injective resolution of the coarse direct
image to the direct image of an injective resolution computes the canonical cohomology map.
This characterizes its components in every degree. -/
@[stacks 0EZC "canonical map via injective resolutions"]
theorem cohomologyComparison_eq_injectiveResolution (S : CohomologyComparison C) (X : C) (i : ℕ)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((abelianComparisonPushforward S.fineCoverage
      S.coarseCoverage S.coarse_le_fine X).obj F))
    (φ : J.cocomplex ⟶
      ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 =
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).map (I.ι.f 0)) :
    (cohomologyComparison S X i).app F =
      (J.isoRightDerivedObj (globalSectionsOver S.coarseCoverage.toGrothendieck X) i).hom ≫
        HomologicalComplex.homologyMap
          (((globalSectionsOver S.coarseCoverage.toGrothendieck X).mapHomologicalComplex
            (.up ℕ)).map φ) i ≫
          (I.isoRightDerivedObj (globalSectionsOver S.fineCoverage.toGrothendieck X) i).inv := by
  have : (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).PreservesInjectiveObjects :=
    changePreservesInjectives S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  exact derivedComparison_eq (abelianComparisonPushforward S.fineCoverage
    S.coarseCoverage S.coarse_le_fine X)
    (globalSectionsOver S.coarseCoverage.toGrothendieck X) i I J φ hφ

/-- The version of `cohomologyComparison_eq_injectiveResolution` over an object `U` of the
localized site: an augmentation-preserving comparison from an injective resolution of the coarse
direct image to the direct image of an injective resolution computes `cohomologyComparisonAt`. -/
theorem cohomologyComparisonAt_eq_injectiveResolution (S : CohomologyComparison C) (X : C)
    (U : Over X) (i : ℕ)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((abelianComparisonPushforward S.fineCoverage
      S.coarseCoverage S.coarse_le_fine X).obj F))
    (φ : J.cocomplex ⟶
      ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 =
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).map (I.ι.f 0)) :
    (cohomologyComparisonAt S X U i).app F =
      (J.isoRightDerivedObj (((sheafSections
          (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U))) i).hom ≫
        HomologicalComplex.homologyMap
          (((((sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj
              (op U))).mapHomologicalComplex
            (.up ℕ)).map φ) i ≫
          (I.isoRightDerivedObj (((sheafSections
              (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U))) i).inv := by
  have : (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).PreservesInjectiveObjects :=
    changePreservesInjectives S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  exact derivedComparison_eq (abelianComparisonPushforward S.fineCoverage
    S.coarseCoverage S.coarse_le_fine X)
    (((sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U))) i I J φ hφ

section Partial

variable {A : Type*} [Category* A] [Abelian A]

/-- A partial comparison in the direction opposite to a map of resolutions: if `K` receives `F`
in degree zero, is exact there and in the degrees `1, …, n`, and `L` is a complex of injectives
receiving `F` in degree zero, then there are maps `K.X i ⟶ L.X i` commuting with the
differentials up to degree `n` and compatible with the augmentations. -/
private lemma exists_partial_comparison
    (K L : CochainComplex A ℕ) [∀ i, Injective (L.X i)]
    {F : A} (a : F ⟶ K.X 0) [Mono a] (b : F ⟶ L.X 0)
    (ha : a ≫ K.d 0 1 = 0) (hb : b ≫ L.d 0 1 = 0)
    (hex₀ : (ShortComplex.mk a (K.d 0 1) ha).Exact)
    (n : ℕ) (hex : ∀ i, i < n → K.ExactAt (i + 1)) :
    ∃ f : ∀ i, K.X i ⟶ L.X i,
      a ≫ f 0 = b ∧ ∀ i, i ≤ n → f i ≫ L.d i (i + 1) = K.d i (i + 1) ≫ f (i + 1) := by
  let State (i : ℕ) := Σ' f : K.X i ⟶ L.X i, Σ' g : K.X (i + 1) ⟶ L.X (i + 1),
    i ≤ n → f ≫ L.d i (i + 1) = K.d i (i + 1) ≫ g
  let f₀ := Injective.factorThru b a
  have hf₀ : a ≫ f₀ = b := Injective.comp_factorThru _ _
  let f₁ := hex₀.descToInjective (f₀ ≫ L.d 0 1)
    (by dsimp; rw [← Category.assoc, hf₀, hb])
  let start : State 0 := ⟨f₀, f₁, fun _ => (hex₀.comp_descToInjective _ _).symm⟩
  let step (i : ℕ) (s : State i) : State (i + 1) := by
    refine ⟨s.2.1, ?_⟩
    by_cases hi : i + 1 ≤ n
    · have he : (ShortComplex.mk (K.d i (i + 1)) (K.d (i + 1) (i + 2)) (K.d_comp_d _ _ _)).Exact :=
        (K.exactAt_iff' i (i + 1) (i + 2) (by simp) (by simp)).1 (hex i (by omega))
      have hz : K.d i (i + 1) ≫ (s.2.1 ≫ L.d (i + 1) (i + 2)) = 0 := by
        rw [← Category.assoc, ← s.2.2 (by omega), Category.assoc, L.d_comp_d, comp_zero]
      exact ⟨he.descToInjective _ hz, fun _ => (he.comp_descToInjective _ _).symm⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  let seq : ∀ i, State i := Nat.rec start step
  have hseq (i : ℕ) : (seq (i + 1)).1 = (seq i).2.1 := by
    dsimp [seq, step]
  refine ⟨fun i => (seq i).1, hf₀, fun i hi => ?_⟩
  dsimp only
  rw [hseq]
  exact (seq i).2.2 hi

/-- A family of endomorphisms of an injective resolution which kills the augmentation and
commutes with the differentials below degree `m` is, in degree `m`, a boundary up to the
differential: this is the inductive step of the homotopy to zero. -/
private lemma exists_homotopy_component
    {F : A} (J : InjectiveResolution F) (f : ∀ i, J.cocomplex.X i ⟶ J.cocomplex.X i)
    (hf₀ : J.ι.f 0 ≫ f 0 = 0) (m : ℕ)
    (hf : ∀ i, i < m → f i ≫ J.cocomplex.d i (i + 1) = J.cocomplex.d i (i + 1) ≫ f (i + 1)) :
    ∃ h : J.cocomplex.X (m + 1) ⟶ J.cocomplex.X m,
      f m ≫ J.cocomplex.d m (m + 1) =
        J.cocomplex.d m (m + 1) ≫ h ≫ J.cocomplex.d m (m + 1) := by
  induction m with
  | zero =>
    refine ⟨J.exact₀.descToInjective (f 0) hf₀, ?_⟩
    rw [← Category.assoc, J.exact₀.comp_descToInjective]
  | succ m ih =>
    obtain ⟨h, hh⟩ := ih (fun i hi => hf i (by omega))
    have hz : J.cocomplex.d m (m + 1) ≫ (f (m + 1) - h ≫ J.cocomplex.d m (m + 1)) = 0 := by
      rw [Preadditive.comp_sub, ← hf m (by omega), ← hh, sub_self]
    refine ⟨(J.exact_succ m).descToInjective _ hz, ?_⟩
    rw [← Category.assoc, (J.exact_succ m).comp_descToInjective,
      Preadditive.sub_comp, Category.assoc, J.cocomplex.d_comp_d, comp_zero, sub_zero]

/-- In degree `n + 1` such a family of endomorphisms is a sum of two boundary terms, which is
exactly the homotopy datum needed to invert a comparison on homology in that degree. -/
private lemma exists_homotopy_succ
    {F : A} (J : InjectiveResolution F) (f : ∀ i, J.cocomplex.X i ⟶ J.cocomplex.X i)
    (hf₀ : J.ι.f 0 ≫ f 0 = 0) (n : ℕ)
    (hf : ∀ i, i ≤ n → f i ≫ J.cocomplex.d i (i + 1) = J.cocomplex.d i (i + 1) ≫ f (i + 1)) :
    ∃ (k : J.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
      (h : J.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1)),
      f (n + 1) = k ≫ J.cocomplex.d n (n + 1) + J.cocomplex.d (n + 1) (n + 2) ≫ h := by
  obtain ⟨k, hk⟩ := exists_homotopy_component J f hf₀ n (fun i hi => hf i (by omega))
  have hz : J.cocomplex.d n (n + 1) ≫ (f (n + 1) - k ≫ J.cocomplex.d n (n + 1)) = 0 := by
    rw [Preadditive.comp_sub, ← hf n le_rfl, ← hk, sub_self]
  refine ⟨k, (J.exact_succ n).descToInjective _ hz, ?_⟩
  rw [(J.exact_succ n).comp_descToInjective, add_sub_cancel]

/-- A family of endomorphisms of a complex of injectives which kills the augmentation and
commutes with the differentials below degree `n` is a boundary up to the differential in degree
`n`, when the complex is exact in the relevant degrees. -/
private lemma partial_homotopy_component
    (K : CochainComplex A ℕ) [∀ i, Injective (K.X i)]
    {F : A} (a : F ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (hex₀ : (ShortComplex.mk a (K.d 0 1) ha).Exact)
    (f : ∀ i, K.X i ⟶ K.X i) (hf₀ : a ≫ f 0 = 0) (n : ℕ)
    (hex : ∀ i, i < n → K.ExactAt (i + 1))
    (hf : ∀ i, i < n → f i ≫ K.d i (i + 1) = K.d i (i + 1) ≫ f (i + 1)) :
    ∃ h : K.X (n + 1) ⟶ K.X n,
      f n ≫ K.d n (n + 1) = K.d n (n + 1) ≫ h ≫ K.d n (n + 1) := by
  induction n with
  | zero =>
    refine ⟨hex₀.descToInjective (f 0) hf₀, ?_⟩
    rw [← Category.assoc, hex₀.comp_descToInjective]
  | succ n ih =>
    obtain ⟨h, hh⟩ := ih (fun i hi => hex i (by omega)) (fun i hi => hf i (by omega))
    have he : (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2)) (K.d_comp_d _ _ _)).Exact :=
      (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).1 (hex n (by omega))
    have hz : K.d n (n + 1) ≫ (f (n + 1) - h ≫ K.d n (n + 1)) = 0 := by
      rw [Preadditive.comp_sub, ← hf n (by omega), ← hh, sub_self]
    refine ⟨he.descToInjective _ hz, ?_⟩
    rw [← Category.assoc, he.comp_descToInjective, Preadditive.sub_comp,
      Category.assoc, K.d_comp_d, comp_zero, sub_zero]

end Partial

section Homology

/-- A homology class of a complex of abelian groups vanishes exactly when its cocycle is a
boundary. -/
private lemma homologyπ_eq_zero_iff (K : CochainComplex Ab ℕ) (n : ℕ) (z : K.cycles (n + 1)) :
    K.homologyπ (n + 1) z = 0 ↔ ∃ b : K.X n, K.toCycles n (n + 1) b = z := by
  let S := ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
    (K.toCycles_comp_homologyπ _ _)
  have he : S.Exact := S.exact_of_g_is_cokernel (K.homologyIsCokernel _ _ (by simp))
  constructor
  · exact (S.ab_exact_iff.1 he) z
  · rintro ⟨b, rfl⟩
    exact S.ab_zero_apply b

/-- The same criterion, read on the underlying element of the term of the complex. -/
private lemma homologyπ_eq_zero_iff_boundary (K : CochainComplex Ab ℕ) (n : ℕ)
    (z : K.cycles (n + 1)) :
    K.homologyπ (n + 1) z = 0 ↔ ∃ b : K.X n, K.d n (n + 1) b = K.iCycles (n + 1) z := by
  rw [homologyπ_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    simpa only [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i]
      using congrArg (K.iCycles (n + 1)) hb
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles (n + 1))).1 inferInstance
    simpa only [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i] using hb

/-- A map of complexes of abelian groups which admits a partial inverse in degrees `n` and
`n + 1`, up to a homotopy in degree `n + 1`, is injective on homology in degree `n + 1`. -/
private lemma mono_homologyMap_of_partial_inverse (J K : CochainComplex Ab ℕ)
    (φ : J ⟶ K) (n : ℕ) (a : K.X n ⟶ J.X n) (b : K.X (n + 1) ⟶ J.X (n + 1))
    (hab : a ≫ J.d n (n + 1) = K.d n (n + 1) ≫ b)
    (k : J.X (n + 1) ⟶ J.X n) (h : J.X (n + 2) ⟶ J.X (n + 1))
    (hh : φ.f (n + 1) ≫ b - 𝟙 _ = k ≫ J.d n (n + 1) + J.d (n + 1) (n + 2) ≫ h) :
    Mono (HomologicalComplex.homologyMap φ (n + 1)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  apply (injective_iff_map_eq_zero _).2
  intro ξ hξ
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (J.homologyπ (n + 1))).1 inferInstance ξ
  have hz : K.homologyπ (n + 1) (HomologicalComplex.cyclesMap φ (n + 1) z) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
    exact hξ
  obtain ⟨x, hx⟩ := (homologyπ_eq_zero_iff K n _).1 hz
  have hx' : K.d n (n + 1) x = φ.f (n + 1) (J.iCycles (n + 1) z) := by
    have hhx := congrArg (fun v => K.iCycles (n + 1) v) hx
    change (K.toCycles n (n + 1) ≫ K.iCycles (n + 1)) x =
      (HomologicalComplex.cyclesMap φ (n + 1) ≫ K.iCycles (n + 1)) z at hhx
    rw [HomologicalComplex.toCycles_i, HomologicalComplex.cyclesMap_i] at hhx
    exact hhx
  have hcycle : J.d (n + 1) (n + 2) (J.iCycles (n + 1) z) = 0 := by
    rw [← ConcreteCategory.comp_apply, J.iCycles_d]
    rfl
  have hb : b (φ.f (n + 1) (J.iCycles (n + 1) z)) = J.d n (n + 1) (a x) := by
    rw [← hx', ← ConcreteCategory.comp_apply, ← hab, ConcreteCategory.comp_apply]
  have hhom := congrArg (fun v : J.X (n + 1) ⟶ J.X (n + 1) => v (J.iCycles (n + 1) z)) hh
  have hz' : J.d n (n + 1) (a x - k (J.iCycles (n + 1) z)) = J.iCycles (n + 1) z := by
    change b (φ.f (n + 1) (J.iCycles (n + 1) z)) - J.iCycles (n + 1) z =
      J.d n (n + 1) (k (J.iCycles (n + 1) z)) +
        h (J.d (n + 1) (n + 2) (J.iCycles (n + 1) z)) at hhom
    rw [hcycle, map_zero, add_zero, hb] at hhom
    rw [map_sub]
    exact sub_eq_iff_eq_add.2 (sub_eq_iff_eq_add.1 hhom |>.trans (add_comm _ _))
  apply (homologyπ_eq_zero_iff J n z).2
  refine ⟨a x - k (J.iCycles (n + 1) z), ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (J.iCycles (n + 1))).1 inferInstance
  simpa only [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i] using hz'

/-- Applying an additive functor to abelian groups to an augmentation-compatible map from an
injective resolution into a complex of injectives which is exact in degrees `1, …, n` gives a
map which is injective on homology in degree `n + 1`. -/
private lemma mono_homologyMap_map_of_exact {A : Type*} [Category* A] [Abelian A]
    (G : A ⥤ Ab) [G.Additive] {F : A} (J : InjectiveResolution F)
    (K : CochainComplex A ℕ) (a : F ⟶ K.X 0) (hmono : Mono a)
    (ha : a ≫ K.d 0 1 = 0) (hex₀ : (ShortComplex.mk a (K.d 0 1) ha).Exact)
    (φ : J.cocomplex ⟶ K) (hφ : J.ι.f 0 ≫ φ.f 0 = a)
    (n : ℕ) (hex : ∀ i, i < n → K.ExactAt (i + 1)) :
    Mono (HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℕ)).map φ) (n + 1)) := by
  have := hmono
  obtain ⟨ψ, hψ₀, hψ⟩ := exists_partial_comparison K J.cocomplex a (J.ι.f 0) ha
    J.ι_f_zero_comp_complex_d hex₀ n hex
  let f (i : ℕ) := φ.f i ≫ ψ i - 𝟙 (J.cocomplex.X i)
  have hf₀ : J.ι.f 0 ≫ f 0 = 0 := by
    dsimp [f]
    rw (transparency := .default) [Preadditive.comp_sub, ← Category.assoc, hφ, hψ₀,
      Category.comp_id, sub_self]
    rfl
  have hf (i : ℕ) (hi : i ≤ n) :
      f i ≫ J.cocomplex.d i (i + 1) = J.cocomplex.d i (i + 1) ≫ f (i + 1) := by
    dsimp [f]
    rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
      Category.assoc, hψ i hi, ← Category.assoc, φ.comm, Category.assoc]
  obtain ⟨k, h, hh⟩ := exists_homotopy_succ J f hf₀ n hf
  apply mono_homologyMap_of_partial_inverse _ _ _ n (G.map (ψ n)) (G.map (ψ (n + 1)))
    _ (G.map k) (G.map h)
  · simpa [f, Functor.mapHomologicalComplex]
      using congrArg G.map hh
  · simpa [Functor.mapHomologicalComplex] using congrArg G.map (hψ n le_rfl)

end Homology

section Local

variable {D : Type u} [Category.{v} D]

/-- The complex of sections of a complex of sheaves over an object of the site. -/
private abbrev sectionsComplex {J : GrothendieckTopology D}
    (K : CochainComplex (Sheaf J Ab.{max u v}) ℕ) (U : D) :=
  (((sheafSections J Ab.{max u v}).obj (op U)).mapHomologicalComplex (.up ℕ)).obj K

/-- A cohomology class represented by a cocycle of sections over `U` restricts to zero over `V`
exactly when that cocycle becomes a boundary over `V`. -/
private lemma restriction_eq_zero_iff_boundary
    (J : GrothendieckTopology D) {F : Sheaf J Ab.{max u v}} (I : InjectiveResolution F)
    {U V : D} (f : V ⟶ U) (n : ℕ) (z : (sectionsComplex I.cocomplex U).cycles (n + 1)) :
    sheafCohomologyRestriction J f (n + 1) F
      ((I.isoRightDerivedObj ((sheafSections J Ab.{max u v}).obj (op U)) (n + 1)).inv
        ((sectionsComplex I.cocomplex U).homologyπ (n + 1) z)) = 0 ↔
    ∃ b : (I.cocomplex.X n).obj.obj (op V),
      (I.cocomplex.d n (n + 1)).hom.app (op V) b =
        (I.cocomplex.X (n + 1)).obj.map f.op
          ((sectionsComplex I.cocomplex U).iCycles (n + 1) z) := by
  let α := (sheafSections J Ab.{max u v}).map f.op
  let φ := (NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex
  rw [sheafCohomologyRestriction, I.rightDerived_app_eq]
  simp only [ConcreteCategory.comp_apply]
  rw (transparency := .default) [Iso.inv_hom_id_apply]
  rw [← map_zero (ConcreteCategory.hom
      (I.isoRightDerivedObj ((sheafSections J Ab.{max u v}).obj (op V)) (n + 1)).inv),
    (AddCommGrpCat.mono_iff_injective
      (I.isoRightDerivedObj ((sheafSections J Ab.{max u v}).obj (op V))
        (n + 1)).inv).1 inferInstance |>.eq_iff]
  change HomologicalComplex.homologyMap φ (n + 1)
    ((sectionsComplex I.cocomplex U).homologyπ (n + 1) z) = 0 ↔ _
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, homologyπ_eq_zero_iff_boundary]
  have he : (sectionsComplex I.cocomplex V).iCycles (n + 1)
      (HomologicalComplex.cyclesMap φ (n + 1) z) =
        (I.cocomplex.X (n + 1)).obj.map f.op
          ((sectionsComplex I.cocomplex U).iCycles (n + 1) z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ (n + 1)) z
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb.trans he⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb.trans he.symm⟩

/-- Naturality of a morphism of sheaves, read on elements. -/
private lemma sheaf_naturality_apply
    {J : GrothendieckTopology D} {A B : Sheaf J Ab.{max u v}}
    (f : A ⟶ B) {U V : D} (g : V ⟶ U) (z : A.obj.obj (op U)) :
    f.hom.app (op V) (A.obj.map g.op z) = B.obj.map g.op (f.hom.app (op U) z) :=
  ConcreteCategory.congr_hom (f.hom.naturality g.op) z

/-- If a homology class of the sections of `K` over `U` comes from the sections of an exact
complex `L`, then its cocycle is locally a boundary. -/
private lemma locally_boundary_of_homology_image
    {J : GrothendieckTopology D} (L K : CochainComplex (Sheaf J Ab.{max u v}) ℕ)
    (φ : L ⟶ K) (n : ℕ) (hL : L.ExactAt (n + 1)) (U : D)
    (z : (sectionsComplex K U).cycles (n + 1))
    (η : (sectionsComplex L U).homology (n + 1))
    (hη : HomologicalComplex.homologyMap
      ((((sheafSections J Ab.{max u v}).obj (op U)).mapHomologicalComplex (.up ℕ)).map φ)
        (n + 1) η =
      (sectionsComplex K U).homologyπ (n + 1) z) :
    Presheaf.imageSieve (K.d n (n + 1)).hom ((sectionsComplex K U).iCycles (n + 1) z) ∈ J U := by
  let P := sectionsComplex L U
  let Q := sectionsComplex K U
  let f := (((sheafSections J Ab.{max u v}).obj (op U)).mapHomologicalComplex (.up ℕ)).map φ
  obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (P.homologyπ (n + 1))).1 inferInstance η
  have hz : Q.homologyπ (n + 1) (HomologicalComplex.cyclesMap f (n + 1) y - z) = 0 := by
    rw [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply,
      ← HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
    exact hη
  obtain ⟨b, hb⟩ := (homologyπ_eq_zero_iff_boundary Q n _).1 hz
  have hb' : Q.d n (n + 1) b = f.f (n + 1) (P.iCycles (n + 1) y) - Q.iCycles (n + 1) z := by
    rw [map_sub, ← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply] at hb
    exact hb
  have hy : (L.d (n + 1) (n + 2)).hom.app (op U) (P.iCycles (n + 1) y) = 0 := by
    change P.d (n + 1) (n + 2) (P.iCycles (n + 1) y) = 0
    rw [← ConcreteCategory.comp_apply, P.iCycles_d]
    rfl
  have hloc := Stacks.AbelianSheaves.imageSieve_mem_of_exact (L.sc' n (n + 1) (n + 2))
    ((L.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).1 hL) U _ hy
  apply J.superset_covering (S := Presheaf.imageSieve (L.d n (n + 1)).hom (P.iCycles (n + 1) y))
    ?_ hloc
  intro V g hg
  obtain ⟨x, hx⟩ := hg
  refine ⟨(φ.f n).hom.app (op V) x - (K.X n).obj.map g.op b, ?_⟩
  rw [map_sub, sheaf_naturality_apply]
  have hf := ConcreteCategory.congr_hom
    (congrArg (fun t : L.X n ⟶ K.X (n + 1) => t.hom.app (op V)) (φ.comm n (n + 1))) x
  change (K.d n (n + 1)).hom.app (op V) ((φ.f n).hom.app (op V) x) =
    (φ.f (n + 1)).hom.app (op V) ((L.d n (n + 1)).hom.app (op V) x) at hf
  rw [hf, hx, sheaf_naturality_apply]
  change _ - (K.X (n + 1)).obj.map g.op (Q.d n (n + 1) b) = _
  rw [hb', map_sub]
  exact sub_sub_cancel _ _

/-- Conversely, a cocycle which is locally a boundary represents a homology class in the image,
given a partial inverse in the relevant degrees. -/
private lemma homology_image_of_locally_boundary
    {J : GrothendieckTopology D} (L K : CochainComplex (Sheaf J Ab.{max u v}) ℕ)
    (φ : L ⟶ K) (n : ℕ) (a : K.X n ⟶ L.X n)
    (b : K.X (n + 1) ⟶ L.X (n + 1)) (h : K.X (n + 1) ⟶ K.X n)
    (hab : a ≫ L.d n (n + 1) = K.d n (n + 1) ≫ b)
    (hh : K.d n (n + 1) ≫ (b ≫ φ.f (n + 1) - 𝟙 _) =
      K.d n (n + 1) ≫ h ≫ K.d n (n + 1))
    (U : D) (z : (sectionsComplex K U).cycles (n + 1))
    (hz : Presheaf.imageSieve (K.d n (n + 1)).hom
      ((sectionsComplex K U).iCycles (n + 1) z) ∈ J U) :
    ∃ η : (sectionsComplex L U).homology (n + 1),
      HomologicalComplex.homologyMap
        ((((sheafSections J Ab.{max u v}).obj (op U)).mapHomologicalComplex (.up ℕ)).map φ)
          (n + 1) η =
        (sectionsComplex K U).homologyπ (n + 1) z := by
  let P := sectionsComplex L U
  let Q := sectionsComplex K U
  let f := (((sheafSections J Ab.{max u v}).obj (op U)).mapHomologicalComplex (.up ℕ)).map φ
  let x : (K.X (n + 1)).obj.obj (op U) := Q.iCycles (n + 1) z
  have hcycle : P.d (n + 1) (n + 2) (b.hom.app (op U) x) = 0 :=
    Stacks.AbelianSheaves.app_eq_zero_of_imageSieve_mem (K.d n (n + 1))
      (b ≫ L.d (n + 1) (n + 2))
      (by rw [← Category.assoc, ← hab, Category.assoc, L.d_comp_d, comp_zero]) U x hz
  let E := ShortComplex.mk (P.iCycles (n + 1)) (P.d (n + 1) (n + 2)) (P.iCycles_d _ _)
  have hE : E.Exact := E.exact_of_f_is_kernel (P.cyclesIsKernel (n + 1) (n + 2) (by simp))
  obtain ⟨y, hy⟩ := (E.ab_exact_iff.1 hE) (b.hom.app (op U) x) hcycle
  refine ⟨P.homologyπ (n + 1) y, ?_⟩
  have hzero := Stacks.AbelianSheaves.app_eq_zero_of_imageSieve_mem (K.d n (n + 1))
    (b ≫ φ.f (n + 1) - 𝟙 _ - h ≫ K.d n (n + 1))
    (by rw [Preadditive.comp_sub, hh, sub_self]) U x hz
  have hx : (φ.f (n + 1)).hom.app (op U) (b.hom.app (op U) x) - x =
      Q.d n (n + 1) (h.hom.app (op U) x) := by
    change (_ - x) - (K.d n (n + 1)).hom.app (op U) (h.hom.app (op U) x) = 0 at hzero
    exact sub_eq_zero.1 hzero
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  apply sub_eq_zero.1
  rw [← map_sub]
  apply (homologyπ_eq_zero_iff_boundary Q n _).2
  refine ⟨h.hom.app (op U) x, ?_⟩
  have hci : Q.iCycles (n + 1) (HomologicalComplex.cyclesMap f (n + 1) y) =
      (φ.f (n + 1)).hom.app (op U) (P.iCycles (n + 1) y) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f (n + 1)) y
  rw [map_sub, hci, show P.iCycles (n + 1) y = b.hom.app (op U) x from hy]
  exact hx.symm

/-- A sieve on the terminal object of a localized site is covering exactly when it contains the
members of a covering family of the object itself. -/
private lemma covering_over_terminal_iff (K : Precoverage C)
    [K.HasIsos] [K.HasPullbacks] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition]
    (X : C) (s : Sieve (Over.mk (𝟙 X))) :
    s ∈ K.toGrothendieck.over X (Over.mk (𝟙 X)) ↔
      ∃ R : Presieve X, R ∈ K X ∧ ∀ ⦃V : C⦄ (f : V ⟶ X), R f →
        s (Over.homMk (U := Over.mk f) (V := Over.mk (𝟙 X)) f (by simp)) := by
  have he {V : C} (f : V ⟶ X) :
      (Sieve.overEquiv (Over.mk (𝟙 X)) s) f ↔
        s (Over.homMk (U := Over.mk f) (V := Over.mk (𝟙 X)) f (by simp)) := by
    change ((Sieve.overEquiv (Over.mk (𝟙 X))).symm
      (Sieve.overEquiv (Over.mk (𝟙 X)) s))
        (Over.homMk (U := Over.mk f) (V := Over.mk (𝟙 X)) f (by simp)) ↔ _
    rw [OrderIso.symm_apply_apply]
  rw [GrothendieckTopology.mem_over_iff,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  constructor
  · rintro ⟨R, hR, h⟩
    exact ⟨R, hR, fun {_} f hf => (he f).1 (h _ _ hf)⟩
  · rintro ⟨R, hR, h⟩
    exact ⟨R, hR, fun _ f hf => (he f).2 (h f hf)⟩

/-- The two descriptions of the image of the map on homology: coming from the sections of the
resolution, and being locally a boundary. -/
private lemma homology_image_iff_locally_boundary
    {J : GrothendieckTopology D} {F : Sheaf J Ab.{max u v}} (L : InjectiveResolution F)
    (K : CochainComplex (Sheaf J Ab.{max u v}) ℕ) [∀ i, Injective (K.X i)]
    (a : F ⟶ K.X 0) (hmono : Mono a) (ha : a ≫ K.d 0 1 = 0)
    (hex₀ : (ShortComplex.mk a (K.d 0 1) ha).Exact)
    (φ : L.cocomplex ⟶ K) (hφ : L.ι.f 0 ≫ φ.f 0 = a)
    (n : ℕ) (hex : ∀ i, i < n → K.ExactAt (i + 1))
    (U : D) (z : (sectionsComplex K U).cycles (n + 1)) :
    (∃ η : (sectionsComplex L.cocomplex U).homology (n + 1),
      HomologicalComplex.homologyMap
        ((((sheafSections J Ab.{max u v}).obj (op U)).mapHomologicalComplex (.up ℕ)).map φ)
          (n + 1) η =
        (sectionsComplex K U).homologyπ (n + 1) z) ↔
      Presheaf.imageSieve (K.d n (n + 1)).hom
        ((sectionsComplex K U).iCycles (n + 1) z) ∈ J U := by
  constructor
  · rintro ⟨η, hη⟩
    apply locally_boundary_of_homology_image L.cocomplex K φ n _ U z η hη
    exact (L.cocomplex.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).2 (L.exact_succ n)
  · intro hz
    have := hmono
    obtain ⟨ψ, hψ₀, hψ⟩ := exists_partial_comparison K L.cocomplex a (L.ι.f 0) ha
      L.ι_f_zero_comp_complex_d hex₀ n hex
    let f (i : ℕ) := ψ i ≫ φ.f i - 𝟙 (K.X i)
    have hf₀ : a ≫ f 0 = 0 := by
      dsimp [f]
      rw (transparency := .default) [Preadditive.comp_sub, ← Category.assoc, hψ₀, hφ,
        Category.comp_id, sub_self]
    have hf (i : ℕ) (hi : i ≤ n) :
        f i ≫ K.d i (i + 1) = K.d i (i + 1) ≫ f (i + 1) := by
      dsimp [f]
      rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
        Category.assoc, φ.comm, ← Category.assoc, hψ i hi, Category.assoc]
    obtain ⟨h, hh⟩ := partial_homotopy_component K a ha hex₀ f hf₀ n hex
      (fun i hi => hf i (by omega))
    exact homology_image_of_locally_boundary L.cocomplex K φ n (ψ n) (ψ (n + 1)) h
      (hψ n le_rfl) (by rw [← hf n le_rfl]; exact hh) U z hz

end Local

/-- Applying a limit-preserving additive functor to an injective resolution gives a complex
with monic augmentation which is left exact in degree zero, and exact in degrees `1, …, n` when
the higher derived functors vanish there. -/
private lemma map_resolution_exactness {A B : Type*} [Category* A] [Category* B] [Abelian A]
    [Abelian B] [HasInjectiveResolutions A] (T : A ⥤ B) [T.Additive] [PreservesLimits T]
    {F : A} (I : InjectiveResolution F) (n : ℕ)
    (hV : ∀ i, 1 ≤ i → i ≤ n → IsZero ((T.rightDerived i).obj F)) :
    ∃ ha : T.map (I.ι.f 0) ≫ ((T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).d 0 1 = 0,
      (ShortComplex.mk (T.map (I.ι.f 0)) _ ha).Exact ∧ Mono (T.map (I.ι.f 0)) ∧
        ∀ j, j < n → ((T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (j + 1) := by
  have ha : T.map (I.ι.f 0) ≫ ((T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).d 0 1 = 0 := by
    change T.map (I.ι.f 0) ≫ T.map (I.cocomplex.d 0 1) = 0
    rw [← T.map_comp, I.ι_f_zero_comp_complex_d, T.map_zero]
  refine ⟨ha, ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ I.isLimitKernelFork T),
    mono_of_isLimit_fork (KernelFork.mapIsLimit _ I.isLimitKernelFork T), fun j hj => ?_⟩
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hV (j + 1) (by omega) (by omega)).of_iso (I.isoRightDerivedObj T (j + 1)).symm

/-- An element of the source of `f ≫ g`, for a monomorphism `g`, hits the image of `q` exactly
when `q` is in the image of `f`; the source is allowed to be changed by an isomorphism. -/
private lemma exists_comp_apply_eq_iff.{w} {A B C D : Ab.{w}} (e : A ≅ B) (f : B ⟶ C)
    (g : C ⟶ D) [Mono g] (q : C) :
    (∃ η : A, (e.hom ≫ f ≫ g) η = g q) ↔ ∃ η : B, f η = q := by
  constructor
  · rintro ⟨η, hη⟩
    exact ⟨e.hom η, (AddCommGrpCat.mono_iff_injective g).1 inferInstance hη⟩
  · rintro ⟨η, rfl⟩
    exact ⟨e.inv η, by simp⟩

/-- Under `(Vₙ)`, the change-of-topology map over an object `U` of the localized site is
injective on cohomology in degree `n + 1`. -/
private lemma mono_cohomologyComparisonAt_aux (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C) (U : Over X)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F) :
    Mono ((cohomologyComparisonAt S X U (n + 1)).app F) := by
  let T := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  let I := injectiveResolution F
  let J := injectiveResolution (T.obj F)
  let K := (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have : PreservesLimits T :=
      (abelianComparisonAdjunction _ _ S.coarse_le_fine X).rightAdjoint_preservesLimits
  obtain ⟨ha, hex₀, hmono, hex⟩ := map_resolution_exactness T I n (hV X F hF)
  obtain ⟨φ, hφ⟩ := exists_injectiveResolutionComparison S X F I J
  have hmap := mono_homologyMap_map_of_exact
    (((sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj
        (op U))) J K _ hmono ha hex₀ φ hφ n hex
  rw [cohomologyComparisonAt_eq_injectiveResolution S X U (n + 1) F I J φ hφ]
  have h2 := (inferInstance : Mono ((I.isoRightDerivedObj
    ((sheafSections (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U)) (n + 1)).inv))
  exact mono_comp' inferInstance (mono_comp' hmap h2)

/-- Under `(Vₙ)`, every class of degree `n + 1` over `U` is represented by a cocycle `z`, and it
is in the image of the change-of-topology map exactly when `z` is locally a boundary. -/
private lemma exists_cycle_and_range_iff (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C) (U : Over X)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F)
    (ξ : sheafCohomology (S.fineCoverage.toGrothendieck.over X) F U (n + 1)) :
    let T := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
    let I := injectiveResolution F
    let K := (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    ∃ z : (sectionsComplex K U).cycles (n + 1),
      ξ = (I.isoRightDerivedObj ((sheafSections (S.fineCoverage.toGrothendieck.over X)
        Ab.{max u v}).obj (op U)) (n + 1)).inv ((sectionsComplex K U).homologyπ (n + 1) z) ∧
      ((∃ η : sheafCohomology (S.coarseCoverage.toGrothendieck.over X) (T.obj F) U (n + 1),
          (cohomologyComparisonAt S X U (n + 1)).app F η = ξ) ↔
        Presheaf.imageSieve (K.d n (n + 1)).hom ((sectionsComplex K U).iCycles (n + 1) z) ∈
          S.coarseCoverage.toGrothendieck.over X U) := by
  intro T I K
  let G := ((sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U))
  let H := ((sheafSections (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U))
  let J := injectiveResolution (T.obj F)
  let P := sectionsComplex J.cocomplex U
  let Q := sectionsComplex K U
  have : PreservesLimits T :=
      (abelianComparisonAdjunction _ _ S.coarse_le_fine X).rightAdjoint_preservesLimits
  have : T.PreservesInjectiveObjects := changePreservesInjectives _ _ _ _
  have : ∀ i, Injective (K.X i) := fun i => T.injective_obj _
  obtain ⟨ha, hex₀, hmono, hex⟩ := map_resolution_exactness T I n (hV X F hF)
  obtain ⟨φ, hφ⟩ := exists_injectiveResolutionComparison S X F I J
  let f := (G.mapHomologicalComplex (.up ℕ)).map φ
  let eI := I.isoRightDerivedObj H (n + 1)
  let eJ := J.isoRightDerivedObj G (n + 1)
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective
    (Q.homologyπ (n + 1))).1 inferInstance (eI.hom ξ)
  have hξ : ξ = eI.inv (Q.homologyπ (n + 1) z) := by
    rw [hz, Iso.hom_inv_id_apply]
  refine ⟨z, hξ, ?_⟩
  rw [hξ]
  have hmap : (cohomologyComparisonAt S X U (n + 1)).app F =
      eJ.hom ≫ HomologicalComplex.homologyMap f (n + 1) ≫ eI.inv :=
    cohomologyComparisonAt_eq_injectiveResolution S X U (n + 1) F I J φ hφ
  rw [hmap]
  exact (exists_comp_apply_eq_iff eJ _ eI.inv _).trans
    (homology_image_iff_locally_boundary J K (T.map (I.ι.f 0)) hmono ha hex₀ φ hφ n hex U z)

/-- **Stacks 0EZC.** Under `(Vₙ)`, the change-of-topology map on cohomology in degree `n + 1`
is injective. -/
@[stacks 0EZC "injectivity"]
theorem mono_cohomologyComparison (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F) :
    Mono ((cohomologyComparison S X (n + 1)).app F) :=
  mono_cohomologyComparisonAt_aux S n hV X (Over.mk (𝟙 X)) F hF

/-- **Stacks 0EZC.** Under `(Vₙ)`, a class in degree `n + 1` is in the image of the
change-of-topology map on cohomology precisely when it becomes zero on the members of a
covering for the coarser topology. -/
@[stacks 0EZC "image of the map"]
theorem mem_range_cohomologyComparison_iff (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F)
    (ξ : sheafCohomology (S.fineCoverage.toGrothendieck.over X) F (Over.mk (𝟙 X)) (n + 1)) :
    (∃ η : sheafCohomology (S.coarseCoverage.toGrothendieck.over X)
        ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).obj F) (Over.mk (𝟙 X)) (n + 1),
        (cohomologyComparison S X (n + 1)).app F η = ξ) ↔
      (∃ R : Presieve X, R ∈ S.coarseCoverage X ∧
        ∀ ⦃V : C⦄ (f : V ⟶ X), R f →
          sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X)
            (Over.homMk (U := Over.mk f) (V := Over.mk (𝟙 X)) f (by simp))
            (n + 1) F ξ = 0) := by
  obtain ⟨z, rfl, h⟩ := exists_cycle_and_range_iff S n hV X (Over.mk (𝟙 X)) F hF ξ
  refine h.trans ?_
  rw [covering_over_terminal_iff]
  constructor
  · rintro ⟨R, hR, h⟩
    refine ⟨R, hR, fun {_} g hg => ?_⟩
    apply (restriction_eq_zero_iff_boundary (S.fineCoverage.toGrothendieck.over X)
      (injectiveResolution F)
      (Over.homMk (U := Over.mk g) (V := Over.mk (𝟙 X)) g (by simp)) n z).2
    exact h g hg
  · rintro ⟨R, hR, h⟩
    refine ⟨R, hR, fun {_} g hg => ?_⟩
    exact (restriction_eq_zero_iff_boundary (S.fineCoverage.toGrothendieck.over X)
      (injectiveResolution F)
      (Over.homMk (U := Over.mk g) (V := Over.mk (𝟙 X)) g (by simp)) n z).1 (h g hg)

/-- Under `(Vₙ)`, the change-of-topology map on cohomology over any object of the localized
site is injective in degree `n + 1`. -/
theorem mono_cohomologyComparisonAt (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C) (U : Over X)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F) :
    Mono ((cohomologyComparisonAt S X U (n + 1)).app F) :=
  mono_cohomologyComparisonAt_aux S n hV X U F hF

/-- Under `(Vₙ)`, a class of degree `n + 1` over an object `U` of the localized site is in the
image of the change-of-topology map over `U` exactly when it dies on a covering of `U` for the
coarser topology. -/
theorem mem_range_cohomologyComparisonAt_iff (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C) (U : Over X)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F)
    (ξ : sheafCohomology (S.fineCoverage.toGrothendieck.over X) F U (n + 1)) :
    (∃ η : sheafCohomology (S.coarseCoverage.toGrothendieck.over X)
        ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).obj F) U (n + 1),
        (cohomologyComparisonAt S X U (n + 1)).app F η = ξ) ↔
      (∃ R : (S.coarseCoverage.toGrothendieck.over X).Cover U, ∀ g : R.Arrow,
        sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X) g.f (n + 1) F ξ = 0) := by
  obtain ⟨z, rfl, h⟩ := exists_cycle_and_range_iff S n hV X U F hF ξ
  rw [h]
  constructor
  · intro h
    exact ⟨⟨_, h⟩, fun g ↦ (restriction_eq_zero_iff_boundary (S.fineCoverage.toGrothendieck.over X)
      (injectiveResolution F) g.f n z).2 g.hf⟩
  · rintro ⟨R, hR⟩
    exact (S.coarseCoverage.toGrothendieck.over X).superset_covering
      (fun Z g hg ↦ (restriction_eq_zero_iff_boundary (S.fineCoverage.toGrothendieck.over X)
        (injectiveResolution F) g n z).1 (hR ⟨Z, g, hg⟩)) R.2

/-- **The change-of-topology map on cohomology is natural in the object of the localized
site**: it commutes with the restriction maps along `k : U' ⟶ U`. -/
theorem cohomologyComparisonAt_naturality (S : CohomologyComparison C) (X : C) {U' U : Over X}
    (k : U' ⟶ U) (i : ℕ) (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) :
    (cohomologyComparisonAt S X U i).app F ≫
        sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X) k i F =
      sheafCohomologyRestriction (S.coarseCoverage.toGrothendieck.over X) k i
          ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
            S.coarse_le_fine X).obj F) ≫
        (cohomologyComparisonAt S X U' i).app F := by
  let I := injectiveResolution F
  let J := injectiveResolution ((abelianComparisonPushforward S.fineCoverage
    S.coarseCoverage S.coarse_le_fine X).obj F)
  obtain ⟨φ, hφ⟩ := exists_injectiveResolutionComparison S X F I J
  let αc := (sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).map k.op
  have key : (((sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj
      (op U)).mapHomologicalComplex (.up ℕ)).map φ ≫
        (NatTrans.mapHomologicalComplex αc (.up ℕ)).app
          (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
            S.coarse_le_fine X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) =
      (NatTrans.mapHomologicalComplex αc (.up ℕ)).app J.cocomplex ≫
        (((sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj
          (op U')).mapHomologicalComplex (.up ℕ)).map φ :=
    ((NatTrans.mapHomologicalComplex αc (.up ℕ)).naturality φ)
  have hkey := congrArg (fun g => HomologicalComplex.homologyMap g i) key
  simp only [HomologicalComplex.homologyMap_comp] at hkey
  rw [cohomologyComparisonAt_eq_injectiveResolution S X U i F I J φ hφ,
    cohomologyComparisonAt_eq_injectiveResolution S X U' i F I J φ hφ,
    sheafCohomologyRestriction, sheafCohomologyRestriction,
    InjectiveResolution.rightDerived_app_eq _ I i, InjectiveResolution.rightDerived_app_eq _ J i]
  have gen : ∀ {Q₁ Q₂ Q₃ Q₄ Q₅ Q₆ : Ab.{max u v}} (a : Q₁ ⟶ Q₂) (b : Q₂ ⟶ Q₃) (c : Q₄ ≅ Q₃)
      (d : Q₃ ⟶ Q₅) (e : Q₅ ⟶ Q₆), (a ≫ b ≫ c.inv) ≫ c.hom ≫ d ≫ e = a ≫ (b ≫ d) ≫ e := by
    intros
    simp
  exact (gen _ _ _ _ _).trans
    ((congrArg (fun z => (J.isoRightDerivedObj
      ((sheafSections (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U)) i).hom ≫
        z ≫ (I.isoRightDerivedObj
          ((sheafSections (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}).obj (op U'))
            i).inv) hkey).trans (gen _ _ _ _ _).symm)

end ComparingTopologies

end Stacks

end
