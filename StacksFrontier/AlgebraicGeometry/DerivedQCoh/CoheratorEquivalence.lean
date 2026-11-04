module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ComparisonAffine
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ComparisonEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.CoheratorQuasiInverse
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedModules
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison functor is an equivalence: the first clause of Stacks 09T6

Let `X` be a quasi-compact quasi-separated scheme. [Stacks, Tag 06VT] provides the comparison
functor `i_X : D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X)` from the derived category of the quasi-coherent
`𝒪_X`-modules to the full subcategory of `D(𝒪_X)` on the complexes with quasi-coherent
cohomology. [Stacks, Tag 09T6] asserts that `i_X` is an equivalence, with quasi-inverse the
derived coherator `RQ_X`, under the hypothesis that for every affine open `U ⊆ X` the right
derived functor `Φ` of `j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)` fits into the commutative square
`i_X ∘ Φ ≅ Rj_* ∘ i_U`. That hypothesis is
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible`, recorded in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/CoheratorQuasiInverse.lean`, where the *second* clause
— the identification of the quasi-inverse, given the equivalence — is proved. **This file proves
the first clause: the comparison functor is an equivalence.**

The proof is the source's induction on the number of affine opens needed to cover the support.
The inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is exact with right adjoint the coherator
([Stacks, Tag 077P]), and the coherator has a total right derived functor `RQ_X` because
`Mod(𝒪_X)` is Grothendieck abelian; the derived adjunction `ι_* ⊣ RQ_X` of [Stacks, Tag 09T5]
restricts along the fully faithful inclusion `J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` to an adjunction
`i_X ⊣ J ∘ RQ_X`. The comparison functor is conservative, because the derived inclusion detects
zero objects, so `i_X` is an equivalence as soon as the counit of `ι_* ⊣ RQ_X` is invertible at
every complex with quasi-coherent cohomology. The counit is a natural transformation of exact
functors of triangulated categories, hence invertible at the first vertex of a distinguished
triangle whenever it is invertible at the other two, and it is invertible at a zero object. The
induction step, for an affine open `U` and a complex `E` with quasi-coherent cohomology supported
on a closed set `S`, is the recollement triangle `E ⟶ Rj_*(E|_U) ⟶ C`: its third vertex is
supported on `S \ U`, and its second vertex has invertible counit because on the affine open `U`
the comparison functor is already an equivalence ([Stacks, Tag 06Z0]) and the commutative square
of the hypothesis identifies `Rj_* ∘ i_U` with `i_X ∘ Φ`, both `Rj_*` and `Φ` being fully
faithful.

## Main definitions

* `Stacks.DerivedQCoh.schemeDerivedCoherator` — the total right derived functor of the coherator
  `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` of [Stacks, Tag 077P] on an arbitrary scheme, with its derivation
  unit `Stacks.DerivedQCoh.schemeDerivedCoheratorUnit`; this is
  `Stacks.DerivedQCoh.affineDerivedCoherator` without the affineness.
* `Stacks.DerivedQCoh.mapDerivedCategoryCoheratorAdjunction` — the derived coherator adjunction
  `ι_* ⊣ RQ_X`, with the derived functor of the inclusion presented as
  `CategoryTheory.Functor.mapDerivedCategory`.
* `Stacks.DerivedQCoh.homotopyUnitOfCochainUnit` — a derivation unit on the cochain complexes
  read on the homotopy category. The converse direction is
  `Stacks.DerivedQCoh.cochainUnitOfHomotopyUnit` of
  `StacksFrontier/AlgebraicGeometry/DerivedQCoh/OpenPushforwardAdjunction.lean`, which is used here.

## Main results

* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_affineOpenCompatible` —
  **[Stacks, Tag 09T6], the equivalence clause**: on a quasi-compact quasi-separated scheme
  satisfying `Stacks.DerivedQCoh.AffineOpenPushforwardCompatible`, the comparison functor of
  [Stacks, Tag 06VT] is an equivalence.
* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_reflectsIsomorphisms_atModel` — the
  comparison functor is conservative, on an arbitrary scheme and at an arbitrary model of the two
  derived categories.
* `Stacks.DerivedQCoh.isRightDerivedFunctor_homotopyUnitOfCochainUnit` — a total right derived
  functor along the localization of the cochain complexes is one along the localization of the
  homotopy category.
* `Stacks.DerivedQCoh.derivedPushforward_fullyFaithful` and its quasi-coherent analogue — a total
  right derived functor of direct image along the inclusion of an open subscheme is fully
  faithful.

## Implementation notes

**Universes and the model of the derived categories.** Everything except the last section is
stated with the two derived categories of `X` as instance arguments, at an arbitrary model
`HasDerivedCategory.{w}`, as in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/WeakSerre/DerivedComparison.lean`. The main theorem
is stated at the *standard* model, `w = u + 1`, with
`CategoryTheory.HasDerivedCategory.standard` installed as a local instance of raised priority:
the support machinery it consumes, in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDerivedModules.lean`, is stated there,
following `StacksFrontier/AlgebraicGeometry/Perfect/SupportedCohomology.lean`. The priority is
raised for the reason recorded in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/NoetherianExtension/Basic.lean`: the import closure
carries the locally small models `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`,
`SheafOfModules.hasDerivedCategory` and
`Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent` as global instances at universe `u`, and
with two models in play at equal priority instance search no longer resolves
`HasDerivedCategory.{u + 1}`. The choice of model is immaterial to the content: the comparison
functor is an equivalence at one model exactly when it is at another, by
`Stacks.DerivedQCoh.isEquivalence_derivedQuasicoherentComparison_of_model`.

**The two spellings of the category of modules.** `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules X.ringCatSheaf` are the same type with separately declared `Category`,
`Preadditive` and `Abelian` instances, so instance search does not cross between them even though
terms do. The comparison functor and the hypothesis of [Stacks, Tag 09T6] are stated in the
second spelling and the restriction and direct image API in the first, so the functors used here
are re-ascribed to the second spelling — `Stacks.DerivedQCoh.modulesRestrict` beside the existing
`Stacks.DerivedQCoh.modulesPushforward` — and their additivity and exactness are re-registered
there. Where a statement of the support machinery is applied, the triangle it produces is
re-ascribed to the second spelling before the triangulated-subcategory API is used, since that
API is found by instance search only in one spelling at a time.

**Why the derivation units are translated between the two localizations.**
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` asks for the derivation units along the
localization `CategoryTheory.DerivedCategory.Q` of the cochain complexes, as [Stacks, Tag 08D8]
does, whereas the derived adjunctions of
`StacksFrontier/AlgebraicGeometry/DerivedTildeEquivalence/DerivedAdjunction.lean` and the support
machinery ask for them along the localization `CategoryTheory.DerivedCategory.Qh` of the homotopy
category. The two are interchangeable: a derivation unit on one side restricts or descends along
`CategoryTheory.HomotopyCategory.quotient` to one on the other, and both derived-functor
properties are detected by the invertibility of the unit at the K-injective complexes
(Spaltenstein's criterion
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`).

## References

* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 08D8](https://stacks.math.columbia.edu/tag/08D8)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe w w' v u

namespace Stacks.DerivedQCoh

section Conservativity

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory]

/-- A complex of quasi-coherent modules whose image under the derived inclusion
`D(QCoh(𝒪_X)) ⥤ D(𝒪_X)` is zero is itself zero: the inclusion is exact, so it carries the
cohomology of the complex to the cohomology of its image, and it is faithful. -/
theorem isZero_of_isZero_mapDerivedCategory_ι
    (A : DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (hA : IsZero ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.obj A)) :
    IsZero A := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  have hz : IsZero ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.obj
      ((DerivedCategory.homologyFunctor _ n).obj A)) :=
    (Functor.map_isZero (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n)
      hA).of_iso ((Functor.mapDerivedCategoryHomologyIso
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι n).app A).symm
  refine (IsZero.iff_id_eq_zero _).2
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map_injective ?_)
  simpa using (IsZero.iff_id_eq_zero _).1 hz

/-- **The comparison functor of [Stacks, Tag 06VT] is conservative.** A morphism of
`D(QCoh(𝒪_X))` whose image in `D_QCoh(𝒪_X)` is invertible is invertible.

The comparison functor is exact, so the cone of such a morphism is carried to a zero object, and
after the fully faithful inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` that says the cone has zero image
under the derived inclusion of the quasi-coherent modules; the cone is then zero by
`Stacks.DerivedQCoh.isZero_of_isZero_mapDerivedCategory_ι`, and a morphism whose cone vanishes is
an isomorphism.

`Stacks.DerivedQCoh.derivedQuasicoherentComparison_reflectsIsomorphisms` is the same assertion at
the locally small model alone, that is the case `w = u`. This one quantifies over the model, which
is what the dévissage below consumes — it runs at the standard model `w = u + 1` — and it is an
`instance`, so that the conservativity is available to instance search there. -/
instance derivedQuasicoherentComparison_reflectsIsomorphisms_atModel :
    (derivedQuasicoherentComparison.{w} X).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  obtain ⟨D, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  have hD : IsZero ((derivedQuasicoherentComparison.{w} X).obj D) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁
      ((derivedQuasicoherentComparison.{w} X).mapTriangle.obj (Pretriangulated.Triangle.mk f g δ))
      ((derivedQuasicoherentComparison.{w} X).map_distinguished _ hT) hf
  have hID : IsZero ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.obj D) :=
    (Functor.map_isZero (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι hD).of_iso
        ((derivedQuasicoherentComparisonCompι.{w} X).app D).symm
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ (Pretriangulated.Triangle.mk f g δ) hT).1
    (isZero_of_isZero_mapDerivedCategory_ι X D hID)

end Conservativity

section Shim

open Stacks.Injectives.KInjectiveResolution (InvertsQuasiIsoOfIsKInjective
  isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
  isRightDerivedFunctor_iff_isIso_app_of_isKInjective isIso_app_of_isKInjective
  quasiIso_mapHomologicalComplex_map_of_isKInjective)

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
  (G : A ⥤ B) [G.Additive] (R : DerivedCategory A ⥤ DerivedCategory B)

omit [HasDerivedCategory.{w} A] in
/-- Degreewise application of an additive functor followed by the localization of the cochain
complexes inverts the quasi-isomorphisms between K-injective complexes: an additive functor
carries such a quasi-isomorphism to a homotopy equivalence, hence to a quasi-isomorphism. -/
theorem invertsQuasiIsoOfIsKInjective_mapHomologicalComplex :
    InvertsQuasiIsoOfIsKInjective
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := B)) :=
  fun s hK hL hs =>
    Localization.inverts (DerivedCategory.Q (C := B))
      (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) _
      ((HomologicalComplex.mem_quasiIso_iff _).2
        (quasiIso_mapHomologicalComplex_map_of_isKInjective G s hK hL hs))

/-- Restricting the degreewise functor on homotopy categories along
`CategoryTheory.HomotopyCategory.quotient` gives back the degreewise functor on cochain complexes
followed by the localization `CategoryTheory.DerivedCategory.Q`. -/
def quotientCompMapHomotopyCategoryCompQhIso :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := B) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)

/-- Restricting `Qh ⋙ R` along `CategoryTheory.HomotopyCategory.quotient` gives back `Q ⋙ R`. -/
def quotientCompQhCompIso :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ (DerivedCategory.Qh ⋙ R) ≅
      DerivedCategory.Q (C := A) ⋙ R :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) R

/-- **A derivation unit on cochain complexes read on the homotopy category.** A natural
transformation `G(−) ⋙ Q ⟶ Q ⋙ R` out of the cochain complexes descends to the homotopy
category, the two sides being restrictions along `CategoryTheory.HomotopyCategory.quotient` of
functors on the homotopy category and that functor being a quotient. -/
def homotopyUnitOfCochainUnit
    (α : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := B) ⟶
      DerivedCategory.Q (C := A) ⋙ R) :
    G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R :=
  Quotient.natTransLift _
    ((quotientCompMapHomotopyCategoryCompQhIso G).hom ≫ α ≫ (quotientCompQhCompIso R).inv)

/-- **A total right derived functor along the localization of the cochain complexes is one along
the localization of the homotopy category.** Both are detected by the invertibility of the
derivation unit at the K-injective complexes, and the two units agree there by construction. -/
theorem isRightDerivedFunctor_homotopyUnitOfCochainUnit [IsGrothendieckAbelian.{w'} A]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (α : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := B) ⟶
      DerivedCategory.Q (C := A) ⋙ R)
    [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    R.IsRightDerivedFunctor (homotopyUnitOfCochainUnit G R α)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_quotient_isKInjective hA _ R _ fun I hI => ?_
  have hα : IsIso (α.app I) :=
    isIso_app_of_isKInjective.{w'} (DerivedCategory.Q (C := A)) R α
      (invertsQuasiIsoOfIsKInjective_mapHomologicalComplex G) I hI
  have happ : (homotopyUnitOfCochainUnit G R α).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =
      ((quotientCompMapHomotopyCategoryCompQhIso G).hom ≫ α ≫
        (quotientCompQhCompIso R).inv).app I := rfl
  rw [happ]
  dsimp only [NatTrans.comp_app]
  infer_instance

/-- The derived adjunction `L_* ⊣ R` for an adjunction `L ⊣ G` with `L` exact and `R` any total
right derived functor of `G` along the cochain complexes. -/
private def derivedAdjunctionOfCochainUnit [IsGrothendieckAbelian.{w'} A] {L : B ⥤ A}
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ G)
    (α : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := B) ⟶
      DerivedCategory.Q (C := A) ⋙ R)
    [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    L.mapDerivedCategory ⊣ R :=
  haveI := isRightDerivedFunctor_homotopyUnitOfCochainUnit G R hA α
  Stacks.SmallDerivedCategory.derivedAdjunction adj (Iso.refl _)
    (homotopyUnitOfCochainUnit G R α) hA

/-- **Total right derived functors of `G` are fully faithful when the counit of `L ⊣ G` is
invertible and `L` is exact**, as the counit of the derived adjunction is then invertible. -/
private def fullyFaithful_of_isIso_counit [IsGrothendieckAbelian.{w'} A] {L : B ⥤ A}
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ G)
    [IsIso adj.counit]
    (α : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := B) ⟶
      DerivedCategory.Q (C := A) ⋙ R)
    [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    R.FullyFaithful :=
  haveI := isRightDerivedFunctor_homotopyUnitOfCochainUnit G R hA α
  haveI : IsIso (derivedAdjunctionOfCochainUnit G R adj α hA).counit :=
    Stacks.SmallDerivedCategory.isIso_derivedAdjunction_counit adj (Iso.refl _)
      (homotopyUnitOfCochainUnit G R α) hA
  (derivedAdjunctionOfCochainUnit G R adj α hA).fullyFaithfulROfIsIsoCounit

end Shim

section Coherator

open Stacks.Injectives.KInjectiveResolution (hasRightDerivedFunctor_mapHomologicalComplex_comp_Q)

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory]

/-- **The derived coherator of a scheme** at the cochain-complex level: the total right derived
functor of the coherator `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` of [Stacks, Tag 077P] relative to
`CategoryTheory.DerivedCategory.Q`.

It exists because `Mod(𝒪_X)` is Grothendieck abelian, so every cochain complex of
`𝒪_X`-modules admits a K-injective resolution. This is
`Stacks.DerivedQCoh.affineDerivedCoherator` for an arbitrary scheme. -/
def schemeDerivedCoherator :
    DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (modulesCoherator X)
  ((modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- The derivation unit of `Stacks.DerivedQCoh.schemeDerivedCoherator`: the canonical comparison
from degreewise application of the coherator to its derived functor. -/
def schemeDerivedCoheratorUnit :
    (modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q
          (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶
      DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⋙ schemeDerivedCoherator.{w} X :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (modulesCoherator X)
  ((modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- `Stacks.DerivedQCoh.schemeDerivedCoherator` is a total right derived functor of the coherator,
which is the universal property characterising it. -/
instance schemeDerivedCoherator_isRightDerivedFunctor :
    (schemeDerivedCoherator.{w} X).IsRightDerivedFunctor (schemeDerivedCoheratorUnit.{w} X)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (modulesCoherator X)
  inferInstanceAs ((((modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ))).IsRightDerivedFunctor
    (((modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ)))
    (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)))

/-- **The derived coherator adjunction**: the derived functor of the exact inclusion
`ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is left adjoint to the derived coherator. This is
[Stacks, Tag 09T5] for the coherator adjunction `ι ⊣ Q_X` of [Stacks, Tag 077P], read at
`CategoryTheory.Functor.mapDerivedCategory` through
`Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory`. -/
def mapDerivedCategoryCoheratorAdjunction :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⊣
      schemeDerivedCoherator.{w} X :=
  (derivedCoheratorAdjunction X (schemeDerivedCoherator.{w} X)
      (schemeDerivedCoheratorUnit.{w} X)).ofNatIsoLeft
    (derivedFunctorOfExactIsoMapDerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι)

/-- **The comparison functor is an equivalence as soon as the counit of the derived coherator
adjunction is invertible on the complexes with quasi-coherent cohomology.**

Restricting the adjunction `ι_* ⊣ RQ_X` along the fully faithful inclusion
`J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` turns that hypothesis into the invertibility of the counit of
`i_X ⊣ J ∘ RQ_X`; the comparison functor is conservative, so its unit is invertible too, and an
adjunction with invertible unit and counit is an equivalence. -/
private theorem isEquivalence_of_isIso_counit_app_of_derivedCategoryB
    (hcounit : ∀ E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf),
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) E →
        IsIso ((mapDerivedCategoryCoheratorAdjunction.{w} X).counit.app E)) :
    (derivedQuasicoherentComparison.{w} X).IsEquivalence := by
  let J := (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι
  let a : derivedQuasicoherentComparison.{w} X ⊣ J ⋙ schemeDerivedCoherator.{w} X :=
    (mapDerivedCategoryCoheratorAdjunction.{w} X).restrictFullyFaithful
      (Functor.FullyFaithful.id _) (Functor.FullyFaithful.ofFullyFaithful J)
      (Functor.leftUnitor _ ≪≫ (derivedQuasicoherentComparisonCompι.{w} X).symm)
      (Functor.rightUnitor _).symm
  have hc (E : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory) :
      IsIso (a.counit.app E) := by
    have h₁ : IsIso ((mapDerivedCategoryCoheratorAdjunction.{w} X).counit.app (J.obj E)) :=
      hcounit E.obj E.property
    have h₂ : IsIso (J.map (a.counit.app E)) := by
      dsimp only [a]
      rw [Adjunction.map_restrictFullyFaithful_counit_app]
      infer_instance
    exact isIso_of_reflects_iso _ J
  have := NatIso.isIso_of_isIso_app a.counit
  exact isEquivalence_of_reflectsIsomorphisms_of_isIso_counit a

/-- The counit of the derived coherator adjunction is invertible at a zero object: both of its
sides are then zero objects, and every morphism between zero objects is invertible. -/
private theorem isIso_coheratorCounit_app_of_isZero
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) (hE : IsZero E) :
    IsIso ((mapDerivedCategoryCoheratorAdjunction.{w} X).counit.app E) :=
  let : (schemeDerivedCoherator.{w} X).Additive :=
    (mapDerivedCategoryCoheratorAdjunction.{w} X).right_adjoint_additive
  ((schemeDerivedCoherator.{w} X ⋙
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory).map_isZero hE).isIso hE _

/-- **The counit of the derived coherator adjunction is invertible at the first vertex of a
distinguished triangle as soon as it is invertible at the other two.** The derived coherator is
right adjoint to an exact functor of triangulated categories, hence itself exact and compatible
with translation, and the counit of such an adjunction is a natural transformation of exact
functors; two invertible components of a morphism of distinguished triangles force the third to
be invertible. -/
private theorem isIso_coheratorCounit_app₁_of_app₂₃
    (T : Pretriangulated.Triangle (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)))
    (hT : T ∈ distTriang (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)))
    (h₂ : IsIso ((mapDerivedCategoryCoheratorAdjunction.{w} X).counit.app T.obj₂))
    (h₃ : IsIso ((mapDerivedCategoryCoheratorAdjunction.{w} X).counit.app T.obj₃)) :
    IsIso ((mapDerivedCategoryCoheratorAdjunction.{w} X).counit.app T.obj₁) := by
  let : (schemeDerivedCoherator.{w} X).CommShift ℤ :=
    (mapDerivedCategoryCoheratorAdjunction.{w} X).rightAdjointCommShift ℤ
  let : (mapDerivedCategoryCoheratorAdjunction.{w} X).CommShift ℤ :=
    (mapDerivedCategoryCoheratorAdjunction.{w} X).commShift_of_leftAdjoint ℤ
  let : (schemeDerivedCoherator.{w} X).IsTriangulated :=
    (mapDerivedCategoryCoheratorAdjunction.{w} X).isTriangulated_rightAdjoint
  let : (schemeDerivedCoherator.{w} X).Additive :=
    (mapDerivedCategoryCoheratorAdjunction.{w} X).right_adjoint_additive
  exact isIso_app₁_of_isIso_app₂₃ (schemeDerivedCoherator.{w} X ⋙
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory) (𝟭 _)
    (mapDerivedCategoryCoheratorAdjunction.{w} X).counit T hT h₂ h₃

end Coherator

section AffineOpen

variable {X : Scheme.{u}} (U : X.Opens)

/-- **Restriction is left adjoint to direct image along the inclusion of an open subscheme**, in
the `SheafOfModules` spelling of `Stacks.DerivedQCoh.modulesRestrict` and
`Stacks.DerivedQCoh.modulesPushforward`. -/
private def modulesRestrictAdjunction : modulesRestrict U ⊣ modulesPushforward U.ι :=
  Scheme.Modules.restrictAdjunction U.ι

/-- The counit of the restriction–direct image adjunction along the inclusion of an open
subscheme is invertible: restricting a direct image from an open subscheme to that subscheme
recovers the module. -/
private instance isIso_modulesRestrictAdjunction_counit :
    IsIso (modulesRestrictAdjunction U).counit :=
  inferInstanceAs (IsIso (Scheme.Modules.restrictAdjunction U.ι).counit)

/-- Direct image along the inclusion of an open subscheme is full. -/
private instance modulesPushforward_full : (modulesPushforward U.ι).Full :=
  inferInstanceAs ((Scheme.Modules.pushforward U.ι).Full)

/-- Direct image along the inclusion of an open subscheme is faithful. -/
private instance modulesPushforward_faithful : (modulesPushforward U.ι).Faithful :=
  inferInstanceAs ((Scheme.Modules.pushforward U.ι).Faithful)

variable [QuasiCompact U.ι] [QuasiSeparated U.ι]

/-- The counit of `Stacks.DerivedQCoh.quasicoherentRestrictPushforwardAdjunction` is invertible,
its right adjoint being fully faithful. -/
private instance isIso_quasicoherentRestrictAdjunction_counit :
    IsIso (quasicoherentRestrictPushforwardAdjunction U).counit :=
  haveI := (fullyFaithful_quasicoherentPushforward U.ι).some.full
  haveI := (fullyFaithful_quasicoherentPushforward U.ι).some.faithful
  Adjunction.counit_isIso_of_R_fully_faithful _

section Counit

variable [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory]
  [HasDerivedCategory.{w} (SheafOfModules.{u} U.toScheme.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory]
  (Rj : DerivedCategory (SheafOfModules.{u} U.toScheme.ringCatSheaf) ⥤
    DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
  (ηj : (modulesPushforward U.ι).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⟶
    DerivedCategory.Q (C := SheafOfModules.{u} U.toScheme.ringCatSheaf) ⋙ Rj)
  [Rj.IsRightDerivedFunctor ηj
    (HomologicalComplex.quasiIso (SheafOfModules.{u} U.toScheme.ringCatSheaf)
      (ComplexShape.up ℤ))]
  (Φ : DerivedCategory (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
    DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
  (ηΦ : (quasicoherentPushforward U.ι).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q
        (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶
    DerivedCategory.Q
        (C := (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory) ⋙ Φ)
  [Φ.IsRightDerivedFunctor ηΦ
    (HomologicalComplex.quasiIso
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory
      (ComplexShape.up ℤ))]

/-- The derived adjunction `j^* ⊣ Rj_*` of all modules along the inclusion of an open subscheme,
for an arbitrary total right derived functor `Rj_*` of direct image. -/
private def derivedModulesRestrictAdjunction :
    (modulesRestrict U).mapDerivedCategory ⊣ Rj :=
  derivedAdjunctionOfCochainUnit _ Rj (modulesRestrictAdjunction U) ηj
    (exists_quasiIso_isKInjective_ringCatSheaf U.toScheme)

/-- **An arbitrary total right derived functor of direct image along the inclusion of an open
subscheme is fully faithful.** The counit of the underived adjunction is invertible and
restriction is exact, so the counit of the derived adjunction is invertible. -/
private def derivedPushforward_fullyFaithful : Rj.FullyFaithful :=
  fullyFaithful_of_isIso_counit _ Rj (modulesRestrictAdjunction U) ηj
    (exists_quasiIso_isKInjective_ringCatSheaf U.toScheme)

/-- The derived adjunction `j^* ⊣ Φ` on quasi-coherent modules along the inclusion of an open
subscheme, for an arbitrary total right derived functor `Φ` of direct image of quasi-coherent
modules. -/
private def derivedQuasicoherentRestrictAdjunction :
    (quasicoherentRestrict U).mapDerivedCategory ⊣ Φ :=
  derivedAdjunctionOfCochainUnit _ Φ (quasicoherentRestrictPushforwardAdjunction U) ηΦ
    (exists_quasiIso_isKInjective_quasicoherentModules U.toScheme)

/-- **An arbitrary total right derived functor of direct image of quasi-coherent modules along
the inclusion of an open subscheme is fully faithful**, by the argument of
`Stacks.DerivedQCoh.derivedPushforward_fullyFaithful` on the quasi-coherent side. -/
private def derivedQuasicoherentPushforward_fullyFaithful : Φ.FullyFaithful :=
  fullyFaithful_of_isIso_counit _ Φ (quasicoherentRestrictPushforwardAdjunction U) ηΦ
    (exists_quasiIso_isKInjective_quasicoherentModules U.toScheme)

/-- Derived restriction of quasi-coherent modules, followed by the derived inclusion, is the
derived inclusion followed by derived restriction of all modules. -/
private def derivedQuasicoherentRestrictCompιIso :
    (quasicoherentRestrict U).mapDerivedCategory ⋙
        (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι.mapDerivedCategory ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⋙
        (modulesRestrict U).mapDerivedCategory :=
  Stacks.DerivedGlueing.mapDerivedCategoryCompIso _ _ ≪≫
    Stacks.DerivedGlueing.mapDerivedCategoryCongr (quasicoherentRestrictCompι U) ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCompIso _ _).symm

/-- **The derived coherator commutes with derived direct image from an open subscheme.** Both
`Rj_* ∘ RQ_X` and `RQ_U ∘ Φ` are right adjoint to the derived inclusion of the quasi-coherent
modules followed by derived restriction, and a right adjoint is unique up to a unique natural
isomorphism. -/
private def derivedCoheratorPushforwardIso :
    Rj ⋙ schemeDerivedCoherator.{w} X ≅ schemeDerivedCoherator.{w} U.toScheme ⋙ Φ :=
  ((mapDerivedCategoryCoheratorAdjunction.{w} X).comp
      (derivedModulesRestrictAdjunction U Rj ηj)).rightAdjointUniq
    (((derivedQuasicoherentRestrictAdjunction U Φ ηΦ).comp
      (mapDerivedCategoryCoheratorAdjunction.{w} U.toScheme)).ofNatIsoLeft
        (derivedQuasicoherentRestrictCompιIso U))

include ηj ηΦ in
/-- **The counit of the derived coherator adjunction is invertible at the derived direct image of
a complex with quasi-coherent cohomology from an affine open.**

On an affine open the comparison functor is an equivalence, so the derived direct image `Rj_*`
restricted to the complexes with quasi-coherent cohomology and the derived direct image `Φ` of
quasi-coherent modules are two fully faithful functors fitting, together with the commutative
square of the hypothesis, into a restriction of the derived coherator adjunction whose left
adjoint is the comparison functor over the affine open. The counit of a restricted adjunction
whose left adjoint is an equivalence is invertible, hence so is the ambient counit at every
object in the image of the inclusion. -/
private theorem isIso_coheratorCounit_derivedPushforward (hU : IsAffineOpen U)
    (e : Φ ⋙ derivedQuasicoherentComparison.{w} X ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
      derivedQuasicoherentComparison.{w} U.toScheme ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).ι ⋙ Rj)
    (E : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).FullSubcategory) :
    IsIso ((mapDerivedCategoryCoheratorAdjunction.{w} X).counit.app (Rj.obj E.obj)) := by
  have : IsAffine U.toScheme := hU
  have := derivedQuasicoherentComparison_isEquivalence_of_isAffine_atModel.{w} U.toScheme
  let ffRj := derivedPushforward_fullyFaithful U Rj ηj
  have := ffRj.full
  have := ffRj.faithful
  let JU := (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).ι
  exact isIso_counit_app_of_restrictFullyFaithful (mapDerivedCategoryCoheratorAdjunction.{w} X)
    (derivedQuasicoherentPushforward_fullyFaithful U Φ ηΦ)
    (Functor.FullyFaithful.ofFullyFaithful (JU ⋙ Rj))
    (Functor.isoWhiskerLeft Φ (derivedQuasicoherentComparisonCompι.{w} X).symm ≪≫ e)
    (Functor.associator JU Rj (schemeDerivedCoherator.{w} X) ≪≫
      Functor.isoWhiskerLeft JU (derivedCoheratorPushforwardIso U Rj ηj Φ ηΦ) ≪≫
      (Functor.associator JU (schemeDerivedCoherator.{w} U.toScheme) Φ).symm) E

end Counit

end AffineOpen

section Main

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 09T6], the equivalence.** Let `X` be a quasi-compact quasi-separated scheme
for which the right derived functor of direct image of quasi-coherent modules from every affine
open fits into the commutative square of
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible`. Then the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 06VT] is an equivalence.

The proof is the source's induction. The comparison functor is left adjoint to the derived
coherator restricted to the complexes with quasi-coherent cohomology, and it is conservative, so
it suffices to see that the counit of the adjunction `ι_* ⊣ RQ_X` is invertible at every complex
with quasi-coherent cohomology. The counit is a natural transformation of exact functors of
triangulated categories, hence invertible at the first vertex of a distinguished triangle as soon
as it is invertible at the other two, and it is invertible at a zero object; so it suffices to
produce, for a complex `E` with quasi-coherent cohomology supported on a closed set `S` and an
affine open `U`, a distinguished triangle on `E` whose second vertex has invertible counit and
whose third vertex again has quasi-coherent cohomology but is supported on `S \ U`. Finitely many
affine opens cover `X`, so the support is exhausted. The triangle is the recollement triangle
`E ⟶ Rj_*(E|_U) ⟶ C`: its second vertex has invertible counit by
`Stacks.DerivedQCoh.isIso_coheratorCounit_derivedPushforward`, which is where the commutative
square of the hypothesis and the equivalence on the affine open `U` are used, and its third
vertex is supported on `S \ U` because `E ⟶ Rj_*(E|_U)` becomes invertible on `U`. -/
@[stacks 09T6 "equivalence"]
theorem derivedQuasicoherentComparison_isEquivalence_of_affineOpenCompatible
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (hcompat : AffineOpenPushforwardCompatible.{u + 1} X) :
    (derivedQuasicoherentComparison.{u + 1} X).IsEquivalence := by
  have hPiso : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  refine isEquivalence_of_isIso_counit_app_of_derivedCategoryB X ?_
  refine property_of_finite_affine_support_standard X
    (fun E => IsIso ((mapDerivedCategoryCoheratorAdjunction.{u + 1} X).counit.app E))
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf))
    (isIso_coheratorCounit_app_of_isZero.{u + 1} X)
    (isIso_coheratorCounit_app₁_of_app₂₃.{u + 1} X) ?_
  intro U hU S hS E hE hSupp
  have hUaff : IsAffine U.toScheme := hU
  obtain ⟨Rj, ηj, Φ, ηΦ, hRj, hΦ, ⟨e⟩⟩ := hcompat U hU
  have hRjQh := isRightDerivedFunctor_homotopyUnitOfCochainUnit (modulesPushforward U.ι) Rj
    (exists_quasiIso_isKInjective_ringCatSheaf U.toScheme) ηj
  have hPush : CohomologySupportedOn X.ringCatSheaf S
      (Rj.obj ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E)) :=
    @cohomologySupportedOn_derivedPushforward X U S hS Rj
      (homotopyUnitOfCochainUnit (modulesPushforward U.ι) Rj ηj) hRjQh _
      (cohomologySupportedOn_derivedRestrict U S E hSupp)
  obtain ⟨T, hT₁, hT₂, hTdist, hTsupp⟩ := @exists_derivedRestrict_triangle X U S hS Rj
    (homotopyUnitOfCochainUnit (modulesPushforward U.ι) Rj ηj) hRjQh E hSupp hPush
  have hEU : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) :=
    isQuasicoherent_derivedRestrict U E hE
  have hcomp : IsIso ((mapDerivedCategoryCoheratorAdjunction.{u + 1} X).counit.app T.obj₂) := by
    rw [hT₂]
    exact isIso_coheratorCounit_derivedPushforward U Rj ηj Φ ηΦ hU e ⟨_, hEU⟩
  refine ⟨T, hT₁, hTdist, hcomp, ?_, hTsupp⟩
  have hequiv := derivedQuasicoherentComparison_isEquivalence_of_isAffine_atModel.{u + 1} U.toScheme
  have hpush : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (Rj.obj ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E)) := by
    refine (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).prop_of_iso
      (e.app ((derivedQuasicoherentComparison.{u + 1} U.toScheme).objPreimage ⟨_, hEU⟩) ≪≫
        Rj.mapIso ((DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).ι.mapIso
            ((derivedQuasicoherentComparison.{u + 1} U.toScheme).objObjPreimageIso ⟨_, hEU⟩)))
      ((derivedQuasicoherentComparison.{u + 1} X).obj (Φ.obj
        ((derivedQuasicoherentComparison.{u + 1} U.toScheme).objPreimage ⟨_, hEU⟩))).property
  let T' : Pretriangulated.Triangle (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) := T
  have hdist' : T' ∈ distTriang (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) := hTdist
  exact (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ext_of_isTriangulatedClosed₃ T' hdist'
    (hT₁ ▸ hE) (hT₂ ▸ hpush)

end Main

end Stacks.DerivedQCoh

end
