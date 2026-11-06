module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroAndSheafCondition
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech augmentation and the cohomology of a covered object

Let `𝒰 = {U_i → U}` be a family of morphisms of a category with a fixed target, with all its
finite nonempty fibre products. For an abelian presheaf `F` the sections of `F` over `U`
restrict to a matching family on the members of `𝒰`, hence to a degree-zero Čech cocycle;
this file builds that comparison as a *natural transformation*

```
Γ(U, -) ⟶ Ȟ⁰(𝒰, -)
```

of functors on abelian presheaves, and shows that it is an isomorphism on abelian sheaves as
soon as `𝒰` generates a covering sieve. Naturality is what distinguishes this from the
objectwise bijection of Stacks 03AN: it is what lets the two functors have the same right
derived functors, and that is exactly what identifies the abutment of the Čech-to-cohomology
spectral sequence with the cohomology of the covered object.

Combining it with the spectral sequence of Stacks 03OW gives the Čech-to-cohomology spectral
sequence with its abutment expressed through the inclusion of abelian sheaves into abelian
presheaves, whose value in nonnegative degrees is the sheaf cohomology `H^n(U, F)`.

## Main definitions

* `Stacks.CechSite.sectionsToCochain`: the restriction of a section over `U` to the
  degree-zero Čech cochain group.
* `Stacks.CechSite.cechCochainAugmentation`: the same, as a natural transformation into the
  degree-zero term of the Čech complex.
* `Stacks.CechSite.cechAugmentation`: the natural transformation `Γ(U, -) ⟶ Ȟ⁰(𝒰, -)` on
  abelian presheaves.
* `Stacks.CechSite.cechAugmentationIso`: the induced natural isomorphism on abelian sheaves.
* `Stacks.CechSite.cechCohomologyZeroFunctorIso`: the same isomorphism written for
  `Stacks.CechSite.cechCohomologyZeroFunctor`, the degree-zero part of the Čech δ-functor of
  Stacks 03AR.
* `Stacks.CechSite.rightDerivedPlus_cechZero_obj_iso`: the right derived functors of
  `Ȟ⁰(𝒰, -) ∘ i` are the values over `U` of the right derived functors of the inclusion
  `i : Ab(C) ⥤ PAb(C)`.
* `Stacks.CechSite.rightDerivedPlus_cechZero_obj_iso_cohomologyPresheaf`: in nonnegative
  degrees those values are the sheaf cohomology groups `H^n(U, F)`.

## Main results

* `Stacks.CechSite.isIso_cechAugmentation_app_of_isSheaf`: the Čech augmentation of an abelian
  sheaf is an isomorphism, for every family generating a covering sieve.
* `Stacks.CechSite.exists_cechToCohomology_spectralSequence_cohomologyAbutment`: the
  Čech-to-cohomology spectral sequence with second page `Ȟ^p(𝒰, H^q(F))` abutting to the
  cohomology of `U`.
* `Stacks.CechSite.exists_cechToCohomology_spectralSequence_sheafCohomologyAbutment`: the same
  spectral sequence, with its abutment written as the sheaf cohomology groups `H^n(U, F)`.

## Implementation notes

The natural transformation is built in two stages. First the degree-zero comparison
`Γ(U, -) ⟶ 𝒞⁰(𝒰, -)` is assembled from `Stacks.CechSite.cechRestriction` and
`Stacks.CechSite.familyToCochain`; naturality is checked on the product coordinates, using
that the Čech complex is degreewise a product of evaluations, so that a morphism of presheaves
acts on it coordinatewise. Then the composite with the differential vanishes — this is the
matching condition — and `HomologicalComplex.liftCycles` lands the comparison in the cycles,
which in degree zero are the homology because a cochain complex indexed by `ℕ` has no
differential into degree zero.

That the result is an isomorphism on sheaves is read off from Stacks 03AN through
`Stacks.CechSite.cechCohomologyZeroEquiv`: the composite of the augmentation with that
comparison is `Stacks.CechSite.cechRestriction`, so the augmentation is bijective exactly when
restriction to matching families is, which for a sheaf and a covering family it is.

The abutment identification uses that evaluation at an object is exact on abelian presheaves,
so it commutes with passing to right derived functors
(`Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusPostcomposeIso`), and that a
natural isomorphism of functors induces one of their right derived functors
(`Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusNatIsoOfIso`). The abutment is
therefore stated as the graded family `n ↦ (R^n i(F))(U)`, indexed by `ℤ` as
`CategoryTheory.SpectralSequence.AbutsTo` requires, and its nonnegative part is identified
with `H^n(U, F)` separately.

**The functoriality of the spectral sequence in the sheaf, which is the last sentence of
Stacks 03AZ, is not proved here, and no declaration below claims it.** The spectral sequence
comes from Stacks 03OW and hence from the Grothendieck spectral sequence of Stacks 015N,
`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`, which is an
existence statement producing a spectral sequence one sheaf at a time, so no functorial data can
be extracted from it. A functorial statement — a functor
`Sheaf J AddCommGrpCat ⥤ E₂CohomologicalSpectralSequenceNat AddCommGrpCat` together with a
natural second-page isomorphism and a
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` abutment, in the shape of
`Stacks.CategoryTheory.Hypercovering.hypercoveringSpectralSequence` for Stacks 01GY and of
`Stacks.Cohomology.CechSpectral.cechSpectralSequence` for Stacks 01ES — needs the construction
through a functorial injective resolution of abelian sheaves and the Čech double complex of its
coefficient complex instead.

That construction is carried out, for a **small** site, in
`StacksFrontier/CategoryTheory/Sites/CechToCohomologyFunctorial.lean`:
`Stacks.CechSite.cechToCohomologySpectralSequenceFunctor` is the functor,
`Stacks.CechSite.cechToCohomologyPageTwoIso` the natural second-page isomorphism and
`Stacks.CechSite.cechToCohomologyFunctorialAbutment` the functorial filtered abutment. It is
obtained from the hypercovering spectral sequence of Stacks 01GY at the Čech simplicial object of
the family, and its abutment is the cohomology of the total complex of the Čech double complex,
identified with `H^n(U, F)` in
`StacksFrontier/CategoryTheory/Sites/CechToCohomologyAbutment.lean` by
`Stacks.CechSite.cechToCohomologySheafCohomologyAbutment`, for a family covering `U` for a
pretopology. So neither file subsumes the other: the convergence clause below holds for an
arbitrary `Category.{u} C` on `Type u` and is not functorial, and that development is functorial
on a small site.

## References

* [Stacks Project, Tag 03AN](https://stacks.math.columbia.edu/tag/03AN)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03AZ](https://stacks.math.columbia.edu/tag/03AZ)
* [Stacks Project, Tag 03OW](https://stacks.math.columbia.edu/tag/03OW)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a w v u

namespace Stacks.CechSite

section Augmentation

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasProducts.{w} AddCommGrpCat.{a}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- The degree-zero Čech cochain obtained from a section over the covered object by
restricting it to every member of the family. -/
public noncomputable def sectionsToCochain (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    F.obj (op X) →+ (cechComplex E F).X 0 :=
  (familyToCochain E F).comp ((cechH0 E F).subtype.comp (cechRestriction E F))

/-- The product coordinates of the degree-zero Čech cochain of a section. -/
public lemma sectionsToCochain_π (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) (s : F.obj (op X))
    (k : Fin 1 → E.I₀) :
    Pi.π (cochainFactor E F 0) k (sectionsToCochain E F s) =
      F.map (Pi.π (fun j : Fin 1 ↦ Over.mk (E.f (k j))) 0).left.op
        (F.map (E.f (k 0)).op s) :=
  familyToCochain_π E F _ k

/-- The degree-zero Čech cochain of a section is a cocycle: this is the matching condition for
the family of its restrictions. -/
public lemma d_sectionsToCochain (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) (s : F.obj (op X)) :
    (cechComplex E F).d 0 1 (sectionsToCochain E F s) = 0 :=
  (differential_eq_zero_iff E F _).2 (cechRestriction E F s).2

/-- Restriction to the degree-zero Čech cochain group is natural in the abelian presheaf. -/
public lemma sectionsToCochain_naturality {F G : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ G) :
    φ.app (op X) ≫ AddCommGrpCat.ofHom (sectionsToCochain E G) =
      AddCommGrpCat.ofHom (sectionsToCochain E F) ≫
        ((cechComplexFunctor E).map φ).f 0 := by
  ext s
  apply (productAddEquiv (cochainFactor E G 0)).injective
  ext k
  show Pi.π (cochainFactor E G 0) k (sectionsToCochain E G (φ.app (op X) s)) =
    Pi.π (cochainFactor E G 0) k
      (((cechComplexFunctor E).map φ).f 0 (sectionsToCochain E F s))
  rw [cechComplexFunctor_map_f_π_apply, sectionsToCochain_π, sectionsToCochain_π,
    ← NatTrans.naturality_apply]
  exact (NatTrans.naturality_apply φ _ _).symm

/-- The Čech augmentation in degree zero, as a natural transformation from the sections over
the covered object to the degree-zero term of the Čech complex. -/
public noncomputable def cechCochainAugmentation :
    (evaluation Cᵒᵖ AddCommGrpCat.{a}).obj (op X) ⟶
      cechComplexFunctor E ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) 0 where
  app F := AddCommGrpCat.ofHom (sectionsToCochain E F)
  naturality _ _ φ := sectionsToCochain_naturality E φ

/-- The Čech augmentation composed with the first differential vanishes. -/
public lemma cechCochainAugmentation_comp_d (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    AddCommGrpCat.ofHom (sectionsToCochain E F) ≫ (cechComplex E F).d 0 1 = 0 := by
  ext s
  exact d_sectionsToCochain E F s

/-- The Čech augmentation of an abelian presheaf, landed in the degree-zero cycles. -/
public noncomputable def cechAugmentationCycles (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    F.obj (op X) ⟶ (cechComplex E F).cycles 0 :=
  (cechComplex E F).liftCycles (AddCommGrpCat.ofHom (sectionsToCochain E F)) 1 (by simp)
    (cechCochainAugmentation_comp_d E F)

/-- The cycle underlying the Čech augmentation is the degree-zero Čech cochain of a section. -/
public lemma cechAugmentationCycles_i (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    cechAugmentationCycles E F ≫ (cechComplex E F).iCycles 0 =
      AddCommGrpCat.ofHom (sectionsToCochain E F) :=
  (cechComplex E F).liftCycles_i _ 1 (by simp) (cechCochainAugmentation_comp_d E F)

/-- The Čech augmentation into the degree-zero cycles is natural in the abelian presheaf. -/
public lemma cechAugmentationCycles_naturality {F G : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (φ : F ⟶ G) :
    φ.app (op X) ≫ cechAugmentationCycles E G =
      cechAugmentationCycles E F ≫
        HomologicalComplex.cyclesMap ((cechComplexFunctor E).map φ) 0 := by
  rw [← cancel_mono ((cechComplex E G).iCycles 0), Category.assoc,
    cechAugmentationCycles_i, Category.assoc, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, cechAugmentationCycles_i]
  exact sectionsToCochain_naturality E φ

/-- The Čech augmentation of a single abelian presheaf: the map from the sections over the
covered object to the degree-zero Čech cohomology of the family. -/
public noncomputable def cechAugmentationApp (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    F.obj (op X) ⟶ cechCohomology E (A := AddCommGrpCat.{a}) F 0 :=
  cechAugmentationCycles E F ≫ (cechComplex E F).homologyπ 0

/-- **The Čech augmentation, naturally.** The natural transformation from the sections over
the covered object to the degree-zero Čech cohomology of the family, on abelian presheaves. -/
public noncomputable def cechAugmentation :
    (evaluation Cᵒᵖ AddCommGrpCat.{a}).obj (op X) ⟶
      cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{a} (ComplexShape.up ℕ) 0 where
  app F := cechAugmentationApp E F
  naturality {F G} φ := by
    change φ.app (op X) ≫ cechAugmentationCycles E G ≫ (cechComplex E G).homologyπ 0 =
      (cechAugmentationCycles E F ≫ (cechComplex E F).homologyπ 0) ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor E).map φ) 0
    rw [← Category.assoc, cechAugmentationCycles_naturality E φ, Category.assoc,
      Category.assoc, HomologicalComplex.homologyπ_naturality]

/-- The Čech augmentation, read through the identification of degree-zero Čech cohomology with
the group of matching families, is restriction to the members of the family. -/
public lemma cechCohomologyZeroEquiv_cechAugmentationApp (F : Cᵒᵖ ⥤ AddCommGrpCat.{a})
    (s : F.obj (op X)) :
    cechCohomologyZeroEquiv E F (cechAugmentationApp E F s) = cechRestriction E F s := by
  ext i
  rw [cechCohomologyZeroEquiv_apply]
  have key : cechAugmentationApp E F ≫
      ((cechComplex E F).isoHomologyπ₀.inv ≫ (cechComplex E F).iCycles 0) =
      AddCommGrpCat.ofHom (sectionsToCochain E F) := by
    rw [show cechAugmentationApp E F =
        cechAugmentationCycles E F ≫ (cechComplex E F).homologyπ 0 from rfl,
      Category.assoc, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc,
      cechAugmentationCycles_i]
  have h1 : ((cechComplex E F).isoHomologyπ₀.inv ≫ (cechComplex E F).iCycles 0)
      (cechAugmentationApp E F s) = sectionsToCochain E F s :=
    ConcreteCategory.congr_hom key s
  rw [h1, sectionsToCochain_π, ← Functor.map_comp_apply, ← op_comp, ← Over.comp_left,
    show ((productUniqueIso fun _ : Fin 1 ↦ Over.mk (E.f i)).inv ≫
        Pi.π (fun _ : Fin 1 ↦ Over.mk (E.f i)) 0) = 𝟙 _ from
      (productUniqueIso (fun _ : Fin 1 ↦ Over.mk (E.f i))).inv_hom_id,
    Over.id_left, op_id, F.map_id]
  rfl

/-- The Čech augmentation is bijective exactly when restriction to matching families is. -/
public lemma bijective_cechAugmentationApp_iff (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    Function.Bijective (cechAugmentationApp E F) ↔
      Function.Bijective (cechRestriction E F) := by
  have h : (cechCohomologyZeroEquiv E F) ∘ (cechAugmentationApp E F) =
      cechRestriction E F :=
    funext (cechCohomologyZeroEquiv_cechAugmentationApp E F)
  rw [← (cechCohomologyZeroEquiv E F).bijective.of_comp_iff' (cechAugmentationApp E F), h]

/-- **The Čech augmentation of an abelian sheaf is an isomorphism.** For a family generating a
covering sieve, the sections of an abelian sheaf over the covered object are its degree-zero
Čech cohomology. This is the Čech-complex form of Stacks 03AN. -/
public lemma isIso_cechAugmentation_app_of_isSheaf (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{a}) (hF : Presheaf.IsSheaf J F) (hE : E.sieve₀ ∈ J X) :
    IsIso (cechAugmentationApp E F) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ((bijective_cechAugmentationApp_iff E F).2
      (cechRestriction_bijective_of_isSheaf J F hF E hE))

/-- **The Čech augmentation is a natural isomorphism on abelian sheaves.** For a family
generating a covering sieve, the sections functor on abelian sheaves is naturally isomorphic
to degree-zero Čech cohomology of the family. -/
public noncomputable def cechAugmentationIso (J : GrothendieckTopology C)
    (hE : E.sieve₀ ∈ J X) :
    sheafToPresheaf J AddCommGrpCat.{a} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{a}).obj (op X) ≅
      sheafToPresheaf J AddCommGrpCat.{a} ⋙ cechComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{a} (ComplexShape.up ℕ) 0 :=
  NatIso.ofComponents
    (fun F ↦ @asIso _ _ _ _ _
      (isIso_cechAugmentation_app_of_isSheaf E J F.obj F.property hE))
    (fun φ ↦ (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{a})
      (cechAugmentation E)).naturality φ)

end Augmentation

section SpectralSequence

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] (U : C) (E : PreZeroHypercover.{u} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- Sections over the covered object, as a functor on abelian presheaves. It is exact,
because limits and colimits of presheaves are computed objectwise. -/
public noncomputable abbrev sectionsFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- **Degree-zero Čech cohomology of an abelian sheaf is its sections over the covered
object, naturally.** This is `Stacks.CechSite.cechAugmentationIso` written for the degree-zero
part `Stacks.CechSite.cechCohomologyZeroFunctor` of the Čech δ-functor of Stacks 03AR, which
is the functor whose right derived functors the Čech-to-cohomology spectral sequence of
Stacks 03OW is built from. -/
public noncomputable def cechCohomologyZeroFunctorIso (hE : E.sieve₀ ∈ J U) :
    Stacks.CechComparison.sheafIncl J ⋙ cechCohomologyZeroFunctor.{u, u, u, u} E ≅
      Stacks.CechComparison.sheafIncl J ⋙ sectionsFunctor U :=
  Functor.isoWhiskerLeft (Stacks.CechComparison.sheafIncl J)
      (eqToIso ((cechCohomologyDeltaFunctor.{u, u, u, u} E).2 0)) ≪≫
    (cechAugmentationIso.{u, u, u, u} E J hE).symm

/-- **The abutment of the Čech-to-cohomology spectral sequence.** The right derived functors
of `Ȟ⁰(𝒰, -) ∘ i`, where `i : Ab(C) ⥤ PAb(C)` is the inclusion of abelian sheaves into
abelian presheaves, are the values over the covered object of the right derived functors of
`i` itself.

Both steps come from the natural isomorphism `Ȟ⁰(𝒰, i(-)) ≅ Γ(U, i(-))` of
`Stacks.CechSite.cechCohomologyZeroFunctorIso`: the first replaces the functor by an
isomorphic one, and the second moves the exact functor `Γ(U, -)` past the right derived
functor. -/
public noncomputable def rightDerivedPlus_cechZero_obj_iso (hE : E.sieve₀ ∈ J U) (n : ℤ)
    (F : Sheaf J AddCommGrpCat.{u}) :
    ((Stacks.CechComparison.sheafIncl J ⋙
        Stacks.CechComparison.cechZeroFunctor E).rightDerivedPlus n).obj F ≅
      (((Stacks.CechComparison.sheafIncl J).rightDerivedPlus n).obj F).obj (op U) :=
  (Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusNatIsoOfIso
      (cechCohomologyZeroFunctorIso J U E hE) n).app F ≪≫
    ((Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusPostcomposeIso
      (Stacks.CechComparison.sheafIncl J) (sectionsFunctor U) n).app F).symm

/-- **In nonnegative degrees the abutment is sheaf cohomology.** The value over the covered
object of the `n`-th right derived functor of the inclusion of abelian sheaves into abelian
presheaves is `H^n(U, F)`; this is the objectwise half of Stacks 03AY, evaluated at `U`. -/
@[sga "4 IV 4.8" "for every U", sga "4 V 2.4.2" "(X), special case"]
public noncomputable def rightDerivedPlus_sheafIncl_obj_obj_iso (n : ℕ)
    (F : Sheaf J AddCommGrpCat.{u}) :
    (((Stacks.CechComparison.sheafIncl J).rightDerivedPlus (n : ℤ)).obj F).obj (op U) ≅
      (F.cohomologyPresheaf n).obj (op U) :=
  (sectionsFunctor U).mapIso
    (Stacks.CechComparison.rightDerivedPlus_sheafToPresheaf_obj_iso_cohomologyPresheaf J F n)

/-- The two previous isomorphisms composed: the `n`-th right derived functor of
`Ȟ⁰(𝒰, -) ∘ i` at an abelian sheaf `F` is the sheaf cohomology `H^n(U, F)`, for `n : ℕ`. -/
public noncomputable def rightDerivedPlus_cechZero_obj_iso_cohomologyPresheaf
    (hE : E.sieve₀ ∈ J U) (n : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    ((Stacks.CechComparison.sheafIncl J ⋙
        Stacks.CechComparison.cechZeroFunctor E).rightDerivedPlus (n : ℤ)).obj F ≅
      (F.cohomologyPresheaf n).obj (op U) :=
  rightDerivedPlus_cechZero_obj_iso J U E hE (n : ℤ) F ≪≫
    rightDerivedPlus_sheafIncl_obj_obj_iso J U n F

/-- **The Čech-to-cohomology spectral sequence with its abutment.** For a family `𝒰 = E`
generating a covering sieve on `U` and an abelian sheaf `F` there is a cohomological spectral
sequence with second page

```
E₂^{p,q} ≅ Ȟ^p(𝒰, H^q(F)),
```

the Čech cohomology of the family with coefficients in the cohomology presheaves
`H^q(F) : V ↦ H^q(V, F)`, abutting to the graded family `n ↦ (R^n i(F))(U)` of values over `U`
of the right derived functors of the inclusion `i : Ab(C) ⥤ PAb(C)`. In nonnegative degrees
that family is the sheaf cohomology of `U`, by
`Stacks.CechSite.rightDerivedPlus_sheafIncl_obj_obj_iso`.

The spectral sequence is the one of Stacks 03OW; what is added here is the abutment, which in
that statement is the cohomology of the right derived functor of the composite
`Ȟ⁰(𝒰, -) ∘ i`. -/
public theorem exists_cechToCohomology_spectralSequence_cohomologyAbutment
    (hE : E.sieve₀ ∈ J U) (F : Sheaf J AddCommGrpCat.{u}) :
    ∃ S : CohomologicalSpectralSequence AddCommGrpCat.{u} 0,
      (∀ p q : ℕ, Nonempty ((S.page 2 zero_le_two).X ((p : ℤ), (q : ℤ)) ≅
        cechCohomology E (F.cohomologyPresheaf q) p)) ∧
      SpectralSequence.AbutsTo S (fun n ↦
        (((Stacks.CechComparison.sheafIncl J).rightDerivedPlus n).obj F).obj (op U)) := by
  obtain ⟨S, hE₂, habuts⟩ :=
    Stacks.CechComparison.exists_cechToCohomology_spectralSequence_pageTwo J E F
  exact ⟨S, hE₂, habuts.of_iso (fun n ↦ rightDerivedPlus_cechZero_obj_iso J U E hE n F)⟩

add_to_stacks 03AZ "the spectral sequence and its second page"
  exists_cechToCohomology_spectralSequence_cohomologyAbutment
add_to_sga "4 V 3.2" "covering case"
  Stacks.CechSite.exists_cechToCohomology_spectralSequence_cohomologyAbutment

/-- **The Čech-to-cohomology spectral sequence of a covering family, for a single abelian
sheaf.** For a family `𝒰 = E` generating a covering sieve on `U` and an abelian sheaf `F` there
is a cohomological spectral sequence with second page

```
E₂^{p,q} ≅ Ȟ^p(𝒰, H^q(F))
```

abutting to a graded family whose value in degree `n : ℕ` is the sheaf cohomology `H^n(U, F)`.

This is `Stacks.CechSite.exists_cechToCohomology_spectralSequence_cohomologyAbutment` with its
abutment read through `Stacks.CechSite.rightDerivedPlus_sheafIncl_obj_obj_iso`; the abutment is
indexed by `ℤ`, as `CategoryTheory.SpectralSequence.AbutsTo` requires, and the identification is
stated in the nonnegative degrees, which are the ones a first-quadrant spectral sequence
contributes to. Functoriality of the spectral sequence in `F` is not asserted; see the
implementation notes of this file. -/
@[stacks 03AZ "the spectral sequence, its second page and its convergence",
  sga "4 V 3.6" "more general"]
public theorem exists_cechToCohomology_spectralSequence_sheafCohomologyAbutment
    (hE : E.sieve₀ ∈ J U) (F : Sheaf J AddCommGrpCat.{u}) :
    ∃ (S : CohomologicalSpectralSequence AddCommGrpCat.{u} 0) (H : ℤ → AddCommGrpCat.{u}),
      (∀ p q : ℕ, Nonempty ((S.page 2 zero_le_two).X ((p : ℤ), (q : ℤ)) ≅
        cechCohomology E (F.cohomologyPresheaf q) p)) ∧
      (∀ n : ℕ, Nonempty (H (n : ℤ) ≅ (F.cohomologyPresheaf n).obj (op U))) ∧
      SpectralSequence.AbutsTo S H := by
  obtain ⟨S, hE₂, habuts⟩ :=
    exists_cechToCohomology_spectralSequence_cohomologyAbutment J U E hE F
  exact ⟨S, _, hE₂, fun n ↦ ⟨rightDerivedPlus_sheafIncl_obj_obj_iso J U n F⟩, habuts⟩

end SpectralSequence

end Stacks.CechSite

end
