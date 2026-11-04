module

public import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctorOnModels
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# The constraints of the re-seated monoidal derived category, on K-flat complexes

`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` is the symmetric monoidal
structure of Stacks Tag 0FPT whose tensor product *is* the derived tensor product of Tag 06YU
and whose unit *is* the structure sheaf in degree zero.  Its coherence constraints are those of
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, transported by
`CategoryTheory.MonoidalCategory.reseat`.

On K-flat complexes the associativity and commutativity constraints of the re-seated structure
are the associator and the Koszul symmetry of `Comp(Mod(O))`, carried across by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison`; these are the two clauses of
Tag 0FPT, stated as equations.

`DerivedModules R` carries two monoidal structures, `derivedMonoidal` and the re-seated one,
and neither is an instance; every declaration names the one it means.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_comparison`: the re-seating isomorphism
  followed by the K-flat comparison of an arbitrary derived tensor product is
  `CochainComplex.KFlatMonoidal.derivedTensorIso`, the K-flat comparison of `derivedMonoidal`.
  `Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_canonicalComparisonHom` is its value
  at the canonical derived tensor product.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_associator`,
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding`: the two clauses of
  Tag 0FPT. The associativity one is stated by
  `Stacks.SheafOfModules.DerivedMonoidal.CanonicalComparisonAssociator`.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_rightUnitor` and
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_leftUnitor`: the same for the two
  unit constraints.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

attribute [local instance 10000] CochainComplex.symmetricCategory
  SheafOfModules.monoidalCategorySheafTensor

/-- The monoidal structure on `Complexes R`. -/
local instance (priority := 100000) monoidalCategoryStructComplexes :
    MonoidalCategoryStruct (Complexes R) := inferInstance

/-! ### The bridging identity -/

omit [HasDerivedCategory.{d} (Mod R)] in
/-- **K-flatness of a total tensor product of K-flat complexes**, at the ringed-site spelling
`Stacks.SheafOfModules.KFlat.KFlat`. -/
theorem kFlat_tensor_complexes {K L : Complexes R}
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    Stacks.SheafOfModules.KFlat.KFlat R ((K ⊗ L : Complexes R)) :=
  CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hK hL

omit [HasDerivedCategory.{d} (Mod R)] in
/-- **K-flatness of the unit of `Comp(Mod(O))`**, at the ringed-site spelling
`Stacks.SheafOfModules.KFlat.KFlat`. -/
theorem kFlat_tensorUnit_complexes :
    Stacks.SheafOfModules.KFlat.KFlat R ((𝟙_ (Complexes R) : Complexes R)) :=
  CochainComplex.KFlatMonoidal.kFlat_tensorUnit (Mod R)

/-- **The first half of the re-seating isomorphism is the comparison of the two derived tensor
bifunctors**, in the spelling of `CochainComplex.KFlatMonoidal.derivedTensorCompare`. -/
theorem derivedTensorBifunctorIso_hom_app_app_eq (X Y : DerivedModules R) :
    ((derivedTensorBifunctorIso R).hom.app X).app Y =
      CochainComplex.KFlatMonoidal.derivedTensorCompare (Mod R) (exists_kFlat_resolution R)
        X Y :=
  congrArg (fun τ ↦ (τ.app X).app Y)
    (CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso_hom (Mod R)
      (exists_kFlat_resolution R))

/-- The re-seating isomorphism of a prescribed derived tensor product, split into its two
halves. -/
theorem reseatIso_trans_hom (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)
    (X Y : DerivedModules R) :
    letI := derivedMonoidal R
    (reseatIso (derivedTensorBifunctorIso R ≪≫ derivedBifunctorTensorIso R T) X Y).hom =
      ((derivedTensorBifunctorIso R).hom.app X).app Y ≫
        ((derivedBifunctorTensorIso R T).hom.app X).app Y :=
  rfl

/-- **The second half of the re-seating isomorphism carries the prescribed K-flat comparison
to the two-sided K-flat comparison of `CochainComplex.KFlatBifunctor.derivedBifunctor`.** -/
theorem derivedBifunctorTensorIso_comp_comparison
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R) (K L : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    ((derivedBifunctorTensorIso R T).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫ (T.comparison K L hK hL).hom =
      (comparison (curriedTensor (Mod R)) K L
        (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat (Mod R) hK) hL).hom :=
  (congrArg (fun v ↦ v ≫ (T.comparison K L hK hL).hom)
        (derivedBifunctorTensorIso_hom_app_app R T K L hK hL)).trans
    (((Category.assoc _ _ _).trans
          (congrArg (fun v ↦ (comparisonRight (curriedTensor (Mod R)) K L hL).hom ≫ v)
            (Iso.inv_hom_id (T.comparison K L hK hL)))).trans
      ((Category.comp_id _).trans
        (comparisonRight_hom_eq_comparison_hom (curriedTensor (Mod R)) K L
          (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat (Mod R) hK) hL)))

/-- **The derived tensor bifunctor of Tag 06YU**,
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`. -/
def derivedTensorBifunctorOfSite :
    DerivedModules R ⥤ DerivedModules R ⥤ DerivedModules R :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R

/-- `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorOfSite` *is* the derived
tensor bifunctor of Tag 06YU, hence the tensor product of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` on the nose. -/
theorem derivedTensorBifunctorOfSite_eq :
    derivedTensorBifunctorOfSite R =
      Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R :=
  rfl

/-- **The K-flat comparison of Tag 06YU**, with its source spelled as the derived tensor
bifunctor applied. -/
def canonicalComparisonHom (K L : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    ((derivedTensorBifunctorOfSite R).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj ((K ⊗ L : Complexes R)) :=
  (canonicalComparison R K L hK hL).hom

/-- `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparisonHom` *is* the morphism
underlying `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison`. -/
theorem canonicalComparisonHom_eq (K L : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    canonicalComparisonHom R K L hK hL = (canonicalComparison R K L hK hL).hom :=
  rfl

/-- **The re-seating isomorphism carries the K-flat comparison of a prescribed derived tensor
product to the K-flat comparison of `derivedMonoidal`.** -/
theorem reseatIso_comp_comparison (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)
    (K L : Complexes R) (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    letI := derivedMonoidal R
    (reseatIso (derivedTensorBifunctorIso R ≪≫ derivedBifunctorTensorIso R T)
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (T.comparison K L hK hL).hom =
      (CochainComplex.KFlatMonoidal.derivedTensorIso (Mod R) (exists_kFlat_resolution R)
        hK hL).hom :=
  let := derivedMonoidal R
  (congrArg (fun v ↦ v ≫ (T.comparison K L hK hL).hom)
        (reseatIso_trans_hom R T (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg
            (fun v ↦ ((derivedTensorBifunctorIso R).hom.app (DerivedCategory.Q.obj K)).app
              (DerivedCategory.Q.obj L) ≫ v)
            (derivedBifunctorTensorIso_comp_comparison R T K L hK hL)).trans
        ((congrArg
              (fun v ↦ v ≫ (comparison (curriedTensor (Mod R)) K L
                (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat (Mod R) hK) hL).hom)
              (derivedTensorBifunctorIso_hom_app_app_eq R (DerivedCategory.Q.obj K)
                (DerivedCategory.Q.obj L))).trans
          (CochainComplex.KFlatMonoidal.derivedTensorCompare_comp_comparison (Mod R)
            (exists_kFlat_resolution R) hK hL))))

/-- `Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_comparison` at the canonical derived
tensor product of Tag 06YU — the one
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` is seated on — with the
comparison in the pinned spelling. -/
theorem reseatIso_comp_canonicalComparisonHom (K L : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    letI := derivedMonoidal R
    (reseatIso (monoidalTensorCanonicalIso R) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L)).hom ≫ canonicalComparisonHom R K L hK hL =
      (CochainComplex.KFlatMonoidal.derivedTensorIso (Mod R) (exists_kFlat_resolution R)
        hK hL).hom :=
  reseatIso_comp_comparison R
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R) K L hK hL

/-! ### The two clauses of Tag 0FPT -/

/-- **The associator of total tensor complexes, pushed into `D(Mod(O))`.** -/
def complexAssociatorHom (K L M : Complexes R) :
    DerivedCategory.Q.obj (((K ⊗ L : Complexes R) ⊗ M : Complexes R)) ⟶
      DerivedCategory.Q.obj ((K ⊗ (L ⊗ M : Complexes R) : Complexes R)) :=
  DerivedCategory.Q.map (α_ K L M).hom

/-- `Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom` *is* the image of the
associator of `Comp(Mod(O))`. -/
theorem complexAssociatorHom_eq (K L M : Complexes R) :
    complexAssociatorHom R K L M = DerivedCategory.Q.map (α_ K L M).hom :=
  rfl

/-- **The Koszul symmetry of total tensor complexes, pushed into `D(Mod(O))`.** -/
def complexBraidingHom (K L : Complexes R) :
    DerivedCategory.Q.obj ((K ⊗ L : Complexes R)) ⟶
      DerivedCategory.Q.obj ((L ⊗ K : Complexes R)) :=
  DerivedCategory.Q.map (β_ K L).hom

/-- `Stacks.SheafOfModules.DerivedMonoidal.complexBraidingHom` *is* the image of the Koszul
symmetry of `Comp(Mod(O))`. -/
theorem complexBraidingHom_eq (K L : Complexes R) :
    complexBraidingHom R K L = DerivedCategory.Q.map (β_ K L).hom :=
  rfl

/-- **The right unitor of total tensor complexes, pushed into `D(Mod(O))`.** -/
def complexRightUnitorHom (K : Complexes R) :
    DerivedCategory.Q.obj ((K ⊗ 𝟙_ (Complexes R) : Complexes R)) ⟶ DerivedCategory.Q.obj K :=
  DerivedCategory.Q.map (ρ_ K).hom

/-- `Stacks.SheafOfModules.DerivedMonoidal.complexRightUnitorHom` *is* the image of the right
unitor of `Comp(Mod(O))`. -/
theorem complexRightUnitorHom_eq (K : Complexes R) :
    complexRightUnitorHom R K = DerivedCategory.Q.map (ρ_ K).hom :=
  rfl

/-- **The left unitor of total tensor complexes, pushed into `D(Mod(O))`.** -/
def complexLeftUnitorHom (K : Complexes R) :
    DerivedCategory.Q.obj ((𝟙_ (Complexes R) ⊗ K : Complexes R)) ⟶ DerivedCategory.Q.obj K :=
  DerivedCategory.Q.map (λ_ K).hom

/-- `Stacks.SheafOfModules.DerivedMonoidal.complexLeftUnitorHom` *is* the image of the left
unitor of `Comp(Mod(O))`. -/
theorem complexLeftUnitorHom_eq (K : Complexes R) :
    complexLeftUnitorHom R K = DerivedCategory.Q.map (λ_ K).hom :=
  rfl

/-- **The associativity constraint of the re-seated structure**, ascribed at the bifunctor
spelling of its source and target. -/
def canonicalAssociatorHom (X Y Z : DerivedModules R) :
    ((derivedTensorBifunctorOfSite R).obj
          (((derivedTensorBifunctorOfSite R).obj X).obj Y)).obj Z ⟶
      ((derivedTensorBifunctorOfSite R).obj X).obj
        (((derivedTensorBifunctorOfSite R).obj Y).obj Z) :=
  letI := canonicalDerivedMonoidal R
  (α_ X Y Z).hom

/-- `Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom` *is* the associator of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
theorem canonicalAssociatorHom_eq (X Y Z : DerivedModules R) :
    letI := canonicalDerivedMonoidal R
    canonicalAssociatorHom R X Y Z = (α_ X Y Z).hom :=
  rfl

/-- **The right unit constraint of the re-seated structure**, ascribed at the bifunctor
spelling of its source and with the unit spelled `DerivedCategory.Q.obj (𝟙_ (Complexes R))`,
the unit of `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
def canonicalRightUnitorHom (X : DerivedModules R) :
    ((derivedTensorBifunctorOfSite R).obj X).obj
        (DerivedCategory.Q.obj (𝟙_ (Complexes R))) ⟶ X :=
  letI := canonicalDerivedMonoidal R
  (ρ_ X).hom

/-- `Stacks.SheafOfModules.DerivedMonoidal.canonicalRightUnitorHom` *is* the right unitor of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
theorem canonicalRightUnitorHom_eq (X : DerivedModules R) :
    letI := canonicalDerivedMonoidal R
    canonicalRightUnitorHom R X = (ρ_ X).hom :=
  rfl

/-- **The left unit constraint of the re-seated structure**, ascribed at the bifunctor
spelling. -/
def canonicalLeftUnitorHom (X : DerivedModules R) :
    ((derivedTensorBifunctorOfSite R).obj
          (DerivedCategory.Q.obj (𝟙_ (Complexes R)))).obj X ⟶ X :=
  letI := canonicalDerivedMonoidal R
  (λ_ X).hom

/-- `Stacks.SheafOfModules.DerivedMonoidal.canonicalLeftUnitorHom` *is* the left unitor of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
theorem canonicalLeftUnitorHom_eq (X : DerivedModules R) :
    letI := canonicalDerivedMonoidal R
    canonicalLeftUnitorHom R X = (λ_ X).hom :=
  rfl

/-- **The commutativity constraint of the re-seated structure**, ascribed at the bifunctor
spelling. -/
def canonicalBraidingHom (X Y : DerivedModules R) :
    ((derivedTensorBifunctorOfSite R).obj X).obj Y ⟶
      ((derivedTensorBifunctorOfSite R).obj Y).obj X :=
  letI := canonicalDerivedMonoidal R
  letI := canonicalDerivedSymmetric R
  (β_ X Y).hom

/-- `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom` *is* the braiding of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`. -/
theorem canonicalBraidingHom_eq (X Y : DerivedModules R) :
    letI := canonicalDerivedMonoidal R
    letI := canonicalDerivedSymmetric R
    canonicalBraidingHom R X Y = (β_ X Y).hom :=
  rfl

/-- **Right whiskering for the re-seated structure**: the action of the derived tensor
bifunctor in its first variable, which is `▷` of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` by construction
(`CategoryTheory.MonoidalCategory.reseatStruct`). -/
def canonicalWhiskerRight {X Y : DerivedModules R} (f : X ⟶ Y) (Z : DerivedModules R) :
    ((derivedTensorBifunctorOfSite R).obj X).obj Z ⟶
      ((derivedTensorBifunctorOfSite R).obj Y).obj Z :=
  ((derivedTensorBifunctorOfSite R).map f).app Z

/-- **Left whiskering for the re-seated structure**: the action of the derived tensor bifunctor
in its second variable, which is `◁` of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
def canonicalWhiskerLeft (X : DerivedModules R) {Y Z : DerivedModules R} (g : Y ⟶ Z) :
    ((derivedTensorBifunctorOfSite R).obj X).obj Y ⟶
      ((derivedTensorBifunctorOfSite R).obj X).obj Z :=
  ((derivedTensorBifunctorOfSite R).obj X).map g

/-- `Stacks.SheafOfModules.DerivedMonoidal.canonicalWhiskerRight` *is* the right whiskering of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
theorem canonicalWhiskerRight_eq {X Y : DerivedModules R} (f : X ⟶ Y)
    (Z : DerivedModules R) :
    letI := canonicalDerivedMonoidal R
    canonicalWhiskerRight R f Z = f ▷ Z :=
  rfl

/-- `Stacks.SheafOfModules.DerivedMonoidal.canonicalWhiskerLeft` *is* the left whiskering of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
theorem canonicalWhiskerLeft_eq (X : DerivedModules R) {Y Z : DerivedModules R} (g : Y ⟶ Z) :
    letI := canonicalDerivedMonoidal R
    canonicalWhiskerLeft R X g = X ◁ g :=
  rfl

/-- **The associativity clause of Tag 0FPT**, as a proposition: on K-flat complexes the
canonical comparison of Tag 06YU carries the associator of `Comp(Mod(O))` to that of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, whose tensor product is the
derived tensor product of Tag 06YU on the nose. -/
def CanonicalComparisonAssociator (K L M : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L)
    (hM : Stacks.SheafOfModules.KFlat.KFlat R M) : Prop :=
  canonicalWhiskerRight R (canonicalComparisonHom R K L hK hL)
        (DerivedCategory.Q.obj M) ≫
      canonicalComparisonHom R (K ⊗ L) M (kFlat_tensor_complexes R hK hL) hM ≫
        complexAssociatorHom R K L M =
    canonicalAssociatorHom R (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj M) ≫
      canonicalWhiskerLeft R (DerivedCategory.Q.obj K)
          (canonicalComparisonHom R L M hL hM) ≫
        canonicalComparisonHom R K (L ⊗ M) hK (kFlat_tensor_complexes R hL hM)

/-- **The associativity constraint of the monoidal derived category of Tag 0FPT is the
associator of the total tensor product of complexes**, in the form
`Stacks.SheafOfModules.DerivedMonoidal.CanonicalComparisonAssociator`. -/
theorem canonicalComparison_associator (K L M : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L)
    (hM : Stacks.SheafOfModules.KFlat.KFlat R M) :
    CanonicalComparisonAssociator R K L M hK hL hM :=
  let := derivedMonoidal R
  reseat_associator_comp_of_eq (monoidalTensorCanonicalIso R) (canonicalUnitIso R)
    (complexAssociatorHom R K L M)
    (reseatIso_comp_canonicalComparisonHom R K L hK hL)
    (reseatIso_comp_canonicalComparisonHom R L M hL hM)
    (reseatIso_comp_canonicalComparisonHom R (K ⊗ L) M (kFlat_tensor_complexes R hK hL) hM)
    (reseatIso_comp_canonicalComparisonHom R K (L ⊗ M) hK (kFlat_tensor_complexes R hL hM))
    (CochainComplex.KFlatMonoidal.associator_derivedTensorIso (Mod R)
      (exists_kFlat_resolution R) hK hL hM)

/-- **The commutativity constraint of the monoidal derived category of Tag 0FPT is the Koszul
symmetry of complexes**: on K-flat complexes the canonical comparison of Tag 06YU carries the
braiding of `Comp(Mod(O))` to that of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`. -/
theorem canonicalComparison_braiding (K L : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    canonicalBraidingHom R (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        canonicalComparisonHom R L K hL hK =
      canonicalComparisonHom R K L hK hL ≫ complexBraidingHom R K L :=
  let := derivedMonoidal R
  let := derivedSymmetric R
  reseatSymmetric_braiding_comp_of_eq (monoidalTensorCanonicalIso R) (canonicalUnitIso R)
    (complexBraidingHom R K L)
    (reseatIso_comp_canonicalComparisonHom R K L hK hL)
    (reseatIso_comp_canonicalComparisonHom R L K hL hK)
    (CochainComplex.KFlatMonoidal.braiding_derivedTensorIso (Mod R)
      (exists_kFlat_resolution R) hK hL).symm

/-- **The right unit constraint of the monoidal derived category of Tag 0FPT is the right
unitor of complexes**: on a K-flat complex the canonical comparison of Tag 06YU at the unit
carries the right unitor of `Comp(Mod(O))` to that of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
theorem canonicalComparison_rightUnitor (K : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K) :
    canonicalRightUnitorHom R (DerivedCategory.Q.obj K) =
      canonicalComparisonHom R K (𝟙_ (Complexes R)) hK (kFlat_tensorUnit_complexes R) ≫
        complexRightUnitorHom R K :=
  let := derivedMonoidal R
  reseat_rightUnitor_comp_of_unitality (monoidalTensorCanonicalIso R) (canonicalUnitIso R)
    (complexRightUnitorHom R K)
    (reseatIso_comp_canonicalComparisonHom R K (𝟙_ (Complexes R)) hK
      (kFlat_tensorUnit_complexes R))
    (CochainComplex.KFlatMonoidal.rightUnitor_derivedTensorIso (Mod R)
      (exists_kFlat_resolution R) hK)

/-- **The left unit constraint of the monoidal derived category of Tag 0FPT is the left unitor
of complexes**: on a K-flat complex the canonical comparison of Tag 06YU at the unit carries
the left unitor of `Comp(Mod(O))` to that of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
theorem canonicalComparison_leftUnitor (K : Complexes R)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K) :
    canonicalLeftUnitorHom R (DerivedCategory.Q.obj K) =
      canonicalComparisonHom R (𝟙_ (Complexes R)) K (kFlat_tensorUnit_complexes R) hK ≫
        complexLeftUnitorHom R K :=
  let := derivedMonoidal R
  reseat_leftUnitor_comp_of_unitality (monoidalTensorCanonicalIso R) (canonicalUnitIso R)
    (complexLeftUnitorHom R K)
    (reseatIso_comp_canonicalComparisonHom R (𝟙_ (Complexes R)) K
      (kFlat_tensorUnit_complexes R) hK)
    (CochainComplex.KFlatMonoidal.leftUnitor_derivedTensorIso (Mod R)
      (exists_kFlat_resolution R) hK)

end Stacks.SheafOfModules.DerivedMonoidal

end
