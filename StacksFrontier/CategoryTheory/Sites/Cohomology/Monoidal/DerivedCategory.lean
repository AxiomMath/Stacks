module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization

/-!
# The symmetric monoidal derived category of a ringed site

For a ringed site `(C, O)` the derived category `D(Mod(O))` is symmetric monoidal, with tensor
product the derived tensor product and unit the structure sheaf in degree zero.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.SymmetricMonoidalDerived`: a symmetric monoidal
  structure on `D(Mod(O))` together with isomorphisms identifying its tensor product with the
  total tensor product on K-flat complexes and its unit with the structure sheaf in degree zero.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`,
  `Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric`: the symmetric monoidal
  structure on `D(Mod(O))`.
* `Stacks.SheafOfModules.DerivedMonoidal.symmetricMonoidalDerived`: that structure with its two
  comparisons.

## Implementation notes

The construction is `CochainComplex.KFlatMonoidal.derivedSymmetric`, which localizes the
symmetric monoidal structure on `Comp(Mod(O))` of Tag 0FPQ twice: first at the homotopy
equivalences, which gives `K(Mod(O))`, then at the quasi-isomorphisms between K-flat objects,
which gives `D(Mod(O))`. The coherence comes from `CategoryTheory.Localization.Monoidal`, and
the associativity and commutativity constraints are the ones induced from `Comp(Mod(O))`, whose
braiding is the Koszul symmetry of Tag 0FNG.

The construction uses the existence of K-flat resolutions,
`Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso` (Tag 06YS). Since K-flat resolutions are
assembled from free modules on the Yoneda presheaves, and
`Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeYoneda` requires the ring universe to equal
the site's hom universe, all four universes of the source statement are taken equal to a single
`u` and the site is small. The restriction is inherited from Tags 06YS and 06YU, not introduced
here. The closure of the K-flat complexes under the tensor product and the unit, and the passage
from K-flatness to K-flatness in the first variable, are *not* hypotheses: the right unitor, the
associator and the braiding of `Comp(Mod(O))` prove them, so neither Tag 079R nor
`StacksTag06YUFlatSymmetry.kFlatLeft_of_kFlat` is used.

What is *not* recorded here is the compatibility of the comparison isomorphisms with the
associator and the braiding — the clause "with usual associativity and commutativity
constraints" of the source. It holds by construction, each constraint being the localization of
the corresponding constraint of `Comp(Mod(O))`, but it is not stated as an equation, and for that
reason no declaration in this file carries the project tag for Tag 0FPT.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `Mod(O)`, the category of `O`-modules on the ringed site `(C, O)`. -/
abbrev Mod := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)

/-- `Comp(Mod(O))`, the category of cochain complexes of `O`-modules. -/
abbrev Complexes := CochainComplex (Mod R) ℤ

variable [HasDerivedCategory.{d} (Mod R)]

/-- `D(Mod(O))`, the unbounded derived category of `O`-modules. -/
abbrev DerivedModules := DerivedCategory (Mod R)

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

omit [HasDerivedCategory.{d} (Mod R)] in
/-- Every complex of `O`-modules receives a quasi-isomorphism from a complex that is K-flat with
respect to `curriedTensor (Mod R)`, which is `Stacks.SheafOfModules.Tensor.sheafTensor R`. -/
theorem exists_kFlat_resolution (G : Complexes R) :
    ∃ (P : Complexes R) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) P ∧ QuasiIso f :=
  Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso R G

/-- **The derived category of modules on a ringed site is monoidal**, under the derived
tensor product. -/
@[instance_reducible]
def derivedMonoidal : MonoidalCategory (DerivedModules R) :=
  CochainComplex.KFlatMonoidal.derivedMonoidal (Mod R) (exists_kFlat_resolution R)

/-- **The derived category of modules on a ringed site is symmetric monoidal**, with the
commutativity constraint induced by the Koszul symmetry of complexes. -/
@[instance_reducible]
def derivedSymmetric :
    @SymmetricCategory (DerivedModules R) _ (derivedMonoidal R) :=
  CochainComplex.KFlatMonoidal.derivedSymmetric (Mod R) (exists_kFlat_resolution R)

/-! ### The field types of `SymmetricMonoidalDerived` -/

/-- A monoidal category structure on `D(Mod(O))`. -/
abbrev Monoidal := MonoidalCategory (DerivedModules R)

/-- A symmetry for a monoidal structure on `D(Mod(O))`. -/
abbrev Symmetric [Monoidal R] := SymmetricCategory (DerivedModules R)

/-- K-flatness of a complex of `O`-modules, Stacks Tag 06YN, in the spelling
`Stacks.DerivedTensor.RingedSite` uses. -/
abbrev KFlat (K : Complexes R) : Prop :=
  CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) K

/-- On K-flat complexes the tensor product of `D(Mod(O))` is the image of the total tensor
product `Tot(- ⊗_O -)`: this is what identifies it as the *derived* tensor product. -/
abbrev Comparison [Monoidal R] :=
  ∀ (K L : Complexes R), KFlat R K → KFlat R L →
    Iso (C := DerivedModules R)
      (MonoidalCategoryStruct.tensorObj (C := DerivedModules R)
        ((DerivedCategory.Q (C := Mod R)).obj K) ((DerivedCategory.Q (C := Mod R)).obj L))
      ((DerivedCategory.Q (C := Mod R)).obj (K ⊗ L))

/-- The unit of `D(Mod(O))` is the structure sheaf in degree zero. -/
abbrev UnitIso [Monoidal R] :=
  Iso (C := DerivedModules R) (𝟙_ (DerivedModules R))
    ((DerivedCategory.Q (C := Mod R)).obj
      ((CochainComplex.singleFunctor (Mod R) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))))

/-! ### The statement -/

/-- A symmetric monoidal structure on the derived category of modules on a ringed site, whose
tensor product is the derived tensor product — on K-flat complexes the total tensor product —
and whose unit is the structure sheaf in degree zero. -/
public structure SymmetricMonoidalDerived where
  /-- The monoidal structure on `D(Mod(O))`. -/
  monoidal : Monoidal R
  /-- The symmetry of the monoidal structure `monoidal`. -/
  symmetric : Symmetric R
  /-- On K-flat complexes the tensor product is the image of the total tensor product. -/
  comparison : Comparison R
  /-- The unit is the structure sheaf in degree zero. -/
  unitIso : UnitIso R

/-! ### The construction -/

/-- **The derived category of modules on a ringed site is symmetric monoidal**, with tensor
product the derived tensor product and unit the structure sheaf in degree zero. -/
public def symmetricMonoidalDerived : SymmetricMonoidalDerived R where
  monoidal := derivedMonoidal R
  symmetric := derivedSymmetric R
  comparison _ _ hK hL :=
    CochainComplex.KFlatMonoidal.derivedTensorIso (Mod R) (exists_kFlat_resolution R) hK hL
  unitIso :=
    CochainComplex.KFlatMonoidal.derivedUnitIso (Mod R) (exists_kFlat_resolution R)

/-! ### The monoidal structures on `Mod(O)` and `Comp(Mod(O))`, at pinned universes

The sections universe of `SheafOfModules.monoidalCategorySheafTensor` and of the three
structures built on it is `max u v` in the two site universes, which instance synthesis has to
solve from the `u` of `Mod R` at every use, and the whiskerings of the consumers cannot reduce
through a monoidal structure on `Comp(Mod(O))` synthesized while those universes are unsolved.
Each instance below fixes both site universes at the single universe `u`, which costs no
generality: the site is `SmallCategory.{u}` and the sheaf of rings is `CommRingCat.{u}`. They are
`local`: the consumers put them back in scope by name. -/

/-- `Mod(O)` is monoidal, at pinned universes. -/
@[instance_reducible] local instance monoidalCategoryMod : MonoidalCategory (Mod R) :=
  SheafOfModules.monoidalCategorySheafTensor.{u, u} R

/-- `Mod(O)` is symmetric monoidal, at pinned universes. -/
@[instance_reducible] local instance symmetricCategoryMod : SymmetricCategory (Mod R) :=
  SheafOfModules.symmetricCategorySheafTensor.{u, u} R

/-- `⊗_O` is bilinear on morphisms, at pinned universes. -/
local instance monoidalPreadditiveMod : MonoidalPreadditive (Mod R) :=
  SheafOfModules.monoidalPreadditiveSheafTensor.{u, u} R

/-- `Mod(O)` is monoidal closed, at pinned universes. -/
@[instance_reducible] local instance monoidalClosedMod : MonoidalClosed (Mod R) :=
  SheafOfModules.monoidalClosedSheafTensor.{u, u} R

/-- The graded tensor products of `O`-modules exist. -/
local instance hasTensorMod :
    ∀ A B : GradedObject ℤ (Mod R), GradedObject.HasTensor A B :=
  fun _ _ => inferInstance

/-- `Comp(Mod(O))` is monoidal, at pinned universes. -/
@[instance_reducible] local instance monoidalComplexes : MonoidalCategory (Complexes R) :=
  HomologicalComplex.monoidalCategory _ _

end Stacks.SheafOfModules.DerivedMonoidal

end
