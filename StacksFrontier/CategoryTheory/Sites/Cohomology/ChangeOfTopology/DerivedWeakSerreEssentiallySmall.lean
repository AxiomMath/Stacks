module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedTransport
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedWeakSerreAcrossTopologies
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDerived

/-!
# Derived categories of a weak Serre subcategory for two topologies on an essentially small site

Let `C` be an essentially small category — its objects may lie in a larger universe than its
morphisms — carrying two Grothendieck topologies `J' ≤ J`, let `𝒪` be a sheaf of commutative
rings for `J`, let `A` be a weak Serre subcategory of `Mod(𝒪_J)` and let `B` be a family of
objects such that every object has a `J'`-covering by members of `B` and such that
`H^p_J(U, F) = 0` for `U` in `B`, `p > 0` and `F` in `A`. Then the derived categories of
complexes with cohomology in `A`, resp. in the image class `A' = ε_*A`, are equivalent:

`D_A(𝒪_J) ≌ D_{A'}(𝒪_{J'})`.

This is the second conclusion of [Stacks, Tag 07A8] for an essentially small site, deduced from
the same statement for a site whose objects, morphisms and sections share one universe,
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE`, by passing to a small model.
The big sites of a scheme are the motivating case: their objects lie one universe above their
morphisms, and they are essentially small.

## Main definitions

* `Stacks.Cohomology.CompareTopologies.EssentiallySmall.topology`: the topology a small model
  of `C` inherits from a topology of `C`.
* `Stacks.Cohomology.CompareTopologies.EssentiallySmall.ringedSite`: the small model as a
  ringed site, with the restriction of `𝒪`.
* `Stacks.Cohomology.CompareTopologies.EssentiallySmall.modulesEquivalence`: restriction of
  sheaves of modules to the small model, an equivalence.
* `Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLEOfEssentiallySmall`: the
  equivalence `D_A(𝒪_J) ≌ D_{A'}(𝒪_{J'})`.

## Main results

* `Stacks.Cohomology.CompareTopologies.EssentiallySmall.exists_covering_smallSet`: the
  covering hypothesis of [Stacks, Tag 07A8] passes to the small model.
* `Stacks.Cohomology.CompareTopologies.EssentiallySmall.isZero_moduleCohomology_smallClass`:
  so does the vanishing hypothesis.
* `Stacks.Cohomology.isZero_moduleCohomology_of_isZero_rightDerived_sections`: on a small site
  the module cohomology `H^p(U, F)` of a sheaf of modules vanishes as soon as the cohomology of
  its underlying abelian sheaf does ([Stacks, Tag 03FD]).

## Implementation notes

*The small model.* The small model `SmallModel C` of `C` comes with an equivalence
`C ≌ SmallModel C`, whose inverse `ι` is a dense subsite inclusion for the topology `ι` induces.
Restriction along `ι` is then an equivalence on sheaves of abelian groups (the Comparison
Lemma) and on sheaves of modules (`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`).
The restriction of `𝒪` is a sheaf of commutative rings on a site whose objects, morphisms and
sections all lie in the morphism universe of `C`, which is where the equivalence of
[Stacks, Tag 07A8] is available. The restriction of the module categories commutes with the
change of topology on the nose, both being restriction of sections, so the image class of the
small model corresponds to the image class of `C`.

*The hypotheses on the small model.* The family `B` is replaced by the objects of the small
model whose image is isomorphic to a member of `B`, which covers every object of the small model
for the coarser induced topology because `ι` is fully faithful. Cohomology of an abelian sheaf
over an object of the small model is cohomology over its image in `C`: the restriction of
abelian sheaves is an equivalence, and an equivalence may be pulled out of a right derived
functor (`CategoryTheory.Equivalence.compRightDerivedIso`). The equivalence of
[Stacks, Tag 07A8] for a ringed site asks for the vanishing of the cohomology of sheaves of
modules, and that is the vanishing of the cohomology of the underlying abelian sheaves by
[Stacks, Tag 03FD], which is available on the small model.

*The vanishing hypothesis.* It is stated, as in the source, for the cohomology `H^p_J(U, F)` of
the underlying abelian sheaf, the right derived functors of the sections over `U`.

*The derived categories.* Both derived categories are taken at arbitrary models
`HasDerivedCategory`; on the small model the standard models are used, which is where
[Stacks, Tag 07A8] for a ringed site is stated, and the comparison with the two given models is
`Stacks.UniverseLift.derivedCategoryBEquivalence`, for the two equivalences of module
categories.

## References

* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe d d' w u u₁

namespace Stacks.Cohomology

/-! ### Cohomology over isomorphic objects, and module cohomology on a small site -/

/-- **Cohomology over isomorphic objects is isomorphic**: an isomorphism `U ≅ V` gives an
isomorphism of the sections functors over `U` and over `V`, hence of their right derived
functors. -/
def rightDerivedSectionsIsoOfIso {C : Type u₁} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})] {U V : C} (e : U ≅ V) (p : ℕ) :
    ((sheafSections J AddCommGrpCat.{u}).obj (op U)).rightDerived p ≅
      ((sheafSections J AddCommGrpCat.{u}).obj (op V)).rightDerived p where
  hom := NatTrans.rightDerived ((sheafSections J AddCommGrpCat.{u}).map e.inv.op) p
  inv := NatTrans.rightDerived ((sheafSections J AddCommGrpCat.{u}).map e.hom.op) p
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, ← Functor.map_comp, ← op_comp, e.hom_inv_id, op_id,
      CategoryTheory.Functor.map_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, ← Functor.map_comp, ← op_comp, e.inv_hom_id, op_id,
      CategoryTheory.Functor.map_id, NatTrans.rightDerived_id]

/-- **On a small site, module cohomology vanishes with the cohomology of the underlying abelian
sheaf.** The module cohomology `H^p(U, F)` is the right derived functor of evaluation at `U`;
the forgetful functor to abelian groups is exact and faithful, so `H^p(U, F)` vanishes when its
underlying group does, and that group is the right derived functor of sections over `U` applied
to the underlying abelian sheaf of `F` by [Stacks, Tag 03FD]
(`ModuleSheafCohomology.sectionsComparisonIso`). -/
theorem isZero_moduleCohomology_of_isZero_rightDerived_sections
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D} (R : Sheaf K RingCat.{u})
    (X : D) (p : ℕ) (N : SheafOfModules.{u} R)
    (hN : IsZero ((((sheafSections K AddCommGrpCat.{u}).obj (op X)).rightDerived p).obj
      ((SheafOfModules.toSheaf R).obj N))) :
    IsZero (moduleCohomology R X p N) := by
  let E := SheafOfModules.evaluation.{u} R (op X)
  have : E.Additive := ⟨rfl⟩
  let Fg := forget₂ (ModuleCat.{u} (R.obj.obj (op X))) AddCommGrpCat.{u}
  have h₃ : IsZero (Fg.obj ((E.rightDerived p).obj N)) :=
    (hN.of_iso ((ModuleSheafCohomology.sectionsComparisonIso K R X p).app N)).of_iso
      ((Functor.rightDerivedCompIso E Fg p).app N).symm
  change IsZero ((E.rightDerived p).obj N)
  rw [IsZero.iff_id_eq_zero]
  exact Fg.zero_of_map_zero _ ((Fg.map_id _).trans (h₃.eq_of_src _ _))

end Stacks.Cohomology

namespace Stacks.Cohomology.CompareTopologies.EssentiallySmall

variable {C : Type u₁} [Category.{u} C] [EssentiallySmall.{u} C]

/-! ### The small model as a ringed site -/

/-- The inclusion of a small model of `C` into `C`, the inverse of `equivSmallModel`. -/
abbrev ι : SmallModel.{u} C ⥤ C := (equivSmallModel.{u} C).inverse

/-- The topology a small model of `C` inherits from a topology of `C`, for which the inclusion
`Stacks.Cohomology.CompareTopologies.EssentiallySmall.ι` is a dense subsite. -/
abbrev topology (J : GrothendieckTopology C) : GrothendieckTopology (SmallModel.{u} C) :=
  (ι (C := C)).inducedTopology J

/-- The inherited topology is monotone in the topology of `C`. -/
theorem topology_mono {J J' : GrothendieckTopology C} (h : J' ≤ J) :
    topology J' ≤ topology J := by
  intro X S hS
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hS ⊢
  exact h _ hS

variable {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})

/-- The small model of `C` as a ringed site: the inherited topology and the restriction of `𝒪`.
All three of its universes are the morphism universe of `C`. -/
abbrev ringedSite : RingedSite.{u, u, u} where
  C := SmallModel.{u} C
  J := topology J
  O := ((ι (C := C)).sheafPushforwardContinuous CommRingCat.{u} (topology J) J).obj O

/-- **Restriction of sheaves of modules to the small model is an equivalence**: it is the
Comparison Lemma for sheaves of modules, along the dense subsite inclusion of the small model. -/
abbrev modulesEquivalence (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) :
    SheafOfModules.{u} R ≌
      SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction (topology J) J ι R) :=
  haveI := ((equivSmallModel.{u} C).sheafCongr J (topology J)
    AddCommGrpCat.{u}).isEquivalence_functor
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (topology J) J ι R

/-- Restriction of sheaves of modules to the small model is additive. -/
instance modulesEquivalence_functor_additive (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u}) : (modulesEquivalence J R).functor.Additive where
  map_add := rfl

/-! ### The covering hypothesis on the small model -/

/-- The objects of the small model whose image in `C` is isomorphic to a member of `B`. -/
def smallSet (B : Set C) : Set (SmallModel.{u} C) :=
  {Y | ∃ U ∈ B, Nonempty ((ι (C := C)).obj Y ≅ U)}

/-- **The covering hypothesis passes to the small model.** If every object of `C` has a
`J'`-covering by members of `B`, every object of the small model has a covering, for the
inherited topology, by objects whose image is isomorphic to a member of `B`: the family of all
morphisms out of such objects. Its image covers the image of the object, since each member of a
covering by members of `B` factors, through an isomorphism, through the image of one of them. -/
theorem exists_covering_smallSet {J' : GrothendieckTopology C} (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{w} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (X : SmallModel.{u} C) :
    ∃ 𝒱 : PreZeroHypercover.{u} X, 𝒱.sieve₀ ∈ topology J' X ∧ ∀ i, smallSet B (𝒱.X i) := by
  obtain ⟨𝒰, h𝒰, hB𝒰⟩ := hB ((ι (C := C)).obj X)
  let 𝒱 : PreZeroHypercover.{u} X :=
    { I₀ := Σ Y : SmallModel.{u} C, {g : Y ⟶ X // smallSet B Y}
      X := fun i => i.1
      f := fun i => i.2.1 }
  refine ⟨𝒱, ?_, fun i => i.2.2⟩
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  refine J'.superset_covering ?_ h𝒰
  rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  let e := equivSmallModel.{u} C
  let g : e.functor.obj (𝒰.X i) ⟶ X :=
    (ι (C := C)).preimage (e.unitInv.app (𝒰.X i) ≫ 𝒰.f i)
  have hg : smallSet B (e.functor.obj (𝒰.X i)) :=
    ⟨𝒰.X i, hB𝒰 i, ⟨e.unitIso.symm.app (𝒰.X i)⟩⟩
  exact ⟨e.functor.obj (𝒰.X i), g, e.unit.app (𝒰.X i),
    ⟨_, 𝟙 _, g, Presieve.ofArrows.mk (⟨_, g, hg⟩ : 𝒱.I₀), Category.id_comp _⟩, by simp [g]⟩

/-! ### The vanishing hypothesis on the small model -/

variable [HasSheafify J AddCommGrpCat.{u}]

/-- **Cohomology on the small model is cohomology on `C`.** The cohomology over an object `Y`
of the small model of the restriction of an abelian sheaf `G` is the cohomology of `G` over the
image of `Y`: restriction is an equivalence of the categories of abelian sheaves, which may be
pulled out of the right derived functor of sections over `Y`, and restriction followed by
sections over `Y` is sections over the image of `Y`. -/
def rightDerivedSectionsSmallIso [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
    (G : Sheaf J AddCommGrpCat.{u}) (Y : SmallModel.{u} C) (p : ℕ) :
    (((sheafSections (topology J) AddCommGrpCat.{u}).obj (op Y)).rightDerived p).obj
        (((ι (C := C)).sheafPushforwardContinuous AddCommGrpCat.{u} (topology J) J).obj G) ≅
      (((sheafSections J AddCommGrpCat.{u}).obj (op ((ι (C := C)).obj Y))).rightDerived p).obj G :=
  let E := (equivSmallModel.{u} C).sheafCongr J (topology J) AddCommGrpCat.{u}
  haveI : E.functor.Additive := ⟨rfl⟩
  ((CategoryTheory.Equivalence.compRightDerivedIso E
      ((sheafSections (topology J) AddCommGrpCat.{u}).obj (op Y)) p).app G).symm

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
  [A.IsWeakSerreClass]

/-- The class `A` read on the small model: the sheaves of modules on the small model which are
restrictions of members of `A`. -/
abbrev smallClass :
    ObjectProperty (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O).O)) :=
  A.inverseImage (modulesEquivalence J (Stacks.SheafOfModules.Tensor.ringSheaf O)).inverse

/-- The class `A` read on the small model is a weak Serre subcategory, being the inverse image of
one under an exact functor. -/
instance isWeakSerreClass_smallClass : (smallClass O A).IsWeakSerreClass :=
  (ObjectProperty.isWeakSerreClass_inverseImage
    (C := SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction (topology J) J ι
      (Stacks.SheafOfModules.Tensor.ringSheaf O))) A
    (modulesEquivalence J (Stacks.SheafOfModules.Tensor.ringSheaf O)).inverse :)

/-- The restriction of a sheaf of modules lies in the class `A` read on the small model exactly
when the sheaf lies in `A`. -/
theorem smallClass_functor_obj_iff
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    smallClass O A
        ((modulesEquivalence J (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor.obj M) ↔
      A M :=
  (A.prop_iff_of_iso
    ((modulesEquivalence J (Stacks.SheafOfModules.Tensor.ringSheaf O)).unitIso.app M)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat] [A.IsWeakSerreClass] in
/-- **The vanishing hypothesis passes to the small model.** If `H^p_J(U, F) = 0` for `U` in `B`,
`p > 0` and `F` in `A`, then the module cohomology of the small model vanishes in positive
degrees over every object whose image is isomorphic to a member of `B`, on every sheaf of the
class `A` read on the small model. -/
theorem isZero_moduleCohomology_smallClass [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
    (B : Set C)
    (hvan : ∀ U : C, B U → ∀ p : ℕ, 0 < p →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O), A F →
        IsZero ((((sheafSections J AddCommGrpCat.{u}).obj (op U)).rightDerived p).obj
          ((SheafOfModules.toSheaf _).obj F)))
    (Y : SmallModel.{u} C) (hY : smallSet B Y) (p : ℕ) (hp : 0 < p)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O).O))
    (hN : smallClass O A N) :
    IsZero (Stacks.Cohomology.moduleCohomology
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O).O) Y p N) := by
  obtain ⟨U, hU, ⟨eY⟩⟩ := hY
  let Φ := modulesEquivalence J (Stacks.SheafOfModules.Tensor.ringSheaf O)
  apply Stacks.Cohomology.isZero_moduleCohomology_of_isZero_rightDerived_sections
  exact (hvan U hU p hp _ hN).of_iso
    ((((sheafSections (topology J) AddCommGrpCat.{u}).obj (op Y)).rightDerived p).mapIso
        ((SheafOfModules.toSheaf _).mapIso (Φ.counitIso.app N).symm) ≪≫
      (rightDerivedSectionsSmallIso
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj
          (Φ.inverse.obj N)) Y p).trans
        ((Stacks.Cohomology.rightDerivedSectionsIsoOfIso J eY p).app _))

/-! ### The image class on the small model -/

variable {J' : GrothendieckTopology C} (h : J' ≤ J)
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The image class corresponds to the image class of the small model.** Restriction of
sheaves of modules to the small model commutes with the change of topology on the nose, so a
sheaf of `𝒪_{J'}`-modules lies in the image class `A'` exactly when its restriction lies in the
image class of `A` read on the small model. -/
theorem imageOfLE_functor_obj_iff
    (N' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf O).ofLE h)) :
    imageOfLE (topology_mono h) (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O).O)
        (smallClass O A)
        ((modulesEquivalence J'
          ((Stacks.SheafOfModules.Tensor.ringSheaf O).ofLE h)).functor.obj N') ↔
      imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf O) A N' := by
  let Φ := modulesEquivalence J (Stacks.SheafOfModules.Tensor.ringSheaf O)
  let Φ' := modulesEquivalence J' ((Stacks.SheafOfModules.Tensor.ringSheaf O).ofLE h)
  constructor
  · rintro ⟨N, hN, ⟨e⟩⟩
    refine ⟨Φ.inverse.obj N, hN, ⟨Φ'.fullyFaithfulFunctor.preimageIso ?_⟩⟩
    exact ((pushforward (topology_mono h)
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O).O)).mapIso
        (Φ.counitIso.app N)).trans e
  · rintro ⟨M, hM, ⟨e⟩⟩
    exact ⟨Φ.functor.obj M, (smallClass_functor_obj_iff O A M).2 hM, ⟨Φ'.functor.mapIso e⟩⟩

end Stacks.Cohomology.CompareTopologies.EssentiallySmall

/-! ### The equivalence -/

namespace Stacks.Cohomology.CompareTopologies

open EssentiallySmall

variable {C : Type u₁} [Category.{u} C] [EssentiallySmall.{u} C]
  {J J' : GrothendieckTopology C} (h : J' ≤ J) (O : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
  [A.IsWeakSerreClass] (B : Set C)
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'}
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf O).ofLE h))]

/-- **The second conclusion of [Stacks, Tag 07A8], on an essentially small site.** Let `C` be an
essentially small category with two topologies `J' ≤ J`, let `𝒪` be a sheaf of commutative rings
for `J`, let `A` be a weak Serre subcategory of `Mod(𝒪_J)` and let `B` be a family of objects of
`C` such that

* every object of `C` has a `J'`-covering whose members lie in `B`, and
* for every `U` in `B` the cohomology `H^p_J(U, F)` vanishes for `p > 0` and `F` in `A`.

Then the derived category of complexes of `𝒪_J`-modules with cohomology in `A` and the derived
category of complexes of `𝒪_{J'}`-modules with cohomology in the image class
`A' = Stacks.Cohomology.CompareTopologies.imageOfLE h 𝒪 A` are equivalent, for any models of
the two derived categories.

On a small model of `C` this is `Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE`;
the two hypotheses pass to the small model by
`Stacks.Cohomology.CompareTopologies.EssentiallySmall.exists_covering_smallSet` and
`Stacks.Cohomology.CompareTopologies.EssentiallySmall.isZero_moduleCohomology_smallClass`, and the
two derived categories of `C` are compared with those of the small model by the derived functors
of the two equivalences of module categories, which match `A` and `A'` with their counterparts
on the small model. -/
def derivedEquivalenceImageOfLEOfEssentiallySmall
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{w} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : C, B U → ∀ p : ℕ, 0 < p →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O), A F →
        IsZero ((((sheafSections J AddCommGrpCat.{u}).obj (op U)).rightDerived p).obj
          ((SheafOfModules.toSheaf _).obj F))) :
    (DerivedCategoryB.derivedCategoryB A).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB
        (imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf O) A)).FullSubcategory :=
  -- On the small model the derived categories are the standard models, at which
  -- `derivedEquivalenceImageOfLE` is stated; the module categories of the small model appear
  -- under two definitionally equal spellings, and each needs its instance.
  letI : HasDerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O).O)) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O).O).ofLE (topology_mono h))) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction
      (topology J) J ι (Stacks.SheafOfModules.Tensor.ringSheaf O))) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction
      (topology J') J' ι ((Stacks.SheafOfModules.Tensor.ringSheaf O).ofLE h))) :=
    HasDerivedCategory.standard _
  haveI : (modulesEquivalence J (Stacks.SheafOfModules.Tensor.ringSheaf O)).inverse.Additive :=
    Equivalence.inverse_additive _
  haveI : (modulesEquivalence J'
      ((Stacks.SheafOfModules.Tensor.ringSheaf O).ofLE h)).inverse.Additive :=
    Equivalence.inverse_additive _
  haveI : @ObjectProperty.IsClosedUnderIsomorphisms (SheafOfModules.{u}
      (Stacks.DenseSubsiteModules.ringRestriction (topology J) J ι
        (Stacks.SheafOfModules.Tensor.ringSheaf O))) _ (smallClass O A) :=
    ⟨fun e hN => A.prop_of_iso
      ((modulesEquivalence J (Stacks.SheafOfModules.Tensor.ringSheaf O)).inverse.mapIso e) hN⟩
  haveI : @ObjectProperty.IsClosedUnderIsomorphisms (SheafOfModules.{u}
      (Stacks.DenseSubsiteModules.ringRestriction (topology J') J' ι
        ((Stacks.SheafOfModules.Tensor.ringSheaf O).ofLE h))) _
      (imageOfLE (topology_mono h) (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O).O)
        (smallClass O A)) :=
    ⟨fun e ⟨M, hM, ⟨e'⟩⟩ => ⟨M, hM, ⟨e'.trans e⟩⟩⟩
  (Stacks.UniverseLift.derivedCategoryBEquivalence
      (modulesEquivalence J (Stacks.SheafOfModules.Tensor.ringSheaf O)) A (smallClass O A)
      (smallClass_functor_obj_iff O A)).trans
    ((derivedEquivalenceImageOfLE (ringedSite O) (topology_mono h) (smallClass O A) (smallSet B)
      (exists_covering_smallSet B hB)
      (isZero_moduleCohomology_smallClass O A B hvan)).trans
    (Stacks.UniverseLift.derivedCategoryBEquivalence
      (modulesEquivalence J' ((Stacks.SheafOfModules.Tensor.ringSheaf O).ofLE h))
      (imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf O) A)
      (imageOfLE (topology_mono h) (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O).O)
        (smallClass O A))
      (imageOfLE_functor_obj_iff O A h)).symm)

end Stacks.Cohomology.CompareTopologies

end
