module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedObjectSizeSmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.SmallRepresentatives
import StacksCore.Tactic.StacksAttribute

/-!
# The two models of modules on a chaotic site agree

Let `C` be a category regarded as a site with the chaotic topology `⊥` and let `R` be a sheaf
of rings on it. Modules on `C` admit two descriptions: as sheaves of modules `SheafOfModules R`
and as presheaves of modules `PresheafOfModules R.obj`. For the chaotic topology every presheaf
is a sheaf (`CategoryTheory.Presheaf.isSheaf_bot`), so the forgetful functor between them is an
equivalence; on objects and morphisms it is the identity, since a sheaf of modules is a presheaf
of modules together with a proposition.

That equivalence is `Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence`. This file
records the exactness it enjoys, the induced equivalence on cochain complexes, and the comparison
of the two size notions attached to the two models: the number of sections of a complex, and the
least size of a complex representing a given object of the derived category.

## Main definitions

* `Stacks.ModulesOnACategory.chaoticComplexEquivalence`: the induced equivalence on cochain
  complexes indexed by `ℤ`.
* `Stacks.ModulesOnACategory.chaoticDerivedEquivalence`: the induced equivalence on derived
  categories.

## Main results

* `Stacks.ModulesOnACategory.chaoticWEqualsLocallyBijective`: for the chaotic topology the
  weak equivalences of abelian-group-valued presheaves are the locally bijective maps.
* `Stacks.ModulesOnACategory.mapDerivedCategory_isEquivalence_of_equivalence`: an additive
  equivalence of abelian categories induces an equivalence of derived categories.
* `Stacks.ModulesOnACategory.complexSectionSize_eq_presheaf`: the size of a complex of sheaves
  of modules agrees with the size of the corresponding complex of presheaves of modules.
* `Stacks.ModulesOnACategory.derivedObjectSize_eq_presheaf`: the size of an object of the
  derived category agrees with the size of the corresponding object in the presheaf model.
* `Stacks.ModulesOnACategory.exists_small_quasiIso_subcomplex_presheaf`: Stacks 0GYY in the
  presheaf model, the uniformly bounded quasi-isomorphic subcomplex.

## Implementation notes

The equivalence is *definitionally* the identity in both directions: the functor sends a sheaf
of modules to its underlying presheaf and the inverse equips a presheaf with the proof that it
is a sheaf, so both round trips are the identity on objects and on morphisms up to proof
irrelevance. Consequently the induced functor on cochain complexes is the identity on terms and
differentials, and the two expressions for the number of sections of a complex are the
cardinality of literally the same type; the only discrepancy is a `Cardinal.lift`, which the
sheaf-side definition carries so that its value lands in the universe `max u v m r`.

## References

* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModulesOnACategory

universe t w u v m r

variable {C : Type u} [Category.{v} C]
  (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})

/-! ### The equivalence between the two models -/

/-- The forward direction of the equivalence forgets the sheaf condition. -/
@[simp]
lemma chaoticSheafPresheafEquivalence_functor_obj (X : SheafOfModules.{m} R) :
    (chaoticSheafPresheafEquivalence R).functor.obj X = X.val :=
  rfl

/-- The inverse direction of the equivalence changes nothing but the sheaf condition. -/
@[simp]
lemma chaoticSheafPresheafEquivalence_inverse_obj (P : PresheafOfModules.{m} R.obj) :
    ((chaoticSheafPresheafEquivalence R).inverse.obj P).val = P :=
  rfl

/-- The forgetful functor from sheaves of modules on a chaotic site to presheaves of modules is
an equivalence. -/
instance forgetIsEquivalence : (SheafOfModules.forget.{m} R).IsEquivalence :=
  (chaoticSheafPresheafEquivalence R).isEquivalence_functor

/-! ### Exactness of the two directions -/

/-- Forgetting the sheaf condition on a chaotic site is additive. -/
instance chaoticSheafPresheafEquivalence_functor_additive :
    (chaoticSheafPresheafEquivalence R).functor.Additive :=
  inferInstanceAs (SheafOfModules.forget R).Additive

/-- Regarding a presheaf of modules on a chaotic site as a sheaf of modules is additive. -/
instance chaoticSheafPresheafEquivalence_inverse_additive :
    (chaoticSheafPresheafEquivalence R).inverse.Additive :=
  inferInstance

/-- Regarding a presheaf of modules on a chaotic site as a sheaf of modules is left exact. -/
instance chaoticSheafPresheafEquivalence_inverse_preservesFiniteLimits :
    PreservesFiniteLimits (chaoticSheafPresheafEquivalence R).inverse :=
  inferInstance

/-- Regarding a presheaf of modules on a chaotic site as a sheaf of modules is right exact. -/
instance chaoticSheafPresheafEquivalence_inverse_preservesFiniteColimits :
    PreservesFiniteColimits (chaoticSheafPresheafEquivalence R).inverse :=
  inferInstance

/-- Forgetting the sheaf condition on a chaotic site is right exact. -/
instance forget_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.forget.{m} R) :=
  inferInstance

/-- For the chaotic topology a map of presheaves of abelian groups is a weak equivalence exactly
when it is locally injective and locally surjective. -/
instance chaoticWEqualsLocallyBijective :
    (⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m} := by
  let : ∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{m},
      IsIso (toSheafify (⊥ : GrothendieckTopology C) P) :=
    fun P => isIso_toSheafify _ (Presheaf.isSheaf_bot P)
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' _ _

/-! ### The induced equivalence on cochain complexes -/

/-- The equivalence between complexes of sheaves of `R`-modules and complexes of presheaves of
modules over the underlying presheaf of rings, induced degreewise by
`chaoticSheafPresheafEquivalence`. -/
def chaoticComplexEquivalence :
    CochainComplex (SheafOfModules.{m} R) ℤ ≌
      CochainComplex (PresheafOfModules.{m} R.obj) ℤ :=
  (chaoticSheafPresheafEquivalence R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The complex of presheaves underlying a complex of sheaves of modules has the same terms. -/
@[simp]
lemma chaoticComplexEquivalence_functor_obj_X
    (G : CochainComplex (SheafOfModules.{m} R) ℤ) (i : ℤ) :
    ((chaoticComplexEquivalence R).functor.obj G).X i = (G.X i).val :=
  rfl

/-- Reading a complex of presheaves of modules on a chaotic site as a complex of sheaves of
modules changes nothing: the round trip is the identity. -/
@[simp]
lemma chaoticComplexEquivalence_functor_obj_inverse_obj
    (F : CochainComplex (PresheafOfModules.{m} R.obj) ℤ) :
    (chaoticComplexEquivalence R).functor.obj
        ((chaoticComplexEquivalence R).inverse.obj F) = F :=
  rfl

/-- Forgetting the sheaf condition is exact, hence carries quasi-isomorphisms of complexes of
sheaves of modules to quasi-isomorphisms of complexes of presheaves of modules. -/
lemma quasiIso_chaoticComplexEquivalence_functor_map
    {G H : CochainComplex (SheafOfModules.{m} R) ℤ} (f : H ⟶ G) [QuasiIso f] :
    QuasiIso ((chaoticComplexEquivalence R).functor.map f) := by
  show QuasiIso (((chaoticSheafPresheafEquivalence R).functor.mapHomologicalComplex
    (ComplexShape.up ℤ)).map f)
  infer_instance

/-- Forgetting the sheaf condition carries subcomplexes to subcomplexes. -/
lemma mono_chaoticComplexEquivalence_functor_map
    {G H : CochainComplex (SheafOfModules.{m} R) ℤ} (f : H ⟶ G) [Mono f] :
    Mono ((chaoticComplexEquivalence R).functor.map f) :=
  (chaoticComplexEquivalence R).functor.map_mono f

/-! ### Comparison of the two size notions -/

/-- The size of a complex of sheaves of modules on a chaotic site is the size of the underlying
complex of presheaves of modules. The sheaf-side count carries a `Cardinal.lift.{max v r}` so
that it lands in `Cardinal.{max u v m r}`; once the module universe `m` already absorbs the site
and ring universes that lift is the identity, and the two counts agree on the nose. -/
lemma complexSectionSize_eq_presheaf
    (G : CochainComplex (SheafOfModules.{max u v r w} R) ℤ) :
    complexSectionSize G =
      QuasiCoherentEquivalence.complexSectionSize.{w} R.obj
        ((chaoticComplexEquivalence R).functor.obj G) := by
  show Cardinal.lift.{max v r} (Cardinal.mk (Σ i : ℤ, Σ U : C, (G.X i).val.obj (op U))) =
    Cardinal.mk (Σ i : ℤ, Σ U : C, (G.X i).val.obj (op U))
  exact Cardinal.lift_id'.{max v r, max u w} _

/-! ### The induced equivalence on derived categories -/

/-- The functor induced on homotopy categories by the identity functor is the identity. -/
def mapHomotopyCategoryIdIso (A : Type*) [Category* A] [Preadditive A] :
    (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)))

/-- An additive equivalence of abelian categories induces an equivalence of derived categories. -/
lemma mapDerivedCategory_isEquivalence_of_equivalence
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (E : A ≌ B) [E.functor.Additive] :
    E.functor.mapDerivedCategory.IsEquivalence := by
  have : E.inverse.Additive := inferInstance
  apply Localization.isEquivalence DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    (E.functor.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    E.functor.mapDerivedCategory
    (E.inverse.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    E.inverse.mapDerivedCategory
  · exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ E.inverse.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso E.unitIso.symm (ComplexShape.up ℤ) ≪≫
          mapHomotopyCategoryIdIso A) _ ≪≫ Functor.leftUnitor _
  · exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ E.functor.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso E.counitIso (ComplexShape.up ℤ) ≪≫
          mapHomotopyCategoryIdIso B) _ ≪≫ Functor.leftUnitor _

section Derived

variable [HasDerivedCategory.{t} (SheafOfModules.{max u v r w} R)]

/-- Forgetting the sheaf condition on a chaotic site induces an equivalence of derived
categories. -/
instance chaoticMapDerivedCategoryIsEquivalence :
    (chaoticSheafPresheafEquivalence R).functor.mapDerivedCategory.IsEquivalence :=
  mapDerivedCategory_isEquivalence_of_equivalence _

/-- The equivalence between the derived category of sheaves of `R`-modules and the derived
category of presheaves of modules over the underlying presheaf of rings. -/
noncomputable def chaoticDerivedEquivalence :
    DerivedCategory (SheafOfModules.{max u v r w} R) ≌
      DerivedCategory (PresheafOfModules.{max u v r w} R.obj) :=
  (chaoticSheafPresheafEquivalence R).functor.mapDerivedCategory.asEquivalence

/-- The equivalence of derived categories carries the object represented by a complex of sheaves
of modules to the object represented by the underlying complex of presheaves of modules. -/
noncomputable def chaoticDerivedEquivalenceQIso
    (G : CochainComplex (SheafOfModules.{max u v r w} R) ℤ) :
    (chaoticDerivedEquivalence R).functor.obj (DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.obj ((chaoticComplexEquivalence R).functor.obj G) :=
  (chaoticSheafPresheafEquivalence R).functor.mapDerivedCategoryFactors.app G

/-- An isomorphism from `Q F` to the image of `K` pulls back along the derived equivalence to an
isomorphism from the object represented by the corresponding sheaf complex to `K`. -/
private theorem nonempty_iso_of_chaoticDerivedEquivalence_functor_obj
    (F : CochainComplex (PresheafOfModules.{max u v r w} R.obj) ℤ)
    {K : DerivedCategory (SheafOfModules.{max u v r w} R)}
    (e : DerivedCategory.Q.obj F ≅ (chaoticDerivedEquivalence R).functor.obj K) :
    Nonempty (DerivedCategory.Q.obj ((chaoticComplexEquivalence R).inverse.obj F) ≅ K) :=
  ⟨(chaoticDerivedEquivalence R).functor.preimageIso
    (chaoticDerivedEquivalenceQIso R ((chaoticComplexEquivalence R).inverse.obj F) ≪≫ e)⟩

/-- The size of an object of the derived category of sheaves of modules on a chaotic site equals
the size of the corresponding object of the derived category of presheaves of modules. -/
lemma derivedObjectSize_eq_presheaf
    (K : DerivedCategory (SheafOfModules.{max u v r w} R)) :
    derivedObjectSize R K =
      QuasiCoherentEquivalence.derivedObjectSize.{w} R.obj
        ((chaoticDerivedEquivalence R).functor.obj K) := by
  have hset :
      {c : Cardinal.{max u v r w} |
          ∃ G : CochainComplex (SheafOfModules.{max u v r w} R) ℤ,
            Nonempty (DerivedCategory.Q.obj G ≅ K) ∧ c = complexSectionSize G} =
        {c : Cardinal.{max u v r w} |
          ∃ F : CochainComplex (PresheafOfModules.{max u v r w} R.obj) ℤ,
            Nonempty (DerivedCategory.Q.obj F ≅
                (chaoticDerivedEquivalence R).functor.obj K) ∧
              c = QuasiCoherentEquivalence.complexSectionSize.{w} R.obj F} := by
    ext c
    constructor
    · rintro ⟨G, ⟨e⟩, rfl⟩
      exact ⟨(chaoticComplexEquivalence R).functor.obj G,
        ⟨(chaoticDerivedEquivalenceQIso R G).symm ≪≫
          (chaoticDerivedEquivalence R).functor.mapIso e⟩,
        complexSectionSize_eq_presheaf R G⟩
    · rintro ⟨F, ⟨e⟩, rfl⟩
      exact ⟨(chaoticComplexEquivalence R).inverse.obj F,
        nonempty_iso_of_chaoticDerivedEquivalence_functor_obj R F e,
        (complexSectionSize_eq_presheaf R ((chaoticComplexEquivalence R).inverse.obj F)).symm⟩
  exact congrArg sInf hset

end Derived

/-! ### Small quasi-isomorphic subcomplexes in the presheaf model -/

/-- There is a cardinal, depending only on the category and its sheaf of rings, such that every
complex of presheaves of modules representing a derived object contains a quasi-isomorphic
subcomplex bounded by that cardinal and the size of the derived object. -/
@[stacks 0GYY "presheaf model"]
theorem exists_small_quasiIso_subcomplex_presheaf :
    ∃ κ : Cardinal.{max u v r w},
      ∀ (F : CochainComplex (PresheafOfModules.{max u v r w} R.obj) ℤ)
        (K : DerivedCategory (PresheafOfModules.{max u v r w} R.obj)),
        Nonempty (DerivedCategory.Q.obj F ≅ K) →
          ∃ (H : CochainComplex (PresheafOfModules.{max u v r w} R.obj) ℤ) (f : H ⟶ F),
            Mono f ∧ QuasiIso f ∧
              QuasiCoherentEquivalence.complexSectionSize.{w} R.obj H ≤
                max κ (QuasiCoherentEquivalence.derivedObjectSize.{w} R.obj K) := by
  let : HasDerivedCategory (SheafOfModules.{max u v r w} R) := HasDerivedCategory.standard _
  obtain ⟨κ, hκ⟩ := exists_small_quasiIso_subcomplex.{v, max u v r w, r, u} R
  refine ⟨κ, fun F K hFK => ?_⟩
  have hcounit : (chaoticDerivedEquivalence R).functor.obj
      ((chaoticDerivedEquivalence R).inverse.obj K) ≅ K :=
    (chaoticDerivedEquivalence R).counitIso.app K
  obtain ⟨Hs, fs, hmono, hqi, hsize⟩ :=
    hκ ((chaoticComplexEquivalence R).inverse.obj F)
      ((chaoticDerivedEquivalence R).inverse.obj K)
      (nonempty_iso_of_chaoticDerivedEquivalence_functor_obj R F (hFK.some ≪≫ hcounit.symm))
  refine ⟨(chaoticComplexEquivalence R).functor.obj Hs,
    (chaoticComplexEquivalence R).functor.map fs,
    mono_chaoticComplexEquivalence_functor_map R fs,
    quasiIso_chaoticComplexEquivalence_functor_map R fs, ?_⟩
  rwa [← complexSectionSize_eq_presheaf R Hs,
    ← QuasiCoherentEquivalence.derivedObjectSize_of_iso.{w} R.obj hcounit,
    ← derivedObjectSize_eq_presheaf R ((chaoticDerivedEquivalence R).inverse.obj K)]

end Stacks.ModulesOnACategory

end
