module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.BoundedCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Transfer
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic

/-!
# The restriction of an exact functor of `D^b_Coh` to the coherent modules

Let `X` and `Y` be Noetherian schemes and let `F : D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` be an exact
functor carrying the coherent modules, placed in degree zero, to objects isomorphic to coherent
modules placed in degree zero. Then `F` restricts to a functor `H : Coh(𝒪_X) ⥤ Coh(𝒪_Y)`, and
`H` is an exact functor of abelian categories: a short exact sequence of coherent modules is a
distinguished triangle of `D^b_Coh(𝒪_X)`, `F` carries it to a distinguished triangle of
`D^b_Coh(𝒪_Y)` whose vertices are concentrated in degree zero, and the long exact cohomology
sequence of that triangle is the short exact sequence `0 → H(A) → H(B) → H(C) → 0`. When `X` and
`Y` are schemes over a ring `R` and `F` is `R`-linear, so is `H`.

## Main definitions

* `AlgebraicGeometry.coherentRestrictionOfBoundedCoherent`: the functor `H`.
* `AlgebraicGeometry.coherentRestrictionOfBoundedCoherentIso`: the isomorphism
  `H ⋙ (Coh(𝒪_Y) ⥤ D^b_Coh(𝒪_Y)) ≅ (Coh(𝒪_X) ⥤ D^b_Coh(𝒪_X)) ⋙ F`.

## Main results

* `AlgebraicGeometry.exactFunctor_coherentRestrictionOfBoundedCoherent`: `H` is exact.
* `AlgebraicGeometry.linear_coherentRestrictionOfBoundedCoherent`: `H` is linear when `F` is.
* `AlgebraicGeometry.subsingleton_hom_boundedCoherentSingle_shift`: there are no negative `Ext`s
  between coherent modules placed in degree zero in `D^b_Coh(𝒪_Y)`.
* `AlgebraicGeometry.AreSiblingsPerfect.objIso`, `AlgebraicGeometry.AreSiblingsPerfect.essSurj`,
  `AlgebraicGeometry.AreSiblingsPerfect.fullyFaithful` and
  `AlgebraicGeometry.AreSiblingsPerfect.isEquivalence`: [Stacks, Tag 0FZV] for sibling functors
  `D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` on Noetherian regular schemes ([Stacks, Tag 0FZZ]), which are
  compared along the equivalence `D^b(Coh(𝒪_X)) ≌ D^b_Coh(𝒪_X) = D_perf(𝒪_X)` of
  [Stacks, Tag 0FDB] and [Stacks, Tag 0FDC]: a sibling of a fully faithful, essentially surjective
  or equivalence functor is again one.

## References

* [Stacks Project, Tag 0G00](https://stacks.math.columbia.edu/tag/0G00)
* [Stacks Project, Tag 0FZV](https://stacks.math.columbia.edu/tag/0FZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

section Single

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The inclusion `Coh(𝒪_X) ⥤ D^b_Coh(𝒪_X)` followed by the inclusion of `D^b_Coh(𝒪_X)` into
`D(𝒪_X)` is the inclusion of the coherent modules into all modules followed by the degree-zero
functor `Mod(𝒪_X) ⥤ D(𝒪_X)`. -/
def boundedCoherentSingleFunctorCompιIso :
    boundedCoherentSingleFunctor X ⋙
        (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι ≅
      (coherentInModules X).ι ⋙ DerivedCategory.singleFunctor _ 0 :=
  Functor.isoWhiskerLeft (boundedSingleFunctor _) (coherentToModulesDerivedBoundedCompιIso X) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedSingleFunctorCompιIso _) _ ≪≫
    (coherentInModules X).ι.mapDerivedCategorySingleFunctor 0

/-- The inclusion of the coherent modules into `D^b_Coh(𝒪_X)` is fully faithful. -/
def boundedCoherentSingleFunctorFullyFaithful :
    (boundedCoherentSingleFunctor X).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι)
    (Functor.FullyFaithful.ofIso
      ((ObjectProperty.fullyFaithfulι _).comp (Functor.FullyFaithful.ofFullyFaithful _))
      (boundedCoherentSingleFunctorCompιIso X).symm)

/-- The inclusion of the coherent modules into `D^b_Coh(𝒪_X)` is full. -/
instance : (boundedCoherentSingleFunctor X).Full :=
  (boundedCoherentSingleFunctorFullyFaithful X).full

/-- The inclusion of the coherent modules into `D^b_Coh(𝒪_X)` is faithful. -/
instance : (boundedCoherentSingleFunctor X).Faithful :=
  (boundedCoherentSingleFunctorFullyFaithful X).faithful

/-- The inclusion of the coherent modules into `D^b_Coh(𝒪_X)` is additive. -/
instance : (boundedCoherentSingleFunctor X).Additive :=
  have : (boundedCoherentSingleFunctor X ⋙
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι).Additive :=
    Functor.additive_of_iso (boundedCoherentSingleFunctorCompιIso X).symm
  Functor.additive_of_comp_faithful _
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι

section Linear

variable (R : Type u) [CommRing R] [Linear R (SheafOfModules.{u} X.ringCatSheaf)]

/-- The inclusion of the coherent modules into `D^b_Coh(𝒪_X)` is linear over any ring acting
linearly on the `𝒪_X`-modules. -/
instance linear_boundedCoherentSingleFunctor : (boundedCoherentSingleFunctor X).Linear R :=
  have : (boundedCoherentSingleFunctor X ⋙
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι).Linear R :=
    Functor.linear_of_iso _ (boundedCoherentSingleFunctorCompιIso X).symm
  linear_of_faithful_comp R _ (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι

end Linear

omit [IsNoetherian X] in
/-- **There are no negative `Ext`s between coherent modules in `D^b_Coh(𝒪_X)`**: a morphism from
a coherent module placed in degree zero to the shift by `q < 0` of another one vanishes. -/
lemma subsingleton_hom_boundedCoherentSingle_shift
    (A B : SheafOfModules.CoherentModules X.ringCatSheaf)
    (q : ℤ) (hq : q < 0) :
    Subsingleton ((boundedCoherentSingleFunctor X).obj A ⟶
      ((boundedCoherentSingleFunctor X).obj B)⟦q⟧) := by
  let ι := (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι
  have h0 : ∀ h : (boundedCoherentSingleFunctor X).obj A ⟶
      ((boundedCoherentSingleFunctor X).obj B)⟦q⟧, ι.map h = 0 := by
    intro h
    let eA := (boundedCoherentSingleFunctorCompιIso X).app A
    let eB := (ι.commShiftIso q).app ((boundedCoherentSingleFunctor X).obj B) ≪≫
      (shiftFunctor _ q).mapIso ((boundedCoherentSingleFunctorCompιIso X).app B)
    have : eA.inv ≫ ι.map h ≫ eB.hom = 0 :=
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ 0 (-q) (by lia)
        (inferInstanceAs (DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.singleFunctor _ 0).obj ((coherentInModules X).ι.obj A)) 0))
        (DerivedCategory.TStructure.t.isGE_shift
          ((DerivedCategory.singleFunctor _ 0).obj ((coherentInModules X).ι.obj B)) 0 q (-q))
    simpa [cancel_epi, cancel_mono] using this
  exact ⟨fun f g => ι.map_injective ((h0 f).trans (h0 g).symm)⟩

end Single

section Restriction

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  (F : (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory ⥤
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y)).FullSubcategory)
  (hF : ∀ A, (boundedCoherentSingleFunctor Y).essImage
    (F.obj ((boundedCoherentSingleFunctor X).obj A)))

include hF

/-- **The restriction of `F` to the coherent modules.** If `F : D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)`
carries every coherent `𝒪_X`-module, placed in degree zero, to an object isomorphic to a coherent
`𝒪_Y`-module placed in degree zero, it restricts to a functor `Coh(𝒪_X) ⥤ Coh(𝒪_Y)`. -/
def coherentRestrictionOfBoundedCoherent :
    SheafOfModules.CoherentModules X.ringCatSheaf ⥤ SheafOfModules.CoherentModules Y.ringCatSheaf :=
  Functor.essImage.liftFunctor (boundedCoherentSingleFunctor X ⋙ F)
    (boundedCoherentSingleFunctor Y) hF

/-- The restriction of `F` to the coherent modules, followed by the inclusion of the coherent
modules into `D^b_Coh(𝒪_Y)`, is the inclusion into `D^b_Coh(𝒪_X)` followed by `F`. -/
def coherentRestrictionOfBoundedCoherentIso :
    coherentRestrictionOfBoundedCoherent F hF ⋙ boundedCoherentSingleFunctor Y ≅
      boundedCoherentSingleFunctor X ⋙ F :=
  Functor.essImage.liftFunctorCompIso _ _ _

omit [IsNoetherian X] [IsNoetherian Y] in
/-- The degree-`n` cohomology of the image under `F` of a coherent module vanishes for `n ≠ 0`. -/
lemma isZero_homology_boundedCoherent_restriction
    (A : SheafOfModules.CoherentModules X.ringCatSheaf)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((F.obj ((boundedCoherentSingleFunctor X).obj A)).obj)) := by
  let e : (F.obj ((boundedCoherentSingleFunctor X).obj A)).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((coherentInModules Y).ι.obj ((coherentRestrictionOfBoundedCoherent F hF).obj A)) :=
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y)).ι.mapIso
        ((coherentRestrictionOfBoundedCoherentIso F hF).symm.app A) ≪≫
      (boundedCoherentSingleFunctorCompιIso Y).app _
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ n).mapIso e)
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 n h
  · exact DerivedCategory.isZero_of_isLE _ 0 n h

/-- The cohomology in degree zero of the image under `F` of a coherent module is the value of the
restriction of `F` at that module, naturally. -/
def coherentRestrictionOfBoundedCoherentHomologyIso :
    boundedCoherentSingleFunctor X ⋙ F ⋙
        (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y)).ι ⋙
          DerivedCategory.homologyFunctor _ 0 ≅
      coherentRestrictionOfBoundedCoherent F hF ⋙ (coherentInModules Y).ι :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coherentRestrictionOfBoundedCoherentIso F hF).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedCoherentSingleFunctorCompιIso Y) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0) ≪≫
      Functor.rightUnitor _)

/-- The restriction of an exact functor to the coherent modules is additive. -/
instance additive_coherentRestrictionOfBoundedCoherent [F.Additive] :
    (coherentRestrictionOfBoundedCoherent F hF).Additive :=
  have : (coherentRestrictionOfBoundedCoherent F hF ⋙ boundedCoherentSingleFunctor Y).Additive :=
    Functor.additive_of_iso (coherentRestrictionOfBoundedCoherentIso F hF).symm
  Functor.additive_of_comp_faithful _ (boundedCoherentSingleFunctor Y)

section Linear

variable (R : Type u) [CommRing R] [Linear R (SheafOfModules.{u} X.ringCatSheaf)]
  [Linear R (SheafOfModules.{u} Y.ringCatSheaf)] [F.Linear R]

/-- **The restriction of a linear functor to the coherent modules is linear.** -/
instance linear_coherentRestrictionOfBoundedCoherent :
    (coherentRestrictionOfBoundedCoherent F hF).Linear R where
  map_smul {A B} f r := by
    apply (boundedCoherentSingleFunctor Y).map_injective
    have e : ∀ {A B} (f : A ⟶ B), (boundedCoherentSingleFunctor Y).map
        ((coherentRestrictionOfBoundedCoherent F hF).map f) =
          (coherentRestrictionOfBoundedCoherentIso F hF).hom.app A ≫
            F.map ((boundedCoherentSingleFunctor X).map f) ≫
              (coherentRestrictionOfBoundedCoherentIso F hF).inv.app B := fun f =>
      (NatIso.naturality_2 (coherentRestrictionOfBoundedCoherentIso F hF) f).symm
    rw [e, Functor.map_smul (boundedCoherentSingleFunctor X), Functor.map_smul F,
      Functor.map_smul (boundedCoherentSingleFunctor Y), e, Linear.smul_comp, Linear.comp_smul]

end Linear

variable [F.CommShift ℤ] [F.IsTriangulated]

omit [IsNoetherian X] [IsNoetherian Y] in
/-- **The restriction of an exact functor carries short exact sequences of coherent modules to
short exact sequences.** -/
lemma shortExact_map_coherentRestrictionOfBoundedCoherent
    {S : ShortComplex (SheafOfModules.CoherentModules X.ringCatSheaf)} (hS : S.ShortExact) :
    (S.map (coherentRestrictionOfBoundedCoherent F hF)).ShortExact := by
  let F' := coherentToModulesDerivedBounded X ⋙ F ⋙
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y)).ι
  let T := F'.mapTriangle.obj (Triangle.mk ((boundedSingleFunctor _).map S.f)
      ((boundedSingleFunctor _).map S.g) (boundedSingleδ hS))
  have hT : T ∈ distTriang _ := F'.map_distinguished _ (boundedSingleTriangle_distinguished hS)
  have hmono : Mono ((DerivedCategory.homologyFunctor _ 0).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (-1) 0).2
      ((isZero_homology_boundedCoherent_restriction F hF S.X₃ (-1) (by decide)).eq_of_src _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor _ 0).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1).2
      ((isZero_homology_boundedCoherent_restriction F hF S.X₁ 1 (by decide)).eq_of_tgt _ _)
  have hG : (ShortComplex.mk ((DerivedCategory.homologyFunctor _ 0).map T.mor₁)
      ((DerivedCategory.homologyFunctor _ 0).map T.mor₂)
      (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT,
        Functor.map_zero])).ShortExact := ⟨DerivedCategory.HomologySequence.exact₂ T hT 0⟩
  let e := coherentRestrictionOfBoundedCoherentHomologyIso F hF
  have hι : ((S.map (coherentRestrictionOfBoundedCoherent F hF)).map
      (coherentInModules Y).ι).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) (e.hom.naturality S.f).symm
        (e.hom.naturality S.g).symm) hG
  have : Mono (S.map (coherentRestrictionOfBoundedCoherent F hF)).f :=
    (coherentInModules Y).ι.mono_of_mono_map hι.mono_f
  have : Epi (S.map (coherentRestrictionOfBoundedCoherent F hF)).g :=
    (coherentInModules Y).ι.epi_of_epi_map hι.epi_g
  exact ⟨(ShortComplex.exact_map_iff_of_faithful _ (coherentInModules Y).ι).1 hι.exact⟩

omit [IsNoetherian X] [IsNoetherian Y] in
/-- **The restriction of an exact functor `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` to the coherent modules
is an exact functor `Coh(𝒪_X) ⥤ Coh(𝒪_Y)`.** -/
theorem exactFunctor_coherentRestrictionOfBoundedCoherent :
    exactFunctor _ _ (coherentRestrictionOfBoundedCoherent F hF) :=
  ((Functor.exact_tfae (coherentRestrictionOfBoundedCoherent F hF)).out 1 4).1
    fun _ hS => shortExact_map_coherentRestrictionOfBoundedCoherent F hF hS

end Restriction

section PerfectSiblings

/-! ### Sibling functors between perfect derived categories -/

variable {X Y : Scheme.{u}} {hX : IsRegular X} {hY : IsRegular Y} [IsNoetherian X]
  [IsNoetherian Y]
  {F F' : (perfectInModules X).FullSubcategory ⥤ (perfectInModules Y).FullSubcategory}
  {_ : F.CommShift ℤ} {_ : F.IsTriangulated} {_ : F'.CommShift ℤ} {_ : F'.IsTriangulated}

/-- The inclusion `D^b_Coh(𝒪_X) ⥤ D_perf(𝒪_X)` coming from the equality of the two properties on a
regular scheme ([Stacks, Tag 0FDC]) is essentially surjective: every perfect object is bounded
with coherent cohomology. -/
private lemma essSurj_ιOfLE_perfectInModules_ge (X : Scheme.{u}) (hX : IsRegular X)
    [CompactSpace X] :
    (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge).EssSurj :=
  ⟨fun K => ⟨⟨K.obj, (perfectInModules_eq_derivedCategoryBBounded X hX).le _ K.property⟩,
    ⟨Iso.refl _⟩⟩⟩

/-- The functor `D^b(Coh(𝒪_X)) ⥤ D_perf(𝒪_X)` is an equivalence on a Noetherian regular scheme
([Stacks, Tag 0FDB] and [Stacks, Tag 0FDC]). -/
private lemma isEquivalence_perfectSiblingComparison (X : Scheme.{u}) (hX : IsRegular X)
    [IsNoetherian X] :
    (coherentToModulesDerivedBounded X ⋙
      ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge).IsEquivalence :=
  have := essSurj_ιOfLE_perfectInModules_ge X hX
  have : (ObjectProperty.ιOfLE
      (perfectInModules_eq_derivedCategoryBBounded X hX).ge).IsEquivalence := {}
  inferInstance

/-- **Siblings agree object by object**: if `F, F' : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` are siblings,
then `F(E) ≅ F'(E)` for every perfect `E`. -/
theorem AreSiblingsPerfect.objIso (h : AreSiblingsPerfect hX hY F F')
    (E : (perfectInModules X).FullSubcategory) : Nonempty (F.obj E ≅ F'.obj E) := by
  let c := coherentToModulesDerivedBounded X ⋙
    ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge
  have := isEquivalence_perfectSiblingComparison X hX
  obtain ⟨e⟩ := AreSiblings.objIso h (c.objPreimage E)
  let iY := ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded Y hY).le
  let i : c.obj (c.objPreimage E) ≅ E := c.objObjPreimageIso E
  exact ⟨F.mapIso i.symm ≪≫ (iY.preimageIso e : F.obj (c.obj (c.objPreimage E)) ≅ _) ≪≫
    F'.mapIso i⟩

/-- **Stacks Project, Tag 0FZV (1), for perfect derived categories.** A sibling of an essentially
surjective exact functor `D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` is essentially surjective. -/
theorem AreSiblingsPerfect.essSurj (h : AreSiblingsPerfect hX hY F F') [hF : F.EssSurj] :
    F'.EssSurj :=
  ⟨fun N => ⟨F.objPreimage N, ⟨((h.objIso (F.objPreimage N)).some).symm ≪≫
    F.objObjPreimageIso N⟩⟩⟩

/-- **Stacks Project, Tag 0FZV (2), for perfect derived categories.** A sibling of a fully
faithful exact functor `D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` is fully faithful. -/
theorem AreSiblingsPerfect.fullyFaithful (h : AreSiblingsPerfect hX hY F F')
    (hF : Nonempty F.FullyFaithful) : Nonempty F'.FullyFaithful := by
  let c := coherentToModulesDerivedBounded X ⋙
    ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge
  let iY := ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded Y hY).le
  have := isEquivalence_perfectSiblingComparison X hX
  have hc : c.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful c
  have hiY : iY.FullyFaithful := ObjectProperty.fullyFaithfulιOfLE _
  obtain ⟨hG'⟩ := fullyFaithful_of_areSiblings h ⟨(hc.comp hF.some).comp hiY⟩
  let e : c.asEquivalence.inverse ⋙ c ⋙ F' ≅ F' :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight c.asEquivalence.counitIso F' ≪≫ F'.leftUnitor
  exact ⟨((Functor.FullyFaithful.ofFullyFaithful c.asEquivalence.inverse).comp
    (Functor.FullyFaithful.ofCompFaithful (G := iY) hG')).ofIso e⟩

/-- **A sibling of an exact equivalence `D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` is an equivalence**, by
[Stacks, Tag 0FZV]: it is fully faithful and essentially surjective. -/
theorem AreSiblingsPerfect.isEquivalence (h : AreSiblingsPerfect hX hY F F')
    [hF : F.IsEquivalence] : F'.IsEquivalence :=
  have := h.essSurj
  have hF' := (h.fullyFaithful ⟨Functor.FullyFaithful.ofFullyFaithful F⟩).some
  have := hF'.full
  have := hF'.faithful
  {}

end PerfectSiblings

end AlgebraicGeometry

end
