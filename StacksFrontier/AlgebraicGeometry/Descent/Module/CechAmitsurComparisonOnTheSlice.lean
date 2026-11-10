module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechAmitsurComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongACoefficientFunctor

/-!
# The Čech-to-Amitsur comparison with coefficients given only on the slice

This file compares the Čech complex of a one-member covering `{V → T}` with the Amitsur complex
`(A/R)_• ⊗_R M` [Stacks, Tag 03FJ], for coefficients `H` given only as a presheaf of `R`-modules
on the slice over `T`, rather than as a presheaf on the ambient category. This is the setting of
the associated module `Fᵃ` of [Stacks, Tag 03DU], a presheaf of `R`-modules on the slice at an
affine object `T` with `R = Γ(T, 𝒪)`.

The Čech cosimplicial object of `{V → T}` is identified with the sections of the powers of `V`
over `T`; under a comparison of those sections with the Amitsur coefficients it becomes
`(A/R)_• ⊗_R M`, and faithful flatness of `R → A` then gives the vanishing of the higher Čech
cohomology.

## Main definitions

* `Stacks.CechSite.sliceSingletonCechProj`, `Stacks.CechSite.sliceSingletonCechSect`,
  `Stacks.CechSite.sliceSingletonCechProjNatTrans` and
  `Stacks.CechSite.sliceSingletonCechCosimplicialIso`: the reduction of the Čech cosimplicial
  object of `{V → T}` to `Stacks.CechSite.powerSections`, for a presheaf on the slice.
* `Stacks.Descent.sliceCechCosimplicialObjectIsoAmitsurOfPowerSections`: the identification of
  that cosimplicial object with `(A/R)_• ⊗_R M`.

## Main results

* `Stacks.Descent.isZero_sliceCechCohomology_singleton_succ_of_powerSections`: for `R → A`
  faithfully flat, the higher Čech cohomology of a one-member covering with slice coefficients
  vanishes, given the coefficient comparison at the powers.
* `Stacks.Descent.isZero_sliceCechCohomology_singleton_succ_of_adjunction_of_powerSections`:
  the same under an adjunction, where the termwise identification
  `Γ(V ×_T ⋯ ×_T V, 𝒪) = A ⊗_R ⋯ ⊗_R A` holds automatically.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 023F](https://stacks.math.columbia.edu/tag/023F)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe w v v' u u' uR uA uM

namespace Stacks.CechSite

section Singleton

variable {C : Type u} [Category.{v} C] {T V : C} (h : V ⟶ T) [HasFiniteProducts (Over T)]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
  (H : (Over T)ᵒᵖ ⥤ A)

/-- The projection of the Čech cosimplicial object of the one-member family `{V → T}` onto its
single factor, the sections over the power of `V`. -/
noncomputable def sliceSingletonCechProj (n : SimplexCategory) :
    (sliceCechCosimplicialObject (PreZeroHypercover.singleton.{w} h) H).obj n ⟶
      (powerSections (Over.mk h) H).obj n :=
  Pi.π (fun _ : (Fin (n.len + 1) → PUnit.{w + 1}) =>
    (powerSections (Over.mk h) H).obj n) (fun _ => PUnit.unit)

/-- The section of `Stacks.CechSite.sliceSingletonCechProj` given by the diagonal. -/
noncomputable def sliceSingletonCechSect (n : SimplexCategory) :
    (powerSections (Over.mk h) H).obj n ⟶
      (sliceCechCosimplicialObject (PreZeroHypercover.singleton.{w} h) H).obj n :=
  Pi.lift (fun _ : (Fin (n.len + 1) → PUnit.{w + 1}) => 𝟙 _)

/-- The diagonal `Stacks.CechSite.sliceSingletonCechSect` is a section of the projection
`Stacks.CechSite.sliceSingletonCechProj`. -/
lemma sliceSingletonCechSect_comp_proj (n : SimplexCategory) :
    sliceSingletonCechSect h H n ≫ sliceSingletonCechProj.{w} h H n = 𝟙 _ := Pi.lift_comp_π _ _

/-- The projection `Stacks.CechSite.sliceSingletonCechProj` followed by the diagonal
`Stacks.CechSite.sliceSingletonCechSect` is the identity. -/
lemma sliceSingletonCechProj_comp_sect (n : SimplexCategory) :
    sliceSingletonCechProj.{w} h H n ≫ sliceSingletonCechSect h H n = 𝟙 _ := by
  refine Pi.hom_ext _ _ (fun i => ?_)
  obtain rfl : (fun _ : Fin (n.len + 1) => PUnit.unit) = i := Subsingleton.elim _ _
  calc (sliceSingletonCechProj.{w} h H n ≫ sliceSingletonCechSect h H n) ≫
        sliceSingletonCechProj.{w} h H n
      = sliceSingletonCechProj.{w} h H n ≫
          (sliceSingletonCechSect h H n ≫ sliceSingletonCechProj.{w} h H n) :=
        Category.assoc _ _ _
    _ = sliceSingletonCechProj.{w} h H n ≫ 𝟙 _ := by rw [sliceSingletonCechSect_comp_proj]
    _ = sliceSingletonCechProj.{w} h H n := Category.comp_id _
    _ = 𝟙 _ ≫ sliceSingletonCechProj.{w} h H n := (Category.id_comp _).symm

/-- The projection is natural in the simplex category: a cosimplicial structure map of the
Čech cosimplicial object of a one-member family is, on the single factor, the restriction
along the reindexing map of the power. -/
lemma sliceSingletonCechProj_naturality {n m : SimplexCategory} (g : n ⟶ m) :
    (sliceCechCosimplicialObject (PreZeroHypercover.singleton.{w} h) H).map g ≫
        sliceSingletonCechProj.{w} h H m =
      sliceSingletonCechProj.{w} h H n ≫
        (powerSections (Over.mk h) H).map g := by
  change (Pi.lift (fun i : Fin (m.len + 1) → PUnit.{w + 1} =>
      Pi.π (fun _ : (Fin (n.len + 1) → PUnit.{w + 1}) =>
          (powerSections (Over.mk h) H).obj n)
        (fun a => i (g.toOrderHom a)) ≫
        (powerSections (Over.mk h) H).map g)) ≫
      Pi.π (fun _ : (Fin (m.len + 1) → PUnit.{w + 1}) =>
        (powerSections (Over.mk h) H).obj m) (fun _ => PUnit.unit) = _
  exact Pi.lift_comp_π _ _

/-- The projection, as a morphism of cosimplicial objects. -/
noncomputable def sliceSingletonCechProjNatTrans :
    sliceCechCosimplicialObject (PreZeroHypercover.singleton.{w} h) H ⟶
      powerSections (Over.mk h) H where
  app n := sliceSingletonCechProj.{w} h H n
  naturality _ _ g := sliceSingletonCechProj_naturality.{w} h H g

/-- The projection `Stacks.CechSite.sliceSingletonCechProj` is an isomorphism in every degree. -/
lemma isIso_sliceSingletonCechProj (n : SimplexCategory) :
    IsIso (sliceSingletonCechProj.{w} h H n) :=
  ⟨sliceSingletonCechSect h H n, sliceSingletonCechProj_comp_sect.{w} h H n,
    sliceSingletonCechSect_comp_proj.{w} h H n⟩

/-- The Čech cosimplicial object of the one-member family `{V → T}` is isomorphic to the sections
of the powers of `V` over `T`. -/
noncomputable def sliceSingletonCechCosimplicialIso :
    sliceCechCosimplicialObject (PreZeroHypercover.singleton.{w} h) H ≅
      powerSections (Over.mk h) H :=
  haveI : ∀ n, IsIso ((sliceSingletonCechProjNatTrans.{w} h H).app n) :=
    fun n => isIso_sliceSingletonCechProj.{w} h H n
  haveI : IsIso (sliceSingletonCechProjNatTrans.{w} h H) := NatIso.isIso_of_isIso_app _
  asIso (sliceSingletonCechProjNatTrans.{w} h H)

end Singleton

end Stacks.CechSite

namespace Stacks.Descent

open Stacks.CechSite

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  {C : Type u} [Category.{v} C] [HasFiniteLimits C] {T V : C} (h : V ⟶ T)
  (H : (Over T)ᵒᵖ ⥤ ModuleCat.{max uR uA uM} R)
  (Γ : (Over T)ᵒᵖ ⥤ CommAlgCat.{max uR uA} (ULift.{uA} R))

/-- The Čech cosimplicial object of the one-member family `{V → T}`, with coefficients `H` on the
slice, is isomorphic to `(A/R)_• ⊗_R M`, given an identification of the sections of the powers of
`V` with the Amitsur coefficients, of the sections of the terminal arrow with `R → A`, and the
invertibility of the comparison maps `Stacks.CechSite.conerveSectionsMap`. -/
noncomputable def sliceCechCosimplicialObjectIsoAmitsurOfPowerSections
    (hpow : powerSections (Over.mk h) H ≅
      powerSections (Over.mk h) Γ ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (Over.mk h) Γ ≅ algebraMapArrow R A)
    (hiso : ∀ n : SimplexCategory, IsIso (conerveSectionsMap (Over.mk h) Γ n)) :
    sliceCechCosimplicialObject (PreZeroHypercover.singleton.{max uR uA uM} h) H ≅
      (amitsurAugmentation R A M).right :=
  sliceSingletonCechCosimplicialIso.{max uR uA uM} h H ≪≫ hpow ≪≫
    Functor.isoWhiskerRight (conerveSectionsIso (Over.mk h) Γ hiso).symm
        (amitsurCoefficients.{uR, uA, uM} R M) ≪≫
      Functor.isoWhiskerRight (CosimplicialObject.cechConerve.mapIso harrow)
        (amitsurCoefficients.{uR, uA, uM} R M)

/-- For `R → A` faithfully flat, the Čech cohomology in positive degrees of the one-member
covering `{V → T}` with coefficients `H` on the slice vanishes, under the hypotheses of
`Stacks.Descent.sliceCechCosimplicialObjectIsoAmitsurOfPowerSections`. -/
theorem isZero_sliceCechCohomology_singleton_succ_of_powerSections [Module.FaithfullyFlat R A]
    (hpow : powerSections (Over.mk h) H ≅
      powerSections (Over.mk h) Γ ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (Over.mk h) Γ ≅ algebraMapArrow R A)
    (hiso : ∀ n : SimplexCategory, IsIso (conerveSectionsMap (Over.mk h) Γ n)) (p : ℕ) :
    IsZero (sliceCechCohomology (PreZeroHypercover.singleton.{max uR uA uM} h) H (p + 1)) :=
  (exactAt_amitsurCochainComplex_succ R A M p).isZero_homology.of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{max uR uA uM} R)
      (ComplexShape.up ℕ) (p + 1)).mapIso
      (sliceCechComplexIsoOfCosimplicialIso (PreZeroHypercover.singleton.{max uR uA uM} h)
        (sliceCechCosimplicialObjectIsoAmitsurOfPowerSections h H Γ hpow harrow hiso)))

section Adjunction

variable {L : Over T ⥤ (CommAlgCat.{max uR uA} (ULift.{uA} R))ᵒᵖ}
  {G : (CommAlgCat.{max uR uA} (ULift.{uA} R))ᵒᵖ ⥤ Over T}

/-- Under an adjunction `L ⊣ G` with `G` fully faithful and preserving limits, the degreewise
comparison map from the Čech conerve of the sections of the terminal arrow to the sections of the
powers is an isomorphism at every simplex. -/
theorem isIso_conerveSectionsMap_of_adjunction (adj : L ⊣ G) [G.Full] [G.Faithful]
    [PreservesLimitsOfSize.{0, 0} G] (a : CommAlgCat.{max uR uA} (ULift.{uA} R))
    (n : SimplexCategory) :
    IsIso (conerveSectionsMap (G.obj (op a)) L.leftOp n) :=
  isIso_conerveSectionsMap _ _ n (isColimitPowerSectionsCoconeOfAdjunction adj a n)

/-- Under an adjunction, the Čech cosimplicial object of `{G a → T}` with coefficients `H` on the
slice is isomorphic to `(A/R)_• ⊗_R M`, given the two coefficient comparisons. -/
noncomputable def sliceCechCosimplicialObjectIsoAmitsurOfAdjunction (adj : L ⊣ G) [G.Full]
    [G.Faithful] [PreservesLimitsOfSize.{0, 0} G] (a : CommAlgCat.{max uR uA} (ULift.{uA} R))
    (hpow : powerSections (G.obj (op a)) H ≅
      powerSections (G.obj (op a)) L.leftOp ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (G.obj (op a)) L.leftOp ≅ algebraMapArrow R A) :
    sliceCechCosimplicialObject
        (PreZeroHypercover.singleton.{max uR uA uM} (G.obj (op a)).hom) H ≅
      (amitsurAugmentation R A M).right :=
  sliceCechCosimplicialObjectIsoAmitsurOfPowerSections (G.obj (op a)).hom H L.leftOp hpow harrow
    (fun n => isIso_conerveSectionsMap_of_adjunction adj a n)

/-- Under an adjunction, the Čech complex of `{G a → T}` with coefficients `H` on the slice is
isomorphic, as a cochain complex, to the Amitsur complex `s((A/R)_• ⊗_R M)`, given the two
coefficient comparisons. -/
noncomputable def sliceCechComplexIsoAmitsurOfAdjunction (adj : L ⊣ G) [G.Full] [G.Faithful]
    [PreservesLimitsOfSize.{0, 0} G] (a : CommAlgCat.{max uR uA} (ULift.{uA} R))
    (hpow : powerSections (G.obj (op a)) H ≅
      powerSections (G.obj (op a)) L.leftOp ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (G.obj (op a)) L.leftOp ≅ algebraMapArrow R A) :
    sliceCechComplex (PreZeroHypercover.singleton.{max uR uA uM} (G.obj (op a)).hom) H ≅
      amitsurCochainComplex R A M :=
  sliceCechComplexIsoOfCosimplicialIso
    (PreZeroHypercover.singleton.{max uR uA uM} (G.obj (op a)).hom)
    (sliceCechCosimplicialObjectIsoAmitsurOfAdjunction H adj a hpow harrow)

/-- Under an adjunction and for `R → A` faithfully flat, the Čech cohomology in positive degrees
of `{G a → T}` with coefficients `H` on the slice vanishes, given the two coefficient
comparisons. -/
theorem isZero_sliceCechCohomology_singleton_succ_of_adjunction_of_powerSections
    [Module.FaithfullyFlat R A] (adj : L ⊣ G) [G.Full] [G.Faithful]
    [PreservesLimitsOfSize.{0, 0} G] (a : CommAlgCat.{max uR uA} (ULift.{uA} R))
    (hpow : powerSections (G.obj (op a)) H ≅
      powerSections (G.obj (op a)) L.leftOp ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (G.obj (op a)) L.leftOp ≅ algebraMapArrow R A)
    (p : ℕ) :
    IsZero (sliceCechCohomology
      (PreZeroHypercover.singleton.{max uR uA uM} (G.obj (op a)).hom) H (p + 1)) :=
  isZero_sliceCechCohomology_singleton_succ_of_powerSections (G.obj (op a)).hom H L.leftOp
    hpow harrow (fun n => isIso_conerveSectionsMap_of_adjunction adj a n) p

end Adjunction

end Stacks.Descent

end
