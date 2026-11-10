module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedCategoryBTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.KernelColocalization

/-!
# Restricting a derived equivalence to the subcategories `D_{𝓟 ∩ 𝓛}` and to the quotients

Let `F : A₁ ⥤ A₂` be an exact functor of abelian categories, let `𝓛ᵢ` be weak Serre classes with
`F(𝓛₁) ⊆ 𝓛₂`, and let `𝓟ᵢ` be classes which `F` matches on `𝓛₁`: for `M` in `𝓛₁`, `M` lies in
`𝓟₁` exactly when `F(M)` lies in `𝓟₂`. Suppose that the functor
`G : D_{𝓛₁}(A₁) ⥤ D_{𝓛₂}(A₂)` induced by `F` is an equivalence. Then:

* the functor `D_{𝓟₁ ∩ 𝓛₁}(A₁) ⥤ D_{𝓟₂ ∩ 𝓛₂}(A₂)` induced by `F` is an equivalence;
* `G` matches the classes of morphisms with cone in `D_{𝓟ᵢ ∩ 𝓛ᵢ}(Aᵢ)`;
* hence `G` descends to an equivalence of the Verdier quotients
  `D_{𝓛₁}(A₁) / D_{𝓟₁ ∩ 𝓛₁}(A₁) ≌ D_{𝓛₂}(A₂) / D_{𝓟₂ ∩ 𝓛₂}(A₂)`.

This is the formal part of the last two assertions of **Stacks 07B8**, where `F = ε^*`, the
`𝓛ᵢ` are `LQCoh^fbc` on the étale and fppf sites and the `𝓟ᵢ` are the parasitic modules: the
source says that the verification that the equivalence `ε^*` induces an equivalence of the
subcategories of complexes with parasitic cohomology sheaves is omitted. Everything here is
stated for arbitrary `HasDerivedCategory` instances.

## Main results

* `DerivedCategory.KernelColocalization.isEquivalence_mapDerivedCategoryLift_inter`: the
  equivalence of the subcategories `D_{𝓟ᵢ ∩ 𝓛ᵢ}(Aᵢ)`.
* `DerivedCategory.KernelColocalization.quotientW_eq_inverseImage`: the matching of the inverted
  classes.
* `DerivedCategory.KernelColocalization.quotientEquivalenceOfExactFunctor`: the equivalence of
  the Verdier quotients.

## References

* [Stacks Project, Tag 07B8](https://stacks.math.columbia.edu/tag/07B8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w₁ w₂

namespace CategoryTheory.Localization

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂]
  (G : C₁ ⥤ C₂) [G.IsEquivalence] (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [W₂.RespectsIso] (hW : W₁ = W₂.inverseImage G)

include hW in
/-- **A localization functor precomposed with an equivalence.** If `G : C₁ ⥤ C₂` is an
equivalence and `W₁` is the inverse image under `G` of a class `W₂` of morphisms respecting
isomorphisms, then `G` followed by the localization functor of `W₂` is a localization functor
for `W₁`: it is the localization functor of `W₂` transported along the equivalence. -/
theorem isLocalization_comp_of_inverseImage : (G ⋙ W₂.Q).IsLocalization W₁ := by
  have hinv : W₁.IsInvertedBy (G ⋙ W₂.Q) := fun _ _ f hf ↦
    Localization.inverts W₂.Q W₂ (G.map f) (by rwa [hW] at hf)
  have hle : W₂ ≤ W₁.isoClosure.inverseImage G.asEquivalence.inverse := by
    intro X Y f hf
    refine W₁.le_isoClosure _ ?_
    rw [hW, MorphismProperty.inverseImage_iff]
    exact (W₂.arrow_mk_iso_iff (Arrow.isoMk (G.asEquivalence.counitIso.app X).symm
      (G.asEquivalence.counitIso.app Y).symm
      (G.asEquivalence.counitIso.inv.naturality f).symm)).mp hf
  have hiso : G.asEquivalence.symm.functor ⋙ (G ⋙ W₂.Q) ≅ W₂.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.asEquivalence.counitIso W₂.Q ≪≫ Functor.leftUnitor _
  exact Functor.IsLocalization.of_equivalence_source W₂.Q W₂ (G ⋙ W₂.Q) W₁
    G.asEquivalence.symm hle hinv hiso

/-- **Two localizations along an equivalence.** Under the hypotheses of
`isLocalization_comp_of_inverseImage`, the localizations of `C₁` at `W₁` and of `C₂` at `W₂` are
equivalent, two localization functors for one class being canonically equivalent. -/
def equivalenceOfEquivalenceOfInverseImage : W₁.Localization ≌ W₂.Localization :=
  haveI := isLocalization_comp_of_inverseImage G W₁ W₂ hW
  Localization.uniq W₁.Q (G ⋙ W₂.Q) W₁

/-- The equivalence of `equivalenceOfEquivalenceOfInverseImage` is induced by `G`. -/
def qCompEquivalenceOfEquivalenceOfInverseImageIso :
    W₁.Q ⋙ (equivalenceOfEquivalenceOfInverseImage G W₁ W₂ hW).functor ≅ G ⋙ W₂.Q :=
  haveI := isLocalization_comp_of_inverseImage G W₁ W₂ hW
  Localization.compUniqFunctor W₁.Q (G ⋙ W₂.Q) W₁

end CategoryTheory.Localization

namespace DerivedCategory.KernelColocalization

open DerivedCategoryB

variable {A₁ : Type*} [Category A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
  {A₂ : Type*} [Category A₂] [Abelian A₂] [HasDerivedCategory.{w₂} A₂]
  (F : A₁ ⥤ A₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (𝓟₁ 𝓛₁ : ObjectProperty A₁) (𝓟₂ 𝓛₂ : ObjectProperty A₂)
  [𝓛₂.IsClosedUnderIsomorphisms] [(𝓟₂ ⊓ 𝓛₂).IsClosedUnderIsomorphisms]
  (hF : ∀ M, 𝓛₁ M → 𝓛₂ (F.obj M)) (hP : ∀ M, 𝓛₁ M → (𝓟₁ M ↔ 𝓟₂ (F.obj M)))

omit [Abelian A₁] [HasDerivedCategory A₁] [Abelian A₂] [HasDerivedCategory A₂] [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [𝓛₂.IsClosedUnderIsomorphisms]
  [(𝓟₂ ⊓ 𝓛₂).IsClosedUnderIsomorphisms] in
include hF hP in
/-- `F` carries `𝓟₁ ∩ 𝓛₁` into `𝓟₂ ∩ 𝓛₂`. -/
theorem prop_inter_obj {M : A₁} (hM : (𝓟₁ ⊓ 𝓛₁) M) : (𝓟₂ ⊓ 𝓛₂) (F.obj M) :=
  ⟨(hP M hM.2).1 hM.1, hF M hM.2⟩

omit [𝓛₂.IsClosedUnderIsomorphisms] in
include hF hP in
/-- **`F` matches `D_{𝓟₁ ∩ 𝓛₁}(A₁)` with `D_{𝓟₂ ∩ 𝓛₂}(A₂)` on `D_{𝓛₁}(A₁)`**: a complex with
cohomology in `𝓛₁` has cohomology in `𝓟₁` exactly when its image has cohomology in `𝓟₂`, the
cohomology of the image being the image of the cohomology. -/
theorem derivedInter_mapDerivedCategory_obj_iff {K : DerivedCategory A₁}
    (hK : derivedCategoryB 𝓛₁ K) :
    derivedInter 𝓟₂ 𝓛₂ (F.mapDerivedCategory.obj K) ↔ derivedInter 𝓟₁ 𝓛₁ K := by
  refine ⟨fun h n ↦ ?_, fun h n ↦ ?_⟩
  · exact ⟨(hP _ (hK n)).2
      ((𝓟₂ ⊓ 𝓛₂).prop_of_iso ((F.mapDerivedCategoryHomologyIso n).app K) (h n)).1, hK n⟩
  · exact (𝓟₂ ⊓ 𝓛₂).prop_of_iso ((F.mapDerivedCategoryHomologyIso n).app K).symm
      (prop_inter_obj F 𝓟₁ 𝓛₁ 𝓟₂ 𝓛₂ hF hP (h n))

/-- The functor `D_{𝓟₁ ∩ 𝓛₁}(A₁) ⥤ D_{𝓟₂ ∩ 𝓛₂}(A₂)` induced by `F`. -/
abbrev mapDerivedCategoryLiftInter :
    (derivedInter 𝓟₁ 𝓛₁).FullSubcategory ⥤ (derivedInter 𝓟₂ 𝓛₂).FullSubcategory :=
  mapDerivedCategoryLift F (𝓟₁ ⊓ 𝓛₁) (𝓟₂ ⊓ 𝓛₂)
    (fun _ hM ↦ prop_inter_obj F 𝓟₁ 𝓛₁ 𝓟₂ 𝓛₂ hF hP hM)

include hP in
/-- **The equivalence `D_{𝓛₁}(A₁) ≌ D_{𝓛₂}(A₂)` restricts to `D_{𝓟₁ ∩ 𝓛₁}(A₁) ≌ D_{𝓟₂ ∩ 𝓛₂}(A₂)`.**
The restricted functor is fully faithful because it is, after the inclusions, the given
equivalence; an object of `D_{𝓟₂ ∩ 𝓛₂}(A₂)` is the image of an object of `D_{𝓛₁}(A₁)`, which
lies in `D_{𝓟₁ ∩ 𝓛₁}(A₁)` by `derivedInter_mapDerivedCategory_obj_iff`. -/
theorem isEquivalence_mapDerivedCategoryLift_inter
    [(mapDerivedCategoryLift F 𝓛₁ 𝓛₂ hF).IsEquivalence] :
    (mapDerivedCategoryLiftInter F 𝓟₁ 𝓛₁ 𝓟₂ 𝓛₂ hF hP).IsEquivalence := by
  let G := mapDerivedCategoryLift F 𝓛₁ 𝓛₂ hF
  let H := mapDerivedCategoryLiftInter F 𝓟₁ 𝓛₁ 𝓟₂ 𝓛₂ hF hP
  have h₁ : derivedInter 𝓟₁ 𝓛₁ ≤ derivedCategoryB 𝓛₁ := fun _ hK n ↦ (hK n).2
  have h₂ : derivedInter 𝓟₂ 𝓛₂ ≤ derivedCategoryB 𝓛₂ := fun _ hK n ↦ (hK n).2
  have hff : H.FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := (derivedInter 𝓟₂ 𝓛₂).ι)
      (((ObjectProperty.fullyFaithfulιOfLE h₁).comp
        (Functor.FullyFaithful.ofFullyFaithful G)).comp (derivedCategoryB 𝓛₂).fullyFaithfulι)
  have := hff.full
  have := hff.faithful
  have : H.EssSurj := by
    refine ⟨fun K' ↦ ?_⟩
    let K₀ := G.objPreimage ⟨K'.obj, h₂ _ K'.property⟩
    let e : G.obj K₀ ≅ ⟨K'.obj, h₂ _ K'.property⟩ := G.objObjPreimageIso _
    have hK₀ : derivedInter 𝓟₁ 𝓛₁ K₀.obj :=
      (derivedInter_mapDerivedCategory_obj_iff F 𝓟₁ 𝓛₁ 𝓟₂ 𝓛₂ hF hP K₀.property).1
        (fun n ↦ (𝓟₂ ⊓ 𝓛₂).prop_of_iso
          ((DerivedCategory.homologyFunctor A₂ n).mapIso
            ((derivedCategoryB 𝓛₂).ι.mapIso e).symm) (K'.property n))
    exact ⟨⟨K₀.obj, hK₀⟩, ⟨(derivedInter 𝓟₂ 𝓛₂).fullyFaithfulι.preimageIso
      ((derivedCategoryB 𝓛₂).ι.mapIso e)⟩⟩
  exact { }

variable [𝓛₁.IsWeakSerreClass] [(𝓟₁ ⊓ 𝓛₁).IsClosedUnderIsomorphisms]

omit [(𝓟₁ ⊓ 𝓛₁).IsClosedUnderIsomorphisms] in
include hP in
/-- **`F` matches the classes of morphisms inverted by the two Verdier quotients.** A morphism
of `D_{𝓛₁}(A₁)` has its cone in `D_{𝓟₁ ∩ 𝓛₁}(A₁)` exactly when its image has its cone in
`D_{𝓟₂ ∩ 𝓛₂}(A₂)`.

`F` acts on derived categories as a triangulated functor, so it carries a distinguished triangle
on a morphism to one on its image; conversely the cone of the image is the image of the cone, by
uniqueness of cones, and the cone lies in `D_{𝓛₁}(A₁)`, a triangulated subcategory, so that
`derivedInter_mapDerivedCategory_obj_iff` applies to it. -/
theorem quotientW_eq_inverseImage :
    quotientW 𝓟₁ 𝓛₁ =
      (quotientW 𝓟₂ 𝓛₂).inverseImage (mapDerivedCategoryLift F 𝓛₁ 𝓛₂ hF) := by
  ext X Y f
  change (derivedInter 𝓟₁ 𝓛₁).trW ((derivedCategoryB 𝓛₁).ι.map f) ↔
    (derivedInter 𝓟₂ 𝓛₂).trW (F.mapDerivedCategory.map ((derivedCategoryB 𝓛₁).ι.map f))
  constructor
  · rintro ⟨Z, g, h, hT, hZ⟩
    exact ObjectProperty.trW.mk _ (F.mapDerivedCategory.map_distinguished _ hT)
      ((derivedInter_mapDerivedCategory_obj_iff F 𝓟₁ 𝓛₁ 𝓟₂ 𝓛₂ hF hP (fun n ↦ (hZ n).2)).2 hZ)
  · rintro ⟨Z', g', h', hT', hZ'⟩
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle ((derivedCategoryB 𝓛₁).ι.map f)
    have hZ₁ : derivedCategoryB 𝓛₁ Z :=
      (derivedCategoryB 𝓛₁).ext_of_isTriangulatedClosed₃ _ hT X.property Y.property
    have e := isoTriangleOfIso₁₂ _ _ (F.mapDerivedCategory.map_distinguished _ hT) hT'
      (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans (Category.id_comp _).symm)
    have hFZ : derivedInter 𝓟₂ 𝓛₂ (F.mapDerivedCategory.obj Z) :=
      (derivedInter 𝓟₂ 𝓛₂).prop_of_iso (Triangle.π₃.mapIso e).symm hZ'
    exact ObjectProperty.trW.mk _ hT
      ((derivedInter_mapDerivedCategory_obj_iff F 𝓟₁ 𝓛₁ 𝓟₂ 𝓛₂ hF hP hZ₁).1 hFZ)

include hP in
/-- **The equivalence `D_{𝓛₁}(A₁) ≌ D_{𝓛₂}(A₂)` induced by `F` descends to the Verdier quotients**
`D_{𝓛₁}(A₁) / D_{𝓟₁ ∩ 𝓛₁}(A₁) ≌ D_{𝓛₂}(A₂) / D_{𝓟₂ ∩ 𝓛₂}(A₂)`, by
`CategoryTheory.Localization.equivalenceOfEquivalenceOfInverseImage` and
`quotientW_eq_inverseImage`. -/
def quotientEquivalenceOfExactFunctor [(mapDerivedCategoryLift F 𝓛₁ 𝓛₂ hF).IsEquivalence] :
    quotient 𝓟₁ 𝓛₁ ≌ quotient 𝓟₂ 𝓛₂ :=
  Localization.equivalenceOfEquivalenceOfInverseImage (mapDerivedCategoryLift F 𝓛₁ 𝓛₂ hF)
    (quotientW 𝓟₁ 𝓛₁) (quotientW 𝓟₂ 𝓛₂) (quotientW_eq_inverseImage F 𝓟₁ 𝓛₁ 𝓟₂ 𝓛₂ hF hP)

include hP in
/-- The equivalence of Verdier quotients is induced by `F`: the quotient functor of the source
followed by it is the functor induced by `F` followed by the quotient functor of the target. -/
def toQuotientCompQuotientEquivalenceOfExactFunctorIso
    [(mapDerivedCategoryLift F 𝓛₁ 𝓛₂ hF).IsEquivalence] :
    toQuotient 𝓟₁ 𝓛₁ ⋙ (quotientEquivalenceOfExactFunctor F 𝓟₁ 𝓛₁ 𝓟₂ 𝓛₂ hF hP).functor ≅
      mapDerivedCategoryLift F 𝓛₁ 𝓛₂ hF ⋙ toQuotient 𝓟₂ 𝓛₂ :=
  Localization.qCompEquivalenceOfEquivalenceOfInverseImageIso _ _ _ _

end DerivedCategory.KernelColocalization

end
