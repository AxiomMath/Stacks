module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechIteratedSliceTransport
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit

/-!
# The condition of Tag 099E restricts to a slice

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals and `a : K ⟶ 𝒪` a map of complexes with
the property of [Stacks, Tag 099E] for `ℐ` —
`AlgebraicGeometry.RingedSite.IsGlobalExtendedCech`. This file proves that for every object `U`
the restriction `a|_U : K|_U ⟶ 𝒪_U` has the same property on the slice site `𝒞/U` for the
restricted sheaf of ideals `ℐ|_U`. Together with the identification of the derived completion
functor of [Stacks, Tag 099F] with `R𝑆heafHom_𝒪(K, -)` this is what makes the completion
functors on `𝒞` and on `𝒞/U` comparable, which is [Stacks, Tag 0A0F].

## Main results

* `AlgebraicGeometry.RingedSite.restrictRestrictTransportComplexIso`: transporting `(K|_U)|_W`
  from the iterated slice `(𝒞/U)/W` to `𝒞/W.left` gives `K|_{W.left}`.
* `AlgebraicGeometry.RingedSite.isGlobalExtendedCech_restrict`: **the condition of
  [Stacks, Tag 099E] restricts to slices.**

## Implementation notes

The proof is a diagram chase in `D(𝒪_{W.left})`, carried out on the images under the transport
of the objects it concerns and then pulled back along the equivalence the transport induces on
derived categories, `Stacks.Injectives.mapDerivedCategory_isEquivalence`. The chase is
`comp_eq_of_chase`, stated in one abstract category because the categories of sheaves of modules
on the slices involved have two spellings each, which a rewrite does not identify.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) (U : X.C)

section Transport

variable (W : Over U)

/-- Restricting to `U`, then to `W`, then transporting to `𝒞/W.left` is isomorphic to
restricting to `W.left`. -/
def restrictRestrictTransportIso :
    SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
        (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) W ⋙
          (Stacks.SheafOfModules.InternalHom.sliceModulesEquiv X U W).inverse) ≅
      SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.left :=
  Functor.isoWhiskerLeft
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
      (eqToIso (show SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) W ⋙
          (Stacks.SheafOfModules.InternalHom.sliceModulesEquiv X U W).inverse =
        SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.hom from rfl)) ≪≫
    SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.hom

/-- Restriction from `𝒞/U` to `(𝒞/U)/W` followed by the transport to `𝒞/W.left` is additive. -/
instance additive_overFunctor_comp_sliceTransport :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) W ⋙
      (Stacks.SheafOfModules.InternalHom.sliceModulesEquiv X U W).inverse).Additive where
  map_add := rfl

/-- The transport of sheaves of modules from `(𝒞/U)/W` to `𝒞/W.left` is additive. -/
instance additive_sliceModulesEquiv_inverse :
    ((Stacks.SheafOfModules.InternalHom.sliceModulesEquiv X U W).inverse).Additive where
  map_add := rfl

/-- `restrictRestrictTransportIso` on complexes: the transport of `(K|_U)|_W` is `K|_{W.left}`.
Built from `CategoryTheory.Functor.mapHomologicalComplexCompIso` rather than as an identity of
complexes, which does not elaborate within the default heartbeat budget. -/
def restrictRestrictTransportComplexIso (K : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((sliceTransport X U W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (restrictComplex X K U)) ≅
      restrictComplex X K W.left :=
  ((Functor.mapHomologicalComplexCompIso
      (F := SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) W)
      (G := (Stacks.SheafOfModules.InternalHom.sliceModulesEquiv X U W).inverse)
      (Iso.refl _) (ComplexShape.up ℤ)).app (restrictComplex X K U)) ≪≫
    (Functor.mapHomologicalComplexCompIso (restrictRestrictTransportIso X U W)
      (ComplexShape.up ℤ)).app K


/-- The transport of the twice-restricted map `(a|_U)|_W` to `𝒪` is the restriction
`a|_{W.left}`, under the identifications of the source with `K|_{W.left}` and of the target with
`𝒪_{W.left}[0]`. -/
theorem restrictRestrictTransport_structureSheafMap [HasWeakSheafify X.J CommRingCat.{u}]
    [HasWeakSheafify (X.over U).J CommRingCat.{u}]
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (a : K ⟶ structureSheafComplex X) :
    ((sliceTransport X U W).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (restrictStructureSheafMap (X.over U) W (restrictStructureSheafMap X U a)) ≫
        (structureSheafComplexTransportIso X U W).hom =
      (restrictRestrictTransportComplexIso X U W K).hom ≫ restrictStructureSheafMap X W.left a := by
  refine HomologicalComplex.to_single_hom_ext ?_
  ext T x
  rfl

end Transport

/-- A functor carries a triple composite to the triple composite of the images. -/
theorem map_comp_map_comp_map_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {A B C D : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} {r : A ⟶ D} (H : f ≫ g ≫ h = r) :
    G.map f ≫ G.map g ≫ G.map h = G.map r := by
  rw [← H, G.map_comp, G.map_comp]

/-- A functor carries a commutative square to a commutative square. -/
theorem map_comp_map_eq_map_comp_map {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {A B B' C : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {f' : A ⟶ B'} {g' : B' ⟶ C}
    (H : f ≫ g = f' ≫ g') : G.map f ≫ G.map g = G.map f' ≫ G.map g' := by
  rw [← G.map_comp, H, G.map_comp]

/-- Given isomorphisms and commutative squares as in the hypotheses, the composite of the chain
of isomorphisms `PC ≅ PL` with `PB` equals `PA`. -/
theorem comp_eq_of_chase {ℬ : Type*} [Category ℬ] {PC C₁ C₂ K₂ L₁ PL PO O₁ O₂ : ℬ}
    (φC : PC ≅ C₁) (qc : C₁ ≅ C₂) (e : C₂ ≅ K₂) (qk : K₂ ≅ L₁) (φL : PL ≅ L₁)
    {PB : PL ⟶ PO} {QB : L₁ ⟶ O₁} (φO : PO ≅ O₁) (hB : PB ≫ φO.hom = φL.hom ≫ QB)
    {PA : PC ⟶ PO} {QA : C₁ ⟶ O₁} (hA : PA ≫ φO.hom = φC.hom ≫ QA)
    {rA : K₂ ⟶ O₂} {augA : C₂ ⟶ O₂} (s : O₁ ≅ O₂)
    (hk : qk.hom ≫ QB ≫ s.hom = rA) (he : e.hom ≫ rA = augA)
    (hc : qc.hom ≫ augA = QA ≫ s.hom) :
    (φC ≪≫ qc ≪≫ e ≪≫ qk ≪≫ φL.symm).hom ≫ PB = PA := by
  rw [← cancel_mono φO.hom, hA]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hB, Iso.inv_hom_id_assoc]
  congr 1
  rw [← cancel_mono s.hom, ← hc, ← he, ← hk]
  simp only [Category.assoc]

attribute [local instance] additive_overFunctor in
/-- **The condition of [Stacks, Tag 099E] restricts to a slice.** If `a : K ⟶ 𝒪` has the property
of [Stacks, Tag 099E] for `ℐ`, then its restriction `a|_U : K|_U ⟶ 𝒪_U` has it for the restricted
sheaf of ideals `ℐ|_U` on the slice site `𝒞/U`. -/
theorem isGlobalExtendedCech_restrict [HasWeakSheafify X.J CommRingCat.{u}]
    [HasWeakSheafify (X.over U).J CommRingCat.{u}]
    {I : SheafOfModules.Submodule (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {a : K ⟶ structureSheafComplex X}
    (ha : IsGlobalExtendedCech X I K a) :
    IsGlobalExtendedCech (X.over U) (overIdeal I U) (restrictComplex X K U)
      (restrictStructureSheafMap X U a) := by
  intro W _ s g hg
  obtain ⟨e', he'⟩ := ha W.left s (fun i => globalSectionTransport X U W (g i))
    (idealOfGlobalSections_globalSectionTransport X U W I g hg)
  have hΨ : (sliceTransport X U W).mapDerivedCategory.IsEquivalence :=
    Stacks.Injectives.mapDerivedCategory_isEquivalence (sliceTransport X U W)
  let φ := (sliceTransport X U W).mapDerivedCategoryFactors
  let e₁ := φ.app (extendedAlternatingCech ((X.over U).over W) g) ≪≫
    DerivedCategory.Q.mapIso (extendedAlternatingCechTransportIso X U W g) ≪≫ e' ≪≫
    DerivedCategory.Q.mapIso (restrictRestrictTransportComplexIso X U W K).symm ≪≫
    (φ.app (((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (restrictComplex X K U))).symm
  refine ⟨(sliceTransport X U W).mapDerivedCategory.preimageIso e₁, ?_⟩
  apply (sliceTransport X U W).mapDerivedCategory.map_injective
  rw [Functor.map_comp]
  refine Eq.trans (congrArg (fun m => m ≫ _)
    (Functor.map_preimage (sliceTransport X U W).mapDerivedCategory e₁.hom)) ?_
  have hK := restrictRestrictTransport_structureSheafMap X U W a
  have hC := sliceTransport_map_cechAugmentation X U W g
  refine comp_eq_of_chase _ _ _ _ _ (φ.app (structureSheafComplex ((X.over U).over W)))
    (φ.hom.naturality _) (φ.hom.naturality _)
    (DerivedCategory.Q.mapIso (structureSheafComplexTransportIso X U W)) ?_ he' ?_
  · exact map_comp_map_comp_map_eq DerivedCategory.Q ((Iso.inv_comp_eq _).2 hK)
  · exact map_comp_map_eq_map_comp_map DerivedCategory.Q hC.symm

end AlgebraicGeometry.RingedSite

end
