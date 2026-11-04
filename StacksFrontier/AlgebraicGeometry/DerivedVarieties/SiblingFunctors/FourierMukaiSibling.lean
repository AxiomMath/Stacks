module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.CoherentRestriction
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Criterion
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.SingleKernel
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentKernels.Equivalence
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksCore.Tactic.StacksAttribute

/-!
# An exact functor of `D^b_Coh` preserving coherent modules has a Fourier-Mukai sibling

Let `k` be a field, let `X` and `Y` be schemes of finite type over `k` with `X` separated, and let
`F : D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` be a `k`-linear exact functor carrying
`Coh(𝒪_X) ⊂ D^b_Coh(𝒪_X)` into `Coh(𝒪_Y) ⊂ D^b_Coh(𝒪_Y)`. Then there is a Fourier-Mukai functor
`F' : D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` whose kernel is a coherent `𝒪_{X ×_k Y}`-module `𝒦`, flat
over `X` and with support finite over `Y`, which is a sibling of `F`.

## Main definitions

* `AlgebraicGeometry.fourierMukaiOfKernel`: the Fourier-Mukai functor
  `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` of a kernel of [Stacks, Tag 0FZN].
* `AlgebraicGeometry.fourierMukaiOfKernelCoherentIso`: on coherent modules, this functor is the
  integral transform of the kernel.

## Main results

* `AlgebraicGeometry.derivedCategoryBBounded_fourierMukai_single`: the Fourier-Mukai functor of
  a kernel of [Stacks, Tag 0FZN] preserves `D^b_Coh`.
* `AlgebraicGeometry.areSiblingsCoherent_fourierMukaiOfKernel`: if the integral transform of
  such a kernel restricts to the restriction of `F` to `Coh(𝒪_X)`, its Fourier-Mukai functor is a
  sibling of `F`.
* `AlgebraicGeometry.exists_fourierMukai_areSiblingsCoherent`: every such `F` has a Fourier-Mukai
  sibling whose kernel is a coherent module flat over `X` with support finite over `Y`.

## References

* [Stacks Project, Tag 0G00](https://stacks.math.columbia.edu/tag/0G00)
* [Stacks Project, Tag 0FZN](https://stacks.math.columbia.edu/tag/0FZN)
* [Stacks Project, Tag 0FYU](https://stacks.math.columbia.edu/tag/0FYU)
* [Stacks Project, Tag 0FZU](https://stacks.math.columbia.edu/tag/0FZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.CoherentKernels RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

-- Two abelian structures on `Coh(𝒪_X)` are in scope; `D^b_Coh` and the sibling relation are
-- stated with the one of `AlgebraicGeometry.CoherentAbelian`, so it is the one selected here.
attribute [local instance 100000] CoherentAbelian.coherentModulesAbelian

/-- `D^b_Coh(𝒪_Z)` is a triangulated subcategory of `D(𝒪_Z)`. -/
lemma isTriangulated_derivedCategoryBBounded_coherentInModules (Z : Scheme.{u}) :
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Z)).IsTriangulated :=
  DerivedCategoryB.isTriangulated_derivedCategoryBBounded _

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] in
/-- A coherent module on `X ×_k Y`, placed in degree zero, is an object of `D^b_Coh`. -/
lemma derivedCategoryBBounded_singleFunctor_coherent (K : (pullback X.hom Y.hom).Modules)
    (hK : K.IsCoherent) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun F : (pullback X.hom Y.hom).Modules => F.IsCoherent)
      ((DerivedCategory.singleFunctor _ 0).obj K) := by
  refine ⟨⟨⟨0, fun n hn => DerivedCategory.isZero_of_isGE _ 0 n hn⟩,
    ⟨0, fun n hn => DerivedCategory.isZero_of_isLE _ 0 n hn⟩⟩, fun n => ?_⟩
  obtain rfl | hn := eq_or_ne n 0
  · have : ((𝟭 (pullback X.hom Y.hom).Modules).obj K).IsCoherent := hK
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app K)
  · exact ProperCoherentFiniteType.isCoherent_of_isZero <| (lt_or_gt_of_ne hn).elim
      (fun h => DerivedCategory.isZero_of_isGE _ 0 n h)
      (fun h => DerivedCategory.isZero_of_isLE _ 0 n h)

/-- The Fourier-Mukai functor of a kernel of [Stacks, Tag 0FZN] carries `D^b_Coh(𝒪_X)` into
`D^b_Coh(𝒪_Y)`. -/
lemma derivedCategoryBBounded_fourierMukai_single
    (K : (finiteFlatCoherentKernel k X Y).FullSubcategory)
    (M : DerivedCategory X.left.Modules)
    (hM : DerivedCategoryB.derivedCategoryBBounded (fun F : X.left.Modules => F.IsCoherent) M) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : Y.left.Modules => N.IsCoherent)
      ((fourierMukai X.hom Y.hom ((DerivedCategory.singleFunctor _ 0).obj K.obj.obj)).obj M) := by
  obtain ⟨hc, hflat, hfin⟩ := K.property
  have : K.obj.obj.IsQuasicoherent := K.obj.property
  have : K.obj.obj.IsFiniteType := hc.isFiniteType
  let I := Scheme.Modules.schemeTheoreticSupport K.obj.obj
  have hI : IsFinite (I.subschemeι ≫ pullback.snd X.hom Y.hom) := hfin
  have hZ : IsProperOver (pullback.snd X.hom Y.hom) I.support :=
    (isProperOver_iff_exists_isProper _ I.support).2 ⟨I, rfl, inferInstance⟩
  let C := (CochainComplex.singleFunctor (pullback X.hom Y.hom).Modules 0).obj K.obj.obj
  have hC0 : ∀ i ≠ 0, IsZero (C.X i) := HomologicalComplex.isZero_single_obj_X _ 0 _
  have hC : ∀ i, SheafOfModules.supp (C.X i) ⊆
      (I.support : Set _) ∧ (C.X i).IsCoherent := by
    intro i
    obtain rfl | hi := eq_or_ne i 0
    · have := hc
      let e : C.X 0 ≅ K.obj.obj := HomologicalComplex.singleObjXSelf _ 0 _
      exact ⟨((SheafOfModules.supp_eq_of_iso e).trans
        (Scheme.Modules.supp_eq_support_schemeTheoreticSupport K.obj.obj)).le,
        Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e⟩
    · exact ⟨(Stacks.AlgebraicGeometry.ConfinedDevissage.supp_eq_empty_of_isZero _
        (hC0 i hi)).trans_subset (Set.empty_subset _),
        ProperCoherentFiniteType.isCoherent_of_isZero (hC0 i hi)⟩
  exact (fourierMukai_derivedCategoryBBounded X.hom Y.hom _
    (derivedCategoryBBounded_singleFunctor_coherent k X Y K.obj.obj hc)).1
    (Or.inr (Or.inl ⟨C, ⟨0, 0,
      (CochainComplex.isStrictlyGE_iff C 0).2 fun i hi => hC0 i (by omega),
      (CochainComplex.isStrictlyLE_iff C 0).2 fun i hi => hC0 i (by omega)⟩, fun i => (hC i).2,
      isFlatOver_single_X X.hom Y.hom K.obj.obj hflat, ⟨I.support, hZ, fun i => (hC i).1⟩,
      ⟨((DerivedCategory.singleFunctorIsoCompQ _ 0).app K.obj.obj).symm⟩⟩)) M hM

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] in
/-- The first projection `X ×_k Y ⟶ X` is flat, `Y ⟶ Spec k` being flat over a field. -/
lemma isFlat_fourierMukaiFst_over_field :
    AlgebraicGeometry.IsFlat (fourierMukaiFst X.hom Y.hom) :=
  fun x => Flat.stalkMap (pullback.fst X.hom Y.hom) x

/-- The Fourier-Mukai functor `Φ_𝒦 : D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` of a kernel of
[Stacks, Tag 0FZN]. -/
abbrev fourierMukaiOfKernel (K : (finiteFlatCoherentKernel k X Y).FullSubcategory) :
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X.left)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y.left)).FullSubcategory :=
  fourierMukaiOn X.hom Y.hom ((DerivedCategory.singleFunctor _ 0).obj K.obj.obj) _ _
    (fun M => derivedCategoryBBounded_fourierMukai_single k X Y K M.obj M.property)

/-- The Fourier-Mukai functor of a kernel of [Stacks, Tag 0FZN] commutes with the shift. -/
instance (K : (finiteFlatCoherentKernel k X Y).FullSubcategory) :
    (fourierMukaiOfKernel k X Y K).CommShift ℤ :=
  @commShift_fourierMukaiOn _ _ _ X.hom Y.hom _ _ _
    (isTriangulated_derivedCategoryBBounded_coherentInModules X.left)
    (isTriangulated_derivedCategoryBBounded_coherentInModules Y.left) _

/-- The Fourier-Mukai functor of a kernel of [Stacks, Tag 0FZN] is exact. -/
instance (K : (finiteFlatCoherentKernel k X Y).FullSubcategory) :
    (fourierMukaiOfKernel k X Y K).IsTriangulated :=
  @isTriangulated_fourierMukaiOn _ _ _ X.hom Y.hom _ _ _
    (isTriangulated_derivedCategoryBBounded_coherentInModules X.left)
    (isTriangulated_derivedCategoryBBounded_coherentInModules Y.left) _

/-- **On coherent modules the Fourier-Mukai functor of a kernel of [Stacks, Tag 0FZN] is its
integral transform**: `Φ_𝒦(ℱ[0]) ≅ pr_{2,*}(pr_1^*ℱ ⊗ 𝒦)[0]`, naturally in the coherent module
`ℱ`, as objects of `D(𝒪_Y)`. -/
def fourierMukaiOfKernelCoherentIso [IsSeparated X.hom]
    (K : (finiteFlatCoherentKernel k X Y).FullSubcategory) :
    letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    letI := quasiSeparatedSpace_left k X
    boundedCoherentSingleFunctor X.left ⋙ fourierMukaiOfKernel k X Y K ⋙
        (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y.left)).ι ≅
      coherentToQuasicoherent X.left ⋙ quasicoherentIntegralTransform k X Y K.obj ⋙
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι ⋙
          DerivedCategory.singleFunctor _ 0 :=
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let := quasiSeparatedSpace_left k X
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let E := coherentToQuasicoherent X.left ⋙
    (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι
  let bridge : modulePullback (fourierMukaiFst X.hom Y.hom) ⋙
      fourierMukaiModuleTensor X.hom Y.hom K.obj.obj ≅
      Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨(pullback X.hom Y.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
              (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
          (K.obj.obj)) :=
    Functor.isoWhiskerLeft _ (fourierMukaiModuleTensorIso X.hom Y.hom K.obj.obj ≪≫
      ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight _ _ (K.obj.obj))).symm)
  have hvan := integralTransformExactKernel_of_finiteFlatCoherentKernel k X Y K.obj K.property
  have hE : ∀ (c : SheafOfModules.CoherentModules X.left.ringCatSheaf) (n : ℕ), 0 < n →
      IsZero (((modulePushforward (pullback.snd X.hom Y.hom).toLRSHom.toShHom).rightDerived n).obj
        ((fourierMukaiModuleTensor X.hom Y.hom K.obj.obj).obj
          ((modulePullback (fourierMukaiFst X.hom Y.hom)).obj (E.obj c)))) := fun c n hn =>
    (hvan.2 ((coherentToQuasicoherent X.left).obj c) n hn).of_iso
      (((modulePushforward (pullback.snd X.hom Y.hom).toLRSHom.toShHom).rightDerived n).mapIso
        (bridge.app (E.obj c)))
  Functor.isoWhiskerLeft _ (ObjectProperty.liftCompιIso _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedCoherentSingleFunctorCompιIso X.left) _ ≪≫
    Functor.associator _ _ _ ≪≫
    fourierMukaiSingleIso X.hom Y.hom K.obj.obj (isFlat_fourierMukaiFst_over_field k X Y)
      K.property.2.1 E hE ≪≫
    Functor.isoWhiskerLeft E (Functor.isoWhiskerRight bridge
      (modulePushforward (pullback.snd X.hom Y.hom).toLRSHom.toShHom ⋙
        DerivedCategory.singleFunctor _ 0)) ≪≫
    Functor.isoWhiskerLeft (coherentToQuasicoherent X.left)
      (Functor.isoWhiskerRight (quasicoherentIntegralTransformData k X Y K.obj).comparison.symm
        (DerivedCategory.singleFunctor _ 0))

section Siblings

variable [IsSeparated X.hom]
  (F : (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X.left)).FullSubcategory ⥤
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y.left)).FullSubcategory)
  [F.CommShift ℤ] [F.IsTriangulated]
  (hF : ∀ A, (boundedCoherentSingleFunctor Y.left).essImage
    (F.obj ((boundedCoherentSingleFunctor X.left).obj A)))

/-- If the integral transform of a kernel `𝒦` of [Stacks, Tag 0FZN] restricts on `Coh(𝒪_X)` to
the restriction of `F`, then the Fourier-Mukai functor of `𝒦` is a sibling of `F`. -/
theorem areSiblingsCoherent_fourierMukaiOfKernel
    (K : (finiteFlatCoherentKernel k X Y).FullSubcategory)
    (e : letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
      letI := quasiSeparatedSpace_left k X
      letI := isNoetherian_of_locallyOfFiniteType X.hom
      letI := isNoetherian_of_locallyOfFiniteType Y.hom
      coherentToQuasicoherent X.left ⋙ quasicoherentIntegralTransform k X Y K.obj ≅
        coherentRestrictionOfBoundedCoherent F hF ⋙ coherentToQuasicoherent Y.left) :
    AreSiblingsCoherent F (fourierMukaiOfKernel k X Y K) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let := quasiSeparatedSpace_left k X
  let := isNoetherian_of_locallyOfFiniteType X.hom
  let := isNoetherian_of_locallyOfFiniteType Y.hom
  let H := coherentRestrictionOfBoundedCoherent F hF
  let ιY := (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y.left)).ι
  let iso₁ : boundedCoherentSingleFunctor X.left ⋙ F ≅ H ⋙ boundedCoherentSingleFunctor Y.left :=
    (coherentRestrictionOfBoundedCoherentIso F hF).symm
  let iso₂' : (boundedCoherentSingleFunctor X.left ⋙ fourierMukaiOfKernel k X Y K) ⋙ ιY ≅
      (H ⋙ boundedCoherentSingleFunctor Y.left) ⋙ ιY :=
    Functor.associator _ _ _ ≪≫ fourierMukaiOfKernelCoherentIso k X Y K ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H (boundedCoherentSingleFunctorCompιIso Y.left).symm ≪≫
      (Functor.associator _ _ _).symm
  let iso₂ : boundedCoherentSingleFunctor X.left ⋙ fourierMukaiOfKernel k X Y K ≅
      H ⋙ boundedCoherentSingleFunctor Y.left :=
    ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso iso₂'
  refine areSiblings_of_restrictionIso_of_negative_ext _ _
    ⟨(iso₁ ≪≫ iso₂.symm : boundedSingleFunctor _ ⋙ (coherentToModulesDerivedBounded X.left ⋙ F) ≅
      boundedSingleFunctor _ ⋙
        (coherentToModulesDerivedBounded X.left ⋙ fourierMukaiOfKernel k X Y K))⟩ ?_
  intro A B q hq
  have := subsingleton_hom_boundedCoherentSingle_shift Y.left (H.obj A) (H.obj B) q hq
  exact @Equiv.subsingleton _ _
    (Iso.homCongr (iso₁.app A) ((shiftFunctor _ q).mapIso (iso₁.app B))) this

end Siblings

/-- Let `k` be a field, let `X` and `Y` be schemes of finite type over `k` with `X` separated, and
let `F : D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` be a `k`-linear exact functor sending
`Coh(𝒪_X) ⊂ D^b_Coh(𝒪_X)` into `Coh(𝒪_Y) ⊂ D^b_Coh(𝒪_Y)`. Then there exists a Fourier-Mukai
functor `F' : D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` whose kernel is a coherent `𝒪_{X ×_k Y}`-module `𝒦`
flat over `X` and with support finite over `Y` which is a sibling of `F`.

Finite type over `k` is `LocallyOfFiniteType` together with `QuasiCompact`; `X ×_k Y` is the
fibre product over `Spec k`. The kernel `𝒦` is an object of
`AlgebraicGeometry.CoherentKernels.finiteFlatCoherentKernel` — coherent, flat over `X`, with
scheme-theoretic support finite over `Y` — and `F'` is the functor induced on `D^b_Coh` by the
Fourier-Mukai functor `Φ_𝒦` of the complex `𝒦[0]`, which preserves `D^b_Coh`
(`fourierMukaiOfKernel`). That `F` sends coherent modules to coherent modules is the statement
that the image under `F` of a coherent module placed in degree zero is isomorphic to a coherent
module placed in degree zero; `k`-linearity is with respect to the `k`-linear structures induced
by the structure morphisms. -/
@[stacks 0G00 "a k-linear exact functor of D^b_Coh sending Coh into Coh has a sibling which is \
the Fourier-Mukai functor of a coherent kernel flat over X with support finite over Y"]
theorem exists_fourierMukai_areSiblingsCoherent [IsSeparated X.hom]
    (F : (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X.left)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y.left)).FullSubcategory)
    [F.CommShift ℤ] [F.IsTriangulated]
    (hlin : letI : Linear k (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear k X
      letI : Linear k (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear k Y
      F.Linear k)
    (hF : ∀ A, (boundedCoherentSingleFunctor Y.left).essImage
      (F.obj ((boundedCoherentSingleFunctor X.left).obj A))) :
    ∃ K : (finiteFlatCoherentKernel k X Y).FullSubcategory,
      AreSiblingsCoherent F (fourierMukaiOfKernel k X Y K) := by
  let := isNoetherian_of_locallyOfFiniteType X.hom
  let := isNoetherian_of_locallyOfFiniteType Y.hom
  let : Linear k (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear k X
  let : Linear k (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear k Y
  obtain ⟨K, ⟨e⟩⟩ := exists_finiteFlatCoherentKernel_iso k X Y
    ⟨coherentRestrictionOfBoundedCoherent F hF, linear_coherentRestrictionOfBoundedCoherent F hF k,
      exactFunctor_coherentRestrictionOfBoundedCoherent F hF⟩
  exact ⟨K, areSiblingsCoherent_fourierMukaiOfKernel k X Y F hF K e⟩

end AlgebraicGeometry

end
