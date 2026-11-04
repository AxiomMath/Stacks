module

public import StacksFrontier.CategoryTheory.Functor.Bifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCertificate
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# The derived tensor product of a ringed space is a total left derived functor

Let `(X, 𝒪_X)` be a ringed space and let `ℱ` be an `𝒪_X`-module. The functor
`- ⊗^{L}_{𝒪_X} ℱ[0]` on `D(𝒪_X)` of Stacks 06YU is the total left derived functor of termwise
tensoring by `ℱ`, the counit being the canonical map from the derived tensor product to the
total tensor complex. Hence the genuine derived tensor product of Stacks 06YU is an inhabitant
of `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, the datum against which
Stacks 08CG is stated here, and the Tor-amplitude predicates that datum defines are the pinned
ones of `Stacks.Cohomology.TorAmplitude`.

This is the ringed-space analogue of `StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived`.

## Main definitions

* `CochainComplex.KFlatBifunctor.totalSingleNatIso`: termwise application of `F(-, M)` is, as a
  functor of the complex, the total complex of the double complex attached to it and to `M` in
  degree `0`.
* `Stacks.DerivedTensor.RingedSite.sheafTensorComparison`: the comparison of `- ⊗^{L}_{O} ℱ[0]`,
  read on complexes, with termwise tensoring by `ℱ`.
* `AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoring`: the derived tensor
  product of Stacks 06YU, packaged as a Stacks 08CG certificate.
* `AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`: the same
  certificate on every open subspace at once, which is the family part (3) of Stacks 08CG asks
  for.

## Main results

* `Stacks.DerivedTensor.RingedSite.isLeftDerivedFunctor_sheafTensorComparison`: **the universal
  property.** The comparison exhibits `- ⊗^{L}_{O} ℱ[0]` as the total left derived functor of
  `- ⊗_{O} ℱ`.
* `AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_canonicalCertificate_iff` and
  `AlgebraicGeometry.RingedSpace.hasFiniteTorDimension_canonicalCertificate_iff`: at this
  certificate the predicates of Stacks 08CG are the pinned ones of
  `Stacks.Cohomology.TorAmplitude`.

## Implementation notes

**No resolution of `ℱ` is needed.** On the module side the analogous certificate replaces `M` by
a projective resolution, because `M[0]` is K-flat only for a flat `M` and the structure's
comparison datum is an isomorphism only at K-flat arguments. Here the structure
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` carries, beyond those isomorphisms, the
canonical map `toTensor` for *arbitrary* complexes together with its naturality, and
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.toTensor_eq_comparisonLeft` says it is
invertible as soon as the *left* factor is K-flat. The left factor is the variable being
derived, so `toTensor` at the single complex `ℱ[0]` is already the counit, invertible exactly on
the resolving class.

**From the homotopy category to the category of complexes.** The K-flat complexes resolve every
complex only in the homotopy category, where the quasi-isomorphisms admit a right calculus of
fractions; so the universal property is first obtained along
`CategoryTheory.DerivedCategory.Qh` by
`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions`, and then
carried to `CategoryTheory.DerivedCategory.Q` by the fullness of precomposition with the
homotopy quotient on functor categories.

**The identification of the degree-zero total complex.**
`CochainComplex.KFlatBifunctor.totalSingleIso` already identifies `Tot(F(K, M[0]))` with the
termwise complex, but objectwise in `K` only, whereas the counit has to be a natural
transformation. `totalSingleNatIso` is therefore built
from the inclusion of the single nonzero summand, whose naturality is
`HomologicalComplex.ι_mapBifunctorMap`; its invertibility is the vanishing of the other
summands, as in `HomologicalComplex.mapBifunctorSingleRightXIso`.

**Everything before the last section is stated on a ringed site**, with the derived tensor
product a hypothesis, because the proof uses nothing about a ringed space: a statement proved at
`Stacks.Cohomology.TorAmplitude.derTensor` would force the elaborator to unfold that choice,
which exhausts the heartbeat budget on the first rewrite.

**The two spellings of the category of `𝒪_X`-modules.** `StrictlyPerfect.OXMod X` and
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf` are the same type by `rfl` but not
syntactically, so the ringed-site statements are made at the second and transported to the first
only at `canonicalCertifiedDerivedSheafTensoring`, where the bridge is a field assignment and no
tactic has to match across it. For the same reason the instances of Stacks 06YM are seated by
hand on a ringed space, as in the Tag 06YS development: their universe pattern `max u v` does
not unify with the ringed space's single `u` by instance search.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect AlgebraicGeometry

universe d u

/-! ### A bifunctor against a second factor in degree zero, naturally in the first -/

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [Preadditive D] [HasZeroObject B]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  (M : B)

/-- **The inclusion of the only possibly nonzero summand.** In degree `i` the total complex
`Tot(F(K, M[0]))` is a biproduct over the pairs `(a, b)` with `a + b = i`, and the summand at
`(i, 0)` is `F(K^i, M)`; this is the resulting map from the termwise complex `p ↦ F(K^p, M)`.

It is a morphism of complexes because the second factor has no differential, so the component of
the total differential in the second variable vanishes. -/
def totalSingleInclusion (K : CochainComplex A ℤ) :
    ((F.flip.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      HomologicalComplex.mapBifunctor K ((CochainComplex.singleFunctor B 0).obj M) F
        (ComplexShape.up ℤ) where
  f i := (F.obj (K.X i)).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
    HomologicalComplex.ιMapBifunctor K ((CochainComplex.singleFunctor B 0).obj M) F
      (ComplexShape.up ℤ) i 0 i (by simp)
  comm' i j hij := by
    dsimp
    rw [Category.assoc, HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hij 0 j (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq (i₂' := 1) _ _ _ _ i (by simp) j
        (by simpa using hij),
      CochainComplex.singleFunctor_obj_d]
    simp only [Functor.map_zero, zero_comp, smul_zero, add_zero]
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 from rfl,
      one_smul]
    exact (F.map (K.d i j)).naturality_assoc _ _

/-- **The summand at `(i, 0)` is the whole biproduct.** All the other summands of degree `i` of
`Tot(F(K, M[0]))` vanish, because `F(K^a, -)` kills the zero object. -/
lemma isIso_ιMapBifunctor_single_right (K : CochainComplex A ℤ) (i : ℤ) :
    IsIso (HomologicalComplex.ιMapBifunctor K ((CochainComplex.singleFunctor B 0).obj M) F
      (ComplexShape.up ℤ) i 0 i (by simp)) := by
  refine ⟨HomologicalComplex.mapBifunctorDesc (fun a b hab =>
    if h : b = 0 then by
      subst h
      obtain rfl : a = i := by simpa using hab
      exact 𝟙 _
    else 0), ?_, ?_⟩
  · simp
  · refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
    by_cases hb : b = 0
    · subst hb
      obtain rfl : a = i := by simpa using hab
      simp
    · exact ((F.obj (K.X a)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M b hb)).eq_of_src _ _

/-- The inclusion of the degree-zero summand is an isomorphism of complexes. -/
lemma isIso_totalSingleInclusion (K : CochainComplex A ℤ) :
    IsIso (totalSingleInclusion F M K) := by
  have (i : ℤ) : IsIso ((totalSingleInclusion F M K).f i) := by
    have := isIso_ιMapBifunctor_single_right F M K i
    dsimp [totalSingleInclusion]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The inclusion of the degree-zero summand is natural in the complex. -/
lemma totalSingleInclusion_naturality {K K' : CochainComplex A ℤ} (f : K ⟶ K') :
    ((F.flip.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫
        totalSingleInclusion F M K' =
      totalSingleInclusion F M K ≫
        HomologicalComplex.mapBifunctorMap f (𝟙 ((CochainComplex.singleFunctor B 0).obj M)) F
          (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simp only [HomologicalComplex.comp_f]
  dsimp [totalSingleInclusion]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((F.map (f.f i)).naturality_assoc _ _).symm

/-- **A second factor concentrated in degree zero makes the total complex the termwise one,
naturally in the first factor.** This is `CochainComplex.KFlatBifunctor.totalSingleIso` upgraded
to an isomorphism of functors of the first factor, and in the opposite direction. -/
def totalSingleNatIso :
    (F.flip.obj M).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj ((CochainComplex.singleFunctor B 0).obj M) :=
  NatIso.ofComponents
    (fun K => @asIso _ _ _ _ (totalSingleInclusion F M K) (isIso_totalSingleInclusion F M K))
    (fun {_ _} f => totalSingleInclusion_naturality F M f)

/-- Naturality of the inverse of `totalSingleNatIso`, with the induced map on total complexes
written as `HomologicalComplex.mapBifunctorMap`. -/
lemma totalSingleNatIso_inv_naturality {K K' : CochainComplex A ℤ} (f : K ⟶ K') :
    HomologicalComplex.mapBifunctorMap f (𝟙 ((CochainComplex.singleFunctor B 0).obj M)) F
        (ComplexShape.up ℤ) ≫ (totalSingleNatIso F M).inv.app K' =
      (totalSingleNatIso F M).inv.app K ≫
        ((F.flip.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).map f :=
  (totalSingleNatIso F M).inv.naturality f

end CochainComplex.KFlatBifunctor

namespace Stacks.DerivedTensor.RingedSite

/-! ### From the homotopy category to the category of complexes -/

section Transfer

open CategoryTheory.Functor CategoryTheory.LeftDerivedByResolutions

universe w

/-- Precomposition which is fully faithful on functor categories preserves the right Kan
universal property. -/
private lemma isRightKanExtension_precomp_of_fullyFaithful
    {C₀ C₁ D₀ H₀ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category H₀]
    (E : C₁ ⥤ C₀) [((whiskeringLeft C₁ C₀ H₀).obj E).Full]
    [((whiskeringLeft C₁ C₀ H₀).obj E).Faithful]
    (L : C₀ ⥤ D₀) (G₀ : C₀ ⥤ H₀) (G : D₀ ⥤ H₀) (α : L ⋙ G ⟶ G₀)
    [G.IsRightKanExtension α] :
    G.IsRightKanExtension ((Functor.associator E L G).hom ≫ whiskerLeft E α) := by
  have : (RightExtension.precomp L G₀ E).IsEquivalence := by
    dsimp only [RightExtension.precomp]
    infer_instance
  let h := (IsTerminal.isTerminalIffObj (RightExtension.precomp L G₀ E)
    (RightExtension.mk G α)).1 (G.isUniversalOfIsRightKanExtension α)
  exact ⟨⟨IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl G))⟩⟩

/-- **Stacks 06Y6 over an abstract abelian category.** A comparison on complexes which is
invertible on a class of complexes resolving every complex exhibits its functor on the derived
category as a total left derived functor, provided the underived functor descends to the
homotopy category. -/
private lemma isLeftDerivedFunctor_of_isIso_on_resolutions_Q
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : ObjectProperty (CochainComplex C ℤ))
    (hP : ∀ K : CochainComplex C ℤ, ∃ (L : CochainComplex C ℤ) (_ : P L) (s : L ⟶ K),
      QuasiIso s)
    {H : Type*} [Category H]
    (U : CochainComplex C ℤ ⥤ H)
    (Uh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H)
    (e : HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Uh ≅ U)
    (G : DerivedCategory C ⥤ H)
    (β : DerivedCategory.Q ⋙ G ⟶ U)
    (hβ : ∀ K : CochainComplex C ℤ, P K → IsIso (β.app K)) :
    G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
  let Qu := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let q := DerivedCategory.quotientCompQhIso C
  let T := (whiskeringLeft _ _ H).obj Qu
  have : T.Full := inferInstanceAs
    (((whiskeringLeft _ _ H).obj
      (CategoryTheory.Quotient.functor (_root_.homotopic C (ComplexShape.up ℤ)))).Full)
  let α₀ : Qu ⋙ (DerivedCategory.Qh ⋙ G) ⟶ Qu ⋙ Uh :=
    whiskerRight q.hom G ≫ β ≫ e.inv
  let α : DerivedCategory.Qh ⋙ G ⟶ Uh := T.preimage α₀
  have hα₀ : whiskerLeft Qu α = α₀ := T.map_preimage α₀
  have hres : ∀ X : HomotopyCategory C (ComplexShape.up ℤ),
      ∃ (Y : HomotopyCategory C (ComplexShape.up ℤ)) (_ : P Y.as) (s : Y ⟶ X),
        HomotopyCategory.quasiIso C (ComplexShape.up ℤ) s := by
    intro X
    obtain ⟨L, hL, s, hs⟩ := hP X.as
    exact ⟨Qu.obj L, hL, Qu.map s, (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hα : ∀ X : HomotopyCategory C (ComplexShape.up ℤ), P X.as → IsIso (α.app X) := by
    intro X hX
    rw [show α.app X = α₀.app X.as from NatTrans.congr_app hα₀ X.as]
    have h1 : IsIso (G.map (q.hom.app X.as)) := inferInstance
    have h2 : IsIso (e.inv.app X.as) := inferInstance
    dsimp [α₀]
    exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' (hβ X.as hX) h2)
  have hUh : ∀ {X Y} (s : X ⟶ Y), HomotopyCategory.quasiIso C (ComplexShape.up ℤ) s →
      P X.as → P Y.as → IsIso (Uh.map s) := by
    intro X Y s hs hX hY
    have := hα X hX
    have := hα Y hY
    have : IsIso (DerivedCategory.Qh.map s) := (DerivedCategory.isIso_Qh_map_iff s).2 hs
    rw [← isIso_comp_left_iff (α.app X), ← α.naturality s]
    dsimp only [Functor.comp_map]
    infer_instance
  have := isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (fun X => P X.as) hres Uh hUh DerivedCategory.Qh G α hα
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension G α
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  have hk := isRightKanExtension_precomp_of_fullyFaithful Qu DerivedCategory.Qh Uh G α
  have : G.IsRightKanExtension (whiskerRight q.hom G ≫ β) := by
    apply (Functor.isRightKanExtension_iff_of_iso₂
      ((Functor.associator Qu DerivedCategory.Qh G).hom ≫ whiskerLeft Qu α)
      (whiskerRight q.hom G ≫ β) e (Iso.refl G) ?_).mp hk
    rw [hα₀]
    ext X
    simp [α₀]
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  apply (Functor.isRightKanExtension_iff_postcomp₁ (𝟭 _)
    ((Qu ⋙ DerivedCategory.Qh).rightUnitor ≪≫ q) β).2
  apply Functor.isRightKanExtension_of_iso G.leftUnitor.symm
    (whiskerRight q.hom G ≫ β)
  ext X
  simp only [comp_obj, Iso.symm_hom, Iso.trans_hom, whiskerRight_comp, Category.assoc,
    NatTrans.comp_app, id_obj, whiskerLeft_app, leftUnitor_inv_app, associator_inv_app,
    whiskerRight_app, rightUnitor_hom_app, map_id, Category.id_comp]
  exact Category.id_comp _

end Transfer

/-! ### The universal property on a ringed site -/

section RingedSite

open Stacks.SheafOfModules.Tensor CochainComplex.KFlatBifunctor

universe uc

variable {Cs : Type uc} [SmallCategory.{uc} Cs] {J : GrothendieckTopology Cs}
  (R : Sheaf J CommRingCat.{uc})
  [HasSheafify J AddCommGrpCat.{uc}] [J.WEqualsLocallyBijective AddCommGrpCat.{uc}]
  [HasDerivedCategory.{d} (Modules R)]
  [(sheafTensor.{_, _, _, uc, uc} R).Additive]
  [∀ M, ((sheafTensor.{_, _, _, uc, uc} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor R) (ComplexShape.up ℤ)]

/-- Termwise tensoring by `ℱ`, read on the homotopy category and followed by the localization to
the derived category. -/
private def termwiseSheafTensorHomotopy (F : Modules R) :
    HomotopyCategory (Modules R) (ComplexShape.up ℤ) ⥤ DerivedCategory (Modules R) :=
  ((sheafTensor R).flip.obj F).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Termwise tensoring by `ℱ` read on the homotopy category, precomposed with the homotopy
quotient, is termwise tensoring on complexes followed by the localization. -/
private def quotientCompTermwiseSheafTensorIso (F : Modules R) :
    HomotopyCategory.quotient (Modules R) (ComplexShape.up ℤ) ⋙
        termwiseSheafTensorHomotopy R F ≅
      ((sheafTensor R).flip.obj F).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerRight
      (((sheafTensor R).flip.obj F).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft
      (((sheafTensor R).flip.obj F).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (Modules R))

variable (T : DerivedTensorProduct.{d, uc} R)

/-- The canonical map to the total tensor complex, followed by the identification of the total
tensor complex with `ℱ[0]` with termwise tensoring by `ℱ`, is natural in the complex. -/
lemma sheafTensorComparison_naturality (F : Modules R)
    {K K' : CochainComplex (Modules R) ℤ} (f : K ⟶ K') :
    (T.tensor.map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Modules R) 0).obj F)) ≫
        T.toTensor K' ((CochainComplex.singleFunctor (Modules R) 0).obj F) ≫
          DerivedCategory.Q.map ((totalSingleNatIso (sheafTensor R) F).inv.app K') =
      (T.toTensor K ((CochainComplex.singleFunctor (Modules R) 0).obj F) ≫
          DerivedCategory.Q.map ((totalSingleNatIso (sheafTensor R) F).inv.app K)) ≫
        DerivedCategory.Q.map
          ((((sheafTensor R).flip.obj F).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have h := T.toTensor_naturality f (𝟙 ((CochainComplex.singleFunctor (Modules R) 0).obj F))
  have hν := totalSingleNatIso_inv_naturality (sheafTensor R) F f
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  rw [h]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
    T.toTensor K ((CochainComplex.singleFunctor (Modules R) 0).obj F) ≫ z)
    (DerivedCategory.Q.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg (fun z =>
    T.toTensor K ((CochainComplex.singleFunctor (Modules R) 0).obj F) ≫
      DerivedCategory.Q.map z) hν) ?_
  exact congrArg (fun z =>
    T.toTensor K ((CochainComplex.singleFunctor (Modules R) 0).obj F) ≫ z)
    (DerivedCategory.Q.map_comp _ _)

/-- **The comparison map of Stacks 06YU at an `O`-module in degree zero.** The natural
transformation from `- ⊗^{L}_{O} ℱ[0]`, read on complexes through the localization, to termwise
tensoring by `ℱ` followed by the localization: the canonical map to the total tensor complex,
followed by the identification of `Tot(K ⊗_{O} ℱ[0])` with the termwise complex. -/
def sheafTensorComparison (F : Modules R) :
    DerivedCategory.Q ⋙ T.tensor.flip.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Modules R) 0).obj F)) ⟶
      ((sheafTensor R).flip.obj F).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q where
  app K := T.toTensor K ((CochainComplex.singleFunctor (Modules R) 0).obj F) ≫
    DerivedCategory.Q.map ((totalSingleNatIso (sheafTensor R) F).inv.app K)
  naturality _ _ f := sheafTensorComparison_naturality R T F f

/-- **The universal property of Stacks 06YU.** Tensoring with `ℱ[0]` in a derived tensor product
of `O`-modules is the total left derived functor of termwise tensoring by `ℱ`, with counit
`sheafTensorComparison`.

The counit is invertible at a K-flat complex, because a K-flat left factor computes the derived
tensor product, and the K-flat complexes resolve every complex by Stacks 06YS; so Stacks 06Y6
identifies it with the total left derived functor. -/
theorem isLeftDerivedFunctor_sheafTensorComparison (F : Modules R) :
    (T.tensor.flip.obj
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Modules R) 0).obj F))).IsLeftDerivedFunctor
      (sheafTensorComparison R T F)
      (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ)) :=
  isLeftDerivedFunctor_of_isIso_on_resolutions_Q
    (fun K => Stacks.SheafOfModules.KFlat.KFlat R K)
    (fun K => by
      obtain ⟨P, p, hP, hp⟩ := exists_kFlat_quasiIso R K
      exact ⟨P, hP, p, hp⟩)
    _ (termwiseSheafTensorHomotopy R F) (quotientCompTermwiseSheafTensorIso R F) _
    (sheafTensorComparison R T F)
    (fun K hK => by
      have h1 : IsIso (T.toTensor K ((CochainComplex.singleFunctor (Modules R) 0).obj F)) := by
        rw [T.toTensor_eq_comparisonLeft K _ hK]
        infer_instance
      have h2 : IsIso (DerivedCategory.Q.map
        ((totalSingleNatIso (sheafTensor R) F).inv.app K)) := inferInstance
      exact IsIso.comp_isIso' h1 h2)

end RingedSite

end Stacks.DerivedTensor.RingedSite

/-! ### The canonical Stacks 08CG certificate on a ringed space -/

namespace AlgebraicGeometry.RingedSpace

open Stacks.Cohomology.TorAmplitude Stacks.SheafOfModules.Tensor
open Stacks.DerivedTensor.RingedSite

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- `HasDerivedCategory` at the spelling the Tag 06YU development is stated at. The type is
`OXMod X` by `rfl`, but an instance proved at one spelling does not fire at the other. -/
local instance hasDerivedCategoryModules : HasDerivedCategory.{d} (Modules X.sheaf) :=
  inferInstanceAs (HasDerivedCategory.{d} (OXMod.{u, u} X))

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-- The total complexes `Tot(K₁ ⊗_{𝒪_X} K₂)` exist. -/
local instance hasMapBifunctorSheafTensor :
    ∀ K₁ K₂ : CochainComplex (Modules X.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.sheaf) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor
    (J := Opens.grothendieckTopology X.carrier) X.sheaf

/-- **The derived tensor product of Stacks 06YU is a Stacks 08CG certificate.** Its underived
half is the tensor product `- ⊗_{𝒪_X} -` of `𝒪_X`-modules and its derived half is the derived
tensor product `Stacks.Cohomology.TorAmplitude.derTensor` of a ringed space, certified as the
total left derived functor of the first by
`Stacks.DerivedTensor.RingedSite.isLeftDerivedFunctor_sheafTensorComparison`.

So the hypothesis bundle of `AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` has the
genuine derived tensor product as an inhabitant, and not only the degenerate
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection`. -/
def canonicalCertifiedDerivedSheafTensoring :
    CertifiedDerivedSheafTensoring.{d, u} X where
  tensor := sheafTensor X.sheaf
  additive F := Functor.flip_obj_additive (sheafTensor X.sheaf) F
  derivedTensor := (derTensor X).tensor
  comparison F := sheafTensorComparison X.sheaf (derTensor X) F
  isLeftDerived F := isLeftDerivedFunctor_sheafTensorComparison X.sheaf (derTensor X) F

/-- **At the canonical certificate, Tor amplitude is the pinned Tor amplitude.** The two
predicates are the same vanishing condition on the same derived tensor product. -/
theorem hasTorAmplitudeIn_canonicalCertificate_iff
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    (canonicalCertifiedDerivedSheafTensoring X).HasTorAmplitudeIn E a b ↔
      HasTorAmplitude X E a b :=
  Iff.rfl

/-- **At the canonical certificate, finite Tor dimension is the pinned finite Tor dimension.** -/
theorem hasFiniteTorDimension_canonicalCertificate_iff
    (E : DerivedCategory (OXMod.{u, u} X)) :
    (canonicalCertifiedDerivedSheafTensoring X).HasFiniteTorDimension E ↔
      HasFiniteTorDimension X E :=
  Iff.rfl

/-- **At the canonical certificate, the Tor dimension of a module is the pinned one.** This is
the last sentence of Stacks 08CG: both sides ask Tor amplitude in `[-n, 0]` of `ℱ[0]`, against
the same derived tensor product. -/
theorem hasTorDimensionLE_canonicalCertificate_iff
    (F : OXMod.{u, u} X) (n : ℤ) :
    (canonicalCertifiedDerivedSheafTensoring X).HasTorDimensionLE F n ↔
      HasTorDimensionLE X F n :=
  Iff.rfl

/-- **The canonical certificate on every open subspace at once.** This is the family of derived
tensor products that part (3) of Stacks 08CG asks for, so
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` can be read at the genuine derived
tensor product of each open subspace. -/
def canonicalCertifiedDerivedSheafTensoringFamily (Y : RingedSpace.{u, u})
    [∀ U : Opens Y.carrier,
      HasDerivedCategory.{d} (OXMod.{u, u} (Y.restrict U.isOpenEmbedding))] :
    ∀ U : Opens Y.carrier,
      CertifiedDerivedSheafTensoring.{d, u} (Y.restrict U.isOpenEmbedding) :=
  fun U => canonicalCertifiedDerivedSheafTensoring (Y.restrict U.isOpenEmbedding)

end AlgebraicGeometry.RingedSpace

end
