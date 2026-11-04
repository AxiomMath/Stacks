module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFinitePresentationOnSite
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.MixedTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# Finite presentation of the tensor product of modules with sections in independent universes

The tensor product of two sheaves of modules of finite presentation on a ringed site is of finite
presentation, in the sense of `SheafOfModules.IsFinitePresentationOnSite` (Stacks 03DL(7)), also
when the universe of the coefficient rings does not contain the site.  On a category fibred in
groupoids over the big fppf category of schemes over a base, whose objects lie one universe above
its structure sheaf, this is the finite presentation clause of Stacks 03L6 for the tensor product
of `𝒪_𝒳`-modules, and it makes coherence of modules on an algebraic stack (Stacks 0GR6) stable
under the tensor product.

## Main results

* `SheafOfModules.HasFiniteGlobalPresentation.of_uliftForPresentation`,
  `SheafOfModules.IsFinitePresentationOnSite.of_uliftForPresentation`,
  `SheafOfModules.hasFiniteGlobalPresentation_uliftForPresentation'` and
  `SheafOfModules.isFinitePresentationOnSite_uliftForPresentation'`: a finite global presentation,
  and finite presentation, are unchanged by raising the universe of the sections.
* `Stacks.Modules.hasFiniteGlobalPresentation_sheafRingULiftDown`,
  `Stacks.Modules.hasFiniteGlobalPresentation_sheafRingULiftUp`,
  `Stacks.Modules.isFinitePresentationOnSite_sheafRingULiftDown` and
  `Stacks.Modules.isFinitePresentationOnSite_sheafRingULiftUp`: the same for raising the universe
  of the coefficient rings.
* `Stacks.Modules.isFinitePresentationOnSite_sheafificationTensorObjUlift`: the statement with the
  sections of the two factors in independent universes and no size hypothesis.
* `AlgebraicGeometry.FibredSite.isFinitePresentationOnSite_tensorSheafMixed` and
  `AlgebraicGeometry.FibredSite.isFinitePresentationOnSite_tensorSheaf`: **the tensor product of
  two modules of finite presentation on an associated site of a category fibred in groupoids is
  of finite presentation.**
* `AlgebraicGeometry.Stack.isCoherent_tensorSheaf`: **the tensor product of two coherent modules on
  an algebraic stack is coherent.**

## Implementation notes

The statements on the fibred site assume the fibred category essentially small, which makes
sheafification available there; for an algebraic stack this is the instance
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r z m n t so sm

/-- A finite presentation (a cokernel of a map between finite coproducts of `E`) is carried to
`D'` by a functor preserving finite colimits, given isomorphisms identifying the images of the
summand and of the presented object. -/
private theorem exists_finite_presentation_of_map {D D' : Type*} [Category D] [Category D']
    [HasZeroMorphisms D] [HasZeroMorphisms D'] (Φ : D ⥤ D') [Φ.PreservesZeroMorphisms]
    [PreservesFiniteColimits Φ] {E' M' : D'} {E₀ M₀ : D}
    (h : ∃ (n k : ℕ) (P Q : D) (ι : Fin n → (E₀ ⟶ P)) (κ : Fin k → (E₀ ⟶ Q)),
      Nonempty (IsColimit (Cofan.mk P ι)) ∧ Nonempty (IsColimit (Cofan.mk Q κ)) ∧
        ∃ (a : Q ⟶ P) (b : P ⟶ M₀) (hab : a ≫ b = 0),
          Nonempty (IsColimit (CokernelCofork.ofπ b hab)))
    (γ : Φ.obj E₀ ≅ E') (δ : Φ.obj M₀ ≅ M') :
    ∃ (n k : ℕ) (P Q : D') (ι : Fin n → (E' ⟶ P)) (κ : Fin k → (E' ⟶ Q)),
      Nonempty (IsColimit (Cofan.mk P ι)) ∧ Nonempty (IsColimit (Cofan.mk Q κ)) ∧
        ∃ (a : Q ⟶ P) (b : P ⟶ M') (hab : a ≫ b = 0),
          Nonempty (IsColimit (CokernelCofork.ofπ b hab)) := by
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  refine ⟨n, k, Φ.obj P, Φ.obj Q, fun j ↦ γ.inv ≫ Φ.map (ι j), fun j ↦ γ.inv ≫ Φ.map (κ j),
    ⟨isColimit_cofan_comp_iso γ.symm _ (isColimitCofanMkObjOfIsColimit Φ _ ι hP)⟩,
    ⟨isColimit_cofan_comp_iso γ.symm _ (isColimitCofanMkObjOfIsColimit Φ _ κ hQ)⟩,
    Φ.map a, Φ.map b ≫ δ.hom, ?_, ⟨?_⟩⟩
  · rw [← Category.assoc, ← Φ.map_comp, hab, Functor.map_zero, zero_comp]
  · exact (isColimitCoforkMapOfIsColimit' Φ hab hb).ofIsoColimit (Cofork.ext δ rfl)

/-- Finite presentation on a site follows from a transfer of finite global presentations of the
restrictions to each object. -/
private theorem isFinitePresentationOnSite_of_over {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}} {R' : Sheaf J RingCat.{z}}
    {M : SheafOfModules.{m} R} {M' : SheafOfModules.{n} R'} (hM : M.IsFinitePresentationOnSite)
    (h : ∀ U : C, (M.over U).HasFiniteGlobalPresentation →
      (M'.over U).HasFiniteGlobalPresentation) :
    M'.IsFinitePresentationOnSite where
  locally_hasFiniteGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpres⟩ := hM.locally_hasFiniteGlobalPresentation U
    exact ⟨I, V, f, hcover, fun i ↦ h _ (hpres i)⟩

namespace SheafOfModules

section SectionLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A finite global presentation of the universe lift of the sections is one of the module
itself.** -/
theorem HasFiniteGlobalPresentation.of_uliftForPresentation {M : SheafOfModules.{m} R}
    (h : (uliftForPresentation.{u, v, r, m, max u v r} M).HasFiniteGlobalPresentation) :
    M.HasFiniteGlobalPresentation := by
  let γ : uliftForPresentation.{u, v, r, r, max u v m} (unit R) ≅
      uliftForPresentation.{u, v, r, r, max u v r m} (unit R) :=
    (uliftForPresentationSelfIso'.{u, v, r, m, max u v r m}
      (uliftForPresentation.{u, v, r, r, max u v m} (unit R))).symm ≪≫
        uliftForPresentationCompIso.{u, v, r, r, max u v m, max u v r m} (unit R)
  let δ : uliftForPresentation.{u, v, r, max u v r m, max u v r}
        (uliftForPresentation.{u, v, r, m, max u v r} M) ≅
      uliftForPresentation.{u, v, r, m, max u v r} M :=
    uliftForPresentationSelfIso'.{u, v, r, m, max u v r} _
  exact exists_finite_presentation_of_map (𝟭 _) h γ.symm δ

/-- **Finite presentation of the universe lift of the sections is finite presentation of the
module itself.** -/
theorem IsFinitePresentationOnSite.of_uliftForPresentation {M : SheafOfModules.{m} R}
    (h : (uliftForPresentation.{u, v, r, m, max u v r} M).IsFinitePresentationOnSite) :
    M.IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_of_over h fun _ hp ↦
    HasFiniteGlobalPresentation.of_uliftForPresentation hp

/-- **A finite global presentation of a sheaf of modules is one of the universe lift of its
sections, by an arbitrary amount.** -/
theorem hasFiniteGlobalPresentation_uliftForPresentation' {M : SheafOfModules.{m} R}
    (h : M.HasFiniteGlobalPresentation) :
    (uliftForPresentation.{u, v, r, m, t} M).HasFiniteGlobalPresentation := by
  have hs₁ : HasSheafify J AddCommGrpCat.{max u v r m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, u} J
  have hw₁ : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m, u, v} J
  have hs₂ : HasSheafify J AddCommGrpCat.{max u v r t m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r t m, v, u} J
  have hw₂ : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r t m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r t m, u, v} J
  have _ : PreservesFiniteColimits
      (uliftForPresentationFunctor.{u, v, r, max u v r m, t} (R := R)) :=
    preservesFiniteColimits_uliftForPresentationFunctor.{u, v, r, max u v m, t}
  let Φ := uliftForPresentationFunctor.{u, v, r, max u v r m, t} (R := R)
  let γ : Φ.obj (uliftForPresentation.{u, v, r, r, max u v m} (unit R)) ≅
      uliftForPresentation.{u, v, r, r, max u v t m} (unit R) :=
    uliftForPresentationCompIso.{u, v, r, r, max u v m, t} (unit R)
  let δ : Φ.obj (uliftForPresentation.{u, v, r, m, max u v r} M) ≅
      uliftForPresentation.{u, v, r, max t m, max u v r}
        (uliftForPresentation.{u, v, r, m, t} M) :=
    uliftForPresentationCompIso.{u, v, r, m, max u v r, t} M ≪≫
      (uliftForPresentationCompIso.{u, v, r, m, t, max u v r} M).symm
  exact exists_finite_presentation_of_map Φ h γ δ

/-- **Finite presentation of a sheaf of modules is finite presentation of the universe lift of its
sections, by an arbitrary amount.** -/
theorem isFinitePresentationOnSite_uliftForPresentation' {M : SheafOfModules.{m} R}
    (h : M.IsFinitePresentationOnSite) :
    (uliftForPresentation.{u, v, r, m, t} M).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_of_over h fun _ hp ↦
    hasFiniteGlobalPresentation_uliftForPresentation'.{max u v, v, r, m, t} hp

end SectionLift

end SheafOfModules

namespace Stacks.Modules

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

attribute [local implicit_reducible] ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.presheaf

section RingLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{r}}
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  (hset : Presheaf.IsSheaf J (structureRingPresheaf 𝒪 ⋙ forget RingCat.{r}))

/-- **A finite global presentation descends along the universe lift of the coefficient rings.** -/
theorem hasFiniteGlobalPresentation_sheafRingULiftDown
    (M : _root_.SheafOfModules.{max u v r z} (structureSheafRingULift.{u, v, r, z} hset))
    (h : M.HasFiniteGlobalPresentation) :
    ((sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset).obj
      M).HasFiniteGlobalPresentation := by
  let D := sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset
  let α := _root_.SheafOfModules.uliftForPresentationCompIso.{u, v, r, r, max u v z, max u v r z}
    (_root_.SheafOfModules.unit (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
  let β : D.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, max u v r z, max u v r z,
        max u v r z} M) ≅
      _root_.SheafOfModules.uliftForPresentation.{u, v, r, max u v r z, max u v r} (D.obj M) :=
    _root_.SheafOfModules.uliftForPresentationSelfIso (D.obj M) ≪≫
      (_root_.SheafOfModules.uliftForPresentationSelfIso'.{u, v, r, z, max u v r}
        (D.obj M)).symm
  exact exists_finite_presentation_of_map D h α β

/-- **Finite presentation descends along the universe lift of the coefficient rings.** -/
theorem isFinitePresentationOnSite_sheafRingULiftDown
    (M : _root_.SheafOfModules.{max u v r z} (structureSheafRingULift.{u, v, r, z} hset))
    (hM : M.IsFinitePresentationOnSite) :
    ((sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset).obj
      M).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_of_over hM fun U hp ↦
    hasFiniteGlobalPresentation_sheafRingULiftDown.{max u v, v, r, z}
      (J := J.over U) (𝒪 := (Over.forget U).op ⋙ 𝒪)
      (Sheaf.over (⟨_, h𝒪⟩ : Sheaf J RingCat.{r}) U).property
      (Sheaf.over (⟨_, hset⟩ : Sheaf J (Type r)) U).property (M.over U) hp

/-- **A finite global presentation ascends along the universe lift of the coefficient rings.** -/
theorem hasFiniteGlobalPresentation_sheafRingULiftUp
    (N : _root_.SheafOfModules.{max u v r z}
      (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (h : N.HasFiniteGlobalPresentation) :
    ((sheafRingULiftUp.{u, v, r, z, max u v r z} h𝒪 hset).obj
      N).HasFiniteGlobalPresentation := by
  let U := sheafRingULiftUp.{u, v, r, z, max u v r z} h𝒪 hset
  let α := _root_.SheafOfModules.uliftForPresentationCompIso.{u, v, r, r, max u v z, max u v r z}
    (_root_.SheafOfModules.unit (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
  let β : U.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, r, max u v r z, max u v r}
        N) ≅
      _root_.SheafOfModules.uliftForPresentation.{u, v, max u v r z, max u v r z, max u v r z}
        (U.obj N) :=
    _root_.SheafOfModules.uliftForPresentationSelfIso'.{u, v, max u v r z, z, max u v r}
        (U.obj N) ≪≫
      (_root_.SheafOfModules.uliftForPresentationSelfIso (U.obj N)).symm
  exact exists_finite_presentation_of_map U h (U.mapIso α).symm β

/-- **Finite presentation ascends along the universe lift of the coefficient rings.** -/
theorem isFinitePresentationOnSite_sheafRingULiftUp
    (N : _root_.SheafOfModules.{max u v r z}
      (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (hN : N.IsFinitePresentationOnSite) :
    ((sheafRingULiftUp.{u, v, r, z, max u v r z} h𝒪 hset).obj
      N).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_of_over hN fun U hp ↦
    hasFiniteGlobalPresentation_sheafRingULiftUp.{max u v, v, r, z}
      (J := J.over U) (𝒪 := (Over.forget U).op ⋙ 𝒪)
      (Sheaf.over (⟨_, h𝒪⟩ : Sheaf J RingCat.{r}) U).property
      (Sheaf.over (⟨_, hset⟩ : Sheaf J (Type r)) U).property (N.over U) hp

end RingLift

section Mixed

variable {C : Type so} [Category.{sm} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- **The tensor product of two sheaves of modules of finite presentation with sections in
independent universes on a ringed site is of finite presentation.**  The tensor product is the
sheafification of the universe lift of the objectwise tensor product. -/
theorem isFinitePresentationOnSite_sheafificationTensorObjUlift
    (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
    (hset : Presheaf.IsSheaf J (structureRingPresheaf 𝒪 ⋙ forget RingCat.{r}))
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m n}]
    [HasWeakSheafify J AddCommGrpCat.{max r m n}]
    (F : _root_.SheafOfModules.{m} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (G : _root_.SheafOfModules.{n} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (hF : F.IsFinitePresentationOnSite) (hG : G.IsFinitePresentationOnSite) :
    ((PresheafOfModules.sheafification.{max r m n}
      (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).obj
        ((PresheafOfModules.tensorObj (O := 𝒪) F.val
          G.val).uliftSections.{r})).IsFinitePresentationOnSite := by
  have _ := _root_.SheafOfModules.isLocallyInjective_id_structure
    (R := SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)
  have _ := _root_.SheafOfModules.isLocallySurjective_id_structure
    (R := SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)
  have hF' := _root_.SheafOfModules.isFinitePresentationOnSite_uliftForPresentation'.{so, sm, r,
    m, max so sm r n} hF
  have hG' := _root_.SheafOfModules.isFinitePresentationOnSite_uliftForPresentation'.{so, sm, r,
    n, max so sm r m} hG
  have leftFP := isFinitePresentationOnSite_sheafRingULiftUp.{so, sm, r, max m n} h𝒪 hset
    (_root_.SheafOfModules.uliftForPresentation.{so, sm, r, m, max so sm r n} F) hF'
  have rightFP := isFinitePresentationOnSite_sheafRingULiftUp.{so, sm, r, max m n} h𝒪 hset
    (_root_.SheafOfModules.uliftForPresentation.{so, sm, r, n, max so sm r m} G) hG'
  have _ : HasSheafify J AddCommGrpCat.{max so sm r m n} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max so sm r m n, sm, so} J
  have _ : J.WEqualsLocallyBijective AddCommGrpCat.{max so sm r m n} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max so sm r m n,
      so, sm} J
  have _ : ∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max so sm r m n} := fun U ↦
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max so sm r m n, sm, max so sm} (J.over U)
  have _ : ∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max so sm r m n} :=
    fun U ↦ AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{
      max so sm r m n, max so sm, sm} (J.over U)
  have _ := _root_.SheafOfModules.isLocallyInjective_id_structure
    (R := structureSheafRingULift.{so, sm, r, max m n} hset)
  have _ := _root_.SheafOfModules.isLocallySurjective_id_structure
    (R := structureSheafRingULift.{so, sm, r, max m n} hset)
  let X : AlgebraicGeometry.RingedSite.{so, sm, max so sm r m n} :=
    { C := C
      J := J
      O := ⟨ringULift.{so, sm, r, max m n} 𝒪, Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ CommRingCat RingCat)
        (isSheaf_structureRingPresheaf_ringULift.{so, sm, r, max m n} 𝒪 hset)⟩ }
  have tensorFP :=
    Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentationOnSite X
      ((sheafRingULiftUp.{so, sm, r, max m n, max so sm r m n} h𝒪 hset).obj
        (_root_.SheafOfModules.uliftForPresentation.{so, sm, r, m, max so sm r n} F))
      ((sheafRingULiftUp.{so, sm, r, max m n, max so sm r m n} h𝒪 hset).obj
        (_root_.SheafOfModules.uliftForPresentation.{so, sm, r, n, max so sm r m} G))
      leftFP rightFP
  have hD := isFinitePresentationOnSite_sheafRingULiftDown.{so, sm, r, max m n} h𝒪 hset _
    tensorFP
  have e₁ := sheafificationRingULiftDownIso.{so, sm, r, max so sm r m n, max m n} h𝒪 hset
    (tensorPresheafRingULift.{so, sm, r, 0, m, n} 𝒪 F.val G.val)
  have e₂ := (PresheafOfModules.sheafification.{max so sm r m n}
      (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).mapIso
    (tensorPresheafRingULiftDownIso.{so, sm, r, 0, m, n} 𝒪 F.val G.val ≪≫
      (PresheafOfModules.uliftSectionsCompIso.{so, sm, r, max m n, r, max so sm}
        (PresheafOfModules.tensorObj (O := 𝒪) F.val G.val)).symm)
  have e₃ := PresheafOfModules.sheafificationUliftObjIso.{so, sm, r, max r m n, max so sm r}
    (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)
    ((PresheafOfModules.tensorObj (O := 𝒪) F.val G.val).uliftSections.{r})
  exact _root_.SheafOfModules.IsFinitePresentationOnSite.of_uliftForPresentation.{so, sm, r,
    max r m n}
    (_root_.SheafOfModules.IsFinitePresentationOnSite.of_iso (e₁.symm ≪≫ e₂ ≪≫ e₃) hD)

end Mixed

end Stacks.Modules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) [EssentiallySmall.{u} 𝒳]

/-- **The tensor product of two modules of finite presentation with sections in independent
universes on an associated site of a category fibred in groupoids is of finite presentation.**
The tensor product is `AlgebraicGeometry.FibredSite.tensorSheafMixed`, the object carrying the
universal property of Stacks 06WN(2). -/
theorem isFinitePresentationOnSite_tensorSheafMixed (τ : SiteKind)
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ))
    (G : SheafOfModules.{n} (ringStructureSheafCore B S hS p hp τ))
    (hF : F.IsFinitePresentationOnSite) (hG : G.IsFinitePresentationOnSite) :
    (tensorSheafMixed B S hS p hp τ F G).IsFinitePresentationOnSite :=
  have _ := hasWeakSheafify_associatedTopology_above.{u, v, max m n} B S hS p τ
  have _ := wEqualsLocallyBijective_associatedTopology_above.{u, v, max m n} B S hS p τ
  Stacks.Modules.isFinitePresentationOnSite_sheafificationTensorObjUlift.{u, m, n, v, u}
    (𝒪 := (structureSheaf B S hS p hp τ).obj)
    (ringStructureSheafCore B S hS p hp τ).property
    (structureRingPresheaf_isSheafOfSets B S hS p hp τ) F G hF hG

/-- **Stacks Project, Tag 03L6, finite presentation case, on an associated site of a category
fibred in groupoids.**  The tensor product `Stacks.SheafOfModules.Tensor.sheafTensor` of two
modules of finite presentation, with sections in the universe of the coefficient rings, is of
finite presentation.  It is identified with `AlgebraicGeometry.FibredSite.tensorSheafMixed` by
`AlgebraicGeometry.FibredSite.tensorSheafMixedIsoTensorSheaf`. -/
theorem isFinitePresentationOnSite_tensorSheaf (τ : SiteKind)
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ))
    (hF : F.IsFinitePresentationOnSite) (hG : G.IsFinitePresentationOnSite) :
    letI := hasWeakSheafify_associatedTopology B S hS p τ
    letI := wEqualsLocallyBijective_associatedTopology B S hS p τ
    (((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf B S hS p hp τ)).obj F).obj
      G).IsFinitePresentationOnSite :=
  SheafOfModules.IsFinitePresentationOnSite.of_iso
    (tensorSheafMixedIsoTensorSheaf B S hS p hp τ F G)
    (isFinitePresentationOnSite_tensorSheafMixed B S hS p hp τ F G hF hG)

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The tensor product of two coherent modules on an algebraic stack is coherent.**  The tensor
product is the tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` on the fppf site of
`𝒳`. -/
theorem isCoherent_tensorSheaf (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hF : IsCoherent B S hS 𝒳 F) (hG : IsCoherent B S hS 𝒳 G) :
    letI := FibredSite.hasWeakSheafify_associatedTopology B S hS 𝒳.val.val.p .fppf
    letI := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p .fppf
    IsCoherent B S hS 𝒳
      (((Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.structureSheaf B S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).obj F).obj G) :=
  have h := FibredSite.isFinitePresentationOnSite_tensorSheaf B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf F G hF.isFinitePresentationOnSite
    hG.isFinitePresentationOnSite
  ⟨⟨@SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ _ h,
    @SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _ h⟩, h⟩

end AlgebraicGeometry.Stack

end
