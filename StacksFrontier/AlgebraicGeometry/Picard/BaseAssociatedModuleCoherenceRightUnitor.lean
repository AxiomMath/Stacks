module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf
public import StacksFrontier.AlgebraicGeometry.Picard.BaseAssociatedModuleCoherenceComplete
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor

/-!
# The right unit coherence of the tensor comparison of the associated-module functor

Of the four coherences that
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` asks of the object-level
comparisons of `𝓕 ↦ 𝓕^a`, three are discharged:
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_natural`,
`baseAssociatedModuleTensorIso'_braiding` and `baseAssociatedModuleTensorIso'_associator`.  This
file carries the **right unit** one as far as it can be carried: the transport lemma, the
coherence of Stacks 03EL in the vocabulary of Tag 01CA, and the coherence at the base spelling
are all proved unconditionally, and
`Stacks.SheafOfModules.TensorPowerTransport.TensorIsoRightUnitor` follows from exactly **one**
further equation, which is proved in
`StacksFrontier/CategoryTheory/Sites/Modules/RingedToposModulesPullbackToposGeneralUnit.lean` and
supplied in `StacksFrontier/AlgebraicGeometry/Picard/BaseAssociatedModuleRightUnitor.lean`.

## The one further equation

`AlgebraicGeometry.BigFppfOver.baseAssociatedModulePicardUnitIso` and
`Stacks.SheafOfModules.RingedToposPullback.pullbackUnitComparison` are two *different*
constructions of the identification `f^*𝒪_S ≅ 𝒪` of Stacks 03LU at the morphism
`((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`:

* the first is Mathlib's `SheafOfModules.pullbackObjUnitToUnit` at
  `AlgebraicGeometry.BigFppfOver.baseStructureMap`, characterised only as an adjoint transpose by
  `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`;
* the second is `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, built by
  corepresentability and characterised by
  `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_hom_comp`, and after
  `pullbackModulesObjUnitIso_eq` by the formula `ν(1 ⊗ t) = f♯(t)` of
  `moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv`.

They are conjugate under
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule`, which is a
`CategoryTheory.Adjunction.leftAdjointUniq` and carries no formula.  The equation is neither
`rfl` nor reachable by `simp` or `aesop_cat`; it is assembled out of the two transpose
characterisations in
`StacksFrontier/CategoryTheory/Sites/Modules/RingedToposModulesPullbackToposGeneralUnit.lean`, where
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral_hom_app_unit` proves it
for an arbitrary morphism of ringed sites:
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` compares the two transpositions and
`SheafOfModules.unitHomEquiv` is injective, which pins a morphism out of the unit object.

`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_rightUnitor_of_unitComparison_eq`
takes that equation as its one hypothesis, and so is **not** by itself a proof of the coherence.
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_rightUnitor`, in
`StacksFrontier/AlgebraicGeometry/Picard/BaseAssociatedModuleRightUnitor.lean`, supplies the
hypothesis and is the unconditional coherence.

## Main results

* `Stacks.SheafOfModules.TransportCoherence.transported_rightUnitor'`: **the right unit coherence
  transports along a natural isomorphism of functors**, the third companion of
  `transported_associator'` and `transported_braiding`.
* `Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_rightUnitality`: the right
  unit coherence of Stacks 03EL retyped out of the whiskering-and-unitor vocabulary of the strict
  monoidal structure into the `tensorProductRightUnitor` vocabulary of Tag 01CA, with the two
  sheaf conditions as explicit arguments.
* `AlgebraicGeometry.BigFppfOver.baseTensorComparison_rightUnitor`: that coherence at the
  structure sheaf of the ringed site.

## Implementation notes

The crossing between the ringed-site and the ringed-topos spellings is paid factor by factor, by
four `rfl` lemmas, for the reason recorded at the head of
`StacksFrontier/AlgebraicGeometry/Picard/BaseAssociatedModuleCoherenceComplete.lean`: each factor
crosses on its own, all four at once exceed the recursion limit.  Each crossing is its own
declaration rather than a `have` inside the proof — as a `have` the recursion is measured on top
of the enclosing elaboration and the third one overflows.

The naturality of the right unit constraint at the bifunctor spelling is not restated here: it is
`Stacks.IdealTorsion.Eta.tensorProductRightUnitor_naturality`, already stated over a presheaf of
commutative rings together with a sheaf condition, which is the index this needs.  Importing it
costs twelve modules.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)
open Stacks.SheafOfModules.Invertible (tensorProductRightUnitor tensorProductBifunctor)
open Stacks.SheafOfModules.TensorEncodings (isSheaf_structureRingPresheaf)
open Stacks.SheafOfModules.RingedToposPullback (pullbackTensorComparison pullbackUnitComparison)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe w w' v u v' u'

/-! ### The right unit coherence transports along an isomorphism of functors -/

namespace Stacks.SheafOfModules.TransportCoherence

variable {C₁ : Type u} [Category.{v} C₁] {C₂ : Type u'} [Category.{v'} C₂]
  {G₁ G₂ : C₁ ⥤ C₂} (Z : G₁ ≅ G₂)
  (T₁ : C₁ → C₁ → C₁) (T₂ : C₂ → C₂ → C₂)
  (t₂ : ∀ X X' Y Y' : C₂, (X ⟶ X') → (Y ⟶ Y') → (T₂ X Y ⟶ T₂ X' Y'))
  (u₁ : C₁) (u₂ : C₂)
  (r₁ : ∀ A : C₁, T₁ A u₁ ≅ A) (r₂ : ∀ X : C₂, T₂ X u₂ ≅ X)
  (δ : ∀ A B : C₁, G₁.obj (T₁ A B) ⟶ T₂ (G₁.obj A) (G₁.obj B))
  (ε₁ : G₁.obj u₁ ⟶ u₂)

/-- **The right unit coherence transports along a natural isomorphism of functors.**  Let
`Z : G₁ ≅ G₂` be an isomorphism of functors, let `T₁` and `T₂` be binary operations with units
`u₁`, `u₂` and right unit constraints `r₁`, `r₂`, let `t₂` act on pairs of morphisms, and let
`δ` and `ε₁` be comparisons for `G₁` compatible with the right unit constraints (`hδ`).  Then the
comparisons `h` and `ε₂` of `G₂` obtained from them by conjugating with `Z` (`hh`, `hε`) are
compatible with them as well.

As in `Stacks.SheafOfModules.TransportCoherence.transported_associator'` and
`transported_braiding`, the operation, its unit and its constraint are explicit data rather than
a `CategoryTheory.MonoidalCategory` instance, so that nothing has to be matched against a
competing instance when this is used on sheaves of modules.  `ht₂comp` is the functoriality of
`t₂` and `hr₂` the naturality of `r₂`. -/
public theorem transported_rightUnitor'
    (h : ∀ A B : C₁, G₂.obj (T₁ A B) ⟶ T₂ (G₂.obj A) (G₂.obj B))
    (ε₂ : G₂.obj u₁ ⟶ u₂)
    (hh : ∀ A B : C₁, h A B = Z.inv.app (T₁ A B) ≫ δ A B ≫
        t₂ (G₁.obj A) (G₂.obj A) (G₁.obj B) (G₂.obj B) (Z.hom.app A) (Z.hom.app B))
    (hε : ε₂ = Z.inv.app u₁ ≫ ε₁)
    (ht₂comp : ∀ (X X' X'' Y Y' Y'' : C₂) (u : X ⟶ X') (u' : X' ⟶ X'') (v : Y ⟶ Y')
      (v' : Y' ⟶ Y''), t₂ X X' Y Y' u v ≫ t₂ X' X'' Y' Y'' u' v' = t₂ X X'' Y Y'' (u ≫ u') (v ≫ v'))
    (hr₂ : ∀ (X X' : C₂) (u : X ⟶ X'), t₂ X X' u₂ u₂ u (𝟙 u₂) ≫ (r₂ X').hom = (r₂ X).hom ≫ u)
    (hδ : ∀ A : C₁, G₁.map (r₁ A).hom = δ A u₁ ≫
        t₂ (G₁.obj A) (G₁.obj A) (G₁.obj u₁) u₂ (𝟙 (G₁.obj A)) ε₁ ≫ (r₂ (G₁.obj A)).hom)
    (A : C₁) :
    G₂.map (r₁ A).hom =
      h A u₁ ≫
        t₂ (G₂.obj A) (G₂.obj A) (G₂.obj u₁) u₂ (𝟙 (G₂.obj A)) ε₂ ≫ (r₂ (G₂.obj A)).hom := by
  have s : t₂ (G₁.obj A) (G₂.obj A) (G₁.obj u₁) u₂ (Z.hom.app A) ε₁ =
      t₂ (G₁.obj A) (G₁.obj A) (G₁.obj u₁) u₂ (𝟙 (G₁.obj A)) ε₁ ≫
        t₂ (G₁.obj A) (G₂.obj A) u₂ u₂ (Z.hom.app A) (𝟙 u₂) := by
    rw [ht₂comp]
    simp only [Category.id_comp, Category.comp_id]
  rw [hh A u₁, hε]
  simp only [Category.assoc]
  rw [reassoc_of% (ht₂comp (G₁.obj A) (G₂.obj A) (G₂.obj A) (G₁.obj u₁) (G₂.obj u₁) u₂
    (Z.hom.app A) (𝟙 (G₂.obj A)) (Z.hom.app u₁) (Z.inv.app u₁ ≫ ε₁))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [s, Category.assoc, hr₂ (G₁.obj A) (G₂.obj A) (Z.hom.app A), ← reassoc_of% (hδ A),
    ← Z.inv.naturality_assoc (r₁ A).hom (Z.hom.app A)]
  simp

end Stacks.SheafOfModules.TransportCoherence

/-! ### The right unit coherence of Tag 03EL, in the Tag 01CA vocabulary -/

namespace Stacks.SheafOfModules.RingedToposPullback

open _root_.AlgebraicGeometry (RingedTopos)
open _root_.Stacks.Sheaves.RingedToposModules (RingedToposHom)

variable {Xt : RingedTopos.{v, u, w}} {Yt : RingedTopos.{v', u', w'}}
  [Xt.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Yt.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Xt.J.HasSheafCompose (forget RingCat.{w})] [Yt.J.HasSheafCompose (forget RingCat.{w'})]
  [Xt.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Yt.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify Xt.J AddCommGrpCat.{w}] [Xt.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Yt.J AddCommGrpCat.{w'}] [Yt.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom Xt Yt)
  (hOX : Presheaf.IsSheaf Xt.J (structureRingPresheaf Xt.O.obj))
  (hOY : Presheaf.IsSheaf Yt.J (structureRingPresheaf Yt.O.obj))

/-- **The comparison of Stacks 03EL along an arbitrary morphism of ringed topoi, together with
the comparison `ν : f^*𝒪_D ≅ 𝒪_C` of the structure sheaves, is compatible with the right unit
constraint of Tag 01CA**, with no hypothesis.  This is
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.rightUnitality` retyped out of the
whiskering-and-unitor vocabulary of `Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf`.

The two sheaf conditions are explicit arguments, and each rewrite is given its own arguments
explicitly, for the reasons recorded at
`Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_associator`. -/
public theorem pullbackTensorComparison_rightUnitality
    (F : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      Yt.O.obj hOY)) :
    (pullbackModules f).map (tensorProductRightUnitor Yt.O.obj hOY F).hom =
      pullbackTensorComparison f F (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf Yt.O.obj hOY)) ≫
        (tensorProductBifunctor Xt.O.obj hOX).map
          (X := ((pullbackModules f).obj F, (pullbackModules f).obj (SheafOfModules.unit
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf Yt.O.obj hOY))))
          (Y := ((pullbackModules f).obj F, SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf Xt.O.obj hOX)))
          (𝟙 ((pullbackModules f).obj F), (pullbackUnitComparison f).hom) ≫
        (tensorProductRightUnitor Xt.O.obj hOX ((pullbackModules f).obj F)).hom := by
  have h := (pullbackCoherence f).rightUnitality F
  have hL : ((Stacks.SheafOfModules.Tensor.sheafTensor Xt.O).map
          (𝟙 ((pullbackModules f).obj F))).app ((pullbackModules f).obj (SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf Yt.O.obj hOY))) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Xt.O).obj ((pullbackModules f).obj F)).map
          (pullbackUnitComparison f).hom =
      (tensorProductBifunctor Xt.O.obj hOX).map
        (X := ((pullbackModules f).obj F, (pullbackModules f).obj (SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf Yt.O.obj hOY))))
        (Y := ((pullbackModules f).obj F, (SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf Xt.O.obj hOX))))
        (𝟙 ((pullbackModules f).obj F), (pullbackUnitComparison f).hom) :=
    Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Xt.O
      (𝟙 ((pullbackModules f).obj F)) (pullbackUnitComparison f).hom
  rw [Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map Xt.O
      ((pullbackModules f).obj F) (pullbackUnitComparison f).hom,
    Stacks.SheafOfModules.Strict.rightUnitor_hom_eq_tensorProductRightUnitor Yt.O F,
    Stacks.SheafOfModules.Strict.rightUnitor_hom_eq_tensorProductRightUnitor Xt.O
      ((pullbackModules f).obj F)] at h
  rw [← hL]
  exact h

end Stacks.SheafOfModules.RingedToposPullback

/-! ### The right unit coherence at the base spelling -/

namespace AlgebraicGeometry.BigFppfOver

open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Each factor of the right unit square crosses between the ringed-site and the ringed-topos
spelling by `rfl`; crossing all four at once does not finish inside the recursion limit, so the
four are crossed separately. -/
private theorem e1 (τ : SiteKind) (M : S.Modules) :
    (basePullbackModules B S hS τ).map (tensorProductRightUnitor S.presheaf (zariskiStructureIsSheaf
      S) M).hom =
      (basePullbackModules B S hS τ).map (tensorProductRightUnitor
        S.zariskiRingedSite.toRingedTopos.O.obj (zariskiStructureIsSheaf S) M).hom := rfl

private theorem e2 (τ : SiteKind) (M : S.Modules) :
    baseTensorComparison B S hS τ M (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf (zariskiStructureIsSheaf
        S))) =
      pullbackTensorComparison (baseRingedToposModulesHom B S hS τ) M (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          S.zariskiRingedSite.toRingedTopos.O.obj (zariskiStructureIsSheaf S))) := rfl

private theorem e3 (τ : SiteKind) (M : S.Modules) :
    (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2).map
        (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
            (zariskiStructureIsSheaf S)))))
        (Y := ((basePullbackModules B S hS τ).obj M, SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf (baseRingedSite B S hS τ).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2)))
        (𝟙 ((basePullbackModules B S hS τ).obj M), (pullbackUnitComparison
          (baseRingedToposModulesHom B S hS τ)).hom) =
      (tensorProductBifunctor (baseRingedSite B S hS τ).toRingedTopos.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2).map
        (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
            S.zariskiRingedSite.toRingedTopos.O.obj (zariskiStructureIsSheaf S)))))
        (Y := ((basePullbackModules B S hS τ).obj M, SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf (baseRingedSite B S hS
            τ).toRingedTopos.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2)))
        (𝟙 ((basePullbackModules B S hS τ).obj M), (pullbackUnitComparison
          (baseRingedToposModulesHom B S hS τ)).hom) := rfl

private theorem e4 (τ : SiteKind) (M : S.Modules) :
    (tensorProductRightUnitor (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
      ((basePullbackModules B S hS τ).obj M)).hom =
      (tensorProductRightUnitor (baseRingedSite B S hS τ).toRingedTopos.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
        ((basePullbackModules B S hS τ).obj M)).hom := rfl

/-- **The comparison of Stacks 03EL at `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, together with the
comparison of the structure sheaves, is compatible with the right unit constraint of
Tag 01CA**, read at the structure sheaf and sheaf condition of the ringed site
`AlgebraicGeometry.BigFppfOver.baseRingedSite`.

It is `Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_rightUnitality` at
that morphism, with the four factors crossed one at a time. -/
theorem baseTensorComparison_rightUnitor (τ : SiteKind) (M : S.Modules) :
    (basePullbackModules B S hS τ).map (tensorProductRightUnitor S.presheaf (zariskiStructureIsSheaf
      S) M).hom =
      baseTensorComparison B S hS τ M (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
          (zariskiStructureIsSheaf S))) ≫
        (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2).map
        (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
            (zariskiStructureIsSheaf S)))))
        (Y := ((basePullbackModules B S hS τ).obj M, SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf (baseRingedSite B S hS τ).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2)))
        (𝟙 ((basePullbackModules B S hS τ).obj M), (pullbackUnitComparison
          (baseRingedToposModulesHom B S hS τ)).hom) ≫
        (tensorProductRightUnitor (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
          ((basePullbackModules B S hS τ).obj M)).hom := by
  rw [e1 B S hS τ M, e2 B S hS τ M, e3 B S hS τ M, e4 B S hS τ M]
  exact Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_rightUnitality
    (baseRingedToposModulesHom B S hS τ)
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
    (zariskiStructureIsSheaf S) M

/-- **The object-level comparisons of `𝓕 ↦ 𝓕^a` are compatible with the right unit constraint of
Tag 01CA, given that its unit comparison is the conjugate of the one of Stacks 03EL.**

This is **not** a proof of
`Stacks.SheafOfModules.TensorPowerTransport.TensorIsoRightUnitor` for `𝓕 ↦ 𝓕^a`: the hypothesis
`hunit` is the whole of what is missing, and it is discussed at the head of this file.  Every
other input is proved unconditionally —
`AlgebraicGeometry.BigFppfOver.baseTensorComparison_rightUnitor` for the coherence of the
pullback, `baseAssociatedModuleTensorIso'_hom'` for the conjugation of the tensor comparison,
`Stacks.IdealTorsion.Eta.tensorProductRightUnitor_naturality` for the naturality of the
constraint, and the functoriality of
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor` for the tensor action — so discharging
`hunit` discharges the coherence, and with it the last of the four data
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` asks for. -/
public theorem baseAssociatedModuleTensorIso'_rightUnitor_of_unitComparison_eq (τ : SiteKind)
    (hunit : (baseAssociatedModulePicardUnitIso B S hS τ).hom =
      (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
          (zariskiStructureIsSheaf S))) ≫
        (pullbackUnitComparison (baseRingedToposModulesHom B S hS τ)).hom) :
    Stacks.SheafOfModules.TensorPowerTransport.TensorIsoRightUnitor S.presheaf
      (zariskiStructureIsSheaf S) (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
      (baseAssociatedModule B S hS τ)
      (baseAssociatedModulePicardUnitIso B S hS τ)
      (baseAssociatedModuleTensorIso' B S hS τ) :=
  fun A =>
    Stacks.SheafOfModules.TransportCoherence.transported_rightUnitor'
      (pullbackModulesIsoBaseAssociatedModule B S hS τ)
      ((fun tensorLeft tensorRight => (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
          (zariskiStructureIsSheaf S)⟩).obj tensorLeft).obj tensorRight)))
      ((fun tensorLeft tensorRight => (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
          (baseRingedSite B S hS τ).O.obj (forget₂ CommRingCat RingCat)
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2⟩).obj
            tensorLeft).obj tensorRight)))
      (fun X X' Y Y' u v =>
        (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2).map
          (X := (X, Y)) (Y := (X', Y')) (u, v))
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        S.presheaf (zariskiStructureIsSheaf S)))
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2))
      (tensorProductRightUnitor S.presheaf (zariskiStructureIsSheaf S))
      (tensorProductRightUnitor (baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2)
      (baseTensorComparison B S hS τ)
      (pullbackUnitComparison (baseRingedToposModulesHom B S hS τ)).hom
      (fun M N => (baseAssociatedModuleTensorIso' B S hS τ M N).hom)
      (baseAssociatedModulePicardUnitIso B S hS τ).hom
      (baseAssociatedModuleTensorIso'_hom' B S hS τ)
      hunit
      (fun X X' X'' Y Y' Y'' u u' v v' =>
        ((tensorProductBifunctor (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2).map_comp
          (X := (X, Y)) (Y := (X', Y')) (Z := (X'', Y'')) (u, v) (u', v')).symm)
      (fun X X' u => by
        have hu : (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2).map
              (X := (X, SheafOfModules.unit
                (Stacks.SheafOfModules.TensorSheafification.structureSheaf
                  (baseRingedSite B S hS τ).O.obj
                  (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2)))
              (Y := (X', SheafOfModules.unit
                (Stacks.SheafOfModules.TensorSheafification.structureSheaf
                  (baseRingedSite B S hS τ).O.obj
                  (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2)))
              (u, 𝟙 (SheafOfModules.unit
                (Stacks.SheafOfModules.TensorSheafification.structureSheaf
                  (baseRingedSite B S hS τ).O.obj
                  (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2))) =
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
                  (baseRingedSite B S hS τ).O.obj
                  (forget₂ CommRingCat RingCat)
                  (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2⟩)).map
              (X := (X, SheafOfModules.unit _)) (Y := (X', SheafOfModules.unit _))
              (u, 𝟙 _)) :=
          (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
            ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
              (baseRingedSite B S hS τ).O.obj
              (forget₂ CommRingCat RingCat)
              (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2⟩ u (𝟙 _)).symm
        exact (congrArg (fun z => z ≫ (tensorProductRightUnitor (baseRingedSite B S hS τ).O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2 X').hom)
            hu).trans
          (Stacks.IdealTorsion.Eta.tensorProductRightUnitor_naturality
            (baseRingedSite B S hS τ).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2 u))
      (baseTensorComparison_rightUnitor B S hS τ)
      A

end AlgebraicGeometry.BigFppfOver

end
