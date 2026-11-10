module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackBraiding
public import StacksFrontier.AlgebraicGeometry.Picard.BaseAssociatedModuleCoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor

/-!
# The symmetry coherence of the tensor comparison of the associated-module functor

`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'` is the comparison of Stacks 03EL
at the morphism of ringed sites `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, packaged as the object-level
tensor comparison of the associated-module functor `𝓕 ↦ 𝓕^a` of Stacks 03DU (4).  This file proves
that this comparison is compatible with the symmetry constraint of Tag 01CA, in the form
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` asks for it.

The symmetry one became available only with
`Stacks.SheafOfModules.RingedToposPullback.braiding`, the braiding coherence of Tag 03EL for a
morphism of ringed *topoi*; before it the repository had the statement for a morphism of ringed
*spaces* alone, and `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence` has only the
three fields `associativity`, `leftUnitality` and `rightUnitality`.  That theorem stands outside
the structure, so it is consumed here without touching `PullbackCoherence`.

## Main results

* `Stacks.SheafOfModules.Strict.braiding_hom_eq_tensorProductBraiding`: **the symmetry constraint
  of the strict monoidal structure is the fixed symmetry constraint of Tag 01CA.**
* `Stacks.SheafOfModules.TransportCoherence.transported_braiding`: **the symmetry coherence
  transports along a natural isomorphism of functors**.
* `Stacks.SheafOfModules.Invertible.tensorProductBraiding_naturality_bifunctorMap`: naturality of
  the symmetry constraint of Tag 01CA.
* `Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_braiding'`: the braiding
  coherence of Tag 03EL retyped into the `tensorProductBraiding` vocabulary of Tag 01CA.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_braiding`: **the symmetry
  coherence for `𝓕 ↦ 𝓕^a`**, at every one of the five topologies and with no hypothesis on `S`.

## Implementation notes

The two transport lemmas are stated in an abstract braided monoidal category, for the reason
recorded in `StacksFrontier/AlgebraicGeometry/Picard/BaseAssociatedModuleCoherence.lean`: the
composites to reassociate straddle three categories of sheaves of modules whose ring sheaves are
spelled differently, so a single composite carries two `CategoryTheory.Category` instances that
agree only at default transparency and neither `rw` nor `simp` nor `CategoryTheory.Category.assoc`
will fire on it.  In the abstract statement no object carries a projection of a ringed site and
the monoidal lemmas do fire; the sheaf case is an instance of it, taken by `exact`.

`Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf` is switched on by
`attribute [local instance]` only inside the section that needs it.  Left in scope in the
consuming namespace it silently wins instance search over the `letI` of
`Stacks.SheafOfModules.sheafTensorMonoidal`, so that `α_` and `β_` elaborate to the strict
versions and every later crossing stops being definitional.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.SheafOfModules.Invertible (tensorProductIso tensorProductAssociator
  tensorProductBraiding tensorProductRightUnitor)
open Stacks.SheafOfModules.TensorEncodings (isSheaf_structureRingPresheaf)
open Stacks.SheafOfModules.RingedToposPullback (pullbackTensorComparison)

universe w w' v u v' u'

/-! ### The symmetry coherence transports along an isomorphism of functors -/

namespace Stacks.SheafOfModules.TransportCoherence

variable {C₁ : Type u} [Category.{v} C₁] {C₂ : Type u'} [Category.{v'} C₂]
  {G₁ G₂ : C₁ ⥤ C₂} (Z : G₁ ≅ G₂)
  (T₁ : C₁ → C₁ → C₁) (T₂ : C₂ → C₂ → C₂)
  (t₂ : ∀ X X' Y Y' : C₂, (X ⟶ X') → (Y ⟶ Y') → (T₂ X Y ⟶ T₂ X' Y'))
  (b₁ : ∀ A B : C₁, T₁ A B ≅ T₁ B A) (b₂ : ∀ X Y : C₂, T₂ X Y ≅ T₂ Y X)
  (δ : ∀ A B : C₁, G₁.obj (T₁ A B) ⟶ T₂ (G₁.obj A) (G₁.obj B))

/-- **The symmetry coherence transports along a natural isomorphism of functors.**  Let
`Z : G₁ ≅ G₂` be an isomorphism of functors, let `T₁` and `T₂` be binary operations on objects
carrying symmetries `b₁` and `b₂`, let `t₂` act on pairs of morphisms, and let
`δ A B : G₁(T₁ A B) ⟶ T₂ (G₁ A) (G₁ B)` be a comparison compatible with the symmetries (`hδ`).
Then the comparison `h` of `G₂` obtained from `δ` by conjugating with `Z` (`hh`) is compatible
with them as well.

The tensor product, its symmetry and its action on morphisms are *explicit data* rather than a
`CategoryTheory.MonoidalCategory` instance, which is what makes this usable on sheaves of
modules: those carry the localized monoidal structure of
`Stacks.SheafOfModules.monoidalCategory` as a global instance, so `⊗` and `β_` in a statement
written with the notation resolve to that structure and not to the fixed constraints of Tag 01CA,
and matching the two is a `whnf` of the induced structure that exhausts the heartbeat budget.
At the spelling below nothing has to be matched.  It is the companion of
`Stacks.SheafOfModules.TransportCoherence.transported_associator`, which is stated with the
notation and is therefore applicable only where no competing instance is in scope. -/
theorem transported_braiding
    (h : ∀ A B : C₁, G₂.obj (T₁ A B) ⟶ T₂ (G₂.obj A) (G₂.obj B))
    (hh : ∀ A B : C₁, h A B =
      Z.inv.app (T₁ A B) ≫ δ A B ≫
        t₂ (G₁.obj A) (G₂.obj A) (G₁.obj B) (G₂.obj B) (Z.hom.app A) (Z.hom.app B))
    (ht₂ : ∀ (X X' Y Y' : C₂) (u : X ⟶ X') (v : Y ⟶ Y'),
      t₂ X X' Y Y' u v ≫ (b₂ X' Y').hom =
        (b₂ X Y).hom ≫ t₂ Y Y' X X' v u)
    (hδ : ∀ A B : C₁, G₁.map (b₁ A B).hom ≫ δ B A =
      δ A B ≫ (b₂ (G₁.obj A) (G₁.obj B)).hom)
    (A B : C₁) :
    G₂.map (b₁ A B).hom ≫ h B A =
      h A B ≫ (b₂ (G₂.obj A) (G₂.obj B)).hom := by
  rw [hh A B, hh B A, ← Category.assoc (G₂.map (b₁ A B).hom), Z.inv.naturality (b₁ A B).hom]
  simp only [Category.assoc]
  rw [reassoc_of% (hδ A B),
    ht₂ (G₁.obj A) (G₂.obj A) (G₁.obj B) (G₂.obj B) (Z.hom.app A) (Z.hom.app B)]

end Stacks.SheafOfModules.TransportCoherence

/-! ### Naturality of the symmetry constraint of Tag 01CA -/

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The symmetry constraint of Tag 01CA is natural in its two arguments**, at the spelling in
which the tensor product of two morphisms is the action of
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor`.

Both the bifunctor and the constraint are the sheafification of the corresponding presheaf datum,
so this is the naturality of the braiding of the symmetric monoidal category of presheaves of
modules, carried along `Stacks.SheafOfModules.TensorSheafification.sheafify` by its
functoriality.  The presheaf braiding is where the monoidal notation is used, and there the
instance is unambiguous. -/
theorem tensorProductBraiding_naturality_bifunctorMap
    {A A' Bb Bb' : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (u : A ⟶ A') (v : Bb ⟶ Bb') :
    (tensorProductBifunctor O hO).map (X := (A, Bb)) (Y := (A', Bb')) (u, v) ≫
        (tensorProductBraiding O hO A' Bb').hom =
      (tensorProductBraiding O hO A Bb).hom ≫
        (tensorProductBifunctor O hO).map (X := (Bb, A)) (Y := (Bb', A')) (v, u) := by
  let : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        := by
    change MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    infer_instance
  let : BraidedCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        := by
    change BraidedCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    infer_instance
  change (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (u.val ⊗ₘ v.val) ≫
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (β_ A'.val Bb'.val).hom =
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (β_ A.val Bb.val).hom ≫
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (v.val ⊗ₘ u.val)
  rw [← Functor.map_comp, ← Functor.map_comp, BraidedCategory.braiding_naturality u.val v.val]

end Stacks.SheafOfModules.Invertible

/-! ### The symmetry constraint of the strict monoidal structure -/

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

section WithStrictInstance

attribute [local instance] monoidalUnderlyingRingSheaf braidedUnderlyingRingSheaf

/-- **The symmetry constraint of the strict monoidal structure is the fixed symmetry constraint
of Tag 01CA.**  Both are carried to the localized braiding by
`Stacks.SheafOfModules.tensorObjIso` — the first by
`Stacks.SheafOfModules.Strict.braiding_aux`, the second by
`Stacks.SheafOfModules.tensorObjIso_braiding` — and that comparison is an isomorphism, so the two
agree.  This is the companion of
`Stacks.SheafOfModules.Strict.associator_hom_eq_tensorProductAssociator`, and the spelling of the
ring sheaf is `Stacks.SheafOfModules.Tensor.ringSheaf`, the one the coherence
of Stacks 03EL is stated at. -/
theorem braiding_hom_eq_tensorProductBraiding (A B : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (β_ A B).hom =
      (tensorProductBraiding O.obj (isSheaf_structureRingPresheaf O) A B).hom :=
  (Iso.cancel_iso_hom_left (tensorObjIso O.obj (isSheaf_structureRingPresheaf O) A B) _ _).mp
    ((braiding_aux O.obj (isSheaf_structureRingPresheaf O) A B).trans
      (Stacks.SheafOfModules.tensorObjIso_braiding O.obj
        (isSheaf_structureRingPresheaf O) A B).symm)

end WithStrictInstance

end Stacks.SheafOfModules.Strict

/-! ### The braiding coherence of Tag 03EL, in the Tag 01CA vocabulary -/

namespace Stacks.SheafOfModules.RingedToposPullback

open _root_.AlgebraicGeometry (RingedTopos)
open _root_.Stacks.Sheaves.RingedToposModules (RingedToposHom)
open _root_.Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

variable {Xt : RingedTopos.{v, u, w}} {Yt : RingedTopos.{v', u', w'}}
  [Xt.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Yt.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Xt.J.HasSheafCompose (forget RingCat.{w})] [Yt.J.HasSheafCompose (forget RingCat.{w'})]
  [Xt.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Yt.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify Xt.J AddCommGrpCat.{w}] [Xt.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Yt.J AddCommGrpCat.{w'}] [Yt.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom Xt Yt)

/-- **The comparison of Stacks 03EL along an arbitrary morphism of ringed topoi is compatible
with the symmetry constraint of Tag 01CA**, with no hypothesis.  This is
`Stacks.SheafOfModules.RingedToposPullback.braiding` retyped out of the `β_` of
`Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf` into the `tensorProductBraiding`
vocabulary that Tag 01CA's coherences are stated with. -/
theorem pullbackTensorComparison_braiding'
    (F G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Yt.O)) :
    (pullbackModules f).map
          (tensorProductBraiding Yt.O.obj (isSheaf_structureRingPresheaf Yt.O) F G).hom ≫
        pullbackTensorComparison f G F =
      pullbackTensorComparison f F G ≫
        (tensorProductBraiding Xt.O.obj (isSheaf_structureRingPresheaf Xt.O)
          ((pullbackModules f).obj F) ((pullbackModules f).obj G)).hom := by
  have h := braiding f F G
  rw [Strict.braiding_hom_eq_tensorProductBraiding Yt.O,
    Strict.braiding_hom_eq_tensorProductBraiding Xt.O] at h
  exact h

end Stacks.SheafOfModules.RingedToposPullback

/-! ### The symmetry coherence of the associated-module functor -/

namespace AlgebraicGeometry.BigFppfOver

open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)
open Stacks.SheafOfModules.Invertible (tensorProductBifunctor)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison `AlgebraicGeometry.BigFppfOver.baseTensorComparison` of the pullback of modules
to `(Sch/S)_τ` is compatible with the symmetry constraint of Tag 01CA. -/
theorem baseTensorComparison_braiding (τ : SiteKind) (M N : S.Modules) :
    (basePullbackModules B S hS τ).map
          (tensorProductBraiding S.presheaf (zariskiStructureIsSheaf S) M N).hom ≫
        baseTensorComparison B S hS τ N M =
      baseTensorComparison B S hS τ M N ≫
        (tensorProductBraiding (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
          ((basePullbackModules B S hS τ).obj M)
          ((basePullbackModules B S hS τ).obj N)).hom :=
  Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_braiding'
    (baseRingedToposModulesHom B S hS τ) M N

/-- The comparison of `𝓕 ↦ 𝓕^a` is the conjugate of the comparison of the pullback by
`pullbackModulesIsoBaseAssociatedModule`, with the tensor product of the two components written
as an action of the bifunctor of Tag 0GMW rather than as
`Stacks.SheafOfModules.Invertible.tensorProductIso`. -/
theorem baseAssociatedModuleTensorIso'_hom' (τ : SiteKind) (M N : S.Modules) :
    (baseAssociatedModuleTensorIso' B S hS τ M N).hom =
      (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
              (zariskiStructureIsSheaf S)⟩).obj M).obj N)) ≫
        baseTensorComparison B S hS τ M N ≫
        (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2).map
          (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj N))
          (Y := ((baseAssociatedModule B S hS τ).obj M, (baseAssociatedModule B S hS τ).obj N))
          ((pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app M,
            (pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app N) :=
  baseAssociatedModuleTensorIso'_hom B S hS τ M N


/-- **The object-level tensor comparison of `𝓕 ↦ 𝓕^a` is compatible with the symmetry constraint
of Tag 01CA**, at every one of the five topologies and with no hypothesis on `S`.  This is the
third of the four data `Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor`
asks for, and the one that was unavailable while the braiding coherence of Tag 03EL was known
for a morphism of ringed spaces only.

It is `AlgebraicGeometry.BigFppfOver.baseTensorComparison_braiding`, the coherence for the
pullback of modules, transported along
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` by
`Stacks.SheafOfModules.TransportCoherence.transported_braiding`.  Every argument is supplied
already crossed into one spelling — `baseAssociatedModuleTensorIso'_hom'` for the conjugation and
`baseTensorComparison_braiding` for the coherence — because a term that leaves two of them to be
matched here exhausts the heartbeat budget at `whnf`, while each crossing on its own is cheap. -/
public theorem baseAssociatedModuleTensorIso'_braiding (τ : SiteKind) :
    Stacks.SheafOfModules.TensorPowerTransport.TensorIsoBraiding S.presheaf
      (zariskiStructureIsSheaf S) (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
      (baseAssociatedModule B S hS τ)
      (baseAssociatedModuleTensorIso' B S hS τ) :=
  fun A D =>
    Stacks.SheafOfModules.TransportCoherence.transported_braiding
      (pullbackModulesIsoBaseAssociatedModule B S hS τ)
      ((fun tensorLeft tensorRight => (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
          (zariskiStructureIsSheaf S)⟩).obj tensorLeft).obj tensorRight)))
      ((fun tensorLeft tensorRight => (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(baseRingedSite B S hS τ).O.obj,
          Presheaf.isSheaf_of_isSheaf_comp _ (baseRingedSite B S hS τ).O.obj
            (forget₂ CommRingCat RingCat)
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2⟩).obj
          tensorLeft).obj tensorRight)))
      (fun X X' Y Y' u v =>
        (tensorProductBifunctor (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2).map
            (X := (X, Y)) (Y := (X', Y')) (u, v))
      (tensorProductBraiding S.presheaf (zariskiStructureIsSheaf S))
      (tensorProductBraiding (baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2)
      (baseTensorComparison B S hS τ)
      (fun M N => (baseAssociatedModuleTensorIso' B S hS τ M N).hom)
      (baseAssociatedModuleTensorIso'_hom' B S hS τ)
      (fun _ _ _ _ u v =>
        Stacks.SheafOfModules.Invertible.tensorProductBraiding_naturality_bifunctorMap
          (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2 u v)
      (baseTensorComparison_braiding B S hS τ)
      A D

end AlgebraicGeometry.BigFppfOver

end
