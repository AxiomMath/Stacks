module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerTransportTensorProduct
public import StacksFrontier.AlgebraicGeometry.Picard.BaseAssociatedModuleTensorNatural
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor

/-!
# Towards the further coherences of the tensor comparison of the associated-module functor

`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'` is Stacks 03EL at the morphism of
ringed sites `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, packaged as the object-level tensor comparison
`Stacks.SheafOfModules.Picard.TensorIso` of the associated-module functor `𝓕 ↦ 𝓕^a` of Stacks
03DU (4).  `StacksFrontier/AlgebraicGeometry/Picard/BaseAssociatedModuleTensorNatural.lean`
discharges its naturality,
`Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural`.  The transport of tensor powers of
a *tensor product* asks for three further data of the same kind — compatibility with the
associativity constraint, with the symmetry constraint and (together with the unit comparison)
with the right unit constraint of Tag 01CA.  This file collects the inputs those three reduce to,
and proves the ones available.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseTensorComparison`: the comparison of Stacks 03EL at that
  morphism, with its source and target ascribed at the tensor product sheaf of Tag 01CA rather
  than at the bifunctor of Tag 0GMW.

## Main results

* `Stacks.SheafOfModules.Strict.associator_hom_eq_tensorProductAssociator` and
  `rightUnitor_hom_eq_tensorProductRightUnitor`: **the two monoidal structures of Tag 01CA on
  sheaves of modules have the same associativity and right unit constraints** — the structural
  morphisms of `Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf`, which the coherence of
  Stacks 03EL is stated with, are the fixed constraints
  `Stacks.SheafOfModules.Invertible.tensorProductAssociator` and `tensorProductRightUnitor`,
  which Tag 01CA's coherences are stated with.
* `Stacks.SheafOfModules.Invertible.tensorProductAssociator_naturality`, in
  `StacksFrontier/AlgebraicGeometry/Picard/BaseAssociatedModuleCoherenceComplete.lean`: the
  associativity constraint of Tag 01CA is natural in its three arguments, at the bifunctor
  spelling of the tensor product.
* `Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison_associator`: **the
  comparison of Stacks 03EL along an arbitrary morphism of ringed topoi is compatible with the
  associativity constraint of Tag 01CA**, at the bifunctor spelling and with no hypothesis.  This
  is `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.associativity` retyped out of
  the whiskering-and-associator vocabulary of a `CategoryTheory.MonoidalCategory` instance into
  the `tensorProductAssociator` vocabulary of Tag 01CA.
* `Stacks.SheafOfModules.TransportCoherence.transported_associator`: **the associativity
  coherence transports along a natural isomorphism of functors**, as an identity of an abstract
  monoidal category: if `Z : G₁ ≅ G₂` and a comparison `δ` for `G₁` is compatible with the
  associator, then so is the comparison `Z⁻¹ ≫ δ ≫ (Z ⊗ Z)` for `G₂`.
* `AlgebraicGeometry.BigFppfOver.basePullbackCoherence`: the three coherences of Stacks 03EL at
  `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, at every one of the five topologies and with no hypothesis.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_hom`: the comparison of
  `𝓕 ↦ 𝓕^a` read as the composite of its three constituents, in the Tag 01CA spelling.

## Implementation notes

**Which coherence each reduces to.**  The compatibility of the comparison of `𝓕 ↦ 𝓕^a` with the
associativity constraint reduces to
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.associativity`, proved
unconditionally in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullbackCoherence.lean`, pasted with the
naturality of `AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` and the
naturality of the associativity constraint; the compatibility with the right unit constraint
reduces the same way to `PullbackCoherence.rightUnitality`.  Nothing in the repository proves the
compatibility of the comparison of Stacks 03EL with the *symmetry* constraint for a morphism of
ringed topoi; `Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding` is the statement
for a morphism of ringed *spaces* and for a different comparison, and `PullbackCoherence` has only
the three fields `associativity`, `leftUnitality` and `rightUnitality`.

**Why the paste is done as terms, and where it is done.**  The composites to reassociate straddle
three categories of sheaves of modules whose ring sheaves are spelled differently — the one of
the associated-module functor, the one of the pullback of modules, and the one of
`Stacks.SheafOfModules.Tensor.sheafTensor` — so a single composite carries two
`CategoryTheory.Category` instances that agree only at default transparency, and neither `rw` nor
`simp` nor `CategoryTheory.Category.assoc` will fire on it; this is the obstruction recorded in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Picard/BaseAssociatedModuleTensorNatural.lean`.  The paste is
therefore kept inside `Stacks.SheafOfModules.TransportCoherence.transported_associator`, which is
stated in an *abstract* monoidal category, where the objects carry no projections of a ringed
site and the monoidal lemmas do fire.  The source and target of every
`CategoryTheory.Functor.map` of a tensor bifunctor are given explicitly as `X :=` and `Y :=`, for
the reason recorded there.

**The two monoidal structures.**  Sheaves of modules carry two monoidal structures whose tensor
product is the tensor product sheaf of Tag 01CA on the nose:
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose constraints are the localized ones
conjugated by `Stacks.SheafOfModules.tensorObjIso`, and
`Stacks.SheafOfModules.sheafTensorMonoidal`, whose constraints are the fixed
`Stacks.SheafOfModules.Invertible.tensorProduct…` on the nose.  The coherence of Stacks 03EL is
stated at the first and Tag 01CA's coherences at the second, so the two have to be matched; that
is what the two bridge lemmas of `Stacks.SheafOfModules.Strict` do, each by one application of
the corresponding `…_eq_comparison` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalInduced.lean`.  Neither structure is left
to instance synthesis: the first is switched on by `attribute [local instance]` only inside the
section that needs it, and the second is never an instance here at all.

No `@[stacks]` attribute is claimed: Stacks 03EL is registered on
`Stacks.SheafOfModules.pullbackTensorIso` and its coherence on
`Stacks.SheafOfModules.RingedToposPullback.pullbackCoherence`; this module retypes and
instantiates them.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.SheafOfModules.Invertible (tensorProductIso tensorProductAssociator
  tensorProductBraiding tensorProductRightUnitor)
open Stacks.SheafOfModules.TensorEncodings (isSheaf_structureRingPresheaf)
open Stacks.SheafOfModules.RingedToposPullback (pullbackTensorComparison pullbackUnitComparison)

universe w w' v u v' u'

namespace Stacks.SheafOfModules.TransportCoherence

variable {C₁ : Type u} [Category.{v} C₁] [MonoidalCategory C₁]
  {C₂ : Type u'} [Category.{v'} C₂] [MonoidalCategory C₂]
  {G₁ G₂ : C₁ ⥤ C₂} (Z : G₁ ≅ G₂)
  (δ : ∀ A B : C₁, G₁.obj (A ⊗ B) ⟶ G₁.obj A ⊗ G₁.obj B)

/-- **The associativity coherence transports along a natural isomorphism of functors.**  Let
`Z : G₁ ≅ G₂` be an isomorphism of functors between monoidal categories and let
`δ A B : G₁(A ⊗ B) ⟶ G₁ A ⊗ G₁ B` be a comparison compatible with the associator (`hδ`).  Then
the comparison `h` of `G₂` obtained from `δ` by conjugating with `Z` (`hh`) is compatible with
the associator as well.  Stated in an abstract monoidal category, so that the monoidal lemmas
fire; the sheaf case is an instance of it. -/
theorem transported_associator
    (h : ∀ A B : C₁, G₂.obj (A ⊗ B) ⟶ G₂.obj A ⊗ G₂.obj B)
    (hh : ∀ A B : C₁, h A B =
      Z.inv.app (A ⊗ B) ≫ δ A B ≫ (Z.hom.app A ⊗ₘ Z.hom.app B))
    (hδ : ∀ A B D : C₁, G₁.map (α_ A B D).hom ≫ δ A (B ⊗ D) ≫
        (𝟙 (G₁.obj A) ⊗ₘ δ B D) =
      δ (A ⊗ B) D ≫ (δ A B ⊗ₘ 𝟙 (G₁.obj D)) ≫
        (α_ (G₁.obj A) (G₁.obj B) (G₁.obj D)).hom)
    (A B D : C₁) :
    G₂.map (α_ A B D).hom ≫ h A (B ⊗ D) ≫ (𝟙 (G₂.obj A) ⊗ₘ h B D) =
      h (A ⊗ B) D ≫ (h A B ⊗ₘ 𝟙 (G₂.obj D)) ≫
        (α_ (G₂.obj A) (G₂.obj B) (G₂.obj D)).hom := by
  simp only [hh, Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Iso.hom_inv_id_app_assoc, Category.comp_id]
  rw [← Category.assoc (G₂.map (α_ A B D).hom), Z.inv.naturality (α_ A B D).hom,
    Category.assoc, ← Category.assoc (Z.hom.app (A ⊗ B) ⊗ₘ Z.hom.app D),
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Iso.hom_inv_id_app_assoc, Category.comp_id]
  rw [show (Z.hom.app A ⊗ₘ δ B D ≫ (Z.hom.app B ⊗ₘ Z.hom.app D)) =
      (𝟙 (G₁.obj A) ⊗ₘ δ B D) ≫ (Z.hom.app A ⊗ₘ (Z.hom.app B ⊗ₘ Z.hom.app D)) from by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp],
    show ((δ A B ≫ (Z.hom.app A ⊗ₘ Z.hom.app B)) ⊗ₘ Z.hom.app D) =
      (δ A B ⊗ₘ 𝟙 (G₁.obj D)) ≫ ((Z.hom.app A ⊗ₘ Z.hom.app B) ⊗ₘ Z.hom.app D) from by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp],
    reassoc_of% (hδ A B D),
    ← MonoidalCategory.associator_naturality (Z.hom.app A) (Z.hom.app B) (Z.hom.app D)]
  simp only [Category.assoc]

end Stacks.SheafOfModules.TransportCoherence

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

variable {A A' B B' D D' : SheafOfModules.{w}
  (Stacks.SheafOfModules.Tensor.ringSheaf O)}

section WithStrictInstance

attribute [local instance] monoidalUnderlyingRingSheaf

/-- **The associativity constraint of the strict monoidal structure is the fixed associativity
constraint of Tag 01CA.**  One application of
`Stacks.SheafOfModules.tensorProductAssociator_eq_comparison`, at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the ring sheaf, which is
the spelling the coherence of Stacks 03EL is stated at. -/
theorem associator_hom_eq_tensorProductAssociator (A B D : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (α_ A B D).hom =
      (tensorProductAssociator O.obj (isSheaf_structureRingPresheaf O) A B D).hom :=
  (Stacks.SheafOfModules.tensorProductAssociator_eq_comparison O.obj
    (isSheaf_structureRingPresheaf O) A B D).symm

/-- **The right unit constraint of the strict monoidal structure is the fixed right unit
constraint of Tag 01CA.**  The two differ in the shape
`CategoryTheory.Monoidal.InducingFunctorData` asks the constraint in — a tensor of two identity
isomorphisms — and `Stacks.SheafOfModules.Strict.rightUnitor_hom_aux` removes it. -/
theorem rightUnitor_hom_eq_tensorProductRightUnitor (A : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (ρ_ A).hom = (tensorProductRightUnitor O.obj (isSheaf_structureRingPresheaf O) A).hom :=
  ((Stacks.SheafOfModules.tensorProductRightUnitor_eq_comparison O.obj
    (isSheaf_structureRingPresheaf O) A).trans
      (rightUnitor_hom_aux O.obj (isSheaf_structureRingPresheaf O) A)).symm

end WithStrictInstance

/-- **The tensor product sheaf of two isomorphisms is the action of the bifunctor of Tag 0GMW on
the pair**, by `rfl`.  It is what lets a coherence written with
`Stacks.SheafOfModules.Invertible.tensorProductIso` be read as one written with the bifunctor. -/
theorem tensorProductIso_hom_eq_tensorSheafBifunctor_map (e : A ≅ A') (f : B ≅ B') :
    (tensorProductIso O.obj (isSheaf_structureRingPresheaf O) e f).hom =
      (Stacks.SheafOfModules.Invertible.tensorProductBifunctor O.obj
          (isSheaf_structureRingPresheaf O)).map
        (X := (A, B)) (Y := (A', B')) (e.hom, f.hom) :=
  rfl


end Stacks.SheafOfModules.Strict

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

set_option maxHeartbeats 1600000 in
/-- **The comparison of Stacks 03EL along an arbitrary morphism of ringed topoi is compatible
with the associativity constraint of Tag 01CA**, with no hypothesis, at the
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor` spelling of the tensor product of two
morphisms and with the two sheaf conditions as *explicit arguments*.

Taking the sheaf conditions as arguments is what makes this usable at a ringed site, where the
structure sheaf arrives as `Stacks.SheafOfModules.Tensor.ringSheaf` of the site's own `O` and its
sheaf condition is therefore not the term
`Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf`
produces.  The two are definitionally equal, and each individual factor of the square crosses
between them by `rfl`, but an instantiation asked to discover that while matching all six
factors at once exceeds the recursion limit; one which receives the caller's own sheaf condition
matches every factor on the nose.

This is `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.associativity` retyped out
of the whiskering-and-associator vocabulary of
`Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf`.  Each rewrite is given its arguments
explicitly: left as patterns they are matched against objects at the
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` index and do not fire.

The two whiskerings are carried across in one step each:
`Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map` states a whiskering as the
curried action of `Stacks.SheafOfModules.Tensor.sheafTensor`, and
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map` identifies that curried action with the
sheafification of a tensor product of morphisms, which is
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor` on the pair by `rfl`. -/
theorem pullbackTensorComparison_associator
    (hOX : Presheaf.IsSheaf Xt.J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Xt.O.obj))
    (hOY : Presheaf.IsSheaf Yt.J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Yt.O.obj))
    (F G H : _root_.SheafOfModules.{w'}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf Yt.O.obj hOY)) :
    (pullbackModules f).map (tensorProductAssociator Yt.O.obj hOY F G H).hom ≫
        pullbackTensorComparison f F
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Yt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Yt.O.obj (forget₂ CommRingCat RingCat)
              hOY⟩).obj G).obj H)) ≫
        (Invertible.tensorProductBifunctor Xt.O.obj hOX).map
          (X := ((pullbackModules f).obj F, (pullbackModules f).obj
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨Yt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Yt.O.obj (forget₂ CommRingCat RingCat)
                hOY⟩).obj G).obj H))))
          (Y := ((pullbackModules f).obj F, (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨Xt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Xt.O.obj (forget₂ CommRingCat RingCat)
                hOX⟩).obj ((pullbackModules f).obj G)).obj ((pullbackModules f).obj H))))
          (𝟙 ((pullbackModules f).obj F), pullbackTensorComparison f G H) =
      pullbackTensorComparison f ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Yt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Yt.O.obj (forget₂ CommRingCat RingCat)
            hOY⟩).obj F).obj G)) H ≫
        (Invertible.tensorProductBifunctor Xt.O.obj hOX).map
          (X := ((pullbackModules f).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨Yt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Yt.O.obj (forget₂ CommRingCat RingCat)
                hOY⟩).obj F).obj G)), (pullbackModules f).obj H))
          (Y := ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨Xt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Xt.O.obj (forget₂ CommRingCat RingCat)
                hOX⟩).obj ((pullbackModules f).obj F)).obj ((pullbackModules f).obj G)),
              (pullbackModules f).obj H))
          (pullbackTensorComparison f F G, 𝟙 ((pullbackModules f).obj H)) ≫
        (tensorProductAssociator Xt.O.obj hOX ((pullbackModules f).obj F)
          ((pullbackModules f).obj G) ((pullbackModules f).obj H)).hom := by
  have h := (pullbackCoherence f).associativity F G H
  have hL : ((Stacks.SheafOfModules.Tensor.sheafTensor Xt.O).map
          (𝟙 ((pullbackModules f).obj F))).app ((pullbackModules f).obj
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨Yt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Yt.O.obj (forget₂ CommRingCat RingCat)
                hOY⟩).obj G).obj H))) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Xt.O).obj ((pullbackModules f).obj F)).map
          (pullbackTensorComparison f G H) =
      (Invertible.tensorProductBifunctor Xt.O.obj hOX).map
        (X := ((pullbackModules f).obj F, (pullbackModules f).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Yt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Yt.O.obj (forget₂ CommRingCat RingCat)
              hOY⟩).obj G).obj H))))
        (Y := ((pullbackModules f).obj F, (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Xt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Xt.O.obj (forget₂ CommRingCat RingCat)
              hOX⟩).obj ((pullbackModules f).obj G)).obj ((pullbackModules f).obj H))))
        (𝟙 ((pullbackModules f).obj F), pullbackTensorComparison f G H) :=
    Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Xt.O
      (𝟙 ((pullbackModules f).obj F)) (pullbackTensorComparison f G H)
  have hR : ((Stacks.SheafOfModules.Tensor.sheafTensor Xt.O).map
          (pullbackTensorComparison f F G)).app ((pullbackModules f).obj H) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Xt.O).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Xt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Xt.O.obj (forget₂ CommRingCat RingCat)
              hOX⟩).obj ((pullbackModules f).obj F)).obj ((pullbackModules f).obj G))).map
          (𝟙 ((pullbackModules f).obj H)) =
      (Invertible.tensorProductBifunctor Xt.O.obj hOX).map
        (X := ((pullbackModules f).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Yt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Yt.O.obj (forget₂ CommRingCat RingCat)
              hOY⟩).obj F).obj G)), (pullbackModules f).obj H))
        (Y := ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Xt.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Xt.O.obj (forget₂ CommRingCat RingCat)
              hOX⟩).obj ((pullbackModules f).obj F)).obj ((pullbackModules f).obj G)),
            (pullbackModules f).obj H))
        (pullbackTensorComparison f F G, 𝟙 ((pullbackModules f).obj H)) :=
    Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Xt.O
      (pullbackTensorComparison f F G) (𝟙 ((pullbackModules f).obj H))
  rw [Strict.whiskerLeft_eq_tensorSheafBifunctor_map Xt.O ((pullbackModules f).obj F)
      (pullbackTensorComparison f G H),
    Strict.whiskerRight_eq_tensorSheafBifunctor_map Xt.O (pullbackTensorComparison f F G)
      ((pullbackModules f).obj H),
    Strict.associator_hom_eq_tensorProductAssociator Yt.O F G H,
    Strict.associator_hom_eq_tensorProductAssociator Xt.O ((pullbackModules f).obj F)
      ((pullbackModules f).obj G) ((pullbackModules f).obj H)] at h
  rw [← hL, ← hR]
  exact h

end Stacks.SheafOfModules.RingedToposPullback

namespace AlgebraicGeometry.BigFppfOver

open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The three coherences of Tag 03EL at the morphism. -/
public theorem basePullbackCoherence (τ : SiteKind) :
    Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.{u, u, u, u + 1, u, u}
      (baseRingedToposModulesHom B S hS τ) :=
  Stacks.SheafOfModules.RingedToposPullback.pullbackCoherence
    (baseRingedToposModulesHom B S hS τ)

/-- Stacks 03EL at `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, with source and target spelled by the
tensor product sheaf of Tag 01CA. -/
public def baseTensorComparison (τ : SiteKind) (M N : S.Modules) :
    (basePullbackModules B S hS τ).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
            (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj M).obj N)) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(baseRingedSite B S hS τ).O.obj, Presheaf.isSheaf_of_isSheaf_comp _
          (baseRingedSite B S hS τ).O.obj (forget₂ CommRingCat RingCat)
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2⟩).obj
        ((basePullbackModules B S hS τ).obj M)).obj ((basePullbackModules B S hS τ).obj N)) :=
  (Stacks.SheafOfModules.pullbackTensorIso
    (baseRingedToposModulesHom B S hS τ)).hom.app (M, N)

/-- **The comparison of `𝓕 ↦ 𝓕^a` read as the composite of its three constituents**, in the
Tag 01CA spelling: the inverse of the identification of `𝓕 ↦ 𝓕^a` with the pullback of modules,
the comparison of Stacks 03EL for that pullback, and the identification again in each argument,
the last one written as a tensor product sheaf of two isomorphisms rather than as an action of
the bifunctor of Tag 0GMW.  This is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso_hom`; the crossing of the two
spellings happens here, once, inside a defeq-tolerant `:=`. -/
public theorem baseAssociatedModuleTensorIso'_hom (τ : SiteKind) (M N : S.Modules) :
    (baseAssociatedModuleTensorIso' B S hS τ M N).hom =
      (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
              (forget₂ CommRingCat RingCat) (zariskiStructureIsSheaf S)⟩).obj M).obj N)) ≫
        baseTensorComparison B S hS τ M N ≫
        (tensorProductIso (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
          ((pullbackModulesIsoBaseAssociatedModule B S hS τ).app M)
          ((pullbackModulesIsoBaseAssociatedModule B S hS τ).app N)).hom := by
  have hb : (tensorSheafBifunctorBase B S hS τ).map
        (X := ((basePullbackModules B S hS τ).obj M, (basePullbackModules B S hS τ).obj N))
        (Y := ((baseAssociatedModule B S hS τ).obj M, (baseAssociatedModule B S hS τ).obj N))
        ((pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app M,
          (pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app N) =
      (tensorProductIso (baseRingedSite B S hS τ).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
          ((pullbackModulesIsoBaseAssociatedModule B S hS τ).app M)
          ((pullbackModulesIsoBaseAssociatedModule B S hS τ).app N)).hom :=
    Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map (baseRingedSite B S hS τ).O
      ((pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app M)
      ((pullbackModulesIsoBaseAssociatedModule B S hS τ).hom.app N)
  rw [← hb]
  exact baseAssociatedModuleTensorIso_hom B S hS τ M N

end AlgebraicGeometry.BigFppfOver

end
