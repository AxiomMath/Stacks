module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertible sheaves of modules and dual pairings

Let `O` be a sheaf of commutative rings on a site. A sheaf of `O`-modules `L` is *invertible*
when tensoring by it is an equivalence of the category of `O`-modules
(`Stacks.SheafOfModules.IsInvertible`), and *trivial* when it is isomorphic to `O` itself.

This file supplies the criterion by which invertibility is actually recognized: a *dual pairing*.
Given a second sheaf of modules `N` and two morphisms of presheaves of modules
`N.val ⊗ L.val ⟶ O` and `L.val ⊗ N.val ⟶ O` which become isomorphisms after sheafification, the
sheafified tensor functor of `L` is an equivalence with quasi-inverse the one of `N`. Conversely
an invertible sheaf carries such a pairing, so invertibility of `L` is the same as the existence of
a sheaf of modules `N` with `L ⊗_O N ≅ O`; that equivalence is Stacks Tag 0B8K (1) ⟺ (2).

## Main definitions

* `Stacks.SheafOfModules.IsTrivial`: a sheaf of modules isomorphic to the structure sheaf. This is
  the "trivial" clause of [Stacks, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS); the
  "invertible" clause is `Stacks.SheafOfModules.IsInvertible`, in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`.
* `Stacks.SheafOfModules.tensorLeftSheafifyFunctorMapIso`: a morphism of presheaves of modules
  which sheafification inverts induces an isomorphism of the associated sheafified tensor functors.
* `Stacks.SheafOfModules.tensorLeftSheafifyFunctorUnitIso`: tensoring by the unit presheaf and
  sheafifying is the identity functor.
* `Stacks.SheafOfModules.tensorLeftFunctorEquivalenceOfPairing`: the equivalence of categories
  produced by a dual pairing.

## Main results

* `Stacks.SheafOfModules.isInvertible_of_pairing`: a sheaf of modules carrying a dual pairing is
  invertible.
* `Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`: **Tag 0B8K (1) ⟺ (2)**, `L` is
  invertible if and only if there is a sheaf of modules `N` with `L ⊗_O N ≅ O`.
* `Stacks.SheafOfModules.isInvertible_unit` and `Stacks.SheafOfModules.isInvertible_of_isTrivial`:
  the structure sheaf, and more generally any trivial sheaf of modules, is invertible.

## Implementation notes

The site, ring and module universes are those of Stacks Tag 05NA: the site
objects and morphisms live in independent universes `u` and `v`, while the ring and module
sections share the universe `w`, as Mathlib's monoidal structure on presheaves of modules
requires. Nothing here relates `w` to the size of the site, so no statement is specialized to a
particular universe.

There is no `MonoidalCategory (SheafOfModules R)` instance in the pinned Mathlib, so the tensor
product of sheaves of modules is not available as a monoidal structure, and the theory of
invertible objects of a monoidal category (Tags 0FFM and 0FFN, in
`StacksFrontier/CategoryTheory/Monoidal/InvertibleObject.lean`) cannot be instantiated here. Instead
every tensor product is the sheafification of the pointwise tensor product of presheaves of
modules, and the three facts that
make this behave monoidally are the ones Tag 05NA proves: sheafification inverts its own unit, and
the class of morphisms it inverts is stable under tensoring on either side
(`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify`,
  `Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft`,
`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight`). Consequently the
  pairings in
`isInvertible_of_pairing` are morphisms of *presheaves* of modules required to be invertible only
*after* sheafification, which is the weakest hypothesis the argument uses and the one that a local
trivialization supplies.

Both orders of the tensor product occur, because the two composites of an equivalence and its
quasi-inverse do; the symmetry that relates them is Mathlib's symmetric monoidal structure on
presheaves of modules, transported to the index `(structureSheaf O hO).obj` alongside the monoidal
structure and exposed as `braidingVal`.

This file does *not* prove Tag 0B8M, which asserts that a finite locally free sheaf of modules of
rank one is invertible, and conversely when all stalks of the structure sheaf are local rings.
Through `isInvertible_iff_exists_tensor_iso_unit` the unconditional direction is reduced to
exhibiting the dual `SheafHom(L, O)` together with its evaluation pairing, and that needs an
internal hom for sheaves of modules: the pinned Mathlib has no `MonoidalClosed` structure on
`PresheafOfModules` and no construction of the sheaf `SheafHom`, which Stacks Tag 01CO's
`SheafHom` structure carries as unconstructed data. No declaration here carries
the `@[stacks 0B8M]` attribute.

**That disclaims the "rank one ⇒ invertible" direction only, and must not be read as "Tag 0B8M
is unavailable in this repository".** The **converse** — an invertible sheaf of modules on a
ringed space with local stalks is locally free of rank one — **is** proved, as
`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible` and
`Stacks.SheafOfModules.exists_nonempty_linearEquiv_of_isInvertible` in
`StacksFrontier/AlgebraicGeometry/InvertibleTrivialization/Basic.lean`, with a `Scheme` form
where local-ringness of the stalks is automatic. It needs **no finiteness on the stalk** and no
internal hom: the stalk pairing exhibits the stalk as an invertible module over the local ring
directly, and an invertible module over a local ring is already free of rank one, so neither
Nakayama nor `SheafHom` is used. When citing what is available, name the direction.

## References

* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local instance] monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))

/-- A sheaf of `O`-modules is *trivial* when it is isomorphic, as an `O`-module, to `O` itself. -/
-- NO `stacks 01CS "trivial"` ATTRIBUTE HERE, DELIBERATELY. Tag 01CS's `trivial` note is
-- registered on `AlgebraicGeometry.SheafOfModules.IsTrivial`
-- (`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`:230), which states the same thing over
-- the same structure sheaf; this one does not claim it a second time.
abbrev IsTrivial (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
  O hO)) : Prop :=
  Nonempty (L ≅ SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
    hO))

attribute [local instance] symmetricCategoryPresheafOfModules

/-- The braiding of the underlying presheaves of two sheaves of `O`-modules. -/
noncomputable def braidingVal (L N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    N.val ⊗ L.val ≅ L.val ⊗ N.val :=
  β_ N.val L.val

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheafifying the underlying presheaf of a sheaf of modules recovers it: the counit of the
sheafification adjunction is an isomorphism. -/
noncomputable def forgetSheafifyIso :
    SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      Stacks.SheafOfModules.TensorSheafification.sheafify O hO ≅ 𝟭 _ := by
  have h : ((SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
    ⋙
        PresheafOfModules.restrictScalars (𝟙
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)) ⋙
      PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        O hO).obj)) ≅ 𝟭 _ :=
    asIso (PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) (𝟙 _)).counit
  exact h

/-- Sheafification inverts a composite as soon as it inverts both factors. -/
theorem isIso_sheafify_map_comp
    {A B D : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj} (f : A ⟶ B) (g : B ⟶ D)
    (hf : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f))
    (hg : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map g)) :
    IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (f ≫ g)) := by
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- Sheafification inverts the underlying presheaf morphism of an isomorphism of sheaves. -/
private theorem isIso_sheafify_map_forget_map_hom
    {L N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (e : L ≅ N) :
    IsIso ((TensorSheafification.sheafify O hO).map
      ((SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map e.hom)) :=
  ((TensorSheafification.sheafify O hO).mapIso
    ((SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).mapIso e)).isIso_hom

/-- A morphism of presheaves of modules which sheafification inverts induces an isomorphism of the
associated sheafified tensor functors, because the class of morphisms inverted by sheafification
is stable under tensoring on the right (Tag 05NA).

The underlying natural transformation is `Stacks.SheafOfModules.tensorLeftSheafifyFunctorMap`,
which exists for an arbitrary morphism of the left factor; all this adds is that each of its
components is an isomorphism. -/
noncomputable def tensorLeftSheafifyFunctorMapIso
    {A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj} (f : A ⟶ B)
    (hf : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f)) :
    (SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj A ⋙
      TensorSheafification.sheafify O hO) ≅
    (SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj B ⋙
      TensorSheafification.sheafify O hO) :=
  let β := tensorLeftSheafifyFunctorMap O hO f
  have h : ∀ F, IsIso (β.app F) := fun F =>
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight O hO f F.val hf
  NatIso.ofComponents (fun F => @asIso _ _ _ _ (β.app F) (h F)) fun g => β.naturality g

/-- The isomorphism is the natural transformation of
`Stacks.SheafOfModules.tensorLeftSheafifyFunctorMap`. -/
theorem tensorLeftSheafifyFunctorMapIso_hom
    {A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj} (f : A ⟶ B)
    (hf : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f)) :
    (tensorLeftSheafifyFunctorMapIso O hO f hf).hom = tensorLeftSheafifyFunctorMap O hO f := rfl

/-- Tensoring by the unit presheaf and sheafifying is the identity functor: the left unitor
identifies the presheaf tensor product with the underlying presheaf, and sheafifying that returns
the sheaf. -/
noncomputable def tensorLeftSheafifyFunctorUnitIso :
    (SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj
        (𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj)) ⋙
      TensorSheafification.sheafify O hO) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight
      (NatIso.ofComponents
        (F := SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
          (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj
            (𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj)))
        (G := SheafOfModules.forget (TensorSheafification.structureSheaf O hO))
        (fun moduleSheaf => by
          change PresheafOfModules.tensorObj (O := O)
            (𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj))
              moduleSheaf.val ≅ moduleSheaf.val
          exact λ_ moduleSheaf.val)
        (fun {source target} morphism => by
          change PresheafOfModules.tensorHom (𝟙 _) morphism.val ≫ (λ_ target.val).hom =
            (λ_ source.val).hom ≫ morphism.val
          apply PresheafOfModules.tensorObj_hom_ext
          intro openSet ringSection moduleSection
          letI : Module (O.obj openSet) (source.val.obj openSet) :=
            (source.val.obj openSet).isModule
          letI : Module (O.obj openSet) (target.val.obj openSet) :=
            (target.val.obj openSet).isModule
          change (λ_ target.val).hom.app openSet
              ((PresheafOfModules.tensorHom (𝟙 _) morphism.val).app openSet
                (ringSection ⊗ₜ moduleSection)) =
            morphism.val.app openSet ((λ_ source.val).hom.app openSet
              (ringSection ⊗ₜ moduleSection))
          refine (congrArg ((λ_ target.val).hom.app openSet)
            (PresheafOfModules.tensorHom_tmul (O := O)
              (𝟙 (𝟙_ (PresheafOfModules.{w}
                (TensorSheafification.structureSheaf O hO).obj))) morphism.val openSet
              ringSection moduleSection)).trans ?_
          change (ModuleCat.Hom.hom (R := O.obj openSet)
              (leftUnitor (C := ModuleCat.{w} (O.obj openSet)) (target.val.obj openSet)).hom)
              (ringSection ⊗ₜ[O.obj openSet] morphism.val.app openSet moduleSection) =
            morphism.val.app openSet ((ModuleCat.Hom.hom (R := O.obj openSet)
              (leftUnitor (C := ModuleCat.{w} (O.obj openSet)) (source.val.obj openSet)).hom)
                (ringSection ⊗ₜ[O.obj openSet] moduleSection))
          exact (ModuleCat.MonoidalCategory.leftUnitor_hom_apply (R := O.obj openSet) _ _).trans
            (((morphism.val.app openSet).hom.map_smul ringSection moduleSection).symm.trans
              (congrArg (morphism.val.app openSet)
                (ModuleCat.MonoidalCategory.leftUnitor_hom_apply (R := O.obj openSet)
                  ringSection moduleSection)).symm)))
      (TensorSheafification.sheafify O hO) ≪≫
    forgetSheafifyIso O hO

variable {O hO}

/-- A dual pairing for `L` and `N` — a pair of morphisms of presheaves of modules
`N.val ⊗ L.val ⟶ O` and `L.val ⊗ N.val ⟶ O` which sheafification inverts — exhibits the
sheafified tensor functor of `L` as an equivalence, with quasi-inverse that of `N`. -/
noncomputable def tensorLeftFunctorEquivalenceOfPairing
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (ev : N.val ⊗ L.val ⟶ 𝟙_ _) (ev' : L.val ⊗ N.val ⟶ 𝟙_ _)
    (hev : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map ev))
    (hev' : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map ev')) :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  .mk ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L)
    ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N)
    ((tensorLeftSheafifyFunctorTensorIso O hO N.val L.val).symm ≪≫
      tensorLeftSheafifyFunctorMapIso O hO ev hev ≪≫
        tensorLeftSheafifyFunctorUnitIso O hO).symm
    ((tensorLeftSheafifyFunctorTensorIso O hO L.val N.val).symm ≪≫
      tensorLeftSheafifyFunctorMapIso O hO ev' hev' ≪≫
        tensorLeftSheafifyFunctorUnitIso O hO)

/-- A sheaf of modules carrying a dual pairing is invertible. This is the categorical content of
Tag 0B8K: the only geometric input is a pairing of presheaves of modules which becomes an
isomorphism after sheafification. -/
theorem isInvertible_of_pairing
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (ev : N.val ⊗ L.val ⟶ 𝟙_ _) (ev' : L.val ⊗ N.val ⟶ 𝟙_ _)
    (hev : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map ev))
    (hev' : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map ev')) :
    IsInvertible O hO L :=
  (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO L).mpr
    (tensorLeftFunctorEquivalenceOfPairing L N ev ev' hev hev').isEquivalence_functor

/-- **Stacks Project, Tag 0B8K and Tag 0B8N, (1) ⟺ (2).** A sheaf of `O`-modules `L` is invertible
if and only if there is a sheaf of `O`-modules `N` whose tensor product with `L` is isomorphic
to `O`.

For the forward implication the tensor functor of `L` is an equivalence, so `O` has a preimage `N`
under it, and the universal property identifies the image of that preimage with `L ⊗_O N`. For the
converse the isomorphism `L ⊗_O N ≅ O` is turned into a pairing of presheaves of modules by
composing with the sheafification unit, and `isInvertible_of_pairing` applies.

Tag 0B8K states this for a ringed space and Tag 0B8N for an arbitrary ringed site; the statement
here is the one on a ringed site, so it carries both. -/
@[stacks 0B8K "(1) ⟺ (2)", stacks 0B8N "(1) ⟺ (2)"]
theorem isInvertible_iff_exists_tensor_iso_unit
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    IsInvertible O hO L ↔ ∃ N : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
      Nonempty (((Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L).obj N ≅
        SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) := by
  constructor
  · rintro ⟨F, hF, ⟨a⟩⟩
    let := hF
    refine ⟨F.inv.obj (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)), ⟨?_⟩⟩
    exact ((a.uniqueIso (tensorLeftFunctorUniversal O hO L)).symm.app _) ≪≫
      F.asEquivalence.counitIso.app (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  · rintro ⟨N, ⟨e⟩⟩
    have h1 : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (L.val ⊗ N.val))) :=
      Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO _
    have h2 := isIso_sheafify_map_forget_map_hom O hO e
    have h3 := isIso_sheafify_map_comp O hO _ _ h1 h2
    have h4 : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (braidingVal O
      hO L N).hom) := inferInstance
    exact isInvertible_of_pairing L N _ _ (isIso_sheafify_map_comp O hO _ _ h4 h3) h3

end Sheafification

section Trivial

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

variable {O hO}

/-- A trivial sheaf of modules is invertible. This is the globally trivial case of Tag 0B8M; the
locally trivial case, which is what that tag asserts, is not proved here — see the implementation
notes. -/
theorem isInvertible_of_isTrivial
    {L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (hL :
      IsTrivial O hO L) :
    IsInvertible O hO L := by
  refine (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO L).mpr ?_
  refine (Functor.isEquivalence_iff_of_iso (tensorLeftSheafifyFunctorMapIso O hO
    ((SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map
      hL.some.hom)
    (isIso_sheafify_map_forget_map_hom O hO hL.some) ≪≫
      tensorLeftSheafifyFunctorUnitIso O hO).symm).mp ?_
  exact Functor.isEquivalence_refl

variable (O hO)

/-- The structure sheaf, viewed as a module over itself, is invertible. -/
instance isInvertible_unit :
    IsInvertible O hO (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :=
  isInvertible_of_isTrivial ⟨Iso.refl _⟩

end Trivial

end Stacks.SheafOfModules

end
