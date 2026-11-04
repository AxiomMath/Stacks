module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineReconstruction

/-!
# Inverting the reconstruction pair

The conclusion of [Stacks, Tag 0GPJ] presents an equivalence `QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` as inverse
image along an isomorphism of schemes `f : Y ≅ X` followed by tensoring with an invertible sheaf
`L` of `𝒪_Y`-modules — in this repository
`AlgebraicGeometry.pullbackTensorFunctor f.hom L`, through
`AlgebraicGeometry.exists_schemeIso_invertibleSheaf_of_quasicoherentEquivalence`.  This file
proves that such a pair is **invertible in its own shape**: there is an invertible sheaf `L'` of
`𝒪_X`-modules — a tensor inverse of `(f^{-1})^*L` — for which the two twisted inverse images,
along `f.hom` with `L` and along `f.inv` with `L'`, are mutually inverse equivalences.

The statement is made about functors between the categories of **all** modules, because
`AlgebraicGeometry.pullbackTensorFunctor f.hom L` goes from the quasi-coherent modules on `X` to
all modules on `Y`, so two of them cannot be composed.
`AlgebraicGeometry.twistedPullback f L` is the same construction read on all modules, and
`AlgebraicGeometry.pullbackTensorFunctor f L` is, by definition, the inclusion of the
quasi-coherent modules followed by it (`AlgebraicGeometry.pullbackTensorFunctor_eq`).  The
composites in the shape the consumer meets are recorded in
`AlgebraicGeometry.exists_isInvertible_pullbackTensorFunctor_inverse`: the twisted inverse image
along `f.inv` cancels `pullbackTensorFunctor f.hom L` back to the inclusion, and symmetrically.

## Main definitions

* `AlgebraicGeometry.twistedPullback` — `M ↦ f^*M ⊗_{𝒪_Y} L`, on all modules.
* `AlgebraicGeometry.modulePullbackEquivalenceOfSchemeIso` — inverse image of modules along an
  isomorphism of schemes is an equivalence, with inverse image along the inverse as its
  quasi-inverse.
* `AlgebraicGeometry.tensorLeftFunctorCompModulePullback` — [Stacks, Tag 01CD] for inverse image
  of modules along a morphism of schemes.
* `AlgebraicGeometry.twistedPullbackCompIsoId` — the cancellation isomorphism itself.
* `Stacks.SheafOfModules.tensorLeftFunctorCompIsoId` — a trivialisation `B ⊗_O A ≅ O` makes the
  two tensor functors mutually inverse.
* `CategoryTheory.Functor.compIsoIdSwap` — if `F` is an equivalence and `F ⋙ G ≅ 𝟭`, then
  `G ⋙ F ≅ 𝟭`.

## Main results

* `AlgebraicGeometry.isInvertible_modulePullbackObj` — the inverse image of an invertible sheaf
  of modules along a morphism of schemes is invertible ([Stacks, Tag 0B8L] at the scheme level,
  in the spelling `AlgebraicGeometry.pullbackTensorFunctor` uses).
* `Stacks.SheafOfModules.isInvertible_of_tensorLeftFunctor_obj_iso_unit` — a tensor inverse of
  an invertible sheaf of modules is itself invertible.
* `AlgebraicGeometry.twistedPullback_isEquivalence` — `AlgebraicGeometry.twistedPullback f.hom L`
  is an equivalence for `f` an isomorphism and `L` invertible.
* `AlgebraicGeometry.exists_isInvertible_twistedPullback_inverse` — **the inversion statement**:
  for `f : Y ≅ X` and `L` invertible on `Y` there are an invertible sheaf `L'` on `X` and
  isomorphisms `twistedPullback f.hom L ⋙ twistedPullback f.inv L' ≅ 𝟭` and
  `twistedPullback f.inv L' ⋙ twistedPullback f.hom L ≅ 𝟭`, so the inverse of a reconstruction
  pair is again a reconstruction pair, for the inverse isomorphism of schemes.
* `AlgebraicGeometry.exists_isInvertible_pullbackTensorFunctor_inverse` — the same, read against
  `AlgebraicGeometry.pullbackTensorFunctor`.

## Implementation notes

**Where `L'` comes from.**  Inverse image of an invertible sheaf is invertible ([Stacks, Tag
0B8L], `Stacks.RingedSpace.modulePullback_isInvertible`), so `Lp = (f^{-1})^*L` is an invertible
sheaf of `𝒪_X`-modules and [Stacks, Tag 0B8K] supplies some `L'` with `Lp ⊗_{𝒪_X} L' ≅ 𝒪_X`.
Nothing says a priori that *that* `L'` is invertible, and the trivialisation comes in the wrong
order for the composite that has to be contracted — what is needed is the cancellation of
`tensorLeftFunctor Lp ⋙ tensorLeftFunctor L'`, and the trivialisation gives the other one.  Both
gaps are closed by the same observation: the trivialisation makes
`tensorLeftFunctor L' ⋙ tensorLeftFunctor Lp` isomorphic to the identity, hence an equivalence,
so `tensorLeftFunctor L'` is an equivalence by
`CategoryTheory.Functor.isEquivalence_of_comp_right` — which is invertibility of `L'` — and
`CategoryTheory.Functor.compIsoIdSwap` then turns the contraction around.  No braiding of the
tensor product sheaf, and no right unitor for it, is needed anywhere.

**Why the second composite is not proved twice.**  `twistedPullback f.hom L` is an equivalence,
being inverse image along an isomorphism followed by tensoring with an invertible sheaf, so
`CategoryTheory.Functor.compIsoIdSwap` derives
`twistedPullback f.inv L' ⋙ twistedPullback f.hom L ≅ 𝟭` from the other composite.  Proving it
by hand would need the trivialisation of `L'` pulled back along `f.hom`, which is the same
argument again.

**The `implicit_reducible` block.**  One object is named through two chains of definitions — the
structure sheaf of a scheme as `AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  The same list is
declared in `StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean` and in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalIso.lean` for the same reason.
Where invertibility is turned into an equivalence it is turned by the explicit
`Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence` rather than by instance
search, so that the chains do not have to be seen through at all.

**What this does not give.**  The composites are contracted to the identity of the categories of
*all* modules, not of the quasi-coherent ones: that would ask for `twistedPullback` to preserve
quasi-coherence, hence for an invertible sheaf of modules to be quasi-coherent, which this
repository does not prove.  The gluing step of [Stacks, Tag 0GPJ] does not need it; the
reconstruction data is compared after forgetting quasi-coherence there too.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Lemma 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Lemma 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Turning a one-sided cancellation around.**  If `F` is an equivalence and `F ⋙ G ≅ 𝟭`, then
`G ⋙ F ≅ 𝟭` as well.  The hypothesis identifies `G` with the quasi-inverse `F.inv`, and the
counit of `F.asEquivalence` is the required isomorphism. -/
def compIsoIdSwap {F : C ⥤ D} {G : D ⥤ C} [F.IsEquivalence] (h : F ⋙ G ≅ 𝟭 C) :
    G ⋙ F ≅ 𝟭 D :=
  have i : G ≅ F.inv :=
    G.leftUnitor.symm ≪≫ Functor.isoWhiskerRight F.asEquivalence.counitIso.symm G ≪≫
      Functor.associator F.inv F G ≪≫ Functor.isoWhiskerLeft F.inv h ≪≫ F.inv.rightUnitor
  Functor.isoWhiskerRight i F ≪≫ F.asEquivalence.counitIso

end CategoryTheory.Functor

namespace Stacks.SheafOfModules

universe v₀ u₀ w₀

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w₀})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w₀}] [HasWeakSheafify J AddCommGrpCat.{w₀}]

/-- **A trivialising tensor product makes the two tensor functors mutually inverse.**  If
`B ⊗_O A ≅ O`, then tensoring by `A` followed by tensoring by `B` is the identity functor.  The
two outer steps are `Stacks.SheafOfModules.tensorLeftFunctorObjIso`, which splits the tensor
functor of a tensor product, and `Stacks.SheafOfModules.tensorLeftSheafifyFunctorUnitIso`, which
contracts the tensor functor of the structure sheaf; the middle step transports along the
trivialisation. -/
def tensorLeftFunctorCompIsoId
    (A B : SheafOfModules.{w₀} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, w₀, w₀}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj B).obj A ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, w₀, w₀}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj A ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, w₀, w₀}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj B ≅
        𝟭 _ :=
  have h : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      ((SheafOfModules.forget
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map e.hom)) :=
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso
      ((SheafOfModules.forget
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).mapIso e)).isIso_hom
  (tensorLeftFunctorObjIso O hO B A).symm ≪≫
    tensorLeftSheafifyFunctorMapIso O hO
      ((SheafOfModules.forget
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map e.hom) h ≪≫
    tensorLeftSheafifyFunctorUnitIso O hO

/-- **A tensor inverse of an invertible sheaf of modules is invertible.**  If `B` is invertible
and `B ⊗_O A ≅ O`, then `A` is invertible: the trivialisation makes the composite of the two
tensor functors the identity, hence an equivalence, and a functor whose composite with an
equivalence is an equivalence is one. -/
theorem isInvertible_of_tensorLeftFunctor_obj_iso_unit
    (A B : SheafOfModules.{w₀} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hB : IsInvertible O hO B)
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, w₀, w₀}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj B).obj A ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    IsInvertible O hO A := by
  have hB' : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, w₀, w₀}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        B).IsEquivalence :=
    (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO B).mp hB
  have hcomp : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, w₀, w₀}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj A ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, w₀, w₀}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O
          (forget₂ CommRingCat RingCat) hO⟩).obj B).IsEquivalence :=
    Functor.isEquivalence_of_iso (tensorLeftFunctorCompIsoId O hO A B e).symm
  exact (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO A).mpr
    (Functor.isEquivalence_of_comp_right
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, w₀, w₀}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj A)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, w₀, w₀}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj B))

end Stacks.SheafOfModules

namespace AlgebraicGeometry

universe u

/- The `implicit_reducible` block of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean`; see the implementation
notes above. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-! ### Inverse image of modules along an isomorphism of schemes -/

/-- **Inverse image of modules along an isomorphism of schemes is an equivalence**, with inverse
image along the inverse isomorphism as its quasi-inverse.  The two units are the
pseudofunctoriality of inverse image (`AlgebraicGeometry.Scheme.Modules.pullbackComp`) composed
with the two identities of the isomorphism. -/
def modulePullbackEquivalenceOfSchemeIso {X Y : Scheme.{u}} (f : Y ≅ X) :
    X.Modules ≌ Y.Modules :=
  .mk (Scheme.Modules.pullback f.hom) (Scheme.Modules.pullback f.inv)
    ((Scheme.Modules.pullbackComp f.inv f.hom ≪≫
      Scheme.Modules.pullbackCongr f.inv_hom_id ≪≫ Scheme.Modules.pullbackId X).symm)
    (Scheme.Modules.pullbackComp f.hom f.inv ≪≫
      Scheme.Modules.pullbackCongr f.hom_inv_id ≪≫ Scheme.Modules.pullbackId Y)

/-- **Stacks Project, Tag 0B8L, for a morphism of schemes.**  The inverse image of an invertible
sheaf of modules is invertible.  This is `Stacks.RingedSpace.modulePullback_isInvertible` read for
the structure sheaf of a scheme and with the inverse image spelled as
`AlgebraicGeometry.Scheme.Modules.pullback`, which is the spelling
`AlgebraicGeometry.pullbackTensorFunctor` uses. -/
theorem isInvertible_modulePullbackObj {X Y : Scheme.{u}} (g : X ⟶ Y)
    (L : SheafOfModules.{u} Y.ringCatSheaf)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj L) :=
  @Stacks.RingedSpace.modulePullback_isInvertible _ _ g.toLRSHom.toShHom L hL

/-! ### The twisted inverse image on all modules -/

/-- **Inverse image along `f` followed by tensoring with a fixed sheaf `L` of `𝒪_Y`-modules**, as
a functor between the categories of all modules.  This is
`AlgebraicGeometry.pullbackTensorFunctor` with the quasi-coherence of the source dropped, which
is what makes two of them composable. -/
def twistedPullback {X Y : Scheme.{u}} (f : Y ⟶ X) (L : SheafOfModules.{u} Y.ringCatSheaf) :
    X.Modules ⥤ Y.Modules :=
  Scheme.Modules.pullback f ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
        (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj L

/-- `AlgebraicGeometry.pullbackTensorFunctor` is the inclusion of the quasi-coherent modules
followed by `AlgebraicGeometry.twistedPullback`.  Both sides are the same term. -/
theorem pullbackTensorFunctor_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : SheafOfModules.{u} Y.ringCatSheaf) :
    pullbackTensorFunctor f L =
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙ twistedPullback f L :=
  rfl

/-- **Stacks Project, Tag 01CD, for inverse image of modules along a morphism of schemes.**
Tensoring with `L` followed by inverse image along `g` is inverse image along `g` followed by
tensoring with `g^*L`.  This is `AlgebraicGeometry.tensorLeftFunctorCompPullback` for the
underlying morphism of ringed spaces. -/
def tensorLeftFunctorCompModulePullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (L : SheafOfModules.{u} Y.ringCatSheaf) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
          (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj L ⋙
      Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback g ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj
          ((Scheme.Modules.pullback g).obj L) :=
  tensorLeftFunctorCompPullback g.toLRSHom.toShHom X.ringCatSheaf.2 Y.ringCatSheaf.2 L

/-- **`AlgebraicGeometry.twistedPullback` along an isomorphism, with an invertible twist, is an
equivalence.** -/
theorem twistedPullback_isEquivalence {X Y : Scheme.{u}} (f : Y ≅ X)
    (L : SheafOfModules.{u} Y.ringCatSheaf)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    (twistedPullback f.hom L).IsEquivalence :=
  have : (Scheme.Modules.pullback f.hom).IsEquivalence :=
    (modulePullbackEquivalenceOfSchemeIso f).isEquivalence_functor
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
        (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj L).IsEquivalence :=
    (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence Y.presheaf
      Y.ringCatSheaf.2 L).mp hL
  ((Scheme.Modules.pullback f.hom).asEquivalence.trans
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
        (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj L).asEquivalence).isEquivalence_functor

/-! ### The cancellation isomorphism -/

/-- **The two twisted inverse images cancel.**  Let `f : Y ≅ X`, let `L` be a sheaf of
`𝒪_Y`-modules and let `L'` be a sheaf of `𝒪_X`-modules whose tensor functor cancels that of
`(f^{-1})^*L`.  Then `M ↦ (f^{-1})^*(f^*M ⊗_{𝒪_Y} L) ⊗_{𝒪_X} L'` is the identity functor.

Reading from the inside out: tensoring with `L` commutes past inverse image along `f.inv` at the
cost of replacing `L` by `(f^{-1})^*L`
(`AlgebraicGeometry.tensorLeftFunctorCompModulePullback`, Tag 01CD), the two inverse images then
compose to inverse image along `f.inv ≫ f.hom = 𝟙`
(`AlgebraicGeometry.Scheme.Modules.pullbackComp`), and the two tensor factors cancel by
hypothesis. -/
def twistedPullbackCompIsoId {X Y : Scheme.{u}} (f : Y ≅ X)
    (L : SheafOfModules.{u} Y.ringCatSheaf) (L' : SheafOfModules.{u} X.ringCatSheaf)
    (hT : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
              (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj
          ((Scheme.Modules.pullback f.inv).obj L) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj L' ≅ 𝟭 X.Modules) :
    twistedPullback f.hom L ⋙ twistedPullback f.inv L' ≅ 𝟭 X.Modules :=
  let P := Scheme.Modules.pullback f.hom
  let Q := Scheme.Modules.pullback f.inv
  let TY := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
      (forget₂ CommRingCat RingCat) Y.ringCatSheaf.2⟩).obj L
  let TX := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
      (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj L'
  let TXp := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
      (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj (Q.obj L)
  have hPQ : P ⋙ Q ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp f.inv f.hom ≪≫
      Scheme.Modules.pullbackCongr f.inv_hom_id ≪≫ Scheme.Modules.pullbackId X
  Functor.associator P TY (Q ⋙ TX) ≪≫
    Functor.isoWhiskerLeft P ((Functor.associator TY Q TX).symm ≪≫
      Functor.isoWhiskerRight (tensorLeftFunctorCompModulePullback f.inv L) TX ≪≫
      Functor.associator Q TXp TX) ≪≫
    (Functor.associator P Q (TXp ⋙ TX)).symm ≪≫
    Functor.isoWhiskerRight hPQ (TXp ⋙ TX) ≪≫
    Functor.leftUnitor (TXp ⋙ TX) ≪≫ hT

/-! ### The inversion statement -/

/-- **The inverse of a reconstruction pair is a reconstruction pair.**  Let `f : Y ≅ X` be an
isomorphism of schemes and let `L` be an invertible sheaf of `𝒪_Y`-modules.  Then there is an
invertible sheaf `L'` of `𝒪_X`-modules — a tensor inverse of `(f^{-1})^*L` — such that the two
twisted inverse images `M ↦ f^*M ⊗_{𝒪_Y} L` and `N ↦ (f^{-1})^*N ⊗_{𝒪_X} L'` are mutually
inverse equivalences.

So the functor inverting `AlgebraicGeometry.pullbackTensorFunctor f.hom L` is again of the shape
`AlgebraicGeometry.pullbackTensorFunctor f.inv L'` for an invertible `L'`, with the *inverse*
isomorphism of schemes; see
`AlgebraicGeometry.exists_isInvertible_pullbackTensorFunctor_inverse` for that reading. -/
theorem exists_isInvertible_twistedPullback_inverse {X Y : Scheme.{u}} (f : Y ≅ X)
    (L : SheafOfModules.{u} Y.ringCatSheaf)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    ∃ L' : SheafOfModules.{u} X.ringCatSheaf,
      Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L' ∧
        Nonempty (twistedPullback f.hom L ⋙ twistedPullback f.inv L' ≅ 𝟭 X.Modules) ∧
          Nonempty (twistedPullback f.inv L' ⋙ twistedPullback f.hom L ≅ 𝟭 Y.Modules) := by
  have hLp : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback f.inv).obj L) :=
    isInvertible_modulePullbackObj f.inv L hL
  obtain ⟨L', ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := X.ringCatSheaf.2)
    ((Scheme.Modules.pullback f.inv).obj L)).mp hLp
  -- `e : ((f^{-1})^*L) ⊗ L' ≅ 𝒪_X`, which is the order the trivialisation comes in.
  have hL' : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L' :=
    Stacks.SheafOfModules.isInvertible_of_tensorLeftFunctor_obj_iso_unit X.presheaf
      X.ringCatSheaf.2 L' ((Scheme.Modules.pullback f.inv).obj L) hLp e
  have hTX : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj L').IsEquivalence :=
    (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence X.presheaf
      X.ringCatSheaf.2 L').mp hL'
  have h1 : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj L' ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj
        ((Scheme.Modules.pullback f.inv).obj L) ≅
        𝟭 X.Modules :=
    Stacks.SheafOfModules.tensorLeftFunctorCompIsoId X.presheaf X.ringCatSheaf.2 L'
      ((Scheme.Modules.pullback f.inv).obj L) e
  -- Turned around, it contracts the composite in the order the functors compose.
  have hT : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj
        ((Scheme.Modules.pullback f.inv).obj L) ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj L' ≅ 𝟭 X.Modules :=
    Functor.compIsoIdSwap h1
  have hfwd : twistedPullback f.hom L ⋙ twistedPullback f.inv L' ≅ 𝟭 X.Modules :=
    twistedPullbackCompIsoId f L L' hT
  have hequiv : (twistedPullback f.hom L).IsEquivalence := twistedPullback_isEquivalence f L hL
  exact ⟨L', hL', ⟨hfwd⟩, ⟨Functor.compIsoIdSwap hfwd⟩⟩

/-- If `F ⋙ G ≅ 𝟭`, then precomposing with any functor `ι` gives `(ι ⋙ F) ⋙ G ≅ ι`. -/
private theorem nonempty_comp_comp_iso_of_comp_iso_id {A B C : Type*} [Category A] [Category B]
    [Category C] (ι : A ⥤ B) (F : B ⥤ C) (G : C ⥤ B) (h : F ⋙ G ≅ 𝟭 B) :
    Nonempty ((ι ⋙ F) ⋙ G ≅ ι) :=
  ⟨Functor.associator ι F G ≪≫ Functor.isoWhiskerLeft ι h ≪≫ Functor.rightUnitor ι⟩

/-- **The inversion statement read against `AlgebraicGeometry.pullbackTensorFunctor`.**  For
`f : Y ≅ X` and `L` invertible on `Y` there is an invertible sheaf `L'` of `𝒪_X`-modules such
that composing `AlgebraicGeometry.pullbackTensorFunctor f.hom L` with the twisted inverse image
along `f.inv` and `L'` recovers the inclusion of the quasi-coherent modules, and symmetrically
with the roles of `f.hom` and `f.inv` exchanged.

This is the form the gluing step of [Stacks, Tag 0GPJ] consumes: the mirror overlap compatibility
of `AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible` has to recognise the
inverse of a chart's reconstruction functor as a reconstruction functor for the inverse chart
map, which is what the two isomorphisms below say. -/
theorem exists_isInvertible_pullbackTensorFunctor_inverse {X Y : Scheme.{u}} (f : Y ≅ X)
    (L : SheafOfModules.{u} Y.ringCatSheaf)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    ∃ L' : SheafOfModules.{u} X.ringCatSheaf,
      Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L' ∧
        Nonempty (pullbackTensorFunctor f.hom L ⋙ twistedPullback f.inv L' ≅
          ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)) ∧
          Nonempty (pullbackTensorFunctor f.inv L' ⋙ twistedPullback f.hom L ≅
            ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) := by
  obtain ⟨L', hL', ⟨hfwd⟩, ⟨hbwd⟩⟩ := exists_isInvertible_twistedPullback_inverse f L hL
  exact ⟨L', hL', nonempty_comp_comp_iso_of_comp_iso_id _ _ _ hfwd,
    nonempty_comp_comp_iso_of_comp_iso_id _ _ _ hbwd⟩

end AlgebraicGeometry

end
