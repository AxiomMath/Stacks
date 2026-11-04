module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransportCommRing
public import StacksFrontier.Homology.KFlat.BifunctorTransportEquivalence

/-!
# The derived tensor product transported along an equivalence of ringed sites

Let `e : C' ≌ C` be an equivalence of categories which is an equivalence of sites for topologies
`J'` on `C'` and `J` on `C`, and let `𝒪` be a sheaf of commutative rings on `(C, J)`.
`Stacks.SheafOfModules.reindexEquivalence` is the induced equivalence of the categories of
sheaves of modules and `Stacks.SheafOfModules.reindexCommRingGeneral` the transported structure
sheaf.
This file carries the **derived** tensor product across that equivalence:

`Φ(K ⊗^𝐋_𝒪 L) ≅ Φ K ⊗^𝐋_{𝒪|_{C'}} Φ L`

for `Φ` the reindexing of modules, on arbitrary objects `K`, `L` of `D(𝒪)` and naturally in both
of them.

## Why the abelian comparison is the only input

`CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence` asks for nothing beyond the
comparison of the *abelian*-level tensor products together with its two naturality squares: along
an equivalence its two K-flatness hypotheses are free, because an acyclic complex of the target
is the image of an acyclic complex of the source, and the total complex of the transported
bicomplex is produced from the comparison as well.  So this file supplies the abelian comparison
in the shape the engine consumes and reads off the derived one.

The abelian comparison is `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso`, [Stacks,
Tag 01CU]: the reindexing is the pushforward of sheaves of modules along `e.functor`, which is
continuous and cocontinuous, and that is exactly the hypothesis of the whiskering comparison.
Nothing is reproved and no comparison is named again — the two naturality squares are
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality` with one of its two
morphisms the identity, which is the shape the engine wants, and the isomorphism itself is passed
to the engine at its own spelling.  Three identifications make that possible and each is `rfl`:

* `Stacks.SheafOfModules.reindexRing J' e (ringSheaf 𝒪)` is
  `ringSheaf (Stacks.SheafOfModules.reindexCommRingGeneral J' e 𝒪)`, where `ringSheaf` is
  `Stacks.SheafOfModules.Tensor.ringSheaf`;
* `Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪.obj _` is `ringSheaf 𝒪`, and the
  same with `e.functor.op ⋙ 𝒪.obj` in place of `𝒪.obj` is the transported one;
* `(reindexEquivalence e (ringSheaf 𝒪)).functor` *is*
  `Stacks.SheafOfModules.TensorPower.whiskerRestriction`, both being the pushforward of sheaves
  of modules along `e.functor` with the identity comparison of structure sheaves.

The tensor product itself needs no identification:
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` is stated at
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is the spelling the derived tensor product is
formed at here.

This is the same route as
`StacksFrontier/AlgebraicGeometry/Duality/GorensteinSchemes/OverEquivInvertible.lean`, which runs it
at the one equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv U`; what is added here is the
statement for an arbitrary equivalence of ringed sites, which is what a consumer comparing two
presentations of one site needs.

## Main definitions

* `Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod`: the reindexing equivalence of
  module categories, with both categories named at the tensor product's spelling.
* `Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexDerivedTensorNatIso`: **the derived
  tensor product transported along the equivalence**, as an isomorphism of bifunctors on the
  derived categories.
* `Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexDerivedTensorObjIso`: its value at a
  pair of objects.

## Main results

* `Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod_functor_eq_whiskerRestriction`:
  the `rfl` on which the whole file rests.
* `Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.isInvertible_of_isInvertible_reindexMod`
  and `isInvertible_reindexMod_of_isInvertible`: invertibility of an object of the derived
  category is reflected and preserved by the reindexing, from the same inputs.

## Implementation notes

**The two sites' object and morphism universes are independent of each other**, which is what
the comparison of the small étale site of a scheme with its `Type u` model,
`AlgebraicGeometry.SmallEtale.smallModelRingedTopos`, needs: that site has its objects one
universe above its morphisms and the model has them in one universe.  Both
`Stacks.SheafOfModules.reindexEquivalence` and
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` are universe-independent already, and
the transported structure sheaf is the only input that was not: it is stated beside
`Stacks.SheafOfModules.reindexRing` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SiteEquivalenceTransport.lean`, the module whose
subject is the universe-independent transport, as
`Stacks.SheafOfModules.reindexCommRingGeneral`.  Its same-universe reading
`Stacks.SheafOfModules.reindexCommRing` stays in
`StacksFrontier/AlgebraicGeometry/Topologies/SiteEquivalenceTensor.lean`, where the same-universe
development that consumes it lives.  The sections of the structure sheaf and of the modules live
in a further independent universe, and the derived categories' hom universe is independent of all
of them; the underived transport of [Stacks, Tag 03EL] along an equivalence,
`Stacks.SheafOfModules.reindexTensorIso`, is still pinned to equal object universes.

The four K-flat localization hypotheses of the engine are carried as instance arguments rather
than discharged, because asking for them is the weaker hypothesis.  They hold whenever every
complex of modules has a K-flat resolution, and at the universes here the resolutions are the
instances `Stacks.DerivedTensor.RingedSite.kFlatLocalizer_hasLeftResolutions` and
`Stacks.DerivedTensor.RingedSite.kFlatLocalizerLeft_hasLeftResolutions`, so wherever those are
imported instance search discharges all four.

No comparison is named for the abelian level: `Stacks.SheafOfModules.reindexTensorIso` is the
transport of [Stacks, Tag 03EL] along this very equivalence, and naming a second
isomorphism with the same content at the `Stacks.SheafOfModules.Tensor.sheafTensor` spelling
would be a duplicate.  The engine is handed `whiskerTensorSheafIso` directly, its type matching
by the `rfl`s listed above.

No `@[stacks]` attribute is claimed.  [Stacks, Tag 06YU] is registered on
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` and on
`Stacks.DerivedTensor.derivedTensorSheaf`, and [Stacks, Tag 01CU] on the whiskering comparison;
this is one transport of those along one equivalence.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe d w v' u' v u

namespace Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [e.functor.IsCocontinuous J' J]
  (O : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-! ### The reindexing equivalence, with both categories named once -/

/-- **The reindexing equivalence of the categories of sheaves of modules**, with both of its
categories named at the spelling the tensor product uses.

This is `Stacks.SheafOfModules.reindexEquivalence` and nothing else — the target's two namings
are equal by `rfl` — but it is the naming at which the transport engine's instance arguments can
be stated.  Handing `reindexEquivalence` to the engine directly produces an additivity goal
whose source category is named one way, by the tensor bifunctor, and whose target the other, by
the equivalence; no instance exists at that mixed naming.  The same fix is applied to
`AlgebraicGeometry.Scheme.Modules.overEquiv` in
`Stacks.SheafOfModules.OverEquivTensor.overEquivMod`. -/
abbrev reindexMod : _root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O) ≌
    _root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O)) :=
  reindexEquivalence.{w, w, u, v, u', v'} e (Tensor.ringSheaf.{u, v, w} O)

omit [e.functor.IsCocontinuous J' J] [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J' AddCommGrpCat.{w}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The functor of the reindexing equivalence is restriction along the functor of sites
`e.functor`**, on the nose.  Both are the pushforward of sheaves of modules along `e.functor`
with the identity comparison of structure sheaves: `reindexEquivalence` goes through
`SheafOfModules.pushforwardPushforwardEquivalence`, whose comparison it supplies as `𝟙`.

This is the identification the tensor comparison below is read through. -/
theorem reindexMod_functor_eq_whiskerRestriction :
    (reindexMod J' e O).functor =
      TensorPower.whiskerRestriction (J' := J') O.obj (Tensor.ringSheaf.{u, v, w} O).property
        e.functor :=
  rfl

/-- The functor of the reindexing equivalence is additive, at the tensor product's naming of the
two categories.  It is a pushforward of sheaves of modules, hence the identity on the underlying
maps of sheaves. -/
instance reindexMod_functor_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
      (reindexMod J' e O).functor where
  map_add := by intros; rfl

/-- The inverse of the reindexing equivalence is additive, at the tensor product's naming of the
two categories.  See
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod_functor_additive`. -/
instance reindexMod_inverse_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
      (reindexMod J' e O).inverse where
  map_add := by intros; rfl

/-- **The whiskering comparison is natural in the first variable.**  This is
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality` with the second morphism the
identity, the two tensored identities removed by `CategoryTheory.Functor.map_id`.  The engine
below asks for the square in this shape, with no identity left in it.

`Stacks.SheafOfModules.OverEquivTensor.overEquivTensorIso_naturality_left` is the same square,
and is proved the same way, for the single equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv
U` at equal object universes.  This one is for an arbitrary equivalence of ringed sites with the
two site universes and the sections universe independent, which is what the transport below
needs; neither statement is an instance of the other. -/
theorem reindexTensorIso_naturality_left
    {A A' : _root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)} (f : A ⟶ A')
    (N : _root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)) :
    (reindexMod J' e O).functor.map (((Tensor.sheafTensor.{u, v, w} O).map f).app N) ≫
        (TensorPower.whiskerTensorSheafIso (J' := J') O.obj
          (Tensor.ringSheaf.{u, v, w} O).property e.functor A' N).hom =
      (TensorPower.whiskerTensorSheafIso (J' := J') O.obj
          (Tensor.ringSheaf.{u, v, w} O).property e.functor A N).hom ≫
        ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).map
          ((reindexMod J' e O).functor.map f)).app ((reindexMod J' e O).functor.obj N) := by
  have naturality :
      (reindexMod J' e O).functor.map
            (((Tensor.sheafTensor.{u, v, w} O).map f).app N ≫
              ((Tensor.sheafTensor.{u, v, w} O).obj A').map (𝟙 N)) ≫
          (TensorPower.whiskerTensorSheafIso (J' := J') O.obj
            (Tensor.ringSheaf.{u, v, w} O).property e.functor A' N).hom =
        (TensorPower.whiskerTensorSheafIso (J' := J') O.obj
            (Tensor.ringSheaf.{u, v, w} O).property e.functor A N).hom ≫
          ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).map
              ((reindexMod J' e O).functor.map f)).app ((reindexMod J' e O).functor.obj N) ≫
            ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).obj
              ((reindexMod J' e O).functor.obj A')).map
                ((reindexMod J' e O).functor.map (𝟙 N)) :=
    TensorPower.whiskerTensorSheafIso_naturality (J' := J') O.obj
      (Tensor.ringSheaf.{u, v, w} O).property e.functor f (𝟙 N)
  have expand : (reindexMod J' e O).functor.map
          (((Tensor.sheafTensor.{u, v, w} O).map f).app N) =
        (reindexMod J' e O).functor.map
          (((Tensor.sheafTensor.{u, v, w} O).map f).app N ≫
            ((Tensor.sheafTensor.{u, v, w} O).obj A').map (𝟙 N)) := by
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have collapse :
      ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).map
              ((reindexMod J' e O).functor.map f)).app ((reindexMod J' e O).functor.obj N) ≫
            ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).obj
              ((reindexMod J' e O).functor.obj A')).map
                ((reindexMod J' e O).functor.map (𝟙 N)) =
          ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).map
              ((reindexMod J' e O).functor.map f)).app
                ((reindexMod J' e O).functor.obj N) := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [expand, naturality]
  exact congrArg _ collapse

/-- **The whiskering comparison is natural in the second variable.**  See
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexTensorIso_naturality_left`. -/
theorem reindexTensorIso_naturality_right
    (M : _root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O))
    {B B' : _root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)} (g : B ⟶ B') :
    (reindexMod J' e O).functor.map (((Tensor.sheafTensor.{u, v, w} O).obj M).map g) ≫
        (TensorPower.whiskerTensorSheafIso (J' := J') O.obj
          (Tensor.ringSheaf.{u, v, w} O).property e.functor M B').hom =
      (TensorPower.whiskerTensorSheafIso (J' := J') O.obj
          (Tensor.ringSheaf.{u, v, w} O).property e.functor M B).hom ≫
        ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).obj
          ((reindexMod J' e O).functor.obj M)).map
            ((reindexMod J' e O).functor.map g) := by
  have naturality :
      (reindexMod J' e O).functor.map
            (((Tensor.sheafTensor.{u, v, w} O).map (𝟙 M)).app B ≫
              ((Tensor.sheafTensor.{u, v, w} O).obj M).map g) ≫
          (TensorPower.whiskerTensorSheafIso (J' := J') O.obj
            (Tensor.ringSheaf.{u, v, w} O).property e.functor M B').hom =
        (TensorPower.whiskerTensorSheafIso (J' := J') O.obj
            (Tensor.ringSheaf.{u, v, w} O).property e.functor M B).hom ≫
          ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).map
              ((reindexMod J' e O).functor.map (𝟙 M))).app
                ((reindexMod J' e O).functor.obj B) ≫
            ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).obj
              ((reindexMod J' e O).functor.obj M)).map
                ((reindexMod J' e O).functor.map g) :=
    TensorPower.whiskerTensorSheafIso_naturality (J' := J') O.obj
      (Tensor.ringSheaf.{u, v, w} O).property e.functor (𝟙 M) g
  have expand : (reindexMod J' e O).functor.map
          (((Tensor.sheafTensor.{u, v, w} O).obj M).map g) =
        (reindexMod J' e O).functor.map
          (((Tensor.sheafTensor.{u, v, w} O).map (𝟙 M)).app B ≫
            ((Tensor.sheafTensor.{u, v, w} O).obj M).map g) := by
    rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  have collapse :
      ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).map
              ((reindexMod J' e O).functor.map (𝟙 M))).app
                ((reindexMod J' e O).functor.obj B) ≫
            ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).obj
              ((reindexMod J' e O).functor.obj M)).map
                ((reindexMod J' e O).functor.map g) =
          ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).obj
              ((reindexMod J' e O).functor.obj M)).map
                ((reindexMod J' e O).functor.map g) := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp]
  rw [expand, naturality]
  exact congrArg _ collapse

/-! ### The comparison on the derived categories -/

section Derived

variable
  [(Tensor.sheafTensor.{u, v, w} O).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, v, w} O).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Tensor.sheafTensor.{u, v, w} O) (ComplexShape.up ℤ)]
  [(Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).Additive]
  [∀ M, ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).obj M).Additive]
  [∀ (K L : CochainComplex
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O))]
  [HasDerivedCategory.{d}
    (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O)))]
  [(kFlatQLeft (Tensor.sheafTensor.{u, v, w} O)).IsLocalization
    (kFlatQuasiIsoLeft (Tensor.sheafTensor.{u, v, w} O))]
  [(kFlatQ (Tensor.sheafTensor.{u, v, w} O)).IsLocalization
    (kFlatQuasiIso (Tensor.sheafTensor.{u, v, w} O))]
  [(kFlatQLeft (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O))).IsLocalization
    (kFlatQuasiIsoLeft (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)))]
  [(kFlatQ (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O))).IsLocalization
    (kFlatQuasiIso (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)))]

/-- **The derived tensor product transported along an equivalence of ringed sites**, as an
isomorphism of bifunctors on the derived categories:

`Φ(K ⊗^𝐋_𝒪 L) ≅ Φ K ⊗^𝐋_{𝒪|_{C'}} Φ L`

for `Φ` the reindexing of sheaves of modules along `e`.

This is `CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence`, whose only input is the
abelian-level comparison with its two naturality squares: here
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` — [Stacks, Tag 01CU], the compatibility
of restriction along a continuous and cocontinuous functor of sites with the tensor product of
sheaves of modules — and `whiskerTensorSheafIso_naturality` with one morphism the identity. -/
def reindexDerivedTensorNatIso :
    derivedTransportSource (Tensor.sheafTensor.{u, v, w} O) (reindexMod J' e O).functor ≅
      derivedTransportTarget (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O))
        (reindexMod J' e O).functor (reindexMod J' e O).functor :=
  derivedTransportIsoOfEquivalence (Tensor.sheafTensor.{u, v, w} O)
    (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u, v, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g)

/-- **`Φ(K ⊗^𝐋_𝒪 L) ≅ Φ K ⊗^𝐋_{𝒪|_{C'}} Φ L`** at a pair of objects of the derived categories,
read off `Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexDerivedTensorNatIso`.  Unlike
a comparison produced at chosen K-flat representatives this is the value of a natural
isomorphism, so it commutes with morphisms in each variable. -/
def reindexDerivedTensorObjIso
    (K L : DerivedCategory (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O))) :
    (reindexMod J' e O).functor.mapDerivedCategory.obj
        (((derivedBifunctor (Tensor.sheafTensor.{u, v, w} O)).obj K).obj L) ≅
      ((derivedBifunctor (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O))).obj
          ((reindexMod J' e O).functor.mapDerivedCategory.obj K)).obj
        ((reindexMod J' e O).functor.mapDerivedCategory.obj L) :=
  ((reindexDerivedTensorNatIso J' e O).app K).app L

/-- **The reindexing reflects invertibility on the derived categories**, with the two monoidal
structures as explicit arguments, each identified by a pairwise comparison of its tensor product
with the derived tensor bifunctor of [Stacks, Tag 06YU], and `unitε` identifying the images of
the units: if `Φ K` is an invertible object of `D(𝒪|_{C'})` then `K` is an invertible object of
`D(𝒪)`.

This is `CochainComplex.KFlatBifunctor.isInvertible_of_isInvertible_mapDerivedCategory` at the
reindexing equivalence; no coherence of the comparison and no monoidal structure on the functor
is used. -/
theorem isInvertible_of_isInvertible_reindexMod
    (mC : MonoidalCategory
      (DerivedCategory (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O))))
    (mC' : MonoidalCategory (DerivedCategory
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O)))))
    (bC : letI := mC; BraidedCategory
      (DerivedCategory (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O))))
    (cmpC : letI := mC; ∀ A B : DerivedCategory
        (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)),
      A ⊗ B ≅ ((derivedBifunctor (Tensor.sheafTensor.{u, v, w} O)).obj A).obj B)
    (cmpC' : letI := mC'; ∀ A B : DerivedCategory
        (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O))),
      A ⊗ B ≅ ((derivedBifunctor
        (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O))).obj A).obj B)
    (unitε : letI := mC; letI := mC';
      (reindexMod J' e O).functor.mapDerivedCategory.obj
          (𝟙_ (DerivedCategory (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)))) ≅
        𝟙_ (DerivedCategory (_root_.SheafOfModules.{w}
          (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O)))))
    (K : DerivedCategory (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)))
    (hK : letI := mC'; MonoidalCategory.IsInvertible
      ((reindexMod J' e O).functor.mapDerivedCategory.obj K)) :
    letI := mC; MonoidalCategory.IsInvertible K :=
  isInvertible_of_isInvertible_mapDerivedCategory (Tensor.sheafTensor.{u, v, w} O)
    (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u, v, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g)
    mC mC' bC cmpC cmpC' unitε K hK

/-- **The reindexing preserves invertibility on the derived categories**, the companion of
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.isInvertible_of_isInvertible_reindexMod` in
the forward direction, with the braiding asked of the target rather than of the source: if `K` is
an invertible object of `D(𝒪)` then `Φ K` is an invertible object of `D(𝒪|_{C'})`.

This is `CochainComplex.KFlatBifunctor.isInvertible_mapDerivedCategory_of_isInvertible`.  Along an
equivalence both directions are available from the same inputs, and a consumer carrying an object
*onto* the reindexed site needs this one. -/
theorem isInvertible_reindexMod_of_isInvertible
    (mC : MonoidalCategory
      (DerivedCategory (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O))))
    (mC' : MonoidalCategory (DerivedCategory
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O)))))
    (bC' : letI := mC'; BraidedCategory (DerivedCategory
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O)))))
    (cmpC : letI := mC; ∀ A B : DerivedCategory
        (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)),
      A ⊗ B ≅ ((derivedBifunctor (Tensor.sheafTensor.{u, v, w} O)).obj A).obj B)
    (cmpC' : letI := mC'; ∀ A B : DerivedCategory
        (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O))),
      A ⊗ B ≅ ((derivedBifunctor
        (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O))).obj A).obj B)
    (unitε : letI := mC; letI := mC';
      (reindexMod J' e O).functor.mapDerivedCategory.obj
          (𝟙_ (DerivedCategory (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)))) ≅
        𝟙_ (DerivedCategory (_root_.SheafOfModules.{w}
          (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O)))))
    (K : DerivedCategory (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)))
    (hK : letI := mC; MonoidalCategory.IsInvertible K) :
    letI := mC'; MonoidalCategory.IsInvertible
      ((reindexMod J' e O).functor.mapDerivedCategory.obj K) :=
  isInvertible_mapDerivedCategory_of_isInvertible (Tensor.sheafTensor.{u, v, w} O)
    (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u, v, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g)
    mC mC' bC' cmpC cmpC' unitε K hK

end Derived

end Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

end
