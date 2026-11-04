module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatIsFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekSumResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.TensorProduct
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0961 for a quasi-compact quasi-separated scheme

Stacks Tag 0961 asks nothing of the scheme: for **any** scheme `X`, any Noetherian ring `Λ` and
any `K, L ∈ D_c^-(X_étale, Λ)`, the derived tensor product `K ⊗_Λ^L L` is again in
`D_c^-(X_étale, Λ)` — it is bounded above and all of its cohomology sheaves are constructible.

This file proves that statement for a **quasi-compact quasi-separated** `X`, by the source's own
argument, from the flat constructible representative of Tag 0960 (1) ⟹ (3). Compactness and
quasi-separatedness are hypotheses the tag does not have, and they enter only through Tag 0960, so
the tag is not registered here: it is registered on
`Stacks.EtaleCohomology.minus_and_isConstructible_derivedTensor_of_arbitraryScheme`, which asks
nothing of the scheme. Neither the boundedness estimate for the derived tensor product nor the
bounded case of the tag is assumed.

## Main definitions

* `Stacks.EtaleCohomology.IsDerivedTensorOnFlatComplexes` — the hypothesis identifying a
  bifunctor on `D(X_étale, Λ)` as the derived tensor product: its value on a pair of complexes
  whose right member is a bounded above complex of flat sheaves is the total tensor complex.

## Main results

* `Stacks.EtaleCohomology.exists_isStrictlyLE_isConstructibleModuleSheaf_derivedTensor` — the
  engine: `K ⊗_Λ^L L` is represented by a bounded above complex of constructible sheaves of
  `Λ`-modules, namely the total tensor complex of two flat constructible representatives.
* `Stacks.EtaleCohomology.minus_and_isConstructible_derivedTensor_of_flat` — **both halves of the
  conclusion of Tag 0961**, for a quasi-compact quasi-separated scheme.

## The argument

The source's proof is "this follows from Lemmas 0960 and 095I", and that is the proof here.

By Tag 0960, the implication (1) ⟹ (3) —
`Stacks.EtaleCohomology.isRepresentedByBoundedAboveConstructibleFlatComplex_of_isConstructible`
— each of `K` and `L` is represented by a bounded above complex of *flat constructible* sheaves
of `Λ`-modules, say `P` in degrees `≤ p` and `G` in degrees `≤ q`. A bounded above complex of
flat sheaves computes the derived tensor product as the ordinary total tensor complex, so

`K ⊗_Λ^L L ≅ Tot(P ⊗_Λ G)`.

That complex is bounded above by `p + q`, by
`Stacks.ConstantSheaf.isStrictlyLE_mapBifunctor`: a summand `P^a ⊗_Λ G^b` of its term in a
degree `n > p + q` has `a > p` or `b > q`, so one factor vanishes. That is the first half of the
conclusion.

Its term in degree `n` is a finite direct sum of the sheaves `P^a ⊗_Λ G^b`, by
`Stacks.ConstantSheaf.prop_mapBifunctor_of_isStrictlyLE`. Each `P^a` and each `G^b` is
constructible, being flat constructible
(`AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf`), so each
summand is constructible by Tag 095I,
`Stacks.EtaleCohomology.isConstructibleModuleSheaf_tensor`, and the finite direct sum is
constructible because Tag 03RZ (3) is a weak Serre condition,
`AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty`. A complex of
constructible sheaves has constructible cohomology sheaves, again by that weak Serre property:
`Stacks.EtaleCohomology.isConstructible_of_forall_isConstructibleModuleSheaf`. That is the
second half.

## What is assumed of the derived tensor product, and what is not

The derived tensor product enters as a bifunctor `T` on `D(X_étale, Λ)` together with the
hypothesis `Stacks.EtaleCohomology.IsDerivedTensorOnFlatComplexes`: the value of `T` at the classes
of two cochain complexes is the class of their total tensor complex whenever the right factor is a
bounded above complex of flat sheaves. This is not a result about `K ⊗^L_Λ L`; it is what
*identifies* `T` as the derived tensor product, and it is the `comparisonRight` field of
`Stacks.SheafOfModules.DerivedTensorProduct` — restricted to the bounded above complexes of flat
sheaves, which Tag 06YQ puts among the K-flat ones — read in the category in which constructibility
is a property of an object. In particular `T` is not assumed exact in either variable.

Flatness of a sheaf of `Λ`-modules is this development's notion of it: flatness of the sheaf of
modules over the constant coefficient ring sheaf which the sheaf determines, as in
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`.
That theorem is what supplies the hypothesis of `IsDerivedTensorOnFlatComplexes` for the
representatives Tag 0960 produces — the flat constructible sheaves of its condition (3) are
local constancy with finite projective values on strata, not a flatness predicate, and that
theorem is the bridge.

The tensor product itself is `AlgebraicGeometry.SmallEtale.moduleSheafMonoidal`, the monoidal
structure `CategoryTheory.Sheaf.monoidalCategory` of Tags 093V, 095D and 095I: the sheafification
of the objectwise tensor product over `Λ`. The three standing hypotheses on it —
additivity in each variable and the existence of total complexes — are the ones the derived
tensor product carries everywhere in this development, as in
`Stacks.SheafOfModules.DerivedTensorProduct`; they are what makes `Tot(P ⊗_Λ G)` exist and say
nothing about constructibility.

## Why `X` is quasi-compact and quasi-separated

The source states Tag 0961 for an arbitrary scheme, and its proof cites Tag 0960, which is
stated — in the source and here — for a quasi-compact quasi-separated scheme: the flat
constructible representative is produced by a descending induction whose steps rest on Tag 095Z
and on the compactness of a constructible sheaf, Tag 095P. That restriction on Tag 0960 is not an
artefact: its conditions (2) and (3) present a complex by *finite* direct sums of the generators
`j_{U!}Λ-underline`, and on a scheme which is not quasi-compact a constructible sheaf need not be
a quotient of a finite such sum.

So the passage to an arbitrary scheme does not go through a flat *constructible* representative.
It goes through a flat one: the generators `j_{U!}Λ-underline` have projective étale stalks, flat
étale stalks pass to an arbitrary coproduct, and Tag 05T7 therefore resolves any bounded above
object by a bounded above complex whose terms have flat étale stalks, hence are flat over the
constant coefficient ring sheaf. That is
`AlgebraicGeometry.exists_isStrictlyLE_flat_etaleModuleStalk_of_isLE` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FlatEtaleStalks`, and it is
what makes `Stacks.EtaleCohomology.IsDerivedTensorOnFlatComplexes` say something over an
arbitrary scheme. With it, `K ⊗^L_Λ L` *is* a single total tensor complex, so there is no
representative to compare and no further property of `T` to assume; the bound is the sum of the
two bounds, and only constructibility has to be localized. The three localization facts that
costs are:

1. **Constructibility of the cohomology sheaves is Zariski local, with no hypothesis on `X`.**
   `AlgebraicGeometry.isConstructibleModuleSheaf_of_openCover` is Tag 095F for modules over a
   Noetherian ring and asks only that the images of a family of open immersions cover `X`;
   `AlgebraicGeometry.exists_affine_openCover_of_bigEtaleSite` supplies such a family of affine
   objects of `B`; and the degree-`i` cohomology sheaf of a restriction is the restriction of the
   degree-`i` cohomology sheaf, for the exact inverse image.
2. **The bound is global and needs no localization.** Membership in
   `CategoryTheory.Triangulated.TStructure.minus` is the existence of *one* bound valid in every
   degree, and an affine open cover of a scheme which is not quasi-compact is infinite, so bounds
   read off the members need not be bounded — but none has to be: the bound `a + b` comes from
   the two global representatives, by `Stacks.ConstantSheaf.isStrictlyLE_mapBifunctor`. The bound
   `p + q` of the statement below, which comes from
   `Stacks.EtaleCohomology.IsRepresentedByBoundedAboveConstructibleFlatComplex` and is
   existentially quantified there, is not the one used.
3. **The formation of the total tensor complex commutes with restriction to an open.** The
   comparison of sheaves is `AlgebraicGeometry.smallEtaleSheafPullbackTensorIso`, the small étale
   instance of `Stacks.InverseImageTensor.sheafPullbackTensorIso`; its two naturality squares are
   `AlgebraicGeometry.smallEtaleSheafPullbackTensorIso_naturality_left` and `_right` in
   `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.TensorProductNaturality`,
   and `CategoryTheory.Functor.mapBifunctorTotalIso` transports them to the total complex, which
   is `Stacks.EtaleCohomology.smallEtaleSheafPullbackMapBifunctorIso` in
   `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.TotalTensorRestriction`.

On the quasi-compact quasi-separated members of the cover the constructibility of the cohomology
of that total complex is then obtained without changing representatives inside the derived
category: Tag 0960 (1) ⟹ (2) presents each factor by an actual *morphism* of complexes from one
with finite affine shriek sums as terms, and the induced map of total complexes is a
quasi-isomorphism because a bounded above complex with flat étale stalks is K-flat on either
side, which is Tag 06YQ in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.TotalTensorKFlat`.

## The coefficient universe

The coefficient ring is `Λ : Type (max (u + 1) w)` with modules in `ModuleCat.{max (u + 1) w} Λ`,
which is the universe of Tag 095I: the small étale site of Tag 021B has objects in
`Type (u + 1)` and morphisms in `Type u`, and `ModuleCat.{s} Λ` is monoidal only for
`Λ : Type s`, so the tensor product of sheaves of `Λ`-modules exists only once the module
universe contains `u + 1` and the ring universe agrees with it. At that universe Tag 0960 is
available — its coefficient universe `max (u + 1) r` is `max (u + 1) w` here — and every
sheafification hypothesis but the right-adjointness of small étale pushforward, itself part of
the statement of Tag 03RW (3), is automatic.

The monoidal structure is named by `AlgebraicGeometry.SmallEtale.moduleSheafMonoidal` rather than
left to instance synthesis on `CategoryTheory.Sheaf.monoidalCategory`: the two are the same
structure, but synthesising the second one's `GrothendieckTopology.W.IsMonoidal` argument fails
in the import closure of Tag 0960, where a competing filtered-colimit instance for
`forget (ModuleCat Λ)` fixes the enriched-hom universes wrongly. The named form has those
arguments already discharged.

## References

* [Stacks Project, Tag 0961](https://stacks.math.columbia.edu/tag/0961)
* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
* [Stacks Project, Tag 095I](https://stacks.math.columbia.edu/tag/095I)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.SmallEtale.moduleSheafMonoidal
  SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (max (u + 1) w)) [CommRing Λ]
  [IsNoetherianRing Λ]
  [∀ (S S' : B.Scheme) (f : S' ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B S'.obj S'.property)).IsRightAdjoint]
  [(curriedTensor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive]
  [∀ (P G : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
      (ComplexShape.up ℤ)]

variable (T : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ⥤
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ⥤
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)))

/-- **The hypothesis identifying `T` as the derived tensor product.** The value of `T` at the
classes of two cochain complexes of sheaves of `Λ`-modules is the class of their total tensor
complex, as soon as the right factor is bounded above and all of its terms are flat.

This is the `comparisonRight` field of `Stacks.SheafOfModules.DerivedTensorProduct` restricted to
the bounded above complexes of flat sheaves, which Tag 06YQ puts among the K-flat ones. Flatness
of a sheaf of `Λ`-modules is flatness of the sheaf of modules over the constant coefficient ring
sheaf which it determines, the notion
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`
establishes for a flat constructible sheaf. -/
def IsDerivedTensorOnFlatComplexes : Prop :=
  ∀ (P G : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ) (q : ℤ),
    G.IsStrictlyLE q →
    (∀ i : ℤ, Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w, max (u + 1) w}
      (moduleSheafOverConstantCoefficients.{u, max (u + 1) w, max (u + 1) w} B X Λ (G.X i))) →
    Nonempty
      ((T.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj G) ≅
        DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P G
          (curriedTensor
            (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
          (ComplexShape.up ℤ)))

/-- **The engine of Tag 0961.** Let `X` be a quasi-compact quasi-separated scheme, `Λ` a
Noetherian ring and `K, L ∈ D_c^-(X_étale, Λ)`. Then `K ⊗^L_Λ L` is represented by a bounded
above complex of constructible sheaves of `Λ`-modules.

Tag 0960 (1) ⟹ (3) presents `K` and `L` by bounded above complexes `P` and `G` of flat
constructible sheaves, so `hcomp` identifies `K ⊗^L_Λ L` with `Tot(P ⊗_Λ G)`; the terms of that
complex are finite direct sums of the sheaves `P^a ⊗_Λ G^b`, which are constructible by Tag 095I,
and its bound above is the sum of the two bounds. -/
theorem exists_isStrictlyLE_isConstructibleModuleSheaf_derivedTensor
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (hcomp : IsDerivedTensorOnFlatComplexes.{u, w} B X Λ T)
    (K L : DerivedCategory.Minus (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsConstructible B X Λ K.obj) (hL : IsConstructible B X Λ L.obj) :
    ∃ (M : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ)
      (n : ℤ), M.IsStrictlyLE n ∧
        (∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (M.X i)) ∧
        Nonempty (DerivedCategory.Q.obj M ≅ (T.obj K.obj).obj L.obj) := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := L.property
  obtain ⟨P, hPminus, hPterm, ⟨eP⟩⟩ :=
    isRepresentedByBoundedAboveConstructibleFlatComplex_of_isConstructible B X Λ K.obj hK a
      (fun i hi => DerivedCategory.isZero_of_isLE K.obj a i hi)
  obtain ⟨G, hGminus, hGterm, ⟨eG⟩⟩ :=
    isRepresentedByBoundedAboveConstructibleFlatComplex_of_isConstructible B X Λ L.obj hL b
      (fun i hi => DerivedCategory.isZero_of_isLE L.obj b i hi)
  obtain ⟨p, hp⟩ := hPminus
  obtain ⟨q, hq⟩ := hGminus
  obtain ⟨e⟩ := hcomp P G q hq (fun i =>
    isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf B X Λ _
      (hGterm i))
  have := isWeakSerreClass_isConstructibleModuleSheafProperty.{u, max (u + 1) w} B X Λ
  have : ObjectProperty.IsClosedUnderFiniteCoproducts
      (isConstructibleModuleSheafProperty.{u, max (u + 1) w, max (u + 1) w} B X Λ) :=
    Stacks.ConstantSheaf.isClosedUnderFiniteCoproducts_of_isWeakSerreClass _
  refine ⟨HomologicalComplex.mapBifunctor P G (curriedTensor _) (ComplexShape.up ℤ), p + q,
    Stacks.ConstantSheaf.isStrictlyLE_mapBifunctor _ P G p q, fun i => ?_,
    ⟨e.symm ≪≫ (T.mapIso eP).app (DerivedCategory.Q.obj G) ≪≫ (T.obj K.obj).mapIso eG⟩⟩
  exact Stacks.ConstantSheaf.prop_mapBifunctor_of_isStrictlyLE (curriedTensor _) P G p q
    (isConstructibleModuleSheafProperty.{u, max (u + 1) w, max (u + 1) w} B X Λ)
    (fun a' b' => isConstructibleModuleSheaf_tensor B X Λ _ _
      (isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hPterm a'))
      (isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hGterm b'))) i

/-- **The conclusion of Tag 0961 for a quasi-compact quasi-separated scheme.** Let `X` be a
quasi-compact quasi-separated scheme, let `Λ` be a Noetherian ring and let
`K, L ∈ D_c^-(X_étale, Λ)`. Then `K ⊗_Λ^L L` is in `D_c^-(X_étale, Λ)`: it is bounded above, and
all of its cohomology sheaves are constructible.

Tag 0961 asks nothing of the scheme, so compactness and quasi-separatedness of `X` are additions,
and the tag is not registered here; it is registered on
`Stacks.EtaleCohomology.minus_and_isConstructible_derivedTensor_of_arbitraryScheme`, which proves
the same conclusion for an arbitrary scheme. The proof uses the flat constructible representative
of Tag 0960 (1) ⟹ (3).

No part of the conclusion is assumed. The only thing asked of the derived tensor product `T` is
`hcomp`, which says that `T` *is* the derived tensor product: its value on a pair of complexes
whose right member is a bounded above complex of flat sheaves is the total tensor complex. Both
halves of the conclusion come from the single complex
`Stacks.EtaleCohomology.exists_isStrictlyLE_isConstructibleModuleSheaf_derivedTensor` produces —
boundedness above because that complex is bounded above, constructibility of the cohomology
sheaves because its terms are constructible and Tag 03RZ (3) is a weak Serre condition. -/
theorem minus_and_isConstructible_derivedTensor_of_flat
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (hcomp : IsDerivedTensorOnFlatComplexes.{u, w} B X Λ T)
    (K L : DerivedCategory.Minus (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsConstructible B X Λ K.obj) (hL : IsConstructible B X Λ L.obj) :
    (DerivedCategory.TStructure.t (C := Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))).minus ((T.obj K.obj).obj L.obj) ∧
      IsConstructible B X Λ ((T.obj K.obj).obj L.obj) := by
  obtain ⟨M, n, hn, hterm, ⟨e⟩⟩ :=
    exists_isStrictlyLE_isConstructibleModuleSheaf_derivedTensor B X Λ T hcomp K L hK hL
  refine ⟨⟨n, DerivedCategory.TStructure.t.isLE_of_iso e n⟩, ?_⟩
  exact isConstructible_of_forall_isConstructibleModuleSheaf B X Λ
    (isWeakSerreClass_isConstructibleModuleSheafProperty.{u, max (u + 1) w} B X Λ) M hterm _ e

end Stacks.EtaleCohomology

end
