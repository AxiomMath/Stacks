module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SchemePushforwardPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeConverse

/-!
# Crossing between the sheaf-level and the module-level local condition on an affine scheme

The local condition out of which relative pseudo-coherence of Stacks 09UI is built asks for
`m`-pseudo-coherence of the derived pushforward of an object of `D(𝒪_X)` along a closed immersion
`X ⟶ 𝔸ⁿ_V`. Where `X` and `V` are affine, that condition is a statement about *modules*: the
affine space is `Spec` of a polynomial ring, the closed immersion is `Spec` of a surjection of
rings, and the pushforward of an associated sheaf is the associated sheaf of a restriction of
scalars. This file supplies that translation.

Two file-level notes in this library record the translation as the one thing still missing between
them and a proof of Stacks 09VC —
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/KoszulPushforward.lean` ("that comparison is not
part of this library, and it is the only thing still missing between this file and a proof of
Stacks 09VC") and
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SchemePushforwardPseudoCoherent.lean`. Both notes
predate the landing of Stacks 08E7 in
`StacksFrontier/Homology/PseudoCoherentRelative/TildePseudoCoherent.lean` and
`StacksFrontier/Homology/PseudoCoherentRelative/TildeConverse.lean`; what was still genuinely absent
is the passage from a statement about `Spec R` to a statement about an arbitrary affine scheme,
which is the transport along an isomorphism proved here.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryId`: the functor induced on derived categories by the
  identity is the identity.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompInvIso` and
  `AlgebraicGeometry.Scheme.Modules.pushforwardUnitIso`: pushforward along an isomorphism of
  schemes carries the structure sheaf to the structure sheaf.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_singleFunctor_unit`: the structure sheaf of a
  scheme is a pseudo-coherent sheaf of modules.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff`: **the transport.**
  Sheaf-level `m`-pseudo-coherence is unchanged by pushing forward along an isomorphism of
  schemes, in both directions.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_congr`,
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_postcomp_isIso_iff` and
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_isIso_iff`: the
  local condition of Stacks 09UI only depends on the closed immersion up to equality, and is
  unchanged by composing with an isomorphism on either side.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_tilde_iff`: **Stacks 08E7 for
  a module.** An `R`-module is `m`-pseudo-coherent exactly when the associated sheaf on
  `Spec R`, placed in degree zero, is.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_specMap_tilde_iff`:
  **the crossing.** For a closed immersion `Spec φ : Spec S ⟶ Spec R`, the local condition of
  Stacks 09UI at `Spec φ` for the associated sheaf of an `S`-module `N` holds exactly when `N`,
  with scalars restricted along `φ`, is an `m`-pseudo-coherent `R`-module.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_specMap_unit_iff`: the
  same at `N = S`, which is the case the structure sheaf needs.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_unit_iff_of_isAffine`:
  **the crossing at an arbitrary closed immersion of affine schemes.** For `i : X ⟶ Y` a closed
  immersion of affine schemes, `Ri_*𝒪_X` is `m`-pseudo-coherent on `Y` exactly when `Γ(X, ⊤)` is
  an `m`-pseudo-coherent `Γ(Y, ⊤)`-module.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall`: sheaf-level pseudo-coherence of an
  object of the derived category is `m`-pseudo-coherence in every degree.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_singleFunctor_pushforward_unit_of_isAffine`:
  **the side condition of Stacks 09VA at a closed immersion of affine schemes, reduced to
  algebra.** `i_*𝒪_X` is a pseudo-coherent sheaf as soon as `Γ(X, ⊤)` is an `m`-pseudo-coherent
  `Γ(Y, ⊤)`-module for every `m`.

## Implementation notes

**Why the transport along an isomorphism is not formal.** Sheaf-level `m`-pseudo-coherence
(Stacks 08CB) is a condition on an object of the derived category of modules on a *ringed space*,
phrased through restriction to open subspaces, so it does not transport along an isomorphism of
schemes by any general nonsense. It is obtained here from the forward half of Stacks 09VA, which
is proved as
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory`: an
isomorphism is a closed immersion, its side condition on the pushforward of the structure sheaf is
satisfied because that pushforward *is* the structure sheaf, and applying the same implication to
the inverse gives the converse. So both directions of the transport come from the half of
Stacks 09VA that is proved; none of it needs the reverse half.

The side condition is `AlgebraicGeometry.RingedSpace.isPseudoCoherent_singleFunctor_unit`, that
`𝒪_X` is a pseudo-coherent sheaf of modules on any scheme. It is the structure sheaf placed in
degree zero, which is strictly perfect: `𝒪_X` is a retract of `𝒪_X^{⊕1}`
(`StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule`) and
`StrictlyPerfect.isStrictlyPerfect_single` puts it in a single degree.

`AlgebraicGeometry.Scheme.Modules.pushforwardUnitIso` goes through the *restriction* functor
rather than through `SheafOfModules.unitToPushforwardObjUnit`, whose being an isomorphism for an
isomorphism of schemes is not recorded. Restriction along an isomorphism `k` is invertible by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorId`, it carries the structure sheaf to the
structure sheaf by `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` identifies its composite with the
pushforward; only the one natural isomorphism
`restrictFunctor k ⋙ restrictFunctor (inv k) ≅ 𝟭` is needed, so no equivalence of categories and
no coherence condition has to be produced.

`CategoryTheory.Functor.mapDerivedCategoryId` is what lets the two applications of Stacks 09VA
compose back to the identity: `k_*` followed by `(k⁻¹)_*` is `(k ≫ k⁻¹)_*`, and that is
`(𝟙)_* ≅ 𝟭` only after the induced functor of the identity has been identified with the identity.
It is the lift of the isomorphism
`(𝟭).mapHomologicalComplex _ ⋙ DerivedCategory.Q ≅ DerivedCategory.Q` through the localization,
exactly as `CategoryTheory.Functor.mapDerivedCategoryCompIso` is.

**Shape of the crossing.** The two halves of Stacks 08E7 are stated for a *complex* of `R`-modules
and the complex `\widetilde{M^•}` formed termwise; the statements here are for a single module,
obtained by taking `M^•` to be the module placed in degree zero and commuting
`HomologicalComplex.single` past `M ↦ M^~` with
`HomologicalComplex.singleMapHomologicalComplex`. The `m`-pseudo-coherence of an object of the
derived category is then read off `DerivedCategory.singleFunctorIsoCompQ`. The crossing itself
adds `AlgebraicGeometry.pushforwardTildeIso` (Stacks 01I9), that pushing an associated sheaf
forward along `Spec φ` restricts the scalar action, and
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, which commutes an exact functor on
derived categories past placing a module in degree zero.

## References

* [The Stacks Project, Lemma 36.17.1 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [The Stacks Project, Lemma 20.49.2 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Lemma 29.4.5 (01I9)](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace CategoryTheory.Functor

universe v u w

/-- The functor induced on derived categories by the identity functor is the identity: both lift
`DerivedCategory.Q` through the localization, since
`(𝟭).mapHomologicalComplex _ ⋙ DerivedCategory.Q` is `DerivedCategory.Q`. -/
public def mapDerivedCategoryId (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] : (𝟭 C).mapDerivedCategory ≅ 𝟭 (DerivedCategory C) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((𝟭 C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q _ _
    (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫ Functor.leftUnitor _)

end CategoryTheory.Functor

namespace AlgebraicGeometry

universe u d

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Modules

/-- Restricting along an isomorphism `k` of schemes and then along its inverse is the identity on
sheaves of modules. This is all that is needed of the fact that restriction along an isomorphism
is an equivalence, and unlike the equivalence it carries no coherence obligation. -/
public def restrictFunctorCompInvIso {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k] :
    restrictFunctor k ⋙ restrictFunctor (inv k) ≅ 𝟭 Z.Modules :=
  (restrictFunctorComp (inv k) k).symm ≪≫ restrictFunctorCongr (IsIso.inv_hom_id k) ≪≫
    restrictFunctorId

/-- **Pushforward along an isomorphism of schemes carries the structure sheaf to the structure
sheaf.** Restriction along `k` sends `𝒪_Z` to `𝒪_Y` by
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso` and sends `k_*𝒪_Y` to `𝒪_Y` by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`, so the two agree after restricting
along `k`; restricting further along `inv k` returns both to `Z`. -/
public def pushforwardUnitIso {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k] :
    (pushforward k).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  (restrictFunctorCompInvIso k).symm.app _ ≪≫
    (restrictFunctor (inv k)).mapIso
      ((restrictFunctorAdjCounitIso k).app _ ≪≫ (restrictUnitIso k).symm) ≪≫
    (restrictFunctorCompInvIso k).app _

end Scheme.Modules

namespace RingedSpace

/-- **The structure sheaf of a scheme is a pseudo-coherent sheaf of modules.** Placed in degree
zero it is a strictly perfect complex, being a retract of `𝒪_Z^{⊕1}` in the one degree where it
is nonzero. -/
public theorem isPseudoCoherent_singleFunctor_unit (Z : Scheme.{u}) :
    IsPseudoCoherent (X := Z.toRingedSpace)
      ((DerivedCategory.singleFunctor Z.Modules 0).obj (SheafOfModules.unit Z.ringCatSheaf)) :=
  ⟨(CochainComplex.singleFunctor Z.Modules 0).obj (structureModule Z.toRingedSpace),
    isPseudoCoherentComplex_of_isStrictlyPerfect
      (isStrictlyPerfect_single (isDirectSummandOfFiniteFree_structureModule _) 0),
    ⟨((DerivedCategory.singleFunctorIsoCompQ Z.Modules 0).app _).symm⟩⟩

/-- **Pseudo-coherence is `m`-pseudo-coherence in every degree.** Stacks 08CB part (3) asks for a
*single* complex representing the object which is `m`-pseudo-coherent for all `m`, and a priori
`m`-pseudo-coherence in each degree supplies a different representative in each; but Stacks 08CC
part (2) makes *every* representative `m`-pseudo-coherent, so the canonical representative
`DerivedCategory.Q.objPreimage E` serves for all degrees at once. -/
public theorem isPseudoCoherent_iff_forall {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (E : DerivedCategory (OXMod.{u, u} X)) :
    IsPseudoCoherent E ↔ ∀ m : ℤ, IsPseudoCoherentFrom E m := by
  refine ⟨fun ⟨K, hK, he⟩ m => ⟨K, hK m, he⟩, fun h =>
    ⟨DerivedCategory.Q.objPreimage E, fun m => ?_,
      ⟨DerivedCategory.Q.objObjPreimageIso E⟩⟩⟩
  exact isPseudoCoherentComplexFrom_of_iso E m (h m) _ (DerivedCategory.Q.objObjPreimageIso E)

/-- The side condition of Stacks 09VA at an isomorphism of schemes: the pushforward of the
structure sheaf along an isomorphism is the structure sheaf, which is pseudo-coherent. -/
public theorem isPseudoCoherent_singleFunctor_pushforward_unit {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    [IsIso k] :
    IsPseudoCoherent (X := Z.toRingedSpace)
      ((DerivedCategory.singleFunctor Z.Modules 0).obj
        ((Scheme.Modules.pushforward k).obj (SheafOfModules.unit Y.ringCatSheaf))) :=
  (isPseudoCoherent_singleFunctor_unit Z).of_iso
    ((DerivedCategory.singleFunctor Z.Modules 0).mapIso
      (Scheme.Modules.pushforwardUnitIso k)).symm

end RingedSpace

namespace Scheme.Modules

/-- Pushing forward along an isomorphism `k` of schemes and then along its inverse is the identity
on derived categories. -/
public def mapDerivedCategoryPushforwardInv {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k] :
    (pushforward k).mapDerivedCategory ⋙ (pushforward (inv k)).mapDerivedCategory ≅
      𝟭 (DerivedCategory Y.Modules) :=
  Functor.mapDerivedCategoryCompIso
      (pushforwardComp k (inv k) ≪≫ pushforwardCongr (IsIso.hom_inv_id k) ≪≫
        pushforwardId Y) ≪≫
    Functor.mapDerivedCategoryId Y.Modules

/-- **Sheaf-level `m`-pseudo-coherence is unchanged by an isomorphism of schemes.** For `k` an
isomorphism, an object of `D(𝒪_Y)` is `m`-pseudo-coherent if and only if `k_*` of it is.

Both directions are the *forward* half of Stacks 09VA
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory`), applied
to `k` and to its inverse; its side condition holds at an isomorphism by
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_singleFunctor_pushforward_unit`. -/
public theorem isPseudoCoherentFrom_pushforward_isIso_iff {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k]
    (A : DerivedCategory Y.Modules) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := Z.toRingedSpace)
        ((pushforward k).mapDerivedCategory.obj A) m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) A m := by
  refine ⟨fun h => ?_, fun h =>
    isPseudoCoherentFrom_pushforward_mapDerivedCategory k
      (RingedSpace.isPseudoCoherent_singleFunctor_pushforward_unit k) m A h⟩
  exact (isPseudoCoherentFrom_pushforward_mapDerivedCategory (inv k)
    (RingedSpace.isPseudoCoherent_singleFunctor_pushforward_unit (inv k)) m _ h).of_iso
      ((mapDerivedCategoryPushforwardInv k).app A)

/-- Sheaf-level `m`-pseudo-coherence is invariant under isomorphism, as an `Iff`. -/
private theorem sheaf_isPseudoCoherentFrom_iff_of_iso {Z : Scheme.{u}}
    {A B : DerivedCategory Z.Modules} (e : A ≅ B) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := Z.toRingedSpace) A m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Z.toRingedSpace) B m :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- The local condition of Stacks 09UI depends on the closed immersion only through its value, not
through the instance that elaborated it. The equality cannot be used by `rw`, because the
condition's elaboration depends on the `IsClosedImmersion` instance and the rewrite motive is not
type correct; it is used through
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` instead. -/
public theorem isPseudoCoherentFromAfterPushforward_congr {X Y : Scheme.{u}} {i i' : X ⟶ Y}
    [IsClosedImmersion i] [IsClosedImmersion i'] (h : i = i') (E : DerivedCategory X.Modules)
    (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward i E m ↔ IsPseudoCoherentFromAfterPushforward i' E m := by
  rw [isPseudoCoherentFromAfterPushforward_iff, isPseudoCoherentFromAfterPushforward_iff]
  exact sheaf_isPseudoCoherentFrom_iff_of_iso
    ((Functor.mapDerivedCategoryCongr (pushforwardCongr h)).app E) m

/-- The local condition of Stacks 09UI only depends on the isomorphism class of the object, as an
`Iff`.

The two implications are
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.of_iso`, written out by
name: that declaration's name has to be spelled in full, because
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` is an `abbrev` and
resolving `h.of_iso` against a hypothesis of that type sends the elaborator through the unfolded
existential, which exhausts the heartbeat budget. -/
public theorem isPseudoCoherentFromAfterPushforward_iff_of_iso {X Y : Scheme.{u}} (i : X ⟶ Y)
    {E E' : DerivedCategory X.Modules} (e : E ≅ E') (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward i E m ↔ IsPseudoCoherentFromAfterPushforward i E' m :=
  ⟨fun h => IsPseudoCoherentFromAfterPushforward.of_iso i h e,
    fun h => IsPseudoCoherentFromAfterPushforward.of_iso i h e.symm⟩

/-- Composing a closed immersion with an isomorphism of its target does not change the local
condition of Stacks 09UI. -/
public theorem isPseudoCoherentFromAfterPushforward_postcomp_isIso_iff {X Y Y' : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (b : Y ⟶ Y') [IsIso b] (E : DerivedCategory X.Modules)
    (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (i ≫ b) E m ↔
      IsPseudoCoherentFromAfterPushforward i E m := by
  rw [isPseudoCoherentFromAfterPushforward_comp_iff, isPseudoCoherentFromAfterPushforward_iff]
  exact isPseudoCoherentFrom_pushforward_isIso_iff b _ m

/-- Composing a closed immersion with an isomorphism of its source does not change the local
condition of Stacks 09UI, once the object is carried across the isomorphism. -/
public theorem isPseudoCoherentFromAfterPushforward_precomp_isIso_iff {X' X Y : Scheme.{u}}
    (a : X' ⟶ X) [IsIso a] (i : X ⟶ Y) [IsClosedImmersion i] (E : DerivedCategory X'.Modules)
    (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (a ≫ i) E m ↔
      IsPseudoCoherentFromAfterPushforward i ((pushforward a).mapDerivedCategory.obj E) m := by
  rw [isPseudoCoherentFromAfterPushforward_comp_iff, isPseudoCoherentFromAfterPushforward_iff]

end Scheme.Modules

namespace RingedSpace

/-- **Stacks 08E7 for a module.** An `R`-module is `m`-pseudo-coherent exactly when the
`𝒪_{Spec R}`-module it determines, placed in degree zero, is `m`-pseudo-coherent in the sheaf-level
sense of Stacks 08CB.

Both halves of Stacks 08E7 are proved for complexes; this is the case of a module placed in degree
zero, with `HomologicalComplex.singleMapHomologicalComplex` commuting `M ↦ M^~` past that
placement. -/
public theorem isPseudoCoherentFrom_singleFunctor_tilde_iff {R : CommRingCat.{u}}
    (N : ModuleCat.{u} R) (m : ℤ) :
    IsPseudoCoherentFrom (X := (Spec R).toRingedSpace)
        ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj ((tilde.functor R).obj N)) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) m := by
  have e₁ : DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N).symm
  have e₂ : DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≅
      (DerivedCategory.singleFunctor (Spec R).Modules 0).obj ((tilde.functor R).obj N) :=
    DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (tilde.functor R)
          (ComplexShape.up ℤ) 0).app N) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (Spec R).Modules 0).app _).symm
  exact ⟨fun h =>
      (Stacks.AffineTilde.isPseudoCoherentFrom_of_isPseudoCoherentFrom_tildeComplex _ m
        (h.of_iso e₂.symm)).ofIso e₁,
    fun h =>
      (Stacks.AffineTilde.isPseudoCoherentFrom_tildeComplex _ m (h.ofIso e₁.symm)).of_iso e₂⟩

end RingedSpace

namespace Scheme.Modules

/-- **The crossing between the sheaf-level and the module-level local condition.** Let
`φ : R ⟶ S` be a morphism of commutative rings whose spectrum is a closed immersion, and let `N`
be an `S`-module. The local condition of Stacks 09UI at `Spec φ` for the sheaf `N^~` placed in
degree zero holds for `m` if and only if `N`, with its scalars restricted along `φ`, is an
`m`-pseudo-coherent `R`-module.

Pushing `N^~` forward along `Spec φ` is the sheaf associated to the restriction of scalars, by
`AlgebraicGeometry.pushforwardTildeIso` (Stacks 01I9); Stacks 08E7 then reads off the module-level
condition. -/
public theorem isPseudoCoherentFromAfterPushforward_specMap_tilde_iff {R S : CommRingCat.{u}}
    (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)] (N : ModuleCat.{u} S) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (Spec.map φ)
        ((DerivedCategory.singleFunctor (Spec S).Modules 0).obj ((tilde.functor S).obj N)) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars φ.hom).obj N)) m := by
  have e : (pushforward (Spec.map φ)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (Spec S).Modules 0).obj ((tilde.functor S).obj N)) ≅
      (DerivedCategory.singleFunctor (Spec R).Modules 0).obj
        ((tilde.functor R).obj ((ModuleCat.restrictScalars φ.hom).obj N)) :=
    ((pushforward (Spec.map φ)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor (Spec R).Modules 0).mapIso
        ((pushforwardTildeIso R S φ).app N)
  rw [isPseudoCoherentFromAfterPushforward_iff,
    ← RingedSpace.isPseudoCoherentFrom_singleFunctor_tilde_iff]
  exact sheaf_isPseudoCoherentFrom_iff_of_iso e m

/-- **The crossing at the structure sheaf.** For `φ : R ⟶ S` whose spectrum is a closed
immersion, the local condition of Stacks 09UI at `Spec φ` for `𝒪_{Spec S}` holds for `m` if and
only if `S`, as an `R`-module through `φ`, is `m`-pseudo-coherent.

This is the case `N = S` of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_specMap_tilde_iff`:
`AlgebraicGeometry.tildeSelf` is `CategoryTheory.Iso.refl`, so the two statements are
definitionally equal and the application is checked at default transparency. Rewriting with the
previous result instead exhausts the heartbeat budget, matching the written-out statement rather
than constructing the term. -/
public theorem isPseudoCoherentFromAfterPushforward_specMap_unit_iff {R S : CommRingCat.{u}}
    (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)] (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (Spec.map φ)
        ((DerivedCategory.singleFunctor (Spec S).Modules 0).obj
          (SheafOfModules.unit (Spec S).ringCatSheaf)) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))) m :=
  isPseudoCoherentFromAfterPushforward_specMap_tilde_iff φ (ModuleCat.of S S) m

/-- **The local condition of Stacks 09UI for `𝒪` is unchanged by isomorphisms on either side.**
Composing a closed immersion `i : X ⟶ Y` with an isomorphism `a : X' ⟶ X` of its source and an
isomorphism `b : Y ⟶ Y'` of its target gives the same condition at the structure sheaf, because
`a_*𝒪_{X'}` is `𝒪_X`. -/
public theorem isPseudoCoherentFromAfterPushforward_conj_unit_iff {X' X Y Y' : Scheme.{u}}
    (a : X' ⟶ X) [IsIso a] (i : X ⟶ Y) [IsClosedImmersion i] (b : Y ⟶ Y') [IsIso b] (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (a ≫ i ≫ b)
        ((DerivedCategory.singleFunctor X'.Modules 0).obj
          (SheafOfModules.unit X'.ringCatSheaf)) m ↔
      IsPseudoCoherentFromAfterPushforward i
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit X.ringCatSheaf)) m :=
  (isPseudoCoherentFromAfterPushforward_precomp_isIso_iff a (i ≫ b) _ m).trans
    ((isPseudoCoherentFromAfterPushforward_postcomp_isIso_iff i b _ m).trans
      (isPseudoCoherentFromAfterPushforward_iff_of_iso i
        (((pushforward a).mapDerivedCategorySingleFunctor 0).app _ ≪≫
          (DerivedCategory.singleFunctor X.Modules 0).mapIso (pushforwardUnitIso a)) m))

/-- **The local condition of Stacks 09UI at the structure sheaf of an affine scheme is
module-level `m`-pseudo-coherence of its ring of sections.** For a closed immersion `i : X ⟶ Y`
of affine schemes, `Ri_*𝒪_X` is `m`-pseudo-coherent on `Y` if and only if `Γ(X, ⊤)` is an
`m`-pseudo-coherent `Γ(Y, ⊤)`-module through `i`.

This is the statement that both the side condition of Stacks 09VA and the per-pair content of
Stacks 09VF at the structure sheaf reduce to: with `Y = 𝔸ⁿ_V` it says that `Ri_*𝒪_X` is
`m`-pseudo-coherent exactly when `Γ(X, ⊤)` is `m`-pseudo-coherent over the polynomial ring, which
is the module-level condition of Stacks 065I read at one presentation.

The proof conjugates `i` by `AlgebraicGeometry.Scheme.isoSpec` on both sides, where
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality` turns it into `Spec` of its map on global
sections, and applies
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_specMap_unit_iff`. -/
public theorem isPseudoCoherentFromAfterPushforward_unit_iff_of_isAffine {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (i : X ⟶ Y) [IsClosedImmersion i] (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward i
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, ⊤)) 0).obj
          ((ModuleCat.restrictScalars i.appTop.hom).obj (ModuleCat.of Γ(X, ⊤) Γ(X, ⊤)))) m := by
  have hfac : X.isoSpec.inv ≫ i ≫ Y.isoSpec.hom = Spec.map i.appTop := by
    rw [← Scheme.isoSpec_hom_naturality i, Iso.inv_hom_id_assoc]
  have hci : IsClosedImmersion (X.isoSpec.inv ≫ i ≫ Y.isoSpec.hom) := inferInstance
  rw [hfac] at hci
  have := hci
  exact (isPseudoCoherentFromAfterPushforward_conj_unit_iff X.isoSpec.inv i
      Y.isoSpec.hom m).symm.trans
    ((isPseudoCoherentFromAfterPushforward_congr hfac _ m).trans
      (isPseudoCoherentFromAfterPushforward_specMap_unit_iff i.appTop m))

/-- **The side condition of Stacks 09VA at a closed immersion of affine schemes, reduced to
algebra.** For `i : X ⟶ Y` a closed immersion of affine schemes, `i_*𝒪_X` is a pseudo-coherent
sheaf of `𝒪_Y`-modules as soon as `Γ(X, ⊤)` is an `m`-pseudo-coherent `Γ(Y, ⊤)`-module for every
`m`.

This is the shape in which the side condition of Stacks 09VA is consumed by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory` and by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_reflect_fin`. Pushing
`𝒪_X` forward along a closed immersion needs no derived functor —
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` identifies `Ri_*𝒪_X` with `i_*𝒪_X` in
degree zero — and `AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall` assembles the
degrees. -/
public theorem isPseudoCoherent_singleFunctor_pushforward_unit_of_isAffine {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (i : X ⟶ Y) [IsClosedImmersion i]
    (h : ∀ m : ℤ, StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, ⊤)) 0).obj
        ((ModuleCat.restrictScalars i.appTop.hom).obj (ModuleCat.of Γ(X, ⊤) Γ(X, ⊤)))) m) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        ((pushforward i).obj (SheafOfModules.unit X.ringCatSheaf))) :=
  (RingedSpace.isPseudoCoherent_iff_forall (X := Y.toRingedSpace) _).2 fun m =>
    RingedSpace.IsPseudoCoherentFrom.of_iso (X := Y.toRingedSpace)
      ((isPseudoCoherentFromAfterPushforward_iff i _ m).1
        ((isPseudoCoherentFromAfterPushforward_unit_iff_of_isAffine i m).2 (h m)))
      (((pushforward i).mapDerivedCategorySingleFunctor 0).app _)

end Scheme.Modules

end AlgebraicGeometry

end
