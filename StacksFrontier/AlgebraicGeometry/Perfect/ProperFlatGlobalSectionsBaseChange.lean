module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.Homology.PseudoCoherent.BaseChangeFlat

/-!
# Base change for the derived global sections of a flat quasi-coherent module

Let `φ : A ⟶ A'` be a homomorphism of commutative rings, let `f : X ⟶ Spec A` be a separated
morphism of schemes, let

```
X' --g--> X
|         |
f'        f
v         v
Spec A' -> Spec A
```

be cartesian, and let `F` be a quasi-coherent `𝒪_X`-module flat over `Spec A`. This file proves
[Stacks, Tag 07VK] (2): the base-change comparison

`RΓ(X, F) ⊗^L_A A' ⟶ RΓ(X', g^* F)`

is an isomorphism in `D(A')`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplexBaseChangeIso`:
  extension of scalars along `φ` carries the `A`-linear alternating Čech model of
  `StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSections.lean` for a finite affine cover
  `U` of `X` to the `A'`-linear model for the inverse-image cover `g⁻¹ U` of `X'`.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.derivedGlobalSectionsBaseChangeMap`: **the
  base-change map** `RΓ(X, F) ⊗^L_A A' ⟶ RΓ(X', g^* F)` of [Stacks, Tag 07VK] (2), as the source
  writes it down: the counit of derived extension of scalars at the Čech model, read through the
  two identifications of the models with derived global sections and the base-change isomorphism
  of the models.

## Main results

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.top_eq_iSup_preimage`,
  `…isAffineOpen_preimage` and `…iInf_preimage_isAffineOpen`: the inverse image of a finite
  affine cover of `X` with affine finite intersections is such a cover of `X'`. Affineness is
  base change of an affine morphism, not a separate hypothesis.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.isSeparated_of_isPullback` and
  `…isAffineHom_of_isPullback`: `f'` is separated and `g` is affine, by base change.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.isIso_derivedGlobalSectionsBaseChangeMap`:
  **[Stacks, Tag 07VK] (2)**. Unconditional: it needs no Noetherian hypothesis, no properness,
  no coherence and nothing about higher direct images.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_finiteAffineCover_of_isProper`: a
  proper morphism to an affine base admits a cover of the kind the theorem asks for, so the
  theorem does apply in the source's own situation.

## Implementation notes

**What the proof is.** The source proves clause (2) by exhibiting a bounded termwise flat Čech
representative and tensoring it. All three ingredients are already in the library and this file
only composes them:

* the `A`-linear alternating Čech model `baseAlternatingCechComplex` of a finite affine cover
  computes `RΓ(X, F)` in `D(A)` — `alternatingCechIsoDerivedGlobalSectionsOverBase`, which is
  [Stacks, Tag 01FM] followed by [Stacks, Tag 01ET];
* ordinary extension of scalars carries that model to the model of the inverse-image cover on
  `X'` — `Stacks.Cech.cechBaseChangeData`, which is [Stacks, Tag 01XL]: over an affine open the
  sections of `g^* F` are the base change of the sections of `F`;
* on a bounded above termwise flat complex the ordinary extension of scalars *is* the derived
  one — `StacksDraft.PseudoCoherence.isIso_extendScalarsDerivedCounit_app_of_flat`, which is the
  [Stacks, Tag 06XY] step, and flatness of the terms is [Stacks, Tag 01U4] in the form
  `flat_baseAlternatingCechComplex_X`.

So the base-change map below is invertible because each of its four factors is, the middle one
by flatness.

**Why the cover appears in the statement.** `derivedGlobalSectionsBaseChangeMap` takes the finite
affine cover as data, and it is *that* map — not merely some isomorphism — which is proved
invertible. Writing the comparison without reference to a cover would need the derived
pullback-of-sections morphism

`RΓ(X, F) ⟶ restrictScalars_φ (RΓ(X', g^* F))`

in `D(A)`, together with the counit of a derived `extendScalars ⊣ restrictScalars` adjunction.
Neither exists in the library: the pullback-of-sections morphism is the Leray edge map for `g`,
which in this library is available only for the unbounded total right derived functors of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayForDerivedSections.lean`
([Stacks, Tag 0D5W]) and not for the `D⁺`-model `derivedGlobalSections` that clause (1) uses, and
identifying the resulting map with the comparison below would in addition need the compatibility
of the Čech-to-derived-sections transformation of [Stacks, Tag 01EQ] with a morphism of schemes.
The hypotheses of the theorem are exactly the source's own, minus the ones clause (2) does not
use; a cover of the required kind exists for every proper `f`, which is
`exists_finiteAffineCover_of_isProper`.

**The derived-category model.** As in
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSections.lean`, everything runs under
`CategoryTheory.HasDerivedCategory.standard`, activated here as a local instance *with the same
raised priority*: without it the global locally small instance wins for `ModuleCat Γ(X, ⊤)` but
not for `ModuleCat (SectionRing X.ringCatSheaf ⊤)`, and the two `DerivedCategory.Plus` that
result do not unify.

**Instance synthesis around `Stacks.DerivedIndexing.mapExtendIso`.** Its two ambient categories
are given explicitly, as they are in `baseAlternatingCechComplexIsoExtend`; otherwise the
`Additive` instance of `ModuleCat.extendScalars` is not synthesized.

## References

* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
* [Stacks Project, Tag 06XY](https://stacks.math.columbia.edu/tag/06XY)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

section Cover

/-- **The inverse image of a cover is a cover.** Taking preimages along `g` commutes with
suprema of opens and carries `⊤` to `⊤`. -/
theorem top_eq_iSup_preimage {X X' : Scheme.{u}} (g : X' ⟶ X) {I : Type u} (U : I → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i) :
    (⊤ : X'.Opens) = ⨆ i, g ⁻¹ᵁ U i := by
  rw [show (⨆ i, g ⁻¹ᵁ U i) = g ⁻¹ᵁ (⨆ i, U i) from (Opens.map_iSup _ _).symm, ← hU]
  simp

/-- **The base change of a separated morphism is separated.** -/
theorem isSeparated_of_isPullback {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] {f' : X' ⟶ Spec (.of A')}
    {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) :
    IsSeparated f' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq ‹IsSeparated f›

/-- **The base change of a morphism of affine schemes is an affine morphism.** This is what makes
the inverse image of an affine open affine, with no further hypothesis. -/
theorem isAffineHom_of_isPullback {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} {f' : X' ⟶ Spec (.of A')}
    {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) :
    IsAffineHom g :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip
    (P := @IsAffineHom) inferInstance

/-- **The inverse image of an affine open is affine.** -/
theorem isAffineOpen_preimage {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} {f' : X' ⟶ Spec (.of A')}
    {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {I : Type u} (U : I → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (i : I) :
    IsAffineOpen (g ⁻¹ᵁ U i) :=
  have := isAffineHom_of_isPullback φ hsq
  (hUaff i).preimage g

/-- **The finite intersections of the inverse-image cover are affine.** The members are affine by
`isAffineOpen_preimage` and `f'` is separated by `isSeparated_of_isPullback`, so
[Stacks, Tag 01XL] in the form `Stacks.Cech.inter_isAffineOpen` applies on `X'`. -/
theorem iInf_preimage_isAffineOpen {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] {f' : X' ⟶ Spec (.of A')}
    {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {I : Type u} (U : I → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i))
    (r : ℕ) (s : Fin (r + 1) → I) :
    IsAffineOpen (⨅ k, g ⁻¹ᵁ U (s k)) :=
  have := isSeparated_of_isPullback φ hsq
  Stacks.Cech.inter_isAffineOpen f' (fun i => g ⁻¹ᵁ U i)
    (isAffineOpen_preimage φ hsq U hUaff) s

end Cover

section BaseChange

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] {f' : X' ⟶ Spec (.of A')}
  {g : X' ⟶ X} (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I]
  (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- **Extension of scalars carries the `A`-linear alternating Čech model of `U` to the `A'`-linear
model of the inverse-image cover.** This is [Stacks, Tag 01XL] — over an affine open the sections
of `g^* F` are the base change of the sections of `F` — in the form
`Stacks.Cech.cechBaseChangeData`, transported from the `ℕ`-indexed complexes to the `ℤ`-indexed
models through `baseAlternatingCechComplexIsoExtend` and
`Stacks.DerivedIndexing.mapExtendIso`. -/
def baseAlternatingCechComplexBaseChangeIso :
    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (baseAlternatingCechComplex f U hU F) ≅
      baseAlternatingCechComplex f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
        ((Scheme.Modules.pullback g).obj F) :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (baseAlternatingCechComplexIsoExtend f U hU F) ≪≫
    (@Stacks.DerivedIndexing.mapExtendIso ℕ ℤ (ComplexShape.up ℕ) (ComplexShape.up ℤ)
        (ModuleCat.{u} A) (ModuleCat.{u} A') _ _ _ _ _ _
        (ModuleCat.extendScalars.{u, u, u} φ) inferInstance ComplexShape.embeddingUpNat
        (Stacks.Cech.alternatingCechModuleComplex f U F)).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A')).mapIso
      (Stacks.Cech.cechBaseChangeData φ f f' g hsq F U hUaff (fun i => g ⁻¹ᵁ U i)
        (Equiv.refl I) (fun _ => rfl)).alternatingIso ≪≫
    (baseAlternatingCechComplexIsoExtend f' (fun i => g ⁻¹ᵁ U i) (top_eq_iSup_preimage g U hU)
      ((Scheme.Modules.pullback g).obj F)).symm

variable [LinearOrder I]
  (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))

/-- **The base-change map `RΓ(X, F) ⊗^L_A A' ⟶ RΓ(X', g^* F)` of [Stacks, Tag 07VK] (2)**, for a
finite affine open cover `U` of `X` whose finite intersections are affine.

It is the comparison the source writes down, in four factors. Read `RΓ(X, F)` through the
alternating Čech model of `U` (`alternatingCechIsoDerivedGlobalSectionsOverBase`); apply the
counit `StacksDraft.PseudoCoherence.extendScalarsDerivedCounit` of derived extension of scalars,
which compares `- ⊗^L_A A'` with the ordinary `- ⊗_A A'` on that model; identify the ordinary
extension of scalars of the model with the model of the inverse-image cover on `X'`
(`baseAlternatingCechComplexBaseChangeIso`); and read the latter back as `RΓ(X', g^* F)`.

The middle factor is the only one that is not invertible for a general complex; it is invertible
here because the model is bounded and termwise flat, which is the [Stacks, Tag 06XY] step of the
source's proof. -/
def derivedGlobalSectionsBaseChangeMap :
    (StacksDraft.PseudoCoherence.extendScalarsDerived φ).obj
        (derivedGlobalSectionsOverBase f F) ⟶
      derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F) :=
  (StacksDraft.PseudoCoherence.extendScalarsDerived φ).map
      (alternatingCechIsoDerivedGlobalSectionsOverBase f U hU F haff).inv ≫
    (StacksDraft.PseudoCoherence.extendScalarsDerivedCounit φ).app
      (baseAlternatingCechComplex f U hU F) ≫
    DerivedCategory.Q.map (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff).hom ≫
    (alternatingCechIsoDerivedGlobalSectionsOverBase f' (fun i => g ⁻¹ᵁ U i)
      (top_eq_iSup_preimage g U hU) ((Scheme.Modules.pullback g).obj F)
      (iInf_preimage_isAffineOpen φ hsq U hUaff)).hom

include hU in
/-- **[Stacks, Tag 07VK] (2).** Let `φ : A ⟶ A'` be a homomorphism of commutative rings, let
`f : X ⟶ Spec A` be separated, let `g : X' ⟶ X` and `f' : X' ⟶ Spec A'` exhibit `X'` as the base
change of `X` along `Spec A' ⟶ Spec A`, and let `F` be a quasi-coherent `𝒪_X`-module flat over
`Spec A`. Then the base-change map

`RΓ(X, F) ⊗^L_A A' ⟶ RΓ(X', g^* F)`

is an isomorphism in `D(A')`.

The proof is the source's. The alternating Čech complex of a finite affine cover whose finite
intersections are affine computes `RΓ(X, F)` ([Stacks, Tag 01FM] and [Stacks, Tag 01ET]), it is
bounded, and flatness of `F` over the base makes it termwise flat ([Stacks, Tag 01U4]); for such
a complex the ordinary extension of scalars is the derived one ([Stacks, Tag 06XY]), and the
ordinary extension of scalars of the model is the model of the inverse-image cover on `X'`
([Stacks, Tag 01XL]), which computes `RΓ(X', g^* F)`.

**Unconditional.** No Noetherian hypothesis, no properness, no coherence, and in particular no
appeal to `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`,
which clause (1) threads and clause (2) does not need. The hypotheses are weaker than the
source's: for `A` Noetherian, `f` proper and `F` coherent and flat they hold, a suitable cover
being supplied by `exists_finiteAffineCover_of_isProper`. Both clauses of the tag, under the
source's hypotheses, are stated together in
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.isPerfect_and_isIso_baseChange`, which carries
the tag. -/
theorem isIso_derivedGlobalSectionsBaseChangeMap
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsIso (derivedGlobalSectionsBaseChangeMap φ hsq F U hU hUaff haff) := by
  let _ : Fintype I := Fintype.ofFinite I
  have hflatX : ∀ n : ℤ, Module.Flat A ((baseAlternatingCechComplex f U hU F).X n) :=
    flat_baseAlternatingCechComplex_X f U hU F hUaff hflat
  have hcounit : IsIso ((StacksDraft.PseudoCoherence.extendScalarsDerivedCounit φ).app
      (baseAlternatingCechComplex f U hU F)) :=
    StacksDraft.PseudoCoherence.isIso_extendScalarsDerivedCounit_app_of_flat φ
      (baseAlternatingCechComplex f U hU F) (Fintype.card I : ℤ)
  dsimp only [derivedGlobalSectionsBaseChangeMap]
  infer_instance

end BaseChange

section ProperCover

/-- **A proper morphism to an affine base admits a cover of the kind
`isIso_derivedGlobalSectionsBaseChangeMap` asks for.** Properness makes `X` quasi-compact, so the
affine open cover of `X` has a finite subcover, and it makes `f` separated, so the finite
intersections of the members are affine ([Stacks, Tag 01XL]). This is the construction in the
proof of `isPerfect_derivedGlobalSections`, recorded on its own: together with
`isIso_derivedGlobalSectionsBaseChangeMap` it says that the base-change map of [Stacks, Tag 07VK]
(2) is invertible in exactly the source's situation. -/
theorem exists_finiteAffineCover_of_isProper {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    ∃ (I : Type u) (_ : Fintype I) (_ : LinearOrder I) (U : I → X.Opens),
      (⊤ : X.Opens) = ⨆ i, U i ∧ (∀ i, IsAffineOpen (U i)) ∧
        ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)) := by
  classical
  have hcompact : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineOpenCover
  let V := C.openCover.finiteSubcover
  let T : X.AffineOpenCover.{u, u} :=
    { I₀ := V.I₀
      X i := C.X (C.openCover.idx i.1)
      f i := C.f (C.openCover.idx i.1)
      idx := V.idx
      covers := V.covers
      map_prop i := C.map_prop (C.openCover.idx i.1) }
  have hUaff : ∀ i, IsAffineOpen ((T.f i).opensRange) := fun i => isAffineOpen_opensRange (T.f i)
  exact ⟨T.I₀, inferInstance, linearOrderOfSTO WellOrderingRel, fun i => (T.f i).opensRange,
    T.openCover.iSup_opensRange.symm, hUaff,
    fun _ s => Stacks.Cech.inter_isAffineOpen f (fun i => (T.f i).opensRange) hUaff s⟩

end ProperCover

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
