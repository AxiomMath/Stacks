module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The conormal module of an immersion commutes with étale localization

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `φ : U ⟶ X` be étale and let

```
Z_U --p--> Z
|i_U       |i
U  --φ-->  X
```

be the cartesian square it induces, so that `Z_U = U ×_X Z`.  This file proves Stacks 04CO:
`Z_U` is a locally closed subspace of `U`, and

`𝒞_{Z/X}|_{Z_U} = p^*𝒞_{Z/X} ≅ 𝒞_{Z_U/U}`.

The conormal module of an immersion is the one this development already has: the degree-one
piece of `AlgebraicGeometry.Space.conormalAlgebraOfImmersion`, that is the inverse image of the
ideal sheaf of the closed immersion of `Z` into the complement `X ∖ ∂Z` of the boundary of its
image, through which `i` factors by Stacks 04CE.

The route is a *bridge*: for an immersion the conormal module taken through that closed
factorisation agrees with `i^*Ker(i^♯)`, the degree-one piece of
`AlgebraicGeometry.Space.conormalAlgebra` of `i` itself, because the open immersion
`ι : X ∖ ∂Z ⟶ X` is étale and `Z = Z ×_X (X ∖ ∂Z)` — so the agreement is an instance of the
étale-localization isomorphism `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso`
with `𝟙 Z` as its projection.  The conormal-algebra statement is proved for an arbitrary
morphism, so the isomorphism of the tag is that statement in degree one conjugated by the
bridge at `i` and at `i_U`.

## Main definitions

* `AlgebraicGeometry.Space.immersionConormalModule`: the conormal module `𝒞_{Z/X}` of an
  immersion, as the degree-one piece of the conormal algebra of its closed factorisation.
* `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso`: the bridge, the identification
  of `i^*(Ker(i^♯)ⁿ)` with the degree-`n` piece of the conormal algebra of the closed
  factorisation of `i`.
* `AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso`: **Stacks 04CO**, the
  canonical isomorphism `p^*𝒞_{Z/X} ≅ 𝒞_{Z_U/U}` for an immersion `i : Z ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.isLocallyClosedSubspace_preimage`: **Stacks 04CO**, the inverse image
  of a locally closed subspace is a locally closed subspace, which is the clause `Z_U ⊆ U` is
  locally closed.
* `AlgebraicGeometry.Space.immersionAmbientInclusion`,
  `AlgebraicGeometry.Space.isEtale_immersionAmbientInclusion` and
  `AlgebraicGeometry.Space.isPullback_closedFactorization_ambientInclusion`: the inclusion of the
  complement of the boundary of an immersion is étale, and the closed factorisation of
  Stacks 04CE exhibits `Z` as the base change of `Z` along it — the two inputs of the bridge.
* `AlgebraicGeometry.Space.etaleModulePullback_kernelIdealSheafZPow_eq_comp`: the
  **identification of ideal sheaves is functorial in the étale source on the nose**: restricting
  along a composite of two étale morphisms and restricting along the two in turn give the *same*
  module, not merely isomorphic ones.

## Implementation notes

**Why the conormal module of an immersion is `i^*Ker(i^♯)` after all.**  For a general morphism
`i` the two differ: for an open immersion `Ker(i^♯)` is the ideal of functions vanishing on the
image, which is not zero, while the conormal module of an open immersion is.  They agree because
the inverse image along `i` of a sheaf of ideals on `X` is the inverse image along the closed
factorisation of its restriction to `X ∖ ∂Z`, and that restriction is the kernel ideal sheaf of
the factorisation — which is exactly
`AlgebraicGeometry.Space.etaleModulePullback_kernelIdealSheafZPow_eq` at the cartesian square
with `𝟙 Z` on top.  The bridge below is that instance, and so the agreement is proved rather
than assumed.

**Why `𝟙 Z` makes the square cartesian.**  `Z = Z ×_X (X ∖ ∂Z)` because the image of `i` lies in
`X ∖ ∂Z` and the inclusion of an open subspace is a monomorphism: a square with an invertible
top edge and a monomorphism along the bottom is cartesian,
`CategoryTheory.IsPullback.of_horiz_isIso_mono`.

**No hypothesis beyond the tag's.**  The statements below take `U` to be an arbitrary algebraic
space étale over `X`, where the source takes a scheme, and the square to be an arbitrary
cartesian square rather than the canonical preimage: both are more general, and the preimage
square of `CategoryTheory.Subfunctor.isPullback_preimage` is an instance of the latter.

## What is not proved

* **The functoriality in the étale source `U` is not proved for the module comparison built
  here.**  Stacks 04CO asserts the identification "canonically and functorially in `U`", and the
  clause itself is proved — for the identification taken to be the canonical map of Stacks 04CP,
  at closed-subspace generality — in
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestrictionCanonical.lean`, where it
  is the composition law of Stacks 04G2, part (3); that route needs Stacks 03LW nowhere.  What is
  open is the clause for *this* comparison, and at immersion generality.  For `ψ : V ⟶ U` a
  further étale morphism the two sides of the functoriality equation unwind to the comparison of
  Stacks 03LU for `ψ` and `φ` read against the identification of Stacks 03LW: the isomorphism
  above uses Stacks 03LW along `ψ ≫ φ` on one side and along `ψ` and `φ` separately on the other.
  That composition law for Stacks 03LW is
  `AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`, which
  **nothing in this development discharges** — every consumer carries it as a hypothesis — and
  `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction` reduces it to one
  equality of units.  The composition law for the comparison of Stacks 03LQ at an arbitrary
  sheaf of sets is not the missing input: it is
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleInverseImageIsoComp.lean`, which recovers
  `AlgebraicGeometry.Space.structureSharpSet_comp` as its structure-sheaf case.  What assembling
  the unit equality from it still asks for is listed in the module documentation of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompIsoEtaleRestriction.lean`.
  What *is* proved unconditionally here is the functoriality of the ideal-sheaf identification
  that carries the content of the source's proof,
  `AlgebraicGeometry.Space.etaleModulePullback_kernelIdealSheafZPow_eq_comp`; it holds on the
  nose, because étale restriction of the ideal sheaf is an equality and equalities compose.
* **That the canonical map of Stacks 04CP is this isomorphism is not proved**, for the reason the
  module documentation of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` records: no
  statement brings the description of `AlgebraicGeometry.Space.idealSheafMap` after both
  transposes and the description of the Stacks 03LW comparison after the unit to a common form.

## References

* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The inverse image of a locally closed subspace -/

/-- The preimage square of a subfunctor, as a cartesian square of algebraic spaces. -/
private theorem isPullback_homMk_preimage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ X) (Z : Subfunctor X)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z.toFunctor)
    (hP : IsAlgebraicSpace B S hS (Z.preimage f).toFunctor) :
    IsPullback
      (ObjectProperty.homMk (Z.fromPreimage f) :
        (⟨(Z.preimage f).toFunctor, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZ⟩)
      (ObjectProperty.homMk (Z.preimage f).ι :
        (⟨(Z.preimage f).toFunctor, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk Z.ι : (⟨Z.toFunctor, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk f : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS T))
    (Subfunctor.isPullback_preimage f Z)

/-- **Stacks 04CO, the locally closed clause.**  The inverse image of a locally closed subspace
of an algebraic space along a morphism of algebraic spaces over `S` is a locally closed subspace
of the source.

For an étale `f` this is the clause of Stacks 04CO that `Z_U = U ×_X Z` is a locally closed
subspace of `U`; no étaleness is needed, the inverse image being the fibre product by
Stacks 083Q and immersions being stable under base change by Stacks 02YW. -/
@[stacks 04CO "Z_U = U ×_X Z is a locally closed subspace of U"]
theorem isLocallyClosedSubspace_preimage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (Z : Subfunctor X)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsLocallyClosedSubspace B S hS Z) :
    IsLocallyClosedSubspace B S hS (Z.preimage f) := by
  have hsq := Subfunctor.isPullback_preimage f Z
  have hP : IsAlgebraicSpace B S hS (Z.preimage f).toFunctor :=
    isAlgebraicSpace_of_iso B S hS hsq.isoPullback.symm
      (isAlgebraicSpace_pullback B S hS Z.ι f hZ.1 hY hX)
  exact ⟨hP, isImmersion_of_isPullback B S hS
    (isPullback_homMk_preimage B S hS f Z hX hY hZ.1 hP) hZ.2⟩

section Immersion

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V X Z ZU ZV : AlgebraicSpaces B S hS}

/-! ### The ambient open subspace of an immersion -/

/-- The inclusion of the complement `X ∖ ∂Z` of the boundary of an immersion `i : Z ⟶ X`, as a
morphism of algebraic spaces: the ambient space in which `i` is a closed immersion, by
Stacks 04CE. -/
noncomputable def immersionAmbientInclusion (i : Z ⟶ X) (hi : IsImmersion B S hS i.hom) :
    immersionAmbient B S hS X.2 Z.2 i.hom hi ⟶ X :=
  ObjectProperty.homMk
    (boundaryComplement B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom))).ι

/-- **The inclusion of the ambient open subspace of an immersion is étale.**  It is the inclusion
of an open subspace, and an open immersion is étale. -/
theorem isEtale_immersionAmbientInclusion (i : Z ⟶ X) (hi : IsImmersion B S hS i.hom) :
    IsEtale B S hS (immersionAmbientInclusion B S hS i hi).hom :=
  isEtale_of_isOpenImmersion B S hS
    (isOpenSubspace_boundaryComplement B S hS X.2
      (isLocallyClosed_range_pointsMap_of_isImmersion B S hS X.2 i.hom hi)).2

/-- **Stacks 04CE as a factorisation of morphisms of algebraic spaces.**  The closed
factorisation of an immersion followed by the inclusion of the complement of its boundary is the
immersion. -/
theorem immersionClosedFactorization_comp_immersionAmbientInclusion
    (i : Z ⟶ X) (hi : IsImmersion B S hS i.hom) :
    immersionClosedFactorization B S hS X.2 Z.2 i.hom hi ≫
        immersionAmbientInclusion B S hS i hi = i :=
  ObjectProperty.hom_ext _ (boundaryComplementLift_comp_ι B S hS X.2 Z.2 i.hom hi)

/-- The inclusion of the ambient open subspace of an immersion is a monomorphism: it is the
inclusion of a subfunctor, and the forgetful functor to presheaves is faithful. -/
theorem mono_immersionAmbientInclusion (i : Z ⟶ X) (hi : IsImmersion B S hS i.hom) :
    Mono (immersionAmbientInclusion B S hS i hi) :=
  ⟨fun _a _b hab ↦ ObjectProperty.hom_ext _
    ((cancel_mono (boundaryComplement B S hS X.1
        (Set.range (pointsMap B S hS Z.1 i.hom))).ι).mp
      (congrArg (fun k ↦ k.hom) hab))⟩

/-- **The closed factorisation of an immersion is a base change of the immersion itself.**  The
square with `𝟙 Z` on top, the closed factorisation of Stacks 04CE down the left, the immersion
down the right and the inclusion of the complement of the boundary along the bottom is
cartesian, because the inclusion of an open subspace is a monomorphism.

This is what lets the conormal module taken through the factorisation be compared with
`i^*Ker(i^♯)` by the étale-localization isomorphism of Stacks 09RR. -/
theorem isPullback_closedFactorization_ambientInclusion (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) :
    IsPullback (𝟙 Z) (immersionClosedFactorization B S hS X.2 Z.2 i.hom hi) i
      (immersionAmbientInclusion B S hS i hi) :=
  have := mono_immersionAmbientInclusion B S hS i hi
  IsPullback.of_horiz_isIso_mono
    ⟨by rw [Category.id_comp,
      immersionClosedFactorization_comp_immersionAmbientInclusion B S hS i hi]⟩

/-! ### The conormal module of an immersion -/

/-- The conormal module `𝒞_{Z/X}` of an immersion `i : Z ⟶ X` of algebraic spaces: the
degree-one piece of the conormal algebra of Stacks 09RN of its closed factorisation, that is the
inverse image along that factorisation of the ideal sheaf of `Z` in `X ∖ ∂Z`.

This is a name for the degree-one piece of
`AlgebraicGeometry.Space.conormalAlgebraOfImmersion` and not a second construction of the
conormal module; `AlgebraicGeometry.Space.conormalModule` is the closed-subspace case, and
`AlgebraicGeometry.Space.conormalAlgebra_piece_one_eq_conormalModule` identifies the two
there.  The inverse-image construction `AlgebraicGeometry.Space.conormalModuleOfImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebra.lean` is the same module, by
`AlgebraicGeometry.Space.conormalModuleOfImmersion_eq_conormalAlgebraOfImmersion_piece_one`;
this abbreviation reads it as the degree-one piece on the nose, for an immersion between
bundled algebraic spaces. -/
noncomputable abbrev immersionConormalModule (i : Z ⟶ X) (hi : IsImmersion B S hS i.hom) :
    Modules.{u, u} B S hS Z.1 Z.2 :=
  (conormalAlgebraOfImmersion B S hS X.2 Z.2 i.hom hi).piece 1

/-- **The conormal algebra of an immersion is the conormal algebra of the immersion itself.**
For an immersion `i : Z ⟶ X` the degree-`n` piece of the conormal algebra of the closed
factorisation of Stacks 04CE is canonically isomorphic to `i^*(Ker(i^♯)ⁿ)`, the degree-`n` piece
of `AlgebraicGeometry.Space.conormalAlgebra` of `i`.

This is the étale-localization isomorphism of Stacks 09RR at the cartesian square of
`AlgebraicGeometry.Space.isPullback_closedFactorization_ambientInclusion`, whose transverse
morphism is the étale inclusion of `X ∖ ∂Z` and whose projection is `𝟙 Z`; the inverse image
along `𝟙 Z` is stripped by the unit law of Stacks 03LU. -/
noncomputable def conormalAlgebraOfImmersionPieceIso (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) (n : ℤ) :
    (conormalAlgebra B S hS i).piece n ≅
      (conormalAlgebraOfImmersion B S hS X.2 Z.2 i.hom hi).piece n :=
  ((modulePullbackIdIso B S hS Z).app ((conormalAlgebra B S hS i).piece n)).symm ≪≫
    conormalAlgebraEtaleRestrictionPieceIso B S hS (𝟙 Z)
      (immersionClosedFactorization B S hS X.2 Z.2 i.hom hi) i
      (immersionAmbientInclusion B S hS i hi)
      (isPullback_closedFactorization_ambientInclusion B S hS i hi)
      (isEtale_immersionAmbientInclusion B S hS i hi) n

/-! ### Stacks 04CO -/

/-- **Stacks 04CO.**  Let `i : Z ⟶ X` be an immersion of algebraic spaces over `S`, let
`φ : U ⟶ X` be étale and let `Z_U = U ×_X Z` with projections `p : Z_U ⟶ Z` and `i_U : Z_U ⟶ U`.
Then the inverse image along `p` of the conormal module of `Z` in `X` is the conormal module of
`Z_U` in `U`:

`𝒞_{Z/X}|_{Z_U} = p^*𝒞_{Z/X} ≅ 𝒞_{Z_U/U}`.

Both conormal modules are taken through the closed factorisation of Stacks 04CE, as
`AlgebraicGeometry.Space.immersionConormalModule`; `i_U` is an immersion because immersions are
stable under base change.  The isomorphism is the degree-one instance of the conormal-algebra
isomorphism of Stacks 09RR, conjugated by the bridge
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` at `i` and at `i_U`. -/
@[stacks 04CO "the conormal module of an immersion commutes with etale localisation"]
noncomputable def conormalModuleOfImmersionEtaleRestrictionIso (p : ZU ⟶ Z) (iU : ZU ⟶ U)
    (i : Z ⟶ X) (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hi : IsImmersion B S hS i.hom)
    (hφ : IsEtale B S hS φ.hom) :
    (modulePullback B S hS p).obj (immersionConormalModule B S hS i hi) ≅
      immersionConormalModule B S hS iU (isImmersion_of_isPullback B S hS sq hi) :=
  (modulePullback B S hS p).mapIso
      (conormalAlgebraOfImmersionPieceIso B S hS i hi 1).symm ≪≫
    conormalAlgebraEtaleRestrictionPieceIso B S hS p iU i φ sq hφ 1 ≪≫
    conormalAlgebraOfImmersionPieceIso B S hS iU (isImmersion_of_isPullback B S hS sq hi) 1

/-- **Stacks 083Q as a cartesian square of algebraic spaces.**  For a morphism `φ : U ⟶ X` of
algebraic spaces over `S` and a subspace `Z` of `X`, the square formed by the inverse image of
`Z`, its inclusion into `U` and the projection to `Z` is cartesian.

This is `CategoryTheory.Subfunctor.isPullback_preimage` read in the category of algebraic
spaces, the two algebraicity hypotheses being what makes the four corners objects of it. -/
theorem isPullback_fromPreimage (φ : U ⟶ X) (Z : Subfunctor X.1)
    (hZ : IsAlgebraicSpace B S hS Z.toFunctor)
    (hP : IsAlgebraicSpace B S hS (Z.preimage φ.hom).toFunctor) :
    IsPullback
      (ObjectProperty.homMk (Z.fromPreimage φ.hom) :
        (⟨(Z.preimage φ.hom).toFunctor, hP⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨Z.toFunctor, hZ⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (Z.preimage φ.hom).ι :
        (⟨(Z.preimage φ.hom).toFunctor, hP⟩ : AlgebraicSpaces B S hS) ⟶ U)
      (ObjectProperty.homMk Z.ι : (⟨Z.toFunctor, hZ⟩ : AlgebraicSpaces B S hS) ⟶ X) φ :=
  isPullback_homMk_preimage B S hS φ.hom Z X.2 U.2 hZ hP

/-- **Stacks 04CO in the shape the source states it.**  Let `Z` be a locally closed subspace of
an algebraic space `X` over `S`, let `φ : U ⟶ X` be étale and let `Z_U = U ×_X Z` be the inverse
image of `Z`, a locally closed subspace of `U` by
`AlgebraicGeometry.Space.isLocallyClosedSubspace_preimage`.  Then the inverse image along the
projection `p : Z_U ⟶ Z` of the conormal module of `Z` in `X` is the conormal module of `Z_U` in
`U`.

This is `AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso` at the cartesian
square of Stacks 083Q, the inverse image being the fibre product by
`CategoryTheory.Subfunctor.isPullback_preimage`. -/
@[stacks 04CO "the conormal module of a locally closed subspace commutes with etale localisation"]
noncomputable def conormalModuleSubspaceEtaleRestrictionIso (φ : U ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (Z : Subfunctor X.1)
    (hZ : IsLocallyClosedSubspace B S hS Z) :
    (modulePullback B S hS (ObjectProperty.homMk (Z.fromPreimage φ.hom) :
          (⟨(Z.preimage φ.hom).toFunctor,
              (isLocallyClosedSubspace_preimage B S hS φ.hom Z X.2 U.2 hZ).1⟩ :
            AlgebraicSpaces B S hS) ⟶
          (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS))).obj
        (immersionConormalModule B S hS
          (ObjectProperty.homMk Z.ι : (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
          hZ.2) ≅
      immersionConormalModule B S hS
        (ObjectProperty.homMk (Z.preimage φ.hom).ι :
          (⟨(Z.preimage φ.hom).toFunctor,
              (isLocallyClosedSubspace_preimage B S hS φ.hom Z X.2 U.2 hZ).1⟩ :
            AlgebraicSpaces B S hS) ⟶ U)
        (isLocallyClosedSubspace_preimage B S hS φ.hom Z X.2 U.2 hZ).2 :=
  conormalModuleOfImmersionEtaleRestrictionIso B S hS
    (p := (ObjectProperty.homMk (Z.fromPreimage φ.hom) :
      (⟨(Z.preimage φ.hom).toFunctor,
          (isLocallyClosedSubspace_preimage B S hS φ.hom Z X.2 U.2 hZ).1⟩ :
        AlgebraicSpaces B S hS) ⟶ (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS)))
    (iU := (ObjectProperty.homMk (Z.preimage φ.hom).ι :
      (⟨(Z.preimage φ.hom).toFunctor,
          (isLocallyClosedSubspace_preimage B S hS φ.hom Z X.2 U.2 hZ).1⟩ :
        AlgebraicSpaces B S hS) ⟶ U))
    (i := (ObjectProperty.homMk Z.ι :
      (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ X))
    (φ := φ)
    (sq := isPullback_fromPreimage B S hS φ Z hZ.1
      (isLocallyClosedSubspace_preimage B S hS φ.hom Z X.2 U.2 hZ).1)
    (hi := hZ.2) (hφ := hφ)

/-! ### Functoriality of the identification of ideal sheaves -/

/-- **The identification of ideal sheaves of Stacks 04CO is functorial in the étale source, on
the nose.**  For two cartesian squares stacked along a composite `ψ ≫ φ` of étale morphisms, the
étale restriction of the `n`-th power of the kernel ideal sheaf of `i` along the composite *is*
its iterated restriction along the two factors: both are the `n`-th power of the kernel ideal
sheaf of the twice base-changed morphism.

This is the clause the source calls clear from the construction of `𝓘`, read functorially: the
restriction is an equality of modules by
`AlgebraicGeometry.Space.etaleModulePullback_kernelIdealSheafZPow_eq`, and equalities
compose. -/
theorem etaleModulePullback_kernelIdealSheafZPow_eq_comp (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (q : ZV ⟶ ZU) (iV : ZV ⟶ V) (ψ : V ⟶ U)
    (sq' : IsPullback q iV iU ψ) (hφ : IsEtale B S hS φ.hom) (hψ : IsEtale B S hS ψ.hom)
    (hψφ : IsEtale B S hS (ψ ≫ φ).hom) (n : ℤ) :
    (etaleModulePullback.{u, u} B S hS ψ hψ).obj
        ((etaleModulePullback.{u, u} B S hS φ hφ).obj
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules) =
      (etaleModulePullback.{u, u} B S hS (ψ ≫ φ) hψφ).obj
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules := by
  rw [etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n,
    etaleModulePullback_kernelIdealSheafZPow_eq B S hS q iV iU ψ sq' hψ n,
    etaleModulePullback_kernelIdealSheafZPow_eq B S hS (q ≫ p) iV i (ψ ≫ φ)
      (sq'.paste_horiz sq) hψφ n]

end Immersion

end AlgebraicGeometry.Space

end
