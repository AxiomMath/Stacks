module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.FinitelyManyClosedPoints
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumExactSequence
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Properties

/-!
# The local exact sequence at one closed point of a scheme

Let `X` be a connected scheme, let `x ∈ X` be a closed point, and let `U = X ∖ {x}`, the open
subscheme `AlgebraicGeometry.GlueingNearPoint.puncturedOpen`, assumed connected and retrocompact in
`X`. Write `A = 𝒪_{X,x}`, let `Aˢʰ` be a strict henselization of `A` and let `Uˢʰ` be the preimage
of `U` under `Spec Aˢʰ ⟶ Spec A ⟶ X`. Assume that the punctured spectrum of every strict
henselization of `A` is connected, and that `A` satisfies the descent hypothesis of Stacks 0BSB:
a finite étale cover of the punctured spectrum of `A` whose base change to the punctured spectrum
of `Aˢʰ` is a finite coproduct of copies of it is the restriction of a finite étale cover of
`Spec A`. Then

```
π₁(Uˢʰ, ū) → π₁(U, ū) → π₁(X, ū) → 1
```

is exact in the sense of `Stacks.FundamentalGroup.IsExactSequence`. This is the one-point case of
Stacks Tag 0BSC, under the descent hypothesis above.

By Stacks 0BS9, exactness follows from full faithfulness of `FÉt_X ⥤ FÉt_U` (Stacks 0BSA)
together with a description of its essential image: a finite étale cover of `U` extends to `X`
exactly when its base change to `Uˢʰ` is a finite coproduct of copies of `Uˢʰ`. A cover with this
property descends to `Spec A` along the overlap `Spec A ∖ {𝔪} = Spec 𝒪_{X,x} ∩ U`, and the two
covers glue (Stacks 0BPA) to a scheme of finite presentation over `X`, which is finite étale by
Stacks 0EY3.

## Main results

* `AlgebraicGeometry.finiteEtale_of_restrictions_at_closedPoint`: a morphism of finite
  presentation to `X` is finite étale as soon as its restrictions to `U` and to `Spec 𝒪_{X,x}`
  are.
* `AlgebraicGeometry.essImage_finiteEtaleBaseChange_of_glueing_at_closedPoint`: glueing a finite
  étale cover of `U` to a finite étale cover of `Spec 𝒪_{X,x}` along an isomorphism over the
  overlap produces a finite étale cover of `X`.
* `AlgebraicGeometry.isFiniteCoproductOfTerminal_finiteEtaleBaseChange_of_henselian`: the
  restriction to `Uˢʰ` of the restriction to `U` of a finite étale cover of `X` is a finite
  coproduct of copies of `Uˢʰ`.
* `AlgebraicGeometry.connectedSpace_preimage_puncturedOpen_of_isStrictHenselization`: `Uˢʰ` is
  the punctured spectrum of `Aˢʰ`, hence connected.
* `AlgebraicGeometry.essImage_finiteEtaleBaseChange_puncturedOpen_iff`: the essential image of
  `FÉt_X ⥤ FÉt_U` consists of the covers of `U` that split over `Uˢʰ`, under the descent
  hypothesis.
* `AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedOpen`: the exact sequence
  above, under the descent hypothesis.

## Implementation notes

The descent hypothesis `hdescent` is stated as in
`AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum`. It is the descent
half of the proof of Stacks 0BSB, so the results that assume it discharge neither Stacks 0BSB nor
the kernel clause of Stacks 0BSC.

`Uˢʰ` is the open `(Spec.map (CommRingCat.ofHom (algebraMap A Aˢʰ)) ≫ X.fromSpecStalk x) ⁻¹ᵁ
puncturedOpen hs`, and `Uˢʰ ⟶ U` is the restriction of that composite. This open is the preimage
under `Spec Aˢʰ ⟶ Spec A` of the overlap `Spec 𝒪_{X,x} ∩ U`, which
`AlgebraicGeometry.preimage_fromSpecStalk_eq_puncturedSpectrum` identifies with the punctured
spectrum of `A`.

The connectedness hypothesis at `x` is
`AlgebraicGeometry.IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x)`, quantified over
all strict henselizations.

## References

* [Stacks Project, Tag 0BSC](https://stacks.math.columbia.edu/tag/0BSC)
* [Stacks Project, Tag 0BSB](https://stacks.math.columbia.edu/tag/0BSB)
* [Stacks Project, Tag 0BSA](https://stacks.math.columbia.edu/tag/0BSA)
* [Stacks Project, Tag 0BS9](https://stacks.math.columbia.edu/tag/0BS9)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 0EY3](https://stacks.math.columbia.edu/tag/0EY3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.Divisors
open Stacks.FundamentalGroup
open AlgebraicGeometry.GlueingNearPoint

universe u

namespace AlgebraicGeometry

/-! ### Transferring a property of the structure morphism along isomorphisms -/

/-- A property of the structure morphism of a scheme over a base is invariant under isomorphism
in the slice category. -/
private lemma prop_iff_of_overIso {T : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {A B : Over T} (e : A ≅ B) : P A.hom ↔ P B.hom :=
  P.arrow_mk_iso_iff (Arrow.isoMk ((Over.forget T).mapIso e) (Iso.refl T) (by simp))

/-- Base change along an isomorphism does not change whether the structure morphism has a given
property: the first projection of the base change is then an isomorphism too. -/
private lemma prop_pullback_iff_of_isIso {T S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (g : T ⟶ S) [IsIso g] (A : Over S) :
    P ((Over.pullback g).obj A).hom ↔ P A.hom :=
  P.arrow_mk_iso_iff (Arrow.isoMk (asIso (pullback.fst A.hom g)) (asIso g)
    (by simpa using pullback.condition))

/-! ### Finiteness and étaleness of a glued object -/

/-- A closed point does not lie in its own open complement. -/
private alias notMem_puncturedOpen' := GlueingNearPoint.notMem_puncturedOpen

/-- The open complement of a closed point is retrocompact as soon as its inclusion is
quasi-compact. -/
private lemma isRetrocompact_puncturedOpen {S : Scheme.{u}} {s : S}
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι) :
    IsRetrocompact ((puncturedOpen hs : S.Opens) : Set S) := by
  intro W hWc hWo
  have h := (hqc.isCompact_preimage W hWo hWc).image (puncturedOpen hs).ι.continuous
  rwa [Set.image_preimage_eq_range_inter, Scheme.Opens.range_ι] at h

/-- An open containing both the complement of a closed point and the point itself is
everything. -/
private lemma eq_top_of_puncturedOpen_le {S : Scheme.{u}} {s : S} (hs : IsClosed ({s} : Set S))
    (V : S.Opens) (hUV : puncturedOpen hs ≤ V) (hsV : s ∈ V) : V = ⊤ := by
  refine top_unique fun z _ ↦ ?_
  by_cases hz : z = s
  · subst hz; exact hsV
  · exact hUV (by simpa [puncturedOpen] using hz)

/-- A scheme of finite presentation over `S`, viewed as a scheme of finite presentation over the
open neighbourhood `⊤` of the complement of a point together with that point. -/
private def neighborhoodModelOfFinitePresentation {S : Scheme.{u}} (U : S.Opens) (s : S)
    (Y : FinitePresentationOver S) : FinitePresentationNeighborhoodModel S U s where
  neighborhood := ⟨⊤, le_top, by simp⟩
  source := Y.obj.left
  hom := Y.obj.hom ≫ S.topIso.inv
  finitePresentation := by
    let : LocallyOfFinitePresentation Y.obj.hom := Y.property.1
    let : QuasiCompact Y.obj.hom := Y.property.2.1
    let : QuasiSeparated Y.obj.hom := Y.property.2.2
    exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The neighbourhood model of a scheme of finite presentation over `S`, read back as a scheme
over `S`, is the scheme one started with. -/
private def neighborhoodModelOfFinitePresentationIso {S : Scheme.{u}} (U : S.Opens) (s : S)
    (Y : FinitePresentationOver S) :
    (neighborhoodModelToAmbient S U s).obj (neighborhoodModelOfFinitePresentation U s Y) ≅
      Y.obj := by
  refine Over.isoMk (Iso.refl Y.obj.left) ?_
  dsimp [neighborhoodModelOfFinitePresentation, neighborhoodModelToAmbient]
  rw [Category.id_comp, Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]

/-- **A property of the structure morphism is detected at a closed point.** Let `s` be a closed
point of `S` and `U = S ∖ {s}`. Suppose a property `P` of morphisms, invariant under isomorphism,
can be spread out from the restrictions to `U` and to `Spec 𝒪_{S,s}` of a scheme of finite
presentation over a neighbourhood of `U ∪ {s}` to some smaller such neighbourhood. Then it holds
for the structure morphism of any scheme of finite presentation over `S` whose restrictions to
`U` and to `Spec 𝒪_{S,s}` have it. -/
private theorem prop_of_restrictions_at_closedPoint {S : Scheme.{u}} {s : S}
    (hs : IsClosed ({s} : Set S)) (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (Y : FinitePresentationOver S)
    (hopen : P ((Over.pullback (puncturedOpen hs).ι).obj Y.obj).hom)
    (hlocal : P ((Over.pullback (S.fromSpecStalk s)).obj Y.obj).hom)
    (hspread : ∀ M : FinitePresentationNeighborhoodModel S (puncturedOpen hs) s,
      P ((Over.pullback (puncturedOpen hs).ι).obj
        ((neighborhoodModelToAmbient S (puncturedOpen hs) s).obj M)).hom →
      P ((Over.pullback (S.fromSpecStalk s)).obj
        ((neighborhoodModelToAmbient S (puncturedOpen hs) s).obj M)).hom →
      ∃ V : S.Opens, puncturedOpen hs ≤ V ∧ V ≤ M.neighborhood.V ∧ s ∈ V ∧
        P ((Over.pullback V.ι).obj
          ((neighborhoodModelToAmbient S (puncturedOpen hs) s).obj M)).hom) :
    P Y.obj.hom := by
  let M := neighborhoodModelOfFinitePresentation (puncturedOpen hs) s Y
  let e := neighborhoodModelOfFinitePresentationIso (puncturedOpen hs) s Y
  obtain ⟨V, hUV, hVT, hsV, hPV⟩ := hspread M
    ((prop_iff_of_overIso P ((Over.pullback (puncturedOpen hs).ι).mapIso e)).mpr hopen)
    ((prop_iff_of_overIso P ((Over.pullback (S.fromSpecStalk s)).mapIso e)).mpr hlocal)
  obtain rfl := eq_top_of_puncturedOpen_le hs V hUV hsV
  have : IsIso (⊤ : S.Opens).ι := (Scheme.topIso S).isIso_hom
  exact (prop_iff_of_overIso P e).mp ((prop_pullback_iff_of_isIso P (⊤ : S.Opens).ι _).mp hPV)

/-- **A scheme of finite presentation over `S` which is finite étale over the complement of a
closed point and over the local scheme there is finite étale.** Let `s` be a closed point of `S`
whose open complement `U = S ∖ {s}` has quasi-compact inclusion, and let `Y ⟶ S` be of finite
presentation. If the restrictions of `Y` to `U` and to `Spec 𝒪_{S,s}` are both finite and étale,
then `Y ⟶ S` is finite and étale. -/
theorem finiteEtale_of_restrictions_at_closedPoint {S : Scheme.{u}} {s : S}
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι)
    (Y : FinitePresentationOver S)
    (hopen : finiteEtale ((Over.pullback (puncturedOpen hs).ι).obj Y.obj).hom)
    (hlocal : finiteEtale ((Over.pullback (S.fromSpecStalk s)).obj Y.obj).hom) :
    finiteEtale Y.obj.hom := by
  have _ : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@IsFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨prop_of_restrictions_at_closedPoint hs (@IsFinite) Y hopen.1 hlocal.1
      (exists_open_isFinite S (puncturedOpen hs) s (notMem_puncturedOpen' hs)
        (isRetrocompact_puncturedOpen hs hqc)),
    prop_of_restrictions_at_closedPoint hs (@Etale) Y hopen.2 hlocal.2
      (exists_open_etale S (puncturedOpen hs) s (notMem_puncturedOpen' hs)
        (isRetrocompact_puncturedOpen hs hqc))⟩

/-! ### Glueing a finite étale cover at a closed point -/

/-- A finite étale cover, viewed as a scheme of finite presentation over the same base. -/
private def finiteEtaleToFinitePresentation {T : Scheme.{u}} (V : FiniteEtaleOver T) :
    FinitePresentationOver T :=
  ⟨Over.mk V.hom, finitePresentation_of_finiteEtale V⟩

/-- An isomorphism of finite étale covers, read as an isomorphism in the slice category. -/
private def finiteEtaleOverIso {T : Scheme.{u}} {V W : FiniteEtaleOver T} (α : V ≅ W) :
    (finiteEtaleToFinitePresentation V).obj ≅ (finiteEtaleToFinitePresentation W).obj :=
  (MorphismProperty.Over.forget (finiteEtale : MorphismProperty Scheme.{u}) ⊤ T).mapIso α

/-- The glueing datum attached to a finite étale cover of the complement of a closed point, a
finite étale cover of the local scheme there, and an isomorphism of their restrictions to the
overlap. -/
private def glueingDatumOfFiniteEtale {X : Scheme.{u}} {x : X} (hs : IsClosed ({x} : Set X))
    (V : FiniteEtaleOver (puncturedOpen hs).toScheme)
    (W : FiniteEtaleOver (Spec (X.presheaf.stalk x)))
    (α : (finiteEtaleBaseChange (X.fromSpecStalk x ∣_ puncturedOpen hs)).obj V ≅
      (finiteEtaleBaseChange (X.fromSpecStalk x ⁻¹ᵁ puncturedOpen hs).ι).obj W) :
    glueingDataNearPoint X (puncturedOpen hs) x :=
  ⟨⟨finiteEtaleToFinitePresentation V, finiteEtaleToFinitePresentation W,
      (ObjectProperty.isoMk _ (finiteEtaleOverIso α)).hom⟩,
    (ObjectProperty.isoMk _ (finiteEtaleOverIso α)).isIso_hom⟩

/-- The component of a glueing datum over the open complement. -/
private def glueingDatumOpenComponent (S : Scheme.{u}) (U : S.Opens) (s : S) :
    glueingDataNearPoint S U s ⥤ FinitePresentationOver U.toScheme :=
  (show ObjectProperty (Comma (restrictOpenToPuncturedLocal S U s)
    (restrictLocalToPuncturedLocal S U s)) from fun Z ↦ IsIso Z.hom).ι ⋙ Comma.fst _ _

/-- The component of a glueing datum over the local scheme. -/
private def glueingDatumLocalComponent (S : Scheme.{u}) (U : S.Opens) (s : S) :
    glueingDataNearPoint S U s ⥤ FinitePresentationOver (Spec (S.presheaf.stalk s)) :=
  (show ObjectProperty (Comma (restrictOpenToPuncturedLocal S U s)
    (restrictLocalToPuncturedLocal S U s)) from fun Z ↦ IsIso Z.hom).ι ⋙ Comma.snd _ _

/-- **Glueing a finite étale cover at a closed point.** Let `x` be a closed point of a scheme `X`
whose open complement `U = X ∖ {x}` has quasi-compact inclusion. Let `V` be a finite étale cover
of `U`, let `W` be a finite étale cover of `Spec 𝒪_{X,x}`, and let `α` be an isomorphism of their
restrictions to the overlap `Spec 𝒪_{X,x} ∩ U`. Then `V` is the restriction to `U` of a finite
étale cover of `X`. -/
theorem essImage_finiteEtaleBaseChange_of_glueing_at_closedPoint {X : Scheme.{u}} {x : X}
    (hs : IsClosed ({x} : Set X)) (hqc : QuasiCompact (puncturedOpen hs).ι)
    (V : FiniteEtaleOver (puncturedOpen hs).toScheme)
    (W : FiniteEtaleOver (Spec (X.presheaf.stalk x)))
    (α : (finiteEtaleBaseChange (X.fromSpecStalk x ∣_ puncturedOpen hs)).obj V ≅
      (finiteEtaleBaseChange (X.fromSpecStalk x ⁻¹ᵁ puncturedOpen hs).ι).obj W) :
    (finiteEtaleBaseChange (puncturedOpen hs).ι).essImage V := by
  have hequiv := restrictionFunctorAtPoint_isEquivalence X x hs hqc
  let F := restrictionFunctorAtPoint X (puncturedOpen hs) x
  let D := glueingDatumOfFiniteEtale hs V W α
  let Y : FinitePresentationOver X := F.objPreimage D
  have ε : F.obj Y ≅ D := F.objObjPreimageIso D
  have εL : (finitePresentationBaseChange (puncturedOpen hs).ι).obj Y ≅
      finiteEtaleToFinitePresentation V :=
    (glueingDatumOpenComponent X (puncturedOpen hs) x).mapIso ε
  have εR : (finitePresentationBaseChange (X.fromSpecStalk x)).obj Y ≅
      finiteEtaleToFinitePresentation W :=
    (glueingDatumLocalComponent X (puncturedOpen hs) x).mapIso ε
  have εL' : (Over.pullback (puncturedOpen hs).ι).obj Y.obj ≅ Over.mk V.hom :=
    (ObjectProperty.ι _).mapIso εL
  have εR' : (Over.pullback (X.fromSpecStalk x)).obj Y.obj ≅ Over.mk W.hom :=
    (ObjectProperty.ι _).mapIso εR
  have _ : MorphismProperty.RespectsIso (finiteEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hfe : finiteEtale Y.obj.hom :=
    finiteEtale_of_restrictions_at_closedPoint hs hqc Y
      ((prop_iff_of_overIso _ εL').mpr V.prop) ((prop_iff_of_overIso _ εR').mpr W.prop)
  exact ⟨MorphismProperty.Over.mk ⊤ Y.obj.hom hfe,
    ⟨MorphismProperty.Over.isoMk ((Over.forget _).mapIso εL') (Over.w εL'.hom)⟩⟩

/-! ### The splitting of a cover of `X` over the punctured strict local scheme -/

/-- **A finite étale cover of `X` splits over the preimage of an open in the spectrum of a
strictly henselian local ring.** Let `h : Spec Aˢʰ ⟶ X` with `Aˢʰ` henselian local with
separably closed residue field, let `U ⊆ X` be open and let `Uˢʰ = h⁻¹(U)`. Then the restriction
to `Uˢʰ` of the restriction to `U` of a finite étale cover of `X` is a finite coproduct of copies
of `Uˢʰ`. -/
theorem isFiniteCoproductOfTerminal_finiteEtaleBaseChange_of_henselian {X : Scheme.{u}}
    (U : X.Opens) (Ash : Type u) [CommRing Ash] [HenselianLocalRing Ash]
    [IsSepClosed (ResidueField Ash)]
    (h : Spec (.of Ash) ⟶ X) [ConnectedSpace X] [ConnectedSpace U.toScheme]
    [ConnectedSpace (h ⁻¹ᵁ U)] (w : GeometricPoint (h ⁻¹ᵁ U).toScheme) (Y : FiniteEtaleOver X) :
    IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange (h ∣_ U)).obj ((finiteEtaleBaseChange U.ι).obj Y)) := by
  have : ConnectedSpace (Spec (.of Ash)) := connectedSpace_spec_of_isLocalRing Ash
  have heq : (h ∣_ U) ≫ U.ι = (h ⁻¹ᵁ U).ι ≫ h := morphismRestrict_ι h U
  let e₁ : finiteEtaleBaseChange ((h ∣_ U) ≫ U.ι) ≅
      finiteEtaleBaseChange U.ι ⋙ finiteEtaleBaseChange (h ∣_ U) :=
    MorphismProperty.Over.pullbackComp (h ∣_ U) U.ι
  let e₂ : finiteEtaleBaseChange ((h ∣_ U) ≫ U.ι) ≅
      finiteEtaleBaseChange h ⋙ finiteEtaleBaseChange (h ⁻¹ᵁ U).ι :=
    MorphismProperty.Over.pullbackComp (h ⁻¹ᵁ U).ι h ((h ∣_ U) ≫ U.ι) heq
  have hsplit : IsFiniteCoproductOfTerminal ((finiteEtaleBaseChange h).obj Y) :=
    isFiniteCoproductOfTerminal_of_henselian_isSepClosed Ash _
  have : PreservesFiniteLimits (finiteEtaleBaseChange (h ⁻¹ᵁ U).ι) :=
    (exactFunctor_finiteEtaleBaseChange (h ⁻¹ᵁ U).ι w).1
  have : PreservesFiniteColimits (finiteEtaleBaseChange (h ⁻¹ᵁ U).ι) :=
    (exactFunctor_finiteEtaleBaseChange (h ⁻¹ᵁ U).ι w).2
  exact isFiniteCoproductOfTerminal_of_iso ((e₂.symm ≪≫ e₁).app Y)
    (isFiniteCoproductOfTerminal_map (finiteEtaleBaseChange (h ⁻¹ᵁ U).ι) hsplit)

/-! ### The exact sequence at a closed point -/

/-- At a closed point `x` of `X` the local scheme meets `U = X ∖ {x}` exactly in the punctured
spectrum of `𝒪_{X,x}`. -/
private lemma preimage_fromSpecStalk_puncturedOpen {X : Scheme.{u}} {x : X}
    (hs : IsClosed ({x} : Set X)) :
    X.fromSpecStalk x ⁻¹ᵁ puncturedOpen hs = puncturedSpectrum ↥(X.presheaf.stalk x) := by
  refine preimage_fromSpecStalk_eq_puncturedSpectrum (puncturedOpen hs) x
    (by simp [puncturedOpen]) fun y hy ↦ ?_
  rwa [show y = x by simpa [puncturedOpen] using hy]

/-- **`Uˢʰ` is connected.** If the punctured spectrum of a strict henselization `Aˢʰ` of
`𝒪_{X,x}` is connected, then so is the preimage of `U = X ∖ {x}` under
`Spec Aˢʰ ⟶ Spec 𝒪_{X,x} ⟶ X`, which is that punctured spectrum. -/
theorem connectedSpace_preimage_puncturedOpen_of_isStrictHenselization {X : Scheme.{u}} {x : X}
    (hs : IsClosed ({x} : Set X)) (κsep : Type u) [Field κsep]
    [Algebra (maximalIdeal ↥(X.presheaf.stalk x)).ResidueField κsep]
    [IsSepClosure (maximalIdeal ↥(X.presheaf.stalk x)).ResidueField κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra ↥(X.presheaf.stalk x) Ash]
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization ↥(X.presheaf.stalk x) κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash))) :
    ConnectedSpace ((Spec.map (CommRingCat.ofHom (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫
      X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hs) := by
  rw [Scheme.Hom.comp_preimage, preimage_fromSpecStalk_puncturedOpen hs,
    preimage_puncturedSpectrum_of_isStrictHenselization _ κsep Ash hAsh]
  exact isConnected_iff_connectedSpace.mp hconnected

/-- **The essential image of `FÉt_X ⥤ FÉt_U` at a closed point, under descent.** Let
`x` be a closed point of `X` with open complement `U = X ∖ {x}` whose inclusion is quasi-compact,
let `Aˢʰ` be a strict henselization of `A = 𝒪_{X,x}` and let `Uˢʰ` be the preimage of `U` under
`Spec Aˢʰ ⟶ Spec A ⟶ X`. Granted the descent hypothesis `hdescent` of Stacks 0BSB for `A`, a
finite étale cover of `U` is the restriction of a finite étale cover of `X` exactly when its base
change to `Uˢʰ` is a finite coproduct of copies of `Uˢʰ`. -/
theorem essImage_finiteEtaleBaseChange_puncturedOpen_iff {X : Scheme.{u}} {x : X}
    (hs : IsClosed ({x} : Set X)) (hqc : QuasiCompact (puncturedOpen hs).ι)
    [ConnectedSpace X] [ConnectedSpace (puncturedOpen hs).toScheme]
    (κsep : Type u) [Field κsep]
    [Algebra (maximalIdeal ↥(X.presheaf.stalk x)).ResidueField κsep]
    [IsSepClosure (maximalIdeal ↥(X.presheaf.stalk x)).ResidueField κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra ↥(X.presheaf.stalk x) Ash]
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization ↥(X.presheaf.stalk x) κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    (hdescent : ∀ V : FiniteEtaleOver (puncturedSpectrum ↥(X.presheaf.stalk x)).toScheme,
      IsFiniteCoproductOfTerminal
          ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom
            (algebraMap ↥(X.presheaf.stalk x) Ash)) ∣_
              puncturedSpectrum ↥(X.presheaf.stalk x))).obj V) →
        (finiteEtaleBaseChange (puncturedSpectrum ↥(X.presheaf.stalk x)).ι).essImage V)
    (w : GeometricPoint ((Spec.map (CommRingCat.ofHom
      (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ⁻¹ᵁ
        puncturedOpen hs).toScheme)
    (V : FiniteEtaleOver (puncturedOpen hs).toScheme) :
    letI : ConnectedSpace ((Spec.map (CommRingCat.ofHom
        (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hs) :=
      connectedSpace_preimage_puncturedOpen_of_isStrictHenselization hs κsep Ash hAsh hconnected
    (finiteEtaleBaseChange (puncturedOpen hs).ι).essImage V ↔
      IsFiniteCoproductOfTerminal ((finiteEtaleBaseChange ((Spec.map (CommRingCat.ofHom
        (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ∣_
          puncturedOpen hs)).obj V) := by
  have : ConnectedSpace ((Spec.map (CommRingCat.ofHom
      (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hs) :=
    connectedSpace_preimage_puncturedOpen_of_isStrictHenselization hs κsep Ash hAsh hconnected
  have : HenselianLocalRing Ash := hAsh.henselian
  have : IsSepClosed (maximalIdeal Ash).ResidueField := hAsh.sepClosed
  have : IsSepClosed (ResidueField Ash) := isSepClosed_residueField_of_maximalIdeal Ash
  have hP : X.fromSpecStalk x ⁻¹ᵁ puncturedOpen hs =
    puncturedSpectrum ↥(X.presheaf.stalk x) := preimage_fromSpecStalk_puncturedOpen hs
  rw [← hP] at hdescent
  let e : finiteEtaleBaseChange ((Spec.map (CommRingCat.ofHom
        (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ∣_ puncturedOpen hs) ≅
      finiteEtaleBaseChange (X.fromSpecStalk x ∣_ puncturedOpen hs) ⋙
        finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(X.presheaf.stalk x) Ash)) ∣_
            (X.fromSpecStalk x ⁻¹ᵁ puncturedOpen hs)) :=
    MorphismProperty.Over.pullbackComp (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(X.presheaf.stalk x) Ash)) ∣_ (X.fromSpecStalk x ⁻¹ᵁ puncturedOpen hs))
      (X.fromSpecStalk x ∣_ puncturedOpen hs) ((Spec.map (CommRingCat.ofHom
        (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ∣_ puncturedOpen hs)
      (morphismRestrict_comp _ _ _)
  refine ⟨fun hV ↦ ?_, fun hV ↦ ?_⟩
  · obtain ⟨Y, ⟨eY⟩⟩ := hV
    exact isFiniteCoproductOfTerminal_of_iso (Functor.mapIso _ eY)
      (isFiniteCoproductOfTerminal_finiteEtaleBaseChange_of_henselian (puncturedOpen hs) Ash
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫
          X.fromSpecStalk x) w Y)
  · obtain ⟨W, ⟨α⟩⟩ := hdescent
      ((finiteEtaleBaseChange (X.fromSpecStalk x ∣_ puncturedOpen hs)).obj V)
      (isFiniteCoproductOfTerminal_of_iso (e.app V) hV)
    exact essImage_finiteEtaleBaseChange_of_glueing_at_closedPoint hs hqc V W α.symm

/-- **The local exact sequence at one closed point, under descent.** Let `X` be a
connected scheme, let `x ∈ X` be a closed point, and let `U = X ∖ {x}`, assumed connected and
retrocompact in `X`. Let `A = 𝒪_{X,x}`, let `Aˢʰ` be a strict henselization of `A`, let `Uˢʰ` be
the preimage of `U` under `Spec Aˢʰ ⟶ Spec A ⟶ X` and let `ū` be a geometric point of `Uˢʰ`.
Assume that the punctured spectrum of every strict henselization of `A` is connected, which is
hypothesis (2) of Stacks 0BSC at `x`. If moreover every finite étale cover of `Spec A ∖ {𝔪}`
whose base change to the punctured spectrum of `Aˢʰ` is a finite coproduct of copies of it is the
restriction of a finite étale cover of `Spec A`, then

```
π₁(Uˢʰ, ū) → π₁(U, ū) → π₁(X, ū) → 1
```

is exact in the sense of `Stacks.FundamentalGroup.IsExactSequence`: the second map is surjective,
the composite is trivial, and the kernel of the second map is the smallest closed normal subgroup
containing the image of the first. -/
theorem isExactSequence_etaleFundamentalGroupMap_puncturedOpen {X : Scheme.{u}} {x : X}
    (hs : IsClosed ({x} : Set X)) (hqc : QuasiCompact (puncturedOpen hs).ι)
    [ConnectedSpace X] [ConnectedSpace (puncturedOpen hs).toScheme]
    (hconn : IsConnectedPuncturedStrictHenselization ↥(X.presheaf.stalk x))
    (κsep : Type u) [Field κsep]
    [Algebra (maximalIdeal ↥(X.presheaf.stalk x)).ResidueField κsep]
    [IsSepClosure (maximalIdeal ↥(X.presheaf.stalk x)).ResidueField κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra ↥(X.presheaf.stalk x) Ash]
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization ↥(X.presheaf.stalk x) κsep Ash)
    (hdescent : ∀ V : FiniteEtaleOver (puncturedSpectrum ↥(X.presheaf.stalk x)).toScheme,
      IsFiniteCoproductOfTerminal
          ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom
            (algebraMap ↥(X.presheaf.stalk x) Ash)) ∣_
              puncturedSpectrum ↥(X.presheaf.stalk x))).obj V) →
        (finiteEtaleBaseChange (puncturedSpectrum ↥(X.presheaf.stalk x)).ι).essImage V)
    (w : GeometricPoint ((Spec.map (CommRingCat.ofHom
      (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ⁻¹ᵁ
        puncturedOpen hs).toScheme) :
    letI : ConnectedSpace ((Spec.map (CommRingCat.ofHom
        (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hs) :=
      connectedSpace_preimage_puncturedOpen_of_isStrictHenselization hs κsep Ash hAsh
        (hconn κsep Ash hAsh)
    IsExactSequence
      (etaleFundamentalGroupMap ((Spec.map (CommRingCat.ofHom
        (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ∣_ puncturedOpen hs) w)
      (etaleFundamentalGroupMap (puncturedOpen hs).ι
        (w.map ((Spec.map (CommRingCat.ofHom (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫
          X.fromSpecStalk x) ∣_ puncturedOpen hs))) := by
  have : ConnectedSpace ((Spec.map (CommRingCat.ofHom
      (algebraMap ↥(X.presheaf.stalk x) Ash)) ≫ X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hs) :=
    connectedSpace_preimage_puncturedOpen_of_isStrictHenselization hs κsep Ash hAsh
      (hconn κsep Ash hAsh)
  have hrange : (Set.range (puncturedOpen hs).ι.base)ᶜ = ({x} : Set X) := by
    rw [Scheme.Opens.range_ι]
    simp [puncturedOpen]
  have hx : ∀ y : X, y ∉ Set.range (puncturedOpen hs).ι.base → y = x :=
    fun y hy ↦ (hrange ▸ hy : y ∈ ({x} : Set X))
  have hclosed : ∀ y : X, y ∉ Set.range (puncturedOpen hs).ι.base → IsClosed ({y} : Set X) :=
    fun y hy ↦ hx y hy ▸ hs
  have hconn' : ∀ y : X, y ∉ Set.range (puncturedOpen hs).ι.base →
      IsConnectedPuncturedStrictHenselization ↥(X.presheaf.stalk y) :=
    fun y hy ↦ hx y hy ▸ hconn
  have : IsDominant (puncturedOpen hs).ι :=
    isDominant_of_finite_isClosed_compl (puncturedOpen hs).ι
      (by rw [hrange]; exact Set.finite_singleton x) hclosed
  have : QuasiCompact (puncturedOpen hs).ι := hqc
  exact isExactSequence_etaleFundamentalGroupMap _ (puncturedOpen hs).ι w
    (fullyFaithful_finiteEtaleBaseChange_of_quasiCompact_of_isClosed_compl
      (puncturedOpen hs).ι hclosed hconn')
    (essImage_finiteEtaleBaseChange_puncturedOpen_iff hs hqc κsep Ash hAsh
      (hconn κsep Ash hAsh) hdescent w)

end AlgebraicGeometry

end
