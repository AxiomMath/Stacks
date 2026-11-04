module

public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent.Olivier
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent.Gluing
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent.Cocycle
public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcEffectivity
public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumRealizations
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.CanonicalFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseLocality
public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumAlongRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumPullbackSquare
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.EffectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The descent step of the local exact sequence of a punctured spectrum

Let `(A, 𝔪)` be a local ring, `X = Spec A`, `U = X ∖ {𝔪}` its punctured spectrum, `Aˢʰ` a strict
henselization of `A`, `Xˢʰ = Spec Aˢʰ` and `Uˢʰ` the punctured spectrum of `Aˢʰ`. A finite étale
cover of `U` which becomes a finite coproduct of copies of `Uˢʰ` after base change comes from a
finite étale cover of `X`. This is the hypothesis `hdescent` of
`AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum`, which then gives
the exactness of

```
π₁(Uˢʰ, ū) → π₁(U, ū) → π₁(X, ū) → 1
```

(Stacks Tag 0BSB).

## Main definitions

* `AlgebraicGeometry.DescentDatum.resBaseDatumIsoCanonical`: the restriction of that descent datum
  to `U` is isomorphic to the canonical descent datum of `V`.

## Main results

* `AlgebraicGeometry.exists_finiteEtale_of_descentDatum`: a descent datum along a surjective flat
  quasi-compact morphism whose scheme is finite étale is effective, and the descended scheme is
  finite étale.
* `AlgebraicGeometry.essImage_finiteEtaleBaseChange_puncturedSpectrum`: a finite étale cover of `U`
  which becomes a finite coproduct of copies of `Uˢʰ` comes from a finite étale cover of `X`.
* `AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum_of_quasiCompact`:
  the exact sequence `π₁(Uˢʰ, ū) → π₁(U, ū) → π₁(X, ū) → 1`.

## References

* [Stacks Project, Tag 0BSB](https://stacks.math.columbia.edu/tag/0BSB)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.Divisors
open Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] [IsLocalRing A]
  (κsep : Type u) [Field κsep] [Algebra (maximalIdeal A).ResidueField κsep]
  [IsSepClosure (maximalIdeal A).ResidueField κsep]
  (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]

/-! ### The descent datum over the spectrum of a strict henselization -/

/-- Let `(A, 𝔪)` be a local ring with retrocompact punctured spectrum `U`, let `Aˢʰ` be a strict
henselization of `A` with connected punctured spectrum, write `f : Xˢʰ = Spec Aˢʰ ⟶ X = Spec A`,
and let `V` be a finite étale cover of `U` which becomes a finite coproduct of copies of `Uˢʰ`
after base change. Then there is a finite étale cover `Y` of `Xˢʰ` restricting to `V` on `Uˢʰ` and
a descent datum relative to `f` with underlying scheme `Y`. -/
theorem exists_descentDatum_puncturedSpectrum
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    [QuasiCompact (puncturedSpectrum A).ι]
    (w : GeometricPoint
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).toScheme)
    (V : FiniteEtaleOver (puncturedSpectrum A).toScheme)
    (hV : IsFiniteCoproductOfTerminal ((finiteEtaleBaseChange
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)).obj V)) :
    ∃ (Y : FiniteEtaleOver (Spec (CommRingCat.of Ash)))
      (D : DescentDatum (Spec.map (CommRingCat.ofHom (algebraMap A Ash)))),
      D.over = Over.mk Y.hom ∧
        Nonempty ((finiteEtaleBaseChange
            (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).ι).obj Y ≅
          (finiteEtaleBaseChange
            (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)).obj V) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) :=
    (flat_and_surjective_specMap_algebraMap_of_isStrictHenselization A κsep Ash hAsh).1
  have : ConnectedSpace (Spec (CommRingCat.of Ash)) := connectedSpace_spec_of_isLocalRing Ash
  have hcU : ConnectedSpace (puncturedSpectrum A).toScheme :=
    connectedSpace_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected
  have : ConnectedSpace
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A) :=
    connectedSpace_preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected
  have hne : ({closedPoint A}ᶜ : Set (PrimeSpectrum A)).Nonempty := by
    obtain ⟨x⟩ := hcU.toNonempty
    exact ⟨x.1, x.2⟩
  obtain ⟨Y, ⟨ε⟩⟩ := essImage_finiteEtaleBaseChange_of_isFiniteCoproductOfTerminal
    (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).ι w hV
  have hYfin : IsFinite Y.hom := Y.prop.1
  have hYet : Etale Y.hom := Y.prop.2
  have : Unramified Y.hom := inferInstance
  have : IsSeparated Y.hom := inferInstance
  have : Flat (Over.mk Y.hom).hom := inferInstanceAs (Flat Y.hom)
  refine ⟨Y, DescentDatum.ofGluingIsoPullbackFstSnd _ (puncturedSpectrum A) Y V ε
    (fullyFaithful_finiteEtaleBaseChange_pullback_puncturedSpectrum A κsep Ash hAsh
      hconnected).some
    (isDominant_preimage_puncturedSpectrum_ι_of_flat A hne _).1, rfl, ⟨ε⟩⟩

/-! ### Effectivity and the descended finite étale cover -/

/-- The scheme of a descent datum isomorphic to the canonical datum of `W` is isomorphic to the
base change of `W`. -/
private def pullbackIsoOfCanonicalIso {S X : Scheme.{u}} {f : X ⟶ S} {W : Over S}
    {D : DescentDatum f} (α : (DescentData.canonicalFunctor f).obj W ≅ D) :
    (Over.pullback f).obj W ≅ D.over :=
  (DescentData.canonicalFunctor_obj_obj f W) ▸ (DescentDatum.forget f).mapIso α

/-- Let `f : X ⟶ S` be surjective, flat and quasi-compact and let `D` be a descent datum relative
to `f` whose scheme is finite étale over `X`. Then `D` is isomorphic to the canonical descent datum
of a scheme over `S`, and that scheme is finite étale over `S`. -/
@[sga "1 IX 4.1" "partial", sga "1 VIII 7.8" "special case", sga "3 X 4.2" "partial"]
theorem exists_finiteEtale_of_descentDatum {S X : Scheme.{u}} (f : X ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] (D : DescentDatum f)
    (hfin : IsFinite D.over.hom) (het : Etale D.over.hom) :
    ∃ W : Over S, IsFinite W.hom ∧ Etale W.hom ∧
      Nonempty ((DescentData.canonicalFunctor f).obj W ≅ D) := by
  have _hF := Space.isFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  obtain ⟨W, ⟨α⟩⟩ := DescentDatum.isEffective_of_isAffineHom D
    (inferInstanceAs (IsAffineHom D.over.hom))
  have β := pullbackIsoOfCanonicalIso α
  have hw : β.hom.left ≫ D.over.hom = ((Over.pullback f).obj W).hom := Over.w β.hom
  have hiso : IsIso β.hom.left := ((Over.forget X).mapIso β).isIso_hom
  have key : ∀ (P : MorphismProperty Scheme)
      [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)],
      P (β.hom.left ≫ D.over.hom) → P W.hom := fun P _ h ↦
    MorphismProperty.of_pullback_snd_of_descendsAlong (f := W.hom) (g := f)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹Surjective f›, ‹Flat f›⟩, ‹QuasiCompact f›⟩
      (by rwa [hw] at h)
  exact ⟨W, key @IsFinite inferInstance, key @Etale inferInstance, ⟨α⟩⟩

/-- With the notation of `AlgebraicGeometry.exists_descentDatum_puncturedSpectrum`, there is a
finite étale cover `W` of `X = Spec A` whose restriction to `U` becomes isomorphic to `V` after
base change along `Uˢʰ ⟶ U`. -/
theorem exists_finiteEtaleOver_baseChange_iso_puncturedSpectrum
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    [QuasiCompact (puncturedSpectrum A).ι]
    (w : GeometricPoint
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).toScheme)
    (V : FiniteEtaleOver (puncturedSpectrum A).toScheme)
    (hV : IsFiniteCoproductOfTerminal ((finiteEtaleBaseChange
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)).obj V)) :
    ∃ W : FiniteEtaleOver (Spec (CommRingCat.of A)),
      Nonempty ((finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_
            puncturedSpectrum A)).obj
          ((finiteEtaleBaseChange (puncturedSpectrum A).ι).obj W) ≅
        (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_
          puncturedSpectrum A)).obj V) := by
  obtain ⟨hflat, hsurj⟩ :=
    flat_and_surjective_specMap_algebraMap_of_isStrictHenselization A κsep Ash hAsh
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) := hflat
  have hsu : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) := hsurj
  obtain ⟨Y, D, hDover, ⟨ε⟩⟩ :=
    exists_descentDatum_puncturedSpectrum A κsep Ash hAsh hconnected w V hV
  have hYfin : IsFinite Y.hom := Y.prop.1
  have hYet : Etale Y.hom := Y.prop.2
  obtain ⟨W₀, hWfin, hWet, ⟨α⟩⟩ := exists_finiteEtale_of_descentDatum
    (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) D
    (by rw [hDover]; exact inferInstanceAs (IsFinite Y.hom))
    (by rw [hDover]; exact inferInstanceAs (Etale Y.hom))
  have βY := pullbackIsoOfCanonicalIso α ≪≫ eqToIso hDover
  refine ⟨MorphismProperty.Over.mk ⊤ W₀.hom ⟨hWfin, hWet⟩, ⟨?_⟩⟩
  refine (finiteEtaleBaseChangeFactorIso
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)
      (puncturedSpectrum A).ι
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).ι
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)))
      (morphismRestrict_ι _ _)).app _ ≪≫ ?_
  refine (finiteEtaleBaseChange
    (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).ι).mapIso ?_ ≪≫ ε
  exact MorphismProperty.Over.isoMk ((Over.forget _).mapIso βY) (Over.w βY.hom)

/-! ### The restriction to `U` is the canonical datum of the given cover -/

namespace DescentDatum

section StepEight

variable {T₀ B : Scheme.{u}} {f : T₀ ⟶ B} {U : B.Opens} {Y : FiniteEtaleOver T₀}
  {V : FiniteEtaleOver U.toScheme}
  (ε : (finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y ≅ (finiteEtaleBaseChange (f ∣_ U)).obj V)
  (hff : (finiteEtaleBaseChange ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι).FullyFaithful)

/-- `AlgebraicGeometry.DescentDatum.gluingPullbackIsoOfFstSndIso` for
`AlgebraicGeometry.gluingIsoPullbackFstSnd`. -/
abbrev gluingDatumIso : pullback (Y.hom ≫ f) f ≅ pullback f (Y.hom ≫ f) :=
  gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)

/-- If `u₂` is the action of `z₂` on `u₁` for `AlgebraicGeometry.DescentDatum.gluingDatumIso`,
where `z₁` and `z₂` lie over one point of `U`, then `u₂` and `u₁` have the same transport to `V`
along `ε`. -/
theorem transportPoint_actPullback_gluingIsoPullbackFstSnd {Z : Scheme.{u}}
    (u₁ u₂ : Z ⟶ Y.left) (z₁ z₂ : Z ⟶ (f ⁻¹ᵁ U).toScheme)
    (hz : z₁ ≫ (f ∣_ U) = z₂ ≫ (f ∣_ U))
    (hu₁ : u₁ ≫ Y.hom = z₁ ≫ (f ⁻¹ᵁ U).ι)
    (hu₂ : u₂ ≫ Y.hom = z₂ ≫ (f ⁻¹ᵁ U).ι)
    (hact : u₁ ≫ Y.hom ≫ f = (z₂ ≫ (f ⁻¹ᵁ U).ι) ≫ f)
    (hu₂def : u₂ = actPullback (Over.mk Y.hom) (gluingDatumIso ε hff).hom u₁
      (z₂ ≫ (f ⁻¹ᵁ U).ι) hact)
    (hp : transportPoint ε u₁ z₁ hu₁ ≫ V.hom = z₂ ≫ (f ∣_ U)) :
    transportPoint ε u₂ z₂ hu₂ = transportPoint ε u₁ z₁ hu₁ := by
  have hact' : (u₁ ≫ Y.hom) ≫ f = (z₂ ≫ (f ⁻¹ᵁ U).ι) ≫ f := by
    rw [Category.assoc]; exact hact
  have hw₁ : (pullback.lift z₁ z₂ hz ≫ (pullbackMorphismRestrictIsoPreimage f U).hom) ≫
      resFstPreimage f U = z₁ := by
    rw [Category.assoc, pullbackMorphismRestrictIsoPreimage_hom_comp_resFst, pullback.lift_fst]
  have hw₂ : (pullback.lift z₁ z₂ hz ≫ (pullbackMorphismRestrictIsoPreimage f U).hom) ≫
      resSndPreimage f U = z₂ := by
    rw [Category.assoc, pullbackMorphismRestrictIsoPreimage_hom_comp_resSnd, pullback.lift_snd]
  have hw : (pullback.lift z₁ z₂ hz ≫ (pullbackMorphismRestrictIsoPreimage f U).hom) ≫
      ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι
      = pullback.lift (u₁ ≫ Y.hom) (z₂ ≫ (f ⁻¹ᵁ U).ι) hact' := by
    rw [Category.assoc, pullbackMorphismRestrictIsoPreimage_hom_comp_ι]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, toPullbackOfMorphismRestrict_fst, ← Category.assoc, pullback.lift_fst,
        pullback.lift_fst, hu₁]
    · rw [Category.assoc, toPullbackOfMorphismRestrict_snd, ← Category.assoc, pullback.lift_snd,
        pullback.lift_snd]
  have hu₁' : u₁ ≫ Y.hom = ((pullback.lift z₁ z₂ hz ≫
      (pullbackMorphismRestrictIsoPreimage f U).hom) ≫ resFstPreimage f U) ≫
      (f ⁻¹ᵁ U).ι := by rw [hw₁, hu₁]
  have hp' : transportPoint ε u₁ ((pullback.lift z₁ z₂ hz ≫
        (pullbackMorphismRestrictIsoPreimage f U).hom) ≫ resFstPreimage f U) hu₁' ≫ V.hom
      = ((pullback.lift z₁ z₂ hz ≫ (pullbackMorphismRestrictIsoPreimage f U).hom) ≫
        resSndPreimage f U) ≫ (f ∣_ U) := by
    rw [hw₂, transportPoint_congr ε rfl hw₁ hu₁' hu₁]
    exact hp
  have hkey := actPullback_gluingIsoPullbackFstSnd f U Y V ε hff u₁ (z₂ ≫ (f ⁻¹ᵁ U).ι) hact hact'
    (pullback.lift z₁ z₂ hz ≫ (pullbackMorphismRestrictIsoPreimage f U).hom) hw hu₁' hp'
  have huu : u₂ = transportPointSymm ε (transportPoint ε u₁ z₁ hu₁) z₂ hp :=
    hu₂def.trans (hkey.trans (transportPointSymm_congr ε
      (transportPoint_congr ε rfl hw₁ hu₁' hu₁) hw₂ _ hp))
  rw [transportPoint_congr ε huu rfl hu₂ (transportPointSymm_comp_hom ε _ _ hp),
    transportPoint_transportPointSymm]

variable [Unramified Y.hom] [IsSeparated Y.hom]
  (hdense : DenseRange (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι).base)

/-- `AlgebraicGeometry.DescentDatum.ofGluingIsoPullbackFstSnd`, abbreviated. -/
abbrev gluingDatum : DescentDatum f := ofGluingIsoPullbackFstSnd f U Y V ε hff hdense

/-- The restriction to `U` of `AlgebraicGeometry.DescentDatum.gluingDatum`: a descent datum
relative to `f ∣_ U`, obtained by base change along the open immersion `U ⟶ B`. -/
abbrev resBaseDatum : DescentDatum (f ∣_ U) :=
  (baseOpenPullbackFunctor f U).functor.obj (gluingDatum ε hff hdense)

/-- The projection of the scheme of the restricted datum onto the base change of `Y`
to `Uˢʰ`. -/
abbrev resBaseDatumProj :
    (resBaseDatum ε hff hdense).over.left ⟶ ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).left :=
  ((baseOpenPullbackFunctor f U).objIso (gluingDatum ε hff hdense)).hom.left

/-- The scheme of the restricted datum is isomorphic, through `ε`, to the base change of `V`. -/
def resBaseDatumIso :
    (resBaseDatum ε hff hdense).over ≅ (Over.pullback (f ∣_ U)).obj (Over.mk V.hom) :=
  (baseOpenPullbackFunctor f U).objIso _ ≪≫
    (MorphismProperty.Over.forget (finiteEtale : MorphismProperty Scheme.{u}) ⊤
      (f ⁻¹ᵁ U).toScheme).mapIso ε

/-- The identification of the scheme of the restricted datum, on underlying schemes. -/
lemma resBaseDatumIso_hom_left :
    (resBaseDatumIso ε hff hdense).hom.left = (resBaseDatumProj ε hff hdense) ≫ ε.hom.left := rfl

/-- The projection onto the base change of `Y` lies over `Uˢʰ`. -/
lemma resBaseDatumProj_comp_hom :
    (resBaseDatumProj ε hff hdense) ≫ ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom
      = (resBaseDatum ε hff hdense).over.hom :=
  CategoryTheory.Over.w _

/-- The point of `V` determined by a generalized point of the restricted datum is the transport
along `ε` of its two components. -/
lemma resBaseDatum_transportPoint {Z : Scheme.{u}} (m : Z ⟶ (resBaseDatum ε hff hdense).over.left)
    (hm : (m ≫ (resBaseDatumProj ε hff hdense) ≫ finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y) ≫ Y.hom
      = (m ≫ (resBaseDatumProj ε hff hdense) ≫
        ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι) :
    m ≫ ((resBaseDatumProj ε hff hdense) ≫ ε.hom.left) ≫ finiteEtaleBaseChangeProj (f ∣_ U) V
      = transportPoint ε
        (m ≫ (resBaseDatumProj ε hff hdense) ≫ finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
        (m ≫ (resBaseDatumProj ε hff hdense) ≫
          ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) hm := by
  simpa only [Category.assoc] using comp_left_proj_eq_transportPoint ε
    (m ≫ (resBaseDatumProj ε hff hdense)) (by simpa only [Category.assoc] using hm)

/-- The gluing isomorphism of the restricted datum preserves the projection to `V`. -/
lemma resBaseDatum_gluing_comp_proj :
    ((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
        pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
        ((resBaseDatumProj ε hff hdense) ≫ ε.hom.left) ≫ finiteEtaleBaseChangeProj (f ∣_ U) V =
      pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
        ((resBaseDatumProj ε hff hdense) ≫ ε.hom.left) ≫ finiteEtaleBaseChangeProj (f ∣_ U) V := by
  have hL := resBaseDatum_transportPoint ε hff hdense
    (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
      pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)))
    (by simp only [Category.assoc, finiteEtaleBaseChangeProj_comp_hom])
  have hR := resBaseDatum_transportPoint ε hff hdense
    (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U))
    (by simp only [Category.assoc, finiteEtaleBaseChangeProj_comp_hom])
  simp only [Category.assoc] at hL hR ⊢
  rw [hL, hR]
  have hz₁ : pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
      resBaseDatumProj ε hff hdense ≫
      ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom
      = pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
        (resBaseDatum ε hff hdense).over.hom := by
    rw [resBaseDatumProj_comp_hom]
  have hz₂ : ((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
      pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
      resBaseDatumProj ε hff hdense ≫
      ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom
      = pullback.snd ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) := by
    rw [resBaseDatumProj_comp_hom]
    exact DescentData.gluingPullbackIso_hom_snd (resBaseDatum ε hff hdense) () ()
  have hu₁ : (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
        resBaseDatumProj ε hff hdense ≫
        finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y) ≫ Y.hom
      = (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
        resBaseDatumProj ε hff hdense ≫
        ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι := by
    simp only [Category.assoc, finiteEtaleBaseChangeProj_comp_hom]
  have hu₂ : (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
        pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
        resBaseDatumProj ε hff hdense ≫
        finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y) ≫ Y.hom
      = (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
        pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
        resBaseDatumProj ε hff hdense ≫
        ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι := by
    simp only [Category.assoc, finiteEtaleBaseChangeProj_comp_hom]
  have hz : (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
        resBaseDatumProj ε hff hdense ≫
        ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ∣_ U)
      = (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
        pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
        resBaseDatumProj ε hff hdense ≫
        ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ∣_ U) := by
    rw [hz₁, hz₂, Category.assoc]
    exact pullback.condition
  have hact : (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
        resBaseDatumProj ε hff hdense ≫
        finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y) ≫ Y.hom ≫ f
      = ((((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
        pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
        resBaseDatumProj ε hff hdense ≫
        ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι) ≫ f := by
    have e1 : ∀ {W' : Scheme.{u}} (t : W' ⟶ (f ⁻¹ᵁ U).toScheme),
        (t ≫ (f ⁻¹ᵁ U).ι) ≫ f = (t ≫ (f ∣_ U)) ≫ U.ι := by
      intro W' t
      rw [Category.assoc, Category.assoc, morphismRestrict_ι f U]
    have h2 : ((pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
          resBaseDatumProj ε hff hdense ≫
          ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι) ≫ f
        = ((((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
          pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
          resBaseDatumProj ε hff hdense ≫
          ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι) ≫ f := by
      rw [e1, e1, hz]
    rw [← Category.assoc]
    exact (congrArg (· ≫ f) hu₁).trans h2
  have hsm : (baseOpenPullbackFunctor f U).sourceMap (gluingDatum ε hff hdense)
      = pullback.lift
        (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
          resBaseDatumProj ε hff hdense ≫
          finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
        ((((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
          pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
          resBaseDatumProj ε hff hdense ≫
          ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι) hact :=
    pullback.hom_ext
      (((baseOpenPullbackFunctor f U).sourceMap_fst _).trans
        (pullback.lift_fst _ _ _).symm)
      (((baseOpenPullbackFunctor f U).sourceMap_snd _).trans
        ((congrArg (· ≫ (f ⁻¹ᵁ U).ι) hz₂.symm).trans (pullback.lift_snd _ _ _).symm))
  have htm : pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
      (resBaseDatumProj ε hff hdense) ≫ finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y
      = (baseOpenPullbackFunctor f U).targetMap (gluingDatum ε hff hdense) ≫
        pullback.snd f (Y.hom ≫ f) :=
    ((baseOpenPullbackFunctor f U).targetMap_snd _).symm
  have hu₂def : (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
        pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
        resBaseDatumProj ε hff hdense ≫
        finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
      = actPullback (Over.mk Y.hom) (gluingDatumIso ε hff).hom
        (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
          resBaseDatumProj ε hff hdense ≫
          finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
        ((((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
          pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
          resBaseDatumProj ε hff hdense ≫
          ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι) hact :=
    calc (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
          pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
          resBaseDatumProj ε hff hdense ≫
          finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
        = ((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
            (baseOpenPullbackFunctor f U).targetMap (gluingDatum ε hff hdense) ≫
            pullback.snd f (Y.hom ≫ f) := by rw [htm]
      _ = (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
            (baseOpenPullbackFunctor f U).targetMap (gluingDatum ε hff hdense)) ≫
            pullback.snd f (Y.hom ≫ f) :=
          (Category.assoc _ _ _).symm
      _ = ((baseOpenPullbackFunctor f U).sourceMap (gluingDatum ε hff hdense) ≫
            ((gluingDatum ε hff hdense).gluingPullbackIso () ()).hom) ≫
            pullback.snd f (Y.hom ≫ f) := by
          rw [(baseOpenPullbackFunctor f U).gluing _]
      _ = (pullback.lift
              (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
              resBaseDatumProj ε hff hdense ≫
              finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
              ((((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
              pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
              resBaseDatumProj ε hff hdense ≫
              ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι) hact ≫
            (gluingDatumIso ε hff).hom) ≫ pullback.snd f (Y.hom ≫ f) :=
          congrArg (· ≫ pullback.snd f (Y.hom ≫ f))
            (by rw [hsm, ofGluingIsoPullbackFstSnd_gluingPullbackIso_hom]; rfl)
      _ = actPullback (Over.mk Y.hom) (gluingDatumIso ε hff).hom
            (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
            resBaseDatumProj ε hff hdense ≫
            finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
            ((((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
            pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
            resBaseDatumProj ε hff hdense ≫
            ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ⁻¹ᵁ U).ι) hact :=
          Category.assoc _ _ _
  have hp : transportPoint ε
        (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
        resBaseDatumProj ε hff hdense ≫
        finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
        (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
        resBaseDatumProj ε hff hdense ≫
        ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) hu₁ ≫ V.hom
      = (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
        pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
        resBaseDatumProj ε hff hdense ≫
        ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) ≫ (f ∣_ U) := by
    rw [transportPoint_comp_hom, hz]
  exact transportPoint_actPullback_gluingIsoPullbackFstSnd ε hff
    (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
      resBaseDatumProj ε hff hdense ≫
      finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
    (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
      pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
      resBaseDatumProj ε hff hdense ≫
      finiteEtaleBaseChangeProj (f ⁻¹ᵁ U).ι Y)
    (pullback.fst ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) (f ∣_ U) ≫
      resBaseDatumProj ε hff hdense ≫
      ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom)
    (((resBaseDatum ε hff hdense).gluingPullbackIso () ()).hom ≫
      pullback.snd (f ∣_ U) ((resBaseDatum ε hff hdense).over.hom ≫ (f ∣_ U)) ≫
      resBaseDatumProj ε hff hdense ≫
      ((finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y).hom) hz hu₁ hu₂ hact hu₂def hp

/-- The restriction to `U` of `AlgebraicGeometry.DescentDatum.gluingDatum` is isomorphic to the
canonical descent datum of `V`. -/
def resBaseDatumIsoCanonical :
    (resBaseDatum ε hff hdense) ≅ (DescentData.canonicalFunctor (f ∣_ U)).obj (Over.mk V.hom) :=
  DescentData.isoCanonicalDatum _ (Over.mk V.hom)
      (fun _ ↦ resBaseDatumIso ε hff hdense)
      (fun _ _ ↦ resBaseDatum_gluing_comp_proj ε hff hdense) ≪≫
    ((DescentData.canonicalFunctorIso (f ∣_ U)).app (Over.mk V.hom)).symm

end StepEight

end DescentDatum

/-! ### The descent half of Stacks 0BSB, and the full exact sequence -/

/-- **The descent half of Stacks Project, Tag 0BSB.** Let `(A, 𝔪)` be a local ring with
retrocompact punctured spectrum `U`, let `Aˢʰ` be a strict henselization of `A` with connected
punctured spectrum, and write `f : Xˢʰ = Spec Aˢʰ ⟶ X = Spec A`. A finite étale cover `V` of `U`
whose base change to `Uˢʰ` is a finite coproduct of copies of `Uˢʰ` comes from a finite étale cover
of `X`. -/
theorem essImage_finiteEtaleBaseChange_puncturedSpectrum
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    [QuasiCompact (puncturedSpectrum A).ι]
    (w : GeometricPoint
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).toScheme)
    (V : FiniteEtaleOver (puncturedSpectrum A).toScheme)
    (hV : IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)).obj V)) :
    (finiteEtaleBaseChange (puncturedSpectrum A).ι).essImage V := by
  obtain ⟨hflat, hsurj⟩ :=
    flat_and_surjective_specMap_algebraMap_of_isStrictHenselization A κsep Ash hAsh
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) := hflat
  have hsu : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) := hsurj
  have : ConnectedSpace (Spec (CommRingCat.of Ash)) := connectedSpace_spec_of_isLocalRing Ash
  have hcU : ConnectedSpace (puncturedSpectrum A).toScheme :=
    connectedSpace_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected
  have : ConnectedSpace (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A) :=
    connectedSpace_preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected
  have hne : ({closedPoint A}ᶜ : Set (PrimeSpectrum A)).Nonempty := by
    obtain ⟨x⟩ := hcU.toNonempty
    exact ⟨x.1, x.2⟩
  obtain ⟨Y, ⟨ε⟩⟩ := essImage_finiteEtaleBaseChange_of_isFiniteCoproductOfTerminal
    (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).ι w hV
  have hYfin : IsFinite Y.hom := Y.prop.1
  have hYet : Etale Y.hom := Y.prop.2
  have : Unramified Y.hom := inferInstance
  have : IsSeparated Y.hom := inferInstance
  have : Flat (Over.mk Y.hom).hom := inferInstanceAs (Flat Y.hom)
  have hff := (fullyFaithful_finiteEtaleBaseChange_pullback_puncturedSpectrum A κsep Ash hAsh
    hconnected).some
  have hdense := (isDominant_preimage_puncturedSpectrum_ι_of_flat A hne
    (DescentDatum.tripleY (Over.mk Y.hom)
      (f := Spec.map (CommRingCat.ofHom (algebraMap A Ash))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A Ash)))).1
  obtain ⟨W₀, hWfin, hWet, ⟨α⟩⟩ := exists_finiteEtale_of_descentDatum
    (Spec.map (CommRingCat.ofHom (algebraMap A Ash)))
    (DescentDatum.ofGluingIsoPullbackFstSnd (Spec.map (CommRingCat.ofHom (algebraMap A Ash)))
      (puncturedSpectrum A) Y V ε hff hdense)
    (inferInstanceAs (IsFinite Y.hom)) (inferInstanceAs (Etale Y.hom))
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A) :=
    IsZariskiLocalAtTarget.restrict hsu _
  obtain ⟨θ⟩ := DescentData.nonempty_iso_of_canonicalFunctor_iso
    (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)
    ((DescentData.canonicalDatumPullbackIso
        (DescentDatum.baseOpenPullbackFunctor (Spec.map (CommRingCat.ofHom (algebraMap A Ash)))
          (puncturedSpectrum A)) W₀).symm ≪≫
      (DescentDatum.baseOpenPullbackFunctor (Spec.map (CommRingCat.ofHom (algebraMap A Ash)))
        (puncturedSpectrum A)).functor.mapIso α ≪≫
      DescentDatum.resBaseDatumIsoCanonical ε hff hdense)
  exact ⟨MorphismProperty.Over.mk ⊤ W₀.hom ⟨hWfin, hWet⟩,
    ⟨MorphismProperty.Over.isoMk ((Over.forget _).mapIso θ) (Over.w θ.hom)⟩⟩

/-- **Stacks Project, Tag 0BSB.** Let `(A, 𝔪)` be a local ring whose punctured spectrum
`U = Spec A ∖ {𝔪}` is retrocompact, let `Aˢʰ` be a strict henselization of `A` whose punctured
spectrum `Uˢʰ` is connected, and let `ū` be a geometric point of `Uˢʰ`. Then

```
π₁(Uˢʰ, ū) → π₁(U, ū) → π₁(X, ū) → 1
```

is exact: `π₁(U) → π₁(X)` is surjective, the composite is trivial, and the kernel of
`π₁(U) → π₁(X)` is the smallest closed normal subgroup containing the image of `π₁(Uˢʰ)`. -/
@[stacks 0BSB "the full exact sequence, with the descent half discharged"]
theorem isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum_of_quasiCompact
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    [QuasiCompact (puncturedSpectrum A).ι]
    (w : GeometricPoint
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).toScheme) :
    letI : ConnectedSpace (Spec (CommRingCat.of A)) := connectedSpace_spec_of_isLocalRing A
    letI : ConnectedSpace (puncturedSpectrum A).toScheme :=
      connectedSpace_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected
    letI : ConnectedSpace
        (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A) :=
      connectedSpace_preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh
        hconnected
    IsExactSequence
      (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A) w)
      (etaleFundamentalGroupMap (puncturedSpectrum A).ι
        (w.map (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A))) :=
  isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum A κsep Ash hAsh hconnected w
    (fun V hV ↦
      essImage_finiteEtaleBaseChange_puncturedSpectrum A κsep Ash hAsh hconnected w V hV)

end AlgebraicGeometry

end
