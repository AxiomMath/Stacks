module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Locus
public import StacksFrontier.RingTheory.CohenMacaulay.LocusBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the Cohen–Macaulay locus

For a flat morphism of schemes locally of finite presentation, formation of the locus where the
morphism is Cohen–Macaulay commutes with arbitrary base change.

## Main results

* `AlgebraicGeometry.isCohenMacaulayAt_pullback_locus` identifies the Cohen–Macaulay locus of a
  base-changed morphism with the inverse image of the original locus.

## Implementation notes

The base change is the categorical pullback. Local finite presentation ensures that every fibre
of either morphism is locally Noetherian, as required by
`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulayAt`.

By `AlgebraicGeometry.isCohenMacaulayAt_set_eq_fiberLocalRing` both loci are cut out by
Cohen–Macaulayness of a fibre local ring, so the statement reduces to the invariance of that
condition under extending the residue field of the base point. That invariance is
`Algebra.IsPushout.isMaximalCohenMacaulay_iff` read through affine open neighbourhoods.

## References

* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Cohen–Macaulayness of the local ring of `Spec B` at `q'` is Cohen–Macaulayness of the local
ring of `Spec A` at its contraction, when `B` is a base change of `A` along a field
extension. -/
private theorem isCohenMacaulayLocalRing_spec_pushout_iff
    {k K A B : Type*} [Field k] [Field K] [CommRing A] [CommRing B]
    [Algebra k K] [Algebra k A] [Algebra k B] [Algebra K B] [Algebra A B]
    [IsScalarTower k K B] [IsScalarTower k A B] [Algebra.IsPushout k K A B]
    [Algebra.FiniteType k A]
    [IsNoetherianRing A] [IsNoetherianRing B] (q' : PrimeSpectrum B)
    [IsNoetherianRing ((Spec (CommRingCat.of B)).presheaf.stalk q')]
    [IsLocalRing ((Spec (CommRingCat.of B)).presheaf.stalk q')]
    [IsNoetherianRing ((Spec (CommRingCat.of A)).presheaf.stalk
      (PrimeSpectrum.comap (algebraMap A B) q'))]
    [IsLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk
      (PrimeSpectrum.comap (algebraMap A B) q'))] :
    IsCohenMacaulayLocalRing ((Spec (CommRingCat.of B)).presheaf.stalk q') ↔
      IsCohenMacaulayLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk
        (PrimeSpectrum.comap (algebraMap A B) q')) := by
  let q := PrimeSpectrum.comap (algebraMap A B) q'
  let _ : q'.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  let es := (Spec.stalkIso (CommRingCat.of B) q').commRingCatIsoToRingEquiv
  let et := (Spec.stalkIso (CommRingCat.of A) q).commRingCatIsoToRingEquiv
  rw [isCohenMacaulayLocalRing_iff_of_ringEquiv es, isCohenMacaulayLocalRing_iff_of_ringEquiv et,
    isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay,
    isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay]
  exact (Algebra.IsPushout.isMaximalCohenMacaulay_iff k K A B q.asIdeal q'.asIdeal
    (Localization.AtPrime q.asIdeal) (Localization.AtPrime q'.asIdeal)).symm

/-- Cohen–Macaulayness of a stalk is computed in an affine open neighbourhood. -/
private theorem isCohenMacaulayLocalRing_stalk_affineOpen {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (x : U) [IsAffine U.toScheme] [IsLocallyNoetherian X]
    [IsNoetherianRing ((Spec (Γ(U.toScheme, ⊤))).presheaf.stalk
      (U.toScheme.isoSpec.hom x))] :
    IsCohenMacaulayLocalRing (X.presheaf.stalk x.1) ↔
    IsCohenMacaulayLocalRing
        ((Spec (Γ(U.toScheme, ⊤))).presheaf.stalk (U.toScheme.isoSpec.hom x)) := by
  have : IsNoetherianRing (U.toScheme.presheaf.stalk x) :=
    isNoetherianRing_of_ringEquiv (X.presheaf.stalk x.1)
      (U.stalkIso x).commRingCatIsoToRingEquiv.symm
  have : IsLocalRing (U.toScheme.presheaf.stalk x) :=
    (U.stalkIso x).commRingCatIsoToRingEquiv.symm.isLocalRing
  have : IsNoetherianRing (Γ(X, U)).1 := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherianRing (Γ(U.toScheme, ⊤)).1 :=
    isNoetherianRing_of_ringEquiv (Γ(X, U)).1 U.topIso.commRingCatIsoToRingEquiv.symm
  have : IsIso (U.toScheme.isoSpec.hom.stalkMap x) :=
    (isIso_iff_isIso_stalkMap U.toScheme.isoSpec.hom).mp inferInstance |>.2 x
  exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
    (U.stalkIso x).commRingCatIsoToRingEquiv).symm.trans
    (isCohenMacaulayLocalRing_iff_of_ringEquiv
      (asIso (U.toScheme.isoSpec.hom.stalkMap x)).commRingCatIsoToRingEquiv).symm

/-- The canonical fibre point, transported along an equality of base points, maps back to its
source point. -/
private lemma fiberι_cast_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (y : Y) (h : y = f x) : f.fiberι y (h.symm ▸ f.asFiber x) = x := by
  cases h
  exact Scheme.Hom.fiberι_asFiber f x

/-- Cohen–Macaulayness of a stalk transports along an equality of points. -/
private lemma isCohenMacaulayLocalRing_stalk_congr_point {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x y : X) (h : x = y) :
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) ↔
      IsCohenMacaulayLocalRing (X.presheaf.stalk y) := by
  subst y
  rfl

/-- Cohen–Macaulayness of a stalk transports along an isomorphism of schemes. -/
private lemma isCohenMacaulayLocalRing_stalk_iso {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (e : X ≅ Y) (x : X) :
    IsCohenMacaulayLocalRing (X.presheaf.stalk x) ↔
      IsCohenMacaulayLocalRing (Y.presheaf.stalk (e.hom x)) := by
  let _ : IsIso (e.hom.stalkMap x) :=
    (isIso_iff_isIso_stalkMap e.hom).mp inferInstance |>.2 x
  exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv).symm

/-- **Cohen–Macaulayness of a stalk is insensitive to extending the ground field.** For a
cartesian square whose base is an extension of fields, the local ring of the base change at a
point is Cohen–Macaulay exactly when the local ring of the original scheme at its image is. -/
@[ega "IV 6.7.2" "special case",
  ega "IV 6.7.8" "(ii), special case",
  ega "IV 6.8.2" "(ii), special case", sga "3 VIA 1.1.1" "more general"]
private theorem isCohenMacaulayLocalRing_stalk_fieldBaseChange {X X' : Scheme.{u}}
    {k K : Type u} [Field k] [Field K] [Algebra k K] (f : X ⟶ Spec (CommRingCat.of k))
    (g : X' ⟶ Spec (CommRingCat.of K)) (u : X' ⟶ X)
    (v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (H : IsPullback u g f v) [LocallyOfFiniteType f] (x' : X')
    [IsLocallyNoetherian X] [IsLocallyNoetherian X']
    [IsNoetherianRing (X'.presheaf.stalk x')]
    [IsNoetherianRing (X.presheaf.stalk (u x'))] :
    IsCohenMacaulayLocalRing (X'.presheaf.stalk x') ↔
      IsCohenMacaulayLocalRing (X.presheaf.stalk (u x')) := by
  have : LocallyOfFiniteType g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback H ‹LocallyOfFiniteType f›
  have : IsAffineHom u :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback H.flip inferInstance
  obtain ⟨i, z, hz⟩ := X.affineCover.exists_eq (u x')
  let V : X.Opens := (X.affineCover.f i).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange _
  let xV : V := ⟨u x', ⟨z, hz⟩⟩
  let V' : X'.Opens := u ⁻¹ᵁ V
  have hV' : IsAffineOpen V' := hV.preimage u
  let xV' : V' := ⟨x', xV.2⟩
  have H' := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := ⊤) (UX := V) (UY := V')
    (by simp) (by simp) (by simp [V'])
  let uV := u.resLE V V' (by simp [V'])
  let gV := g.resLE ⊤ V' (by simp [V'])
  let fV := f.resLE ⊤ V (by simp)
  let vV := v.resLE ⊤ ⊤ (by simp)
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  have : IsAffine ((⊤ : (Spec (CommRingCat.of k)).Opens).toScheme) := isAffineOpen_top _
  have : IsAffine ((⊤ : (Spec (CommRingCat.of K)).Opens).toScheme) := isAffineOpen_top _
  have hPO : IsPushout (fV.appTop) (vV.appTop) (uV.appTop) (gV.appTop) :=
    isPushout_appTop_of_isPullback H'
  let R := (Γ(((⊤ : (Spec (CommRingCat.of k)).Opens).toScheme), ⊤)).1
  let K₀ := (Γ(((⊤ : (Spec (CommRingCat.of K)).Opens).toScheme), ⊤)).1
  let A := (Γ(V.toScheme, ⊤)).1
  let B := (Γ(V'.toScheme, ⊤)).1
  let eR : R ≃+* k :=
    (Scheme.Opens.topIso (⊤ : (Spec (CommRingCat.of k)).Opens)).trans
      (Scheme.ΓSpecIso (CommRingCat.of k)) |>.commRingCatIsoToRingEquiv
  let eK : K₀ ≃+* K :=
    (Scheme.Opens.topIso (⊤ : (Spec (CommRingCat.of K)).Opens)).trans
      (Scheme.ΓSpecIso (CommRingCat.of K)) |>.commRingCatIsoToRingEquiv
  let _ : Nontrivial R := eR.symm.injective.nontrivial
  let _ : Nontrivial K₀ := eK.symm.injective.nontrivial
  let _ : Field R := Field.ofIsUnitOrEqZero (by
    intro r
    by_cases hr : r = 0
    · exact Or.inr hr
    · left
      have hne : eR r ≠ 0 := fun h => hr (eR.injective (by simpa using h))
      have hu : IsUnit (eR r) := (isUnit_iff_ne_zero).2 hne
      simpa using IsUnit.map eR.symm hu)
  let _ : Field K₀ := Field.ofIsUnitOrEqZero (by
    intro r
    by_cases hr : r = 0
    · exact Or.inr hr
    · left
      have hne : eK r ≠ 0 := fun h => hr (eK.injective (by simpa using h))
      have hu : IsUnit (eK r) := (isUnit_iff_ne_zero).2 hne
      simpa using IsUnit.map eK.symm hu)
  let _ : Algebra R K₀ := vV.appTop.hom.toAlgebra
  let _ : Algebra R A := fV.appTop.hom.toAlgebra
  let _ : Algebra K₀ B := gV.appTop.hom.toAlgebra
  let _ : Algebra A B := uV.appTop.hom.toAlgebra
  let _ : Algebra R B := (uV.appTop.hom.comp fV.appTop.hom).toAlgebra
  have hcomm : uV.appTop.hom.comp fV.appTop.hom =
      gV.appTop.hom.comp vV.appTop.hom := by
    ext x
    have h := congrArg (fun e : Γ(((⊤ : (Spec (CommRingCat.of k)).Opens).toScheme), ⊤) ⟶
        Γ(V'.toScheme, ⊤) => e x) (congrArg Scheme.Hom.appTop H'.w)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, RingHom.comp_apply] using h
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R K₀ B := IsScalarTower.of_algebraMap_eq' hcomm
  let _ : Algebra.IsPushout R K₀ A B :=
    (CommRingCat.isPushout_iff_isPushout).mp hPO.flip
  let _ : LocallyOfFiniteType fV := by
    change LocallyOfFiniteType (f.resLE ⊤ V _)
    delta Scheme.Hom.resLE
    let hAffine := HasRingHomProperty.HasAffineProperty @LocallyOfFiniteType
    let _ : IsZariskiLocalAtTarget @LocallyOfFiniteType :=
      (HasAffineProperty.iff.mp hAffine).1
    let _ : LocallyOfFiniteType (f ∣_ (⊤ : (Spec (CommRingCat.of k)).Opens)) :=
      IsZariskiLocalAtTarget.restrict ‹LocallyOfFiniteType f› _
    let _ : LocallyOfFiniteType (X.homOfLE (show V ≤ f ⁻¹ᵁ ⊤ from by simp)) :=
      locallyOfFiniteType_of_isOpenImmersion _
    exact locallyOfFiniteType_comp _ _
  let _ : LocallyOfFiniteType gV := by
    change LocallyOfFiniteType (g.resLE ⊤ V' _)
    delta Scheme.Hom.resLE
    let hAffine := HasRingHomProperty.HasAffineProperty @LocallyOfFiniteType
    let _ : IsZariskiLocalAtTarget @LocallyOfFiniteType :=
      (HasAffineProperty.iff.mp hAffine).1
    let _ : LocallyOfFiniteType (g ∣_ (⊤ : (Spec (CommRingCat.of K)).Opens)) :=
      IsZariskiLocalAtTarget.restrict ‹LocallyOfFiniteType g› _
    let _ : LocallyOfFiniteType (X'.homOfLE (show V' ≤ g ⁻¹ᵁ ⊤ from by simp)) :=
      locallyOfFiniteType_of_isOpenImmersion _
    exact locallyOfFiniteType_comp _ _
  let _ : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.appTop @LocallyOfFiniteType fV inferInstance)
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  let _ : IsNoetherianRing B := by
    let _ : Algebra.FiniteType K₀ B := RingHom.finiteType_algebraMap.mp
      (HasRingHomProperty.appTop @LocallyOfFiniteType gV inferInstance)
    exact Algebra.FiniteType.isNoetherianRing K₀ B
  let _ : IsLocallyNoetherian (Spec (CommRingCat.of A)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  let _ : IsLocallyNoetherian (Spec (CommRingCat.of B)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  let q' : PrimeSpectrum B := V'.toScheme.isoSpec.hom xV'
  let q : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q'
  have hxmap : uV xV' = xV := by
    apply Subtype.ext
    rw [Scheme.Hom.coe_resLE_apply]
  have hq : q = V.toScheme.isoSpec.hom xV := by
    change Spec.map (uV.appTop) q' = V.toScheme.isoSpec.hom xV
    have hnat := congrArg (fun F => F xV') (Scheme.isoSpec_hom_naturality uV)
    change Spec.map (uV.appTop) q' = V.toScheme.isoSpec.hom (uV xV') at hnat
    rwa [hxmap] at hnat
  let eB := (Spec.stalkIso (CommRingCat.of B) q').commRingCatIsoToRingEquiv
  let eA := (Spec.stalkIso (CommRingCat.of A) q).commRingCatIsoToRingEquiv
  let _ : IsNoetherianRing ((Spec (CommRingCat.of B)).presheaf.stalk q') :=
    isNoetherianRing_of_ringEquiv (Localization.AtPrime q'.asIdeal) eB.symm
  let _ : IsNoetherianRing ((Spec (CommRingCat.of A)).presheaf.stalk q) :=
    isNoetherianRing_of_ringEquiv (Localization.AtPrime q.asIdeal) eA.symm
  let _ : IsLocalRing ((Spec (CommRingCat.of B)).presheaf.stalk q') := eB.symm.isLocalRing
  let _ : IsLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk q) := eA.symm.isLocalRing
  have hCMspec' : IsCohenMacaulayLocalRing ((Spec (CommRingCat.of B)).presheaf.stalk q') ↔
      IsCohenMacaulayLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk q) := by
    simpa [q] using isCohenMacaulayLocalRing_spec_pushout_iff
      (k := R) (K := K₀) (A := A) (B := B) q'
  have hOpen' := isCohenMacaulayLocalRing_stalk_affineOpen V' hV' xV'
  have hOpen := isCohenMacaulayLocalRing_stalk_affineOpen V hV xV
  rw [← hq] at hOpen
  exact hOpen'.trans (hCMspec'.trans hOpen.symm)

/-- **Stacks Project, Tag 045U (base change).** The Cohen–Macaulay locus of a flat, locally
finitely presented morphism commutes with arbitrary base change. -/
@[stacks 045U "cm_locus_base_change", ega "IV 6.8.2" "(ii), special case"]
public theorem isCohenMacaulayAt_pullback_locus {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    let f' := pullback.snd f g
    let g' := pullback.fst f g
    let hf : ∀ s : S, IsLocallyNoetherian (f.fiber s) := fun s =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f s
    let hf' : ∀ s' : S', IsLocallyNoetherian (f'.fiber s') := fun s' =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f' s'
    {x' : (pullback f g : Scheme) | Scheme.Hom.IsCohenMacaulayAt f' hf' x'} =
      g'.base ⁻¹' {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x} := by
  classical
  dsimp only
  rw [isCohenMacaulayAt_set_eq_fiberLocalRing, isCohenMacaulayAt_set_eq_fiberLocalRing]
  ext x'
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  let s' := (pullback.snd f g) x'
  let s := g s'
  let xF : (pullback.snd f g).fiber s' := (pullback.snd f g).asFiber x'
  let hf : ∀ s : S, IsLocallyNoetherian (f.fiber s) := fun s =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f s
  let f' := pullback.snd f g
  let hf' : ∀ s' : S', IsLocallyNoetherian (f'.fiber s') := fun s' =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f' s'
  have hBase := IsPullback.of_hasPullback f g
  let uF := pullback.map _ _ _ _ (pullback.fst f g)
    (Spec.map (g.residueFieldMap s')) g hBase.w.symm
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g s').symm
  let Hfiber := isPullback_fiberToSpecResidueField_of_isPullback hBase s'
  have hs0 : g ((pullback.snd f g) x') = f ((pullback.fst f g) x') := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : pullback f g ⟶ S => q.base x') pullback.condition.symm
  let x0 : f.fiber (g s') := hs0.symm ▸ f.asFiber (pullback.fst f g x')
  have hmap : uF ≫ f.fiberι (g s') =
      (pullback.snd f g).fiberι s' ≫ pullback.fst f g := by
    dsimp [uF, Scheme.Hom.fiberι, Scheme.Hom.fiber, pullback.map]
    exact pullback.lift_fst _ _ _
  have hx0 : uF xF = x0 := by
    apply (f.fiberι s).isEmbedding.injective
    calc
      (f.fiberι s) (uF xF) = (uF ≫ f.fiberι s) xF :=
        (Scheme.Hom.comp_apply uF (f.fiberι s) xF).symm
      _ = ((pullback.snd f g).fiberι s' ≫ pullback.fst f g) xF := by
        rw [hmap]
        rfl
      _ = pullback.fst f g x' := by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]
      _ = (f.fiberι s) x0 :=
        (fiberι_cast_asFiber f (pullback.fst f g x') (g s') hs0).symm
  let _ : IsLocallyNoetherian ((pullback.snd f g).fiber s') := hf' s'
  let _ : IsLocallyNoetherian (f.fiber s) := hf s
  let gF := (pullback.snd f g).fiberToSpecResidueField s'
  let _ : Algebra (S.residueField (g s')) (S'.residueField s') :=
    (g.residueFieldMap s').hom.toAlgebra
  let _ : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  have hCM := isCohenMacaulayLocalRing_stalk_fieldBaseChange
    (k := S.residueField (g s')) (K := S'.residueField s')
    (f := f.fiberToSpecResidueField s)
    (g := gF)
    (u := uF)
    (v := Spec.map (g.residueFieldMap s'))
    Hfiber xF
  let eFiberHom := pullback.map f (S.fromSpecResidueField (g s')) f
    (S.fromSpecResidueField (f (pullback.fst f g x'))) (𝟙 _)
    (Spec.map (S.residueFieldCongr hs0).symm.hom) (𝟙 _) (by simp)
    (Scheme.residueFieldCongr_fromSpecResidueField hs0.symm).symm
  let _ : IsIso (Spec.map (S.residueFieldCongr hs0).symm.hom) := inferInstance
  let hIsoFiber : IsIso eFiberHom := by
    dsimp [eFiberHom]
    apply pullback.map_isIso
  let eFiber : f.fiber (g s') ≅ f.fiber (f (pullback.fst f g x')) :=
    @asIso Scheme _ _ _ eFiberHom hIsoFiber
  have hmapFiber : eFiber.hom ≫ f.fiberι (f (pullback.fst f g x')) =
      f.fiberι (g s') := by
    change eFiberHom ≫ pullback.fst f (S.fromSpecResidueField
      (f (pullback.fst f g x'))) = pullback.fst f (S.fromSpecResidueField (g s'))
    dsimp [eFiberHom, pullback.map]
    rw [pullback.lift_fst]
    simp
  have hpt : eFiber.hom x0 = f.asFiber (pullback.fst f g x') := by
    apply (f.fiberι (f (pullback.fst f g x'))).isEmbedding.injective
    calc
      (f.fiberι (f (pullback.fst f g x'))) (eFiber.hom x0) =
          (eFiber.hom ≫ f.fiberι (f (pullback.fst f g x'))) x0 :=
        (Scheme.Hom.comp_apply eFiber.hom _ x0).symm
      _ = (f.fiberι (g s')) x0 := by rw [hmapFiber]
      _ = pullback.fst f g x' :=
        fiberι_cast_asFiber f (pullback.fst f g x') (g s') hs0
      _ = (f.fiberι (f (pullback.fst f g x'))) (f.asFiber (pullback.fst f g x')) := by simp
  let _ : IsLocallyNoetherian (f.fiber (f (pullback.fst f g x'))) :=
    hf (f (pullback.fst f g x'))
  exact hCM.trans <| (isCohenMacaulayLocalRing_stalk_congr_point
    (X := f.fiber s) (uF xF) x0 hx0).trans
    ((isCohenMacaulayLocalRing_stalk_iso eFiber x0).trans
    (isCohenMacaulayLocalRing_stalk_congr_point
      (X := f.fiber (f (pullback.fst f g x')))
      (eFiber.hom x0) (f.asFiber (pullback.fst f g x')) hpt))

end AlgebraicGeometry
