module

public import Mathlib.RingTheory.RingHom.FiniteType
public import StacksFrontier.RingTheory.ChangeOfRings.ExtendScalarsRingIso
public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.Homology.PseudoCoherent.Relative.Locality
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Pseudo-coherent ring maps are a local property

Pseudo-coherence of a ring homomorphism, `RingHom.PseudoCoherent`, which is
`Algebra.PseudoCoherent` for the algebra structure that the homomorphism induces, is shown here to
be a `RingHom.PropertyIsLocal`: it is preserved by localization away from an element of the
source, it descends along a cover of the target by standard opens, and it is stable under
composition with such a localization on either side.

## Main results

* `Algebra.PseudoCoherent.trans`: a composition of pseudo-coherent ring maps is pseudo-coherent
  (the algebra content of Stacks 0681).
* `Algebra.PseudoCoherent.of_restrictScalars`: if `R → A` and `R → B` are pseudo-coherent and
  `A → B` is an `R`-algebra map, then `A → B` is pseudo-coherent (the algebra content of
  Stacks 0683).
* `Algebra.PseudoCoherent.of_isLocalizationAway`: a localization away from an element is
  pseudo-coherent.
* `Algebra.PseudoCoherent.of_span_eq_top_target`: pseudo-coherence descends along a finite
  cover of the target by standard opens.
* `RingHom.pseudoCoherent_isLocal`: `RingHom.PseudoCoherent` satisfies
  `RingHom.PropertyIsLocal`, so that `AlgebraicGeometry.affineLocally` applies to it.
* `RingHom.isRelativelyPseudoCoherentFrom_of_iso`: relative `m`-pseudo-coherence of an object of
  the derived category only depends on its isomorphism class.
* `RingHom.localizationAwayIsoDerivedExtensionScalars`: derived localization away from an element
  agrees with the general derived extension of scalars along the localization map.

## Implementation notes

Everything rests on three results about relative pseudo-coherence of objects of the derived
category: invariance under composition with a relatively pseudo-coherent finite-type algebra
(Stacks 067D), locality on a finite cover by standard opens (Stacks 067E), and the behaviour
under localization of the base (Stacks 0679). The rings of the results proved through them
therefore live in a single universe, although `Algebra.PseudoCoherent` allows two.
`Algebra.PseudoCoherent.of_isLocalizationAway` and `Algebra.PseudoCoherent.of_ringEquiv` need none
of the three and allow two universes.

Pseudo-coherence of a localization away from an element is not proved by hand: the localization
`Localization.Away r` is flat and of finite presentation, hence perfect by Stacks 067J, hence
pseudo-coherent, and every other model of it is isomorphic to it (`Algebra.PseudoCoherent.equiv`).
The same observation applies to an isomorphism, which is `Algebra.PseudoCoherent.of_ringEquiv`;
it is what transports the statement between the arbitrary models of the two localizations in
`RingHom.pseudoCoherent_localizationAwayPreserves`. `RingHom.RespectsIso` is not stated
separately: it follows from `RingHom.pseudoCoherent_isLocal` by
`RingHom.PropertyIsLocal.respectsIso`.

The passage between a ring homomorphism and the algebra structure it induces is the usual
`RingHom.toAlgebra` bookkeeping; `RingHom.pseudoCoherent_algebraMap` is the bridge, and the
`Localization.Away.map` normalisations in the proof of
`RingHom.pseudoCoherent_localizationAwayPreserves` are forced by the fact that
`RingHom.LocalizationAwayPreserves` quantifies over arbitrary models of the two localizations.

## References

* [The Stacks Project, Definition 15.83.1 (067H)](https://stacks.math.columbia.edu/tag/067H)
* [The Stacks Project, Lemma 15.82.7 (0679)](https://stacks.math.columbia.edu/tag/0679)
* [The Stacks Project, Lemma 15.82.11 (067D)](https://stacks.math.columbia.edu/tag/067D)
* [The Stacks Project, Lemma 15.82.12 (067E)](https://stacks.math.columbia.edu/tag/067E)
* [The Stacks Project, Lemma 15.83.5 (067J)](https://stacks.math.columbia.edu/tag/067J)
* [The Stacks Project, Definition 29.14.1 (01SR)](https://stacks.math.columbia.edu/tag/01SR)
-/

open CategoryTheory CategoryTheory.Limits

namespace RingHom

universe u v

attribute [local instance] HasDerivedCategory.standard

/-! ### Composition and cancellation -/

/-- **The algebra content of Stacks 0681.** A composition of pseudo-coherent ring maps is
pseudo-coherent. -/
@[sga "6 III 1.14" "special case"]
public theorem _root_.Algebra.PseudoCoherent.trans
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hRA : Algebra.PseudoCoherent R A) (hAB : Algebra.PseudoCoherent A B) :
    Algebra.PseudoCoherent R B := by
  obtain ⟨hftRA, hrelRA⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp hRA
  obtain ⟨hftAB, hrelAB⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp hAB
  let : Algebra.FiniteType R B := Algebra.FiniteType.trans hftRA hftAB
  refine Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mpr ?_
  exact (PseudoCoherence.relativelyPseudoCoherent_iff_of_comp hrelRA _ 0).2.mp hrelAB

/-- **The algebra content of Stacks 0683.** If two algebras over `R` are pseudo-coherent over
`R`, then any `R`-algebra map between them is pseudo-coherent. -/
public theorem _root_.Algebra.PseudoCoherent.of_restrictScalars
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hRA : Algebra.PseudoCoherent R A) (hRB : Algebra.PseudoCoherent R B) :
    Algebra.PseudoCoherent A B := by
  obtain ⟨_, hRApc⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp hRA
  obtain ⟨hRBft, hRBpc⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp hRB
  have hcomp : (algebraMap A B).comp (algebraMap R A) = algebraMap R B := by
    ext r; exact (IsScalarTower.algebraMap_apply R A B r).symm
  let : Algebra.FiniteType A B := finiteType_algebraMap.mp <|
    FiniteType.of_comp_finiteType (f := algebraMap R A) (by
      rw [hcomp]
      exact finiteType_algebraMap.mpr hRBft)
  exact Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mpr
    ((PseudoCoherence.relativelyPseudoCoherent_iff_of_comp (R := R) (A := A) (B := B) hRApc
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) 0).2.mpr hRBpc)

/-- `RingHom.PseudoCoherent` is stable under composition. -/
public theorem pseudoCoherent_stableUnderComposition :
    StableUnderComposition @PseudoCoherent := by
  intro R A B _ _ _ f g hf hg
  algebraize_only [f, g, g.comp f]
  exact hf.trans hg

/-! ### Flat maps of finite presentation -/

/-- A localization away from an element is a pseudo-coherent ring map: the localization
`Localization.Away r` is flat and of finite presentation, hence perfect by Stacks 067J, and `S` is
isomorphic to it as an `R`-algebra. -/
public theorem _root_.Algebra.PseudoCoherent.of_isLocalizationAway {R : Type u} [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (r : R) [IsLocalization.Away r S] :
    Algebra.PseudoCoherent R S := by
  have : Algebra.FinitePresentation R (Localization.Away r) :=
    IsLocalization.Away.finitePresentation r
  exact (isPerfectRingMap_of_flat_of_finitePresentation R (Localization.Away r)).1.equiv
    (IsLocalization.algEquiv (Submonoid.powers r) _ S)

/-- An isomorphism of rings is a pseudo-coherent ring map: `R` is pseudo-coherent over itself by
Stacks 067J, and `e` is an isomorphism of `R`-algebras. -/
public theorem _root_.Algebra.PseudoCoherent.of_ringEquiv {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] (e : R ≃+* S) : @Algebra.PseudoCoherent R S _ _ e.toRingHom.toAlgebra := by
  algebraize [e.toRingHom]
  exact (isPerfectRingMap_of_flat_of_finitePresentation R R).1.equiv
    (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl)

/-- `RingHom.PseudoCoherent` holds for every localization away from an element. -/
public theorem pseudoCoherent_holdsForLocalizationAway :
    HoldsForLocalizationAway @PseudoCoherent := by
  intro R S _ _ _ r _
  exact pseudoCoherent_algebraMap.mpr (Algebra.PseudoCoherent.of_isLocalizationAway S r)

/-- `RingHom.PseudoCoherent` is stable under composition with a localization away from an
element, on the source and on the target. -/
public theorem pseudoCoherent_stableUnderCompositionWithLocalizationAway :
    StableUnderCompositionWithLocalizationAway @PseudoCoherent :=
  pseudoCoherent_stableUnderComposition.stableUnderCompositionWithLocalizationAway
    pseudoCoherent_holdsForLocalizationAway

/-! ### Descent along a cover of the target by standard opens -/

/-- Relative `m`-pseudo-coherence only depends on the isomorphism class of the object: if `K` is
pseudo-coherent relative to `R` from `m` on and `K ≅ L`, then so is `L`. Pseudo-coherence from
`m` on is tested after restriction of scalars along the maps out of `R`, and restriction of
scalars followed by passage to the derived category preserves isomorphisms. -/
public lemma isRelativelyPseudoCoherentFrom_of_iso
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    {K L : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ L) (m : ℤ)
    (h : PseudoCoherence.IsRelativelyPseudoCoherentFrom (R := R) K m) :
    PseudoCoherence.IsRelativelyPseudoCoherentFrom (R := R) L m := fun n f hf ↦
  StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso (h n f hf)
    ((ModuleCat.restrictScalars f.toRingHom).mapDerivedCategory.mapIso e)

/-- The derived localization away from `r` of `A`, viewed as a module over itself, is `A_r`
viewed as a module over itself. -/
@[no_expose]
private noncomputable def localizationAwaySingleIso {A : Type u} [CommRing A] (r : A) :
    (StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} r).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away r)) 0).obj
        (ModuleCat.of (Localization.Away r) (Localization.Away r)) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away r))
  letI : F.Additive := extendScalars_additive.{u, u} _
  letI : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (flat_algebraMap_iff.mpr (IsLocalization.flat (Localization.Away r) (Submonoid.powers r)))
  exact (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A A) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away r)) 0).mapIso
      (extendScalarsRingIso (algebraMap A (Localization.Away r)))

/-- **The algebra content of the descent condition (1)(c) of Stacks 01SR for pseudo-coherent
ring maps.** If finitely many elements generate the unit ideal of `C` and each localization of
`C` away from one of them is pseudo-coherent over `R`, then `C` is pseudo-coherent over `R`.
This is Stacks 067E applied to `C` as a module over itself. -/
public theorem _root_.Algebra.PseudoCoherent.of_span_eq_top_target
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    {ι : Type u} [_root_.Finite ι] (s : ι → C) (hs : Ideal.span (Set.range s) = ⊤)
    (hlocal : ∀ i, Algebra.PseudoCoherent R (Localization.Away (s i))) :
    Algebra.PseudoCoherent R C := by
  have hft : Algebra.FiniteType R C :=
    Algebra.FiniteType.of_span_eq_top_target (Set.range s) hs fun c hc ↦ by
      obtain ⟨i, rfl⟩ := hc
      infer_instance
  refine Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mpr ?_
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).obj (ModuleCat.of C C)
  have hloc : ∀ i, PseudoCoherence.IsRelativelyPseudoCoherent (R := R)
      ((StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} (s i)).obj K) := by
    intro i
    obtain ⟨_, hrel'⟩ :=
      Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp (hlocal i)
    exact fun m ↦ isRelativelyPseudoCoherentFrom_of_iso
      (localizationAwaySingleIso (s i)).symm m (hrel' m)
  exact (PseudoCoherence.relativelyPseudoCoherent_iff_localizationAway_of_span_eq_top
    (R := R) (A := C) s hs K 0).2.mp hloc

/-- `RingHom.PseudoCoherent` descends along a cover of the target by standard opens. -/
public theorem pseudoCoherent_ofLocalizationSpanTarget :
    OfLocalizationSpanTarget @PseudoCoherent := by
  rw [ofLocalizationSpanTarget_iff_finite]
  intro R S _ _ f s hs hlocal
  let : Algebra R S := f.toAlgebra
  refine pseudoCoherent_algebraMap.mpr
    (Algebra.PseudoCoherent.of_span_eq_top_target (fun r : s ↦ (r : S)) ?_ fun r ↦ ?_)
  · simpa using hs
  · have := hlocal r
    rwa [show (algebraMap S (Localization.Away (r : S))).comp f =
      algebraMap R (Localization.Away (r : S)) from
        (IsScalarTower.algebraMap_eq R S (Localization.Away (r : S))).symm,
      pseudoCoherent_algebraMap] at this

/-! ### Localization of the base -/

/-- The derived localization away from `r` is the general derived extension of scalars along the
localization map: both are left derived functors of the same exact functor, namely `· ⊗[A] A_r`,
which is exact because `A → A_r` is flat, and a left derived functor is unique up to a unique
isomorphism compatible with the two comparison transformations. -/
@[no_expose]
public noncomputable def localizationAwayIsoDerivedExtensionScalars
    {A : Type u} [CommRing A] (r : A) :
    StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} r ≅
      (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap A (Localization.Away r))).functor := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away r))
  letI : F.Additive := extendScalars_additive.{u, u} _
  letI : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (flat_algebraMap_iff.mpr (IsLocalization.flat (Localization.Away r) (Submonoid.powers r)))
  letI : PreservesColimitsOfSize.{u, u} F :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Localization.Away r))).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
    (algebraMap A (Localization.Away r))
  exact @Functor.leftDerivedUnique _ _ _ _ _ _ D.functor F.mapDerivedCategory _ _
    F.mapDerivedCategoryFactors.hom D.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    inferInstance (Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors)
    D.isLeftDerived

/-- Localizing the target of a pseudo-coherent algebra away from an element keeps it relatively
pseudo-coherent over the same base. This is Stacks 0679 with a trivial localization of the
base. -/
private lemma relativelyPseudoCoherent_localizationAway_target
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (r : S) [Algebra.FiniteType R (Localization.Away r)]
    (h : PseudoCoherence.IsRelativelyPseudoCoherent (R := R)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S))) :
    PseudoCoherence.IsRelativelyPseudoCoherent (R := R)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away r)) 0).obj
        (ModuleCat.of (Localization.Away r) (Localization.Away r))) := by
  let S' := Localization.Away r
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S)
  let : IsLocalization.Away (1 : R) R :=
    IsLocalization.away_of_isUnit_of_bijective R isUnit_one Function.bijective_id
  have hderived :
      (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap S S')).functor.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S') 0).obj (ModuleCat.of S' S') :=
    ((localizationAwayIsoDerivedExtensionScalars r).app K).symm.trans
      (localizationAwaySingleIso r)
  exact fun m ↦ isRelativelyPseudoCoherentFrom_of_iso hderived m
    ((PseudoCoherence.localization_preserves_relativePseudoCoherent
      (R := R) (Rf := R) (A := S) (Ag := S') (1 : R) r K m).1 (h m))

/-- The canonical model of the localization of a pseudo-coherent ring map away from an element
of the source is pseudo-coherent. -/
private lemma _root_.Algebra.PseudoCoherent.awayMap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    (h : @Algebra.PseudoCoherent R S _ _ f.toAlgebra) :
    @Algebra.PseudoCoherent (Localization.Away r) (Localization.Away (f r)) _ _
      (Localization.awayMap f r).toAlgebra := by
  let Rr := Localization.Away r
  let Sr := Localization.Away (f r)
  let : Algebra R S := f.toAlgebra
  let : Algebra Rr Sr := (Localization.awayMap f r).toAlgebra
  have hy : Submonoid.powers r ≤ (Submonoid.powers (f r)).comap f := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  have hmap : (Localization.awayMap f r).comp (algebraMap R Rr) = (algebraMap S Sr).comp f := by
    change (IsLocalization.map Sr f hy).comp (algebraMap R Rr) = _
    exact IsLocalization.map_comp (Q := Sr) hy
  have hfmap : algebraMap R S = f := algebraMap_toAlgebra f
  let : IsScalarTower R Rr Sr := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R S Sr, hfmap, ← hmap]
    simp [algebraMap_toAlgebra])
  let : Algebra.FiniteType S Sr :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (f r)) Sr
  let : Algebra.FiniteType R Sr :=
    Algebra.FiniteType.trans (R := R) (S := S) (A := Sr) inferInstance inferInstance
  let : Algebra.FiniteType Rr Sr := Algebra.FiniteType.of_restrictScalars_finiteType R Rr Sr
  exact Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mpr
    ((PseudoCoherence.relativelyPseudoCoherent_iff_of_comp
      (Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp
        (Algebra.PseudoCoherent.of_isLocalizationAway (R := R) Rr r)).2 _ 0).2.mpr
      (relativelyPseudoCoherent_localizationAway_target (R := R) (S := S) (r := f r)
        (Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mp h)))

/-- `RingHom.PseudoCoherent` is preserved by localization away from an element of the
source. -/
public theorem pseudoCoherent_localizationAwayPreserves :
    LocalizationAwayPreserves @PseudoCoherent := by
  intro R S _ _ f r R' S' _ _ _ _ _ _ hf
  let : Algebra R S := f.toAlgebra
  let Rr := Localization.Away r
  let Sr := Localization.Away (f r)
  let eR : R' ≃ₐ[R] Rr := IsLocalization.algEquiv (Submonoid.powers r) R' Rr
  let eS : S' ≃ₐ[S] Sr := IsLocalization.algEquiv (Submonoid.powers (f r)) S' Sr
  let : Algebra R' Rr := eR.toRingEquiv.toRingHom.toAlgebra
  let : Algebra Rr Sr := (Localization.awayMap f r).toAlgebra
  let : Algebra R' Sr :=
    ((Localization.awayMap f r).comp eR.toRingEquiv.toRingHom).toAlgebra
  let : IsScalarTower R' Rr Sr := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra Sr S' := eS.toRingEquiv.symm.toRingHom.toAlgebra
  let : Algebra R' S' :=
    (eS.toRingEquiv.symm.toRingHom.comp
      ((Localization.awayMap f r).comp eR.toRingEquiv.toRingHom)).toAlgebra
  let : IsScalarTower R' Sr S' := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp' := ((Algebra.PseudoCoherent.of_ringEquiv eR.toRingEquiv).trans
    (Algebra.PseudoCoherent.awayMap f r hf)).trans
      (Algebra.PseudoCoherent.of_ringEquiv eS.toRingEquiv.symm)
  have hy : Submonoid.powers r ≤ (Submonoid.powers (f r)).comap f := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  have hmap : IsLocalization.Away.map R' S' f r =
      eS.toRingEquiv.symm.toRingHom.comp
        ((Localization.awayMap f r).comp eR.toRingEquiv.toRingHom) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
    have hRcomm : eR.toRingEquiv.toRingHom.comp (algebraMap R R') = algebraMap R Rr := by
      ext x; exact eR.commutes x
    have hScomm : eS.toRingEquiv.symm.toRingHom.comp (algebraMap S Sr) = algebraMap S S' := by
      ext x; exact eS.symm.commutes x
    have hcancomp : (Localization.awayMap f r).comp (algebraMap R Rr) =
        (algebraMap S Sr).comp f := by
      change (IsLocalization.map Sr f hy).comp (algebraMap R Rr) = _
      exact IsLocalization.map_comp (Q := Sr) hy
    calc (IsLocalization.Away.map R' S' f r).comp (algebraMap R R')
        = (algebraMap S S').comp f := by
          change (IsLocalization.map S' f hy).comp (algebraMap R R') = _
          exact IsLocalization.map_comp (Q := S') hy
      _ = eS.toRingEquiv.symm.toRingHom.comp
            ((Localization.awayMap f r).comp
              (eR.toRingEquiv.toRingHom.comp (algebraMap R R'))) := by
          rw [hRcomm, hcancomp, ← comp_assoc, hScomm]
  change @Algebra.PseudoCoherent R' S' _ _ (IsLocalization.Away.map R' S' f r).toAlgebra
  rw [congrArg (fun g : R' →+* S' ↦ g.toAlgebra) hmap]
  exact hcomp'

/-! ### Locality -/

/-- `RingHom.PseudoCoherent` descends along a cover of the source by standard opens. -/
public theorem pseudoCoherent_ofLocalizationSpan : OfLocalizationSpan @PseudoCoherent :=
  pseudoCoherent_ofLocalizationSpanTarget.ofLocalizationSpan
    pseudoCoherent_stableUnderCompositionWithLocalizationAway.left

/-- **The affine-local conditions of Stacks 01SR for pseudo-coherent ring maps.**
Pseudo-coherence of ring maps is a local property: it is preserved by localization away from an
element of the source, it descends along a cover of the source or of the target by standard
opens, and it is stable under composition with a localization of the target away from an
element. -/
public theorem pseudoCoherent_isLocal : PropertyIsLocal @PseudoCoherent :=
  ⟨pseudoCoherent_localizationAwayPreserves, pseudoCoherent_ofLocalizationSpanTarget,
    pseudoCoherent_ofLocalizationSpan,
    pseudoCoherent_stableUnderCompositionWithLocalizationAway.right⟩

end RingHom
