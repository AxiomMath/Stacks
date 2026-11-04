module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.PurityDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.HenselizationAscent
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.QuasiFiniteTestFamily
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.QuasiFiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ImpurityDescent
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.RingTheory.Branches.Completion
public import StacksFrontier.RingTheory.Henselian.Canonicity

/-!
# Purity along a fibre over a Noetherian local ring

Let `f : X ⟶ S` be a morphism of finite type, let `ℱ` be a finite type quasi-coherent
`𝒪_X`-module and let `s` be a point of `S`. If the local ring `𝒪_{S, s}` is Noetherian then
purity of `ℱ` along the fibre `X_s` is the same as universal purity of `ℱ` along `X_s`.

One implication is formal: an impurity over an elementary étale neighbourhood of `s` is an
impurity. For the other, the base is replaced by the henselization `S^h` of `S` at `s`. Purity
ascends to `S^h`, because an impurity over an elementary étale neighbourhood of the closed point
of `S^h` produces one over the henselization of `S^h` at that point — which is `S^h` itself,
since the local ring of `S^h` there is henselian — and hence one over an elementary étale
neighbourhood of `s`. The base `S^h` is the spectrum of a henselization of `𝒪_{S, s}`, so it is
Noetherian, and over a locally Noetherian base purity implies universal purity: any impurity may
be taken with its test family quasi-finite at the distinguished point, and then with its test
family an elementary étale neighbourhood. Finally universal purity descends from `S^h` to `S`
because `S^h → S` is flat at the closed point.

## Main results

* `AlgebraicGeometry.isUniversallyPureAlong_of_isPureAlong_of_isLocallyNoetherian`: over a
  locally Noetherian base, purity along a fibre implies universal purity along that fibre.
* `AlgebraicGeometry.isPureAlong_iff_isUniversallyPureAlong_of_isNoetherianRing_stalk`: purity
  along the fibre over a point whose local ring is Noetherian is universal purity along that
  fibre.

## Implementation notes

The henselization of `S` at `s` is `AlgebraicGeometry.henselization`, the spectrum of the
henselization `AlgebraicGeometry.henselizationRing` of the local ring of `S` at `s` taken in the
chosen henselization tower. Its closed point is the closed point of that local ring, and the
canonical morphism to `S` is `AlgebraicGeometry.henselizationToBase`.

The base change of the pre-pure situation along that morphism is packaged as a
`AlgebraicGeometry.FlatPointedBaseChangeSituation`, whose canonical base change is the pre-pure
situation that flat descent of universal purity applies to.

## References

* [Stacks Project, Tag 05J8](https://stacks.math.columbia.edu/tag/05J8)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

universe u

/-- A henselization of a henselian local ring is the ring itself: the structure map is
bijective. -/
private theorem bijective_algebraMap_of_henselianLocalRing (R A : Type u) [CommRing R]
    [HenselianLocalRing R] [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsHenselization R (ResidueField R) A] : Function.Bijective (algebraMap R A) := by
  have : IsLocalHom (algebraMap R A) := IsHenselization.isLocalHom (L := ResidueField R)
  have : HenselianLocalRing A := IsHenselization.henselian R (ResidueField R)
  have hind := IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := A)
  have hres := (IsHenselization.residueField_map_bijective (R := R) (Rh := A)).surjective
  obtain ⟨f, hf, _⟩ := HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
    (R := R) (Rh := A) (Sh := R) hind hres
  have : IsLocalHom f := hf
  obtain ⟨_, _, hu⟩ := HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
    (R := R) (Rh := A) (Sh := A) hind hres
  have hcomp : IsLocalHom ((Algebra.ofId R A).comp f) := ⟨fun x hx =>
    IsLocalHom.map_nonunit (f := f) x
      (IsLocalHom.map_nonunit (f := algebraMap R A) (f x) hx)⟩
  have hid : (Algebra.ofId R A).comp f = AlgHom.id R A :=
    (hu _ hcomp).trans (hu _ ⟨fun _ hx => hx⟩).symm
  exact ⟨fun x y hxy => by simpa using congrArg f hxy,
    fun x => ⟨f x, DFunLike.congr_fun hid x⟩⟩

/-- The henselization of the spectrum of a henselian local ring at its closed point is that
spectrum: the canonical morphism to the base is an isomorphism. -/
@[ega "IV 18.6.6"]
private theorem isIso_henselizationToBase_of_henselianLocalRing (R : CommRingCat.{u})
    [HenselianLocalRing R] : IsIso (henselizationToBase (Spec R) (closedPoint R)) := by
  have : HenselianLocalRing ((Spec R).presheaf.stalk (closedPoint R)) :=
    HenselianLocalRing.of_ringEquiv (stalkClosedPointIso R).commRingCatIsoToRingEquiv.symm
  have : IsIso (CommRingCat.ofHom (algebraMap
      ((Spec R).presheaf.stalk (closedPoint R))
      (henselizationRing (Spec R) (closedPoint R)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_algebraMap_of_henselianLocalRing _ _)
  have : IsIso ((Spec R).fromSpecStalk (closedPoint R)) := by
    rw [← Spec_stalkClosedPointIso]
    infer_instance
  unfold henselizationToBase
  infer_instance

/-- The structure map from the local ring of `S` at `s` to the henselization of that local ring
is local. -/
@[ega "IV 18.6.6" "(i)"]
private instance isLocalHom_algebraMap_henselizationRing (S : Scheme.{u}) (s : S) :
    IsLocalHom (algebraMap (S.presheaf.stalk s) (henselizationRing S s)) :=
  HenselizationTower.instIsLocalHomHenselization (localHenselizationTower S s)

/-- The henselization of the local ring of `S` at `s` is flat over that local ring. -/
@[ega "IV 18.6.6" "(iii)"]
private instance flat_algebraMap_henselizationRing (S : Scheme.{u}) (s : S) :
    Module.Flat (S.presheaf.stalk s) (henselizationRing S s) :=
  HenselizationTower.instFlatHenselization (localHenselizationTower S s)

/-- The base change of a pre-pure situation along the canonical morphism from the henselization
of the base at the distinguished point, which is flat at the closed point. -/
private def henselianBaseChange (P : PrePureSituation.{u}) :
    FlatPointedBaseChangeSituation.{u} where
  X := P.X
  S := P.S
  f := P.f
  F := P.F
  s := P.s
  S' := henselization P.S P.s
  s' := closedPoint (henselizationRing P.S P.s)
  g := henselizationToBase P.S P.s
  mapsTo := by
    have : IsLocalHom (CommRingCat.ofHom
        (algebraMap (P.S.presheaf.stalk P.s) (henselizationRing P.S P.s))).hom :=
      isLocalHom_algebraMap_henselizationRing P.S P.s
    change (P.S.fromSpecStalk P.s).base
      ((Spec.map (CommRingCat.ofHom (algebraMap (P.S.presheaf.stalk P.s)
        (henselizationRing P.S P.s)))).base (closedPoint (henselizationRing P.S P.s))) = P.s
    rw [Spec_closedPoint]
    exact Scheme.fromSpecStalk_closedPoint
  flatAt := by
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap (P.S.presheaf.stalk P.s)
        (henselizationRing P.S P.s)))) :=
      Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
    have : Flat (P.S.fromSpecStalk P.s) := flat_fromSpecStalk P.S P.s
    have : Flat (henselizationToBase P.S P.s) := by
      unfold henselizationToBase
      infer_instance
    exact Flat.stalkMap (henselizationToBase P.S P.s) _

/-- The pre-pure situation over the henselization of the base at the distinguished point. -/
private abbrev henselianSituation (P : PrePureSituation.{u}) : PrePureSituation.{u} :=
  (henselianBaseChange P).baseChangedSituation

/-- An impurity diagram over the canonical base change of a flat pointed base change situation,
read as one over the original base by composing its test family with the base-change
morphism. -/
private abbrev impurityAlongBaseChangedSituation (H : FlatPointedBaseChangeSituation.{u})
    (E : ImpurityDiagram H.baseChangedSituation) :
    ImpurityDiagram H.toPrePureSituation :=
  ImpurityDiagram.alongBaseChange
    (P := H.toPrePureSituation) (Q := H.baseChangedSituation) H.g H.mapsTo
    (Limits.pullback.fst H.f H.g)
    (IsPullback.of_hasPullback _ _) E

/-- An impurity over the canonical base change of a flat pointed base change situation is an
impurity over the original base. -/
private theorem isImpurity_impurityAlongBaseChangedSituation
    (H : FlatPointedBaseChangeSituation.{u}) (E : ImpurityDiagram H.baseChangedSituation)
    (hE : IsImpurity H.baseChangedSituation E) :
    IsImpurity H.toPrePureSituation (impurityAlongBaseChangedSituation H E) :=
  isImpurity_alongBaseChange
    (P := H.toPrePureSituation) (Q := H.baseChangedSituation) H.g H.mapsTo
    (Limits.pullback.fst H.f H.g)
    (IsPullback.of_hasPullback _ _) (Iso.refl _) E hE

/-- Purity along a fibre ascends to the henselization of the base at the distinguished point. -/
private theorem isPureAlong_henselianSituation (P : PrePureSituation.{u})
    (hP : IsPureAlong P) : IsPureAlong (henselianSituation P) := by
  intro D hEtale hElem hImp
  obtain ⟨E, e, he, hE⟩ :=
    (exists_isImpurity_henselization_iff_elementaryEtaleNeighborhood
      (henselianSituation P)).mpr ⟨D, hEtale, hImp, hElem⟩
  have : HenselianLocalRing (CommRingCat.of (henselizationRing P.S P.s)) :=
    inferInstanceAs (HenselianLocalRing (henselizationRing P.S P.s))
  have hIso : IsIso (henselizationToBase (henselianSituation P).S (henselianSituation P).s) :=
    isIso_henselizationToBase_of_henselianLocalRing
      (CommRingCat.of (henselizationRing P.S P.s))
  let eH : henselization (henselianSituation P).S (henselianSituation P).s ≅
      (henselianSituation P).S := @asIso _ _ _ _ _ hIso
  have hbase : (impurityAlongBaseChangedSituation (henselianBaseChange P) E).g =
      (e ≪≫ eH).hom ≫ henselizationToBase P.S P.s := by
    show E.g ≫ henselizationToBase P.S P.s =
      (e.hom ≫ henselizationToBase (henselianSituation P).S (henselianSituation P).s) ≫
        henselizationToBase P.S P.s
    rw [he]
  obtain ⟨D₁, hEtale₁, hImp₁, hElem₁⟩ :=
    (exists_isImpurity_henselization_iff_elementaryEtaleNeighborhood P).mp
      ⟨impurityAlongBaseChangedSituation (henselianBaseChange P) E, e ≪≫ eH, hbase,
        isImpurity_impurityAlongBaseChangedSituation (henselianBaseChange P) E hE⟩
  exact hP D₁ hEtale₁ hElem₁ hImp₁

/-- Over a locally Noetherian base, purity of a finite type quasi-coherent module along the
fibre over a point implies universal purity along that fibre: an impurity can be taken with its
test family quasi-finite at the distinguished point, and then with its test family an elementary
étale neighbourhood. -/
theorem isUniversallyPureAlong_of_isPureAlong_of_isLocallyNoetherian
    (P : PrePureSituation.{u}) [IsLocallyNoetherian P.S] (hP : IsPureAlong P) :
    IsUniversallyPureAlong P := by
  intro D hD
  obtain ⟨E, hE, hEqf⟩ := exists_isImpurity_quasiFiniteAt P ⟨D, hD⟩
  obtain ⟨E', hEtale', hE', hElem'⟩ :=
    exists_isImpurity_elementaryEtaleNeighborhood_of_quasiFiniteAt P ⟨E, hE, hEqf⟩
  exact hP E' hEtale' hElem' hE'

/-- **Stacks Project, Tag 05J8.** Let `f : X ⟶ S` be of finite type, let `ℱ` be a finite type
quasi-coherent `𝒪_X`-module and let `s` be a point of `S` whose local ring `𝒪_{S, s}` is
Noetherian. Then `ℱ` is pure along the fibre `X_s` if and only if it is universally pure
along `X_s`. -/
@[stacks 05J8]
theorem isPureAlong_iff_isUniversallyPureAlong_of_isNoetherianRing_stalk
    (P : PrePureSituation.{u}) [IsNoetherianRing (P.S.presheaf.stalk P.s)] :
    IsPureAlong P ↔ IsUniversallyPureAlong P := by
  refine ⟨fun hP => ?_, fun hP D _ _ => hP D⟩
  have : IsNoetherianRing (henselizationRing P.S P.s) :=
    isNoetherianRing_of_isHenselization (P.S.presheaf.stalk P.s) (henselizationRing P.S P.s)
  have : IsLocallyNoetherian (henselianSituation P).S :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (henselizationRing P.S P.s))))
  exact universallyPureAlong_of_flatPointedBaseChange (henselianBaseChange P)
    (isUniversallyPureAlong_of_isPureAlong_of_isLocallyNoetherian (henselianSituation P)
      (isPureAlong_henselianSituation P hP))

end AlgebraicGeometry

end
