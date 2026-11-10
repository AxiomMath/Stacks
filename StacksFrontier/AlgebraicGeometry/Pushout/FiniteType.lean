module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.Gluing
public import StacksFrontier.RingTheory.FibreProduct
public import StacksFrontier.RingTheory.IntegralClosure.Basic

/-!
# Finite type of a pushout along a closed immersion and an integral morphism

In the standing situation of [Stacks Project, Tag 0ECI], if the base is locally Noetherian and
all three schemes of the original diagram are locally of finite type over it, then the pushout
`Y ⨿_Z X` is locally of finite type over the base.

## Main results

* `AlgebraicGeometry.pushoutToBase_locallyOfFiniteType`: the canonical structure morphism from
  the pushout is locally of finite type.

## Implementation notes

The statement is local on the base and on the pushout, so it reduces to an assertion about the
ring of sections over an affine open `V` of the pushout lying over an affine open `U` of the
base. By the identification of the sections of the pushout as a fibre product
(`AlgebraicGeometry.pushoutStructureSheaf_isPullback`) that ring is the fibre product of the
sections on `X` and on `Y` over those on `Z`, and the ring-theoretic input is then
`Algebra.FiniteType.pullback` ([Stacks Project, Tag 00IT]): a fibre product of two finite-type
algebras over a Noetherian base along a surjection and a finite map is of finite type. The
surjection is the one coming from the closed immersion `i`, and the finite map is the one coming
from the integral morphism `j`, which is of finite type because its composite with the structure
map of `Y` is.

Transporting the ring-theoretic fibre product onto the ring of sections of the pushout is the
only technical step: the two are identified by the uniqueness of a limit cone, and the
identification is checked to be an `R`-algebra map by testing it against both projections.

## References

* [Stacks Project, Tag 0E27](https://stacks.math.columbia.edu/tag/0E27)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 00IT](https://stacks.math.columbia.edu/tag/00IT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

private lemma appLE_comp_eqToHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    {V W : X.Opens} (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ f ⁻¹ᵁ U)
    (e : V = W) :
    f.appLE U V hV ≫ eqToHom (congrArg (fun V ↦ Γ(X, V)) e) = f.appLE U W hW := by
  subst W
  simp

private lemma preimage_le_preimage_of_comp {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    {h : X ⟶ S} (e : f ≫ g = h) {U : S.Opens} {V : Y.Opens} (hV : V ≤ g ⁻¹ᵁ U) :
    f ⁻¹ᵁ V ≤ h ⁻¹ᵁ U := by
  subst e
  exact fun _ hx ↦ hV hx

private lemma appLE_hom_comp_appLE_hom {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    {h : X ⟶ S} (e : f ≫ g = h) {U : S.Opens} {V : Y.Opens} {W : X.Opens}
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ f ⁻¹ᵁ V) (hW' : W ≤ h ⁻¹ᵁ U) :
    (f.appLE V W hW).hom.comp (g.appLE U V hV).hom = (h.appLE U W hW').hom := by
  subst e
  change (g.appLE U V hV ≫ f.appLE V W hW).hom = _
  rw [Scheme.Hom.appLE_comp_appLE]

private lemma appLE_hom_comp_appLE_eqToHom_hom {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    {h : X ⟶ S} (e : f ≫ g = h) {U : S.Opens} {V : Y.Opens} {W : X.Opens}
    (hW : f ⁻¹ᵁ V = W) (hV : V ≤ g ⁻¹ᵁ U) (hW' : W ≤ h ⁻¹ᵁ U) :
    (f.appLE V (f ⁻¹ᵁ V) le_rfl ≫ eqToHom (congrArg (fun W : X.Opens ↦ Γ(X, W)) hW)).hom.comp
      (g.appLE U V hV).hom = (h.appLE U W hW').hom := by
  subst e hW
  rw [eqToHom_refl, Category.comp_id]
  exact appLE_hom_comp_appLE_hom rfl hV le_rfl hW'

private theorem finiteType_of_isPullback
    {R A B C P : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R P]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (pA : P →ₐ[R] A) (pB : P →ₐ[R] B)
    (hPB : IsPullback (CommRingCat.ofHom pA.toRingHom) (CommRingCat.ofHom pB.toRingHom)
      (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom))
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (hf : Function.Surjective f) (hBC : g.toRingHom.Finite) : Algebra.FiniteType R P := by
  let pc := CommRingCat.pullbackCone
    (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)
  let lim := CommRingCat.pullbackConeIsLimit
    (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)
  let iso : CommRingCat.of (↥(f.pullback g)) ≅ CommRingCat.of P :=
    lim.conePointUniqueUpToIso hPB.isLimit
  let er : (↥(f.pullback g)) ≃+* P := iso.commRingCatIsoToRingEquiv
  have hIsoA' : pA.toRingHom.comp er.toRingHom = pc.fst.hom :=
    congrArg CommRingCat.Hom.hom (lim.conePointUniqueUpToIso_hom_comp hPB.isLimit .left)
  have hIsoB' : pB.toRingHom.comp er.toRingHom = pc.snd.hom :=
    congrArg CommRingCat.Hom.hom (lim.conePointUniqueUpToIso_hom_comp hPB.isLimit .right)
  have hmaps : CommRingCat.ofHom (er.toRingHom.comp (algebraMap R (↥(f.pullback g)))) =
      CommRingCat.ofHom (algebraMap R P) := by
    apply hPB.hom_ext
    · apply CommRingCat.hom_ext
      change pA.toRingHom.comp (er.toRingHom.comp (algebraMap R (↥(f.pullback g)))) =
        pA.toRingHom.comp (algebraMap R P)
      rw [← RingHom.comp_assoc, hIsoA']
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]
      ext r
      rfl
    · apply CommRingCat.hom_ext
      change pB.toRingHom.comp (er.toRingHom.comp (algebraMap R (↥(f.pullback g)))) =
        pB.toRingHom.comp (algebraMap R P)
      rw [← RingHom.comp_assoc, hIsoB']
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]
      ext r
      rfl
  have he (r : R) : er (algebraMap R (↥(f.pullback g)) r) = algebraMap R P r :=
    congrArg (fun h : R →+* P => h r) (congrArg CommRingCat.Hom.hom hmaps)
  exact (Algebra.FiniteType.pullback f g hf hBC).equiv (AlgEquiv.ofRingEquiv (f := er) he)

private theorem finiteType_of_isPullback_of_comp
    {R A B C P : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing P]
    {α : R →+* A} {β : R →+* B} {γ : R →+* C} {δ : R →+* P}
    {f : A →+* C} {g : B →+* C} {pA : P →+* A} {pB : P →+* B}
    (hPB : IsPullback (CommRingCat.ofHom pA) (CommRingCat.ofHom pB)
      (CommRingCat.ofHom f) (CommRingCat.ofHom g))
    (hfα : f.comp α = γ) (hgβ : g.comp β = γ) (hpA : pA.comp δ = α) (hpB : pB.comp δ = β)
    [IsNoetherianRing R] (hα : α.FiniteType) (hβ : β.FiniteType) (hγ : γ.FiniteType)
    (hf : Function.Surjective f) (hg : g.IsIntegral) : δ.FiniteType := by
  let := α.toAlgebra
  let := β.toAlgebra
  let := γ.toAlgebra
  let := δ.toAlgebra
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp hα
  have : Algebra.FiniteType R B := RingHom.finiteType_algebraMap.mp hβ
  have hgft : g.FiniteType :=
    RingHom.FiniteType.of_comp_finiteType (f := β) (by simpa only [hgβ] using hγ)
  exact RingHom.finiteType_algebraMap.mpr <| finiteType_of_isPullback
    ⟨f, fun r ↦ DFunLike.congr_fun hfα r⟩ ⟨g, fun r ↦ DFunLike.congr_fun hgβ r⟩
    ⟨pA, fun r ↦ DFunLike.congr_fun hpA r⟩ ⟨pB, fun r ↦ DFunLike.congr_fun hpB r⟩ hPB hf
    (RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨hg, hgft⟩)

/-- **Stacks Project, Tag 0E27.** In the standing situation of [Stacks Project, Tag 0ECI], if
the base is locally Noetherian and `X`, `Y` and `Z` are locally of finite type over it, then the
pushout `Y ⨿_Z X` of [Stacks Project, Tag 0E25] is locally of finite type over the base. -/
@[stacks 0E27]
instance pushoutToBase_locallyOfFiniteType
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    [IsLocallyNoetherian s.S]
    [LocallyOfFiniteType s.pX]
    [LocallyOfFiniteType s.pY]
    [LocallyOfFiniteType s.pZ] :
    LocallyOfFiniteType (pushoutToBase s) := by
  refine ⟨?_⟩
  intro U hU V hV hVU
  let Vx := pushoutInl s ⁻¹ᵁ V
  let Vy := pushoutInr s ⁻¹ᵁ V
  let Vz := s.j ⁻¹ᵁ Vy
  have hVx : IsAffineOpen Vx := hV.preimage (pushoutInl s)
  have hVy : IsAffineOpen Vy := hV.preimage (pushoutInr s)
  have he : s.i ⁻¹ᵁ Vx = Vz := by
    dsimp [Vz, Vx, Vy]
    exact congrArg (fun f : s.Z ⟶ pushoutScheme s ↦ f ⁻¹ᵁ V)
      (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
  have hcompX : pushoutInl s ≫ pushoutToBase s = s.pX := by simp [pushoutToBase]
  have hcompY : pushoutInr s ≫ pushoutToBase s = s.pY := by simp [pushoutToBase]
  have hXbase : Vx ≤ s.pX ⁻¹ᵁ U := preimage_le_preimage_of_comp hcompX hVU
  have hYbase : Vy ≤ s.pY ⁻¹ᵁ U := preimage_le_preimage_of_comp hcompY hVU
  have hZbase : Vz ≤ s.pZ ⁻¹ᵁ U := preimage_le_preimage_of_comp s.j_over hYbase
  have : IsNoetherianRing Γ(s.S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hsurj : Function.Surjective (s.i.appLE Vx (s.i ⁻¹ᵁ Vx) le_rfl ≫
      eqToHom (congrArg (fun W : s.Z.Opens ↦ Γ(s.Z, W)) he)).hom := by
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    apply Function.Surjective.comp
    · exact (ConcreteCategory.bijective_of_isIso
        (eqToHom (congrArg (fun W : s.Z.Opens ↦ Γ(s.Z, W)) he))).2
    · simpa [Scheme.Hom.app_eq_appLE] using s.i.app_surjective Vx hVx
  have hPB : IsPullback (CommRingCat.ofHom ((pushoutInl s).appLE V Vx le_rfl).hom)
      (CommRingCat.ofHom ((pushoutInr s).appLE V Vy le_rfl).hom)
      (CommRingCat.ofHom (s.i.appLE Vx (s.i ⁻¹ᵁ Vx) le_rfl ≫
        eqToHom (congrArg (fun W : s.Z.Opens ↦ Γ(s.Z, W)) he)).hom)
      (CommRingCat.ofHom (s.j.appLE Vy Vz le_rfl).hom) := by
    simpa [Vx, Vy, Vz, Scheme.Hom.app_eq_appLE] using (pushoutStructureSheaf_isPullback s V).flip
  exact finiteType_of_isPullback_of_comp hPB
    (appLE_hom_comp_appLE_eqToHom_hom s.i_over he hXbase hZbase)
    (appLE_hom_comp_appLE_hom s.j_over hYbase le_rfl hZbase)
    (appLE_hom_comp_appLE_hom hcompX hVU le_rfl hXbase)
    (appLE_hom_comp_appLE_hom hcompY hVU le_rfl hYbase)
    (LocallyOfFiniteType.finiteType_appLE s.pX hU hVx hXbase)
    (LocallyOfFiniteType.finiteType_appLE s.pY hU hVy hYbase)
    (LocallyOfFiniteType.finiteType_appLE s.pZ hU (hVy.preimage s.j) hZbase) hsurj
    (by simpa [Scheme.Hom.app_eq_appLE] using IsIntegralHom.isIntegral_app s.j Vy hVy)

end AlgebraicGeometry

end
