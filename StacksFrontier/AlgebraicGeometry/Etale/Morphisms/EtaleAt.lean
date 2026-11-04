module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale morphisms over locally Noetherian schemes

For a morphism locally of finite type over a locally Noetherian scheme, étaleness at a point
means that the induced homomorphism of local rings is an étale local homomorphism. A morphism
is étale when it is étale at every point, and that pointwise stalk condition agrees with
étaleness on suitable affine neighbourhoods.

## Main definitions

* `AlgebraicGeometry.IsEtaleAt` is étaleness at a point, in terms of local rings.

## Main results

* `AlgebraicGeometry.etale_iff_forall_isEtaleAt` identifies the global notion of an étale
  morphism with the pointwise local-ring condition.
* `AlgebraicGeometry.isEtaleLocalHom_iff_isEtaleAt_affine` reads étaleness of the stalk map on a
  pair of affine opens as étaleness of the algebra of sections at the corresponding prime.
* `AlgebraicGeometry.isEtaleAt_iff_etaleAt` identifies the local-ring condition at a point with
  the affine-neighbourhood condition.

## Implementation notes

A locally finite type scheme over a locally Noetherian scheme is locally Noetherian, so both
local rings in the definition are Noetherian. The pointwise predicate is an abbreviation,
letting the local-ring API be used directly. The global notion is Mathlib's
`AlgebraicGeometry.Etale`, which is the same property expressed on affine open neighbourhoods
rather than as a universal condition on stalk maps; the equivalence below records that the
affine-chart notion agrees with the all-points condition for locally finite type morphisms over
a locally Noetherian base.

## References

* [Stacks Project, Tag 0259](https://stacks.math.columbia.edu/tag/0259)
* [Stacks Project, Tag 039N](https://stacks.math.columbia.edu/tag/039N)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A locally finite type morphism over a locally Noetherian scheme is étale at
`x` when the induced local homomorphism on stalks is étale. -/
@[stacks 0259 "étale at a point", sga "1 I 4.1" "loc. Noetherian base"]
abbrev IsEtaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] : Prop :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  RingHom.IsEtaleLocalHom (f.stalkMap x).hom

add_to_stacks 0259 "étale morphism" AlgebraicGeometry.Etale
add_to_sga "1 I 4.1" AlgebraicGeometry.Etale
add_to_sga "3 XI 1.1" AlgebraicGeometry.Etale
add_to_sga "3 XI 1.6" AlgebraicGeometry.Etale
add_to_sga "4 VII 1.1" AlgebraicGeometry.Etale
add_to_ega "IV 17.3.1" AlgebraicGeometry.Etale

/-- Over a locally Noetherian scheme, a locally finite type morphism is étale
if and only if it is étale at each point in the local-ring sense. -/
@[stacks 0259 "global étaleness is étaleness at every point", sga "1 I 4.1" "loc. Noetherian base"]
theorem etale_iff_forall_isEtaleAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    AlgebraicGeometry.Etale f ↔ ∀ x : X, IsEtaleAt f x := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rw [AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified]
  refine ⟨fun ⟨_, _, _⟩ x ↦ ⟨Flat.stalkMap f x, FormallyUnramified.stalkMap f x,
    LocallyOfFiniteType.stalkMap f x⟩, fun h ↦ ⟨Flat.of_stalkMap f (fun x ↦ (h x).1),
      AlgebraicGeometry.HasRingHomProperty.of_stalkMap
        RingHom.FormallyUnramified.ofLocalizationPrime (fun x ↦ (h x).2.1), inferInstance⟩⟩

/-- Étaleness of a local homomorphism is invariant under an isomorphism of arrows. -/
private lemma isEtaleLocalHom_iff_of_arrowIso
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C] [IsNoetherianRing D]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C] [IsLocalRing D]
    (f : A →+* B) (g : C →+* D) [IsLocalHom f] [IsLocalHom g]
    (e : Arrow.mk (CommRingCat.ofHom f) ≅ Arrow.mk (CommRingCat.ofHom g)) :
    RingHom.IsEtaleLocalHom f ↔ RingHom.IsEtaleLocalHom g := by
  show f.Flat ∧ f.FormallyUnramified ∧ f.EssFiniteType ↔
    g.Flat ∧ g.FormallyUnramified ∧ g.EssFiniteType
  exact and_congr (RingHom.Flat.respectsIso.arrow_mk_iso_iff e)
    (and_congr (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff e)
      (RingHom.EssFiniteType.respectsIso.arrow_mk_iso_iff e))

/-- On a pair of affine opens, étaleness of the stalk map at `x` is étaleness of the algebra of
sections at the prime corresponding to `x`. -/
theorem isEtaleLocalHom_iff_isEtaleAt_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
    (V : Y.Opens) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    RingHom.IsEtaleLocalHom (f.stalkMap x).hom ↔
      letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      Algebra.IsEtaleAt Γ(Y, V) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  let A := Γ(Y, V)
  let B := Γ(X, U)
  let : Algebra A B := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra.FiniteType A B :=
    (RingHom.finiteType_algebraMap).mp (f.finiteType_appLE hV hU hUV)
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian (⟨V, hV⟩ : Y.affineOpens)
  let p : Ideal A := (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal
  let q : Ideal B := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hcomap : q.comap (f.appLE V U hUV).hom = p := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU)
  let : q.LiesOver p := ⟨hcomap.symm⟩
  let : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let localMap := Localization.localRingHom p q (f.appLE V U hUV).hom hcomap.symm
  exact (isEtaleLocalHom_iff_of_arrowIso (f.stalkMap x).hom localMap
    (IsAffineOpen.arrowStalkMapIso f V hV U hU hUV hxU)).trans
    (Algebra.isEtaleAt_iff_isEtaleLocalHom p q).symm

/-- **Stacks Project, Tag 039N.** For a morphism locally of finite type over a locally
Noetherian scheme, étaleness of the induced map of local rings at `x` is equivalent to
étaleness on suitable affine neighbourhoods of `x` and its image. -/
@[stacks 039N]
theorem isEtaleAt_iff_etaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    IsEtaleAt f x ↔ EtaleAt f x := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  constructor
  · intro hx
    change RingHom.IsEtaleLocalHom (f.stalkMap x).hom at hx
    obtain ⟨V, hV, hxV, _⟩ :=
      exists_isAffineOpen_mem_and_subset (show f x ∈ (⊤ : Y.Opens) by simp)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ V from hxV)
    let A := Γ(Y, V)
    let B := Γ(X, U)
    let : Algebra A B := (f.appLE V U hUV).hom.toAlgebra
    let q : Ideal B := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
    let : Algebra.IsEtaleAt A q :=
      (isEtaleLocalHom_iff_isEtaleAt_affine f x U hU hxU V hV hUV).mp hx
    let : Algebra.FiniteType A B :=
      (RingHom.finiteType_algebraMap).mp (f.finiteType_appLE hV hU hUV)
    let : IsNoetherianRing A :=
      IsLocallyNoetherian.component_noetherian (⟨V, hV⟩ : Y.affineOpens)
    let : Algebra.FinitePresentation A B :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    obtain ⟨g, hgq, hgEtale⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) q
    let W : X.Opens := X.basicOpen g
    have hW : IsAffineOpen W := hU.basicOpen g
    have hxW : x ∈ W := by
      have hpre : hU.primeIdealOf ⟨x, hxU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
        rw [hU.fromSpec_preimage_basicOpen]; exact hgq
      have hx' : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ∈ X.basicOpen g := hpre
      simpa [W, hU.fromSpec_primeIdealOf] using hx'
    have hWU : W ≤ U := Scheme.basicOpen_le X g
    have hWV : W ≤ f ⁻¹ᵁ V := hWU.trans hUV
    let : Algebra B Γ(X, W) :=
      (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, W) := hU.isLocalization_basicOpen g
    let : Algebra A Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
    have : IsScalarTower A B Γ(X, W) := IsScalarTower.of_algebraMap_eq (by
      intro r
      have hm := Scheme.Hom.appLE_map (f := f) (U := V) (V := U)
        hUV (homOfLE hWU).op
      exact (congrArg (fun φ : Γ(Y, V) ⟶ Γ(X, W) => φ.hom r) hm).symm)
    have : Algebra.Etale A Γ(X, W) :=
      let : Algebra.Etale A (Localization.Away g) := hgEtale
      Algebra.Etale.of_equiv
        ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
          Γ(X, W)).restrictScalars A)
    have hring : (f.appLE V W hWV).hom.Etale := by
      show (algebraMap A Γ(X, W)).Etale
      exact RingHom.etale_algebraMap.mpr inferInstance
    exact ⟨W, hW, hxW, V, hV, hWV, hring⟩
  · rintro ⟨U, hU, hxU, V, hV, hUV, hEtale⟩
    apply (isEtaleLocalHom_iff_isEtaleAt_affine f x U hU hxU V hV hUV).mpr
    let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    let : Algebra.Etale Γ(Y, V) Γ(X, U) := RingHom.etale_algebraMap.mpr hEtale
    infer_instance

end AlgebraicGeometry
