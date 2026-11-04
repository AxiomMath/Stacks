module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensor

/-!
# An affine local model for a base change of the ground field

Let `X` be a scheme over a field `k` and let `K / k` be a field extension. Above an affine open
neighbourhood `U` of a point of `X`, the base change of `X` to `K` is the spectrum of
`Γ(X, U) ⊗[k] K`. Under this description the map on local rings is the localization of the
inclusion of the left tensor factor, and the canonical map from the pushout `𝒪_{X,x} ⊗[k] K` to
the local ring of the base change is a localization at the contracted maximal ideal. This is the
local computation behind the description of the local rings of a base change in Tag 0C4Y.

## Main results

* `AlgebraicGeometry.affineBaseChangeLocalModel` gives the affine description of the inverse-image
  open and identifies the actual map on stalks with the corresponding localization map.
* `AlgebraicGeometry.stalkBaseChange_isLocalization` identifies the canonical map from the pushout
  `𝒪_{X,x} ⊗[k] K` to the target stalk as localization at its contracted maximal ideal.

## Implementation notes

The inverse image of `U` in the chosen pullback is used as the base-changed open. Equality with
an affine spectrum is represented by an isomorphism commuting with the projection to `U`. The
local-ring assertion is represented by an isomorphism in the arrow category, which records
simultaneously the identifications of both stalks and of the map between them. The pushout
characterization additionally records the maps from both tensor factors and uses
`IsLocalization.AtPrime` with the algebra structure induced by their canonical map to the stalk.
All rings lie in the universe of `CommRingCat` used by `Scheme`.

## References

* [Stacks Project, Tag 0C4Y](https://stacks.math.columbia.edu/tag/0C4Y), whose proof this is the
  local input to
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- On an affine open `U` of a `k`-scheme `X`, the structure morphism factors through
`Spec Γ(X, U) → Spec k`. -/
theorem IsAffineOpen.ι_comp_eq_isoSpec_hom_comp_SpecMap {k : Type u} [CommRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) :
    letI : Algebra k Γ(X, U) :=
      (CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom ≫ p.appLE ⊤ U (by simp)).hom.toAlgebra
    U.ι ≫ p = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) := by
  let : Algebra k Γ(X, U) :=
    (CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom ≫ p.appLE ⊤ U (by simp)).hom.toAlgebra
  have hh := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top (Spec (.of k))) hU (by simp)
  rw [IsAffineOpen.fromSpec_top, IsAffineOpen.fromSpec] at hh
  have hm : CommRingCat.ofHom (algebraMap k Γ(X, U)) =
      CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom ≫ p.appLE ⊤ U (by simp) := rfl
  have hSpec : Spec.map (CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom) =
      (Spec (.of k)).isoSpec.inv := by
    calc
      _ = inv (Spec (.of k)).toSpecΓ :=
        (IsIso.inv_eq_of_hom_inv_id (toSpecΓ_SpecMap_ΓSpecIso_inv (.of k))).symm
      _ = (Spec (.of k)).isoSpec.inv := by simp [Scheme.isoSpec]
  have hh' : Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) =
      hU.isoSpec.inv ≫ U.ι ≫ p := by
    rw [hm, Spec.map_comp, hSpec]
    exact hh
  apply (cancel_epi hU.isoSpec.inv).mp
  rw [hh']
  simp

/-- For an affine open `U` of a `k`-scheme `X` and a `k`-algebra `K`, the pullback of
`U → Spec k` along `Spec K → Spec k` is `Spec (Γ(X, U) ⊗[k] K)`, compatibly with both
projections. -/
theorem exists_iso_pullback_ι_comp_SpecMap_tensorProduct
    (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(X, U) :=
      (CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom ≫ p.appLE ⊤ U (by simp)).hom.toAlgebra
    ∃ E : pullback (U.ι ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
        Spec (.of (Γ(X, U) ⊗[k] K)),
      E.hom ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X, U) ⊗[k] K)) =
        pullback.fst _ _ ≫ hU.isoSpec.hom ∧
      E.hom ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom : K →+* Γ(X, U) ⊗[k] K)) =
        pullback.snd _ _ := by
  let : Algebra k Γ(X, U) :=
    (CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom ≫ p.appLE ⊤ U (by simp)).hom.toAlgebra
  let a : Spec (.of Γ(X, U)) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))
  let b : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hb : U.ι ≫ p = hU.isoSpec.hom ≫ a := hU.ι_comp_eq_isoSpec_hom_comp_SpecMap p
  let E₃ : pullback (U.ι ≫ p) b ≅ pullback (hU.isoSpec.hom ≫ a) b :=
    pullback.congrHom hb rfl
  let E₄ : pullback (hU.isoSpec.hom ≫ a) b ≅ pullback (hU.isoSpec.hom) (pullback.fst a b) :=
    (pullbackRightPullbackFstIso a b hU.isoSpec.hom).symm
  let E₅ : pullback (hU.isoSpec.hom) (pullback.fst a b) ≅ pullback a b :=
    asIso (pullback.snd hU.isoSpec.hom (pullback.fst a b))
  let E₆ : pullback a b ≅ Spec (.of (Γ(X, U) ⊗[k] K)) := pullbackSpecIso k Γ(X, U) K
  have hE3 : E₃.hom ≫ pullback.fst (hU.isoSpec.hom ≫ a) b = pullback.fst (U.ι ≫ p) b ∧
      E₃.hom ≫ pullback.snd (hU.isoSpec.hom ≫ a) b = pullback.snd (U.ι ≫ p) b := by
    dsimp [E₃]
    rw [pullback.congrHom_hom]
    constructor <;> simp only [pullback.map, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
  have hE4fst : E₄.hom ≫ E₅.hom ≫ pullback.fst a b =
      pullback.fst (hU.isoSpec.hom ≫ a) b ≫ hU.isoSpec.hom :=
    pullbackRightPullbackFstIso_inv_snd_fst a b hU.isoSpec.hom
  have hE4snd : E₄.hom ≫ E₅.hom ≫ pullback.snd a b =
      pullback.snd (hU.isoSpec.hom ≫ a) b :=
    pullbackRightPullbackFstIso_inv_snd_snd a b hU.isoSpec.hom
  refine ⟨E₃ ≪≫ E₄ ≪≫ E₅ ≪≫ E₆, ?_, ?_⟩
  · show E₃.hom ≫ E₄.hom ≫ E₅.hom ≫ E₆.hom ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
    dsimp [E₆]
    simp only [pullbackSpecIso_hom_fst]
    rw [hE4fst, ← Category.assoc, hE3.1]
  · show E₃.hom ≫ E₄.hom ≫ E₅.hom ≫ E₆.hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
    dsimp [E₆]
    simp only [pullbackSpecIso_hom_snd]
    rw [hE4snd, hE3.2]

/-- A commutative square `eV.hom ≫ f' = f ≫ eU.hom` whose vertical maps are isomorphisms
identifies the map `f` on stalks at `v` with the map `f'` on stalks at `eV.hom v`. -/
noncomputable def Scheme.Hom.arrowStalkMapIsoOfCommSq {V V' U U' : Scheme.{u}} (eV : V ≅ V')
    (eU : U ≅ U') (f : V ⟶ U) (f' : V' ⟶ U') (h : eV.hom ≫ f' = f ≫ eU.hom) (v : V) :
    Arrow.mk (f.stalkMap v) ≅ Arrow.mk (f'.stalkMap (eV.hom v)) := by
  have hpt : f' (eV.hom v) = eU.hom (f v) := congrArg (fun z : V ⟶ U' => z v) h
  let iUpt := U'.presheaf.stalkCongr (Inseparable.of_eq hpt)
  let iUmap := eU.hom.stalkMap (f v)
  let iVmap := eV.hom.stalkMap v
  have : IsIso iUmap := by infer_instance
  have : IsIso iVmap := by infer_instance
  let iUmap' := iUpt.hom ≫ iUmap
  have : IsIso iUmap' := by infer_instance
  have htransport : f'.stalkMap (eV.hom v) ≫ iVmap = iUmap' ≫ f.stalkMap v := by
    have hh' := Scheme.Hom.stalkMap_congr_hom (eV.hom ≫ f') (f ≫ eU.hom) h v
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hh'
    change f'.stalkMap (eV.hom v) ≫ eV.hom.stalkMap v =
      iUpt.hom ≫ eU.hom.stalkMap (f v) ≫ f.stalkMap v
    exact hh'
  refine Arrow.isoMk' _ _ (asIso iUmap').symm (asIso iVmap).symm ?_
  apply (cancel_mono iVmap).mp
  rw [Category.assoc, htransport]
  simp

/-- Let `Y = X ×_{Spec k} Spec K`. Over an affine open neighbourhood `U` of the image
of `y : Y`, the inverse-image open is `Spec (Γ(X, U) ⊗[k] K)`. If `q` is the prime
corresponding to `y` under this identification and `r` is its contraction to `Γ(X, U)`,
then the map `𝒪_{X,x} → 𝒪_{Y,y}` is identified with
`Γ(X, U)_r → (Γ(X, U) ⊗[k] K)_q`. -/
theorem affineBaseChangeLocalModel
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k))
    (y : (pullback p
      (Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec (.of K) ⟶ Spec (.of k)) : Scheme.{u}))
    (U : X.Opens) (hU : IsAffineOpen U)
    (hy : pullback.fst p
      (Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec (.of K) ⟶ Spec (.of k)) y ∈ U) :
    let f := pullback.fst p
      (Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec (.of K) ⟶ Spec (.of k))
    let V := f ⁻¹ᵁ U
    letI : Algebra k Γ(X, U) :=
      (CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom ≫ p.appLE ⊤ U (by simp)).hom.toAlgebra
    ∃ (_hV : IsAffineOpen V)
      (e : V.toScheme ≅ Spec (.of (Γ(X, U) ⊗[k] K))),
      (e.hom ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              Γ(X, U) →+* Γ(X, U) ⊗[k] K)) =
        f.resLE U V le_rfl ≫ hU.isoSpec.hom) ∧
      (e.hom ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom :
              K →+* Γ(X, U) ⊗[k] K)) =
        V.ι ≫ pullback.snd p
          (Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec (.of K) ⟶ Spec (.of k))) ∧
      let q : PrimeSpectrum (Γ(X, U) ⊗[k] K) := e.hom ⟨y, hy⟩
      (q.comap (Algebra.TensorProduct.includeLeftRingHom :
          Γ(X, U) →+* Γ(X, U) ⊗[k] K) = hU.primeIdealOf ⟨f y, hy⟩) ∧
        Nonempty (Arrow.mk (f.stalkMap y) ≅
          Arrow.mk (CommRingCat.ofHom <|
            Localization.localRingHom
              (q.comap (Algebra.TensorProduct.includeLeftRingHom :
                Γ(X, U) →+* Γ(X, U) ⊗[k] K)).asIdeal
              q.asIdeal
              (Algebra.TensorProduct.includeLeftRingHom :
                Γ(X, U) →+* Γ(X, U) ⊗[k] K) rfl)) := by
  intro g V
  let : Algebra k Γ(X, U) :=
    (CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).inv.hom ≫ p.appLE ⊤ U (by simp)).hom.toAlgebra
  let b : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsAffineHom g :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback p b).flip inferInstance
  obtain ⟨E, hEfst, hEsnd⟩ := exists_iso_pullback_ι_comp_SpecMap_tensorProduct k K X p U hU
  let E₁ : V.toScheme ≅ pullback U.ι g := (isPullback_morphismRestrict g U).isoPullback
  let E₂ : pullback U.ι g ≅ pullback (U.ι ≫ p) b := pullbackRightPullbackFstIso p b U.ι
  let e : V.toScheme ≅ Spec (.of (Γ(X, U) ⊗[k] K)) := E₁ ≪≫ E₂ ≪≫ E
  let vV : V.toScheme := ⟨y, hy⟩
  let fV : V.toScheme ⟶ U.toScheme := g.resLE U V le_rfl
  let xU : U.toScheme := fV vV
  have hres : fV = g ∣_ U := by
    dsimp [fV]
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
  have hxU : xU = ⟨g y, hy⟩ := by
    dsimp [xU]
    rw [hres]
    exact Subtype.ext (morphismRestrict_base_coe g U vV)
  let left : Γ(X, U) →+* Γ(X, U) ⊗[k] K := Algebra.TensorProduct.includeLeftRingHom
  let q : Spec (.of (Γ(X, U) ⊗[k] K)) := e.hom vV
  have hE1fst : E₁.hom ≫ pullback.fst U.ι g = fV :=
    (isPullback_morphismRestrict g U).isoPullback_hom_fst.trans hres.symm
  have hE1snd : E₁.hom ≫ pullback.snd U.ι g = V.ι :=
    (isPullback_morphismRestrict g U).isoPullback_hom_snd
  have hleftRestr : e.hom ≫ Spec.map (CommRingCat.ofHom left) = fV ≫ hU.isoSpec.hom := by
    show E₁.hom ≫ E₂.hom ≫ E.hom ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
    rw [hEfst, ← Category.assoc E₂.hom, pullbackRightPullbackFstIso_hom_fst, ← Category.assoc,
      hE1fst]
  have hright : e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom)) = V.ι ≫ pullback.snd p b := by
    show E₁.hom ≫ E₂.hom ≫ E.hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
    rw [hEsnd, pullbackRightPullbackFstIso_hom_snd, ← Category.assoc, hE1snd]
  have hprime : q.comap left = hU.primeIdealOf xU := by
    show Spec.map (CommRingCat.ofHom left) (e.hom vV) = hU.isoSpec.hom xU
    rw [← Scheme.Hom.comp_apply, hleftRestr]
    rfl
  refine ⟨hU.preimage g, e, hleftRestr, hright, ?_, ?_⟩
  · simpa [q, left, xU, hxU] using hprime
  let iActual : Arrow.mk (g.stalkMap y) ≅ Arrow.mk (fV.stalkMap vV) := by
    rw [hres]
    exact (morphismRestrictStalkMap g U vV).symm
  exact ⟨iActual.trans ((Scheme.Hom.arrowStalkMapIsoOfCommSq e hU.isoSpec fV _ hleftRestr
    vV).trans (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom left) (e.hom vV)))⟩

/-! The statement that used to stand here as `specMap_fieldToStalk` is
`AlgebraicGeometry.specMap_stalkStructureMap` of
`StacksFrontier/AlgebraicGeometry/Pullback/StalkTensor.lean`, which is public and has the same
statement and the same proof. The copy is deleted and the two consumers below use it. -/

/- `stalkMap_isIso_of_flat_preimmersion` stood here, one of four private copies of one
statement. All four are replaced by the public
`AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion`,
`StacksFrontier/AlgebraicGeometry/Pullback/StalkFromSpecStalk.lean:68`, whose proof is the same
and which every one of the four modules already imported. -/

/-- If `Y.fromSpecStalk y` factors as `Spec.map φ ≫ w` through a flat preimmersion
`w : Spec A ⟶ Y`, then `𝒪_{Y,y}` is the localization of `A` at the contraction of its maximal
ideal. -/
theorem isLocalization_atPrime_of_SpecMap_comp_eq_fromSpecStalk {A : CommRingCat.{u}}
    {Y : Scheme.{u}} {y : Y} (φ : A ⟶ Y.presheaf.stalk y) (w : Spec A ⟶ Y) [Flat w]
    [IsPreimmersion w] (hfac : Spec.map φ ≫ w = Y.fromSpecStalk y) :
    letI : Algebra A (Y.presheaf.stalk y) := φ.hom.toAlgebra
    IsLocalization.AtPrime (Y.presheaf.stalk y)
      (Ideal.comap φ.hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))) := by
  let C := Y.presheaf.stalk y
  let q : Spec A := Spec.map φ (IsLocalRing.closedPoint C)
  have : IsIso (w.stalkMap q) := isIso_stalkMap_of_flat_isPreimmersion w q
  let ρ : (Spec A).presheaf.stalk q ⟶ C := Scheme.stalkClosedPointTo (Spec.map φ)
  have hρcomp : IsIso (w.stalkMap q ≫ ρ) := by
    have h : IsIso (Scheme.stalkClosedPointTo (Spec.map φ ≫ w)) := by
      rw [hfac, Scheme.stalkClosedPointTo_fromSpecStalk]
      infer_instance
    show IsIso (w.stalkMap ((Spec.map φ) (IsLocalRing.closedPoint C)) ≫
      Scheme.stalkClosedPointTo (Spec.map φ))
    rw [← Scheme.stalkClosedPointTo_comp]
    exact h
  have : IsIso ρ := (isIso_comp_left_iff _ _).mp hρcomp
  let : Algebra A ((Spec A).presheaf.stalk q) := StructureSheaf.stalkAlgebra A q
  have hmap : CommRingCat.ofHom (algebraMap A ((Spec A).presheaf.stalk q)) ≫ ρ = φ := by
    show ((Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.germ ⊤ q trivial) ≫ ρ = φ
    rw [Category.assoc, Scheme.germ_stalkClosedPointTo_Spec]
    simp
  let e : ((Spec A).presheaf.stalk q : Type u) ≃+* C :=
    (asIso ρ).commRingCatIsoToRingEquiv
  let : Algebra A C := φ.hom.toAlgebra
  let ae : ((Spec A).presheaf.stalk q : Type u) ≃ₐ[A] C :=
    AlgEquiv.ofRingEquiv (f := e) (fun r => DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hmap) r)
  have : q.asIdeal.IsPrime := q.2
  have : IsLocalization.AtPrime ((Spec A).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A q
  exact IsLocalization.isLocalization_of_algEquiv q.asIdeal.primeCompl ae

/-- The canonical map `𝒪_{X,x} ⊗[k] K → 𝒪_{Y,y}`, represented by a pushout in
`CommRingCat`, is localization at the inverse image of the maximal ideal of `𝒪_{Y,y}`.
The two equations characterize the canonical map on both factors. This contracted ideal is
also the kernel of the composite to `κ(y)`, hence the inverse image of the prime in
`κ(x) ⊗[k] K` appearing in Tag 0C4Y. -/
theorem stalkBaseChange_isLocalization
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k))
    (y : (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    let Y := (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})
    let f : Y ⟶ X := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let g : Y ⟶ Spec (.of K) := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let a := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (f y) trivial
    let b := CommRingCat.ofHom (algebraMap k K)
    ∃ φ : pushout a b ⟶ Y.presheaf.stalk y,
      pushout.inl a b ≫ φ = f.stalkMap y ∧
      pushout.inr a b ≫ φ =
        (Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y trivial ∧
      letI : Algebra (pushout a b : CommRingCat) (Y.presheaf.stalk y) := φ.hom.toAlgebra
      IsLocalization.AtPrime (Y.presheaf.stalk y)
        (Ideal.comap φ.hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))) := by
  intro Y f g a b
  let c := (Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ y trivial
  have ha : Spec.map a = X.fromSpecStalk (f y) ≫ p := specMap_stalkStructureMap p (f y)
  have hc : Spec.map c = Y.fromSpecStalk y ≫ g := specMap_stalkStructureMap g y
  have hab : a ≫ f.stalkMap y = b ≫ c := by
    apply Spec.map_injective
    simp only [Spec.map_comp, ha, hc, ← Category.assoc]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc, Category.assoc]
    exact congrArg (Y.fromSpecStalk y ≫ ·) pullback.condition
  let φ : pushout a b ⟶ Y.presheaf.stalk y := pushout.desc (f.stalkMap y) c hab
  have hleft : pushout.inl a b ≫ φ = f.stalkMap y := pushout.inl_desc _ _ _
  have hright : pushout.inr a b ≫ φ = c := pushout.inr_desc _ _ _
  refine ⟨φ, hleft, hright, ?_⟩
  let A := pushout a b
  let w : Spec A ⟶ Y := pullback.lift
    (Spec.map (pushout.inl a b) ≫ X.fromSpecStalk (f y))
    (Spec.map (pushout.inr a b)) (by
      rw [Category.assoc, ← ha, ← Spec.map_comp, ← Spec.map_comp, pushout.condition])
  have hwleft : w ≫ f = Spec.map (pushout.inl a b) ≫ X.fromSpecStalk (f y) :=
    pullback.lift_fst _ _ _
  have hwright : w ≫ g = Spec.map (pushout.inr a b) := pullback.lift_snd _ _ _
  have hw : IsPullback w (Spec.map (pushout.inl a b)) f (X.fromSpecStalk (f y)) := by
    apply IsPullback.of_right (h₁₂ := g) (h₂₂ := p) (v₁₃ := Spec.map b) _ hwleft
      (IsPullback.of_hasPullback p (Spec.map b)).flip
    rw [hwright, ← ha]
    exact (isPullback_SpecMap_pushout a b).flip
  have : Flat (X.fromSpecStalk (f y)) := flat_fromSpecStalk X (f y)
  have : Flat w := MorphismProperty.IsStableUnderBaseChange.of_isPullback hw.flip inferInstance
  have : IsPreimmersion w :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hw.flip inferInstance
  have hfac : Spec.map φ ≫ w = Y.fromSpecStalk y := by
    apply pullback.hom_ext
    · rw [Category.assoc, hwleft, ← Category.assoc, ← Spec.map_comp, hleft]
      exact Scheme.SpecMap_stalkMap_fromSpecStalk f
    · rw [Category.assoc, hwright, ← Spec.map_comp, hright]
      exact hc
  exact isLocalization_atPrime_of_SpecMap_comp_eq_fromSpecStalk φ w hfac

end AlgebraicGeometry
