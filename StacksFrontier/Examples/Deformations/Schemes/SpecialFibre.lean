module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.Examples.Geometric.Schemes
public import StacksFrontier.Examples.Deformations.Schemes.Pushout
public import StacksFrontier.Examples.Deformations.Schemes.Stalks

/-!
# The special fibre of a scheme deformation, on sections and on stalks

Let `P` be a deformation of a scheme `X` over the residue field `k` of an Artinian local base
`A`. The square identifying the special fibre of `P` with `X` is cartesian, and the closed
immersion `X ⟶ P.scheme` is affine, so over an affine open `U` of `P.scheme` the square of
coordinate rings is a pushout. This file localizes that pushout at a point of `X` and then
transports it to stalks, which produces the square

`A → 𝒪_{P.scheme, y}`, `A → k`, `𝒪_{P.scheme, y} → 𝒪_{X, x}`, `k → 𝒪_{X, x}`

as a pushout of commutative rings. In words: the local ring of `X` at `x` is the reduction of
the local ring of the deformation at the image of `x`.

## Main results

* `Deformation.Examples.residueMap_ker`: the kernel of the residue map of an object of `𝒞_Λ`
  is its maximal ideal.
* `Deformation.Examples.special_sections_localized_pushout`: the pushout square of coordinate
  rings of the special-fibre square, localized at a point.
* `Deformation.Examples.special_stalk_pushout`: the same square on stalks, for an affine open
  containing the image point with affine preimage.
* `Deformation.Examples.special_stalk_pushout_any`: the stalk square, for an arbitrary point,
  obtained by choosing an affine open from the standard affine cover.

## Implementation notes

The algebra structures on the two stalks are the ones induced by the structure morphisms, and
they are introduced by `letI` in the statements rather than being found by instance search:
a stalk is not an algebra over the base ring until the structure morphism says so, and the
morphism in question differs from statement to statement.

The identification of the localized coordinate ring with the stalk is
`AlgebraicGeometry.IsAffineOpen.arrowStalkMapIso`, used on each of the four corners; the four
compatibility squares are then checked on germs of sections, which is what
`arrowStalkMapIso_left_germ` and `Localization.localRingHom_to_map` supply.

The closed point of `Spec A` is the maximal ideal because `A` is Artinian local, so every prime
of `A` is maximal; the closed point of `Spec k` is the zero ideal.

## References

* [Stacks Project, Tag 0DZM](https://stacks.math.columbia.edu/tag/0DZM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

/-- The kernel of the residue map of an object of `𝒞_Λ` is its maximal ideal: the chosen
identification of the residue field with `k` is injective. -/
theorem residueMap_ker
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    RingHom.ker (Deformation.Artin.residueMap A) = IsLocalRing.maximalIdeal A := by
  show RingHom.ker
    (A.residueEquiv.toAlgHom.toRingHom.comp (IsLocalRing.residue A)) = _
  rw [RingHom.ker_comp_of_injective _ A.residueEquiv.injective]
  exact IsLocalRing.ker_residue

/-- For a local ring `A` and the closed point `p` of `Spec A`, the identification
`localStalkRingEquiv` of `A` with the stalk at `p`, precomposed with `Scheme.ΓSpecIso`, is the
germ map on global sections. -/
private theorem localStalkRingEquiv_germ_top
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : PrimeSpectrum A) (hp : p.asIdeal = IsLocalRing.maximalIdeal A)
    (a : Γ(Spec (.of A), ⊤)) :
    ((Scheme.ΓSpecIso (CommRingCat.of A)) ≪≫
        (localStalkRingEquiv p hp).toCommRingCatIso).hom a =
      (Spec (.of A)).presheaf.germ ⊤ p trivial a := by
  have h₁ := congrArg (fun f : CommRingCat.of Γ(Spec (.of A), ⊤) ⟶
      CommRingCat.of (Localization.AtPrime p.asIdeal) => f.hom a)
    (Spec.germ_stalkMapIso_hom (R := CommRingCat.of A) (x := p))
  have h₂ (t : A) :
      (Spec.stalkIso (CommRingCat.of A) p).hom.hom (localStalkRingEquiv p hp t) =
        algebraMap A (Localization.AtPrime p.asIdeal) t := by
    have hM : p.asIdeal.primeCompl = IsUnit.submonoid A := by
      ext b
      show b ∉ p.asIdeal ↔ IsUnit b
      rw [hp, IsLocalRing.mem_maximalIdeal]
      simp [mem_nonunits_iff]
    show (StructureSheaf.stalkIso A p).symm
      ((StructureSheaf.stalkIso A p)
        ((IsLocalization.atUnits A p.asIdeal.primeCompl hM.le).toRingEquiv t)) = _
    rw [AlgEquiv.symm_apply_apply]
    exact (IsLocalization.atUnits A p.asIdeal.primeCompl hM.le).commutes t
  apply (Spec.stalkIso (CommRingCat.of A) p).commRingCatIsoToRingEquiv.injective
  calc
    _ = algebraMap A (Localization.AtPrime p.asIdeal)
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) := h₂ _
    _ = _ := h₁.symm

/-- The localization square of `arrowStalkMapIso`, read from the global sections of an affine open
`U` whose stalk at `f x` is identified with the sections by `e`, commutes with `f.stalkMap`. -/
private theorem ofHom_localization_comp_arrowStalkMapIso_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V)
    (e : CommRingCat.of Γ(Y, U) ≅ CommRingCat.of (Y.presheaf.stalk (f x)))
    (he : ∀ a, e.hom a = Y.presheaf.germ U (f x) (hVU hx) a) :
    CommRingCat.ofHom ((algebraMap Γ(X, V)
        (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal)).comp
          (f.appLE U V hVU).hom) ≫
      (asIso (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx).hom.right).symm.hom =
    e.hom ≫ f.stalkMap x := by
  set i := IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx
  apply (cancel_mono i.hom.right).1
  have hcan : (asIso i.hom.right).symm.hom ≫ i.hom.right = 𝟙 _ := by simp
  rw [Category.assoc, hcan, Category.assoc]
  refine (Category.comp_id _).trans ?_
  rw [show f.stalkMap x ≫ i.hom.right = _ from i.hom.w.symm]
  apply CommRingCat.hom_ext
  ext a
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [he, arrowStalkMapIso_left_germ f U hU V hV hVU hx a]
  exact (Localization.localRingHom_to_map _ _ (f.appLE U V hVU).hom
    (congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (f := f) U hU V hV hVU hx)).symm a).symm

/-- The special-fibre square of a scheme deformation, read on coordinate rings over an affine
open `U` of the deformation whose preimage in `X` is affine, and then localized at a point `x`
of `X` lying over `U`. -/
theorem special_sections_localized_pushout
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (U : P.scheme.Opens) (hU : IsAffineOpen U)
    (hy : P.specialMap x ∈ U)
    (hV : IsAffineOpen (P.specialMap ⁻¹ᵁ U)) :
    let V : X.left.Opens := P.specialMap ⁻¹ᵁ U
    let hxV : x ∈ V := by change P.specialMap x ∈ U; exact hy
    let p : PrimeSpectrum Γ(P.scheme, U) := hU.primeIdealOf ⟨P.specialMap x, hy⟩
    letI : p.asIdeal.IsPrime := p.isPrime
    let q : PrimeSpectrum Γ(X.left, V) := hV.primeIdealOf ⟨x, hxV⟩
    letI : q.asIdeal.IsPrime := q.isPrime
    IsPushout
      (CommRingCat.ofHom ((algebraMap Γ(P.scheme, U)
        (Localization.AtPrime p.asIdeal)).comp (P.toBase.appLE ⊤ U (by simp)).hom))
      (CommRingCat.ofHom ((residueSpecMap P.base).appLE
        ⊤ ⊤ (by simp)).hom)
      (CommRingCat.ofHom (Localization.localRingHom p.asIdeal q.asIdeal
        ((P.specialMap.appLE U V le_rfl).hom) (by
          have hh := IsAffineOpen.comap_primeIdealOf_appLE
            (f := P.specialMap) U hU V hV le_rfl hxV
          exact (congrArg PrimeSpectrum.asIdeal hh).symm)))
      (CommRingCat.ofHom ((algebraMap Γ(X.left, V) (Localization.AtPrime q.asIdeal)).comp
        ((X.hom.appLE ⊤ V (by simp)).hom))) := by
  classical
  let V : X.left.Opens := P.specialMap ⁻¹ᵁ U
  have hxV : x ∈ V := hy
  let p : PrimeSpectrum Γ(P.scheme, U) := hU.primeIdealOf ⟨P.specialMap x, hy⟩
  let q : PrimeSpectrum Γ(X.left, V) := hV.primeIdealOf ⟨x, hxV⟩
  have : IsClosedImmersion (residueSpecMap P.base) := residueSpecMap_isClosedImmersion P.base
  have : IsClosedImmersion P.specialMap := deformationSpecialMap_isClosedImmersion P
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  let : IsAffine ((⊤ : (baseSpec P.base).Opens).toScheme) :=
    isAffineOpen_top _
  let : IsAffine ((⊤ : (Spec (.of k)).Opens).toScheme) := isAffineOpen_top _
  have eBase : U ≤ P.toBase ⁻¹ᵁ (⊤ : (baseSpec P.base).Opens) := by simp
  have eSpecK : (⊤ : (Spec (.of k)).Opens) ≤
      (residueSpecMap P.base) ⁻¹ᵁ (⊤ : (baseSpec P.base).Opens) := by simp
  have eX : V ≤ X.hom ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  have : IsClosedImmersion (P.specialMap.resLE U V le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have hpull : IsPullback (P.specialMap.resLE U V le_rfl)
      (X.hom.resLE ⊤ V eX)
      (P.toBase.resLE ⊤ U eBase)
      ((residueSpecMap P.base).resLE ⊤ ⊤ eSpecK) := by
    apply Scheme.Hom.isPullback_resLE P.specialCartesian eSpecK eBase
    simp [V]
  have hglob : IsPushout
      (CommRingCat.ofHom (P.toBase.appLE ⊤ U eBase).hom)
      (CommRingCat.ofHom ((residueSpecMap P.base).appLE ⊤ ⊤ eSpecK).hom)
      (CommRingCat.ofHom (P.specialMap.appLE U V le_rfl).hom)
      (CommRingCat.ofHom (X.hom.appLE ⊤ V eX).hom) :=
    (isPushout_appTop_of_isPullback hpull).of_iso
      (⊤ : (baseSpec P.base).Opens).topIso
      U.topIso (⊤ : (Spec (.of k)).Opens).topIso V.topIso
      (arrowResLEAppIso P.toBase ⊤ U eBase).hom.w.symm
      (arrowResLEAppIso (residueSpecMap P.base) ⊤ ⊤ eSpecK).hom.w.symm
      (arrowResLEAppIso P.specialMap U V le_rfl).hom.w.symm
      (arrowResLEAppIso X.hom ⊤ V eX).hom.w.symm
  have hs : Function.Surjective (P.specialMap.appLE U V le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact Scheme.Hom.app_surjective P.specialMap U hU
  exact isPushout_localization_prime
    (P.toBase.appLE ⊤ U eBase).hom
    ((residueSpecMap P.base).appLE ⊤ ⊤ eSpecK).hom
    (P.specialMap.appLE U V le_rfl).hom
    (X.hom.appLE ⊤ V eX).hom hglob p q hs (congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (f := P.specialMap) U hU V hV le_rfl hxV)).symm

/-- **The special fibre on stalks.** For a deformation `P` of `X` and a point `x` of `X` lying
in the preimage of an affine open `U` of `P.scheme` with affine preimage, the square of local
rings at `x` and its image is a pushout: the local ring of `X` at `x` is the reduction of the
local ring of `P.scheme` at the image of `x` along the residue map of the base. -/
theorem special_stalk_pushout
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (U : P.scheme.Opens) (hU : IsAffineOpen U)
    (hy : P.specialMap x ∈ U)
    (hV : IsAffineOpen (P.specialMap ⁻¹ᵁ U)) :
    letI : Algebra k (X.left.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
        StructureSheaf.stalkAlgebra k (X.hom.base x)
      ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
    let y := P.specialMap x
    letI : Algebra P.base (P.scheme.presheaf.stalk y) :=
      letI : Algebra P.base
          ((Spec (.of P.base)).presheaf.stalk (P.toBase.base y)) :=
        StructureSheaf.stalkAlgebra P.base (P.toBase.base y)
      ((P.toBase.stalkMap y).hom.comp (algebraMap P.base _)).toAlgebra
    IsPushout
      (CommRingCat.ofHom (algebraMap P.base (P.scheme.presheaf.stalk y)))
      (CommRingCat.ofHom (Deformation.Artin.residueMap P.base))
      (CommRingCat.ofHom (P.specialMap.stalkMap x).hom)
      (CommRingCat.ofHom (algebraMap k (X.left.presheaf.stalk x))) := by
  classical
  let : Algebra k (X.left.presheaf.stalk x) :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
      StructureSheaf.stalkAlgebra k (X.hom.base x)
    ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
  let y := P.specialMap x
  let : Algebra P.base ((Spec (.of P.base)).presheaf.stalk (P.toBase.base y)) :=
    StructureSheaf.stalkAlgebra P.base (P.toBase.base y)
  let : Algebra ((Spec (.of P.base)).presheaf.stalk (P.toBase.base y))
      (P.scheme.presheaf.stalk y) := (P.toBase.stalkMap y).hom.toAlgebra
  let : Algebra P.base (P.scheme.presheaf.stalk y) :=
    ((P.toBase.stalkMap y).hom.comp
      (algebraMap P.base ((Spec (.of P.base)).presheaf.stalk (P.toBase.base y)))).toAlgebra
  let V : X.left.Opens := P.specialMap ⁻¹ᵁ U
  have hxV : x ∈ V := hy
  let p : PrimeSpectrum Γ(P.scheme, U) := hU.primeIdealOf ⟨y, hy⟩
  let q : PrimeSpectrum Γ(X.left, V) := hV.primeIdealOf ⟨x, hxV⟩
  have hbaseAffine : IsAffineOpen (⊤ : (Spec (.of P.base)).Opens) := isAffineOpen_top _
  have hfieldAffine : IsAffineOpen (⊤ : (Spec (.of k)).Opens) := isAffineOpen_top _
  let z : PrimeSpectrum (CommRingCat.of P.base) := P.toBase.base y
  let z₀ : PrimeSpectrum (CommRingCat.of k) := X.hom.base x
  have hz : residueSpecMap P.base z₀ = z := by
    have hw := congrArg (fun f : X.left ⟶ Spec (.of P.base) => f x)
      P.specialCartesian.w
    simpa [z, z₀, Scheme.Hom.comp_apply] using hw.symm
  let rz : (⊤ : (Spec (.of P.base)).Opens) := ⟨z, trivial⟩
  let sz : (⊤ : (Spec (.of k)).Opens) := ⟨z₀, trivial⟩
  let r : PrimeSpectrum Γ(Spec (.of P.base), ⊤) := hbaseAffine.primeIdealOf rz
  let s : PrimeSpectrum Γ(Spec (.of k), ⊤) := hfieldAffine.primeIdealOf sz
  let : z.asIdeal.IsPrime := z.isPrime
  have hzmax : z.asIdeal = IsLocalRing.maximalIdeal P.base :=
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime z.asIdeal)
  have hz0 : z₀ = (⟨⊥, inferInstance⟩ : PrimeSpectrum k) := Subsingleton.elim _ _
  let eA : P.base ≃+* (Spec (.of P.base)).presheaf.stalk z :=
    localStalkRingEquiv z hzmax
  have hz0max : z₀.asIdeal = IsLocalRing.maximalIdeal k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact congrArg PrimeSpectrum.asIdeal hz0
  let ek : k ≃+* (Spec (.of k)).presheaf.stalk z₀ := localStalkRingEquiv z₀ hz0max
  have hsec := special_sections_localized_pushout X x P U hU hy hV
  let iBase := IsAffineOpen.arrowStalkMapIso P.toBase ⊤ hbaseAffine U hU (by simp) hy
  let iSpecial := IsAffineOpen.arrowStalkMapIso P.specialMap U hU V hV le_rfl hxV
  let iX := IsAffineOpen.arrowStalkMapIso X.hom ⊤ hfieldAffine V hV (by simp) hxV
  let eP : CommRingCat.of (Localization.AtPrime p.asIdeal) ≅
      CommRingCat.of (P.scheme.presheaf.stalk y) := (asIso iBase.hom.right).symm
  let eX : CommRingCat.of (Localization.AtPrime q.asIdeal) ≅
      CommRingCat.of (X.left.presheaf.stalk x) := (asIso iX.hom.right).symm
  let eBaseStalk : CommRingCat.of Γ(Spec (.of P.base), ⊤) ≅
      CommRingCat.of ((Spec (.of P.base)).presheaf.stalk z) :=
    (Scheme.ΓSpecIso (CommRingCat.of P.base)) ≪≫ eA.toCommRingCatIso
  let eFieldStalk : CommRingCat.of Γ(Spec (.of k), ⊤) ≅
      CommRingCat.of ((Spec (.of k)).presheaf.stalk z₀) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)) ≪≫ ek.toCommRingCatIso
  have hGammaGerm (a : Γ(Spec (.of P.base), ⊤)) :
      eBaseStalk.hom a = (Spec (.of P.base)).presheaf.germ ⊤ z trivial a :=
    localStalkRingEquiv_germ_top z hzmax a
  have hFieldGerm (a : Γ(Spec (.of k), ⊤)) :
      eFieldStalk.hom a = (Spec (.of k)).presheaf.germ ⊤ z₀ trivial a :=
    localStalkRingEquiv_germ_top z₀ hz0max a
  let residueStalkMap :
      (Spec (.of P.base)).presheaf.stalk z ⟶
        (Spec (.of k)).presheaf.stalk z₀ :=
    eqToHom (congrArg (fun (t : Spec (.of P.base)) =>
      (Spec (.of P.base)).presheaf.stalk t) hz.symm) ≫
      (residueSpecMap P.base).stalkMap z₀
  have hstalk : IsPushout (P.toBase.stalkMap y) residueStalkMap
      (P.specialMap.stalkMap x) (X.hom.stalkMap x) :=
    hsec.of_iso eBaseStalk eP eFieldStalk eX
    (ofHom_localization_comp_arrowStalkMapIso_inv P.toBase ⊤ hbaseAffine U hU (by simp) hy
      eBaseStalk hGammaGerm)
    (by
      apply CommRingCat.hom_ext
      ext a
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
      rw [hGammaGerm, hFieldGerm]
      dsimp only [residueStalkMap]
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
      have htransport :
          (eqToHom (congrArg (fun (t : Spec (.of P.base)) =>
            (Spec (.of P.base)).presheaf.stalk t) hz.symm)).hom
              ((Spec (.of P.base)).presheaf.germ ⊤ z trivial a) =
            (Spec (.of P.base)).presheaf.germ ⊤
              ((residueSpecMap P.base) z₀) trivial a :=
        germ_top_transport hz.symm a
      rw [htransport]
      exact
        (Scheme.Hom.germ_stalkMap_apply
          (f := residueSpecMap P.base) ⊤ z₀ trivial a).symm)
    (by
      apply (cancel_epi iBase.hom.right).1
      apply (cancel_mono iX.hom.right).1
      have hcanP : iBase.hom.right ≫ eP.hom = 𝟙 _ := by simp [eP]
      have hcanX : eX.hom ≫ iX.hom.right = 𝟙 _ := by simp [eX]
      simp only [← Category.assoc, hcanP, Category.id_comp]
      rw [Category.assoc, hcanX, Category.comp_id]
      exact iSpecial.hom.w)
    (ofHom_localization_comp_arrowStalkMapIso_inv X.hom ⊤ hfieldAffine V hV (by simp) hxV
      eFieldStalk hFieldGerm)
  have hResidue (a : P.base) :
      residueStalkMap (eA a) = ek (Deformation.Artin.residueMap P.base a) := by
    rw [localStalkRingEquiv_apply z hzmax,
      localStalkRingEquiv_apply z₀ hz0max]
    show (residueSpecMap P.base).stalkMap z₀
      ((eqToHom (congrArg (fun (t : Spec (.of P.base)) =>
        (Spec (.of P.base)).presheaf.stalk t) hz.symm)).hom
        ((StructureSheaf.toStalk P.base z).hom a)) = _
    rw [toStalk_transport hz.symm a]
    convert (AlgebraicGeometry.stalkMap_toStalk_apply
      (CommRingCat.ofHom (Deformation.Artin.residueMap P.base)) z₀ a) using 1
    rfl
  exact hstalk.of_iso (eA.toCommRingCatIso).symm (Iso.refl _) (ek.toCommRingCatIso).symm
    (Iso.refl _)
    (by
      apply CommRingCat.hom_ext
      ext b
      show (P.toBase.stalkMap y).hom b =
        algebraMap P.base (P.scheme.presheaf.stalk y) (eA.symm b)
      calc
        (P.toBase.stalkMap y).hom b =
            (P.toBase.stalkMap y).hom (eA (eA.symm b)) := by rw [eA.apply_symm_apply]
        _ = _ := by
          rw [localStalkRingEquiv_apply z hzmax]
          rfl)
    (by
      apply CommRingCat.hom_ext
      ext b
      show ek.symm (residueStalkMap b) = Deformation.Artin.residueMap P.base (eA.symm b)
      calc
        ek.symm (residueStalkMap b) =
            ek.symm (residueStalkMap (eA (eA.symm b))) := by rw [eA.apply_symm_apply]
        _ = _ := by rw [hResidue, ek.symm_apply_apply])
    (by simp)
    (by
      apply CommRingCat.hom_ext
      ext b
      show (X.hom.stalkMap x).hom b =
        algebraMap k (X.left.presheaf.stalk x) (ek.symm b)
      calc
        (X.hom.stalkMap x).hom b =
            (X.hom.stalkMap x).hom (ek (ek.symm b)) := by rw [ek.apply_symm_apply]
        _ = _ := by
          rw [localStalkRingEquiv_apply z₀ hz0max]
          rfl)

/-- The stalk square of `special_stalk_pushout` at an arbitrary point of `X`: an affine open
containing the image point is supplied by the standard affine cover of the deformation, and its
preimage is affine because the special-fibre immersion is affine. -/
theorem special_stalk_pushout_any
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    letI : Algebra k (X.left.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
        StructureSheaf.stalkAlgebra k (X.hom.base x)
      ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
    let y := P.specialMap x
    letI : Algebra P.base (P.scheme.presheaf.stalk y) :=
      letI : Algebra P.base
          ((Spec (.of P.base)).presheaf.stalk (P.toBase.base y)) :=
        StructureSheaf.stalkAlgebra P.base (P.toBase.base y)
      ((P.toBase.stalkMap y).hom.comp (algebraMap P.base _)).toAlgebra
    IsPushout
      (CommRingCat.ofHom (algebraMap P.base (P.scheme.presheaf.stalk y)))
      (CommRingCat.ofHom (Deformation.Artin.residueMap P.base))
      (CommRingCat.ofHom (P.specialMap.stalkMap x).hom)
      (CommRingCat.ofHom (algebraMap k (X.left.presheaf.stalk x))) := by
  let U := (P.scheme.affineCover.f (P.scheme.affineCover.idx (P.specialMap x))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hy : P.specialMap x ∈ U := P.scheme.affineCover.covers (P.specialMap x)
  have : IsClosedImmersion P.specialMap := deformationSpecialMap_isClosedImmersion P
  exact special_stalk_pushout X x P U hU hy (hU.preimage P.specialMap)

end Deformation.Examples

end
