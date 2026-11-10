module

public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.Deformation.Artin.Versality
import all StacksFrontier.Deformation.ArtinCriteria.Versality

/-!
# Versality tested on small extensions of local rings

An object `x` of a category `q : 𝒳 ⥤ Over S` lying over `U` is versal at a point `u₀` of `U`
when every lifting problem along a surjection of Artinian local algebras over the local ring
`𝒪_{S,s}` at the image `s` of `u₀`, with residue field identified with `κ(u₀)`, has a solution
(`Deformation.Artin.IsVersalAt`). This file restates that condition without the bundled
category of Artinian local algebras: for a small extension `B' ⟶ B` of local rings and a
morphism `α : Spec B ⟶ U` sending the closed point to `u₀` and inducing an isomorphism of
residue fields, every arrow `y ⟶ x` over `α` from an object `y` over `Spec B` extends along any
arrow `y ⟶ z` over `Spec B' ⟶ Spec B`.

This is the form in which versality is used to check the infinitesimal lifting criterion for
smoothness of Stacks 02HX, condition (4), as in Stacks 0CXL and Stacks 0CXM.

## Main results

* `Deformation.Artin.IsVersalAt.exists_lift_of_isSmallExtension`: versality at `u₀` solves the
  lifting problems along small extensions of local rings whose thin end maps to `u₀` with
  trivial residue field extension.

## Implementation notes

The structure of algebra over `𝒪_{S,s}` on `B` and `B'` comes from the morphisms
`Spec B ⟶ S` and `Spec B' ⟶ S` through their stalk maps at the closed points, transported to
the stalk at `s` along the specialization given by the equality of points. The identification
of the residue field of `B` with `κ(u₀)` is the inverse of the map induced by `α` on residue
fields, and that of `B'` is obtained through the isomorphism of residue fields induced by the
surjection `B' ⟶ B`. The objects `y` and `z` are only required to lie over `Spec B` and
`Spec B'` with the given structure morphisms; that these structure morphisms are the ones
coming from the algebra structures is part of the proof.

## References

* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
* [Stacks Project, Tag 0CXL](https://stacks.math.columbia.edu/tag/0CXL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local implicit_reducible] AlgebraicGeometry.Spec
  AlgebraicGeometry.Spec.locallyRingedSpaceObj AlgebraicGeometry.Spec.sheafedSpaceObj
  AlgebraicGeometry.Spec.topObj

namespace Deformation.Artin

universe u v w

variable {S : Scheme.{u}} {X : Type v} [Category.{w} X] (q : X ⥤ Over S)

/-- **Versality on small extensions.** Let `x` be versal at `u₀`. Let `B' ⟶ B` be a small
extension of local rings, `α : Spec B ⟶ U` a morphism sending the closed point to `u₀` and
inducing an isomorphism of residue fields, and `β : Spec B' ⟶ S` with `α ≫ (U ⟶ S)` equal to
`Spec B ⟶ Spec B' ⟶ S`. Then for objects `y` over `Spec B` and `z` over `Spec B'`, an arrow
`i : y ⟶ z` over `Spec B ⟶ Spec B'` and an arrow `a : y ⟶ x` over `α`, there is `b : z ⟶ x`
with `i ≫ b = a`. -/
theorem IsVersalAt.exists_lift_of_isSmallExtension (U : Over S) (u₀ : U.left) (x : X)
    (hx : q.obj x = U) (hvers : IsVersalAt U q u₀ x hx)
    {B' B : CommRingCat.{u}} (Φ : B' ⟶ B) (hsmall : InfinitesimalLifting.IsSmallExtension Φ)
    (α : Spec B ⟶ U.left) (β : Spec B' ⟶ S) (hcommS : α ≫ U.hom = Spec.map Φ ≫ β)
    (hclosed : α.base (@IsLocalRing.closedPoint B _ hsmall.2.1) = u₀)
    (hresIso : IsIso (α.residueFieldMap (@IsLocalRing.closedPoint B _ hsmall.2.1)))
    (y z : X) (hy : q.obj y = Over.mk (α ≫ U.hom)) (hz : q.obj z = Over.mk β)
    (i : y ⟶ z)
    (hi : eqToHom (congrArg Over.left hy).symm ≫ (q.map i).left ≫
        eqToHom (congrArg Over.left hz) = Spec.map Φ)
    (a : y ⟶ x)
    (ha : eqToHom (congrArg Over.left hy).symm ≫ (q.map a).left ≫
        eqToHom (congrArg Over.left hx) = α) :
    ∃ b : z ⟶ x, i ≫ b = a := by
  rcases hsmall with ⟨hB', hB, hArtB', hArtB, hsurj, hlen⟩
  let : IsLocalRing B' := hB'
  let : IsLocalRing B := hB
  let : IsArtinianRing B := hArtB
  let : IsArtinianRing B' := hArtB'
  subst u₀
  let s := basePoint U (α.base (IsLocalRing.closedPoint B))
  let R := S.presheaf.stalk s
  let K := U.left.residueField (α.base (IsLocalRing.closedPoint B))
  let : Algebra R K := residueFieldAlgebra U (α.base (IsLocalRing.closedPoint B))
  have hΦloc : IsLocalHom Φ.hom := Function.Surjective.isLocalHom Φ.hom hsurj
  let cp : Spec (CommRingCat.of B) := IsLocalRing.closedPoint B
  let cp' : Spec (CommRingCat.of B') := IsLocalRing.closedPoint B'
  let θ : U.left ⟶ S := U.hom
  have hptS' : β.base cp' = θ.base (α.base cp) := by
    have h1 := congrArg (fun q => q.base cp) hcommS
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
    rw [AlgebraicGeometry.Spec_closedPoint (f := Φ)] at h1
    exact h1.symm
  have hs : basePoint U (α.base (IsLocalRing.closedPoint B)) =
      θ.base (α.base (IsLocalRing.closedPoint B)) := by
    dsimp [basePoint, residueFieldBasePoint, θ]
    simp [Scheme.fromSpecResidueField_apply]
  let σ : CommRingCat.of R ⟶
      CommRingCat.of (S.presheaf.stalk (θ.base (α.base cp))) :=
    S.presheaf.stalkSpecializes (Specializes.of_eq hs.symm)
  let bθ : CommRingCat.of (S.presheaf.stalk (θ.base (α.base cp))) ⟶
      CommRingCat.of B' :=
    S.presheaf.stalkSpecializes (Specializes.of_eq hptS') ≫
      Scheme.stalkClosedPointTo β
  let b := σ ≫ bθ
  let bThin := b ≫ Φ
  have hcompat := InfinitesimalLifting.stalkMap_stalkClosedPointTo_comm θ Φ α β
    hcommS hptS'
  let : Algebra R B' := b.hom.toAlgebra
  let : Algebra R B := bThin.hom.toAlgebra
  let a' : CommRingCat.of (U.left.presheaf.stalk (α.base cp)) ⟶ CommRingCat.of B :=
    Scheme.stalkClosedPointTo α
  let : IsLocalHom a'.hom := Scheme.isLocalHom_stalkClosedPointTo' α
  let a0 : CommRingCat.of R ⟶ CommRingCat.of (U.left.presheaf.stalk (α.base cp)) :=
    σ ≫ θ.stalkMap (α.base cp)
  let : Algebra R (U.left.presheaf.stalk (α.base cp)) := a0.hom.toAlgebra
  let : Algebra (U.left.presheaf.stalk (α.base cp)) K :=
    (IsLocalRing.residue (U.left.presheaf.stalk (α.base cp))).toAlgebra
  have hAK : algebraMap R K =
      (algebraMap (U.left.presheaf.stalk (α.base cp)) K).comp a0.hom := by
    let τ := U.left.fromSpecResidueField (α.base cp)
    have hτ : τ (IsLocalRing.closedPoint K) = α.base cp := by
      simp [τ]
    let hp : α.base cp ⤳ τ (IsLocalRing.closedPoint K) :=
      Specializes.of_eq hτ.symm
    have hσ : σ = S.presheaf.stalkSpecializes
        (Specializes.of_eq (congrArg θ hτ.symm)) := rfl
    have hres : U.left.presheaf.stalkSpecializes hp ≫ U.left.residue (α.base cp) =
        Scheme.stalkClosedPointTo τ := by
      rw [stalkClosedPointTo_fromSpecResidueField]
      simpa [hp] using (Scheme.residue_residueFieldCongr U.left hτ).symm
    change (Scheme.stalkClosedPointTo (τ ≫ θ)).hom =
      (algebraMap (U.left.presheaf.stalk (α.base cp)) K).comp a0.hom
    rw [Scheme.stalkClosedPointTo_comp]
    change (θ.stalkMap (τ (IsLocalRing.closedPoint K)) ≫
      Scheme.stalkClosedPointTo τ).hom =
      (U.left.residue (α.base cp)).hom.comp
        ((σ ≫ θ.stalkMap (α.base cp)).hom)
    have hassoc := Scheme.Hom.stalkSpecializes_stalkMap_assoc θ
      (α.base cp) (τ (IsLocalRing.closedPoint K)) hp (U.left.residue (α.base cp))
    have hcat : θ.stalkMap (τ (IsLocalRing.closedPoint K)) ≫
        Scheme.stalkClosedPointTo τ =
      σ ≫ θ.stalkMap (α.base cp) ≫ U.left.residue (α.base cp) := by
      rw [← hres, hσ]
      exact hassoc.symm
    have hcat' := congrArg CommRingCat.Hom.hom
      (hcat.trans (Category.assoc σ (θ.stalkMap (α.base cp)) (U.left.residue (α.base cp))).symm)
    simp only [CommRingCat.hom_comp] at hcat'
    exact hcat'
  let : IsScalarTower R (U.left.presheaf.stalk (α.base cp)) K :=
    IsScalarTower.of_algebraMap_eq' hAK
  have hacompat : a0 ≫ a' = bThin := by
    change (σ ≫ θ.stalkMap (α.base cp)) ≫ a' = (σ ≫ bθ) ≫ Φ
    rw [Category.assoc, hcompat]
    exact (Category.assoc _ _ _).symm
  let aAlg : (U.left.presheaf.stalk (α.base cp)) →ₐ[R] B :=
    { a'.hom with
      commutes' := fun r => by
        change a'.hom (a0.hom r) = bThin.hom r
        exact congrArg (fun z : _ ⟶ CommRingCat.of B => z.hom r) hacompat }
  let : IsLocalHom aAlg := ⟨fun x hx => (inferInstance : IsLocalHom a'.hom).map_nonunit x hx⟩
  let eInduced := IsLocalRing.ResidueField.mapAlgHom aAlg
  let eB_ring : K ≃+* IsLocalRing.ResidueField B := by
    apply RingEquiv.ofBijective eInduced.toRingHom
    let eSpec : (Spec B).residueField cp ≃+* IsLocalRing.ResidueField B :=
      IsLocalRing.ResidueField.mapEquiv
        (stalkClosedPointIso B).commRingCatIsoToRingEquiv
    have hmap : eInduced.toRingHom =
        eSpec.toRingHom.comp (α.residueFieldMap cp).hom := by
      ext z
      dsimp [eInduced, IsLocalRing.ResidueField.mapAlgHom,
        Scheme.Hom.residueFieldMap]
      change IsLocalRing.ResidueField.map
          ((stalkClosedPointIso B).hom.hom.comp (α.stalkMap cp).hom) z =
        eSpec (IsLocalRing.ResidueField.map (α.stalkMap cp).hom z)
      change IsLocalRing.ResidueField.map
          ((stalkClosedPointIso B).hom.hom.comp (α.stalkMap cp).hom) z =
        IsLocalRing.ResidueField.map (stalkClosedPointIso B).hom.hom
          (IsLocalRing.ResidueField.map (α.stalkMap cp).hom z)
      exact (IsLocalRing.ResidueField.map_map (α.stalkMap cp).hom
        (stalkClosedPointIso B).hom.hom z).symm
    rw [hmap]
    have hαbij : Function.Bijective (α.residueFieldMap cp).hom :=
      (ConcreteCategory.isIso_iff_bijective _).mp hresIso
    exact eSpec.bijective.comp hαbij
  let eB : K ≃ₐ[R] IsLocalRing.ResidueField B :=
    AlgEquiv.ofRingEquiv (f := eB_ring) (by
      intro r
      rw [hAK]
      change IsLocalRing.ResidueField.mapAlgHom aAlg
          (IsLocalRing.residue (U.left.presheaf.stalk (α.base cp)) (a0.hom r)) =
        IsLocalRing.residue B (bThin.hom r)
      rw [IsLocalRing.ResidueField.mapAlgHom_residue]
      exact congrArg _ (congrArg (fun z : _ ⟶ CommRingCat.of B => z.hom r) hacompat))
  let φAlg : B' →ₐ[R] B :=
    { Φ.hom with
      commutes' := fun r => by
        change Φ.hom (b.hom r) = bThin.hom r
        simp [bThin, CommRingCat.hom_comp, RingHom.coe_comp] }
  let : IsLocalHom φAlg :=
    ⟨fun x hx => hΦloc.map_nonunit x hx⟩
  let eφMap := IsLocalRing.ResidueField.mapAlgHom φAlg
  have hφsurj : Function.Surjective eφMap.toRingHom := by
    intro y
    obtain ⟨b₀, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨b₁, rfl⟩ := hsurj b₀
    exact ⟨IsLocalRing.residue B' b₁, by
      simp [eφMap, IsLocalRing.ResidueField.mapAlgHom, φAlg]⟩
  let eφ : IsLocalRing.ResidueField B' ≃ₐ[R] IsLocalRing.ResidueField B :=
    AlgEquiv.ofBijective eφMap ⟨eφMap.toRingHom.injective, hφsurj⟩
  let eBThick := eB.trans eφ.symm
  let Aobj : ArtinianLocalAlgCat.{u, u, u} R K :=
    { carrier := B
      residueEquiv := eB.symm }
  let Bobj : ArtinianLocalAlgCat.{u, u, u} R K :=
    { carrier := B'
      residueEquiv := eBThick.symm }
  let φobj : Bobj ⟶ Aobj :=
    { hom := φAlg
      isLocal := hΦloc
      residue_comm := by
        intro z
        apply eB.injective
        dsimp [Aobj, Bobj]
        rfl }
  have hβbase : β = Spec.map (CommRingCat.ofHom (algebraMap R B')) ≫ S.fromSpecStalk s := by
    symm
    change Spec.map b ≫ S.fromSpecStalk s = β
    exact (specializes_comp_fromSpecStalk (Specializes.of_eq hs.symm) bθ).trans
      ((specializes_comp_fromSpecStalk (Specializes.of_eq hptS')
          (Scheme.stalkClosedPointTo β)).trans
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk β))
  have hαbase : α ≫ U.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ S.fromSpecStalk s := by
    rw [hcommS, hβbase, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hy' : q.obj y = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap R Aobj)) ≫ S.fromSpecStalk s) :=
    hy.trans (congrArg Over.mk hαbase)
  have hz' : q.obj z = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap R Bobj)) ≫ S.fromSpecStalk s) :=
    hz.trans (congrArg Over.mk hβbase)
  have hi' : eqToHom (congrArg Over.left hy').symm ≫ (q.map i).left ≫
      eqToHom (congrArg Over.left hz') = Spec.map (CommRingCat.ofHom φobj.hom.toRingHom) :=
    hi
  have ha' : Spec.map (CommRingCat.ofHom (residueMap Aobj)) ≫
      eqToHom (congrArg Over.left hy').symm ≫ (q.map a).left ≫
      eqToHom (congrArg Over.left hx) = U.left.fromSpecResidueField (α.base cp) := by
    have ha'' : eqToHom (congrArg Over.left hy').symm ≫ (q.map a).left ≫
        eqToHom (congrArg Over.left hx) = α := ha
    rw [ha'']
    let ρ : CommRingCat.of B ⟶ CommRingCat.of K :=
      CommRingCat.ofHom (residueMap Aobj)
    have hresA : Function.Surjective (residueMap Aobj) := by
      dsimp [residueMap]
      exact Aobj.residueEquiv.toRingEquiv.surjective.comp
        (IsLocalRing.residue_surjective (R := B))
    let : IsLocalHom ρ.hom := Function.Surjective.isLocalHom _ hresA
    have hρa : Scheme.stalkClosedPointTo α ≫ ρ = U.left.residue (α.base cp) := by
      apply CommRingCat.hom_ext
      ext r
      change eB.symm (IsLocalRing.residue B (aAlg r)) = _
      rw [← IsLocalRing.ResidueField.mapAlgHom_residue aAlg r]
      change eB.symm (eB (U.left.residue (α.base cp) r)) = _
      exact eB.symm_apply_apply _
    let pB := (Spec.map ρ).base (IsLocalRing.closedPoint K)
    have hpB : pB = cp := AlgebraicGeometry.Spec_closedPoint (f := ρ)
    let xρ := (Spec.map ρ ≫ α).base (IsLocalRing.closedPoint K)
    have hpoint : (Spec.map ρ ≫ α).base (IsLocalRing.closedPoint K) = α.base cp := by
      change α.base pB = α.base cp
      rw [hpB]
    let hpInsep : Inseparable xρ (α.base cp) := Inseparable.of_eq hpoint
    have hlocal : (U.left.presheaf.stalkCongr hpInsep).hom ≫
        (Scheme.stalkClosedPointTo α ≫ ρ) =
        Scheme.stalkClosedPointTo (Spec.map ρ ≫ α) := by
      rw [Scheme.stalkClosedPointTo_comp, InfinitesimalLifting.stalkClosedPointTo_specMap ρ]
      rw [TopCat.Presheaf.stalkCongr_hom]
      have hnat := Scheme.Hom.stalkSpecializes_stalkMap α cp pB
        (Specializes.of_eq hpB.symm)
      have hnat' := congrArg
        (fun m => m ≫ (stalkClosedPointIso B).hom ≫ ρ) hnat
      convert hnat' using 1
      rfl
    have hresf : Scheme.stalkClosedPointTo (Spec.map ρ ≫ α) =
        U.left.residue xρ ≫ (U.left.residueFieldCongr hpoint).hom := by
      rw [← hlocal, hρa, Scheme.residue_residueFieldCongr]
    let : IsLocalHom (Scheme.stalkClosedPointTo (Spec.map ρ ≫ α)).hom :=
      Scheme.isLocalHom_stalkClosedPointTo' (Spec.map ρ ≫ α)
    have hdesc : U.left.descResidueField
        (Scheme.stalkClosedPointTo (Spec.map ρ ≫ α)) =
          (U.left.residueFieldCongr hpoint).hom := by
      apply (cancel_epi (U.left.residue xρ)).mp
      rw [Scheme.residue_descResidueField, hresf]
    let τ : Spec (CommRingCat.of K) ⟶ U.left := U.left.fromSpecResidueField (α.base cp)
    let : IsLocalHom (Scheme.stalkClosedPointTo τ).hom :=
      Scheme.isLocalHom_stalkClosedPointTo' τ
    let hpCanon := Scheme.fromSpecResidueField_apply (X := U.left) (α.base cp)
      (IsLocalRing.closedPoint K)
    let pCanon := τ (IsLocalRing.closedPoint K)
    have hdescCanonical : U.left.descResidueField
        (Scheme.stalkClosedPointTo τ) = (U.left.residueFieldCongr hpCanon).hom := by
      apply (cancel_epi (U.left.residue pCanon)).mp
      rw [Scheme.residue_descResidueField,
        stalkClosedPointTo_fromSpecResidueField]
    apply (Scheme.SpecToEquivOfField (↑K) U.left).injective
    rw [Scheme.SpecToEquivOfField_eq_iff]
    refine ⟨?_, ?_⟩
    · rw [Scheme.SpecToEquivOfField_apply_fst,
        Scheme.SpecToEquivOfField_apply_fst]
      exact hpoint.trans hpCanon.symm
    rw [Scheme.SpecToEquivOfField_apply_snd,
      Scheme.SpecToEquivOfField_apply_snd, hdesc, hdescCanonical]
    exact (Scheme.residueFieldCongr_trans_hom U.left _ hpCanon).symm
  exact hvers Aobj Bobj φobj hsurj y z hy' hz' i hi' a ha'

/-- For an arrow of a category over `Over S` lying over a morphism `f` of `Over S`, the
underlying morphism of schemes of its image is that of `f`, up to the identifications of the
source and target. -/
theorem left_map_of_isHomLift {R R' : Over S} (f : R ⟶ R') {a b : X} (φ : a ⟶ b)
    [q.IsHomLift f φ] (h₁ : R.left = (q.obj a).left) (h₂ : (q.obj b).left = R'.left) :
    eqToHom h₁ ≫ (q.map φ).left ≫ eqToHom h₂ = f.left := by
  rw [IsHomLift.fac' q f φ]
  simp [Over.eqToHom_left]

/-- **Versality on small extensions, for arrows lying over morphisms of `Over S`.** The form of
`Deformation.Artin.IsVersalAt.exists_lift_of_isSmallExtension` in which `i` lies over
`Spec B ⟶ Spec B'` and `a` lies over `α`, as morphisms of schemes over `S`. -/
theorem IsVersalAt.exists_lift_of_isSmallExtension_of_isHomLift (U : Over S) (u₀ : U.left)
    (x : X) (hx : q.obj x = U) (hvers : IsVersalAt U q u₀ x hx)
    {B' B : CommRingCat.{u}} (Φ : B' ⟶ B) (hsmall : InfinitesimalLifting.IsSmallExtension Φ)
    (α : Spec B ⟶ U.left) (β : Spec B' ⟶ S) (hcommS : α ≫ U.hom = Spec.map Φ ≫ β)
    (hclosed : α.base (@IsLocalRing.closedPoint B _ hsmall.2.1) = u₀)
    (hresIso : IsIso (α.residueFieldMap (@IsLocalRing.closedPoint B _ hsmall.2.1)))
    (y z : X) (i : y ⟶ z) (a : y ⟶ x)
    (hi : q.IsHomLift (Over.homMk (U := Over.mk (α ≫ U.hom)) (V := Over.mk β) (Spec.map Φ)
      hcommS.symm) i)
    (ha : q.IsHomLift (Over.homMk (U := Over.mk (α ≫ U.hom)) (V := U) α rfl) a) :
    ∃ b : z ⟶ x, i ≫ b = a := by
  let f : Over.mk (α ≫ U.hom) ⟶ Over.mk β := Over.homMk (Spec.map Φ) hcommS.symm
  let g : Over.mk (α ≫ U.hom) ⟶ U := Over.homMk α rfl
  exact hvers.exists_lift_of_isSmallExtension q U u₀ x hx Φ hsmall α β hcommS hclosed hresIso
    y z (IsHomLift.domain_eq q f i) (IsHomLift.codomain_eq q f i) i
    (left_map_of_isHomLift q f i _ _) a (left_map_of_isHomLift q g a _ _)

end Deformation.Artin

end
