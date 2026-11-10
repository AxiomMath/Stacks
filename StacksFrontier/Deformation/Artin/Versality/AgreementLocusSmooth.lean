module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Smooth.LocalSectionThroughThickening
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.Deformation.Artin.Versality.SmallExtensionLift
import all StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting

/-!
# Smoothness of an agreement locus at a versal point

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `x` and
`ξ'` be objects of `𝒳` over schemes `U` and `U'`, and let `Z` be a scheme with morphisms
`Z ⟶ U` and `Z ⟶ U'` representing the locus where the pullbacks of `x` and `ξ'` agree: a pair
of morphisms `T ⟶ U`, `T ⟶ U'` factors, necessarily uniquely, through `Z` exactly when the two
pullbacks are joined by an object of `𝒳` over `T` mapping to both. When `𝒳` is fibred in setoids
this is the scheme representing the 2-fibre product `(Sch/U) ×_𝒳 (Sch/U')` of Stacks 0CXM.

If `i : U ⟶ Z` is a section of `Z ⟶ U` and `x` is versal at `u₀`, then `Z ⟶ U'` is smooth at
`i u₀`. This is the case of Stacks 0CXM in which the 2-fibre product is a scheme and the point
`z₀ = i u₀` has residue field `κ(u₀)`; the proof is the source's, without the étale chart and
the change of residue field: a lifting problem for `Z ⟶ U'` along a small extension with
trivial residue field extension is, through the universal property of `Z`, a lifting problem
for `x`, which versality solves, and the infinitesimal lifting criterion of Stacks 02HX converts
the solutions into smoothness.

## Main results

* `Deformation.Artin.smoothAt_of_isVersalAt_of_agreementLocus`: smoothness of `Z ⟶ U'` at
  `i u₀`.

## Implementation notes

The universal property of `Z` is recorded by three hypotheses: two morphisms to `Z` agreeing
after both projections are equal; an object of `𝒳` with arrows to `x` and to `ξ'` gives a
morphism to `Z`; and every morphism to `Z` from a scheme of the site comes from such an object,
which may be chosen over the given scheme. Only schemes of the site are tested, so `Z` itself
need not belong to the site.

The spectra of the Artinian local rings of the lifting criterion lie in the site because their
residue fields are residue fields of `U`, which lies in the site, and an Artinian local ring is
bounded in cardinality by its residue field.

## References

* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [local implicit_reducible] AlgebraicGeometry.Spec
  AlgebraicGeometry.Spec.locallyRingedSpaceObj AlgebraicGeometry.Spec.sheafedSpaceObj
  AlgebraicGeometry.Spec.topObj

namespace Deformation.Artin

universe u v w

/-! ### Spectra of Artinian local rings in the site -/

/-- The residue field of `R` is that of `X` at the image of the closed point, if `α : Spec R ⟶ X`
is an isomorphism on residue fields there. -/
private noncomputable def residueFieldEquivOfIsIso {X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (α : Spec R ⟶ X) (hα : IsIso (α.residueFieldMap (IsLocalRing.closedPoint R))) :
    IsLocalRing.ResidueField R ≃+* X.residueField (α.base (IsLocalRing.closedPoint R)) :=
  (IsLocalRing.ResidueField.mapEquiv (stalkClosedPointIso R).commRingCatIsoToRingEquiv).symm.trans
    (asIso (α.residueFieldMap (IsLocalRing.closedPoint R))).commRingCatIsoToRingEquiv.symm

/-- A morphism `α : Spec B ⟶ X` from the spectrum of an Artinian local ring inducing an
isomorphism of residue fields at the closed point has `Spec B` in every big fppf site that
contains `X`. -/
theorem contains_spec_of_isIso_residueFieldMap (B : AlgebraicGeometry.BigFppfSite.{u})
    {X : Scheme.{u}} (hX : B.Contains X) {R : CommRingCat.{u}} [IsLocalRing R] [IsArtinianRing R]
    (α : Spec R ⟶ X) (hα : IsIso (α.residueFieldMap (IsLocalRing.closedPoint R))) :
    B.Contains (Spec R) := by
  exact AlgebraicGeometry.Space.contains_spec_of_isArtinianRing_of_residueFieldEquiv (R := R) B
    (AlgebraicGeometry.BigFppfSite.residueField_spec_contains B hX _)
    (residueFieldEquivOfIsIso α hα)

/-! ### Residue fields along a section -/

/-- For a section `i` of `π`, the map `π` induces on residue fields at `i x` is an isomorphism. -/
theorem isIso_residueFieldMap_of_section {X Y : Scheme.{u}} (i : X ⟶ Y) (π : Y ⟶ X)
    (h : i ≫ π = 𝟙 X) (x : X) : IsIso (π.residueFieldMap (i.base x)) := by
  have hcomp : IsIso ((i ≫ π).residueFieldMap x) := by
    have key : ∀ g : X ⟶ X, g = 𝟙 X → IsIso (g.residueFieldMap x) := by
      rintro g rfl
      rw [Scheme.residueFieldMap_id]
      exact IsIso.id _
    exact key _ h
  have hbij := (ConcreteCategory.isIso_iff_bijective _).mp hcomp
  rw [Scheme.residueFieldMap_comp] at hbij
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨RingHom.injective _, fun v => ?_⟩
  obtain ⟨w, hw⟩ := hbij.2 ((i.residueFieldMap x).hom v)
  exact ⟨w, RingHom.injective (i.residueFieldMap x).hom hw⟩


/-! ### Smoothness at a versal point -/

section Smooth

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)

/-- **Smoothness of an agreement locus at a versal point.** Let `x` and `ξ'` be objects of a
category fibred in groupoids over the big fppf site of `S`, over `U` and `U'`, and let `Z` with
`π : Z ⟶ U` and `π' : Z ⟶ U'` (agreeing over `S`) represent the locus where the pullbacks of
`x` and `ξ'` agree: morphisms to `Z` are determined by their two projections (`huniq`); an
object of `𝒳` mapping to `x` and to `ξ'` gives a morphism to `Z` (`hexists`); and every morphism
to `Z` from an object of the site comes from such an object over it (`hcover`). If `i` is a
section of `π`, `π'` is locally of finite type with locally Noetherian target, and `x` is versal
at `u₀`, then `π'` is smooth at `i u₀`. -/
theorem smoothAt_of_isVersalAt_of_agreementLocus (hp : p.IsFiberedInGroupoids)
    (x ξ' : F) (Z : Scheme.{u})
    (π : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (π' : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ'))
    (hZS : π ≫ B.inclusion.map (p.obj x).hom = π' ≫ B.inclusion.map (p.obj ξ').hom)
    [IsLocallyNoetherian ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ'))]
    [LocallyOfFiniteType π']
    (huniq : ∀ {T : Scheme.{u}} (g g' : T ⟶ Z), g ≫ π = g' ≫ π → g ≫ π' = g' ≫ π' → g = g')
    (hexists : ∀ (z : F) (d : z ⟶ x) (d' : z ⟶ ξ'),
      ∃ g : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj z) ⟶ Z,
        g ≫ π = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d) ∧
        g ≫ π' = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d'))
    (hcover : ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
      (g : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T ⟶ Z),
      g ≫ π ≫ B.inclusion.map (p.obj x).hom = B.inclusion.map T.hom →
      ∃ (z : F) (d : z ⟶ x) (d' : z ⟶ ξ') (hz : p.obj z = T),
        eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj hz).symm ≫
            (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d) = g ≫ π ∧
        eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj hz).symm ≫
            (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d') = g ≫ π')
    (i : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x) ⟶ Z) (hi : i ≫ π = 𝟙 _)
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion)
      u₀ x rfl) :
    InfinitesimalLifting.SmoothAt π' (i.base u₀) := by
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let q := p ⋙ Over.post B.inclusion
  refine ((InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness π'
    (i.base u₀)).out 4 1).mp ?_
  intro B' B₀ Φ hsmall _ α β hcomm hclosed hres
  have hsmall' := hsmall
  rcases hsmall' with ⟨hB', hB, hArtB', hArtB, hsurj, hlen⟩
  let : IsLocalRing B' := hB'
  let : IsArtinianRing B₀ := hArtB
  let : IsArtinianRing B' := hArtB'
  let cp : Spec B₀ := IsLocalRing.closedPoint B₀
  let Ux := (p.obj x).hom
  let Uξ := (p.obj ξ').hom
  -- the residue field of `Spec B₀` is that of `u₀`
  have hπres : ∀ z (_ : z = i.base u₀), IsIso (π.residueFieldMap z) := by
    rintro _ rfl
    exact isIso_residueFieldMap_of_section i π hi u₀
  have hresU : IsIso ((α ≫ π).residueFieldMap cp) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (hπres _ hclosed) hres
  have hclosedU : (α ≫ π).base cp = u₀ := by
    change π.base (α.base cp) = u₀
    rw [hclosed, ← Scheme.Hom.comp_apply, hi]
    rfl
  have hcB : B.Contains (Spec B₀) := contains_spec_of_isIso_residueFieldMap B
    (p.obj x).left.2 (α ≫ π) hresU
  -- `Spec B'` has residue field that of `Spec B₀`, through the surjection
  have hcB' : B.Contains (Spec B') := by
    have e₁ := AlgebraicGeometry.Space.residueFieldEquivOfSurjective Φ hsurj
    exact AlgebraicGeometry.Space.contains_spec_of_isArtinianRing_of_residueFieldEquiv (R := B') B
      (AlgebraicGeometry.BigFppfSite.residueField_spec_contains B (p.obj x).left.2 _)
      (e₁.trans (residueFieldEquivOfIsIso (α ≫ π) hresU))
  -- the site objects over `Spec B₀` and `Spec B'`
  let TB : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (X := B.obj hcB) (Y := B.obj hS)
      ((α ≫ π) ≫ B.inclusion.map Ux))
  let TB' : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (X := B.obj hcB') (Y := B.obj hS)
      (β ≫ B.inclusion.map Uξ))
  have hcommS : (α ≫ π) ≫ B.inclusion.map Ux = Spec.map Φ ≫ β ≫ B.inclusion.map Uξ := by
    rw [Category.assoc, hZS, ← Category.assoc, hcomm, Category.assoc]
  -- an object over `Spec B₀` mapping to `x` and `ξ'` along `α`
  obtain ⟨y, d, d', hy, hd, hd'⟩ := hcover TB α (Category.assoc _ _ _).symm
  -- the pullback of `ξ'` to `Spec B'`
  let mβ : TB' ⟶ p.obj ξ' := Over.homMk (ObjectProperty.homMk β) (by
    apply ObjectProperty.hom_ext
    rfl)
  obtain ⟨z, cz, hcz⟩ := hp.exists_lift mβ ξ' rfl
  have hz : p.obj z = TB' := IsHomLift.domain_eq p mβ cz
  have hczV : V.map (p.map cz) = eqToHom (congrArg V.obj hz) ≫ β := by
    rw [IsHomLift.fac' p mβ cz, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
      eqToHom_refl, Category.comp_id]
    rfl
  let gΦ : TB ⟶ TB' := Over.homMk (ObjectProperty.homMk (Spec.map Φ)) (by
    apply ObjectProperty.hom_ext
    exact hcommS.symm)
  have hdV : V.map (p.map d) = eqToHom (congrArg V.obj hy) ≫ α ≫ π := (eqToHom_comp_iff _ _ _).mp hd
  have hd'V : V.map (p.map d') = eqToHom (congrArg V.obj hy) ≫ α ≫ π' :=
    (eqToHom_comp_iff _ _ _).mp hd'
  have hfac : (eqToHom hy ≫ gΦ ≫ eqToHom hz.symm) ≫ p.map cz = p.map d' := by
    apply V.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, hczV, hd'V, eqToHom_map,
      eqToHom_map]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    change eqToHom _ ≫ Spec.map Φ ≫ β = eqToHom _ ≫ α ≫ π'
    rw [hcomm]
  obtain ⟨iyz, ⟨hiyz, -⟩, -⟩ := hp.unique_lift cz d' _ hfac
  -- the two arrows as lifts of morphisms of schemes over `S`
  have hyq : q.obj y = Over.mk ((α ≫ π) ≫ ((Over.post B.inclusion).obj (p.obj x)).hom) := by
    change (Over.post B.inclusion).obj (p.obj y) = _
    rw [hy]
    rfl
  have hzq : q.obj z = Over.mk (β ≫ B.inclusion.map Uξ) := by
    change (Over.post B.inclusion).obj (p.obj z) = _
    rw [hz]
    rfl
  have hiLift : q.IsHomLift (Over.homMk
      (U := Over.mk ((α ≫ π) ≫ ((Over.post B.inclusion).obj (p.obj x)).hom))
      (V := Over.mk (β ≫ B.inclusion.map Uξ)) (Spec.map Φ) hcommS.symm) iyz := by
    refine IsHomLift.of_fac' q _ iyz hyq hzq ?_
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left]
    change V.map (p.map iyz) = _
    rw [hiyz, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    rfl
  have hdLift : q.IsHomLift (Over.homMk
      (U := Over.mk ((α ≫ π) ≫ ((Over.post B.inclusion).obj (p.obj x)).hom))
      (V := (Over.post B.inclusion).obj (p.obj x)) (α ≫ π) rfl) d := by
    refine IsHomLift.of_fac' q _ d hyq rfl ?_
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left, eqToHom_refl,
      Category.comp_id]
    change V.map (p.map d) = _
    rw [hdV]
    rfl
  obtain ⟨b, hb⟩ := IsVersalAt.exists_lift_of_isSmallExtension_of_isHomLift q
    ((Over.post B.inclusion).obj (p.obj x)) u₀ x rfl hvers
    Φ hsmall (α ≫ π) (β ≫ B.inclusion.map Uξ) hcommS hclosedU hresU y z iyz d hiLift hdLift
  -- the morphism `Spec B' ⟶ Z`
  obtain ⟨γ₀, hγ₁, hγ₂⟩ := hexists z b cz
  have hzV : V.obj (p.obj z) = Spec B' := congrArg V.obj hz
  let γ : Spec B' ⟶ Z := eqToHom hzV.symm ≫ γ₀
  have hγ : γ ≫ π' = β := by
    simp only [γ, Category.assoc]
    rw [hγ₂, hczV, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  refine ⟨γ, ?_, hγ⟩
  · apply huniq
    · have h1 : V.map (p.map iyz) ≫ V.map (p.map b) = V.map (p.map d) := by
        rw [← Functor.map_comp, ← Functor.map_comp, hb]
      have h2 : V.map (p.map iyz) = eqToHom (congrArg V.obj hy) ≫ Spec.map Φ ≫
          eqToHom (congrArg V.obj hz).symm := by
        rw [hiyz, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
        rfl
      rw [h2, hdV, ← hγ₁] at h1
      simp only [Category.assoc] at h1
      have h1' := congrArg (fun m => eqToHom (congrArg V.obj hy).symm ≫ m) h1
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at h1'
      simp only [γ, Category.assoc]
      exact h1'
    · rw [Category.assoc, hγ]
      exact hcomm.symm

end Smooth

/-! ### Local retractions through a first-order thickening -/

section Retraction

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)

/-- **A local retraction at a versal point.** Let `𝒳` be fibred in setoids over the big fppf site
of `S`, let `r : x ⟶ ξ'` lie over a first-order thickening `U ⟶ U'`, and let `Z ⟶ U`, `Z ⟶ U'`
represent the locus where the pullbacks of `x` and `ξ'` agree, with `Z ⟶ U'` locally of finite
type over a locally Noetherian `U'`. If `x` is versal at `u₀`, there are an open neighbourhood
`j : W ⟶ U'` of the image of `u₀`, an arrow `w ⟶ ξ'` over it, and `β : w ⟶ x` retracting `r`
over `W`: for every arrow `t' : z' ⟶ x` and `s' : z' ⟶ w` over a pullback of `j` along
`U ⟶ U'` with `t' ≫ r = s' ≫ (w ⟶ ξ')`, one has `s' ≫ β = t'`. The neighbourhood is the
image of `w ⟶ ξ'`, and the pullback squares are given through arrows of the site over which
`t'` and `s'` lie.

This is the step shared by the proofs of Stacks 0G2K and Stacks 0CXU, in the case where the
2-fibre product `(Sch/U) ×_𝒳 (Sch/U')` is a scheme; the source extends the section over all of
`U'` by Stacks 04AM after shrinking, and the contradiction it derives only uses a neighbourhood
of the image of `u₀`. -/
theorem exists_localRetraction_of_isVersalAt (hp : p.IsFiberedInGroupoids) [p.Faithful]
    (x ξ' : F) (Z : Scheme.{u})
    (π : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (π' : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ'))
    (hZS : π ≫ B.inclusion.map (p.obj x).hom = π' ≫ B.inclusion.map (p.obj ξ').hom)
    [IsLocallyNoetherian ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ'))]
    [LocallyOfFiniteType π']
    (huniq : ∀ {T : Scheme.{u}} (g g' : T ⟶ Z), g ≫ π = g' ≫ π → g ≫ π' = g' ≫ π' → g = g')
    (hexists : ∀ (z : F) (d : z ⟶ x) (d' : z ⟶ ξ'),
      ∃ g : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj z) ⟶ Z,
        g ≫ π = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d) ∧
        g ≫ π' = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d'))
    (hcover : ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
      (g : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T ⟶ Z),
      g ≫ π ≫ B.inclusion.map (p.obj x).hom = B.inclusion.map T.hom →
      ∃ (z : F) (d : z ⟶ x) (d' : z ⟶ ξ') (hz : p.obj z = T),
        eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj hz).symm ≫
            (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d) = g ≫ π ∧
        eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj hz).symm ≫
            (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d') = g ≫ π')
    (r : x ⟶ ξ')
    (hr : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r)))
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion)
      u₀ x rfl) :
    ∃ (w : F) (cw : w ⟶ ξ')
      (_ : IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map cw)))
      (w₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj w))
      (_ : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map cw)).base w₀ =
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map r)).base u₀)
      (β : w ⟶ x),
      ∀ (z' : F) (t' : z' ⟶ x) (s' : z' ⟶ w), t' ≫ r = s' ≫ cw → s' ≫ β = t' := by
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨i, hi, hi'⟩ := hexists x (𝟙 x) r
  have hiπ : i ≫ π = 𝟙 _ := by
    rw [hi, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have hsmooth := smoothAt_of_isVersalAt_of_agreementLocus B S hS p hp x ξ' Z π π' hZS
    huniq hexists hcover i hiπ u₀ hvers
  obtain ⟨W₀, j₀, hj₀, w₀, hw₀, s, hs, hcompat⟩ :=
    AlgebraicGeometry.exists_openImmersion_section_of_smoothAt π' hr i hi' u₀ hsmooth
  have hW : B.Contains W₀ :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion j₀) (p.obj ξ').left.2
  let W : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (X := B.obj hW) (Y := B.obj hS)
      (j₀ ≫ B.inclusion.map (p.obj ξ').hom))
  have hsW : s ≫ π ≫ B.inclusion.map (p.obj x).hom = B.inclusion.map W.hom := by
    change s ≫ π ≫ _ = j₀ ≫ _
    rw [hZS, ← Category.assoc, hs]
  obtain ⟨w, β, cw, hw, hβ, hcw⟩ := hcover W s hsW
  have hcwV : V.map (p.map cw) = eqToHom (congrArg V.obj hw) ≫ j₀ :=
    (eqToHom_comp_iff _ _ _).mp (hcw.trans hs)
  have hβV : V.map (p.map β) = eqToHom (congrArg V.obj hw) ≫ s ≫ π :=
    (eqToHom_comp_iff _ _ _).mp hβ
  have hopen : IsOpenImmersion (V.map (p.map cw)) := by
    rw [hcwV]
    infer_instance
  refine ⟨w, cw, hopen, (eqToHom (congrArg V.obj hw).symm).base w₀, ?_, β, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hcwV, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact hw₀
  intro z' t' s' hts
  apply Functor.map_injective p
  apply V.map_injective
  have hcomm : V.map (p.map t') ≫ V.map (p.map r) =
      (V.map (p.map s') ≫ eqToHom (congrArg V.obj hw)) ≫ j₀ := by
    rw [Category.assoc, ← hcwV, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, hts]
  rw [Functor.map_comp, Functor.map_comp, hβV]
  calc V.map (p.map s') ≫ eqToHom (congrArg V.obj hw) ≫ s ≫ π
      = (V.map (p.map t') ≫ i) ≫ π := by
        rw [hcompat _ _ _ hcomm, Category.assoc, Category.assoc]
    _ = V.map (p.map t') := by rw [Category.assoc, hiπ, Category.comp_id]

end Retraction


end Deformation.Artin

end
