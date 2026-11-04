module

public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.Deformation.Artin.Versality.AgreementLocusSmooth
public import StacksFrontier.Deformation.Artin.Versality.NonversalThickening

/-!
# Versality and generalization for categories fibred in setoids

Let `𝒳` be a category fibred in setoids over the big fppf site of a locally Noetherian scheme
`S`, satisfying (RS*), whose agreement loci are schemes locally of finite type, and in which an
object over a first-order thickening of an affine scheme of finite type descends to a first-order
thickening of finite type. If an object `x` over an affine scheme `U` of finite type over `S` is
versal at a point `u₀`, then `x` is versal at every finite type point `u` of `U` specializing to
`u₀`.

This is Stacks 0G2K for categories fibred in setoids, with the proof of the source. If `x` is not
versal at `u`, Stacks 0G2J produces `x ⟶ y` over a first-order thickening `U ⟶ T` admitting no
retraction over any open neighbourhood of `u`. The object `y` descends to `x'` over a first-order
thickening `U ⟶ U'` of finite type, and the locus `Z ⊆ U ×_S U'` where the pullbacks of `x` and
`x'` agree is smooth over `U'` at the image of `u₀` by Stacks 0CXM; a section of `Z ⟶ U'` over an
open neighbourhood of that image restricts to a retraction of `x ⟶ y` over a neighbourhood of
`u`, since `u` specializes to `u₀`.

## Main definitions

* `Deformation.Artin.IsAgreementLocus`: a scheme with morphisms to the schemes under two objects
  representing the locus where their pullbacks agree.
* `Deformation.Artin.HasAgreementLoci`: any two objects over schemes locally of finite type have
  an agreement locus locally of finite type over the second scheme.
* `Deformation.Artin.HasThickeningDescent`: an object over a first-order thickening of an affine
  scheme of finite type is the pullback of one over a first-order thickening of finite type.

## Main results

* `Deformation.Artin.exists_open_localRetraction_comp`: a versal object retracts, over a
  neighbourhood, every arrow through which a first-order thickening of finite type factors.
* `Deformation.Artin.isVersalAt_of_specializes_of_faithful`: Stacks 0G2K for categories
  fibred in setoids.

## Implementation notes

For a category fibred in setoids the 2-fibre product `(Sch/U) ×_𝒳 (Sch/U')` of the source is a
subfunctor of `U ×_S U'`, so an agreement locus represents it whenever it is a scheme. The
source extends the section of `Z ⟶ U'` over all of `U'` by Stacks 04AM; only a neighbourhood of
the image of `u₀` is used here, which is all its contradiction needs.

Descent along the limit `T = lim U'` is the use the source makes of limit preservation; it is
recorded as `Deformation.Artin.HasThickeningDescent`, which is what the argument consumes.

## References

* [Stacks Project, Tag 0G2K](https://stacks.math.columbia.edu/tag/0G2K)
* [Stacks Project, Tag 0G2J](https://stacks.math.columbia.edu/tag/0G2J)
* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)

/-! ### Agreement loci and descent along thickenings -/

/-- A scheme `Z` with morphisms `π` and `π'` to the schemes under `x` and `ξ'`, agreeing over
`S`, *represents the locus where the pullbacks of `x` and `ξ'` agree*: morphisms to `Z` are
determined by their two projections; an object with arrows to `x` and to `ξ'` gives a morphism
to `Z`; and every morphism to `Z` from an object of the site comes from such an object over
it. -/
structure IsAgreementLocus (x ξ' : F) (Z : Scheme.{u})
    (π : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (π' : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ')) : Prop where
  /-- The two projections agree over `S`. -/
  comm : π ≫ B.inclusion.map (p.obj x).hom = π' ≫ B.inclusion.map (p.obj ξ').hom
  /-- A morphism to `Z` is determined by its two projections. -/
  ext : ∀ {T : Scheme.{u}} (g g' : T ⟶ Z), g ≫ π = g' ≫ π → g ≫ π' = g' ≫ π' → g = g'
  /-- An object with arrows to `x` and `ξ'` gives a morphism to `Z`. -/
  exists_hom : ∀ (z : F) (d : z ⟶ x) (d' : z ⟶ ξ'),
    ∃ g : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj z) ⟶ Z,
      g ≫ π = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d) ∧
      g ≫ π' = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d')
  /-- Every morphism to `Z` from an object of the site comes from an object over it. -/
  cover : ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
    (g : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T ⟶ Z),
    g ≫ π ≫ B.inclusion.map (p.obj x).hom = B.inclusion.map T.hom →
    ∃ (z : F) (d : z ⟶ x) (d' : z ⟶ ξ') (hz : p.obj z = T),
      eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj hz).symm ≫
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d) = g ≫ π ∧
      eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj hz).symm ≫
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map d') = g ≫ π'

/-- Any two objects over schemes locally of finite type over `S` have an agreement locus, and
it is locally of finite type over the scheme under the second object. -/
abbrev HasAgreementLoci : Prop :=
  ∀ x ξ' : F, LocallyOfFiniteType (B.inclusion.map (p.obj x).hom) →
    LocallyOfFiniteType (B.inclusion.map (p.obj ξ').hom) →
    ∃ (Z : Scheme.{u}) (π : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
      (π' : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ')),
      IsAgreementLocus B S hS p x ξ' Z π π' ∧ LocallyOfFiniteType π'

/-- *Descent along first-order thickenings.* Let `ξ` lie over a first-order thickening
`i : U ⟶ T` of an affine scheme `U` locally of finite type over `S` whose image lies in an
affine open of `S`. Then there is an arrow `ξ ⟶ ξ'` to an object over an affine scheme locally
of finite type over `S`, such that the composite `U ⟶ T ⟶ U'` is again a first-order
thickening. For a limit preserving category this is the descent of `ξ` to a finite type
`Λ`-subalgebra of `Γ(T)` surjecting onto `Γ(U)`. -/
abbrev HasThickeningDescent : Prop :=
  ∀ (ξ : F) (U : AlgebraicGeometry.BigFppfOver B S hS) (i : U ⟶ p.obj ξ),
    IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) →
    LocallyOfFiniteType (B.inclusion.map U.hom) →
    Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) →
    (∃ W : S.Opens, IsAffineOpen W ∧ Set.range (B.inclusion.map U.hom).base ⊆ (W : Set S)) →
    ∃ (ξ' : F) (e : ξ ⟶ ξ'),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ')) ∧
      LocallyOfFiniteType (B.inclusion.map (p.obj ξ').hom) ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i ≫
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map e))

/-! ### Retractions over a neighbourhood -/

/-- A morphism of the site, viewed as a morphism of schemes, commutes with the maps to `S`. -/
private theorem map_comp_inclusion_hom
    {X Y : AlgebraicGeometry.BigFppfOver B S hS} (f : X ⟶ Y) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map Y.hom =
      B.inclusion.map X.hom :=
  (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w f))

/-- The scheme map under an arrow lying over `f` is `f` up to the `eqToHom` of the domains. -/
private theorem map_comp_eqToHom_eq_of_isHomLift {z y : F}
    {R R' : AlgebraicGeometry.BigFppfOver B S hS} (f : R ⟶ R') (φ : z ⟶ y) [p.IsHomLift f φ]
    (h : p.obj y = R') :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map φ ≫ eqToHom h) =
      eqToHom (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
        (IsHomLift.domain_eq p f φ)) ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f := by
  rw [IsHomLift.fac' p f φ]
  simp

/-- **A versal object retracts an arrow through which a first-order thickening factors.** Let
`𝒳` be fibred in setoids, let `r : x ⟶ y` and `e : y ⟶ ξ'` be such that `r ≫ e` lies over a
first-order thickening, and let `Z` represent the agreement locus of `x` and `ξ'`, locally of
finite type over the locally Noetherian scheme under `ξ'`. If `x` is versal at `u₀`, there is an
open neighbourhood `O'` of the image of `u₀` such that every arrow `s : z ⟶ y` whose composite
with `e` lies over a morphism with image in `O'` admits `β : z ⟶ x` retracting `r` along `s`:
`b ≫ β = a` whenever `a ≫ r = b ≫ s`. -/
theorem exists_open_localRetraction_comp (hp : p.IsFiberedInGroupoids) [p.Faithful]
    (x y ξ' : F) (Z : Scheme.{u})
    (π : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (π' : Z ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ'))
    (hZ : IsAgreementLocus B S hS p x ξ' Z π π')
    [IsLocallyNoetherian ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ'))]
    [LocallyOfFiniteType π']
    (r : x ⟶ y) (e : y ⟶ ξ')
    (hr : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (r ≫ e))))
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion)
      u₀ x rfl) :
    ∃ O' : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj ξ')).Opens,
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (r ≫ e))).base u₀ ∈ O' ∧
      ∀ (z : F) (s : z ⟶ y),
        Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
          (p.map (s ≫ e))).base ⊆ O' →
        ∃ β : z ⟶ x, ∀ (x' : F) (a : x' ⟶ x) (b : x' ⟶ z), a ≫ r = b ≫ s → b ≫ β = a := by
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨w, cw, hopen, w₀, hw₀, β, hret⟩ := exists_localRetraction_of_isVersalAt B S hS p hp
    x ξ' Z π π' hZ.comm hZ.ext hZ.exists_hom hZ.cover (r ≫ e) hr u₀ hvers
  refine ⟨(V.map (p.map cw)).opensRange, ⟨w₀, hw₀⟩, ?_⟩
  intro z s hrange
  -- the arrow `s ≫ e` lies over a morphism factoring through the open immersion under `cw`
  let m : V.obj (p.obj z) ⟶ V.obj (p.obj w) :=
    IsOpenImmersion.lift (V.map (p.map cw)) (V.map (p.map (s ≫ e))) fun _ ht => hrange ht
  have hm : m ≫ V.map (p.map cw) = V.map (p.map (s ≫ e)) := IsOpenImmersion.lift_fac _ _ _
  let mS : p.obj z ⟶ p.obj w := Over.homMk (ObjectProperty.homMk m) (by
    apply ObjectProperty.hom_ext
    show m ≫ B.inclusion.map (p.obj w).hom = B.inclusion.map (p.obj z).hom
    rw [← map_comp_inclusion_hom B S hS (p.map cw), ← Category.assoc, hm,
      map_comp_inclusion_hom B S hS (p.map (s ≫ e))])
  have hmS : mS ≫ p.map cw = p.map (s ≫ e) := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hm
  obtain ⟨zw, ⟨-, hzw⟩, -⟩ := hp.unique_lift cw (s ≫ e) mS hmS
  refine ⟨zw ≫ β, fun x' a b hab => ?_⟩
  simpa only [Category.assoc] using
    hret x' a (b ≫ zw) (by simp only [Category.assoc, hzw, reassoc_of% hab])

/-- Precomposing both legs of a pullback square with an `eqToHom` keeps it a pullback square. -/
theorem isPullback_eqToHom_comp {C : Type*} [Category C] {P P' X Y Z : C} (h : P' = P)
    {f : P ⟶ X} {g : P ⟶ Y} {k : X ⟶ Z} {l : Y ⟶ Z} (H : IsPullback f g k l) :
    IsPullback (eqToHom h ≫ f) (eqToHom h ≫ g) k l := by
  subst h
  simpa using H

/-! ### Versality and generalization -/

/-- **Stacks 0G2K for categories fibred in setoids.** Let `𝒳` be fibred in setoids over the big
fppf site of a locally Noetherian scheme `S`, satisfying (RS*), with agreement loci locally of
finite type and descent along first-order thickenings. Let `x` lie over an affine scheme `U`
locally of finite type over `S` whose image lies in an affine open of `S`. If `x` is versal at
`u₀` and `u` is a finite type point of `U` specializing to `u₀`, then `x` is versal at `u`. -/
theorem isVersalAt_of_specializes_of_faithful (hp : p.IsFiberedInGroupoids) [p.Faithful]
    [IsLocallyNoetherian S] (hRS : SatisfiesRSStar B S hS p hp)
    (hZ : HasAgreementLoci B S hS p) (hD : HasThickeningDescent B S hS p) (x : F)
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))]
    [LocallyOfFiniteType (B.inclusion.map (p.obj x).hom)]
    (hW : ∃ W : S.Opens, IsAffineOpen W ∧
      Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (W : Set S))
    {u u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)}
    (hu : IsFiniteTypePoint u) (hspec : u ⤳ u₀)
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion)
      u₀ x rfl) :
    IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion) u x rfl := by
  classical
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have : LocallyOfFiniteType ((Over.post B.inclusion).obj (p.obj x)).hom :=
    inferInstanceAs (LocallyOfFiniteType (B.inclusion.map (p.obj x).hom))
  by_contra hnot
  obtain ⟨T, i, y, hy, r, hr, hthick, -, -, hno⟩ :=
    exists_firstOrderThickening_without_localRetraction B S hS p hp hRS (p.obj x) x rfl u hu
      hnot
  subst hy
  have hr' : p.map r = i := by simpa using hr
  -- descend `y` to a first-order thickening of finite type
  obtain ⟨ξ', e, -, hlft', hthick'⟩ := hD y (p.obj x) (p.map r) inferInstance inferInstance
    (by rwa [hr']) hW
  obtain ⟨Z, π, π', hlocus, hπ'⟩ := hZ x ξ' inferInstance hlft'
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := ‹IsLocallyNoetherian S›
  have : IsLocallyNoetherian (V.obj (p.obj ξ')) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map (p.obj ξ').hom)
  obtain ⟨O', hO'₀, hO'⟩ := exists_open_localRetraction_comp B S hS p hp x y ξ' Z π π' hlocus
    r e (by rwa [Functor.map_comp, Functor.map_comp]) u₀ hvers
  -- the open neighbourhood of `u` in `T` lying over `O'`
  let Wsch : (V.obj (p.obj y)).Opens := (V.map (p.map e)) ⁻¹ᵁ O'
  have hWc : B.Contains Wsch :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion Wsch.ι) (p.obj y).left.2
  let W := AlgebraicGeometry.BigFppfOver.siteObjectOver B S hS (p.obj y) hWc Wsch.ι
  let j : W ⟶ p.obj y := AlgebraicGeometry.BigFppfOver.siteMapOver B S hS (p.obj y) hWc Wsch.ι
  have hu_mem : (V.map i).base u ∈ Wsch := by
    have h1 := (hspec.map (V.map (p.map (r ≫ e))).continuous).mem_open O'.isOpen hO'₀
    show (V.map (p.map e)).base ((V.map i).base u) ∈ O'
    rwa [Functor.map_comp, Functor.map_comp, hr', Scheme.Hom.comp_apply] at h1
  obtain ⟨z, s, hs⟩ := hp.exists_lift j y rfl
  have hz : p.obj z = W := IsHomLift.domain_eq p j s
  have hsV : V.map (p.map s) = eqToHom (congrArg V.obj hz) ≫ V.map j := by
    simpa only [eqToHom_refl, Category.comp_id] using
      map_comp_eqToHom_eq_of_isHomLift B S hS p j s rfl
  have hrange : Set.range (V.map (p.map (s ≫ e))).base ⊆ O' := by
    rintro _ ⟨t, rfl⟩
    rw [Functor.map_comp, Functor.map_comp, hsV, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (show ((Wsch : Scheme.{u}) : Type u) from
      (eqToHom (congrArg V.obj hz)).base t).2
  obtain ⟨β, hβ⟩ := hO' z s hrange
  have hsc : p.IsCartesian (p.map s) s :=
    (hp.isStronglyCartesian s).isCartesian_of_isStronglyCartesian
  refine hno W j ⟨(V.map i).base u, hu_mem⟩ rfl (inferInstanceAs (IsOpenImmersion Wsch.ι)) z hz s
    (IsHomLift.fac' p j s) hsc ?_
  -- the pullback of the neighbourhood to `U`
  let Pop : (V.obj (p.obj x)).Opens := (V.map i) ⁻¹ᵁ Wsch
  have hPc : B.Contains Pop :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion Pop.ι) (p.obj x).left.2
  let P := AlgebraicGeometry.BigFppfOver.siteObjectOver B S hS (p.obj x) hPc Pop.ι
  let ta : P ⟶ p.obj x :=
    AlgebraicGeometry.BigFppfOver.siteMapOver B S hS (p.obj x) hPc Pop.ι
  let g : P ⟶ W := Over.homMk (ObjectProperty.homMk (V.map i ∣_ Wsch)) (by
    apply ObjectProperty.hom_ext
    show (V.map i ∣_ Wsch) ≫ Wsch.ι ≫ B.inclusion.map (p.obj y).hom =
      Pop.ι ≫ B.inclusion.map (p.obj x).hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc,
      map_comp_inclusion_hom B S hS i])
  have hsq : ta ≫ i = g ≫ j := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (morphismRestrict_ι (V.map i) Wsch).symm
  obtain ⟨x', a, ha⟩ := hp.exists_lift ta x rfl
  have hx' : p.obj x' = P := IsHomLift.domain_eq p ta a
  have : p.IsHomLift i r := by
    rw [← hr']
    infer_instance
  have : p.IsStronglyCartesian j s := hp.isStronglyCartesian_homLift j s
  let b : x' ⟶ z := Functor.IsStronglyCartesian.map p j s hsq (a ≫ r)
  have hb : b ≫ s = a ≫ r := Functor.IsStronglyCartesian.fac p j s hsq (a ≫ r)
  have hbl : p.IsHomLift g b := inferInstance
  refine ⟨β, x', a, b, (hp.isStronglyCartesian a).isCartesian_of_isStronglyCartesian,
    (hp.isStronglyCartesian b).isCartesian_of_isStronglyCartesian, ?_, hb.symm,
    hβ x' a b hb.symm⟩
  rw [map_comp_eqToHom_eq_of_isHomLift B S hS p ta a rfl,
    map_comp_eqToHom_eq_of_isHomLift B S hS p g b hz]
  exact isPullback_eqToHom_comp _ (isPullback_morphismRestrict (V.map i) Wsch).flip

end Deformation.Artin

end
