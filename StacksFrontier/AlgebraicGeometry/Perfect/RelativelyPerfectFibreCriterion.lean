module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibresAffineConverse
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChangeTorAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOpenLocality
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseOpen
import StacksCore.Tactic.StacksAttribute

/-!
# Local boundedness below on schemes, and fibres along open immersions

This file collects the local statements that reduce Stacks 0GEH to the affine case: local
boundedness below on a scheme is checked on a covering by open immersions, and the fibre of the
restriction `U ⟶ V` of a morphism `f : X ⟶ S` to opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`, over
a point `s ∈ V`, is an open subscheme of the fibre of `f` over the image of `s`.

## Main results

* `AlgebraicGeometry.isLocallyBoundedBelow_iff_forall_openImmersion`: local boundedness below on
  a scheme is boundedness below of the derived pullbacks along the members of a covering by open
  immersions.
* `AlgebraicGeometry.isLocallyBoundedBelow_derivedPullback_of_isOpenImmersion`: local boundedness
  below is preserved by derived pullback along an open immersion, and
  `AlgebraicGeometry.isLocallyBoundedBelow_of_forall_openImmersion`: it glues along a covering by
  open immersions.
* `AlgebraicGeometry.isLocallyBoundedBelow_fibre_iff_of_arrowIso`: the fibre condition transports
  along an isomorphism of morphisms of schemes.
* `AlgebraicGeometry.isLocallyBoundedBelow_fibre_of_openImmersion` and
  `AlgebraicGeometry.exists_openImmersion_fibre`: the fibres of the restriction `U ⟶ V` are open
  subschemes of the fibres of `f`, and these opens cover them.
* `AlgebraicGeometry.exists_affineOpens_le`: every point of `X` lies in an affine open mapped
  into an affine open of `S`.

## Implementation notes

The fibre of `U ⟶ V` over `s ∈ V` is an open subscheme of the fibre of `f` over the image of `s`
in `S`, by the open immersion `pullback.map` attached to the open immersions `U ⟶ X`, `V ⟶ S`
and the isomorphism of residue fields. Stacks 0GEH itself,
`AlgebraicGeometry.isPerfectRelativeTo_iff_isLocallyBoundedBelow_and_fibres`, is in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres`.

## References

* [Stacks Project, Lemma 36.35.13 (Tag 0GEH)](https://stacks.math.columbia.edu/tag/0GEH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-! ### Local boundedness below on schemes -/

section LocallyBoundedBelow

/-- Local boundedness below depends only on the isomorphism class of the object. -/
theorem RingedSpace.IsLocallyBoundedBelow.of_iso {X : RingedSpace.{u, u}}
    {E E' : DerivedCategory (OXMod.{u, u} X)} (e : E ≅ E')
    (h : RingedSpace.IsLocallyBoundedBelow X E) : RingedSpace.IsLocallyBoundedBelow X E' := by
  intro x
  obtain ⟨U, hxU, N, hN⟩ := h x
  exact ⟨U, hxU, N, fun i hi => (hN i hi).of_iso
    ((RingedSpace.restrictModules X U).mapIso
      ((DerivedCategory.homologyFunctor _ i).mapIso e)).symm⟩

/-- Local boundedness below depends only on the isomorphism class of the object. -/
theorem RingedSpace.isLocallyBoundedBelow_iso_iff {X : RingedSpace.{u, u}}
    {E E' : DerivedCategory (OXMod.{u, u} X)} (e : E ≅ E') :
    RingedSpace.IsLocallyBoundedBelow X E ↔ RingedSpace.IsLocallyBoundedBelow X E' :=
  ⟨RingedSpace.IsLocallyBoundedBelow.of_iso e, RingedSpace.IsLocallyBoundedBelow.of_iso e.symm⟩

variable {P Q : Scheme.{u}}

/-- Derived pullback along an open immersion of schemes preserves boundedness below. -/
theorem isGE_derivedPullback_openImmersion (φ : P ⟶ Q) [IsOpenImmersion φ]
    (F : DerivedCategory (OXMod.{u, u} Q.toRingedSpace)) (N : ℤ) (h : F.IsGE N) :
    ((derivedPullback φ.toLRSHom.toShHom).obj F).IsGE N := by
  have : SheafedSpace.IsOpenImmersion φ.toLRSHom.toShHom := (inferInstance : IsOpenImmersion φ)
  have := (modulePullback φ.toLRSHom.toShHom).preservesFiniteLimits_of_preservesHomology
  exact isGE_derivedPullback _ F N h

/-- **Local boundedness below on a scheme, through open immersions.** An object `F` of
`D(𝒪_Q)` is locally bounded below exactly when every point of `Q` lies in the image of an open
immersion `j : Y ⟶ Q` with `Lj^*F` bounded below. -/
theorem isLocallyBoundedBelow_iff_forall_openImmersion
    (F : DerivedCategory (OXMod.{u, u} Q.toRingedSpace)) :
    RingedSpace.IsLocallyBoundedBelow Q.toRingedSpace F ↔
      ∀ q : Q, ∃ (Y : Scheme.{u}) (j : Y ⟶ Q) (_ : IsOpenImmersion j), q ∈ Set.range j.base ∧
        ∃ N : ℤ, ((derivedPullback j.toLRSHom.toShHom).obj F).IsGE N := by
  rw [RingedSpace.isLocallyBoundedBelow_iff_forall_exists_isBoundedBelow]
  refine forall_congr' fun q => ⟨?_, ?_⟩
  · rintro ⟨W, hqW, N, hN⟩
    let W' : Q.Opens := W
    refine ⟨W', W'.ι, inferInstance, by rw [Scheme.Opens.range_ι]; exact hqW, N, ?_⟩
    exact (isGE_congr ((Scheme.Modules.derivedRestrictModulesIsoDerivedPullback Q W').app F) N).1
      ((DerivedCategory.isGE_iff _ N).2 hN)
  · rintro ⟨Y, j, _, hq, N, hN⟩
    refine ⟨j.opensRange, by rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]; exact hq, N, ?_⟩
    have h1 : ((derivedPullback j.opensRange.ι.toLRSHom.toShHom).obj F).IsGE N :=
      (isGE_congr ((Stacks.DerivedPullback.schemeFactorIso j.isoOpensRange.inv j _
        (Scheme.Hom.isoOpensRange_inv_comp j)).app F) N).1
        (isGE_derivedPullback_openImmersion _ _ N hN)
    exact (DerivedCategory.isGE_iff _ N).1 ((isGE_congr
      ((Scheme.Modules.derivedRestrictModulesIsoDerivedPullback Q j.opensRange).app F) N).2 h1)

/-- **Local boundedness below is preserved by derived pullback along an open immersion.** -/
theorem isLocallyBoundedBelow_derivedPullback_of_isOpenImmersion (φ : P ⟶ Q) [IsOpenImmersion φ]
    (F : DerivedCategory (OXMod.{u, u} Q.toRingedSpace))
    (h : RingedSpace.IsLocallyBoundedBelow Q.toRingedSpace F) :
    RingedSpace.IsLocallyBoundedBelow P.toRingedSpace
      ((derivedPullback φ.toLRSHom.toShHom).obj F) := by
  rw [isLocallyBoundedBelow_iff_forall_openImmersion] at h
  refine (isLocallyBoundedBelow_iff_forall_openImmersion _).2 fun p => ?_
  obtain ⟨Y, j, _, hq, N, hN⟩ := h (φ.base p)
  refine ⟨pullback j φ, pullback.snd j φ, inferInstance, ?_, N, ?_⟩
  · rw [Scheme.Pullback.range_snd]
    exact hq
  · refine (isGE_congr (((Stacks.DerivedPullback.schemeFactorIso (pullback.snd j φ) φ _
      rfl).app F) ≪≫ ((Stacks.DerivedPullback.schemeFactorIso (pullback.fst j φ) j _
      pullback.condition).app F).symm) N).2 ?_
    exact isGE_derivedPullback_openImmersion _ _ N hN

/-- **Local boundedness below glues along open immersions.** If every point of `Q` lies in the
image of an open immersion `φ : P ⟶ Q` with `Lφ^*F` locally bounded below, then `F` is locally
bounded below. -/
theorem isLocallyBoundedBelow_of_forall_openImmersion
    (F : DerivedCategory (OXMod.{u, u} Q.toRingedSpace))
    (h : ∀ q : Q, ∃ (P : Scheme.{u}) (φ : P ⟶ Q) (_ : IsOpenImmersion φ),
      q ∈ Set.range φ.base ∧ RingedSpace.IsLocallyBoundedBelow P.toRingedSpace
        ((derivedPullback φ.toLRSHom.toShHom).obj F)) :
    RingedSpace.IsLocallyBoundedBelow Q.toRingedSpace F := by
  refine (isLocallyBoundedBelow_iff_forall_openImmersion _).2 fun q => ?_
  obtain ⟨P, φ, _, ⟨p, rfl⟩, hP⟩ := h q
  obtain ⟨Y, j, _, ⟨y, rfl⟩, N, hN⟩ := (isLocallyBoundedBelow_iff_forall_openImmersion _).1 hP p
  exact ⟨Y, j ≫ φ, inferInstance, ⟨y, rfl⟩, N,
    (isGE_congr ((Stacks.DerivedPullback.schemeFactorIso j φ _ rfl).app F) N).1 hN⟩

/-- **Local boundedness below transports along an isomorphism of schemes.** -/
theorem isLocallyBoundedBelow_derivedPullback_iso_iff (φ : P ≅ Q)
    (F : DerivedCategory (OXMod.{u, u} Q.toRingedSpace)) :
    RingedSpace.IsLocallyBoundedBelow P.toRingedSpace
        ((derivedPullback φ.hom.toLRSHom.toShHom).obj F) ↔
      RingedSpace.IsLocallyBoundedBelow Q.toRingedSpace F := by
  refine ⟨fun h => ?_, isLocallyBoundedBelow_derivedPullback_of_isOpenImmersion φ.hom F⟩
  exact (isLocallyBoundedBelow_derivedPullback_of_isOpenImmersion φ.inv _ h).of_iso
    ((Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso
      (Scheme.forgetToRingedSpace.mapIso φ)).app F)

end LocallyBoundedBelow

/-! ### Fibres -/

section Fibre

/-- **The fibre condition transports along an isomorphism of morphisms of schemes.** For a
commutative square `f ≫ β = α ≫ f'` with `α`, `β` isomorphisms and a point `s` of `S`, the derived
fibre of `Lα^*E'` over `s` is locally bounded below exactly when the derived fibre of `E'` over
`β(s)` is. -/
theorem isLocallyBoundedBelow_fibre_iff_of_arrowIso {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (α : X ≅ X') (β : S ≅ S') (w : f ≫ β.hom = α.hom ≫ f')
    (E' : DerivedCategory (OXMod.{u, u} X'.toRingedSpace)) (s : S) :
    RingedSpace.IsLocallyBoundedBelow (pullback f (S.fromSpecResidueField s)).toRingedSpace
        ((derivedPullback (pullback.fst f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj
          ((derivedPullback α.hom.toLRSHom.toShHom).obj E')) ↔
      RingedSpace.IsLocallyBoundedBelow
        (pullback f' (S'.fromSpecResidueField (β.hom.base s))).toRingedSpace
        ((derivedPullback
          (pullback.fst f' (S'.fromSpecResidueField (β.hom.base s))).toLRSHom.toShHom).obj E') := by
  let Φ := pullback.map f (S.fromSpecResidueField s) f' (S'.fromSpecResidueField (β.hom.base s))
    α.hom (Spec.map (β.hom.residueFieldMap s)) β.hom w
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField β.hom s).symm
  have hΦ : Φ ≫ pullback.fst f' (S'.fromSpecResidueField (β.hom.base s)) =
      pullback.fst f (S.fromSpecResidueField s) ≫ α.hom := pullback.lift_fst _ _ _
  refine Iff.trans (RingedSpace.isLocallyBoundedBelow_iso_iff ?_)
    (isLocallyBoundedBelow_derivedPullback_iso_iff (asIso Φ) _)
  exact (Stacks.DerivedPullback.schemeFactorIso _ α.hom _ rfl).app E' ≪≫
    ((Stacks.DerivedPullback.schemeFactorIso Φ _ _ hΦ).app E').symm

variable {X S U V : Scheme.{u}} (f : X ⟶ S) (g : U ⟶ V) (ι : U ⟶ X) (j : V ⟶ S)
  [IsOpenImmersion ι] [IsOpenImmersion j] (hsq : g ≫ j = ι ≫ f)

/-- The open immersion of the fibre of `g : U ⟶ V` over `s` into the fibre of `f : X ⟶ S` over
`j(s)`, for a commutative square `g ≫ j = ι ≫ f` whose horizontal edges `ι`, `j` are open
immersions. -/
def fibreOpenImmersion (s : V) :
    pullback g (V.fromSpecResidueField s) ⟶ pullback f (S.fromSpecResidueField (j.base s)) :=
  pullback.map g (V.fromSpecResidueField s) f (S.fromSpecResidueField (j.base s)) ι
    (Spec.map (j.residueFieldMap s)) j hsq
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j s).symm

/-- The morphism `fibreOpenImmersion f g ι j hsq s` is an open immersion. -/
instance (s : V) : IsOpenImmersion (fibreOpenImmersion f g ι j hsq s) := by
  unfold fibreOpenImmersion
  infer_instance

omit [IsOpenImmersion ι] [IsOpenImmersion j] in
/-- The composite of `fibreOpenImmersion f g ι j hsq s` with the projection of the fibre of `f`
to `X` equals the projection of the fibre of `g` to `U` followed by `ι`. -/
theorem fibreOpenImmersion_fst (s : V) :
    fibreOpenImmersion f g ι j hsq s ≫ pullback.fst f (S.fromSpecResidueField (j.base s)) =
      pullback.fst g (V.fromSpecResidueField s) ≫ ι :=
  pullback.lift_fst _ _ _

/-- The derived fibre of `Lι^*E` over `s` is the restriction of the derived fibre of `E` over
`j(s)` to the open subscheme `fibreOpenImmersion`. -/
def fibreOpenImmersionObjIso (s : V) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (derivedPullback (fibreOpenImmersion f g ι j hsq s).toLRSHom.toShHom).obj
        ((derivedPullback (pullback.fst f (S.fromSpecResidueField (j.base s))).toLRSHom.toShHom).obj
          E) ≅
      (derivedPullback (pullback.fst g (V.fromSpecResidueField s)).toLRSHom.toShHom).obj
        ((derivedPullback ι.toLRSHom.toShHom).obj E) :=
  (Stacks.DerivedPullback.schemeFactorIso _ _ _ (fibreOpenImmersion_fst f g ι j hsq s)).app E ≪≫
    ((Stacks.DerivedPullback.schemeFactorIso _ ι _ rfl).app E).symm

include hsq in
/-- **The fibre condition restricts to an open of the source and of the base.** -/
theorem isLocallyBoundedBelow_fibre_of_openImmersion (s : V)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : RingedSpace.IsLocallyBoundedBelow
      (pullback f (S.fromSpecResidueField (j.base s))).toRingedSpace
      ((derivedPullback (pullback.fst f (S.fromSpecResidueField (j.base s))).toLRSHom.toShHom).obj
        E)) :
    RingedSpace.IsLocallyBoundedBelow (pullback g (V.fromSpecResidueField s)).toRingedSpace
      ((derivedPullback (pullback.fst g (V.fromSpecResidueField s)).toLRSHom.toShHom).obj
        ((derivedPullback ι.toLRSHom.toShHom).obj E)) :=
  (isLocallyBoundedBelow_derivedPullback_of_isOpenImmersion _ _ h).of_iso
    (fibreOpenImmersionObjIso f g ι j hsq s E)

include hsq in
/-- A point of the fibre of `f` over `s₀ = j(s)` lying over the image of `ι` lies in the image of
`fibreOpenImmersion`, on which the derived fibre of `E` is that of `Lι^*E`. -/
theorem exists_openImmersion_fibre (s : V) (s₀ : S) (hs : j.base s = s₀)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (z : ↥(pullback f (S.fromSpecResidueField s₀)))
    (hz : (pullback.fst f (S.fromSpecResidueField s₀)).base z ∈ Set.range ι.base)
    (h : RingedSpace.IsLocallyBoundedBelow (pullback g (V.fromSpecResidueField s)).toRingedSpace
      ((derivedPullback (pullback.fst g (V.fromSpecResidueField s)).toLRSHom.toShHom).obj
        ((derivedPullback ι.toLRSHom.toShHom).obj E))) :
    ∃ (P : Scheme.{u}) (φ : P ⟶ pullback f (S.fromSpecResidueField s₀))
      (_ : IsOpenImmersion φ), z ∈ Set.range φ.base ∧
        RingedSpace.IsLocallyBoundedBelow P.toRingedSpace
          ((derivedPullback φ.toLRSHom.toShHom).obj
            ((derivedPullback (pullback.fst f (S.fromSpecResidueField s₀)).toLRSHom.toShHom).obj
              E)) := by
  subst hs
  refine ⟨_, fibreOpenImmersion f g ι j hsq s, inferInstance, ?_,
    h.of_iso (fibreOpenImmersionObjIso f g ι j hsq s E).symm⟩
  unfold fibreOpenImmersion
  rw [Scheme.Pullback.range_map]
  exact ⟨hz, (Spec.map (j.residueFieldMap s)).surjective _⟩

end Fibre

/-! ### Isomorphisms of morphisms of schemes -/

/-- The square of ringed spaces attached to an isomorphism of morphisms of schemes. -/
def ringedArrowIsoOfIso {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (α : X ≅ X')
    (β : S ≅ S') (w : f ≫ β.hom = α.hom ≫ f') :
    Scheme.Hom.ringedArrow f ≅ Scheme.Hom.ringedArrow f' :=
  Arrow.isoMk (Scheme.forgetToRingedSpace.mapIso α) (Scheme.forgetToRingedSpace.mapIso β) (by
    change Scheme.forgetToRingedSpace.map α.hom ≫ Scheme.forgetToRingedSpace.map f' =
      Scheme.forgetToRingedSpace.map f ≫ Scheme.forgetToRingedSpace.map β.hom
    rw [← Scheme.forgetToRingedSpace.map_comp, ← Scheme.forgetToRingedSpace.map_comp, w])

/-! ### Affine opens -/

section AffineOpens

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Every point of `X` lies in an affine open `U` mapped by `f` into an affine open `V` of `S`. -/
theorem exists_affineOpens_le (x : X) :
    ∃ (V : S.Opens) (U : X.Opens), IsAffineOpen V ∧ IsAffineOpen U ∧ x ∈ U ∧ U ≤ f ⁻¹ᵁ V := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top
    (f.base x))
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) hxV
  exact ⟨V, U, hV, hU, hxU, hUV⟩

end AffineOpens

end AlgebraicGeometry

end
