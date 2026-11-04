module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsChartSquare

/-!
# Affineness of the spectrum of a ring map, read on functors of points

Let `ψ : R →+* R'` be a homomorphism of `u`-rings. Its spectrum `Spec R' ⟶ Spec R` is a
morphism of schemes, and `AlgebraicGeometry.Space.schemePointsMap` reads it as a morphism
`Spec R' ⟶ Spec R` of presheaves on the big fppf site of `S`. Neither of these presheaves is
representable by an object of the site — the site is bounded by a size cutoff and `R` need not
lie below it — so the representability results stated for `yoneda.obj T` with `T` an object of
the site do not apply.

This file proves that the morphism is nevertheless affine, and of finite presentation, as soon
as `ψ` makes `R'` an algebra of finite type, respectively of finite presentation, over `R`. The
finiteness hypothesis is what keeps the base changes inside the site and is not an artefact: for
an arbitrary `ψ` the base change of `Spec R' ⟶ Spec R` along a point of an object `Z` of the
site is `Spec (R' ⊗_R Γ(Z, ⊤))`, whose size is unbounded.

## Main definitions

* `AlgebraicGeometry.Space.schemePointsUnit`: the comparison of the two functors of points of
  an object of the site — the one taken in the site and the one taken in all schemes.

## Main results

* `AlgebraicGeometry.Space.isPullback_schemePointsUnit`: the comparison is Cartesian over every
  morphism of the site.
* `AlgebraicGeometry.Space.isPullback_schemePointsMap`: the functor of points of a scheme,
  restricted to the site, carries Cartesian squares of schemes to Cartesian squares.
* `AlgebraicGeometry.Space.presheaf_inverseImage_schemePointsMap`: for a property of scheme
  morphisms stable under base change, the spectrum of a ring map which is affine and locally of
  finite type satisfies the relatively representable form of that property.
* `AlgebraicGeometry.Space.isAffineHom_schemePointsMap_Spec_map`: **the affineness statement.**
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_schemePointsMap_Spec_map` and
  `AlgebraicGeometry.Space.isFinitePresentation_schemePointsMap_Spec_map`: its finite-presentation
  strengthenings.

## Implementation notes

*How the base change is produced.* The comparison `schemePointsUnit` lets the base change be
assembled from two Cartesian squares rather than built by hand. Given an object `Z` of the site
and a point `g : yoneda.obj Z ⟶ schemePoints B S hS (Spec R)`, let `γ` be the corresponding
morphism of schemes out of the scheme underlying `Z` and form the scheme fibre product
`P = Z ×_{Spec R} Spec R'`. Its projection to `Z` is affine, hence quasi-compact, and locally of
finite type, so `AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact` places
`P` below the cutoff and `AlgebraicGeometry.BigFppfOver.siteObjectOver` turns it into an object
of the site over `Z` whose underlying scheme is `P` on the nose. Pasting
`isPullback_schemePointsUnit` for that object with `isPullback_schemePointsMap` for the scheme
fibre product gives the required Cartesian square, the bottom edge being `g` because a point of
a functor of points is determined by its value on the identity.

*Why affineness is not asked of the base changes separately.* `Space.IsAffineHom` is Stacks
03WG, condition (2), and `AlgebraicGeometry.Space.isAffineHom_of_presheaf` is the implication
from condition (1), which is exactly the relatively representable form proved here. The same
form feeds `AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp` for
local finite presentation, so one construction serves both.

*The quasi-compactness and quasi-separatedness of the finite-presentation statement.* These are
deduced from affineness, and the two lemmas that do so ask their source and target to be
algebraic spaces over `S`. That is a genuine hypothesis on `schemePoints`, not a defect of those
lemmas: the functor of points of a scheme too large for the site is a sheaf but has no chart in
the site. It is dischargeable where the statement is used, because a base change of the morphism
along a point of an algebraic space is affine over that algebraic space and therefore is one.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of the site from morphisms of their underlying schemes -/

/-- A morphism between the underlying schemes of two objects of the big fppf category over `S`
which commutes with their structure morphisms, as a morphism of that category. This is the
constructive form of `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`. -/
def BigFppfOver.homOfCompEq {T W : BigFppfOver B S hS}
    (v : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hv : v ≫ B.inclusion.map W.hom = B.inclusion.map T.hom) : T ⟶ W :=
  Over.homMk (B.inclusion.preimage v) (B.inclusion.map_injective (by
    rw [Functor.map_comp, B.inclusion.map_preimage]; exact hv))

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigFppfOver.homOfCompEq v hv` is
`v`. -/
@[simp]
theorem BigFppfOver.toScheme_map_homOfCompEq {T W : BigFppfOver B S hS}
    (v : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hv : v ≫ B.inclusion.map W.hom = B.inclusion.map T.hom) :
    (BigFppfOver.toScheme B S hS).map (BigFppfOver.homOfCompEq B S hS v hv) = v :=
  B.inclusion.map_preimage v

namespace Space

/-! ### The comparison of the two functors of points of an object of the site -/

/-- **The comparison of the two functors of points of an object of the site.** An object `Z` of
the big fppf category over `S` is tested by the objects of that category, giving the presheaf
`yoneda.obj Z`, and its underlying scheme is tested by all schemes, giving on the site the
presheaf `AlgebraicGeometry.Space.schemePoints`. Forgetting the structure morphism to `S` of a
point of the first is a point of the second. -/
def schemePointsUnit (Z : BigFppfOver B S hS) :
    yoneda.obj Z ⟶ schemePoints B S hS ((BigFppfOver.toScheme B S hS).obj Z) :=
  yonedaEquiv.symm (𝟙 ((BigFppfOver.toScheme B S hS).obj Z))

/-- The comparison `schemePointsUnit` sends a point `t` of `yoneda.obj Z` to its underlying
morphism of schemes. -/
@[simp]
theorem schemePointsUnit_app (Z : BigFppfOver B S hS) (T : (BigFppfOver B S hS)ᵒᵖ)
    (t : (yoneda.obj Z).obj T) :
    (schemePointsUnit B S hS Z).app T t = (BigFppfOver.toScheme B S hS).map t := by
  change (BigFppfOver.toScheme B S hS).map t ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The morphism `schemePointsMap f` sends a point `v` of a scheme to its composite `v ≫ f`. -/
theorem schemePointsMap_app {T T' : Scheme.{u}} (f : T ⟶ T') (U : (BigFppfOver B S hS)ᵒᵖ)
    (v : (schemePoints B S hS T).obj U) :
    (schemePointsMap B S hS f).app U v = v ≫ f := rfl

/-- The restriction of a point `v` of the functor of points of a scheme along a morphism `k` of
the site is the composite of the underlying morphism of schemes of `k` with `v`. -/
theorem schemePoints_map {T : Scheme.{u}} {U V : (BigFppfOver B S hS)ᵒᵖ} (k : U ⟶ V)
    (v : (schemePoints B S hS T).obj U) :
    (schemePoints B S hS T).map k v = (BigFppfOver.toScheme B S hS).map k.unop ≫ v := rfl

/-- The point of the functor of points of the underlying scheme of `Z` corresponding to the
comparison `schemePointsUnit Z` is the identity. -/
@[simp]
theorem yonedaEquiv_schemePointsUnit (Z : BigFppfOver B S hS) :
    yonedaEquiv (schemePointsUnit B S hS Z) = 𝟙 ((BigFppfOver.toScheme B S hS).obj Z) :=
  Equiv.apply_symm_apply _ _

/-- A point of the functor of points of a scheme is the comparison morphism followed by the
morphism of schemes it corresponds to. -/
theorem schemePointsUnit_comp_schemePointsMap (Z : BigFppfOver B S hS) {T : Scheme.{u}}
    (g : yoneda.obj Z ⟶ schemePoints B S hS T) :
    schemePointsUnit B S hS Z ≫ schemePointsMap B S hS (yonedaEquiv g) = g := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp_schemePointsMap, yonedaEquiv_schemePointsUnit]
  exact Category.id_comp _

section UnitPullback

variable {W Z : BigFppfOver B S hS} (π : W ⟶ Z)

/-- The comparison square of a morphism of the site commutes. -/
theorem commSq_schemePointsUnit :
    schemePointsUnit B S hS W ≫
        schemePointsMap B S hS ((BigFppfOver.toScheme B S hS).map π) =
      yoneda.map π ≫ schemePointsUnit B S hS Z := by
  ext T t
  change (BigFppfOver.toScheme B S hS).map t ≫ (BigFppfOver.toScheme B S hS).map π =
    (BigFppfOver.toScheme B S hS).map (t ≫ π)
  rw [Functor.map_comp]

variable (s : PullbackCone (schemePointsMap B S hS ((BigFppfOver.toScheme B S hS).map π))
  (schemePointsUnit B S hS Z))

/-- The scheme-level reading of the compatibility condition of a cone over the comparison
square. -/
private theorem unitCone_cond (T : (BigFppfOver B S hS)ᵒᵖ) (x : s.pt.obj T) :
    s.fst.app T x ≫ (BigFppfOver.toScheme B S hS).map π =
      (BigFppfOver.toScheme B S hS).map (s.snd.app T x) := by
  have h := CategoryTheory.congr_fun (NatTrans.congr_app s.condition T) x
  simp only [NatTrans.comp_app_apply] at h
  exact h

/-- The point of the source of a morphism of the site determined by a point of a cone over the
comparison square. -/
private def unitConeLiftApp (T : (BigFppfOver B S hS)ᵒᵖ) (x : s.pt.obj T) : T.unop ⟶ W :=
  BigFppfOver.homOfCompEq B S hS (s.fst.app T x) (by
    rw [← BigFppfOver.toScheme_map_comp_hom π, ← Category.assoc,
      unitCone_cond B S hS π s T x, BigFppfOver.toScheme_map_comp_hom])

@[simp]
private theorem toScheme_map_unitConeLiftApp (T : (BigFppfOver B S hS)ᵒᵖ) (x : s.pt.obj T) :
    (BigFppfOver.toScheme B S hS).map (unitConeLiftApp B S hS π s T x) = s.fst.app T x :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS _ _

/-- The morphism to the source of a morphism of the site determined by a cone over the
comparison square: its underlying morphism of schemes is the first projection of the cone. -/
private def unitConeLift : s.pt ⟶ yoneda.obj W where
  app T := TypeCat.ofHom fun x => unitConeLiftApp B S hS π s T x
  naturality T T' k := by
    ext x
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    have h := CategoryTheory.congr_fun (s.fst.naturality k) x
    simp only [ConcreteCategory.comp_apply] at h
    change (BigFppfOver.toScheme B S hS).map (unitConeLiftApp B S hS π s T' (s.pt.map k x)) =
      (BigFppfOver.toScheme B S hS).map (k.unop ≫ unitConeLiftApp B S hS π s T x)
    rw [Functor.map_comp, toScheme_map_unitConeLiftApp, toScheme_map_unitConeLiftApp, h]
    exact (schemePoints_map B S hS k _)

/-- **The comparison of the two functors of points is Cartesian over every morphism of the
site.** A point of the underlying scheme of `W` and a point of `Z` which agree in the underlying
scheme of `Z` come from a unique point of `W`: the first is already compatible with the structure
morphism to `S`, because the second is and because the morphism of the site is. -/
theorem isPullback_schemePointsUnit :
    IsPullback (schemePointsUnit B S hS W) (yoneda.map π)
      (schemePointsMap B S hS ((BigFppfOver.toScheme B S hS).map π))
      (schemePointsUnit B S hS Z) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (commSq_schemePointsUnit B S hS π) (unitConeLift B S hS π) (fun s => ?_) (fun s => ?_)
    (fun s m hm _ => ?_))
  · ext T x
    exact toScheme_map_unitConeLiftApp B S hS π s T x
  · ext T x
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    change (BigFppfOver.toScheme B S hS).map (unitConeLiftApp B S hS π s T x ≫ π) =
      (BigFppfOver.toScheme B S hS).map (s.snd.app T x)
    rw [Functor.map_comp, toScheme_map_unitConeLiftApp]
    exact unitCone_cond B S hS π s T x
  · ext T x
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    have h := CategoryTheory.congr_fun (NatTrans.congr_app hm T) x
    simp only [NatTrans.comp_app_apply, schemePointsUnit_app] at h
    change (BigFppfOver.toScheme B S hS).map (m.app T x) =
      (BigFppfOver.toScheme B S hS).map (unitConeLiftApp B S hS π s T x)
    rw [toScheme_map_unitConeLiftApp]
    exact h

end UnitPullback

/-! ### The functor of points of a scheme preserves Cartesian squares -/

/-- **The functor of points of a scheme carries Cartesian squares to Cartesian squares.** The
Yoneda embedding of schemes preserves limits, and restricting a presheaf along a functor is
computed pointwise, so precomposition with the forgetful functor of the site preserves them
too. -/
theorem isPullback_schemePointsMap {P Q T T' : Scheme.{u}} {a : P ⟶ Q} {b : P ⟶ T} {f : Q ⟶ T'}
    {g : T ⟶ T'} (h : IsPullback a b f g) :
    IsPullback (schemePointsMap B S hS a) (schemePointsMap B S hS b)
      (schemePointsMap B S hS f) (schemePointsMap B S hS g) :=
  (h.map yoneda).map
    ((Functor.whiskeringLeft (BigFppfOver B S hS)ᵒᵖ Scheme.{u}ᵒᵖ (Type u)).obj
      (BigFppfOver.toScheme B S hS).op)

/-! ### The relatively representable form of a property of the spectrum of a ring map -/

/-- **The base changes of the spectrum of a ring map, read on functors of points.** Let
`f : T ⟶ T'` be an affine morphism of schemes which is locally of finite type and has a property
`Q` of scheme morphisms stable under base change. Then the morphism of presheaves on the big fppf
site of `S` which `f` induces on functors of points is relatively representable, and each of its
represented base changes has `Q`.

Affineness and local finite type are what keep the base change inside the site: it is the scheme
fibre product of `f` with a point of an object of the site, its projection to that object is
affine hence quasi-compact and is locally of finite type, so Stacks 000R, clause (5) bounds its
size by the size of the object. -/
theorem presheaf_inverseImage_schemePointsMap (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] {T T' : Scheme.{u}} (f : T ⟶ T')
    [AlgebraicGeometry.IsAffineHom f] [LocallyOfFiniteType f] (hf : Q f) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (schemePointsMap B S hS f) := by
  have _ := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS Q
  refine MorphismProperty.relative.of_exists (fun Z g => ?_)
  set γ := yonedaEquiv g
  have hflip : IsPullback (pullback.snd γ f) (pullback.fst γ f) f γ :=
    (IsPullback.of_hasPullback γ f).flip
  have hsize : B.Contains (pullback γ f) :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (pullback.fst γ f)).trans_lt Z.left.2
  refine ⟨BigFppfOver.siteObjectOver B S hS Z hsize (pullback.fst γ f),
    schemePointsUnit B S hS (BigFppfOver.siteObjectOver B S hS Z hsize (pullback.fst γ f)) ≫
      schemePointsMap B S hS (pullback.snd γ f),
    BigFppfOver.siteMapOver B S hS Z hsize (pullback.fst γ f), ?_, ?_⟩
  · have hpaste := IsPullback.paste_horiz
      (isPullback_schemePointsUnit B S hS
        (BigFppfOver.siteMapOver B S hS Z hsize (pullback.fst γ f)))
      (isPullback_schemePointsMap B S hS hflip)
    rwa [schemePointsUnit_comp_schemePointsMap B S hS Z g] at hpaste
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q) hflip hf

/-! ### Affineness and finite presentation -/

/-- **The spectrum of a ring map of finite type is affine, read on functors of points.** Let
`φ : R ⟶ R'` be a homomorphism of `u`-rings making `R'` an `R`-algebra of finite type. Then the
morphism of presheaves on the big fppf site of `S` which `Spec φ` induces on functors of points
is an affine morphism in the sense of Stacks 03WF.

Neither functor of points is asked to be representable by an object of the site, so this does not
follow from affineness of a morphism of objects of the site; finite type is what the construction
of the base changes needs. -/
theorem isAffineHom_schemePointsMap_Spec_map {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : RingHom.FiniteType φ.hom) :
    IsAffineHom B S hS (schemePointsMap B S hS (Spec.map φ)) := by
  have _ : LocallyOfFiniteType (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{u})).mpr hφ
  exact isAffineHom_of_presheaf
    (presheaf_inverseImage_schemePointsMap B S hS _ (Spec.map φ) inferInstance)

/-- **The spectrum of a ring map of finite presentation is locally of finite presentation, read
on functors of points.** This is the chart condition of Stacks 03XP, part (1), obtained from the
represented base changes through the implication of Stacks 03MJ. -/
theorem isLocallyOfFinitePresentation_schemePointsMap_Spec_map {R R' : CommRingCat.{u}}
    (φ : R ⟶ R') (hφ : RingHom.FinitePresentation φ.hom) :
    IsLocallyOfFinitePresentation B S hS (schemePointsMap B S hS (Spec.map φ)) := by
  have hlfp : LocallyOfFinitePresentation (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation.{u})).mpr hφ
  refine presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS _
    (fun i p hi hp => ?_) _
    (presheaf_inverseImage_schemePointsMap B S hS _ (Spec.map φ) hlfp)
  have _ : Etale i := hi
  have _ : LocallyOfFinitePresentation p := hp
  infer_instance

/-- **The spectrum of a ring map of finite presentation is of finite presentation, read on
functors of points.** This is Stacks 03XP, part (3): the chart condition together with
quasi-compactness and quasi-separatedness, the last two deduced from affineness.

Algebraicity of the two functors of points is a hypothesis because the two lemmas deducing
quasi-compactness and quasi-separatedness from affineness need it, and the functor of points of
a scheme too large for the site has no chart in the site. It is dischargeable after base change
along a point of an algebraic space. -/
theorem isFinitePresentation_schemePointsMap_Spec_map {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : RingHom.FinitePresentation φ.hom)
    (hsrc : IsAlgebraicSpace B S hS (schemePoints B S hS (Spec R')))
    (htgt : IsAlgebraicSpace B S hS (schemePoints B S hS (Spec R))) :
    IsFinitePresentation B S hS (schemePointsMap B S hS (Spec.map φ)) := by
  have haff := isAffineHom_schemePointsMap_Spec_map B S hS φ
    (RingHom.FiniteType.of_finitePresentation hφ)
  exact ⟨isLocallyOfFinitePresentation_schemePointsMap_Spec_map B S hS φ hφ,
    isQuasiCompact_of_isAffineHom' B S hS _ hsrc htgt haff,
    isQuasiSeparated_of_isAffineHom B S hS _ hsrc htgt haff⟩

end Space

end AlgebraicGeometry

end
