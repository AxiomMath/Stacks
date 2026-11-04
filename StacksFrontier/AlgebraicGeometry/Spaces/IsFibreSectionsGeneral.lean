module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.IsFibreSectionsSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.IsFibreSectionsSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# The restriction of scalars along a finite morphism is an algebraic space étale over the base

Let `z : Z ⟶ Q` be a finite morphism of algebraic spaces over `S` and let `x : X ⟶ Z` be étale.
The restriction of scalars `Res_{Z/Q}(X)` of Stacks 05YA is an algebraic space over `S` and its
projection to `Q` is étale. This is **Stacks 05XR**, with no separatedness hypothesis on `x`.

The source assumes `z` finite *locally free*; only finiteness of `z` is used here, so the
hypothesis is weaker and the statement correspondingly stronger. The source also takes the base
to be an object of the site, while `Q` here is an arbitrary algebraic space over `S`; that is
the form the fibre of a morphism of restrictions of scalars lives in, and the form Stacks 05YD
and Stacks 05YF consume.

## The shape of the argument

Choose a surjective étale chart `c : h_V ⟶ X` of `X` whose underlying scheme `V` is separated,
by Stacks 03FX. Then `c ≫ x` is étale and separated, so `Res_{Z/Q}(h_V)` is an algebraic space
with étale projection to `Q` by the separated case
(`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isSeparated`).

The induced morphism `a : Res_{Z/Q}(h_V) ⟶ Res_{Z/Q}(X)` is representable by algebraic spaces,
because every morphism into a restriction of scalars from an algebraic space is
(`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_to_restrictionOfScalars`). Its fibre
over a scheme-valued point of `Res_{Z/Q}(X)` is identified by
`AlgebraicGeometry.Space.fibreIso` with the restriction of scalars of the fibre data of the
corresponding pair of Stacks 05Y9, whose projection is étale by the separated case again — the
fibre datum is a base change of `c`, hence separated — and surjective by Stacks 05XQ over a base
object, `AlgebraicGeometry.Space.isSurjective_projection_restrictionOfScalars`. So `a` is
surjective and étale, and Stacks 03Y3 makes `Res_{Z/Q}(X)` an algebraic space, the remaining
clause — the fppf sheaf condition — being
`AlgebraicGeometry.Space.isSheaf_restrictionOfScalars`.

Étaleness of the projection is then Stacks 03FS condition (2), read on the chart obtained by
composing an atlas of `Res_{Z/Q}(h_V)` with `a`: that composite is surjective and étale, and its
composite with the projection of `Res_{Z/Q}(X)` is the atlas followed by the projection of
`Res_{Z/Q}(h_V)`, because `a` commutes with the two projections.

## Main results

* `AlgebraicGeometry.Space.restrictionOfScalarsMap_comp_projection`: the morphism of
  restrictions of scalars induced by a morphism over `Z` commutes with the projections to `Q`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars` and
  `AlgebraicGeometry.Space.isEtale_projection_restrictionOfScalars`: **Stacks 05XR**.
* `AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale_of_isFinite` and
  `AlgebraicGeometry.Space.isFibreSectionsSurjective_of_isFinite`: the two predicate-shaped
  inputs of Stacks 05YD, `AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale` and
  `AlgebraicGeometry.Space.IsFibreSectionsSurjective`, hold for a finite `z`.

## References

* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03Y3](https://stacks.math.columbia.edu/tag/03Y3)
* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z} {z : Z ⟶ Q}

/-- **The morphism of restrictions of scalars induced by a morphism over `Z` reads off the same
first component of a pair.** Postcomposition in the second component does not change the
first. -/
theorem restrictionOfScalarsMap_app_comp_projection {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    {x' : X' ⟶ Z} (hg : g ≫ x = x') (z : Z ⟶ Q) (T : BigFppfOver B S hS)
    (v : (restrictionOfScalars B S hS x' z).presheaf.obj (op T)) :
    (restrictionOfScalars B S hS x z).projection.app (op T)
        ((restrictionOfScalarsMap g hg z).1.app (op T) v) =
      (restrictionOfScalars B S hS x' z).projection.app (op T) v := by
  rw [(restrictionOfScalars B S hS x z).projection_pairEquiv T
      ((restrictionOfScalarsMap g hg z).1.app (op T) v),
    (restrictionOfScalarsMap g hg z).2 T v,
    (restrictionOfScalars B S hS x' z).projection_pairEquiv T v]
  rfl

/-- **The morphism of restrictions of scalars induced by a morphism over `Z` commutes with the
projections to `Q`.** -/
theorem restrictionOfScalarsMap_comp_projection {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    {x' : X' ⟶ Z} (hg : g ≫ x = x') (z : Z ⟶ Q) :
    (restrictionOfScalarsMap g hg z).1 ≫ (restrictionOfScalars B S hS x z).projection =
      (restrictionOfScalars B S hS x' z).projection := by
  ext T v
  exact restrictionOfScalarsMap_app_comp_projection g hg z T.unop v

/-! ### The fibre of the comparison with the separated case -/

/-- The fibre datum of a pair over `Z_U` is a base change of `z`, hence finite over `U`; and its
total morphism is a base change of `g`, hence surjective, étale and separated when `g` is. -/
private theorem fibre_data {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (hz : IsFinite B S hS z.hom) {U : BigFppfOver B S hS}
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    IsFinite B S hS p.fibreBaseMap.hom ∧
      (IsEtale B S hS g.hom → IsEtale B S hS (p.fibreTotalMap g).hom) ∧
      (IsSurjective B S hS g.hom → IsSurjective B S hS (p.fibreTotalMap g).hom) ∧
      (IsSeparated B S hS g.hom → IsSeparated B S hS (p.fibreTotalMap g).hom) :=
  ⟨isFinite_of_isPullback B S hS (IsPullback.of_hasPullback p.base z.hom).flip hz,
    fun hge => isEtale_pullback_fst B S hS p.fibreBase.property X.property X'.property
      p.lift g.hom hge,
    fun hgs => isSurjective_pullback_fst B S hS p.fibreBase.property X.property X'.property
      p.lift g.hom hgs,
    fun hgsep => MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := separatedProperty B S hS)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk p.lift : p.fibreBase ⟶ X) g).flip hgsep⟩

/-- **The fibre of the comparison morphism is surjective and étale over the test object.** The
fibre of `Res_{Z/Q}(X') ⟶ Res_{Z/Q}(X)` over a scheme-valued point is the restriction of scalars
of the fibre datum of the corresponding pair, by `AlgebraicGeometry.Space.fibreIso`; that datum
is a base change of `g`, so the separated case gives étaleness of its projection and Stacks 05XQ
over a base object gives surjectivity. -/
private theorem isSurjective_isEtale_pullback_fst_restrictionOfScalarsMap
    {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {x' : X' ⟶ Z} (hg : g ≫ x = x')
    (hg_etale : IsEtale B S hS g.hom) (hg_surjective : IsSurjective B S hS g.hom)
    (hg_separated : IsSeparated B S hS g.hom) (hz : IsFinite B S hS z.hom)
    (U : BigFppfOver B S hS)
    (ξ : yoneda.obj U ⟶ (restrictionOfScalars B S hS x z).presheaf) :
    IsSurjective B S hS (pullback.fst ξ (restrictionOfScalarsMap g hg z).1) ∧
      IsEtale B S hS (pullback.fst ξ (restrictionOfScalarsMap g hg z).1) := by
  obtain ⟨p, rfl⟩ : ∃ p : RestrictionPair B S hS x z (yoneda.obj U), p.point = ξ :=
    ⟨_, point_pairEquiv z ξ⟩
  obtain ⟨hζ, hwe, hws, hwsep⟩ := fibre_data g hz p
  have hproj_surjective : IsSurjective B S hS (p.fibreSections g).projection :=
    isSurjective_projection_restrictionOfScalars hζ (hws hg_surjective) (hwe hg_etale)
  have hproj_etale : IsEtale B S hS (p.fibreSections g).projection :=
    isEtale_projection_restrictionOfScalars_of_isSeparated (hwe hg_etale)
      (hwsep hg_separated) hζ
  have hfst : pullback.fst p.point (restrictionOfScalarsMap g hg z).1 =
      inv (fibreComparison g hg p) ≫ (p.fibreSections g).projection := by
    rw [← fibreComparison_fst g hg p, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hfst]
  exact ⟨isSurjective_comp B S hS (pointsMap_surjective_of_isIso B S hS _) hproj_surjective,
    isEtale_comp B S hS (isEtale_of_isIso B S hS _) hproj_etale⟩

/-- **A surjective étale chart of `X` by a separated scheme of the site**, packaged as a
morphism of algebraic spaces over `S` which is étale, surjective and separated, and whose
composite with `x` is separated as well. Both come from `X.obj` receiving a surjective étale
morphism from the representable presheaf of a separated scheme, by Stacks 03FX. -/
private theorem exists_separated_etale_surjective_chart (X : AlgebraicSpaces B S hS)
    (x : X ⟶ Z) :
    ∃ (X' : AlgebraicSpaces B S hS) (g : X' ⟶ X),
      IsEtale B S hS g.hom ∧ IsSurjective B S hS g.hom ∧ IsSeparated B S hS g.hom ∧
        IsSeparated B S hS (g ≫ x).hom := by
  obtain ⟨V, c, hVsep, hcS, hcE⟩ :=
    IsAlgebraicSpace.exists_etale_surjective_isSeparated_cover B S hS X.obj X.property
  exact ⟨⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩, ObjectProperty.homMk c,
    isEtale_of_presheaf_etale B S hS hcE, isSurjective_of_presheafSurjective B S hS c hcS,
    isSeparated_of_scheme_isSeparated B S hS hVsep c,
    isSeparated_of_scheme_isSeparated B S hS hVsep (c ≫ x.hom)⟩

/-! ### Stacks 05XR -/

/-- **Stacks 05XR, the algebraic space.** The restriction of scalars `Res_{Z/Q}(X)` of an étale
`x : X ⟶ Z` along a finite `z : Z ⟶ Q` is an algebraic space over `S`.

The source states this for `z` finite locally free and for `Q` an object of the site; finiteness
of `z` is all that is used, and `Q` is an arbitrary algebraic space over `S`. -/
@[stacks 05XR "algebraic space"]
theorem isAlgebraicSpace_restrictionOfScalars (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) :
    IsAlgebraicSpace B S hS (restrictionOfScalars B S hS x z).presheaf := by
  obtain ⟨X', g, hg_etale, hg_surjective, hg_separated, hx'sep⟩ :=
    exists_separated_etale_surjective_chart X x
  have hx' : IsEtale B S hS (g ≫ x).hom := isEtale_comp B S hS hg_etale hx
  have hG := isAlgebraicSpace_restrictionOfScalars_of_isSeparated hx' hx'sep hz
  have hfibre := isSurjective_isEtale_pullback_fst_restrictionOfScalarsMap (x := x) g rfl
    hg_etale hg_surjective hg_separated hz
  exact isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale
    (isSheaf_restrictionOfScalars x z) hG (restrictionOfScalarsMap (x := x) g rfl z).1
    (isRepresentableByAlgebraicSpaces_to_restrictionOfScalars hx hz hG _)
    (fun U ξ => (hfibre U ξ).1) (fun U ξ => (hfibre U ξ).2)

/-- **Stacks 05XR, the étale morphism.** The projection `Res_{Z/Q}(X) ⟶ Q` of the restriction of
scalars of an étale `x : X ⟶ Z` along a finite `z : Z ⟶ Q` is étale.

The source states this for `z` finite locally free and for `Q` an object of the site; finiteness
of `z` is all that is used, and `Q` is an arbitrary algebraic space over `S`. -/
@[stacks 05XR "étale morphism"]
theorem isEtale_projection_restrictionOfScalars (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) :
    IsEtale B S hS (restrictionOfScalars B S hS x z).projection := by
  obtain ⟨X', g, hg_etale, hg_surjective, hg_separated, hx'sep⟩ :=
    exists_separated_etale_surjective_chart X x
  have hx' : IsEtale B S hS (g ≫ x).hom := isEtale_comp B S hS hg_etale hx
  have hG := isAlgebraicSpace_restrictionOfScalars_of_isSeparated hx' hx'sep hz
  have hF := isAlgebraicSpace_restrictionOfScalars hx hz
  have hfibre := isSurjective_isEtale_pullback_fst_restrictionOfScalarsMap (x := x) g rfl
    hg_etale hg_surjective hg_separated hz
  -- The base change of the comparison morphism along a test point is surjective and étale.
  have hsnd : ∀ (W : BigFppfOver B S hS) (q : yoneda.obj W ⟶
      (restrictionOfScalars B S hS x z).presheaf),
      IsSurjective B S hS (pullback.snd (restrictionOfScalarsMap (x := x) g rfl z).1 q) ∧
        IsEtale B S hS (pullback.snd (restrictionOfScalarsMap (x := x) g rfl z).1 q) := by
    intro W q
    rw [← pullbackSymmetry_hom_comp_fst]
    exact ⟨isSurjective_comp B S hS (pointsMap_surjective_of_isIso B S hS _) (hfibre W q).1,
      isEtale_comp B S hS (isEtale_of_isIso B S hS _) (hfibre W q).2⟩
  -- The comparison morphism is surjective and étale.
  have ha_surjective : IsSurjective B S hS (restrictionOfScalarsMap (x := x) g rfl z).1 :=
    isSurjective_of_isSurjective_affine_baseChange B S hS _ fun W _ q => (hsnd W q).1
  have ha_etale : IsEtale B S hS (restrictionOfScalarsMap (x := x) g rfl z).1 := by
    obtain ⟨W, q, hqS, hqE⟩ := hF.exists_atlas
    exact (isEtale_iff_exists_target_chart B S hS hG hF _).2 ⟨W, q, hqS, hqE, (hsnd W q).2⟩
  -- The chart of `Res_{Z/Q}(X)` obtained from an atlas of the separated case.
  obtain ⟨W, b, hbS, hbE⟩ := hG.exists_atlas
  have hb := (isEtale_iff_presheaf_of_yoneda B S hS b).2 hbE
  refine (isEtale_iff_exists_source_chart B S hS hF Q.property _).2
    ⟨W, b ≫ (restrictionOfScalarsMap (x := x) g rfl z).1, ?_, ?_, ?_⟩
  · exact (presheafSurjective_iff_isSurjective_yoneda B S hS _ hF W _).2
      (isSurjective_comp B S hS (isSurjective_of_presheafSurjective B S hS b hbS) ha_surjective)
  · exact (isEtale_iff_presheaf_of_yoneda B S hS _).1 (isEtale_comp B S hS hb ha_etale)
  · rw [Category.assoc, restrictionOfScalarsMap_comp_projection]
    exact isEtale_comp B S hS hb
      (isEtale_projection_restrictionOfScalars_of_isSeparated hx' hx'sep hz)

/-! ### The predicate-shaped inputs of Stacks 05YD -/

section FibreSections

variable {X' : AlgebraicSpaces B S hS}

/-- **The input Stacks 05YD takes from Stacks 05XR holds for a finite `z`.** The fibre data of
the proof of Stacks 05YD are base changes of `g` and of `z`, so `Stacks 05XR` applies to them:
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars` and
`AlgebraicGeometry.Space.isEtale_projection_restrictionOfScalars`.

The predicate is stated with `z` finite locally free; that hypothesis is not used, finiteness of
`z` being enough. -/
theorem isFibreSectionsAlgebraicEtale_of_isFinite (g : X' ⟶ X) (z : Z ⟶ Q)
    (hz : IsFinite B S hS z.hom) : IsFibreSectionsAlgebraicEtale B S hS g z := by
  intro hg_etale _ U ZU W ζ w a ι b κ hζpb hwpb
  have hζ : IsFinite B S hS ζ.hom := isFinite_of_isPullback B S hS hζpb.flip hz
  have hw_etale : IsEtale B S hS w.hom :=
    isEtale_of_isPullback B S hS _ _ _ _
      (isPullback_homMk B S hS ZU.property X'.property X.property W.property hwpb).flip hg_etale
  exact ⟨isAlgebraicSpace_restrictionOfScalars hw_etale hζ,
    isEtale_projection_restrictionOfScalars hw_etale hζ⟩

/-- **The input Stacks 05YD takes from Stacks 05XQ holds for a finite `z`.** The fibre data of
the proof of Stacks 05YD are base changes of `g` and of `z`, so Stacks 05XQ over a base object
applies to them through
`AlgebraicGeometry.Space.isSurjective_projection_restrictionOfScalars`.

The predicate is stated with `z` finite locally free; that hypothesis is not used, finiteness of
`z` being enough. -/
theorem isFibreSectionsSurjective_of_isFinite (g : X' ⟶ X) (z : Z ⟶ Q)
    (hz : IsFinite B S hS z.hom) : IsFibreSectionsSurjective B S hS g z := by
  intro hg_etale hg_surjective _ U ZU W ζ w a ι b κ hζpb hwpb
  have hζ : IsFinite B S hS ζ.hom := isFinite_of_isPullback B S hS hζpb.flip hz
  have hsq := (isPullback_homMk B S hS ZU.property X'.property X.property W.property hwpb).flip
  exact isSurjective_projection_restrictionOfScalars hζ
    (isSurjective_of_isPullback B S hS hsq hg_surjective)
    (isEtale_of_isPullback B S hS _ _ _ _ hsq hg_etale)

end FibreSections

end AlgebraicGeometry.Space

end
