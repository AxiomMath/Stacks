module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodFieldPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PresheafPointTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Elementary étale charts of a closed immersion with surjective stalk map

Let `f : X' ⟶ X` be a closed immersion of algebraic spaces over `S` with `X'` decent, let `ξ` be
a point of `X'` and let `V` be an elementary étale neighborhood of `f(ξ)` in `X`. The base change
`V ×_X X'` is an object `W` of the big site whose projection `p : W ⟶ V.scheme` is a closed
immersion of *schemes*, and it is an elementary étale neighborhood of `ξ` in `X'` at the point
`w` of `W` lying over `V.point`. In particular the Zariski stalk map

  `𝒪_{V, V.point} ⟶ 𝒪_{W, w}`

is surjective.

## Main definitions

* `AlgebraicGeometry.Space.closedImmersionBaseChangeNeighborhood`: the base change `V ×_X X'`,
  pointed at a point `w` of it over `ξ` and over `V.point`, as an elementary étale neighborhood
  of `ξ`.

## Main results

* `AlgebraicGeometry.Space.exists_point_closedImmersionBaseChangeNeighborhood`: such a point `w`
  exists.
* `AlgebraicGeometry.Space.surjective_stalkMap_rep_snd`: the projection `V ×_X X' ⟶ V` is
  surjective on Zariski stalks.
* `AlgebraicGeometry.Space.exists_elementaryEtaleNeighborhood_surjective_stalkMap`: for a closed
  immersion and a chosen elementary étale neighborhood `V` of the image point, an elementary
  étale neighborhood `U` of `ξ` together with a morphism `j : U.scheme ⟶ V.scheme` over `f`
  carrying the distinguished point to the distinguished point and surjective on Zariski stalks.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0EPL](https://stacks.math.columbia.edu/tag/0EPL)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of schemes surjective on stalks induces an isomorphism of residue fields. -/
private theorem isIso_residueFieldMap_of_surjective_stalkMap {T Q : Scheme.{u}} (g : T ⟶ Q)
    (hg : ∀ t, Function.Surjective (g.stalkMap t)) (t : T) :
    IsIso (g.residueFieldMap t) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(g.residueFieldMap t).hom.injective, ?_⟩
  refine Function.Surjective.of_comp (g := (Q.residue (g t)).hom) ?_
  change Function.Surjective (Q.residue (g t) ≫ g.residueFieldMap t).hom
  rw [Scheme.residue_residueFieldMap]
  exact IsLocalRing.residue_surjective.comp (hg t)

/-- The morphism of residue-field objects of the site induced by a morphism surjective on
stalks is an isomorphism. -/
private theorem isIso_pointedResidueFieldMap_of_surjective_stalkMap
    {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (hg : ∀ v, Function.Surjective (g.left.1.stalkMap v))
    (v : V.left.1) (w : W.left.1) (hgv : g.left.1 v = w)
    (hv : B.Contains (Spec (.of (V.left.1.residueField v))))
    (hw : B.Contains (Spec (.of (W.left.1.residueField w)))) :
    IsIso (pointedResidueFieldMap B S hS g v w hgv hv hw) := by
  have : IsIso (g.left.1.residueFieldMap v) :=
    isIso_residueFieldMap_of_surjective_stalkMap g.left.1 hg v
  have : IsIso (B.inclusion.map ((Over.forget (B.obj hS)).map
      (pointedResidueFieldMap B S hS g v w hgv hv hw))) := by
    change IsIso (Spec.map
      ((W.left.1.residueFieldCongr hgv).inv ≫ g.left.1.residueFieldMap v))
    infer_instance
  have : IsIso ((Over.forget (B.obj hS)).map
      (pointedResidueFieldMap B S hS g v w hgv hv hw)) :=
    isIso_of_reflects_iso _ B.inclusion
  exact isIso_of_reflects_iso _ (Over.forget (B.obj hS))

/-- Applying a composite of two morphisms of the site to a point of the source scheme. -/
private theorem toScheme_map_comp_apply {T Q R : BigFppfOver B S hS} (a : T ⟶ Q) (b : Q ⟶ R)
    (z : T.left.1) : (a ≫ b).left.1 z = b.left.1 (a.left.1 z) := by
  change ((BigFppfOver.toScheme B S hS).map (a ≫ b)) z = _
  rw [Functor.map_comp]
  exact Scheme.Hom.comp_apply _ _ z

/-- The projection `V ×_X X' ⟶ V` of the base change of an elementary étale neighborhood along
a closed immersion is a closed immersion of schemes, hence surjective on Zariski stalks. -/
theorem surjective_stalkMap_rep_snd {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {f : X' ⟶ X} (hf : IsClosedImmersion B S hS f)
    {x : points B S hS X} (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (z : (hf.rep.pullback V.toSpace).left.1) :
    Function.Surjective ((hf.rep.snd V.toSpace).left.1.stalkMap z) := by
  have : AlgebraicGeometry.IsClosedImmersion (hf.rep.snd V.toSpace).left.1 :=
    hf.property_snd V.toSpace
  exact (hf.rep.snd V.toSpace).left.1.stalkMap_surjective z

/-- The residue-field point of the base change `V ×_X X'` at a point over the distinguished
point of `V` is a monomorphism into `X'`. -/
theorem mono_residueFieldMap_comp_rep_fst {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {f : X' ⟶ X} (hf : IsClosedImmersion B S hS f)
    {x : points B S hS X} (V : ElementaryEtaleNeighborhood B S hS X hX x)
    (w : (hf.rep.pullback V.toSpace).left.1)
    (hpw : (hf.rep.snd V.toSpace).left.1 w = V.point) :
    Mono (yoneda.map (residueFieldMap B S hS (hf.rep.pullback V.toSpace) w
        (B.residueField_spec_contains (hf.rep.pullback V.toSpace).left.property w)) ≫
      hf.rep.fst V.toSpace) := by
  let W : BigFppfOver B S hS := hf.rep.pullback V.toSpace
  let p : W ⟶ V.scheme := hf.rep.snd V.toSpace
  let q : yoneda.obj W ⟶ X' := hf.rep.fst V.toSpace
  have hwsq : q ≫ f = yoneda.map p ≫ V.toSpace := hf.rep.w V.toSpace
  have hwcont : B.Contains (Spec (.of (W.left.1.residueField w))) :=
    B.residueField_spec_contains W.left.property w
  let ν := pointedResidueFieldMap B S hS p w V.point hpw hwcont V.residueField_contained
  have hν : ν ≫ residueFieldMap B S hS V.scheme V.point V.residueField_contained =
      residueFieldMap B S hS W w hwcont ≫ p :=
    pointedResidueFieldMap_comp B S hS p w V.point hpw hwcont V.residueField_contained
  have hνiso : IsIso ν :=
    isIso_pointedResidueFieldMap_of_surjective_stalkMap B S hS p
      (surjective_stalkMap_rep_snd B S hS hf V) w V.point hpw hwcont V.residueField_contained
  have hkey : (yoneda.map (residueFieldMap B S hS W w hwcont) ≫ q) ≫ f =
      yoneda.map ν ≫
        (yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) ≫
          V.toSpace) := by
    rw [Category.assoc, hwsq, ← Category.assoc, ← yoneda.map_comp, ← hν, yoneda.map_comp,
      Category.assoc]
  have hmono : Mono ((yoneda.map (residueFieldMap B S hS W w hwcont) ≫ q) ≫ f) := by
    rw [hkey]
    have : Mono (yoneda.map ν) := inferInstance
    have := V.mono_residueField
    infer_instance
  exact mono_of_mono _ f

/-- **The base change `V ×_X X'` as an elementary étale neighborhood of a point of `X'`.** Let
`f : X' ⟶ X` be a closed immersion of algebraic spaces over `S`, let `V` be an elementary étale
neighborhood of a point `x` of `X`, and let `w` be a point of the base change `V ×_X X'` lying
over the distinguished point of `V` and over a point `ξ` of `X'`. Then `V ×_X X'`, pointed at
`w`, is an elementary étale neighborhood of `ξ`, with structure morphism the first projection. -/
def closedImmersionBaseChangeNeighborhood {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} (hX' : IsAlgebraicSpace B S hS X')
    {f : X' ⟶ X} (hf : IsClosedImmersion B S hS f)
    {x : points B S hS X} (V : ElementaryEtaleNeighborhood B S hS X hX x)
    {ξ : points B S hS X'} (w : (hf.rep.pullback V.toSpace).left.1)
    (hw : pointsMap B S hS (yoneda.obj (hf.rep.pullback V.toSpace)) (hf.rep.fst V.toSpace)
      (presheafPoint B S hS (hf.rep.pullback V.toSpace) w
        (B.residueField_spec_contains (hf.rep.pullback V.toSpace).left.property w)) = ξ)
    (hpw : (hf.rep.snd V.toSpace).left.1 w = V.point) :
    ElementaryEtaleNeighborhood B S hS X' hX' ξ where
  scheme := hf.rep.pullback V.toSpace
  point := w
  residueField_contained :=
    B.residueField_spec_contains (hf.rep.pullback V.toSpace).left.property w
  toSpace := hf.rep.fst V.toSpace
  etale_toSpace :=
    isEtale_of_isPullback_yoneda B S hS (hf.rep.isPullback V.toSpace).flip V.etale_toSpace
  map_point := hw
  mono_residueField := mono_residueFieldMap_comp_rep_fst B S hS hf V w hpw

/-- **A point of the base change over both distinguished points exists.** For a closed immersion
`f : X' ⟶ X` of algebraic spaces over `S` with `X'` decent, a point `ξ` of `X'` lying over `x`
and an elementary étale neighborhood `V` of `x`, the base change `V ×_X X'` has a point lying
over `ξ` in `X'` and over the distinguished point of `V`. -/
theorem exists_point_closedImmersionBaseChangeNeighborhood
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hX'd : IsDecentSpace B S hS X')
    (f : X' ⟶ X) (hf : IsClosedImmersion B S hS f) (ξ : points B S hS X')
    (x : points B S hS X) (hx : pointsMap B S hS X' f ξ = x)
    (V : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ w : (hf.rep.pullback V.toSpace).left.1,
      pointsMap B S hS (yoneda.obj (hf.rep.pullback V.toSpace)) (hf.rep.fst V.toSpace)
          (presheafPoint B S hS (hf.rep.pullback V.toSpace) w
            (B.residueField_spec_contains (hf.rep.pullback V.toSpace).left.property w)) = ξ ∧
        (hf.rep.snd V.toSpace).left.1 w = V.point := by
  subst hx
  obtain ⟨U₀, j₀, hj₀, hsq₀, -⟩ :=
    exists_elementaryEtaleNeighborhood_pullback_isLocalHom B S hS hX hX' hX'd f ξ V
  let W : BigFppfOver B S hS := hf.rep.pullback V.toSpace
  let p : W ⟶ V.scheme := hf.rep.snd V.toSpace
  let q : yoneda.obj W ⟶ X' := hf.rep.fst V.toSpace
  let k : U₀.scheme ⟶ W := hf.rep.lift U₀.toSpace j₀ hsq₀.symm
  have hkq : yoneda.map k ≫ q = U₀.toSpace := hf.rep.lift_fst _ _ _
  have hkp : k ≫ p = j₀ := hf.rep.lift_snd _ _ _
  refine ⟨k.left.1 U₀.point, ?_,
    (toScheme_map_comp_apply B S hS k p U₀.point).symm.trans (by rw [hkp]; exact hj₀)⟩
  have hU := U₀.map_point
  rw [← hkq, pointsMap_comp, Function.comp_apply,
    pointsMap_presheafPoint B S hS U₀.scheme W k U₀.point U₀.residueField_contained
      (B.residueField_spec_contains W.left.property _)] at hU
  exact hU

/-- **Elementary étale charts of a closed immersion, surjective on Zariski stalks.** Let
`f : X' ⟶ X` be a closed immersion of algebraic spaces over `S` with `X'` decent, let `ξ` be a
point of `X'` and let `V` be an elementary étale neighborhood of the image of `ξ`. Then `ξ` has
an elementary étale neighborhood `U` admitting a morphism of schemes `j : U.scheme ⟶ V.scheme`
over `f` which carries the distinguished point to the distinguished point and whose Zariski
stalk map `𝒪_{V, V.point} ⟶ 𝒪_{U, U.point}` is surjective. -/
theorem exists_elementaryEtaleNeighborhood_surjective_stalkMap
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hX'd : IsDecentSpace B S hS X')
    (f : X' ⟶ X) (hf : IsClosedImmersion B S hS f) (ξ : points B S hS X')
    (V : ElementaryEtaleNeighborhood B S hS X hX (pointsMap B S hS X' f ξ)) :
    ∃ (U : ElementaryEtaleNeighborhood B S hS X' hX' ξ) (j : U.scheme ⟶ V.scheme)
      (hj : j.left.1 U.point = V.point),
      yoneda.map j ≫ V.toSpace = U.toSpace ≫ f ∧
        Function.Surjective ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
          j.left.1.stalkMap U.point).hom := by
  obtain ⟨w, hw, hpw⟩ := exists_point_closedImmersionBaseChangeNeighborhood B S hS hX hX' hX'd
    f hf ξ _ rfl V
  refine ⟨closedImmersionBaseChangeNeighborhood B S hS hX' hf V w hw hpw,
    hf.rep.snd V.toSpace, hpw, (hf.rep.w V.toSpace).symm, ?_⟩
  have hb : Function.Bijective
      ((V.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hpw.symm)).hom : _ ⟶ _).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [CommRingCat.hom_comp]
  exact (surjective_stalkMap_rep_snd B S hS hf V w).comp hb.2

end AlgebraicGeometry.Space

end
