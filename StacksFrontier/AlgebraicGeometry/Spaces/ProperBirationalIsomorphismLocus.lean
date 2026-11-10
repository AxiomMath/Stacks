module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalIsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteNearCodimensionOnePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteNearFiniteGeometricFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.LargestOpenLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus
public import StacksFrontier.RingTheory.Etale.LocalRingPropertyList
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# The isomorphism locus of a proper birational morphism of algebraic spaces

Let `S` be a scheme, let `X` be a Noetherian algebraic space over `S` and let `f : Y ⟶ X` be a
proper birational morphism of algebraic spaces with `Y` reduced. Let `U ⊆ X` be the maximal open
subspace over which `f` becomes an isomorphism. **Stacks 0BBQ** says that `U` contains

1. every point of `|X|` of codimension `0`,
2. every point of `|X|` of codimension `1` whose local ring is normal, and
3. every point of `|X|` whose fibre in `|Y|` is finite and whose local ring is normal.

## Main results

* `AlgebraicGeometry.Space.mem_isomorphismLocus_of_localRingDimension_eq_zero`: part (1).
* `AlgebraicGeometry.Space.mem_isomorphismLocus_of_localRingDimension_eq_one_of_normal`:
  part (2).
* `AlgebraicGeometry.Space.mem_isomorphismLocus_of_finite_fibre_of_normal`: part (3).

## Implementation notes

The maximal open subspace is expressed by its universal property, as the greatest element of
the set of open subspaces `V ⊆ X` for which the restriction `f^{-1}(V) ⟶ V` — the second
projection of the fibre product of `f` with the inclusion of `V` — is an isomorphism. The
conclusion is membership of the point in the image of `|U| → |X|`, the point set of an open
subspace being described this way throughout; Stacks 03BZ turns that image into an open subset
of `|X|`.

Birationality of a morphism of algebraic spaces is only defined, in Stacks 0ACV as here, for
decent spaces with finitely many irreducible components, so the hypothesis carries those
witnesses existentially: the hypothesis is exactly "`f` is birational", and the witnesses are
facts about the Noetherian situation rather than extra assumptions.

Normality of the local ring of `X` at a point is `AlgebraicGeometry.IsNormalDomain` asked of
the stalk of an étale scheme chart, through the étale-invariance predicate of Stacks 0BBL; the
invariance input is `AlgebraicGeometry.isNormalDomain_localizationAtPrime_iff_of_etale`.

Part (1) is Stacks 0BBF: a birational morphism is an isomorphism over a *dense* open subspace,
and a dense open subspace of a Noetherian point space meets every irreducible component, hence
contains every generic point. Part (3) follows the source: Stacks 0A4W makes `f` finite over a
neighbourhood of the point, an affine étale chart of that neighbourhood turns the situation
into a finite birational morphism of Noetherian affine schemes, Stacks 0BFP handles that case,
and Stacks 06R2 descends the resulting isomorphism neighbourhood back to `X`. Part (2) is
part (1) together with Stacks 0AD2: the morphism is quasi-finite at every codimension-zero
point of `|Y|`, because part (1) already puts the image of such a point in `U`, so Stacks 0AD2
makes `f` finite over a neighbourhood and part (3)'s argument applies.

## References

* [Stacks Project, Tag 0BBQ](https://stacks.math.columbia.edu/tag/0BBQ)
* [Stacks Project, Tag 06R2](https://stacks.math.columbia.edu/tag/06R2)
* [Stacks Project, Tag 0A4W](https://stacks.math.columbia.edu/tag/0A4W)
* [Stacks Project, Tag 0AD2](https://stacks.math.columbia.edu/tag/0AD2)
* [Stacks Project, Tag 0B4D](https://stacks.math.columbia.edu/tag/0B4D)
* [Stacks Project, Tag 0BBF](https://stacks.math.columbia.edu/tag/0BBF)
* [Stacks Project, Tag 0BBL](https://stacks.math.columbia.edu/tag/0BBL)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Isomorphisms are local on the target for the étale topology -/

/-- A containment of subfunctors is a containment of the images of their inclusions on
points. -/
private theorem range_pointsMap_le (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V U : Subfunctor X} (hVU : V ≤ U) :
    Set.range (pointsMap B S hS V.toFunctor V.ι) ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  rintro _ ⟨z, rfl⟩
  exact ⟨pointsMap B S hS V.toFunctor (Subfunctor.homOfLe hVU) z, by
    rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩

/-- The point set of an open subspace is open. -/
private theorem isOpen_range_pointsMap_ι (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : Subfunctor X) (hV : IsOpenSubspace B S hS V) :
    IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
  rw [← openSubspacesOrderIso_apply B S hS X hX ⟨V, hV⟩]
  exact (openSubspacesOrderIso B S hS X hX ⟨V, hV⟩).isOpen

/-- In a cartesian square the second projection out of the chosen fibre product is an
isomorphism exactly when the parallel edge of the square is. -/
private theorem isIso_pullback_snd_iff {C : Type*} [Category C] {W X Y Z : C}
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g]
    (h : IsPullback a b f g) :
    IsIso (pullback.snd f g) ↔ IsIso b := by
  rw [← h.isoPullback_hom_snd, isIso_comp_left_iff]

/-- The restriction of a morphism of algebraic spaces over an open subspace of its target is an
isomorphism of algebraic spaces exactly when it is an isomorphism of presheaves: fibre products
of algebraic spaces are computed in presheaves. -/
private theorem isIso_pullback_snd_iff_hom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIso (pullback.snd f g) ↔ IsIso (pullback.snd f.hom g.hom) := by
  rw [isIso_pullback_snd_iff (AlgebraicSpaces.isPullback_fiberProduct B S hS f g)]
  exact (ObjectProperty.isIso_hom_iff
    (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
      AlgebraicSpaces.fiberProduct B S hS f g ⟶ Y)).symm

/-- Being an isomorphism is local on the target for the étale topology of Stacks 03YH: it is
local for the fpqc topology, and an étale covering family is an fpqc covering family. -/
private theorem isomorphisms_isLocalAtTarget_etale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget
      (Topology.precoverage.{u, u + 1} .etale B S hS) := by
  apply MorphismProperty.IsLocalAtTarget.of_le
    (L := Topology.precoverage.{u, u + 1} .fpqc B S hS)
  rintro X R ⟨I, Xi, f, rfl, hX, hXi, hf⟩
  exact ⟨I, Xi, f, rfl, hX, hXi, isFpqcCovering_of_isEtaleCovering B S hS _ _ hf⟩

private theorem etale_ne_fpqc : (Topology.etale : Topology) ≠ .fpqc := by decide

/-- **Stacks 06R2 for isomorphisms.** Every morphism of algebraic spaces over `S` has a
greatest open subspace of its target over which it becomes an isomorphism, so the hypothesis
`hU` of the three parts of Stacks 0BBQ below is satisfiable. -/
theorem exists_isGreatest_isIso_pullback_snd (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X) (f : Y ⟶ X) :
    ∃ U : Subfunctor X, IsGreatest {V : Subfunctor X | IsOpenSubspace B S hS V ∧
      IsIso (pullback.snd f V.ι)} U := by
  let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let f' : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X' := ObjectProperty.homMk f
  let P := MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)
  have : P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .etale B S hS) :=
    isomorphisms_isLocalAtTarget_etale B S hS
  let V := largestOpenSubspace B S hS .etale etale_ne_fpqc P f'
  refine ⟨V.1.1, ⟨V.1.2,
    (isIso_pullback_snd_iff_hom B S hS f' (openInclusion B S hS V.1)).mp V.2.1⟩, ?_⟩
  intro W hW
  let W' : {W' : Subfunctor X'.obj // IsOpenSubspace B S hS W'} := ⟨W, hW.1⟩
  exact V.2.2 W' ((isIso_pullback_snd_iff_hom B S hS f' (openInclusion B S hS W')).mpr hW.2)

/-- **The étale descent step.** If `f` becomes an isomorphism after base change along an étale
morphism `a : T ⟶ X`, then the image in `|X|` of every point of `|T|` lies in the point set of
the maximal open subspace over which `f` is an isomorphism.

Stacks 06R2 provides the largest open subspace over which `f` is an isomorphism, which is
contained in `U` by maximality of `U`, and part (1) of that tag factors `a` through it. -/
private theorem mem_isomorphismLocus_of_isEtale_isIso_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hT : IsAlgebraicSpace B S hS T)
    (f : Y ⟶ X) (a : T ⟶ X) (ha : IsEtale B S hS a) (hfa : IsIso (pullback.snd f a))
    (U : Subfunctor X)
    (hU : IsGreatest {V : Subfunctor X | IsOpenSubspace B S hS V ∧
      IsIso (pullback.snd f V.ι)} U)
    (t : points B S hS T) :
    pointsMap B S hS T a t ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let f' : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X' := ObjectProperty.homMk f
  let a' : (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ X' := ObjectProperty.homMk a
  let P := MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)
  have : P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .etale B S hS) :=
    isomorphisms_isLocalAtTarget_etale B S hS
  let V := largestOpenSubspace B S hS .etale etale_ne_fpqc P f'
  have hV : IsIso (pullback.snd f V.1.1.ι) :=
    (isIso_pullback_snd_iff_hom B S hS f' (openInclusion B S hS V.1)).mp V.2.1
  have hVU : V.1.1 ≤ U := hU.2 ⟨V.1.2, hV⟩
  obtain ⟨b, hb⟩ := factorsThrough_largestOpenSubspace B S hS .etale etale_ne_fpqc P f' a' ha
    ((isIso_pullback_snd_iff_hom B S hS f' a').mpr hfa)
  let b' : T ⟶ V.1.1.toFunctor := b.hom
  have hb' : b' ≫ V.1.1.ι = a := congrArg (fun k => k.hom) hb
  refine range_pointsMap_le B S hS hVU ⟨pointsMap B S hS T b' t, ?_⟩
  rw [← pointsMap_comp_apply, hb']

/-! ### Finiteness over a neighbourhood of a point with finite fibre -/

/-- **Stacks 0A4W in the set-theoretic form the source uses.** A proper morphism of decent
algebraic spaces whose fibre over a point of the target is a finite set is finite over an open
neighbourhood of that point.

The point is the image of a geometric point by Stacks 0488, and for decent spaces a finite
set-theoretic fibre forces the geometric fibre to be finite as well, by Stacks 0ACK. -/
@[ega "III 4.4.11" "partial"]
private theorem exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fibre
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hDY : IsDecentSpace B S hS Y) (hDX : IsDecentSpace B S hS X)
    (f : Y ⟶ X) (hf : IsProper B S hS f) (x : points B S hS X)
    (hfinite : ((pointsMap B S hS Y f) ⁻¹' {x}).Finite) :
    ∃ V : Subfunctor X, IsOpenSubspace B S hS V ∧
      x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      IsFinite B S hS (pullback.snd f V.ι) := by
  classical
  obtain ⟨p, hp⟩ := exists_geometricRepresentative B S hS X x
  have hpfinite : (setFibre B S hS f p.val).Finite :=
    hfinite.subset fun y hy => hy.trans hp
  have huniv : (Set.univ : Set (points B S hS (fieldFibre B S hS f p.val))).Finite :=
    finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent B S hS hY hX f p.val
      hf.2.1.1 hDY hDX hpfinite
  obtain ⟨V, hV, hxV, hfin⟩ :=
    exists_isOpenSubspace_isFinite_pullback_snd_of_finite_geometricFibre B S hS hY hX f hf p
      (Set.finite_univ_iff.mp huniv)
  exact ⟨V, hV, hp ▸ hxV, hfin⟩

/-- The inverse of the comparison homeomorphism of Stacks 03BX is natural in the site object. -/
theorem schemePointsHomeomorph_symm_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A C : BigFppfOver B S hS} (q : A ⟶ C)
    (y : (BigFppfOver.toScheme B S hS).obj A) :
    (schemePointsHomeomorph B S hS C).symm ((BigFppfOver.toScheme B S hS).map q y) =
      pointsMap B S hS (yoneda.obj A) (yoneda.map q)
        ((schemePointsHomeomorph B S hS A).symm y) := by
  apply (schemePointsHomeomorph B S hS C).injective
  rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply,
    pointsToScheme_pointsMap_yoneda, ← schemePointsHomeomorph_apply,
    Homeomorph.apply_symm_apply]

/-- The inverse of the comparison homeomorphism of Stacks 03BX sends the scheme point of a
field-valued point to its class. -/
private theorem schemePointsHomeomorph_symm_schemePoint (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (A : BigFppfOver B S hS) (p : FieldValuedPoint B S hS (yoneda.obj A)) :
    (schemePointsHomeomorph B S hS A).symm (schemePoint B S hS A p) =
      p.class B S hS (yoneda.obj A) := by
  apply (schemePointsHomeomorph B S hS A).injective
  rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply, pointsToScheme_class]

/-- An open immersion of schemes carries a normal-domain stalk at the image of a point back to
the stalk at that point. -/
theorem isDomain_and_isIntegrallyClosed_stalk_of_isOpenImmersion {X Y : Scheme.{u}}
    (g : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion g] (y : Y)
    (hn : IsNormalDomain (X.presheaf.stalk (g y))) :
    IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
  have : IsIso (g.stalkMap y) :=
    (AlgebraicGeometry.IsOpenImmersion.iff_isIso_stalkMap.mp
      ‹AlgebraicGeometry.IsOpenImmersion g›).2 y
  let e : X.presheaf.stalk (g y) ≃+* Y.presheaf.stalk y :=
    (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv
  have hd : IsDomain (Y.presheaf.stalk y) := e.toMulEquiv.isDomain_iff.mp hn.isDomain
  have := hn.isIntegrallyClosed
  exact ⟨hd, IsIntegrallyClosed.of_equiv e⟩

/-! ### Birationality of a representable model -/

/-- A representable model of a birational morphism of algebraic spaces is bijective on generic
points. -/
private theorem bijOn_genericPoints_map_of_isBirational
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hDF : IsDecentSpace B S hS F) (hDG : IsDecentSpace B S hS G)
    (hCF : (irreducibleComponents (points B S hS F)).Finite)
    (hCG : (irreducibleComponents (points B S hS G)).Finite)
    (f : F ⟶ G) (hf : IsBirational B S hS hF hG hDF hDG hCF hCG f)
    (A C : BigFppfOver B S hS) (eA : yoneda.obj A ≅ F) (eC : yoneda.obj C ≅ G)
    (q : A ⟶ C) (hq : eA.hom ≫ f = yoneda.map q ≫ eC.hom) :
    Set.BijOn ((BigFppfOver.toScheme B S hS).map q)
      (genericPoints ((BigFppfOver.toScheme B S hS).obj A))
      (genericPoints ((BigFppfOver.toScheme B S hS).obj C)) := by
  let T := BigFppfOver.toScheme B S hS
  let qS := T.map q
  let a := (schemePointsHomeomorph B S hS A).symm.trans (pointsHomeomorphOfIso B S hS eA)
  let c := (schemePointsHomeomorph B S hS C).symm.trans (pointsHomeomorphOfIso B S hS eC)
  have hcompat (y : T.obj A) : c (qS y) = pointsMap B S hS F f (a y) := by
    have hmap : (schemePointsHomeomorph B S hS C).symm (qS y) =
        pointsMap B S hS (yoneda.obj A) (yoneda.map q)
          ((schemePointsHomeomorph B S hS A).symm y) :=
      schemePointsHomeomorph_symm_map B S hS q y
    change pointsMap B S hS (yoneda.obj C) eC.hom
        ((schemePointsHomeomorph B S hS C).symm (qS y)) =
      pointsMap B S hS F f
        (pointsMap B S hS (yoneda.obj A) eA.hom ((schemePointsHomeomorph B S hS A).symm y))
    rw [hmap, ← pointsMap_comp_apply, ← pointsMap_comp_apply, hq]
  have hb := hf.bijOn B S hS hF hG hDF hDG hCF hCG
  change Set.BijOn qS (genericPoints (T.obj A)) (genericPoints (T.obj C))
  refine ⟨fun y hy => ?_, fun y hy z hz hyz => ?_, fun z hz => ?_⟩
  · have hh := c.symm.mem_genericPoints (hb.mapsTo (a.mem_genericPoints hy))
    rwa [← hcompat, c.symm_apply_apply] at hh
  · refine a.injective (hb.injOn (a.mem_genericPoints hy) (a.mem_genericPoints hz) ?_)
    rw [← hcompat, ← hcompat, hyz]
  · obtain ⟨w, hw, hwz⟩ := hb.surjOn (c.mem_genericPoints hz)
    refine ⟨a.symm w, a.symm.mem_genericPoints hw, c.injective ?_⟩
    rw [hcompat, a.apply_symm_apply, hwz]

/-- **A representable model of a birational morphism of algebraic spaces is birational as a
morphism of schemes.** The two isomorphisms identify the point spaces with the point spaces of
the two schemes, by Stacks 03BX, so bijectivity on generic points transports; the local ring
map of Stacks 0ACV at a generic point is, by its characterisation on compatible generic charts,
the stalk map of the morphism of schemes there. -/
private theorem isBirational_map_of_isBirational
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hDF : IsDecentSpace B S hS F) (hDG : IsDecentSpace B S hS G)
    (hCF : (irreducibleComponents (points B S hS F)).Finite)
    (hCG : (irreducibleComponents (points B S hS G)).Finite)
    (f : F ⟶ G) (hf : IsBirational B S hS hF hG hDF hDG hCF hCG f)
    (A C : BigFppfOver B S hS) (eA : yoneda.obj A ≅ F) (eC : yoneda.obj C ≅ G)
    (q : A ⟶ C) (hq : eA.hom ≫ f = yoneda.map q ≫ eC.hom) :
    _root_.AlgebraicGeometry.IsBirational ((BigFppfOver.toScheme B S hS).map q) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let qS := T.map q
  let a := (schemePointsHomeomorph B S hS A).symm.trans (pointsHomeomorphOfIso B S hS eA)
  have hb := hf.bijOn B S hS hF hG hDF hDG hCF hCG
  refine _root_.AlgebraicGeometry.isBirational_of_bijOn_of_isIso_stalkMap qS
    (bijOn_genericPoints_map_of_isBirational B S hS hF hG hDF hDG hCF hCG f hf A C eA eC q hq)
    fun y hy => ?_
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS A y
  have hclass : (schemePointsHomeomorph B S hS A).symm y = p.class B S hS (yoneda.obj A) :=
    hp ▸ schemePointsHomeomorph_symm_schemePoint B S hS A p
  let r := FieldValuedPoint.map B S hS (yoneda.obj A) (yoneda.map q) p
  let z := a y
  have hz : z ∈ genericPoints (points B S hS F) := a.mem_genericPoints hy
  have hw : pointsMap B S hS F f z ∈ genericPoints (points B S hS G) := hb.mapsTo hz
  let ca : GenericChart B S hS z :=
    { U := A
      immersion := eA.hom
      isOpen := isOpenImmersion_of_isIso B S hS eA.hom
      point := p
      mapsTo := by
        rw [← hclass]
        rfl }
  let cc : GenericChart B S hS (pointsMap B S hS F f z) :=
    { U := C
      immersion := eC.hom
      isOpen := isOpenImmersion_of_isIso B S hS eC.hom
      point := r
      mapsTo := by
        change pointsMap B S hS (yoneda.obj C) eC.hom
            (pointsMap B S hS (yoneda.obj A) (yoneda.map q) (p.class B S hS (yoneda.obj A))) = _
        rw [← pointsMap_comp_apply, ← hq, pointsMap_comp_apply, ← hclass]
        rfl }
  have hr : qS (schemePoint B S hS A p) = schemePoint B S hS C r :=
    (schemePoint_map_yoneda B S hS q p).symm
  have hspec := (exists_genericLocalRingMap B S hS hF hG
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hF hDF)
    (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hG hDG)
    hCF hCG f z hz hw).choose_spec ca cc q hq hr
  have hi := hf.isIso_genericLocalRingMap B S hS hF hG hDF hDG hCF hCG z hz
  rw [show genericLocalRingMap B S hS hF hG
      (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hF hDF)
      (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hG hDG) hCF hCG f z hz hw =
    (exists_genericLocalRingMap B S hS hF hG
      (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hF hDF)
      (hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hG hDG)
      hCF hCG f z hz hw).choose from rfl, hspec] at hi
  simp only [isIso_comp_left_iff, isIso_comp_right_iff] at hi
  rwa [hp] at hi

/-! ### The affine chart over which the morphism is finite -/

/-- The restriction of a morphism of the site to an open subscheme of its target becomes, after
Yoneda, an isomorphism over the open subspace cut out by that open subscheme. -/
private theorem isIso_yoneda_pullback_snd_of_isIso_morphismRestrict
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A C : BigFppfOver B S hS} (q : C ⟶ A)
    (W : ((BigFppfOver.toScheme B S hS).obj A).Opens)
    (hW : IsIso (((BigFppfOver.toScheme B S hS).map q) ∣_ W)) :
    IsIso (pullback.snd (yoneda.map q) (yoneda.map (openSiteObjectHom B S hS A W))) := by
  let T := BigFppfOver.toScheme B S hS
  let j := openSiteObjectHom B S hS A W
  have : PreservesLimitsOfShape WalkingCospan T := comp_preservesLimitsOfShape _ _
  have hi : IsIso (pullback.snd (T.map q) (T.map j)) := by
    rw [map_openSiteObjectHom]
    rwa [show (T.map q) ∣_ W =
      (pullbackRestrictIsoRestrict (T.map q) W).inv ≫ pullback.snd (T.map q) W.ι from rfl,
      isIso_comp_left_iff] at hW
  have : IsIso (T.map (pullback.snd q j)) :=
    (isIso_pullback_snd_iff ((IsPullback.of_hasPullback q j).map T)).mp hi
  have : IsIso (pullback.snd q j) := isIso_of_reflects_iso (pullback.snd q j) T
  exact (isIso_pullback_snd_iff ((IsPullback.of_hasPullback q j).map yoneda)).mpr
    (inferInstance : IsIso (yoneda.map (pullback.snd q j)))

/-- Composing the Yoneda image of the inclusion of an open subscheme with an étale morphism gives
an étale morphism. -/
private theorem presheaf_etale_yoneda_map_openSiteObjectHom_comp (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (a : yoneda.obj T ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf a) :
    (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (openSiteObjectHom B S hS T W) ≫ a) := by
  have := isMultiplicative_presheaf_etale B S hS
  have hWι : AlgebraicGeometry.IsOpenImmersion W.ι := inferInstance
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (openSiteObjectHom B S hS T W)) := by
    rw [map_openSiteObjectHom]
    exact hWι
  exact MorphismProperty.comp_mem _ _ _
    (presheaf_etale_of_isOpenImmersion B S hS (isOpenImmersion_yoneda_map B S hS _ this)) ha

/-- **The affine case.** Let `f : Y ⟶ X` be a birational morphism of algebraic spaces with `X`
locally Noetherian and `Y` reduced, let `a : h_A ⟶ X` be an étale chart with `A` affine, and
suppose the base change of `f` along `a` is represented by a finite morphism `q` of schemes.
Then the image in `|X|` of any point of `A` with normal local ring lies in the maximal open
subspace over which `f` is an isomorphism.

Stacks 0B4D makes the base change birational as a morphism of algebraic spaces, hence (see
`AlgebraicGeometry.Space.isBirational_map_of_isBirational`) `q` birational as a morphism of
schemes; `q` is finite, so proper, and Stacks 0BFP gives an open neighbourhood of the point in
`A` over which `q` is an isomorphism. Composing the étale chart with the inclusion of that
neighbourhood gives an étale morphism over which `f` becomes an isomorphism, and the descent
step concludes. -/
private theorem mem_isomorphismLocus_of_finite_affine_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hDY : IsDecentSpace B S hS Y) (hDX : IsDecentSpace B S hS X)
    (hCY : (irreducibleComponents (points B S hS Y)).Finite)
    (hCX : (irreducibleComponents (points B S hS X)).Finite)
    (f : Y ⟶ X) (hf : IsBirational B S hS hY hX hDY hDX hCY hCX f)
    (hN : HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hR : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsReduced Z))
    (A C : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj A)]
    (a : yoneda.obj A ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (q : C ⟶ A) (i : yoneda.obj C ⟶ Y) (hp : IsPullback i (yoneda.map q) f a)
    [AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map q)]
    (t : (BigFppfOver.toScheme B S hS).obj A)
    [IsDomain (((BigFppfOver.toScheme B S hS).obj A).presheaf.stalk t)]
    [IsIntegrallyClosed (((BigFppfOver.toScheme B S hS).obj A).presheaf.stalk t)]
    (U : Subfunctor X)
    (hU : IsGreatest {V : Subfunctor X | IsOpenSubspace B S hS V ∧
      IsIso (pullback.snd f V.ι)} U) :
    pointsMap B S hS _ a ((schemePointsHomeomorph B S hS A).symm t) ∈
      Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  have he := isEtale_of_presheaf_etale B S hS ha
  have : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hi : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf i :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip ha
  have : IsLocallyNoetherian (T.obj A) :=
    (exists_atlas_iff_forall_etale B S hS X (fun Z : Scheme.{u} => IsLocallyNoetherian Z)
      hX).mp hN A a ha
  have : IsReduced (T.obj C) :=
    (exists_atlas_iff_forall_etale B S hS Y (fun Z : Scheme.{u} => IsReduced Z) hY).mp hR C i hi
  have hbir := isBirational_pullback_snd_of_isEtale B S hS hY hX hDY hDX hCY hCX f hf A a he
  have hqbir := isBirational_map_of_isBirational B S hS
    (isAlgebraicSpace_pullback B S hS f a hY (isAlgebraicSpace_yoneda B S hS A) hX)
    (isAlgebraicSpace_yoneda B S hS A) _ _ _ _ (pullback.snd f a) hbir C A hp.isoPullback
    (Iso.refl _) q (by simp)
  have : _root_.AlgebraicGeometry.IsNoetherian (T.obj A) :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  obtain ⟨W, htW, hW⟩ := exists_isIso_restrict_of_finite_fiber_of_normal (T.map q) hqbir t
    ((T.map q).finite_preimage_singleton t)
  let A' := openSiteObject B S hS A W
  let j := openSiteObjectHom B S hS A W
  have hs := (IsPullback.of_hasPullback (yoneda.map q) (yoneda.map j)).paste_horiz hp
  have hfb : IsIso (pullback.snd f (yoneda.map j ≫ a)) :=
    (isIso_pullback_snd_iff hs).mpr
      (isIso_yoneda_pullback_snd_of_isIso_morphismRestrict B S hS q W hW)
  have hmem := mem_isomorphismLocus_of_isEtale_isIso_pullback B S hS hY hX
    (isAlgebraicSpace_yoneda B S hS A') f (yoneda.map j ≫ a)
    (isEtale_of_presheaf_etale B S hS
      (presheaf_etale_yoneda_map_openSiteObjectHom_comp B S hS W a ha)) hfb U hU
    ((schemePointsHomeomorph B S hS A').symm ⟨t, htW⟩)
  rw [pointsMap_comp_apply] at hmem
  exact Set.mem_of_eq_of_mem
    (congrArg (pointsMap B S hS _ a) (schemePointsHomeomorph_symm_map B S hS j ⟨t, htW⟩)) hmem

/-! ### From finiteness over a neighbourhood to the isomorphism locus -/

/-- **A morphism is quasi-finite at a point whose image lies in the isomorphism locus.** The
preimage of the open subspace is an open subspace containing the point, and its inclusion
composed with the morphism is an open immersion, hence étale, hence locally quasi-finite by
Stacks 03XU. -/
private theorem isQuasiFiniteAt_of_mem_isomorphismLocus
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (f : Y ⟶ X) (V : Subfunctor X) (hV : IsOpenSubspace B S hS V)
    (hiso : IsIso (pullback.snd f V.ι)) (y : points B S hS Y)
    (hy : pointsMap B S hS Y f y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)) :
    IsQuasiFiniteAt B S hS f y := by
  have hP := isOpenSubspace_preimage B S hS f V hX hY hV
  obtain ⟨p, hp⟩ : y ∈ Set.range (pointsMap B S hS (V.preimage f).toFunctor
      (V.preimage f).ι) := by
    rwa [range_pointsMap_preimage_ι]
  refine ⟨V.preimage f, hP, p, hp, ?_⟩
  have : IsIso (V.fromPreimage f) :=
    (isIso_pullback_snd_iff (Subfunctor.isPullback_preimage f V).flip).mp hiso
  have hopen : IsOpenImmersion B S hS ((V.preimage f).ι ≫ f) := by
    rw [← Subfunctor.fromPreimage_ι]
    exact MorphismProperty.RespectsIso.precomp _ (V.fromPreimage f) V.ι hV.2
  exact isLocallyQuasiFinite_of_isEtale B S hS hX
    (isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS hopen))

/-! ### Normality of a local ring as an étale-invariant property -/

/-- Normality of local rings is invariant under étale localization: this is
`AlgebraicGeometry.isNormalDomain_localizationAtPrime_iff_of_etale` in the shape
`AlgebraicGeometry.Space.HasLocalRingPropertyAtPoint` asks for. -/
theorem isNormalDomain_localization_etale_invariant :
    ∀ {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C]
      (p : Ideal A) [p.IsPrime] (q : Ideal C) [q.IsPrime],
      q.comap (algebraMap A C) = p →
        (IsNormalDomain (Localization.AtPrime p) ↔
          IsNormalDomain (Localization.AtPrime q)) := by
  intro A C _ _ _ _ p _ q _ hq
  exact isNormalDomain_localizationAtPrime_iff_of_etale p q hq

/-- **Stacks 0BBL, normal**, as a property of the local ring of an algebraic space over `S` at
a point: some étale scheme chart has a point above it whose stalk is a normal domain. -/
abbrev HasNormalLocalRingAtPoint (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) : Prop :=
  HasLocalRingPropertyAtPoint B S hS X hX x
    (fun (R : Type u) => fun [CommRing R] => IsNormalDomain R)
    isNormalDomain_localization_etale_invariant

/-! ### From finiteness over a neighbourhood to membership of the isomorphism locus -/

/-- **The inductive step of parts (2) and (3).** Let `f : Y ⟶ X` be a birational morphism with
`X` Noetherian and `Y` reduced, let `x ∈ |X|` have normal local ring, and suppose `f` is finite
over an open subspace `V ⊆ X` whose point set contains `x`. Then `x` lies in the point set of
the maximal open subspace over which `f` is an isomorphism.

An affine open neighbourhood inside the preimage of `|V|` in a normal étale chart through `x`
maps into `V`, so finiteness of `f` over `V` represents the base change of `f` along it by a
finite morphism of affine schemes, and
`AlgebraicGeometry.Space.mem_isomorphismLocus_of_finite_affine_chart` applies. -/
private theorem mem_isomorphismLocus_of_isFinite_over_neighbourhood
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hDY : IsDecentSpace B S hS Y) (hDX : IsDecentSpace B S hS X)
    (hCY : (irreducibleComponents (points B S hS Y)).Finite)
    (hCX : (irreducibleComponents (points B S hS X)).Finite)
    (f : Y ⟶ X) (hf : IsBirational B S hS hY hX hDY hDX hCY hCX f)
    (hN : HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hR : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsReduced Z))
    (U : Subfunctor X)
    (hU : IsGreatest {V : Subfunctor X | IsOpenSubspace B S hS V ∧
      IsIso (pullback.snd f V.ι)} U)
    (x : points B S hS X) (V : Subfunctor X) (hV : IsOpenSubspace B S hS V)
    (hxV : x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι))
    (hfin : IsFinite B S hS (pullback.snd f V.ι))
    (hNormal : HasNormalLocalRingAtPoint B S hS X hX x) :
    x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  classical
  obtain ⟨T, a, ha, p, hp, hn⟩ := hNormal
  let K := BigFppfOver.toScheme B S hS
  let t := schemePoint B S hS T p
  let e := (schemePointsHomeomorph B S hS T).symm
  have het : e t = p.class B S hS (yoneda.obj T) :=
    schemePointsHomeomorph_symm_schemePoint B S hS T p
  have hvopen := isOpen_range_pointsMap_ι B S hS hX V hV
  let D : (K.obj T).Opens :=
    ⟨(fun y => pointsMap B S hS (yoneda.obj T) a (e y)) ⁻¹'
        Set.range (pointsMap B S hS V.toFunctor V.ι),
      hvopen.preimage ((continuous_pointsMap B S hS a).comp e.continuous)⟩
  have htD : t ∈ D := by
    change pointsMap B S hS (yoneda.obj T) a (e t) ∈
      Set.range (pointsMap B S hS V.toFunctor V.ι)
    rwa [het, hp]
  obtain ⟨W, hWaff, htW, hWD⟩ := exists_isAffineOpen_mem_and_subset htD
  let A := openSiteObject B S hS T W
  let j := openSiteObjectHom B S hS T W
  have hjK : K.map j = W.ι := map_openSiteObjectHom B S hS T W
  have : IsAffine (K.obj A) := hWaff
  have hg := presheaf_etale_yoneda_map_openSiteObjectHom_comp B S hS W a ha
  obtain ⟨d, hd⟩ := (factorsThrough_openSubspace_iff_points B S hS hX
    (isAlgebraicSpace_yoneda B S hS A) V hV (yoneda.map j ≫ a)).mpr (by
      rintro _ ⟨z, rfl⟩
      rw [pointsMap_comp_apply, ← Homeomorph.symm_apply_apply (schemePointsHomeomorph B S hS A) z,
        ← schemePointsHomeomorph_symm_map]
      change K.map j (schemePointsHomeomorph B S hS A z) ∈ D
      rw [hjK]
      exact hWD (schemePointsHomeomorph B S hS A z).property)
  obtain ⟨C, q, i, -, hq, hs⟩ := hfin A inferInstance d
  have hs' : IsPullback (i ≫ pullback.fst f V.ι) (yoneda.map q) f (yoneda.map j ≫ a) := by
    simpa only [hd] using hs.paste_horiz (IsPullback.of_hasPullback f V.ι)
  have : AlgebraicGeometry.IsFinite (K.map q) := hq
  let t' : K.obj A := ⟨t, htW⟩
  obtain ⟨_, _⟩ : IsDomain ((K.obj A).presheaf.stalk t') ∧
      IsIntegrallyClosed ((K.obj A).presheaf.stalk t') :=
    isDomain_and_isIntegrallyClosed_stalk_of_isOpenImmersion W.ι t' hn
  have hmem := mem_isomorphismLocus_of_finite_affine_chart B S hS hY hX hDY hDX hCY hCX f hf
    hN hR A C (yoneda.map j ≫ a) hg q (i ≫ pullback.fst f V.ι) hs' t' U hU
  rw [pointsMap_comp_apply] at hmem
  have hpoint : pointsMap B S hS (yoneda.obj A) (yoneda.map j)
      ((schemePointsHomeomorph B S hS A).symm t') = p.class B S hS (yoneda.obj T) :=
    (schemePointsHomeomorph_symm_map B S hS j t').symm.trans het
  rwa [hpoint, hp] at hmem

/-! ### Stacks 0BBQ -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
  (hNoeth : IsNoetherian B S hS hZ X) (f : Y ⟶ X)
  (hBir : ∃ (hDY : IsDecentSpace B S hS Y) (hDX : IsDecentSpace B S hS X)
    (hCY : (irreducibleComponents (points B S hS Y)).Finite)
    (hCX : (irreducibleComponents (points B S hS X)).Finite),
    IsBirational B S hS hY hX hDY hDX hCY hCX f)
  (hProper : IsProper B S hS f)
  (hReduced : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsReduced Z))
  (U : Subfunctor X)
  (hU : IsGreatest {V : Subfunctor X | IsOpenSubspace B S hS V ∧
    IsIso (pullback.snd f V.ι)} U)

include hX hY hNoeth hBir hProper hReduced hU

omit hReduced in
/-- **Stacks 0BBQ, part (1).** Let `X` be a Noetherian algebraic space over `S` and let
`f : Y ⟶ X` be a proper birational morphism with `Y` reduced. The maximal open subspace `U` of
`X` over which `f` is an isomorphism contains every point of `|X|` of codimension `0`.

By Stacks 0BBF the morphism is an isomorphism over a *dense* open subspace `V ⊆ X`, which is
contained in `U` by maximality. A dense subset of the Noetherian point space `|X|` meets the
nonempty open part of every irreducible component, so it meets the component of the given
codimension-zero point, which is therefore in `V`. -/
@[stacks 0BBQ "part (1): every point of codimension zero"]
theorem mem_isomorphismLocus_of_localRingDimension_eq_zero
    (x : points B S hS X) (hx : localRingDimension B S hS x = 0) :
    x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  obtain ⟨hDY, hDX, hCY, hCX, hf⟩ := hBir
  have : NoetherianSpace (points B S hS X) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X hX hNoeth.1 hNoeth.2.2
  have hxg : x ∈ genericPoints (points B S hS X) :=
    ((mem_genericPoints_tfae B S hS hX hDX x).out 1 4).mpr hx
  obtain ⟨V, hV, hdense, hiso⟩ :=
    exists_isDenseOpenSubspace_isIso_pullback_snd_of_isBirational B S hS hY hX hDY hDX hCY hCX
      f hf (Or.inr hProper.1)
      (Or.inr (isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS hY hX f
        hNoeth.2.2 hProper.2.1.1))
  refine range_pointsMap_le B S hS (hU.2 ⟨hV, hiso⟩) ?_
  have hopen := isOpen_range_pointsMap_ι B S hS hX V hV
  refine ((genericPoints.isGenericPoint
    (⟨x, hxg⟩ : genericPoints (points B S hS X))).mem_open_set_iff hopen).2 ?_
  obtain ⟨W, hW, hWne, hWsub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hxg
  obtain ⟨z, hzW, hzV⟩ := hdense.inter_open_nonempty W hW hWne
  exact ⟨z, hWsub hzW, hzV⟩

/-- **Stacks 0BBQ, part (3).** With the hypotheses of part (1), the maximal open subspace over
which `f` is an isomorphism contains every point of `|X|` whose fibre in `|Y|` is finite and
whose local ring is normal.

Stacks 0A4W, applied through Stacks 0ACK to convert the finite set-theoretic fibre into a
finite geometric fibre, makes `f` finite over an open neighbourhood of the point, and
`AlgebraicGeometry.Space.mem_isomorphismLocus_of_isFinite_over_neighbourhood` concludes. -/
@[stacks 0BBQ "part (3): every point with finite fibre and normal local ring"]
theorem mem_isomorphismLocus_of_finite_fibre_of_normal
    (x : points B S hS X) (hfibre : ((pointsMap B S hS Y f) ⁻¹' {x}).Finite)
    (hNormal : HasNormalLocalRingAtPoint B S hS X hX x) :
    x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  obtain ⟨hDY, hDX, hCY, hCX, hf⟩ := hBir
  obtain ⟨V, hV, hxV, hfin⟩ := exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fibre
    B S hS hY hX hDY hDX f hProper x hfibre
  exact mem_isomorphismLocus_of_isFinite_over_neighbourhood B S hS hY hX hDY hDX hCY hCX f hf
    hNoeth.2.2 hReduced U hU x V hV hxV hfin hNormal

/-- **Stacks 0BBQ, part (2).** With the hypotheses of part (1), the maximal open subspace over
which `f` is an isomorphism contains every point of `|X|` of codimension `1` whose local ring
is normal.

Part (1) already puts the image of every codimension-zero point of `|Y|` in `U`, which makes
`f` quasi-finite there, so the third generic condition of Stacks 0AD2 holds and `f` is finite
over an open neighbourhood of the given point; part (3)'s argument then concludes. -/
@[stacks 0BBQ "part (2): every point of codimension one with normal local ring"]
theorem mem_isomorphismLocus_of_localRingDimension_eq_one_of_normal
    (x : points B S hS X) (hx : localRingDimension B S hS x = 1)
    (hNormal : HasNormalLocalRingAtPoint B S hS X hX x) :
    x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  obtain ⟨hDY, hDX, hCY, hCX, hf⟩ := hBir
  have hqf : ∀ y : points B S hS Y, localRingDimension B S hS y = 0 →
      IsQuasiFiniteAt B S hS f y := by
    intro y hy
    have hyg := ((mem_genericPoints_tfae B S hS hY hDY y).out 1 4).mpr hy
    have hxg := (hf.bijOn B S hS hY hX hDY hDX hCY hCX).mapsTo hyg
    have hdim := ((mem_genericPoints_tfae B S hS hX hDX
      (pointsMap B S hS Y f y)).out 1 4).mp hxg
    exact isQuasiFiniteAt_of_mem_isomorphismLocus B S hS hY hX f U hU.1.1 hU.1.2 y
      (mem_isomorphismLocus_of_localRingDimension_eq_zero B S hS hZ hX hY hNoeth f
        ⟨hDY, hDX, hCY, hCX, hf⟩ hProper U hU _ hdim)
  obtain ⟨V, hV, hxV, hfin⟩ :=
    exists_isOpenSubspace_isFinite_pullback_snd_of_localRingDimension_le_one B S hS hY hX f
      hProper hNoeth.2.2 x hx.le (Or.inr (Or.inr (Or.inl hqf)))
  exact mem_isomorphismLocus_of_isFinite_over_neighbourhood B S hS hY hX hDY hDX hCY hCX f hf
    hNoeth.2.2 hReduced U hU x V hV hxV hfin hNormal

end AlgebraicGeometry.Space

end
