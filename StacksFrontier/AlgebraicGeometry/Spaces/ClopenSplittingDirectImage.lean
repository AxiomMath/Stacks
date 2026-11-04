module

public import StacksFrontier.AlgebraicGeometry.ClopenModules.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCoversTopOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# Direct images along a decomposition of an algebraic space into two open and closed pieces

Let `V` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`a : W ⟶ V` and `a' : W' ⟶ V` present `V` as the disjoint union of two open and closed pieces:
each of `a`, `a'` is étale and a closed immersion, their images on points are disjoint, and
together those images are all of `|V|`.  Then every `𝒪_V`-module `F` is the biproduct of the
direct images of its restrictions to the two pieces,

`F ≅ a_*(a^*F) ⊞ a'_*(a'^*F)`,

the comparison being the pair of units of the two adjunctions `a^* ⊣ a_*`, `a'^* ⊣ a'_*` of
Stacks 03LU.  Pushing that forward along any `q : V ⟶ Z` and composing direct images gives the
decomposition of a direct image along the splitting,

`q_*F ≅ (a ≫ q)_*(a^*F) ⊞ (a' ≫ q)_*(a'^*F)`,

and the form needed when the splitting is a splitting of a base change `U ×_X Y` along an étale
`u : U ⟶ X` is obtained from this by the base change of Stacks 03LX:

`(π_*G)|_U ≅ (a ≫ p)_*(G|_W) ⊞ (a' ≫ p)_*(G|_{W'})`,

where `p : U ×_X Y ⟶ U` is the projection and `W`, `W'` are the two pieces of `U ×_X Y`.

This is the module-theoretic counterpart of the open-and-closed decompositions produced by
Stacks 082H and Stacks 0ADU, whose conclusion `U ×_Y X = W ⨿ V` is a decomposition of the
*space*; nothing is added here about where such a decomposition comes from.

## Main results

* `AlgebraicGeometry.Space.isZero_modulePullback_modulePushforward_of_disjoint`: the restriction
  to one piece of the direct image from the other piece vanishes.
* `AlgebraicGeometry.Space.isIso_of_isIso_modulePullback_of_union_range_eq_univ`: a morphism of
  `𝒪_V`-modules whose restrictions to two étale pieces jointly covering `|V|` are isomorphisms
  is an isomorphism.
* `AlgebraicGeometry.Space.isIso_biprod_lift_unit_of_clopen`: the pair of units
  `F ⟶ a_*(a^*F) ⊞ a'_*(a'^*F)` is an isomorphism.
* `AlgebraicGeometry.Space.modulePushforwardBiprodIsoOfClopen`: the resulting decomposition of a
  direct image `q_*F` along the splitting.
* `AlgebraicGeometry.Space.modulePushforwardBaseChangeBiprodIsoOfClopen`: the same
  decomposition for the restriction to an étale `u : U ⟶ X` of a direct image along `π : Y ⟶ X`,
  split along a decomposition of the base change `U ×_X Y`.

## Implementation notes

The three inputs are the counit identity of Stacks 04CJ, part (2), the base change of Stacks
03LX, and the étale locality of isomorphisms of modules.

* Invertibility of `a^*(unit)` is the left triangle identity of the adjunction together with
  invertibility of the counit, which for a closed immersion is
  `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit`.  It is used through
  `AlgebraicGeometry.Space.modulePullback`, the inverse image of Stacks 03LU, rather than
  through `AlgebraicGeometry.Space.etaleModulePullback`; the two are identified by
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which is what lets the base
  change isomorphism, stated for the latter, be used alongside it.
* The vanishing `a'^*(a_*G) = 0` is Stacks 03LX for the cartesian square with corners
  `W ×_V W'`, `W`, `W'`, `V`: it identifies `a'^*(a_*G)` with a direct image from `W ×_V W'`,
  and that space has no points, so the empty family of charts covers its small étale site and
  every module on it is zero.
* Étale locality is
  `AlgebraicGeometry.Space.isIso_of_isIso_modulePullback_chartToSpace`, applied to the two-member
  family of charts obtained from scheme atlases of `W` and of `W'`.  A chart of `W` composed with
  `a` is a chart of `V` whose structure morphism factors through `a`, and the inverse image along
  a factored morphism is the composite of the two inverse images
  (`AlgebraicGeometry.Space.modulePullbackCompIso`).  The factorisation is stated as an equation
  `b ≫ g = chartToSpace V c` between morphisms with a common source, so that no identification of
  categories of modules over the two chart spaces is ever asked of the elaborator; that is what
  keeps the step cheap.

The hypotheses on `a` are `IsEtale` and `IsClosedImmersion`, which is what the inclusion of an
open and closed subspace satisfies; openness enters only through étaleness.  No representability
hypothesis is needed, the direct and inverse images of Stacks 03LU existing for an arbitrary
morphism of algebraic spaces.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W W' : AlgebraicSpaces B S hS} (a : W ⟶ V) (a' : W' ⟶ V)

/-- **The restriction to one piece of a direct image from a disjoint piece vanishes.**  If the
images on points of `a : W ⟶ V` and of an étale `a' : W' ⟶ V` are disjoint, then
`a'^*(a_*G) = 0` for every `𝒪_W`-module `G`.

By the base change of Stacks 03LX for the cartesian square with corners `W ×_V W'`, `W`, `W'`,
`V`, the module `a'^*(a_*G)` is a direct image from `W ×_V W'`.  A point of `W ×_V W'` would give
a point of `|V|` in both images, so `W ×_V W'` has no points; the empty family of charts
therefore covers its small étale site, every module on it is zero, and a direct image of a zero
module is zero. -/
theorem isZero_modulePullback_modulePushforward_of_disjoint
    (ha' : IsEtale B S hS a'.hom)
    (hdisj : Disjoint (Set.range (pointsMap B S hS W.1 a.hom))
      (Set.range (pointsMap B S hS W'.1 a'.hom)))
    (G : Modules.{u, u} B S hS W.1 W.2) :
    IsZero ((modulePullback B S hS a').obj ((modulePushforward B S hS a).obj G)) := by
  set P := AlgebraicSpaces.fiberProduct B S hS a a'
  set i : P ⟶ W := ObjectProperty.homMk (pullback.fst a.hom a'.hom)
  set j : P ⟶ W' := ObjectProperty.homMk (pullback.snd a.hom a'.hom)
  have sq : IsPullback i j a a' := AlgebraicSpaces.isPullback_fiberProduct B S hS a a'
  have hw : i.hom ≫ a.hom = j.hom ≫ a'.hom := congrArg (fun k => k.hom) sq.w
  have hP : IsEmpty (points B S hS P.1) := by
    refine ⟨fun p => ?_⟩
    have hpt : pointsMap B S hS W.1 a.hom (pointsMap B S hS P.1 i.hom p) =
        pointsMap B S hS W'.1 a'.hom (pointsMap B S hS P.1 j.hom p) := by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hw]
    exact Set.disjoint_left.1 hdisj ⟨_, rfl⟩ ⟨_, hpt.symm⟩
  have hzero : ∀ M : Modules.{u, u} B S hS P.1 P.2, IsZero M := fun M =>
    isZero_of_isZero_modulePullback_chartToSpace B S hS
      (SmallEtale.coversTop_of_iUnion_range_eq_univ B S hS P
        (Empty.elim : Empty → SmallEtale B S hS P.1)
        (by rw [Set.iUnion_of_empty]; exact (Set.univ_eq_empty_iff.2 hP).symm)) M
      (fun e => e.elim)
  have := modulePushforward_additive B S hS j
  refine IsZero.of_iso ?_ (((modulePullbackIsoEtaleModulePullback B S hS a' ha').app _).trans
    ((modulePushforwardEtaleBaseChangeIso B S hS i j a a' sq ha').app G).symm)
  exact Functor.map_isZero (modulePushforward B S hS j) (hzero _)

/-- **Isomorphisms of modules are detected on two étale pieces covering the space.**  If
`a : W ⟶ V` and `a' : W' ⟶ V` are étale and their images on points are all of `|V|`, then a
morphism of `𝒪_V`-modules whose inverse images along `a` and along `a'` are isomorphisms is an
isomorphism.

A scheme atlas of `W` composed with `a` is an étale chart of `V` whose structure morphism
factors through `a` as the atlas followed by `a`, so the inverse image along that chart of `V` is
the inverse image along `a` followed by the inverse image along the atlas
(`AlgebraicGeometry.Space.modulePullbackCompIso`).  The two charts so obtained cover `|V|`
because an atlas is surjective on points, and isomorphisms are étale local
(`AlgebraicGeometry.Space.isIso_of_isIso_modulePullback_chartToSpace`). -/
theorem isIso_of_isIso_modulePullback_of_union_range_eq_univ
    (ha : IsEtale B S hS a.hom) (ha' : IsEtale B S hS a'.hom)
    (hcov : Set.range (pointsMap B S hS W.1 a.hom) ∪
      Set.range (pointsMap B S hS W'.1 a'.hom) = Set.univ)
    {M N : Modules.{u, u} B S hS V.1 V.2} (φ : M ⟶ N)
    (h : IsIso ((modulePullback B S hS a).map φ))
    (h' : IsIso ((modulePullback B S hS a').map φ)) :
    IsIso φ := by
  have piece : ∀ {X : AlgebraicSpaces B S hS} (g : X ⟶ V), IsEtale B S hS g.hom →
      IsIso ((modulePullback B S hS g).map φ) → ∃ c : SmallEtale B S hS V.1,
        Set.range (pointsMap B S hS (chartSpace B S hS V c).1
          (chartToSpace B S hS V c).hom) = Set.range (pointsMap B S hS X.1 g.hom) ∧
        IsIso ((modulePullback B S hS (chartToSpace B S hS V c)).map φ) := by
    intro X g hg hgi
    obtain ⟨T, t, hts, hte⟩ := X.2.exists_atlas
    have ht : IsEtale B S hS t := (isEtale_iff_presheaf_of_yoneda B S hS t).2 hte
    have hA := (isEtale_iff_presheaf_of_yoneda B S hS (t ≫ g.hom)).1 (isEtale_comp B S hS ht hg)
    have hsurj := surjective_pointsMap_of_presheaf_surjective B S hS t hts
    refine ⟨⟨CostructuredArrow.mk (t ≫ g.hom), hA⟩, ?_, ?_⟩
    · refine Set.Subset.antisymm ?_ ?_
      · rintro x ⟨w, rfl⟩
        exact ⟨_, (pointsMap_comp_apply B S hS t g.hom w).symm⟩
      · rintro x ⟨y, rfl⟩
        obtain ⟨w, rfl⟩ := hsurj y
        exact ⟨w, pointsMap_comp_apply B S hS t g.hom w⟩
    · have hb : chartToSpace B S hS X (⟨CostructuredArrow.mk t, hte⟩ : SmallEtale B S hS X.1) ≫ g =
          chartToSpace B S hS V (⟨CostructuredArrow.mk (t ≫ g.hom), hA⟩ : SmallEtale B S hS V.1) :=
        ObjectProperty.hom_ext _ rfl
      rw [← hb]
      exact (NatIso.isIso_map_iff (modulePullbackCompIso B S hS _ g) φ).1
        (inferInstanceAs (IsIso ((modulePullback B S hS _).map
          ((modulePullback B S hS g).map φ))))
  obtain ⟨c, hc, hic⟩ := piece a ha h
  obtain ⟨c', hc', hic'⟩ := piece a' ha' h'
  refine isIso_of_isIso_modulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_of_iUnion_range_eq_univ B S hS V (fun b : Bool => cond b c c') ?_) φ ?_
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases (Set.eq_univ_iff_forall.1 hcov x) with hx | hx
    · exact Set.mem_iUnion.2 ⟨true, (hc.symm.subset hx : _)⟩
    · exact Set.mem_iUnion.2 ⟨false, (hc'.symm.subset hx : _)⟩
  · intro b
    cases b
    · dsimp only [cond]
      exact hic'
    · dsimp only [cond]
      exact hic

/-- **A module on an algebraic space split into two open and closed pieces is the biproduct of
the direct images of its restrictions to the pieces.**  For `a : W ⟶ V` and `a' : W' ⟶ V` étale
closed immersions with disjoint images on points covering `|V|`, the map
`F ⟶ a_*(a^*F) ⊞ a'_*(a'^*F)` whose components are the units of the two adjunctions of
Stacks 03LU is an isomorphism.

It is checked after restriction to each piece, where one component is the restricted unit — an
isomorphism, by the left triangle identity and the invertibility of the counit of Stacks 04CJ,
part (2) — and the other lands in zero. -/
theorem isIso_biprod_lift_unit_of_clopen
    (ha : IsEtale B S hS a.hom) (ha' : IsEtale B S hS a'.hom)
    (hca : IsClosedImmersion B S hS a.hom) (hca' : IsClosedImmersion B S hS a'.hom)
    (hcov : Set.range (pointsMap B S hS W.1 a.hom) ∪
      Set.range (pointsMap B S hS W'.1 a'.hom) = Set.univ)
    (hdisj : Disjoint (Set.range (pointsMap B S hS W.1 a.hom))
      (Set.range (pointsMap B S hS W'.1 a'.hom)))
    (F : Modules.{u, u} B S hS V.1 V.2) :
    IsIso (biprod.lift ((modulePullbackAdjunction B S hS a).unit.app F)
      ((modulePullbackAdjunction B S hS a').unit.app F)) := by
  have hunit : ∀ {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
      (hg : IsClosedImmersion B S hS g.hom) (M : Modules.{u, u} B S hS Y.1 Y.2),
      IsIso ((modulePullback B S hS g).map ((modulePullbackAdjunction B S hS g).unit.app M)) := by
    intro X Y g hg M
    have := isIso_modulePullbackAdjunction_counit B S hS g hg ((modulePullback B S hS g).obj M)
    have htri := (modulePullbackAdjunction B S hS g).left_triangle_components M
    have : IsIso ((modulePullback B S hS g).map
        ((modulePullbackAdjunction B S hS g).unit.app M) ≫
        (modulePullbackAdjunction B S hS g).counit.app ((modulePullback B S hS g).obj M)) := by
      rw [htri]; infer_instance
    exact IsIso.of_isIso_comp_right _
      ((modulePullbackAdjunction B S hS g).counit.app ((modulePullback B S hS g).obj M))
  have := (modulePullbackAdjunction B S hS a).isLeftAdjoint
  have := (modulePullbackAdjunction B S hS a').isLeftAdjoint
  have : PreservesBinaryBiproducts (modulePullback B S hS a) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : PreservesBinaryBiproducts (modulePullback B S hS a') :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  refine isIso_of_isIso_modulePullback_of_union_range_eq_univ B S hS a a' ha ha' hcov _ ?_ ?_
  · rw [← isIso_comp_right_iff _ ((modulePullback B S hS a).mapBiprod _ _).hom,
      biprod.map_lift_mapBiprod]
    have := hunit a hca F
    exact Scheme.Modules.isIso_biprod_lift_of_isZero_right _ _
      (isZero_modulePullback_modulePushforward_of_disjoint B S hS a' a ha hdisj.symm _)
  · rw [← isIso_comp_right_iff _ ((modulePullback B S hS a').mapBiprod _ _).hom,
      biprod.map_lift_mapBiprod]
    have := hunit a' hca' F
    exact Scheme.Modules.isIso_biprod_lift_of_isZero_left _ _
      (isZero_modulePullback_modulePushforward_of_disjoint B S hS a a' ha' hdisj _)

/-- **The decomposition of a direct image along a splitting of its source into two open and
closed pieces.**  For `a : W ⟶ V`, `a' : W' ⟶ V` étale closed immersions with disjoint images on
points covering `|V|` and any `q : V ⟶ Z`,

`q_*F ≅ (a ≫ q)_*(a^*F) ⊞ (a' ≫ q)_*(a'^*F)`.

This is `AlgebraicGeometry.Space.isIso_biprod_lift_unit_of_clopen` pushed forward along `q`,
which is additive, followed by the comparison of direct images of a composite of Stacks 03LU. -/
def modulePushforwardBiprodIsoOfClopen {Z : AlgebraicSpaces B S hS} (q : V ⟶ Z)
    (ha : IsEtale B S hS a.hom) (ha' : IsEtale B S hS a'.hom)
    (hca : IsClosedImmersion B S hS a.hom) (hca' : IsClosedImmersion B S hS a'.hom)
    (hcov : Set.range (pointsMap B S hS W.1 a.hom) ∪
      Set.range (pointsMap B S hS W'.1 a'.hom) = Set.univ)
    (hdisj : Disjoint (Set.range (pointsMap B S hS W.1 a.hom))
      (Set.range (pointsMap B S hS W'.1 a'.hom)))
    (F : Modules.{u, u} B S hS V.1 V.2) :
    (modulePushforward B S hS q).obj F ≅
      (modulePushforward B S hS (a ≫ q)).obj ((modulePullback B S hS a).obj F) ⊞
        (modulePushforward B S hS (a' ≫ q)).obj ((modulePullback B S hS a').obj F) :=
  have := isIso_biprod_lift_unit_of_clopen B S hS a a' ha ha' hca hca' hcov hdisj F
  have := modulePushforward_additive B S hS q
  have : PreservesBinaryBiproducts (modulePushforward B S hS q) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  (modulePushforward B S hS q).mapIso
      (asIso (biprod.lift ((modulePullbackAdjunction B S hS a).unit.app F)
        ((modulePullbackAdjunction B S hS a').unit.app F))) ≪≫
    (modulePushforward B S hS q).mapBiprod _ _ ≪≫
    biprod.mapIso ((modulePushforwardCompIso B S hS a q).app _)
      ((modulePushforwardCompIso B S hS a' q).app _)

/-- **The decomposition of the restriction to an étale chart of a direct image, along a splitting
of the base change.**  Let `π : Y ⟶ X` be a morphism of algebraic spaces, let `u : U ⟶ X` be
étale, and let

```
V --iV--> Y
|pV       |π
U --u-->  X
```

be cartesian, so that `V` is the base change `U ×_X Y` with projection `pV`.  If `V` is split by
`a : W ⟶ V` and `a' : W' ⟶ V` into two open and closed pieces, then for every `𝒪_Y`-module `G`

`(π_*G)|_U ≅ (a ≫ pV)_*(G|_W) ⊞ (a' ≫ pV)_*(G|_{W'})`.

The base change of Stacks 03LX identifies `(π_*G)|_U` with `(pV)_*(G|_V)`, to which
`AlgebraicGeometry.Space.modulePushforwardBiprodIsoOfClopen` applies; the restrictions of `G|_V`
to the two pieces are then its restrictions along `a ≫ iV` and `a' ≫ iV` by the comparison of
inverse images of a composite of Stacks 03LU. -/
def modulePushforwardBaseChangeBiprodIsoOfClopen {X Y U : AlgebraicSpaces B S hS} (π : Y ⟶ X)
    (u : U ⟶ X) (hu : IsEtale B S hS u.hom) (iV : V ⟶ Y) (pV : V ⟶ U)
    (sqV : IsPullback iV pV π u)
    (ha : IsEtale B S hS a.hom) (ha' : IsEtale B S hS a'.hom)
    (hca : IsClosedImmersion B S hS a.hom) (hca' : IsClosedImmersion B S hS a'.hom)
    (hcov : Set.range (pointsMap B S hS W.1 a.hom) ∪
      Set.range (pointsMap B S hS W'.1 a'.hom) = Set.univ)
    (hdisj : Disjoint (Set.range (pointsMap B S hS W.1 a.hom))
      (Set.range (pointsMap B S hS W'.1 a'.hom)))
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS u).obj ((modulePushforward B S hS π).obj G) ≅
      (modulePushforward B S hS (a ≫ pV)).obj ((modulePullback B S hS (a ≫ iV)).obj G) ⊞
        (modulePushforward B S hS (a' ≫ pV)).obj
          ((modulePullback B S hS (a' ≫ iV)).obj G) :=
  have hiV : IsEtale B S hS iV.hom := isEtale_of_isPullback B S hS pV iV u π sqV.flip hu
  ((modulePullbackIsoEtaleModulePullback B S hS u hu).app _) ≪≫
    ((modulePushforwardEtaleBaseChangeIso B S hS iV pV π u sqV hu).app G).symm ≪≫
    modulePushforwardBiprodIsoOfClopen B S hS a a' pV ha ha' hca hca' hcov hdisj
      ((etaleModulePullback B S hS iV hiV).obj G) ≪≫
    biprod.mapIso
      ((modulePushforward B S hS (a ≫ pV)).mapIso
        ((modulePullback B S hS a).mapIso
            ((modulePullbackIsoEtaleModulePullback B S hS iV hiV).app G).symm ≪≫
          (modulePullbackCompIso B S hS a iV).app G))
      ((modulePushforward B S hS (a' ≫ pV)).mapIso
        ((modulePullback B S hS a').mapIso
            ((modulePullbackIsoEtaleModulePullback B S hS iV hiV).app G).symm ≪≫
          (modulePullbackCompIso B S hS a' iV).app G))

end AlgebraicGeometry.Space

end
