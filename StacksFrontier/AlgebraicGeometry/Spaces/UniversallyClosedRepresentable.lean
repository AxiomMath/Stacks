module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.UniversallyClosedCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Universal closedness of a representable morphism of algebraic spaces (Stacks 03XD)

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is universally closed in the sense of
**Stacks 03HI** — every base change of it by an algebraic space over `S` is closed on points —
exactly when every represented base change of it is a universally closed morphism of schemes in
the sense of Mathlib.

## Main results

* `AlgebraicGeometry.Space.presheaf_universallyClosed_of_universallyClosed`: the implication
  from the point-set condition, which needs no algebraic space hypothesis at all.
* `AlgebraicGeometry.Space.universallyClosed_of_presheaf_universallyClosed`: the converse.
* `AlgebraicGeometry.Space.presheaf_universallyClosed_iff`: **Stacks 03XD**.
* `AlgebraicGeometry.Space.universallyClosed_yoneda_map`: the represented reading of Stacks 03XD
  — a universally closed morphism of schemes of the site represents a universally closed
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isClosedMap_of_isOpenMap_family_cartesian` and its one-member case
  `AlgebraicGeometry.Space.isClosedMap_of_isOpenMap_surjective_cartesian`: the point-set
  descent of closedness along an open covering family of squares cartesian on underlying sets,
  which is what every test for universal closedness of a morphism of algebraic spaces rests on.

## Implementation notes

The two directions are of quite different weight.

*From the point-set condition.* Given a represented base change `snd` of `f`, taking the
hypothesis at the representable algebraic space in question and translating along the
identification of the points of a represented presheaf with the points of the representing
scheme (`AlgebraicGeometry.Space.isClosedMap_map_relativelyRepresentable_snd`) shows that the
morphism of schemes underlying `snd` is a closed map. The same argument applied to the base
change of `snd` along any morphism *from a scheme inside `B`* shows that all those base changes
are closed maps. That is weaker than Mathlib's `AlgebraicGeometry.UniversallyClosed`, which
quantifies over all schemes; the gap is closed by
`AlgebraicGeometry.universallyClosed_of_bounded_closed_baseChanges`, and that is the whole
mathematical content of this direction.

*To the point-set condition.* Let `Z` be an algebraic space over `S` with `g : Z ⟶ Y`, and let
`C = Z ×_Y X`. Choose a surjective étale atlas `a : h_U ⟶ Z` and put `D = h_U ×_Z C`. By
**Stacks 03BX** (3) and **Stacks 03H5** the map on points induced by `a` is open and
surjective, and by **Stacks 03H4** the square of point sets is cartesian in the set-theoretic
sense. In that situation closedness of `D ⟶ h_U` forces closedness of `C ⟶ Z`, which is
`isClosedMap_of_isOpenMap_surjective_cartesian`. And `D ⟶ h_U` is, up to the associativity
isomorphism of fibre products, the base change of `f` along `a ≫ g`, which is represented; so
its closedness on points is the hypothesis read through the same identification of points.

## References

* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Descent of closedness along an open covering family -/

/-- A map `q : A → C` of topological spaces is closed as soon as it is covered by a family of
commuting squares
```
D i --p i--> A
 |           |
r i          q
 |           |
 v           v
V i --v i--> C
```
which are cartesian on underlying sets, whose right-hand edges `v i` are open maps whose images
cover `C`, and whose bottom edges `r i` are closed.

The complement of `q '' s` is the union over `i` of `v i '' (r i '' (p i ⁻¹' s))ᶜ`: a point
outside `q '' s` has a preimage under some `v i`, which is outside `r i '' (p i ⁻¹' s)` by
commutativity, and conversely such a point cannot be in `q '' s` by cartesianity. Each member
of the union is open because `r i` is closed and `v i` is an open map. -/
theorem isClosedMap_of_isOpenMap_family_cartesian
    {A C : Type*} [TopologicalSpace A] [TopologicalSpace C] {I : Type*}
    {D : I → Type*} {V : I → Type*} [∀ i, TopologicalSpace (D i)]
    [∀ i, TopologicalSpace (V i)] (q : A → C) (p : ∀ i, D i → A) (r : ∀ i, D i → V i)
    (v : ∀ i, V i → C) (hcomm : ∀ i d, q (p i d) = v i (r i d))
    (hcart : ∀ i (a : A) (w : V i), q a = v i w → ∃ d, p i d = a ∧ r i d = w)
    (hp : ∀ i, Continuous (p i)) (hv : ∀ i, IsOpenMap (v i))
    (hcover : ∀ c, ∃ i w, v i w = c) (hr : ∀ i, IsClosedMap (r i)) :
    IsClosedMap q := by
  intro s hs
  rw [← isOpen_compl_iff]
  have hcompl : (q '' s)ᶜ = ⋃ i, v i '' (r i '' (p i ⁻¹' s))ᶜ := by
    refine Set.eq_of_subset_of_subset (fun c hc ↦ ?_) (fun c hc ↦ ?_)
    · obtain ⟨i, w, hwc⟩ := hcover c
      refine Set.mem_iUnion.2 ⟨i, w, ?_, hwc⟩
      rintro ⟨d, hd, hrd⟩
      exact hc ⟨p i d, hd, by rw [hcomm i d, hrd, hwc]⟩
    · obtain ⟨i, w, hw, hwc⟩ := Set.mem_iUnion.1 hc
      rintro ⟨a, ha, hqa⟩
      obtain ⟨d, hpd, hrd⟩ := hcart i a w (hqa.trans hwc.symm)
      exact hw ⟨d, by rwa [Set.mem_preimage, hpd], hrd⟩
  rw [hcompl]
  exact isOpen_iUnion fun i ↦ hv i _ (hr i _ (hs.preimage (hp i))).isOpen_compl

/-- The one-member case of `isClosedMap_of_isOpenMap_family_cartesian`: a map `q` sitting in a
commuting square, cartesian on underlying sets, whose right-hand edge is an open surjection and
whose bottom edge is closed, is closed. -/
theorem isClosedMap_of_isOpenMap_surjective_cartesian
    {A C D V : Type*} [TopologicalSpace A] [TopologicalSpace C] [TopologicalSpace D]
    [TopologicalSpace V] (q : A → C) (p : D → A) (r : D → V) (v : V → C)
    (hcomm : ∀ d, q (p d) = v (r d))
    (hcart : ∀ (a : A) (w : V), q a = v w → ∃ d, p d = a ∧ r d = w)
    (hp : Continuous p) (hv : IsOpenMap v) (hvs : Function.Surjective v)
    (hr : IsClosedMap r) : IsClosedMap q :=
  isClosedMap_of_isOpenMap_family_cartesian (I := PUnit.{1}) q (fun _ ↦ p) (fun _ ↦ r)
    (fun _ ↦ v) (fun _ ↦ hcomm) (fun _ ↦ hcart) (fun _ ↦ hp) (fun _ ↦ hv)
    (fun c ↦ ⟨PUnit.unit, hvs c⟩) (fun _ ↦ hr)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03XD**, the implication from the point-set condition. If every base change of a
representable morphism `f` of presheaves by an algebraic space over `S` is closed on points,
then every represented base change of `f` is a universally closed morphism of schemes.

No algebraicity hypothesis on the source or the target is needed: the hypothesis is only ever
used at represented presheaves, which are algebraic spaces. -/
theorem presheaf_universallyClosed_of_universallyClosed {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : UniversallyClosed B S hS f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  refine ⟨hf, fun U V g fst snd sq ↦ ?_⟩
  let T := BigFppfOver.toScheme B S hS
  -- every base change of `T.map snd` along a scheme inside the site is a closed map
  have hclosedBounded : ∀ (W : Scheme.{u}) (_ : B.Contains W) (k : W ⟶ T.obj U),
      IsClosedMap (pullback.snd (T.map snd) k) := by
    intro W hW k
    let k' : B.inclusion.obj (B.obj hW) ⟶ B.inclusion.obj U.left := k
    let kSite : B.obj hW ⟶ U.left := B.inclusion.preimage k'
    let Wov : BigFppfOver B S hS := Over.mk (kSite ≫ U.hom)
    let kOver : Wov ⟶ U := Over.homMk kSite
    have hk : T.map kOver = k := B.inclusion.map_preimage k'
    rw [← hk]
    -- the base change of `f` along `kOver ≫ g` is represented, and closed by hypothesis
    have hR := isClosedMap_map_relativelyRepresentable_snd B S hS hf (yoneda.map kOver ≫ g)
      (h _ (isAlgebraicSpace_yoneda B S hS Wov) _)
    -- it is the base change of `T.map snd` along `T.map kOver`
    let lNat : yoneda.obj (hf.pullback (yoneda.map kOver ≫ g)) ⟶ yoneda.obj V :=
      sq.lift (hf.fst (yoneda.map kOver ≫ g))
        (yoneda.map (hf.snd (yoneda.map kOver ≫ g)) ≫ yoneda.map kOver)
        (by simpa using (hf.isPullback (yoneda.map kOver ≫ g)).w)
    have hpaste : IsPullback (lNat ≫ fst)
        (yoneda.map (hf.snd (yoneda.map kOver ≫ g))) f (yoneda.map kOver ≫ g) := by
      rw [show lNat ≫ fst = hf.fst (yoneda.map kOver ≫ g) by simp [lNat]]
      exact hf.isPullback (yoneda.map kOver ≫ g)
    have hpbOver : IsPullback (yoneda.preimage lNat)
        (hf.snd (yoneda.map kOver ≫ g)) snd kOver := by
      apply IsPullback.of_map_of_faithful (F := yoneda)
      simpa using (IsPullback.paste_horiz_iff sq (by simp [lNat])).mp hpaste
    have hpbScheme : IsPullback (T.map (yoneda.preimage lNat))
        (T.map (hf.snd (yoneda.map kOver ≫ g))) (T.map snd) (T.map kOver) := hpbOver.map T
    rw [← hpbScheme.isoIsPullback_inv_snd _ _
      (IsPullback.of_hasPullback (T.map snd) (T.map kOver))]
    exact hR.comp (Scheme.Hom.isClosedMap _)
  exact universallyClosed_of_bounded_closed_baseChanges B (T.map snd)
    V.left.property U.left.property hclosedBounded

/-- **Stacks 03XD**, the implication to the point-set condition. If every represented base
change of a representable morphism of algebraic spaces over `S` is a universally closed
morphism of schemes, then every base change of it by an algebraic space over `S` is closed on
points. -/
theorem universallyClosed_of_presheaf_universallyClosed
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    UniversallyClosed B S hS f := by
  intro Z hZ g
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, a, haSurj, haEtale⟩ := hZ.exists_atlas
  have hC : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hZ hX hY
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hD : IsAlgebraicSpace B S hS (pullback a (pullback.fst g f)) :=
    isAlgebraicSpace_pullback B S hS a (pullback.fst g f) hU hC hZ
  -- the square of point sets is cartesian
  have hcart : ∀ (c : points B S hS (pullback g f)) (z : points B S hS (yoneda.obj U)),
      pointsMap B S hS (pullback g f) (pullback.fst g f) c =
        pointsMap B S hS (yoneda.obj U) a z →
      ∃ d : points B S hS (pullback a (pullback.fst g f)),
        pointsMap B S hS _ (pullback.snd a (pullback.fst g f)) d = c ∧
          pointsMap B S hS _ (pullback.fst a (pullback.fst g f)) d = z := by
    intro c z hcz
    have sq' : IsPullback
        (ObjectProperty.homMk (pullback.fst a (pullback.fst g f)) :
          (⟨_, hD⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hU⟩)
        (ObjectProperty.homMk (pullback.snd a (pullback.fst g f)) :
          (⟨_, hD⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hC⟩)
        (ObjectProperty.homMk a : (⟨_, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
        (ObjectProperty.homMk (pullback.fst g f) :
          (⟨_, hC⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) (IsPullback.of_hasPullback _ _)
    obtain ⟨d, hdu, hdc⟩ := exists_point_of_isPullback B S hS sq' z c hcz.symm
    exact ⟨d, hdc, hdu⟩
  -- the left-hand edge of the square is closed, being a represented base change of `f`
  have hQclosed : IsClosedMap
      (pointsMap B S hS (yoneda.obj (hf.pullback (a ≫ g)))
        (yoneda.map (hf.snd (a ≫ g)))) := by
    refine (isClosedMap_pointsMap_yoneda_iff B S hS (hf.snd (a ≫ g))).2 ?_
    have : AlgebraicGeometry.UniversallyClosed (T.map (hf.snd (a ≫ g))) :=
      h.property_snd (a ≫ g)
    exact (T.map (hf.snd (a ≫ g))).isClosedMap
  let e : pullback a (pullback.fst g f) ≅ yoneda.obj (hf.pullback (a ≫ g)) :=
    pullbackRightPullbackFstIso g f a ≪≫
      ((hf.isPullback (a ≫ g)).isoPullback ≪≫ pullbackSymmetry f (a ≫ g)).symm
  have he : e.hom ≫ yoneda.map (hf.snd (a ≫ g)) = pullback.fst a (pullback.fst g f) := by
    simpa only [e, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
      pullbackSymmetry_inv_comp_snd, IsPullback.isoPullback_inv_snd] using
      pullbackRightPullbackFstIso_hom_fst g f a
  have hdClosed : IsClosedMap
      (pointsMap B S hS (pullback a (pullback.fst g f))
        (pullback.fst a (pullback.fst g f))) := by
    rw [← he, pointsMap_comp]
    exact hQclosed.comp (pointsHomeomorphOfIso B S hS e).isClosedMap
  have hcomm : pointsMap B S hS (yoneda.obj U) a ∘
      pointsMap B S hS (pullback a (pullback.fst g f))
        (pullback.fst a (pullback.fst g f)) =
      pointsMap B S hS (pullback g f) (pullback.fst g f) ∘
        pointsMap B S hS (pullback a (pullback.fst g f))
          (pullback.snd a (pullback.fst g f)) := by
    rw [← pointsMap_comp, ← pointsMap_comp, pullback.condition]
  exact isClosedMap_of_isOpenMap_surjective_cartesian
    (pointsMap B S hS (pullback g f) (pullback.fst g f))
    (pointsMap B S hS (pullback a (pullback.fst g f))
      (pullback.snd a (pullback.fst g f)))
    (pointsMap B S hS (pullback a (pullback.fst g f))
      (pullback.fst a (pullback.fst g f)))
    (pointsMap B S hS (yoneda.obj U) a)
    (fun d ↦ (congrFun hcomm d).symm) hcart
    (continuous_pointsMap B S hS _) (isOpenMap_pointsMap_of_etale B S hS hZ U a haEtale)
    ((surjective_iff_surjective_pointsMap B S hS Z hZ U a).mp haSurj) hdClosed

/-- **Stacks 03XD.** A representable morphism of algebraic spaces over `S` is universally
closed in the sense of Stacks 03HI exactly when each of its represented base changes is a
universally closed morphism of schemes. -/
@[stacks 03XD]
theorem presheaf_universallyClosed_iff
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f ↔ UniversallyClosed B S hS f :=
  ⟨universallyClosed_of_presheaf_universallyClosed B S hS hX hY hf,
    presheaf_universallyClosed_of_universallyClosed B S hS hf⟩

/-! ### The represented reading -/

section Represented

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The Yoneda image of a universally closed morphism of the site is universally closed.**
Universal closedness of morphisms of schemes is stable under base change, so every represented
base change of the Yoneda image is again universally closed, and
`AlgebraicGeometry.Space.presheaf_universallyClosed_iff` turns that into universal closedness
in the sense of Stacks 03HI part (2). -/
theorem universallyClosed_yoneda_map {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (hf : AlgebraicGeometry.UniversallyClosed
      ((BigFppfOver.toScheme B S hS).map f)) :
    UniversallyClosed B S hS (yoneda.map f) :=
  (presheaf_universallyClosed_iff B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V)
      (Functor.relativelyRepresentable.map yoneda f)).mp
    ((presheaf_yoneda_map_iff B S hS
      (P := @AlgebraicGeometry.UniversallyClosed.{u}) inferInstance f).mpr hf)

end Represented

end AlgebraicGeometry.Space

end
