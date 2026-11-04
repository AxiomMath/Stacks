module

public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumRealizations
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphism
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Descending a morphism out of an effective descent datum, inside a big fppf category

Let `f i : Z i ⟶ S` be a family of morphisms of schemes and let `D` be a descent datum for it.
A morphism `r i : D_i ⟶ Y` out of each component is *gluing invariant* when the two copies of
`r` on the pairwise fibre products `D_i ×_S Z j` and `Z i ×_S D_j` agree across the gluing
isomorphism. If `D` is effective, say `D_i ≅ W ×_S Z i` for a scheme `W` over `S`, then gluing
invariance says exactly that the transported morphisms `W ×_S Z i ⟶ Y` agree on the fibre
products over `W`, which is the hypothesis a descent of `r` along the covering of `W` consumes.

This file proves that, and transports the conclusion into a big fppf category over a scheme: for
a surjective flat morphism `f : T' ⟶ T` of the site and an object `V` over `T'`, a descended
scheme supplied by effectivity automatically satisfies the site's size bound, so the
isomorphism `W ×_T T' ≅ V` and the invariance of `V ⟶ U` can be stated with `W` an object of the
site and `W ×_T T'` its fibre product there.

## Main definitions

* `AlgebraicGeometry.DescentData.IsGluingInvariant`: a family of morphisms out of the components
  of a descent datum which is compatible with the gluing isomorphisms.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_of_flat_of_surjective`: the target of a surjective flat
  morphism out of a scheme contained in a big fppf site is contained in that site.
* `AlgebraicGeometry.DescentData.IsGluingInvariant.of_iso`: gluing invariance transports along an
  isomorphism of descent data.
* `AlgebraicGeometry.DescentData.isGluingInvariant_iff`: gluing invariance read on the literal
  fibre products of schemes rather than on the products of the slice over `S`.
* `AlgebraicGeometry.CanonicalDatum.pullback_fst_comp_eq_of_isGluingInvariant`: for the canonical
  descent datum of `W`, gluing invariance is agreement on the fibre products over `W`.
* `AlgebraicGeometry.DescentData.exists_descended_of_isGluingInvariant`: an effective descent
  datum with a gluing-invariant family of morphisms to `Y` produces a scheme `W` over `S`,
  isomorphisms `W ×_S Z i ≅ D_i`, and the agreement of the transported morphisms over `W`.
* `AlgebraicGeometry.BigFppfOver.exists_iso_pullback_of_iso_pullback_toScheme`: a fibre product
  identification between objects of the big fppf category over `S` which holds for the
  underlying schemes holds in that category.
* `AlgebraicGeometry.BigFppfOver.exists_objectOver_iso_pullback_of_iso_pullback_toScheme`: the
  same with the descended scheme produced as an object of that category rather than assumed to
  be one.
* `AlgebraicGeometry.BigFppfOver.exists_objectOver_iso_pullback_of_isFamilyEffective`: the
  composite — effectivity of the descent datum of `V/T'/T` together with gluing invariance of
  `V ⟶ U` gives the descended object, the isomorphism `T' ×_T W ≅ V` and the invariance, all in
  the big fppf category over `S`.

## Implementation notes

Gluing invariance is stated in the coordinates a descent datum carries natively: the gluing
isomorphism is an isomorphism of objects over the pairwise base in the slice over `S`, so the two
copies of `r` are read off the two product projections there. On the literal fibre products of
schemes the same condition reads
`(D.gluingPullbackIso i j).hom ≫ pullback.snd (f i) _ ≫ r j = pullback.fst _ (f j) ≫ r i`, and
the transport between the two coordinate systems is conjugation by
`CategoryTheory.Over.prodLeftIsoPullback`.

For the canonical descent datum of `W` the pairwise base of the slice product is identified with
the fibre product of two components over `W`, and no comparison isomorphism is constructed: a
single morphism from the fibre product over `W` into the slice product, matching both
projections, is enough to pull the invariance back.

The size bound is the only point at which the big fppf site enters. The descended scheme receives
a surjective flat morphism from the fibre product `W ×_T T'`, which is isomorphic to the given
object `V` of the site, so the unconditional bound for the target of a surjective flat morphism
places it below the site's cutoff — the cutoff of a big fppf site being a strong prelimit
cardinal is exactly what that bound asks for. Membership in the site is therefore a conclusion
rather than a hypothesis.

## References

* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- **The target of a surjective flat morphism out of a scheme contained in a big fppf site is
contained in that site.**

Nothing is assumed of the target: the cutoff of a big fppf site is a strong prelimit cardinal,
and that is what the unconditional bound
`AlgebraicGeometry.Scheme.size_le_of_flat_of_surjective` asks for. This is the quotient
counterpart of `AlgebraicGeometry.BigFppfSite.contains_of_mono`. -/
theorem BigFppfSite.contains_of_flat_of_surjective (B : BigFppfSite.{u}) {X Y : Scheme.{u}}
    (g : X ⟶ Y) [Flat g] [Surjective g] (hX : B.Contains X) : B.Contains Y :=
  Scheme.size_lt_of_flat_of_surjective_of_isStrongPrelimit B.cutoff_isStrongPrelimit g hX

namespace DescentData

variable {ι : Type v} {S : Scheme.{u}} {Z : ι → Scheme.{u}} {f : ∀ i, Z i ⟶ S}

/-- A family of morphisms out of the components of a descent datum is **gluing invariant** when
its two copies on each pairwise fibre product agree across the gluing isomorphism.

The condition is written in the coordinates the datum carries: the gluing isomorphism lies over
the product `Z i ×_S Z j` taken in the slice over `S`, and the two copies of the family are the
two product projections followed by it. On the literal fibre products of schemes this says that
`(D.gluingPullbackIso i j).hom` carries the projection `Z i ×_S D_j ⟶ D_j` followed by `r j` to
the projection `D_i ×_S Z j ⟶ D_i` followed by `r i`. -/
def IsGluingInvariant (D : DescentData f) {Y : Scheme.{u}}
    (r : ∀ i, (D.obj i).left ⟶ Y) : Prop :=
  ∀ i j, (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶
        (Over.map (f i)).obj (D.obj i)).left ≫ r i =
    ((D.gluing i j).hom.left ≫ (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶
        (Over.map (f j)).obj (D.obj j))).left ≫ r j

/-- **Gluing invariance transports along an isomorphism of descent data.** Pulling a
gluing-invariant family back along the components of an isomorphism `D ≅ E` gives a
gluing-invariant family on `D`. -/
lemma IsGluingInvariant.of_iso {D E : DescentData f} (ξ : D ≅ E) {Y : Scheme.{u}}
    {r : ∀ i, (E.obj i).left ⟶ Y} (h : E.IsGluingInvariant r) :
    D.IsGluingInvariant fun i ↦ (ξ.hom.hom i).left ≫ r i := by
  intro i j
  have hA : prod.map ((Over.map (f i)).map (ξ.hom.hom i)) (𝟙 (Over.mk (f j))) ≫
      (prod.fst : (Over.map (f i)).obj (E.obj i) ⨯ Over.mk (f j) ⟶ _) =
      (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _) ≫
        (Over.map (f i)).map (ξ.hom.hom i) := prod.map_fst _ _
  have hB : prod.map ((Over.map (f i)).map (ξ.hom.hom i)) (𝟙 (Over.mk (f j))) ≫
      (E.gluing i j).hom.left ≫
        (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (E.obj j) ⟶ _) =
      (D.gluing i j).hom.left ≫
        (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _) ≫
        (Over.map (f j)).map (ξ.hom.hom j) := by
    rw [← Category.assoc, ξ.hom.comm i j, Category.assoc, prod.map_snd]
  have hA' := congrArg Over.Hom.left hA
  have hB' := congrArg Over.Hom.left hB
  have key := h i j
  simp only [Over.comp_left, Over.map_map_left, Category.assoc] at hA' hB' key ⊢
  rw [← reassoc_of% hA', key, reassoc_of% hB']

/-- **Gluing invariance read on the literal fibre products of schemes.** The gluing isomorphism
`D_i ×_S Z j ≅ Z i ×_S D_j` carries the projection to `D_j` followed by `r j` to the projection
to `D_i` followed by `r i`.

This is the form in which a construction of the gluing isomorphism delivers the condition; the
definition is stated in the products of the slice over `S`, which is the form in which a
morphism of descent data delivers it. -/
lemma isGluingInvariant_iff (D : DescentData f) {Y : Scheme.{u}}
    (r : ∀ i, (D.obj i).left ⟶ Y) :
    D.IsGluingInvariant r ↔ ∀ i j,
      (D.gluingPullbackIso i j).hom ≫ pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫ r j =
        pullback.fst ((D.obj i).hom ≫ f i) (f j) ≫ r i := by
  refine ⟨fun h i j ↦ ?_, fun h i j ↦ ?_⟩
  · refine (gluingPullbackIso_hom_snd_comp_iff D i j (r j) (r i)).2 ?_
    simpa only [Over.comp_left, Category.assoc] using (h i j).symm
  · have hc := (gluingPullbackIso_hom_snd_comp_iff D i j (r j) (r i)).1 (h i j)
    simpa only [Over.comp_left, Category.assoc] using hc.symm

end DescentData

namespace CanonicalDatum

variable {ι : Type v} {S : Scheme.{u}} {Z : ι → Scheme.{u}} {f : ∀ i, Z i ⟶ S}

/-- **For the canonical descent datum of `W`, gluing invariance is agreement on the fibre
products over `W`.** The pairwise base of the canonical datum is `W ×_S Z i ×_S Z j`, which is
the fibre product of the two components over `W`, and the gluing isomorphism preserves the
projection to `W`; so a gluing-invariant family agrees on that fibre product. -/
lemma pullback_fst_comp_eq_of_isGluingInvariant {W : Over S} {Y : Scheme.{u}}
    {r : ∀ i, pullback W.hom (f i) ⟶ Y}
    (h : (CanonicalDatum.datum f W).IsGluingInvariant r) (i j : ι) :
    pullback.fst (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫ r i =
      pullback.snd (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫ r j := by
  have hpb : IsPullback
      (prod.fst : component W (f i) ⨯ Over.mk (f j) ⟶ component W (f i)).left
      (prod.snd : component W (f i) ⨯ Over.mk (f j) ⟶ Over.mk (f j)).left
      (component W (f i)).hom (Over.mk (f j)).hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst (X := component W (f i)) (Y := Over.mk (f j))) prod.snd)
      (prodIsProd _ _)
  have hcond : pullback.fst (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
      pullback.fst W.hom (f i) =
      pullback.snd (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
        pullback.fst W.hom (f j) := pullback.condition
  have hc : pullback.fst (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
      (component W (f i)).hom =
      (pullback.snd (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
        pullback.snd W.hom (f j)) ≫ (Over.mk (f j)).hom := by
    show pullback.fst _ _ ≫ pullback.snd W.hom (f i) ≫ f i =
      (pullback.snd _ _ ≫ pullback.snd W.hom (f j)) ≫ f j
    rw [← pullback.condition (f := W.hom) (g := f i), Category.assoc,
      ← pullback.condition (f := W.hom) (g := f j), ← Category.assoc, ← Category.assoc, hcond]
  obtain ⟨κ, h₁, h₂⟩ : ∃ κ : pullback (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ⟶
      (component W (f i) ⨯ Over.mk (f j) : Over S).left,
      κ ≫ (prod.fst : component W (f i) ⨯ Over.mk (f j) ⟶ component W (f i)).left =
        pullback.fst (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ∧
      κ ≫ (prod.snd : component W (f i) ⨯ Over.mk (f j) ⟶ Over.mk (f j)).left =
        pullback.snd (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
          pullback.snd W.hom (f j) :=
    ⟨hpb.lift _ _ hc, hpb.lift_fst _ _ hc, hpb.lift_snd _ _ hc⟩
  have hglue : ((CanonicalDatum.datum f W).gluing i j).hom.left =
      transition W (f i) (f j) := rfl
  have eo : transition W (f i) (f j) ≫
      (prod.snd : Over.mk (f i) ⨯ component W (f j) ⟶ component W (f j)) ≫
      originalProjection W (f j) =
      (prod.fst : component W (f i) ⨯ Over.mk (f j) ⟶ component W (f i)) ≫
        originalProjection W (f i) := transition_original W (f i) (f j)
  have es : transition W (f i) (f j) ≫
      (prod.snd : Over.mk (f i) ⨯ component W (f j) ⟶ component W (f j)) ≫
      structureMap (f j) ((Over.pullback (f j)).obj W) =
      (prod.snd : component W (f i) ⨯ Over.mk (f j) ⟶ Over.mk (f j)) :=
    transition_structure W (f i) (f j)
  have h₃ : κ ≫ (((CanonicalDatum.datum f W).gluing i j).hom.left ≫
      (prod.snd : Over.mk (f i) ⨯ component W (f j) ⟶ component W (f j))).left =
      pullback.snd (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) := by
    rw [hglue]
    refine pullback.hom_ext ?_ ?_
    · calc κ ≫ (transition W (f i) (f j) ≫
            (prod.snd : Over.mk (f i) ⨯ component W (f j) ⟶ component W (f j))).left ≫
            pullback.fst W.hom (f j)
          = κ ≫ (transition W (f i) (f j) ≫
            (prod.snd : Over.mk (f i) ⨯ component W (f j) ⟶ component W (f j)) ≫
            originalProjection W (f j)).left := by
            simp [Over.comp_left, originalProjection]
        _ = κ ≫ ((prod.fst : component W (f i) ⨯ Over.mk (f j) ⟶ component W (f i)) ≫
            originalProjection W (f i)).left := by rw [eo]
        _ = pullback.fst (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
            pullback.fst W.hom (f i) := by
            rw [Over.comp_left, ← Category.assoc, h₁]
            simp [originalProjection]
        _ = pullback.snd (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
            pullback.fst W.hom (f j) := hcond
    · calc κ ≫ (transition W (f i) (f j) ≫
            (prod.snd : Over.mk (f i) ⨯ component W (f j) ⟶ component W (f j))).left ≫
            pullback.snd W.hom (f j)
          = κ ≫ (transition W (f i) (f j) ≫
            (prod.snd : Over.mk (f i) ⨯ component W (f j) ⟶ component W (f j)) ≫
            structureMap (f j) ((Over.pullback (f j)).obj W)).left := by
            simp [Over.comp_left, structureMap]
        _ = κ ≫ (prod.snd : component W (f i) ⨯ Over.mk (f j) ⟶ Over.mk (f j)).left := by
            rw [es]
        _ = pullback.snd (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
            pullback.snd W.hom (f j) := h₂
  exact (congrArg (fun m ↦ m ≫ r i) h₁).symm.trans
    ((Category.assoc _ _ _).trans ((congrArg (fun m ↦ κ ≫ m) (h i j)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m ↦ m ≫ r j) h₃))))

end CanonicalDatum

namespace DescentData

variable {ι : Type v} {S : Scheme.{u}} {Z : ι → Scheme.{u}} {f : ∀ i, Z i ⟶ S}

/-- **An effective descent datum descends a gluing-invariant family of morphisms.** If `D` is
isomorphic to the canonical descent datum of a scheme `W` over `S`, a gluing-invariant family
`r i : D_i ⟶ Y` transported to the components `W ×_S Z i` of the canonical datum agrees on the
fibre products over `W`.

This is the hypothesis that a descent of `r` along the covering of `W` by the `W ×_S Z i`
consumes. The isomorphisms `γ i` are the components of the isomorphism of descent data, so each
one is a morphism of `Z i`-schemes: `(γ i).hom.left` composed with the structure morphism of
`D_i` is the projection `W ×_S Z i ⟶ Z i`. -/
theorem exists_descended_of_isGluingInvariant {D : DescentData f}
    (hD : D.IsFamilyEffective) {Y : Scheme.{u}} {r : ∀ i, (D.obj i).left ⟶ Y}
    (hr : D.IsGluingInvariant r) :
    ∃ (W : Over S) (γ : ∀ i, (Over.pullback (f i)).obj W ≅ D.obj i),
      ∀ i j, pullback.fst (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
            (γ i).hom.left ≫ r i =
          pullback.snd (pullback.fst W.hom (f i)) (pullback.fst W.hom (f j)) ≫
            (γ j).hom.left ≫ r j := by
  obtain ⟨W, ⟨ξ⟩⟩ := hD
  refine ⟨W, fun i ↦ (evaluation (f := f) i).mapIso ξ, fun i j ↦ ?_⟩
  exact CanonicalDatum.pullback_fst_comp_eq_of_isGluingInvariant (W := W)
    (r := fun k ↦ ((evaluation (f := f) k).mapIso ξ).hom.left ≫ r k)
    (IsGluingInvariant.of_iso ξ hr) i j

end DescentData

namespace BigFppfOver

/-- If `fst ≫ m = snd ≫ m` on the self-fibre product of `g`, then `m` agrees on any two
morphisms which agree after composing with `g`. -/
private theorem comp_eq_comp_of_fst_comp_eq_snd_comp {C : Type*} [Category C] {A X Y P : C}
    {g : A ⟶ X} [HasPullback g g] {m : A ⟶ Y}
    (h : pullback.fst g g ≫ m = pullback.snd g g ≫ m) {a b : P ⟶ A} (hab : a ≫ g = b ≫ g) :
    a ≫ m = b ≫ m := by
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using
    pullback.lift a b hab ≫= h

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The fibre product identification transported from schemes into the big fppf category over
`S`.**

Let `f : T' ⟶ T` and `w : W ⟶ T` be morphisms of the big fppf category over `S`, let
`p : V ⟶ T'` and `q : V ⟶ U`, and suppose the underlying scheme of `V` is the fibre product of
the underlying morphisms of `f` and `w`, compatibly with `p`, and that the underlying morphism
of `q` is invariant for the two projections of the self-fibre product of that fibre product over
`W`. Then the same holds in the big fppf category over `S`: the fibre product of `f` and `w`
there is isomorphic to `V` over `T'`, and `q` is invariant for the two projections of its
self-fibre product over `W`.

The canonical functor to schemes is faithful and preserves fibre products, and an isomorphism
of schemes compatible with the structure morphisms to `S` is an isomorphism of the category, so
nothing is lost in either direction; what the statement provides is that the fibre products may
be taken in the category rather than in schemes. -/
theorem exists_iso_pullback_of_iso_pullback_toScheme
    {T T' U V W : BigFppfOver B S hS} (f : T' ⟶ T) (w : W ⟶ T) (p : V ⟶ T') (q : V ⟶ U)
    (γ : pullback ((toScheme B S hS).map f) ((toScheme B S hS).map w) ≅
      (toScheme B S hS).obj V)
    (hγ : γ.hom ≫ (toScheme B S hS).map p =
      pullback.fst ((toScheme B S hS).map f) ((toScheme B S hS).map w))
    (hinv : pullback.fst (pullback.snd ((toScheme B S hS).map f) ((toScheme B S hS).map w))
            (pullback.snd ((toScheme B S hS).map f) ((toScheme B S hS).map w)) ≫ γ.hom ≫
            (toScheme B S hS).map q =
          pullback.snd (pullback.snd ((toScheme B S hS).map f) ((toScheme B S hS).map w))
            (pullback.snd ((toScheme B S hS).map f) ((toScheme B S hS).map w)) ≫ γ.hom ≫
            (toScheme B S hS).map q) :
    ∃ α : pullback f w ≅ V,
      α.hom ≫ p = pullback.fst f w ∧
      pullback.fst (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q =
        pullback.snd (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q := by
  have hsq : IsPullback ((toScheme B S hS).map (pullback.fst f w))
      ((toScheme B S hS).map (pullback.snd f w)) ((toScheme B S hS).map f)
      ((toScheme B S hS).map w) :=
    (IsPullback.of_hasPullback f w).map (toScheme B S hS)
  have hfst : hsq.isoPullback.hom ≫
      pullback.fst ((toScheme B S hS).map f) ((toScheme B S hS).map w) =
      (toScheme B S hS).map (pullback.fst f w) := hsq.isoPullback_hom_fst
  have hsnd : hsq.isoPullback.hom ≫
      pullback.snd ((toScheme B S hS).map f) ((toScheme B S hS).map w) =
      (toScheme B S hS).map (pullback.snd f w) := hsq.isoPullback_hom_snd
  have hdp : (hsq.isoPullback ≪≫ γ).hom ≫ (toScheme B S hS).map p =
      (toScheme B S hS).map (pullback.fst f w) := by
    rw [Iso.trans_hom, Category.assoc, hγ, hfst]
  have hcomm : (ObjectProperty.isoMk (schemeSizeBelow B.cutoff)
        (hsq.isoPullback ≪≫ γ)).hom ≫ V.hom =
      (pullback f w).hom := by
    apply ObjectProperty.hom_ext
    have hp : (toScheme B S hS).map p ≫ B.inclusion.map T'.hom =
        B.inclusion.map V.hom := by
      have hw := congrArg B.inclusion.map (Over.w p)
      rwa [B.inclusion.map_comp] at hw
    have hfw : (toScheme B S hS).map (pullback.fst f w) ≫ B.inclusion.map T'.hom =
        B.inclusion.map (pullback f w).hom := by
      have hw := congrArg B.inclusion.map (Over.w (pullback.fst f w))
      rwa [B.inclusion.map_comp] at hw
    show (hsq.isoPullback ≪≫ γ).hom ≫ B.inclusion.map V.hom =
      B.inclusion.map (pullback f w).hom
    rw [← hp, ← hfw, ← Category.assoc, hdp]
  have hamap : (toScheme B S hS).map (Over.isoMk
      (ObjectProperty.isoMk (schemeSizeBelow B.cutoff) (hsq.isoPullback ≪≫ γ)) hcomm).hom =
      (hsq.isoPullback ≪≫ γ).hom := rfl
  refine ⟨Over.isoMk
    (ObjectProperty.isoMk (schemeSizeBelow B.cutoff) (hsq.isoPullback ≪≫ γ)) hcomm, ?_, ?_⟩
  · exact (toScheme B S hS).map_injective (by rw [Functor.map_comp, hamap]; exact hdp)
  · refine (toScheme B S hS).map_injective ?_
    have hsq2 : IsPullback
        ((toScheme B S hS).map (pullback.fst (pullback.snd f w) (pullback.snd f w)))
        ((toScheme B S hS).map (pullback.snd (pullback.snd f w) (pullback.snd f w)))
        ((toScheme B S hS).map (pullback.snd f w)) ((toScheme B S hS).map (pullback.snd f w)) :=
      (IsPullback.of_hasPullback _ _).map (toScheme B S hS)
    have key := comp_eq_comp_of_fst_comp_eq_snd_comp hinv
      (a := (toScheme B S hS).map (pullback.fst (pullback.snd f w) (pullback.snd f w)) ≫
        hsq.isoPullback.hom)
      (b := (toScheme B S hS).map (pullback.snd (pullback.snd f w) (pullback.snd f w)) ≫
        hsq.isoPullback.hom)
      (by rw [Category.assoc, Category.assoc, hsnd]; exact hsq2.w)
    simpa only [Functor.map_comp, hamap, Iso.trans_hom, Category.assoc] using key

/-- **A scheme descended along a surjective flat morphism of the big fppf category over `S` is
again an object of that category.**

Let `f : T' ⟶ T` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is surjective and flat, let `p : V ⟶ T'` and `q : V ⟶ U`, and suppose the underlying
scheme of `V` is the fibre product of `f` with a morphism `W ⟶ T` of *schemes*, compatibly with
`p`, and that `q` is invariant for the two projections of the self-fibre product of that fibre
product over `W`. Then the same data exists with `W` an object of the big fppf category over `S`
and the fibre product taken in that category.

No size hypothesis is needed on `W`: the projection `V ≅ T' ×_T W ⟶ W` is surjective and flat,
so `AlgebraicGeometry.BigFppfSite.contains_of_flat_of_surjective` places `W` below the site's
cutoff. This is the shape in which the middle paragraph of the proof of Stacks 0APL consumes
effectivity of descent for the datum a section of an algebraic space determines. -/
theorem exists_objectOver_iso_pullback_of_iso_pullback_toScheme
    {T T' U V : BigFppfOver B S hS} (f : T' ⟶ T) (p : V ⟶ T') (q : V ⟶ U)
    (hff : Flat ((toScheme B S hS).map f)) (hfs : Surjective ((toScheme B S hS).map f))
    (W : Over ((toScheme B S hS).obj T))
    (γ : pullback ((toScheme B S hS).map f) W.hom ≅ (toScheme B S hS).obj V)
    (hγ : γ.hom ≫ (toScheme B S hS).map p = pullback.fst ((toScheme B S hS).map f) W.hom)
    (hinv : pullback.fst (pullback.snd ((toScheme B S hS).map f) W.hom)
            (pullback.snd ((toScheme B S hS).map f) W.hom) ≫ γ.hom ≫
            (toScheme B S hS).map q =
          pullback.snd (pullback.snd ((toScheme B S hS).map f) W.hom)
            (pullback.snd ((toScheme B S hS).map f) W.hom) ≫ γ.hom ≫
            (toScheme B S hS).map q) :
    ∃ (W' : BigFppfOver B S hS) (w : W' ⟶ T) (α : pullback f w ≅ V),
      α.hom ≫ p = pullback.fst f w ∧
      pullback.fst (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q =
        pullback.snd (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q := by
  have hsurj : Surjective (pullback.snd ((toScheme B S hS).map f) W.hom) := inferInstance
  have hflat : Flat (pullback.snd ((toScheme B S hS).map f) W.hom) := inferInstance
  have hWc : B.Contains W.left :=
    B.contains_of_flat_of_surjective (pullback.snd ((toScheme B S hS).map f) W.hom)
      ((Scheme.size_congr γ).trans_lt V.left.property)
  exact ⟨Over.mk (ObjectProperty.homMk
      (X := B.obj hWc) (W.hom ≫ B.inclusion.map T.hom)),
    Over.homMk (ObjectProperty.homMk (X := B.obj hWc) W.hom)
      (by apply ObjectProperty.hom_ext; rfl),
    exists_iso_pullback_of_iso_pullback_toScheme f _ p q γ hγ hinv⟩

/-- **Effective descent for the datum a chart determines, in the shape the proof of Stacks 0APL
consumes it.**

Let `f : T' ⟶ T` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is surjective and flat, let `p : V ⟶ T'` and `q : V ⟶ U`. A gluing isomorphism `φ` for
`V/T'/T` satisfying the cocycle condition makes `V` a descent datum relative to `f`; if that
datum is effective and `q` is invariant for its gluing, then there are an object `W` of the big
fppf category over `S`, a morphism `w : W ⟶ T`, and an isomorphism `α : T' ×_T W ≅ V` over `T'`
in that category, for which `q` is invariant for the two projections of the self-fibre product
of `T' ×_T W` over `W`.

This is the conversion of effectivity — in the form
`AlgebraicGeometry.DescentData.IsFamilyEffective`, membership in the essential image of the
canonical-datum functor — into the statement about the site which the middle paragraph of the
proof of Stacks 0APL uses. Everything beyond effectivity and gluing invariance of `q` is
discharged here: the descended scheme lies below the site's cutoff because it receives a
surjective flat morphism from `V`, the fibre product may be taken in the category because the
canonical functor to schemes preserves fibre products and is fully faithful on morphisms over
`S`, and the invariance passes through the identification of the self-fibre product of
`T' ×_T W` over `W` with the pairwise base of the canonical datum of `W`. -/
theorem exists_objectOver_iso_pullback_of_isFamilyEffective
    {T T' U V : BigFppfOver B S hS} (f : T' ⟶ T) (p : V ⟶ T') (q : V ⟶ U)
    (hff : Flat ((toScheme B S hS).map f)) (hfs : Surjective ((toScheme B S hS).map f))
    (φ : Over.mk (prod.map (structureMap ((toScheme B S hS).map f)
          (Over.mk ((toScheme B S hS).map p)))
        (𝟙 (Over.mk ((toScheme B S hS).map f)))) ≅
      Over.mk (prod.map (𝟙 (Over.mk ((toScheme B S hS).map f)))
        (structureMap ((toScheme B S hS).map f) (Over.mk ((toScheme B S hS).map p)))))
    (cocycle : prod.map φ.hom.left (𝟙 (Over.mk ((toScheme B S hS).map f))) ≫
        prodMapLastTwo φ.hom.left = prodMapFirstThird φ.hom.left)
    (heff : (DescentDatum.mk' (f := (toScheme B S hS).map f)
      (Over.mk ((toScheme B S hS).map p)) φ cocycle).IsFamilyEffective)
    (hq : (DescentDatum.mk' (f := (toScheme B S hS).map f)
      (Over.mk ((toScheme B S hS).map p)) φ cocycle).IsGluingInvariant
      fun _ ↦ (toScheme B S hS).map q) :
    ∃ (W : BigFppfOver B S hS) (w : W ⟶ T) (α : pullback f w ≅ V),
      α.hom ≫ p = pullback.fst f w ∧
      pullback.fst (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q =
        pullback.snd (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q := by
  obtain ⟨W, γ, hagree⟩ := DescentData.exists_descended_of_isGluingInvariant heff hq
  have hw : (γ ()).hom.left ≫ (toScheme B S hS).map p =
      pullback.snd W.hom ((toScheme B S hS).map f) := Over.w (γ ()).hom
  refine exists_objectOver_iso_pullback_of_iso_pullback_toScheme f p q hff hfs W
    (pullbackSymmetry ((toScheme B S hS).map f) W.hom ≪≫
      (Over.forget ((toScheme B S hS).obj T')).mapIso (γ ())) ?_ ?_
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Over.forget_map]
    rw [Category.assoc, hw, pullbackSymmetry_hom_comp_snd]
  · have key := comp_eq_comp_of_fst_comp_eq_snd_comp (hagree () ())
      (a := pullback.fst (pullback.snd ((toScheme B S hS).map f) W.hom)
          (pullback.snd ((toScheme B S hS).map f) W.hom) ≫
        (pullbackSymmetry ((toScheme B S hS).map f) W.hom).hom)
      (b := pullback.snd (pullback.snd ((toScheme B S hS).map f) W.hom)
          (pullback.snd ((toScheme B S hS).map f) W.hom) ≫
        (pullbackSymmetry ((toScheme B S hS).map f) W.hom).hom)
      (by rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst]
          exact pullback.condition)
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc] using key

end BigFppfOver

end AlgebraicGeometry

end

end
