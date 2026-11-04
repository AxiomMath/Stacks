module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringIndexUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePointIso
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict

/-!
# Descent of a relative property along a locally essentially surjective 1-morphism (Stacks 045D)

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of morphisms of
algebraic spaces over `S` which is stable under base change and local on the target for the fppf
precoverage. Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf
site of `S` which is representable by algebraic spaces, let `g : 𝒵 ⟶ 𝒴` be any 1-morphism, and fix
a 2-fibre product square over the cospan `(g, f)`. Stacks 045D says that if every object of `𝒴`
becomes, after restriction to a covering sieve, isomorphic to an object coming from `𝒵`, then the
relative property `P` of Stacks 03YK *descends*: if the projection to `𝒵` has `P`, so does `f`.

The proof is the one the source points to (Spaces, Lemma 03KD). Fix a scheme `U` over `S`, a
scheme-valued point `y` of `𝒴` over `U` and an algebraic space `F` over `U` representing the base
change `U ×_𝒴 𝒳`. The structural morphism of `F` read over `S` is
`CategoryTheory.OverShriek.relocalizeToYoneda`
(`AlgebraicGeometry.Space.prop_relocalizeToYoneda_iff`), so the goal is a property of a morphism
of algebraic spaces over `S` with target the representable algebraic space of `U`, and that
property may be tested on a covering of the target. Local essential surjectivity at the object of
`𝒴` that `y` names supplies a covering sieve of `U`;
`AlgebraicGeometry.exists_family_of_mem_topology` extracts from it a flat, locally of finite
presentation and jointly surjective family of morphisms
`kᵢ : Vᵢ ⟶ U` of the site, all of whose members lie in the sieve, and
`AlgebraicGeometry.Space.ofArrows_yoneda_mem_fppfPrecoverage` makes the represented family a
covering of the fppf precoverage on algebraic spaces over `S`.

It remains to see that the base change of the structural morphism of `F` to one member of that
covering has `P`. The base change is the structural morphism of the *restriction* of `F` to `Vᵢ`
(`CategoryTheory.OverShriek.isPullback_relocalizeRestrictMap`), that restriction is again an
algebraic space (Stacks 03I5 part (1)), and it represents the base change of `f` along the
restricted point `Over.map mᵢ ⋙ y`
(`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_relocalizeRestrict`). Since `kᵢ`
lies in the sieve, the object of `𝒴` over `Vᵢ` carried by that restricted point is isomorphic to
the image of an object `z` of `𝒵`; 2-Yoneda turns `z` into a scheme-valued point `z♯` of `𝒵` over
`Vᵢ` (`StacksRepresentableCFG.exists_pointOverMap_of_obj`) and the isomorphism of objects into a
2-isomorphism of the two points `z♯ ⋙ g` and `Over.map mᵢ ⋙ y`
(`StacksRepresentableCFG.exists_natIso_of_iso_at_id`). Reindexing the 2-fibre product along that
2-isomorphism (`CategoryTheory.TwoFibreProductOver.reindexEquivalenceOver`) and cancelling the
middle factor as in Stacks 045C
(`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver`) exhibit the restriction of `F` as a
representing algebraic space for the base change of the projection along `z♯` — which is exactly
what the hypothesis on the projection applies to.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_of_baseChange`: the descent, with no witness of
  representability in scope.
* `AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange`: **Stacks 045D**.

## Implementation notes

The universes of the three categories fibred in groupoids are those of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange` (Stacks 0302), whose
conclusion is the representability witness the statement has to feed to
`AlgebraicGeometry.Stack.HasRelativeProperty`: morphism universe `max u v` and object universe
`max (max (u + 1) w) v` for the site's universe `u` and arbitrary `v`, `w`. This is the same
saturation Stacks 045C carries, and for the same reason; the unconstrained assignment
`CatFiberedInGroupoids.{u, v, u + 1, w}` is not used, since it is defective for Stacks 0302.

The index universe of `AlgebraicGeometry.Space.Topology.fppf.precoverage` in the locality
hypothesis is `max u t` for a free `t`, which is every index universe at or above the site's own
universe `u`. The proof needs the hypothesis at `t = u`: the covering family produced by local
essential surjectivity is indexed by the points of the underlying scheme of `U`, a type in
`Type u`, and a covering presieve of
`AlgebraicGeometry.Space.Topology.fppf.precoverage.{u, t}` is by definition presented by a
`Type t`-indexed family. It reaches that instance from the stated one by
`AlgebraicGeometry.Space.Topology.precoverage_le_precoverage_max` together with
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`, so the pin to `u` this statement used to
carry is forced only *below* the site universe. What is still not reached is an index universe
that is not above `u`, and that is the strongest form available rather than a gap: membership in
`AlgebraicGeometry.Space.Topology.precoverage.{u, v}` is presentation by a `Type v`-indexed
family and the order on `CategoryTheory.Precoverage` is containment, with no refinement
permitted, so a family indexed below the site cannot be reindexed into `Type u`.

The covering family is reindexed by the points of the underlying scheme of `U` rather than taken
as `AlgebraicGeometry.exists_family_of_mem_topology` produces it, whose index type lives in
`Type (u + 1)`: one member per point suffices for joint surjectivity, and that keeps the index
universe at `u`.

## References

* [Stacks Project, Tag 03KD](https://stacks.math.columbia.edu/tag/03KD)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.OverShriek
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u v w t

/-- **Stacks 045D with no representability witness in scope.** Let `P` be a property of morphisms
of algebraic spaces over `S` which is stable under base change and local on the target for the
fppf precoverage, and let `f : 𝒳 ⟶ 𝒴` and `g : 𝒵 ⟶ 𝒴` be 1-morphisms of categories fibred in
groupoids over the big fppf site of `S`. Assume that every object of a fibre of `𝒴` becomes, after
restriction to a covering sieve, isomorphic to the image of an object of `𝒵`. Then in a 2-fibre
product square over the cospan `(g, f)`, if the projection to `𝒵` satisfies the condition of
Stacks 03YK at `P`, so does `f`.

The source states this for an `f` representable by algebraic spaces, and
`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange` is this result stated that way. The
witness is not used by the argument, which reads the representing algebraic space of each base
change off the quantifier being proved rather than off a global witness, so it is dropped here;
that is what lets a consumer with no witness — Stacks 06FH, whose representability input is the
uncited Stacks 04WZ — descend a property all the same. -/
theorem relativeProperty_of_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (D : Bicategory.TwoCommSq g f)
    (hD : Bicategory.IsTwoFibreProduct D)
    (hg : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒵.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1,
            𝒴.val.p.IsHomLift k φ)
    (hP : RelativeProperty B S hS P D.fst) :
    RelativeProperty B S hS P f := by
  classical
  have : P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.Topology.precoverage_le_precoverage_max .fppf B S hS)
  intro U y hy F hF hE
  obtain ⟨E⟩ := hE
  -- the object of `𝒴` over `U` determined by the point `y`
  have hUid : (Over.map U.hom).obj (Over.mk (𝟙 U.left)) = U :=
    StacksRepresentableCFG.forget_obj_iteratedSliceBackward_id U
  have hy₀ : 𝒴.val.p.obj (y.obj (Over.mk (𝟙 U.left))) = U :=
    (Functor.congr_obj hy (Over.mk (𝟙 U.left))).trans hUid
  obtain ⟨R, hR, hlift⟩ := hg U ⟨y.obj (Over.mk (𝟙 U.left)), hy₀⟩
  obtain ⟨I, W, m, hmem, hflat, hlfp, hsurj⟩ :=
    exists_family_of_mem_topology B S hS (U := U) hR
  choose ι hι using hsurj
  -- the covering family, reindexed by the points of the underlying scheme of `U`
  let V' : (B.inclusion.obj U.left) → BigFppfOver B S hS :=
    fun x => Over.mk (m (ι x) ≫ U.hom)
  let k' : ∀ x, V' x ⟶ U := fun x => Over.homMk (m (ι x))
  have hcov := Space.ofArrows_yoneda_mem_fppfPrecoverage.{u, u} B S hS (U := U) V' k'
    (fun x => hflat (ι x)) (fun x => hlfp (ι x)) (fun x => by
      obtain ⟨z, hz⟩ := hι x
      exact ⟨x, z, hz⟩)
  refine (Space.prop_relocalizeToYoneda_iff B S hS P U F hF).1 ?_
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := P) (K := Space.Topology.fppf.precoverage.{u, u} B S hS) hcov).2 ?_
  intro T q hpb hq
  obtain ⟨x⟩ := hq
  have hFx : IsAlgebraicSpace B (W (ι x)).1 (W (ι x)).2
      ((relocalizeRestrict (m (ι x))).obj F) :=
    isAlgebraicSpace_relocalizeRestrict B (W (ι x)).1 U.left.1 (W (ι x)).2 U.left.2
      (m (ι x)) F hF
  have hΛF := Space.isAlgebraicSpace_relocalizePresheaf B S hS U F hF
  have hΛFx := Space.isAlgebraicSpace_relocalizePresheaf B S hS (V' x)
    ((relocalizeRestrict (m (ι x))).obj F) hFx
  have hc := OverShriek.isPullback_relocalizeRestrictMap U.hom (m (ι x)) F
  have hsq : IsPullback
      (ObjectProperty.homMk (relocalizeRestrictMap U.hom (m (ι x)) F) :
        (⟨_, hΛFx⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hΛF⟩)
      (ObjectProperty.homMk
          (relocalizeToYoneda (m (ι x) ≫ U.hom) ((relocalizeRestrict (m (ι x))).obj F)) :
        (⟨_, hΛFx⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (V' x), isAlgebraicSpace_yoneda B S hS (V' x)⟩)
      (ObjectProperty.homMk (relocalizeToYoneda U.hom F) :
        (⟨_, hΛF⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (ObjectProperty.homMk (yoneda.map (k' x))) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hc
  rw [← P.cancel_left_of_respectsIso hsq.isoPullback.hom, hsq.isoPullback_hom_snd]
  refine (Space.prop_relocalizeToYoneda_iff B S hS P (V' x) _ hFx).2 ?_
  -- the lift of the object of `𝒴` over `V' x` to `𝒵`
  obtain ⟨z, φ, hφ⟩ := hlift (hmem (ι x))
  have hz₀ : 𝒵.val.p.obj z = V' x :=
    (Functor.congr_obj g.hom.w z).symm.trans
      (CategoryTheory.IsHomLift.domain_eq 𝒴.val.p (k' x) φ)
  obtain ⟨zp, hzp, ξ, hξ⟩ :=
    StacksRepresentableCFG.exists_pointOverMap_of_obj 𝒵.val.p 𝒵.property (V' x) z hz₀
  have hVid : (Over.map (V' x).hom).obj (Over.mk (𝟙 (V' x).left)) = V' x :=
    StacksRepresentableCFG.forget_obj_iteratedSliceBackward_id (V' x)
  have hu₁ : (zp ⋙ CatFiberedInGroupoids.homFunctor g) ⋙ 𝒴.val.p
      = Over.map (V' x).hom := by
    rw [Functor.assoc, g.hom.w, hzp]
  have hu₂ : (Over.map (m (ι x)) ⋙ y) ⋙ 𝒴.val.p = Over.map (V' x).hom := by
    rw [Functor.assoc, hy, ← Over.mapComp_eq]
    rfl
  -- verticality of the comparison of the two points at the tautological object
  have hξ' : 𝒴.val.p.IsHomLift (𝟙 (V' x))
      ((CatFiberedInGroupoids.homFunctor g).map ξ.hom) := by
    have _ := hξ
    exact Functor.isHomLift_map_of_comp_eq g.hom.w (𝟙 (V' x)) ξ.hom
  have hψ₁ : 𝒴.val.p.IsHomLift (𝟙 (V' x) ≫ k' x)
      ((CatFiberedInGroupoids.homFunctor g).map ξ.hom ≫ φ) := by
    have _ := hξ'
    have _ := hφ
    exact CategoryTheory.IsHomLift.comp 𝒴.val.p (𝟙 (V' x)) (k' x) _ _
  have hid₂ : 𝒴.val.p.obj
      ((Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left))) = V' x :=
    (Functor.congr_obj hu₂ (Over.mk (𝟙 (V' x).left))).trans hVid
  let σ := y.map (StacksRepresentableCFG.toTautological
    ((Over.map (m (ι x))).obj (Over.mk (𝟙 (V' x).left))))
  have hσ : 𝒴.val.p.IsHomLift (k' x) σ := by
    refine CategoryTheory.IsHomLift.of_fac' _ (k' x) _ hid₂ hy₀ ?_
    have hcg := Functor.congr_hom hy (StacksRepresentableCFG.toTautological
      ((Over.map (m (ι x))).obj (Over.mk (𝟙 (V' x).left))))
    rw [show 𝒴.val.p.map σ = (y ⋙ 𝒴.val.p).map (StacksRepresentableCFG.toTautological
        ((Over.map (m (ι x))).obj (Over.mk (𝟙 (V' x).left)))) from rfl, hcg]
    refine Over.OverMorphism.ext ?_
    simp [k']
  obtain ⟨θ, hθ⟩ : ∃ θ : (zp ⋙ CatFiberedInGroupoids.homFunctor g).obj
        (Over.mk (𝟙 (V' x).left)) ≅
        (Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left)),
      𝒴.val.p.IsHomLift
        (𝟙 ((Over.map (V' x).hom).obj (Over.mk (𝟙 (V' x).left)))) θ.hom := by
    have _ := hσ
    have _ := hψ₁
    have _ : 𝒴.val.p.IsHomLift (𝟙 (V' x))
        (𝟙 ((Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left)))) :=
      CategoryTheory.IsHomLift.id hid₂
    have hiso := 𝒴.property.isHomLift_twoStepLiftIso_hom (𝟙 (V' x)) (k' x) σ
      (𝟙 ((Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left))))
      ((CatFiberedInGroupoids.homFunctor g).map ξ.hom ≫ φ)
    refine ⟨(𝒴.property.twoStepLiftIso (𝟙 (V' x)) (k' x) σ
      (𝟙 ((Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left))))
      ((CatFiberedInGroupoids.homFunctor g).map ξ.hom ≫ φ)).symm, ?_⟩
    rw [hVid]
    have _ := hiso
    exact CategoryTheory.IsHomLift.lift_id_inv 𝒴.val.p (V' x) _
  obtain ⟨α, hα⟩ := StacksRepresentableCFG.exists_natIso_of_iso_at_id (V' x).hom
    (zp ⋙ CatFiberedInGroupoids.homFunctor g) (Over.map (m (ι x)) ⋙ y) hu₁ hu₂
    𝒴.property θ hθ
  obtain ⟨E1⟩ := nonempty_baseChangeEquivalenceOver.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g D hD (V' x) zp hzp
  obtain ⟨E3⟩ := nonempty_equivalenceOver_relocalizeRestrict U.hom (m (ι x)) F y
    (CatFiberedInGroupoids.homFunctor f) hy f.hom.w 𝒳.property 𝒴.property E
  exact hP (V' x) zp hzp _ hFx
    ⟨E1.trans ((TwoFibreProductOver.reindexEquivalenceOver α hα).trans E3)⟩

/-- **Stacks 045D.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
stable under base change and local on the target for the fppf precoverage, let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of categories fibred in groupoids over the big fppf site of `S` representable by
algebraic spaces and let `g : 𝒵 ⟶ 𝒴` be any 1-morphism. Assume that every object of a fibre of
`𝒴` becomes, after restriction to a covering sieve, isomorphic to the image of an object of `𝒵`.
Then in a 2-fibre product square over the cospan `(g, f)`, if the projection to `𝒵` has the
relative property `P` of Stacks 03YK, so does `f`.

This is `AlgebraicGeometry.Stack.relativeProperty_of_baseChange` with the representability of `f`
assumed as the source assumes it, which is what names the relative property of Stacks 03YK on
both sides. -/
@[stacks 045D]
theorem hasRelativeProperty_of_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (D : Bicategory.TwoCommSq g f)
    (hD : Bicategory.IsTwoFibreProduct D)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒵.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1,
            𝒴.val.p.IsHomLift k φ)
    (hP : HasRelativeProperty B S hS P D.fst
      (isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g D hD hf)) :
    HasRelativeProperty B S hS P f hf :=
  relativeProperty_of_baseChange.{u, v, w, t} B S hS 𝒳 𝒴 𝒵 P f g D hD hg hP

end AlgebraicGeometry.Stack

end
