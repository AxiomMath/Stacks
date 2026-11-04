module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealizationSelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SplittingAffineSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupAtPointSpaceMap

/-!
# Automorphism groups of points of the quotient stack of an open subgroupoid scheme

Let `φ : G ⟶ H` be a morphism of groupoid schemes which is an open immersion on arrows and an
equality on objects (the inclusion of an open subgroupoid `P ⊆ R` on the same objects `U`), and
let `u ∈ U` be a point such that `P` contains the arrow of every point of the stabilizer of `R`
over `u`. The proof of **Stacks 0DU4** uses that the 1-morphism `[U/P] ⟶ [U/R]` then induces an
isomorphism between the automorphism groups at the point `u`. This file proves the statement on
the presented objects: at the object of `[U/P]` presented by a generalized point of `U` lying
over `u`, `[φ]` is bijective on the automorphisms lying over an identity.

## Main results

* `Stacks.Groupoids.GroupoidScheme.Hom.realization_arrow_lift_of_stabilizer`: an arrow of the
  realization of `H` with source and target the image of a generalized point over `u` is the
  image of an arrow of the realization of `G`.
* `Stacks.Groupoids.GroupoidScheme.Hom.bijective_verticalAutMap_quotientStackMap_realization`:
  `[φ]` is bijective on the vertical automorphism group of an object presented by a generalized
  point over `u`.

## Implementation notes

An automorphism over an identity of a presented object of a quotient stack is, by Stacks 044X,
the image of a unique arrow of the groupoid of points, and `[φ]` acts on it, up to the
2-isomorphism of Stacks 046Q, as the arrow map of `φ`
(`AlgebraicGeometry.Stack.quotientStackMap_map_pointwiseToQuotientStackFiber`). Injectivity is
the faithfulness of `[φ]`; surjectivity is the lift of an arrow of `R` whose source and target
are a generalized point over `u`, which is
`Stacks.Groupoids.GroupoidScheme.exists_comp_mapArrows_eq_of_stabilizer_le`.

## References

* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 0DU4](https://stacks.math.columbia.edu/tag/0DU4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Space Opposite
open CategoryTheory.Pseudofunctor

universe u

namespace Stacks.Groupoids.GroupoidScheme.Hom

variable {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S)
  {G H : GroupoidScheme S} (φ : Hom G H)
  (hGU : C.Contains G.objects.left) (hGR : C.Contains G.arrows.left)
  (hGP : C.Contains (pullback G.source G.target).left)
  (hHU : C.Contains H.objects.left) (hHR : C.Contains H.arrows.left)
  (hHP : C.Contains (pullback H.source H.target).left)

/-- **Arrows over a point at which the subgroupoid contains the stabilizer lift.** Let
`φ : G ⟶ H` be a morphism of groupoid schemes which is an open immersion on arrows and an
equality on objects, and let `u` be a point of the object scheme of `H` such that the image of
`φ` contains the arrow of every stabilizer point of `H` over `u`. Then an arrow of the
realization of `H` over a test object whose source and target are both the image of one
generalized point of `G` lying over `u` is the image of an arrow of the realization of `G` with
that source and target. -/
theorem realization_arrow_lift_of_stabilizer [IsOpenImmersion φ.mapArrows.left]
    (e : G.objects = H.objects) (hφ : φ.mapObjects = eqToHom e) (u : H.objects.left)
    (hstab : ∀ y : (AlgebraicGeometry.stabilizer H).left,
      (AlgebraicGeometry.stabilizer H).hom.base y = u →
        ∃ p : G.arrows.left,
          φ.mapArrows.left.base p = (AlgebraicGeometry.stabilizerArrow H).base y)
    (T : BigFppfOver C S hS) (x : (G.realization C hS hGU hGR hGP).objects.obj.obj (op T))
    (hx : IsOverPoint C hS hGU hGR hGP ((eqToHom e.symm).left.base u) T x)
    (b : (H.realization C hS hHU hHR hHP).arrows.obj.obj (op T))
    (hbs : (H.realization C hS hHU hHR hHP).toGroupoidInFunctors.source.app (op T) b =
      (realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapObjects.app (op T) x)
    (hbt : (H.realization C hS hHU hHR hHP).toGroupoidInFunctors.target.app (op T) b =
      (realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapObjects.app (op T) x) :
    ∃ a : (G.realization C hS hGU hGR hGP).arrows.obj.obj (op T),
      (G.realization C hS hGU hGR hGP).toGroupoidInFunctors.source.app (op T) a = x ∧
      (G.realization C hS hGU hGR hGP).toGroupoidInFunctors.target.app (op T) a = x ∧
      (realization C hS φ hGU hGR hGP hHU hHR hHP).toGroupoidHom.mapArrows.app (op T) a = b := by
  set eHU := yonedaSchemePointEquiv C hS hHU (op T)
  set eHR := yonedaSchemePointEquiv C hS hHR (op T)
  set eGU := yonedaSchemePointEquiv C hS hGU (op T)
  set eGR := yonedaSchemePointEquiv C hS hGR (op T)
  have hs : eHR b ≫ H.source = eGU x ≫ φ.mapObjects :=
    (yonedaSchemePointEquiv_map C hS hHR hHU H.source (op T) b).symm.trans ((congrArg eHU hbs).trans
      (yonedaSchemePointEquiv_realization_mapObjects C hS φ hGU hGR hGP hHU hHR hHP (op T) x))
  have ht : eHR b ≫ H.target = eGU x ≫ φ.mapObjects :=
    (yonedaSchemePointEquiv_map C hS hHR hHU H.target (op T) b).symm.trans ((congrArg eHU hbt).trans
      (yonedaSchemePointEquiv_realization_mapObjects C hS φ hGU hGR hGP hHU hHR hHP (op T) x))
  have hpt : ∀ τ, (eGU x ≫ φ.mapObjects).left.base τ = u := fun τ => by
    rw [hφ, Over.comp_left, Scheme.Hom.comp_apply]
    rw [hx τ]
    exact over_eqToHom_apply_symm e u
  obtain ⟨a', ha'⟩ := exists_comp_mapArrows_eq_of_stabilizer_le φ inferInstance hstab
    (eGU x ≫ φ.mapObjects) hpt (eHR b) hs ht
  have : IsIso φ.mapObjects := by
    rw [hφ]
    infer_instance
  refine ⟨eGR.symm a', ?_, ?_, ?_⟩
  · apply eGU.injective
    refine (yonedaSchemePointEquiv_map C hS hGR hGU G.source (op T) _).trans ?_
    rw [Equiv.apply_symm_apply, ← cancel_mono φ.mapObjects, Category.assoc,
      ← φ.map_source, ← Category.assoc, ha', hs]
  · apply eGU.injective
    refine (yonedaSchemePointEquiv_map C hS hGR hGU G.target (op T) _).trans ?_
    rw [Equiv.apply_symm_apply, ← cancel_mono φ.mapObjects, Category.assoc,
      ← φ.map_target, ← Category.assoc, ha', ht]
  · apply eHR.injective
    refine (yonedaSchemePointEquiv_realization_mapArrows C hS φ hGU hGR hGP hHU hHR hHP (op T)
      _).trans ?_
    rw [Equiv.apply_symm_apply, ha']

/-- **`[φ]` is surjective on the automorphism group of an object presented by a point over
`u`.** Under the hypotheses of `realization_arrow_lift_of_stabilizer`, every automorphism over an
identity of the image under `[φ]` of the object of `[U/G]` presented by a generalized point over
`u` is the image of an automorphism over an identity. -/
private theorem surjective_verticalAutMap_quotientStackMap_realization
    [IsOpenImmersion φ.mapArrows.left]
    (e : G.objects = H.objects) (hφ : φ.mapObjects = eqToHom e) (u : H.objects.left)
    (hstab : ∀ y : (AlgebraicGeometry.stabilizer H).left,
      (AlgebraicGeometry.stabilizer H).hom.base y = u →
        ∃ p : G.arrows.left,
          φ.mapArrows.left.base p = (AlgebraicGeometry.stabilizerArrow H).base y)
    (T : BigFppfOver C S hS) (x : (G.realization C hS hGU hGR hGP).objects.obj.obj (op T))
    (hx : IsOverPoint C hS hGU hGR hGP ((eqToHom e.symm).left.base u) T x) :
    Function.Surjective (Functor.verticalAutMap
      (Stack.quotientStackMap (realization C hS φ hGU hGR hGP hHU hHR hHP)).toFunctor
      (Stack.quotientStackMap (realization C hS φ hGU hGR hGP hHU hHR hHP)).w
      ((Stack.pointwiseToQuotientStackFiber (G.realization C hS hGU hGR hGP) T).obj x).1) := by
  let G' := G.realization C hS hGU hGR hGP
  let H' := H.realization C hS hHU hHR hHP
  let Φ := realization C hS φ hGU hGR hGP hHU hHR hHP
  have hFH := (Stack.fullyFaithful_pointwiseToQuotientStackFiber H' T).some
  intro β
  let A := (Stack.pointwiseToQuotientStackFiber G' T).obj x
  let x' := (Φ.toGroupoidHom.evaluation (op T)).obj x
  let B' := (Stack.pointwiseToQuotientStackFiber H' T).obj x'
  let α := Stack.quotientStackMapCommutesIso Φ
  let X := (CoGrothendieck.ι (Stack.evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
    Grpd.forgetToCat).toPseudofunctor' T).obj x
  have hαh : (Stack.quotientStack H').p.IsHomLift (𝟙 T) (α.hom.app X) :=
    (Stack.quotientStackMap_commutes Φ).hom.isHomLift' X
  have hαi : (Stack.quotientStack H').p.IsHomLift (𝟙 T) (α.inv.app X) :=
    (Stack.quotientStackMap_commutes Φ).inv.isHomLift' X
  have hT : (Stack.quotientStack H').p.obj ((Stack.quotientStackMap Φ).obj A.1) = T := by
    rw [← Functor.comp_obj, (Stack.quotientStackMap Φ).w]
    exact A.2
  have hβ : (Stack.quotientStack H').p.IsHomLift (𝟙 T) β.1.hom :=
    IsHomLift.of_fac' _ _ _ hT hT (by
      rw [Functor.verticalAut.cond β, Category.id_comp, eqToHom_trans]
      rfl)
  let n : B' ⟶ B' := Functor.Fiber.homMk _ T (α.hom.app X) ≫
    Functor.Fiber.homMk _ T β.1.hom ≫ Functor.Fiber.homMk _ T (α.inv.app X)
  let r' := hFH.preimage n
  let b := H'.toGroupoidInFunctors.evaluationArrowEquiv (op T) x' x' r'
  obtain ⟨a, has, hat, hab⟩ := realization_arrow_lift_of_stabilizer C hS φ hGU hGR hGP hHU hHR
    hHP e hφ u hstab T x hx b.1 b.2.1 b.2.2
  let xe : G'.toGroupoidInFunctors.Evaluation (op T) := x
  let r : xe ⟶ xe :=
    (G'.toGroupoidInFunctors.evaluationArrowEquiv (op T) xe xe).symm ⟨a, has, hat⟩
  have hr : (Φ.toGroupoidHom.evaluation (op T)).map r = r' := by
    apply (H'.toGroupoidInFunctors.evaluationArrowEquiv (op T) x' x').injective
    apply Subtype.ext
    refine (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow Φ.toGroupoidHom (op T)
      r).trans ?_
    rw [Equiv.apply_symm_apply]
    exact hab
  let m := (Stack.pointwiseToQuotientStackFiber G' T).map r
  refine ⟨⟨Functor.Fiber.fiberInclusion.mapIso (asIso m),
    (Functor.mem_verticalAut_iff _ _).mpr (Functor.map_fiberInclusion_map_eq_id _ m)⟩, ?_⟩
  apply Subtype.ext
  apply Aut.ext
  show (Stack.quotientStackMap Φ).toFunctor.map m.1 = β.1.hom
  rw [Stack.quotientStackMap_map_pointwiseToQuotientStackFiber, hr,
    congrArg Subtype.val (hFH.map_preimage n)]
  show α.inv.app X ≫ (α.hom.app X ≫ β.1.hom ≫ α.inv.app X) ≫ α.hom.app X = _
  have aux : ∀ {𝒞 : Type (u + 1)} [Category.{u + 1} 𝒞] {P Q : 𝒞} (i : P ≅ Q) (c : Q ⟶ Q),
      i.inv ≫ (i.hom ≫ c ≫ i.inv) ≫ i.hom = c := fun _ _ => by simp
  exact aux (α.app X) β.1.hom

/-- **`[φ]` preserves the automorphism group of an object presented by a point over `u`.** Let
`φ : G ⟶ H` be a morphism of groupoid schemes which is an open immersion on arrows and an
equality on objects, and let `u` be a point of the object scheme of `H` such that the image of
`φ` contains the arrow of every stabilizer point of `H` over `u`. Then at the object of `[U/G]`
presented by a generalized point of the object scheme lying over `u`, the 1-morphism
`[φ] : [U/G] ⟶ [U/H]` is bijective on the automorphisms lying over an identity of the site. -/
theorem bijective_verticalAutMap_quotientStackMap_realization [IsOpenImmersion φ.mapArrows.left]
    (e : G.objects = H.objects) (hφ : φ.mapObjects = eqToHom e) (u : H.objects.left)
    (hstab : ∀ y : (AlgebraicGeometry.stabilizer H).left,
      (AlgebraicGeometry.stabilizer H).hom.base y = u →
        ∃ p : G.arrows.left,
          φ.mapArrows.left.base p = (AlgebraicGeometry.stabilizerArrow H).base y)
    (T : BigFppfOver C S hS) (x : (G.realization C hS hGU hGR hGP).objects.obj.obj (op T))
    (hx : IsOverPoint C hS hGU hGR hGP ((eqToHom e.symm).left.base u) T x) :
    Function.Bijective (Functor.verticalAutMap
      (Stack.quotientStackMap (realization C hS φ hGU hGR hGP hHU hHR hHP)).toFunctor
      (Stack.quotientStackMap (realization C hS φ hGU hGR hGP hHU hHR hHP)).w
      ((Stack.pointwiseToQuotientStackFiber (G.realization C hS hGU hGR hGP) T).obj x).1) := by
  have : Mono φ.mapArrows :=
    (Over.forget S).mono_of_mono_map (inferInstance : Mono φ.mapArrows.left)
  have := Stack.faithful_quotientStackMap_of_mono (realization C hS φ hGU hGR hGP hHU hHR hHP)
    (mono_realization_mapArrows C hS φ hGU hGR hGP hHU hHR hHP)
  refine ⟨fun α β h => ?_, surjective_verticalAutMap_quotientStackMap_realization C hS φ hGU hGR
    hGP hHU hHR hHP e hφ u hstab T x hx⟩
  exact Subtype.ext <| Iso.ext <| (Stack.quotientStackMap _).toFunctor.map_injective
    (congrArg (fun z => (z : Aut _).hom) (congrArg Subtype.val h))

end Stacks.Groupoids.GroupoidScheme.Hom

end
