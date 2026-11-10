module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechTermMate
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionFace
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent

/-!
# The augmentation of the simplex-coefficient resolution on the identity-labelled summand

Let `S` be a simplicial-site situation and `F` an abelian sheaf on its total site. Over the
component of simplicial degree `0`, the degree-`0` term of the simplex-coefficient resolution of
Stacks 0D78 carries the distinguished summand labelled by the identity simplex map
(`CategoryTheory.SimplicialSiteSituation.componentPresheafInclusion'`), and the augmentation of
that resolution sums the summands by the identity of `F`. So the identity-labelled summand
followed by the augmentation is the identity.

This is the degree-zero companion of
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationResolutionFace.lean`, which says what
the *simplicial structure maps* do to the identity-labelled summand. It is the resolution-side
input to the mate identity for the cone leg of the complex of Stacks 0D79 — the companion of
`CategoryTheory.SimplicialSiteSituation.Augmentation.homEquiv_degIso_inv_comp_barSimplicial_map'`,
which is that identity for a cosimplicial transition.

Transposed along `g_{0!} ⊣ g_0^{-1}`, that says that the transpose of the augmentation of
Stacks 0D78, read through the degree-`0` identification of its term with `g_{0!}(a_0⁻¹𝒢)`, is the
restriction comparison of Stacks 0D70, compatibility (b), and nothing more.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentPresheafInclusion_comp_augmentation`: the
  statement above, on sections.
* `CategoryTheory.SimplicialSiteSituation.toSheafify_comp_barAugmentation`: the sheafification
  unit followed by the augmentation of the resolution is the presheaf-level augmentation.
* `CategoryTheory.SimplicialSiteSituation.componentSheafInclusion_comp_barAugmentation`: the
  sheafified form — the identity-labelled summand inclusion followed by the augmentation of the
  resolution is the identity.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.homEquiv_degIso_inv_comp_barAugmentation`: **the transpose of the augmentation of
  Stacks 0D78 is the restriction comparison of Stacks 0D70.**
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.homEquiv_comp_abelianCechConeNatTrans_app`: **the leg in simplicial degree `n` of a
  transpose along `a⁻¹ ⊣ a_*` is the transpose of the restriction to that degree**, the abelian
  form of `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.inverseImageTranspose_comp_projection`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.conjugateEquiv_abelianCechConeNatTrans_app_app`: **the mate of the cone leg of the complex of
  Stacks 0D79 is the augmentation of the resolution of Stacks 0D78** — the degree-zero companion
  of `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.conjugateEquiv_abelianCosimplicialPushforward_map_app'`.

## Implementation notes

`CategoryTheory.Limits.Sigma.desc` and `.ι` are written out with their namespace: the summand
maps of the simplex-coefficient diagram are coproduct maps, and unqualified `Sigma.desc` resolves
to the functor-sigma one and fails to elaborate.

The computation lives at the presheaf level — the augmentation is `Sigma.desc (fun _ => 𝟙)` on
sections, so the identity is `Sigma.ι_desc`. The sheafified form needs two more inputs, because
the augmentation of the resolution is normalised to land in `F` itself rather than in its
sheafification and so carries the counit of the sheafification adjunction: the naturality of
`toSheafify`, and `(sheafificationAdjunction _ _).right_triangle_components` to collapse the unit
followed by the counit.

`toSheafify_comp_barAugmentation` is proved by a chain of `Eq.trans` and `congrArg` rather than by
`rw`. Both available rewrites fail silently here: the goal arrives already left-associated, so
`← Category.assoc` fires at the wrong site, and the naturality square and the right triangle are
each stated at a spelling of `toSheafify` that is only definitionally the one in the goal — the
naturality square at `(SimplicialObject.const _).obj F.obj _⦋0⦌` and the right triangle at
`(sheafToPresheaf _ _).obj F`.

The transposition is the same rewrite as `homEquiv_degIso_inv_comp_barSimplicial_map'`, minus the
`Functor.map_comp` step that one needs for the summand factor.

`homEquiv_comp_abelianCechConeNatTrans_app` is proved on underlying sheaves of sets, where
`inverseImageTranspose_comp_projection` is the statement and the cone leg is literally the leg of
the defining limit of Stacks 0D70, part (2). Two spelling steps are needed to get there: the
abelian transposition forgets to the geometric one
(`Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_homEquiv_forget`), and the
geometric transposition of Stacks 0D70, part (2), is built by `Adjunction.mkOfHomEquiv`, so
`Adjunction.mkOfHomEquiv_homEquiv` is what identifies `(totalMorphismOfTopoi S D K a).adj.homEquiv`
with `inverseImageTranspose`. That identification is taken with its two object arguments written
out: left to unification they are solved from the morphism being transposed and come out as
objects of the wrong category.

`conjugateEquiv_abelianCechConeNatTrans_app_app` follows
`conjugateEquiv_abelianCosimplicialPushforward_map_app'` line for line, with the identity of `a⁻¹𝒢`
where that one has the identity of a term of the resolution, so that `Adjunction.homEquiv_id`
supplies the unit of `a⁻¹ ⊣ a_*`. Its last step — cancelling the identity that
`CategoryTheory.Functor.map_id` leaves behind — is taken as a `congrArg` term: `rw`'s motive for
`Category.comp_id` there is rejected, because the identity sits at
`(componentInverseImageAb S D K a ⦋0⦌).obj 𝒢` while the transposition that surrounds it is anchored
at `Sites.abelianInverseImage (componentAugmentation S D K a ⦋0⦌)`, and the two spellings of that
one object are only definitionally equal.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (F : Sheaf S.totalTopology Ab.{u})

/-- On sections over an object of the component of degree `0`, the summand of the degree-`0` term
of the simplex-coefficient presheaf labelled by the identity, followed by the augmentation, is the
identity: the augmentation sums the summands by the identity of `F`. -/
theorem componentPresheafInclusion_comp_augmentation (U : S.component ⦋0⦌) :
    (componentPresheafInclusion' S F ⦋0⦌).app (Opposite.op U) ≫
        ((simplexCoefficientAugmentation' ((totalSimplexDegree S).leftOp) F.obj).app
          (Opposite.op ⦋0⦌)).app
            (Opposite.op ((S.componentFunctor ⦋0⦌).obj U)) =
      𝟙 (F.obj.obj (Opposite.op ((S.componentFunctor ⦋0⦌).obj U))) := by
  change Limits.Sigma.ι _ (eqToHom
        (totalSimplexDegree_leftOp_obj_op_componentFunctor_obj S ⦋0⦌ U).symm) ≫
      Limits.Sigma.desc (fun _ => 𝟙 (F.obj.obj
        (Opposite.op ((S.componentFunctor ⦋0⦌).obj U)))) = _
  exact Limits.Sigma.ι_comp_desc _ _

/-- The sheafification unit followed by the augmentation of the simplex-coefficient resolution is
the presheaf-level augmentation: the augmentation is normalised through the counit of the
sheafification adjunction, and the right triangle of that adjunction collapses the unit followed
by the counit. -/
theorem toSheafify_comp_barAugmentation (U : S.component ⦋0⦌) :
    (toSheafify S.totalTopology
          (((simplexCoefficientDiagram' ((totalSimplexDegree S).leftOp)).obj F.obj).obj
            (Opposite.op ⦋0⦌))).app
        (Opposite.op ((S.componentFunctor ⦋0⦌).obj U)) ≫
      ((S.restrictAb ⦋0⦌).map (barAugmentation' S F)).hom.app (Opposite.op U) =
    ((simplexCoefficientAugmentation' ((totalSimplexDegree S).leftOp) F.obj).app
      (Opposite.op ⦋0⦌)).app (Opposite.op ((S.componentFunctor ⦋0⦌).obj U)) := by
  have hnat := congr_app (toSheafify_naturality S.totalTopology
    ((simplexCoefficientAugmentation' ((totalSimplexDegree S).leftOp) F.obj).app (Opposite.op ⦋0⦌)))
    (Opposite.op ((S.componentFunctor ⦋0⦌).obj U))
  have htri := congr_app
    ((sheafificationAdjunction S.totalTopology Ab.{u}).right_triangle_components F)
    (Opposite.op ((S.componentFunctor ⦋0⦌).obj U))
  simp only [NatTrans.comp_app] at hnat
  change (toSheafify S.totalTopology _).app _ ≫
      (sheafifyMap S.totalTopology
          ((simplexCoefficientAugmentation' ((totalSimplexDegree S).leftOp) F.obj).app
            (Opposite.op ⦋0⦌))).app _ ≫
        ((sheafificationAdjunction S.totalTopology Ab.{u}).counit.app F).hom.app _ = _
  refine Eq.trans (congrArg (fun g => g ≫
      ((sheafificationAdjunction S.totalTopology Ab.{u}).counit.app F).hom.app
        (Opposite.op ((S.componentFunctor ⦋0⦌).obj U))) hnat.symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun g =>
      ((simplexCoefficientAugmentation' ((totalSimplexDegree S).leftOp) F.obj).app
          (Opposite.op ⦋0⦌)).app (Opposite.op ((S.componentFunctor ⦋0⦌).obj U)) ≫ g) htri) ?_
  exact Category.comp_id _

/-- **The identity-labelled summand inclusion followed by the augmentation of the resolution of
Stacks 0D78 is the identity.** -/
theorem componentSheafInclusion_comp_barAugmentation :
    (componentSheafInclusion' S ⦋0⦌).app F ≫ (S.restrictAb ⦋0⦌).map (barAugmentation' S F) =
      𝟙 ((S.restrictAb ⦋0⦌).obj F) := by
  apply (sheafToPresheaf (S.componentTopology ⦋0⦌) Ab.{u}).map_injective
  apply NatTrans.ext
  funext Y
  obtain ⟨U⟩ := Y
  change ((componentSheafInclusion' S ⦋0⦌).app F).hom.app (Opposite.op U) ≫
      ((S.restrictAb ⦋0⦌).map (barAugmentation' S F)).hom.app (Opposite.op U) = 𝟙 _
  refine Eq.trans (congrArg (fun g => g ≫
      ((S.restrictAb ⦋0⦌).map (barAugmentation' S F)).hom.app (Opposite.op U))
      (componentSheafInclusion_hom_app' S F ⦋0⦌ U)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun g =>
      (componentPresheafInclusion' S F ⦋0⦌).app (Opposite.op U) ≫ g)
      (toSheafify_comp_barAugmentation S F U)) ?_
  exact componentPresheafInclusion_comp_augmentation S F U

namespace Augmentation

variable (D : Cat.{u, u}) (K : GrothendieckTopology ↑D) (a : S.Augmentation D K)
  (G : Sheaf K Ab.{u})

/-- **The transpose of the augmentation of Stacks 0D78 is the restriction comparison of
Stacks 0D70.** The transpose along `g_{0!} ⊣ g_0^{-1}` of the augmentation of the resolution,
read through the degree-`0` identification of its term with `g_{0!}(a_0⁻¹𝒢)`, is the restriction
comparison of Stacks 0D70, compatibility (b), and nothing more — there is no summand factor,
unlike the companion statement at a cosimplicial transition. -/
theorem homEquiv_degIso_inv_comp_barAugmentation :
    (S.componentLowerShriekAbAdjunction' ⦋0⦌).homEquiv
        ((componentInverseImageAb S D K a ⦋0⦌).obj G) ((totalInverseImageAb S D K a).obj G)
        ((degIso' S D K a G 0).inv ≫
          barAugmentation' S ((totalInverseImageAb S D K a).obj G)) =
      (componentRestrictionAbInverseImageIso' S D K a G ⦋0⦌).inv := by
  rw [degIso_inv', Category.assoc, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right,
    show (S.componentLowerShriekAbAdjunction' ⦋0⦌).homEquiv
        ((S.restrictAb ⦋0⦌).obj ((totalInverseImageAb S D K a).obj G))
        (((barSimplicial' S).obj ((totalInverseImageAb S D K a).obj G)).obj (Opposite.op ⦋0⦌))
        ((componentLowerShriekMap' S ⦋0⦌).app ((totalInverseImageAb S D K a).obj G)) =
      (componentSheafInclusion' S ⦋0⦌).app ((totalInverseImageAb S D K a).obj G) from
      ((S.componentLowerShriekAbAdjunction' ⦋0⦌).homEquiv _ _).apply_symm_apply _,
    componentSheafInclusion_comp_barAugmentation, Category.comp_id]

variable [HasSheafify K Ab.{u}]

/-- **The legs of a transpose along the total augmentation are the transposes of its
restrictions, on abelian sheaves.** The transpose along `a⁻¹ ⊣ a_*` of a morphism out of
`a⁻¹𝒢`, followed by the leg of the cone of Stacks 0D70, part (2), in simplicial degree `n`, is
the transpose along `a_n⁻¹ ⊣ a_{n,*}` of the restriction of that morphism to the component of
degree `n`, read through the restriction comparison of Stacks 0D70, compatibility (b), and
corrected by the comparison of Stacks 04DB. -/
theorem homEquiv_comp_abelianCechConeNatTrans_app (Y : Sheaf S.totalTopology Ab.{u})
    (α : (totalInverseImageAb S D K a).obj G ⟶ Y) (n : SimplexCategory) :
    (abelianTotalAdjunction S D K a).homEquiv G Y α ≫
        ((abelianCechConeNatTrans S D K a).app n).app Y =
      (abelianInverseImageAdjPushforward (S.componentTopology n)
            (componentAugmentation S D K a n)).homEquiv G ((S.restrictAb n).obj Y)
          ((componentRestrictionAbInverseImageIso' S D K a G n).inv ≫
            (S.restrictAb n).map α) ≫
        (abelianComponentPushforwardIso S D K a n).inv.app Y := by
  apply Functor.map_injective (sheafCompose K (forget Ab.{u}))
  have hleg : (sheafCompose K (forget Ab.{u})).map
        (((abelianCechConeNatTrans S D K a).app n).app Y) =
      pushforwardProjection S D K a
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj Y) n :=
    rfl
  have hcore : (totalMorphismOfTopoi S D K a).adj.homEquiv
        ((sheafCompose K (forget Ab.{u})).obj G)
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj Y) =
      homEquiv S D K a ((sheafCompose K (forget Ab.{u})).obj G)
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj Y) :=
    congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _
  have hTot : (sheafCompose K (forget Ab.{u})).map
        ((abelianTotalAdjunction S D K a).homEquiv G Y α) =
      inverseImageTranspose S D K a
        ((sheafCompose S.totalTopology (forget Ab.{u})).map α) := by
    refine Eq.trans (abelianInverseImageAdjPushforward_homEquiv_forget S.totalTopology
      (totalMorphismOfTopoi S D K a) G Y α) ?_
    exact congrArg (fun (e : _ ≃ _) => e ((sheafCompose S.totalTopology (forget Ab.{u})).map α))
      hcore
  have hmid : inverseImageTranspose S D K a
          ((sheafCompose S.totalTopology (forget Ab.{u})).map α) ≫
        pushforwardProjection S D K a
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj Y) n =
      (componentAugmentation S D K a n).adj.homEquiv
        ((sheafCompose K (forget Ab.{u})).obj G) _
        ((componentRestrictionIso S D K a ((sheafCompose K (forget Ab.{u})).obj G) n).inv ≫
          (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
            ((S.restrictAb n).map α)) :=
    inverseImageTranspose_comp_projection S D K a
      ((sheafCompose S.totalTopology (forget Ab.{u})).map α) n
  refine Eq.trans ((sheafCompose K (forget Ab.{u})).map_comp _ _) ?_
  refine Eq.trans (congrArg (fun t => t ≫ (sheafCompose K (forget Ab.{u})).map
      (((abelianCechConeNatTrans S D K a).app n).app Y)) hTot) ?_
  refine Eq.trans (congrArg (fun t => inverseImageTranspose S D K a
      ((sheafCompose S.totalTopology (forget Ab.{u})).map α) ≫ t) hleg) ?_
  refine hmid.trans ?_
  refine Eq.trans (forget_abelianHomEquiv_comp' S D K a G Y n ((S.restrictAb n).map α)).symm ?_
  refine Eq.trans (Category.comp_id _).symm ?_
  refine Eq.trans (congrArg (fun t => (sheafCompose K (forget Ab.{u})).map
      ((abelianInverseImageAdjPushforward (S.componentTopology n)
            (componentAugmentation S D K a n)).homEquiv G ((S.restrictAb n).obj Y)
          ((componentRestrictionAbInverseImageIso' S D K a G n).inv ≫
            (S.restrictAb n).map α)) ≫ t)
    (abelianComponentPushforwardIso_inv_forget S D K a n Y).symm) ?_
  exact ((sheafCompose K (forget Ab.{u})).map_comp _ _).symm

/-- **The mate of the cone leg of the complex of Stacks 0D79 is the augmentation of the
resolution of Stacks 0D78.** The degree-`0` term of the complex is a right adjoint whose left
adjoint is the degree-`0` term of the resolution (`cechTermAdjunction`), and the direct image
`a_*` along the total augmentation is a right adjoint whose left adjoint is `a⁻¹`; this says that
the conjugate, along those two adjunctions, of the degree-`0` leg of the cone of Stacks 0D70,
part (2), is the augmentation of the resolution, read through the degree-`0` identification of
its term. -/
theorem conjugateEquiv_abelianCechConeNatTrans_app_app :
    ((conjugateEquiv (abelianTotalAdjunction S D K a)
          (cechTermAdjunction S D K a ⦋0⦌)).symm
        ((abelianCechConeNatTrans S D K a).app ⦋0⦌ :
          abelianTotalPushforward S D K a ⟶
            abelianComponentPushforward S D K a ⦋0⦌)).app G =
      (degIso' S D K a G 0).inv ≫
        barAugmentation' S ((totalInverseImageAb S D K a).obj G) := by
  have hc := Stacks.CategoryTheory.homEquiv_conjugate (abelianTotalAdjunction S D K a)
    (cechTermAdjunction S D K a ⦋0⦌)
    ((abelianCechConeNatTrans S D K a).app ⦋0⦌ :
      abelianTotalPushforward S D K a ⟶ abelianComponentPushforward S D K a ⦋0⦌)
    (X := G) (𝟙 ((totalInverseImageAb S D K a).obj G))
  have hc' : (cechTermAdjunction S D K a ⦋0⦌).homEquiv G
        ((totalInverseImageAb S D K a).obj G)
        (((conjugateEquiv (abelianTotalAdjunction S D K a)
              (cechTermAdjunction S D K a ⦋0⦌)).symm
            ((abelianCechConeNatTrans S D K a).app ⦋0⦌ :
              abelianTotalPushforward S D K a ⟶
                abelianComponentPushforward S D K a ⦋0⦌)).app G) =
      (abelianTotalAdjunction S D K a).homEquiv G ((totalInverseImageAb S D K a).obj G)
          (𝟙 ((totalInverseImageAb S D K a).obj G)) ≫
        ((abelianCechConeNatTrans S D K a).app ⦋0⦌).app
          ((totalInverseImageAb S D K a).obj G) :=
    (congrArg ((cechTermAdjunction S D K a ⦋0⦌).homEquiv G
      ((totalInverseImageAb S D K a).obj G)) (Category.comp_id _).symm).trans hc
  refine ((cechTermAdjunction S D K a ⦋0⦌).homEquiv G
    ((totalInverseImageAb S D K a).obj G)).injective (hc'.trans ?_)
  rw [cechTermAdjunction_homEquiv_apply', homEquiv_degIso_inv_comp_barAugmentation,
    homEquiv_comp_abelianCechConeNatTrans_app, CategoryTheory.Functor.map_id]
  exact congrArg (fun t => (abelianInverseImageAdjPushforward (S.componentTopology ⦋0⦌)
        (componentAugmentation S D K a ⦋0⦌)).homEquiv G
        ((S.restrictAb ⦋0⦌).obj ((totalInverseImageAb S D K a).obj G)) t ≫
      (abelianComponentPushforwardIso S D K a ⦋0⦌).inv.app
        ((totalInverseImageAb S D K a).obj G))
    (Category.comp_id (componentRestrictionAbInverseImageIso' S D K a G ⦋0⦌).inv)

end Augmentation

end CategoryTheory.SimplicialSiteSituation

end
