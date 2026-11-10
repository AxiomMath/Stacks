module

public import StacksFrontier.Topology.Simplicial.AugmentationSections
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.SiteFunctor

/-!
# The quasi-compact and the Zariski topos of a simplicial space

Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces
and let `a : U → X` be an augmentation. Stacks Lemma 0DAF compares two topoi attached to `U`: the
topos of the total site `(LC_qc/U)_total` of Stacks Section 09X8, and the topos of the site
`U_Zar` of simplicial opens of the underlying simplicial space. There is a commutative diagram

```
Sh((LC_qc/U)_total) --h--> Sh(U_Zar)
        | a_qc                 | a
Sh(LC_qc/X)       --h₋₁--> Sh(X)
```

whose left vertical arrow is the augmentation of Section 09X8, whose right vertical arrow is
the augmentation of Tag 09W4, and whose horizontal arrows are the morphisms of topoi of the
open-subset functors `V ↦ V/U_n` and `V ↦ V/X` of Cohomology on Sites, Section 21.31.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonSquarePushforwardIso`:
  **Stacks 0DAF**, the square commutes on direct images.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonSquareInverseImageIso`: the
  same square on inverse images.

## Implementation notes

The source deduces the lemma from the formal commutation of total morphisms with augmentations
(Stacks 0D99). Here it is computed directly on sections. For a sheaf `F` on the total site and
an open `Ω ⊆ X`, going around the top gives `lim_{[n] ∈ Δ} F(a_n⁻¹(Ω)/U_n)` by the description of
the direct image of Tag 09W4 on sections, and going around the bottom gives the value at `Ω/X`
of the right Kan extension of `F` along `V/U_n ↦ V/X`, a limit over all objects of the total
site mapping to `Ω/X`. The objects `a_n⁻¹(Ω)/U_n` are initial among those: an object `V/U_k` of
the total site mapping to `Ω/X` maps uniquely, in its own simplicial degree, to
`a_k⁻¹(Ω)/U_k`, because `Ω/X` is a monomorphism. So the two limits agree.

Commutativity of a square of morphisms of topoi is expressed by natural isomorphisms of the
composite direct-image and inverse-image functors, as in Tags 0D98 and 0D99.

The sheaves of sets take values in the universe of the spaces, which is where the sheaves of
sets on the topological spaces of the right-hand column, and the augmentation of Tag 09W4,
live. The quasi-compact topoi of the left-hand column can be formed there because the sites
`LC_qc/X` and `(LC_qc/U)_total` are essentially small in that universe
(`essentiallySmall_over`, `essentiallySmall_qcTotal`).

## References

* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.SemiRepresentable.Simplicial
open Stacks.CategoryTheory.Hypercovering Stacks.Topology.Simplicial

universe x u w

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
  (U : SimplicialObject S.category) {X : S.category}
  (a : U ⟶ (SimplicialObject.const S.category).obj X)

section OpensSlice

variable {S}

/-- Morphisms into the open immersion `Ω → X`, viewed as an object of `LC_qc/X`, are unique. -/
theorem opensToSlice_hom_subsingleton (Ω : Opens X.obj) {Z : Over X}
    (f g : Z ⟶ (S.opensToSlice X).1.obj Ω) : f = g :=
  Over.OverMorphism.ext (opensToSlice_hom_ext X Ω ((Over.w f).trans (Over.w g).symm))

/-- An object of `LC_qc/X` whose structure map lands in `Ω` maps to the open immersion
`Ω → X`. -/
def toOpensSlice (Ω : Opens X.obj) (Z : Over X) (h : ∀ z, Z.hom z ∈ Ω) :
    Z ⟶ (S.opensToSlice X).1.obj Ω :=
  Over.homMk (opensFactor X Ω Z.hom h) (opensFactor_comp X Ω Z.hom h)

end OpensSlice

/-- The simplicial opens `a_n⁻¹(Ω)/U_n` of the total site, as a cosimplicial diagram in the
opposite of `(LC_qc/U)_total`, functorially in `Ω`. -/
abbrev totalOpensDiagram : (Opens X.obj)ᵒᵖ ⥤ SimplexCategory ⥤ (qcTotal.{x} S U a)ᵒᵖ :=
  augmentationOpensDiagram (simplicialSpace S U) ((toTop S).obj X) (spaceAugmentation S U a) ⋙
    (Functor.whiskeringRight _ _ _).obj (siteFunctor.{x} S U a).op

/-- The object `a_n⁻¹(Ω)/U_n` of the total site maps to `Ω/X` under `V/U_n ↦ V/X`. -/
def totalOpensToSlice (Ω : Opens X.obj) (n : SimplexCategory) :
    (qcTotalForget.{x} S U a).obj (((totalOpensDiagram.{x} S U a).obj (op Ω)).obj n).unop ⟶
      (S.opensToSlice X).1.obj Ω :=
  toOpensSlice Ω _ (fun z => by
    change ((simplicialOpenSlice S U _).hom ≫ a.app (op n)) z ∈ Ω
    exact mem_of_factors (U.obj (op n)) _ (𝟙 _) z)

/-- The simplicial opens `a_n⁻¹(Ω)/U_n`, as objects of the category of objects of the total site
over `Ω/X`. -/
def totalOpensArrow (Ω : Opens X.obj) :
    SimplexCategory ⥤
      StructuredArrow (op ((S.opensToSlice X).1.obj Ω)) (qcTotalForget.{x} S U a).op where
  obj n := StructuredArrow.mk (Y := ((totalOpensDiagram.{x} S U a).obj (op Ω)).obj n)
    (totalOpensToSlice.{x} S U a Ω n).op
  map φ := StructuredArrow.homMk (((totalOpensDiagram.{x} S U a).obj (op Ω)).map φ)
    (Quiver.Hom.unop_inj (opensToSlice_hom_subsingleton Ω _ _))
  map_id n := StructuredArrow.hom_ext _ _ (((totalOpensDiagram.{x} S U a).obj (op Ω)).map_id n)
  map_comp φ ψ := StructuredArrow.hom_ext _ _
    (((totalOpensDiagram.{x} S U a).obj (op Ω)).map_comp φ ψ)

/-- The objects `a_n⁻¹(Ω)/U_n` are initial among the objects of the total site over `Ω/X`: an
object `V/U_k` over `Ω/X` maps, in its own simplicial degree, to `a_k⁻¹(Ω)/U_k`, and every other
map to some `a_n⁻¹(Ω)/U_n` factors uniquely through that one. -/
instance totalOpensArrow_initial (Ω : Opens X.obj) :
    (totalOpensArrow.{x} S U a Ω).Initial where
  out d := by
    let Z := d.right.unop
    let P : SimplicialOpen (simplicialSpace S U) :=
      augmentationOpen (simplicialSpace S U) ((toTop S).obj X) (spaceAugmentation S U a) Ω Z.right
    have hZ : ∀ z, (structureMap Z ≫ U.map (𝟙 Z.right)) z ∈ P.toOpens := fun z => by
      change ((structureMap Z ≫ U.map (𝟙 Z.right)) ≫ a.app Z.right) z ∈ Ω
      rw [CategoryTheory.Functor.map_id, Category.comp_id, structureMap_comp_app]
      have h : d.hom.unop.left ≫ ((S.opensToSlice X).1.obj Ω).hom = Z.left.hom :=
        Over.w d.hom.unop
      rw [← h]
      exact mem_of_factors X Ω _ z
    let t : CostructuredArrow (totalOpensArrow.{x} S U a Ω) d :=
      CostructuredArrow.mk (Y := Z.right.unop)
        (StructuredArrow.homMk (toSiteFunctor Z P (𝟙 _) hZ).op
          (Quiver.Hom.unop_inj (opensToSlice_hom_subsingleton Ω _ _)))
    refine isConnected_of_isTerminal _ (x := t) (IsTerminal.ofUniqueHom
      (fun s : CostructuredArrow (totalOpensArrow.{x} S U a Ω) d =>
        CostructuredArrow.homMk s.hom.right.unop.right.unop (by
        apply StructuredArrow.hom_ext
        apply Quiver.Hom.unop_inj
        apply siteFunctor_hom_ext
        change 𝟙 _ ≫ s.hom.right.unop.right = s.hom.right.unop.right
        exact Category.id_comp _))
      (fun (s : CostructuredArrow (totalOpensArrow.{x} S U a Ω) d) m => ?_))
    apply CostructuredArrow.hom_ext
    have hm := congrArg (fun k => k.right.unop.right) (CostructuredArrow.w m)
    change 𝟙 _ ≫ (m.left).op = s.hom.right.unop.right at hm
    exact Quiver.Hom.op_inj ((Category.id_comp _).symm.trans hm)

/-- The comparison map from the value at `Ω/X` of the right Kan extension of a presheaf `G` on the
total site along `V/U_n ↦ V/X` to `lim_n G(a_n⁻¹(Ω)/U_n)`: the projections of the right Kan
extension to the objects `a_n⁻¹(Ω)/U_n` over `Ω/X`. -/
def ranSectionsMap (G : (qcTotal.{x} S U a)ᵒᵖ ⥤ Type u) (Ω : Opens X.obj) :
    ((qcTotalForget.{x} S U a).op.ran.obj G).obj (op ((S.opensToSlice X).1.obj Ω)) ⟶
      limit (((totalOpensDiagram.{x} S U a).obj (op Ω)) ⋙ G) :=
  limit.lift _ (((Functor.RightExtension.mk _ ((qcTotalForget.{x} S U a).op.ranCounit.app G)).coneAt
    (op ((S.opensToSlice X).1.obj Ω))).whisker (totalOpensArrow.{x} S U a Ω))

/-- The `n`-th component of the comparison map `ranSectionsMap` is the restriction of the right
Kan extension along `a_n⁻¹(Ω)/U_n → Ω/X` followed by the counit at `a_n⁻¹(Ω)/U_n`. -/
@[reassoc (attr := simp)]
theorem ranSectionsMap_π (G : (qcTotal.{x} S U a)ᵒᵖ ⥤ Type u) (Ω : Opens X.obj)
    (n : SimplexCategory) :
    ranSectionsMap.{x} S U a G Ω ≫ limit.π _ n =
      ((qcTotalForget.{x} S U a).op.ran.obj G).map (totalOpensToSlice.{x} S U a Ω n).op ≫
        ((qcTotalForget.{x} S U a).op.ranCounit.app G).app
          (((totalOpensDiagram.{x} S U a).obj (op Ω)).obj n) :=
  limit.lift_π _ _

/-- The comparison map is an isomorphism: the right Kan extension is a limit over all objects
of the total site over `Ω/X`, and the objects `a_n⁻¹(Ω)/U_n` are initial among them. -/
instance isIso_ranSectionsMap (G : (qcTotal.{x} S U a)ᵒᵖ ⥤ Type u)
    (Ω : Opens X.obj) : IsIso (ranSectionsMap.{x} S U a G Ω) := by
  let c := ((Functor.RightExtension.mk _ ((qcTotalForget.{x} S U a).op.ranCounit.app G)).coneAt
    (op ((S.opensToSlice X).1.obj Ω)))
  have hc' : IsLimit (c.whisker (totalOpensArrow.{x} S U a Ω)) :=
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm
      ((qcTotalForget.{x} S U a).op.isPointwiseRightKanExtensionRanCounit G _)
  exact (hc'.conePointUniqueUpToIso (limit.isLimit _)).isIso_hom

variable {S U a} in
/-- The comparison map `ranSectionsMap` is natural in the open `Ω` of `X`. -/
theorem ranSectionsMap_naturality (G : (qcTotal.{x} S U a)ᵒᵖ ⥤ Type u) {Ω Ω' : (Opens X.obj)ᵒᵖ}
    (g : Ω ⟶ Ω') :
    ((qcTotalForget.{x} S U a).op.ran.obj G).map ((S.opensToSlice X).1.op.map g) ≫
        ranSectionsMap.{x} S U a G Ω'.unop =
      ranSectionsMap.{x} S U a G Ω.unop ≫
        limMap (Functor.whiskerRight ((totalOpensDiagram.{x} S U a).map g) G) := by
  refine limit.hom_ext fun n => ?_
  let c := ((totalOpensDiagram.{x} S U a).obj Ω).obj n
  let c' := ((totalOpensDiagram.{x} S U a).obj Ω').obj n
  let k : c ⟶ c' := ((totalOpensDiagram.{x} S U a).map g).app n
  let R := (qcTotalForget.{x} S U a).op.ran.obj G
  let ε := (qcTotalForget.{x} S U a).op.ranCounit.app G
  have hnat : ε.app c ≫ G.map k = R.map ((qcTotalForget.{x} S U a).op.map k) ≫ ε.app c' :=
    (ε.naturality k).symm
  rw [Category.assoc, ranSectionsMap_π, Category.assoc, limMap_π,
    ← Category.assoc (ranSectionsMap.{x} S U a G Ω.unop), ranSectionsMap_π,
    Functor.whiskerRight_app, Category.assoc]
  change R.map _ ≫ R.map _ ≫ ε.app c' = R.map _ ≫ ε.app c ≫ G.map k
  rw [hnat, ← Category.assoc, ← Category.assoc, ← R.map_comp, ← R.map_comp]
  congr 2
  exact Quiver.Hom.unop_inj (opensToSlice_hom_subsingleton Ω.unop _ _)

variable {S U a} in
/-- The comparison map `ranSectionsMap` is natural in the presheaf `G` on the total site. -/
theorem ranSectionsMap_naturality_presheaf {G G' : (qcTotal.{x} S U a)ᵒᵖ ⥤ Type u} (α : G ⟶ G')
    (Ω : Opens X.obj) :
    ((qcTotalForget.{x} S U a).op.ran.map α).app (op ((S.opensToSlice X).1.obj Ω)) ≫
        ranSectionsMap.{x} S U a G' Ω =
      ranSectionsMap.{x} S U a G Ω ≫
        limMap (Functor.whiskerLeft ((totalOpensDiagram.{x} S U a).obj (op Ω)) α) := by
  refine limit.hom_ext fun n => ?_
  rw [Category.assoc, ranSectionsMap_π, Category.assoc, limMap_π,
    ← Category.assoc (ranSectionsMap.{x} S U a G Ω), ranSectionsMap_π, Functor.whiskerLeft_app,
    ← NatTrans.naturality_assoc]
  have h := NatTrans.congr_app ((qcTotalForget.{x} S U a).op.ranCounit.naturality α)
    (((totalOpensDiagram.{x} S U a).obj (op Ω)).obj n)
  simp only [NatTrans.comp_app, Functor.comp_map, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, Functor.id_map] at h
  exact congrArg (_ ≫ ·) h

/-- The value at `Ω/X` of the right Kan extension of a presheaf `G` on the total site along
`V/U_n ↦ V/X` is `lim_n G(a_n⁻¹(Ω)/U_n)`, naturally in `G` and `Ω`. -/
def ranSectionsIso :
    (qcTotalForget.{x} S U a).op.ran ⋙ (Functor.whiskeringLeft _ _ (Type u)).obj
        (S.opensToSlice X).1.op ≅
      (Functor.whiskeringLeft _ _ (Type u)).obj (siteFunctor.{x} S U a).op ⋙
        augmentationSections (simplicialSpace S U) ((toTop S).obj X) (spaceAugmentation S U a) :=
  NatIso.ofComponents
    (fun G => NatIso.ofComponents
      (fun Ω => @asIso _ _ _ _ _ (isIso_ranSectionsMap.{x} S U a G Ω.unop))
      (fun g => ranSectionsMap_naturality G g))
    (fun α => NatTrans.ext (funext fun Ω => ranSectionsMap_naturality_presheaf α Ω.unop))

/-- The square of Stacks 0DAF on direct images, read on underlying presheaves. -/
def comparisonSquarePresheafIso :
    ((totalComparisonMorphism.{x} S U a).pushforward ⋙
        (augmentationMorphism (simplicialSpace S U) ((toTop S).obj X)
          (spaceAugmentation S U a)).pushforward) ⋙
        sheafToPresheaf (Opens.grothendieckTopology ((toTop S).obj X)) (Type u) ≅
      ((qcAugmentation.{x} S U a).pushforward ⋙
        (qcTopologicalMorphism.{u, w, 0} S X).pushforward) ⋙
        sheafToPresheaf (Opens.grothendieckTopology ((toTop S).obj X)) (Type u) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (totalComparisonMorphism.{x} S U a).pushforward
      (augmentationMorphism_pushforward_sectionsIso (simplicialSpace S U) ((toTop S).obj X)
        (spaceAugmentation S U a)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((siteFunctor.{x} S U a).sheafPushforwardContinuousCompSheafToPresheafIso (Type u) _ _)
      (augmentationSections (simplicialSpace S U) ((toTop S).obj X)
        (spaceAugmentation S U a)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (qcTotalTopology.{x} S U a) (Type u))
      (ranSectionsIso.{x} S U a).symm ≪≫
    Iso.refl _

/-- **Stacks Tag 0DAF.** Let `U` be a simplicial object of `LC` and let `a : U → X` be an
augmentation. There is a commutative diagram of topoi

```
Sh((LC_qc/U)_total) --h--> Sh(U_Zar)
        | a_qc                 | a
Sh(LC_qc/X)       --h₋₁--> Sh(X)
```

where the left vertical arrow is the augmentation `qcAugmentation` of Stacks Section 09X8, the
right vertical arrow is the augmentation `augmentationMorphism` of Tag 09W4, the top arrow
`totalComparisonMorphism` is the morphism of topoi of the continuous functor
`U_Zar → (LC_qc/U)_total`, `V ↦ V/U_n`, and the bottom arrow `qcTopologicalMorphism` is the
comparison morphism of the continuous functor `X_Zar → LC_qc/X`, `V ↦ V/X`. Commutativity is
the natural isomorphism `a_* ∘ h_* ≅ h₋₁,* ∘ a_qc,*` of direct images. -/
@[stacks 0DAF]
def comparisonSquarePushforwardIso :
    (totalComparisonMorphism.{x} S U a).pushforward ⋙
        (augmentationMorphism (simplicialSpace S U) ((toTop S).obj X)
          (spaceAugmentation S U a)).pushforward ≅
      (qcAugmentation.{x} S U a).pushforward ⋙ (qcTopologicalMorphism.{u, w, 0} S X).pushforward :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology ((toTop S).obj X))
    (Type u)).whiskeringRight _).preimageIso (comparisonSquarePresheafIso.{x} S U a)

/-- The square of Stacks 0DAF on inverse images: the commutative square of
`comparisonSquarePushforwardIso` gives `a_qc⁻¹ ∘ h₋₁⁻¹ ≅ h⁻¹ ∘ a⁻¹`, by uniqueness of left
adjoints. -/
def comparisonSquareInverseImageIso :
    (qcTopologicalMorphism.{u, w, 0} S X).inverseImage ⋙ (qcAugmentation.{x} S U a).inverseImage ≅
      (augmentationMorphism (simplicialSpace S U) ((toTop S).obj X)
          (spaceAugmentation S U a)).inverseImage ⋙
        (totalComparisonMorphism.{x} S U a).inverseImage :=
  ((qcTopologicalMorphism.{u, w, 0} S X).adj.comp (qcAugmentation.{x} S U a).adj).leftAdjointUniq
    (((augmentationMorphism (simplicialSpace S U) ((toTop S).obj X)
        (spaceAugmentation S U a)).adj.comp
      (totalComparisonMorphism.{x} S U a).adj).ofNatIsoRight
        (comparisonSquarePushforwardIso.{x} S U a))

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
