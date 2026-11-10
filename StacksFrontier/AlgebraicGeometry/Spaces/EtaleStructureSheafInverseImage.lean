module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of the structure sheaf along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Stacks 03LV asserts that the inverse image of the structure sheaf of `Y` along
the morphism of small étale ringed topoi of Stacks 03G8 *is* the structure sheaf of `X`.  This
file proves it, in the form that the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` is an isomorphism.

The mechanism is the description of the inverse image of Stacks 03LP: postcomposition with `f`
carries an étale scheme chart of `X` to an étale scheme chart of `Y` with the same underlying
scheme, so restriction along `AlgebraicGeometry.Space.smallEtalePostcomp` carries the structure
sheaf of `Y` to the structure sheaf of `X` on the nose, and more generally a commutative diagram
of étale scheme charts over `f` is the same datum as a morphism of charts of `Y` out of the
postcomposite of its upper chart.  So the `f`-maps of Stacks 03G3 into a sheaf on the small
étale site of `X` are the homomorphisms into it from the restriction of the target sheaf
(`AlgebraicGeometry.Space.fMapRestrictionEquiv`), and the chart correspondence of Stacks 03G8
turns that into the statement that the structure map is a universal arrow, hence invertible.

## Main definitions

* `AlgebraicGeometry.Space.FMap.compSource` is an `f`-map followed by a morphism of the
  presheaves of sections on the source.
* `AlgebraicGeometry.Space.identityChartDiagram` is the diagram of étale scheme charts over an
  étale `f` whose upper chart is a given chart of `X`, whose lower chart is its postcomposite,
  and whose vertical morphism is the identity.
* `AlgebraicGeometry.Space.fMapRestrictionEquiv` identifies the `f`-maps of Stacks 03G3 along an
  étale morphism with the homomorphisms out of the restriction along postcomposition.
* `AlgebraicGeometry.Space.etaleStructureSheafIso` is the canonical isomorphism
  `f⁻¹𝒪_Y ≅ 𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_source_map` and
  `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_symm_app_map`: the chart
  correspondence of Stacks 03G8 is natural in the sheaf on the source.
* `AlgebraicGeometry.Space.isIso_fSharpInverseImage_of_isEtale`: for an étale morphism the
  inverse-image form of the structure map is an isomorphism.
* `AlgebraicGeometry.Space.etaleStructureSheafIso_hom`: its forward map is that structure map.

## Implementation notes

The naturality statement for the chart correspondence is proved through the geometric comparison
rather than from the chartwise characterization:
`AlgebraicGeometry.Space.descendedHomTypeU_source_map` generalizes
`AlgebraicGeometry.Space.descendedHomTypeU_map` from two presentations of one sheaf to a
morphism of presented sheaves, and
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_comparison` transfers it to the
chart correspondence itself.  Both halves are an application of
`AlgebraicGeometry.Space.descendedSectionTypeU_restrict`.

Invertibility is proved by exhibiting the structure map as a universal arrow:
`isIso_of_coyoneda_map_bijective` reduces it to the bijectivity of composition with it, and that
composition is identified with the inverse of the composite bijection

  `Hom(f⁻¹𝒪_Y, T) ≃ Hom(𝒪_Y, f_*T) ≃ FMap(T, 𝒪_Y) ≃ Hom(𝒪_X, T)`,

whose last factor uses that restricting the structure sheaf of `Y` along postcomposition gives
the structure sheaf of `X` definitionally.  The chartwise formula for the structure map,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_chart`, is what makes the composite of the
first two factors send the structure map to the identity: at the diagram with identity vertical
morphism it is pullback of regular functions along the identity.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-! ### Naturality of the chart correspondence in the sheaf on the source -/

/-- An `f`-map of Stacks 03G3 followed by a morphism of the presheaves of sections on the
source: on a diagram of charts it is the map of sections of the `f`-map followed by the
component of the morphism at the upper chart. -/
def FMap.compSource {P P' : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type v}
    {Q : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type w}
    (ξ : FMap B S hS X.1 Y.1 f.hom P Q) (α : P ⟶ P') :
    FMap B S hS X.1 Y.1 f.hom P' Q where
  app d s := α.app (op d.U) (ξ.app d s)
  naturality d d' i j h s := by
    rw [ξ.naturality d d' i j h s]
    exact NatTrans.naturality_apply α i.op (ξ.app d s)

/-- The sections map of `AlgebraicGeometry.Space.FMap.compSource`. -/
@[simp]
theorem FMap.compSource_app {P P' : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type v}
    {Q : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type w}
    (ξ : FMap B S hS X.1 Y.1 f.hom P Q) (α : P ⟶ P')
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : Q.obj (op d.V)) :
    (FMap.compSource B S hS f ξ α).app d s = α.app (op d.U) (ξ.app d s) :=
  rfl

/-- Morphisms of `Type`-valued sheaves are equal when they agree on every section. -/
private theorem sheaf_hom_ext_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type u)} {a b : F ⟶ G}
    (h : ∀ (U : Cᵒᵖ) (s : F.obj.obj U), a.hom.app U s = b.hom.app U s) : a = b := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply TypeCat.homEquiv.injective
  funext s
  exact h U s

/-- The homomorphism of sheaves attached to an `f`-map is natural in the sheaf on the source:
a morphism `α` of sheaves on the small étale site of `X`, presented by a morphism `φ` of
spaces-étale sheaves, carries the descended homomorphism of an `f`-map to the descended
homomorphism of its composite with `α`.

This generalizes `AlgebraicGeometry.Space.descendedHomTypeU_map`, which is the case of two
presentations of one and the same sheaf. -/
theorem descendedHomTypeU_source_map
    (F F' : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (H H' : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (i : F ≅ (smallEtaleComparisonRestriction B S hS X).obj H)
    (i' : F' ≅ (smallEtaleComparisonRestriction B S hS X).obj H')
    (α : F ⟶ F') (φ : H ⟶ H')
    (hφ : i.hom ≫ (smallEtaleComparisonRestriction B S hS X).map φ = α ≫ i'.hom)
    (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj) :
    descendedHomTypeU B S hS f F G H i ξ ≫
        (spacesDirectImageRestrictionTypeU B S hS f).map φ =
      descendedHomTypeU B S hS f F' G H' i' (FMap.compSource B S hS f ξ α.hom) := by
  refine sheaf_hom_ext_apply fun V s ↦ ?_
  obtain ⟨V⟩ := V
  refine spacesEtale_section_ext_charts B S hS X (chartBaseChange B S hS f V) H'
    (fun U k ↦ ?_)
  change H'.obj.map k.op
    (φ.hom.app _ (fMapDescendedSectionTypeU B S hS f F G H i ξ V s)) =
      H'.obj.map k.op (fMapDescendedSectionTypeU B S hS f F' G H' i'
        (FMap.compSource B S hS f ξ α.hom) V s)
  rw [← NatTrans.naturality_apply φ.hom k.op
    (fMapDescendedSectionTypeU B S hS f F G H i ξ V s)]
  refine (congrArg (fun t ↦ φ.hom.app (op ((comparisonFunctor B S hS X).obj U)) t)
    (descendedSectionTypeU_restrict B S hS f F G H i ξ U V k s)).trans ?_
  refine Eq.trans ?_ (descendedSectionTypeU_restrict B S hS f F' G H' i'
    (FMap.compSource B S hS f ξ α.hom) U V k s).symm
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun a ↦ a.hom) hφ) (op U)) _

/-- The chart correspondence of Stacks 03G8 is natural in the sheaf on the source, for a chosen
presentation of the two sheaves and a morphism of the presenting spaces-étale sheaves.

`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_source_map` is this without the
presentation data, which the comparison equivalence of Stacks 03G1 supplies. -/
theorem fMapEquivPushforwardHom_ringUniverse_source_map_of_presentation
    (F F' : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (H H' : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (i : F ≅ (smallEtaleComparisonRestriction B S hS X).obj H)
    (i' : F' ≅ (smallEtaleComparisonRestriction B S hS X).obj H')
    (α : F ⟶ F') (φ : H ⟶ H')
    (hφ : i.hom ≫ (smallEtaleComparisonRestriction B S hS X).map φ = α ≫ i'.hom)
    (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj) :
    fMapEquivPushforwardHom_ringUniverse B S hS f F' G
        (FMap.compSource B S hS f ξ α.hom) =
      fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map α := by
  refine (cancel_mono
    ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i'.hom ≫
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H')).mp ?_
  have hnat : (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
          ((smallEtaleComparisonRestriction B S hS X).map φ) ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H' =
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H ≫
        (spacesDirectImageRestrictionTypeU B S hS f).map φ :=
    (smallEtaleRingedToposHom_pushforward B S hS f).hom.naturality φ
  have hmid : ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H) ≫
      (spacesDirectImageRestrictionTypeU B S hS f).map φ =
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map α ≫
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i'.hom ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H' := by
    rw [Category.assoc, ← hnat,
      ← (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map_comp_assoc, hφ,
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map_comp_assoc]
  calc fMapEquivPushforwardHom_ringUniverse B S hS f F' G
          (FMap.compSource B S hS f ξ α.hom) ≫
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i'.hom ≫
          (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H')
      = descendedHomTypeU B S hS f F' G H' i' (FMap.compSource B S hS f ξ α.hom) :=
        fMapEquivPushforwardHom_ringUniverse_comparison B S hS f F' G H' i' _
    _ = descendedHomTypeU B S hS f F G H i ξ ≫
          (spacesDirectImageRestrictionTypeU B S hS f).map φ :=
        (descendedHomTypeU_source_map B S hS f F F' G H H' i i' α φ hφ ξ).symm
    _ = (fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
          ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
          (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H)) ≫
          (spacesDirectImageRestrictionTypeU B S hS f).map φ := by
        rw [fMapEquivPushforwardHom_ringUniverse_comparison B S hS f F G H i ξ]
    _ = fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
          ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map α ≫
          ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i'.hom ≫
            (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H')) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun m ↦ fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫ m) hmid)
    _ = _ := (Category.assoc _ _ _).symm

/-- **Stacks 03G8**, naturality of the chart correspondence in the sheaf on the source: the
homomorphism into the direct image attached to an `f`-map followed by a morphism of sheaves on
the small étale site of `X` is the homomorphism attached to the `f`-map, followed by the direct
image of that morphism. -/
theorem fMapEquivPushforwardHom_ringUniverse_source_map
    (F F' : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (α : F ⟶ F')
    (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj) :
    fMapEquivPushforwardHom_ringUniverse B S hS f F' G
        (FMap.compSource B S hS f ξ α.hom) =
      fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map α :=
  fMapEquivPushforwardHom_ringUniverse_source_map_of_presentation B S hS f F F' G
    ((smallEtaleComparisonRestriction B S hS X).objPreimage F)
    ((smallEtaleComparisonRestriction B S hS X).objPreimage F')
    ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm
    ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F').symm α
    ((smallEtaleComparisonRestriction B S hS X).preimage
      (((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫ α ≫
        ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F').symm.hom))
    (by
      rw [Functor.map_preimage]
      exact Iso.hom_inv_id_assoc _ _) ξ

/-- **Stacks 03G8**, naturality of the chart correspondence in the sheaf on the source, read on
the `f`-map side and on sections: the `f`-map of a homomorphism postcomposed with the direct
image of `α` is the `f`-map of the homomorphism, followed on sections by `α`. -/
theorem fMapEquivPushforwardHom_ringUniverse_symm_app_map
    (F F' : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (α : F ⟶ F')
    (β : G ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.obj.obj (op d.V)) :
    ((fMapEquivPushforwardHom_ringUniverse B S hS f F' G).symm
        (β ≫ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map α)).app d s =
      α.hom.app (op d.U)
        (((fMapEquivPushforwardHom_ringUniverse B S hS f F G).symm β).app d s) := by
  have h := fMapEquivPushforwardHom_ringUniverse_source_map B S hS f F F' G α
    ((fMapEquivPushforwardHom_ringUniverse B S hS f F G).symm β)
  rw [Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply]
  rfl

/-! ### `f`-maps along an étale morphism -/

variable (hf : IsEtale B S hS f.hom)

/-- The commutative diagram of étale scheme charts over an étale `f : X ⟶ Y` whose upper chart
is a given chart `U` of `X`, whose lower chart is the postcomposite of `U` with `f`, and whose
vertical morphism of schemes is the identity.  Every diagram of charts over `f` factors through
it, which is what `AlgebraicGeometry.Space.fMapRestrictionEquiv` expresses. -/
def identityChartDiagram (U : SmallEtale B S hS X.1) :
    ChartDiagram B S hS X.1 Y.1 f.hom :=
  ⟨U, (smallEtalePostcomp B S hS f hf).obj U, 𝟙 _, by simp [smallEtalePostcomp]⟩

/-- The morphism of étale scheme charts of `Y` from the postcomposite of the upper chart of a
diagram of charts over `f` to its lower chart: the vertical morphism of the diagram, read as a
morphism over `Y` using that the diagram commutes. -/
def chartDiagramTargetMap (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (smallEtalePostcomp B S hS f hf).obj d.U ⟶ d.V :=
  ObjectProperty.homMk (CostructuredArrow.homMk d.g d.comm.symm)

/-- **Stacks 03LP** for maps of sections: along an étale morphism, an `f`-map of Stacks 03G3
into a sheaf `F` on the small étale site of `X` is the same datum as a homomorphism into `F`
from the restriction along postcomposition of the sheaf on the small étale site of `Y`.

A diagram of charts over `f` is carried to the morphism of charts of `Y` out of the
postcomposite of its upper chart, and conversely a chart of `X` gives the diagram with identity
vertical morphism. -/
def fMapRestrictionEquiv
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    FMap B S hS X.1 Y.1 f.hom F.obj G.obj ≃
      (((smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous
        (Type u) (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1)).obj G ⟶ F) where
  toFun ξ := ⟨{
    app := fun U ↦ TypeCat.ofHom (ξ.app (identityChartDiagram B S hS f hf U.unop))
    naturality := by
      intro U V k
      apply TypeCat.homEquiv.injective
      funext s
      exact ξ.naturality (identityChartDiagram B S hS f hf U.unop)
        (identityChartDiagram B S hS f hf V.unop) k.unop
        ((smallEtalePostcomp B S hS f hf).map k.unop)
        (by simp [identityChartDiagram, smallEtalePostcomp]) s }⟩
  invFun α :=
    { app := fun d s ↦ α.hom.app (op d.U)
        (G.obj.map (chartDiagramTargetMap B S hS f hf d).op s)
      naturality := by
        intro d d' iU jV h s
        have hcomm : chartDiagramTargetMap B S hS f hf d' ≫ jV =
            (smallEtalePostcomp B S hS f hf).map iU ≫
              chartDiagramTargetMap B S hS f hf d :=
          ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h.symm)
        have hα := α.hom.naturality_apply iU.op
          (G.obj.map (chartDiagramTargetMap B S hS f hf d).op s)
        dsimp at hα ⊢
        rw [← hα]
        congr 1
        change G.obj.map (chartDiagramTargetMap B S hS f hf d').op (G.obj.map jV.op s) =
          G.obj.map ((smallEtalePostcomp B S hS f hf).map iU).op
            (G.obj.map (chartDiagramTargetMap B S hS f hf d).op s)
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        exact congrArg (fun k ↦ G.obj.map k s) (congrArg Quiver.Hom.op hcomm) }
  left_inv ξ := by
    cases ξ with
    | mk app nat =>
      dsimp only
      congr 1
      funext d s
      refine (nat d (identityChartDiagram B S hS f hf d.U) (𝟙 _)
        (chartDiagramTargetMap B S hS f hf d)
        rfl s).trans ?_
      change F.obj.map (𝟙 _) _ = _
      rw [F.obj.map_id]
      rfl
  right_inv α := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply TypeCat.homEquiv.injective
    funext s
    change α.hom.app U (G.obj.map (chartDiagramTargetMap B S hS f hf
      (identityChartDiagram B S hS f hf U.unop)).op s) = _
    have hid : chartDiagramTargetMap B S hS f hf
        (identityChartDiagram B S hS f hf U.unop) = 𝟙 _ := by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      rfl
    rw [hid]
    change α.hom.app U (G.obj.map (𝟙 _) s) = _
    rw [G.obj.map_id]
    rfl

/-! ### The structure map of an étale morphism is invertible -/

/-- A morphism is invertible as soon as composition with it has a retraction on each hom set
given by a bijection: the retraction forces composition to be that bijection's inverse, hence
bijective, and `CategoryTheory.isIso_of_coyoneda_map_bijective` applies. -/
private theorem isIso_of_homEquiv_comp {C : Type*} [Category.{v} C] {P Q : C} (a : P ⟶ Q)
    (e : ∀ T : C, (P ⟶ T) ≃ (Q ⟶ T)) (he : ∀ (T : C) (k : Q ⟶ T), e T (a ≫ k) = k) :
    IsIso a := by
  refine isIso_of_coyoneda_map_bijective a fun T ↦ ?_
  have h : (fun k : Q ⟶ T ↦ a ≫ k) = (e T).symm := by
    funext k
    exact (e T).injective ((he T k).trans ((e T).apply_symm_apply k).symm)
  rw [h]
  exact (e T).symm.bijective

include hf

/-- **Stacks 03LV.** For an étale morphism of algebraic spaces the inverse-image form
`f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of the morphism of small étale ringed topoi of Stacks 03G8
is an isomorphism.

The proof exhibits it as a universal arrow: composition with it is identified with the inverse
of the composite of `AlgebraicGeometry.Space.fMapRestrictionEquiv` with the chart correspondence
and the adjunction, and the chartwise formula for the structure map says that the identification
sends the structure map itself to the identity. -/
@[stacks 03LV "the inverse image of the structure sheaf, h⁻¹𝒪_V = 𝒪_U"]
theorem isIso_fSharpInverseImage_of_isEtale :
    IsIso (smallEtaleRingedToposHom B S hS f).fSharpInverseImage := by
  suffices h : IsIso ((smallEtaleRingedTopos B S hS X).forgetRing.map
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) from
    isIso_of_reflects_iso _ (smallEtaleRingedTopos B S hS X).forgetRing
  rw [AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv
    (smallEtaleRingedToposHom B S hS f)]
  set Φ := smallEtaleRingedToposHom B S hS f
  set OX := (smallEtaleRingedTopos B S hS X).forgetRing.obj
    (smallEtaleRingedTopos B S hS X).O
  set OY := (smallEtaleRingedTopos B S hS Y).forgetRing.obj
    (smallEtaleRingedTopos B S hS Y).O
  refine isIso_of_homEquiv_comp _
    (fun T ↦ ((Φ.toToposHom.adj.homEquiv OY T).trans
      (fMapEquivPushforwardHom_ringUniverse B S hS f T OY).symm).trans
        (fMapRestrictionEquiv B S hS f hf T OY)) (fun T k ↦ ?_)
  have hak : Φ.toToposHom.adj.homEquiv OY T
        ((Φ.toToposHom.adj.homEquiv OY OX).symm
          ((smallEtaleRingedTopos B S hS Y).forgetRing.map Φ.fSharp) ≫ k) =
      (smallEtaleRingedTopos B S hS Y).forgetRing.map Φ.fSharp ≫
        Φ.toToposHom.pushforward.map k := by
    rw [Φ.toToposHom.adj.homEquiv_naturality_right]
    exact congrArg (fun q ↦ q ≫ Φ.toToposHom.pushforward.map k)
      ((Φ.toToposHom.adj.homEquiv OY OX).apply_symm_apply _)
  refine sheaf_hom_ext_apply fun U s ↦ ?_
  change ((fMapEquivPushforwardHom_ringUniverse B S hS f T OY).symm
    (Φ.toToposHom.adj.homEquiv OY T
      ((Φ.toToposHom.adj.homEquiv OY OX).symm
        ((smallEtaleRingedTopos B S hS Y).forgetRing.map Φ.fSharp) ≫ k))).app
      (identityChartDiagram B S hS f hf U.unop) s = k.hom.app U s
  rw [hak]
  refine (fMapEquivPushforwardHom_ringUniverse_symm_app_map B S hS f OX T OY k
    ((smallEtaleRingedTopos B S hS Y).forgetRing.map Φ.fSharp)
    (identityChartDiagram B S hS f hf U.unop) s).trans ?_
  refine congrArg (fun t ↦ k.hom.app U t) ?_
  refine (smallEtaleRingedToposHom_chart B S hS f
    (identityChartDiagram B S hS f hf U.unop) s).trans ?_
  change Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (𝟙 _))) s = s
  rw [(BigFppfOver.toScheme B S hS).map_id]
  change Scheme.Γ.map (𝟙 _) s = s
  rw [Scheme.Γ.map_id]
  rfl

/-- **Stacks 03LV.** For an étale morphism of algebraic spaces the inverse image of the
structure sheaf of the target along the morphism of small étale ringed topoi of Stacks 03G8 is
canonically isomorphic to the structure sheaf of the source. -/
@[stacks 03LV "inverse image of the structure sheaf"]
noncomputable def etaleStructureSheafIso :
    (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        (smallEtaleRingedToposHom B S hS f).toToposHom).obj
      (smallEtaleRingedTopos B S hS Y).O ≅ (smallEtaleRingedTopos B S hS X).O :=
  haveI := isIso_fSharpInverseImage_of_isEtale B S hS f hf
  asIso (smallEtaleRingedToposHom B S hS f).fSharpInverseImage

/-- **Stacks 03LV.** The forward map of the canonical isomorphism of structure sheaves along an
étale morphism is the inverse-image form of the structure map; the isomorphism is not an extra
choice. -/
@[stacks 03LV "canonical structure map"]
theorem etaleStructureSheafIso_hom :
    (etaleStructureSheafIso B S hS f hf).hom =
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage :=
  rfl

end AlgebraicGeometry.Space

end
