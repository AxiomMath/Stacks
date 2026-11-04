module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigZariski.SmallSiteComparison

/-!
# The canonical restriction of a big Zariski sheaf to a compatible system

The sheaves on the small sites constructed from a big Zariski sheaf, together with the
section maps they carry along morphisms over the base, assemble into a compatible system in
the sense of Tag 0213.  This file builds the resulting functor and pins down what it does:
each component is the inverse image along the small-to-big morphism of topoi, and the
comparison maps are the restriction maps of the original sheaf.

## Main definitions

* `AlgebraicGeometry.bigZariskiSheafRestriction` — the canonical restriction functor.

## Main results

* `AlgebraicGeometry.bigZariskiSheafRestriction_sectionEquiv` and
  `AlgebraicGeometry.bigZariskiSheafRestriction_sectionEquiv_naturality` — global sections of
  a component at `T` are the sections of the original sheaf at `T`, naturally in the sheaf.
* `AlgebraicGeometry.bigZariskiSheafRestriction_pullback_sections` — under that
  identification the comparison map is the restriction map of the big-site sheaf.
* `AlgebraicGeometry.bigZariskiSheafRestriction_sheaf` and
  `AlgebraicGeometry.bigZariskiSheafRestriction_sheafNatIso` — each component is the
  canonical small-site sheaf, naturally in the big-site sheaf.

## References

* [Stacks Project, Tag 0213](https://stacks.math.columbia.edu/tag/0213)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical restriction of a big-site sheaf to all ordinary Zariski sites,
including its comparison maps induced by big-site restrictions. -/
@[stacks 0213 "canonical restriction functor"]
public noncomputable def bigZariskiSheafRestriction :
    Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)) ⥤
      BigZariskiSheafData.{u, v} B S hS where
  obj F := {
    sheaf := canonicalSmallSheaf B S hS F
    pullback := fun {T T'} f =>
      TopCat.Sheaf.inverseImageSectionFamilyHom (B.inclusion.map f.left).base
        (canonicalSmallSheaf B S hS F T) (canonicalSmallSheaf B S hS F T')
        (canonicalSmallPullbackFamily B S hS F f)
    pullback_comp := by
      intro T T' T'' f g
      apply TopCat.Sheaf.inverseImage_hom_comp
      let FT := canonicalSmallSheaf B S hS F T
      let FT'' := canonicalSmallSheaf B S hS F T''
      let ψ := TopCat.Sheaf.inverseImageSectionFamilyAdjoint (B.inclusion.map (g ≫ f).left).base
        FT FT'' (canonicalSmallPullbackFamily B S hS F (g ≫ f))
      have hc : (TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v}
          ((B.inclusion.map g.left).base ≫ (B.inclusion.map f.left).base)).homEquiv
          FT FT'' (TopCat.Sheaf.inverseImageSectionFamilyHom (B.inclusion.map (g ≫ f).left).base
            FT FT'' (canonicalSmallPullbackFamily B S hS F (g ≫ f))) = ψ := by
        change ((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v}
          (B.inclusion.map (g ≫ f).left).base).homEquiv FT FT'')
          (((TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v}
            (B.inclusion.map (g ≫ f).left).base).homEquiv FT FT'').symm ψ) = ψ
        exact Equiv.apply_symm_apply _ _
      rw [hc]
      simp only [TopCat.Sheaf.inverseImageSectionFamilyHom, Equiv.apply_symm_apply]
      ext V s
      exact canonicalSmallPullbackFamily_comp B S hS F f g _ _ V.unop
        le_rfl le_rfl le_rfl s
    isIso_pullback := by
      intro T T' f hf
      let := hf
      let ftop := (B.inclusion.map f.left).base
      let htop := Scheme.Hom.isOpenEmbedding (B.inclusion.map f.left)
      apply TopCat.Sheaf.isIso_inverseImageSectionFamilyHom ftop htop
      intro U
      let V := htop.functor.obj U
      let X := smallOpenObject B S hS T' U
      let Y := smallOpenObject B S hS T V
      have hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
          (Opens.map ftop).obj
            ((smallZariskiToOpens B T.left.1 T.left.2).obj Y) := by
        rw [smallOpenObject_toOpens, smallOpenObject_toOpens]
        exact (htop.isOpenMap.adjunction.unit.app U).le
      have : IsIso (smallSiteArrow B S hS f X Y hXY) :=
        smallSiteArrow_isIso B S hS f X Y hXY (by
          rw [smallOpenObject_toOpens, smallOpenObject_toOpens]
          rfl)
      change Function.Bijective (canonicalSmallPairMap B S hS F f U V X Y _ _ hXY)
      apply (CategoryTheory.isIso_iff_bijective _).mp
      dsimp only [canonicalSmallPairMap]
      infer_instance
  }
  map {F G} α := {
    app := fun T => (canonicalSmallSheafFunctor B S hS T).map α
    naturality := by
      intro T T' f
      let ftop := (B.inclusion.map f.left).base
      let FT := canonicalSmallSheaf B S hS F T
      let GT := canonicalSmallSheaf B S hS G T
      let FT' := canonicalSmallSheaf B S hS F T'
      let GT' := canonicalSmallSheaf B S hS G T'
      let ξF := canonicalSmallPullbackFamily B S hS F f
      let ξG := canonicalSmallPullbackFamily B S hS G f
      let cF := TopCat.Sheaf.inverseImageSectionFamilyHom ftop FT FT' ξF
      let cG := TopCat.Sheaf.inverseImageSectionFamilyHom ftop GT GT' ξG
      let adj := TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} ftop
      let αT : FT ⟶ GT :=
        (canonicalSmallSheafFunctor B S hS T).map α
      let αT' : FT' ⟶ GT' :=
        (canonicalSmallSheafFunctor B S hS T').map α
      apply (adj.homEquiv FT GT').injective
      have hF : (adj.homEquiv FT FT') cF =
          TopCat.Sheaf.inverseImageSectionFamilyAdjoint ftop FT FT' ξF := by
        simp [cF, adj, TopCat.Sheaf.inverseImageSectionFamilyHom]
      have hG : (adj.homEquiv GT GT') cG =
          TopCat.Sheaf.inverseImageSectionFamilyAdjoint ftop GT GT' ξG := by
        simp [cG, adj, TopCat.Sheaf.inverseImageSectionFamilyHom]
      change (adj.homEquiv FT GT')
          ((TopCat.Sheaf.inverseImage.{u, v} ftop).map αT ≫ cG) =
        (adj.homEquiv FT GT') (cF ≫ αT')
      rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
        hF, hG]
      ext V s
      let U := (Opens.map ftop).obj V.unop
      let X := smallOpenObject B S hS T' U
      let Y := smallOpenObject B S hS T V.unop
      have hX : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X = U :=
        smallOpenObject_toOpens B S hS T' U
      have hY : (smallZariskiToOpens B T.left.1 T.left.2).obj Y = V.unop :=
        smallOpenObject_toOpens B S hS T V.unop
      have hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
          (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
            ((smallZariskiToOpens B T.left.1 T.left.2).obj Y) := by
        rw [hX, hY]
        exact le_rfl
      change (((canonicalSmallSheafFunctor B S hS T).map α).1.app V ≫
          canonicalSmallPairMap B S hS G f U V.unop X Y hX hY hXY) s =
        (canonicalSmallPairMap B S hS F f U V.unop X Y hX hY hXY ≫
          ((canonicalSmallSheafFunctor B S hS T').map α).1.app (op U)) s
      exact congrArg (fun k => k s)
        (canonicalSmallPairMap_naturality_in_F B S hS α f U V.unop X Y hX hY hXY)
  }
  map_id F := BigZariskiSheafData.Hom.ext B S hS fun T =>
    ((canonicalSmallSheafFunctor B S hS T).map_id F).symm
  map_comp {F G H} (α : F ⟶ G) (β : G ⟶ H) := BigZariskiSheafData.Hom.ext B S hS fun T =>
    (canonicalSmallSheafFunctor B S hS T).map_comp α β

/-- Global sections of the canonical restriction at a scheme are the sections
of the original big-site sheaf at that scheme. -/
@[stacks 0213 "canonical identification of sections"]
public noncomputable def bigZariskiSheafRestriction_sectionEquiv
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS) :
    (((bigZariskiSheafRestriction.{u, v} B S hS).obj F).sheaf T).1.obj (op ⊤) ≃
      F.1.obj (op T) :=
  CategoryTheory.Iso.toEquiv (canonicalSmallTopSectionsIso B S hS F T)

/-- The identification of global sections is natural in the big-site sheaf. -/
@[stacks 0213 "naturality of section identification"]
public theorem bigZariskiSheafRestriction_sectionEquiv_naturality
    {F G : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v))}
    (α : F ⟶ G) (T : BigZariskiOver B S hS)
    (s : (((bigZariskiSheafRestriction.{u, v} B S hS).obj F).sheaf T).1.obj (op ⊤)) :
  bigZariskiSheafRestriction_sectionEquiv B S hS G T
      (((((bigZariskiSheafRestriction.{u, v} B S hS).map α).app T).1.app (op ⊤)) s) =
    α.1.app (op T)
      (bigZariskiSheafRestriction_sectionEquiv B S hS F T s) := by
  show (canonicalSmallTopSectionsIso B S hS G T).hom
      (((canonicalSmallSheafFunctor B S hS T).map α).1.app (op ⊤) s) =
    α.1.app (op T) ((canonicalSmallTopSectionsIso B S hS F T).hom s)
  exact (congrArg (fun k => k s) (canonicalSmallTopSectionsIso_naturality B S hS α T)).symm

/-- The top representative isomorphism lies over the structure morphism of the top open. -/
private theorem canonicalSmallTopRepresentativeIso_hom_left (T : BigZariskiOver B S hS) :
    (canonicalSmallTopRepresentativeIso B S hS T).hom.left =
      (smallOpenObject B S hS T ⊤).obj.hom :=
  B.inclusion.map_injective (by
    show B.inclusion.map (B.inclusion.preimage
      (B.inclusion.map (smallOpenObject B S hS T ⊤).obj.hom)) = _
    rw [B.inclusion.map_preimage])

/-- The top representative isomorphisms conjugate the small-site arrow of the top opens back
to the original morphism. -/
private theorem canonicalSmallTopRepresentativeIso_inv_comp_smallSiteArrow_comp_hom
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj (smallOpenObject B S hS T' ⊤) ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj (smallOpenObject B S hS T ⊤))) :
    (canonicalSmallTopRepresentativeIso B S hS T').inv ≫
        smallSiteArrow B S hS f (smallOpenObject B S hS T' ⊤) (smallOpenObject B S hS T ⊤) hXY ≫
          (canonicalSmallTopRepresentativeIso B S hS T).hom = f := by
  let X := smallOpenObject B S hS T' ⊤
  let Y := smallOpenObject B S hS T ⊤
  let a := smallSiteArrow B S hS f X Y hXY
  let eX := canonicalSmallTopRepresentativeIso B S hS T'
  let eY := canonicalSmallTopRepresentativeIso B S hS T
  have hx : eX.hom.left = X.obj.hom := canonicalSmallTopRepresentativeIso_hom_left B S hS T'
  have hy : eY.hom.left = Y.obj.hom := canonicalSmallTopRepresentativeIso_hom_left B S hS T
  have hxinv : eX.inv.left ≫ X.obj.hom = 𝟙 _ := by
    rw [← hx]
    simp
  have hfac : a.left ≫ Y.obj.hom = X.obj.hom ≫ f.left :=
    B.inclusion.map_injective (smallSiteArrow_fac B S hS f X Y hXY)
  apply Over.OverMorphism.ext
  show eX.inv.left ≫ a.left ≫ eY.hom.left = f.left
  rw [hy, hfac, ← Category.assoc, hxinv]
  simp

/-- Under the canonical identifications of global sections, the pullback
comparison is exactly the restriction map of the big-site sheaf. Applying this
to every object, including open subschemes, controls the comparison on opens. -/
@[stacks 0213 "canonicality of pullback comparisons"]
public theorem bigZariskiSheafRestriction_pullback_sections
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (s : F.1.obj (op T)) :
    let D := (bigZariskiSheafRestriction.{u, v} B S hS).obj F
    let ftop := (B.inclusion.map f.left).base
    let η := (TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} ftop).unit.app
      (D.sheaf T)
    bigZariskiSheafRestriction_sectionEquiv B S hS F T'
      ((D.pullback f).1.app (op ⊤)
        (η.1.app (op ⊤)
          ((bigZariskiSheafRestriction_sectionEquiv B S hS F T).symm s))) =
      F.1.map f.op s  := by
  let ftop := (B.inclusion.map f.left).base
  let η := (TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} ftop).unit.app
    (canonicalSmallSheaf B S hS F T)
  show CategoryTheory.Iso.toEquiv (canonicalSmallTopSectionsIso B S hS F T')
      ((TopCat.Sheaf.inverseImageSectionFamilyHom ftop (canonicalSmallSheaf B S hS F T)
        (canonicalSmallSheaf B S hS F T')
        (canonicalSmallPullbackFamily B S hS F f)).1.app (op ⊤)
        (η.1.app (op ⊤)
          ((CategoryTheory.Iso.toEquiv (canonicalSmallTopSectionsIso B S hS F T)).symm s))) = _
  have htop := TopCat.Sheaf.inverseImageSectionFamilyHom_unit_app ftop
    (canonicalSmallSheaf B S hS F T) (canonicalSmallSheaf B S hS F T')
    (canonicalSmallPullbackFamily B S hS F f) ⊤
    ((CategoryTheory.Iso.toEquiv (canonicalSmallTopSectionsIso B S hS F T)).symm s)
  have htop' := by simpa only [Opens.map_top] using htop
  dsimp [η]
  let X := smallOpenObject B S hS T' ⊤
  let Y := smallOpenObject B S hS T ⊤
  have hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y) := by
    rw [smallOpenObject_toOpens, smallOpenObject_toOpens]
    simp
  have harrowOp : (canonicalSmallTopRepresentativeIso B S hS T).hom.op ≫
      (smallSiteArrow B S hS f X Y hXY).op ≫
        (canonicalSmallTopRepresentativeIso B S hS T').inv.op = f.op :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.op)
      (canonicalSmallTopRepresentativeIso_inv_comp_smallSiteArrow_comp_hom B S hS f hXY))
  have hcat : (canonicalSmallTopSectionsIso B S hS F T).inv ≫
      canonicalSmallPairMap B S hS F f ⊤ ⊤ X Y
        (smallOpenObject_toOpens B S hS T' ⊤)
        (smallOpenObject_toOpens B S hS T ⊤) hXY ≫
        (canonicalSmallTopSectionsIso B S hS F T').hom = F.1.map f.op := by
    simp only [canonicalSmallTopSectionsIso, Functor.comp_obj, ObjectProperty.ι_obj,
      Iso.op_symm, Functor.mapIso_symm, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
      Iso.op_hom, canonicalSmallPairMap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
      Iso.op_inv, Category.assoc, cancelIso]
    rw [← F.1.map_comp, ← F.1.map_comp, harrowOp]
  calc
    _ = (canonicalSmallTopSectionsIso B S hS F T').hom
        ((canonicalSmallPullbackFamily B S hS F f).app ⊤ ⊤ le_rfl
          ((canonicalSmallTopSectionsIso B S hS F T).inv s)) :=
      congrArg (fun z => (canonicalSmallTopSectionsIso B S hS F T').hom z) htop'
    _ = F.1.map f.op s := by
      simpa [canonicalSmallPullbackFamily, X, Y] using congrArg (fun m => m s) hcat

/-- At each scheme over `S` the sheaf produced by canonical restriction is the inverse image
of the big-site sheaf along the small-to-big morphism of topoi, transported to the space of
that scheme. -/
@[stacks 0213 "canonical sheaf on each scheme"]
public noncomputable def bigZariskiSheafRestriction_sheaf
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS) :
    ((bigZariskiSheafRestriction.{u, v} B S hS).obj F).sheaf T ≅
      canonicalSmallSheaf B S hS F T :=
  Iso.refl _

/-- The componentwise identification is natural in the big-site sheaf; hence
its maps on every open subset are the canonical restriction maps. -/
@[stacks 0213 "naturality on opens and in the sheaf"]
public noncomputable def bigZariskiSheafRestriction_sheafNatIso
    (T : BigZariskiOver B S hS) :
    bigZariskiSheafRestriction.{u, v} B S hS ⋙ BigZariskiSheafData.eval B S hS T ≅
      canonicalSmallSheafFunctor.{u, v} B S hS T := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) fun _ => ?_
  ext U
  rfl

end AlgebraicGeometry
