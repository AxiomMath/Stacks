module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponents

/-!
# The number of geometric connected components of a fibre is well defined

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. A geometric point `p` of
`Y`, that is a field-valued point of Stacks 03BU whose field is algebraically closed, cuts out
the geometric fibre `X_p`, and
`AlgebraicGeometry.Space.geometricFiberComponentCount` counts the connected components of its
point space. Stacks 0E1B says that this count depends only on the point of `|Y|` represented by
`p`, so that the function `AlgebraicGeometry.Space.numberGeometricConnectedComponents` is the
count at every geometric representative, and that the resulting function is compatible with
arbitrary base change.

Both statements are proved here; the definitions themselves, and the existence of a geometric
representative of every point, are in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Fibres/GeometricComponents.lean`.

## Main definitions

* `AlgebraicGeometry.Space.fiberOverField` is the fibre of a morphism over a field-valued point
  of the target, read as a presheaf on the big fppf site over the field of that point, and
  `AlgebraicGeometry.Space.extendFiberOverFieldIso` identifies its lower-shriek extension back
  to the site over `S` with the fibre itself.
* `AlgebraicGeometry.Space.fiberOverFieldBaseChangeIso` exhibits the fibre over a dominated
  field-valued point as a base change of the fibre over the dominating one.

## Main results

* `AlgebraicGeometry.Space.geometricFiberComponentCount_eq_of_same_image`: two geometric points
  of the target with the same image in the point set have equinumerous sets of connected
  components in their fibres.
* `AlgebraicGeometry.Space.numberGeometricConnectedComponents_eq`: **Stacks 0E1B**, the value of
  the function at the image of a geometric point is the number of connected components of the
  fibre over that very geometric point. Equivalently: any two geometric points with the same
  image have equinumerous sets of connected components in their fibres.
* `AlgebraicGeometry.Space.numberGeometricConnectedComponents_baseChange`: **Stacks 0E1B**, the
  function attached to a base change `X ×_Y Z ⟶ Z` is the function attached to `X ⟶ Y` composed
  with the map `|Z| → |Y|` on points.

## Implementation notes

Two geometric points with the same image are, by Stacks 03BU, both dominated by a single
field-valued point, so the whole statement reduces to the case of a field-valued point `q`
dominated by a geometric point `p`: the field `κ(q)` is then an extension of the algebraically
closed — in particular separably closed — field `κ(p)`, and the fibre over `q` is the base
change of the fibre over `p` along that extension. Stacks 0A12
(`AlgebraicGeometry.Space.bijective_connectedComponents_relocalizeRestrict_of_isSepClosed`)
says that such a base change is a bijection on connected components. That is the only
geometric input.

To apply it, the fibre has to be read as an algebraic space over `Spec κ(p)` rather than over
`S`. `AlgebraicGeometry.Space.fiberOverField` is that reading: the fibre product, formed on the
big fppf site over `Spec κ(p)`, of the base change of `f` with the tautological section of the
base change of `Y`. Its lower-shriek extension back to the site over `S` is the fibre itself
(`AlgebraicGeometry.Space.extendFiberOverFieldIso`), and the lower-shriek extension does not
change the point space (`AlgebraicGeometry.Space.relocalizedPointsHomeo`), so the two counts
agree.

The counit of the relocalization adjunction exhibits the extension of a restriction as a
product with the base, whence the naturality squares of that counit are cartesian; this is
`CategoryTheory.OverShriek.isPullback_map_relocalizeRestrictCounit`, and pasting it onto the
image of the defining square of `fiberOverField` is what produces
`AlgebraicGeometry.Space.extendFiberOverFieldIso`.

## References

* [Stacks Project, Tag 0E1B](https://stacks.math.columbia.edu/tag/0E1B)
* [Stacks Project, Tag 0A12](https://stacks.math.columbia.edu/tag/0A12)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-- **The naturality squares of the counit of the relocalization adjunction are cartesian.**
For `f : V ⟶ U` the extension `Λ_f (j^{-1} X)` of a restriction is the product of `X` with the
representable presheaf of `(V →f U)`, so a morphism `α : X ⟶ Y` of presheaves on the slice over
`U` turns the counit into a base change of `α`. -/
theorem isPullback_map_relocalizeRestrictCounit {X Y : (Over U)ᵒᵖ ⥤ Type v} (α : X ⟶ Y) :
    IsPullback (relocalizeRestrictCounit f X)
      ((relocalizePresheafFunctor f).map ((relocalizeRestrict f).map α)) α
      (relocalizeRestrictCounit f Y) := by
  have hcounitY := isPullback_relocalizeRestrictCounit f Y subsingleton_yoneda_obj_mkId
    (toYonedaMkId Y) (toYonedaMkId (yoneda.obj (Over.mk f)))
  have hcomm : relocalizeRestrictCounit f X ≫ α =
      (relocalizePresheafFunctor f).map ((relocalizeRestrict f).map α) ≫
        relocalizeRestrictCounit f Y := by
    ext W x
    exact NatTrans.naturality_apply α (Over.homMk (𝟙 (unop W).left)
      (by rw [Category.id_comp]; exact x.2) : unop W ⟶ Over.mk (x.1.1 ≫ f)).op x.1.2
  have htoYoneda : (relocalizePresheafFunctor f).map ((relocalizeRestrict f).map α) ≫
      relocalizeToYoneda f ((relocalizeRestrict f).obj Y) =
      relocalizeToYoneda f ((relocalizeRestrict f).obj X) := by
    ext W x
    exact Over.OverMorphism.ext rfl
  have hterminal : α ≫ toYonedaMkId Y = toYonedaMkId X := by
    ext W x
    exact (subsingleton_yoneda_obj_mkId W).elim _ _
  have houter : IsPullback (relocalizeRestrictCounit f X)
      ((relocalizePresheafFunctor f).map ((relocalizeRestrict f).map α) ≫
        relocalizeToYoneda f ((relocalizeRestrict f).obj Y))
      (α ≫ toYonedaMkId Y) (toYonedaMkId (yoneda.obj (Over.mk f))) := by
    rw [htoYoneda, hterminal]
    exact isPullback_relocalizeRestrictCounit f X subsingleton_yoneda_obj_mkId
      (toYonedaMkId X) (toYonedaMkId (yoneda.obj (Over.mk f)))
  exact IsPullback.of_bot houter hcomm hcounitY

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The fibre over a field-valued point, read over that field -/

/-- The fibre of `f : F ⟶ G` over a field-valued point `p` of `G`, read as a presheaf on the
big fppf site over the field of `p`: the fibre product, formed there, of the base change of `f`
with the tautological section of the base change of `G`. -/
noncomputable def fiberOverField (f : F ⟶ G) (p : FieldValuedPoint B S hS G) :
    (BigFppfOver B (Spec (.of p.carrier)) p.contained)ᵒᵖ ⥤ Type u :=
  pullback ((OverShriek.relocalizeRestrict p.siteObject.hom).map f)
    (yonedaEquiv.symm
      (show ((OverShriek.relocalizeRestrict p.siteObject.hom).obj G).obj
          (op (Over.mk (𝟙 (B.obj p.contained)))) from p.value))

/-- The fibre of a morphism of algebraic spaces over a field-valued point of the target is an
algebraic space over that field: it is a fibre product of base changes of algebraic spaces with
a representable presheaf. -/
theorem fiberOverField_isAlgebraicSpace (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (p : FieldValuedPoint B S hS G) :
    IsAlgebraicSpace B (Spec (.of p.carrier)) p.contained (fiberOverField B S hS f p) :=
  isAlgebraicSpace_pullback B (Spec (.of p.carrier)) p.contained _ _
    (isAlgebraicSpace_relocalizeRestrict B (Spec (.of p.carrier)) S p.contained hS
      p.siteObject.hom F hF)
    (isAlgebraicSpace_yoneda B (Spec (.of p.carrier)) p.contained
      (Over.mk (𝟙 (B.obj p.contained))))
    (isAlgebraicSpace_relocalizeRestrict B (Spec (.of p.carrier)) S p.contained hS
      p.siteObject.hom G hG)

/-- **The fibre over a field-valued point, viewed again over `S`, is the fibre.** The
lower-shriek extension of `AlgebraicGeometry.Space.fiberOverField` along the structure morphism
of the point is the fibre product of `f` with the morphism represented by the point. -/
noncomputable def extendFiberOverFieldIso (f : F ⟶ G) (p : FieldValuedPoint B S hS G) :
    (OverShriek.relocalizePresheafFunctor p.siteObject.hom).obj (fiberOverField B S hS f p) ≅
      pullback f (yonedaEquiv.symm p.value) := by
  let g : B.obj p.contained ⟶ B.obj hS := p.siteObject.hom
  let R := OverShriek.relocalizeRestrict g
  let L := OverShriek.relocalizePresheafFunctor g
  let T : BigFppfOver B (Spec (.of p.carrier)) p.contained := Over.mk (𝟙 (B.obj p.contained))
  let β : yoneda.obj T ⟶ R.obj G :=
    yonedaEquiv.symm (show (R.obj G).obj (op T) from p.value)
  let i : yoneda.obj p.siteObject ≅ L.obj (yoneda.obj T) :=
    (relocalizedYonedaRepresentableBy B (B.obj p.contained) (B.obj hS) g T).toIso
  have hi : i.hom ≫ L.map β ≫ OverShriek.relocalizeRestrictCounit g G =
      yonedaEquiv.symm p.value := by
    ext W x
    change G.map _ (G.map _ p.value) = G.map _ p.value
    refine (G.map_comp_apply _ _ p.value).symm.trans
      (congrArg (fun m => G.map m p.value) ?_)
    exact Quiver.Hom.unop_inj (Over.OverMorphism.ext (Category.id_comp x.left))
  have h := ((IsPullback.of_hasPullback (R.map f) β).map L).paste_horiz
    (OverShriek.isPullback_map_relocalizeRestrictCounit g f)
  have h' : IsPullback
      (L.map (pullback.fst (R.map f) β) ≫ OverShriek.relocalizeRestrictCounit g F)
      (L.map (pullback.snd (R.map f) β) ≫ i.inv) f (yonedaEquiv.symm p.value) := by
    refine h.of_iso (Iso.refl _) (Iso.refl _) i.symm (Iso.refl _) (by simp) (by simp) (by simp) ?_
    calc (L.map β ≫ OverShriek.relocalizeRestrictCounit g G) ≫ 𝟙 G
        = i.inv ≫ i.hom ≫ L.map β ≫ OverShriek.relocalizeRestrictCounit g G := by simp
      _ = i.symm.hom ≫ yonedaEquiv.symm p.value := by rw [hi]; rfl
  exact h'.isoPullback

/-- The number of connected components of the fibre over a field-valued point is computed on
the site over the field of that point. -/
theorem geometricFiberComponentCount_eq_overField (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (p : FieldValuedPoint B S hS G) :
    geometricFiberComponentCount B S hS f p =
      Cardinal.toENat (Cardinal.mk (ConnectedComponents
        (points B (Spec (.of p.carrier)) p.contained (fiberOverField B S hS f p)))) := by
  have he := Cardinal.mk_congr
    (relocalizedPointsHomeo B (Spec (.of p.carrier)) S p.contained hS p.siteObject.hom
      (fiberOverField B S hS f p)
      (fiberOverField_isAlgebraicSpace B S hS hF hG f p)).connectedComponentsCongr.toEquiv
  have hi := cardinalMk_connectedComponents_eq_of_iso B S hS
    (extendFiberOverFieldIso B S hS f p)
  exact congrArg Cardinal.toENat (he.trans hi).symm

/-! ### Changing the field of the representative -/

/-- **The fibre over a dominated field-valued point is a base change.** If the field-valued
point `q` is the restriction of `p` along a morphism `t` of their field spectra over `S`, then
the fibre over `q` is the base change along `t` of the fibre over `p`. -/
noncomputable def fiberOverFieldBaseChangeIso (f : F ⟶ G) (p q : FieldValuedPoint B S hS G)
    (t : B.obj q.contained ⟶ B.obj p.contained)
    (ht : t ≫ p.siteObject.hom = q.siteObject.hom)
    (hv : G.map (Over.homMk t ht).op p.value = q.value) :
    (OverShriek.relocalizeRestrict t).obj (fiberOverField B S hS f p) ≅
      fiberOverField B S hS f q := by
  dsimp [fiberOverField]
  let R := OverShriek.relocalizeRestrict t
  let Rp := OverShriek.relocalizeRestrict p.siteObject.hom
  let Rq := OverShriek.relocalizeRestrict q.siteObject.hom
  let α : Rp.obj F ⟶ Rp.obj G := Rp.map f
  let T := Over.mk (𝟙 (B.obj p.contained))
  let pval : (Rp.obj G).obj (Opposite.op T) := p.value
  let β : yoneda.obj T ⟶ Rp.obj G := yonedaEquiv.symm pval
  let e₁ : R.obj (pullback α β) ≅ pullback (R.map α) (R.map β) :=
    (preservesLimitIso R (cospan α β)).trans (HasLimit.isoOfNatIso (cospanCompIso R α β))
  let eop : (Over.map t).op ⋙ (Over.map p.siteObject.hom).op ≅
      (Over.map q.siteObject.hom).op :=
    (Functor.opComp (Over.map t) (Over.map p.siteObject.hom)).symm ≪≫
      NatIso.op (Over.mapComp t p.siteObject.hom) ≪≫
        eqToIso (congrArg (fun m => (Over.map m).op) ht)
  let ecomp : Rp ⋙ R ≅ Rq := by
    dsimp [Rp, R, Rq, OverShriek.relocalizeRestrict]
    refine NatIso.ofComponents (fun X => ?_) ?_
    · exact (Functor.associator (Over.map t).op (Over.map p.siteObject.hom).op X).symm ≪≫
        Functor.isoWhiskerRight eop X
    · intro X Y a
      ext Z
      simp [Functor.associator, Functor.whiskerRight_app]
  let eF := ecomp.app F
  let eG := ecomp.app G
  let Tq := Over.mk (𝟙 (B.obj q.contained))
  let βq : yoneda.obj Tq ⟶ Rq.obj G :=
    yonedaEquiv.symm (show (Rq.obj G).obj (Opposite.op Tq) from q.value)
  have hT : IsTerminal T := Over.mkIdTerminal
  have hTq : IsTerminal Tq := Over.mkIdTerminal
  letI : ∀ X : (Over (B.obj q.contained))ᵒᵖ,
      Unique ((R.obj (yoneda.obj T)).obj X) := by
    intro X
    change Unique ((Over.map t).obj X.unop ⟶ T)
    exact ⟨⟨hT.from _⟩, fun m => hT.hom_ext _ _⟩
  letI : ∀ X : (Over (B.obj q.contained))ᵒᵖ, Unique ((yoneda.obj Tq).obj X) := by
    intro X
    change Unique (X.unop ⟶ Tq)
    exact ⟨⟨hTq.from _⟩, fun m => hTq.hom_ext _ _⟩
  let eT : R.obj (yoneda.obj T) ≅ yoneda.obj Tq :=
    NatIso.ofComponents (fun X => Equiv.toIso (Equiv.ofUnique _ _)) (by
      intro X Y m
      ext Z
      exact Subsingleton.elim _ _)
  have hmor :
      ((Over.map p.siteObject.hom).map (hT.from ((Over.map t).obj Tq))).op ≫
          eop.hom.app (Opposite.op Tq) = (Over.homMk t ht).op := by
    refine Quiver.Hom.unop_inj (Over.OverMorphism.ext ?_)
    rw [hT.hom_ext (hT.from ((Over.map t).obj Tq)) (Over.homMk t (by simp [T, Tq]))]
    simp [eop, Over.mapComp, Over.map_obj_left]
    rfl
  have hα : eF.hom ≫ Rq.map f = R.map α ≫ eG.hom := by
    simpa [eF, eG] using (ecomp.hom.naturality f).symm
  have hβ : eT.hom ≫ βq = R.map β ≫ eG.hom := by
    have hβ' : βq = eT.inv ≫ R.map β ≫ eG.hom := by
      apply (yonedaEquiv (X := Tq) (F := Rq.obj G)).injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rw [show yonedaEquiv eT.inv = hT.from ((Over.map t).obj Tq) from Subsingleton.elim _ _]
      have hstep : q.value =
          G.map (eop.hom.app (op Tq))
            (G.map ((Over.map p.siteObject.hom).map
              (hT.from ((Over.map t).obj Tq))).op pval) := by
        rw [← Functor.map_comp_apply, hmor]
        dsimp [pval, Tq, Over.map, Comma.mapRight, FieldValuedPoint.siteObject]
        exact hv.symm
      refine hstep.trans ?_
      simp [NatTrans.comp_app, β, eG, ecomp, Rp, R, Rq,
        OverShriek.relocalizeRestrict, Functor.associator]
      rfl
    rw [hβ', Iso.hom_inv_id_assoc]
  exact e₁.trans (HasLimit.isoOfNatIso (cospanExt eF eT eG hα hβ))

/-- The number of connected components of the fibre over a field-valued point dominated by a
geometric point is the number of connected components of the fibre over the geometric point:
the first fibre is the base change of the second along an extension of the separably closed
field of the geometric point, which is Stacks 0A12. -/
@[ega "III 4.3.4" "partial"]
theorem geometricFiberComponentCount_eq_of_dominates (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (p : GeometricPoint B S hS G)
    (q : FieldValuedPoint B S hS G) (t : q.siteObject ⟶ p.val.siteObject)
    (hv : G.map t.op p.val.value = q.value) :
    geometricFiberComponentCount B S hS f p.val =
      geometricFiberComponentCount B S hS f q := by
  let _ : Algebra p.val.carrier q.carrier :=
    (Spec.homEquiv (B.inclusion.map t.left)).hom.toAlgebra
  have hα : (Spec.homEquiv (B.inclusion.map t.left)).hom =
      algebraMap p.val.carrier q.carrier :=
    (RingHom.algebraMap_toAlgebra _).symm
  let g : B.obj q.contained ⟶ B.obj p.val.contained :=
    fieldExtensionMap B p.val.carrier q.carrier p.val.contained q.contained
  have hscheme : B.inclusion.map t.left =
      Spec.map (CommRingCat.ofHom (algebraMap p.val.carrier q.carrier)) := by
    apply Spec.homEquiv.injective
    exact CommRingCat.hom_ext (hα.trans (by simp))
  have htMap : t.left = g := by
    apply B.inclusion.map_injective
    rw [hscheme, map_fieldExtensionMap]
  let Xp := fiberOverField B S hS f p.val
  have hXp := fiberOverField_isAlgebraicSpace B S hS hF hG f p.val
  let _ : IsAlgClosed p.val.carrier := p.property
  have hfield := Cardinal.mk_congr (Equiv.ofBijective _
    (bijective_connectedComponents_relocalizeRestrict_of_isSepClosed B p.val.carrier q.carrier
      p.val.contained q.contained Xp hXp))
  have ht : t.left ≫ p.val.siteObject.hom = q.siteObject.hom := t.w
  have hv' : G.map (Over.homMk t.left ht).op p.val.value = q.value := by
    rw [show (Over.homMk t.left ht : q.siteObject ⟶ p.val.siteObject) = t from
      Over.OverMorphism.ext rfl]
    exact hv
  have hIsoG : (OverShriek.relocalizeRestrict g).obj Xp ≅ fiberOverField B S hS f q :=
    (eqToIso (congrArg (fun m => (OverShriek.relocalizeRestrict m).obj Xp) htMap.symm)).trans
      (fiberOverFieldBaseChangeIso B S hS f p.val q t.left ht hv')
  have hcardIso := cardinalMk_connectedComponents_eq_of_iso B (Spec (.of q.carrier))
    q.contained hIsoG
  rw [geometricFiberComponentCount_eq_overField B S hS hF hG f p.val,
    geometricFiberComponentCount_eq_overField B S hS hF hG f q]
  exact congrArg Cardinal.toENat (hfield.symm.trans hcardIso)

/-- Two geometric points of `G` with the same image in `|G|` have equinumerous sets of
connected components in their fibres: they are both dominated by a single field-valued point
of `G`. -/
theorem geometricFiberComponentCount_eq_of_same_image (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (p q : GeometricPoint B S hS G)
    (hpq : p.image = q.image) :
    geometricFiberComponentCount B S hS f p.val =
      geometricFiberComponentCount B S hS f q.val := by
  obtain ⟨r, ⟨t, ht⟩, ⟨t', ht'⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS G p.val q.val).mp hpq
  exact (geometricFiberComponentCount_eq_of_dominates B S hS hF hG f p r t ht).trans
    (geometricFiberComponentCount_eq_of_dominates B S hS hF hG f q r t' ht').symm

/-! ### Stacks 0E1B -/

/-- **Stacks 0E1B.** The number of geometric connected components of the fibres of a morphism
of algebraic spaces is, at the image of a geometric point, the number of connected components
of the fibre over that geometric point. In particular the defining infimum is attained at every
geometric representative. -/
@[stacks 0E1B "well-definedness", ega "III 4.3.4" "more general", ega "IV 4.5.1" "partial"]
theorem numberGeometricConnectedComponents_eq (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (p : GeometricPoint B S hS G) :
    numberGeometricConnectedComponents B S hS f p.image =
      geometricFiberComponentCount B S hS f p.val := by
  have hset : {n : ℕ∞ | ∃ q : GeometricPoint B S hS G,
      q.image = p.image ∧ geometricFiberComponentCount B S hS f q.val = n} =
      {geometricFiberComponentCount B S hS f p.val} := by
    ext n
    constructor
    · rintro ⟨q, hq, hqn⟩
      exact ((geometricFiberComponentCount_eq_of_same_image B S hS hF hG f p q hq.symm).trans
        hqn).symm
    · rintro rfl
      exact ⟨p, rfl, rfl⟩
  exact (congrArg sInf hset).trans (csInf_singleton _)

/-- **Stacks 0E1B.** Formation of the number of geometric connected components of the fibres
commutes with arbitrary base change: the function attached to the projection `F ×_G H ⟶ H` is
the function attached to `f : F ⟶ G` composed with the map `|H| → |G|` on points. -/
@[stacks 0E1B "base change"]
theorem numberGeometricConnectedComponents_baseChange
    {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H) (f : F ⟶ G) (g : H ⟶ G) :
    numberGeometricConnectedComponents B S hS (pullback.snd f g) =
      numberGeometricConnectedComponents B S hS f ∘ pointsMap B S hS H g := by
  funext y
  obtain ⟨p, rfl⟩ := exists_geometricRepresentative B S hS H y
  have hP := isAlgebraicSpace_pullback B S hS f g hF hH hG
  let pG : GeometricPoint B S hS G := ⟨FieldValuedPoint.map B S hS H g p.val, p.property⟩
  have himage : pG.image = pointsMap B S hS H g p.image := rfl
  rw [numberGeometricConnectedComponents_eq B S hS hP hH (pullback.snd f g) p,
    Function.comp_apply, ← himage,
    numberGeometricConnectedComponents_eq B S hS hF hG f pG]
  exact geometricFiberComponentCount_pullback_snd_eq B S hS f g p.val

end AlgebraicGeometry.Space

end
