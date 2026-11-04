module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReducedFieldExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionFibre

/-!
# Geometrically reduced fibres of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `y` be a point of
`|Y|`. The fibre of `f` at `y` is *geometrically reduced* when, for a field-valued
representative `Spec k ⟶ Y` of `y`, the algebraic space `X_k = X ×_Y Spec k` is geometrically
reduced over `k`; this does not depend on the representative. The locus of such points pulls
back along an arbitrary morphism of algebraic spaces `Y' ⟶ Y`.

## Main definitions

* `AlgebraicGeometry.Space.restrictedFibre` is the fibre of `f` over a section of `Y` over an
  object of the big fppf site, formed over that object as a base.
* `AlgebraicGeometry.Space.fibreOverFieldValuedPoint` is the fibre over a field-valued point,
  an algebraic space over the point's field of definition.
* `AlgebraicGeometry.Space.IsGeometricallyReducedFibre` is geometric reducedness of that
  fibre, and `AlgebraicGeometry.Space.geometricallyReducedFibreLocus` is the set of points of
  `|Y|` whose fibre is geometrically reduced.
* `AlgebraicGeometry.Space.IsGeometricallyReducedFibreAt` is Stacks 0E08: the fibre of `f` at a
  point of `|Y|` is geometrically reduced, that is, the point lies in the locus above.

## Main results

* `AlgebraicGeometry.Space.isGeometricallyReduced_congr_iso`: geometric reducedness of an
  algebraic space over a field is invariant under isomorphism.
* `AlgebraicGeometry.Space.isGeometricallyReducedFibre_tfae` is Stacks 0E07: the three
  equivalent conditions on a point of `|Y|` — the fibre is geometrically reduced over the
  field of *some* field-valued representative, over the field of *every* one, or merely
  reduced over every one.
* `AlgebraicGeometry.Space.geometricallyReducedFibreLocus_pullback` is Stacks 0E09: the
  geometrically reduced fibre locus of a base change is the inverse image of the
  geometrically reduced fibre locus.

## Implementation notes

The fibre over a section of `Y` over `T ⟶ S` is formed over `T`: both `X` and `Y` are
restricted to the big fppf site of `T` along `CategoryTheory.OverShriek.relocalizeRestrict`,
and the fibre is the fibre product of the restricted `f` with the tautological section of the
restricted `Y` over the final object `T / T`. Restriction is reindexing, so
`relocalizeRestrict` of a composite is the composite of the restrictions on the nose, which
is what makes the fibre over an extension `Spec K ⟶ Spec k ⟶ Y` of a field-valued point the
base change along `K/k` of the fibre over the point itself. Independence of the fibre
condition from the chosen representative — the equivalence of conditions (1) and (2) of
Stacks 0E07 — then comes from Stacks 0E04, geometric reducedness being insensitive to
extension of the ground field, together with the description of equality in `|Y|` by common
extensions of representatives (Stacks 03BU). Condition (3) of Stacks 0E07, reducedness of the
fibre over every representative, is stated as the étale-local scheme property
`AlgebraicGeometry.IsReduced` of Stacks 03E6; it implies the other two because every
representative is dominated by one defined over an algebraic closure of its field, where
reducedness already gives geometric reducedness by Stacks 020I.

With that in hand Stacks 0E09 is the computation of the source: a field-valued
representative of a point of `|Y'|` is carried by `Y' ⟶ Y` to one of its image in `|Y|`, over
the same field, and the two fibres agree because `(X ×_Y Y') ×_{Y'} Spec k = X ×_Y Spec k`.
This is `AlgebraicGeometry.Space.restrictedFibreBaseChangeIso`, obtained from the fact that
restriction preserves fibre products and from pullback pasting.

Geometric reducedness is a condition attached to an algebraic space together with a proof that
it is one, so transporting it along an isomorphism of presheaves needs an argument: by Stacks
0DMS it is a condition on the étale scheme charts, and composing a chart with the isomorphism
is a bijection between the charts of the two spaces.

## References

* [Stacks Project, Tag 0E07](https://stacks.math.columbia.edu/tag/0E07)
* [Stacks Project, Tag 0E08](https://stacks.math.columbia.edu/tag/0E08)
* [Stacks Project, Tag 0E09](https://stacks.math.columbia.edu/tag/0E09)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The tautological section of the restriction of `Y` to `T`, attached to a section of `Y`
over an object `T ⟶ S` of the big fppf site. -/
noncomputable def restrictedSection (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {T : Scheme.{u}}
    (hT : B.Contains T) (g : B.obj hT ⟶ B.obj hS) (v : Y.obj (op (Over.mk g))) :
    yoneda.obj (Over.mk (𝟙 (B.obj hT))) ⟶ (OverShriek.relocalizeRestrict g).obj Y :=
  yonedaEquiv.symm (show ((OverShriek.relocalizeRestrict g).obj Y).obj
    (op (Over.mk (𝟙 (B.obj hT)))) from v)

/-- The fibre of `f : X ⟶ Y` over a section of `Y` over an object `T ⟶ S` of the big fppf
site, as a presheaf on the big fppf site of `T`. -/
noncomputable def restrictedFibre (f : X ⟶ Y) {T : Scheme.{u}} (hT : B.Contains T)
    (g : B.obj hT ⟶ B.obj hS) (v : Y.obj (op (Over.mk g))) :
    (BigFppfOver B T hT)ᵒᵖ ⥤ Type u :=
  pullback ((OverShriek.relocalizeRestrict g).map f) (restrictedSection B S hS Y hT g v)

/-- The fibre over a section is an algebraic space over `T`. -/
theorem isAlgebraicSpace_restrictedFibre (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {T : Scheme.{u}} (hT : B.Contains T)
    (g : B.obj hT ⟶ B.obj hS) (v : Y.obj (op (Over.mk g))) :
    IsAlgebraicSpace B T hT (restrictedFibre B S hS f hT g v) :=
  isAlgebraicSpace_pullback_mkId
    (isAlgebraicSpace_relocalizeRestrict B T S hT hS g X hX)
    (isAlgebraicSpace_relocalizeRestrict B T S hT hS g Y hY) _ _

section Comparison

variable (f : X ⟶ Y) {T T' : Scheme.{u}} (hT : B.Contains T) (hT' : B.Contains T')
  (g : B.obj hT ⟶ B.obj hS) (m : B.obj hT' ⟶ B.obj hT) (v : Y.obj (op (Over.mk g)))

/-- The terminal object of the big fppf site of `T'`, viewed over `T`. -/
private def terminalIso :
    yoneda.obj (Over.mk (𝟙 (B.obj hT'))) ≅
      (OverShriek.relocalizeRestrict m).obj (yoneda.obj (Over.mk (𝟙 (B.obj hT)))) :=
  NatIso.ofComponents
    (fun W => Equiv.toIso
      { toFun := fun _ => Over.homMk (W.unop.hom ≫ m) (by simp)
        invFun := fun _ => Over.homMk W.unop.hom (by simp)
        left_inv := fun _ => Over.mkIdTerminal.hom_ext _ _
        right_inv := fun _ => Over.mkIdTerminal.hom_ext _ _ })
    (fun _ => by ext _; exact Over.mkIdTerminal.hom_ext _ _)

private theorem terminalIso_hom_comp_restrictedSection :
    (terminalIso B hT hT' m).hom ≫
        (OverShriek.relocalizeRestrict m).map (restrictedSection B S hS Y hT g v) =
      restrictedSection B S hS Y hT' (m ≫ g) (Y.map (Over.homMk m rfl).op v) := by
  ext W h
  show Y.map ((Over.map g).map (Over.homMk (W.unop.hom ≫ m) (by simp) :
        (Over.map m).obj W.unop ⟶ Over.mk (𝟙 (B.obj hT)))).op v =
      Y.map ((Over.map (m ≫ g)).map h).op (Y.map (Over.homMk m rfl).op v)
  rw [← Functor.map_comp_apply, ← op_comp]
  refine congrArg (fun t => Y.map (Quiver.Hom.op t) v) (Over.OverMorphism.ext ?_)
  have hh : h.left ≫ 𝟙 (B.obj hT') = W.unop.hom := Over.w h
  simp only [Over.comp_left, Over.map_map_left]
  show W.unop.hom ≫ m = h.left ≫ m
  simpa using congrArg (fun t => t ≫ m) hh.symm

/-- The fibre over a section restricted along `m` is the restriction along `m` of the fibre:
restriction preserves fibre products, and it carries the tautological section of `Y` over `T`
to the tautological section over `T'`. -/
private noncomputable def restrictedFibreRestrictIso :
    restrictedFibre B S hS f hT' (m ≫ g) (Y.map (Over.homMk m rfl).op v) ≅
      (OverShriek.relocalizeRestrict m).obj (restrictedFibre B S hS f hT g v) := by
  letI : PreservesLimitsOfShape WalkingCospan
      (OverShriek.relocalizeRestrict m :
        ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B T' hT')ᵒᵖ ⥤ Type u)) :=
    ((OverShriek.relocalizeAdjunction m).rightAdjoint_preservesLimits).preservesLimitsOfShape
  have h₁ : (OverShriek.relocalizeRestrict m).map ((OverShriek.relocalizeRestrict g).map f) ≫
        𝟙 ((OverShriek.relocalizeRestrict m).obj ((OverShriek.relocalizeRestrict g).obj Y)) =
      𝟙 ((OverShriek.relocalizeRestrict m).obj ((OverShriek.relocalizeRestrict g).obj X)) ≫
        (OverShriek.relocalizeRestrict m).map ((OverShriek.relocalizeRestrict g).map f) := by
    simp
  have h₂ : ((terminalIso B hT hT' m).hom ≫ (OverShriek.relocalizeRestrict m).map
          (restrictedSection B S hS Y hT g v)) ≫
        𝟙 ((OverShriek.relocalizeRestrict m).obj ((OverShriek.relocalizeRestrict g).obj Y)) =
      (terminalIso B hT hT' m).hom ≫ (OverShriek.relocalizeRestrict m).map
        (restrictedSection B S hS Y hT g v) := by
    simp
  have hIso := pullback.map_isIso
    ((OverShriek.relocalizeRestrict m).map ((OverShriek.relocalizeRestrict g).map f))
    ((terminalIso B hT hT' m).hom ≫
      (OverShriek.relocalizeRestrict m).map (restrictedSection B S hS Y hT g v))
    ((OverShriek.relocalizeRestrict m).map ((OverShriek.relocalizeRestrict g).map f))
    ((OverShriek.relocalizeRestrict m).map (restrictedSection B S hS Y hT g v))
    (𝟙 _) (terminalIso B hT hT' m).hom (𝟙 _) h₁ h₂
  refine ?_ ≪≫ @asIso _ _ _ _ _ hIso ≪≫
    (PreservesPullback.iso (OverShriek.relocalizeRestrict m)
      ((OverShriek.relocalizeRestrict g).map f) (restrictedSection B S hS Y hT g v)).symm
  exact pullback.congrHom
    (show (OverShriek.relocalizeRestrict (m ≫ g)).map f =
      (OverShriek.relocalizeRestrict m).map ((OverShriek.relocalizeRestrict g).map f) from rfl)
    (terminalIso_hom_comp_restrictedSection B S hS hT hT' g m v).symm

end Comparison

/-- Étaleness of a morphism of presheaves on the big fppf site is unchanged by composing with
an isomorphism. -/
private theorem isEtale_comp_iso {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (e : G ≅ H) (hf : IsEtale B S hS f) : IsEtale B S hS (f ≫ e.hom) := by
  intro V φ hφ
  have hQ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso := inferInstance
  simpa only [Category.assoc] using
    MorphismProperty.RespectsIso.postcomp _ e.hom (φ ≫ f) (hf V φ hφ)

/-- Geometric reducedness of an algebraic space over a field is invariant under isomorphism:
by Stacks 0DMS it is a condition on the étale scheme charts, and composition with the
isomorphism matches up the charts of the two spaces. -/
theorem isGeometricallyReduced_congr_iso (k : Type u) [Field k] (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    {F G : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (Spec (.of k)) hk F)
    (hG : IsAlgebraicSpace B (Spec (.of k)) hk G) (e : F ≅ G) :
    IsGeometricallyReduced k B hk F hF ↔ IsGeometricallyReduced k B hk G hG := by
  rw [isGeometricallyReduced_iff_forall_etaleChart k B hk F hF,
    isGeometricallyReduced_iff_forall_etaleChart k B hk G hG]
  exact ⟨fun h U a ha => h U (a ≫ e.inv) (isEtale_comp_iso B _ hk a e.symm ha),
    fun h U a ha => h U (a ≫ e.hom) (isEtale_comp_iso B _ hk a e ha)⟩

section FieldExtension

variable (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

/-- **Stacks 0E04 for a fibre.** The fibre over a section defined over a field `k` is
geometrically reduced over `k` exactly when the fibre over the restricted section, defined
over a field extension `K/k`, is geometrically reduced over `K`. -/
private theorem isGeometricallyReduced_restrictedFibre_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (g : B.obj hk ⟶ B.obj hS) (v : Y.obj (op (Over.mk g))) :
    IsGeometricallyReduced k B hk (restrictedFibre B S hS f hk g v)
        (isAlgebraicSpace_restrictedFibre B S hS f hX hY hk g v) ↔
      IsGeometricallyReduced K B hK
        (restrictedFibre B S hS f hK (fieldExtensionMap B k K hk hK ≫ g)
          (Y.map (Over.homMk (fieldExtensionMap B k K hk hK) rfl).op v))
        (isAlgebraicSpace_restrictedFibre B S hS f hX hY hK _ _) :=
  (isGeometricallyReduced_relocalizeRestrict_iff k K B hk hK
    (restrictedFibre B S hS f hk g v)
    (isAlgebraicSpace_restrictedFibre B S hS f hX hY hk g v)).trans
    (isGeometricallyReduced_congr_iso K B hK _ _
      (restrictedFibreRestrictIso B S hS f hk hK g (fieldExtensionMap B k K hk hK) v)).symm

/-- Geometric reducedness of the fibre is unchanged when the section is restricted along a
morphism of field spectra of the site. -/
private theorem isGeometricallyReduced_restrictedFibre_congr
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (g : B.obj hk ⟶ B.obj hS) (g' : B.obj hK ⟶ B.obj hS)
    (hg : fieldExtensionMap B k K hk hK ≫ g = g')
    (v : Y.obj (op (Over.mk g))) (v' : Y.obj (op (Over.mk g')))
    (hv : v' = Y.map (Over.homMk (fieldExtensionMap B k K hk hK) hg).op v) :
    IsGeometricallyReduced k B hk (restrictedFibre B S hS f hk g v)
        (isAlgebraicSpace_restrictedFibre B S hS f hX hY hk g v) ↔
      IsGeometricallyReduced K B hK (restrictedFibre B S hS f hK g' v')
        (isAlgebraicSpace_restrictedFibre B S hS f hX hY hK g' v') := by
  subst hg hv
  exact isGeometricallyReduced_restrictedFibre_fieldExtension B S hS f hX hY k K hk hK g v

end FieldExtension

section BaseChange

variable (f : X ⟶ Y) {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y' ⟶ Y)
  {T : Scheme.{u}} (hT : B.Contains T) (gT : B.obj hT ⟶ B.obj hS)
  (v : Y'.obj (op (Over.mk gT)))

/-- **The fibre of a base change is a fibre of the original morphism.** The fibre of
`X ×_Y Y' ⟶ Y'` over a section `v` of `Y'` is the fibre of `f` over the section of `Y`
underneath it. -/
noncomputable def restrictedFibreBaseChangeIso :
    restrictedFibre B S hS (pullback.snd f g) hT gT v ≅
      restrictedFibre B S hS f hT gT (g.app (op (Over.mk gT)) v) := by
  letI : PreservesLimitsOfShape WalkingCospan
      (OverShriek.relocalizeRestrict gT :
        ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u)) :=
    ((OverShriek.relocalizeAdjunction gT).rightAdjoint_preservesLimits).preservesLimitsOfShape
  have hσ : restrictedSection B S hS Y' hT gT v ≫ (OverShriek.relocalizeRestrict gT).map g =
      restrictedSection B S hS Y hT gT (g.app (op (Over.mk gT)) v) := by
    ext W h
    exact NatTrans.naturality_apply g ((Over.map gT).map h).op v
  have h₁ : (OverShriek.relocalizeRestrict gT).map (pullback.snd f g) ≫
        𝟙 ((OverShriek.relocalizeRestrict gT).obj Y') =
      (PreservesPullback.iso (OverShriek.relocalizeRestrict gT) f g).hom ≫
        pullback.snd ((OverShriek.relocalizeRestrict gT).map f)
          ((OverShriek.relocalizeRestrict gT).map g) := by
    rw [Category.comp_id,
      PreservesPullback.iso_hom_snd (OverShriek.relocalizeRestrict gT) f g]
  have h₂ : restrictedSection B S hS Y' hT gT v ≫
        𝟙 ((OverShriek.relocalizeRestrict gT).obj Y') =
      𝟙 (yoneda.obj (Over.mk (𝟙 (B.obj hT)))) ≫ restrictedSection B S hS Y' hT gT v := by
    simp
  have hIso := pullback.map_isIso
    ((OverShriek.relocalizeRestrict gT).map (pullback.snd f g))
    (restrictedSection B S hS Y' hT gT v)
    (pullback.snd ((OverShriek.relocalizeRestrict gT).map f)
      ((OverShriek.relocalizeRestrict gT).map g))
    (restrictedSection B S hS Y' hT gT v)
    (PreservesPullback.iso (OverShriek.relocalizeRestrict gT) f g).hom (𝟙 _) (𝟙 _) h₁ h₂
  exact @asIso _ _ _ _ _ hIso ≪≫
    pullbackLeftPullbackSndIso ((OverShriek.relocalizeRestrict gT).map f)
      ((OverShriek.relocalizeRestrict gT).map g)
      (restrictedSection B S hS Y' hT gT v) ≪≫
    pullback.congrHom rfl hσ

end BaseChange

section Locus

variable (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

/-- The fibre of `f : X ⟶ Y` over a field-valued point `p` of `Y`, as a presheaf on the big
fppf site of the field of definition of `p`. -/
noncomputable def fibreOverFieldValuedPoint (p : FieldValuedPoint B S hS Y) :
    (BigFppfOver B (Spec (.of p.carrier)) p.contained)ᵒᵖ ⥤ Type u :=
  restrictedFibre B S hS f p.contained ⟨p.toBase⟩ p.value

include hX hY

/-- The fibre over a field-valued point is an algebraic space over the field. -/
theorem isAlgebraicSpace_fibreOverFieldValuedPoint (p : FieldValuedPoint B S hS Y) :
    IsAlgebraicSpace B (Spec (.of p.carrier)) p.contained
      (fibreOverFieldValuedPoint B S hS f p) :=
  isAlgebraicSpace_restrictedFibre B S hS f hX hY p.contained _ _

/-- The fibre of `f` over a field-valued point of `Y` is geometrically reduced over the field
of definition of that point. -/
abbrev IsGeometricallyReducedFibre (p : FieldValuedPoint B S hS Y) : Prop :=
  IsGeometricallyReduced p.carrier B p.contained (fibreOverFieldValuedPoint B S hS f p)
    (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY p)

/-- Geometric reducedness of the fibre does not change when the field-valued point is
replaced by an extension of it: the fibre over the extension is the base change of the fibre
to the larger field, and geometric reducedness is insensitive to that by Stacks 0E04. -/
private theorem isGeometricallyReducedFibre_iff_of_dominates
    {p s : FieldValuedPoint B S hS Y} (h : FieldValuedPoint.Dominates B S hS Y s p) :
    IsGeometricallyReducedFibre B S hS f hX hY p ↔
      IsGeometricallyReducedFibre B S hS f hX hY s := by
  obtain ⟨f₀, hf₀⟩ := h
  let _ : Algebra p.carrier s.carrier :=
    (Spec.preimage (B.inclusion.map f₀.left)).hom.toAlgebra
  have hm : fieldExtensionMap B p.carrier s.carrier p.contained s.contained = f₀.left := by
    apply B.inclusion.map_injective
    rw [map_fieldExtensionMap]
    show Spec.map (CommRingCat.ofHom (Spec.preimage (B.inclusion.map f₀.left)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hg : fieldExtensionMap B p.carrier s.carrier p.contained s.contained ≫
      (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS) = ⟨s.toBase⟩ := by
    rw [hm]
    exact Over.w f₀
  refine isGeometricallyReduced_restrictedFibre_congr B S hS f hX hY p.carrier s.carrier
    p.contained s.contained ⟨p.toBase⟩ ⟨s.toBase⟩ hg p.value s.value ?_
  rw [← hf₀]
  exact congrArg (fun t => Y.map (Quiver.Hom.op t) p.value)
    (Over.OverMorphism.ext hm.symm)

/-- Geometric reducedness of the fibre depends only on the point of `|Y|` represented by the
field-valued point, since two representatives of one point have a common extension. -/
private theorem isGeometricallyReducedFibre_iff_of_class_eq
    {p q : FieldValuedPoint B S hS Y} (h : q.class B S hS Y = p.class B S hS Y) :
    IsGeometricallyReducedFibre B S hS f hX hY q ↔
      IsGeometricallyReducedFibre B S hS f hX hY p := by
  obtain ⟨r, hrq, hrp⟩ := (FieldValuedPoint.class_eq_class_iff B S hS Y q p).mp h
  exact (isGeometricallyReducedFibre_iff_of_dominates B S hS f hX hY hrq).trans
    (isGeometricallyReducedFibre_iff_of_dominates B S hS f hX hY hrp).symm

/-- The set of points of `|Y|` at which the fibre of `f` is geometrically reduced: those
admitting a field-valued representative whose fibre is geometrically reduced. -/
def geometricallyReducedFibreLocus : Set (points B S hS Y) :=
  {y | ∃ p : FieldValuedPoint B S hS Y, p.class B S hS Y = y ∧
    IsGeometricallyReducedFibre B S hS f hX hY p}

/-- A point of `|Y|` lies in the geometrically reduced fibre locus exactly when the fibre over
*any* chosen field-valued representative of it is geometrically reduced. -/
theorem mem_geometricallyReducedFibreLocus_iff (p : FieldValuedPoint B S hS Y) :
    p.class B S hS Y ∈ geometricallyReducedFibreLocus B S hS f hX hY ↔
      IsGeometricallyReducedFibre B S hS f hX hY p :=
  ⟨fun ⟨_, hq, hred⟩ =>
    (isGeometricallyReducedFibre_iff_of_class_eq B S hS f hX hY hq).mp hred,
   fun h => ⟨p, rfl, h⟩⟩

/-- **Stacks 0E08.** The fibre of `f : X ⟶ Y` at a point `y` of `|Y|` is *geometrically reduced*
when the equivalent conditions of Stacks 0E07 hold: the fibre over some — equivalently, every —
field-valued representative of `y` is geometrically reduced over the field of that
representative. -/
@[stacks 0E08]
abbrev IsGeometricallyReducedFibreAt (y : points B S hS Y) : Prop :=
  y ∈ geometricallyReducedFibreLocus B S hS f hX hY

/-- The fibre of `f` at the point of `|Y|` represented by a field-valued point `p` is
geometrically reduced exactly when the fibre over `p` is geometrically reduced over the field
of `p`. -/
theorem isGeometricallyReducedFibreAt_class_iff (p : FieldValuedPoint B S hS Y) :
    IsGeometricallyReducedFibreAt B S hS f hX hY (p.class B S hS Y) ↔
      IsGeometricallyReducedFibre B S hS f hX hY p :=
  mem_geometricallyReducedFibreLocus_iff B S hS f hX hY p

end Locus

/-- **Stacks 0E09.** The locus of points with geometrically reduced fibre commutes with base
change: the fibre of the base change `X ×_Y Y' ⟶ Y'` over a point of `|Y'|` is geometrically
reduced exactly when the fibre of `f` over the image of that point in `|Y|` is. -/
@[stacks 0E09]
theorem geometricallyReducedFibreLocus_pullback {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y') :
    geometricallyReducedFibreLocus B S hS (pullback.snd f g)
        (isAlgebraicSpace_pullback B S hS f g hX hY' hY) hY' =
      pointsMap B S hS Y' g ⁻¹' geometricallyReducedFibreLocus B S hS f hX hY := by
  ext y'
  obtain ⟨p, rfl⟩ := Quot.exists_rep y'
  refine Iff.trans (mem_geometricallyReducedFibreLocus_iff B S hS (pullback.snd f g)
      (isAlgebraicSpace_pullback B S hS f g hX hY' hY) hY' p)
    (Iff.trans ?_ (mem_geometricallyReducedFibreLocus_iff B S hS f hX hY
      (FieldValuedPoint.map B S hS Y' g p)).symm)
  exact isGeometricallyReduced_congr_iso p.carrier B p.contained _ _
    (restrictedFibreBaseChangeIso B S hS f g p.contained ⟨p.toBase⟩ p.value)

section Reduced

/-- Every field-valued point is dominated by one whose field of definition is perfect: an
algebraic closure of the field of definition is again small enough for the chosen big fppf
site, and the section restricts along the resulting morphism of field spectra.

This is not `AlgebraicGeometry.Space.exists_geometricRepresentative`, which produces a
representative of a given *point* of `|F|` and therefore relates the new field-valued point to
no prescribed one. The domination recorded here is what lets a property of the fibre over `q`
be carried back to the fibre over `p`. -/
theorem exists_dominates_perfectField (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : FieldValuedPoint B S hS F) :
    ∃ q : FieldValuedPoint B S hS F, PerfectField q.carrier ∧
      FieldValuedPoint.Dominates B S hS F q p := by
  have hkbar : B.Contains (Spec (.of (AlgebraicClosure p.carrier))) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit p.contained
      ((Algebra.IsAlgebraic.cardinalMk_le_max p.carrier (AlgebraicClosure p.carrier)).trans_eq
        (max_comm _ _))
  let φ : Spec (.of (AlgebraicClosure p.carrier)) ⟶ Spec (.of p.carrier) :=
    Spec.map (CommRingCat.ofHom (algebraMap p.carrier (AlgebraicClosure p.carrier)))
  let m : (Over.mk (⟨φ ≫ p.toBase⟩ : B.obj hkbar ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
      p.siteObject := Over.homMk (⟨φ⟩ : B.obj hkbar ⟶ B.obj p.contained) (by ext; rfl)
  exact ⟨{ carrier := AlgebraicClosure p.carrier
           contained := hkbar
           toBase := φ ≫ p.toBase
           value := F.map m.op p.value }, inferInstance, ⟨m, rfl⟩⟩

/-- **Stacks 0E07.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` and a point `y`
of `|Y|` the following are equivalent: (1) the fibre `X_k` is geometrically reduced over `k`
for *some* morphism `Spec k ⟶ Y` in the equivalence class of `y`; (2) the same for *every*
such morphism; (3) the fibre `X_k` is reduced for every such morphism.

Conditions (1) and (2) agree because geometric reducedness of the fibre only depends on the
point of `|Y|` represented by the field-valued point, two representatives of one point having
a common extension. Condition (3) implies (2) because every representative is dominated by
one whose field of definition is algebraically closed, hence perfect, where reducedness of
the fibre already gives geometric reducedness. -/
@[stacks 0E07]
theorem isGeometricallyReducedFibre_tfae (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (y : points B S hS Y) :
    List.TFAE
      [ ∃ p : FieldValuedPoint B S hS Y, p.class B S hS Y = y ∧
          IsGeometricallyReducedFibre B S hS f hX hY p,
        ∀ p : FieldValuedPoint B S hS Y, p.class B S hS Y = y →
          IsGeometricallyReducedFibre B S hS f hX hY p,
        ∀ p : FieldValuedPoint B S hS Y, p.class B S hS Y = y →
          HasEtaleLocalProperty B (Spec (.of p.carrier)) p.contained
            (fibreOverFieldValuedPoint B S hS f p) (fun T : Scheme.{u} => IsReduced T) ] := by
  tfae_have 1 → 2 := by
    rintro ⟨p, hp, hred⟩ q hq
    exact (isGeometricallyReducedFibre_iff_of_class_eq B S hS f hX hY
      (hq.trans hp.symm)).mpr hred
  tfae_have 2 → 1 := by
    intro h
    obtain ⟨p, rfl⟩ := Quot.exists_rep y
    exact ⟨p, rfl, h p rfl⟩
  tfae_have 2 → 3 := fun h p hp =>
    hasEtaleLocalProperty_isReduced_of_isGeometricallyReduced p.carrier B p.contained _
      (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY p) (h p hp)
  tfae_have 3 → 2 := by
    intro h p hp
    obtain ⟨q, hqperf, hdom⟩ := exists_dominates_perfectField B S hS Y p
    have hclass : q.class B S hS Y = y :=
      Eq.trans (FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS Y
        ⟨q, FieldValuedPoint.dominates_refl B S hS Y q, hdom⟩) hp
    exact (isGeometricallyReducedFibre_iff_of_dominates B S hS f hX hY hdom).mpr
      (isGeometricallyReduced_of_isReduced q.carrier B q.contained _
        (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY q) (h q hclass))
  tfae_finish

/-- The fibre of `f` at a point of `|Y|` is geometrically reduced exactly when the fibre over
*every* field-valued representative of that point is geometrically reduced over its field. -/
theorem isGeometricallyReducedFibreAt_iff_forall (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (y : points B S hS Y) :
    IsGeometricallyReducedFibreAt B S hS f hX hY y ↔
      ∀ p : FieldValuedPoint B S hS Y, p.class B S hS Y = y →
        IsGeometricallyReducedFibre B S hS f hX hY p :=
  (isGeometricallyReducedFibre_tfae B S hS f hX hY y).out 1 2

/-- The fibre of `f` at a point of `|Y|` is geometrically reduced exactly when the fibre over
every field-valued representative of that point is reduced, étale-locally on charts. -/
theorem isGeometricallyReducedFibreAt_iff_forall_isReduced (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (y : points B S hS Y) :
    IsGeometricallyReducedFibreAt B S hS f hX hY y ↔
      ∀ p : FieldValuedPoint B S hS Y, p.class B S hS Y = y →
        HasEtaleLocalProperty B (Spec (.of p.carrier)) p.contained
          (fibreOverFieldValuedPoint B S hS f p) (fun T : Scheme.{u} => IsReduced T) :=
  (isGeometricallyReducedFibre_tfae B S hS f hX hY y).out 1 3

end Reduced

end AlgebraicGeometry.Space

end
