module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectCornerTilde
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectEssSurjFunctor

/-!
# The canonical comparison of Stacks Tag 0D2J is the affine coherence of Tag 0EXC

`MilnorPatching.OneGeneratorFrobenius.finProjComparison` sends a finite projective
`A ⧸ (J ∩ fA)`-module `L` to the pair of its two reductions together with the canonical
identification of their two further extensions of scalars to `A ⧸ (J + fA)`. This file
identifies that structural isomorphism with the comparison
`AlgebraicGeometry.FinProj.extendScalarsCompOf` of the two extensions along the two composites,
and feeds the identification to `AlgebraicGeometry.tildeVectPullbackIso_corner`. The outcome is
the hypothesis `H` of `AlgebraicGeometry.vectCornerFlat` for the exceptional corner of Stacks
Example 0EVG.

## Main results

* `AlgebraicGeometry.extensionOfScalarsToPullback_comp_obj_iso_hom`: **the structural
  isomorphism of `ModuleGlueing.extensionOfScalarsToPullback`, read after the comparison of the
  extension of scalars along the composite through one corner**, is the transport along the
  commuting square followed by the comparison through the other corner.
* `AlgebraicGeometry.extendScalarsCompOf_extensionOfScalarsToPullback`: **the structural
  isomorphism of the canonical comparison intertwines the two comparisons
  `AlgebraicGeometry.FinProj.extendScalarsCompOf`** of the extensions of scalars along the two
  composites.
* `AlgebraicGeometry.tildeVectPullbackIso_cornerFlat`: **the affine comparison over the
  exceptional corner in the shape `AlgebraicGeometry.vectCornerFlat` consumes it.**
* `AlgebraicGeometry.OneGeneratorSquare.tildeVect_cornerFlat_hyp`: **that hypothesis for the
  compatible pair attached to a finite projective `A ⧸ (J ∩ fA)`-module.**

## Implementation notes

Every statement whose proof needs a definitional comparison of two spellings of one extension of
scalars is proved with the ring maps left as variables, because the kernel compares
`ModuleCat.extendScalars φ` with `ModuleCat.extendScalars ψ` by congruence only while `φ` and `ψ`
are variables; for the concrete reductions out of `A ⧸ (J ∩ fA)` the same comparison exhausts its
budget. Concretely:

* `AlgebraicGeometry.eqToIso_extendScalars_hom_app_congr` identifies the transport of
  `ModuleCat.extendScalars` along an equality of morphisms of `CommRingCat` with the transport
  along the corresponding equality of ring maps. The two equalities have definitionally equal but
  differently spelled types, so this is proof irrelevance; stated for variable morphisms it is
  immediate, and instantiating it later costs nothing.
* `AlgebraicGeometry.finProj_extensionOfScalarsToPullback_comp` takes the structural isomorphism
  as a variable `κ` together with the equation `hκ` identifying it on underlying modules. This is
  what lets `AlgebraicGeometry.FinProj.extendScalarsCongr_hom_app_hom` — a reflexivity lemma
  whose two sides carry different spellings of one type — be used as a rewrite at all: in the
  variable setting the resulting term is still definitionally checkable, and at the concrete
  instance it is not.

`AlgebraicGeometry.OneGeneratorSquare.tildeVect_cornerFlat_hyp` is stated for the morphisms
`AlgebraicGeometry.OneGeneratorSquare.ctrToExc` and `…modToExc` of the square, while its proof
instantiates the general statement at
`MilnorPatching.OneGeneratorFrobenius.toBase` and `…surjection`; the two agree by definition, and
spelling the statement in the square's own names is what makes it usable downstream.

## References

* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius
open MilnorPatching.OneGeneratorFrobenius

universe u

namespace AlgebraicGeometry

/-! ### Transport of extension of scalars along an equality of ring maps -/

/-- **Transporting `ModuleCat.extendScalars` along an equality of morphisms of `CommRingCat` is
transporting it along the corresponding equality of ring maps.** The two equalities prove
definitionally equal propositions, so this is proof irrelevance; it is stated for variable
morphisms because that is the only setting in which the kernel checks the two propositions equal
cheaply. -/
lemma eqToIso_extendScalars_hom_app_congr {R T : CommRingCat.{u}} {φ ψ : R ⟶ T}
    (h : φ = ψ) (h' : φ.hom = ψ.hom) (M : ModuleCat.{u} R) :
    (eqToIso (congrArg (fun α : R ⟶ T ↦ ModuleCat.extendScalars.{u, u, u} α.hom) h)).hom.app M =
      (eqToIso (congrArg ModuleCat.extendScalars h')).hom.app M :=
  rfl

/-! ### The structural isomorphism of the comparison into the categorical pullback -/

/-- **The structural isomorphism of `ModuleGlueing.extensionOfScalarsToPullback`, read after the
comparison of the extension of scalars along one of the two composites.** Extending scalars along
`r₂` and then along `ε₂`, compared with extending along the composite, and then identified with
the extension along `r₁` and `ε₁`, is the transport along the commuting square followed by the
comparison for the other composite. -/
lemma extensionOfScalarsToPullback_comp_obj_iso_hom {R S₁ S₂ T : CommRingCat.{u}}
    (r₁ : R ⟶ S₁) (r₂ : R ⟶ S₂) (ε₁ : S₁ ⟶ T) (ε₂ : S₂ ⟶ T)
    (comm : ε₂.hom.comp r₂.hom = ε₁.hom.comp r₁.hom) (hq : r₂ ≫ ε₂ = r₁ ≫ ε₁)
    (M : ModuleCat.{u} R) :
    (ModuleGlueing.extendScalarsComp.{u, u, u, u} r₂.hom ε₂.hom).hom.app M ≫
        ((ModuleGlueing.extensionOfScalarsToPullback.{u, u, u, u, u} r₂.hom r₁.hom ε₂.hom ε₁.hom
          comm).obj M).iso.hom =
      (eqToIso (congrArg (fun α : R ⟶ T ↦ ModuleCat.extendScalars.{u, u, u} α.hom)
            hq)).hom.app M ≫
        (ModuleGlueing.extendScalarsComp.{u, u, u, u} r₁.hom ε₁.hom).hom.app M :=
  ((congrArg
        (fun z ↦ (ModuleGlueing.extendScalarsComp.{u, u, u, u} r₂.hom ε₂.hom).hom.app M ≫ z)
        (extensionOfScalarsToPullback_obj_iso_hom r₂.hom r₁.hom ε₂.hom ε₁.hom comm M)).trans
      (Iso.hom_inv_id_app_assoc
        (ModuleGlueing.extendScalarsComp.{u, u, u, u} r₂.hom ε₂.hom) M _)).trans
    (congrArg (fun z ↦ z ≫ (ModuleGlueing.extendScalarsComp.{u, u, u, u} r₁.hom ε₁.hom).hom.app M)
      (eqToIso_extendScalars_hom_app_congr hq comm M).symm)

/-- **The same identification on finite projective modules.** The structural isomorphism is given
as a morphism `κ` of `AlgebraicGeometry.FinProj` together with the equation identifying it on
underlying modules, so that the reflexivity lemmas computing the comparisons on underlying
modules are applied with the ring maps still variables. -/
lemma finProj_extensionOfScalarsToPullback_comp {R S₁ S₂ T : CommRingCat.{u}}
    (r₁ : R ⟶ S₁) (r₂ : R ⟶ S₂) (ε₁ : S₁ ⟶ T) (ε₂ : S₂ ⟶ T)
    (comm : ε₂.hom.comp r₂.hom = ε₁.hom.comp r₁.hom) (hq : r₂ ≫ ε₂ = r₁ ≫ ε₁)
    (L : FinProj R)
    (κ : (FinProj.extendScalars r₂ ⋙ FinProj.extendScalars ε₂).obj L ⟶
      (FinProj.extendScalars r₁ ⋙ FinProj.extendScalars ε₁).obj L)
    (hκ : κ.hom =
      ((ModuleGlueing.extensionOfScalarsToPullback.{u, u, u, u, u} r₂.hom r₁.hom ε₂.hom ε₁.hom
        comm).obj L.obj).iso.hom) :
    (FinProj.extendScalarsComp r₂ ε₂).hom.app L ≫ κ =
      (FinProj.extendScalarsCongr hq).hom.app L ≫
        (FinProj.extendScalarsComp r₁ ε₁).hom.app L := by
  refine ObjectProperty.hom_ext _ ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, FinProj.extendScalarsComp_hom_app_hom,
    FinProj.extendScalarsCongr_hom_app_hom]
  rw [hκ]
  exact extensionOfScalarsToPullback_comp_obj_iso_hom r₁ r₂ ε₁ ε₂ comm hq L.obj

/-- **The structural isomorphism of the comparison into the categorical pullback intertwines the
two comparisons `AlgebraicGeometry.FinProj.extendScalarsCompOf`** of the extensions of scalars
along the two composites `R ⟶ T`. This is the hypothesis `hκ` of
`AlgebraicGeometry.tildeVectPullbackIso_corner`. -/
lemma extendScalarsCompOf_extensionOfScalarsToPullback {R S₁ S₂ T : CommRingCat.{u}}
    (r₁ : R ⟶ S₁) (r₂ : R ⟶ S₂) (ε₁ : S₁ ⟶ T) (ε₂ : S₂ ⟶ T)
    (comm : ε₂.hom.comp r₂.hom = ε₁.hom.comp r₁.hom) (hq : r₂ ≫ ε₂ = r₁ ≫ ε₁)
    (L : FinProj R)
    (κ : (FinProj.extendScalars r₂ ⋙ FinProj.extendScalars ε₂).obj L ⟶
      (FinProj.extendScalars r₁ ⋙ FinProj.extendScalars ε₁).obj L)
    (hκ : κ.hom =
      ((ModuleGlueing.extensionOfScalarsToPullback.{u, u, u, u, u} r₂.hom r₁.hom ε₂.hom ε₁.hom
        comm).obj L.obj).iso.hom) :
    (FinProj.extendScalarsCompOf r₂ ε₂ (r₁ ≫ ε₁) hq).hom.app L ≫ κ =
      (FinProj.extendScalarsCompOf r₁ ε₁ (r₁ ≫ ε₁) rfl).hom.app L := by
  rw [FinProj.extendScalarsCompOf_hom_app, extendScalarsCompOf_rfl_hom_app, Category.assoc,
    finProj_extensionOfScalarsToPullback_comp r₁ r₂ ε₁ ε₂ comm hq L κ hκ, ← Category.assoc,
    FinProj.extendScalarsCongr_trans_hom_app hq.symm hq rfl,
    FinProj.extendScalarsCongr_refl_hom_app, Category.id_comp]

/-! ### The affine comparison in the shape of the flat coherence -/

/-- **The affine content of the compatibility over the exceptional corner, in the shape
`AlgebraicGeometry.vectCornerFlat` consumes it.** This is
`AlgebraicGeometry.tildeVectPullbackIso_corner` with the trailing comparison of
`AlgebraicGeometry.tildeVectPullbackIso` for `ε₁` cancelled; the morphism `w` over the corner is
given as a variable with its defining equation, so that a consumer supplies a morphism of its own
spelling. -/
theorem tildeVectPullbackIso_cornerFlat {R S₁ S₂ T : CommRingCat.{u}} (r₁ : R ⟶ S₁) (r₂ : R ⟶ S₂)
    (ε₁ : S₁ ⟶ T) (ε₂ : S₂ ⟶ T) (q : R ⟶ T) (hq₁ : r₁ ≫ ε₁ = q) (hq₂ : r₂ ≫ ε₂ = q)
    (L : FinProj R)
    (κ : (FinProj.extendScalars r₂ ⋙ FinProj.extendScalars ε₂).obj L ⟶
      (FinProj.extendScalars r₁ ⋙ FinProj.extendScalars ε₁).obj L)
    (hκ : (FinProj.extendScalarsCompOf r₂ ε₂ q hq₂).hom.app L ≫ κ =
      (FinProj.extendScalarsCompOf r₁ ε₁ q hq₁).hom.app L)
    (hv : Spec.map ε₁ ≫ Spec.map r₁ = Spec.map ε₂ ≫ Spec.map r₂)
    (w : (Scheme.Vect.pullback (Spec.map ε₂)).obj
          ((tildeVect S₂).obj ((FinProj.extendScalars r₂).obj L)) ⟶
      (Scheme.Vect.pullback (Spec.map ε₁)).obj
        ((tildeVect S₁).obj ((FinProj.extendScalars r₁).obj L)))
    (hw : w = (tildeVectPullbackIso ε₂).hom.app ((FinProj.extendScalars r₂).obj L) ≫
      (tildeVect T).map κ ≫
        (tildeVectPullbackIso ε₁).inv.app ((FinProj.extendScalars r₁).obj L)) :
    (Scheme.Vect.pullback (Spec.map ε₁)).map ((tildeVectPullbackIso r₁).hom.app L) =
      ((Scheme.Vect.pullbackComp (Spec.map ε₁) (Spec.map r₁)).hom.app ((tildeVect R).obj L) ≫
          (Scheme.Vect.pullbackCongr hv).hom.app ((tildeVect R).obj L) ≫
            (Scheme.Vect.pullbackComp (Spec.map ε₂) (Spec.map r₂)).inv.app
              ((tildeVect R).obj L)) ≫
        (Scheme.Vect.pullback (Spec.map ε₂)).map ((tildeVectPullbackIso r₂).hom.app L) ≫ w := by
  subst hw
  rw [← cancel_mono ((tildeVectPullbackIso ε₁).hom.app ((FinProj.extendScalars r₁).obj L)),
    tildeVectPullbackIso_corner r₁ r₂ ε₁ ε₂ q hq₁ hq₂ L κ hκ hv]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]

/-! ### The exceptional corner of the one-generator square -/

namespace OneGeneratorSquare

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A)
  (L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))))

/-- **The two reductions of `A ⧸ (J ∩ fA)` give the same map to the exceptional corner after
`Spec`.** This is `Spec` of
`MilnorPatching.OneGeneratorFrobenius.ofHom_toBase_comp_factor_eq`. -/
theorem specMap_factor_square :
    Spec.map (ctrToExc A f J) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f}))) =
      Spec.map (modToExc A f J) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (inf_le_left : J ⊓ Ideal.span {f} ≤ J))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (ofHom_toBase_comp_factor_eq f J)).symm

/-- **The flat coherence hypothesis over the exceptional corner for the compatible pair attached
to a finite projective `A ⧸ (J ∩ fA)`-module.** The comparison of
`AlgebraicGeometry.tildeVectPullbackIso` for the reduction to the centre, restricted to the
corner, is the comparison for the reduction to the modification followed by the structural
isomorphism `AlgebraicGeometry.OneGeneratorSquare.finProjCornerIso` of the compatible pair. -/
theorem tildeVect_cornerFlat_hyp :
    (Scheme.Vect.pullback (Spec.map (ctrToExc A f J))).map
        ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
          (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))).hom.app L) =
      ((Scheme.Vect.pullbackComp (Spec.map (ctrToExc A f J))
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
                (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f}))))).hom.app
            ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L) ≫
          (Scheme.Vect.pullbackCongr (specMap_factor_square A f J)).hom.app
              ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L) ≫
            (Scheme.Vect.pullbackComp (Spec.map (modToExc A f J))
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
                  (inf_le_left : J ⊓ Ideal.span {f} ≤ J))))).inv.app
              ((tildeVect (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))).obj L)) ≫
        (Scheme.Vect.pullback (Spec.map (modToExc A f J))).map
            ((tildeVectPullbackIso (CommRingCat.ofHom (Ideal.Quotient.factor
              (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))).hom.app L) ≫
          (finProjCornerIso A f J L).hom :=
  tildeVectPullbackIso_cornerFlat
    (CommRingCat.ofHom (Ideal.Quotient.factor
      (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))
    (CommRingCat.ofHom (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))
    (CommRingCat.ofHom (surjection f J)) (CommRingCat.ofHom (toBase f J)) _ rfl
    (CommRingCat.hom_ext (ofHom_toBase_comp_factor_eq f J)) L
    (((finProjComparison A f J).obj L).iso.hom)
    (extendScalarsCompOf_extensionOfScalarsToPullback _ _ _ _
      (ofHom_toBase_comp_factor_eq f J)
      (CommRingCat.hom_ext (ofHom_toBase_comp_factor_eq f J)) L _
      (finProjComparison_obj_iso_hom_hom A f J L))
    (specMap_factor_square A f J) (finProjCornerIso A f J L).hom rfl

end OneGeneratorSquare

end AlgebraicGeometry

end
