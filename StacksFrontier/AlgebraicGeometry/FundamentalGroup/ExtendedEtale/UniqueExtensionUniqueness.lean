module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DepthCoherence.ReflexiveExtension
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionCover
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of the finite extension of a finite étale cover

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` an open immersion whose complement consists
of points at which `𝒪_X` has depth at least two, and `π : V ⟶ U` a finite étale morphism. The
relative spectrum of `𝓑 = (π ≫ j)_* 𝒪_V` is a finite extension of `X` restricting to the given
cover over `U` and again having depth at least two off `U`. This file proves that it is the
*only* such extension: any other one is uniquely isomorphic to it over `X` and compatibly with
the cover.

## Main results

* `extendedEtale_unique` — the uniqueness clause of [Stacks, Tag 0EY6].

The auxiliary results are of independent interest:

* `Stacks.RelativeSpec.isIso_chart_app` — a gluing chart of a relative spectrum induces an
  isomorphism on the sections over the part of the base it covers.
* `Stacks.RelativeSpec.relativeSpecPair_eq_id_of_eq` and
  `Stacks.RelativeSpec.relativeSpecPair_eq_of_pullback_eq` — the two bookkeeping facts about
  equality of relative-spectrum pairs that the comparison needs.
* `isIso_of_isIso_app_affineOpens` — a morphism of schemes affine over a common base is an
  isomorphism as soon as it is so on the sections over the inverse images of the affine opens of
  that base.
* `isIso_app_of_depth` — an open immersion into a locally Noetherian scheme whose complement has
  depth at least two induces isomorphisms on all sections. This is the depth input, and it is
  [Stacks, Tag 0E9I] in the form supplied by
  `Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive`.

## Implementation notes

**No `@[stacks]` attribute is placed here.** The bare tag `0EY6` has six clauses across eighteen
covering-set members and the audit scanner matches the bare four characters, so a single
attribute anywhere would render the whole tag as formalized.

Two bookkeeping hazards shape the proof and are worth naming.

*The second component of a relative-spectrum pair has a dependent type.*
`Stacks.RelativeSpec.RelativeSpecPair s T` is a `Σ f : T ⟶ s.base, …` whose second factor
mentions `f`, so extracting "the second components agree" from an equality of pairs lands in
`HEq` and `subst` is available in neither direction: the structure morphism of the competing
extension occurs in the definition of the comparison morphism, and the comparison morphism
occurs in the first component. The route taken is the one already used in
`Stacks.RelativeSpec.canonicalMap_on_affineOpen`: apply `congrArg` to a function out of a
*subtype* of pairs whose value type does not depend on the pair.

*An inverse in an `Under` category.* `CategoryTheory.inv` applied to a morphism of `Under`
objects requires the `IsIso` hypothesis to be stated for the same `Category` instance that
elaboration picks for the goal, and the two routes to that instance do not agree here. Rather
than invert in `Under`, `underInvOfIsIsoRight` produces an explicit two-sided inverse from
invertibility of the *underlying* morphism, which is where the hypothesis actually lives.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.FundamentalGroup.DepthCoherence
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.RelativeSpec

/-! ### Isomorphisms on the sections of a relative spectrum -/

/-- An open immersion induces an isomorphism on sections over `W` as soon as the restriction map
from `W` to the image of its preimage does. -/
private lemma isIso_app_of_isIso_map_homOfLE {T Y : Scheme.{u}} (g : T ⟶ Y) [IsOpenImmersion g]
    (W : Y.Opens) (h : IsIso (Y.presheaf.map (homOfLE (g.image_preimage_le W)).op)) :
    IsIso (g.app W) := by
  have : IsIso (g.app W ≫ (g.appIso (g ⁻¹ᵁ W)).inv) := by
    rw [g.app_appIso_inv]
    exact h
  exact IsIso.of_isIso_comp_right (g.app W) ((g.appIso (g ⁻¹ᵁ W)).inv)

/-- **A gluing chart of a relative spectrum is an isomorphism on the sections over the part of
the base that it covers.** The chart is an open immersion whose image is exactly that part, so
its section map differs from the identity by a restriction along an equality of opens. -/
public theorem isIso_chart_app (s : RelativeSpecSituation.{u}) (U : s.base.affineOpens) :
    have := isOpenImmersion_chart s U
    IsIso (((gluedSpectrum s).chart U).app ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)) := by
  have := isOpenImmersion_chart s U
  set k := (gluedSpectrum s).chart U with hk
  set O : (gluedSpectrum s).scheme.Opens := (gluedSpectrum s).toBase ⁻¹ᵁ U.1 with hO
  have himg : k ''ᵁ (k ⁻¹ᵁ O) = O := by
    rw [k.image_preimage_eq_opensRange_inf, show k.opensRange = O from chart_opensRange s U]
    exact inf_idem O
  exact isIso_app_of_isIso_map_homOfLE k O (isIso_map_homOfLE (k.image_preimage_le O) himg.ge)

/-! ### Equality of relative-spectrum pairs -/

/-- **A pair whose algebra component is the transport of the identity along an equality of base
morphisms is the identity pair.** This is the shape in which the comparison morphism is
recognized as the canonical one. -/
public theorem relativeSpecPair_eq_id_of_eq {T X : Scheme.{u}}
    (first second : T ⟶ X) (heq : first = second) :
    (⟨first, eqToHom (congrArg (fun morphism : T ⟶ X => Under.mk morphism.c) heq.symm)⟩ :
      Σ morphism : T ⟶ X, Under.mk second.c ⟶ Under.mk morphism.c) = ⟨second, 𝟙 _⟩ := by
  subst second
  rfl

/-- **Two relative-spectrum pairs over the same base morphism with the same pullback agree**, as
soon as pullback along the test morphism is monic on algebra maps — which it is when the test
morphism induces an isomorphism of pushed-forward structure sheaves. -/
public theorem relativeSpecPair_eq_of_pullback_eq
    {s : RelativeSpecSituation.{u}} {T T' : Scheme.{u}}
    (morphism : T' ⟶ T) (first second : RelativeSpecPair s T)
    (hbase : first.1 = second.1)
    [IsIso ((TopCat.Presheaf.pushforward CommRingCat second.1.base).map morphism.c)]
    (heq : RelativeSpecPair.pullback morphism first =
      RelativeSpecPair.pullback morphism second) : first = second := by
  obtain ⟨base, firstMap⟩ := first
  obtain ⟨otherBase, secondMap⟩ := second
  dsimp at hbase
  subst otherBase
  let algebraMap : Under.mk base.c ⟶ Under.mk (morphism ≫ base).c :=
    Under.homMk ((TopCat.Presheaf.pushforward CommRingCat base.base).map morphism.c) (by rfl)
  have : IsIso algebraMap := by
    have : IsIso ((Under.forget _).map algebraMap) :=
      inferInstanceAs (IsIso ((TopCat.Presheaf.pushforward CommRingCat base.base).map morphism.c))
    exact isIso_of_reflects_iso algebraMap (Under.forget _)
  obtain rfl : firstMap = secondMap :=
    (cancel_mono algebraMap).mp (eq_of_heq (Sigma.mk.inj heq).2)
  rfl

end Stacks.RelativeSpec

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

/-! ### Two small bookkeeping lemmas -/

/-- Restricting the sections of a scheme along the transport of an open along an equality with
itself is the identity. Stated as a lemma because the goal it closes sits under a telescope whose
types need the relative-spectrum situation unfolded, so `rw` cannot build its motive there. -/
private lemma map_eqToHom_op_self {Z : Scheme.{u}} {W : Z.Opens} (h : W = W) :
    Z.presheaf.map (eqToHom h).op = 𝟙 (Z.presheaf.obj (.op W)) := by
  rw [eqToHom_refl, op_id, Z.presheaf.map_id]

/-- **A morphism of `Under` objects whose underlying morphism is invertible has an explicit
two-sided inverse.** Stated as an existential rather than as `IsIso`, because the inverse is
wanted as a term: `CategoryTheory.inv` in an `Under` category asks for its `IsIso` argument at
the `Category` instance that elaboration picks for the goal, and the two routes to that instance
do not agree in the application below. -/
public theorem underInvOfIsIsoRight {T : Type*} [Category T] {Z : T} {a b : Under Z}
    (m : a ⟶ b) [IsIso m.right] : ∃ n : b ⟶ a, m ≫ n = 𝟙 a ∧ n ≫ m = 𝟙 b := by
  have hw : b.hom ≫ inv m.right = a.hom := by
    rw [← Under.w m, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨Under.homMk (inv m.right) hw, Under.UnderMorphism.ext ?_,
    Under.UnderMorphism.ext ?_⟩
  · change m.right ≫ inv m.right = Under.Hom.right (𝟙 a)
    rw [IsIso.hom_inv_id, Under.id_right]
  · change inv m.right ≫ m.right = Under.Hom.right (𝟙 b)
    rw [IsIso.inv_hom_id, Under.id_right]

/-! ### Two criteria for a morphism of schemes to be an isomorphism -/

/-- **A morphism of schemes affine over a common base is an isomorphism as soon as it is so on
the sections over the inverse images of the affine opens of that base.** Being an isomorphism is
Zariski-local at the target, and those inverse images cover. -/
public theorem isIso_of_isIso_app_affineOpens {T Y X : Scheme.{u}} (f : T ⟶ Y) (r : Y ⟶ X)
    [IsAffineHom r] [IsAffineHom (f ≫ r)]
    (h : ∀ W : X.affineOpens, IsIso (f.app (r ⁻¹ᵁ W.1))) : IsIso f := by
  have : IsAffineHom f := IsAffineHom.of_comp f r
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun W : X.affineOpens => r ⁻¹ᵁ W.1)
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · exact fun W => (isIso_morphismRestrict_iff_isIso_app f (W.2.preimage r)).mpr (h W)

/-- **An open immersion into a locally Noetherian scheme whose complement consists of points of
depth at least two induces an isomorphism on the sections over every open.** This is
[Stacks, Tag 0E9I] for the structure sheaf: the unit of the restriction adjunction at the
structure module is an isomorphism because that module is coherent and reflexive, and the
component of that unit over an open is exactly the restriction map whose invertibility is
asserted. -/
@[ega "IV 19.9.8" "special case", sga "2 III 3.5" "F = O_X; (1) ⇒ (2)"]
public theorem isIso_app_of_depth {T Y : Scheme.{u}} [IsLocallyNoetherian Y] (g : T ⟶ Y)
    [IsOpenImmersion g]
    (hdepth : ∀ y : Y, y ∉ (g.opensRange : Set Y) →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
    (W : Y.Opens) : IsIso (g.app W) := by
  have : _root_.SheafOfModules.IsCoherent (unitModule Y) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      g.opensRange.ι).unit.app (unitModule Y)) :=
    isIso_unit_of_isReflexive g.opensRange (unitModule Y) (isReflexive_unit Y) hdepth
  have heq := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction g.opensRange.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction g.opensRange.ι) (unitModule Y)
  have hrestrictUnit : IsIso ((Scheme.Modules.restrictAdjunction
      g.opensRange.ι).unit.app (unitModule Y)) := by
    have hwhole : IsIso ((Scheme.Modules.restrictAdjunction g.opensRange.ι).unit.app
        (unitModule Y) ≫ (Scheme.Modules.pushforward g.opensRange.ι).map
          (((Scheme.Modules.restrictAdjunction g.opensRange.ι).leftAdjointUniq
            (Scheme.Modules.pullbackPushforwardAdjunction g.opensRange.ι)).hom.app
            (unitModule Y))) := heq ▸ hunit
    exact IsIso.of_isIso_comp_right _
      ((Scheme.Modules.pushforward g.opensRange.ι).map
        (((Scheme.Modules.restrictAdjunction g.opensRange.ι).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction g.opensRange.ι)).hom.app
          (unitModule Y)))
  refine isIso_app_of_isIso_map_homOfLE g W ?_
  have hb := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictAdjunction g.opensRange.ι).unit.app (unitModule Y)).app W)
  rw [Scheme.Modules.restrictAdjunction_unit_app_app] at hb
  have h2 : IsIso (Y.presheaf.map
      (homOfLE (g.opensRange.ι.image_preimage_le W)).op) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have heq2 : g ''ᵁ g ⁻¹ᵁ W = g.opensRange.ι ''ᵁ g.opensRange.ι ⁻¹ᵁ W := by
    rw [g.image_preimage_eq_opensRange_inf, g.opensRange.ι.image_preimage_eq_opensRange_inf]
    simp
  have hcomp : Y.presheaf.map (homOfLE (g.image_preimage_le W)).op =
      Y.presheaf.map (homOfLE (g.opensRange.ι.image_preimage_le W)).op ≫
        Y.presheaf.map (eqToHom heq2).op := by
    rw [← Functor.map_comp]
    rfl
  rw [hcomp]
  infer_instance

/-! ### The uniqueness clause -/

/-- **The extension of a finite étale cover is the unique finite extension with the same
restriction over the open subscheme and the same depth condition off it.** This is the
uniqueness clause of [Stacks, Tag 0EY6]: for any finite `f' : Y' ⟶ X` whose restriction over
`U` is the given cover and whose local rings off `U` have depth at least two, there is exactly
one isomorphism of `Y'` with the relative spectrum of `(π ≫ j)_* 𝒪_V` commuting both with the
structure morphisms to `X` and with the canonical comparison from the cover. -/
@[stacks 0EY6 "unique_extension"]
public theorem extendedEtale_unique {U X V Y' : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))
    (f' : Y' ⟶ X) [IsFinite f'] (g' : V ⟶ Y')
    (hg' : IsPullback π g' j f')
    (hdepth' : ∀ y : Y', f' y ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (Y'.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y'.presheaf.stalk y))
        (Y'.presheaf.stalk y)) :
    ∃! e : Y' ≅ (gluedSpectrum (extendedEtaleSituation j π hdepth)).scheme,
      (e.hom ≫ (gluedSpectrum (extendedEtaleSituation j π hdepth)).toBase = f') ∧
      (g' ≫ e.hom = extendedEtaleCoverMap j π hdepth) := by
  classical
  let s := extendedEtaleSituation j π hdepth
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian f'
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback hg' inferInstance
  have : IsFinite (gluedSpectrum s).toBase :=
    isFinite_relativeSpectrum_extendedEtaleSituation j π hdepth
  -- the depth hypothesis transported to the complement of the cover inside `Y'`
  have hdepthg : ∀ y : Y', y ∉ (g'.opensRange : Set Y') →
      (2 : ℕ∞) ≤ Module.depth (Y'.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y'.presheaf.stalk y)) (Y'.presheaf.stalk y) := by
    refine fun y hy => hdepth' y fun hmem => ?_
    obtain ⟨point, hpoint⟩ := hmem
    obtain ⟨preimage, _, hpreimage⟩ := Scheme.exists_preimage_of_isPullback hg' point y hpoint
    exact hy ⟨preimage, hpreimage⟩
  -- the cover is an isomorphism on sections, hence so is the induced map of algebras
  have : IsIso g'.c := by
    have : ∀ W, IsIso (g'.c.app W) := fun W => isIso_app_of_depth g' hdepthg W.unop
    exact NatIso.isIso_of_isIso_app g'.c
  let algebraMap : Under.mk f'.c ⟶ Under.mk (g' ≫ f').c :=
    Under.homMk ((TopCat.Presheaf.pushforward CommRingCat f'.base).map g'.c) (by rfl)
  have : IsIso algebraMap.right :=
    inferInstanceAs (IsIso ((TopCat.Presheaf.pushforward CommRingCat f'.base).map g'.c))
  obtain ⟨algebraInv, hai1, hai2⟩ := underInvOfIsIsoRight algebraMap
  let transport : Under.mk (g' ≫ f').c ≅ Under.mk (π ≫ j).c :=
    eqToIso (congrArg (fun morphism : V ⟶ X => Under.mk morphism.c) hg'.w.symm)
  let comparison : Under.mk f'.c ⟶ Under.mk (π ≫ j).c := algebraMap ≫ transport.hom
  let cinv : Under.mk (π ≫ j).c ⟶ Under.mk f'.c := transport.inv ≫ algebraInv
  have hcc1 : comparison ≫ cinv = 𝟙 (Under.mk f'.c) := by
    change (algebraMap ≫ transport.hom) ≫ transport.inv ≫ algebraInv = _
    rw [Category.assoc, ← Category.assoc transport.hom transport.inv algebraInv,
      transport.hom_inv_id, Category.id_comp, hai1]
  have hcc2 : cinv ≫ comparison = 𝟙 (Under.mk (π ≫ j).c) := by
    change (transport.inv ≫ algebraInv) ≫ algebraMap ≫ transport.hom = _
    rw [Category.assoc, ← Category.assoc algebraInv algebraMap transport.hom, hai2,
      Category.id_comp, transport.inv_hom_id]
  -- the classifying morphism of the competing extension
  let ext : Y' ⟶ (gluedSpectrum s).scheme :=
    (relativeSpecRepresentableBy s).homEquiv.symm ⟨f', cinv⟩
  have hpair : (relativeSpecRepresentableBy s).homEquiv ext =
      (⟨f', cinv⟩ : RelativeSpecPair s Y') := Equiv.apply_symm_apply _ _
  have hbase : ext ≫ (gluedSpectrum s).toBase = f' :=
    (relativeSpecRepresentableBy_homEquiv_fst s ext).symm.trans (congrArg Sigma.fst hpair)
  have hcover : g' ≫ ext = extendedEtaleCoverMap j π hdepth := by
    refine (relativeSpecRepresentableBy s).homEquiv.injective ?_
    rw [Functor.RepresentableBy.homEquiv_comp, hpair, extendedEtaleCoverMap_homEquiv]
    change RelativeSpecPair.pullback g' (⟨f', cinv⟩ : RelativeSpecPair s Y') =
      (⟨π ≫ j, 𝟙 _⟩ : RelativeSpecPair s V)
    rw [Stacks.RelativeSpec.RelativeSpecPair.pullback_eq]
    have hmap : cinv ≫ algebraMap = eqToHom (congrArg
        (fun morphism : V ⟶ X => Under.mk morphism.c) hg'.w.symm.symm) := by
      change (transport.inv ≫ algebraInv) ≫ algebraMap = _
      rw [Category.assoc, hai2, Category.comp_id]
      rfl
    exact (congrArg
        (fun m : Under.mk (π ≫ j).c ⟶ Under.mk (g' ≫ f').c =>
          (⟨g' ≫ f', m⟩ : Σ morphism : V ⟶ X,
            Under.mk (π ≫ j).c ⟶ Under.mk morphism.c)) hmap).trans
      (relativeSpecPair_eq_id_of_eq (g' ≫ f') (π ≫ j) hg'.w.symm)
  -- the classifying morphism is an isomorphism
  have : IsAffineHom (ext ≫ (gluedSpectrum s).toBase) := by
    have haff : IsAffineHom f' := inferInstance
    rw [hbase]
    exact haff
  have : IsIso ext := by
    refine isIso_of_isIso_app_affineOpens ext (gluedSpectrum s).toBase fun W => ?_
    have hPP : RelativeSpecPair.pullback ext
        (⟨(gluedSpectrum s).toBase, universalAlgebraMap s⟩ :
          RelativeSpecPair s (gluedSpectrum s).scheme) =
        (⟨f', cinv⟩ : RelativeSpecPair s Y') :=
      (relativeSpecRepresentableBy_homEquiv s ext).symm.trans hpair
    have hfst : (RelativeSpecPair.pullback ext
        (⟨(gluedSpectrum s).toBase, universalAlgebraMap s⟩ :
          RelativeSpecPair s (gluedSpectrum s).scheme)).1 ⁻¹ᵁ W.1 = f' ⁻¹ᵁ W.1 :=
      congrArg (fun morphism : Y' ⟶ X => morphism ⁻¹ᵁ W.1) hbase
    let pairApp : {p : RelativeSpecPair s Y' // p.1 ⁻¹ᵁ W.1 = f' ⁻¹ᵁ W.1} →
        (s.algebra.right.obj.obj (.op W.1) ⟶ Y'.presheaf.obj (.op (f' ⁻¹ᵁ W.1))) :=
      fun p => p.1.2.right.app (.op W.1) ≫ Y'.presheaf.map (eqToHom p.2.symm).op
    have hmaps : pairApp ⟨_, hfst⟩ = pairApp ⟨⟨f', cinv⟩, rfl⟩ :=
      congrArg pairApp (Subtype.ext hPP)
    have hsplit : (universalAlgebraMap s).right.app (.op W.1) ≫
        ext.app ((gluedSpectrum s).toBase ⁻¹ᵁ W.1) ≫
          Y'.presheaf.map (eqToHom hfst.symm).op = cinv.right.app (.op W.1) := by
      refine Eq.trans ?_ (hmaps.trans ?_)
      · rfl
      · exact (congrArg (fun m => cinv.right.app (.op W.1) ≫ m)
          (map_eqToHom_op_self (Z := Y') (W := f' ⁻¹ᵁ W.1) _)).trans (Category.comp_id _)
    have hrestrict : IsIso (Y'.presheaf.map (eqToHom hfst.symm).op) := inferInstance
    have hcinv : IsIso (cinv.right.app (.op W.1)) := by
      refine ⟨comparison.right.app (.op W.1), ?_, ?_⟩
      · rw [← NatTrans.comp_app, ← Under.comp_right, hcc2, Under.id_right, NatTrans.id_app]
      · rw [← NatTrans.comp_app, ← Under.comp_right, hcc1, Under.id_right, NatTrans.id_app]
    have huniv := isIso_universalAlgebraMap_app s W
    have hwhole : IsIso ((universalAlgebraMap s).right.app (.op W.1) ≫
        ext.app ((gluedSpectrum s).toBase ⁻¹ᵁ W.1) ≫
          Y'.presheaf.map (eqToHom hfst.symm).op) := hsplit ▸ hcinv
    have hcomp : IsIso (ext.app ((gluedSpectrum s).toBase ⁻¹ᵁ W.1) ≫
        Y'.presheaf.map (eqToHom hfst.symm).op) :=
      @IsIso.of_isIso_comp_left _ _ _ _ _
        ((universalAlgebraMap s).right.app (.op W.1)) _ huniv hwhole
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      (ext.app ((gluedSpectrum s).toBase ⁻¹ᵁ W.1))
      (Y'.presheaf.map (eqToHom hfst.symm).op) hrestrict hcomp
  -- existence and uniqueness
  have hpullback : ∀ m : Y' ⟶ (gluedSpectrum s).scheme,
      RelativeSpecPair.pullback g'
          ((relativeSpecRepresentableBy s).homEquiv m) =
        (relativeSpecRepresentableBy s).homEquiv (g' ≫ m) := fun m =>
    ((relativeSpecRepresentableBy s).homEquiv_comp g' m).symm
  refine ⟨asIso ext, ⟨hbase, hcover⟩, fun other hother =>
    Iso.ext (?_ : other.hom = ext)⟩
  refine (relativeSpecRepresentableBy s).homEquiv.injective ?_
  refine relativeSpecPair_eq_of_pullback_eq g' _ _ ?_ ?_
  · rw [relativeSpecRepresentableBy_homEquiv_fst, relativeSpecRepresentableBy_homEquiv_fst]
    exact hother.1.trans hbase.symm
  · rw [hpullback other.hom, hpullback ext, hother.2, hcover]

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
