module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PseudoTorsors
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.AbelianTorsor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.FiberTorsor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.PushoutExtension

/-!
# Torsors and first cohomology

For an abelian sheaf on a site, the isomorphism classes of torsors under the
sheaf are canonically in bijection with its first cohomology group.

## Main results

* `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1` is the canonical bijection between
  isomorphism classes of torsors and first cohomology.
* `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_eq_boundary_iff` characterizes the
  bijection by fibers of short exact sequences and their connecting maps.
* `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_trivial` gives its normalization.
* `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_naturality` gives naturality in the
  coefficient sheaf.

## Implementation notes

A global section of an abelian sheaf is represented by a morphism from the
constant presheaf of integers. The connecting map is composition with the
extension class in `Ext`. The fiber characterization applies to every short
exact sequence: in particular, it identifies the fiber over a section of an
injective quotient with the boundary of that section. Applied to the pushout
extension constructed from the free abelian sheaf on a torsor, it identifies
that torsor's class with the boundary of the constant section one. Thus the
equivalence is specified, rather than merely an arbitrary bijection of sets.
Coefficient naturality is expressed using a morphism of torsor sheaves
equivariant with respect to the given morphism of abelian sheaves.

## References

* [The Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w t v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable [HasSheafify J AddCommGrpCat.{t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

/-- The canonical generator identifies a torsor with the fiber of the
extension constructed from it. -/
public def torsorPushoutFiberHom
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    F.1.Hom (fiberPseudoTorsor (torsorPushoutComplex H F)
      (torsorPushoutComplex_shortExact H F)
      (toSheafify J
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))))) where
  hom :=
    { app := fun U => ↾(fun s =>
        ⟨(torsorPushoutGenerator H F).app U s,
          torsorPushoutGenerator_projection H F U s⟩)
      naturality := by
        intro U V f
        ext s
        apply Subtype.ext
        exact (torsorPushoutGenerator H F).naturality_apply f s }
  map_act := by
    intro U g s
    apply Subtype.ext
    have hs := torsorPushoutGenerator_sub H F U (F.1.act U g s) s
    rw [torsorDifference_eq_of_act H F U (F.1.act U g s) s (Multiplicative.toAdd g) rfl] at hs
    exact sub_eq_iff_eq_add.mp hs

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorPushoutFiberHom_isIso
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    (torsorPushoutFiberHom H F).IsIso :=
  torsorHom_isIso H F
    (fiberTorsor (torsorPushoutComplex H F)
      (torsorPushoutComplex_shortExact H F)
      (toSheafify J
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))))
    (torsorPushoutFiberHom H F)

/-- An isomorphism of the middle terms of two pushout extensions, compatible
with their endpoint maps, induces an equivariant map of the unit fibers. -/
public def pushoutFiberHomOfIso
    (H : Sheaf J AddCommGrpCat.{t}) (F G : AbelianTorsor H)
    (φ : torsorPushoutMiddle H F ≅ torsorPushoutMiddle H G)
    (hf : (torsorPushoutComplex H F).f ≫ φ.hom = (torsorPushoutComplex H G).f)
    (hg : φ.hom ≫ (torsorPushoutComplex H G).g = (torsorPushoutComplex H F).g) :
    (fiberPseudoTorsor (torsorPushoutComplex H F)
      (torsorPushoutComplex_shortExact H F)
      (constantUnit (J := J) (C := C))).Hom
    (fiberPseudoTorsor (torsorPushoutComplex H G)
      (torsorPushoutComplex_shortExact H G)
      (constantUnit (J := J) (C := C))) where
  hom :=
    { app := fun U => ↾(fun x => ⟨φ.hom.hom.app U x.1, by
        have hU := congrArg (fun k => k.hom.app U x.1) hg
        have hx := x.2
        change (torsorPushoutComplex H G).g.hom.app U
          (φ.hom.hom.app U x.1) =
          (torsorPushoutComplex H F).g.hom.app U x.1 at hU
        change (torsorPushoutComplex H G).g.hom.app U
          (φ.hom.hom.app U x.1) = constantUnit.app U ⟨1⟩
        exact hU.trans hx⟩)
      naturality := by
        intro U V f
        ext x
        exact Subtype.ext (NatTrans.naturality_apply φ.hom.hom f x.1) }
  map_act := by
    intro U g s
    apply Subtype.ext
    have hfU := congrArg (fun k => k.hom.app U (Multiplicative.toAdd g)) hf
    have hadd : φ.hom.hom.app U
          ((torsorPushoutComplex H F).f.hom.app U (Multiplicative.toAdd g) + s.1) =
        φ.hom.hom.app U
            ((torsorPushoutComplex H F).f.hom.app U (Multiplicative.toAdd g)) +
          φ.hom.hom.app U s.1 :=
      map_add _ _ _
    refine hadd.trans ?_
    exact congrArg (fun c => c + φ.hom.hom.app U s.1) hfU

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma pushoutFiberHomOfIso_isIso
    (H : Sheaf J AddCommGrpCat.{t}) (F G : AbelianTorsor H)
    (φ : torsorPushoutMiddle H F ≅ torsorPushoutMiddle H G)
    (hf : (torsorPushoutComplex H F).f ≫ φ.hom = (torsorPushoutComplex H G).f)
    (hg : φ.hom ≫ (torsorPushoutComplex H G).g = (torsorPushoutComplex H F).g) :
    (pushoutFiberHomOfIso H F G φ hf hg).IsIso :=
  torsorHom_isIso H
    (fiberTorsor (torsorPushoutComplex H F)
      (torsorPushoutComplex_shortExact H F) (constantUnit (J := J) (C := C)))
    (fiberTorsor (torsorPushoutComplex H G)
      (torsorPushoutComplex_shortExact H G) (constantUnit (J := J) (C := C)))
    (pushoutFiberHomOfIso H F G φ hf hg)

/-- Equivariant maps of torsors preserve the class of the associated
pushout extension. -/
public lemma torsorPushoutClass_eq_of_hom
    (H : Sheaf J AddCommGrpCat.{t}) (F G : AbelianTorsor H)
    (e : F.1.Hom G.1) :
    torsorPushoutClass H F = torsorPushoutClass H G := by
  let S := torsorPushoutComplex H G
  let q := constantUnit (J := J) (C := C)
  let i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t} :=
    e.hom ≫ torsorPushoutGenerator H G
  have hi : ∀ (U : Cᵒᵖ) (h : H.obj.obj U) (s : F.1.presheaf.obj U),
      let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
      iU (F.1.act U (Multiplicative.ofAdd h) s) =
        S.f.hom.app U h + iU s := by
    intro U h s
    exact (congrArg (fun y => (torsorPushoutGenerator H G).app U y)
      (e.map_act U (Multiplicative.ofAdd h) s)).trans
      (torsorPushoutGenerator_act H G U h (e.hom.app U s))
  have hiFiber : ∀ (U : Cᵒᵖ) (s : F.1.presheaf.obj U),
      S.g.hom.app U (i.app U s) = q.app U ⟨1⟩ := by
    intro U s
    change (torsorPushoutProjection H G).hom.app U
      ((torsorPushoutGenerator H G).app U (e.hom.app U s)) = q.app U ⟨1⟩
    exact (torsorPushoutGenerator_projection H G U (e.hom.app U s)).trans
      (constantUnit_app_one U).symm
  have h := torsorPushout_extClass_eq_boundary S
    (torsorPushoutComplex_shortExact H G) q F i hi hiFiber
  rw [constantUnit_adj_inverse, Abelian.Ext.mk₀_id_comp] at h
  exact h

public lemma torsorPushoutClass_fiber
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    torsorPushoutClass S.X₁ (fiberTorsor S hS q) =
      (Abelian.Ext.mk₀ (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm q)).comp
        hS.extClass (zero_add 1) :=
  torsorPushout_extClass_eq_boundary S hS q
    (fiberTorsor S hS q) (fiberInclusion S q)
    (fiberInclusion_spec S hS q).1
    (fun _ s => s.2)

/-- The extension construction descends to isomorphism classes of torsors. -/
public noncomputable def torsorIsoClassesToH1
    (H : Sheaf J AddCommGrpCat.{t}) :
    torsorIsoClasses H → Sheaf.H H 1 :=
  Quotient.lift (torsorPushoutClass H) (by
    intro F G h
    obtain ⟨e, _⟩ := h
    exact torsorPushoutClass_eq_of_hom H F G e)

public lemma torsorIsoClassesToH1_surjective
    (H : Sheaf J AddCommGrpCat.{t}) :
    Function.Surjective (torsorIsoClassesToH1 H) := by
  intro x
  let B := (presheafToSheaf J AddCommGrpCat).obj
    ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))
  obtain ⟨E, i, p, w, hS, hx⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (Sheaf J AddCommGrpCat.{t}) B H).1 x
  let S : ShortComplex (Sheaf J AddCommGrpCat.{t}) := ShortComplex.mk i p w
  let q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj :=
    constantUnit (J := J) (C := C)
  refine ⟨Quotient.mk (torsorSetoid H) (fiberTorsor S hS q), ?_⟩
  change torsorPushoutClass H (fiberTorsor S hS q) = x
  have h := torsorPushoutClass_fiber S hS q
  rw [constantUnit_adj_inverse, Abelian.Ext.mk₀_id_comp] at h
  exact h.trans hx

public lemma torsorIsoClassesToH1_injective
    (H : Sheaf J AddCommGrpCat.{t}) :
    Function.Injective (torsorIsoClassesToH1 H) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ F =>
    induction y using Quotient.inductionOn with
    | _ G =>
      change torsorPushoutClass H F = torsorPushoutClass H G at h
      obtain ⟨φ, hf, hg⟩ :=
        ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
          (Sheaf J AddCommGrpCat.{t})
          (torsorPushoutComplex H F).X₃ H).2.1
          (torsorPushoutMiddle H F) (torsorPushoutMiddle H G)
          (torsorPushoutComplex H F).f (torsorPushoutComplex H F).g
          (torsorPushoutComplex H F).zero
          (torsorPushoutComplex H G).f (torsorPushoutComplex H G).g
          (torsorPushoutComplex H G).zero
          (torsorPushoutComplex_shortExact H F)
          (torsorPushoutComplex_shortExact H G)).1 h
      apply Quotient.sound
      have hF : F.IsIsomorphic
          (fiberTorsor (torsorPushoutComplex H F)
            (torsorPushoutComplex_shortExact H F)
            (constantUnit (J := J) (C := C))) :=
        ⟨torsorPushoutFiberHom H F, torsorPushoutFiberHom_isIso H F⟩
      have hG : G.IsIsomorphic
          (fiberTorsor (torsorPushoutComplex H G)
            (torsorPushoutComplex_shortExact H G)
            (constantUnit (J := J) (C := C))) :=
        ⟨torsorPushoutFiberHom H G, torsorPushoutFiberHom_isIso H G⟩
      have hFib : (fiberTorsor (torsorPushoutComplex H F)
          (torsorPushoutComplex_shortExact H F)
          (constantUnit (J := J) (C := C))).IsIsomorphic
          (fiberTorsor (torsorPushoutComplex H G)
            (torsorPushoutComplex_shortExact H G)
            (constantUnit (J := J) (C := C))) :=
        ⟨pushoutFiberHomOfIso H F G φ hf hg,
          pushoutFiberHomOfIso_isIso H F G φ hf hg⟩
      exact (torsorSetoid H).iseqv.trans
        ((torsorSetoid H).iseqv.trans hF hFib)
        ((torsorSetoid H).iseqv.symm hG)

/-- Vanishing of the boundary of a quotient section is equivalent to lifting
the section as a morphism of abelian presheaves. -/
public lemma boundary_eq_zero_iff_presheaf_lift
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    (Abelian.Ext.mk₀
        (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm q)).comp
          hS.extClass (zero_add 1) = 0 ↔
      ∃ r : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₂.obj,
        r ≫ S.g.hom = q := by
  let P := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))
  let adj := sheafificationAdjunction J AddCommGrpCat.{t}
  let q' : (presheafToSheaf J AddCommGrpCat).obj P ⟶ S.X₃ :=
    (adj.homEquiv P S.X₃).symm q
  have hq : adj.homEquiv P S.X₃ q' = q :=
    (adj.homEquiv P S.X₃).apply_symm_apply q
  change (Abelian.Ext.mk₀ q').comp hS.extClass (zero_add 1) = 0 ↔ _
  rw [ext_one_boundary_eq_zero_iff_lift S hS _ q']
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨adj.homEquiv P S.X₂ f, ?_⟩
    have h := adj.homEquiv_naturality_right f S.g
    change adj.homEquiv P S.X₃ (f ≫ S.g) =
      (adj.homEquiv P S.X₂ f) ≫ S.g.hom at h
    rw [hf, hq] at h
    exact h.symm
  · rintro ⟨r, hr⟩
    refine ⟨(adj.homEquiv P S.X₂).symm r, ?_⟩
    apply (adj.homEquiv P S.X₃).injective
    rw [adj.homEquiv_naturality_right, (adj.homEquiv P S.X₂).apply_symm_apply, hq]
    exact hr

/-- A quotient section has zero boundary exactly when its fiber has a
compatible global family of sections. -/
public lemma boundary_eq_zero_iff_fiberSectionFamily
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    (Abelian.Ext.mk₀
        (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm q)).comp
          hS.extClass (zero_add 1) = 0 ↔
      ∃ s : ∀ U, (fiberPseudoTorsor S hS q).presheaf.obj U,
        ∀ {U V : Cᵒᵖ} (f : U ⟶ V),
          (fiberPseudoTorsor S hS q).presheaf.map f (s U) = s V := by
  rw [boundary_eq_zero_iff_presheaf_lift S hS q]
  constructor
  · rintro ⟨r, hr⟩
    let s : ∀ U, (fiberPseudoTorsor S hS q).presheaf.obj U := fun U =>
      ⟨r.app U ⟨1⟩, by
        have h := congrArg (fun α => α.app U (⟨1⟩ : ULift.{t} ℤ)) hr
        simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h⟩
    exact ⟨s, fun f => Subtype.ext (sectionFamilyOfMorphism_naturality S.X₂.obj r f)⟩
  · rintro ⟨s, hs⟩
    let b : ∀ U, S.X₂.obj.obj U := fun U => (s U).1
    have hb : ∀ {U V : Cᵒᵖ} (f : U ⟶ V),
        S.X₂.obj.map f (b U) = b V := fun f => congrArg Subtype.val (hs f)
    let r := morphismOfSectionFamily S.X₂.obj b hb
    refine ⟨r, ?_⟩
    apply NatTrans.ext
    funext U
    apply liftedInt_hom_ext
    change S.g.hom.app U (r.app U ⟨1⟩) = q.app U ⟨1⟩
    rw [morphismOfSectionFamily_one]
    exact (s U).2

public lemma nonempty_globalSections_iff_sectionFamily
    (P : Cᵒᵖ ⥤ Type t) :
    Nonempty (GlobalSections P) ↔
      ∃ s : ∀ U, P.obj U,
        ∀ {U V : Cᵒᵖ} (f : U ⟶ V), P.map f (s U) = s V := by
  constructor
  · rintro ⟨σ⟩
    let τ : termPresheaf (C := C) ⟶ P := termIso.inv ≫ σ
    exact ⟨fun U => τ.app U PUnit.unit, fun f => (NatTrans.naturality_apply τ f PUnit.unit).symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨termIso.hom ≫ familyToNat P s hs⟩

/-- A quotient section has zero boundary exactly when its fiber torsor is
trivial. -/
public lemma boundary_eq_zero_iff_fiberTrivial
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    (Abelian.Ext.mk₀
        (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm q)).comp
          hS.extClass (zero_add 1) = 0 ↔
      Quotient.mk (torsorSetoid S.X₁)
        ⟨trivialTorsor (abelianSheafAsGroupSheaf S.X₁),
          trivialTorsor_isTorsor (abelianSheafAsGroupSheaf S.X₁)⟩ =
      Quotient.mk (torsorSetoid S.X₁) (fiberTorsor S hS q) := by
  rw [boundary_eq_zero_iff_fiberSectionFamily]
  rw [torsor_class_eq_trivial_iff]
  exact (nonempty_globalSections_iff_sectionFamily
    (fiberPseudoTorsor S hS q).presheaf).symm

/-- **Stacks Project, Tag 03AJ.** Isomorphism classes of torsors under an
abelian sheaf are canonically in bijection with its first cohomology group. -/
@[stacks 03AJ "the canonical bijection",
  sga "4½ Cycle 1.1.1" "the bijection",
  ega "IV 16.5.15" "abelian sheaf of groups",
  sga "4½ Arcata 2.2.1" "H^1 = torsor classes",
  sga "4½ Cycle 1.1" "H^1 ≅ torsor classes", sga "4½ Arcata 1.6.6" "H¹ = torsor classes"]
public noncomputable def torsorIsoClassesEquivH1
    (H : Sheaf J AddCommGrpCat.{t}) :
    torsorIsoClasses H ≃ Sheaf.H H 1 :=
  Equiv.ofBijective (torsorIsoClassesToH1 H)
    ⟨torsorIsoClassesToH1_injective H, torsorIsoClassesToH1_surjective H⟩

/-- The class of a torsor is the boundary of a global section precisely when
the torsor is equivariantly isomorphic to its fiber in the middle sheaf of
the short exact sequence. The embedding is required to be injective on
sections and to have exactly that fiber as its image. -/
@[stacks 03AJ "characterization by the boundary map and fiber torsor",
  sga "4½ Cycle 1.1.1" "normalization by ∂h"]
public lemma torsorIsoClassesEquivH1_eq_boundary_iff
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj)
    (F : AbelianTorsor S.X₁) :
    torsorIsoClassesEquivH1 S.X₁ (Quotient.mk (torsorSetoid S.X₁) F) =
        (Abelian.Ext.mk₀ (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm q)).comp
          hS.extClass (zero_add 1) ↔
      ∃ i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat,
        (∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U) (s : F.1.presheaf.obj U),
          let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
          iU (F.1.act U (Multiplicative.ofAdd h) s) = S.f.hom.app U h + iU s) ∧
        (∀ U : Cᵒᵖ, Function.Injective (i.app U)) ∧
        (∀ (U : Cᵒᵖ) (x : S.X₂.obj.obj U),
          S.g.hom.app U x = q.app U ⟨1⟩ ↔ ∃ s, i.app U s = x) := by
  change torsorPushoutClass S.X₁ F = _ ↔ _
  rw [← torsorPushoutClass_fiber S hS q]
  exact ⟨fun h => (fiberEmbedding_iff_isomorphic S hS q F).2
      (Quotient.exact (torsorIsoClassesToH1_injective S.X₁ h)),
    fun h => congrArg (torsorIsoClassesToH1 S.X₁)
      (Quotient.sound ((fiberEmbedding_iff_isomorphic S hS q F).1 h))⟩

/-- The trivial torsor corresponds to zero in first cohomology. -/
@[stacks 03AJ "normalization at the trivial torsor"]
public lemma torsorIsoClassesEquivH1_trivial (H : Sheaf J AddCommGrpCat.{t}) :
    torsorIsoClassesEquivH1 H
      (Quotient.mk (torsorSetoid H)
        ⟨trivialTorsor (abelianSheafAsGroupSheaf H),
          trivialTorsor_isTorsor (abelianSheafAsGroupSheaf H)⟩) = 0 := by
  let F : AbelianTorsor H :=
    ⟨trivialTorsor (abelianSheafAsGroupSheaf H),
      trivialTorsor_isTorsor (abelianSheafAsGroupSheaf H)⟩
  let S := torsorPushoutComplex H F
  let q := constantUnit (J := J) (C := C)
  have hClass : Quotient.mk (torsorSetoid H) F =
      Quotient.mk (torsorSetoid H)
        (fiberTorsor S (torsorPushoutComplex_shortExact H F) q) :=
    Quotient.sound ⟨torsorPushoutFiberHom H F,
      torsorPushoutFiberHom_isIso H F⟩
  have hz := (boundary_eq_zero_iff_fiberTrivial S
    (torsorPushoutComplex_shortExact H F) q).2 hClass
  rw [constantUnit_adj_inverse, Abelian.Ext.mk₀_id_comp] at hz
  exact hz

/-! ### Vanishing first cohomology trivializes every torsor

The three statements below are the consequence of [Stacks Project, Tag 03AJ] which every
deformation-theoretic torsor argument uses, including step (II) of [Stacks Project, Tag 04AM]:
once `H¹` of the acting sheaf is a subsingleton, a torsor under it has a global section.  They
were previously written out privately, twice, at two unrelated instantiations. -/

/-- **A torsor under an abelian sheaf whose first cohomology is a subsingleton has the class of
the trivial torsor.**  The bijection of [Stacks Project, Tag 03AJ] carries the trivial class to
`0` by `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_trivial`, so if the target of that
bijection has at most one element there is only one class. -/
public lemma torsor_class_eq_trivial_of_subsingleton_sheafH_one (H : Sheaf J AddCommGrpCat.{t})
    (hH : Subsingleton (Sheaf.H.{w} H 1)) (F : AbelianTorsor H) :
    Quotient.mk (torsorSetoid H)
        ⟨trivialTorsor (abelianSheafAsGroupSheaf H),
          trivialTorsor_isTorsor (abelianSheafAsGroupSheaf H)⟩ =
      Quotient.mk (torsorSetoid H) F :=
  (torsorIsoClassesEquivH1 H).injective
    ((torsorIsoClassesEquivH1_trivial H).trans (@Subsingleton.elim _ hH _ _))

/-- **A torsor under an abelian sheaf whose first cohomology is a subsingleton has a global
section.**  This is the previous statement read through
`Stacks.Cohomology.Torsors.torsor_class_eq_trivial_iff`. -/
public lemma nonempty_globalSections_of_subsingleton_sheafH_one
    (H : Sheaf J AddCommGrpCat.{t}) (hH : Subsingleton (Sheaf.H.{w} H 1))
    (F : AbelianTorsor H) :
    Nonempty (GlobalSections F.1.presheaf) :=
  (torsor_class_eq_trivial_iff H F).1
    (torsor_class_eq_trivial_of_subsingleton_sheafH_one H hH F)

/-- **A torsor under an abelian sheaf whose first cohomology is a subsingleton is trivial**, that
is isomorphic as a torsor to the sheaf acting on itself.  This is the previous statement read
through [Stacks Project, Tag 03AI], `isTrivial_iff_nonempty_globalSections`. -/
public lemma isTrivial_of_subsingleton_sheafH_one (H : Sheaf J AddCommGrpCat.{t})
    (hH : Subsingleton (Sheaf.H.{w} H 1)) (F : AbelianTorsor H) :
    F.1.IsTrivial :=
  (isTrivial_iff_nonempty_globalSections F.1 F.2).2
    (nonempty_globalSections_of_subsingleton_sheafH_one H hH F)

/-- An equivariant map of torsors relative to a morphism of coefficient
sheaves carries the torsor class to the induced first cohomology class. -/
private noncomputable def freeMap {P Q : Cᵒᵖ ⥤ Type t} (f : P ⟶ Q) :
    freeAbelianPresheaf P ⟶ freeAbelianPresheaf Q :=
  Functor.whiskerRight f AddCommGrpCat.free

private lemma freeMap_aug {P Q : Cᵒᵖ ⥤ Type t} (f : P ⟶ Q) :
    freeMap f ≫ freeAbelianPresheafAugmentation Q =
      freeAbelianPresheafAugmentation P := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro s
  change (FreeAbelianGroup.lift (fun _ : Q.obj U => (⟨1⟩ : ULift.{t} ℤ)))
      (FreeAbelianGroup.map (f.app U) (FreeAbelianGroup.of s)) =
    (FreeAbelianGroup.lift (fun _ : P.obj U => (⟨1⟩ : ULift.{t} ℤ)))
      (FreeAbelianGroup.of s)
  rw [FreeAbelianGroup.map_of_apply]
  simp only [FreeAbelianGroup.lift_apply_of]

private noncomputable def kernelMap {P Q : Cᵒᵖ ⥤ Type t} (f : P ⟶ Q) :
    freeAbelianPresheafAugmentationKernel P ⟶
      freeAbelianPresheafAugmentationKernel Q :=
  Limits.kernel.lift (freeAbelianPresheafAugmentation Q)
    (Limits.kernel.ι (freeAbelianPresheafAugmentation P) ≫ freeMap f)
    (by rw [Category.assoc, freeMap_aug, Limits.kernel.condition])

private lemma kernelMap_ι {P Q : Cᵒᵖ ⥤ Type t} (f : P ⟶ Q) :
    kernelMap f ≫ Limits.kernel.ι (freeAbelianPresheafAugmentation Q) =
      Limits.kernel.ι (freeAbelianPresheafAugmentation P) ≫ freeMap f :=
  Limits.kernel.lift_ι _ _ _

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
private lemma kernelMap_difference
    {H H' : Sheaf J AddCommGrpCat.{t}} (φ : H ⟶ H')
    (F : AbelianTorsor H) (F' : AbelianTorsor H')
    (f : F.1.presheaf ⟶ F'.1.presheaf)
    (hf : ∀ (U : Cᵒᵖ) (h : H.obj.obj U) (s : F.1.presheaf.obj U),
      f.app U (F.1.act U (Multiplicative.ofAdd h) s) =
        F'.1.act U (Multiplicative.ofAdd (φ.hom.app U h)) (f.app U s))
    (U : Cᵒᵖ) (x : (freeAbelianPresheafAugmentationKernel F.1.presheaf).obj U) :
    torsorAugmentationKernelMapAt H' F' U ((kernelMap f).app U x) =
      φ.hom.app U (torsorAugmentationKernelMapAt H F U x) := by
  classical
  let ιF := Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)
  let ιF' := Limits.kernel.ι (freeAbelianPresheafAugmentation F'.1.presheaf)
  have hι := congrArg (fun α => α.app U x) (kernelMap_ι f)
  change ιF'.app U ((kernelMap f).app U x) =
    FreeAbelianGroup.map (f.app U) (ιF.app U x) at hι
  by_cases hs : Nonempty (F.1.presheaf.obj U)
  · let s₀ := Classical.choice hs
    rw [torsorAugmentationKernelMapAt_eq H' F' U (f.app U s₀),
      torsorAugmentationKernelMapAt_eq H F U s₀]
    change torsorAffineLinearMap H' F' U (f.app U s₀)
        (ιF'.app U ((kernelMap f).app U x)) =
      φ.hom.app U (torsorAffineLinearMap H F U s₀ (ιF.app U x))
    rw [hι]
    exact torsorAffineLinearMap_map φ F F' f hf U s₀ (ιF.app U x)
  · have : IsEmpty (F.1.presheaf.obj U) := ⟨fun s => hs ⟨s⟩⟩
    have : Subsingleton ((freeAbelianPresheaf F.1.presheaf).obj U) := by
      change Subsingleton (FreeAbelianGroup (F.1.presheaf.obj U))
      infer_instance
    have hx : x = 0 :=
      (AddCommGrpCat.mono_iff_injective (ιF.app U)).1 inferInstance (Subsingleton.elim _ _)
    subst x
    simp

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
private lemma kernelMap_difference_nat
    {H H' : Sheaf J AddCommGrpCat.{t}} (φ : H ⟶ H')
    (F : AbelianTorsor H) (F' : AbelianTorsor H')
    (f : F.1.presheaf ⟶ F'.1.presheaf)
    (hf : ∀ (U : Cᵒᵖ) (h : H.obj.obj U) (s : F.1.presheaf.obj U),
      f.app U (F.1.act U (Multiplicative.ofAdd h) s) =
        F'.1.act U (Multiplicative.ofAdd (φ.hom.app U h)) (f.app U s)) :
    kernelMap f ≫ torsorAugmentationKernelMap H' F' =
      torsorAugmentationKernelMap H F ≫ φ.hom := by
  ext U x
  exact kernelMap_difference φ F F' f hf U x

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
private lemma sheafKernelMap_difference
    {H H' : Sheaf J AddCommGrpCat.{t}} (φ : H ⟶ H')
    (F : AbelianTorsor H) (F' : AbelianTorsor H')
    (f : F.1.presheaf ⟶ F'.1.presheaf)
    (hf : ∀ (U : Cᵒᵖ) (h : H.obj.obj U) (s : F.1.presheaf.obj U),
      f.app U (F.1.act U (Multiplicative.ofAdd h) s) =
        F'.1.act U (Multiplicative.ofAdd (φ.hom.app U h)) (f.app U s)) :
    (presheafToSheaf J AddCommGrpCat).map (kernelMap f) ≫
        torsorSheafAugmentationKernelMap H' F' =
      torsorSheafAugmentationKernelMap H F ≫ φ := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{t}
  apply (adj.homEquiv _ H').injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  dsimp only [adj, torsorSheafAugmentationKernelMap]
  simp only [Equiv.apply_symm_apply]
  change kernelMap f ≫ torsorAugmentationKernelMap H' F' =
    torsorAugmentationKernelMap H F ≫ φ.hom
  exact kernelMap_difference_nat φ F F' f hf

@[stacks 03AJ "naturality in the coefficient sheaf"]
public lemma torsorIsoClassesEquivH1_naturality
    {H H' : Sheaf J AddCommGrpCat.{t}} (φ : H ⟶ H')
    (F : AbelianTorsor H) (F' : AbelianTorsor H')
    (f : F.1.presheaf ⟶ F'.1.presheaf)
    (hf : ∀ (U : Cᵒᵖ) (h : H.obj.obj U) (s : F.1.presheaf.obj U),
      f.app U (F.1.act U (Multiplicative.ofAdd h) s) =
        F'.1.act U (Multiplicative.ofAdd (φ.hom.app U h)) (f.app U s)) :
    Sheaf.H.map φ 1 (torsorIsoClassesEquivH1 H (Quotient.mk (torsorSetoid H) F)) =
      torsorIsoClassesEquivH1 H' (Quotient.mk (torsorSetoid H') F') := by
  let A := presheafToSheaf J AddCommGrpCat.{t}
  let e := A.map (Limits.kernel.ι
    (freeAbelianPresheafAugmentation F.1.presheaf))
  let a := torsorSheafAugmentationKernelMap H F
  let e' := A.map (Limits.kernel.ι
    (freeAbelianPresheafAugmentation F'.1.presheaf))
  let a' := torsorSheafAugmentationKernelMap H' F'
  let l' := Limits.pushout.inl e' a'
  let r' := Limits.pushout.inr e' a'
  let fm := A.map (freeMap f)
  let km := A.map (kernelMap f)
  have he : e ≫ fm = km ≫ e' := by
    dsimp [e, fm, km, e', A]
    rw [← Functor.map_comp, ← Functor.map_comp, kernelMap_ι]
  have ha : km ≫ a' = a ≫ φ := sheafKernelMap_difference φ F F' f hf
  have hdesc : e ≫ (fm ≫ l') = a ≫ (φ ≫ r') := by
    calc
      e ≫ (fm ≫ l') = km ≫ (e' ≫ l') := by rw [← Category.assoc, he, Category.assoc]
      _ = km ≫ (a' ≫ r') := by rw [Limits.pushout.condition]
      _ = a ≫ (φ ≫ r') := by rw [← Category.assoc, ha, Category.assoc]
  let mid := Limits.pushout.desc (fm ≫ l') (φ ≫ r') hdesc
  have haug : fm ≫ freeAbelianSheafAugmentation F'.1.presheaf =
      freeAbelianSheafAugmentation F.1.presheaf := by
    change A.map (freeMap f) ≫ A.map (freeAbelianPresheafAugmentation F'.1.presheaf) =
      A.map (freeAbelianPresheafAugmentation F.1.presheaf)
    rw [← Functor.map_comp, freeMap_aug]
  have hproj : mid ≫ torsorPushoutProjection H' F' =
      torsorPushoutProjection H F := by
    apply Limits.pushout.hom_ext
    · change Limits.pushout.inl e a ≫ mid ≫ torsorPushoutProjection H' F' =
        Limits.pushout.inl e a ≫ torsorPushoutProjection H F
      rw [← Category.assoc, Limits.pushout.inl_desc]
      simpa only [Category.assoc, l', torsorPushoutProjection,
        Limits.pushout.inl_desc] using haug
    · change Limits.pushout.inr e a ≫ mid ≫ torsorPushoutProjection H' F' =
        Limits.pushout.inr e a ≫ torsorPushoutProjection H F
      have hz' : r' ≫ torsorPushoutProjection H' F' = 0 := by
        change Limits.pushout.inr e' a' ≫
          Limits.pushout.desc (freeAbelianSheafAugmentation F'.1.presheaf) 0 _ = 0
        exact Limits.pushout.inr_desc _ _ _
      have hz : Limits.pushout.inr e a ≫ torsorPushoutProjection H F = 0 := by
        change Limits.pushout.inr e a ≫
          Limits.pushout.desc (freeAbelianSheafAugmentation F.1.presheaf) 0 _ = 0
        exact Limits.pushout.inr_desc _ _ _
      rw [← Category.assoc, Limits.pushout.inr_desc]
      rw [Category.assoc, hz', Limits.comp_zero, hz]
  let ψ : torsorPushoutComplex H F ⟶ torsorPushoutComplex H' F' :=
    { τ₁ := φ
      τ₂ := mid
      τ₃ := 𝟙 _
      comm₁₂ := by
        change φ ≫ r' = Limits.pushout.inr e a ≫ mid
        exact (Limits.pushout.inr_desc _ _ _).symm
      comm₂₃ := by
        change mid ≫ torsorPushoutProjection H' F' =
          torsorPushoutProjection H F ≫ 𝟙 _
        simpa only [Category.comp_id] using hproj }
  have hnat := (torsorPushoutComplex_shortExact H F).extClass_naturality
    (torsorPushoutComplex_shortExact H' F') ψ
  change (torsorPushoutClass H F).comp (Abelian.Ext.mk₀ φ) (add_zero 1) =
    torsorPushoutClass H' F'
  simpa only [torsorPushoutClass, torsorPushoutComplex, constantSheaf,
    Functor.comp_obj, ψ, Abelian.Ext.mk₀_id_comp] using hnat

/-! ### Vanishing of `H¹` trivializes every torsor

The bijection `torsorIsoClassesEquivH1` of Tag 03AJ is stated as an equivalence of a quotient
with a cohomology group; the two packagings below are the forms a consumer needs when the
cohomology group is known to vanish. Neither carries a `@[stacks]` attribute: Tag 03AJ asserts
the bijection, and "a bijection with a subsingleton has subsingleton domain" is not a clause of
it, so these are repackagings of 03AJ rather than statements of any part of it.
-/

/-- **Vanishing of `H¹` trivializes every torsor.** If the first cohomology group of an abelian
sheaf `H` is a subsingleton then every torsor under `H` has a global section.

Both isomorphism classes, that of `F` and that of the trivial torsor, are sent by the bijection
of Tag 03AJ to elements of `Sheaf.H H 1`, which the hypothesis forces to be equal; injectivity
then identifies the two classes, and a torsor has the class of the trivial torsor exactly when
it has a global section (`torsor_class_eq_trivial_iff`). Note that the normalization
`torsorIsoClassesEquivH1_trivial` is not needed: the hypothesis equates the two images without
either of them having to be identified with `0`.

This is the converse of the implication that `H¹` vanishes as soon as every torsor has a global
section; both directions need `HasSheafify` and `HasExt` because both go through the bijection
of Tag 03AJ, which is where those instances are used. -/
public theorem nonempty_globalSections_of_subsingleton_sheafH1
    (H : Sheaf J AddCommGrpCat.{t}) (h : Subsingleton (Sheaf.H H 1))
    (F : AbelianTorsor H) :
    Nonempty (GlobalSections F.1.presheaf) :=
  (torsor_class_eq_trivial_iff H F).1
    ((torsorIsoClassesEquivH1 H).injective (h.allEq _ _))

/-- **Vanishing of `H¹` trivializes every torsor, in the `IsTrivial` form.** If the first
cohomology group of an abelian sheaf `H` is a subsingleton then every torsor under `H` is
isomorphic to the trivial one.

This is `nonempty_globalSections_of_subsingleton_sheafH1` followed by
`isTrivial_of_nonempty_globalSections`, which turns a global section into a trivialization and
needs no torsor axiom of its own. -/
public theorem isTrivial_of_subsingleton_sheafH1
    (H : Sheaf J AddCommGrpCat.{t}) (h : Subsingleton (Sheaf.H H 1))
    (F : AbelianTorsor H) :
    F.1.IsTrivial :=
  isTrivial_of_nonempty_globalSections F.1
    (nonempty_globalSections_of_subsingleton_sheafH1 H h F)

end Stacks.Cohomology.Torsors
