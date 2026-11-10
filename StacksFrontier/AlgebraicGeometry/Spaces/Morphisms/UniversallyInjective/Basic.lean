module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves

/-!
# Universally injective morphisms of algebraic spaces: definition and permanence

A morphism of algebraic spaces over a scheme `S` is *universally injective* (Stacks 03MV) when
every base change of it along a morphism from an algebraic space induces an injective map on
points. This file proves the characterization by field-valued points for representable
morphisms (Stacks 03MU), stability under base change (Stacks 03MW) and composition
(Stacks 03MY), and the field-point criterion of Stacks 040X, (1) implies (2).

See `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective` for the overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03MV.** A morphism is universally injective if every base change along an
algebraic space induces an injective map on points. -/
@[stacks 03MV]
abbrev UniversallyInjective {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y' → ∀ (g : Y' ⟶ Y),
    Function.Injective (pointsMap B S hS (pullback g f) (pullback.fst g f))

/-- A representable transformation all of whose represented base changes are universally
injective scheme morphisms is injective on field-valued points. -/
private theorem injective_app_of_universallyInjective_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (h : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyInjective : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) a)
    (K : Type u) [Field K] (T : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of K)) :
    Function.Injective (a.app (Opposite.op T)) := by
  classical
  intro x y hxy
  have ha := h.1
  let ix : yoneda.obj T ⟶ F := yonedaEquiv.symm x
  let iy : yoneda.obj T ⟶ F := yonedaEquiv.symm y
  let g : yoneda.obj T ⟶ G := ix ≫ a
  have hcomp : iy ≫ a = g := by
    simpa [g, ix, iy, hxy] using
      (yonedaEquiv_symm_naturality_right T a y).trans
        ((congrArg yonedaEquiv.symm hxy.symm).trans
          (yonedaEquiv_symm_naturality_right T a x).symm)
  let V := ha.pullback g
  let q := ha.snd g
  have hq : AlgebraicGeometry.UniversallyInjective
      ((BigFppfOver.toScheme B S hS).map q) :=
    h.2 (g := g) (fst := ha.fst g) (snd := q) (ha.isPullback g)
  have hlx : ix ≫ a = yoneda.map (𝟙 T) ≫ g := by simp [g]
  let lx := ha.lift ix (𝟙 T) hlx
  let ly := ha.lift iy (𝟙 T) (hcomp.trans hlx)
  have hfield : ∀ (K' : Type u) [Field K'], Function.Injective
      (fun z : Spec (.of K') ⟶ (BigFppfOver.toScheme B S hS).obj V =>
        z ≫ (BigFppfOver.toScheme B S hS).map q) :=
    ((AlgebraicGeometry.tfae_universallyInjective
      ((BigFppfOver.toScheme B S hS).map q)).out 1 2).mp hq
  have hmaps : (e.inv ≫ (BigFppfOver.toScheme B S hS).map lx) =
      (e.inv ≫ (BigFppfOver.toScheme B S hS).map ly) := by
    apply hfield K
    simp only [Category.assoc, ← (BigFppfOver.toScheme B S hS).map_comp]
    rw [ha.lift_snd, ha.lift_snd]
  have hlift : lx = ly :=
    (BigFppfOver.toScheme B S hS).map_injective ((cancel_epi e.inv).mp hmaps)
  have hsections : ix = iy := by
    have hf : yoneda.map lx ≫ ha.fst g = yoneda.map ly ≫ ha.fst g := by rw [hlift]
    simpa [lx, ly, ha.lift_fst] using hf
  simpa [ix, iy] using
    congrArg (fun z : yoneda.obj T ⟶ F => z.app (Opposite.op T) (𝟙 T)) hsections

/-- In a cartesian square over a representable transformation `a`, two morphisms into the
represented corner agree as soon as they agree after the projection `snd` and `a` is injective
on sections over their source. -/
private theorem eq_of_comp_snd_eq_of_isPullback {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} {U V T : BigFppfOver B S hS} {g : yoneda.obj U ⟶ G}
    {fst : yoneda.obj V ⟶ F} {snd : V ⟶ U} (hp : IsPullback fst (yoneda.map snd) a g)
    (hT : Function.Injective (a.app (Opposite.op T))) {t₁ t₂ : T ⟶ V}
    (hts : t₁ ≫ snd = t₂ ≫ snd) : t₁ = t₂ := by
  have hcomp : (yoneda.map t₁ ≫ fst) ≫ a = (yoneda.map t₂ ≫ fst) ≫ a := by
    simp only [Category.assoc, hp.w, ← Functor.map_comp_assoc, hts]
  have hfst : yoneda.map t₁ ≫ fst = yoneda.map t₂ ≫ fst :=
    yonedaEquiv.injective <| hT <| by
      rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, hcomp]
  exact yoneda.map_injective (hp.hom_ext hfst (by simpa using congrArg yoneda.map hts))

/-- A point of `X ×_Y X` whose residue field point has equal projections lies on the
diagonal. -/
private theorem exists_diagonal_apply_eq_of_fromSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    (z : (pullback f f : Scheme.{u}))
    (hz : (pullback f f).fromSpecResidueField z ≫ pullback.fst f f =
      (pullback f f).fromSpecResidueField z ≫ pullback.snd f f) :
    ∃ x, pullback.diagonal f x = z := by
  let W := pullback f f
  let K : Type u := W.residueField z
  let p : Spec (.of K) ⟶ W := W.fromSpecResidueField z
  have hdiag : p = (p ≫ pullback.fst f f) ≫ pullback.diagonal f := by cat_disch
  let c : Spec (.of K) :=
    ⟨IsLocalRing.closedPoint K, (IsLocalRing.closedPoint K).isPrime⟩
  refine ⟨(p ≫ pullback.fst f f) c, ?_⟩
  have heval := congrArg (fun k : Spec (.of K) ⟶ W => k c) hdiag
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, W.fromSpecResidueField_apply] at heval
  have hc : p c = z := by
    change W.fromSpecResidueField z c = z
    simp [Scheme.fromSpecResidueField_apply]
  rw [Scheme.Hom.comp_apply, hc]
  exact heval.symm

/-- A representable transformation injective on field-valued points has universally injective
scheme morphisms on all of its represented base changes. -/
private theorem universallyInjective_presheaf_of_injective_on_field_points
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : yoneda.relativelyRepresentable a)
    (h : ∀ (K : Type u) [Field K] (T : BigFppfOver B S hS),
        ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of K)) →
      Function.Injective (a.app (Opposite.op T))) :
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyInjective : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) a := by
  classical
  refine ⟨ha, ?_⟩
  intro U V g fst snd hp
  let f := (BigFppfOver.toScheme B S hS).map snd
  apply (AlgebraicGeometry.UniversallyInjective.iff_diagonal f).2
  rw [surjective_iff]
  intro z
  let W := pullback f f
  let K : Type u := W.residueField z
  let p : Spec (.of K) ⟶ W := W.fromSpecResidueField z
  have hK : (Spec (.of K)).size < B.cutoff :=
    (Scheme.size_le_of_mono_quasiCompact p).trans_lt <|
      (Scheme.size_pullback_le f f).trans_lt (max_lt V.left.property V.left.property)
  let t₀ : B.Schemes := B.obj hK
  let b : Spec (.of K) ⟶ S := p ≫ pullback.fst f f ≫ f ≫ B.inclusion.map U.hom
  let t₀s : t₀ ⟶ B.obj hS := B.inclusion.preimage b
  let T : BigFppfOver B S hS := Over.mk t₀s
  let r₁ : B.inclusion.obj t₀ ⟶ B.inclusion.obj V.left := p ≫ pullback.fst f f
  let r₂ : B.inclusion.obj t₀ ⟶ B.inclusion.obj V.left := p ≫ pullback.snd f f
  let r₁' : t₀ ⟶ V.left := B.inclusion.preimage r₁
  let r₂' : t₀ ⟶ V.left := B.inclusion.preimage r₂
  have hVhom : B.inclusion.map V.hom =
      B.inclusion.map snd.left ≫ B.inclusion.map U.hom := by
    rw [← snd.w, B.inclusion.map_comp]
  have hr₁ : r₁' ≫ V.hom = t₀s := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage, hVhom]
    simp [r₁, b, f, Category.assoc]
  have hr₂ : r₂' ≫ V.hom = t₀s := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage, hVhom]
    simp only [r₂, b, Category.assoc]
    exact whisker_eq p (pullback.condition_assoc _).symm
  let t₁ : T ⟶ V := Over.homMk r₁' hr₁
  let t₂ : T ⟶ V := Over.homMk r₂' hr₂
  have hmap₁ : B.inclusion.map r₁' = r₁ := B.inclusion.map_preimage r₁
  have hmap₂ : B.inclusion.map r₂' = r₂ := B.inclusion.map_preimage r₂
  have hts : t₁ ≫ snd = t₂ ≫ snd := by
    apply Over.OverMorphism.ext
    change r₁' ≫ snd.left = r₂' ≫ snd.left
    apply B.inclusion.map_injective
    simp only [B.inclusion.map_comp, hmap₁, hmap₂]
    simp only [r₁, r₂, Category.assoc]
    exact whisker_eq p pullback.condition
  have hbase : p ≫ pullback.fst f f = p ≫ pullback.snd f f :=
    hmap₁.symm.trans ((congrArg (fun t : T ⟶ V => B.inclusion.map t.left)
      (eq_of_comp_snd_eq_of_isPullback B S hS hp (h K T (Iso.refl _)) hts)).trans hmap₂)
  exact exists_diagonal_apply_eq_of_fromSpecResidueField f z hbase

/-- **Stacks 03MU.** A representable transformation is universally injective if and only if
its maps on field-valued points are injective. -/
@[stacks 03MU]
theorem universallyInjective_iff_injective_on_field_points
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : yoneda.relativelyRepresentable a) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyInjective : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) a ↔
      ∀ (K : Type u) [Field K] (T : BigFppfOver B S hS),
        ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of K)) →
      Function.Injective (a.app (Opposite.op T))) :=
  ⟨fun h _ _ T e => injective_app_of_universallyInjective_presheaf B S hS a h _ T e,
    universallyInjective_presheaf_of_injective_on_field_points B S hS a ha⟩

/-! ### Transport along an isomorphism -/

section Transport

variable {F F' G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If a morphism of presheaves on the big fppf site of `S` becomes, after precomposition with
an isomorphism, a morphism which is injective on points, then it is itself injective on
points. -/
theorem injective_pointsMap_of_comp_isIso (e : F ⟶ F') [IsIso e] {g : F' ⟶ G} {f : F ⟶ G}
    (hfg : e ≫ g = f) (hg : Function.Injective (pointsMap B S hS F' g)) :
    Function.Injective (pointsMap B S hS F f) := by
  subst hfg
  rw [pointsMap_comp]
  exact hg.comp (pointsMap_injective_of_mono B S hS e)

/-- The map on points of a composite is injective as soon as the maps on points of the two
factors are. -/
theorem injective_pointsMap_comp {f : F ⟶ G} {g : G ⟶ H}
    (hg : Function.Injective (pointsMap B S hS G g))
    (hf : Function.Injective (pointsMap B S hS F f)) :
    Function.Injective (pointsMap B S hS F (f ≫ g)) := by
  rw [pointsMap_comp]
  exact hg.comp hf

end Transport

/-! ### Base change -/

section BaseChange

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03MW.** A base change of a universally injective morphism of algebraic spaces
over `S` is universally injective.

Nothing is needed beyond unwinding the definition: a base change of `Z ×_Y X ⟶ Z` along
`k : W ⟶ Z` is a base change of `X ⟶ Y` along `k ≫ g`. -/
@[stacks 03MW, ega "IV 11.9.14" "base change stability"]
theorem universallyInjective_pullback (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : UniversallyInjective B S hS f) :
    UniversallyInjective B S hS (pullback.fst g f) := fun V hV k ↦
  injective_pointsMap_of_comp_isIso B S hS (pullbackRightPullbackFstIso g f k).hom
    (pullbackRightPullbackFstIso_hom_fst g f k) (hf V hV (k ≫ g))

/-- An isomorphism of presheaves on the big fppf site of `S` is universally injective: each of
its base changes is again an isomorphism, and an isomorphism is injective on points. -/
theorem universallyInjective_of_isIso (e : X ⟶ Y) [IsIso e] :
    UniversallyInjective B S hS e := fun V _ g ↦
  have : IsIso (pullback.fst g e) :=
    (IsPullback.of_isLimit (pullback.isLimit g e)).isIso_fst_of_isIso
  pointsMap_injective_of_mono B S hS (pullback.fst g e)

end BaseChange

/-! ### Composition -/

section Comp

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03MY.** A composition of universally injective morphisms of algebraic spaces over
`S` is universally injective.

The base change `W ×_Z X ⟶ W` of the composite along `k : W ⟶ Z` is identified by the pasting
isomorphism `W ×_Z X ≅ (W ×_Z Y) ×_Y X` with the composition of a base change of `X ⟶ Y` and a
base change of `Y ⟶ Z`. -/
@[stacks 03MY]
theorem universallyInjective_comp (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : UniversallyInjective B S hS f) (hg : UniversallyInjective B S hS g) :
    UniversallyInjective B S hS (f ≫ g) := by
  intro W hW k
  have hP : IsAlgebraicSpace B S hS (pullback k g) :=
    isAlgebraicSpace_pullback B S hS k g hW hY hZ
  exact injective_pointsMap_of_comp_isIso B S hS (pullbackLeftPullbackSndIso k g f).inv
    (pullbackLeftPullbackSndIso_inv_fst k g f)
    (injective_pointsMap_comp B S hS (hg W hW k) (hf (pullback k g) hP (pullback.snd k g)))

end Comp

/-! ### Base change along an arbitrary cartesian square -/

section Square

variable {A C Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03MW** for an arbitrary cartesian square: if `IsPullback a b g f` and `f` is
universally injective, then so is `a`.

This is `AlgebraicGeometry.Space.universallyInjective_pullback` composed with the
identification of the given square with the canonical fibre product. -/
@[stacks 03MW, ega "IV 11.9.14" "base change stability"]
theorem universallyInjective_of_isPullback (hC : IsAlgebraicSpace B S hS C)
    (hZ : IsAlgebraicSpace B S hS Z) (hT : IsAlgebraicSpace B S hS T) (f : C ⟶ T) (g : Z ⟶ T)
    (hf : UniversallyInjective B S hS f) {a : A ⟶ Z} {b : A ⟶ C}
    (hpb : IsPullback a b g f) : UniversallyInjective B S hS a := by
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hZ hC hT
  have hc := universallyInjective_comp B S hS hP hZ hpb.isoPullback.hom (pullback.fst g f)
    (universallyInjective_of_isIso B S hS hpb.isoPullback.hom)
    (universallyInjective_pullback B S hS f g hf)
  rwa [hpb.isoPullback_hom_fst] at hc

end Square

/-! ### Lifting a field-valued point along a locally surjective morphism -/

section LocallySurjective

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A section of the target of a locally surjective morphism of presheaves over the spectrum of
a field in the site lifts, after restriction along a single morphism from the spectrum of a
field in the site, to a section of the source.

Surjectivity on points gives a field-valued point of the source whose image is the class of the
given section; the restricting morphism is the one exhibited by the resulting common
field-valued extension of the two representatives. -/
theorem exists_fieldSpec_lift_of_isLocallySurjective (f : F ⟶ G)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f)
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (t : Spec (.of K) ⟶ S)
    (x : G.obj (Opposite.op (Over.mk (⟨t⟩ : B.obj hK ⟶ B.obj hS)))) :
    ∃ (L : Type u) (_ : Field L) (hL : B.Contains (Spec (.of L))) (s : Spec (.of L) ⟶ S)
      (c : (Over.mk (⟨s⟩ : B.obj hL ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
        Over.mk (⟨t⟩ : B.obj hK ⟶ B.obj hS))
      (v : F.obj (Opposite.op (Over.mk (⟨s⟩ : B.obj hL ⟶ B.obj hS)))),
      f.app (Opposite.op (Over.mk (⟨s⟩ : B.obj hL ⟶ B.obj hS))) v = G.map c.op x := by
  obtain ⟨z, hz⟩ := surjective_pointsMap_of_isLocallySurjective B S hS f hf
    (({ carrier := K, contained := hK, toBase := t, value := x } :
      FieldValuedPoint B S hS G).class B S hS G)
  obtain ⟨q, rfl⟩ := Quot.exists_rep z
  obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS G _ _).mp hz
  refine ⟨r.carrier, r.field, r.contained, r.toBase, b, F.map a.op q.value, ?_⟩
  change G.map b.op x = r.value at hb
  change G.map a.op (f.app _ q.value) = r.value at ha
  change f.app (Opposite.op (FieldValuedPoint.siteObject B S hS G r))
    (F.map a.op q.value) = _
  rw [hb, ← ha]
  exact NatTrans.naturality_apply f a.op q.value

end LocallySurjective

/-! ### Universal injectivity from the field-valued points -/

section FieldPoints

variable {F G Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A section of a fibre product of presheaves is determined by its two components. -/
private theorem pullback_section_ext (g : Y ⟶ G) (f : F ⟶ G) {T : BigFppfOver B S hS}
    {x y : (pullback g f).obj (Opposite.op T)}
    (h₁ : (pullback.fst g f).app (Opposite.op T) x = (pullback.fst g f).app (Opposite.op T) y)
    (h₂ : (pullback.snd g f).app (Opposite.op T) x =
      (pullback.snd g f).app (Opposite.op T) y) : x = y := by
  refine yonedaEquiv.symm.injective (pullback.hom_ext ?_ ?_)
  · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h₁]
  · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h₂]

/-- **Stacks 03MV from the field-valued points.** A morphism of presheaves on the big fppf
site of `S` is universally injective as soon as any two sections over the spectrum of a field
in the site with the same image agree after restriction along a single morphism from the
spectrum of a field in the site.

This is the implication (1) implies (2) of Stacks 040X, and it needs nothing of the
algebraicity of the source, the target or the test object: a point of the fibre product
`Y' ×_G F` is a pair of a point of `Y'` and a section of `F` over its field of definition, so
two points with the same image in `Y'` become, over a common field-valued extension of the two
representatives, a pair of sections of `F` with the same image in `G`; the hypothesis makes
them agree over a further field spectrum, and there the two pairs coincide componentwise. -/
theorem universallyInjective_of_fieldPoints (f : F ⟶ G)
    (hf : ∀ (p : FieldValuedPoint B S hS F) (y : F.obj (Opposite.op p.siteObject)),
      f.app (Opposite.op p.siteObject) p.value = f.app (Opposite.op p.siteObject) y →
      ∃ (q : FieldValuedPoint B S hS F) (c : q.siteObject ⟶ p.siteObject),
        F.map c.op p.value = q.value ∧ F.map c.op y = q.value) :
    UniversallyInjective B S hS f := by
  intro Y' _ g x y hxy
  obtain ⟨p₀, rfl⟩ := Quot.exists_rep x
  obtain ⟨q₀, rfl⟩ := Quot.exists_rep y
  obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS Y' _ _).mp hxy
  change Y'.map a.op ((pullback.fst g f).app _ p₀.value) = r.value at ha
  change Y'.map b.op ((pullback.fst g f).app _ q₀.value) = r.value at hb
  set xT := (pullback g f).map a.op p₀.value with hxT
  set yT := (pullback g f).map b.op q₀.value with hyT
  have hfstx : (pullback.fst g f).app _ xT = r.value := by
    rw [hxT, NatTrans.naturality_apply (pullback.fst g f) a.op p₀.value]
    exact ha
  have hfsty : (pullback.fst g f).app _ yT = r.value := by
    rw [hyT, NatTrans.naturality_apply (pullback.fst g f) b.op q₀.value]
    exact hb
  have hcond : ∀ z : (pullback g f).obj (Opposite.op
      (FieldValuedPoint.siteObject B S hS Y' r)),
      g.app _ ((pullback.fst g f).app _ z) = f.app _ ((pullback.snd g f).app _ z) := by
    intro z
    have h := congrArg (fun α : pullback g f ⟶ G ↦
      α.app (Opposite.op (FieldValuedPoint.siteObject B S hS Y' r)) z)
      (pullback.condition (f := g) (g := f))
    simpa using h
  have hsnd : f.app _ ((pullback.snd g f).app _ xT) =
      f.app _ ((pullback.snd g f).app _ yT) := by
    rw [← hcond xT, ← hcond yT, hfstx, hfsty]
  obtain ⟨q, c, hq₁, hq₂⟩ := hf
    { carrier := r.carrier
      field := r.field
      contained := r.contained
      toBase := r.toBase
      value := (pullback.snd g f).app _ xT } ((pullback.snd g f).app _ yT) hsnd
  change F.map c.op ((pullback.snd g f).app
    (Opposite.op (FieldValuedPoint.siteObject B S hS Y' r)) xT) = q.value at hq₁
  change F.map c.op ((pullback.snd g f).app
    (Opposite.op (FieldValuedPoint.siteObject B S hS Y' r)) yT) = q.value at hq₂
  have hc : (pullback g f).map c.op xT = (pullback g f).map c.op yT := by
    refine pullback_section_ext B S hS g f ?_ ?_
    · rw [NatTrans.naturality_apply (pullback.fst g f) c.op xT,
        NatTrans.naturality_apply (pullback.fst g f) c.op yT]
      change Y'.map c.op ((pullback.fst g f).app
          (Opposite.op (FieldValuedPoint.siteObject B S hS Y' r)) xT) =
        Y'.map c.op ((pullback.fst g f).app
          (Opposite.op (FieldValuedPoint.siteObject B S hS Y' r)) yT)
      rw [hfstx, hfsty]
    · rw [NatTrans.naturality_apply (pullback.snd g f) c.op xT,
        NatTrans.naturality_apply (pullback.snd g f) c.op yT]
      change F.map c.op ((pullback.snd g f).app
          (Opposite.op (FieldValuedPoint.siteObject B S hS Y' r)) xT) =
        F.map c.op ((pullback.snd g f).app
          (Opposite.op (FieldValuedPoint.siteObject B S hS Y' r)) yT)
      rw [hq₁, hq₂]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
    ⟨{ carrier := q.carrier
       field := q.field
       contained := q.contained
       toBase := q.toBase
       value := (pullback g f).map c.op xT }, ⟨c ≫ a, ?_⟩, ⟨c ≫ b, ?_⟩⟩
  · change (pullback g f).map (c ≫ a).op p₀.value = (pullback g f).map c.op xT
    rw [hxT]
    rw [op_comp, CategoryTheory.Functor.map_comp]
    rfl
  · change (pullback g f).map (c ≫ b).op q₀.value = (pullback g f).map c.op xT
    rw [hc, hyT]
    rw [op_comp, CategoryTheory.Functor.map_comp]
    rfl

end FieldPoints

end AlgebraicGeometry.Space

end
