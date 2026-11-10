module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Localization.Construction
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.OverIntermediate
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.CompactificationFractions
public import StacksFrontier.CategoryTheory.Localization.RightFraction.CommonDenominator
public import StacksCore.Tactic.StacksAttribute

/-!
# Compactifiable schemes as a localization of compactifications

Over a quasi-compact and quasi-separated scheme, forgetting the ambient proper scheme
identifies the compactifiable schemes with the compactifications localized at those
morphisms which are isomorphisms on the open subschemes.

## Main definitions

* `AlgebraicGeometry.IsCompactifyable` records the existence of a compactification of a
  scheme over the base.
* `AlgebraicGeometry.Compactifyable` is the full subcategory of such schemes.
* `AlgebraicGeometry.compactificationInterior` forgets the ambient proper scheme.
* `AlgebraicGeometry.compactificationInteriorFacIso` identifies the localization lift of
  that functor, precomposed with the localization functor, with the functor itself.

## Main results

* `AlgebraicGeometry.localizedInteriorEquivalence` is the equivalence induced by forgetting
  the ambient scheme.
* `AlgebraicGeometry.localizedInteriorEquivalenceCompQ` identifies its composite with the
  localization functor with the original forgetful functor.

## Implementation notes

Compactifiability is invariant under isomorphism over the base, so it is expressed by an
isomorphism to the interior of a compactification. The localization is Mathlib's canonical
localization of the right multiplicative system
`AlgebraicGeometry.interiorIsomorphisms`, whose right calculus of fractions is
`AlgebraicGeometry.interiorIsomorphisms_hasRightCalculusOfFractions`; the natural isomorphism
specifies the functor underlying the equivalence.

Fullness uses that any morphism between the interiors of two compactifications is realized by
a common refinement, obtained from `AlgebraicGeometry.exists_quasiCompact_compactification_over`
applied to the fibre product of the two ambient schemes over the base. Faithfulness uses the
common-denominator presentation of a pair of morphisms in the localization together with the
equalizer refinement of two parallel morphisms of compactifications.

## References

* [Stacks Project, Tag 0ATW](https://stacks.math.columbia.edu/tag/0ATW)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme over `S` is compactifiable if it is isomorphic over `S` to the interior of a
compactification. -/
def IsCompactifyable (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X => ∃ C : Compactification S, Nonempty (X ≅ C.obj.left)

/-- The category of compactifiable schemes over `S`. -/
abbrev Compactifyable (S : Scheme.{u}) :=
  (IsCompactifyable S).FullSubcategory

/-- Forget the ambient proper scheme of a compactification. -/
def compactificationInterior (S : Scheme.{u}) :
    Compactification S ⥤ Compactifyable S :=
  (IsCompactifyable S).lift
    ((IsCompactification S).ι ⋙ Arrow.leftFunc)
    (fun C => ⟨C, ⟨Iso.refl _⟩⟩)

/-- Forgetting the ambient scheme sends interior isomorphisms to isomorphisms. -/
lemma compactificationInterior_inverts (S : Scheme.{u}) :
    (interiorIsomorphisms S).IsInvertedBy (compactificationInterior S) := by
  intro X Y f hf
  apply (IsCompactifyable S).isIso_hom_iff ((compactificationInterior S).map f) |>.1
  change IsIso (Arrow.Hom.left f.hom)
  have : IsIso ((Over.forget S).map (Arrow.Hom.left f.hom)) := hf
  exact isIso_of_reflects_iso (Arrow.Hom.left f.hom) (Over.forget S)

/-- The localization lift restricts to the forgetful functor on compactifications. -/
noncomputable def compactificationInteriorFacIso (S : Scheme.{u}) :
    (interiorIsomorphisms S).Q ⋙
      Localization.Construction.lift (compactificationInterior S)
        (compactificationInterior_inverts S) ≅ compactificationInterior S :=
  eqToIso (Localization.Construction.fac (compactificationInterior S)
    (compactificationInterior_inverts S))

/-- The identification `compactificationInteriorFacIso` is natural in a right fraction. -/
private lemma compactificationInterior_lift_fraction_naturality
    (S : Scheme.{u}) {X Y : Compactification S}
    (φ : (interiorIsomorphisms S).RightFraction X Y) :
    (Localization.Construction.lift (compactificationInterior S)
      (compactificationInterior_inverts S)).map (φ.map (interiorIsomorphisms S).Q
        (Localization.inverts _ (interiorIsomorphisms S))) ≫
        (compactificationInteriorFacIso S).hom.app Y =
      (compactificationInteriorFacIso S).hom.app X ≫ φ.map (compactificationInterior S)
        (compactificationInterior_inverts S) := by
  let W := interiorIsomorphisms S
  let F := compactificationInterior S
  let L := Localization.Construction.lift F (compactificationInterior_inverts S)
  let η := compactificationInteriorFacIso S
  have hnat {P Q : Compactification S} (g : P ⟶ Q) :
      L.map (W.Q.map g) ≫ η.hom.app Q = η.hom.app P ≫ F.map g := by
    simpa only [Functor.comp_map] using η.hom.naturality g
  have : IsIso (F.map φ.s) := compactificationInterior_inverts S φ.s φ.hs
  have : IsIso (W.Q.map φ.s) := Localization.inverts W.Q W φ.s φ.hs
  have hstep : inv (L.map (W.Q.map φ.s)) ≫ η.hom.app φ.X' =
      η.hom.app X ≫ inv (F.map φ.s) := by
    rw [IsIso.inv_comp_eq, reassoc_of% hnat φ.s]
    simp
  dsimp [MorphismProperty.RightFraction.map]
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc]
  rw [hnat φ.f, reassoc_of% hstep]

/-- The lift of the interior functor is essentially surjective. -/
lemma compactificationInterior_lift_essSurj (S : Scheme.{u}) :
    (Localization.Construction.lift (compactificationInterior S)
      (compactificationInterior_inverts S)).EssSurj := by
  constructor
  intro Y
  rcases Y.property with ⟨X, ⟨e⟩⟩
  exact ⟨(interiorIsomorphisms S).Q.obj X, ⟨(IsCompactifyable S).isoMk e.symm⟩⟩

/-- The compactification refining a compactification by the equalizer of two parallel
morphisms of ambient schemes out of it. -/
private noncomputable def equalizerRefinement (S : Scheme.{u})
    {X Y : Compactification S} (f g : X ⟶ Y)
    (_h : (Arrow.Hom.left f.hom).left = (Arrow.Hom.left g.hom).left) :
    Compactification S := by
  let fB := Arrow.Hom.right f.hom
  let gB := Arrow.Hom.right g.hom
  let e : equalizer fB gB ⟶ X.obj.right := equalizer.ι fB gB
  have : IsProper X.obj.right.hom := X.property.1
  have : IsProper Y.obj.right.hom := Y.property.1
  have : IsClosedImmersion e.left := isClosedImmersion_equalizer_ι_left fB gB
  let b : (equalizer fB gB).left ⟶ S := (equalizer fB gB).hom
  have : IsProper b := by
    have hb : e.left ≫ X.obj.right.hom = b := Over.w e
    rw [← hb]
    infer_instance
  let j := X.obj.hom.left
  let q := pullback.snd j e.left
  have : IsOpenImmersion j := X.property.2.1
  have : QuasiCompact j := X.property.2.2
  have : IsOpenImmersion q := inferInstance
  have : QuasiCompact q := inferInstance
  let a : pullback j e.left ⟶ S := q ≫ b
  let A : Over S := Over.mk a
  let B : Over S := Over.mk b
  let i : A ⟶ B := Over.homMk q rfl
  exact ⟨Arrow.mk i, by
    change IsProper b ∧ IsOpenImmersion q ∧ QuasiCompact q
    exact ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The morphism from the equalizer refinement back to the original compactification. -/
private noncomputable def equalizerRefinementToX (S : Scheme.{u})
    {X Y : Compactification S} (f g : X ⟶ Y)
    (h : (Arrow.Hom.left f.hom).left = (Arrow.Hom.left g.hom).left) :
    equalizerRefinement S f g h ⟶ X := by
  let fB := Arrow.Hom.right f.hom
  let gB := Arrow.Hom.right g.hom
  let e : equalizer fB gB ⟶ X.obj.right := equalizer.ι fB gB
  let j := X.obj.hom.left
  let p := pullback.fst j e.left
  let q := pullback.snd j e.left
  let b := (equalizer fB gB).hom
  have hbase : p ≫ X.obj.left.hom = q ≫ b := by
    dsimp [b]
    rw [← Over.w X.obj.hom, ← Over.w e, ← Category.assoc, pullback.condition]
    simp only [Category.assoc]
    rfl
  dsimp only [equalizerRefinement]
  exact ObjectProperty.homMk (Arrow.homMk (Over.homMk p hbase) e
    (Over.OverMorphism.ext pullback.condition))

/-- The morphism from the equalizer refinement is an interior isomorphism. -/
private lemma equalizerRefinementToX_mem (S : Scheme.{u})
    {X Y : Compactification S} (f g : X ⟶ Y)
    (h : (Arrow.Hom.left f.hom).left = (Arrow.Hom.left g.hom).left) :
    interiorIsomorphisms S (equalizerRefinementToX S f g h) := by
  let fB := Arrow.Hom.right f.hom
  let gB := Arrow.Hom.right g.hom
  let e : equalizer fB gB ⟶ X.obj.right := equalizer.ι fB gB
  have heq : X.obj.hom ≫ fB = X.obj.hom ≫ gB := by
    calc
      X.obj.hom ≫ fB = Arrow.Hom.left f.hom ≫ Y.obj.hom := (Arrow.w f.hom).symm
      _ = Arrow.Hom.left g.hom ≫ Y.obj.hom := by
        congr 1
        exact Over.OverMorphism.ext h
      _ = X.obj.hom ≫ gB := Arrow.w g.hom
  let l : X.obj.left ⟶ equalizer fB gB := equalizer.lift X.obj.hom heq
  have hl : l.left ≫ e.left = X.obj.hom.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (equalizer.lift_ι X.obj.hom heq)
  have : Mono e.left := by
    have : IsProper X.obj.right.hom := X.property.1
    have : IsProper Y.obj.right.hom := Y.property.1
    have : IsClosedImmersion e.left := isClosedImmersion_equalizer_ι_left fB gB
    infer_instance
  dsimp only [interiorIsomorphisms, equalizerRefinementToX]
  change IsIso (pullback.fst X.obj.hom.left e.left)
  rw [← hl]
  infer_instance

/-- The equalizer refinement equalizes the two parallel morphisms. -/
private lemma equalizerRefinementToX_condition (S : Scheme.{u})
    {X Y : Compactification S} (f g : X ⟶ Y)
    (h : (Arrow.Hom.left f.hom).left = (Arrow.Hom.left g.hom).left) :
    equalizerRefinementToX S f g h ≫ f = equalizerRefinementToX S f g h ≫ g := by
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · apply Over.OverMorphism.ext
    dsimp only [equalizerRefinementToX]
    change pullback.fst X.obj.hom.left
      (equalizer.ι (Arrow.Hom.right f.hom) (Arrow.Hom.right g.hom)).left ≫
      (Arrow.Hom.left f.hom).left =
      pullback.fst X.obj.hom.left
      (equalizer.ι (Arrow.Hom.right f.hom) (Arrow.Hom.right g.hom)).left ≫
      (Arrow.Hom.left g.hom).left
    rw [h]
  · exact Over.OverMorphism.ext (congrArg Over.Hom.left (equalizer.condition _ _))

/-- Two right fractions with a common denominator whose numerators agree on interiors have
the same image in the localization. -/
private lemma rightFraction_map_Q_eq_of_map_eq (S : Scheme.{u}) {A B Z : Compactification S}
    (s : Z ⟶ A) (hs : interiorIsomorphisms S s) (f₁ f₂ : Z ⟶ B)
    (h : (compactificationInterior S).map f₁ = (compactificationInterior S).map f₂) :
    (MorphismProperty.RightFraction.mk s hs f₁).map (interiorIsomorphisms S).Q
        (Localization.inverts _ _) =
      (MorphismProperty.RightFraction.mk s hs f₂).map (interiorIsomorphisms S).Q
        (Localization.inverts _ _) := by
  have hleft : (Arrow.Hom.left f₁.hom).left = (Arrow.Hom.left f₂.hom).left :=
    congrArg Over.Hom.left (congrArg (IsCompactifyable S).ι.map h)
  exact (MorphismProperty.RightFraction.map_eq_iff (interiorIsomorphisms S).Q
    (interiorIsomorphisms S) _ _).2
    ⟨equalizerRefinement S f₁ f₂ hleft, equalizerRefinementToX S f₁ f₂ hleft,
      equalizerRefinementToX S f₁ f₂ hleft, rfl, equalizerRefinementToX_condition S f₁ f₂ hleft,
      (interiorIsomorphisms S).comp_mem _ _ (equalizerRefinementToX_mem S f₁ f₂ hleft) hs⟩

/-- The lift of the interior functor is faithful. -/
lemma localizedInteriorLift_faithful (S : Scheme.{u}) :
    (Localization.Construction.lift (compactificationInterior S)
      (compactificationInterior_inverts S)).Faithful := by
  let W := interiorIsomorphisms S
  let F := compactificationInterior S
  let L := Localization.Construction.lift F (compactificationInterior_inverts S)
  refine ⟨?_⟩
  intro A B a b hab
  rcases A with ⟨⟨A⟩⟩
  rcases B with ⟨⟨B⟩⟩
  change W.Q.obj A ⟶ W.Q.obj B at a b
  let gs : Fin 2 → (W.Q.obj A ⟶ W.Q.obj B) := fun i => if i = 0 then a else b
  obtain ⟨Z, s, hs, n, hn⟩ := Localization.exists_common_rightFraction W gs
  let φ : W.RightFraction A B := MorphismProperty.RightFraction.mk s hs (n 0)
  let ψ : W.RightFraction A B := MorphismProperty.RightFraction.mk s hs (n 1)
  have ha : a = φ.map W.Q (Localization.inverts _ W) := by
    simpa [gs, φ] using hn 0
  have hb : b = ψ.map W.Q (Localization.inverts _ W) := by
    simpa [gs, ψ] using hn 1
  have hfrac : φ.map F (compactificationInterior_inverts S) =
      ψ.map F (compactificationInterior_inverts S) :=
    (cancel_epi ((compactificationInteriorFacIso S).hom.app A)).1 (by
      rw [← compactificationInterior_lift_fraction_naturality S φ,
        ← compactificationInterior_lift_fraction_naturality S ψ, ← ha, ← hb]
      exact congrArg (· ≫ (compactificationInteriorFacIso S).hom.app B) hab)
  have hnum : F.map (n 0) = F.map (n 1) := by
    dsimp [φ, ψ, MorphismProperty.RightFraction.map] at hfrac ⊢
    have : IsIso (F.map s) := compactificationInterior_inverts S s hs
    exact (cancel_epi (inv (F.map s))).1 hfrac
  rw [ha, hb]
  exact rightFraction_map_Q_eq_of_map_eq S s hs (n 0) (n 1) hnum

/-- A factorization of the interior of `A` through a proper scheme mapping to the ambient
schemes of `A` and `B` yields a common refinement realizing `f`. -/
private lemma exists_refinement_of_factorization (S : Scheme.{u})
    (A B : Compactification S) (f : A.obj.left ⟶ B.obj.left) {Z : Scheme.{u}}
    (i : A.obj.left.left ⟶ Z) (p : Z ⟶ S) (hp : IsProper p) (hio : IsOpenImmersion i)
    (hqc : QuasiCompact i) (hi : i ≫ p = A.obj.left.hom)
    (a : Z ⟶ A.obj.right.left) (b : Z ⟶ B.obj.right.left)
    (ha : a ≫ A.obj.right.hom = p) (hb : b ≫ B.obj.right.hom = p)
    (hia : i ≫ a = A.obj.hom.left) (hib : i ≫ b = f.left ≫ B.obj.hom.left) :
    ∃ (C : Compactification S) (u : C ⟶ A) (v : C ⟶ B),
      interiorIsomorphisms S u ∧
      (Arrow.Hom.left v.hom).left = (Arrow.Hom.left u.hom).left ≫ f.left := by
  let cOver : Over S := Over.mk p
  let cImmersion : A.obj.left ⟶ cOver := Over.homMk i hi
  let C : Compactification S := ⟨Arrow.mk cImmersion, by
    change IsProper p ∧ IsOpenImmersion i ∧ QuasiCompact i
    exact ⟨hp, hio, hqc⟩⟩
  let leftU : C.obj.left ⟶ A.obj.left := Over.homMk (𝟙 A.obj.left.left) rfl
  let rightU : cOver ⟶ A.obj.right := Over.homMk a ha
  have squareU : cImmersion ≫ rightU = leftU ≫ A.obj.hom := by
    apply Over.OverMorphism.ext
    change i ≫ a = 𝟙 _ ≫ A.obj.hom.left
    rw [hia, Category.id_comp]
  let leftV : C.obj.left ⟶ B.obj.left := Over.homMk f.left (Over.w f)
  let rightV : cOver ⟶ B.obj.right := Over.homMk b hb
  have squareV : cImmersion ≫ rightV = leftV ≫ B.obj.hom := Over.OverMorphism.ext hib
  refine ⟨C, ObjectProperty.homMk (Arrow.homMk leftU rightU squareU.symm),
    ObjectProperty.homMk (Arrow.homMk leftV rightV squareV.symm), ?_, rfl⟩
  change IsIso (𝟙 A.obj.left.left)
  infer_instance

/-- Every morphism between the interiors of two compactifications is realized by a common
refinement of the two compactifications. -/
private lemma compactification_lift_of_interior_hom (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S]
    (A B : Compactification S) (f : A.obj.left ⟶ B.obj.left) :
    ∃ (C : Compactification S) (u : C ⟶ A) (v : C ⟶ B),
      interiorIsomorphisms S u ∧
      (Arrow.Hom.left v.hom).left = (Arrow.Hom.left u.hom).left ≫ f.left := by
  let jA := A.obj.hom.left
  let jB := B.obj.hom.left
  let P := pullback B.obj.right.hom A.obj.right.hom
  let pB := pullback.fst B.obj.right.hom A.obj.right.hom
  let pA := pullback.snd B.obj.right.hom A.obj.right.hom
  have hcomm : (f.left ≫ jB) ≫ B.obj.right.hom = jA ≫ A.obj.right.hom := by
    rw [Category.assoc, Over.w B.obj.hom, Over.w f]
    exact (Over.w A.obj.hom).symm
  let k : A.obj.left.left ⟶ P := pullback.lift (f.left ≫ jB) jA hcomm
  let g : P ⟶ S := pB ≫ B.obj.right.hom
  have : IsProper A.obj.right.hom := A.property.1
  have : IsProper B.obj.right.hom := B.property.1
  have : IsProper g := by
    dsimp [g, pB, P]
    infer_instance
  have hk : k ≫ g = A.obj.left.hom :=
    (pullback.lift_fst_assoc _ _ hcomm _).trans (hcomm.trans (Over.w A.obj.hom))
  let T : Over S := Over.mk (k ≫ g)
  let jTA : T ⟶ A.obj.right := Over.homMk jA ((Over.w A.obj.hom).trans hk.symm)
  let auxA : CompactificationOf T :=
    ⟨StructuredArrow.mk jTA, by
      change IsOpenImmersion jA ∧ IsProper A.obj.right.hom
      exact ⟨A.property.2.1, A.property.1⟩⟩
  obtain ⟨J, hJ⟩ := exists_quasiCompact_compactification_over
    (f := k) (g := g) ⟨auxA, A.property.2.2⟩
  have hJbase : J.immersion ≫ J.toBase = k := Over.w J.obj.hom
  have : IsProper J.toBase := J.property.2
  have hJk {W : Scheme.{u}} (z : P ⟶ W) : J.immersion ≫ J.toBase ≫ z = k ≫ z := by
    rw [← Category.assoc, hJbase]
  have hi : J.immersion ≫ J.toBase ≫ g = A.obj.left.hom := (hJk g).trans hk
  have ha : (J.toBase ≫ pA) ≫ A.obj.right.hom = J.toBase ≫ g := by
    simp only [Category.assoc]
    exact congrArg (fun z => J.toBase ≫ z) pullback.condition.symm
  have hia : J.immersion ≫ J.toBase ≫ pA = jA := (hJk pA).trans (pullback.lift_snd _ _ _)
  have hib : J.immersion ≫ J.toBase ≫ pB = f.left ≫ jB := (hJk pB).trans (pullback.lift_fst _ _ _)
  exact exists_refinement_of_factorization S A B f J.immersion (J.toBase ≫ g) inferInstance
    J.property.1 hJ hi (J.toBase ≫ pA) (J.toBase ≫ pB) ha (Category.assoc _ _ _) hia hib

/-- The lift of the interior functor is full, by the common-refinement construction. -/
lemma localizedInteriorLift_full (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    (Localization.Construction.lift (compactificationInterior S)
      (compactificationInterior_inverts S)).Full := by
  let W := interiorIsomorphisms S
  let F := compactificationInterior S
  let L := Localization.Construction.lift F (compactificationInterior_inverts S)
  let η := compactificationInteriorFacIso S
  refine ⟨?_⟩
  intro X Y f
  rcases X with ⟨⟨A⟩⟩
  rcases Y with ⟨⟨B⟩⟩
  change L.obj (W.Q.obj A) ⟶ L.obj (W.Q.obj B) at f
  let fbar : F.obj A ⟶ F.obj B := η.inv.app A ≫ f ≫ η.hom.app B
  let f₀ : A.obj.left ⟶ B.obj.left := fbar.hom
  obtain ⟨C, u, v, hu, hv⟩ := compactification_lift_of_interior_hom S A B f₀
  have hfactor : F.map v = F.map u ≫ fbar :=
    (IsCompactifyable S).hom_ext (Over.OverMorphism.ext hv)
  let φ : W.RightFraction A B := .mk u hu v
  have hq : L.map (φ.map W.Q (Localization.inverts _ W)) ≫ η.hom.app B =
      η.hom.app A ≫ fbar := by
    have h := compactificationInterior_lift_fraction_naturality S φ
    dsimp [φ, MorphismProperty.RightFraction.map] at h ⊢
    simpa [L, F, η, hfactor, Category.assoc] using h
  have hbar : η.hom.app A ≫ fbar = f ≫ η.hom.app B := by simp [fbar]
  exact ⟨φ.map W.Q (Localization.inverts _ W), (cancel_mono (η.hom.app B)).1 (hq.trans hbar)⟩

/-- **Stacks Project, Tag 0ATW.** The equivalence induced by forgetting the ambient proper
scheme after localizing compactifications at interior isomorphisms. -/
@[stacks 0ATW "the equivalence"]
noncomputable def localizedInteriorEquivalence (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    (interiorIsomorphisms S).Localization ≌ Compactifyable S := by
  let L := Localization.Construction.lift (compactificationInterior S)
    (compactificationInterior_inverts S)
  have : L.Full := localizedInteriorLift_full S
  have : L.Faithful := localizedInteriorLift_faithful S
  have : L.EssSurj := compactificationInterior_lift_essSurj S
  have : L.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact L.asEquivalence

/-- **Stacks Project, Tag 0ATW.** The equivalence extends the forgetful functor from
compactifications, up to a canonical natural isomorphism. -/
@[stacks 0ATW "the forgetful functor"]
noncomputable def localizedInteriorEquivalenceCompQ (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    (interiorIsomorphisms S).Q ⋙
        (localizedInteriorEquivalence S).functor ≅ compactificationInterior S :=
  compactificationInteriorFacIso S

end AlgebraicGeometry
