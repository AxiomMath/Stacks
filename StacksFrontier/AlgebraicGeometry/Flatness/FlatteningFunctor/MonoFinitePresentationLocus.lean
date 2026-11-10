module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ImmersionLocalRepresentatives
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Monomorphism

/-!
# Loci cut out by monomorphisms of finite presentation

Let `S` be a scheme and let `P` be a property of schemes over `S` which is inherited along
morphisms of schemes over `S`. Such a property is the same thing as a subterminal functor
`(Sch/S)ᵒᵖ ⥤ Sets`, and it is *cut out by a monomorphism of finite presentation* if there is a
monomorphism of finite presentation `Z ⟶ S` such that a scheme `T` over `S` has the property
exactly when `T ⟶ S` factors through `Z`; this is what it means for the functor to be
representable by a monomorphism of finite presentation.

This file records the formal properties of this notion used in the proof of Stacks 05UG:
invariance under base change, finite intersections, composition, and the fact that it is local
for the étale topology on `S` as soon as the property satisfies the fpqc sheaf condition. The
last statement is the descent argument of Stacks 05UG: a monomorphism of finite presentation is
separated and quasi-finite (Stacks 0CT8), such morphisms satisfy effective descent along fppf
coverings (Stacks 02W8), and being a monomorphism and being of finite presentation are fpqc local
on the base (Stacks 02YK and 02L0).

## Main definitions

* `Stacks.Flatness.propertyFunctor`: the subterminal functor of a property inherited along
  morphisms.
* `Stacks.Flatness.IsCutOutByMonoFP`: the property is cut out by a monomorphism of finite
  presentation.

## Main results

* `Stacks.Flatness.isCutOutByMonoFP_iff_exists_representableBy`: the notion is
  representability of the subterminal functor by a monomorphism of finite presentation.
* `Stacks.Flatness.IsCutOutByMonoFP.baseChange`, `.inf`, `.finite_inf`, `.comp`: the formal
  properties.
* `Stacks.Flatness.IsCutOutByMonoFP.of_etale_local`: étale locality.

## References

* [Stacks Project, Tag 05UG](https://stacks.math.columbia.edu/tag/05UG)
* [Stacks Project, Tag 0CT8](https://stacks.math.columbia.edu/tag/0CT8)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02YK](https://stacks.math.columbia.edu/tag/02YK)
* [Stacks Project, Tag 02L0](https://stacks.math.columbia.edu/tag/02L0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


universe u

namespace Stacks.Flatness

variable {S : Scheme.{u}}

/-- The subterminal functor `(Sch/S)ᵒᵖ ⥤ Sets` of a property of schemes over `S` inherited along
morphisms: a singleton where the property holds and empty elsewhere. -/
def propertyFunctor (P : Over S → Prop) (hP : ∀ {T T' : Over S}, (T' ⟶ T) → P T → P T') :
    (Over S)ᵒᵖ ⥤ Type where
  obj T := PLift (P T.unop)
  map g := ↾fun h ↦ ⟨hP g.unop h.down⟩
  map_id _ := by ext; exact Subsingleton.elim _ _
  map_comp _ _ := by ext; exact Subsingleton.elim _ _

/-- Each value of the functor `propertyFunctor P hP` has at most one element. -/
instance (P : Over S → Prop) (hP : ∀ {T T' : Over S}, (T' ⟶ T) → P T → P T')
    (T : (Over S)ᵒᵖ) : Subsingleton ((propertyFunctor P hP).obj T) :=
  inferInstanceAs (Subsingleton (PLift _))

/-- A property of schemes over `S` is *cut out by a monomorphism of finite presentation* if a
monomorphism of finite presentation `Z ⟶ S` exists such that a scheme over `S` has the property
exactly when it factors through `Z`. -/
def IsCutOutByMonoFP (P : Over S → Prop) : Prop :=
  ∃ Z : Over S, Mono Z.hom ∧ AlgebraicGeometry.FinitePresentation Z.hom ∧
    ∀ T : Over S, P T ↔ Nonempty (T ⟶ Z)

/-- A subterminal functor is represented by an object with monomorphic structure morphism as
soon as the two are inhabited together. -/
def representableByOfNonemptyIff (G : (Over S)ᵒᵖ ⥤ Type*) [∀ T, Subsingleton (G.obj T)]
    (Z : Over S) [Mono Z.hom] (h : ∀ T : Over S, Nonempty (G.obj (op T)) ↔ Nonempty (T ⟶ Z)) :
    G.RepresentableBy Z := by
  classical
  have := fun T ↦ subsingleton_overHom_of_mono T Z
  refine ⟨fun {T} ↦
    { toFun := fun g ↦ Classical.choice ((h T).2 ⟨g⟩)
      invFun := fun x ↦ Classical.choice ((h T).1 ⟨x⟩)
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }, ?_⟩
  intro _ _ _ _
  exact Subsingleton.elim _ _

/-- For a subterminal functor, being cut out by a monomorphism of finite presentation is
representability by a monomorphism of finite presentation. -/
theorem isCutOutByMonoFP_iff_exists_representableBy (G : (Over S)ᵒᵖ ⥤ Type*)
    [∀ T, Subsingleton (G.obj T)] :
    IsCutOutByMonoFP (fun T ↦ Nonempty (G.obj (op T))) ↔
      ∃ Z : Over S, Mono Z.hom ∧ AlgebraicGeometry.FinitePresentation Z.hom ∧
        Nonempty (G.RepresentableBy Z) := by
  constructor
  · rintro ⟨Z, hm, hfp, h⟩
    exact ⟨Z, hm, hfp, ⟨representableByOfNonemptyIff G Z h⟩⟩
  · rintro ⟨Z, hm, hfp, ⟨e⟩⟩
    exact ⟨Z, hm, hfp, fun T ↦ ⟨fun ⟨x⟩ ↦ ⟨e.homEquiv.symm x⟩, fun ⟨g⟩ ↦ ⟨e.homEquiv g⟩⟩⟩

namespace IsCutOutByMonoFP

/-- Being cut out depends only on the property up to equivalence. -/
theorem of_iff {P Q : Over S → Prop} (h : IsCutOutByMonoFP P) (hPQ : ∀ T, P T ↔ Q T) :
    IsCutOutByMonoFP Q := by
  obtain ⟨Z, hm, hfp, hZ⟩ := h
  exact ⟨Z, hm, hfp, fun T ↦ (hPQ T).symm.trans (hZ T)⟩

/-- The property that always holds is cut out by the identity. -/
theorem of_forall {P : Over S → Prop} (h : ∀ T, P T) : IsCutOutByMonoFP P :=
  ⟨Over.mk (𝟙 S), inferInstanceAs (Mono (𝟙 S)),
    AlgebraicGeometry.FinitePresentation.mk (inferInstanceAs (LocallyOfFinitePresentation (𝟙 S)))
      (inferInstanceAs (QuasiCompact (𝟙 S))) (inferInstanceAs (QuasiSeparated (𝟙 S))),
    fun T ↦ ⟨fun _ ↦ ⟨Over.homMk T.hom (Category.comp_id _)⟩, fun _ ↦ h T⟩⟩

/-- **Base change.** If `P` is cut out by `Z ⟶ S`, then for every `q : U ⟶ S` the property of
schemes over `U` of having `P` over `S` is cut out by `Z ×_S U ⟶ U`. -/
theorem baseChange {P : Over S → Prop} (h : IsCutOutByMonoFP P) {U : Scheme.{u}} (q : U ⟶ S) :
    IsCutOutByMonoFP (fun T : Over U ↦ P ((Over.map q).obj T)) := by
  obtain ⟨Z, hm, hfp, hZ⟩ := h
  refine ⟨(Over.pullback q).obj Z, inferInstanceAs (Mono (pullback.snd Z.hom q)), ?_,
    fun T ↦ ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hfp
    exact AlgebraicGeometry.FinitePresentation.mk
      (inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Z.hom q)))
      (inferInstanceAs (QuasiCompact (pullback.snd Z.hom q)))
      (inferInstanceAs (QuasiSeparated (pullback.snd Z.hom q)))
  · refine (hZ _).trans ?_
    let adj := Over.mapPullbackAdj q
    exact ⟨fun ⟨g⟩ ↦ ⟨adj.homEquiv _ _ g⟩, fun ⟨g⟩ ↦ ⟨(adj.homEquiv _ _).symm g⟩⟩

/-- The structure morphism of a composite `W ⟶ Z ⟶ S` of monomorphisms of finite presentation is
a monomorphism of finite presentation. -/
private theorem mono_fp_comp {Z : Over S} {W : Over Z.left} (hZm : Mono Z.hom)
    (hZfp : AlgebraicGeometry.FinitePresentation Z.hom) (hWm : Mono W.hom)
    (hWfp : AlgebraicGeometry.FinitePresentation W.hom) :
    Mono ((Over.map Z.hom).obj W).hom ∧
      AlgebraicGeometry.FinitePresentation ((Over.map Z.hom).obj W).hom := by
  obtain ⟨a1, a2, a3⟩ := hZfp
  obtain ⟨b1, b2, b3⟩ := hWfp
  exact ⟨inferInstanceAs (Mono (W.hom ≫ Z.hom)),
    AlgebraicGeometry.FinitePresentation.mk
      (inferInstanceAs (LocallyOfFinitePresentation (W.hom ≫ Z.hom)))
      (inferInstanceAs (QuasiCompact (W.hom ≫ Z.hom)))
      (inferInstanceAs (QuasiSeparated (W.hom ≫ Z.hom)))⟩

/-- **Composition.** Let `Q` be cut out by `Z ⟶ S` and let `P` imply `Q` and be inherited along
morphisms. If the property of schemes over `Z` of having `P` over `S` is cut out by a
monomorphism of finite presentation `W ⟶ Z`, then `P` is cut out by `W ⟶ Z ⟶ S`. -/
theorem comp {P Q : Over S → Prop} (hP : ∀ {T T' : Over S}, (T' ⟶ T) → P T → P T')
    (hPQ : ∀ T, P T → Q T) {Z : Over S} (hZm : Mono Z.hom)
    (hZfp : AlgebraicGeometry.FinitePresentation Z.hom)
    (hZ : ∀ T : Over S, Q T ↔ Nonempty (T ⟶ Z))
    (h : IsCutOutByMonoFP (fun T : Over Z.left ↦ P ((Over.map Z.hom).obj T))) :
    IsCutOutByMonoFP P := by
  obtain ⟨W, hWm, hWfp, hW⟩ := h
  obtain ⟨hm, hfp⟩ := mono_fp_comp hZm hZfp hWm hWfp
  refine ⟨(Over.map Z.hom).obj W, hm, hfp, fun T ↦ ⟨fun hT ↦ ?_, fun ⟨g⟩ ↦ ?_⟩⟩
  · obtain ⟨g⟩ := (hZ T).mp (hPQ T hT)
    let T' : Over Z.left := Over.mk g.left
    let e : (Over.map Z.hom).obj T' ⟶ T := Over.homMk (𝟙 _) (by simp [T'])
    let e' : T ⟶ (Over.map Z.hom).obj T' := Over.homMk (𝟙 _) (by simp [T'])
    obtain ⟨k⟩ := (hW T').mp (hP e hT)
    exact ⟨e' ≫ (Over.map Z.hom).map k⟩
  · let T' : Over Z.left := Over.mk (g.left ≫ W.hom)
    have hT' : P ((Over.map Z.hom).obj T') :=
      (hW T').mpr ⟨Over.homMk g.left rfl⟩
    exact hP (Over.homMk (𝟙 _) (by simpa [T'] using Over.w g) : T ⟶ (Over.map Z.hom).obj T') hT'

/-- **Intersection.** If `P` and `Q` are cut out by monomorphisms of finite presentation, then so
is `P ∧ Q`, by the fibre product of the two. -/
theorem inf {P Q : Over S → Prop} (hP : IsCutOutByMonoFP P) (hQ : IsCutOutByMonoFP Q) :
    IsCutOutByMonoFP (fun T ↦ P T ∧ Q T) := by
  obtain ⟨Z₁, hm₁, hfp₁, h₁⟩ := hP
  obtain ⟨Z₂, hm₂, hfp₂, h₂⟩ := hQ
  have hb := baseChange ⟨Z₂, hm₂, hfp₂, h₂⟩ Z₁.hom
  have hfpZ := hfp₁
  refine comp (P := fun T ↦ P T ∧ Q T) (Q := P) ?_ (fun T h ↦ h.1) hm₁ hfp₁ h₁ ?_
  · intro T T' g h
    exact ⟨(h₁ T').mpr ⟨g ≫ Classical.choice ((h₁ T).mp h.1)⟩,
      (h₂ T').mpr ⟨g ≫ Classical.choice ((h₂ T).mp h.2)⟩⟩
  · refine hb.of_iff fun T ↦ ⟨fun h ↦ ⟨?_, h⟩, fun h ↦ h.2⟩
    exact (h₁ _).mpr ⟨Over.homMk T.hom rfl⟩

/-- **Finite intersection.** A finite conjunction of properties each cut out by a monomorphism of
finite presentation is cut out by a monomorphism of finite presentation. -/
theorem finite_inf {m : ℕ} {P : Fin m → Over S → Prop} (h : ∀ i, IsCutOutByMonoFP (P i)) :
    IsCutOutByMonoFP (fun T ↦ ∀ i, P i T) := by
  induction m with
  | zero => exact of_forall fun T i ↦ i.elim0
  | succ m ih =>
    refine ((h 0).inf (ih (P := fun i ↦ P i.succ) fun i ↦ h i.succ)).of_iff fun T ↦ ?_
    exact ⟨fun ⟨h0, hs⟩ i ↦ Fin.cases h0 hs i, fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩⟩

end IsCutOutByMonoFP

/-! ### Étale locality -/

section Local

variable (P : Over S → Prop) (hP : ∀ {T T' : Over S}, (T' ⟶ T) → P T → P T')
  {I : Type u} {U : I → Scheme.{u}} (q : ∀ i, U i ⟶ S) (W : ∀ i, Over (U i))

include hP in
/-- A scheme over a member of the family with the property lifts, over the base, to the local
representative there. -/
private theorem exists_lift_of_localRepresentative {U' : Scheme.{u}} (q' : U' ⟶ S) (W' : Over U')
    (h : ∀ V : Over U', P ((Over.map q').obj V) ↔ Nonempty (V ⟶ W'))
    {T : Over S} (a : T ⟶ Over.mk q') (hT : P T) :
    ∃ b : T ⟶ (Over.map q').obj W', b ≫ AlgebraicGeometry.structureMap q' W' = a := by
  let V := Over.mk a.left
  let e : (Over.map q').obj V ⟶ T := Over.homMk (𝟙 _) (by simpa [V] using (Over.w a).symm)
  obtain ⟨b⟩ := (h V).mp (hP e hT)
  refine ⟨Over.homMk b.left ?_, Over.OverMorphism.ext (Over.w b)⟩
  change b.left ≫ W'.hom ≫ q' = T.hom
  rw [← Category.assoc, Over.w b]
  exact Over.w a

variable {U₁ U₂ : Scheme.{u}} (q₁ : U₁ ⟶ S) (q₂ : U₂ ⟶ S) (W₁ : Over U₁) (W₂ : Over U₂)

/-- The comparison morphism between two local representatives over the fibre product of the two
base changes. -/
private def localTransition (hW₁ : P ((Over.map q₁).obj W₁))
    (h₂ : ∀ T : Over U₂, P ((Over.map q₂).obj T) ↔ Nonempty (T ⟶ W₂)) :
    (Over.map q₁).obj W₁ ⨯ Over.mk q₂ ⟶ Over.mk q₁ ⨯ (Over.map q₂).obj W₂ :=
  prod.lift (prod.fst ≫ AlgebraicGeometry.structureMap q₁ W₁)
    (Classical.choose (exists_lift_of_localRepresentative P hP q₂ W₂ h₂ prod.snd
      (hP prod.fst hW₁)))

private theorem localTransition_fst (hW₁ : P ((Over.map q₁).obj W₁))
    (h₂ : ∀ T : Over U₂, P ((Over.map q₂).obj T) ↔ Nonempty (T ⟶ W₂)) :
    localTransition P hP q₁ q₂ W₁ W₂ hW₁ h₂ ≫ prod.fst =
      prod.fst ≫ AlgebraicGeometry.structureMap q₁ W₁ := by
  simp [localTransition]

private theorem localTransition_snd (hW₁ : P ((Over.map q₁).obj W₁))
    (h₂ : ∀ T : Over U₂, P ((Over.map q₂).obj T) ↔ Nonempty (T ⟶ W₂)) :
    localTransition P hP q₁ q₂ W₁ W₂ hW₁ h₂ ≫ prod.snd ≫
      AlgebraicGeometry.structureMap q₂ W₂ = prod.snd := by
  simpa [localTransition] using
    Classical.choose_spec (exists_lift_of_localRepresentative P hP q₂ W₂ h₂
      (prod.snd : (Over.map q₁).obj W₁ ⨯ Over.mk q₂ ⟶ Over.mk q₂) (hP prod.fst hW₁))

attribute [local simp] localTransition_fst localTransition_snd

/-- The comparison morphism of two local representatives is an isomorphism. -/
private def localTransitionIso [Mono W₁.hom] [Mono W₂.hom]
    (h₁ : ∀ T : Over U₁, P ((Over.map q₁).obj T) ↔ Nonempty (T ⟶ W₁))
    (h₂ : ∀ T : Over U₂, P ((Over.map q₂).obj T) ↔ Nonempty (T ⟶ W₂)) :
    (Over.map q₁).obj W₁ ⨯ Over.mk q₂ ≅ Over.mk q₁ ⨯ (Over.map q₂).obj W₂ where
  hom := localTransition P hP q₁ q₂ W₁ W₂ ((h₁ W₁).mpr ⟨𝟙 W₁⟩) h₂
  inv := (prod.braiding _ _).hom ≫
    localTransition P hP q₂ q₁ W₂ W₁ ((h₂ W₂).mpr ⟨𝟙 W₂⟩) h₁ ≫ (prod.braiding _ _).hom
  hom_inv_id := by
    have := mono_structureMap q₁ W₁
    refine prod.hom_ext ?_ ?_
    · refine (cancel_mono (AlgebraicGeometry.structureMap q₁ W₁)).mp ?_
      simp
    · simp
  inv_hom_id := by
    have := mono_structureMap q₂ W₂
    refine prod.hom_ext ?_ ?_
    · simp
    · refine (cancel_mono (AlgebraicGeometry.structureMap q₂ W₂)).mp ?_
      simp

/-- The local representatives form a descent datum: the gluing isomorphisms are the comparison
morphisms, and the cocycle condition holds because the property is subterminal. -/
private def localDescentData [∀ i, Mono (W i).hom]
    (h : ∀ i, ∀ T : Over (U i), P ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    AlgebraicGeometry.DescentData q where
  obj := W
  gluing i j := Over.isoMk
    (localTransitionIso P hP (q i) (q j) (W i) (W j) (h i) (h j)) (by
      refine prod.hom_ext ?_ ?_ <;> simp [localTransitionIso])
  cocycle i j k := by
    change prod.map (localTransition P hP (q i) (q j) (W i) (W j)
      ((h i (W i)).mpr ⟨𝟙 _⟩) (h j)) (𝟙 _) ≫
      prodMapLastTwo (localTransition P hP (q j) (q k) (W j) (W k)
        ((h j (W j)).mpr ⟨𝟙 _⟩) (h k)) =
      prodMapFirstThird (localTransition P hP (q i) (q k) (W i) (W k)
        ((h i (W i)).mpr ⟨𝟙 _⟩) (h k))
    have := mono_structureMap (q k) (W k)
    refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_
    · simp [prodMapLastTwo, prodMapFirstThird]
    · simp [prodMapLastTwo, prodMapFirstThird]
    · refine (cancel_mono (AlgebraicGeometry.structureMap (q k) (W k))).mp ?_
      simp [prodMapLastTwo, prodMapFirstThird]

/-- **Local representatives glue along an fppf covering.** -/
private theorem isCutOutByMonoFP_of_localRepresentatives
    (hsheaf : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (propertyFunctor P hP))
    (hq : Presieve.ofArrows U q ∈ Scheme.fppfPrecoverage S)
    [∀ i, Mono (W i).hom] (hfp : ∀ i, AlgebraicGeometry.FinitePresentation (W i).hom)
    (h : ∀ i, ∀ T : Over (U i), P ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    IsCutOutByMonoFP P := by
  classical
  have hq' := Scheme.fppfPrecoverage_le_fpqcPrecoverage S hq
  have hlft (i : I) : LocallyOfFiniteType (W i).hom := by
    have := (hfp i).1
    infer_instance
  let d := localDescentData P hP q W h
  obtain ⟨Z, ⟨e⟩⟩ :=
    AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isSeparated_of_locallyQuasiFinite q hq
      d (fun i ↦ (isSeparated_and_locallyQuasiFinite_of_mono (W i).hom).1)
      (fun i ↦ (isSeparated_and_locallyQuasiFinite_of_mono (W i).hom).2) hlft
  let ei (i : I) : (Over.pullback (q i)).obj Z ≅ W i :=
    (eqToIso ((AlgebraicGeometry.canonicalFamilyDescentFunctor q).obj Z i)).symm ≪≫
      (AlgebraicGeometry.DescentData.evaluation i).mapIso e
  have hsnd (i : I) : pullback.snd Z.hom (q i) = (ei i).hom.left ≫ (W i).hom :=
    (Over.w (ei i).hom).symm
  have hiso (i : I) : IsIso (ei i).hom.left := Functor.map_isIso (Over.forget (U i)) (ei i).hom
  have hZm : Mono Z.hom := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := MorphismProperty.monomorphisms Scheme.{u}) hq' ?_
    rintro V' g' _ ⟨i⟩
    change Mono (pullback.snd Z.hom (q i))
    rw [hsnd i]
    infer_instance
  have hZfp : AlgebraicGeometry.FinitePresentation Z.hom := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := (@AlgebraicGeometry.FinitePresentation : MorphismProperty Scheme.{u})) hq' ?_
    rintro V' g' _ ⟨i⟩
    show AlgebraicGeometry.FinitePresentation (pullback.snd Z.hom (q i))
    rw [hsnd i]
    obtain ⟨h1, h2, h3⟩ := hfp i
    exact AlgebraicGeometry.FinitePresentation.mk inferInstance inferInstance inferInstance
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp hsheaf
  have hZ : Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj Z) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  refine ⟨Z, hZm, hZfp, fun T ↦ ?_⟩
  let Q (i : I) := (Over.map (q i)).obj ((Over.pullback (q i)).obj T)
  let a (i : I) : Q i ⟶ T := overBaseChangeProjection (q i) T
  have ha : Sieve.ofArrows Q a ∈ (Scheme.fpqcTopology.over S) T :=
    overBaseChangeProjection_covering q hq' T
  have hPT : P T ↔ Nonempty ((propertyFunctor P hP).obj (op T)) :=
    ⟨fun h ↦ ⟨⟨h⟩⟩, fun ⟨h⟩ ↦ h.down⟩
  rw [hPT, nonempty_iff_forall_of_subsingleton_sheaf (propertyFunctor P hP) hF
      (fun T ↦ inferInstance) Q a ha,
    show Nonempty (T ⟶ Z) ↔ ∀ i, Nonempty (Q i ⟶ Z) from
      nonempty_iff_forall_of_subsingleton_sheaf (yoneda.obj Z) hZ
        (fun T' ↦ subsingleton_overHom_of_mono T' Z) Q a ha]
  refine forall_congr' fun i ↦ ?_
  change Nonempty (PLift (P (Q i))) ↔ Nonempty (Q i ⟶ Z)
  rw [nonempty_plift, nonempty_prop, h i ((Over.pullback (q i)).obj T)]
  let adj := Over.mapPullbackAdj (q i)
  exact ⟨fun ⟨g⟩ ↦ ⟨(adj.homEquiv _ _).symm (g ≫ (ei i).inv)⟩,
    fun ⟨g⟩ ↦ ⟨adj.homEquiv _ _ g ≫ (ei i).hom⟩⟩

end Local

/-- **Étale locality.** Let `P` be a property of schemes over `S` inherited along morphisms whose
subterminal functor satisfies the fpqc sheaf condition. If every point of `S` lies in the image
of an étale morphism `U ⟶ S` over which the property is cut out by a monomorphism of finite
presentation, then `P` is cut out by a monomorphism of finite presentation. -/
theorem IsCutOutByMonoFP.of_etale_local (P : Over S → Prop)
    (hP : ∀ {T T' : Over S}, (T' ⟶ T) → P T → P T')
    (hsheaf : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (propertyFunctor P hP))
    (hloc : ∀ s : S, ∃ (U : Scheme.{u}) (q : U ⟶ S), Etale q ∧ s ∈ Set.range q ∧
      IsCutOutByMonoFP (fun T : Over U ↦ P ((Over.map q).obj T))) :
    IsCutOutByMonoFP P := by
  classical
  choose U q hq hs W hWm hWfp hW using hloc
  have (s : S) : Mono (W s).hom := hWm s
  have hcover : Presieve.ofArrows U q ∈ Scheme.fppfPrecoverage S := by
    refine (Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun s ↦ ⟨s, (hs s).choose, (hs s).choose_spec⟩, fun s ↦ ⟨inferInstance, inferInstance⟩⟩
  exact isCutOutByMonoFP_of_localRepresentatives P hP q W hsheaf hcover hWfp hW

end Stacks.Flatness

end
