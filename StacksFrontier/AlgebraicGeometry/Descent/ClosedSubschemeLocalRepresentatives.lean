module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Gluing closed subschemes characterized locally along an fpqc covering

Let `{q i : U i ⟶ P}` be an fpqc covering and let `Φ` be a property of schemes over `P` that
is stable under pullback: if `A ⟶ B` is a morphism over `P` and `B` has `Φ`, so does `A`.
Suppose that over each `U i` there is a closed subscheme `W i ⊂ U i` such that a scheme `T`
over `U i` has `Φ` (as a scheme over `P`) exactly when `T ⟶ U i` factors through `W i`. Then
there is a closed subscheme `Z ⊂ P` whose pullback to each `U i` is `W i`.

The closed subschemes `W i` form a descent datum relative to the covering: the gluing maps are
forced, because each `W i ⟶ U i` is a monomorphism and both ways around a triangle are maps into
one of the `W k`. The descent datum is effective because closed immersions descend along fpqc
coverings ([Stacks, Tag 03I0]), and the descended morphism is a closed immersion because that
property is fpqc local on the target ([Stacks, Tag 02L6]).

## Main results

* `AlgebraicGeometry.ClosedSubschemeDescent.exists_isClosedImmersion_of_localRepresentatives`:
  the glued closed subscheme.

## References

* [Stacks Project, Tag 03I0](https://stacks.math.columbia.edu/tag/03I0)
* [Stacks Project, Tag 02L6](https://stacks.math.columbia.edu/tag/02L6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ClosedSubschemeDescent

variable {P : Scheme.{u}}

/-- A property of schemes over `P` is *stable under pullback* if a scheme mapping to one with the
property has it too. -/
def IsStableUnderPullback (Φ : Over P → Prop) : Prop :=
  ∀ ⦃A B : Over P⦄, (A ⟶ B) → Φ B → Φ A

variable {Φ : Over P → Prop}

/-- A scheme over the base with the property, mapping to a member `V` of the family, lifts over
the base to the local representative over `V`. -/
theorem exists_lift (hΦ : IsStableUnderPullback Φ) {V : Scheme.{u}} (r : V ⟶ P) (Z : Over V)
    (hZ : ∀ T : Over V, Φ ((Over.map r).obj T) ↔ Nonempty (T ⟶ Z))
    {T : Over P} (a : T ⟶ Over.mk r) (hT : Φ T) :
    ∃ b : T ⟶ (Over.map r).obj Z, b ≫ structureMap r Z = a := by
  let V' : Over V := Over.mk a.left
  let e : (Over.map r).obj V' ≅ T :=
    Over.isoMk (Iso.refl _) (by simpa [V'] using (Over.w a).symm)
  obtain ⟨b⟩ := (hZ V').mp (hΦ e.hom hT)
  refine ⟨Over.homMk b.left ?_, Over.OverMorphism.ext (Over.w b)⟩
  show b.left ≫ Z.hom ≫ r = T.hom
  rw [← Category.assoc, Over.w b]
  exact Over.w a

variable {U V : Scheme.{u}} (q : U ⟶ P) (r : V ⟶ P) (W : Over U) (Z : Over V)

/-- The comparison morphism between two local representatives over the pairwise fibre product:
the first factor has the property, so it lifts to the second representative. -/
def transition (hΦ : IsStableUnderPullback Φ) (hW : Φ ((Over.map q).obj W))
    (hZ : ∀ T : Over V, Φ ((Over.map r).obj T) ↔ Nonempty (T ⟶ Z)) :
    (Over.map q).obj W ⨯ Over.mk r ⟶ Over.mk q ⨯ (Over.map r).obj Z :=
  prod.lift (prod.fst ≫ structureMap q W)
    (Classical.choose (exists_lift hΦ r Z hZ prod.snd (hΦ prod.fst hW)))

/-- The first component of `transition` is the first projection followed by the structure map
of the representative `W`. -/
theorem transition_fst (hΦ : IsStableUnderPullback Φ) (hW : Φ ((Over.map q).obj W))
    (hZ : ∀ T : Over V, Φ ((Over.map r).obj T) ↔ Nonempty (T ⟶ Z)) :
    transition q r W Z hΦ hW hZ ≫ prod.fst = prod.fst ≫ structureMap q W := by
  simp [transition]

/-- The second component of `transition`, followed by the structure map of `Z`, is the second
projection. -/
theorem transition_snd (hΦ : IsStableUnderPullback Φ) (hW : Φ ((Over.map q).obj W))
    (hZ : ∀ T : Over V, Φ ((Over.map r).obj T) ↔ Nonempty (T ⟶ Z)) :
    transition q r W Z hΦ hW hZ ≫ prod.snd ≫ structureMap r Z = prod.snd := by
  simpa [transition] using
    Classical.choose_spec (exists_lift hΦ r Z hZ
      (prod.snd : (Over.map q).obj W ⨯ Over.mk r ⟶ Over.mk r) (hΦ prod.fst hW))

attribute [local simp] transition_fst transition_snd

/-- The structure map of a local representative is a monomorphism when the representative's own
structure morphism is. -/
theorem mono_structureMap {S U' : Scheme.{u}} (q' : U' ⟶ S) (W' : Over U') [Mono W'.hom] :
    Mono (structureMap q' W') :=
  (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono W'.hom))

attribute [local instance] mono_structureMap

/-- The comparison morphism of two local representatives is an isomorphism: both composites are
morphisms into an object with a monomorphic structure map, so they are forced. -/
def transitionIso (hΦ : IsStableUnderPullback Φ) [Mono W.hom] [Mono Z.hom]
    (hW : ∀ T : Over U, Φ ((Over.map q).obj T) ↔ Nonempty (T ⟶ W))
    (hZ : ∀ T : Over V, Φ ((Over.map r).obj T) ↔ Nonempty (T ⟶ Z)) :
    (Over.map q).obj W ⨯ Over.mk r ≅ Over.mk q ⨯ (Over.map r).obj Z where
  hom := transition q r W Z hΦ ((hW W).mpr ⟨𝟙 W⟩) hZ
  inv := (prod.braiding _ _).hom ≫
    transition r q Z W hΦ ((hZ Z).mpr ⟨𝟙 Z⟩) hW ≫ (prod.braiding _ _).hom
  hom_inv_id := by
    refine prod.hom_ext ?_ ?_
    · refine (cancel_mono (structureMap q W)).mp ?_
      simp
    · simp
  inv_hom_id := by
    refine prod.hom_ext ?_ ?_
    · simp
    · refine (cancel_mono (structureMap r Z)).mp ?_
      simp

variable {I : Type v} {U : I → Scheme.{u}} (q : ∀ i, U i ⟶ P) (W : ∀ i, Over (U i))

/-- **The local representatives form a descent datum.** The gluing isomorphisms are the
comparison morphisms, and the cocycle condition holds because any two morphisms into a local
representative over the same base agree. -/
def descentData (hΦ : IsStableUnderPullback Φ) [∀ i, Mono (W i).hom]
    (h : ∀ i, ∀ T : Over (U i), Φ ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    DescentData q where
  obj := W
  gluing i j := Over.isoMk (transitionIso (q i) (q j) (W i) (W j) hΦ (h i) (h j)) (by
    refine prod.hom_ext ?_ ?_ <;> simp [transitionIso])
  cocycle i j k := by
    change prod.map (transition (q i) (q j) (W i) (W j) hΦ ((h i (W i)).mpr ⟨𝟙 _⟩) (h j))
        (𝟙 _) ≫
      prodMapLastTwo (transition (q j) (q k) (W j) (W k) hΦ ((h j (W j)).mpr ⟨𝟙 _⟩) (h k)) =
        prodMapFirstThird (transition (q i) (q k) (W i) (W k) hΦ ((h i (W i)).mpr ⟨𝟙 _⟩) (h k))
    refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_
    · simp [prodMapLastTwo, prodMapFirstThird]
    · simp [prodMapLastTwo, prodMapFirstThird]
    · refine (cancel_mono (structureMap (q k) (W k))).mp ?_
      simp [prodMapLastTwo, prodMapFirstThird]

/-- **Closed subschemes characterized locally glue along an fpqc covering.** Let `{q i}` be an
fpqc covering of `P`, let `Φ` be a property of schemes over `P` stable under pullback, and let
`W i ⊂ U i` be closed subschemes such that a scheme over `U i` has `Φ` exactly when it factors
through `W i`. Then there is a closed subscheme of `P` whose pullback to each `U i` is
isomorphic to `W i` over `U i`. -/
@[sga "3 IV 6.4.1" "partial"]
theorem exists_isClosedImmersion_of_localRepresentatives
    (hq : Presieve.ofArrows U q ∈ Scheme.fpqcPrecoverage P) (hΦ : IsStableUnderPullback Φ)
    [∀ i, IsClosedImmersion (W i).hom]
    (h : ∀ i, ∀ T : Over (U i), Φ ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    ∃ Z : Over P, IsClosedImmersion Z.hom ∧
      ∀ i, Nonempty ((Over.pullback (q i)).obj Z ≅ W i) := by
  let d := descentData q W hΦ h
  obtain ⟨Z, ⟨e⟩⟩ := DescentData.isFamilyEffective_of_isClosedImmersion q hq d
    fun i ↦ inferInstanceAs (IsClosedImmersion (W i).hom)
  let ei (i : I) : (Over.pullback (q i)).obj Z ≅ W i :=
    (eqToIso ((canonicalFamilyDescentFunctor q).obj Z i)).symm ≪≫
      (DescentData.evaluation i).mapIso e
  refine ⟨Z, ?_, fun i ↦ ⟨ei i⟩⟩
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := @IsClosedImmersion) hq ?_
  rintro V' g' _ ⟨i⟩
  have : IsIso (ei i).hom.left := Functor.map_isIso (Over.forget (U i)) (ei i).hom
  have hw : (ei i).hom.left ≫ (W i).hom = pullback.snd Z.hom (q i) := Over.w (ei i).hom
  rw [← hw]
  infer_instance

end AlgebraicGeometry.ClosedSubschemeDescent

namespace AlgebraicGeometry.Scheme.IdealSheafData

open ClosedSubschemeDescent

/-- Precomposing can only enlarge the kernel ideal sheaf: `ker g ≤ ker (f ≫ g)`. -/
theorem ker_le_ker_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : g.ker ≤ (f ≫ g).ker := by
  rw [← map_ker, ← map_bot]
  exact map_mono g bot_le

/-- A morphism factors through the closed subscheme cut out by `J` exactly when `J` is contained in
its kernel. -/
theorem nonempty_overHom_iff {Y : Scheme.{u}} (J : Y.IdealSheafData) (T : Over Y) :
    Nonempty (T ⟶ Over.mk J.subschemeι) ↔ J ≤ T.hom.ker := by
  refine ⟨fun ⟨b⟩ ↦ ?_, fun h ↦ ?_⟩
  · calc J = J.subschemeι.ker := (ker_subschemeι J).symm
      _ ≤ (b.left ≫ J.subschemeι).ker := ker_le_ker_comp _ _
      _ = T.hom.ker := congrArg Scheme.Hom.ker (Over.w b)
  · exact ⟨Over.homMk (IsClosedImmersion.lift J.subschemeι T.hom (by rwa [ker_subschemeι]))
      (IsClosedImmersion.lift_fac _ _ _)⟩

variable {I : Type v} {P : Scheme.{u}} {U : I → Scheme.{u}} (q : ∀ i, U i ⟶ P)
  (J : ∀ i, (U i).IdealSheafData)

/-- The property of a scheme over `P` that its pullback to each `U j` lies in the closed subscheme
cut out by `J j`. -/
def LiesInFamily (A : Over P) : Prop :=
  ∀ j, J j ≤ (pullback.snd A.hom (q j)).ker

/-- Lying in the family `J` is stable under pullback: if `A ⟶ B` is a morphism over `P` and `B`
lies in the family, so does `A`, because the kernel of a composite contains the kernel of its last
factor. -/
theorem liesInFamily_isStableUnderPullback :
    IsStableUnderPullback (LiesInFamily q J) := by
  intro A B φ hB j
  have : pullback.snd A.hom (q j) =
      pullback.map A.hom (q j) B.hom (q j) φ.left (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
        pullback.snd B.hom (q j) := by
    simp only [pullback.map, Category.comp_id]
    exact (pullback.lift_snd _ _ _).symm
  rw [this]
  exact (hB j).trans (ker_le_ker_comp _ _)

/-- Under the compatibility of the `J i` on the pairwise fibre products, a scheme over `U i` lies
in the family exactly when it lies in the closed subscheme cut out by `J i`. -/
theorem liesInFamily_map_iff
    (hJ : ∀ i j, (J i).comap (pullback.fst (q i) (q j)) = (J j).comap (pullback.snd (q i) (q j)))
    (i : I) (T : Over (U i)) :
    LiesInFamily q J ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ Over.mk (J i).subschemeι) := by
  rw [nonempty_overHom_iff]
  refine ⟨fun h ↦ ?_, fun h j ↦ ?_⟩
  · have h' : J i ≤ (pullback.snd (T.hom ≫ q i) (q i)).ker := h i
    have : T.hom = pullback.lift (𝟙 _) T.hom (by simp) ≫ pullback.snd (T.hom ≫ q i) (q i) :=
      (pullback.lift_snd _ _ _).symm
    rw [this]
    exact h'.trans (ker_le_ker_comp _ _)
  · show J j ≤ (pullback.snd (T.hom ≫ q i) (q j)).ker
    let m : pullback (T.hom ≫ q i) (q j) ⟶ pullback (q i) (q j) :=
      pullback.map _ _ _ _ T.hom (𝟙 _) (𝟙 _) (by simp) (by simp)
    have hm : pullback.snd (T.hom ≫ q i) (q j) = m ≫ pullback.snd (q i) (q j) := by
      simp only [m, pullback.map, Category.comp_id]
      exact (pullback.lift_snd _ _ _).symm
    have hm' : m ≫ pullback.fst (q i) (q j) = pullback.fst (T.hom ≫ q i) (q j) ≫ T.hom := by
      simp only [m, pullback.map, Category.comp_id]
      exact pullback.lift_fst _ _ _
    rw [hm, ← map_ker, le_map_iff_comap_le, ← hJ, ← le_map_iff_comap_le, map_ker, hm']
    exact h.trans (ker_le_ker_comp _ _)

/-- **Ideal sheaves glue along an fpqc covering.** Let `{q i : U i ⟶ P}` be an fpqc covering and
let `J i` be ideal sheaves on the `U i` whose pullbacks to the pairwise fibre products
`U i ×_P U j` agree. Then there is an ideal sheaf on `P` pulling back to each `J i`.

This is effective descent of closed immersions along fpqc coverings, [Stacks, Tag 03I0], read on
ideal sheaves. -/
@[sga "1 VIII 1.9" "partial", sga "3 IV 6.4.1" "partial", sga "3 VIII 6.4" "partial"]
theorem exists_comap_eq_of_fpqc_anyIndexUniverse
    (hq : Presieve.ofArrows U q ∈ Scheme.fpqcPrecoverage P)
    (hJ : ∀ i j, (J i).comap (pullback.fst (q i) (q j)) = (J j).comap (pullback.snd (q i) (q j))) :
    ∃ K : P.IdealSheafData, ∀ i, K.comap (q i) = J i := by
  have : ∀ i, IsClosedImmersion (Over.mk (J i).subschemeι).hom :=
    fun i ↦ inferInstanceAs (IsClosedImmersion (J i).subschemeι)
  obtain ⟨Z, hZ, e⟩ := exists_isClosedImmersion_of_localRepresentatives q
    (fun i ↦ Over.mk (J i).subschemeι) hq (liesInFamily_isStableUnderPullback q J)
    (liesInFamily_map_iff q J hJ)
  refine ⟨Z.hom.ker, fun i ↦ ?_⟩
  obtain ⟨ei⟩ := e i
  have : IsIso ei.hom.left := Functor.map_isIso (Over.forget (U i)) ei.hom
  have hw : ei.hom.left ≫ (J i).subschemeι = pullback.snd Z.hom (q i) := Over.w ei.hom
  rw [← ker_fst_of_isClosedImmersion, ← ker_subschemeι (J i),
    ← Scheme.Hom.ker_comp_of_isIso ei.hom.left, hw, ← pullbackSymmetry_hom_comp_fst,
    Scheme.Hom.ker_comp_of_isIso]

end AlgebraicGeometry.Scheme.IdealSheafData

end
