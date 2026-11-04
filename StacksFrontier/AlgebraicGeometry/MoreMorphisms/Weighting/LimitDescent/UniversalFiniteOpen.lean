module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.Logic.Small.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.Constructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.LevelSetConstructible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.UniversalFiniteOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.Topology.Spectral.DescentConstructible
public import StacksFrontier.Topology.Spectral.LimitConstructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.LimitDescent.ConstructibleFibreSum

/-!
# Weightings tested on a universal finite open subscheme

Pullback-square lemmas for weighted fibre sums over finite open pieces of base changes, and the
criterion that a function on the source of a morphism is a weighting once the weighted fibre sum
over the universal finite open subscheme of a universal base change is locally constant, together
with its version after a further base change. Combined with the constructibility of weighted
fibre sums this gives `AlgebraicGeometry.exists_universal_constructible_integral`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe v u

namespace AlgebraicGeometry

private lemma isLocallyConstant_finiteOpen_integral
    {X Y U : Scheme.{u}} {f : X ⟶ Y} {w : X → ℤ}
    (hw : IsWeighting f w)
    (j : U ⟶ X) [IsOpenImmersion j] [IsFinite (j ≫ f)] :
    IsLocallyConstant (separableDegreeWeightedFiberSum (j ≫ f) (w ∘ j)) := by
  have comm : j ≫ f = (j ≫ f) ≫ 𝟙 Y := by simp
  apply hw j (j ≫ f) (𝟙 Y) comm (by infer_instance) _ (by infer_instance)
  have : IsOpenImmersion
      (pullback.lift j (j ≫ f) comm ≫ pullback.fst f (𝟙 Y)) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst f (𝟙 Y))

private lemma isLocallyConstant_baseChange_finiteOpen_integral
    {X Y V : Scheme.{u}} {f : X ⟶ Y}
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    {w : X → ℤ} (hw : IsWeighting f w)
    (g : V ⟶ Y) (U : (pullback f g).Opens)
    [IsFinite (U.ι ≫ pullback.snd f g)] :
    IsLocallyConstant (separableDegreeWeightedFiberSum
      (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g))) := by
  have hw' : IsWeighting (pullback.snd f g) (w ∘ pullback.fst f g) :=
    IsWeighting.comp_of_isPullback hw (IsPullback.of_hasPullback f g)
  exact isLocallyConstant_finiteOpen_integral hw' U.ι

/-- The preimage of a finite open piece under a pullback square is again finite over the base. -/
private lemma isFinite_preimage_ι_comp_of_isPullback
    {X X' Y Y' : Scheme.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {q : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback q p' p g)
    (U : X.Opens) [IsFinite (U.ι ≫ p)] :
    IsFinite ((q ⁻¹ᵁ U).ι ≫ p') := by
  let t : ((q ⁻¹ᵁ U : X'.Opens) : Scheme) ⟶ (U : Scheme) := q.resLE U _ le_rfl
  have ht : t ≫ U.ι = (q ⁻¹ᵁ U).ι ≫ q := by simp [t]
  have hs : IsPullback t (q ⁻¹ᵁ U).ι U.ι q :=
    IsOpenImmersion.isPullback t _ _ q ht.symm (by simp)
  exact MorphismProperty.of_isPullback (hs.paste_vert sq) inferInstance

private lemma finiteOpen_integral_comp_of_isPullback
    {X X' Y Y' : Scheme.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    {q : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback q p' p g)
    (U : X.Opens) (U' : X'.Opens) (hU : q ⁻¹ᵁ U = U')
    [IsFinite (U.ι ≫ p)] (w : X → ℤ) (w' : X' → ℤ) (hw : w ∘ q = w') :
    separableDegreeWeightedFiberSum (U.ι ≫ p) (w ∘ U.ι) ∘ g =
      separableDegreeWeightedFiberSum (U'.ι ≫ p') (w' ∘ U'.ι) := by
  let t : (U' : Scheme) ⟶ (U : Scheme) := q.resLE U U' hU.symm.le
  have ht : t ≫ U.ι = U'.ι ≫ q := by simp [t]
  have hs : IsPullback t U'.ι U.ι q :=
    IsOpenImmersion.isPullback t U'.ι U.ι q ht.symm (by simpa using hU)
  have hwt : (w ∘ U.ι) ∘ t = w' ∘ U'.ι := by
    subst hw
    funext x
    simp only [Function.comp_apply, ← Scheme.Hom.comp_apply, ht]
  rw [← hwt]
  exact separableDegreeWeightedFiberSum_comp_of_isPullback
    (U.ι ≫ p) t (U'.ι ≫ p') g (hs.paste_vert sq)
    (fun y ↦ (U.ι ≫ p).finite_preimage_singleton y) (w ∘ U.ι)

lemma isPullback_lift_snd
    {C : Type*} [Category C] [HasPullbacks C]
    {X Y V V' : C} (f : X ⟶ Y) (g : V ⟶ Y) (g' : V' ⟶ Y)
    (h : V' ⟶ V) (hh : h ≫ g = g') :
    IsPullback
      (pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ h)
        (by rw [Category.assoc, hh]; exact pullback.condition))
      (pullback.snd f g') (pullback.snd f g) h := by
  let q : pullback f g' ⟶ pullback f g :=
    pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ h)
      (by rw [Category.assoc, hh]; exact pullback.condition)
  have hs : IsPullback (q ≫ pullback.fst f g) (pullback.snd f g') f (h ≫ g) := by
    simpa only [q, pullback.lift_fst, hh] using IsPullback.of_hasPullback f g'
  exact hs.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f g)

private lemma isPullback_test_of_isPullback
    {X Y X' Y' V : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {b : Y' ⟶ Y}
    (sq : IsPullback p f' f b) (t : V ⟶ Y') :
    ∃ q : pullback f' t ⟶ pullback f (t ≫ b),
      IsPullback q (pullback.snd f' t) (pullback.snd f (t ≫ b)) (𝟙 V) ∧
        q ≫ pullback.fst f (t ≫ b) = pullback.fst f' t ≫ p := by
  let q : pullback f' t ⟶ pullback f (t ≫ b) :=
    pullback.lift (pullback.fst f' t ≫ p) (pullback.snd f' t)
      (by rw [Category.assoc, sq.w, ← Category.assoc, pullback.condition,
            Category.assoc])
  have hfst : q ≫ pullback.fst f (t ≫ b) = pullback.fst f' t ≫ p := pullback.lift_fst _ _ _
  have hs : IsPullback (q ≫ pullback.fst f (t ≫ b)) (pullback.snd f' t) f (𝟙 V ≫ (t ≫ b)) := by
    rw [hfst, Category.id_comp]
    exact (IsPullback.of_hasPullback f' t).paste_horiz sq
  exact ⟨q, hs.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (t ≫ b)), hfst⟩

private lemma isPullback_pullback_of_isPullback
    {X Y X' Y' V : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {b : Y' ⟶ Y}
    (sq : IsPullback p f' f b) (g : V ⟶ Y) :
    ∃ q : pullback f' (pullback.fst b g) ⟶ pullback f g,
      IsPullback q (pullback.snd f' (pullback.fst b g)) (pullback.snd f g) (pullback.snd b g) ∧
        q ≫ pullback.fst f g = pullback.fst f' (pullback.fst b g) ≫ p := by
  obtain ⟨q, hq, hqfst⟩ := isPullback_test_of_isPullback sq (pullback.fst b g)
  have key := hq.paste_horiz (isPullback_lift_snd f g (pullback.fst b g ≫ b) (pullback.snd b g)
    pullback.condition.symm)
  rw [Category.id_comp] at key
  exact ⟨_, key, by rw [Category.assoc, pullback.lift_fst, hqfst]⟩

lemma isLocallyConstant_finiteOpen_integral_of_isPullback
    {X Y X' Y' V : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {b : Y' ⟶ Y}
    (sq : IsPullback p f' f b) [LocallyOfFiniteType f'] [LocallyQuasiFinite f']
    (g : V ⟶ Y) (U : (pullback f g).Opens)
    [IsFinite (U.ι ≫ pullback.snd f g)]
    (w : X → ℤ) (w' : X' → ℤ) (hww : w' = w ∘ p)
    (hw' : IsWeighting f' w') :
    IsLocallyConstant
      (separableDegreeWeightedFiberSum
        (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g)) ∘
          pullback.snd b g) := by
  obtain ⟨q, sq', hq⟩ := isPullback_pullback_of_isPullback sq g
  have := isFinite_preimage_ι_comp_of_isPullback sq' U
  have heq := finiteOpen_integral_comp_of_isPullback sq' U (q ⁻¹ᵁ U) rfl
    (w ∘ pullback.fst f g) (w' ∘ pullback.fst f' (pullback.fst b g)) (by
      funext x
      simp only [hww, Function.comp_apply, ← Scheme.Hom.comp_apply, hq])
  exact (congrArg IsLocallyConstant heq).mpr
    (isLocallyConstant_baseChange_finiteOpen_integral hw' (pullback.fst b g) (q ⁻¹ᵁ U))

private lemma isLocallyConstant_finiteOpen_of_universal
    {X Y V V' S : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y) (g' : V' ⟶ Y)
    (U : (pullback f g).Opens) (U' : (pullback f g').Opens)
    [IsFinite (U.ι ≫ pullback.snd f g)]
    (h : V' ⟶ V) (hh : h ≫ g = g')
    (hU : (pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ h)
      (by rw [Category.assoc, hh]; exact pullback.condition)) ⁻¹ᵁ U = U')
    (w : X → ℤ) (m : S ⟶ V) (k : V' ⟶ S) (hk : k ≫ m = h)
    (hτ : IsLocallyConstant (separableDegreeWeightedFiberSum
      (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g)) ∘ m)) :
    IsLocallyConstant (separableDegreeWeightedFiberSum
      (U'.ι ≫ pullback.snd f g') (w ∘ (U'.ι ≫ pullback.fst f g'))) := by
  have heq := finiteOpen_integral_comp_of_isPullback
    (isPullback_lift_snd f g g' h hh) U U' hU (w ∘ pullback.fst f g) (w ∘ pullback.fst f g')
    (by funext x; simp only [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst])
  have hmk : (h : V' → V) = m ∘ k := by rw [← hk]; rfl
  refine (congrArg IsLocallyConstant heq).mp ?_
  rw [hmk]
  exact hτ.comp_continuous k.continuous

private lemma isLocallyConstant_integral_of_affine_finiteOpen
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) [IsAffine V]
    (H : ∀ (g : V ⟶ Y) (W : (pullback f g).Opens),
      IsFinite (W.ι ≫ pullback.snd f g) →
      IsLocallyConstant (separableDegreeWeightedFiberSum
        (W.ι ≫ pullback.snd f g) (w ∘ (W.ι ≫ pullback.fst f g))))
    (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y) (comm : h ≫ f = π ≫ g)
    [IsOpenImmersion (pullback.lift h π comm)] [IsFinite π] :
    IsLocallyConstant (separableDegreeWeightedFiberSum π (w ∘ h)) := by
  let j : U ⟶ pullback f g := pullback.lift h π comm
  let W := j.opensRange
  let e : U ≅ (W : Scheme) := IsOpenImmersion.isoOfRangeEq j W.ι (by simp [W])
  have he : e.hom ≫ W.ι = j := by simp [e]
  have heπ : e.hom ≫ (W.ι ≫ pullback.snd f g) = π := by
    rw [← Category.assoc, he]
    exact pullback.lift_snd _ _ _
  have heh : e.hom ≫ (W.ι ≫ pullback.fst f g) = h := by
    rw [← Category.assoc, he]
    exact pullback.lift_fst _ _ _
  have hπ : W.ι ≫ pullback.snd f g = e.inv ≫ π := by
    rw [← heπ]
    simp only [Iso.inv_hom_id_assoc]
  have : IsFinite (W.ι ≫ pullback.snd f g) := by rw [hπ]; infer_instance
  have hτ := H g W inferInstance
  have sq : IsPullback e.hom π (W.ι ≫ pullback.snd f g) (𝟙 V) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using heπ⟩
  have heq := separableDegreeWeightedFiberSum_comp_of_isPullback
    (W.ι ≫ pullback.snd f g) e.hom π (𝟙 V) sq
    (fun v ↦ (W.ι ≫ pullback.snd f g).finite_preimage_singleton v)
    (w ∘ (W.ι ≫ pullback.fst f g))
  have hw : (w ∘ (W.ι ≫ pullback.fst f g)) ∘ e.hom = w ∘ h := by
    funext x
    simp only [Function.comp_apply, ← Scheme.Hom.comp_apply, heh]
  rw [hw] at heq
  change IsLocallyConstant
    (separableDegreeWeightedFiberSum (W.ι ≫ pullback.snd f g)
      (w ∘ (W.ι ≫ pullback.fst f g)) ∘ (𝟙 V : V ⟶ V)) at hτ
  rwa [heq] at hτ

private lemma isLocallyConstant_of_affineOpen
    {X : Scheme.{u}} {B : Type*} (w : X → B)
    (H : ∀ T : X.affineOpens, IsLocallyConstant (w ∘ T.1.ι)) :
    IsLocallyConstant w := by
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro b
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨_, ⟨T, hT, rfl⟩, hxT, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let j := Scheme.Opens.ι (X := X) T
  let S : Set T := {y | w (j y) = b}
  have hS : IsOpen S := (H ⟨T, hT⟩).isOpen_fiber b
  refine ⟨j '' S, ?_, (Scheme.Hom.isOpenEmbedding j).isOpenMap _ hS, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hz
  · exact ⟨⟨x, hxT⟩, hx, rfl⟩

private lemma isWeighting_of_affine_finiteOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ)
    (H : ∀ (V : Scheme.{u}) [IsAffine V] (g : V ⟶ Y)
      (W : (pullback f g).Opens), IsFinite (W.ι ≫ pullback.snd f g) →
      IsLocallyConstant (separableDegreeWeightedFiberSum
        (W.ι ≫ pullback.snd f g) (w ∘ (W.ι ≫ pullback.fst f g)))) :
    IsWeighting f w := by
  intro U V h π g comm _ hj hπ
  let := hj
  let := hπ
  apply isLocallyConstant_of_affineOpen
  intro T
  let U' := π ⁻¹ᵁ T.1
  let π' : (U' : Scheme) ⟶ (T.1 : Scheme) := π ∣_ T.1
  let h' : (U' : Scheme) ⟶ X := U'.ι ≫ h
  let g' : (T.1 : Scheme) ⟶ Y := T.1.ι ≫ g
  have hπ' : π' ≫ T.1.ι = U'.ι ≫ π := by simp [π', U']
  have comm' : h' ≫ f = π' ≫ g' := by
    dsimp only [h', g']
    rw [Category.assoc, comm, ← Category.assoc, ← hπ', Category.assoc]
  let j : U ⟶ pullback f g := pullback.lift h π comm
  let j' : (U' : Scheme) ⟶ pullback f g' := pullback.lift h' π' comm'
  let q : pullback f g' ⟶ pullback f g :=
    pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ T.1.ι)
      (by rw [Category.assoc]; exact pullback.condition)
  have sq : IsPullback q (pullback.snd f g') (pullback.snd f g) T.1.ι :=
    isPullback_lift_snd f g g' T.1.ι rfl
  have : IsOpenImmersion q := MorphismProperty.of_isPullback sq.flip inferInstance
  have hjq : j' ≫ q = U'.ι ≫ j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, q, j', j, pullback.lift_fst]
      rfl
    · simp only [Category.assoc, q, j', j, pullback.lift_snd, pullback.lift_snd_assoc]
      exact hπ'
  have : IsOpenImmersion (j' ≫ q) := by rw [hjq]; infer_instance
  have : IsOpenImmersion j' := IsOpenImmersion.of_comp j' q
  have : IsFinite π' := inferInstanceAs (IsFinite (π ∣_ T.1))
  have hlocal := isLocallyConstant_integral_of_affine_finiteOpen f w (H T.1)
    h' π' g' comm'
  have sq' : IsPullback U'.ι π' π T.1.ι :=
    (IsOpenImmersion.isPullback π' U'.ι T.1.ι π hπ'.symm (by simp [U'])).flip
  have heq := separableDegreeWeightedFiberSum_comp_of_isPullback
    π U'.ι π' T.1.ι sq' (fun v ↦ π.finite_preimage_singleton v) (w ∘ h)
  rw [heq]
  exact hlocal

private lemma isWeighting_of_universal_finiteOpen
    {X Y V : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y)
    (U : (pullback f g).Opens) [IsFinite (U.ι ≫ pullback.snd f g)]
    (huniv : ∀ (V' : Scheme.{u}) [IsAffine V'] (g' : V' ⟶ Y)
      (U' : (pullback f g').Opens), IsFinite (U'.ι ≫ pullback.snd f g') →
      ∃ (h : V' ⟶ V) (hh : h ≫ g = g'),
        (pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ h)
          (by rw [Category.assoc, hh]; exact pullback.condition)) ⁻¹ᵁ U = U')
    (w : X → ℤ)
    (hτ : IsLocallyConstant (separableDegreeWeightedFiberSum
      (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g)))) :
    IsWeighting f w := by
  apply isWeighting_of_affine_finiteOpen f w
  intro V' _ g' U' hU'
  obtain ⟨h, hh, hpre⟩ := huniv V' g' U' hU'
  exact isLocallyConstant_finiteOpen_of_universal f g g' U U' h hh hpre w (𝟙 V) h
    (Category.comp_id h) hτ

lemma isWeighting_of_universal_finiteOpen_baseChange
    {X Y X' Y' V : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {b : Y' ⟶ Y}
    (sq : IsPullback p f' f b) (g : V ⟶ Y)
    (U : (pullback f g).Opens) [IsFinite (U.ι ≫ pullback.snd f g)]
    (huniv : ∀ (T : Scheme.{u}) [IsAffine T] (t : T ⟶ Y)
      (W : (pullback f t).Opens), IsFinite (W.ι ≫ pullback.snd f t) →
      ∃ (h : T ⟶ V) (hh : h ≫ g = t),
        (pullback.lift (pullback.fst f t) (pullback.snd f t ≫ h)
          (by rw [Category.assoc, hh]; exact pullback.condition)) ⁻¹ᵁ U = W)
    (w : X → ℤ) (w' : X' → ℤ) (hww : w' = w ∘ p)
    (hτ : IsLocallyConstant
      (separableDegreeWeightedFiberSum
        (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g)) ∘
          pullback.snd b g)) :
    IsWeighting f' w' := by
  apply isWeighting_of_affine_finiteOpen f' w'
  intro T _ t W hW
  obtain ⟨q, hq, hqfst⟩ := isPullback_test_of_isPullback sq t
  let : IsIso q := hq.isIso_fst_of_isIso
  let r : pullback f (t ≫ b) ⟶ pullback f' t := inv q
  have hr : r ≫ pullback.snd f' t = pullback.snd f (t ≫ b) := by
    have hq' := hq.w
    rw [Category.comp_id] at hq'
    rw [← hq']
    simp [r]
  have hrsq : IsPullback r (pullback.snd f (t ≫ b))
      (pullback.snd f' t) (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hr⟩
  have := isFinite_preimage_ι_comp_of_isPullback hrsq W
  obtain ⟨h, hh, hpre⟩ := huniv T (t ≫ b) (r ⁻¹ᵁ W) inferInstance
  have hτ' := isLocallyConstant_finiteOpen_of_universal f g (t ≫ b) U (r ⁻¹ᵁ W)
    h hh hpre w (pullback.snd b g) (pullback.lift t h hh.symm) (pullback.lift_snd _ _ _) hτ
  have hrfst : r ≫ pullback.fst f' t ≫ p = pullback.fst f (t ≫ b) := by
    rw [← hqfst, ← Category.assoc]
    simp [r]
  exact (congrArg IsLocallyConstant (finiteOpen_integral_comp_of_isPullback hrsq W (r ⁻¹ᵁ W) rfl
    (w' ∘ pullback.fst f' t) (w ∘ pullback.fst f (t ≫ b)) (by
      funext x
      simp only [hww, Function.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, hrfst]))).mpr
    hτ'

lemma exists_universal_constructible_integral
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyQuasiFinite f] (hf : FinitePresentation f)
    (w : X → ℤ) (hfinite : (Set.range w).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | w x = n}) :
    ∃ (V : Scheme.{u}) (g : V ⟶ Y) (U : (pullback f g).Opens),
      FinitePresentation g ∧ IsFinite (U.ι ≫ pullback.snd f g) ∧
      (∀ (V' : Scheme.{u}) [IsAffine V'] (g' : V' ⟶ Y)
        (U' : (pullback f g').Opens), IsFinite (U'.ι ≫ pullback.snd f g') →
        ∃ (h : V' ⟶ V) (hh : h ≫ g = g'),
          (pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ h)
            (by rw [Category.assoc, hh]; exact pullback.condition)) ⁻¹ᵁ U = U') ∧
      (Set.range (separableDegreeWeightedFiberSum
        (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g)))).Finite ∧
      (∀ n, Topology.IsConstructible
        {v | separableDegreeWeightedFiberSum
          (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g)) v = n}) ∧
      (IsWeighting f w ↔
        IsLocallyConstant (separableDegreeWeightedFiberSum
          (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g)))) := by
  let : LocallyOfFinitePresentation f := hf.1
  obtain ⟨V, g, U, hg, hU, huniv⟩ :=
    exists_universal_finite_open_subscheme f hf
  let : QuasiCompact g := hg.2.1
  let : QuasiSeparated g := hg.2.2
  let : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace g
  let : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated g
  let : IsFinite (U.ι ≫ pullback.snd f g) := hU
  obtain ⟨hfin, hlev⟩ := constructible_finiteOpen_integral f g U w hfinite hlevels
  exact ⟨V, g, U, hg, hU, huniv, hfin, hlev,
    fun hw ↦ isLocallyConstant_baseChange_finiteOpen_integral hw g U,
    isWeighting_of_universal_finiteOpen f g U huniv w⟩

end AlgebraicGeometry

