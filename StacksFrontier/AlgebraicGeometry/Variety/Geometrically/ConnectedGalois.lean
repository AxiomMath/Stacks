module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Galois.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Connectedness after a Galois base change

Let `T → X` be a morphism of schemes over a field. If, after base change to a Galois
extension, `T` is connected while `X` is disconnected, then `X` was already disconnected.

## Main results

* `AlgebraicGeometry.not_connectedSpace_of_galois_baseChange` descends the failure of
  connectedness from a Galois field extension in the presence of a morphism from a connected
  scheme.

## Implementation notes

The structural morphism of `T` is written as the composite of `f : T ⟶ X` with the structural
morphism of `X`. Thus the displayed morphism is automatically a morphism over the base field.
Base changes are expressed as categorical pullbacks against the morphism of spectra induced by
the field extension.

## References

* [Stacks Project, Tag 038C](https://stacks.math.columbia.edu/tag/038C)
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

universe u

/-- A space receiving a continuous map from a connected space and mapping to a connected space
by a clopen-preserving map, with liftable fibres, is connected. -/
@[sga "3 VIA 2.1.2" "more general"]
public lemma connectedSpace_of_clopen_image
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [ConnectedSpace A] [ConnectedSpace C]
    (i : A → B) (q : B → C) (hi : Continuous i)
    (hclopen : ∀ U : Set B, IsClopen U → IsClopen (q '' U))
    (hlift : ∀ (a : A) (b : B), q b = q (i a) → ∃ a' : A, i a' = b) :
    ConnectedSpace B := by
  rw [connectedSpace_iff_clopen]
  obtain ⟨a⟩ : Nonempty A := inferInstance
  refine ⟨⟨i a⟩, fun U hU => ?_⟩
  have hsplit := IsPreconnected.subset_or_subset (s := Set.range i)
    hU.isOpen hU.compl.isOpen disjoint_compl_right (by simp) (isPreconnected_range hi)
  have himage (V : Set B) (hV : IsClopen V) (h : Set.range i ⊆ V) : V = Set.univ := by
    have hc : IsClopen (q '' Vᶜ) := hclopen Vᶜ hV.compl
    have hproper : q (i a) ∉ q '' Vᶜ := by
      rintro ⟨b, hb, heq⟩
      obtain ⟨a', rfl⟩ := hlift a b heq
      exact hb (h (Set.mem_range_self a'))
    have hempty : q '' Vᶜ = ∅ :=
      (isClopen_iff.mp hc).resolve_right fun he => hproper (he.symm ▸ Set.mem_univ _)
    exact Set.eq_univ_iff_forall.mpr fun b => by
      by_contra hb
      have : q b ∈ q '' Vᶜ := ⟨b, hb, rfl⟩
      simp [hempty] at this
  rcases hsplit with h | h
  · exact Or.inr (himage U hU h)
  · exact Or.inl (Set.compl_univ_iff.mp (himage Uᶜ hU.compl h))

/-- Connectedness of the base change of `X` to a Galois extension, given connectedness of the
base change of `T` and of `X` itself. -/
private lemma connectedSpace_baseChange_of_galois
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
    {T X : Scheme.{u}} (f : T ⟶ X) (p : X ⟶ Spec (.of k))
    (hT : ConnectedSpace
      ((pullback (f ≫ p) (Spec.map <| ofHom <| algebraMap k kbar)) : Scheme.{u}))
    (hX : ConnectedSpace X) :
    ConnectedSpace ((pullback p (Spec.map <| ofHom <| algebraMap k kbar)) : Scheme.{u}) := by
  let y : Spec (.of kbar) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k kbar))
  let q : pullback p y ⟶ X := pullback.fst p y
  let qT : pullback (f ≫ p) y ⟶ T := pullback.fst (f ≫ p) y
  let e : pullback f q ≅ pullback (f ≫ p) y := pullbackRightPullbackFstIso p y f
  let i : pullback (f ≫ p) y ⟶ pullback p y := e.inv ≫ pullback.snd f q
  let : IsIntegralHom y := by
    show IsIntegralHom (Spec.map (ofHom (algebraMap k kbar)))
    rw [IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.mpr ⟨IsGalois.integral k⟩
  have hclopen (U : Set (pullback p y : Scheme.{u})) (hU : IsClopen U) :
      IsClopen (q '' U) := ⟨q.isClosedMap U hU.isClosed, q.isOpenMap U hU.isOpen⟩
  have hpull : IsPullback qT i f q := by
    apply IsPullback.of_iso_pullback (by simp [qT, i, q, e]) e.symm
    · exact pullbackRightPullbackFstIso_inv_fst p y f
    · rfl
  have hlift (a : (pullback (f ≫ p) y : Scheme.{u}))
      (b : (pullback p y : Scheme.{u}))
      (hab : q b = q (i a)) : ∃ a' : (pullback (f ≫ p) y : Scheme.{u}), i a' = b := by
    have hqi : q (i a) = f (qT a) := by
      have h := congrArg (fun g : pullback (f ≫ p) y ⟶ X => g a) hpull.w
      simpa [Scheme.Hom.comp_apply] using h.symm
    have hb : b ∈ q ⁻¹' (f '' {qT a}) := by
      show q b ∈ f '' {qT a}
      exact ⟨qT a, rfl, (hab.trans hqi).symm⟩
    rw [← Scheme.image_preimage_eq_of_isPullback hpull] at hb
    obtain ⟨a', _, ha'⟩ := hb
    exact ⟨a', ha'⟩
  let : ConnectedSpace (pullback (f ≫ p) y : Scheme.{u}) := hT
  let : ConnectedSpace X := hX
  exact connectedSpace_of_clopen_image i q i.continuous hclopen hlift

/-- Let `kbar/k` be a possibly infinite Galois extension and let `T → X` be a morphism of
schemes over `k`. If `T_kbar` is connected and `X_kbar` is disconnected, then `X` is
disconnected. -/
@[stacks 038C]
public theorem not_connectedSpace_of_galois_baseChange
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
    {T X : Scheme.{u}} (f : T ⟶ X) (p : X ⟶ Spec (.of k))
    (hT : ConnectedSpace
      ((pullback (f ≫ p) (Spec.map <| ofHom <| algebraMap k kbar)) : Scheme.{u}))
    (hX : ¬ ConnectedSpace
      ((pullback p (Spec.map <| ofHom <| algebraMap k kbar)) : Scheme.{u})) :
    ¬ ConnectedSpace X := fun h =>
  hX (connectedSpace_baseChange_of_galois k kbar f p hT h)

end AlgebraicGeometry
