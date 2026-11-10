module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOpenAmbient
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSupportedInOpen
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSupportedInOpenRepresentable
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeDoubledLine
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.HilbertPresheaf
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.OpenSubfunctor
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Hilbert families of an open subscheme

Let `i : X' ⟶ X` be an open immersion of `S`-schemes with `X ⟶ S` separated. A degree-`d`
Hilbert family `Z ⊆ X'_T` is also a closed subscheme of `X_T`: it is finite over `T`, hence
universally closed, and `X_T ⟶ T` is separated, so its immersion into `X_T` is closed. This
identifies the Hilbert families of `X'` with the Hilbert families of `X` supported in the image
of `i`, naturally in `T`. In the proof of Stacks Tag 0B9A this is the identification of the
subfunctor `F_U` of families supported in an affine open `U` with the Hilbert functor of `U`.

## Main definitions

* `Stacks.Hilbert.push`: the Hilbert family of `X` defined by a Hilbert family of `X'`.
* `Stacks.Hilbert.restrictFamily`: the Hilbert family of `X'` defined by a Hilbert family of `X`
  supported in the image of `i`.

## Main results

* `Stacks.Hilbert.restrictFamily_push`, `Stacks.Hilbert.push_restrictFamily`: the two are
  inverse.
* `Stacks.Hilbert.pushMap`, `Stacks.Hilbert.isOpenSubfunctor_pushMap`: the Hilbert functor of
  `X'` is an open subfunctor of that of `X`.
* `Stacks.Hilbert.push_supportedIn`: pushed families are supported in the image.
* `Stacks.Hilbert.baseChange_push`: pushing forward commutes with base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}} {X' X : Over S} (i : X' ⟶ X) [IsOpenImmersion i.left] {d : ℕ}

/-- The base change `X'_T ⟶ X_T` of an open immersion is an open immersion. -/
instance isOpenImmersion_familyAmbientMap (T : Over S) :
    IsOpenImmersion (familyAmbientMap i T) := by
  unfold familyAmbientMap
  infer_instance

/-- The base change `X_T ⟶ T` of a separated morphism is separated. -/
instance (T : Over S) [IsSeparated X.hom] : IsSeparated ((Over.pullback T.hom).obj X).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X.hom T.hom))

/-- A Hilbert family of `X'` is finite over `T`. -/
theorem isFinite_structural {T : Over S} (Z : HilbertFamily X' T d) :
    IsFinite (Z.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X').hom) := by
  have := Z.isFiniteLocallyFreeOfRank
  exact ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d)).1

/-- The closed subscheme of `X_T` defined by a family of `X'`: its immersion is closed. -/
theorem isClosedImmersion_push [IsSeparated X.hom] {T : Over S} (Z : HilbertFamily X' T d) :
    IsClosedImmersion (Z.ideal.subschemeι ≫ familyAmbientMap i T) := by
  have := isFinite_structural Z
  have : UniversallyClosed ((Z.ideal.subschemeι ≫ familyAmbientMap i T) ≫
      ((Over.pullback T.hom).obj X).hom) := by
    rw [Category.assoc, familyAmbientMap_comp_hom]
    infer_instance
  have : UniversallyClosed (Z.ideal.subschemeι ≫ familyAmbientMap i T) :=
    UniversallyClosed.of_comp_of_isSeparated _ ((Over.pullback T.hom).obj X).hom
  exact .of_isPreimmersion _ (Scheme.Hom.isClosedMap _).isClosed_range

/-- **The Hilbert family of `X` defined by a Hilbert family of `X'`.** -/
def push [IsSeparated X.hom] {T : Over S} (Z : HilbertFamily X' T d) : HilbertFamily X T d where
  ideal := (Z.ideal.subschemeι ≫ familyAmbientMap i T).ker
  isFiniteLocallyFreeOfRank := by
    have := isClosedImmersion_push i Z
    let φ := Z.ideal.subschemeι ≫ familyAmbientMap i T
    have hφ : inv φ.toImage ≫ φ = φ.ker.subschemeι := by
      rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
    have e : φ.ker.subschemeι ≫ ((Over.pullback T.hom).obj X).hom =
        inv φ.toImage ≫ Z.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X').hom := by
      rw [← hφ, Category.assoc, Category.assoc, familyAmbientMap_comp_hom]
    rw [e]
    exact (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d).cancel_left_of_respectsIso
      _ _ |>.mpr Z.isFiniteLocallyFreeOfRank

/-- The ideal of a pushed family is the kernel of its immersion into `X_T`. -/
theorem push_ideal [IsSeparated X.hom] {T : Over S} (Z : HilbertFamily X' T d) :
    (push i Z).ideal = (Z.ideal.subschemeι ≫ familyAmbientMap i T).ker :=
  rfl

/-- **Pulling back the kernel of a composite with an open immersion.** -/
theorem comap_ker_comp_of_isOpenImmersion {Z V Y : Scheme.{u}} (ψ : Z ⟶ V) (j : V ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact (ψ ≫ j)] : (ψ ≫ j).ker.comap j = ψ.ker := by
  ext W : 2
  have hsq : IsPullback ψ (𝟙 Z) j (ψ ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (ψ ≫ j) ψ (𝟙 Z) j hsq W).symm

/-- **Restricting a pushed family recovers its ideal.** -/
theorem comap_push_ideal [IsSeparated X.hom] {T : Over S} (Z : HilbertFamily X' T d) :
    (push i Z).ideal.comap (familyAmbientMap i T) = Z.ideal := by
  have := isClosedImmersion_push i Z
  rw [push_ideal, comap_ker_comp_of_isOpenImmersion, Scheme.IdealSheafData.ker_subschemeι]

/-- A pushed family is supported in the image of `X'`. -/
theorem push_supportedIn [IsSeparated X.hom] {T : Over S} (Z : HilbertFamily X' T d) :
    (push i Z).SupportedIn i.left.opensRange := by
  have := isClosedImmersion_push i Z
  let φ := Z.ideal.subschemeι ≫ familyAmbientMap i T
  have h : φ.imageι = inv φ.toImage ≫ φ := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  intro z
  change (φ.imageι ≫ familyProjection X T) z ∈ i.left.opensRange
  rw [h]
  refine ⟨familyProjection X' T (Z.ideal.subschemeι (inv φ.toImage z)), ?_⟩
  simp only [φ, Category.assoc, familyAmbientMap_familyProjection]
  rfl

/-- The family of `X'` defined by a family of `X` supported in the image of `X'`. -/
def restrictFamily {T : Over S} (W : HilbertFamily X T d) (hW : W.SupportedIn i.left.opensRange) :
    HilbertFamily X' T d where
  ideal := W.ideal.comap (familyAmbientMap i T)
  isFiniteLocallyFreeOfRank := by
    let jT := familyAmbientMap i T
    have hsurj : Function.Surjective (pullback.snd jT W.ideal.subschemeι) := by
      intro z
      have hz : W.ideal.subschemeι z ∈ Set.range jT := by
        rw [range_familyAmbientMap]
        exact hW z
      obtain ⟨v, hv⟩ := hz
      obtain ⟨q, -, hq⟩ := Scheme.Pullback.exists_preimage_pullback v z hv
      exact ⟨q, hq⟩
    have : IsIso (pullback.snd jT W.ideal.subschemeι) := by
      rw [isIso_iff_isOpenImmersion_and_surjective]
      exact ⟨inferInstance, ⟨hsurj⟩⟩
    have e : (W.ideal.comap jT).subschemeι ≫ ((Over.pullback T.hom).obj X').hom =
        ((W.ideal.comapIso jT).hom ≫ pullback.snd jT W.ideal.subschemeι) ≫
          W.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom := by
      rw [← familyAmbientMap_comp_hom i T, ← Scheme.IdealSheafData.comapIso_hom_fst]
      simp only [Category.assoc]
      rw [pullback.condition_assoc]
    change Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((W.ideal.comap jT).subschemeι ≫ ((Over.pullback T.hom).obj X').hom) d
    rw [e]
    exact (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d).cancel_left_of_respectsIso
      _ _ |>.mpr W.isFiniteLocallyFreeOfRank

/-- **A family supported in the image of `X'` is pushed forward from its restriction.** -/
theorem push_restrictFamily [IsSeparated X.hom] {T : Over S} (W : HilbertFamily X T d)
    (hW : W.SupportedIn i.left.opensRange) : push i (restrictFamily i W hW) = W := by
  let jT := familyAmbientMap i T
  have hsurj : Function.Surjective (pullback.snd jT W.ideal.subschemeι) := by
    intro z
    have hz : W.ideal.subschemeι z ∈ Set.range jT := by
      rw [range_familyAmbientMap]
      exact hW z
    obtain ⟨v, hv⟩ := hz
    obtain ⟨q, -, hq⟩ := Scheme.Pullback.exists_preimage_pullback v z hv
    exact ⟨q, hq⟩
  have : IsIso (pullback.snd jT W.ideal.subschemeι) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    exact ⟨inferInstance, ⟨hsurj⟩⟩
  refine HilbertFamily.ext ?_
  rw [push_ideal]
  change ((W.ideal.comap jT).subschemeι ≫ jT).ker = W.ideal
  rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition,
    ← Category.assoc, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- Restricting a pushed family recovers the family. -/
theorem restrictFamily_push [IsSeparated X.hom] {T : Over S} (Z : HilbertFamily X' T d) :
    restrictFamily i (push i Z) (push_supportedIn i Z) = Z :=
  HilbertFamily.ext (comap_push_ideal i Z)

/-- Pushing families forward is injective. -/
theorem push_injective [IsSeparated X.hom] {T : Over S} :
    Function.Injective (push i : HilbertFamily X' T d → HilbertFamily X T d) := by
  intro Z Z' h
  rw [← restrictFamily_push i Z, ← restrictFamily_push i Z']
  exact HilbertFamily.ext (congrArg (fun W => W.ideal.comap (familyAmbientMap i T)) h)

/-- **Pushing forward commutes with base change.** -/
theorem baseChange_push [IsSeparated X.hom] {T' T : Over S} (g : T' ⟶ T)
    (Z : HilbertFamily X' T d) : baseChange X g (push i Z) = push i (baseChange X' g Z) := by
  have h1 := (push_supportedIn i Z).baseChange g
  rw [← push_restrictFamily i _ h1]
  congr 1
  refine HilbertFamily.ext ?_
  change ((push i Z).ideal.comap (familyBaseChangeMap X g)).comap (familyAmbientMap i T') =
    (baseChange X' g Z).ideal
  rw [← Scheme.IdealSheafData.comap_comp, familyAmbientMap_comp_familyBaseChangeMap,
    Scheme.IdealSheafData.comap_comp, comap_push_ideal, baseChange_ideal]

/-! ### The open subfunctor of families supported in an open -/

variable (d)

/-- **The Hilbert functor of `X'` as a subfunctor of that of `X`.** -/
def pushMap [IsSeparated X.hom] : hilbPresheaf X' d ⟶ hilbPresheaf X d where
  app T := ↾fun p => ⟨p.1, push i p.2⟩
  naturality T T' g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, Z⟩
    change (⟨_, push i (familyPullback X' d g.unop rfl Z)⟩ : HilbSections X d _) =
      ⟨_, familyPullback X d g.unop rfl (push i Z)⟩
    rw [familyPullback, familyPullback, baseChange_push]

/-- `pushMap` sends a family to its pushed family. -/
theorem pushMap_app [IsSeparated X.hom] {T : Scheme.{u}} (s : T ⟶ S)
    (Z : HilbertFamily X' (Over.mk s) d) :
    (pushMap i d).app (op T) ⟨s, Z⟩ = ⟨s, push i Z⟩ :=
  rfl

/-- A family of `X` lies in the image of `pushMap` exactly when it is supported in the image of
`X'`. -/
theorem inImage_pushMap_iff [IsSeparated X.hom] {T : Scheme.{u}} (s : T ⟶ S)
    (W : HilbertFamily X (Over.mk s) d) :
    AlgebraicGeometry.InImage (pushMap i d) (⟨s, W⟩ : (hilbPresheaf X d).obj (op T)) ↔
      W.SupportedIn i.left.opensRange := by
  constructor
  · rintro ⟨⟨s', Z⟩, h⟩
    rw [pushMap_app] at h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    rw [← eq_of_heq h]
    exact push_supportedIn i Z
  · intro hW
    exact ⟨⟨s, restrictFamily i W hW⟩, by rw [pushMap_app, push_restrictFamily]⟩

/-- **The families supported in an open form an open subfunctor** (condition (2)(b) of the
gluing criterion in the proof of Stacks Tag 0B9A). -/
theorem isOpenSubfunctor_pushMap [IsSeparated X.hom] :
    AlgebraicGeometry.IsOpenSubfunctorHom (pushMap i d) := by
  refine ⟨fun T => ?_, fun T p => ?_⟩
  · rintro ⟨s, Z⟩ ⟨s', Z'⟩ h
    change (⟨s, push i Z⟩ : HilbSections X d T.unop) = ⟨s', push i Z'⟩ at h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    rw [push_injective i (eq_of_heq h)]
  · obtain ⟨s, W⟩ := p
    refine ⟨⟨(W.notSupportedLocus i.left.opensRange)ᶜ,
      (W.isClosed_notSupportedLocus _).isOpen_compl⟩, fun T' g => ?_⟩
    change AlgebraicGeometry.InImage (pushMap i d) (⟨g ≫ s, baseChange X (Over.homMk g rfl :
      Over.mk (g ≫ s) ⟶ Over.mk s) W⟩ : (hilbPresheaf X d).obj (op T')) ↔ _
    rw [inImage_pushMap_iff, HilbertFamily.baseChange_supportedIn_iff]
    exact ⟨fun h _ ⟨t, ht⟩ => ht ▸ h t, fun h t => h ⟨t, rfl⟩⟩

end Stacks.Hilbert

end
