module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectGlueCover
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectRestrictOpen
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTrivialisedHom

/-!
# Refining local solutions of [Stacks, Tag 0EXD] to free ones over members of a basis

Given a commutative square of schemes in characteristic `p` and an object `T` of the categorical
fibre product of [Stacks, Tag 0EXD] whose restriction over each member of an open cover of the
base is in the essential image of the restricted comparison functor, the cover can be refined to
one by members of a prescribed basis over each of which the restriction of `T` is the image of a
**free** module.  This is the shape the Zariski glueing of the tag consumes.

## Main results

* `AlgebraicGeometry.exists_cover_free_of_mem_essImage_restrict`: the refinement.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

section Refine

variable {X X' Z E : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z)

/-- The free module on a finite type is isomorphic to the free module of rank its cardinality,
on the finite locally free modules over the Frobenius colimit. -/
noncomputable def frobeniusColimitFreeIsoOfFinite {Y : Scheme.{u}} (hY : IsInCharacteristic Y p)
    (K : Type u) [hK : Finite K] :
    (⟨_root_.SheafOfModules.free K, isFiniteLocallyFreeFrobeniusColimitFree p hY K⟩ :
        frobeniusColimitVectorBundles Y p hY) ≅
      frobeniusColimitFreeVectorBundle p hY (Nat.card K) :=
  ObjectProperty.isoMk _ ((_root_.SheafOfModules.freeFunctor
    (R := frobeniusColimitRingSheaf Y p hY)).mapIso
      ((Finite.equivFin K).trans Equiv.ulift.symm).toIso)

/-- **A cover by local solutions refines to a cover by members of a basis with free local
solutions.** If, over every member `V s` of an open cover of `X`, the restriction of `T` is in
the essential image of the restricted comparison functor, then there are members `W j` of the
basis `B` covering `X` and ranks `m j` such that the restriction of `T` over `W j` is isomorphic
to the image under the comparison functor of the free module of rank `m j`. -/
theorem exists_cover_free_of_mem_essImage_restrict {B : Set X.Opens} (hB : Opens.IsBasis B)
    {σ : Type u} (V : σ → X.Opens) (hV : ⨆ s, V s = ⊤)
    (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX'))
    (h : ∀ s, (frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw (V s)).essImage
      ((frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (V s)).obj T)) :
    ∃ (J : Type u) (W : J → X.Opens) (m : J → ℕ), (∀ j, W j ∈ B) ∧ (⨆ j, W j = ⊤) ∧
      ∀ j, Nonempty ((frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw (W j)).obj
        (frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX (W j)) (m j)) ≅
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (W j)).obj T) := by
  have key : ∀ y : X, ∃ (W : X.Opens) (m : ℕ), W ∈ B ∧ y ∈ W ∧
      Nonempty ((frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw W).obj
        (frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX W) m) ≅
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw W).obj T) := by
    intro y
    obtain ⟨s, hs⟩ := Opens.mem_iSup.mp (hV ▸ trivial : y ∈ ⨆ s, V s)
    obtain ⟨M, ⟨μ⟩⟩ := h s
    have hVs := isInCharacteristic_toScheme hX (V s)
    obtain ⟨J', W', K, hK, hcov, hfree⟩ :=
      exists_cover_free_frobeniusColimitVectorBundlesPullback p (V s).toScheme hVs M
    let y' : (V s).toScheme := ⟨y, hs⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov ▸ trivial : y' ∈ ⨆ i, W' i)
    have hyO : y ∈ (V s).ι ''ᵁ W' i := ⟨y', hi, rfl⟩
    obtain ⟨W, hWB, hyW, hWO⟩ := (Opens.isBasis_iff_nbhd.mp hB) hyO
    have hWV : W ≤ V s := hWO.trans (Scheme.Opens.ι_image_le _ _)
    have hrange : Set.range (X.homOfLE hWV).base ⊆ Set.range (W' i).ι.base := by
      rintro _ ⟨w, rfl⟩
      obtain ⟨v, hv, hvw⟩ := hWO w.2
      have : X.homOfLE hWV w = v := Subtype.ext ((Scheme.homOfLE_apply hWV w).trans hvw.symm)
      rwa [Scheme.Opens.range_ι, this]
    let g := IsOpenImmersion.lift (W' i).ι (X.homOfLE hWV) hrange
    have hg : g ≫ (W' i).ι = X.homOfLE hWV := IsOpenImmersion.lift_fac _ _ _
    have hW := isInCharacteristic_toScheme hX W
    have hW' := isInCharacteristic_toScheme hVs (W' i)
    have : Finite (K i) := hK i
    let φ : (frobeniusColimitVectorBundlesPullback p (X.homOfLE hWV) hW hVs).obj M ≅
        frobeniusColimitFreeVectorBundle p hW (Nat.card (K i)) :=
      ((frobeniusColimitVectorBundlesPullbackTriangleIso p g (W' i).ι (X.homOfLE hWV)
          hW hW' hVs hg).app M).symm ≪≫
        (frobeniusColimitVectorBundlesPullback p g hW hW').mapIso
          ((hfree i).some ≪≫ frobeniusColimitFreeIsoOfFinite p hW' (K i)) ≪≫
        frobeniusColimitFreeVectorBundlePullbackIso p g hW hW' _
    exact ⟨W, Nat.card (K i), hWB, hyW,
      ⟨(frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw W).mapIso φ.symm ≪≫
        (frobeniusColimitLocNestedIso p b z q e hX hX' hZ hE hw hWV M).symm ≪≫
        (frobeniusColimitLocNested p b z q e hX' hZ hE hw hWV).mapIso μ ≪≫
        (frobeniusColimitLocRestrictComp p b z q e hX' hZ hE hw hWV).app T⟩⟩
  choose W m hWB hyW hiso using key
  exact ⟨X, W, m, hWB, top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ⟨y, hyW y⟩, hiso⟩

end Refine

end AlgebraicGeometry

end
