module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.SchemeStructure
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.FamilyOfRationalPoints

/-!
# The closed points of the fibre of the Abel map are the complete linear system

Let `X` be a smooth projective curve over an algebraically closed field `k` and `D` an effective
Cartier divisor of degree `d`. A `k`-point of the fibre of the Abel map `γ_d` over the point of
`𝒪_X(D)` is a degree-`d` family over `Spec k`, that is an effective Cartier divisor `E ⊆ X` of
degree `d` with `𝒪_X(E) ≅ 𝒪_X(D)`; every member of `|D|` has degree `d`, because the degree of
an effective Cartier divisor is the degree of its invertible sheaf. So the `k`-points of the
fibre are the complete linear system `|D|`.

## Main results

* `Stacks.LinearSystemScheme.abelFibreSpecEquiv`: the `k`-points of the fibre of `γ_d` over the
  point of `𝒪_X(D)` are `|D|`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Hilbert

universe u

namespace Stacks.LinearSystemScheme

/-- An isomorphism `e : Y ≅ Y'` turns `e^* A ≅ B` into `A ≅ e⁻¹^* B`. -/
def isoPullbackInvOfIso {Y Y' : Scheme.{u}} (e : Y ≅ Y') {A : Y'.Modules} {B : Y.Modules}
    (i : (Scheme.Modules.pullback e.hom).obj A ≅ B) :
    A ≅ (Scheme.Modules.pullback e.inv).obj B :=
  (Scheme.Modules.pullbackId _).symm.app A ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id).symm.app A ≪≫
    ((Scheme.Modules.pullbackComp e.inv e.hom).symm.app A) ≪≫
    (Scheme.Modules.pullback e.inv).mapIso i

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
  (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- The identification `X ×_k k ≅ X`. -/
abbrev basePointIso : pullback f (𝟙 (Spec (.of k))) ≅ X :=
  asIso (pullback.fst f (𝟙 (Spec (.of k))))

/-- **The members of `|D|` as `k`-points of the fibre of `γ_d`.** -/
def pointOfMem {d : ℕ}
    (hd : invertibleCurveDegree k f (topologicalKrullDim_le_one k f)
      (Stacks.Divisors.modulesInvertibleSheaf D) = d)
    (E : X.IdealSheafData) (hE : E ∈ Stacks.Divisors.completeLinearSystem D) :
    abelFibre f D d (Stacks.Hilbert.fieldPoint k) := by
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor E := hE.1
  let π := pullback.fst f (𝟙 (Spec (.of k)))
  haveI hZ : Stacks.Divisors.IsEffectiveCartierDivisor (E.comap π) :=
    Stacks.Divisors.isPullbackDefined_of_flat π E ‹_›
  refine ⟨⟨E.comap π, ?_⟩, fun t => ?_⟩
  · have hsq : IsPullback (Scheme.IdealSheafData.subschemeMap _ _ π (E.le_map_comap π))
        ((E.comap π).subschemeι ≫ pullback.snd f (𝟙 (Spec (.of k)))) (E.subschemeι ≫ f)
        (𝟙 (Spec (.of k))) :=
      IsPullback.paste_vert (Stacks.Bertini.isPullback_subschemeι_comap E π).flip
        (IsPullback.of_hasPullback f (𝟙 _))
    let : Algebra k Γ(E.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (E.subschemeι ≫ f).appTop).hom.toAlgebra
    have h1 := isFiniteLocallyFreeOfRank_divisorSubscheme k f (topologicalKrullDim_le_one k f) E
    have h2 := invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections k f
      (topologicalKrullDim_le_one k f) E
    have h3 : invertibleCurveDegree k f (topologicalKrullDim_le_one k f)
        (Stacks.Divisors.modulesInvertibleSheaf E) = d :=
      (invertibleCurveDegree_eq_of_iso k f _ hE.2.some).trans hd
    have hr : Module.finrank k Γ(E.subscheme, ⊤) = d := by
      have := h2.symm.trans h3; exact_mod_cast this
    rw [hr] at h1
    exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hsq
  · refine ⟨⊤, isAffineOpen_top (Spec (.of k)), trivial, ?_⟩
    have hoi := isOpenImmersion_familyBaseChangeMap (curveOver f)
      (restrictHom (k := k) (T := Stacks.Hilbert.fieldPoint k) (⊤ : (Spec (.of k)).Opens).ι)
      (inferInstanceAs (IsOpenImmersion (⊤ : (Spec (.of k)).Opens).ι))
    set j := familyBaseChangeMap (curveOver f)
      (restrictHom (k := k) (T := Stacks.Hilbert.fieldPoint k) (⊤ : (Spec (.of k)).Opens).ι)
    have hpd : Stacks.Divisors.IsPullbackDefined j (E.comap π) :=
      Stacks.Divisors.isPullbackDefined_of_flat _ _ hZ
    have hpd' : Stacks.Divisors.IsPullbackDefined (j ≫ π) E :=
      Stacks.Divisors.isPullbackDefined_of_flat _ _ ‹_›
    have hjπ : j ≫ π = pullback.fst f ((⊤ : (Spec (.of k)).Opens).ι ≫ 𝟙 (Spec (.of k))) :=
      familyBaseChangeMap_comp_fst _ _
    refine ⟨@Stacks.Divisors.invertibleSheafPullbackIso _ _ j (E.comap π) hZ hpd ≪≫
      eqToIso (by rw [← Scheme.IdealSheafData.comap_comp]) ≪≫
      (Stacks.Divisors.invertibleSheafPullbackIso (j ≫ π) E).symm ≪≫
      (Scheme.Modules.pullback (j ≫ π)).mapIso hE.2.some ≪≫
      (Scheme.Modules.pullbackCongr hjπ).app _⟩

omit [IsAlgClosed k] [IsProjectiveVariety k f] [Divisors.IsEffectiveCartierDivisor D] in
/-- **A `k`-point of the fibre of `γ_d` is a member of `|D|`.** -/
theorem mem_of_point {d : ℕ} (Z : abelFibre f D d (Stacks.Hilbert.fieldPoint k)) :
    Z.1.ideal.comap (inv (pullback.fst f (𝟙 (Spec (.of k))))) ∈
      Stacks.Divisors.completeLinearSystem D := by
  set π := pullback.fst f (𝟙 (Spec (.of k)))
  have : SmoothOfRelativeDimension 1 f := Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve f
  have : SmoothOfRelativeDimension 1 (pullback.snd f (𝟙 (Spec (.of k)))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback f _) ‹_›
  have hfl : Stacks.Morphisms.IsFiniteLocallyFree
      (Z.1.ideal.subschemeι ≫ pullback.snd f (𝟙 (Spec (.of k)))) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
      (h := Z.1.isFiniteLocallyFreeOfRank)
  have hZ : Stacks.Divisors.IsEffectiveCartierDivisor Z.1.ideal :=
    (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree
      (pullback.snd f (𝟙 (Spec (.of k)))) Z.1.ideal).1
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor (Z.1.ideal.comap (inv π)) :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ hZ
  refine ⟨hE, ?_⟩
  obtain ⟨V, -, ht, ⟨β⟩⟩ := Z.2 (IsLocalRing.closedPoint k)
  have hV : V = ⊤ := eq_top_iff.mpr fun x _ => Subsingleton.elim (IsLocalRing.closedPoint k) x ▸ ht
  subst hV
  set j := familyBaseChangeMap (curveOver f)
    (restrictHom (k := k) (T := Stacks.Hilbert.fieldPoint k) (⊤ : (Spec (.of k)).Opens).ι)
  set pV := pullback.fst f ((⊤ : (Spec (.of k)).Opens).ι ≫ 𝟙 (Spec (.of k)))
  have hiso : IsIso ((⊤ : (Spec (.of k)).Opens).ι ≫ 𝟙 (Spec (.of k))) := by
    rw [Category.comp_id, ← Scheme.topIso_hom]; infer_instance
  have hjπ : j ≫ π = pV := familyBaseChangeMap_comp_fst _ _
  have hψ : inv pV ≫ j = inv π := by
    rw [← cancel_mono π, Category.assoc, hjπ, IsIso.inv_hom_id, IsIso.inv_hom_id]
  have hpd : Stacks.Divisors.IsPullbackDefined (inv pV ≫ j) Z.1.ideal := by
    rw [hψ]; exact hE
  refine ⟨eqToIso (by rw [hψ]; rfl) ≪≫
    (@Stacks.Divisors.invertibleSheafPullbackIso _ _ (inv pV ≫ j) Z.1.ideal hZ hpd).symm ≪≫
    ((Scheme.Modules.pullbackComp (inv pV) j).app _).symm ≪≫
    (Scheme.Modules.pullback (inv pV)).mapIso β ≪≫
    (Scheme.Modules.pullbackComp (inv pV) pV).app _ ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id pV)).app _ ≪≫
    (Scheme.Modules.pullbackId X).app _⟩

/-- **The `k`-points of the fibre of `γ_d` over the point of `𝒪_X(D)` are `|D|`**, a family
`Z ⊆ X ×_k k` corresponding to its image in `X`. -/
def abelFibreSpecEquiv {d : ℕ}
    (hd : invertibleCurveDegree k f (topologicalKrullDim_le_one k f)
      (Stacks.Divisors.modulesInvertibleSheaf D) = d) :
    abelFibre f D d (Stacks.Hilbert.fieldPoint k) ≃ Stacks.Divisors.completeLinearSystem D where
  toFun Z := ⟨_, mem_of_point k f D Z⟩
  invFun E := pointOfMem k f D hd E.1 E.2
  left_inv Z := by
    refine Subtype.ext (HilbertFamily.ext ?_)
    change (Z.1.ideal.comap _).comap _ = _
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  right_inv E := by
    refine Subtype.ext ?_
    change (E.1.comap _).comap _ = _
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]

end Stacks.LinearSystemScheme

end
