module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.LimitStage
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.ProjComparison

/-!
# The levels of a polarized tower inside the relative `Proj` over the limit

For a polarized tower with admissible tower of global sections, let `𝓑 = B̃` on
`S = Spec (lim Γ(Spec R_n, 𝒪))` and `ψ_n : g_n^* 𝓑 ⟶ 𝒜'_n` the isomorphisms of
`PolarizedTower.levelHom`, `g_n : Spec R_n ⟶ S`. The base change morphisms
`c'_n : Proj_{R_n}(𝒜'_n) ⟶ Proj_S(𝓑)` of the `ψ_n` are cartesian over `g_n`, and compatible with
the transitions `Proj_{R_n}(𝒜'_n) ⟶ Proj_{R_{n + 1}}(𝒜'_{n + 1})` of the tower; so are the
comparisons of Serre twists along them.

## Main results

* `Stacks.PolarizedAlgebraization.sectionTransition_of`: the transition of graded rings of global
  sections on a homogeneous section.
* `Stacks.PolarizedAlgebraization.PolarizedTower.sectionTransition_levelHom_globalSectionsHom`:
  on global sections, `ψ_n` is the projection `B ⟶ A_n`.
* `Stacks.PolarizedAlgebraization.PolarizedTower.levelMor_comp`: the compatibility of the `c'_n`
  with the transitions.
* `Stacks.PolarizedAlgebraization.PolarizedTower.levelTwist_eq`: the compatibility of the
  comparisons of Serre twists.

## References

* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.ProjectiveDeformation
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_naturality unitApp_map
  hom_app_map)

universe u

namespace Stacks.PolarizedAlgebraization

section General

variable {S S' : Scheme.{u}} [IsAffine S] [IsAffine S'] {A : SheafGradedAlgebra S} {g : S' ⟶ S}
  {A' : SheafGradedAlgebra S'} (ψ : SheafGradedAlgebraHom (A.pullback g) A')

/-- **`sectionTransition` on a homogeneous section**: the inverse image of the section, followed
by `ψ`, restricted to the whole of `S'`. -/
theorem sectionTransition_of (k : ℕ) (z : Γ(A.piece (k : ℤ), ⊤)) :
    sectionTransition ψ (DirectSum.of (A.sectionPieces ⊤) k z) =
      DirectSum.of (A'.sectionPieces ⊤) k ((A'.piece (k : ℤ)).presheaf.map
        (homOfLE (top_le_preimage_top g)).op
        ((ψ.app (k : ℤ)).app (g ⁻¹ᵁ ⊤) (unitApp g (A.piece (k : ℤ)) ⊤ z))) := by
  show ψ.sectionHom ⊤ (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange A
    g (topSite S) (topSite S') (top_le_preimage_top g) (DirectSum.of _ k z)) = _
  refine (congrArg (ψ.sectionHom ⊤)
    (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange_of A g (topSite S)
      (topSite S') (top_le_preimage_top g) k z)).trans ?_
  refine (SheafGradedAlgebraHom.sectionHom_of ψ ⊤ _).trans ?_
  congr 1
  exact hom_app_map (ψ.app (k : ℤ)) (top_le_preimage_top g) _

/-- Restricting a section to an open with the same points and back is the identity. -/
theorem presheaf_map_map_self {Z : Scheme.{u}} (N : Z.Modules) {W W' : Z.Opens} (h₁ : W ≤ W')
    (h₂ : W' ≤ W) (x : Γ(N, W)) :
    N.presheaf.map (homOfLE h₁).op (N.presheaf.map (homOfLE h₂).op x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have : (homOfLE h₂).op ≫ (homOfLE h₁).op = 𝟙 (op W) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

/-- Two restrictions of a section compose to one. -/
theorem presheaf_map_map_homOfLE {Z : Scheme.{u}} (N : Z.Modules) {W₀ W₁ W₂ : Z.Opens}
    (h₁ : W₀ ≤ W₁) (h₂ : W₁ ≤ W₂) (h : W₀ ≤ W₂) (x : Γ(N, W₂)) :
    N.presheaf.map (homOfLE h₁).op (N.presheaf.map (homOfLE h₂).op x) =
      N.presheaf.map (homOfLE h).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have : (homOfLE h₂).op ≫ (homOfLE h₁).op = (homOfLE h).op := Subsingleton.elim _ _
  rw [this]

/-- **`ψ` on the inverse image of a homogeneous global section**, read off `sectionTransition`: if
`sectionTransition ψ` carries `z` to `y` in degree `k`, then `ψ` carries `g^* z` to `y`. -/
theorem app_unitApp_of_sectionTransition {S S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    {A : SheafGradedAlgebra S} {g : S' ⟶ S} {A' : SheafGradedAlgebra S'}
    (ψ : SheafGradedAlgebraHom (A.pullback g) A') (k : ℕ) (z : Γ(A.piece (k : ℤ), ⊤))
    (y : Γ(A'.piece (k : ℤ), ⊤))
    (h : sectionTransition ψ (DirectSum.of (A.sectionPieces ⊤) k z) =
      DirectSum.of (A'.sectionPieces ⊤) k y) :
    (ψ.app (k : ℤ)).app (g ⁻¹ᵁ ⊤) (unitApp g (A.piece (k : ℤ)) ⊤ z) =
      (A'.piece (k : ℤ)).presheaf.map (homOfLE le_top).op y := by
  have h' := DirectSum.of_injective (β := A'.sectionPieces ⊤) k
    ((sectionTransition_of ψ k z).symm.trans h)
  refine (presheaf_map_map_self _ le_top (top_le_preimage_top g) _).symm.trans ?_
  exact congrArg ((A'.piece (k : ℤ)).presheaf.map (homOfLE le_top).op).hom h'

end General

section Chase

variable {S T₁ T₂ : Scheme.{u}} {𝓑 : SheafGradedAlgebra S}
  {A₁ : SheafGradedAlgebra T₁} {A₂ : SheafGradedAlgebra T₂}
  {g₁ : T₁ ⟶ S} {g₂ : T₂ ⟶ S} {t : T₁ ⟶ T₂} (hg : t ≫ g₂ = g₁)
  (ψ₁ : SheafGradedAlgebraHom (𝓑.pullback g₁) A₁)
  (ψ₂ : SheafGradedAlgebraHom (𝓑.pullback g₂) A₂) (α : SheafGradedAlgebraHom (A₂.pullback t) A₁)

/-- **`IsCompatTriple` from values on generating sections.** If maps out of `g₁^* 𝓑_m` are
determined by the inverse images of the sections `s m i`, if `ψ₁`, `ψ₂` carry these to (the
restrictions of) global sections `w₁ m i`, `w₂ m i`, and `α` carries the inverse image of
`w₂ m i` to `w₁ m i`, then `ψ₁` is `α` after `t^* ψ₂`. -/
theorem isCompatTriple_of_values {ι : ℕ → Type*} (s : ∀ m, ι m → Γ(𝓑.piece (m : ℤ), ⊤))
    (w₁ : ∀ m, ι m → Γ(A₁.piece (m : ℤ), ⊤)) (w₂ : ∀ m, ι m → Γ(A₂.piece (m : ℤ), ⊤))
    (hext : ∀ (m : ℕ) {F : T₁.Modules} (φ φ' : (Scheme.Modules.pullback g₁).obj
        (𝓑.piece (m : ℤ)) ⟶ F),
      (∀ i, φ.app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ _ ⊤ (s m i)) =
        φ'.app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ _ ⊤ (s m i))) → φ = φ')
    (hv₁ : ∀ (m : ℕ) i, (ψ₁.app (m : ℤ)).app (g₁ ⁻¹ᵁ ⊤) (unitApp g₁ _ ⊤ (s m i)) =
      (A₁.piece (m : ℤ)).presheaf.map (homOfLE le_top).op (w₁ m i))
    (hv₂ : ∀ (m : ℕ) i, (ψ₂.app (m : ℤ)).app (g₂ ⁻¹ᵁ ⊤) (unitApp g₂ _ ⊤ (s m i)) =
      (A₂.piece (m : ℤ)).presheaf.map (homOfLE le_top).op (w₂ m i))
    (hvα : ∀ (m : ℕ) i, (α.app (m : ℤ)).app (t ⁻¹ᵁ ⊤) (unitApp t _ ⊤ (w₂ m i)) =
      (A₁.piece (m : ℤ)).presheaf.map (homOfLE le_top).op (w₁ m i)) :
    IsCompatTriple ψ₁ ψ₂ α hg := by
  intro k
  by_cases hk : 0 ≤ k
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [← Iso.cancel_iso_inv_left ((Scheme.Modules.pullbackCongr hg).app (𝓑.piece (m : ℤ)))]
    refine (Iso.inv_hom_id_app_assoc _ _ _).trans ?_
    refine hext m _ _ fun i => ?_
    refine (hv₁ m i).trans ?_
    have hW₁ : g₁ ⁻¹ᵁ ⊤ ≤ t ⁻¹ᵁ (g₂ ⁻¹ᵁ ⊤) := fun _ _ => trivial
    have hW₂ : t ⁻¹ᵁ (g₂ ⁻¹ᵁ ⊤) ≤ t ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have hW₃ : g₁ ⁻¹ᵁ ⊤ ≤ t ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have v0 : ((Scheme.Modules.pullbackCongr hg).inv.app (𝓑.piece (m : ℤ))).app (g₁ ⁻¹ᵁ ⊤)
        (unitApp g₁ _ ⊤ (s m i)) =
        ((Scheme.Modules.pullback (t ≫ g₂)).obj (𝓑.piece (m : ℤ))).presheaf.map
          (homOfLE hW₁).op (unitApp (t ≫ g₂) _ ⊤ (s m i)) :=
      Stacks.AlgebraicGeometry.TwistMulLeg.pullbackCongr_hom_app_unitApp hg.symm _ ⊤ (s m i)
    have v1 : ((Scheme.Modules.pullbackComp t g₂).inv.app (𝓑.piece (m : ℤ))).app (g₁ ⁻¹ᵁ ⊤)
        (((Scheme.Modules.pullbackCongr hg).inv.app (𝓑.piece (m : ℤ))).app (g₁ ⁻¹ᵁ ⊤)
          (unitApp g₁ _ ⊤ (s m i))) =
        ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g₂).obj
          (𝓑.piece (m : ℤ)))).presheaf.map (homOfLE hW₁).op
          (unitApp t _ (g₂ ⁻¹ᵁ ⊤) (unitApp g₂ _ ⊤ (s m i))) := by
      refine (congrArg (fun x => ((Scheme.Modules.pullbackComp t g₂).inv.app
        (𝓑.piece (m : ℤ))).app (g₁ ⁻¹ᵁ ⊤) x) v0).trans ?_
      refine (hom_app_map _ hW₁ _).trans ?_
      exact congrArg (((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g₂).obj
          (𝓑.piece (m : ℤ)))).presheaf.map (homOfLE hW₁).op).hom
        (Scheme.Modules.pullbackComp_inv_unit t g₂ _ ⊤ (s m i))
    have v2 : ((Scheme.Modules.pullback t).map (ψ₂.app (m : ℤ))).app (g₁ ⁻¹ᵁ ⊤)
        (((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g₂).obj
          (𝓑.piece (m : ℤ)))).presheaf.map (homOfLE hW₁).op
          (unitApp t _ (g₂ ⁻¹ᵁ ⊤) (unitApp g₂ _ ⊤ (s m i)))) =
        ((Scheme.Modules.pullback t).obj (A₂.piece (m : ℤ))).presheaf.map (homOfLE hW₃).op
          (unitApp t _ ⊤ (w₂ m i)) := by
      refine (hom_app_map _ hW₁ _).trans ?_
      refine (congrArg (((Scheme.Modules.pullback t).obj (A₂.piece (m : ℤ))).presheaf.map
        (homOfLE hW₁).op).hom (unitApp_naturality t (ψ₂.app (m : ℤ)) (g₂ ⁻¹ᵁ ⊤) _)).trans ?_
      refine (congrArg (fun x => ((Scheme.Modules.pullback t).obj (A₂.piece (m : ℤ))).presheaf.map
        (homOfLE hW₁).op (unitApp t _ (g₂ ⁻¹ᵁ ⊤) x)) (hv₂ m i)).trans ?_
      refine (congrArg (((Scheme.Modules.pullback t).obj (A₂.piece (m : ℤ))).presheaf.map
        (homOfLE hW₁).op).hom (unitApp_map t _ le_top (w₂ m i))).trans ?_
      exact presheaf_map_map_homOfLE _ _ _ _ _
    have v3 : (α.app (m : ℤ)).app (g₁ ⁻¹ᵁ ⊤)
        (((Scheme.Modules.pullback t).obj (A₂.piece (m : ℤ))).presheaf.map (homOfLE hW₃).op
          (unitApp t _ ⊤ (w₂ m i))) =
        (A₁.piece (m : ℤ)).presheaf.map (homOfLE le_top).op (w₁ m i) := by
      refine (hom_app_map _ hW₃ _).trans ?_
      refine (congrArg ((A₁.piece (m : ℤ)).presheaf.map (homOfLE hW₃).op).hom (hvα m i)).trans ?_
      exact presheaf_map_map_homOfLE _ _ _ _ _
    exact (v3.symm.trans (congrArg (fun x => (α.app (m : ℤ)).app (g₁ ⁻¹ᵁ ⊤) x) v2.symm)).trans
      (congrArg (fun x => (α.app (m : ℤ)).app (g₁ ⁻¹ᵁ ⊤)
        (((Scheme.Modules.pullback t).map (ψ₂.app (m : ℤ))).app (g₁ ⁻¹ᵁ ⊤) x)) v1.symm)
  · have h1 : IsZero (𝓑.piece k) := 𝓑.negative_isZero _ (by omega)
    have h2 : IsZero ((Scheme.Modules.pullback (t ≫ g₂)).obj (𝓑.piece k)) :=
      (Scheme.Modules.pullback (t ≫ g₂)).map_isZero h1
    exact h2.eq_of_src _ _

end Chase

namespace PolarizedTower

variable (T : PolarizedTower.{u}) (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- A homogeneous element of the limit is sent by `levelProj` to a homogeneous global section. -/
private theorem exists_of_eq_levelProj (n k : ℕ) (b : (T.tow d₀ hd₀).limGrading k) :
    ∃ w : Γ((T.alg d₀ hd₀ n).piece (k : ℤ), ⊤),
      DirectSum.of ((T.alg d₀ hd₀ n).sectionPieces ⊤) k w =
        T.levelProj d₀ hd₀ n (b : (T.tow d₀ hd₀).Lim) :=
  (T.levelProj d₀ hd₀ n).map_mem b.2

/-- **On global sections, `ψ_n` is the projection `B ⟶ A_n`**: the transition of graded rings
of global sections of `ψ_n`, after `B ≅ Γ(S, B̃)`, is `PolarizedTower.levelProj`. -/
theorem sectionTransition_levelHom_globalSectionsHom (n : ℕ) (b : (T.tow d₀ hd₀).Lim) :
    sectionTransition (T.levelHom d₀ hd₀ n) (globalSectionsHom (T.tow d₀ hd₀).limGrading b) =
      T.levelProj d₀ hd₀ n b := by
  induction b using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | of k y =>
    let b : (T.tow d₀ hd₀).limGrading k := ⟨_, (T.tow d₀ hd₀).lof_mem_limGrading y⟩
    show sectionTransition (T.levelHom d₀ hd₀ n)
      (globalSectionsHom (T.tow d₀ hd₀).limGrading (b : (T.tow d₀ hd₀).Lim)) =
        T.levelProj d₀ hd₀ n (b : (T.tow d₀ hd₀).Lim)
    refine (congrArg (sectionTransition (T.levelHom d₀ hd₀ n))
      (globalSectionsHom_of (T.tow d₀ hd₀).limGrading b)).trans ?_
    refine (sectionTransition_of _ k _).trans ?_
    have h := specGradedHom_app_unitApp (T.tow d₀ hd₀).limGrading (T.levelMap n) (T.alg d₀ hd₀ n)
      (T.levelProj d₀ hd₀ n) (T.levelProj_algebraMap d₀ hd₀ n) k b
    obtain ⟨w, hw⟩ := T.exists_of_eq_levelProj d₀ hd₀ n k b
    refine (congrArg (fun z => DirectSum.of ((T.alg d₀ hd₀ n).sectionPieces ⊤) k
      (((T.alg d₀ hd₀ n).piece (k : ℤ)).presheaf.map (homOfLE (top_le_preimage_top _)).op z))
        h).trans ?_
    refine (congrArg (DirectSum.of ((T.alg d₀ hd₀ n).sectionPieces ⊤) k)
      (presheaf_map_map_self _ _ _ _)).trans ?_
    rw [← hw, DirectSum.of_eq_same]

/-- The base `Spec R_n` of level `n` of the tower is affine. -/
instance isAffine_deformation_S' (n : ℕ) : IsAffine (T.deformation n).S' :=
  inferInstanceAs (IsAffine (Spec (T.R.obj (op n))))

/-- `g_n : Spec R_n ⟶ S = Spec (lim Γ(Spec R_m, 𝒪))`. -/
abbrev levelBase (n : ℕ) : Spec (T.R.obj (op n)) ⟶ Spec (limit T.globalRing) :=
  Spec.map (T.levelMap n)

/-- The ring maps `R ⟶ R_n` are compatible with the transitions. -/
theorem levelMap_comp_ringMap (n : ℕ) :
    T.levelMap (n + 1) ≫ T.ringMap (Nat.le_succ n) = T.levelMap n := by
  ext x
  have h := congrArg (fun φ => φ.hom ((limit.π T.globalRing (op (n + 1))).hom x))
    (Scheme.ΓSpecIso_naturality (T.ringMap (Nat.le_succ n)))
  refine Eq.trans h.symm ?_
  exact congrArg (Scheme.ΓSpecIso (T.R.obj (op n))).hom.hom
    (Stacks.GradedTowerLimit.tr_limit_π T.globalRing n x)

/-- The maps `g_n` are compatible with the transitions. -/
theorem baseMap_comp_levelBase (n : ℕ) :
    T.baseMap (Nat.le_succ n) ≫ T.levelBase (n + 1) = T.levelBase n := by
  rw [levelBase, levelBase, baseMap, ← Spec.map_comp, levelMap_comp_ringMap]

/-- The transitions of graded rings of global sections are compatible with the projections from
the limit. -/
theorem sectionMap_levelProj (n : ℕ) (b : (T.tow d₀ hd₀).Lim) :
    T.sectionMap d₀ hd₀ n (T.levelProj d₀ hd₀ (n + 1) b) = T.levelProj d₀ hd₀ n b :=
  (T.tow d₀ hd₀).ρ_proj n b

/-- **The transitions of global sections of the `ψ_n` are compatible**:
`Γ(𝓑) ⟶ A_{n + 1} ⟶ A_n` is `Γ(𝓑) ⟶ A_n`. -/
theorem sectionMap_comp_sectionTransition (n : ℕ) :
    (T.sectionMap d₀ hd₀ n).comp (sectionTransition (T.levelHom d₀ hd₀ (n + 1))) =
      sectionTransition (T.levelHom d₀ hd₀ n) := by
  refine GradedRingHom.ext fun x => ?_
  obtain ⟨b, rfl⟩ := (bijective_globalSectionsHom (T.tow d₀ hd₀).limGrading).2 x
  show T.sectionMap d₀ hd₀ n (sectionTransition (T.levelHom d₀ hd₀ (n + 1))
    (globalSectionsHom (T.tow d₀ hd₀).limGrading b)) = _
  rw [sectionTransition_levelHom_globalSectionsHom, sectionTransition_levelHom_globalSectionsHom,
    sectionMap_levelProj]

variable (hT : (T.tow d₀ hd₀).IsAdmissible)

/-- **`c'_n : Proj_{R_n}(𝒜'_n) ⟶ Proj_S(𝓑)`**, the base change morphism of `ψ_n`. -/
abbrev levelMor (n : ℕ) :
    (relativeProj (T.alg d₀ hd₀ n)).scheme ⟶ (relativeProj (T.limitAlgebra d₀ hd₀)).scheme :=
  baseChangeMor (T.levelHom d₀ hd₀ n) (T.isIso_levelHom_app d₀ hd₀ hT n)

/-- **`c'_n` is cartesian over `g_n`.** -/
theorem isPullback_levelMor (n : ℕ) :
    IsPullback (T.levelMor d₀ hd₀ hT n) (relativeProj (T.alg d₀ hd₀ n)).toBase
      (relativeProj (T.limitAlgebra d₀ hd₀)).toBase (T.levelBase n) := by
  have h := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.isPullback_baseChangeHom
    (T.limitAlgebra d₀ hd₀) (T.levelBase n)
  have hev : ∀ᶠ d : ℕ in Filter.atTop, IsIso ((T.levelHom d₀ hd₀ n).app (d : ℤ)) :=
    Filter.Eventually.of_forall fun d => T.isIso_levelHom_app d₀ hd₀ hT n d
  refine IsPullback.of_iso h (asIso (projMapOfEventuallyIso (T.levelHom d₀ hd₀ n) hev)).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id]
    rw [IsIso.eq_inv_comp]
  · simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id]
    rw [IsIso.eq_inv_comp, projMapOfEventuallyIso_comp_toBase]

variable (hiso : ∀ (n : ℕ) (k : ℤ),
  IsIso ((AdmissibleDeformation.algebraPullbackHom (T.deformationHom n) d₀ hd₀).app k))

include hiso in
/-- The transitions `φ_n^* 𝒜'_{n + 1} ⟶ 𝒜'_n` are isomorphisms, read on `SheafGradedAlgebraHom`. -/
theorem isIso_transitionHom_app (n : ℕ) (k : ℤ) :
    IsIso ((AdmissibleDeformation.algebraPullbackSheafHom (T.deformationHom n) d₀ hd₀).app k) :=
  hiso n k

/-- The transition `Proj_{R_n}(𝒜'_n) ⟶ Proj_{R_{n + 1}}(𝒜'_{n + 1})` of the tower. -/
abbrev transitionMor (n : ℕ) :
    (relativeProj (T.alg d₀ hd₀ n)).scheme ⟶ (relativeProj (T.alg d₀ hd₀ (n + 1))).scheme :=
  baseChangeMor (AdmissibleDeformation.algebraPullbackSheafHom (T.deformationHom n) d₀ hd₀)
    (T.isIso_transitionHom_app d₀ hd₀ hiso n)

/-- **The `c'_n` are compatible with the transitions of the tower**:
`Proj_{R_n}(𝒜'_n) ⟶ Proj_{R_{n + 1}}(𝒜'_{n + 1}) ⟶ Proj_S(𝓑)` is `c'_n`. -/
theorem levelMor_comp (n : ℕ) :
    T.transitionMor d₀ hd₀ hiso n ≫ T.levelMor d₀ hd₀ hT (n + 1) = T.levelMor d₀ hd₀ hT n := by
  rw [← cancel_epi (topChart (T.alg d₀ hd₀ n))]
  have e1 : topChart (T.alg d₀ hd₀ n) ≫ T.transitionMor d₀ hd₀ hiso n =
      AlgebraicGeometry.Proj.map (T.sectionMap d₀ hd₀ n)
        (irrelevant_le_map_sectionTransition _ (T.isIso_transitionHom_app d₀ hd₀ hiso n)) ≫
        topChart (T.alg d₀ hd₀ (n + 1)) :=
    topChart_comp_projMap_baseChangeHom
      (AdmissibleDeformation.algebraPullbackSheafHom (T.deformationHom n) d₀ hd₀)
      (T.isIso_transitionHom_app d₀ hd₀ hiso n)
  have e : ∀ m, topChart (T.alg d₀ hd₀ m) ≫ T.levelMor d₀ hd₀ hT m =
      AlgebraicGeometry.Proj.map (sectionTransition (T.levelHom d₀ hd₀ m))
        (irrelevant_le_map_sectionTransition _ (T.isIso_levelHom_app d₀ hd₀ hT m)) ≫
        topChart (T.limitAlgebra d₀ hd₀) := fun m =>
    topChart_comp_projMap_baseChangeHom (T.levelHom d₀ hd₀ m) (T.isIso_levelHom_app d₀ hd₀ hT m)
  rw [← Category.assoc, e1, Category.assoc, e, ← Category.assoc,
    ← AlgebraicGeometry.Proj.map_comp, e]
  congr 1
  exact proj_map_congr (T.sectionMap_comp_sectionTransition d₀ hd₀ n) _ _

/-- `baseMap_comp_levelBase`, with the base of the transition of the tower. -/
theorem deformationHom_base_comp_levelBase (n : ℕ) :
    (T.deformationHom n).base ≫ T.levelBase (n + 1) = T.levelBase n :=
  T.baseMap_comp_levelBase n

/-- **`ψ_n` is `φ_n^* ψ_{n + 1}` followed by the transition `φ_n^* 𝒜'_{n + 1} ⟶ 𝒜'_n`**, degreewise
on the pieces of `𝓑`, through `g_n = g_{n + 1} ∘ φ_n`. -/
theorem levelHom_compat (n : ℕ) :
    IsCompatTriple (T.levelHom d₀ hd₀ n) (T.levelHom d₀ hd₀ (n + 1))
      (AdmissibleDeformation.algebraPullbackSheafHom (T.deformationHom n) d₀ hd₀)
      (T.deformationHom_base_comp_levelBase n) := by
  refine isCompatTriple_of_values _ _ _ _ (ι := fun m => (T.tow d₀ hd₀).limGrading m)
    (fun m b => homogeneousSectionTop (T.tow d₀ hd₀).limGrading b)
    (fun m b => (T.levelProj d₀ hd₀ n (b : (T.tow d₀ hd₀).Lim) :
      (T.alg d₀ hd₀ n).sectionRing ⊤) m)
    (fun m b => (T.levelProj d₀ hd₀ (n + 1) (b : (T.tow d₀ hd₀).Lim) :
      (T.alg d₀ hd₀ (n + 1)).sectionRing ⊤) m)
    (fun m _ φ φ' h => hom_ext_pullback_piece (T.tow d₀ hd₀).limGrading (T.levelMap n)
      (T.alg d₀ hd₀ n) (T.levelProj d₀ hd₀ n) (T.levelProj_algebraMap d₀ hd₀ n) m φ φ' h)
    (fun m b => specGradedHom_app_unitApp (T.tow d₀ hd₀).limGrading (T.levelMap n)
      (T.alg d₀ hd₀ n) (T.levelProj d₀ hd₀ n) (T.levelProj_algebraMap d₀ hd₀ n) m b)
    (fun m b => specGradedHom_app_unitApp (T.tow d₀ hd₀).limGrading (T.levelMap (n + 1))
      (T.alg d₀ hd₀ (n + 1)) (T.levelProj d₀ hd₀ (n + 1))
      (T.levelProj_algebraMap d₀ hd₀ (n + 1)) m b) (fun m b => ?_)
  refine app_unitApp_of_sectionTransition _ m _ _ ?_
  obtain ⟨w₂, hw₂⟩ := T.exists_of_eq_levelProj d₀ hd₀ (n + 1) m b
  obtain ⟨w₁, hw₁⟩ := T.exists_of_eq_levelProj d₀ hd₀ n m b
  rw [← hw₂, ← hw₁, DirectSum.of_eq_same, DirectSum.of_eq_same]
  exact (congrArg (T.sectionMap d₀ hd₀ n) hw₂).trans
    ((T.sectionMap_levelProj d₀ hd₀ n b).trans hw₁.symm)

/-- Maps out of `g_n^* 𝓑_m` are determined by the inverse images of the global sections. -/
theorem levelBase_hom_ext (n m : ℕ) {F : (Spec (T.R.obj (op n))).Modules}
    (φ φ' : (Scheme.Modules.pullback (T.levelBase n)).obj
      ((T.limitAlgebra d₀ hd₀).piece (m : ℤ)) ⟶ F)
    (h : ∀ b : Γ((T.limitAlgebra d₀ hd₀).piece (m : ℤ), ⊤),
      φ.app (T.levelBase n ⁻¹ᵁ ⊤) (unitApp (T.levelBase n) _ ⊤ b) =
        φ'.app (T.levelBase n ⁻¹ᵁ ⊤) (unitApp (T.levelBase n) _ ⊤ b)) : φ = φ' :=
  hom_ext_pullback_piece (T.tow d₀ hd₀).limGrading (T.levelMap n) (T.alg d₀ hd₀ n)
    (T.levelProj d₀ hd₀ n) (T.levelProj_algebraMap d₀ hd₀ n) m φ φ' fun _ => h _

/-- **The comparisons of Serre twists along the `c'_n` are compatible with the transitions**: the
comparison along `c'_n` is the one along `c'_{n + 1}`, pulled back along the transition, followed
by the comparison along the transition. -/
theorem levelTwist_eq (n : ℕ) :
    baseChangeTwist (T.levelHom d₀ hd₀ n) (T.isIso_levelHom_app d₀ hd₀ hT n) =
      compositeTwist (T.levelHom d₀ hd₀ n) (T.levelHom d₀ hd₀ (n + 1))
        (AdmissibleDeformation.algebraPullbackSheafHom (T.deformationHom n) d₀ hd₀)
        (T.isIso_levelHom_app d₀ hd₀ hT n) (T.isIso_levelHom_app d₀ hd₀ hT (n + 1))
        (T.isIso_transitionHom_app d₀ hd₀ hiso n) (T.levelMor_comp d₀ hd₀ hT hiso n) :=
  baseChangeTwist_eq_compositeTwist _ _ _ _ _ _ _ (T.deformationHom_base_comp_levelBase n)
    (T.levelHom_compat d₀ hd₀ n) (fun m _ φ φ' h => T.levelBase_hom_ext d₀ hd₀ n m φ φ' h)

end PolarizedTower

end Stacks.PolarizedAlgebraization

end
