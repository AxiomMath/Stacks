module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.IsoGluing
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.Theta
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Gluing morphisms of `Picardstack_{X/B}` along an fpqc covering

Let `C` and `C'` be objects of `Picardstack_{X/B}` and let `β : C.T ⟶ C'.T` be a morphism of
their test schemes.  Let `r i : P i ⟶ C` be morphisms whose base changes `X_{P i} ⟶ X_C` form an
fpqc covering, and let `ρ i : P i ⟶ C'` be morphisms over the composites `r i ≫ β`.  If the
`ρ i` agree on cartesian overlaps `Q i j` of the `P i` — after precomposition with the two
morphisms `Q i j ⟶ P i`, `Q i j ⟶ P j` which the `r i` identify — then there is a morphism
`m : C ⟶ C'` over `β` with `r i ≫ m = ρ i` for every `i`.

This is the descent of morphisms in Stacks 04WN, and the fullness clause of Stacks 04W8 for the
invertible modules of `C` and `C'`, through the comparisons of
`AlgebraicGeometry.Space.PicardHom.theta`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.readIso_pullbackComparison`: the reading of a
  comparison of an inverse image with an iterated one is again such a comparison.
* `AlgebraicGeometry.Space.PicardHom.readIso_theta_comp`: the reading of `Θ(r ≫ m₁, r ≫ m₂)`.
* `AlgebraicGeometry.Space.PicardHom.exists_comp_eq_of_isFpqcCovering`: morphisms of
  `Picardstack_{X/B}` glue along an fpqc covering.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuasiCoherentDescent

/-- **The reading of a comparison of an inverse image with an iterated one is again such a
comparison.**  This is the associativity coherence of Stacks 03LU. -/
theorem readIso_pullbackComparison {Z T P A : AlgebraicSpaces B S hS} (c : Z ⟶ T) (g : T ⟶ P)
    (p : P ⟶ A) (v : T ⟶ A) (hv : g ≫ p = v) (u₁ : Z ⟶ A) (u₂ : Z ⟶ P) (h₁ : c ≫ v = u₁)
    (h₂ : c ≫ g = u₂) (M : Modules.{u, u} B S hS A.1 A.2) :
    readIso c h₁ h₂ (pullbackComparison B S hS g p v hv M) =
      pullbackComparison B S hS u₂ p u₁ (by rw [← h₁, ← h₂, Category.assoc, hv]) M := by
  rw [readIso, ← Iso.trans_assoc,
    pullbackComparison_trans B S hS c g p v hv u₂ h₂ u₁ h₁ _,
    Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- Two comparisons of an inverse image with one and the same iterated inverse image differ by
the transport along the equality of the two morphisms they start from. -/
theorem pullbackComparison_trans_symm {A P T : AlgebraicSpaces B S hS} (g : T ⟶ P) (p : P ⟶ A)
    (v v' : T ⟶ A) (hv : g ≫ p = v) (hv' : g ≫ p = v') (M : Modules.{u, u} B S hS A.1 A.2) :
    pullbackComparison B S hS g p v hv M ≪≫ (pullbackComparison B S hS g p v' hv' M).symm =
      eqToIso (congrArg (fun q : T ⟶ A => (modulePullback B S hS q).obj M)
        (hv.symm.trans hv')) := by
  subst hv hv'
  rw [Iso.self_symm_id, eqToIso_refl]

end QuasiCoherentDescent

namespace PicardHom

variable {s : PicardSituation B S hS}

/-- **The reading of `Θ(r ≫ m₁, r ≫ m₂)`** along `c` is the reading of `Θ(m₁, m₂)` along
`c ≫ X_r`. -/
theorem readIso_theta_comp {P P' A₁ A₂ : PicardObject s} {Z : AlgebraicSpaces B S hS}
    (c : Z ⟶ baseChangeSpace s.f P'.T) (r : PicardHom P' P) (m₁ : PicardHom P A₁)
    (m₂ : PicardHom P A₂) {v₁ : Z ⟶ baseChangeSpace s.f A₁.T}
    {v₂ : Z ⟶ baseChangeSpace s.f A₂.T} (h₁ : c ≫ baseChangeMap s.f (r.comp m₁).base = v₁)
    (h₂ : c ≫ baseChangeMap s.f (r.comp m₂).base = v₂) :
    QuasiCoherentDescent.readIso c h₁ h₂ (theta (r.comp m₁) (r.comp m₂)) =
      QuasiCoherentDescent.readIso (c ≫ baseChangeMap s.f r.base)
        (by rw [Category.assoc, baseChangeMap_comp_base]; exact h₁)
        (by rw [Category.assoc, baseChangeMap_comp_base]; exact h₂) (theta m₁ m₂) := by
  rw [theta_comp, QuasiCoherentDescent.readIso_readIso]

/-- The reading of `Θ(r ≫ m₁, r ≫ m₂)` along the identity is the reading of `Θ(m₁, m₂)` along
`X_r`. -/
theorem readIso_id_theta_comp {P P' A₁ A₂ : PicardObject s} (r : PicardHom P' P)
    (m₁ : PicardHom P A₁) (m₂ : PicardHom P A₂) {v₁ : baseChangeSpace s.f P'.T ⟶
      baseChangeSpace s.f A₁.T} {v₂ : baseChangeSpace s.f P'.T ⟶ baseChangeSpace s.f A₂.T}
    (h₁ : 𝟙 _ ≫ baseChangeMap s.f (r.comp m₁).base = v₁)
    (h₂ : 𝟙 _ ≫ baseChangeMap s.f (r.comp m₂).base = v₂)
    (h₁' : baseChangeMap s.f r.base ≫ baseChangeMap s.f m₁.base = v₁)
    (h₂' : baseChangeMap s.f r.base ≫ baseChangeMap s.f m₂.base = v₂) :
    QuasiCoherentDescent.readIso (𝟙 _) h₁ h₂ (theta (r.comp m₁) (r.comp m₂)) =
      QuasiCoherentDescent.readIso (baseChangeMap s.f r.base) h₁' h₂' (theta m₁ m₂) := by
  rw [readIso_theta_comp]
  exact QuasiCoherentDescent.readIso_congr_left (Category.id_comp _) _ _ _ _ _

variable {C C' P : PicardObject s}

/-- The isomorphism `(X_r)^*(X_β)^*L_{C'} ≅ (X_r)^*L_C` that a morphism `ρ : P ⟶ C'` over
`r ≫ β` induces from a morphism `r : P ⟶ C`. -/
def gluingIso (β : C.T ⟶ C'.T) (r : PicardHom P C) (ρ : PicardHom P C')
    (h : baseChangeMap s.f r.base ≫ baseChangeMap s.f β = baseChangeMap s.f ρ.base) :
    (modulePullback B S hS (baseChangeMap s.f r.base)).obj
        ((modulePullback B S hS (baseChangeMap s.f β)).obj C'.lineBundle) ≅
      (modulePullback B S hS (baseChangeMap s.f r.base)).obj C.lineBundle :=
  (theta r ρ ≪≫ QuasiCoherentDescent.pullbackComparison B S hS (baseChangeMap s.f r.base)
    (baseChangeMap s.f β) (baseChangeMap s.f ρ.base) h C'.lineBundle).symm

/-- The comparison `Θ(r ≫ m, r)` of a composite with its first factor is the comparison of
Stacks 03LU followed by the inverse image of the comparison of modules of `m`. -/
theorem theta_comp_self (r : PicardHom P C) (m : PicardHom C C') :
    theta (r.comp m) r =
      QuasiCoherentDescent.pullbackComparison B S hS (baseChangeMap s.f r.base)
          (baseChangeMap s.f m.base) (baseChangeMap s.f (r.comp m).base)
          (baseChangeMap_comp_base r m) C'.lineBundle ≪≫
        (modulePullback B S hS (baseChangeMap s.f r.base)).mapIso (asIso m.fibre) := by
  rw [theta, asIso_comp_fibre, Iso.trans_assoc, Iso.trans_assoc, Iso.self_symm_id,
    Iso.trans_refl]

/-- **A morphism whose comparison of modules pulls back to the isomorphism induced by `ρ`
restricts to `ρ`.** -/
theorem comp_eq_of_mapIso_eq_gluingIso (r : PicardHom P C) (ρ : PicardHom P C')
    (m : PicardHom C C') (hb : ρ.base = r.base ≫ m.base)
    (h : baseChangeMap s.f r.base ≫ baseChangeMap s.f m.base = baseChangeMap s.f ρ.base)
    (hφ : (modulePullback B S hS (baseChangeMap s.f r.base)).mapIso (asIso m.fibre) =
      gluingIso m.base r ρ h) :
    r.comp m = ρ := by
  have hb' : (r.comp m).base = ρ.base := by rw [comp_base, hb]
  refine eq_of_theta hb' ?_
  rw [← theta_trans _ r, theta_comp_self, hφ, gluingIso, Iso.trans_symm, theta_symm,
    Iso.trans_assoc, Iso.trans_assoc, theta_trans, theta_self, Iso.trans_refl,
    QuasiCoherentDescent.pullbackComparison_trans_symm]

variable {P₁ P₂ Q : PicardObject s}

/-- **The induced isomorphisms agree on an overlap**: for `a : Q ⟶ P₁`, `a' : Q ⟶ P₂` with
`a ≫ r₁ = a' ≫ r₂` and `a ≫ ρ₁ = a' ≫ ρ₂`, the readings of the two isomorphisms induced on
`P₁` and `P₂` agree on `Q`. -/
theorem readIso_gluingIso_eq (β : C.T ⟶ C'.T) (r₁ : PicardHom P₁ C) (ρ₁ : PicardHom P₁ C')
    (r₂ : PicardHom P₂ C) (ρ₂ : PicardHom P₂ C')
    (h₁ : baseChangeMap s.f r₁.base ≫ baseChangeMap s.f β = baseChangeMap s.f ρ₁.base)
    (h₂ : baseChangeMap s.f r₂.base ≫ baseChangeMap s.f β = baseChangeMap s.f ρ₂.base)
    (a : PicardHom Q P₁) (a' : PicardHom Q P₂) (hr : a.comp r₁ = a'.comp r₂)
    (hρ : a.comp ρ₁ = a'.comp ρ₂)
    (hV₁ : baseChangeMap s.f a'.base ≫ baseChangeMap s.f r₂.base =
      baseChangeMap s.f a.base ≫ baseChangeMap s.f r₁.base) :
    QuasiCoherentDescent.readIso (baseChangeMap s.f a.base) rfl rfl (gluingIso β r₁ ρ₁ h₁) =
      QuasiCoherentDescent.readIso (baseChangeMap s.f a'.base) hV₁ hV₁ (gluingIso β r₂ ρ₂ h₂) := by
  have hV₂ : baseChangeMap s.f a'.base ≫ baseChangeMap s.f ρ₂.base =
      baseChangeMap s.f a.base ≫ baseChangeMap s.f ρ₁.base := by
    rw [baseChangeMap_comp_base, baseChangeMap_comp_base, hρ]
  have hθ : QuasiCoherentDescent.readIso (baseChangeMap s.f a.base) rfl rfl (theta r₁ ρ₁) =
      QuasiCoherentDescent.readIso (baseChangeMap s.f a'.base) hV₁ hV₂ (theta r₂ ρ₂) := by
    rw [← readIso_id_theta_comp a r₁ ρ₁ (by simp [baseChangeMap_comp_base])
        (by simp [baseChangeMap_comp_base]),
      ← readIso_id_theta_comp a' r₂ ρ₂ (by simp [← baseChangeMap_comp_base, hV₁])
        (by simp [← baseChangeMap_comp_base, hV₂])]
    exact readIso_theta_congr _ hr hρ _ _ _ _
  simp only [gluingIso]
  rw [← QuasiCoherentDescent.readIso_symm, ← QuasiCoherentDescent.readIso_symm,
    ← QuasiCoherentDescent.readIso_trans _ rfl (rfl : _ = baseChangeMap s.f a.base ≫
      baseChangeMap s.f ρ₁.base) rfl,
    ← QuasiCoherentDescent.readIso_trans _ _ hV₂ _, hθ,
    QuasiCoherentDescent.readIso_pullbackComparison,
    QuasiCoherentDescent.readIso_pullbackComparison]

variable {I : Type v} {P : I → PicardObject s}

/-- **Morphisms of `Picardstack_{X/B}` glue along an fpqc covering.**  Let `β : C.T ⟶ C'.T`, let
`r i : P i ⟶ C` be morphisms whose base changes form an fpqc covering of `X_C`, and let
`ρ i : P i ⟶ C'` lie over `r i ≫ β`.  If on cartesian overlaps `Q i j` of the base changes the
composites with the `ρ i` agree as the composites with the `r i` do, then a morphism `C ⟶ C'`
over `β` restricts to every `ρ i`. -/
theorem exists_comp_eq_of_isFpqcCovering (β : C.T ⟶ C'.T)
    (r : ∀ i, PicardHom (P i) C) (ρ : ∀ i, PicardHom (P i) C')
    (hρ : ∀ i, (ρ i).base = (r i).base ≫ β)
    (hcov : IsFpqcCovering B S hS fun i => (baseChangeMap s.f (r i).base).hom)
    (Q : I → I → PicardObject s) (a : ∀ i j, PicardHom (Q i j) (P i))
    (a' : ∀ i j, PicardHom (Q i j) (P j)) (hr : ∀ i j, (a i j).comp (r i) = (a' i j).comp (r j))
    (hρQ : ∀ i j, (a i j).comp (ρ i) = (a' i j).comp (ρ j))
    (hQ : ∀ i j, IsPullback (baseChangeMap s.f (a i j).base) (baseChangeMap s.f (a' i j).base)
      (baseChangeMap s.f (r i).base) (baseChangeMap s.f (r j).base)) :
    ∃ m : PicardHom C C', m.base = β ∧ ∀ i, (r i).comp m = ρ i := by
  have hM : ((modulePullback B S hS (baseChangeMap s.f β)).obj
      C'.lineBundle).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (isQuasicoherentOnSite_of_isInvertibleModule _ _ C'.invertible)
  have hN : C.lineBundle.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertibleModule _ _ C.invertible
  have hρ' : ∀ i, baseChangeMap s.f (r i).base ≫ baseChangeMap s.f β =
      baseChangeMap s.f (ρ i).base := fun i => by rw [hρ i, baseChangeMap_comp]
  obtain ⟨φ, hφ⟩ := QuasiCoherentDescent.exists_iso_of_readIso_eq
    (fun i => baseChangeMap s.f (r i).base) hcov hM hN (fun i => gluingIso β (r i) (ρ i) (hρ' i))
    (fun i j => baseChangeSpace s.f (Q i j).T) (fun i j => baseChangeMap s.f (a i j).base)
    (fun i j => baseChangeMap s.f (a' i j).base) hQ
    (fun i j => readIso_gluingIso_eq β (r i) (ρ i) (r j) (ρ j) (hρ' i) (hρ' j) (a i j) (a' i j)
      (hr i j) (hρQ i j) (hQ i j).w.symm)
  refine ⟨⟨β, φ.hom, inferInstance⟩, rfl, fun i =>
    comp_eq_of_mapIso_eq_gluingIso (r i) (ρ i) ⟨β, φ.hom, inferInstance⟩ (hρ i) (hρ' i) ?_⟩
  exact (congrArg (fun e => (modulePullback B S hS (baseChangeMap s.f (r i).base)).mapIso e)
      (by ext; rfl : asIso φ.hom = φ)).trans (hφ i)

end PicardHom

end AlgebraicGeometry.Space

end
