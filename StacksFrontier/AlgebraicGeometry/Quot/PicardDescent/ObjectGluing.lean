module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.HomGluing
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.InvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcDescentTransitivity

/-!
# Gluing objects of `Picardstack_{X/B}` along an fpqc covering

Let `T₀` be a test scheme over the base and let `g i : (A i).T ⟶ T₀` be morphisms of test schemes
whose base changes `X_{A i} ⟶ X_{T₀}` form an fpqc covering, the `A i` being objects of
`Picardstack_{X/B}`.  Suppose given, on cartesian overlaps, objects `Q i j` with morphisms
`π i j : Q i j ⟶ A i` and `ξ i j : Q i j ⟶ A j` over the two projections, and on cartesian
triple overlaps the compatibilities that make the comparisons `Θ(π i j, ξ i j)` satisfy the
cocycle condition.  Then the invertible modules of the `A i` glue: there is an invertible module
`L` on `X_{T₀}` and morphisms `κ i : A i ⟶ (T₀, L)` over `g i` with `π i j ≫ κ i = ξ i j ≫ κ j`.

This is the source's proof of Stacks 04WN: the comparisons `Θ(π i j, ξ i j)`, read on the chosen
fibre products, form a descent datum of Stacks 04W3 for the invertible modules of the `A i`
relative to the fpqc covering `{X_{A i} ⟶ X_{T₀}}`; it is effective by Stacks 04W8, and the
module it descends to is invertible because its inverse images are
(`AlgebraicGeometry.Space.isInvertibleModule_of_pullback_isFpqcCovering`).

## Main definitions

* `AlgebraicGeometry.Space.PicardHom.pairTransition`: the pairwise isomorphism of the descent
  datum.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.readIso_mapIso`: the reading of the inverse
  image of an isomorphism.
* `AlgebraicGeometry.Space.PicardHom.exists_picardObject_of_isFpqcCovering`: **the gluing.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuasiCoherentDescent

/-- **The reading of the inverse image of an isomorphism is the inverse image along the
composite.** -/
theorem readIso_mapIso {Z W Y : AlgebraicSpaces B S hS} (c : Z ⟶ W) (a : W ⟶ Y) (v : Z ⟶ Y)
    (h : c ≫ a = v) {M N : Modules.{u, u} B S hS Y.1 Y.2} (φ : M ≅ N) :
    readIso c h h ((modulePullback B S hS a).mapIso φ) = (modulePullback B S hS v).mapIso φ := by
  apply Iso.ext
  simp only [readIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← pullbackComparison_naturality B S hS c a v h φ.hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end QuasiCoherentDescent

namespace PicardHom

variable {s : PicardSituation B S hS}

/-- The reading of `Θ(m₁, m₂)` along `c ≫ X_ρ` is the reading along `c` of the comparison of the
composites with `ρ`. -/
theorem readIso_comp_theta {Z : AlgebraicSpaces B S hS} {R Q A₁ A₂ : PicardObject s}
    (c : Z ⟶ baseChangeSpace s.f R.T) (ρ : PicardHom R Q) (m₁ : PicardHom Q A₁)
    (m₂ : PicardHom Q A₂) (σ₁ : PicardHom R A₁) (σ₂ : PicardHom R A₂)
    (e₁ : ρ.comp m₁ = σ₁) (e₂ : ρ.comp m₂ = σ₂) {v₁ : Z ⟶ baseChangeSpace s.f A₁.T}
    {v₂ : Z ⟶ baseChangeSpace s.f A₂.T}
    (h₁ : (c ≫ baseChangeMap s.f ρ.base) ≫ baseChangeMap s.f m₁.base = v₁)
    (h₂ : (c ≫ baseChangeMap s.f ρ.base) ≫ baseChangeMap s.f m₂.base = v₂)
    (h₁' : c ≫ baseChangeMap s.f σ₁.base = v₁) (h₂' : c ≫ baseChangeMap s.f σ₂.base = v₂) :
    QuasiCoherentDescent.readIso (c ≫ baseChangeMap s.f ρ.base) h₁ h₂ (theta m₁ m₂) =
      QuasiCoherentDescent.readIso c h₁' h₂' (theta σ₁ σ₂) := by
  rw [← readIso_theta_comp c ρ m₁ m₂ (by rwa [← baseChangeMap_comp_base, ← Category.assoc])
    (by rwa [← baseChangeMap_comp_base, ← Category.assoc])]
  exact readIso_theta_congr c e₁ e₂ _ _ _ _

variable {I : Type v} {T₀ : s.SchemesOver} {A : I → PicardObject s}

/-- The comparison of the chosen fibre product of two base changes with a cartesian overlap. -/
def pairIso (g : ∀ i, (A i).T ⟶ T₀) {Q : PicardObject s} (i j : I) (π : PicardHom Q (A i))
    (ξ : PicardHom Q (A j))
    (hQ : IsPullback (baseChangeMap s.f π.base) (baseChangeMap s.f ξ.base)
      (baseChangeMap s.f (g i)) (baseChangeMap s.f (g j))) :
    QuasiCoherentDescent.pair B S hS (fun i => baseChangeSpace s.f (A i).T)
        (fun i => baseChangeMap s.f (g i)) i j ≅ baseChangeSpace s.f Q.T :=
  IsPullback.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS _ _) hQ

/-- The composite of `pairIso` with the base change of `π` is the first projection of the chosen
fibre product of the base changes of `g i` and `g j`. -/
theorem pairIso_hom_fst (g : ∀ i, (A i).T ⟶ T₀) {Q : PicardObject s} (i j : I)
    (π : PicardHom Q (A i)) (ξ : PicardHom Q (A j))
    (hQ : IsPullback (baseChangeMap s.f π.base) (baseChangeMap s.f ξ.base)
      (baseChangeMap s.f (g i)) (baseChangeMap s.f (g j))) :
    (pairIso g i j π ξ hQ).hom ≫ baseChangeMap s.f π.base =
      QuasiCoherentDescent.pairFst B S hS (fun i => baseChangeSpace s.f (A i).T)
        (fun i => baseChangeMap s.f (g i)) i j :=
  IsPullback.isoIsPullback_hom_fst _ _ _ hQ

/-- The composite of `pairIso` with the base change of `ξ` is the second projection of the chosen
fibre product of the base changes of `g i` and `g j`. -/
theorem pairIso_hom_snd (g : ∀ i, (A i).T ⟶ T₀) {Q : PicardObject s} (i j : I)
    (π : PicardHom Q (A i)) (ξ : PicardHom Q (A j))
    (hQ : IsPullback (baseChangeMap s.f π.base) (baseChangeMap s.f ξ.base)
      (baseChangeMap s.f (g i)) (baseChangeMap s.f (g j))) :
    (pairIso g i j π ξ hQ).hom ≫ baseChangeMap s.f ξ.base =
      QuasiCoherentDescent.pairSnd B S hS (fun i => baseChangeSpace s.f (A i).T)
        (fun i => baseChangeMap s.f (g i)) i j :=
  IsPullback.isoIsPullback_hom_snd _ _ _ hQ

/-- **The pairwise isomorphism of the descent datum**: the comparison `Θ(π, ξ)` of a cartesian
overlap, read on the chosen fibre product. -/
def pairTransition (g : ∀ i, (A i).T ⟶ T₀) {Q : PicardObject s} (i j : I) (π : PicardHom Q (A i))
    (ξ : PicardHom Q (A j))
    (hQ : IsPullback (baseChangeMap s.f π.base) (baseChangeMap s.f ξ.base)
      (baseChangeMap s.f (g i)) (baseChangeMap s.f (g j))) :
    (modulePullback B S hS (QuasiCoherentDescent.pairFst B S hS
        (fun i => baseChangeSpace s.f (A i).T) (fun i => baseChangeMap s.f (g i)) i j)).obj
        (A i).lineBundle ≅
      (modulePullback B S hS (QuasiCoherentDescent.pairSnd B S hS
        (fun i => baseChangeSpace s.f (A i).T) (fun i => baseChangeMap s.f (g i)) i j)).obj
        (A j).lineBundle :=
  QuasiCoherentDescent.readIso (pairIso g i j π ξ hQ).hom (pairIso_hom_fst g i j π ξ hQ)
    (pairIso_hom_snd g i j π ξ hQ) (theta π ξ)

/-- **The cocycle condition for the comparisons of three cartesian overlaps, read on a test
space.**  The overlaps `Q₁₂`, `Q₂₃`, `Q₁₃` are read through spaces `P₁₂`, `P₂₃`, `P₁₃` mapping to
their base changes, and the triple overlap is given by an object `R` with morphisms `σ₁`, `σ₂`,
`σ₃` to the three members and `ρ₁₂`, `ρ₂₃`, `ρ₁₃` to the three overlaps compatible with them, the
first two forming a cartesian square of base changes. -/
theorem readIso_theta_cocycle {A₁ A₂ A₃ Q₁₂ Q₂₃ Q₁₃ R : PicardObject s}
    (π₁₂ : PicardHom Q₁₂ A₁) (ξ₁₂ : PicardHom Q₁₂ A₂) (π₂₃ : PicardHom Q₂₃ A₂)
    (ξ₂₃ : PicardHom Q₂₃ A₃) (π₁₃ : PicardHom Q₁₃ A₁) (ξ₁₃ : PicardHom Q₁₃ A₃)
    (σ₁ : PicardHom R A₁) (σ₂ : PicardHom R A₂) (σ₃ : PicardHom R A₃)
    (ρ₁₂ : PicardHom R Q₁₂) (ρ₂₃ : PicardHom R Q₂₃) (ρ₁₃ : PicardHom R Q₁₃)
    (h12a : ρ₁₂.comp π₁₂ = σ₁) (h12b : ρ₁₂.comp ξ₁₂ = σ₂) (h23a : ρ₂₃.comp π₂₃ = σ₂)
    (h23b : ρ₂₃.comp ξ₂₃ = σ₃) (h13a : ρ₁₃.comp π₁₃ = σ₁) (h13b : ρ₁₃.comp ξ₁₃ = σ₃)
    (hR : IsPullback (baseChangeMap s.f ρ₁₂.base) (baseChangeMap s.f ρ₂₃.base)
      (baseChangeMap s.f ξ₁₂.base) (baseChangeMap s.f π₂₃.base))
    (h13 : ∀ {Z : AlgebraicSpaces B S hS} (x y : Z ⟶ baseChangeSpace s.f Q₁₃.T),
      x ≫ baseChangeMap s.f π₁₃.base = y ≫ baseChangeMap s.f π₁₃.base →
      x ≫ baseChangeMap s.f ξ₁₃.base = y ≫ baseChangeMap s.f ξ₁₃.base → x = y)
    {P₁₂ P₂₃ P₁₃ T : AlgebraicSpaces B S hS}
    (d₁₂ : P₁₂ ⟶ baseChangeSpace s.f Q₁₂.T) (d₂₃ : P₂₃ ⟶ baseChangeSpace s.f Q₂₃.T)
    (d₁₃ : P₁₃ ⟶ baseChangeSpace s.f Q₁₃.T)
    {p₁₂ : P₁₂ ⟶ baseChangeSpace s.f A₁.T} {p₂₁ : P₁₂ ⟶ baseChangeSpace s.f A₂.T}
    {p₂₃ : P₂₃ ⟶ baseChangeSpace s.f A₂.T} {p₃₂ : P₂₃ ⟶ baseChangeSpace s.f A₃.T}
    {p₁₃ : P₁₃ ⟶ baseChangeSpace s.f A₁.T} {p₃₁ : P₁₃ ⟶ baseChangeSpace s.f A₃.T}
    (hd₁₂ : d₁₂ ≫ baseChangeMap s.f π₁₂.base = p₁₂) (hd₂₁ : d₁₂ ≫ baseChangeMap s.f ξ₁₂.base = p₂₁)
    (hd₂₃ : d₂₃ ≫ baseChangeMap s.f π₂₃.base = p₂₃) (hd₃₂ : d₂₃ ≫ baseChangeMap s.f ξ₂₃.base = p₃₂)
    (hd₁₃ : d₁₃ ≫ baseChangeMap s.f π₁₃.base = p₁₃) (hd₃₁ : d₁₃ ≫ baseChangeMap s.f ξ₁₃.base = p₃₁)
    (v₁₂ : T ⟶ P₁₂) (v₂₃ : T ⟶ P₂₃) (v₁₃ : T ⟶ P₁₃) {v₁ : T ⟶ baseChangeSpace s.f A₁.T}
    {v₂ : T ⟶ baseChangeSpace s.f A₂.T} {v₃ : T ⟶ baseChangeSpace s.f A₃.T}
    (e₁₂ : v₁₂ ≫ p₁₂ = v₁) (e₂₁ : v₁₂ ≫ p₂₁ = v₂) (e₂₃ : v₂₃ ≫ p₂₃ = v₂)
    (e₃₂ : v₂₃ ≫ p₃₂ = v₃) (e₁₃ : v₁₃ ≫ p₁₃ = v₁) (e₃₁ : v₁₃ ≫ p₃₁ = v₃) :
    QuasiCoherentDescent.readIso v₁₂ e₁₂ e₂₁ (QuasiCoherentDescent.readIso d₁₂ hd₁₂ hd₂₁
        (theta π₁₂ ξ₁₂)) ≪≫
      QuasiCoherentDescent.readIso v₂₃ e₂₃ e₃₂ (QuasiCoherentDescent.readIso d₂₃ hd₂₃ hd₃₂
        (theta π₂₃ ξ₂₃)) =
    QuasiCoherentDescent.readIso v₁₃ e₁₃ e₃₁ (QuasiCoherentDescent.readIso d₁₃ hd₁₃ hd₃₁
        (theta π₁₃ ξ₁₃)) := by
  subst hd₁₂ hd₂₁ hd₂₃ hd₃₂ hd₁₃ hd₃₁
  have hcond : (v₁₂ ≫ d₁₂) ≫ baseChangeMap s.f ξ₁₂.base =
      (v₂₃ ≫ d₂₃) ≫ baseChangeMap s.f π₂₃.base := by
    rw [Category.assoc, Category.assoc, e₂₁, e₂₃]
  let τ := hR.lift (v₁₂ ≫ d₁₂) (v₂₃ ≫ d₂₃) hcond
  have hτ12 : τ ≫ baseChangeMap s.f ρ₁₂.base = v₁₂ ≫ d₁₂ := hR.lift_fst _ _ _
  have hτ23 : τ ≫ baseChangeMap s.f ρ₂₃.base = v₂₃ ≫ d₂₃ := hR.lift_snd _ _ _
  have hσ : ∀ {Q' A' : PicardObject s} (ρ : PicardHom R Q') (m : PicardHom Q' A')
      (σ : PicardHom R A'), ρ.comp m = σ →
      baseChangeMap s.f ρ.base ≫ baseChangeMap s.f m.base = baseChangeMap s.f σ.base :=
    fun ρ m σ e => by rw [baseChangeMap_comp_base, e]
  have hτ1 : τ ≫ baseChangeMap s.f σ₁.base = v₁ := by
    rw [← hσ _ _ _ h12a, ← Category.assoc, hτ12, Category.assoc, e₁₂]
  have hτ2 : τ ≫ baseChangeMap s.f σ₂.base = v₂ := by
    rw [← hσ _ _ _ h12b, ← Category.assoc, hτ12, Category.assoc, e₂₁]
  have hτ3 : τ ≫ baseChangeMap s.f σ₃.base = v₃ := by
    rw [← hσ _ _ _ h23b, ← Category.assoc, hτ23, Category.assoc, e₃₂]
  have hτ13 : τ ≫ baseChangeMap s.f ρ₁₃.base = v₁₃ ≫ d₁₃ := by
    refine h13 _ _ ?_ ?_
    · rw [Category.assoc, hσ _ _ _ h13a, hτ1, Category.assoc, e₁₃]
    · rw [Category.assoc, hσ _ _ _ h13b, hτ3, Category.assoc, e₃₁]
  rw [QuasiCoherentDescent.readIso_readIso, QuasiCoherentDescent.readIso_readIso,
    QuasiCoherentDescent.readIso_readIso,
    QuasiCoherentDescent.readIso_congr_left hτ12.symm _ _
      (by rw [hτ12, Category.assoc, e₁₂]) (by rw [hτ12, Category.assoc, e₂₁]),
    QuasiCoherentDescent.readIso_congr_left hτ23.symm _ _
      (by rw [hτ23, Category.assoc, e₂₃]) (by rw [hτ23, Category.assoc, e₃₂]),
    QuasiCoherentDescent.readIso_congr_left hτ13.symm _ _
      (by rw [hτ13, Category.assoc, e₁₃]) (by rw [hτ13, Category.assoc, e₃₁]),
    readIso_comp_theta τ ρ₁₂ π₁₂ ξ₁₂ σ₁ σ₂ h12a h12b _ _ hτ1 hτ2,
    readIso_comp_theta τ ρ₂₃ π₂₃ ξ₂₃ σ₂ σ₃ h23a h23b _ _ hτ2 hτ3,
    readIso_comp_theta τ ρ₁₃ π₁₃ ξ₁₃ σ₁ σ₃ h13a h13b _ _ hτ1 hτ3,
    QuasiCoherentDescent.readIso_trans, theta_trans]

/-- **Two morphisms into a glued object agree on a cartesian overlap** as soon as the
identifications of the modules of the members with the inverse images of the glued module are
compatible with the comparison of the overlap, read on a space `P` isomorphic to its base change.
-/
theorem comp_eq_comp_of_readIso {A₁ A₂ Q : PicardObject s} (g₁ : A₁.T ⟶ T₀) (g₂ : A₂.T ⟶ T₀)
    (π : PicardHom Q A₁) (ξ : PicardHom Q A₂) (hπξ : π.base ≫ g₁ = ξ.base ≫ g₂)
    (M : Modules.{u, u} B S hS (baseChangeSpace s.f T₀).1 (baseChangeSpace s.f T₀).2)
    (hM : IsInvertibleModule (baseChangeSpace s.f T₀) M)
    (ε₁ : A₁.lineBundle ≅ (modulePullback B S hS (baseChangeMap s.f g₁)).obj M)
    (ε₂ : A₂.lineBundle ≅ (modulePullback B S hS (baseChangeMap s.f g₂)).obj M)
    {P : AlgebraicSpaces B S hS} (p₁ : P ⟶ baseChangeSpace s.f A₁.T)
    (p₂ : P ⟶ baseChangeSpace s.f A₂.T) (d : P ⟶ baseChangeSpace s.f Q.T) [IsIso d]
    (hd₁ : d ≫ baseChangeMap s.f π.base = p₁) (hd₂ : d ≫ baseChangeMap s.f ξ.base = p₂)
    (w : p₁ ≫ baseChangeMap s.f g₁ = p₂ ≫ baseChangeMap s.f g₂)
    (hnat : (modulePullback B S hS p₁).mapIso ε₁ ≪≫
        QuasiCoherentDescent.canonicalComparison p₁ p₂ (baseChangeMap s.f g₁)
          (baseChangeMap s.f g₂) w M =
      QuasiCoherentDescent.readIso d hd₁ hd₂ (theta π ξ) ≪≫
        (modulePullback B S hS p₂).mapIso ε₂) :
    π.comp (⟨g₁, ε₁.inv, inferInstance⟩ : PicardHom A₁ ⟨T₀, M, hM⟩) =
      ξ.comp (⟨g₂, ε₂.inv, inferInstance⟩ : PicardHom A₂ ⟨T₀, M, hM⟩) := by
  subst hd₁ hd₂
  set κ₁ : PicardHom A₁ ⟨T₀, M, hM⟩ := ⟨g₁, ε₁.inv, inferInstance⟩
  set κ₂ : PicardHom A₂ ⟨T₀, M, hM⟩ := ⟨g₂, ε₂.inv, inferInstance⟩
  have hw' : baseChangeMap s.f π.base ≫ baseChangeMap s.f g₁ =
      baseChangeMap s.f ξ.base ≫ baseChangeMap s.f g₂ := by
    rw [← baseChangeMap_comp, ← baseChangeMap_comp, hπξ]
  have e₁ : asIso κ₁.fibre = ε₁.symm := Iso.ext rfl
  have e₂ : asIso κ₂.fibre = ε₂.symm := Iso.ext rfl
  have hnat' : QuasiCoherentDescent.canonicalComparison (d ≫ baseChangeMap s.f π.base)
        (d ≫ baseChangeMap s.f ξ.base) (baseChangeMap s.f g₁) (baseChangeMap s.f g₂) w M =
      ((modulePullback B S hS (d ≫ baseChangeMap s.f π.base)).mapIso ε₁).symm ≪≫
        QuasiCoherentDescent.readIso d rfl rfl (theta π ξ) ≪≫
          (modulePullback B S hS (d ≫ baseChangeMap s.f ξ.base)).mapIso ε₂ := by
    rw [← hnat, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
  have hv₁ : baseChangeMap s.f π.base ≫ baseChangeMap s.f g₁ =
      baseChangeMap s.f (π.comp κ₁).base := baseChangeMap_comp_base π κ₁
  have hv₂ : baseChangeMap s.f ξ.base ≫ baseChangeMap s.f g₂ =
      baseChangeMap s.f (ξ.comp κ₂).base := baseChangeMap_comp_base ξ κ₂
  have hv : baseChangeMap s.f ξ.base ≫ baseChangeMap s.f g₂ =
      baseChangeMap s.f (π.comp κ₁).base := by
    rw [← hw', hv₁]
  refine eq_of_theta (by rwa [comp_base, comp_base]) ?_
  have h₁ : theta (π.comp κ₁) π =
      QuasiCoherentDescent.pullbackComparison B S hS (baseChangeMap s.f π.base)
          (baseChangeMap s.f g₁) (baseChangeMap s.f (π.comp κ₁).base) hv₁ M ≪≫
        (modulePullback B S hS (baseChangeMap s.f π.base)).mapIso ε₁.symm := by
    rw [theta_comp_self, e₁]
  have h₂ : theta ξ (ξ.comp κ₂) =
      ((modulePullback B S hS (baseChangeMap s.f ξ.base)).mapIso ε₂.symm).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS (baseChangeMap s.f ξ.base)
          (baseChangeMap s.f g₂) (baseChangeMap s.f (ξ.comp κ₂).base) hv₂ M).symm := by
    rw [← theta_symm, theta_comp_self, e₂, Iso.trans_symm]
  rw [← theta_trans _ π, ← theta_trans π ξ, h₁, h₂]
  have hK' : (modulePullback B S hS (baseChangeMap s.f π.base)).mapIso ε₁.symm ≪≫
        theta π ξ ≪≫ ((modulePullback B S hS (baseChangeMap s.f ξ.base)).mapIso ε₂.symm).symm =
      (QuasiCoherentDescent.pullbackComparison B S hS (baseChangeMap s.f π.base)
          (baseChangeMap s.f g₁) (baseChangeMap s.f (π.comp κ₁).base) hv₁ M).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS (baseChangeMap s.f ξ.base)
          (baseChangeMap s.f g₂) (baseChangeMap s.f (π.comp κ₁).base) hv M := by
    rw [← QuasiCoherentDescent.canonicalComparison_eq_pullbackComparison B S hS _ _ _ _ hw' _
      hv₁ hv]
    refine QuasiCoherentDescent.eq_of_readIso_eq (modulePushforwardCoherence B S hS) d rfl rfl ?_
    rw [QuasiCoherentDescent.readIso_canonicalComparison, hnat',
      ← QuasiCoherentDescent.readIso_trans d rfl rfl rfl,
      ← QuasiCoherentDescent.readIso_trans d rfl rfl rfl, ← QuasiCoherentDescent.readIso_symm,
      QuasiCoherentDescent.readIso_mapIso, QuasiCoherentDescent.readIso_mapIso,
      Functor.mapIso_symm, Functor.mapIso_symm, Iso.symm_symm_eq]
  have hK'' := congrArg (· ≪≫ (QuasiCoherentDescent.pullbackComparison B S hS
    (baseChangeMap s.f ξ.base) (baseChangeMap s.f g₂) (baseChangeMap s.f (ξ.comp κ₂).base)
    hv₂ M).symm) hK'
  simp only [Iso.trans_assoc] at hK'' ⊢
  rw [hK'', Iso.self_symm_id_assoc, QuasiCoherentDescent.pullbackComparison_trans_symm]

variable (g : ∀ i, (A i).T ⟶ T₀) (Q : I → I → PicardObject s)
  (π : ∀ i j, PicardHom (Q i j) (A i)) (ξ : ∀ i j, PicardHom (Q i j) (A j))
  (hQ : ∀ i j, IsPullback (baseChangeMap s.f (π i j).base) (baseChangeMap s.f (ξ i j).base)
    (baseChangeMap s.f (g i)) (baseChangeMap s.f (g j)))
  (R : I → I → I → PicardObject s) (σ₁ : ∀ i j k, PicardHom (R i j k) (A i))
  (σ₂ : ∀ i j k, PicardHom (R i j k) (A j)) (σ₃ : ∀ i j k, PicardHom (R i j k) (A k))
  (ρ₁₂ : ∀ i j k, PicardHom (R i j k) (Q i j)) (ρ₂₃ : ∀ i j k, PicardHom (R i j k) (Q j k))
  (ρ₁₃ : ∀ i j k, PicardHom (R i j k) (Q i k))
  (h12a : ∀ i j k, (ρ₁₂ i j k).comp (π i j) = σ₁ i j k)
  (h12b : ∀ i j k, (ρ₁₂ i j k).comp (ξ i j) = σ₂ i j k)
  (h23a : ∀ i j k, (ρ₂₃ i j k).comp (π j k) = σ₂ i j k)
  (h23b : ∀ i j k, (ρ₂₃ i j k).comp (ξ j k) = σ₃ i j k)
  (h13a : ∀ i j k, (ρ₁₃ i j k).comp (π i k) = σ₁ i j k)
  (h13b : ∀ i j k, (ρ₁₃ i j k).comp (ξ i k) = σ₃ i j k)
  (hR : ∀ i j k, IsPullback (baseChangeMap s.f (ρ₁₂ i j k).base)
    (baseChangeMap s.f (ρ₂₃ i j k).base) (baseChangeMap s.f (ξ i j).base)
    (baseChangeMap s.f (π j k).base))

/-- **The descent datum of Stacks 04W3** formed by the invertible modules of the `A i` and the
comparisons of the cartesian overlaps, relative to the base changes of the `g i`. -/
def descentDatumOfOverlaps :
    QuasiCoherentDescent.DescentDatum B S hS (fun i => baseChangeSpace s.f (A i).T)
      (fun i => baseChangeMap s.f (g i)) where
  F i := (A i).lineBundle
  quasicoherent i := isQuasicoherentOnSite_of_isInvertibleModule _ _ (A i).invertible
  transition i j := pairTransition g i j (π i j) (ξ i j) (hQ i j)
  cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ :=
    readIso_theta_cocycle (π i j) (ξ i j) (π j k) (ξ j k) (π i k) (ξ i k) (σ₁ i j k)
      (σ₂ i j k) (σ₃ i j k) (ρ₁₂ i j k) (ρ₂₃ i j k) (ρ₁₃ i j k) (h12a i j k) (h12b i j k)
      (h23a i j k) (h23b i j k) (h13a i j k) (h13b i j k) (hR i j k)
      (fun x y h₁ h₂ => (hQ i k).hom_ext h₁ h₂) _ _ _
      (pairIso_hom_fst g i j _ _ (hQ i j)) (pairIso_hom_snd g i j _ _ (hQ i j))
      (pairIso_hom_fst g j k _ _ (hQ j k)) (pairIso_hom_snd g j k _ _ (hQ j k))
      (pairIso_hom_fst g i k _ _ (hQ i k)) (pairIso_hom_snd g i k _ _ (hQ i k))
      vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁

/-- The transition isomorphism of `descentDatumOfOverlaps` on the pair `(i, j)` is the
`pairTransition` of the overlap `π i j, ξ i j`. -/
theorem descentDatumOfOverlaps_transition (i j : I) :
    (descentDatumOfOverlaps g Q π ξ hQ R σ₁ σ₂ σ₃ ρ₁₂ ρ₂₃ ρ₁₃ h12a h12b h23a h23b h13a h13b
      hR).transition i j = pairTransition g i j (π i j) (ξ i j) (hQ i j) :=
  rfl

/-- The module of `descentDatumOfOverlaps` on the `i`-th piece is the invertible module of
`A i`. -/
theorem descentDatumOfOverlaps_F (i : I) :
    (descentDatumOfOverlaps g Q π ξ hQ R σ₁ σ₂ σ₃ ρ₁₂ ρ₂₃ ρ₁₃ h12a h12b h23a h23b h13a h13b
      hR).F i = (A i).lineBundle :=
  rfl

include hQ σ₁ σ₂ σ₃ ρ₁₂ ρ₂₃ ρ₁₃ h12a h12b h23a h23b h13a h13b hR in
/-- **Objects of `Picardstack_{X/B}` glue along an fpqc covering.**  Given morphisms
`g i : (A i).T ⟶ T₀` whose base changes form an fpqc covering of `X_{T₀}`, cartesian overlaps
`π i j, ξ i j` of the `A i` and cartesian triple overlaps compatible with them, there is an
invertible module `L` on `X_{T₀}` and morphisms `κ i : A i ⟶ (T₀, L)` over `g i` with
`π i j ≫ κ i = ξ i j ≫ κ j`. -/
theorem exists_picardObject_of_isFpqcCovering
    (hcov : IsFpqcCovering B S hS fun i => (baseChangeMap s.f (g i)).hom)
    (hπξ : ∀ i j, (π i j).base ≫ g i = (ξ i j).base ≫ g j) :
    ∃ (L : Modules.{u, u} B S hS (baseChangeSpace s.f T₀).1 (baseChangeSpace s.f T₀).2)
      (hL : IsInvertibleModule (baseChangeSpace s.f T₀) L)
      (κ : ∀ i, PicardHom (A i) ⟨T₀, L, hL⟩),
      (∀ i, (κ i).base = g i) ∧ ∀ i j, (π i j).comp (κ i) = (ξ i j).comp (κ j) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := QuasiCoherentDescent.forall_isEffective_of_isFpqcCovering B S hS _ _ hcov
    (descentDatumOfOverlaps g Q π ξ hQ R σ₁ σ₂ σ₃ ρ₁₂ ρ₂₃ ρ₁₃ h12a h12b h23a h23b h13a h13b hR)
  let ε : ∀ i, (A i).lineBundle ≅ (modulePullback B S hS (baseChangeMap s.f (g i))).obj M :=
    fun i => QuasiCoherentDescent.DescentDatum.appIso B S hS e i
  have hL : IsInvertibleModule (baseChangeSpace s.f T₀) M :=
    isInvertibleModule_of_pullback_isFpqcCovering B S hS (fun i => baseChangeMap s.f (g i)) hcov
      M hM fun i => isInvertibleModule_of_iso (ε i) (A i).invertible
  refine ⟨M, hL, fun i => ⟨g i, (ε i).inv, inferInstance⟩, fun i => rfl, fun i j => ?_⟩
  have h0 := QuasiCoherentDescent.appIso_naturality B S hS e i j
  rw [descentDatumOfOverlaps_transition, pairTransition,
    QuasiCoherentDescent.canonicalDescentDatum_transition] at h0
  exact comp_eq_comp_of_readIso (g i) (g j) (π i j) (ξ i j) (hπξ i j) M hL (ε i) (ε j)
    _ _ (pairIso g i j (π i j) (ξ i j) (hQ i j)).hom (pairIso_hom_fst g i j _ _ (hQ i j))
    (pairIso_hom_snd g i j _ _ (hQ i j))
    (QuasiCoherentDescent.pair_condition B S hS _ _ i j) h0

end PicardHom

end AlgebraicGeometry.Space

end
