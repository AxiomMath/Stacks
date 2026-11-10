module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCoverLocalChain07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionGood07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechPackage07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StandardCoverAcyclicity

/-!
# The per-open data of the local step of [Stacks, Tag 07Q9]

Fix a global crystalline situation `(p, (S, I, γ), X)`, affine opens `V ⊆ S` and `W ⊆ X` with `W`
mapping into `V`, and a morphism `f : X' ⟶ X` with `f⁻¹(W)` affine.  The local step of the proof
of [Stacks, Tag 07Q9] compares the Čech system `openSystem07Q9` of `W` with the one of `f⁻¹(W)`,
for a quasi-coherent crystal `F`.  This file supplies the three inputs that are specific to the
open and to the coefficients:

* the conclusion of [Stacks, Tag 07JJ] for the abelian sheaf underlying `F`;
* the surjectivity of the transition maps of `F` along the towers of the Čech system of `W`, which
  are closed immersions between thickenings of `W`, transported from the restricted situation
  `Cris(W/S|_V)` where they are thickenings of the whole space;
* over an open where `f` has the chain normal form `Γ(f⁻¹(W)) ≅ R_n` of a chain
  `Γ(X, W) = R_0 ⟶ R_1 ⟶ ⋯ ⟶ R_n` of `α_p`-extensions `R_{i+1} = R_i[z_{i+1}]/(z_{i+1}^p - c_i)`,
  the surjective polynomial presentation of `Γ(f⁻¹(W))` on the variables `c ∈ Γ(W)` (sent to
  `f^♯ c`) and `z_1, …, z_n`, together with the morphism of presentations from the canonical
  presentation of `Γ(W)`, which renames the variables `c`.

## Main definitions

* `AlgebraicGeometry.AlphaPChain.roots` — the roots `z_1, …, z_n` of a chain, in its last ring.
* `chainPresentation07Q9` — the presentation `Γ(V)[c ∈ Γ(W), z_1, …, z_n] → Γ(f⁻¹(W))`.
* `chainPresentationRename07Q9` — the morphism of presentations `Γ(V)[c] → Γ(V)[c, z]`.
* `chainCechSystemHom07Q9` — the resulting morphism of Čech systems over `f`.

## Main results

* `AlgebraicGeometry.AlphaPChain.surjective_eval₂Hom_roots` — the last ring of a chain is
  generated over the first by the roots.
* `abelianSheaf_vanishing07JJ` — [Stacks, Tag 07JJ] for a quasi-coherent sheaf of modules.
* `hasSurjectiveLevelTransitions_openSystem07Q9` — the level transitions of a quasi-coherent
  crystal along the Čech system of `W` are surjective.
* `surjective_chainPresentation07Q9`, `chainPresentationRename07Q9_C`,
  `chainPresentation07Q9_comp_rename` — the presentation is surjective and the renaming is a
  morphism of presentations over `f^♯`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.AlphaPChain

variable {p : ℕ}

/-- **The roots of a chain**: the `i`-th root is the class `z_{i+1}` of the variable in the
`(i + 1)`-st stage `R_i[z]/(z ^ p - c_i)`, pushed to the last ring of the chain. -/
def roots : {C : CommRingCat.{u}} → {n : ℕ} → (ch : AlphaPChain p C n) → (Fin n → ch.top)
  | _, _, .nil _ => Fin.elim0
  | _, _, .cons _ rest => Fin.cons (rest.toTop.hom (Ideal.Quotient.mk _ Polynomial.X)) rest.roots

/-- The first root of a chain is the image of the adjoined root of its first stage. -/
@[simp]
theorem roots_cons_zero {C : CommRingCat.{u}} {n : ℕ} (c : C)
    (rest : AlphaPChain p (CommRingCat.of (alphaPAlgebra p C c)) n) :
    (cons c rest).roots 0 = rest.toTop.hom (Ideal.Quotient.mk _ Polynomial.X) :=
  rfl

/-- The later roots of a chain are the roots of the rest of the chain. -/
@[simp]
theorem roots_cons_succ {C : CommRingCat.{u}} {n : ℕ} (c : C)
    (rest : AlphaPChain p (CommRingCat.of (alphaPAlgebra p C c)) n) (i : Fin n) :
    (cons c rest).roots i.succ = rest.roots i :=
  rfl

/-- **The inductive step of `surjective_eval₂Hom_roots`**: if a ring `T` is generated over
`C[z]/(z ^ p - c)` by elements `r`, it is generated over `C` by the image of `z` and the `r`. -/
theorem surjective_eval₂Hom_cons {C T : CommRingCat.{u}} (c : C)
    (φ : alphaPAlgebra p C c →+* T) {m : ℕ} (r : Fin m → T)
    (hφ : Function.Surjective (MvPolynomial.eval₂Hom φ r)) :
    Function.Surjective (MvPolynomial.eval₂Hom (φ.comp (algebraMap C (alphaPAlgebra p C c)))
      (Fin.cons (φ (Ideal.Quotient.mk _ Polynomial.X)) r : Fin (m + 1) → T)) := by
  intro y
  obtain ⟨q, rfl⟩ := hφ y
  rw [← RingHom.mem_range]
  set R := (MvPolynomial.eval₂Hom (φ.comp (algebraMap C (alphaPAlgebra p C c)))
      (Fin.cons (φ (Ideal.Quotient.mk _ Polynomial.X)) r : Fin (m + 1) → T)).range
  have hX : φ (Ideal.Quotient.mk _ Polynomial.X) ∈ R :=
    ⟨MvPolynomial.X 0, by simp⟩
  induction q using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [MvPolynomial.eval₂Hom_C]
    induction P using Polynomial.induction_on with
    | C b => exact ⟨MvPolynomial.C b, by simp; rfl⟩
    | add P Q hP hQ => simpa only [map_add] using R.add_mem hP hQ
    | monomial k b ih =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul]
      exact R.mul_mem ih hX
  | add q₁ q₂ h₁ h₂ => simpa only [map_add] using R.add_mem h₁ h₂
  | mul_X q i h =>
    rw [map_mul]
    exact R.mul_mem h ⟨MvPolynomial.X i.succ, by simp⟩

/-- **The last ring of a chain is generated over the first by the roots**: every element of `R_n`
is a polynomial with coefficients in `R_0` in `z_1, …, z_n`. -/
theorem surjective_eval₂Hom_roots : ∀ {C : CommRingCat.{u}} {n : ℕ} (ch : AlphaPChain p C n),
    Function.Surjective (MvPolynomial.eval₂Hom ch.toTop.hom ch.roots)
  | _, _, nil C => fun y ↦ ⟨MvPolynomial.C y, MvPolynomial.eval₂_C _ _ _⟩
  | _, _, cons c rest =>
    surjective_eval₂Hom_cons c rest.toTop.hom rest.roots (surjective_eval₂Hom_roots rest)

end AlgebraicGeometry.AlphaPChain

open CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}}

/-- **[Stacks, Tag 07JJ] for a quasi-coherent sheaf of modules**: the abelian sheaf underlying a
quasi-coherent sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` has vanishing higher cohomology over the
objects with affine ambient scheme.  A quasi-coherent sheaf is locally quasi-coherent. -/
theorem abelianSheaf_vanishing07JJ (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) : Vanishing07JJ S (abelianSheaf F) :=
  vanishing07JJ_abelianSheaf F (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF)

/-- [Stacks, Tag 07JJ] for the abelian sheaf underlying a quasi-coherent crystal. -/
theorem abelianSheaf_vanishing07JJ_of_isQuasiCoherentCrystal
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsQuasiCoherentCrystal S F) :
    Vanishing07JJ S (abelianSheaf F) :=
  abelianSheaf_vanishing07JJ F hF.1

variable (S) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) {ι : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →ₐ[(openAffineSituation07Q9 S hW hVW).A]
    (openAffineSituation07Q9 S hW hVW).C) (hg : Function.Surjective g)

/-- **The level transitions of a quasi-coherent crystal along the Čech system of `W` are
surjective.**  The tower map `T(n)_e ⟶ T(n)_{e + 1}` is the extension to `Cris(X/S)` of a closed
immersion between thickenings of the whole of `W` in `Cris(W/S|_V)`, and the sections of `F` over
the extension of an object are those of the restriction of `F` to `Cris(W/S|_V)`, which is again
locally quasi-coherent with surjective comparison maps; there the surjectivity is
`surjective_abelianSheaf_map_of_isIso_toX`. -/
theorem hasSurjectiveLevelTransitions_openSystem07Q9 (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsQuasiCoherentCrystal S F) :
    HasSurjectiveLevelTransitions (openSystem07Q9 S hV hW hVW g hg) (abelianSheaf F) := by
  intro n e
  have := isAffine_restrictX07Q9 S hW hVW
  exact surjective_abelianSheaf_map_of_isIso_toX (smallExtendSheafRestriction S V W hVW F)
    (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e)))
    (isLocallyQuasiCoherent_smallExtendSheafRestriction S V W hVW F
      (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF.1))
    (isSurjectiveComparison_smallExtendSheafRestriction S V W hVW F
      (isSurjectiveComparison_of_isSheafCrystal hF.2))
    (isClosedImmersion_openSystem07Q9_map S hV hW hVW g hg n (Nat.le_succ e))
    (isIso_toX_openLocalSystem07Q9 S hV hW hVW g hg n e)
    (isIso_toX_openLocalSystem07Q9 S hV hW hVW g hg n (e + 1))

section Chain

variable {X' : Scheme.{u}} (f : X' ⟶ S.X) (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {p n : ℕ}
  (ch : AlphaPChain p Γ(S.X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top)

/-- The chain normal form read on the global sections of the open subscheme `f⁻¹(W)`:
`Γ(f⁻¹(W), ⊤) ≅ Γ(X', f⁻¹(W)) ≅ R_n`. -/
def chainSectionsIso07Q9 : Γ((f ⁻¹ᵁ W).toScheme, ⊤) ≅ ch.top := (f ⁻¹ᵁ W).topIso ≪≫ e

/-- **The presentation of `Γ(f⁻¹(W))` attached to a chain**: the `Γ(V)`-algebra map
`Γ(V)[c ∈ Γ(W), z_1, …, z_n] → Γ(f⁻¹(W))` sending the variable `c` to `f^♯ c` and the variable
`z_i` to the `i`-th root of the chain, read in `Γ(f⁻¹(W))` through `e`.  It is surjective when `e`
identifies `f^♯` with the structure map of the chain, `surjective_chainPresentation07Q9`. -/
def chainPresentation07Q9 :
    MvPolynomial ((openAffineSituation07Q9 S hW hVW).C ⊕ Fin n)
        (openAffineSituation₂07Q9 S hVW f hW₂).A →ₐ[(openAffineSituation₂07Q9 S hVW f hW₂).A]
      (openAffineSituation₂07Q9 S hVW f hW₂).C :=
  MvPolynomial.aeval (Sum.elim (fun c ↦ (restrictMap07Q9 S hVW f).appTop.hom c)
    (fun i ↦ (chainSectionsIso07Q9 S f ch e).inv.hom (ch.roots i)))

/-- The presentation sends the variable `c` to `f^♯ c`. -/
theorem chainPresentation07Q9_X_inl (c : (openAffineSituation07Q9 S hW hVW).C) :
    chainPresentation07Q9 S hW hVW f hW₂ ch e (MvPolynomial.X (Sum.inl c)) =
      (restrictMap07Q9 S hVW f).appTop.hom c :=
  MvPolynomial.aeval_X _ _

/-- The presentation sends the variable `z_i` to the `i`-th root of the chain. -/
theorem chainPresentation07Q9_X_inr (i : Fin n) :
    chainPresentation07Q9 S hW hVW f hW₂ ch e (MvPolynomial.X (Sum.inr i)) =
      (chainSectionsIso07Q9 S f ch e).inv.hom (ch.roots i) :=
  MvPolynomial.aeval_X _ _

/-- **The presentation attached to a chain is surjective.**  The last ring of the chain is
generated over `Γ(X, W)` by the roots, `AlgebraicGeometry.AlphaPChain.surjective_eval₂Hom_roots`,
and under the chain normal form the image of `Γ(X, W)` is the image of `f^♯`, which is the image of
the variables `c`. -/
theorem surjective_chainPresentation07Q9 (he : f.app W ≫ e.hom = ch.toTop) :
    Function.Surjective (chainPresentation07Q9 S hW hVW f hW₂ ch e) := by
  intro y
  obtain ⟨q, hq⟩ := ch.surjective_eval₂Hom_roots ((chainSectionsIso07Q9 S f ch e).hom.hom y)
  have hy : y = (chainSectionsIso07Q9 S f ch e).inv.hom
      (MvPolynomial.eval₂Hom ch.toTop.hom ch.roots q) := by
    rw [hq]
    exact (congrArg (fun k ↦ k.hom y) (chainSectionsIso07Q9 S f ch e).hom_inv_id).symm
  subst hy
  clear hq
  change _ ∈ (chainPresentation07Q9 S hW hVW f hW₂ ch e).toRingHom.range
  set R := (chainPresentation07Q9 S hW hVW f hW₂ ch e).toRingHom.range
  induction q using MvPolynomial.induction_on with
  | C b =>
    refine ⟨MvPolynomial.X (Sum.inl
      (show (openAffineSituation07Q9 S hW hVW).C from W.topIso.inv.hom b)), ?_⟩
    have h := congrArg (fun k ↦ k.hom b) (app_comp_topIso_inv f W)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chainPresentation07Q9_X_inl,
      MvPolynomial.eval₂Hom_C, ← he]
    simp only [chainSectionsIso07Q9, Iso.trans_inv, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [← CommRingCat.comp_apply e.hom e.inv, Iso.hom_inv_id, CommRingCat.id_apply, h]
    rfl
  | add q₁ q₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact R.add_mem h₁ h₂
  | mul_X q i h =>
    rw [map_mul, map_mul]
    refine R.mul_mem h ⟨MvPolynomial.X (Sum.inr i), ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chainPresentation07Q9_X_inr,
      MvPolynomial.eval₂Hom_X']

/-- **The morphism of presentations from the canonical presentation of `Γ(W)`**: the renaming
`Γ(V)[c ∈ Γ(W)] → Γ(V)[c ∈ Γ(W), z_1, …, z_n]` of the variables `c`. -/
def chainPresentationRename07Q9 :
    MvPolynomial (openAffineSituation07Q9 S hW hVW).C (openAffineSituation07Q9 S hW hVW).A →+*
      MvPolynomial ((openAffineSituation07Q9 S hW hVW).C ⊕ Fin n)
        (openAffineSituation₂07Q9 S hVW f hW₂).A :=
  (MvPolynomial.rename (R := (openAffineSituation₂07Q9 S hVW f hW₂).A) Sum.inl).toRingHom

/-- The renaming is the identity on constants. -/
theorem chainPresentationRename07Q9_C (b : (openAffineSituation07Q9 S hW hVW).A) :
    chainPresentationRename07Q9 S hW hVW f hW₂ (n := n) (MvPolynomial.C b) = MvPolynomial.C b :=
  MvPolynomial.rename_C _ _

/-- **The renaming is a morphism of presentations over `f^♯`**: followed by the presentation of
`Γ(f⁻¹(W))` it is the canonical presentation of `Γ(W)` followed by `f^♯`. -/
theorem chainPresentation07Q9_comp_rename :
    (chainPresentation07Q9 S hW hVW f hW₂ ch e).toRingHom.comp
        (chainPresentationRename07Q9 S hW hVW f hW₂) =
      (restrictMap07Q9 S hVW f).appTop.hom.comp
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro b
    have h := RingHom.congr_fun (openAffineSituationHom07Q9 S hW hVW f hW₂).commutes b
    change chainPresentation07Q9 S hW hVW f hW₂ ch e
        (MvPolynomial.rename (R := (openAffineSituation₂07Q9 S hVW f hW₂).A) Sum.inl
          (MvPolynomial.C (R := (openAffineSituation₂07Q9 S hVW f hW₂).A) b)) =
      (restrictMap07Q9 S hVW f).appTop.hom (canonicalPresentation _ (MvPolynomial.C b))
    refine (congrArg (chainPresentation07Q9 S hW hVW f hW₂ ch e)
      (MvPolynomial.rename_C (R := (openAffineSituation₂07Q9 S hVW f hW₂).A) Sum.inl b)).trans ?_
    refine ((chainPresentation07Q9 S hW hVW f hW₂ ch e).commutes b).trans ?_
    refine Eq.trans ?_ (congrArg (restrictMap07Q9 S hVW f).appTop.hom
      ((canonicalPresentation (openAffineSituation07Q9 S hW hVW)).commutes b).symm)
    exact h.symm
  · intro c
    change chainPresentation07Q9 S hW hVW f hW₂ ch e
        (MvPolynomial.rename (R := (openAffineSituation₂07Q9 S hVW f hW₂).A) Sum.inl
          (MvPolynomial.X c)) =
      (restrictMap07Q9 S hVW f).appTop.hom (canonicalPresentation _ (MvPolynomial.X c))
    rw [MvPolynomial.rename_X, chainPresentation07Q9_X_inl, canonicalPresentation,
      MvPolynomial.aeval_X]

/-- **The morphism of Čech systems over `f` attached to a chain normal form**: the morphism
`openCechSystemHom07Q9` from the Čech system of `f⁻¹(W)` for the presentation attached to the
chain to the Čech system of `W` for the canonical presentation. -/
def chainCechSystemHom07Q9 (he : f.app W ≫ e.hom = ch.toTop) :
    CechSystemHom (S := overSituation S f) (S' := S) (𝟙 S.S) f (overSituation_compat S f)
      (openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he))
      (openSystem07Q9 S hV hW hVW (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _)) :=
  openCechSystemHom07Q9 S hV hW hVW _ _ f hW₂ (chainPresentation07Q9 S hW hVW f hW₂ ch e)
    (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
    (chainPresentationRename07Q9 S hW hVW f hW₂)
    (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e)

end Chain

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
