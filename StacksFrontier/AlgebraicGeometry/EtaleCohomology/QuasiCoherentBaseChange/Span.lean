module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentBaseChange.Basic

/-!
# The base change map spans, by dimension shifting

Let `g : Y ⟶ X` be a morphism of schemes and `c : K → Γ(Y, ⊤)` a family of global functions of
`Y` (in the application, the image of the larger ground field). Say that the base change map
`H^q(X_étale, ℱᵉ) ⟶ H^q(Y_étale, (g^* ℱ)ᵉ)` *spans* if every class upstairs is a finite sum of
images of classes downstairs multiplied by functions `c a`.

If it spans in degree `0` for every quasi-coherent module, and every quasi-coherent module `ℱ`
sits in a short exact sequence `0 → ℱ → 𝒢 → 𝒬 → 0` of quasi-coherent modules which stays exact
on both étale sites and whose middle term has vanishing higher cohomology upstairs, then it spans
in every degree for every quasi-coherent module: the connecting map `H^q(𝒬) ⟶ H^{q+1}(ℱ)` upstairs
is onto and commutes with the base change maps and with the multiplications.

## Main definitions

* `AlgebraicGeometry.QcohEtale.Spans`: the spanning property.

## Main results

* `AlgebraicGeometry.QcohEtale.spans_succ`: the dimension-shifting step.
* `AlgebraicGeometry.QcohEtale.spans_of_forall`: the induction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.EtaleCohomology

universe w u

namespace AlgebraicGeometry.QcohEtale

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

section ScalarConnecting

variable {Z : Scheme.{u}} [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Multiplication by a global function, as an endomorphism of `etaleShortComplex S`. -/
def scalarShortComplex (S : ShortComplex Z.Modules) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (r : Γ(Z, ⊤)) :
    etaleShortComplex S ⟶ etaleShortComplex S where
  τ₁ := etaleScalar S.X₁ r
  τ₂ := etaleScalar S.X₂ r
  τ₃ := etaleScalar S.X₃ r
  comm₁₂ := etaleScalar_comp_etaleMap S.f r
  comm₂₃ := etaleScalar_comp_etaleMap S.g r

/-- The connecting maps commute with multiplication by global functions. -/
theorem mk₀_scalar_comp_extClass (S : ShortComplex Z.Modules) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (hS : (etaleShortComplex S).ShortExact)
    (r : Γ(Z, ⊤)) :
    (Ext.mk₀ (etaleScalar S.X₃ r)).comp hS.extClass (zero_add 1) =
      hS.extClass.comp (Ext.mk₀ (etaleScalar S.X₁ r)) (add_zero 1) :=
  (hS.extClass_naturality hS (scalarShortComplex S r)).symm

end ScalarConnecting

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  {K : Type*} (c : K → Γ(Y, ⊤))

/-- The images of classes downstairs, multiplied by the functions `c a`. -/
def scaledImage (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    Set (Sheaf.H.{w} (etaleSheaf ((Scheme.Modules.pullback g).obj F)) q) :=
  {z | ∃ (a : K) (x : Sheaf.H.{w} (etaleSheaf F) q),
    z = (restriction g F q x).comp
      (Ext.mk₀ (etaleScalar ((Scheme.Modules.pullback g).obj F) (c a))) (add_zero q)}

/-- **The base change map spans in degree `q`**: every class of `H^q(Y_étale, (g^* ℱ)ᵉ)` is a
finite sum of images of classes of `H^q(X_étale, ℱᵉ)` multiplied by functions `c a`. -/
def Spans (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) : Prop :=
  ∀ y : Sheaf.H.{w} (etaleSheaf ((Scheme.Modules.pullback g).obj F)) q,
    y ∈ AddSubgroup.closure (scaledImage g c F q)

/-- **The dimension-shifting step.** -/
theorem spans_succ (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (hS : (etaleShortComplex S).ShortExact)
    (hS' : (etaleShortComplex (pullbackShortComplex g S)).ShortExact) (q : ℕ)
    (hvan : Subsingleton
      (Sheaf.H.{w} (etaleSheaf ((Scheme.Modules.pullback g).obj S.X₂)) (q + 1)))
    (h : Spans.{w} g c S.X₃ q) : Spans.{w} g c S.X₁ (q + 1) := by
  intro y
  obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS' y (@Subsingleton.elim _ hvan _ _) rfl
  let δ : Sheaf.H.{w} (etaleSheaf ((Scheme.Modules.pullback g).obj S.X₃)) q →+
      Sheaf.H.{w} (etaleSheaf ((Scheme.Modules.pullback g).obj S.X₁)) (q + 1) :=
    hS'.extClass.postcomp _ (rfl : q + 1 = q + 1)
  change δ z ∈ _
  refine (AddSubgroup.closure_le
    (K := (AddSubgroup.closure (scaledImage g c S.X₁ (q + 1))).comap δ)).2 ?_ (h z)
  rintro _ ⟨a, x, rfl⟩
  refine AddSubgroup.subset_closure ⟨a, x.comp hS.extClass rfl, ?_⟩
  rw [restriction_comp_extClass g S hS hS' q (q + 1) rfl x]
  change ((restriction g S.X₃ q x).comp (Ext.mk₀ (etaleScalar _ (c a))) (add_zero q)).comp
      hS'.extClass rfl = _
  exact (Ext.comp_assoc_of_second_deg_zero _ _ _ _).trans
    ((congrArg (fun z => (restriction g S.X₃ q x).comp z rfl)
      (mk₀_scalar_comp_extClass (pullbackShortComplex g S) hS' (c a))).trans
      (Ext.comp_assoc _ _ _ rfl (add_zero 1) (by omega)).symm)

/-- **The induction.** If the base change map spans in degree `0` for every quasi-coherent
module, and every quasi-coherent module embeds into one with vanishing higher cohomology
upstairs, through a short exact sequence which stays exact on both étale sites, then it spans in
every degree. -/
theorem spans_of_forall
    (hzero : ∀ (F : X.Modules) [F.IsQuasicoherent], Spans.{w} g c F 0)
    (hemb : ∀ (F : X.Modules) [F.IsQuasicoherent], ∃ (G Q : X.Modules) (_ : G.IsQuasicoherent)
      (_ : Q.IsQuasicoherent) (i : F ⟶ G) (p : G ⟶ Q) (w : i ≫ p = 0),
      (etaleShortComplex (ShortComplex.mk i p w)).ShortExact ∧
      (etaleShortComplex (pullbackShortComplex g (ShortComplex.mk i p w))).ShortExact ∧
      ∀ q : ℕ, Subsingleton
        (Sheaf.H.{w} (etaleSheaf ((Scheme.Modules.pullback g).obj G)) (q + 1)))
    (q : ℕ) : ∀ (F : X.Modules) [F.IsQuasicoherent], Spans.{w} g c F q := by
  induction q with
  | zero => exact hzero
  | succ q ih =>
    intro F _
    obtain ⟨G, Q, _, _, i, p, w, hS, hS', hvan⟩ := hemb F
    exact spans_succ g c (ShortComplex.mk i p w) hS hS' q (hvan q) (ih Q)

end AlgebraicGeometry.QcohEtale

end
