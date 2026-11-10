module

public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsAxiom
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeGraded

/-!
# The axiom (A8) descends along a field extension (Lemma 0FVT)

The axiom (A8) of Section 45.14 of the Stacks Project
(`Stacks.WeilCohomology.FirstChernClassData.GlobalSectionsAxiom`) says that for `X` smooth
projective over `k` and `k' = Γ(X, 𝒪_X)` the map `H^0(Spec(k')) → H^0(X)` induced by the canonical
morphism `X ⟶ Spec(k')` is an isomorphism. The proof of Lemma 0FVT deduces (A8) for `H^*` from
(A8) for `(H')^*` by the linear algebra principle of its paragraph (A1). The geometric input is
that `X ⟶ Spec(k')` base changes to a morphism `X_{k'} ⟶ Spec(k')_{k'}` to an affine scheme
which again induces an isomorphism on global sections, by flat base change of global sections
(`Stacks.AlgebraicGeometry.PicardBaseChange`, `Γ(X_{k'}, 𝒪) = Γ(X, 𝒪) ⊗_k k'` for `X`
quasi-compact and quasi-separated); and that (A8) holds for every morphism `g : X ⟶ S` to an
affine smooth projective `S` inducing an isomorphism on global sections, since such a `g` is
`X ⟶ Spec Γ(X, 𝒪_X)` followed by an isomorphism.

## Main results

* `Stacks.WeilDeRham.exists_isIso_toSpecGlobalSections_comp`: a morphism to an affine scheme
  inducing an isomorphism on global sections is `X ⟶ Spec Γ(X, 𝒪_X)` followed by an isomorphism.
* `Stacks.WeilDeRham.bijective_gradedPieceMap_pull_of_isIso_appTop`: (A8) for every such morphism.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.WeilCohomology

universe u w w'

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology.SmoothProjectiveScheme hiding specStructure

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- A smooth projective scheme over a field is quasi-separated. -/
instance quasiSeparatedSpace_toScheme (X : (SmoothProjectiveScheme k).FullSubcategory) :
    QuasiSeparatedSpace ((toScheme k).obj X) := by
  have := (isProjective X).isProper
  exact quasiSeparatedSpace_of_quasiSeparated X.obj.hom

/-- **The square of global sections of a base change along `Spec(k') → Spec(k)` is a pushout**,
that is `Γ(X_{k'}, 𝒪) = Γ(X, 𝒪) ⊗_k k'`. -/
theorem isPushout_appTop_fieldBaseChange (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsPushout X.obj.hom.appTop (specStructure k k').appTop (fieldBaseChangeProj X).appTop
      ((fieldBaseChange k k').obj X).obj.hom.appTop :=
  have : CompactSpace X.obj.left := SmoothProjectiveScheme.compactSpace X
  have : QuasiSeparatedSpace X.obj.left := quasiSeparatedSpace_toScheme X
  Stacks.AlgebraicGeometry.PicardBaseChange.isPushout_appTop_baseChange
    (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k k')) X.obj.hom

/-- **A morphism to an affine scheme inducing an isomorphism on global sections is the canonical
morphism `X ⟶ Spec Γ(X, 𝒪_X)` followed by an isomorphism.** -/
theorem exists_isIso_toSpecGlobalSections_comp {X S : (SmoothProjectiveScheme k).FullSubcategory}
    (g : X ⟶ S) [IsAffine ((toScheme k).obj S)] (hg : IsIso ((toScheme k).map g).appTop) :
    ∃ e : specGlobalSections X ⟶ S, IsIso e ∧ toSpecGlobalSections X ≫ e = g := by
  let X₀ := (toScheme k).obj X
  let S₀ := (toScheme k).obj S
  let g₀ := (toScheme k).map g
  let e₀ : (toScheme k).obj (specGlobalSections X) ⟶ S₀ := Spec.map g₀.appTop ≫ S₀.isoSpec.inv
  have key : X₀.toSpecΓ ≫ e₀ = g₀ := by
    simp only [e₀]
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  -- morphisms out of `Spec Γ(X, 𝒪_X)` to an affine scheme are determined after `X ⟶ Spec Γ`
  have hcancel : ∀ {Y : Scheme.{u}} [IsAffine Y]
      (f₁ f₂ : (toScheme k).obj (specGlobalSections X) ⟶ Y),
      X₀.toSpecΓ ≫ f₁ = X₀.toSpecΓ ≫ f₂ → f₁ = f₂ := by
    intro Y _ f₁ f₂ hf
    have : IsIso X₀.toSpecΓ.appTop := by rw [Scheme.toSpecΓ_appTop]; infer_instance
    apply ext_of_isAffine
    have h := congrArg Scheme.Hom.appTop hf
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
    exact (cancel_mono _).mp h
  have hw : e₀ ≫ S.obj.hom = (specGlobalSections X).obj.hom := by
    apply hcancel
    rw [← Category.assoc, key]
    exact (w g).trans (w (toSpecGlobalSections X)).symm
  refine ⟨homMk e₀ hw, ?_, hom_ext' ?_⟩
  · have : IsIso ((toScheme k).map (homMk e₀ hw)) :=
      inferInstanceAs (IsIso (Spec.map g₀.appTop ≫ S₀.isoSpec.inv))
    exact isIso_of_reflects_iso _ (toScheme k)
  · rw [CategoryTheory.Functor.map_comp, map_homMk]
    exact key

variable {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

/-- **The axiom (A8) for every morphism to an affine scheme inducing an isomorphism on global
sections**: if `g : X ⟶ S` with `S` affine induces `Γ(S, 𝒪_S) ≅ Γ(X, 𝒪_X)`, then
`g^* : H^0(S) → H^0(X)` is bijective. -/
theorem bijective_gradedPieceMap_pull_of_isIso_appTop (hA8 : 𝔇.GlobalSectionsAxiom)
    {X S : (SmoothProjectiveScheme k).FullSubcategory} (g : X ⟶ S) [IsAffine ((toScheme k).obj S)]
    (hg : IsIso ((toScheme k).map g).appTop) :
    Function.Bijective (gradedPieceMap (𝔇.grade S) (𝔇.grade X) (𝔇.pull g) (𝔇.pull_grade g) 0) := by
  obtain ⟨e, he, rfl⟩ := exists_isIso_toSpecGlobalSections_comp g hg
  have h1 : Function.Bijective (gradedPieceMap _ _ (𝔇.pull (toSpecGlobalSections X))
      (𝔇.pull_grade (toSpecGlobalSections X)) 0) := hA8 X
  have h2 : Function.Bijective (gradedPieceMap _ _ (𝔇.pull e) (𝔇.pull_grade e) 0) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨gradedPieceMap _ _ (𝔇.pull (inv e)) (𝔇.pull_grade (inv e)) 0,
        fun a => Subtype.ext (by
          change 𝔇.pull (inv e) (𝔇.pull e a) = a
          rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, IsIso.inv_hom_id, 𝔇.pull_id, AlgHom.id_apply]),
        fun a => Subtype.ext (by
          change 𝔇.pull e (𝔇.pull (inv e) a) = a
          rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, IsIso.hom_inv_id, 𝔇.pull_id, AlgHom.id_apply])⟩
  have hc : gradedPieceMap _ _ (𝔇.pull (toSpecGlobalSections X ≫ e))
      (𝔇.pull_grade (toSpecGlobalSections X ≫ e)) 0 =
      gradedPieceMap _ _ (𝔇.pull (toSpecGlobalSections X))
        (𝔇.pull_grade (toSpecGlobalSections X)) 0 ∘ₗ
        gradedPieceMap _ _ (𝔇.pull e) (𝔇.pull_grade e) 0 :=
    LinearMap.ext fun a => Subtype.ext (by
      change 𝔇.pull (toSpecGlobalSections X ≫ e) a =
        𝔇.pull (toSpecGlobalSections X) (𝔇.pull e a)
      rw [𝔇.pull_comp, AlgHom.comp_apply])
  rw [hc, LinearMap.coe_comp]
  exact h1.comp h2

end Stacks.WeilDeRham

end
