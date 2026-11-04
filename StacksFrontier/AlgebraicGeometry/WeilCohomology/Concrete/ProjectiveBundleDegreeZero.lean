module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.PicardDescent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FiniteEtaleSpec
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernData

/-!
# Degree-zero cohomology of a projective bundle under axiom (A8)

Let `ℰ` be finite locally free of rank `r + 1` on a smooth projective scheme `Z` over `k` and
`p : P = 𝐏(ℰ) ⟶ Z` its projective bundle. Then `p_*𝒪_P = 𝒪_Z`: over an open on which `ℰ` is free,
`p` is the structure morphism of `ℙʳ`, for which this is the degree-zero part of Tag 01XW; and an
isomorphism of sheaves can be checked on a basis of opens. In particular
`p^♯ : Γ(Z, 𝒪_Z) → Γ(P, 𝒪_P)` is bijective.

Axiom (A8) identifies `H^0(X)` with `H^0(Spec Γ(X, 𝒪_X))` through `X ⟶ Spec Γ(X, 𝒪_X)`, naturally
in `X`. So for any morphism `f : X ⟶ Y` of smooth projective schemes inducing a bijection on
global functions, every class of `H^0(X)` is `f^*` of a class of `H^0(Y)`; for `p` this says
`H^0(P) = p^*H^0(Z)`.

Axiom (A3) alone does not give this: it writes a class of `H^0(P)` as `∑ ξ^i ∪ p^*a_i` with
`a_i ∈ H^{-2i}(Z)`, and nothing in (A1)–(A7) forces `H^{-2i}(Z) = 0`.

## Main results

* `Stacks.Chow.isLocallyProjectiveSpace_bundleProj`: `𝐏(ℰ) ⟶ Z` is Zariski-locally `ℙʳ`.
* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.isIso_c`: for such a morphism `f`, the
  comparison `𝒪_Z ⟶ f_*𝒪` is an isomorphism.
* `Stacks.Chow.isIso_appTop_bundleProj`: `Γ(Z, 𝒪_Z) ≅ Γ(𝐏(ℰ), 𝒪)`.
* `Stacks.WeilCohomology.FirstChernClassData.exists_pull_grade_zero_of_isIso_appTop`: under (A8),
  `H^0(X) = f^*H^0(Y)` when `f : X ⟶ Y` is bijective on global functions.
* `Stacks.WeilCohomology.WeilChernData.exists_pull_bundleProj_grade_zero`: under (A8),
  `H^0(𝐏(ℰ)) = p^*H^0(Z)`.

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u w

namespace Stacks.ProjectiveBundle

variable {H P : Scheme.{u}} {f : H ⟶ P} {m : ℕ}

/-- **A morphism which is Zariski-locally on the target a projective space has `f_*𝒪_H = 𝒪_P`**:
the comparison `𝒪_P ⟶ f_*𝒪_H` is an isomorphism. It is one on every open inside a chart, and the
affine opens inside charts cover `P`. -/
theorem IsLocallyProjectiveSpace.isIso_c (hf : IsLocallyProjectiveSpace f m) : IsIso f.c := by
  have hloc : ∀ y : P, ∃ (W : P.Opens) (V : P.Opens), IsAffineOpen W ∧ y ∈ W ∧ W ≤ V ∧
      ∃ e : (f ⁻¹ᵁ V).toScheme ≅ projectiveSpaceOver m V.toScheme,
        e.hom ≫ (projectiveSpaceOver m V.toScheme ↘ V.toScheme) = f ∣_ V := by
    intro y
    obtain ⟨V, hyV, e, he⟩ := hf y
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
      P.isBasis_affineOpens.exists_subset_of_mem_open hyV V.2
    exact ⟨W, V, hW, hyW, hWV, e, he⟩
  choose W V hW hyW hWV e he using hloc
  refine Stacks.AlgebraicGeometry.isIso_c_of_isIso_app_basicOpen f W hW ?_ fun y r => ?_
  · refine eq_top_iff.2 fun y _ => ?_
    exact Opens.mem_iSup.2 ⟨y, hyW y⟩
  · rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_app_of_isoProjectiveSpaceOver f (e y) (he y) _
      ((P.basicOpen_le r).trans (hWV y))

/-- For a morphism which is Zariski-locally on the target a projective space, `f^♯` is an
isomorphism on global functions. -/
theorem IsLocallyProjectiveSpace.isIso_appTop (hf : IsLocallyProjectiveSpace f m) :
    IsIso f.appTop :=
  have := hf.isIso_c
  NatIso.isIso_app_of_isIso f.c (op ⊤)

end Stacks.ProjectiveBundle

namespace Stacks.Chow

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- **The projective bundle of a module finite locally free of constant rank `n + 1` is
Zariski-locally `ℙⁿ`**: over an open on which the module is free it is `𝐏(𝒪^{n+1}) = ℙⁿ`
(Tag 01OE), over that open. -/
theorem isLocallyProjectiveSpace_bundleProj :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    Stacks.ProjectiveBundle.IsLocallyProjectiveSpace (bundleProj E) n := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  intro x
  obtain ⟨U, hxU, Φ, hΦ⟩ :=
    Stacks.ProjectiveBundle.exists_iso_morphismRestrict_free E (bundlePieces E) n x
  refine ⟨U, hxU, Φ.symm ≪≫ Stacks.SymGraded.projectiveBundleIsoProjectiveSpace
    (X := U.toScheme) n, ?_⟩
  exact (Category.assoc Φ.inv _ _).trans ((congrArg (Φ.inv ≫ ·)
    (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := U.toScheme) n)).trans
    ((congrArg (Φ.inv ≫ ·) hΦ.symm).trans (Φ.inv_hom_id_assoc _)))

/-- **`p_*𝒪_{𝐏(ℰ)} = 𝒪_X`** for the projective bundle of a module finite locally free of constant
rank. -/
theorem isIso_c_bundleProj :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    IsIso (bundleProj E).c :=
  (isLocallyProjectiveSpace_bundleProj E n).isIso_c

/-- **`Γ(X, 𝒪_X) = Γ(𝐏(ℰ), 𝒪)`** for the projective bundle of a module finite locally free of
constant rank: `p^♯` is an isomorphism on global functions. -/
theorem isIso_appTop_bundleProj :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    IsIso (bundleProj E).appTop :=
  (isLocallyProjectiveSpace_bundleProj E n).isIso_appTop

end Stacks.Chow

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] {X Y : (SmoothProjectiveScheme k).FullSubcategory}

/-- `f^♯ : Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)` for a morphism `f : X ⟶ Y` of smooth projective `k`-schemes, as
a map of `k`-algebras. -/
def appTopAlgHom (f : X ⟶ Y) : globalSections Y →ₐ[k] globalSections X where
  toRingHom := f.hom.left.appTop.hom
  commutes' r := by
    change f.hom.left.appTop.hom (((Scheme.ΓSpecIso (.of k)).inv ≫ Y.obj.hom.appTop).hom r) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.obj.hom.appTop).hom r
    rw [← Over.w f.hom, Scheme.Hom.comp_appTop]
    rfl

/-- The canonical morphisms `X ⟶ Spec Γ(X, 𝒪_X)` are natural: `Spec(f^♯) ∘ (X ⟶ Spec Γ(X)) =
(Y ⟶ Spec Γ(Y)) ∘ f`. -/
theorem toSpecGlobalSections_comp_specMap_appTopAlgHom (f : X ⟶ Y) :
    toSpecGlobalSections X ≫ specMap (appTopAlgHom f) = f ≫ toSpecGlobalSections Y := by
  apply hom_ext_left
  show X.obj.left.toSpecΓ ≫ Spec.map f.hom.left.appTop = f.hom.left ≫ Y.obj.left.toSpecΓ
  rw [Scheme.toSpecΓ_naturality]

end SmoothProjectiveScheme

namespace FirstChernClassData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- **Under (A8), degree-zero classes come from any target with the same global functions.** If
`f : X ⟶ Y` induces a bijection `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`, every `y ∈ H^0(X)` is `f^*z` for some
`z ∈ H^0(Y)`: by (A8) `y` comes from `H^0(Spec Γ(X, 𝒪_X))`, and `Spec Γ(X, 𝒪_X) ⟶ Spec Γ(Y, 𝒪_Y)`
is an isomorphism compatible with `f`. -/
theorem exists_pull_grade_zero_of_isIso_appTop (hA8 : 𝔇.GlobalSectionsAxiom)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (hf : IsIso f.hom.left.appTop)
    {y : 𝔇.H X} (hy : y ∈ 𝔇.grade X 0) :
    ∃ z ∈ 𝔇.grade Y 0, 𝔇.pull f z = y := by
  have hbij : Function.Bijective (appTopAlgHom f) :=
    (ConcreteCategory.isIso_iff_bijective f.hom.left.appTop).1 hf
  let e : globalSections Y ≃ₐ[k] globalSections X := AlgEquiv.ofBijective (appTopAlgHom f) hbij
  have he : specMap (appTopAlgHom f) ≫ specMap e.symm.toAlgHom = 𝟙 _ := by
    rw [← specMap_comp, ← specMap_id]
    congr 1
    ext a
    exact e.apply_symm_apply a
  obtain ⟨a, ha⟩ := (hA8 X).2 ⟨y, hy⟩
  have ha' : 𝔇.pull (toSpecGlobalSections X) a = y := congrArg Subtype.val ha
  let b := 𝔇.pull (specMap e.symm.toAlgHom) a
  have hb : b ∈ 𝔇.grade _ 0 := 𝔇.pull_grade _ 0 a.1 a.2
  refine ⟨𝔇.pull (toSpecGlobalSections Y) b, 𝔇.pull_grade _ 0 b hb, ?_⟩
  rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, ← toSpecGlobalSections_comp_specMap_appTopAlgHom,
    𝔇.pull_comp, AlgHom.comp_apply]
  show 𝔇.pull (toSpecGlobalSections X)
    (𝔇.pull (specMap (appTopAlgHom f)) (𝔇.pull (specMap e.symm.toAlgHom) a)) = y
  rw [← AlgHom.comp_apply (𝔇.pull (specMap (appTopAlgHom f))), ← 𝔇.pull_comp, he, 𝔇.pull_id,
    AlgHom.id_apply, ha']

end FirstChernClassData

namespace WeilChernData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **Degree-zero cohomology of a projective bundle, under (A8)**: for `ℰ` finite locally free of
rank `r + 1` on `Z` and `p : 𝐏(ℰ) ⟶ Z`, every `y ∈ H^0(𝐏(ℰ))` is `p^*z` for some `z ∈ H^0(Z)`.
Indeed `Γ(𝐏(ℰ), 𝒪) = Γ(Z, 𝒪_Z)` because `p_*𝒪 = 𝒪_Z`, and (A8) applies. -/
theorem exists_pull_bundleProj_grade_zero (hA8 : 𝔚.GlobalSections)
    (Z : (SmoothProjectiveScheme k).FullSubcategory) (M : Z.obj.left.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M (r + 1)]
    (y : 𝔚.H (SmoothProjectiveScheme.bundle Z M r))
    (hy : y ∈ 𝔚.grade (SmoothProjectiveScheme.bundle Z M r) 0) :
    ∃ z ∈ 𝔚.grade Z 0, 𝔚.pull (SmoothProjectiveScheme.bundleProj Z M r) z = y :=
  𝔚.exists_pull_grade_zero_of_isIso_appTop hA8 (SmoothProjectiveScheme.bundleProj Z M r)
    (Stacks.Chow.isIso_appTop_bundleProj M r) hy

end WeilChernData

end Stacks.WeilCohomology

end
