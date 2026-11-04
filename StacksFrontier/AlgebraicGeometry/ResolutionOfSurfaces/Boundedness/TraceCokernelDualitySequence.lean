module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.RingTheory.Dualizing.MatlisExtComparison
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.FirstCohomologyAnnihilationReduction

/-!
# The duality step of Tag 0B4S, as a statement about the triangle `A ⟶ Rf_*𝒪_X ⟶ R¹f_*𝒪_X[-1]`

The proof of [Stacks, Tag 0B4S] applies `RHom_A(-, ω_A^•)` to the distinguished triangle
`A ⟶ Rf_*𝒪_X ⟶ R¹f_*𝒪_X[-1] ⟶ A[1]`, reads the resulting short exact sequence
`0 ⟶ f_*ω_X ⟶ ω_A ⟶ Ext²_A(R¹f_*𝒪_X, ω_A) ⟶ 0` ([Stacks, Tag 0AUE]), identifies the `Ext²`
with a Matlis dual by local duality ([Stacks, Tag 0AAK]) and concludes that a `d` annihilating
the cokernel of the trace annihilates `R¹f_*𝒪_X`. This file performs that step without
constructing the short exact sequence: what the argument uses is only the *surjectivity* of
`Hom(Rf_*𝒪_X, ω_A^•) ⟶ Hom(A, ω_A^•)` modulo `d`, and that is read off the triangle by the
exactness of `Hom(-, ω_A^•)` on a distinguished triangle.

## Main results

All in the namespace `Stacks.ResolutionOfSurfaces`.

* `exists_comp_eq_of_forall_hom_invRotate_eq_zero` and `comp_smul_eq_zero_of_triangle_image` —
  the formal half, in any pretriangulated category: if every morphism `T.invRotate.obj₁ ⟶ W`
  vanishes and every morphism `T.obj₂ ⟶ W` becomes, after composition with `e : W ⟶ W`, a
  morphism factoring through `T.mor₂`, then `e` kills every morphism `T.obj₁ ⟶ W`.
* `exists_distTriang_singleFunctor_homology_of_isIso_homologyMap` — the triangle itself: an
  object `K` of `D(𝒜)` with cohomology in the two degrees `n` and `m = n + 1` only sits in a
  distinguished triangle whose first morphism is a given `M[n] ⟶ K` inducing an isomorphism on
  `Hⁿ` and whose third term is `Hᵐ(K)[m]`.
* `smul_eq_zero_of_smul_ext_into_normalizedDualizing_eq_zero` — local duality in the form the
  argument consumes: if `d` annihilates `Ext⁰_A(H[0], ω_A^•)` for a finite-length `H` and a
  normalized dualizing complex `ω_A^•`, then `d` annihilates `H`. No injective hull appears in
  the statement; one is produced inside the proof by [Stacks, Tag 08Y3].
* `smul_eq_zero_of_triangle_of_forall_hom_eq_zero` — the two combined: the duality step of
  [Stacks, Tag 0B4S] as a statement about an object of `D(A)` with cohomology in the degrees
  `-2` and `-1`.
* `isReductionToRationalSingularitiesPossible_of_triangle_data` — that step fed into
  `isReductionToRationalSingularitiesPossible_of_forall_smul_firstCohomology_eq_zero` of
  `Boundedness/FirstCohomologyAnnihilationReduction.lean`, which is the rest of
  [Stacks, Tag 0B4S]: the conclusion of the tag, granted the duality data of every normal
  modification.

## What the hypotheses mean geometrically

Write `C = RΓ(X, 𝒪_X)[2]`, the `A`-linear derived global sections of the structure sheaf shifted
so that `H^{-2}(C) = Γ(X, 𝒪_X)` and `H^{-1}(C) = H¹(X, 𝒪_X)`, and let `ω_A^•` be a normalized
dualizing complex over `A`. Recall that a normal local domain of dimension two is
Cohen-Macaulay, so `ω_A^•` is the dualizing module `ω_A` placed in degree `-2`; hence
`Hom_{D(A)}(A[2], ω_A^•) = ω_A` and `Hom_{D(A)}(H¹(X, 𝒪_X)[0], ω_A^•) = Ext²_A(H¹(X, 𝒪_X), ω_A)`,
which is the `Ext²` of the source's short exact sequence.

* `C` has cohomology in the degrees `-2` and `-1` only, because `Rⁱf_*𝒪_X = 0` for `i ≥ 2` — the
  fibres have dimension at most one — and `u : A[2] ⟶ C`, the unit `A ⟶ Rf_*𝒪_X` shifted, is an
  isomorphism on `H^{-2}` because `f_*𝒪_X = 𝒪_{Spec A}` for a modification of a normal base. The
  triangle these produce is the source's `A ⟶ Rf_*𝒪_X ⟶ R¹f_*𝒪_X[-1] ⟶ A[1]`, shifted by two.
* `hvan`, the vanishing of `Hom_{D(A)}(C⟦-1⟧, ω_A^•)`, is Grauert-Riemenschneider vanishing.
  Over the affine base that group is `Hom_{D(𝒪_X)}(𝒪_X[-1], ω_X[0]) = H¹(X, ω_X)`, by the
  adjunction `Rf_* ⊣ f^×` of [Stacks, Tag 0A9E]
  (`Stacks.Duality.twistedInverseImageAdjunction`) with the normalization
  `f^×(ω̃_A^•) ≅ ω_X[2]` (`AlgebraicGeometry.VanishingSituation`
  `.exists_isDualizingModule_properRightAdjoint_isoShiftTwo`) and the derived Spec-`Γ`
  equivalence of [Stacks, Tag 06Z0]; and `H¹(X, ω_X) = 0` is [Stacks, Tag 0AXD],
  `AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_normalizedDualizingModule`.
* `himage` is the hypothesis of the tag. `Hom_{D(A)}(C, ω_A^•)` is `Γ(X, ω_X)` by the duality
  transport `RHom_A(RΓ(X, ω_X^•), ω_A^•) ≅ RΓ(X, 𝒪_X)`
  (`Stacks.Duality.nonempty_iso_dualizingDerivedHom_derivedGlobalSections_relativeDualizing`)
  with biduality ([Stacks, Tag 0A7C], `Dualizing.dualizingDerivedHom_biduality_isIso`), and
  composition with `u` is the trace `Γ(X, ω_X) ⟶ ω_A` of [Stacks, Tag 0AWG]
  (`Stacks.Duality.qcqsTrace`); so `himage` says that `d · ω_A` lies in the image of the trace,
  which is the tag's hypothesis that `d` annihilate the cokernel of the trace.

**No `@[stacks 0B4S]` attribute is placed here.** None of the five conditions above is
discharged in this file: what is proved is the implication, which is the step of the source's
proof — duality applied to the triangle, composed with local duality — that this development did
not have. The three inputs still owed are the cohomological concentration of `RΓ(X, 𝒪_X)`
together with `f_*𝒪_X = 𝒪_{Spec A}`, the reading of `hvan` through the adjunction, and the
identification of `Hom_{D(A)}(C, ω_A^•)` with `Γ(X, ω_X)` carrying `u` to the trace. The
registration of the tag stays on
`Stacks.ResolutionOfSurfaces`
`.isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero`
of `Boundedness/TraceCokernelReduction.lean`.

## References

* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
* [Stacks Project, Tag 0A7Q](https://stacks.math.columbia.edu/tag/0A7Q)
* [Stacks Project, Tag 08Y3](https://stacks.math.columbia.edu/tag/08Y3)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace Stacks.ResolutionOfSurfaces

/-! ### The formal half: exactness of `Hom(-, W)` on a distinguished triangle -/

section Formal

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **A morphism out of the first term of a distinguished triangle factors through the second,
provided the preceding term of the rotated triangle sees nothing of the target.** This is
`CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂` at `T.invRotate`, whose second and third
terms are the first and second terms of `T`. -/
theorem exists_comp_eq_of_forall_hom_invRotate_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (W : C) (hvan : ∀ g : T.invRotate.obj₁ ⟶ W, g = 0) (q : T.obj₁ ⟶ W) :
    ∃ r : T.obj₂ ⟶ W, q = T.mor₁ ≫ r :=
  T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) q (hvan (T.invRotate.mor₁ ≫ q))

/-- **The formal duality step.** Let `T` be a distinguished triangle, let `W` be an object such
that every morphism `T.invRotate.obj₁ ⟶ W` vanishes, and let `e : W ⟶ W`. If every morphism
`T.obj₂ ⟶ W` becomes, after composition with `e`, a morphism factoring through `T.mor₂`, then
composition with `e` kills every morphism `T.obj₁ ⟶ W`.

A morphism `q : T.obj₁ ⟶ W` factors as `T.mor₁ ≫ r` by
`exists_comp_eq_of_forall_hom_invRotate_eq_zero`, and `r ≫ e` factors as `T.mor₂ ≫ s`; then
`q ≫ e = T.mor₁ ≫ T.mor₂ ≫ s = 0`, two consecutive morphisms of a distinguished triangle
composing to zero. -/
theorem comp_smul_eq_zero_of_triangle_image (T : Triangle C) (hT : T ∈ distTriang C) (W : C)
    (hvan : ∀ g : T.invRotate.obj₁ ⟶ W, g = 0) (e : W ⟶ W)
    (himage : ∀ q : T.obj₂ ⟶ W, ∃ p : T.obj₃ ⟶ W, T.mor₂ ≫ p = q ≫ e)
    (q : T.obj₁ ⟶ W) : q ≫ e = 0 := by
  obtain ⟨r, hr⟩ := exists_comp_eq_of_forall_hom_invRotate_eq_zero T hT W hvan q
  obtain ⟨s, hs⟩ := himage r
  rw [hr, Category.assoc, ← hs, ← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]

end Formal

/-! ### The triangle of an object with cohomology in two consecutive degrees -/

section TwoDegrees

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- **A morphism of objects of `D(𝒜)` concentrated in one and the same degree which is an
isomorphism on cohomology there is an isomorphism.** -/
theorem isIso_of_isIso_homologyMap_of_isGE_of_isLE {K L : DerivedCategory 𝒜} (n : ℤ)
    [K.IsGE n] [K.IsLE n] [L.IsGE n] [L.IsLE n] (f : K ⟶ L)
    [IsIso ((DerivedCategory.homologyFunctor 𝒜 n).map f)] : IsIso f := by
  refine (DerivedCategory.isIso_iff 𝒜 f).mpr fun j => ?_
  rcases lt_trichotomy j n with hj | rfl | hj
  · exact IsZero.isIso (DerivedCategory.isZero_of_isGE K n j hj)
      (DerivedCategory.isZero_of_isGE L n j hj) _
  · infer_instance
  · exact IsZero.isIso (DerivedCategory.isZero_of_isLE K n j hj)
      (DerivedCategory.isZero_of_isLE L n j hj) _

/-- **An object of `D(𝒜)` with cohomology in the two consecutive degrees `n` and `m = n + 1`
sits in a distinguished triangle `M[n] ⟶ K ⟶ Hᵐ(K)[m] ⟶ M[n][1]` as soon as a morphism
`M[n] ⟶ K` inducing an isomorphism on `Hⁿ` is given.**

The triangle is the truncation triangle of the t-structure at `m`: its first term is `τ_{< m}K`,
which is concentrated in degree `n`, so the given morphism factors through it by
`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂` and the factorisation is an
isomorphism by `isIso_of_isIso_homologyMap_of_isGE_of_isLE`; its third term is `τ_{≥ m}K`, which
is concentrated in degree `m`, hence isomorphic to `Hᵐ(K)[m]`.

The upper degree is carried as a variable `m` with `n + 1 = m` rather than written `n + 1`, so
that a caller may instantiate it at a numeral. -/
theorem exists_distTriang_singleFunctor_homology_of_isIso_homologyMap (M : 𝒜)
    (K : DerivedCategory 𝒜) (n m : ℤ) (hm : n + 1 = m) [K.IsGE n] [K.IsLE m]
    (p : (DerivedCategory.singleFunctor 𝒜 n).obj M ⟶ K)
    (hp : IsIso ((DerivedCategory.homologyFunctor 𝒜 n).map p)) :
    ∃ (g : K ⟶ (DerivedCategory.singleFunctor 𝒜 m).obj
        ((DerivedCategory.homologyFunctor 𝒜 m).obj K))
      (h : (DerivedCategory.singleFunctor 𝒜 m).obj
          ((DerivedCategory.homologyFunctor 𝒜 m).obj K) ⟶
        ((DerivedCategory.singleFunctor 𝒜 n).obj M)⟦(1 : ℤ)⟧),
      Triangle.mk p g h ∈ distTriang (DerivedCategory 𝒜) := by
  subst hm
  set T := (DerivedCategory.TStructure.t (C := 𝒜)).triangleLTGE (n + 1) |>.obj K
  have hT : T ∈ distTriang (DerivedCategory 𝒜) :=
    DerivedCategory.TStructure.t.triangleLTGE_distinguished (n + 1) K
  have : T.obj₁.IsGE n := by
    change ((DerivedCategory.TStructure.t (C := 𝒜)).truncLT (n + 1)).obj K |>.IsGE n
    infer_instance
  have : T.obj₁.IsLE n := by
    change ((DerivedCategory.TStructure.t (C := 𝒜)).truncLT (n + 1)).obj K |>.IsLE n
    exact DerivedCategory.TStructure.t.isLE_truncLT_obj K (n + 1) n (by omega)
  have : T.obj₃.IsGE (n + 1) := by
    change ((DerivedCategory.TStructure.t (C := 𝒜)).truncGE (n + 1)).obj K |>.IsGE (n + 1)
    infer_instance
  have : T.obj₃.IsLE (n + 1) := by
    change ((DerivedCategory.TStructure.t (C := 𝒜)).truncGE (n + 1)).obj K |>.IsLE (n + 1)
    infer_instance
  obtain ⟨q, hq⟩ := T.coyoneda_exact₂ hT p
    (DerivedCategory.TStructure.t.zero (p ≫ T.mor₂) n (n + 1) (by omega))
  have : IsIso ((DerivedCategory.homologyFunctor 𝒜 n).map T.mor₁) :=
    DerivedCategory.isIso_homologyMap_truncLTι_app (n + 1) n (by omega) K
  have : IsIso ((DerivedCategory.homologyFunctor 𝒜 n).map q) := by
    have : IsIso ((DerivedCategory.homologyFunctor 𝒜 n).map q ≫
        (DerivedCategory.homologyFunctor 𝒜 n).map T.mor₁) := by
      rw [← Functor.map_comp, ← hq]
      exact hp
    exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor 𝒜 n).map T.mor₁)
  have : IsIso q := isIso_of_isIso_homologyMap_of_isGE_of_isLE n q
  have : IsIso ((DerivedCategory.homologyFunctor 𝒜 (n + 1)).map T.mor₂) :=
    DerivedCategory.isIso_homologyMap_truncGEπ_app (n + 1) (n + 1) le_rfl K
  set e₃ : T.obj₃ ≅ (DerivedCategory.singleFunctor 𝒜 (n + 1)).obj
      ((DerivedCategory.homologyFunctor 𝒜 (n + 1)).obj K) :=
    Classical.choice
        (DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor T.obj₃ (n + 1)) ≪≫
      (DerivedCategory.singleFunctor 𝒜 (n + 1)).mapIso
        (asIso ((DerivedCategory.homologyFunctor 𝒜 (n + 1)).map T.mor₂)).symm
  refine ⟨T.mor₂ ≫ e₃.hom, e₃.inv ≫ T.mor₃ ≫ (inv q)⟦(1 : ℤ)⟧',
    isomorphic_distinguished T hT _ ?_⟩
  refine Triangle.isoMk _ _ (asIso q) (Iso.refl _) e₃.symm ?_ ?_ ?_
  · change p ≫ 𝟙 K = q ≫ T.mor₁
    rw [Category.comp_id]
    exact hq
  · change (T.mor₂ ≫ e₃.hom) ≫ e₃.inv = 𝟙 K ≫ T.mor₂
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (Category.id_comp T.mor₂).symm
  · change (e₃.inv ≫ T.mor₃ ≫ (inv q)⟦(1 : ℤ)⟧') ≫ q⟦(1 : ℤ)⟧' = e₃.inv ≫ T.mor₃
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
    simp

end TwoDegrees

/-! ### Local duality: annihilating `Ext⁰` into a normalized dualizing complex -/

section LocalDuality

attribute [local instance] HasDerivedCategory.standard

/-- **A nonzero element annihilating `Ext⁰_A(H, ω_A^•)` annihilates `H`.** Let `(A, 𝔪, κ)` be a
Noetherian local ring with a normalized dualizing complex `ω_A^•`, let `H` be an `A`-module of
finite length and let `d ∈ A` annihilate `Ext⁰_A(H[0], ω_A^•)`. Then `d` annihilates `H`.

This is local duality ([Stacks, Tag 0AAK]) in the only form the proof of [Stacks, Tag 0B4S] uses
it, and it is assembled from two results already in the library: the Ext-level Matlis comparison
`Dualizing.exists_naturalMatlisExtComparison` ([Stacks, Tag 0A7Q]), which identifies
`Ext⁰_A(H[0], ω_A^•)` with the Matlis dual `Hom_A(H, E)` naturally in `H`, hence `A`-linearly;
and `Dualizing.smul_eq_zero_of_matlisDual_smul_eq_zero`, which carries the annihilation from the
Matlis dual to `H` because an injective hull of the residue field is a cogenerator.

The injective hull is produced rather than assumed, by [Stacks, Tag 08Y3],
`Module.exists_isInjectiveHull`. -/
theorem smul_eq_zero_of_smul_ext_into_normalizedDualizing_eq_zero (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA)
    (H : ModuleCat.{u} A) (hH : IsFiniteLength A H) (d : A)
    (hd : ∀ x : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj H) ωA 0, d • x = 0)
    (y : H) : d • y = 0 := by
  obtain ⟨E, i, hmono, hi⟩ :=
    Module.exists_isInjectiveHull A (Dualizing.residueFieldModule.{u, u} A)
  have : Mono i := hmono
  have : Mono (show (ModuleCat.uliftFunctor.{u, u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ ModuleCat.of A (E : Type u) from i) :=
    hmono
  obtain ⟨c⟩ := Dualizing.exists_naturalMatlisExtComparison.{u, u} A ωA hωA (E : Type u) i hi
  -- Precomposition on `Ext⁰` with multiplication by `d` is multiplication by `d`.
  have hprecomp : ∀ x : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (H : Type u)))
        ωA 0,
      Dualizing.extPrecomp (LinearMap.lsmul A (H : Type u) d) ωA 0 x = d • x := by
    have hmap : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (LinearMap.lsmul A (H : Type u) d)) =
        d • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (H : Type u))) := by
      have hcat : ModuleCat.ofHom (LinearMap.lsmul A (H : Type u) d) =
          d • 𝟙 (ModuleCat.of A (H : Type u)) := by
        apply ModuleCat.hom_ext
        ext m
        simp [LinearMap.lsmul_apply]
      rw [hcat, Functor.map_smul, CategoryTheory.Functor.map_id]
    intro x
    change (ShiftedHom.mk₀ 0 rfl
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (LinearMap.lsmul A (H : Type u) d)))).comp x (add_zero 0) = d • x
    rw [hmap, ShiftedHom.mk₀_smul, ShiftedHom.smul_comp, ShiftedHom.mk₀_id_comp]
  refine Dualizing.smul_eq_zero_of_matlisDual_smul_eq_zero.{u, u} A E i hi H d ?_ y
  intro φ
  obtain ⟨x, hx⟩ := (c.equiv (H : Type u) hH).surjective φ.hom
  have hlin : c.equiv (H : Type u) hH (d • x) = d • (c.equiv (H : Type u) hH x) := by
    rw [← hprecomp x, c.naturality (H : Type u) (H : Type u) hH hH
      (LinearMap.lsmul A (H : Type u) d) x]
    ext z
    exact map_smul (c.equiv (H : Type u) hH x) d z
  have key : d • φ.hom = 0 := by rw [← hx, ← hlin, hd x, map_zero]
  apply ModuleCat.hom_ext
  change d • φ.hom = (0 : H ⟶ E).hom
  rw [key]
  rfl

/-! ### The duality step, assembled -/

/-- **The duality step of [Stacks, Tag 0B4S].** Let `(A, 𝔪, κ)` be a Noetherian local ring with a
normalized dualizing complex `ω_A^•`, let `C` be an object of `D(A)` with cohomology only in the
degrees `-2` and `-1`, let `u : A[2] ⟶ C` be a morphism which is an isomorphism on `H^{-2}`, and
let `H` be `H^{-1}(C)`, of finite length. Assume

* `hvan`, that every morphism `C⟦-1⟧ ⟶ ω_A^•` vanishes, and
* `himage`, that for every `q : A[2] ⟶ ω_A^•` the morphism `d · q` factors through `u`.

Then `d` annihilates `H`.

Geometrically `C = RΓ(X, 𝒪_X)[2]` for a normal modification `f : X ⟶ Spec A`, `u` is the unit
`A ⟶ Rf_*𝒪_X` shifted, `H = H¹(X, 𝒪_X)`, `hvan` is Grauert-Riemenschneider vanishing
([Stacks, Tag 0AXD]) read through duality and `himage` says that `d · ω_A` lies in the image of
the trace `Γ(X, ω_X) ⟶ ω_A`.

The proof is the source's. The triangle `A[2] ⟶ C ⟶ H[1] ⟶ A[2][1]` of
`exists_distTriang_singleFunctor_homology_of_isIso_homologyMap` is inverse-rotated, and
`comp_smul_eq_zero_of_triangle_image` turns `hvan` and `himage` into the annihilation by `d` of
every morphism `H[0] ⟶ ω_A^•`, that is, of `Ext²_A(H, ω_A)`; local duality
(`smul_eq_zero_of_smul_ext_into_normalizedDualizing_eq_zero`) carries that annihilation to `H`
itself. -/
theorem smul_eq_zero_of_triangle_of_forall_hom_eq_zero (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA)
    (C : DerivedCategory (ModuleCat.{u} A)) [C.IsGE (-2)] [C.IsLE (-1)]
    (u : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj (ModuleCat.of A A) ⟶ C)
    (hu : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map u))
    (hH : IsFiniteLength A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj C))
    (d : A) (hvan : ∀ g : C⟦(-1 : ℤ)⟧ ⟶ ωA, g = 0)
    (himage : ∀ q : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj
        (ModuleCat.of A A) ⟶ ωA, ∃ r : C ⟶ ωA, u ≫ r = q ≫ (d • 𝟙 ωA))
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj C) : d • y = 0 := by
  obtain ⟨g, h, hT⟩ := exists_distTriang_singleFunctor_homology_of_isIso_homologyMap
    (ModuleCat.of A A) C (-2) (-1) (by norm_num) u hu
  set T : Triangle (DerivedCategory (ModuleCat.{u} A)) := Triangle.mk u g h
  have hzero := comp_smul_eq_zero_of_triangle_image T.invRotate
    (inv_rot_of_distTriang T hT) ωA (fun q => hvan q) (d • 𝟙 ωA) (fun q => himage q)
  refine smul_eq_zero_of_smul_ext_into_normalizedDualizing_eq_zero A ωA hωA _ hH d ?_ y
  intro x
  -- `H[0]` is `T.obj₃⟦-1⟧`, the first term of the inverse rotation, ...
  set ρ := ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-1) 0 (-1)
    (by norm_num)).app ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj C)
  -- ... and `Ext⁰` carries a trivial shift of the target.
  set z := (shiftFunctorZero (DerivedCategory (ModuleCat.{u} A)) ℤ).hom.app ωA
  have h1 : (ρ.hom ≫ x ≫ z) ≫ (d • 𝟙 ωA) = 0 := hzero _
  have h2 : ρ.hom ≫ (d • (x ≫ z)) = 0 := by
    simpa [Linear.comp_smul] using h1
  have h3 : d • (x ≫ z) = 0 := (cancel_epi ρ.hom).mp (by simpa using h2)
  have h4 : (d • x) ≫ z = 0 := by simpa [Linear.smul_comp] using h3
  exact (cancel_mono z).mp (by simpa using h4)

/-- **[Stacks, Tag 0B4S] granted the duality data of each normal modification.** Let `(A, 𝔪, κ)`
be a local normal Nagata domain of dimension two with a normalized dualizing complex `ω_A^•` and
let `d ∈ A` be nonzero. Suppose that for every modification `f : X ⟶ Spec A` with `X` normal
there are an object `C` of `D(A)` with cohomology in the degrees `-2` and `-1` only, a morphism
`u : A[2] ⟶ C` which is an isomorphism on `H^{-2}`, an identification of `H^{-1}(C)` with
`H¹(X, 𝒪_X)` making it of finite length, the vanishing of `Hom(C⟦-1⟧, ω_A^•)` and the
factorisation of `d · Hom(A[2], ω_A^•)` through `u`. Then reduction to rational singularities is
possible for `A`.

The intended `C` is `RΓ(X, 𝒪_X)[2]` and the intended `u` the unit `A ⟶ Rf_*𝒪_X`; see the module
documentation for what the five conditions are geometrically. The duality step
`smul_eq_zero_of_triangle_of_forall_hom_eq_zero` turns them into the annihilation of
`H¹(X, 𝒪_X)` by `d`, and
`isReductionToRationalSingularitiesPossible_of_forall_smul_firstCohomology_eq_zero` — which is
[Stacks, Tag 0B4S] downstream of the duality step, with the uniform length bound of
[Stacks, Tag 0AXJ] discharged — concludes. -/
theorem isReductionToRationalSingularitiesPossible_of_triangle_data (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A] (hdim : ringKrullDim A = 2)
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA) (d : A) (hd : d ≠ 0)
    (hdata : ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNormal X]
      (f : X ⟶ AlgebraicGeometry.Spec (.of A)), AlgebraicGeometry.IsModification f →
      ∃ (C : DerivedCategory (ModuleCat.{u} A)) (_ : C.IsGE (-2)) (_ : C.IsLE (-1))
        (u : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj (ModuleCat.of A A) ⟶ C),
        IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map u) ∧
        IsFiniteLength A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj C) ∧
        Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj C ≅
          AlgebraicGeometry.firstCohomologyAsBaseModule X f) ∧
        (∀ g : C⟦(-1 : ℤ)⟧ ⟶ ωA, g = 0) ∧
        ∀ q : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj
          (ModuleCat.of A A) ⟶ ωA, ∃ r : C ⟶ ωA, u ≫ r = q ≫ (d • 𝟙 ωA)) :
    AlgebraicGeometry.IsReductionToRationalSingularitiesPossible A := by
  have : IsNoetherianRing A := ‹IsNagataRing A›.1
  refine isReductionToRationalSingularitiesPossible_of_forall_smul_firstCohomology_eq_zero A hdim
    d hd fun X _ f hf x => ?_
  obtain ⟨C, hge, hle, u, hu, hH, ⟨e⟩, hvan, himage⟩ := hdata X f hf
  have := hge
  have := hle
  have hx : e.hom.hom (e.inv.hom x) = x := by simp
  rw [← hx, ← map_smul,
    smul_eq_zero_of_triangle_of_forall_hom_eq_zero A ωA hωA C u hu hH d hvan himage, map_zero]

end LocalDuality

end Stacks.ResolutionOfSurfaces

end
