module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleCoefficients
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat.CoefficientsExact

/-!
# The sign automorphism and the signed degree-raising map of `X[S]`

## Main definitions

* `SheafOfModules.coeffSignPiece` is the automorphism of `X[S]` which multiplies the summand of
  a generator of degree `j` by `(-1)^j`, and `SheafOfModules.coeffSignPieceIso` is it as an
  isomorphism.

## Main results

* `SheafOfModules.coeffPiece_exact_sign`: the short complex of pieces of `X[S]` twisted by the
  sign automorphism is exact as soon as the degreewise short complex of coefficients is.

## Implementation notes

The degrees do not line up on the nose, and this is where the work is. The summand of a generator
of degree `j` contributes `X^{n - j}` to `X[S]^n` and `X^{n + 1 - j}` to `X[S]^{n + 1}`, while the
differential of `X` carries it to `X^{n - j + 1}`; the two are equal integers but not
definitionally equal. The transport is isolated once, in `SheafOfModules.coeffCastPiece`, stated
for two reindexings of the coefficient degrees at once so that a single definition supplies every
cast needed here and its inverse, and the degree-raising map it assembles into is
`SheafOfModules.coeffSignDiffPiece`.

The `(-1)^{deg s}` in the differential is handled by the sign automorphism `σ` of `X[S]`, which
multiplies the summand of a degree-`j` generator by `(-1)^j`. It is an involution and commutes
with every map induced by the coefficients, so the components `(σ, 𝟙, σ)` are an isomorphism of
short complexes from the untwisted `(P, P')` to the twisted `(σ ≫ P, σ ≫ P')`. That isomorphism
is where the source's throwaway "the sign does not affect exactness" becomes a proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w t a m z v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### The sign automorphism of `X[S]`

The differential of `A[S] ⊗_A N` is, under the identification with `N[S]`, the differential of
`N` multiplied by `(-1)^{deg s}` on the summand of the generator `s`; the canonical generators of
`A[S]` are closed, so the Leibniz rule puts that sign there and nowhere else. The automorphism of
`X[S]` which multiplies the summand of a degree-`j` generator by `(-1)^j` is an involution and
commutes with every map induced by the coefficients, which is exactly what makes the twisted
short complex isomorphic to the untwisted one: with `σ` the automorphism, the components
`(σ, 𝟙, σ)` are an isomorphism from `(σ ≫ P, σ ≫ P')` to `(P, P')`. This is the source's "the
sign does not affect exactness". -/

section Sign

variable [HasWeakSheafify J (Type w)] (S : SheafOfGradedSets.{w} J)

section Presheaf

variable (X : ℤ → SheafOfModules.{a} R) {Y : ℤ → SheafOfModules.{a} R}

/-- The sign `(-1)^{deg s}` on the summand of `s` in the presentation of `X[S]`. -/
noncomputable def coeffSignAddHom (n : ℤ) (U : Cᵒᵖ) :
    coeffSections S X n U →+ coeffSections S X n U :=
  _root_.DirectSum.toAddMonoid fun p =>
    (_root_.DirectSum.of (fun q : S.Index U => ((X (n - q.1)).val.obj U : Type a)) p).comp
      (AddMonoidHom.mk' (fun x => (Int.negOnePow p.1 : ℤ) • x) fun x y => smul_add _ x y)

/-- The sign map multiplies the coefficient of a generator of degree `i` by `(-1)^i`. -/
@[simp] theorem coeffSignAddHom_coeffOf (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (x : (X (n - i)).val.obj U) :
    coeffSignAddHom S X n U (coeffOf S X n U i s hs x) =
      coeffOf S X n U i s hs ((Int.negOnePow i : ℤ) • x) :=
  _root_.DirectSum.toAddMonoid_of _ _ _

/-- The sign map on sections of the presentation of `X[S]` is `R`-linear. -/
theorem coeffSignAddHom_smul (n : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (m : coeffSections S X n U) :
    coeffSignAddHom S X n U (r • m) = r • coeffSignAddHom S X n U m := by
  induction m using coeffSections_induction with
  | hzero => rw [smul_zero, map_zero, smul_zero]
  | hof i s hs x =>
    rw [← coeffOf_smul, coeffSignAddHom_coeffOf, coeffSignAddHom_coeffOf, smul_comm,
      coeffOf_smul]
  | hadd m m' hm hm' => rw [smul_add, map_add, map_add, hm, hm', smul_add]

/-- The sign map on sections of the presentation of `X[S]` commutes with restriction. -/
theorem coeffSignAddHom_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (m : coeffSections S X n U) :
    coeffSignAddHom S X n V (coeffRestrict S X n f m) =
      coeffRestrict S X n f (coeffSignAddHom S X n U m) := by
  induction m using coeffSections_induction with
  | hzero => simp
  | hof i s hs x =>
    rw [coeffRestrict_coeffOf, coeffSignAddHom_coeffOf, coeffSignAddHom_coeffOf,
      coeffRestrict_coeffOf]
    exact coeffOf_congr S X n V i _ _ rfl
      (AddMonoidHom.map_zsmul (sectionRestrict (X (n - i)).val f) (Int.negOnePow i : ℤ) x).symm
  | hadd m m' hm hm' => rw [map_add, map_add, map_add, map_add, hm, hm']

/-- The sign automorphism of the presentation of `X[S]` in degree `n`. -/
noncomputable def coeffSignPres (n : ℤ) : coeffPres S X n ⟶ coeffPres S X n :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (coeffSignAddHom S X n U)
      naturality := fun {U V} f => by
        ext m; exact coeffSignAddHom_naturality S X n f m }
    fun U r m => coeffSignAddHom_smul S X n U r m

/-- The sign automorphism of the presentation is the sign map on sections. -/
@[simp] theorem coeffSignPres_app (n : ℤ) (U : Cᵒᵖ) (m : coeffSections S X n U) :
    (coeffSignPres S X n).app U m = coeffSignAddHom S X n U m := rfl

/-- The sign automorphism of the presentation is an involution: the sign of a given summand
squares to one. -/
theorem coeffSignPres_coeffSignPres (n : ℤ) :
    coeffSignPres S X n ≫ coeffSignPres S X n = 𝟙 (coeffPres S X n) := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  show coeffSignAddHom S X n U (coeffSignAddHom S X n U m) = m
  induction m using coeffSections_induction with
  | hzero => rw [map_zero, map_zero]
  | hof i s hs x =>
    rw [coeffSignAddHom_coeffOf, coeffSignAddHom_coeffOf, smul_smul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_smul]
  | hadd m m' hm hm' => rw [map_add, map_add, hm, hm']

/-- The sign automorphism commutes with the map induced by a morphism of the coefficients: the
sign depends only on the summand, which the induced map preserves. -/
theorem coeffSignPres_coeffPresMap (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) :
    coeffSignPres S X n ≫ coeffPresMap S g n = coeffPresMap S g n ≫ coeffSignPres S Y n := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  show coeffPresAddHom S g n U (coeffSignAddHom S X n U m) =
    coeffSignAddHom S Y n U (coeffPresAddHom S g n U m)
  induction m using coeffSections_induction with
  | hzero => simp
  | hof i s hs x =>
    rw [coeffSignAddHom_coeffOf, coeffPresAddHom_coeffOf, coeffPresAddHom_coeffOf,
      coeffSignAddHom_coeffOf]
    exact coeffOf_congr S Y n U i _ _ rfl
      (AddMonoidHom.map_zsmul (homSections (g (n - i)) U) (Int.negOnePow i : ℤ) x)
  | hadd m m' hm hm' => rw [map_add, map_add, map_add, map_add, hm, hm']

end Presheaf

section Sheafify

variable [HasSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  (X : ℤ → SheafOfModules.{a} R) {Y : ℤ → SheafOfModules.{a} R}

/-- **The sign automorphism of `X[S]` in degree `n`**: it multiplies the summand of a generator
of degree `j` by `(-1)^j`. -/
noncomputable def coeffSignPiece (n : ℤ) : coeffPiece S X n ⟶ coeffPiece S X n :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map (coeffSignPres S X n)

/-- The sign automorphism of `X[S]` is an involution. -/
theorem coeffSignPiece_coeffSignPiece (n : ℤ) :
    coeffSignPiece S X n ≫ coeffSignPiece S X n = 𝟙 (coeffPiece S X n) := by
  refine ((PresheafOfModules.sheafification (𝟙 R.obj)).map_comp _ _).symm.trans ?_
  rw [coeffSignPres_coeffSignPres]
  exact (PresheafOfModules.sheafification (𝟙 R.obj)).map_id _

/-- The sign automorphism of `X[S]` commutes with the map induced by a morphism of the
coefficients. -/
theorem coeffSignPiece_coeffPieceMap (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) :
    coeffSignPiece S X n ≫ coeffPieceMap S g n = coeffPieceMap S g n ≫ coeffSignPiece S Y n := by
  refine ((PresheafOfModules.sheafification (𝟙 R.obj)).map_comp _ _).symm.trans ?_
  rw [coeffSignPres_coeffPresMap]
  exact (PresheafOfModules.sheafification (𝟙 R.obj)).map_comp _ _

/-- The sign automorphism of `X[S]` in degree `n`, as an isomorphism. -/
noncomputable def coeffSignPieceIso (n : ℤ) : coeffPiece S X n ≅ coeffPiece S X n where
  hom := coeffSignPiece S X n
  inv := coeffSignPiece S X n
  hom_inv_id := coeffSignPiece_coeffSignPiece S X n
  inv_hom_id := coeffSignPiece_coeffSignPiece S X n

variable {Z : ℤ → SheafOfModules.{a} R}

/-- The two maps of the sign-twisted short complex compose to zero as soon as the untwisted ones
do: the sign automorphism is an involution and commutes with the untwisted maps. -/
theorem coeffSignPiece_comp_eq_zero (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k)
    (hgh : ∀ k : ℤ, g k ≫ h k = 0) (n : ℤ) :
    (coeffSignPiece S X n ≫ coeffPieceMap S g n) ≫
      (coeffSignPiece S Y n ≫ coeffPieceMap S h n) = 0 := by
  calc (coeffSignPiece S X n ≫ coeffPieceMap S g n) ≫
        (coeffSignPiece S Y n ≫ coeffPieceMap S h n)
      = coeffSignPiece S X n ≫ (coeffPieceMap S g n ≫ coeffSignPiece S Y n) ≫
          coeffPieceMap S h n := by simp only [Category.assoc]
    _ = (coeffSignPiece S X n ≫ coeffSignPiece S X n) ≫
          coeffPieceMap S g n ≫ coeffPieceMap S h n := by
        rw [← coeffSignPiece_coeffPieceMap]; simp only [Category.assoc]
    _ = 0 := by
        rw [coeffSignPiece_coeffSignPiece, Category.id_comp,
          coeffPieceMap_comp_eq_zero S g h hgh n]

/-- **The sign does not affect exactness.** The short complex of pieces of `X[S]` twisted by the
sign automorphism is isomorphic to the untwisted one, by the components `(σ, 𝟙, σ)`, so it is
exact as soon as the degreewise short complex of coefficients is. This is the step the source
leaves to the reader when it passes from `H^*(A[S] ⊗_A N)` to `H^*(N)[S]`. -/
theorem coeffPiece_exact_sign [HasSheafify J AddCommGrpCat.{a}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{a}] (g : ∀ k : ℤ, X k ⟶ Y k)
    (h : ∀ k : ℤ, Y k ⟶ Z k) (hgh : ∀ k : ℤ, g k ≫ h k = 0)
    (hex : ∀ k : ℤ, (ShortComplex.mk (g k) (h k) (hgh k)).Exact) (n : ℤ) :
    (ShortComplex.mk (coeffSignPiece S X n ≫ coeffPieceMap S g n)
      (coeffSignPiece S Y n ≫ coeffPieceMap S h n)
      (coeffSignPiece_comp_eq_zero S X g h hgh n)).Exact := by
  have e : ShortComplex.mk (coeffPieceMap S g n) (coeffPieceMap S h n)
        (coeffPieceMap_comp_eq_zero S g h hgh n) ≅
      ShortComplex.mk (coeffSignPiece S X n ≫ coeffPieceMap S g n)
        (coeffSignPiece S Y n ≫ coeffPieceMap S h n)
        (coeffSignPiece_comp_eq_zero S X g h hgh n) :=
    ShortComplex.isoMk (coeffSignPieceIso S X n) (Iso.refl _) (coeffSignPieceIso S Z n)
      (by
        show coeffSignPiece S X n ≫ coeffSignPiece S X n ≫ coeffPieceMap S g n =
          coeffPieceMap S g n ≫ 𝟙 _
        rw [← Category.assoc, coeffSignPiece_coeffSignPiece, Category.id_comp, Category.comp_id])
      (by
        show 𝟙 _ ≫ coeffSignPiece S Y n ≫ coeffPieceMap S h n =
          coeffPieceMap S h n ≫ coeffSignPiece S Z n
        rw [Category.id_comp]
        exact coeffSignPiece_coeffPieceMap S Y h n)
  exact ShortComplex.exact_of_iso e (coeffPiece_exact S g h hgh hex n)

end Sheafify

end Sign

/-! ### Tag 0FSG, condition (2) of Tag 0FSA: `A[S]` is K-flat

Under the identification `A[S] ⊗_A N = N[S]` the differential of the relative tensor product
becomes, on the summand of a generator `s`, the differential of `N` multiplied by
`(-1)^{deg s}`: the canonical generators of `A[S]` are closed, so the Leibniz rule puts the sign
there and nowhere else. Acyclicity of `A[S] ⊗_A N` is therefore the exactness, in every degree,
of a short complex of pieces of `N[S]` twisted by the sign automorphism, which is
`coeffPiece_exact_sign` applied to the acyclicity of `N`.

The degrees do not line up on the nose: the summand of a generator of degree `j` contributes
`N^{n - j}` to `N[S]^n` and `N^{n + 1 - j}` to `N[S]^{n + 1}`, while the differential of `N`
carries it to `N^{n - j + 1}`. The two are equal integers but not definitionally equal, so the
degree-raising map of `N[S]` is assembled with explicit transport along
`SheafOfModules.castHom`, as everything graded in this development is. The transport is isolated
in `SheafOfModules.coeffCastPiece`, which reindexes the coefficient degrees of `X[S]` and is an
isomorphism; it is what matches the three terms of the short complex computing the homology of
`A[S] ⊗_A N` in a single degree with the three coefficient families that
`coeffPiece_exact_sign` consumes at a single total degree. -/

section CoeffCast

variable [HasWeakSheafify J (Type w)] (S : SheafOfGradedSets.{w} J)
  (W : ℤ → SheafOfModules.{a} R)

/-- A summand of the presentation of `W[S]` is additive, hence commutes with integer
multiples. -/
theorem coeffOf_zsmul (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (c : ℤ) (x : (W (n - i)).val.obj U) :
    coeffOf S W n U i s hs (c • x) = c • coeffOf S W n U i s hs x :=
  AddMonoidHom.map_zsmul _ _ _

/-- **Transport of the presentation of `W[S]` along a reindexing of the coefficient degrees.**
For reindexings `f` and `f'` of the degrees which agree summand by summand, that is with
`f (n - j) = f' (n' - j)` for every `j`, the summand of a generator of degree `j` has the same
coefficients in degree `n` for `f` and in degree `n'` for `f'`, and this is the resulting map of
sections. -/
noncomputable def coeffCastAddHom (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) (U : Cᵒᵖ) :
    coeffSections S (fun k ↦ W (f k)) n U →+ coeffSections S (fun k ↦ W (f' k)) n' U :=
  _root_.DirectSum.toAddMonoid fun p ↦
    (_root_.DirectSum.of (fun q : S.Index U ↦ ((W (f' (n' - q.1))).val.obj U : Type a)) p).comp
      (castHom W (hf p.1) U)

/-- The transport of sections of the presentation of `W[S]` along a reindexing of the
coefficient degrees transports the coefficient of each generator. -/
@[simp] theorem coeffCastAddHom_coeffOf (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (x : (W (f (n - i))).val.obj U) :
    coeffCastAddHom S W f f' n n' hf U (coeffOf S (fun k ↦ W (f k)) n U i s hs x) =
      coeffOf S (fun k ↦ W (f' k)) n' U i s hs (castHom W (hf i) U x) :=
  _root_.DirectSum.toAddMonoid_of _ _ _

/-- The transport of sections of the presentation of `W[S]` along a reindexing of the
coefficient degrees is `R`-linear. -/
theorem coeffCastAddHom_smul (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) (U : Cᵒᵖ) (r : R.obj.obj U)
    (ξ : coeffSections S (fun k ↦ W (f k)) n U) :
    coeffCastAddHom S W f f' n n' hf U (r • ξ) =
      r • coeffCastAddHom S W f f' n n' hf U ξ := by
  induction ξ using coeffSections_induction with
  | hzero => rw [smul_zero, map_zero, smul_zero]
  | hof i s hs x =>
    rw [← coeffOf_smul, coeffCastAddHom_coeffOf, coeffCastAddHom_coeffOf, castHom_smul,
      coeffOf_smul]
  | hadd ξ ξ' hξ hξ' => rw [smul_add, map_add, map_add, hξ, hξ', smul_add]

/-- The transport of sections of the presentation of `W[S]` along a reindexing of the
coefficient degrees commutes with restriction. -/
theorem coeffCastAddHom_naturality (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) {U V : Cᵒᵖ} (g : U ⟶ V)
    (ξ : coeffSections S (fun k ↦ W (f k)) n U) :
    coeffCastAddHom S W f f' n n' hf V (coeffRestrict S (fun k ↦ W (f k)) n g ξ) =
      coeffRestrict S (fun k ↦ W (f' k)) n' g (coeffCastAddHom S W f f' n n' hf U ξ) := by
  induction ξ using coeffSections_induction with
  | hzero => rw [map_zero, map_zero, map_zero, map_zero]
  | hof i s hs x =>
    rw [coeffRestrict_coeffOf, coeffCastAddHom_coeffOf, coeffCastAddHom_coeffOf,
      coeffRestrict_coeffOf]
    exact coeffOf_congr S (fun k ↦ W (f' k)) n' V i _ _ rfl
      (sectionRestrict_castHom W (hf i) g x).symm
  | hadd ξ ξ' hξ hξ' => rw [map_add, map_add, map_add, map_add, hξ, hξ']

/-- The transport of the presentation of `W[S]` along a reindexing of the coefficient degrees is
inverse to the transport along the reversed reindexing: on each summand it is a transport of
sections along an equality of degrees and its inverse. -/
theorem coeffCastAddHom_coeffCastAddHom (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) (U : Cᵒᵖ)
    (ξ : coeffSections S (fun k ↦ W (f k)) n U) :
    coeffCastAddHom S W f' f n' n (fun j ↦ (hf j).symm) U
        (coeffCastAddHom S W f f' n n' hf U ξ) = ξ := by
  induction ξ using coeffSections_induction with
  | hzero => rw [map_zero, map_zero]
  | hof i s hs x =>
    rw [coeffCastAddHom_coeffOf, coeffCastAddHom_coeffOf]
    exact coeffOf_congr S (fun k ↦ W (f k)) n U i _ _ rfl
      ((Cofree.castHom_castHom W (hf i) (hf i).symm U x).trans (castHom_rfl W U x))
  | hadd ξ ξ' hξ hξ' => rw [map_add, map_add, hξ, hξ']

/-- Transport along a reindexing of the coefficient degrees, as a morphism of the
presentations. -/
noncomputable def coeffCastPres (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) :
    coeffPres S (fun k ↦ W (f k)) n ⟶ coeffPres S (fun k ↦ W (f' k)) n' :=
  PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (coeffCastAddHom S W f f' n n' hf U)
      naturality := fun {_ _} g ↦ by
        ext ξ; exact coeffCastAddHom_naturality S W f f' n n' hf g ξ }
    fun U r ξ ↦ coeffCastAddHom_smul S W f f' n n' hf U r ξ

/-- The transport of the presentation of `W[S]` is the transport of sections. -/
@[simp] theorem coeffCastPres_app (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) (U : Cᵒᵖ)
    (ξ : coeffSections S (fun k ↦ W (f k)) n U) :
    (coeffCastPres S W f f' n n' hf).app U ξ = coeffCastAddHom S W f f' n n' hf U ξ := rfl

end CoeffCast

section CoeffCastSheafify

variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}] (S : SheafOfGradedSets.{w} J)
  (W : ℤ → SheafOfModules.{a} R)

/-- A sheafified morphism of presentations of free graded modules with coefficients, read on the
image of the canonical morphism from the presentation. -/
theorem sheafifyCoeffPres_coeffUnit {V V' : ℤ → SheafOfModules.{a} R} {n n' : ℤ}
    (φ : coeffPres S V n ⟶ coeffPres S V' n') (U : Cᵒᵖ) (ζ : (coeffPres S V n).obj U) :
    ((PresheafOfModules.sheafification (𝟙 R.obj)).map φ).val.app U
        ((coeffUnit S V n).app U ζ) = (coeffUnit S V' n').app U (φ.app U ζ) :=
  PresheafOfModules.unit_naturality_apply (α := 𝟙 R.obj) (φ := φ) U ζ

/-- The canonical morphism from the presentation of `W[S]^n` commutes with integer multiples. -/
theorem coeffUnit_zsmul (n : ℤ) (U : Cᵒᵖ) (c : ℤ) (ξ : coeffSections S W n U) :
    (coeffUnit S W n).app U (c • ξ) = c • (coeffUnit S W n).app U ξ :=
  AddMonoidHom.map_zsmul ((coeffUnit S W n).app U).hom.toAddMonoidHom c ξ

/-- **Transport of `W[S]` along a reindexing of the coefficient degrees.** -/
noncomputable def coeffCastPiece (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) :
    coeffPiece S (fun k ↦ W (f k)) n ⟶ coeffPiece S (fun k ↦ W (f' k)) n' :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map (coeffCastPres S W f f' n n' hf)

/-- On the image of the canonical morphism from the presentation, the transport of `W[S]` is
the transport of sections of the presentation. -/
theorem coeffCastPiece_coeffUnit (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) (U : Cᵒᵖ)
    (ζ : (coeffPres S (fun k ↦ W (f k)) n).obj U) :
    (coeffCastPiece S W f f' n n' hf).val.app U ((coeffUnit S (fun k ↦ W (f k)) n).app U ζ) =
      (coeffUnit S (fun k ↦ W (f' k)) n').app U (coeffCastAddHom S W f f' n n' hf U ζ) :=
  sheafifyCoeffPres_coeffUnit S (coeffCastPres S W f f' n n' hf) U ζ

/-- The transport of `W[S]` along a reindexing of the coefficient degrees is inverse to the
transport along the reversed reindexing. -/
theorem coeffCastPiece_coeffCastPiece (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) :
    coeffCastPiece S W f f' n n' hf ≫ coeffCastPiece S W f' f n' n (fun j ↦ (hf j).symm) =
      𝟙 (coeffPiece S (fun k ↦ W (f k)) n) := by
  refine coeffPiece_hom_ext S fun U ζ ↦ ?_
  refine Eq.trans (congrArg
    (fun z ↦ (coeffCastPiece S W f' f n' n (fun j ↦ (hf j).symm)).val.app U z)
    (coeffCastPiece_coeffUnit S W f f' n n' hf U ζ)) ?_
  refine (coeffCastPiece_coeffUnit S W f' f n' n (fun j ↦ (hf j).symm) U _).trans ?_
  exact congrArg (fun z ↦ (coeffUnit S (fun k ↦ W (f k)) n).app U z)
    (coeffCastAddHom_coeffCastAddHom S W f f' n n' hf U ζ)

/-- **Transport of `W[S]` along a reindexing of the coefficient degrees is an isomorphism.** -/
noncomputable def coeffCastPieceIso (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) :
    coeffPiece S (fun k ↦ W (f k)) n ≅ coeffPiece S (fun k ↦ W (f' k)) n' where
  hom := coeffCastPiece S W f f' n n' hf
  inv := coeffCastPiece S W f' f n' n (fun j ↦ (hf j).symm)
  hom_inv_id := coeffCastPiece_coeffCastPiece S W f f' n n' hf
  inv_hom_id := coeffCastPiece_coeffCastPiece S W f' f n' n (fun j ↦ (hf j).symm)

/-- The forward morphism of `coeffCastPieceIso` is `coeffCastPiece`. -/
@[simp] theorem coeffCastPieceIso_hom (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) :
    (coeffCastPieceIso S W f f' n n' hf).hom = coeffCastPiece S W f f' n n' hf := rfl

/-- The inverse of `coeffCastPieceIso` is the transport along the reversed reindexing. -/
@[simp] theorem coeffCastPieceIso_inv (f f' : ℤ → ℤ) (n n' : ℤ)
    (hf : ∀ j : ℤ, f (n - j) = f' (n' - j)) :
    (coeffCastPieceIso S W f f' n n' hf).inv =
      coeffCastPiece S W f' f n' n (fun j ↦ (hf j).symm) := rfl

end CoeffCastSheafify

/-! ### The signed degree-raising map of `W[S]`

For a differential on the coefficients, given as a family of maps indexed by pairs of degrees as
`HomologicalComplex.d` is, the summand of a generator of degree `j` of `W[S]^n` is carried to the
summand of the same generator of `W[S]^{n+1}`, multiplied by `(-1)^j` and transported from degree
`n - j + 1` to degree `n + 1 - j`. This is the map which the differential of `A[S] ⊗_A N` becomes
under the identification with `N[S]`. -/

section SignDiff

/-- Transport commutes with a map of the coefficients: both sides are the same map of sections
once the two equalities of degrees are substituted. -/
theorem homSections_castHom (W : ℤ → SheafOfModules.{a} R) (e : ∀ k k' : ℤ, W k ⟶ W k')
    {i i' j j' : ℤ} (hi : i = i') (hj : j = j') (U : Cᵒᵖ) (x : (W i).val.obj U) :
    homSections (e i' j') U (castHom W hi U x) =
      castHom W hj U (homSections (e i j) U x) := by
  subst hi hj
  rfl

variable [HasWeakSheafify J (Type w)] (S : SheafOfGradedSets.{w} J)
  (W : ℤ → SheafOfModules.{a} R) (e : ∀ k k' : ℤ, W k ⟶ W k')

/-- The signed degree-raising map on sections of the presentation of `W[S]`. -/
noncomputable def coeffSignDiffAddHom (n : ℤ) (U : Cᵒᵖ) :
    coeffSections S W n U →+ coeffSections S W (n + 1) U :=
  (coeffCastAddHom S W (fun k ↦ k + 1) (fun k ↦ k) n (n + 1) (fun j ↦ by omega) U).comp
    ((coeffPresAddHom S (X := W) (Y := fun k ↦ W (k + 1))
      (fun k ↦ e k (k + 1)) n U).comp (coeffSignAddHom S W n U))

/-- The signed degree-raising map carries the coefficient `x` of a generator of degree `i` to
`(-1)^i` times the image of `x` under the differential, transported to degree `n + 1 - i`. -/
@[simp] theorem coeffSignDiffAddHom_coeffOf (n : ℤ) (U : Cᵒᵖ) (i : ℤ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s i) (x : (W (n - i)).val.obj U) :
    coeffSignDiffAddHom S W e n U (coeffOf S W n U i s hs x) =
      coeffOf S W (n + 1) U i s hs ((Int.negOnePow i : ℤ) •
        castHom W (show n - i + 1 = n + 1 - i by omega) U
          (homSections (e (n - i) (n - i + 1)) U x)) := by
  show coeffCastAddHom S W (fun k ↦ k + 1) (fun k ↦ k) n (n + 1) (fun j ↦ by omega) U
      (coeffPresAddHom S (X := W) (Y := fun k ↦ W (k + 1)) (fun k ↦ e k (k + 1)) n U
        (coeffSignAddHom S W n U (coeffOf S W n U i s hs x))) = _
  rw [coeffSignAddHom_coeffOf, coeffPresAddHom_coeffOf, coeffCastAddHom_coeffOf,
    AddMonoidHom.map_zsmul, AddMonoidHom.map_zsmul]

/-- The signed degree-raising map of the presentation of `W[S]`. -/
noncomputable def coeffSignDiffPres (n : ℤ) :
    coeffPres S W n ⟶ coeffPres S W (n + 1) :=
  coeffSignPres S W n ≫
    coeffPresMap S (X := W) (Y := fun k ↦ W (k + 1)) (fun k ↦ e k (k + 1)) n ≫
      coeffCastPres S W (fun k ↦ k + 1) (fun k ↦ k) n (n + 1) (fun j ↦ by omega)

/-- The signed degree-raising map of the presentation is the signed degree-raising map on
sections. -/
@[simp] theorem coeffSignDiffPres_app (n : ℤ) (U : Cᵒᵖ) (ξ : coeffSections S W n U) :
    (coeffSignDiffPres S W e n).app U ξ = coeffSignDiffAddHom S W e n U ξ := rfl

/-- **The signed degree-raising map of the presentation of `W[S]`, read as a map of the
coefficients of the previous degree.** Transporting the coefficients of degree `m` into the
summandwise degrees of total degree `m + 1` turns the signed degree-raising map into the map
induced by the differential on the shifted coefficients. -/
theorem coeffCastPres_coeffSignDiffPres (m : ℤ) :
    coeffCastPres S W (fun k ↦ k) (fun k ↦ k - 1) m (m + 1) (fun j ↦ by omega) ≫
        coeffSignPres S (fun k ↦ W (k - 1)) (m + 1) ≫
          coeffPresMap S (X := fun k ↦ W (k - 1)) (Y := W)
            (fun k ↦ e (k - 1) k) (m + 1) =
      coeffSignDiffPres S W e m := by
  refine PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun ζ ↦ ?_)
  show coeffPresAddHom S (fun k ↦ e (k - 1) k) (m + 1) U
      (coeffSignAddHom S (fun k ↦ W (k - 1)) (m + 1) U
        (coeffCastAddHom S W (fun k ↦ k) (fun k ↦ k - 1) m (m + 1)
          (fun j ↦ by omega) U ζ)) =
    coeffSignDiffAddHom S W e m U ζ
  induction ζ using coeffSections_induction with
  | hzero => rw [map_zero, map_zero, map_zero, map_zero]
  | hof i s hs x =>
    rw [coeffCastAddHom_coeffOf, coeffSignAddHom_coeffOf, coeffPresAddHom_coeffOf,
      coeffSignDiffAddHom_coeffOf]
    refine coeffOf_congr S W (m + 1) U i _ _ rfl ?_
    rw [AddMonoidHom.map_zsmul]
    exact congrArg (fun z ↦ (Int.negOnePow i : ℤ) • z)
      (homSections_castHom W e (show m - i = m + 1 - i - 1 by omega)
        (show m - i + 1 = m + 1 - i by omega) U x)
  | hadd ζ ζ' hζ hζ' => rw [map_add, map_add, map_add, map_add, hζ, hζ']

end SignDiff

section SignDiffSheafify

variable [HasWeakSheafify J (Type w)] [HasSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}] (S : SheafOfGradedSets.{w} J)
  (W : ℤ → SheafOfModules.{a} R) (e : ∀ k k' : ℤ, W k ⟶ W k')

/-- **The signed degree-raising map of `W[S]`**: on the summand of a generator of degree `j` it
is `(-1)^j` times the map induced by the differential of the coefficients, transported from
degree `n - j + 1` to degree `n + 1 - j`. -/
noncomputable def coeffSignDiffPiece (n : ℤ) :
    coeffPiece S W n ⟶ coeffPiece S W (n + 1) :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map (coeffSignDiffPres S W e n)

/-- On the image of the canonical morphism from the presentation, the signed degree-raising
map of `W[S]` is the signed degree-raising map on sections of the presentation. -/
theorem coeffSignDiffPiece_coeffUnit (n : ℤ) (U : Cᵒᵖ) (ζ : (coeffPres S W n).obj U) :
    (coeffSignDiffPiece S W e n).val.app U ((coeffUnit S W n).app U ζ) =
      (coeffUnit S W (n + 1)).app U (coeffSignDiffAddHom S W e n U ζ) :=
  sheafifyCoeffPres_coeffUnit S (coeffSignDiffPres S W e n) U ζ

/-- The signed degree-raising map of `W[S]` is the sign automorphism, followed by the map induced
by the differential of the coefficients, followed by the transport of the degrees. -/
theorem coeffSignDiffPiece_eq (n : ℤ) :
    coeffSignDiffPiece S W e n =
      coeffSignPiece S W n ≫
        coeffPieceMap S (X := W) (Y := fun k ↦ W (k + 1)) (fun k ↦ e k (k + 1)) n ≫
          coeffCastPiece S W (fun k ↦ k + 1) (fun k ↦ k) n (n + 1) (fun j ↦ by omega) := by
  rw [coeffSignDiffPiece, coeffSignDiffPres, Functor.map_comp, Functor.map_comp]
  rfl

/-- **The signed degree-raising map of `W[S]`, read as a map of the coefficients of the previous
degree**: this is `coeffCastPres_coeffSignDiffPres` after sheafification. -/
theorem coeffCastPiece_coeffSignDiffPiece (m : ℤ) :
    coeffCastPiece S W (fun k ↦ k) (fun k ↦ k - 1) m (m + 1) (fun j ↦ by omega) ≫
        coeffSignPiece S (fun k ↦ W (k - 1)) (m + 1) ≫
          coeffPieceMap S (X := fun k ↦ W (k - 1)) (Y := W)
            (fun k ↦ e (k - 1) k) (m + 1) =
      coeffSignDiffPiece S W e m := by
  refine Eq.trans ?_ (congrArg (fun φ ↦ (PresheafOfModules.sheafification (𝟙 R.obj)).map φ)
    (coeffCastPres_coeffSignDiffPres S W e m))
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-- **The signed degree-raising map of `W[S]`, read as a map of the coefficients of its own
degree**: transporting the target back into the summandwise degrees of total degree `n` undoes
the transport the degree-raising map carries, and leaves the map induced by the differential on
the shifted coefficients. -/
theorem coeffSignDiffPiece_coeffCastPiece (n : ℤ) :
    coeffSignDiffPiece S W e n ≫
        coeffCastPiece S W (fun k ↦ k) (fun k ↦ k + 1) (n + 1) n (fun j ↦ by omega) =
      coeffSignPiece S W n ≫
        coeffPieceMap S (X := W) (Y := fun k ↦ W (k + 1)) (fun k ↦ e k (k + 1)) n := by
  rw [coeffSignDiffPiece_eq, Category.assoc, Category.assoc, coeffCastPiece_coeffCastPiece,
    Category.comp_id]

end SignDiffSheafify

end SheafOfModules

end
