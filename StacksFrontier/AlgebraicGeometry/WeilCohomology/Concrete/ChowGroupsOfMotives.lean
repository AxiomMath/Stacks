module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Motives

/-!
# Chow groups of Chow motives, and their representability

Let `k` be a field. Stacks Definition 0FGL defines the `i`th Chow group of a Chow motive
`M = (X, p, m)` over `k` as

  `CH^i(M) = p(CH^{i+m}(X) ⊗ ℚ)`,

the image of the pushforward along the projector `p ∈ Corr⁰(X, X)`. A morphism of motives
`c : (X, p, m) ⟶ (Y, q, n)` is a correspondence `c ∈ Corr^{n-m}(X, Y)` with `c = q ∘ c ∘ p`,
and pushforward along it maps `CH^i(M)` to `CH^i(N)`; Stacks 0FG0 makes this a functor
`CH^i(-) : M_k ⥤ ℚ-vector spaces`. Stacks 0FGM says that this functor is representable by the
Tate motive `𝟏(-i) = (Spec k, 1, -i)`:

  `CH^i(M) = Hom_{M_k}(𝟏(-i), M)`, functorially in `M`.

The proof is the source's: a morphism `𝟏(-i) ⟶ (X, p, m)` is a correspondence of degree
`m - (-i) = i + m` from `Spec k` to `X` fixed by `p`, by Stacks 0FG0 (3) such a correspondence
is a class `α ∈ CH^{i+m}(X) ⊗ ℚ` (`Stacks.WeilCohomology.corrFromPointEquiv`), and under that
identification composing with `p` is pushing forward along `p`
(`Stacks.WeilCohomology.corrFromPointEquiv_pushforward_canonicalDiagonalClassFamily`).

Everything is about the actual objects: the motives are those of
`Stacks.WeilCohomology.ChowMotiveCat k`, whose correspondences are the rational Chow groups of
the products `X × Y`, composed by `pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` with the canonical Gysin
classes of the diagonals; the pushforward `c_*(α) = pr₂,*(c · pr₁^* α)` is
`Stacks.WeilCohomology.pushforward`, of Section 0FFZ.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.totalPushforward`: pushforward by correspondences
  on total rational Chow groups `CH^*(X) ⊗ ℚ`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.totalChowEquiv`: Stacks 0FG0 (3) in all degrees,
  `CH^*(X) ⊗ ℚ = ⨁ᵣ Corrʳ(Spec k, X)`.
* `Stacks.WeilCohomology.ChowMotiveCat.chowGroup`: **Definition 0FGL**, `CH^i(M)`.
* `Stacks.WeilCohomology.ChowMotiveCat.chowMap`: the map `c_* : CH^i(M) ⟶ CH^i(N)` induced by a
  morphism of motives `c : M ⟶ N`.
* `Stacks.WeilCohomology.ChowMotiveCat.chowFunctor`: the functor `CH^i(-)`.
* `Stacks.WeilCohomology.ChowMotiveCat.chowGroupEquivHom`: **Stacks 0FGM**,
  `CH^i(M) ≃ₗ[ℚ] Hom_{M_k}(𝟏(-i), M)`.
* `Stacks.WeilCohomology.ChowMotiveCat.chowFunctorIso`: **Stacks 0FGM**, the isomorphism of
  functors `CH^i(-) ≅ Hom_{M_k}(𝟏(-i), -)`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.totalChowEquiv_totalPushforward`: pushforward by
  a correspondence corresponds to composition with it (Stacks 0FG0 (3)).
* `Stacks.WeilCohomology.ChowMotiveCat.mem_chowGroup_iff`: `α ∈ CH^i(X, p, m)` exactly when the
  correspondence `α` from `Spec k` is fixed by `p`.
* `Stacks.WeilCohomology.ChowMotiveCat.chowMap_id`, `...chowMap_comp`: `CH^i(-)` is a functor.
* `Stacks.WeilCohomology.ChowMotiveCat.chowGroup_h_obj`: `CH^i(h(X)) = CH^i(X) ⊗ ℚ`.
* `Stacks.WeilCohomology.ChowMotiveCat.chowGroupEquivHom_naturality`: **Stacks 0FGM**, the
  identification carries `c_*` to postcomposition with `c`.

## Implementation notes

`CH^i(M)` is a submodule of `CH^{i+m}(X) ⊗ ℚ = ⨁_d CH_{d-(i+m)}(X_d) ⊗ ℚ`
(`Stacks.WeilCohomology.CodimChow`), which is the codimension grading on the possibly
non-equidimensional `X`. Pushing forward along `c ∈ Corr^{n-m}(X, Y)` lands in codimension
`(i + m) + (n - m)`, which is `i + n` only propositionally; the transport
`Stacks.WeilCohomology.codimChowCongr` identifies the two, and reading classes in the total Chow
group `⨁ᵢ CH^i(X) ⊗ ℚ` makes it disappear (`of_codimChowCongr`).

## References

* [Stacks Project, Tag 0FGM](https://stacks.math.columbia.edu/tag/0FGM)
* [Stacks Project, Tag 0FGL](https://stacks.math.columbia.edu/tag/0FGL)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.GradedCategory

universe w v u' u

namespace CategoryTheory

variable (R : Type w) [Ring R] {C : Type u'} [Category.{v} C] [Preadditive C] [Linear R C]

/-- A functor `F` to `R`-modules together with `R`-linear identifications `F(X) ≃ Hom(L, X)`,
natural in `X`, is isomorphic to the linear co-Yoneda functor `Hom(L, -)` of `L`. -/
def linearCoyonedaObjIsoOfLinearEquiv (L : C) (F : C ⥤ ModuleCat.{v} R)
    (e : ∀ X, F.obj X ≃ₗ[R] (L ⟶ X))
    (he : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X), e Y (F.map f x) = e X x ≫ f) :
    F ≅ (linearCoyoneda R C).obj (Opposite.op L) :=
  NatIso.ofComponents (fun X ↦ (e X).toModuleIso) fun {X Y} f ↦ by
    ext x
    exact he f x

end CategoryTheory

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-! ### Pushforward by correspondences on total Chow groups -/

namespace SmoothProjectiveScheme

/-- The total rational Chow group `CH^*(X) ⊗ ℚ = ⨁ᵢ CH^i(X) ⊗ ℚ` of a smooth projective scheme
`X` over `k`, graded by codimension. -/
abbrev TotalChow (X : (SmoothProjectiveScheme k).FullSubcategory) : Type u :=
  DirectSum ℤ fun i ↦ CodimChow k X.obj.hom i

/-- Pushforward by correspondences on total rational Chow groups: a correspondence
`c ∈ Corrʳ(X, Y)` acts on `CH^i(X) ⊗ ℚ` by the pushforward `c_*(α) = pr₂,*(c · pr₁^* α)` of
Section 0FFZ, landing in `CH^{i+r}(Y) ⊗ ℚ`, and a morphism `⨁ᵣ Corrʳ(X, Y)` of the category of
correspondences acts by the sum of its homogeneous pieces. -/
def totalPushforward (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    TotalCorrespondence (fun P Q r ↦ SmoothProjectiveCorr P Q r) X Y →ₗ[ℚ]
      TotalChow X →ₗ[ℚ] TotalChow Y :=
  DirectSum.toModule ℚ ℤ _ fun r ↦
    ((DirectSum.toModule ℚ ℤ _ fun i ↦
      (((pushforward k X.obj.hom Y.obj.hom (canonicalDiagonalClassFamily k) r i).compr₂
        (DirectSum.lof ℚ ℤ (fun j ↦ CodimChow k Y.obj.hom j) (i + r))).comp
          (SmoothProjectiveCorr.toCorr X Y r).toLinearMap).flip).flip)

/-- Pushforward of a homogeneous class `α ∈ CH^i(X) ⊗ ℚ` by a homogeneous correspondence
`c ∈ Corrʳ(X, Y)` is the class `c_*(α) ∈ CH^{i+r}(Y) ⊗ ℚ` in the total Chow group. -/
theorem totalPushforward_of_of (X Y : (SmoothProjectiveScheme k).FullSubcategory) (r i : ℤ)
    (c : SmoothProjectiveCorr X Y r) (α : CodimChow k X.obj.hom i) :
    totalPushforward X Y (DirectSum.of (fun r ↦ SmoothProjectiveCorr X Y r) r c)
        (DirectSum.of (fun i ↦ CodimChow k X.obj.hom i) i α) =
      DirectSum.of (fun j ↦ CodimChow k Y.obj.hom j) (i + r)
        (pushforward k X.obj.hom Y.obj.hom (canonicalDiagonalClassFamily k) r i
          (SmoothProjectiveCorr.toCorr X Y r c) α) := by
  simp only [← DirectSum.lof_eq_of ℚ]
  simp [totalPushforward]

/-- The identification `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)` of Stacks 0FG0 (3)
(`Stacks.WeilCohomology.corrFromPointEquiv`), with `Spec k` read as the unit
`𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)` of the category of smooth projective schemes. -/
def pointCorrEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) :
    CodimChow k X.obj.hom r ≃ₗ[ℚ] SmoothProjectiveCorr
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) X r :=
  (corrFromPointEquiv k X.obj.hom r).trans
    (SmoothProjectiveCorr.toCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) X r).symm

/-- **Stacks Project, Tag 0FG0 (3)**, in every degree at once: the identification
`CH^*(X) ⊗ ℚ = ⨁ᵣ Corrʳ(Spec k, X)`, which is `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)`
(`Stacks.WeilCohomology.corrFromPointEquiv`) on each homogeneous piece. Its target is the space of
morphisms from `Spec k` to `X` in the category of correspondences. -/
def totalChowEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) :
    TotalChow X ≃ₗ[ℚ]
      TotalCorrespondence (fun P Q r ↦ SmoothProjectiveCorr P Q r)
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) X :=
  DirectSum.congrLinearEquiv fun r ↦ pointCorrEquiv X r

/-- On a homogeneous class `α ∈ CH^r(X) ⊗ ℚ`, `totalChowEquiv` is the correspondence
`pointCorrEquiv X r α ∈ Corrʳ(Spec k, X)` in degree `r`. -/
theorem totalChowEquiv_of (X : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ)
    (α : CodimChow k X.obj.hom r) :
    totalChowEquiv X (DirectSum.of (fun i ↦ CodimChow k X.obj.hom i) r α) =
      DirectSum.of
          (fun r ↦ SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) X r) r
        (pointCorrEquiv X r α) := by
  simp only [← DirectSum.lof_eq_of ℚ]
  simp [totalChowEquiv, DirectSum.coe_congrLinearEquiv]

/-- The homogeneous form of the second half of Stacks 0FG0 (3): for `c ∈ Corrʳ(X, Y)` and
`α ∈ CH^i(X) ⊗ ℚ`, the correspondence from `Spec k` corresponding to `c_*(α)` is `c ∘ α`. -/
theorem pointCorrEquiv_pushforward (X Y : (SmoothProjectiveScheme k).FullSubcategory) (i r : ℤ)
    (c : SmoothProjectiveCorr X Y r) (α : CodimChow k X.obj.hom i) :
    pointCorrEquiv Y (i + r) (pushforward k X.obj.hom Y.obj.hom
        (canonicalDiagonalClassFamily k) r i (SmoothProjectiveCorr.toCorr X Y r c) α) =
      (canonicalCorrespondenceCompositionData k).comp (pointCorrEquiv X i α) c := by
  simp only [pointCorrEquiv, LinearEquiv.trans_apply]
  apply (SmoothProjectiveCorr.toCorr _ Y (i + r)).injective
  rw [LinearEquiv.apply_symm_apply, toCorr_correspondenceCompositionData_comp,
    LinearEquiv.apply_symm_apply]
  refine (corrFromPointEquiv_pushforward_canonicalDiagonalClassFamily X.obj.hom Y.obj.hom i r
    (SmoothProjectiveCorr.toCorr X Y r c) α).trans ?_
  rfl

/-- **Pushforward by correspondences corresponds to composition** (Stacks 0FG0 (3)), on total
groups: under `CH^*(-) ⊗ ℚ = ⨁ᵣ Corrʳ(Spec k, -)`, the class `c_*(α)` corresponds to the
composite `c ∘ α` of `c` with the correspondence `α` from `Spec k`. -/
theorem totalChowEquiv_totalPushforward (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (a : TotalCorrespondence (fun P Q r ↦ SmoothProjectiveCorr P Q r) X Y) (x : TotalChow X) :
    totalChowEquiv Y (totalPushforward X Y a x) =
      (canonicalCorrespondenceCompositionData k).compLinear _ X Y (totalChowEquiv X x) a := by
  induction a using DirectSum.induction_on with
  | zero =>
    simp only [LinearMap.map_zero, LinearMap.zero_apply, LinearEquiv.map_zero]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | of r c =>
    induction x using DirectSum.induction_on with
    | zero =>
      simp only [LinearMap.map_zero, LinearMap.zero_apply, LinearEquiv.map_zero]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | of i α =>
      rw [totalPushforward_of_of, totalChowEquiv_of, totalChowEquiv_of,
        GradedCompositionData.compLinear_of_of, pointCorrEquiv_pushforward]

/-- Pushforward by correspondences is functorial: `(b ∘ a)_* = b_* ∘ a_*` (Stacks 0FG0 (4)). -/
theorem totalPushforward_compLinear (X Y Z : (SmoothProjectiveScheme k).FullSubcategory)
    (a : TotalCorrespondence (fun P Q r ↦ SmoothProjectiveCorr P Q r) X Y)
    (b : TotalCorrespondence (fun P Q r ↦ SmoothProjectiveCorr P Q r) Y Z) (x : TotalChow X) :
    totalPushforward X Z ((canonicalCorrespondenceCompositionData k).compLinear X Y Z a b) x =
      totalPushforward Y Z b (totalPushforward X Y a x) := by
  apply (totalChowEquiv Z).injective
  rw [totalChowEquiv_totalPushforward, totalChowEquiv_totalPushforward,
    totalChowEquiv_totalPushforward, GradedCompositionData.compLinear_assoc]

/-- Pushforward by the diagonal `[Δ] ∈ Corr⁰(X, X)` is the identity. -/
theorem totalPushforward_diagonal (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : TotalChow X) :
    totalPushforward X X (DirectSum.of (fun r ↦ SmoothProjectiveCorr X X r) 0
      ((canonicalCorrespondenceCompositionData k).diagonal X)) x = x := by
  apply (totalChowEquiv X).injective
  rw [totalChowEquiv_totalPushforward, GradedCompositionData.compLinear_diagonal]


/-- Transport of rational Chow classes along `i = i` is the identity. -/
theorem codimChowCongr_self (X : (SmoothProjectiveScheme k).FullSubcategory) {i : ℤ} (h : i = i)
    (x : CodimChow k X.obj.hom i) : codimChowCongr k X.obj.hom h x = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, ha, hb]
  | of d a => rw [← DirectSum.lof_eq_of ℚ, codimChowCongr_lof, baseChange_chowGroupDegreeEquiv_self]

/-- Transport of rational Chow classes along an equality of codimensions, read in the total
Chow group, is the identity. -/
theorem of_codimChowCongr (X : (SmoothProjectiveScheme k).FullSubcategory) {i i' : ℤ} (h : i = i')
    (x : CodimChow k X.obj.hom i) :
    DirectSum.of (fun j ↦ CodimChow k X.obj.hom j) i' (codimChowCongr k X.obj.hom h x) =
      DirectSum.of (fun j ↦ CodimChow k X.obj.hom j) i x := by
  subst h
  rw [codimChowCongr_self]

end SmoothProjectiveScheme

open SmoothProjectiveScheme

/-! ### Chow groups of motives -/

namespace ChowMotiveCat

/-- The rational Chow classes of a motive's scheme `X` in codimension `j`, read in the category
of correspondences: `α ∈ CH^j(X) ⊗ ℚ` is the correspondence `Spec k ⟶ X` of degree `j` of
Stacks 0FG0 (3), a morphism from the scheme `Spec k` of the Tate motives to `X`. -/
def toCorrFromPoint (n : ℤ) (M : ChowMotiveCat k) (j : ℤ) :
    CodimChow k M.scheme.obj.hom j →ₗ[ℚ] ((tate k n).X ⟶ M.X) :=
  (totalChowEquiv M.scheme).toLinearMap ∘ₗ
    DirectSum.lof ℚ ℤ (fun i ↦ CodimChow k M.scheme.obj.hom i) j

/-- `toCorrFromPoint n M j α` is the image under `totalChowEquiv` of `α` in the total Chow
group. -/
theorem toCorrFromPoint_apply (n : ℤ) (M : ChowMotiveCat k) (j : ℤ)
    (α : CodimChow k M.scheme.obj.hom j) :
    toCorrFromPoint n M j α =
      totalChowEquiv M.scheme (DirectSum.of (fun i ↦ CodimChow k M.scheme.obj.hom i) j α) :=
  rfl

/-- Distinct rational Chow classes of codimension `j` give distinct correspondences from
`Spec k`. -/
theorem toCorrFromPoint_injective (n : ℤ) (M : ChowMotiveCat k) (j : ℤ) :
    Function.Injective (toCorrFromPoint n M j) :=
  (totalChowEquiv M.scheme).injective.comp (DirectSum.of_injective j)

/-- The correspondence from `Spec k` given by a class of codimension `j` is homogeneous of degree
`j`. -/
theorem toCorrFromPoint_mem_grade (n : ℤ) (M : ChowMotiveCat k) (j : ℤ)
    (α : CodimChow k M.scheme.obj.hom j) :
    toCorrFromPoint n M j α ∈ grade (R := ℚ) (tate k n).X M.X j := by
  rw [toCorrFromPoint_apply, totalChowEquiv_of, ← DirectSum.lof_eq_of ℚ]
  exact homOf_mem_grade _

/-- The pushforward `p_* : CH^j(X) ⊗ ℚ ⟶ CH^j(X) ⊗ ℚ` along the projector
`p ∈ Corr⁰(X, X)` of a motive `(X, p, m)`, by pushforward of cycles by correspondences
(Section 0FFZ). -/
def projectorPushforward (M : ChowMotiveCat k) (j : ℤ) :
    CodimChow k M.scheme.obj.hom j →ₗ[ℚ] CodimChow k M.scheme.obj.hom j :=
  (codimChowCongr k M.scheme.obj.hom (add_zero j)).toLinearMap ∘ₗ
    pushforward k M.scheme.obj.hom M.scheme.obj.hom (canonicalDiagonalClassFamily k) 0 j
      (SmoothProjectiveCorr.toCorr M.scheme M.scheme 0 M.projector)

/-- **Stacks Project, Definition 0FGL.** The `i`th Chow group of a Chow motive
`M = (X, p, m)`,

  `CH^i(M) = p(CH^{i+m}(X) ⊗ ℚ)`,

the image of the pushforward along the projector `p` on `CH^{i+m}(X) ⊗ ℚ`. -/
def chowGroup (M : ChowMotiveCat k) (i : ℤ) :
    Submodule ℚ (CodimChow k M.scheme.obj.hom (i + M.twist)) :=
  LinearMap.range (projectorPushforward M (i + M.twist))

/-- The pushforward `c_* : CH^{i+m}(X) ⊗ ℚ ⟶ CH^{i+n}(Y) ⊗ ℚ` along the correspondence
`c ∈ Corr^{n-m}(X, Y)` underlying a morphism of motives `c : (X, p, m) ⟶ (Y, q, n)`, by
pushforward of cycles by correspondences (Section 0FFZ). -/
def homPushforward {M N : ChowMotiveCat k} (f : M ⟶ N) (i : ℤ) :
    CodimChow k M.scheme.obj.hom (i + M.twist) →ₗ[ℚ] CodimChow k N.scheme.obj.hom (i + N.twist) :=
  (codimChowCongr k N.scheme.obj.hom (show i + M.twist + (N.twist - M.twist) = i + N.twist by
      ring)).toLinearMap ∘ₗ
    pushforward k M.scheme.obj.hom N.scheme.obj.hom (canonicalDiagonalClassFamily k)
      (N.twist - M.twist) (i + M.twist)
      (SmoothProjectiveCorr.toCorr M.scheme N.scheme _ (homEquiv M N f).1)

/-- Pushing a class forward along a correspondence `c` and reading it in the category of
correspondences is composition with `c`. -/
private theorem totalChowEquiv_of_pushforward (n : ℤ) {M N : ChowMotiveCat k} (r j : ℤ)
    (c : SmoothProjectiveCorr M.scheme N.scheme r) (α : CodimChow k M.scheme.obj.hom j) :
    totalChowEquiv N.scheme (DirectSum.of (fun i ↦ CodimChow k N.scheme.obj.hom i) (j + r)
      (pushforward k M.scheme.obj.hom N.scheme.obj.hom (canonicalDiagonalClassFamily k) r j
        (SmoothProjectiveCorr.toCorr M.scheme N.scheme r c) α)) =
      toCorrFromPoint n M j α ≫ homOf r c := by
  rw [← totalPushforward_of_of, totalChowEquiv_totalPushforward]
  rfl

/-- The class of `p_*(α)` in the category of correspondences is the composite of `α` with `p`. -/
theorem toCorrFromPoint_projectorPushforward (n : ℤ) (M : ChowMotiveCat k) (j : ℤ)
    (α : CodimChow k M.scheme.obj.hom j) :
    toCorrFromPoint n M j (projectorPushforward M j α) = toCorrFromPoint n M j α ≫ M.p := by
  rw [toCorrFromPoint_apply, projectorPushforward, LinearMap.comp_apply, LinearEquiv.coe_coe,
    of_codimChowCongr, totalChowEquiv_of_pushforward n, homOf_projector]

/-- **Pushforward by a morphism of motives is composition** (from Stacks 0FG0 (3)): the class of
`c_*(α)` in the category of correspondences is the composite of `α` with `c`. -/
theorem toCorrFromPoint_homPushforward (n : ℤ) {M N : ChowMotiveCat k} (f : M ⟶ N) (i : ℤ)
    (α : CodimChow k M.scheme.obj.hom (i + M.twist)) :
    toCorrFromPoint n N (i + N.twist) (homPushforward f i α) =
      toCorrFromPoint n M (i + M.twist) α ≫ f.val := by
  rw [toCorrFromPoint_apply, homPushforward, LinearMap.comp_apply, LinearEquiv.coe_coe,
    of_codimChowCongr, totalChowEquiv_of_pushforward n, homOf_homEquiv]

/-- A rational Chow class of `X` lies in `CH^i(X, p, m)` exactly when, as a correspondence from
`Spec k`, it is fixed by `p`. -/
theorem mem_chowGroup_iff (M : ChowMotiveCat k) (i : ℤ)
    (α : CodimChow k M.scheme.obj.hom (i + M.twist)) :
    α ∈ chowGroup M i ↔
      toCorrFromPoint (-i) M (i + M.twist) α ≫ M.p = toCorrFromPoint (-i) M (i + M.twist) α := by
  constructor
  · rintro ⟨β, rfl⟩
    rw [toCorrFromPoint_projectorPushforward, Category.assoc, M.idem]
  · intro h
    refine ⟨α, toCorrFromPoint_injective (-i) M _ ?_⟩
    rw [toCorrFromPoint_projectorPushforward, h]

/-- Pushforward along a morphism of motives `c : M ⟶ (Y, q, n)` lands in `CH^i(Y, q, n)`, since
`c = q ∘ c`. -/
theorem homPushforward_mem_chowGroup {M N : ChowMotiveCat k} (f : M ⟶ N) (i : ℤ)
    (α : CodimChow k M.scheme.obj.hom (i + M.twist)) :
    homPushforward f i α ∈ chowGroup N i := by
  rw [mem_chowGroup_iff, toCorrFromPoint_homPushforward, Category.assoc, f.2.2.2]

/-- The map `c_* : CH^i(M) ⟶ CH^i(N)` induced by a morphism of motives `c : M ⟶ N`, the
restriction of the pushforward `c_* : CH^{i+m}(X) ⊗ ℚ ⟶ CH^{i+n}(Y) ⊗ ℚ` along the underlying
correspondence `c ∈ Corr^{n-m}(X, Y)`; it preserves the Chow groups of motives because
`c = q ∘ c ∘ p`. -/
def chowMap {M N : ChowMotiveCat k} (f : M ⟶ N) (i : ℤ) : chowGroup M i →ₗ[ℚ] chowGroup N i :=
  (homPushforward f i).restrict fun α _ ↦ homPushforward_mem_chowGroup f i α

/-- The map `c_*` on Chow groups of motives is the restriction of the pushforward
`homPushforward`. -/
@[simp]
theorem chowMap_apply_coe {M N : ChowMotiveCat k} (f : M ⟶ N) (i : ℤ) (α : chowGroup M i) :
    (chowMap f i α : CodimChow k N.scheme.obj.hom (i + N.twist)) = homPushforward f i α :=
  rfl

/-- The identity of a motive induces the identity on its Chow groups. -/
theorem chowMap_id (M : ChowMotiveCat k) (i : ℤ) (α : chowGroup M i) : chowMap (𝟙 M) i α = α := by
  refine Subtype.ext (toCorrFromPoint_injective (-i) M _ ?_)
  rw [chowMap_apply_coe, toCorrFromPoint_homPushforward]
  exact (mem_chowGroup_iff M i α).1 α.2

/-- The map induced on Chow groups by a composite of morphisms of motives is the composite of the
induced maps. -/
theorem chowMap_comp {M N P : ChowMotiveCat k} (f : M ⟶ N) (g : N ⟶ P) (i : ℤ)
    (α : chowGroup M i) : chowMap (f ≫ g) i α = chowMap g i (chowMap f i α) := by
  refine Subtype.ext (toCorrFromPoint_injective (-i) P _ ?_)
  rw [chowMap_apply_coe, chowMap_apply_coe, chowMap_apply_coe, toCorrFromPoint_homPushforward,
    toCorrFromPoint_homPushforward, toCorrFromPoint_homPushforward, Category.assoc]
  rfl

variable (k) in
/-- The functor `CH^i(-)` from Chow motives to `ℚ`-vector spaces, `M ↦ CH^i(M)` and
`c ↦ c_*`. -/
@[simps]
def chowFunctor (i : ℤ) : ChowMotiveCat k ⥤ ModuleCat.{u} ℚ where
  obj M := ModuleCat.of ℚ (chowGroup M i)
  map f := ModuleCat.ofHom (chowMap f i)
  map_id M := ModuleCat.hom_ext (LinearMap.ext (chowMap_id M i))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext (chowMap_comp f g i))

/-- For a smooth projective scheme `X` over `k`, `CH^i(h(X)) = CH^i(X) ⊗ ℚ`: the projector of
`h(X) = (X, 1, 0)` is the identity. -/
theorem chowGroup_h_obj (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ) :
    chowGroup ((h k).obj (Opposite.op X)) i = ⊤ :=
  eq_top_iff.2 fun α _ ↦ (mem_chowGroup_iff _ i α).2 (Category.comp_id _)

/-! ### Representability -/

/-- A correspondence `𝟏(-i) ⟶ M` is a morphism of motives exactly when it is homogeneous of
degree `i + m` and fixed by the projector of `M`. -/
private theorem mem_homSubmodule_tate_neg_iff (M : ChowMotiveCat k) (i : ℤ)
    (a : (tate k (-i)).X ⟶ M.X) :
    a ∈ TwistedKaroubi.homSubmodule (tate k (-i)) M ↔
      a ∈ grade (R := ℚ) (tate k (-i)).X M.X (i + M.twist) ∧ a ≫ M.p = a := by
  rw [TwistedKaroubi.mem_homSubmodule, tate_twist, show M.twist - -i = i + M.twist by ring]
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, Category.id_comp _, h.2⟩⟩

/-- A class `α ∈ CH^i(M)`, read as a correspondence from `Spec k`, is a morphism of motives
`𝟏(-i) ⟶ M`. -/
theorem toCorrFromPoint_mem_homSubmodule (M : ChowMotiveCat k) (i : ℤ) (α : chowGroup M i) :
    toCorrFromPoint (-i) M (i + M.twist) α ∈ TwistedKaroubi.homSubmodule (tate k (-i)) M :=
  (mem_homSubmodule_tate_neg_iff M i _).2
    ⟨toCorrFromPoint_mem_grade (-i) M _ _, (mem_chowGroup_iff M i α).1 α.2⟩

/-- The class `α ∈ CH^i(M)`, read as a morphism `𝟏(-i) ⟶ M`, i.e. as an element of the space
`Hom_{M_k}(𝟏(-i), M)` of correspondences `Spec k ⟶ X` of degree `m - (-i)` fixed by the
projectors. -/
def chowGroupToHom (M : ChowMotiveCat k) (i : ℤ) :
    chowGroup M i →ₗ[ℚ] TwistedKaroubi.homSubmodule (tate k (-i)) M :=
  ((toCorrFromPoint (-i) M (i + M.twist)).comp (chowGroup M i).subtype).codRestrict _
    (toCorrFromPoint_mem_homSubmodule M i)

/-- The underlying correspondence of `chowGroupToHom M i α` is `α` read as a correspondence from
`Spec k`. -/
@[simp]
theorem chowGroupToHom_coe (M : ChowMotiveCat k) (i : ℤ) (α : chowGroup M i) :
    (chowGroupToHom M i α : (tate k (-i)).X ⟶ M.X) = toCorrFromPoint (-i) M (i + M.twist) α :=
  rfl

/-- Every morphism `Spec k ⟶ X` of the category of correspondences homogeneous of degree `j` is
a rational Chow class of codimension `j`, by Stacks 0FG0 (3). -/
theorem exists_toCorrFromPoint_eq (n : ℤ) (M : ChowMotiveCat k) (j : ℤ)
    {a : (tate k n).X ⟶ M.X} (ha : a ∈ grade (R := ℚ) (tate k n).X M.X j) :
    ∃ α, toCorrFromPoint n M j α = a := by
  obtain ⟨c, rfl⟩ := mem_grade_iff.1 ha
  refine ⟨(pointCorrEquiv M.scheme j).symm c, ?_⟩
  rw [toCorrFromPoint_apply, totalChowEquiv_of, LinearEquiv.apply_symm_apply, homOf,
    DirectSum.lof_eq_of]

/-- The map `chowGroupToHom` from `CH^i(M)` to `Hom_{M_k}(𝟏(-i), M)` is bijective. -/
theorem chowGroupToHom_bijective (M : ChowMotiveCat k) (i : ℤ) :
    Function.Bijective (chowGroupToHom M i) := by
  refine ⟨fun α β h ↦ Subtype.ext (toCorrFromPoint_injective (-i) M _
    (congrArg Subtype.val h)), fun f ↦ ?_⟩
  obtain ⟨hf, hp⟩ := (mem_homSubmodule_tate_neg_iff M i f.1).1 f.2
  obtain ⟨α, hα⟩ := exists_toCorrFromPoint_eq (-i) M (i + M.twist) hf
  exact ⟨⟨α, (mem_chowGroup_iff M i α).2 (by rw [hα, hp])⟩, Subtype.ext hα⟩

/-- The functor `CH^i(-)` on the category `M_k` of Chow motives is representable by `𝟏(-i)`: for
every motive `M` there is a `ℚ`-linear isomorphism

  `CH^i(M) = Hom_{M_k}(𝟏(-i), M)`,

sending `α ∈ CH^i(X, p, m) = p(CH^{i+m}(X) ⊗ ℚ)` to the correspondence
`α ∈ Corr^{i+m}(Spec k, X)` of Stacks 0FG0 (3). It is natural in `M`:
`Stacks.WeilCohomology.ChowMotiveCat.chowGroupEquivHom_naturality`. -/
@[stacks 0FGM "CH^i(M) = Hom_{M_k}(1(-i), M)"]
def chowGroupEquivHom (M : ChowMotiveCat k) (i : ℤ) : chowGroup M i ≃ₗ[ℚ] (tate k (-i) ⟶ M) :=
  (LinearEquiv.ofBijective (chowGroupToHom M i) (chowGroupToHom_bijective M i)).trans
    (TwistedKaroubi.homLinearEquiv (tate k (-i)) M).symm

/-- The underlying correspondence of the morphism `𝟏(-i) ⟶ M` attached to `α ∈ CH^i(M)` is `α`
read as a correspondence from `Spec k`. -/
@[simp]
theorem chowGroupEquivHom_apply_val (M : ChowMotiveCat k) (i : ℤ) (α : chowGroup M i) :
    (chowGroupEquivHom M i α).val = toCorrFromPoint (-i) M (i + M.twist) α :=
  rfl

/-- The identification `CH^i(M) = Hom_{M_k}(𝟏(-i), M)` is natural in `M`: for a morphism of
motives `c : M ⟶ N` it carries `c_* : CH^i(M) ⟶ CH^i(N)` to postcomposition with `c`. -/
@[stacks 0FGM "CH^i(M) = Hom_{M_k}(1(-i), M) functorially in M"]
theorem chowGroupEquivHom_naturality {M N : ChowMotiveCat k} (f : M ⟶ N) (i : ℤ)
    (α : chowGroup M i) :
    chowGroupEquivHom N i (chowMap f i α) = chowGroupEquivHom M i α ≫ f :=
  TwistedKaroubi.hom_ext (toCorrFromPoint_homPushforward (-i) f i α)

variable (k) in
/-- The functor `CH^i(-) : M_k ⥤ ℚ-vector spaces` is representable by `𝟏(-i)`: it is isomorphic
to the functor `Hom_{M_k}(𝟏(-i), -)`, functorially in the motive. -/
@[stacks 0FGM "the functor CH^i(-) on M_k is representable by 1(-i)"]
def chowFunctorIso (i : ℤ) :
    chowFunctor k i ≅ (linearCoyoneda ℚ (ChowMotiveCat k)).obj (Opposite.op (tate k (-i))) :=
  linearCoyonedaObjIsoOfLinearEquiv ℚ (tate k (-i)) (chowFunctor k i)
    (fun M ↦ chowGroupEquivHom M i) fun f α ↦ chowGroupEquivHom_naturality f i α

end ChowMotiveCat

end Stacks.WeilCohomology
