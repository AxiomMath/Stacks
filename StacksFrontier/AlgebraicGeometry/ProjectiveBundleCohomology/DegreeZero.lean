module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.LocalModel
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.PolynomialSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.GradedIsoSections

/-!
# The direct image of the twists on a projective bundle

Let `S` be a scheme, `n ≥ 1`, `E` an `𝒪_S`-module which is finite locally free of constant rank
`n + 1`, and `π : 𝐏(E) ⟶ S` its projective bundle. For every `d ≥ 0` the canonical map
`ψ_d : Sym^d(E) ⟶ π_* 𝒪_{𝐏(E)}(d)` of [Stacks, Tag 01NR] is an isomorphism, and for `d < 0`
the direct image `π_* 𝒪_{𝐏(E)}(d)` is zero. Composed with `R⁰π_* = π_*` this is the `q = 0` row
of [Stacks, Tag 01XX].

Over an affine open `V` over which `E` is free, the sections of `ψ_d` over `V` are, through the
chart of `𝐏(E)` over `V`, the canonical map `Γ(V, Sym(E))_d → Γ(Proj Γ(V, Sym(E)), 𝒪(d))`, and
`Γ(V, Sym(E))` is the polynomial ring `Γ(S, V)[T₀, …, Tₙ]`, for which that map is bijective. Such
opens form a basis of `S`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isIso_psi`: **`ψ_d` is an isomorphism**.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_pushforward_twist_of_neg`:
  `π_* 𝒪_{𝐏(E)}(d) = 0` for `d < 0`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.zeroIso`: **`R⁰π_* 𝒪_{𝐏(E)}(d) ≅ Sym^d(E)`**
  for every integer `d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf degreeSection)
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

/-- **A morphism of sheaves of modules on a scheme which is bijective on the sections over every
member of a basis of opens is an isomorphism.** -/
public theorem isIso_of_bijective_app_basis {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    {B : Set Y.Opens} (hB : Opens.IsBasis B)
    (h : ∀ V ∈ B, Function.Bijective (φ.val.app (op V)).hom) : IsIso φ := by
  rw [← isIso_iff_of_reflects_iso _ (Scheme.Modules.toPresheaf Y)]
  let ψ : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} Y.toTopCat) ⟶
      ⟨N.presheaf, N.isSheaf⟩ := ⟨φ.mapPresheaf⟩
  have hψ : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis (B := (Subtype.val : B → Y.Opens))
    (by simpa using hB) fun i =>
      (ConcreteCategory.isIso_iff_bijective (ψ.hom.app (.op i.1))).2 (h i.1 i.2)
  exact @Functor.map_isIso _ _ _ _ _ _ (TopCat.Sheaf.forget Ab.{u} Y.toTopCat) ψ hψ

/-- **A sheaf of modules on a scheme whose sections over every member of a basis of opens are
trivial is zero.** -/
public theorem isZero_of_subsingleton_app_basis {Y : Scheme.{u}} (M : Y.Modules)
    {B : Set Y.Opens} (hB : Opens.IsBasis B)
    (h : ∀ V ∈ B, ∀ x y : M.val.obj (op V), x = y) : IsZero M := by
  have : IsIso (0 : M ⟶ M) := isIso_of_bijective_app_basis 0 hB fun V hV =>
    ⟨fun x y _ => h V hV x y, fun y => ⟨y, h V hV _ _⟩⟩
  exact (IsZero.iff_id_eq_zero M).mpr ((isIsoZeroSelfEquiv M) this)

/-- Transport of sections along an equality of opens is bijective. -/
public theorem bijective_eqRec {X : Type*} (F : X → Type*) {a b : X} (h : a = b) :
    Function.Bijective (fun x : F a => h ▸ x) := by
  subst h
  exact Function.bijective_id

section Bundle

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))

/-- The comparison of the chart over an affine open is bijective on global sections. -/
public theorem bijective_mapSection {V : S.Opens} (hV : IsAffineOpen V) (d : ℤ) :
    Function.Bijective (D.chartData.mapSection V hV d ⊤) := by
  let := D.chartData.chart_isOpenImmersion V hV
  have h1 := ConcreteCategory.bijective_of_isIso
    ((PresheafOfModules.evaluation _ (op ⊤)).mapIso
      ((SheafOfModules.forget _).mapIso (D.chartData.chartIso V hV d).symm)).hom
  have h2 := ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.restrictAppIso ((relativeProj
      (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) (D.algebra.piece d) ⊤).hom
  exact h2.comp h1

/-- **The sections of `ψ_k` over an affine open trivializing `E` are bijective.** -/
public theorem bijective_psi_app {n : ℕ} (hn : 0 < n) {V : S.Opens} (hV : IsAffineOpen V)
    (e : E.restrict V.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin (n + 1)))) (k : ℕ) :
    Function.Bijective ((D.ψ k).val.app (op V)).hom := by
  obtain ⟨b₀⟩ := nonempty_basis_sections E e
  let b := b₀.reindex Equiv.ulift
  have hdeg : Function.Bijective
      (degreeSection ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) k) :=
    bijective_degreeSection_of_inverse (ofPolyGrading E hqc hV b) (toPolyGrading E hqc hV b)
      (ofPolyGrading_toPolyGrading E hqc hV b) (toPolyGrading_ofPolyGrading E hqc hV b) k
      (bijective_degreeSection_polynomial (R := Γ(S, V)) hn k)
  have hof : Function.Bijective
      (fun a : (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces V k =>
        (⟨DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces V) k a,
          (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).of_mem_grading V a⟩ :
          (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V k)) :=
    ⟨fun a a' h => DirectSum.of_injective k (congrArg Subtype.val h),
      fun z => by
        obtain ⟨a, ha⟩ :=
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).mem_grading_iff V z.1).mp z.2
        exact ⟨a, Subtype.ext ha⟩⟩
  refine (Function.Bijective.of_comp_iff' (bijective_eqRec
    (fun W => (D.algebra.piece (k : ℤ)).val.obj (op W)) (D.chartData.chart_range V hV).symm)
    ((D.ψ k).val.app (op V)).hom).mp ?_
  exact (congrArg Function.Bijective (funext fun a => (D.ψ_chart V hV k a).symm)).mpr
    ((bijective_mapSection E hqc D hV (k : ℤ)).comp (hdeg.comp hof))

/-- **The canonical map `ψ_k : Sym^k(E) ⟶ π_* 𝒪_{𝐏(E)}(k)` is an isomorphism**, for `E` finite
locally free of constant rank `n + 1` with `n ≥ 1`, and every `k ≥ 0`. -/
public theorem isIso_psi {n : ℕ} (hn : 0 < n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) (k : ℕ) :
    IsIso (D.ψ k) :=
  isIso_of_bijective_app_basis _ (ProjectiveBundleVanishing.isBasis_trivializing E hfree)
    fun V hV => bijective_psi_app E hqc D hn hV.1 hV.2.some k

/-- **`π_* 𝒪_{𝐏(E)}(d) = 0` for `d < 0`**, for `E` finite locally free of constant rank `n + 1`
with `n ≥ 1`. -/
public theorem isZero_pushforward_twist_of_neg {n : ℕ} (hn : 0 < n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) {d : ℤ} (hd : d < 0) :
    IsZero ((Scheme.Modules.pushforward
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
        (D.algebra.piece d)) := by
  refine isZero_of_subsingleton_app_basis _
    (ProjectiveBundleVanishing.isBasis_trivializing E hfree) fun V hV => ?_
  suffices h : ∀ x y : (D.algebra.piece d).val.obj
      (op ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V)),
      x = y from h
  intro x y
  obtain ⟨b₀⟩ := nonempty_basis_sections E hV.2.some
  let b := b₀.reindex Equiv.ulift
  have h0 : ∀ s t : (twistingSheaf
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) d).val.obj (op ⊤), s = t :=
    twistSections_eq_of_inverse (ofPolyGrading E hqc hV.1 b) (toPolyGrading E hqc hV.1 b)
      (ofPolyGrading_toPolyGrading E hqc hV.1 b) (toPolyGrading_ofPolyGrading E hqc hV.1 b) d
      (eq_of_neg (R := Γ(S, V)) hn hd)
  have hm := bijective_mapSection E hqc D hV.1 d
  obtain ⟨s, hs⟩ := hm.2 ((D.chartData.chart_range V hV.1).symm ▸ x)
  obtain ⟨t, ht⟩ := hm.2 ((D.chartData.chart_range V hV.1).symm ▸ y)
  exact (bijective_eqRec (fun W => (D.algebra.piece d).val.obj (op W))
    (D.chartData.chart_range V hV.1).symm).1 (hs.symm.trans ((congrArg _ (h0 s t)).trans ht))

/-- **`R⁰π_* 𝒪_{𝐏(E)}(k) ≅ Sym^k(E)`** for `k ≥ 0`: the comparison `R⁰π_* = π_*` of
[Stacks, Tag 05TD] followed by the inverse of `ψ_k`. -/
public def zeroIso {n : ℕ} (hn : 0 < n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) (k : ℕ) :
    ((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      0).obj (D.algebra.piece (k : ℤ)) ≅
      (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ) :=
  haveI := isIso_psi E hqc D hn hfree k
  (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso _).app _ ≪≫ (asIso (D.ψ k)).symm

/-- **`R⁰π_* 𝒪_{𝐏(E)}(d) = 0` for `d < 0`.** -/
public theorem isZero_rightDerivedPlus_zero_of_neg {n : ℕ} (hn : 0 < n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) {d : ℤ} (hd : d < 0) :
    IsZero (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      0).obj (D.algebra.piece d)) :=
  (isZero_pushforward_twist_of_neg E hqc D hn hfree hd).of_iso
    ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso _).app _)

end Bundle

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
