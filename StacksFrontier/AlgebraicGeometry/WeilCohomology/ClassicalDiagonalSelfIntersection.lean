module

public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldIso
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionSelfIntersection
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalDiagonalBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalKunnethTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionRegularImmersionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalSelfIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ZeroCycleTraceDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The self-intersection of the diagonal

Let `X` be a smooth projective variety of dimension `d` over a field `k`, let `P = X × X` with
projections `p, q` and let `δ : X ⟶ P` be the diagonal. The second equality of Stacks 0FH0 is

  `deg([Δ] · [Δ]) = deg(c_d(𝒯_X) ∩ [X])`,

a statement about the Chow groups of Chapter 42 alone. The source's proof: by Stacks 0FFE,
`[Δ] · [Δ] = δ_*(δ^![Δ])`; pushforward preserves the degree of zero cycles; `δ^![Δ]` is the cap
product of `[X]` with the top Chern class of the normal sheaf of `δ` (the excess intersection
formula, Stacks 0FBM, with excess the whole normal bundle); and the normal sheaf of the diagonal
is the tangent sheaf, its conormal sheaf being `Ω_{X/k}` (Stacks 08S2).

## Main definitions

* `Stacks.WeilCohomology.conormalModuleIsoRelativeDifferentials`: the conormal sheaf of a common
  section of the two projections of `X ×_S X` is `Ω_{X/S}`.
* `Stacks.WeilCohomology.codimensionChowGroupCongr`: transport between equal codimensions.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.isFiniteLocallyFreeOfRank_tangentSheaf`: the
  tangent sheaf `𝒯_{X/k}` of `X` of pure dimension `d` has rank `d`.
* `Stacks.WeilCohomology.codimensionDegree_zeroCycleToCodimension`: the degree of `CH^n(X)`
  restricts to the degree of zero cycles.
* `Stacks.WeilCohomology.codimensionDegree_closedSubschemeClass_mul_self`: the self-intersection
  formula `deg([X] · [X]) = deg(c_d(𝒩) ∩ [X])` for a regular closed immersion `X ⟶ P` of pure
  codimension `d = dim X`.
* `Stacks.WeilCohomology.degree_diagonal_mul_eq_degree_chernCap_tangentSheaf`:
  **Stacks 0FH0**, the equality on the right.

## References

* [Stacks Project, Tag 0FH0](https://stacks.math.columbia.edu/tag/0FH0)
* [Stacks Project, Tag 0FFE](https://stacks.math.columbia.edu/tag/0FFE)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

open Stacks.AlgebraicGeometry.ReflexiveModules

/-! ### The tangent sheaf -/

/-- The tangent sheaf of a smooth projective scheme of pure dimension `d` over `k` is finite
locally free of rank `d`: it is the dual of `Ω_{X/k}`, which is finite locally free of rank `d`. -/
@[ega "IV 16.5.8" "special case"]
theorem SmoothProjectiveScheme.isFiniteLocallyFreeOfRank_tangentSheaf {k : Type u} [Field k]
    (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ} (hX : RelativeDimension X.obj.hom d) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (SmoothProjectiveScheme.tangentSheaf X)
      d :=
  isFiniteLocallyFreeOfRank_dualSheaf _ d
    (Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials_of_relativeDimension _ hX)

/-! ### The conormal sheaf of a diagonal section -/

section Conormal

variable {X P S : Scheme.{u}} (s : X ⟶ S) {p q : P ⟶ X} (hpq : IsPullback p q s s) (δ : X ⟶ P)
  (hδp : δ ≫ p = 𝟙 X) (hδq : δ ≫ q = 𝟙 X)

include hδp hδq in
/-- A section `δ` of both projections of a fibre square `P = X ×_S X` is the diagonal, read
through the identification `P ≅ X ×_S X`. -/
theorem comp_isoPullback_hom_eq_diagonal : δ ≫ hpq.isoPullback.hom = pullback.diagonal s := by
  ext <;> simp [hδp, hδq]

include hδp hδq in
/-- The square `δ ≫ (P ≅ X ×_S X) = 𝟙 ≫ Δ` is cartesian, its vertical arrows being
isomorphisms. -/
theorem isPullback_diagonal_section :
    IsPullback δ (𝟙 X) hpq.isoPullback.hom (pullback.diagonal s) :=
  IsPullback.of_vert_isIso ⟨by rw [comp_isoPullback_hom_eq_diagonal s hpq δ hδp hδq,
    Category.id_comp]⟩

include hδp hδq in
/-- **The conormal sheaf of a section `δ` of both projections of `P = X ×_S X` is `Ω_{X/S}`**
(Stacks 08S2): `δ` is the diagonal up to the isomorphism `P ≅ X ×_S X`, the conormal sheaf is
invariant under that isomorphism (flat base change, Stacks 01R4), and the conormal sheaf of the
diagonal is `Ω_{X/S}`. -/
@[sga "6 VIII 2.2" "more general"]
def conormalModuleIsoRelativeDifferentials [IsImmersion δ] :
    conormalModule δ ≅ Scheme.Hom.relativeDifferentials s :=
  haveI := Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat δ (pullback.diagonal s)
    (𝟙 X) hpq.isoPullback.hom (isPullback_diagonal_section s hpq δ hδp hδq)
  (asIso (Stacks.Immersion.immersionConormalSheafMap δ (pullback.diagonal s) (𝟙 X)
      hpq.isoPullback.hom
      (Stacks.Immersion.toShHom_square (isPullback_diagonal_section s hpq δ hδp hδq).w))).symm ≪≫
    (Stacks.PullbackPseudofunctor.modulePullbackIdIso X.toRingedSpace).app _ ≪≫
    (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal s).symm

end Conormal

/-! ### Degrees of zero cycles -/

section Degree

variable {k : Type u} [Field k]

/-- Transport of classes of codimension `i` to classes of codimension `j`, along `i = j`. -/
def codimensionChowGroupCongr {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
    {i j : ℤ} (h : i = j) : codimensionChowGroup k sX i ≃+ codimensionChowGroup k sX j := by
  subst h
  exact AddEquiv.refl _

/-- Transporting a class of `CH_m(X)` read in codimension `i` is reading it in codimension
`j`. -/
theorem codimensionChowGroupCongr_chowGroupToCodimension {X : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] {i j : ℤ} (h : i = j) (m : ℤ)
    (y : chowGroup (fieldChowSituation k) sX m) :
    codimensionChowGroupCongr sX h (chowGroupToCodimension sX m i y) =
      chowGroupToCodimension sX m j y := by
  subst h
  rfl

/-- On a scheme smooth over `k` of pure dimension `n`, reading a zero cycle class in `CH^n(X)` is
injective: `X_n = X` is the only nonempty part. -/
theorem zeroCycleToCodimension_injective {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    [Smooth sX] {n : ℕ} (hX : RelativeDimension sX n) :
    Function.Injective (zeroCycleToCodimension sX n) := by
  intro a b h
  refine (chowGroupDimPartEquiv k sX 0).injective (funext fun e ↦ ?_)
  obtain ⟨e⟩ := e
  by_cases he : e = n
  · subst he
    have h' := congrFun h e
    simp only [zeroCycleToCodimension, AddMonoidHom.pi_apply, sub_self, dite_eq_left,
      AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom] at h'
    rw [chowGroupDimPartEquiv_apply, chowGroupDimPartEquiv_apply]
    exact (chowGroupDegreeEquiv _ _ _).injective h'
  · have := isEmpty_dimPart_of_ne sX hX he
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

/-- **The degree of a zero cycle class read in top codimension.** On a smooth projective scheme
of pure dimension `n`, the degree of `CH^n(X)` (`Stacks.WeilCohomology.codimensionDegree`) of a
zero cycle class read in codimension `n` is its degree as a zero cycle (Stacks 0AZ1). -/
theorem codimensionDegree_zeroCycleToCodimension (X : (SmoothProjectiveScheme k).FullSubcategory)
    {n : ℕ} (hX : RelativeDimension X.obj.hom n) (s : (fieldChowSituation k).S)
    (y : chowGroup (fieldChowSituation k) X.obj.hom 0) :
    codimensionDegree X n (zeroCycleToCodimension X.obj.hom n y) =
      chowDegree (fieldChowSituation k) (fun _ ↦ rfl) X.obj.hom s y := by
  obtain ⟨α, hα, hdeg⟩ :=
    exists_zeroCycleToCodimension_eq hX s (zeroCycleToCodimension X.obj.hom n y)
  rw [← hdeg, zeroCycleToCodimension_injective X.obj.hom hX hα]

/-- `Stacks.WeilCohomology.codimensionDegree_zeroCycleToCodimension` for a class of `CH_m(X)`,
`m = 0`, read in codimension `n` through `Stacks.WeilCohomology.chowGroupToCodimension`. -/
theorem codimensionDegree_chowGroupToCodimension (X : (SmoothProjectiveScheme k).FullSubcategory)
    {n : ℕ} (hX : RelativeDimension X.obj.hom n) (s : (fieldChowSituation k).S) {m : ℤ} (hm : m = 0)
    (y : chowGroup (fieldChowSituation k) X.obj.hom m) :
    codimensionDegree X n (chowGroupToCodimension X.obj.hom m n y) =
      chowDegree (fieldChowSituation k) (fun _ ↦ rfl) X.obj.hom s
        (chowGroupDegreeEquiv _ _ hm y) := by
  subst hm
  exact codimensionDegree_zeroCycleToCodimension X hX s y

end Degree

/-! ### Stacks 0FH0, the Chow-theoretic equality -/

section Diagonal

variable {k : Type u} [Field k]

/-- A smooth projective variety is proper over `k`. -/
instance SmoothProjective.isProper_hom (X : (SmoothProjective k).FullSubcategory) :
    IsProper X.obj.hom :=
  inferInstanceAs (IsProper ((SmoothProjective.toSchemeCat k).obj X).obj.hom)

/-- **The self-intersection of a section of a fibre square, on Chow groups.** Let `P` be a smooth
projective scheme over `k` of pure dimension `2d` and `i : X ⟶ P` a regular closed immersion with
`X` proper of pure dimension `d`. Then the degree of `[X] · [X] ∈ CH^{2d}(P)` is the degree of
`c_d(𝒩) ∩ [X]`, for `𝒩` the normal bundle of `i`, or any module `E` isomorphic to it. -/
theorem codimensionDegree_closedSubschemeClass_mul_self
    (P : (SmoothProjectiveScheme k).FullSubcategory)
    {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [IsProper sX] (i : X ⟶ P.obj.left)
    [IsClosedImmersion i] (hi : i ≫ P.obj.hom = sX)
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) {d : ℕ}
    (hX : RelativeDimension sX d) (hP : RelativeDimension P.obj.hom (d + d)) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E d]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf (conormalModule i)) d]
    (eN : dualSheaf (conormalModule i) ≅ E) (s : (fieldChowSituation k).S) :
    codimensionDegree P (d + d) (codimensionChowGroupCongr P.obj.hom (by push_cast; rfl)
        (codimensionIntersectionProduct k P.obj.hom d d (closedSubschemeClass P.obj.hom i d)
          (closedSubschemeClass P.obj.hom i d))) =
      chowDegree (fieldChowSituation k) (fun _ ↦ rfl) sX s
        (chowGroupDegreeEquiv _ _ (sub_self (d : ℤ))
          (GenuineChern.chernCap (fieldChowSituation k) d sX E d (Fin.last d)
            (fundamentalChowClass (fieldChowSituation k) sX d))) := by
  subst hi
  rw [codimensionIntersectionProduct_closedSubschemeClass P.obj.hom i hreg d hX,
    regularImmersionGysin_closedSubschemeClass_self P.obj.hom i hreg d d (d + d) rfl hP hX,
    codimensionChowGroupCongr_chowGroupToCodimension,
    codimensionDegree_chowGroupToCodimension P hP s (sub_self (d : ℤ))]
  refine (congrArg _ (properChowPushforward_chowGroupDegreeEquiv _ _ _ i rfl (sub_self (d : ℤ))
    _ (properPushforwardDescends _ _ _ _ _ _) _).symm).trans ?_
  obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  refine (AlgebraicGeometry.chowDegree_properChowPushforward k P.obj.hom (i ≫ P.obj.hom) i rfl
    _).symm.trans ?_
  rw [GenuineChern.chernCap_congr _ _ d eN]
  congr 1

/-- **Stacks Project, Tag 0FH0**, the equality on the right: for a smooth projective variety `X`
of dimension `d` over `k`, `deg([Δ] · [Δ]) = deg(c_d(𝒯_X) ∩ [X])`.

The product `X × X` is a smooth projective variety `P` with projections `p, q : P ⟶ X`
exhibiting it as the fibre product over `k`, the diagonal is `δ : X ⟶ P` with
`δ ≫ p = δ ≫ q = 𝟙`, `[Δ] ∈ CH^d(P)` is the class of the closed subscheme `δ(X)`
(`Stacks.WeilCohomology.closedSubschemeClass`), `·` is the intersection product of Chapter 42
(Stacks 0FC0) and `deg` the degree of zero cycles (Stacks 0AZ1) on `CH^{2d}(P) = CH_0(P)` and on
`CH_0(X)`. `𝒯_X` is the tangent sheaf
(`Stacks.WeilCohomology.SmoothProjectiveScheme.tangentSheaf`), finite locally free
of rank `d`, and `c_d(𝒯_X) ∩ -` is the Chern class cap product of Stacks 02U5.

The proof is the source's: `[Δ] · [Δ] = δ_*(δ^![Δ])` (Stacks 0FFE), `δ_*` preserves degrees, and
`δ^![Δ] = c_d(𝒩) ∩ [X]` for the normal bundle `𝒩` of `δ` (the excess intersection formula,
Stacks 0FBM), which is `𝒯_X` because the conormal sheaf of the diagonal is `Ω_{X/k}` (Stacks
08S2). The theory `H^*` of the source plays no role in this equality, so it is not assumed, and
neither is `k` algebraically closed. -/
@[stacks 0FH0 "the equality on the right: deg([Δ] · [Δ]) = deg(c_d(T_X) ∩ [X]), for X × X any \
fibre product P of X with itself over k and Δ the diagonal section", sga "6 XIII 5.3" "partial"]
theorem degree_diagonal_mul_eq_degree_chernCap_tangentSheaf
    (X P : (SmoothProjective k).FullSubcategory) {d : ℕ}
    (hd : topologicalKrullDim X.obj.left = (d : WithBot ℕ∞)) (p q : P ⟶ X)
    (hpq : IsPullback p.hom.left q.hom.left X.obj.hom X.obj.hom) (δ : X ⟶ P)
    (hδp : δ ≫ p = 𝟙 X) (hδq : δ ≫ q = 𝟙 X) :
    haveI := SmoothProjective.isClosedImmersion_of_section p δ hδp
    haveI := SmoothProjectiveScheme.isFiniteLocallyFreeOfRank_tangentSheaf
      ((SmoothProjective.toSchemeCat k).obj X)
      (SmoothProjective.relativeDimension_hom X hd)
    codimensionDegree ((SmoothProjective.toSchemeCat k).obj P) (d + d)
        (codimensionChowGroupCongr _ (by push_cast; rfl) ((chowCycleData k).mul d d
          (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left d)
          (closedSubschemeClass ((SmoothProjective.toSchemeCat k).obj P).obj.hom δ.hom.left d))) =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction k) X.obj.hom
        default (chowGroupDegreeEquiv _ _ (sub_self (d : ℤ))
          (GenuineChern.chernCap (fieldChowSituation k) d X.obj.hom
            (SmoothProjectiveScheme.tangentSheaf ((SmoothProjective.toSchemeCat k).obj X)) d
            (Fin.last d) (fundamentalChowClass (fieldChowSituation k) X.obj.hom d))) := by
  have := SmoothProjective.isClosedImmersion_of_section p δ hδp
  have hX := SmoothProjective.relativeDimension_hom X hd
  have := SmoothProjectiveScheme.isFiniteLocallyFreeOfRank_tangentSheaf
      ((SmoothProjective.toSchemeCat k).obj X) hX
  have hpS : Smooth p.hom.left := MorphismProperty.of_isPullback hpq.flip inferInstance
  have hqS : Smooth q.hom.left := MorphismProperty.of_isPullback hpq inferInstance
  have hreg := Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section p.hom.left
    δ.hom.left (congrArg (·.hom.left) hδp)
  have hP : RelativeDimension P.obj.hom (d + d) := by
    have h := RelativeDimension.comp_of_flat q.hom.left X.obj.hom
      (RelativeDimension.of_isPullback hpq hX) hX
    exact RelativeDimension.congr (Over.w q.hom) h
  let eN : dualSheaf (conormalModule δ.hom.left) ≅
      SmoothProjectiveScheme.tangentSheaf ((SmoothProjective.toSchemeCat k).obj X) :=
    dualSheafIsoOfIso
      (conormalModuleIsoRelativeDifferentials X.obj.hom hpq δ.hom.left
        (congrArg (·.hom.left) hδp) (congrArg (·.hom.left) hδq)).symm
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf (conormalModule δ.hom.left)) d :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} eN.symm inferInstance
  exact codimensionDegree_closedSubschemeClass_mul_self ((SmoothProjective.toSchemeCat k).obj P)
    X.obj.hom δ.hom.left (Over.w δ.hom) hreg hX hP
    (SmoothProjectiveScheme.tangentSheaf ((SmoothProjective.toSchemeCat k).obj X)) eN default

end Diagonal

end Stacks.WeilCohomology

end
