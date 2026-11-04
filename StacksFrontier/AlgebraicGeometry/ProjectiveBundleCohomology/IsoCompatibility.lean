module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistTransportData

/-!
# The identifications of Tag 01XX are compatible with isomorphisms of modules

Let `e : E ≅ E'` be an isomorphism of finite locally free `𝒪_S`-modules of constant rank `n + 1`.
It induces an isomorphism `𝐏(E') ≅ 𝐏(E)` of projective bundles over `S`, and the twists of `𝐏(E)`
restrict along it to the twists of `𝐏(E')` (Tag 01NR), compatibly with the homogeneous-section
maps: this is the compatibility of the isomorphism with `𝒪(1)`. Under the induced isomorphisms
`R⁰π_* 𝒪_{𝐏(E)}(d) ≅ R⁰π'_* 𝒪_{𝐏(E')}(d)` and `Sym^d(e) : Sym^d(E) ≅ Sym^d(E')`, the
identifications `R⁰π_* 𝒪(d) ≅ Sym^d` of [Stacks, Tag 01XX] correspond.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleTwistIso`: the restriction of the
  twists of `𝐏(E)` to `𝐏(E')` is the twists of `𝐏(E')`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.higherDirectImageZeroMap`: the induced map
  `R⁰π_* 𝒪_{𝐏(E)}(d) ⟶ R⁰π'_* 𝒪_{𝐏(E')}(d)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleTwistIso_psi`: the identification of
  the twists commutes with the homogeneous-section maps and `Sym(e)`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.higherDirectImageZeroIso_naturality`: the
  row `q = 0` of Tag 01XX is compatible with `e`.

## References

* [Stacks Project, Tag 01XX](https://stacks.math.columbia.edu/tag/01XX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S : Scheme.{u}} {E E' : S.Modules} {r : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E r)
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' r) (e : E ≅ E')

/-- `Γ(U, Sym(e))` followed by `Γ(U, Sym(e⁻¹))` is the identity. -/
public theorem symHom_sectionHom_inv (U : S.Opens) (x : (bundleAlgebra E' hfree').sectionRing U) :
    (symHom hfree hfree' e.hom).sectionHom U ((symHom hfree' hfree e.inv).sectionHom U x) = x :=
  (symHom_sectionHom_comp hfree' hfree hfree' e.inv e.hom U x).trans
    (by rw [e.inv_hom_id]; exact symHom_sectionHom_id hfree' U x)

/-- `Γ(U, Sym(e⁻¹))` followed by `Γ(U, Sym(e))` is the identity. -/
public theorem symHom_sectionHom_inv' (U : S.Opens) (x : (bundleAlgebra E hfree).sectionRing U) :
    (symHom hfree' hfree e.inv).sectionHom U ((symHom hfree hfree' e.hom).sectionHom U x) = x :=
  symHom_sectionHom_inv hfree' hfree e.symm U x

/-- The morphism of projective bundles induced by `e` is an isomorphism. -/
public instance isIso_bundleMap : IsIso (bundleMap hfree hfree' e) :=
  (bundleIso hfree hfree' e).isIso_hom

/-- The morphism of charts `Proj Γ(U, Sym(E')) ⟶ Proj Γ(U, Sym(E))` induced by `e` is an open
immersion. -/
public instance isOpenImmersion_isoChartMap_bundle (U : S.Opens) :
    IsOpenImmersion (isoChartMap (fun U => (symHom hfree hfree' e.hom).sectionHom U)
      (fun U => (symHom hfree' hfree e.inv).sectionHom U)
      (symHom_sectionHom_inv hfree hfree' e) U) :=
  isOpenImmersion_projMap_inverse _ _ (symHom_sectionHom_inv hfree hfree' e U)
    (symHom_sectionHom_inv' hfree hfree' e U)

/-- The charts of `𝐏(E')` and `𝐏(E)` are related by the induced isomorphism. -/
public theorem chart_comp_bundleMap_iso (U : S.Opens) (hU : IsAffineOpen U) :
    (relativeProj (bundleAlgebra E' hfree')).chart U hU ≫ bundleMap hfree hfree' e =
      isoChartMap (fun U => (symHom hfree hfree' e.hom).sectionHom U)
        (fun U => (symHom hfree' hfree e.inv).sectionHom U)
        (symHom_sectionHom_inv hfree hfree' e) U ≫
        (relativeProj (bundleAlgebra E hfree)).chart U hU :=
  chart_comp_bundleMap hfree hfree' e U hU

variable (D : TwistData (bundleAlgebra E hfree)) (D' : TwistData (bundleAlgebra E' hfree'))

/-- **The isomorphism of projective bundles induced by `e` is compatible with `𝒪(1)`**: the
twists of `𝐏(E)` restricted to `𝐏(E')` are the twists of `𝐏(E')`, as graded algebras. -/
public def bundleTwistIso :
    restrictAlgebra (bundleMap hfree hfree' e) D.algebra ≅ D'.algebra :=
  transportTwistIso (bundleMap hfree hfree' e) (fun U => (symHom hfree hfree' e.hom).sectionHom U)
    (symHom hfree' hfree e.inv) (symHom_sectionHom_inv hfree hfree' e)
    (symHom_sectionHom_inv' hfree hfree' e) (chart_comp_bundleMap_iso hfree hfree' e) D
    (bundleMap_comp_toBase hfree hfree' e) D'

/-- The direct image of a module on `𝐏(E)` maps to the direct image of its restriction to
`𝐏(E')`. -/
public abbrev bundleRestrictPushforward
    (M : (relativeProj (bundleAlgebra E hfree)).scheme.Modules) :
    (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase).obj M ⟶
      (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).obj
        (Scheme.Modules.restrict M (bundleMap hfree hfree' e)) :=
  restrictPushforwardMap (bundleMap hfree hfree' e) (bundleMap_comp_toBase hfree hfree' e) M

/-- **The identification of the twists commutes with the homogeneous-section maps**: the
canonical maps `Sym^k(E) ⟶ π_* 𝒪(k)` and `Sym^k(E') ⟶ π'_* 𝒪(k)` correspond under `Sym^k(e)`. -/
public theorem bundleTwistIso_psi (k : ℕ) :
    D.ψ k ≫ bundleRestrictPushforward hfree hfree' e (D.algebra.piece (k : ℤ)) ≫
        (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).map
          ((bundleTwistIso hfree hfree' e D D').hom.app (k : ℤ)) =
      (symHom hfree hfree' e.hom).app (k : ℤ) ≫ D'.ψ k := by
  have h := transportTwistIso_psi (bundleMap hfree hfree' e)
    (fun U => (symHom hfree hfree' e.hom).sectionHom U) (symHom hfree' hfree e.inv)
    (symHom_sectionHom_inv hfree hfree' e) (symHom_sectionHom_inv' hfree hfree' e)
    (chart_comp_bundleMap_iso hfree hfree' e) D (bundleMap_comp_toBase hfree hfree' e) D' k
  rw [← h, ← Category.assoc ((symHom hfree hfree' e.hom).app (k : ℤ)), symHom_app_comp,
    e.hom_inv_id, symHom_app_id, Category.id_comp]
  rfl

/-- **The map `R⁰π_* 𝒪_{𝐏(E)}(d) ⟶ R⁰π'_* 𝒪_{𝐏(E')}(d)` induced by `e`**: through `R⁰ = π_*`, the
restriction of sections along `𝐏(E') ≅ 𝐏(E)` followed by the identification of the twists. -/
public def higherDirectImageZeroMap (d : ℕ) :
    ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase).rightDerivedPlus
        0).obj (D.algebra.piece (d : ℤ)) ⟶
      ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).rightDerivedPlus
        0).obj (D'.algebra.piece (d : ℤ)) :=
  (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso _).hom.app _ ≫
    bundleRestrictPushforward hfree hfree' e (D.algebra.piece (d : ℤ)) ≫
    (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).map
      ((bundleTwistIso hfree hfree' e D D').hom.app (d : ℤ)) ≫
    (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso _).inv.app _

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S : Scheme.{u}} {E E' : S.Modules} {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1)) (e : E ≅ E')
  (D : TwistData (bundleAlgebra E hfree)) (D' : TwistData (bundleAlgebra E' hfree'))

/-- Cancelling an isomorphism inside a composite. -/
public theorem cancel_iso_middle {C : Type*} [Category C] {a b c d e f' : C} (x : a ⟶ b)
    (f : b ⟶ c) (g : c ⟶ d) (i : e ≅ d) (k : d ⟶ f') (y : a ⟶ f')
    (h : x ≫ f ≫ g ≫ k = y) : x ≫ f ≫ g ≫ i.inv ≫ i.hom ≫ k = y := by
  rwa [Iso.inv_hom_id_assoc]

/-- **[Stacks, Tag 01XX], the row `q = 0` is compatible with isomorphisms.** For an isomorphism
`e : E ≅ E'` of finite locally free modules of constant rank `n + 1`, `n ≥ 1`, the identifications
`R⁰π_* 𝒪_{𝐏(E)}(d) ≅ Sym^d(E)` and `R⁰π'_* 𝒪_{𝐏(E')}(d) ≅ Sym^d(E')` correspond under the map
induced by `e` on `R⁰` and `Sym^d(e)`, for every `d ≥ 0`. -/
public theorem higherDirectImageZeroIso_naturality (hn : 1 ≤ n) (d : ℕ) :
    higherDirectImageZeroMap hfree hfree' e D D' d ≫
        (higherDirectImageZeroIso E' hfree' D' hn d).hom =
      (higherDirectImageZeroIso E hfree D hn d).hom ≫ (symHom hfree hfree' e.hom).app (d : ℤ) := by
  have := isIso_symToPushforwardTwist E hfree D hn d
  have := isIso_symToPushforwardTwist E' hfree' D' hn d
  have h := bundleTwistIso_psi hfree hfree' e D D' d
  have h' : bundleRestrictPushforward hfree hfree' e (D.algebra.piece (d : ℤ)) ≫
      (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).map
        ((bundleTwistIso hfree hfree' e D D').hom.app (d : ℤ)) ≫ inv (D'.ψ d) =
      inv (D.ψ d) ≫ (symHom hfree hfree' e.hom).app (d : ℤ) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← Category.assoc, Category.assoc (D.ψ d), h,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  show (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
        (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase)).hom.app
          (D.algebra.piece (d : ℤ)) ≫
      bundleRestrictPushforward hfree hfree' e (D.algebra.piece (d : ℤ)) ≫
      (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase).map
        ((bundleTwistIso hfree hfree' e D D').hom.app (d : ℤ)) ≫
      (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
        (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase)).inv.app
          (D'.algebra.piece (d : ℤ)) ≫
      (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
        (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase)).hom.app
          (D'.algebra.piece (d : ℤ)) ≫ inv (D'.ψ d) =
    (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
        (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase)).hom.app
          (D.algebra.piece (d : ℤ)) ≫ inv (D.ψ d) ≫ (symHom hfree hfree' e.hom).app (d : ℤ)
  have h'' := congrArg ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
        (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase)).hom.app
          (D.algebra.piece (d : ℤ)) ≫ ·) h'
  exact cancel_iso_middle _ _ _ ((Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
        (Scheme.Modules.pushforward (relativeProj (bundleAlgebra E' hfree')).toBase)).app
          (D'.algebra.piece (d : ℤ))) _ _ h''

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
