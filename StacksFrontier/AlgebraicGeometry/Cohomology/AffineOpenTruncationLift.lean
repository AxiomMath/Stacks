module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineOpenHypercohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.CategoryTheory.Triangulated.TruncGELift

/-!
# Lifting a map out of `(j_{U!} 𝒪_U)^{⊕t}` through a truncation, over an affine chart

Let `X` be a scheme, let `F` be an object of `D(𝒪_X)` all of whose cohomology sheaves are
quasi-coherent, and let `U` be an affine open of `X`.  Every morphism
`(j_{U!} 𝒪_U)^{⊕t} ⟶ τ^{≥0}F` of `D(𝒪_X)` lifts along the canonical `F ⟶ τ^{≥0}F`, **with
nothing shrunk**.

This is the local-lifting step of Stacks 08HE (2) ⇒ (1), assembled.  Its three inputs are now all
present:

* the truncation triangle `τ^{<0}F ⟶ F ⟶ τ^{≥0}F ⟶ (τ^{<0}F)⟦1⟧` and exactness of `coyoneda`
  along it, which is `CategoryTheory.Triangulated.TStructure.exists_lift_truncGEπ_of_subsingleton`;
* the vanishing of the obstruction group `(j_{U!} 𝒪_U)^{⊕t} ⟶ (τ^{<0}F)⟦1⟧`, which is
  `AlgebraicGeometry.subsingleton_hom_cofan_singleExtensionByZeroUnit_of_isAffineOpen` — over an
  affine open the hypercohomology of `τ^{<0}F` in degree `1` is its sections in degree `1`, and
  `τ^{<0}F` has no cohomology there;
* quasi-coherence of the cohomology of `τ^{<0}F`, which is
  `AlgebraicGeometry.isQuasicoherent_homology_truncLE`.

The truncation degree is `0` and not an arbitrary `n` because the source sits in degree zero: for
the use in Stacks 08HE one takes `F = E⟦n⟧`, so that `τ^{≥0}F` is `τ^{≥n}E` shifted and a
morphism `(j_{U!} 𝒪_U)^{⊕t} ⟶ E⟦n⟧` is a morphism `𝒪^{⊕t}[-n] ⟶ E` after the shift.  At a
truncation degree `a` the obstruction would sit in degree `1` of `τ^{<a}F`, which vanishes only
for `a ≤ 1`; the statement is therefore given at `a ≤ 1` and specialised to `0`.

## Main results

* `AlgebraicGeometry.exists_lift_truncGEπ_cofan_of_isAffineOpen`: **the lift**, at a truncation
  degree `a ≤ 1`.
* `AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen`: the same at `a = 0`, which
  is the form Stacks 08HE (2) ⇒ (1) consumes.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (F : DerivedCategory X.Modules)

/-- **The cohomology of a truncation from above is quasi-coherent**, in the `τ^{<a}` spelling.
This is `AlgebraicGeometry.isQuasicoherent_homology_truncLE` read through
`CategoryTheory.Triangulated.TStructure.truncLEIsoTruncLT`. -/
theorem isQuasicoherent_homology_truncLT
    (hF : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj F).IsQuasicoherent)
    (a q : ℤ) : ((DerivedCategory.homologyFunctor X.Modules q).obj
      ((DerivedCategory.TStructure.t.truncLT a).obj F)).IsQuasicoherent :=
  isQuasicoherent_of_iso X _ _
    ((DerivedCategory.homologyFunctor X.Modules q).mapIso
      ((DerivedCategory.TStructure.t.truncLEIsoTruncLT (a - 1) a (by omega)).app F))
    (isQuasicoherent_homology_truncLE X F hF (a - 1) q)

/-- **A morphism out of `(j_{U!} 𝒪_U)^{⊕t}` into a truncation lifts over an affine chart.**  For
an object `F` of `D(𝒪_X)` with quasi-coherent cohomology, an affine open `U` and a truncation
degree `a ≤ 1`, every morphism `g : (j_{U!} 𝒪_U)^{⊕t} ⟶ τ^{≥a}F` is `f ≫ π` for some
`f : (j_{U!} 𝒪_U)^{⊕t} ⟶ F`, with no shrinking of `U`.

The obstruction to the lift is the composite of `g` with the connecting morphism
`τ^{≥a}F ⟶ (τ^{<a}F)⟦1⟧`, and the group it lives in vanishes: over an affine open the degree-`1`
hypercohomology of `τ^{<a}F` is its degree-`1` cohomology sheaf evaluated at `U`, and `τ^{<a}F`
is `≤ a - 1` with `a - 1 < 1`.

The coproduct is taken as a colimiting cofan over an arbitrary index type, so that the statement
applies to whatever presentation of `(j_{U!} 𝒪_U)^{⊕t}` the caller has; finiteness of the index
is not used. -/
theorem exists_lift_truncGEπ_cofan_of_isAffineOpen
    (hF : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj F).IsQuasicoherent)
    (U : X.Opens) (hU : U ∈ X.affineOpens) (a : ℤ) (ha : a ≤ 1) {ι : Type*}
    (c : Cofan (fun _ : ι =>
      Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnit X.zariskiRingedSite U))
    (hc : IsColimit c) (g : c.pt ⟶ (DerivedCategory.TStructure.t.truncGE a).obj F) :
    ∃ f : c.pt ⟶ F, f ≫ (DerivedCategory.TStructure.t.truncGEπ a).app F = g :=
  Triangulated.TStructure.exists_lift_truncGEπ_of_subsingleton
    (DerivedCategory.TStructure.t (C := X.Modules)) a F c.pt g
    (subsingleton_hom_cofan_singleExtensionByZeroUnit_of_isAffineOpen X
      ((DerivedCategory.TStructure.t.truncLT a).obj F)
      (fun q => isQuasicoherent_homology_truncLT X F hF a q) U hU 1
      (DerivedCategory.isZero_of_isLE _ (a - 1) 1 (by omega)) c hc)

/-- **The lifting step of Stacks 08HE (2) ⇒ (1) at an affine chart**, at truncation degree zero:
every morphism `(j_{U!} 𝒪_U)^{⊕t} ⟶ τ^{≥0}F` of `D(𝒪_X)` lifts to `F`, for `U` affine and `F`
with quasi-coherent cohomology.

Taking `F = E⟦n⟧` this is the local lift of a surjection `𝒪^{⊕t} ⟶ H^n(E)` to a map of complexes
`𝒪^{⊕t}[-n] ⟶ E`: the identification of `τ^{≥0}(E⟦n⟧)` with `H^n(E)` placed in degree zero, for
`E` in `D^{≤n}`, is `DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor` read through
`CategoryTheory.Triangulated.TStructure.isLE_iff_isIso_truncLTι_app`.  **Nothing is shrunk** —
over an affine chart the hypercohomology edge map of Stacks 0BKZ is an isomorphism, so the
obstruction vanishes on `U` itself. -/
theorem exists_lift_truncGEπ_zero_cofan_of_isAffineOpen
    (hF : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj F).IsQuasicoherent)
    (U : X.Opens) (hU : U ∈ X.affineOpens) {ι : Type*}
    (c : Cofan (fun _ : ι =>
      Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnit X.zariskiRingedSite U))
    (hc : IsColimit c) (g : c.pt ⟶ (DerivedCategory.TStructure.t.truncGE 0).obj F) :
    ∃ f : c.pt ⟶ F, f ≫ (DerivedCategory.TStructure.t.truncGEπ 0).app F = g :=
  exists_lift_truncGEπ_cofan_of_isAffineOpen X F hF U hU 0 (by omega) c hc g

end AlgebraicGeometry

end
