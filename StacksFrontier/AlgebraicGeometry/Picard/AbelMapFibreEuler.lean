module

public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapDegree
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurve
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicardScheme
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.FibreDims
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData

/-!
# The fibres of the sheaf of a family of divisors on a curve

Let `X` be a geometrically irreducible smooth proper curve of genus `g` over a field `k`, let `T`
be a scheme over `k` and let `D ⊂ X ×_k T` be a degree-`d` Hilbert family, that is a closed
subscheme finite locally free of rank `d` over `T`. Then `D` is a relative effective Cartier
divisor, and for every point `t ∈ T` the fibre of the invertible sheaf `𝒪(D)` at `t` has Euler
characteristic

`dim H⁰(X_t, 𝒪(D)_t) - dim H¹(X_t, 𝒪(D)_t) = d + 1 - g`

over the residue field `κ(t)`.

This is the computation by which the morphism `γ_d` of [Stacks, Tag 0BA0], clause (4), lands in
the degree-`d` component `Pic^d_{X/k}`: that component is cut out by the fibrewise Euler
characteristic `d + 1 - g` ([Stacks, Tag 0B9T]).

## Main results

* `Stacks.AbelMap.fibreEuler_divisorSheaf`: the fibrewise Euler characteristic of `𝒪(D)`.
* `Stacks.AbelMap.euler_divisorSheaf_of_isPullback`: the same computation over any field point of
  the base, in the form used on rational points of the Hilbert scheme.

## Implementation notes

The fibre cohomology is `Stacks.FibreCohomology.fibreCohomology`, the cohomology over `κ(t)` of
the pullback of `𝒪(D)` to the scheme-theoretic fibre `X_T ×_T Spec κ(t)`. It is compared with the
cohomology of the sheaf of the restricted family `D_t` on `X ×_k Spec κ(t)`, the base change in
the form the Hilbert functor uses, by `Stacks.FibreCohomology.finrank_eq_of_isPullback`; there
[Stacks, Tag 0C4U] identifies the pullback of `𝒪(D)` with `𝒪(D_t)`, and
`AlgebraicGeometry.euler_divisorSheaf_eq` is Riemann-Roch for `𝒪(D_t)`. The genus does not change
under the field extension `k ⊂ κ(t)` ([Stacks, Tag 0BY9]).

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Divisors (divisorSheaf IsEffectiveCartierDivisor)
open Stacks.FibreCohomology (fibreCohomology)

universe u

namespace Stacks.AbelMap

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The sheaf of an effective Cartier divisor is quasi-coherent. -/
theorem isQuasicoherent_divisorSheaf {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [IsEffectiveCartierDivisor D] : (divisorSheaf D).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherent_of_isInvertible (divisorSheaf D)

/-- A geometrically irreducible smooth scheme over a field is geometrically integral. -/
theorem geometricallyIntegral_of_smooth [GeometricallyIrreducible f] [Smooth f] :
    GeometricallyIntegral f :=
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

section FieldPoint

variable [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] [IsProper f]
  {K : Type u} [Field K] [Algebra k K] {Z : Scheme.{u}} (gZ : Z ⟶ X)
  (fZ : Z ⟶ Spec (.of K))
  (hZ : IsPullback gZ fZ f (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include hZ

omit [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] in
/-- The base change of the curve to a field is proper. -/
theorem isProper_of_isPullback : IsProper fZ :=
  MorphismProperty.of_isPullback hZ inferInstance

omit [IsCurve k f] [IsProper f] in
/-- The base change of the curve to a field is integral. -/
theorem isIntegral_of_isPullback : IsIntegral Z :=
  have : GeometricallyIntegral f := geometricallyIntegral_of_smooth f
  have : GeometricallyIntegral fZ := MorphismProperty.of_isPullback hZ inferInstance
  GeometricallyIntegral.isIntegral_of_subsingleton fZ

omit [GeometricallyIrreducible f] [IsProper f] in
/-- The base change of the curve to a field is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_isPullback : SmoothOfRelativeDimension 1 fZ :=
  have : SmoothOfRelativeDimension 1 f :=
    AlgebraicGeometry.smoothOfRelativeDimension_one_of_isCurve k f
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hZ inferInstance

omit [IsProper f] in
/-- The base change of the curve to a field is again of dimension one. -/
theorem topologicalKrullDim_eq_one_of_isPullback : topologicalKrullDim Z = 1 := by
  have := smoothOfRelativeDimension_one_of_isPullback f gZ fZ hZ
  have := isIntegral_of_isPullback f gZ fZ hZ
  simpa using AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension fZ 1

omit [IsCurve k f] in
/-- The base change of the curve to a field has only the constants as global functions. -/
theorem isIso_globalSections_of_isPullback : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fZ.appTop) :=
  have : GeometricallyIntegral f := geometricallyIntegral_of_smooth f
  have : GeometricallyIntegral fZ := MorphismProperty.of_isPullback hZ inferInstance
  have := isProper_of_isPullback f gZ fZ hZ
  isIso_globalSections_of_geometricallyIntegral K fZ

/-- **Riemann-Roch for a divisor on the base change of the curve to a field.** If `D` is an
effective Cartier divisor on `X_K` finite locally free of rank `d` over `K`, then
`χ(X_K, 𝒪(D)) = d + 1 - g`, where `g` is the genus of `X` over `k`. -/
theorem euler_divisorSheaf_of_isPullback (D : Z.IdealSheafData) [hDc : IsEffectiveCartierDivisor D]
    {d : ℕ} (hD : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ fZ) d) :
    (Module.finrank K (cohomologyOverField K fZ (divisorSheaf D) 0) : ℤ) -
        Module.finrank K (cohomologyOverField K fZ (divisorSheaf D) 1) =
      d + 1 - genus f := by
  have := isProper_of_isPullback f gZ fZ hZ
  have := isIntegral_of_isPullback f gZ fZ hZ
  have := isIso_globalSections_of_isPullback f gZ fZ hZ
  let : Algebra K Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (D.subschemeι ≫ fZ).appTop).hom.toAlgebra
  have hrank : Module.finrank K Γ(D.subscheme, ⊤) = d :=
    ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq (D.subschemeι ≫ fZ)
      d).mp hD).2.2
  rw [euler_divisorSheaf_eq K fZ (topologicalKrullDim_eq_one_of_isPullback f gZ fZ hZ).le D,
    hrank, genus_baseChange k K gZ fZ f hZ]

end FieldPoint

/-! ### The fibres of the sheaf of a Hilbert family -/

section Family

variable [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] [IsProper f]

/-- The `k`-algebra structure on the residue field of a point of a `k`-scheme. -/
abbrev residueFieldAlgebra {T : Over (Spec (.of k))} (t : T.left) :
    Algebra k (T.left.residueField t) :=
  (Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)).hom.toAlgebra

/-- The `k`-scheme `Spec κ(t)` of a point `t` of a `k`-scheme `T`. -/
abbrev residueFieldPoint {T : Over (Spec (.of k))} (t : T.left) : Over (Spec (.of k)) :=
  letI := residueFieldAlgebra t
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (T.left.residueField t))))

/-- The structure morphism of `Spec κ(t)` over `k` is the composite `Spec κ(t) ⟶ T ⟶ Spec k`. -/
theorem residueFieldPoint_hom {T : Over (Spec (.of k))} (t : T.left) :
    (residueFieldPoint t).hom = T.left.fromSpecResidueField t ≫ T.hom :=
  Spec.map_preimage _

/-- The inclusion `Spec κ(t) ⟶ T` of a point, as a morphism of `k`-schemes. -/
abbrev residueFieldPointι {T : Over (Spec (.of k))} (t : T.left) : residueFieldPoint t ⟶ T :=
  Over.homMk (T.left.fromSpecResidueField t) (residueFieldPoint_hom t).symm

/-- **The fibrewise Euler characteristic of the sheaf of a Hilbert family.** Let `X` be a
geometrically irreducible smooth proper curve of genus `g` over `k` and `D` a degree-`d` Hilbert
family in `X` over a `k`-scheme `T`. Then for every point `t ∈ T`,
`dim_{κ(t)} H⁰(X_t, 𝒪(D)_t) - dim_{κ(t)} H¹(X_t, 𝒪(D)_t) = d + 1 - g`. -/
theorem fibreEuler_divisorSheaf {T : Over (Spec (.of k))} {d : ℕ}
    (D : Stacks.Hilbert.HilbertFamily (Over.mk f) T d) (t : T.left) :
    (Module.finrank (T.left.residueField t)
        (fibreCohomology ((Over.pullback T.hom).obj (Over.mk f)).hom (divisorSheaf D.ideal) t 0)
        : ℤ) -
      Module.finrank (T.left.residueField t)
        (fibreCohomology ((Over.pullback T.hom).obj (Over.mk f)).hom (divisorSheaf D.ideal) t 1) =
      d + 1 - genus f := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    AlgebraicGeometry.smoothOfRelativeDimension_one_of_isCurve k f
  have := D.isEffectiveCartierDivisor_ideal
  let g := residueFieldPointι t
  let D' := Stacks.Hilbert.baseChange (Over.mk f) g D
  have hD' : IsEffectiveCartierDivisor D'.ideal := D'.isEffectiveCartierDivisor_ideal
  have : Stacks.Divisors.IsPullbackDefined (Stacks.Hilbert.familyBaseChangeMap (Over.mk f) g)
      D.ideal := hD'
  have : IsProper ((Over.pullback T.hom).obj (Over.mk f)).hom :=
    inferInstanceAs (IsProper (pullback.snd f T.hom))
  have := isQuasicoherent_divisorSheaf D.ideal
  let := residueFieldAlgebra t
  have hsq : IsPullback (pullback.fst f (residueFieldPoint t).hom)
      ((Over.pullback (residueFieldPoint t).hom).obj (Over.mk f)).hom f
      (Spec.map (CommRingCat.ofHom (algebraMap k (T.left.residueField t)))) :=
    IsPullback.of_hasPullback _ _
  have hfib : IsPullback (Stacks.Hilbert.familyBaseChangeMap (Over.mk f) g)
      ((Over.pullback (residueFieldPoint t).hom).obj (Over.mk f)).hom
      ((Over.pullback T.hom).obj (Over.mk f)).hom
      (Spec.map (𝟙 (T.left.residueField t)) ≫ T.left.fromSpecResidueField t) := by
    rw [Spec.map_id]
    convert Stacks.Hilbert.isPullback_familyBaseChangeMap (Over.mk f) g using 1
    exact Category.id_comp _
  let eM : divisorSheaf D'.ideal ≅ (Scheme.Modules.pullback
      (Stacks.Hilbert.familyBaseChangeMap (Over.mk f) g)).obj (divisorSheaf D.ideal) :=
    (Stacks.Divisors.invertibleSheafPullbackIso _ D.ideal).symm
  have h := Stacks.FibreCohomology.finrank_eq_of_isPullback _ _ t (𝟙 _) _ _ hfib _ eM
  rw [← h 0, ← h 1]
  exact euler_divisorSheaf_of_isPullback f (K := T.left.residueField t) _ _ hsq D'.ideal
    (hDc := hD') D'.isFiniteLocallyFreeOfRank

end Family

end Stacks.AbelMap

end
