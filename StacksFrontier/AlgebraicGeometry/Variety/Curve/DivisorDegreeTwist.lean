module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of `𝒪_X(D)` through its canonical section, and the symmetry of `D ∩ D'`

Let `k` be a field, let `X` be proper of dimension at most one over `k` and let `D ⊆ X` be an
effective Cartier divisor. This file computes `deg(𝒪_X(D)) = dim_k Γ(D, 𝒪_D)` by way of the
zero scheme of the canonical section `1_D`, and develops the restriction of a canonical section
to a second closed subscheme together with the symmetry of the scheme-theoretic intersection
`D ∩ D'`.

This file states no part of [Stacks, Tag 0AYY]: all three of its assertions are stated together,
and carry the tag, as `AlgebraicGeometry.isFinite_and_curveDegree_tensorSheaf_invertibleSheaf`.

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `invertibleCurveDegree_tensorSheaf_eq_add`: the invertible case of [Stacks, Tag 0AYX],
  `deg(ℒ ⊗ ℳ) = deg(ℒ) + deg(ℳ)`.
* `invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme`: for a regular
  global section `s` of an invertible module `ℒ`, `deg(ℒ) = dim_k H⁰(Z(s), 𝒪_{Z(s)})`.
* `invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections`:
  `deg(𝒪_X(D)) = dim_k Γ(D, 𝒪_D)`.
* `restrictCanonicalSection`, `zeroScheme_restrictCanonicalSection` and
  `isRegularSection_restrictCanonicalSection`: the canonical section `1_{D'}` of `𝒪_X(D')`
  restricted to a second closed subscheme `D`, its zero scheme `D' ∩ D` inside `D`, and its
  regularity when `D` is integral and not contained in `D'`.
* `comapCommIso` and `finrank_cohomologyOverField_comap_comm`: the scheme-theoretic intersection
  `D ∩ D'` does not depend on which of the two closed subschemes it is formed inside, so
  `dim_k H⁰(D ∩ D', 𝒪)` is symmetric in `D` and `D'`.

## References

* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.Divisors (IsEffectiveCartierDivisor modulesInvertibleSheaf canonicalSections)

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The invertible case of Tag 0AYX -/

/-- **The invertible case of [Stacks, Tag 0AYX]**, `deg(ℒ ⊗ ℳ) = deg(ℒ) + deg(ℳ)` for
invertible modules on a scheme proper of dimension at most one over a field. -/
theorem invertibleCurveDegree_tensorSheaf_eq_add [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L M : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [hLM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M)))] :
    invertibleCurveDegree k f hdim ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M))) =
      invertibleCurveDegree k f hdim L + invertibleCurveDegree k f hdim M := by
  rw [invertibleCurveDegree_eq_curveDegree_one k f hdim L,
    invertibleCurveDegree_eq_curveDegree_one k f hdim M,
    invertibleCurveDegree_eq_curveDegree_one k f hdim
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M)))]
  simpa using curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f hdim L M 1 1

/-! ### The degree of an invertible module through its zero scheme -/

/-- **The degree of an invertible module with a regular global section is the dimension of the
global sections of the structure sheaf of the zero scheme of that section**,
`deg(ℒ) = dim_k H⁰(Z(s), 𝒪_{Z(s)})`, for an invertible module on a scheme proper of dimension at
most one over a field. -/
theorem invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    @invertibleCurveDegree k _ X f _ hdim L hL =
      (Module.finrank k (cohomologyOverField k
        ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)
        (SheafOfModules.unit
          (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf) 0) : ℤ) := by
  obtain ⟨e⟩ := nonempty_pullback_zeroScheme_iso_unit_of_isRegularSection k f hdim L s hreg
  rw [invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme_of_isRegularSection k f
      hdim L s hreg (forall_finiteDimensional_cohomologyOverField_unit k f),
    finrank_cohomologyOverField_eq_of_iso k
      ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) e 0]

/-- **The degree of `𝒪_X(D)` is the dimension of `H⁰(D, 𝒪_D)`** for an effective Cartier divisor
`D` on a scheme proper of dimension at most one over a field. -/
theorem invertibleCurveDegree_invertibleSheaf_eq_finrank_cohomologyOverField_zero [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    invertibleCurveDegree k f hdim (Stacks.Divisors.modulesInvertibleSheaf D) =
      (Module.finrank k (cohomologyOverField k (D.subschemeι ≫ f)
        (SheafOfModules.unit D.subscheme.ringCatSheaf) 0) : ℤ) := by
  have key := invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme k f hdim
    (Stacks.Divisors.modulesInvertibleSheaf D) (Stacks.Divisors.canonicalSections D)
    (Stacks.Divisors.isRegularSection_canonicalSections D)
  rwa [Stacks.Divisors.zeroScheme_canonicalSections D] at key

/-- **The rank-one case of the second assertion of [Stacks, Tag 0AYY]**,
`deg(𝒪_X(D)) = deg(D)`, the degree of the divisor being the dimension `dim_k Γ(D, 𝒪_D)` of its
ring of global sections, which is the rank at which `D ⟶ Spec(k)` is finite locally free. -/
theorem invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    invertibleCurveDegree k f hdim (Stacks.Divisors.modulesInvertibleSheaf D) =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) := by
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  rw [invertibleCurveDegree_invertibleSheaf_eq_finrank_cohomologyOverField_zero k f hdim D]
  exact congrArg _
    (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k (D.subschemeι ≫ f))

/-! ### The canonical section restricted to a second closed subscheme -/

section Restrict

variable {Y : Scheme.{u}} (D D' : Y.IdealSheafData)

/-- **The canonical section `1_{D'}` of `𝒪_Y(D')` restricted to a closed subscheme `D ⊆ Y`.**
This is the section whose zero scheme is the scheme-theoretic intersection `D ∩ D'`, formed
inside `D`. -/
def restrictCanonicalSection :
    ((Scheme.Modules.pullback D.subschemeι).obj (modulesInvertibleSheaf D')).sections :=
  Stacks.SheafOfModules.sectionsOfTopOfRingSheaf _
    (pullbackGlobalSections D.subschemeι (modulesInvertibleSheaf D')
      ((canonicalSections D').eval (op ⊤)))

/-- The restricted canonical section is, over the whole space, the pullback of `1_{D'}`. -/
theorem eval_restrictCanonicalSection :
    (restrictCanonicalSection D D').eval (op ⊤) =
      pullbackGlobalSections D.subschemeι (modulesInvertibleSheaf D')
        ((canonicalSections D').eval (op ⊤)) :=
  Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top _ _

/-- **The zero scheme of the restricted canonical section is the scheme-theoretic inverse image
of the divisor**, `Z(1_{D'}|_D) = D' ∩ D` as a closed subscheme of `D`. -/
theorem zeroScheme_restrictCanonicalSection [IsEffectiveCartierDivisor D'] :
    zeroScheme D.subscheme
        ((Scheme.Modules.pullback D.subschemeι).obj (modulesInvertibleSheaf D'))
        ((restrictCanonicalSection D D').eval (op ⊤)) =
      D'.comap D.subschemeι := by
  rw [eval_restrictCanonicalSection]
  exact (Stacks.Divisors.zeroScheme_pullback D.subschemeι (modulesInvertibleSheaf D') _).trans
    (congrArg (·.comap D.subschemeι) (Stacks.Divisors.zeroScheme_canonicalSections D'))

/-- **The restricted canonical section is a regular section** when `D` is integral and is not
contained in `D'`. -/
theorem isRegularSection_restrictCanonicalSection [IsEffectiveCartierDivisor D']
    (hD : IsIntegral D.subscheme) (hle : ¬ D' ≤ D) :
    IsRegularSection D.subscheme.sheaf.obj D.subscheme.ringCatSheaf.property
      (restrictCanonicalSection D D') := by
  have hcan : zeroScheme Y (modulesInvertibleSheaf D')
      ((canonicalSections D').eval (op ⊤)) = D' :=
    Stacks.Divisors.zeroScheme_canonicalSections D'
  have h : IsEffectiveCartierDivisor ((zeroScheme Y (modulesInvertibleSheaf D')
      ((canonicalSections D').eval (op ⊤))).comap D.subschemeι) :=
    Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral
    (modulesInvertibleSheaf D') ((canonicalSections D').eval (op ⊤)) D hD
    (fun hh => hle (by rw [← hcan]; exact hh))
  rw [hcan] at h
  refine (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection D.subscheme _
    (restrictCanonicalSection D D')).mp ?_
  rwa [zeroScheme_restrictCanonicalSection D D']

/-! ### The intersection of two closed subschemes is symmetric -/

/-- **The scheme-theoretic intersection of two closed subschemes does not depend on which of
them it is formed inside**: `D' ∩ D`, as a closed subscheme of `D`, is isomorphic to `D ∩ D'` as
a closed subscheme of `D'`, through the symmetry of the fibre product of the two closed
immersions. -/
def comapCommIso : (D'.comap D.subschemeι).subscheme ≅ (D.comap D'.subschemeι).subscheme :=
  D'.comapIso D.subschemeι ≪≫ pullbackSymmetry _ _ ≪≫ (D.comapIso D'.subschemeι).symm

/-- Under `AlgebraicGeometry.comapCommIso` the closed immersion into `D'` is the second
projection of the fibre product. -/
theorem comapCommIso_hom_subschemeι :
    (comapCommIso D D').hom ≫ (D.comap D'.subschemeι).subschemeι =
      (D'.comapIso D.subschemeι).hom ≫ pullback.snd D.subschemeι D'.subschemeι := by
  simp [comapCommIso]

/-- The two descriptions of the intersection have the same closed immersion into the ambient
scheme. -/
theorem comapCommIso_compat :
    (D'.comap D.subschemeι).subschemeι ≫ D.subschemeι =
      ((comapCommIso D D').hom ≫ (D.comap D'.subschemeι).subschemeι) ≫ D'.subschemeι := by
  rw [comapCommIso_hom_subschemeι, ← Scheme.IdealSheafData.comapIso_hom_fst D' D.subschemeι,
    Category.assoc, Category.assoc, pullback.condition]

/-- **The dimension of `H⁰` of the structure sheaf of the intersection is symmetric in the two
closed subschemes**, provided the two structure morphisms over `k` agree on the intersection
under `AlgebraicGeometry.comapCommIso`. -/
theorem finrank_cohomologyOverField_comap_comm (k : Type u) [Field k]
    (g : D.subscheme ⟶ Spec (.of k)) (g' : D'.subscheme ⟶ Spec (.of k))
    (hcompat : ((comapCommIso D D').hom ≫ (D.comap D'.subschemeι).subschemeι) ≫ g' =
      (D'.comap D.subschemeι).subschemeι ≫ g) :
    Module.finrank k (cohomologyOverField k
        ((D'.comap D.subschemeι).subschemeι ≫ g)
        (SheafOfModules.unit (D'.comap D.subschemeι).subscheme.ringCatSheaf) 0) =
      Module.finrank k (cohomologyOverField k
        ((D.comap D'.subschemeι).subschemeι ≫ g')
        (SheafOfModules.unit (D.comap D'.subschemeι).subscheme.ringCatSheaf) 0) := by
  rw [← hcompat, Category.assoc]
  exact finrank_cohomologyOverField_unit_pushforward k (comapCommIso D D').hom
    ((D.comap D'.subschemeι).subschemeι ≫ g') 0

end Restrict

end AlgebraicGeometry

end
