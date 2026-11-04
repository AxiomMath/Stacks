module

public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.AlgebraicGeometry.AffineDifferentials.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sections of the base-change map on relative differentials

For a commutative square of schemes with identity bottom edge

```
X' --f--> X
|         |
p'        p
v         v
S ======= S
```

and opens `U ≤ p ⁻¹ᵁ V` of `X` and `U' ≤ f ⁻¹ᵁ U` of `X'`, the three rings of sections
`R := Γ(S, V)`, `A := Γ(X, U)` and `B := Γ(X', U')` form a tower, and the canonical map
`f^* Ω_{X/S} ⟶ Ω_{X'/S}` of Stacks Project, Tag 01UV reads on sections over `U'` as the
ring-theoretic base-change map `KaehlerDifferential.mapBaseChange R A B` of
`Mathlib.RingTheory.Kaehler.Basic`.

## Main results

* `Stacks.AlgebraicGeometry.AffineDifferentials.relativeDifferentialsMap_app_eq_mapBaseChange`:
  **the identification.** Read through the two comparison maps on sections — each taken as a
  `B`-linear map characterised by its values on universal differentials — the sections over `U'`
  of the canonical map are `KaehlerDifferential.mapBaseChange R A B`.
* `relativeDifferentialsMap_app_kaehlerToSections_eq_mapBaseChange` in the same namespace: the
  same with the comparison on the target taken to be
  `Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections`, which is an isomorphism for
  `U'` and `V` affine by
  `Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections`.

## Implementation notes

The bottom edge of the square is the identity of `S` because that is the exact scope of
`KaehlerDifferential.mapBaseChange`: it names a map `B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R]` for a tower of
*three* rings. For a square with a general bottom edge `g : S' ⟶ S` the sections of the canonical
map go `Γ(X', U') ⊗_{Γ(X, U)} Ω[Γ(X, U)⁄Γ(S, V)] ⟶ Ω[Γ(X', U')⁄Γ(S', V')]`, which is
`mapBaseChange` followed by a `KaehlerDifferential.map`; the bare `mapBaseChange` is the case
`S' = S`, `g = 𝟙 S`. Nothing else is specialised: `V`, `U` and `U'` are arbitrary opens, neither
affine nor carrying any quasi-coherence hypothesis, and `p'` is an arbitrary morphism with
`f ≫ p = p' ≫ 𝟙 S` rather than literally `f ≫ p`.

The three `Algebra` structures are the ones induced by `AlgebraicGeometry.Scheme.Hom.appLE`, and
they are bound by `letI` in the statements rather than taken as instance-implicit hypotheses
pinned by equations. That is what makes the two sides typecheck against each other with no
transport at all: with those instances `Ω[Γ(X, U)⁄Γ(S, V)]` *is* the carrier of
`CommRingCat.KaehlerDifferential (p.appLE V U hUV)`, so no comparison of an abstract `Algebra`
instance with `RingHom.toAlgebra` — ruinous at a sheaf-section type — ever arises.

Both comparisons on sections are parameters pinned by their values, in the shape a caller
supplies them: on the source by its values on `1 ⊗ d a`, which is what
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` provides over affine opens, and on the
target by its values on `d c`, which is what
`Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d` provides. Taking the target
comparison abstractly rather than writing `kaehlerToSections` into the statement is not laziness:
`kaehlerToSections` is a morphism of `ModuleCat`, so a group of sections appears through the
module structure `ModuleCat.of` puts on it, which is only *definitionally* the one `Γ(·, ·)`
carries, and `map_add`, `map_smul` and `AlgebraicGeometry.pullbackSectionHom_smul` then fail to
apply to the goal. A type ascription does not repair this — the type of an application is fixed
by the function, not by the ascription — whereas an abstract `B`-linear map into `Γ(·, ·)` is
linear on the nose. The `kaehlerToSections` form is then recovered by *applying* the theorem,
where the definitional comparison is made once, at the level of the map.

The content is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_pullbackSection`, which
pins the canonical map on a pulled-back universal differential `d a`. It is propagated to the
pure tensors `1 ⊗ x` by `Submodule.span_induction` against
`KaehlerDifferential.span_range_derivation` — the scalar step is
`1 ⊗ a • y = algebraMap a • (1 ⊗ y)`, so only `B`-linearity is ever used, and no semilinearity of
pulling a section back is needed — and then to all of `B ⊗[A] Ω[A⁄R]` by
`TensorProduct.induction_on`.

No `@[stacks]` attribute is attached: this is the affine-local dictionary for the canonical map
of Tag 01UV, not one of the numbered assertions.

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentials

variable {X' X S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S)
  (hcomm : f ≫ p = p' ≫ 𝟙 S) (V : S.Opens) (U : X.Opens) (U' : X'.Opens)
  (hUV : U ≤ p ⁻¹ᵁ V) (hU' : U' ≤ f ⁻¹ᵁ U) (hU'V : U' ≤ p' ⁻¹ᵁ V)

include hcomm in
/-- **The three rings of sections form a tower.** For a commutative square with identity bottom
edge, the map `Γ(S, V) ⟶ Γ(X', U')` induced by `p'` is the composite of the maps induced by `p`
and by `f`. -/
theorem appLE_eq_comp_appLE :
    (p'.appLE V U' hU'V).hom = (f.appLE U U' hU').hom.comp (p.appLE V U hUV).hom := by
  have hp' : f ≫ p = p' := by rw [Category.comp_id] at hcomm; exact hcomm
  subst hp'
  exact congrArg CommRingCat.Hom.hom
    (Scheme.Hom.appLE_comp_appLE f p V U U' hUV hU').symm

include hcomm in
/-- The sections of the structure sheaves over `V`, `U` and `U'` form a tower of algebras for the
structures induced by `AlgebraicGeometry.Scheme.Hom.appLE`. -/
theorem isScalarTower_appLE :
    letI : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U hUV).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(X', U') := (f.appLE U U' hU').hom.toAlgebra
    letI : Algebra Γ(S, V) Γ(X', U') := (p'.appLE V U' hU'V).hom.toAlgebra
    IsScalarTower Γ(S, V) Γ(X, U) Γ(X', U') := by
  let : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X', U') := (f.appLE U U' hU').hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X', U') := (p'.appLE V U' hU'V).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    (appLE_eq_comp_appLE f p p' hcomm V U U' hUV hU' hU'V)

include hcomm in
/-- **The sections of the base-change map on relative differentials are
`KaehlerDifferential.mapBaseChange`.** Let

```
X' --f--> X
|         |
p'        p
v         v
S ======= S
```

be a commutative square of schemes, let `U ≤ p ⁻¹ᵁ V` and `U' ≤ f ⁻¹ᵁ U` be opens, and write
`R := Γ(S, V)`, `A := Γ(X, U)` and `B := Γ(X', U')`. Let

* `T` be a `B`-linear map from `B ⊗[A] Ω[A⁄R]` to the sections of `f^* Ω_{X/S}` over `U'` carrying
  `1 ⊗ d a` to the pullback of the universal differential of `a`, and
* `E` a `B`-linear map from `Ω[B⁄R]` to the sections of `Ω_{X'/S}` over `U'` carrying `d c` to the
  universal differential of `c`

— the two canonical comparisons of sections with Kähler differentials, each pinned by its
defining property. Then the sections over `U'` of the canonical map
`f^* Ω_{X/S} ⟶ Ω_{X'/S}` of Tag 01UV, read through `T` on the source and `E` on the target, are
`KaehlerDifferential.mapBaseChange R A B`. -/
theorem relativeDifferentialsMap_app_eq_mapBaseChange :
    letI : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U hUV).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(X', U') := (f.appLE U U' hU').hom.toAlgebra
    letI : Algebra Γ(S, V) Γ(X', U') := (p'.appLE V U' hU'V).hom.toAlgebra
    haveI := isScalarTower_appLE f p p' hcomm V U U' hUV hU' hU'V
    ∀ (T : Γ(X', U') ⊗[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, V)] →ₗ[Γ(X', U')]
          Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p), U'))
      (E : Ω[Γ(X', U')⁄Γ(S, V)] →ₗ[Γ(X', U')] Γ(Scheme.Hom.relativeDifferentials p', U')),
      (∀ a : Γ(X, U), T ((1 : Γ(X', U')) ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, U) a) =
        pullbackSectionHom f (Scheme.Hom.relativeDifferentials p) U U' hU'
          ((Scheme.Hom.universalRelativeDerivation p).d a)) →
      (∀ c : Γ(X', U'), E (KaehlerDifferential.D Γ(S, V) Γ(X', U') c) =
        (Scheme.Hom.universalRelativeDerivation p').d c) →
      ∀ t : Γ(X', U') ⊗[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, V)],
        (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 S) hcomm).app U' (T t) =
          E (KaehlerDifferential.mapBaseChange Γ(S, V) Γ(X, U) Γ(X', U') t) := by
  let : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X', U') := (f.appLE U U' hU').hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X', U') := (p'.appLE V U' hU'V).hom.toAlgebra
  have := isScalarTower_appLE f p p' hcomm V U U' hUV hU' hU'V
  intro T E hT hE
  have htmul : ∀ (b : Γ(X', U')) (x : Ω[Γ(X, U)⁄Γ(S, V)]),
      b ⊗ₜ[Γ(X, U)] x = b • ((1 : Γ(X', U')) ⊗ₜ[Γ(X, U)] x) := fun b x => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  -- first on the pure tensors `1 ⊗ x`, by induction over the generators of `Ω[A⁄R]`
  have hone : ∀ x : Ω[Γ(X, U)⁄Γ(S, V)],
      (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 S) hcomm).app U'
          (T ((1 : Γ(X', U')) ⊗ₜ x)) =
        E (KaehlerDifferential.mapBaseChange Γ(S, V) Γ(X, U) Γ(X', U')
          ((1 : Γ(X', U')) ⊗ₜ x)) := by
    intro x
    have hx : x ∈ Submodule.span Γ(X, U)
        (Set.range (KaehlerDifferential.D Γ(S, V) Γ(X, U))) := by
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        have hkey : (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 S) hcomm).app U'
              (pullbackSectionHom f (Scheme.Hom.relativeDifferentials p) U U' hU'
                ((Scheme.Hom.universalRelativeDerivation p).d a)) =
            (Scheme.Hom.universalRelativeDerivation p').d
              (algebraMap Γ(X, U) Γ(X', U') a) :=
          Scheme.Hom.relativeDifferentialsMap_pullbackSection f p p' (𝟙 S) hcomm U U' hU' a
        rw [hT a, hkey, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
          one_smul, hE]
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add y z _ _ ihy ihz => simp only [TensorProduct.tmul_add, map_add, ihy, ihz]
    | smul a y _ ihy =>
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
          htmul (algebraMap Γ(X, U) Γ(X', U') a) y]
        simp only [map_smul, Scheme.Modules.Hom.app_smul]
        rw [ihy]
  -- then on all of `B ⊗[A] Ω[A⁄R]`, since `b ⊗ x` is `b • (1 ⊗ x)`
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b x =>
      rw [htmul]
      simp only [map_smul, Scheme.Modules.Hom.app_smul]
      rw [hone]
  | add t₁ t₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

include hcomm in
/-- **The sections of the base-change map on relative differentials are
`KaehlerDifferential.mapBaseChange`**, with the comparison on the target taken to be
`Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections`. For `U'` and `V` affine that
comparison is an isomorphism, by
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections`; so is the comparison
`T` on the source, by `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, and the statement
then identifies the sections of the canonical map with
`KaehlerDifferential.mapBaseChange Γ(S, V) Γ(X, U) Γ(X', U')` outright. -/
@[ega "IV 16.4.3" "special case"]
theorem relativeDifferentialsMap_app_kaehlerToSections_eq_mapBaseChange :
    letI : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U hUV).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(X', U') := (f.appLE U U' hU').hom.toAlgebra
    letI : Algebra Γ(S, V) Γ(X', U') := (p'.appLE V U' hU'V).hom.toAlgebra
    haveI := isScalarTower_appLE f p p' hcomm V U U' hUV hU' hU'V
    ∀ (T : Γ(X', U') ⊗[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, V)] →ₗ[Γ(X', U')]
          Γ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p), U')),
      (∀ x : Ω[Γ(X, U)⁄Γ(S, V)], T ((1 : Γ(X', U')) ⊗ₜ x) =
        pullbackSectionHom f (Scheme.Hom.relativeDifferentials p) U U' hU'
          ((kaehlerToSections p V U hUV).hom x)) →
      ∀ t : Γ(X', U') ⊗[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, V)],
        (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 S) hcomm).app U' (T t) =
          (kaehlerToSections p' V U' hU'V).hom
            (KaehlerDifferential.mapBaseChange Γ(S, V) Γ(X, U) Γ(X', U') t) := by
  let : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X', U') := (f.appLE U U' hU').hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X', U') := (p'.appLE V U' hU'V).hom.toAlgebra
  have := isScalarTower_appLE f p p' hcomm V U U' hUV hU' hU'V
  intro T hT t
  refine relativeDifferentialsMap_app_eq_mapBaseChange f p p' hcomm V U U' hUV hU' hU'V T
    (kaehlerToSections p' V U' hU'V).hom (fun a => ?_)
    (fun c => kaehlerToSections_d p' V U' hU'V c) t
  rw [hT (KaehlerDifferential.D Γ(S, V) Γ(X, U) a)]
  exact congrArg _ (kaehlerToSections_d p V U hUV a)

end Stacks.AlgebraicGeometry.AffineDifferentials

end
