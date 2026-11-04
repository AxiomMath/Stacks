module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicity.QuasiSeparatedOfAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.Topology.Noetherian.CompactSubset
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingFinitePresentationEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProductObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffine

/-!
# The ingredients of Stacks 0E96

**Stacks 0E96.** Let `n ≥ 1`, let `P` be a numerical polynomial and let `T ⊆ |𝒫olarized|` be a
set of points each of which is represented, over some field `k`, by a polarized proper scheme
`(X, ℒ)` such that (1) the Hilbert polynomial of `ℒ` on `X` is `P`, and (2) there is a closed
immersion `i : X → ℙⁿ_k` with `i^*𝒪(1) ≅ ℒ`. Then `T` is a Noetherian topological space.

## The proof

The source's proof has two halves.

* *Topology.* `|𝒫olarized|` is locally Noetherian (Stacks 0DQI), because `𝒫olarized` is locally
  of finite presentation over `Spec(ℤ)` (Stacks 0DPU), hence a locally Noetherian algebraic stack
  (Stacks 06R6). A subset of a quasi-compact subset of a locally Noetherian space is Noetherian
  (Stacks 0053 and 0052), so it suffices to find a quasi-compact subset containing `T`.
* *The image.* The Hilbert space `H = Hilb^{P, 𝒪(1)}_{ℙⁿ_ℤ/ℤ}` is proper over `Spec(ℤ)`
  (Stacks 0DPH), so `|H|` is quasi-compact; its universal family gives a morphism
  `H → 𝒫olarized` (Stacks 0D3W, 0E94), continuous on points, so the image of `|H|` is
  quasi-compact; and conditions (1), (2) say exactly that every point of `T` is the image of a
  point of `H`.

Everything in the first half is proved here, unconditionally except for the algebraicity of
`𝒫olarized` (Quot, Theorem 0D4X), without which `|𝒫olarized|` is not the space of points of an
algebraic stack: `AlgebraicGeometry.isLocallyNoetherianSpace_points_polarizedStackUnconditional`.
The reduction to the image is proved for an arbitrary algebraic space chart:
`AlgebraicGeometry.Stack.noetherianSpace_of_subset_range_spacePointMap`. For the second half, the
family `(Z, 𝒪(1)|_Z)` of a closed subscheme `Z ⊆ ℙⁿ_k` is constructed here
(`AlgebraicGeometry.hilbertPolarizedFamily`) and obtained from conditions (1) and (2) on an
arbitrary `(X, ℒ)` (`AlgebraicGeometry.hilbertPolarizedFamilyHom`,
`AlgebraicGeometry.eulerCharacteristic_tensorPowerModules_congr`). Stacks 0E96 itself is assembled
from these in `StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertBoundedImage`.

## Main definitions

* `AlgebraicGeometry.polarizedHilbertFunction`: `d ↦ χ(X, ℒ^{⊗ d})` for a polarized family over
  the spectrum of a field.
* `AlgebraicGeometry.IsHilbertPolarizedOver`: conditions (1) and (2) of Stacks 0E96.
* `AlgebraicGeometry.IsHilbertPolarizedPoint`: a field-valued point of `𝒫olarized` satisfying
  them.
* `AlgebraicGeometry.hilbertPolarizedFamily`: the polarized family `(Z, i^*𝒪(1))` of a closed
  immersion `i : Z ⟶ ℙⁿ_U`, flat and of finite presentation over `U`, an object of `𝒫olarized`
  over `U`.
* `AlgebraicGeometry.hilbertPolarizedFamilyHom`: under conditions (1) and (2), the morphism
  `(X, i^*𝒪(1)) ⟶ (X, ℒ)` given by the identity of `X`.

## References

* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
* [Stacks Project, Tag 0DQI](https://stacks.math.columbia.edu/tag/0DQI)
* [Stacks Project, Tag 0DPU](https://stacks.math.columbia.edu/tag/0DPU)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 0053](https://stacks.math.columbia.edu/tag/0053)
* [Stacks Project, Tag 0052](https://stacks.math.columbia.edu/tag/0052)
* [Stacks Project, Tag 0DPH](https://stacks.math.columbia.edu/tag/0DPH)
* [Stacks Project, Tag 0D3W](https://stacks.math.columbia.edu/tag/0D3W)
* [Stacks Project, Tag 0E94](https://stacks.math.columbia.edu/tag/0E94)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u w

/-! ### The point space of a stack, through a chart with quasi-compact point space -/

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The reduction of Stacks 0E96 to an image.** Let `𝒳` be a category fibred in groupoids over
the big fppf site of `S` whose space of points is locally Noetherian, and let `c` be a chart of
`𝒳` by an algebraic space whose space of points is quasi-compact. Every set of points of `𝒳`
contained in the image of `c` is a Noetherian topological space: that image is quasi-compact,
the canonical map being continuous (Stacks 04XL), so Stacks 0053 and 0052 apply. -/
theorem noetherianSpace_of_subset_range_spacePointMap
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : letI := pointTopology B S hS 𝒳
      IsLocallyNoetherianSpace (points B S hS 𝒳.val 𝒳.property))
    (c : SpaceChart B S hS 𝒳)
    (hc : letI := Space.pointTopology B S hS c.1.1
      CompactSpace (Space.points B S hS c.1.1))
    (T : Set (points B S hS 𝒳.val 𝒳.property))
    (hT : T ⊆ Set.range (spacePointMap B S hS c.1.1 𝒳 c.2)) :
    letI := pointTopology B S hS 𝒳
    NoetherianSpace T := by
  let := pointTopology B S hS 𝒳
  let := Space.pointTopology B S hS c.1.1
  exact noetherianSpace_of_subset_of_isCompact h𝒳
    (isCompact_range (continuous_spacePointMap B S hS c.1.1 c.1.2 𝒳 c.2)) hT

end Stack

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-! ### The terminal base of the site -/

/-- `Spec(ℤ)` belongs to every big fppf site: its size is `ℵ₀`, below the cutoff. -/
theorem contains_specULiftZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))) := by
  show (Spec (CommRingCat.of (ULift.{u} ℤ))).size < B.cutoff
  rw [Scheme.size_Spec]
  simpa using B.aleph0_lt_cutoff

/-- A terminal object of the underlying category of a big fppf site is `Spec(ℤ)`, up to
isomorphism of schemes. -/
def isoSpecULiftZOfIsTerminal (hT : IsTerminal (B.obj hS)) :
    S ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
  B.inclusion.mapIso (hT.uniqueUpToIso (isTerminal_obj_specULiftZ B (contains_specULiftZ B)))

/-- A terminal base of the big fppf site is locally Noetherian, being `Spec(ℤ)`. -/
theorem isLocallyNoetherian_of_isTerminal (hT : IsTerminal (B.obj hS)) : IsLocallyNoetherian S := by
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact LocallyOfFiniteType.isLocallyNoetherian (isoSpecULiftZOfIsTerminal B hS hT).hom

/-- A terminal base of the big fppf site is affine, being `Spec(ℤ)`. -/
theorem isAffine_of_isTerminal (hT : IsTerminal (B.obj hS)) : IsAffine S :=
  IsAffine.of_isIso (isoSpecULiftZOfIsTerminal B hS hT).hom

/-! ### `|𝒫olarized|` is locally Noetherian -/

/-- **`𝒫olarized` is a locally Noetherian algebraic stack.** Given that it is algebraic (`h`,
Quot, Theorem 0D4X), its structure morphism to the terminal base is locally of finite
presentation (Stacks 0DPU), hence locally of finite type (Stacks 06Q5), and the base `Spec(ℤ)` is
locally Noetherian, so Stacks 06R6 applies. -/
theorem hasPropertyOnSomeSchemeAtlas_isLocallyNoetherian_polarizedAlgebraicStack
    (hT : IsTerminal (B.obj hS))
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    Stack.HasPropertyOnSomeSchemeAtlas B S hS (fun X : Scheme.{u} => IsLocallyNoetherian X)
      (PolarizedAlgebraicity.polarizedAlgebraicStackOf B hS hT h) := by
  let : ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  open PolarizedAlgebraicity in
  refine Stack.AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
    (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))
    (Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (isLocallyOfFinitePresentation_structureMorphism_polarizedAlgebraicStackOf B hS hT h)) ?_
  exact (Stack.exists_scheme_atlas_iff_scheme B S hS _ _).2
    (isLocallyNoetherian_of_isTerminal B hS hT)

/-- **`|𝒫olarized|` is a locally Noetherian topological space** (Stacks 0DQI, as used in the
proof of Stacks 0E96), given that `𝒫olarized` is algebraic (`h`, Quot, Theorem 0D4X). -/
theorem isLocallyNoetherianSpace_points_polarizedStackUnconditional
    (hT : IsTerminal (B.obj hS))
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    letI := Stack.pointTopology B S hS (polarizedStackUnconditional B hS hT)
    IsLocallyNoetherianSpace (Stack.points B S hS (polarizedStackUnconditional B hS hT).val
      (polarizedStackUnconditional B hS hT).property) :=
  Stack.AlgebraicStacks.isLocallyNoetherianSpace_points_of_isLocallyNoetherian B S hS
    (PolarizedAlgebraicity.polarizedAlgebraicStackOf B hS hT h)
    (hasPropertyOnSomeSchemeAtlas_isLocallyNoetherian_polarizedAlgebraicStack B hS hT h)

/-! ### Conditions (1) and (2) of Stacks 0E96 -/

variable {B} in
/-- The total space of a polarized family over the spectrum of a field is locally Noetherian: it
is proper, in particular locally of finite type, over a field. -/
theorem PolarizedFamily.isLocallyNoetherian_total (x : PolarizedFamily B) {k : Type u} [Field k]
    (e : B.inclusion.obj x.base ≅ Spec (.of k)) : IsLocallyNoetherian x.total := by
  have := x.proper
  exact LocallyOfFiniteType.isLocallyNoetherian (x.toBase ≫ e.hom)

variable {B} in
/-- **The Hilbert function of a polarized family over a field.** For a polarized family
`(X → Spec k, ℒ)` over the spectrum of a field `k`, presented by the isomorphism `e` of its base
with `Spec k`, the function `d ↦ χ(X, ℒ^{⊗ d})`, the Euler characteristic over `k` of the
coherent module `ℒ^{⊗ d}` on the proper `k`-scheme `X`. Its values at all integers are those of
the Hilbert polynomial of `ℒ` on `X`. -/
def polarizedHilbertFunction (x : PolarizedFamily B) (k : Type u) [Field k]
    (e : B.inclusion.obj x.base ≅ Spec (.of k)) (d : ℤ) : ℤ :=
  letI := x.proper
  letI := x.invertible
  letI := x.isLocallyNoetherian_total e
  letI := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible (X := x.total)
    (Scheme.Modules.tensorPowerModules x.lineBundle d)
  eulerCharacteristic k (x.toBase ≫ e.hom) (Scheme.Modules.tensorPowerModules x.lineBundle d)

variable {B} in
/-- **Conditions (1) and (2) of Stacks 0E96** on a polarized family `(X, ℒ)` over the spectrum
of a field `k` (presented by `e`): (1) the Hilbert polynomial of `ℒ` on `X` is `P`, that is
`χ(X, ℒ^{⊗ d}) = P(d)` for every integer `d`; and (2) there is a closed immersion
`i : X → ℙⁿ` over the base with `i^*𝒪(1) ≅ ℒ`. The projective space is taken over the base of
the family, which `e` identifies with `Spec k`, so it is `ℙⁿ_k`. -/
def IsHilbertPolarizedOver (n : ℕ) (P : Polynomial ℚ) (x : PolarizedFamily B) (k : Type u)
    [Field k] (e : B.inclusion.obj x.base ≅ Spec (.of k)) : Prop :=
  (∀ d : ℤ, (polarizedHilbertFunction x k e d : ℚ) = P.eval (d : ℚ)) ∧
    ∃ i : x.total ⟶ projectiveSpaceOver n (B.inclusion.obj x.base),
      IsClosedImmersion i ∧
        i ≫ (projectiveSpaceOver n (B.inclusion.obj x.base) ↘ B.inclusion.obj x.base) =
          x.toBase ∧
        Nonempty ((Scheme.Modules.pullback i).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n
            (B.inclusion.obj x.base)) ≅ x.lineBundle)

/-- **The points of `T` in Stacks 0E96.** A field-valued point of `𝒫olarized`, that is a
polarized proper scheme `(X, ℒ)` over the spectrum of its field `k`, satisfying conditions (1)
and (2) of Stacks 0E96 for some identification of its base with `Spec k`. -/
def IsHilbertPolarizedPoint (hT : IsTerminal (B.obj hS)) (n : ℕ) (P : Polynomial ℚ)
    (p : Stack.FieldValuedPoint B S hS (polarizedStackUnconditional B hS hT).val) : Prop :=
  ∃ e : B.inclusion.obj (p.obj : PolarizedFamily B).base ≅ Spec (.of p.carrier),
    IsHilbertPolarizedOver n P (p.obj : PolarizedFamily B) p.carrier e

/-! ### The polarized family of a closed subscheme of projective space -/

variable {B} in
/-- **The polarized family `(Z, 𝒪(1)|_Z)` of a closed subscheme of `ℙⁿ_U`.** For a scheme `U` of
the big fppf site and a closed immersion `i : Z ⟶ ℙⁿ_U` whose composite to `U` is flat and of
finite presentation, the family `Z → U` (proper, as `ℙⁿ_U → U` is) polarized by `i^*𝒪(1)`. This
is the family a point of the Hilbert functor `Hilb_{ℙⁿ/ℤ}` over `U` gives, and the object of
`𝒪olarized` over `U` the classifying morphism of Stacks 0E96's proof sends that point to.

The polarization is invertible as the pullback of the invertible `𝒪(1)` (Stacks 0B8L), and it is
ample relative to `Z → U` because `𝒪(1)` is ample relative to `ℙⁿ_U → U` and `i` is affine
(`Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_of_isAffineHom_toProjectiveSpaceOver`). The
spellings are those of `AlgebraicGeometry.PolarizedFamily` and its base change: the module
pullback `Scheme.Modules.pullback`, invertibility as in its `invertible` field, and the
hyperplane sheaf `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf`. -/
def hilbertPolarizedFamily (n : ℕ) (U : B.Schemes) {Z : Scheme.{u}}
    (i : Z ⟶ projectiveSpaceOver n (B.inclusion.obj U)) [IsClosedImmersion i]
    (hfl : Flat (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)))
    (hfp : FinitePresentation
      (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U))) :
    PolarizedFamily B where
  base := U
  total := Z
  toBase := i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)
  proper := by
    have := isProper_projectiveSpaceOver n (B.inclusion.obj U)
    infer_instance
  flat := hfl
  finitePresentation := hfp
  lineBundle := (Scheme.Modules.pullback i).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (B.inclusion.obj U))
  invertible :=
    have : AlgebraicGeometry.SheafOfModules.IsInvertible
        (projectiveSpaceOver n (B.inclusion.obj U)).presheaf
        (projectiveSpaceOver n (B.inclusion.obj U)).ringCatSheaf.2
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (B.inclusion.obj U)) :=
      Stacks.ProjectiveSpace.isInvertibleModule_projectiveSpaceTwistingSheaf n _
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback i.toLRSHom.toShHom _
  relativelyAmple := by
    have : AlgebraicGeometry.SheafOfModules.IsInvertible
        (projectiveSpaceOver n (B.inclusion.obj U)).presheaf
        (projectiveSpaceOver n (B.inclusion.obj U)).ringCatSheaf.2
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (B.inclusion.obj U)) :=
      Stacks.ProjectiveSpace.isInvertibleModule_projectiveSpaceTwistingSheaf n _
    let : Stacks.Ample.IsInvertibleModule Z ((Scheme.Modules.pullback i).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (B.inclusion.obj U))) :=
      Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback i.toLRSHom.toShHom _
    exact Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_of_isAffineHom_toProjectiveSpaceOver
      (d := 1) _ le_rfl i rfl (Stacks.Ample.tensorPowModuleOneIso Z _)

/-- The Euler characteristics of the tensor powers depend only on the structure morphism and on
the isomorphism class of the invertible module. -/
theorem eulerCharacteristic_tensorPowerModules_congr (k : Type u) [Field k] {X : Scheme.{u}}
    {f g : X ⟶ Spec (.of k)} (hfg : f = g) (hf : IsProper f) (hg : IsProper g)
    {L M : X.Modules} (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M) (φ : L ≅ M) (d : ℤ)
    (hcL : (Scheme.Modules.tensorPowerModules L d).IsCoherent)
    (hcM : (Scheme.Modules.tensorPowerModules M d).IsCoherent) :
    eulerCharacteristic k f (Scheme.Modules.tensorPowerModules L d) =
      eulerCharacteristic k g (Scheme.Modules.tensorPowerModules M d) := by
  subst hfg
  exact eulerCharacteristic_eq_of_iso k f
    (@Stacks.SheafOfModules.TensorPower.tensorPowerCongr _ _ _ _ _ _ _ L M
      (Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
        X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L)
      (Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
        X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M) φ d)

variable {B} in
/-- **A polarized scheme over a field with conditions (1) and (2) is a Hilbert family.** Given
the closed immersion `i : X ⟶ ℙⁿ` over the base and `i^*𝒪(1) ≅ ℒ` of condition (2), the family
`(X, i^*𝒪(1))` of `AlgebraicGeometry.hilbertPolarizedFamily` maps to `(X, ℒ)` by the identity of
`X`. -/
def hilbertPolarizedFamilyHom (n : ℕ) (x : PolarizedFamily B)
    (i : x.total ⟶ projectiveSpaceOver n (B.inclusion.obj x.base)) [IsClosedImmersion i]
    (hi : i ≫ (projectiveSpaceOver n (B.inclusion.obj x.base) ↘ B.inclusion.obj x.base) =
      x.toBase)
    (φ : (Scheme.Modules.pullback i).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n
        (B.inclusion.obj x.base)) ≅ x.lineBundle) :
    hilbertPolarizedFamily n x.base i (hi ▸ x.flat) (hi ▸ x.finitePresentation) ⟶ x where
  baseMap := 𝟙 _
  totalMap := 𝟙 _
  cartesian := by
    change IsPullback (𝟙 x.total)
      (i ≫ (projectiveSpaceOver n (B.inclusion.obj x.base) ↘ B.inclusion.obj x.base)) x.toBase
      (B.inclusion.map (𝟙 x.base))
    rw [hi, CategoryTheory.Functor.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  lineBundleIso := (Scheme.Modules.pullbackId x.total).app x.lineBundle ≪≫ φ.symm

end AlgebraicGeometry

end
