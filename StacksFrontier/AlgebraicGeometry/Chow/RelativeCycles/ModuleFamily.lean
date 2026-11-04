module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The family of cycles associated to a module

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `r ≥ 0` be an integer, and
let `F` be a quasi-coherent `𝒪_X`-module of finite type. Write `F_s` for the pullback of `F` to
the scheme-theoretic fibre `X_s`, and assume `dim (Supp F_s) ≤ r` for every point `s` of `S`.

The fibre `X_s` is locally of finite type over the residue field `κ(s)`, hence locally
Noetherian, so `F_s` — quasi-coherent and of finite type, both properties being stable under
pullback — is coherent. The dimension assumption says exactly that the support of `F_s` has
delta-dimension at most `r` for the Chow situation on `Spec κ(s)`, so the cycle `[F_s]_r` is
defined on every fibre, and `s ↦ [F_s]_r` is a family of `r`-cycles on the fibres of `X/S`:
the family `[F/X/S]_r`.

## Main definitions

* `Stacks.Chow.familyAssociatedToModule` — the family `[F/X/S]_r`.

## Main results

* `Stacks.Chow.relativeDimension_le_of_mem_of_topologicalKrullDim_le` — over a Jacobson base
  whose dimension function vanishes at closed points, the relative dimension at a point is at
  most the dimension of any closed subset containing that point.
* `Stacks.Chow.fiberModule_isCoherent` — `F_s` is coherent.
* `Stacks.Chow.fiberModule_schemeDeltaDimension_le` — the hypothesis `dim (Supp F_s) ≤ r`
  supplies the delta-dimension bound that `[F_s]_r` requires.
* `Stacks.Chow.familyAssociatedToModule_apply` — the member of `[F/X/S]_r` over `s` is `[F_s]_r`.
* `Stacks.Chow.familyAssociatedToModule_apply_coeff` — its coefficients are the lengths of the
  stalks of `F_s` at the points of `Supp F_s` whose closure has delta-dimension `r`, and zero
  elsewhere.

## Implementation notes

The delta-dimension bound is deduced pointwise. By
`Stacks.Chow.schemeDeltaDimension_reducedSupport_le_iff` it suffices to bound the relative
dimension at each point `x` of `Supp F_s`, and that bound is Stacks 02QO applied to the integral
closed subscheme `closure {x}` of the fibre: its dimension is the relative dimension at `x`, and
it is contained in the closed set `Supp F_s`, whose dimension is at most `r` by hypothesis. No
separate argument is needed when the support is empty, where the bound is the empty supremum.

The base of the Chow situation on a residue field is the spectrum of a field, which is a
Jacobson space; the instance is supplied where it is used rather than imported, since the
module that registers it globally also carries the whole projective-line tower.

## References

* [Stacks Project, Tag 0H4Q](https://stacks.math.columbia.edu/tag/0H4Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}}

/-- The scheme-theoretic fibre of a morphism locally of finite type is locally of finite type
over the residue field of the point it lies over, being the base change of that morphism along
`Spec κ(s) ⟶ S`. -/
@[ega "I 6.4.11" "partial"]
instance fiberToSpecResidueField_locallyOfFiniteType (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))

/-! ### Relative dimension and the dimension of a closed subset -/

/-- **Stacks 02QO.** Over a Jacobson base whose dimension function vanishes at closed points,
the relative dimension at a point `x` is at most the topological dimension of any closed subset
containing `x`: the closure of `x` is an integral closed subscheme of that subset, and its
dimension is the relative dimension at `x`. -/
theorem relativeDimension_le_of_mem_of_topologicalKrullDim_le (C : ChowSituation.{u})
    [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] {T : Set Y} (hT : IsClosed T)
    {r : ℕ} (hdim : topologicalKrullDim T ≤ (r : WithBot ℕ∞)) {x : Y} (hx : x ∈ T) :
    relativeDimension C.dimensionFunction p x ≤ (r : ℤ) := by
  let J : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})
  have hJsupp : (J.support : Set Y) = closure ({x} : Set Y) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IrreducibleSpace J.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme Y J (by
      rw [J.range_subschemeι, hJsupp]
      exact isIrreducible_singleton.closure)
  have : IsIntegral J.subscheme := isIntegral_of_irreducibleSpace_of_isReduced J.subscheme
  have hJη : IsGenericPoint (J.subschemeι (genericPoint J.subscheme))
      (closure ({x} : Set Y)) := by
    rw [isGenericPoint_def, ← Set.image_singleton,
      J.subschemeι.isClosedEmbedding.closure_image_eq, genericPoint_closure, Set.image_univ,
      J.range_subschemeι, hJsupp]
  have hJdim : topologicalKrullDim J.subscheme ≤ (r : WithBot ℕ∞) := by
    calc topologicalKrullDim J.subscheme
        = topologicalKrullDim (closure ({x} : Set Y)) :=
          IsHomeomorph.topologicalKrullDim_eq _ (J.subschemeIso.hom.homeomorph.trans
            (J.gluedHomeo.trans (Homeomorph.setCongr hJsupp))).isHomeomorph
      _ ≤ topologicalKrullDim T :=
          Topology.IsInducing.topologicalKrullDim_le
            (Topology.IsEmbedding.inclusion
              (closure_minimal (Set.singleton_subset_iff.mpr hx) hT)).isInducing
      _ ≤ (r : WithBot ℕ∞) := hdim
  have heq := topologicalKrullDim_eq_relativeDimension_toNat C hδ p J.subschemeι
    (genericPoint J.subscheme) (genericPoint_spec J.subscheme)
  rw [hJη.eq isGenericPoint_closure] at heq
  rw [heq] at hJdim
  have hnat : (relativeDimension C.dimensionFunction p x).toNat ≤ r := by exact_mod_cast hJdim
  have hnonneg := relativeDimension_nonneg C hδ p x
  omega

/-! ### The module on a fibre -/

/-- The pullback of a quasi-coherent module of finite type to a scheme-theoretic fibre of a
morphism locally of finite type is coherent: the fibre is locally of finite type over the
residue field of the point it lies over, hence locally Noetherian, and quasi-coherence
(Stacks 01BG) and finite type (Stacks 01B6) are both stable under pullback. -/
instance fiberModule_isCoherent (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (s : S) :
    ((Scheme.Modules.pullback (f.fiberι s)).obj F).IsCoherent :=
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- The dimension bound on the support of the module on each fibre is the delta-dimension bound
that the associated cycle of Stacks 02QX requires: a point of the support lies in the closed set
`Supp F_s`, whose dimension is at most `r`, so its relative dimension over `Spec κ(s)` is at
most `r`. -/
theorem fiberModule_schemeDeltaDimension_le (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) (s : S) :
    schemeDeltaDimension (fieldChowSituation (S.residueField s))
        ((reducedSupport ((Scheme.Modules.pullback (f.fiberι s)).obj F)).subschemeι ≫
          f.fiberToSpecResidueField s) ≤ ((r : ℤ) : EInt) := by
  have : JacobsonSpace (fieldChowSituation (S.residueField s)).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of (S.residueField s))))
  rw [schemeDeltaDimension_reducedSupport_le_iff]
  intro x hx
  exact relativeDimension_le_of_mem_of_topologicalKrullDim_le _ (fun _ _ ↦ rfl) _
    (SheafOfModules.isClosed_supp _) (hdim s) hx

/-! ### The family of cycles -/

/-- **Stacks 0H4Q.** The family `[F/X/S]_r` of `r`-cycles on the fibres of `f` attached to a
quasi-coherent module `F` of finite type whose support on every fibre has dimension at most
`r`: its member over `s` is the cycle `[F_s]_r` associated to the pullback of `F` to the fibre
over `s`. -/
@[stacks 0H4Q "the associated family"]
def familyAssociatedToModule (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) :
    FamilyOfCycles f r :=
  fun s =>
    cycleAssociatedToCoherentSheaf (fieldChowSituation (S.residueField s))
      (f.fiberToSpecResidueField s) ((Scheme.Modules.pullback (f.fiberι s)).obj F) (r : ℤ)
      (fiberModule_schemeDeltaDimension_le f F r hdim s)

/-- **Stacks 0H4Q.** The member of `[F/X/S]_r` over a point `s` of the base is the cycle
`[F_s]_r` associated to the pullback of `F` to the fibre over `s`. -/
@[stacks 0H4Q "fibrewise formula"]
theorem familyAssociatedToModule_apply (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) (s : S) :
    familyAssociatedToModule f F r hdim s =
      cycleAssociatedToCoherentSheaf (fieldChowSituation (S.residueField s))
        (f.fiberToSpecResidueField s) ((Scheme.Modules.pullback (f.fiberι s)).obj F) (r : ℤ)
        (fiberModule_schemeDeltaDimension_le f F r hdim s) :=
  rfl

/-- The coefficients of `[F/X/S]_r` on the fibre over `s`: at a point of `Supp F_s` whose
closure has delta-dimension `r` the coefficient is the length of the stalk of `F_s` there, and
it is zero at every other point. -/
theorem familyAssociatedToModule_apply_coeff (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) (s : S) (x : f.fiber s) :
    (familyAssociatedToModule f F r hdim s).1 x =
      open Classical in
      if x ∈ SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F) ∧
          relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
            (f.fiberToSpecResidueField s) x = (r : ℤ) then
        sheafMultiplicity ((Scheme.Modules.pullback (f.fiberι s)).obj F) x
      else 0 :=
  cycleAssociatedToCoherentSheaf_apply (fieldChowSituation (S.residueField s))
    (f.fiberToSpecResidueField s) ((Scheme.Modules.pullback (f.fiberι s)).obj F) (r : ℤ)
    (fiberModule_schemeDeltaDimension_le f F r hdim s) x

end Stacks.Chow

end
