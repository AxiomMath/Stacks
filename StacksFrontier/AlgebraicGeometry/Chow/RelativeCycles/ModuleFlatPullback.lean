module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatPullbackFamily
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback of the family of cycles associated to a module

Let `f : X ⟶ S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type whose support on every fibre of `f` has dimension at most `r`, and let `j : U ⟶ X` be flat,
locally of finite type and of relative dimension `e`, viewed as a morphism of schemes over `S`
through an identity `j ≫ f = f_U`. On the fibre over `s` the morphism `U_s ⟶ X_s` induced by `j`
is again flat, locally of finite type and of relative dimension `e`, the support of `j^*F` on
`U_s` is the inverse image of the support of `F` on `X_s`, and that inverse image has dimension
at most `r + e`. So `j^*F` again satisfies the hypothesis of Example 0H4Q, in degree `r + e`, and
the family of cycles associated to it is the flat pullback of the family associated to `F`.

## Main results

* `Stacks.Chow.supportDimension_le_of_flatPullback` — the fibrewise dimension bound on the
  support passes to `j^*F` with `r` replaced by `r + e`.
* `Stacks.Chow.familyAssociatedToModule_flatPullback` — the flat pullback of `[F/X/S]_r` along
  `j` is the family `[j^*F/U/S]_{r+e}`.

## Implementation notes

Both statements are read on one fibre at a time, where they become the two halves of
Stacks 02RE, part (2), for the morphism of fibres `U_s ⟶ X_s`: the support dimension bound
`Stacks.Chow.schemeDeltaDimension_support_pullback_le` and the cycle identity
`Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf`. The dimension hypothesis of
Example 0H4Q is a bound on the topological dimension of the fibrewise support while 02RE speaks
of delta-dimensions over the residue field; the two are exchanged by
`Stacks.Chow.fiberModule_schemeDeltaDimension_le` and
`Stacks.Chow.topologicalKrullDim_supp_le_of_field_schemeDeltaDimension_le`, as in the base-change
clause of the same tag.

The module on the fibre of `U` obtained by pulling `F` back in the two possible orders —
restricting to `U` and then to the fibre of `f_U`, or passing to the fibre of `f` and then along
the induced morphism of fibres — is compared by the pullback-composition isomorphism, exactly as
in the restriction clause; nothing is recomputed from the two presentations.

## References

* [Stacks Project, Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S U : Scheme.{u}}

/-- Comparison of the two ways of pulling a module back to the fibre of `U/S` over `s`:
restricting along `j` and then pulling back to the fibre of `f_U`, or pulling back to the fibre
of `f` over `s` and then along the induced morphism of fibres. -/
private def fiberFlatPullbackIso (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X) (h : j ≫ f = fU)
    (F : X.Modules) (s : S) :
    (Scheme.Modules.pullback (fU.fiberι s)).obj ((Scheme.Modules.pullback j).obj F) ≅
      (Scheme.Modules.pullback (fiberRestrict f fU j h s)).obj
        ((Scheme.Modules.pullback (f.fiberι s)).obj F) :=
  (Scheme.Modules.pullbackComp (fU.fiberι s) j).app F ≪≫
    (Scheme.Modules.pullbackCongr (fiberRestrict_fiberι f fU j h s).symm).app F ≪≫
      ((Scheme.Modules.pullbackComp (fiberRestrict f fU j h s) (f.fiberι s)).app F).symm

/-! ### The dimension bound -/

/-- The pullback of `F` to the fibre of `f` and then along the induced morphism of fibres is
coherent. -/
private theorem isCoherent_pullback_fiberRestrict (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) (h : j ≫ f = fU) (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (s : S) :
    ((Scheme.Modules.pullback (fiberRestrict f fU j h s)).obj
      ((Scheme.Modules.pullback (f.fiberι s)).obj F)).IsCoherent := by
  have : IsLocallyNoetherian (fU.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (fU.fiberToSpecResidueField s)
  exact AlgebraicGeometry.isCoherent_pullback _ _

/-- **Stacks Project, Tag 0H4R.** The fibrewise support dimension bound on a quasi-coherent
module of finite type passes to its pullback along a flat morphism `j : U ⟶ X` of schemes over
`S`, locally of finite type and of relative dimension `e`, with `r` replaced by `r + e`: on the
fibre over `s` this is the support dimension bound of Stacks 02RE, part (2), for the induced
morphism `U_s ⟶ X_s`, which is again flat of relative dimension `e`. -/
@[stacks 0H4R "module_flat_pullback: dimension bound"]
theorem supportDimension_le_of_flatPullback (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ S)
    [LocallyOfFiniteType fU] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU)
    (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) :
    ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (fU.fiberι s)).obj
        ((Scheme.Modules.pullback j).obj F))) ≤ ((r + e : ℕ) : WithBot ℕ∞) := by
  intro s
  have := isCoherent_pullback_fiberRestrict f fU j h F s
  refine topologicalKrullDim_supp_le_of_field_schemeDeltaDimension_le
    (S.residueField s) (fU.fiberToSpecResidueField s) _ (r + e) ?_
  have key : schemeDeltaDimension (fieldChowSituation (S.residueField s))
      ((reducedSupport ((Scheme.Modules.pullback (fU.fiberι s)).obj
          ((Scheme.Modules.pullback j).obj F))).subschemeι ≫
        fU.fiberToSpecResidueField s) ≤ (((r : ℤ) + (e : ℤ) : ℤ) : EInt) := by
    rw [schemeDeltaDimension_reducedSupport_le_iff]
    intro x hx
    refine relativeDimension_le_of_mem_supp (fieldChowSituation (S.residueField s))
      (fU.fiberToSpecResidueField s) _
      (schemeDeltaDimension_support_pullback_le (fieldChowSituation (S.residueField s))
        (fU.fiberToSpecResidueField s) (f.fiberToSpecResidueField s)
        (fiberRestrict f fU j h s) (fiberRestrict_fiberToSpecResidueField f fU j h s) e
        (relativeDimension_fiberRestrict f fU j h s he)
        ((Scheme.Modules.pullback (f.fiberι s)).obj F) (r : ℤ)
        (fiberModule_schemeDeltaDimension_le f F r hdim s)) ?_
    rwa [SheafOfModules.supp_eq_of_iso (fiberFlatPullbackIso f fU j h F s)] at hx
  exact_mod_cast key

/-! ### Flat pullback of the associated family -/

/-- **Stacks Project, Tag 0H4R.** The flat pullback of the family `[F/X/S]_r` of cycles
associated to a quasi-coherent module of finite type, along a flat morphism `j : U ⟶ X` of
schemes over `S` which is locally of finite type and of relative dimension `e`, is the family
`[j^*F/U/S]_{r+e}` associated to the pulled-back module.

On the fibre over `s` the morphism `U_s ⟶ X_s` induced by `j` is flat, locally of finite type and
of relative dimension `e`, so Stacks 02RE, part (2), identifies the flat pullback of the cycle
`[F_s]_r` with the cycle of the pullback of `F_s`; that pullback is the restriction of `j^*F` to
the fibre of `f_U`, the two orders of pulling `F` back being compared by the
pullback-composition isomorphism. -/
@[stacks 0H4R "module_flat_pullback"]
theorem familyAssociatedToModule_flatPullback (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ S)
    [LocallyOfFiniteType fU] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU)
    (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) :
    flatPullbackFamily f fU j h e he r (familyAssociatedToModule f F r hdim) =
      familyAssociatedToModule fU ((Scheme.Modules.pullback j).obj F) (r + e)
        (supportDimension_le_of_flatPullback f fU j h e he F r hdim) := by
  funext s
  have := isCoherent_pullback_fiberRestrict f fU j h F s
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  rw [flatPullbackFamily_apply, familyAssociatedToModule_apply,
    familyAssociatedToModule_apply]
  refine Eq.trans (flatPullback_cycleAssociatedToCoherentSheaf
    (fieldChowSituation (S.residueField s)) (fU.fiberToSpecResidueField s)
    (f.fiberToSpecResidueField s) (fiberRestrict f fU j h s)
    (fiberRestrict_fiberToSpecResidueField f fU j h s) e
    (relativeDimension_fiberRestrict f fU j h s he)
    ((Scheme.Modules.pullback (f.fiberι s)).obj F) (r : ℤ)
    (fiberModule_schemeDeltaDimension_le f F r hdim s)) ?_
  exact cycleAssociatedToCoherentSheaf_eq_of_iso' (fieldChowSituation (S.residueField s))
    (fU.fiberToSpecResidueField s) _ _ _ _ _ (fiberFlatPullbackIso f fU j h F s).symm

end Stacks.Chow

end
