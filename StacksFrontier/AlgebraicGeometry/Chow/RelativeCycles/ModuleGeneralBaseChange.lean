module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GeneralBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictionBijection
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the family of cycles of a module along an arbitrary morphism of bases

Let `f : X ⟶ S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type whose support on every fibre of `f` has dimension at most `r`, and let `g : S' ⟶ S` be an
arbitrary morphism of schemes. Write `F'` for the pullback of `F` to `X ×_S S'`. The fibre of
`X ×_S S' ⟶ S'` over a point `t` is the base change of the fibre of `f` over `g t` along the
extension `κ(t)/κ(g t)` of residue fields induced by `g`; that extension is flat and its
dimension shift vanishes, so the support of `F'` on the fibre over `t` is the inverse image of
the support of `F` on the fibre over `g t`, no point of it has larger delta-dimension than its
image, and the dimension bound survives. The family of cycles associated to `F'` is then the
base change of the family associated to `F`, which is the cycle identity of Stacks 0FVI part (2)
read on the fibres.

Nothing is assumed about `g`: the residue field extension `κ(t)/κ(g t)` is arbitrary, so the
flat pullback of cycles along a morphism locally of finite type is unavailable and the base
change of cycle groups attached to a flat change of the base scheme is used instead.

## Main results

* `Stacks.Chow.supportDimension_le_of_baseChange_general` — the fibrewise dimension bound on the
  support of a quasi-coherent module of finite type survives base change along an arbitrary
  morphism of bases.
* `Stacks.Chow.familyAssociatedToModule_baseChange_general` — the base change of `[F/X/S]_r`
  along an arbitrary morphism of bases is the family associated to the pulled-back module.

## Implementation notes

The base change of the family is computed fibrewise through
`Stacks.Chow.baseChangeFamily_eq_baseChangeFiberCycle`, which exhibits it as the base change of
cycle groups along the residue field extension followed by restriction along the canonical
isomorphism `(X ×_S S')_t ≅ X_{g t} ×_{κ(g t)} κ(t)`. The base change of cycle groups is matched
with the base change of the module by Stacks 0FVI part (2); since the dimension shift of a field
extension vanishes, the degree `r + c` occurring there is the degree `r`, and the two are
identified definitionally rather than by a cast. Transport across the canonical isomorphism of
fibres is restriction of cycles along an open immersion, which changes neither the multiplicity
of a module nor the relative dimension of a point, and the two modules on the fibre of the base
change obtained by pulling `F` back in the two possible orders are compared by the
pullback-composition isomorphism.

## References

* [Stacks Project, Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S S' : Scheme.{u}}

/-- Restriction of the cycle of a coherent sheaf along an open immersion over the base is the
cycle of the restricted sheaf: an open immersion changes neither the relative dimension of a
point nor the multiplicity of a module there, and the support is assumed to be carried over by
the same hypothesis. The restricted sheaf is presented as an arbitrary module isomorphic to the
pullback, which is how it arises on a fibre of a base change. -/
private theorem cycleGroupRestrict_cycleAssociatedToCoherentSheaf (C : ChowSituation.{u})
    {Y U : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (j : U ⟶ Y) [IsOpenImmersion j] (hj : j ≫ sY = sU) (k : ℤ)
    (N : Y.Modules) [N.IsCoherent] (P : U.Modules) [P.IsCoherent]
    (e : (Scheme.Modules.pullback j).obj N ≅ P)
    (hsupp : ∀ z : U, z ∈ SheafOfModules.supp P ↔ j.base z ∈ SheafOfModules.supp N)
    (hN : schemeDeltaDimension C ((reducedSupport N).subschemeι ≫ sY) ≤ (k : EInt))
    (hP : schemeDeltaDimension C ((reducedSupport P).subschemeι ≫ sU) ≤ (k : EInt)) :
    cycleGroupRestrict C sY sU j hj k (cycleAssociatedToCoherentSheaf C sY N k hN) =
      cycleAssociatedToCoherentSheaf C sU P k hP := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [cycleGroupRestrict_apply, cycleAssociatedToCoherentSheaf_apply,
    cycleAssociatedToCoherentSheaf_apply]
  have hd : relativeDimension C.dimensionFunction sY (j.base z) =
      relativeDimension C.dimensionFunction sU z := by
    rw [← hj, relativeDimension_comp_isOpenImmersion]
  have hm : sheafMultiplicity N (j.base z) = sheafMultiplicity P z :=
    (sheafMultiplicity_pullback_of_isOpenImmersion j N z).symm.trans
      (sheafMultiplicity_eq_of_iso e z)
  rw [hd, hm]
  simp only [hsupp z]

/-- **Stacks Project, Tag 0H4R.** The fibrewise support dimension bound on a quasi-coherent
module of finite type survives base change along an arbitrary morphism of bases: the fibre of
`X ×_S S' ⟶ S'` over `t` is the base change of the fibre of `f` over `g t` along the residue
field extension `κ(t)/κ(g t)`, the support of the pulled-back module on it is the inverse image
of the support on the fibre over `g t`, and no point of the former has larger delta-dimension
than its image. -/
@[stacks 0H4R "module_base_change, arbitrary morphism of bases: dimension bound"]
theorem supportDimension_le_of_baseChange_general (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) :
    ∀ t : S', topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F))) ≤ (r : WithBot ℕ∞) := by
  intro t
  have : JacobsonSpace (fieldChowSituation (S.residueField (g t))).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of (S.residueField (g t)))))
  refine topologicalKrullDim_supp_le_of_field_schemeDeltaDimension_le
    (S'.residueField t) ((pullback.snd f g).fiberToSpecResidueField t) _ r ?_
  have key : schemeDeltaDimension (fieldChowSituation (S'.residueField t))
      ((reducedSupport ((Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F))).subschemeι ≫
        (pullback.snd f g).fiberToSpecResidueField t) ≤ ((r : ℤ) : EInt) := by
    rw [schemeDeltaDimension_reducedSupport_le_iff]
    intro x hx
    rw [supp_pullback_fiberι_baseChange f g F t] at hx
    refine le_trans (relativeDimension_le_of_restrictedFiberMap f g t x) ?_
    exact relativeDimension_le_of_mem_of_topologicalKrullDim_le _ (fun _ _ ↦ rfl) _
      (SheafOfModules.isClosed_supp _) (hdim (g t)) hx
  exact_mod_cast key

/-- **Stacks Project, Tag 0H4R.** Base change of the family `[F/X/S]_r` of cycles associated to a
quasi-coherent module of finite type along an *arbitrary* morphism `g : S' ⟶ S` of bases is the
family associated to the pulled-back module.

The fibre of `X ×_S S' ⟶ S'` over a point `t` is the base change of the fibre of `f` over `g t`
along the residue field extension `κ(t)/κ(g t)`. That extension is flat and the dimension shift
of the associated base change of Chow situations vanishes, so Stacks 0FVI part (2) applies and
identifies the base change of the cycle `[F_{g t}]_r` with the cycle of the base-changed module;
transporting the result along the canonical isomorphism of fibres, which is an open immersion,
changes neither multiplicities nor relative dimensions. -/
@[stacks 0H4R "module_base_change, arbitrary morphism of bases"]
theorem familyAssociatedToModule_baseChange_general (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        (r : WithBot ℕ∞)) :
    baseChangeFamily f g r (familyAssociatedToModule f F r hdim) =
      familyAssociatedToModule (pullback.snd f g)
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F) r
        (supportDimension_le_of_baseChange_general f g F r hdim) := by
  classical
  funext t
  have : IsLocallyNoetherian (pullback (f.fiberToSpecResidueField (g t))
      (residueFieldBaseChangeSituation g t).g : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (f.fiberToSpecResidueField (g t))
      (residueFieldBaseChangeSituation g t).g)
  have : ((Scheme.Modules.pullback (pullback.fst (f.fiberToSpecResidueField (g t))
      (residueFieldBaseChangeSituation g t).g)).obj
      ((Scheme.Modules.pullback (f.fiberι (g t))).obj F)).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback _ _
  have : IsOpenImmersion (fibreBaseChangeIso f g t).hom := inferInstance
  have hN : schemeDeltaDimension (fieldChowSituation (S'.residueField t))
      ((reducedSupport ((Scheme.Modules.pullback (pullback.fst
          (f.fiberToSpecResidueField (g t))
          (residueFieldBaseChangeSituation g t).g)).obj
          ((Scheme.Modules.pullback (f.fiberι (g t))).obj F))).subschemeι ≫
        pullback.snd (f.fiberToSpecResidueField (g t))
          (residueFieldBaseChangeSituation g t).g) ≤ ((r : ℤ) : EInt) :=
    schemeDeltaDimension_baseChange_support_le (residueFieldBaseChangeSituation g t)
      (f.fiberToSpecResidueField (g t)) ((Scheme.Modules.pullback (f.fiberι (g t))).obj F)
      (fiberModule_schemeDeltaDimension_le f F r hdim (g t))
  have hA : baseChangeCyclePullback (residueFieldBaseChangeSituation g t)
        (f.fiberToSpecResidueField (g t)) (r : ℤ)
        (familyAssociatedToModule f F r hdim (g t)) =
      cycleAssociatedToCoherentSheaf (fieldChowSituation (S'.residueField t))
        (pullback.snd (f.fiberToSpecResidueField (g t))
          (residueFieldBaseChangeSituation g t).g)
        ((Scheme.Modules.pullback (pullback.fst (f.fiberToSpecResidueField (g t))
          (residueFieldBaseChangeSituation g t).g)).obj
          ((Scheme.Modules.pullback (f.fiberι (g t))).obj F)) (r : ℤ) hN :=
    baseChangeCyclePullback_cycleAssociatedToCoherentSheaf (residueFieldBaseChangeSituation g t)
      (f.fiberToSpecResidueField (g t)) ((Scheme.Modules.pullback (f.fiberι (g t))).obj F)
      (r : ℤ) (fiberModule_schemeDeltaDimension_le f F r hdim (g t))
  have e : (Scheme.Modules.pullback (fibreBaseChangeIso f g t).hom).obj
        ((Scheme.Modules.pullback (pullback.fst (f.fiberToSpecResidueField (g t))
          (residueFieldBaseChangeSituation g t).g)).obj
          ((Scheme.Modules.pullback (f.fiberι (g t))).obj F)) ≅
      (Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F) :=
    (Scheme.Modules.pullbackComp (fibreBaseChangeIso f g t).hom
        (pullback.fst (f.fiberToSpecResidueField (g t))
          (residueFieldBaseChangeSituation g t).g)).app
        ((Scheme.Modules.pullback (f.fiberι (g t))).obj F) ≪≫
      (Scheme.Modules.pullbackCongr (fibreBaseChangeIso_hom_fst f g t)).app
        ((Scheme.Modules.pullback (f.fiberι (g t))).obj F) ≪≫
      (Scheme.Modules.pullbackComp (restrictedFiberMap f (pullback.snd f g)
        (pullback.fst f g) g pullback.condition t) (f.fiberι (g t))).app F ≪≫
      (Scheme.Modules.pullbackCongr (restrictedFiberMap_fiberι f (pullback.snd f g)
        (pullback.fst f g) g pullback.condition t)).app F ≪≫
      ((Scheme.Modules.pullbackComp ((pullback.snd f g).fiberι t)
        (pullback.fst f g)).app F).symm
  have hsupp : ∀ z : (pullback.snd f g).fiber t,
      z ∈ SheafOfModules.supp ((Scheme.Modules.pullback ((pullback.snd f g).fiberι t)).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ↔
        (fibreBaseChangeIso f g t).hom.base z ∈ SheafOfModules.supp
          ((Scheme.Modules.pullback (pullback.fst (f.fiberToSpecResidueField (g t))
            (residueFieldBaseChangeSituation g t).g)).obj
            ((Scheme.Modules.pullback (f.fiberι (g t))).obj F)) := by
    intro z
    rw [supp_pullback_fiberι_baseChange f g F t,
      SheafOfModules.supp_pullback (pullback.fst (f.fiberToSpecResidueField (g t))
        (residueFieldBaseChangeSituation g t).g)
        ((Scheme.Modules.pullback (f.fiberι (g t))).obj F),
      Set.mem_preimage, Set.mem_preimage, fst_fibreBaseChangeIso_hom f g t z]
  refine (baseChangeFamily_eq_baseChangeFiberCycle f g r _ t).trans ?_
  refine Eq.trans ?_ (cycleGroupRestrict_cycleAssociatedToCoherentSheaf
    (fieldChowSituation (S'.residueField t))
    (pullback.snd (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
    ((pullback.snd f g).fiberToSpecResidueField t) (fibreBaseChangeIso f g t).hom
    (fibreBaseChangeIso_hom_snd f g t) (r : ℤ) _ _ e hsupp hN
    (fiberModule_schemeDeltaDimension_le (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F) r
      (supportDimension_le_of_baseChange_general f g F r hdim) t))
  rw [← hA]
  rfl

end Stacks.Chow

end
