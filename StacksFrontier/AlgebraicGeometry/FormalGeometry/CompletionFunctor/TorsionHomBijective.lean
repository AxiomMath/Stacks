module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHomCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksCore.Tactic.StacksAttribute

/-!
# Completion is bijective on morphisms when one side is ideal-power torsion

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X` and `ℱ`, `𝒢`
coherent `𝒪_X`-modules, and suppose a power of `ℐ` annihilates `ℱ` or `𝒢`. Then

`Hom_X(ℱ, 𝒢) ⟶ Hom_{Coh(X, ℐ)}(ℱ^∧, 𝒢^∧)`,

the map on morphisms of the completion functor of Stacks 0880, is bijective. This is the `Hom`
half of the second assertion of [Stacks, Tag 0EHP]; the tag itself is registered at
`Stacks.Algebraization.essImage_and_bijective_of_isPowerAnnihilated`.

The proof is the one in the source. Put `ℋ = SheafHom(ℱ, 𝒢)`. Whichever of the two modules a
power of `ℐ` annihilates, that same power annihilates `ℋ`, so the completion of `ℋ` is the
constant system `ℋ` and the canonical map `ℋ ⟶ lim ℋ / ℐ ⁿ⁺¹ ℋ` is an isomorphism. By the
comparison of [Stacks, Tag 0882] — which is an isomorphism, and which carries that canonical map
to `SheafHom(ℱ, –)` of the canonical map of `𝒢` — the morphism
`SheafHom(ℱ, 𝒢) ⟶ SheafHom(ℱ, lim 𝒢 / ℐ ⁿ⁺¹ 𝒢)` is then an isomorphism too. Taking global
sections, postcomposition with `𝒢 ⟶ lim 𝒢 / ℐ ⁿ⁺¹ 𝒢` is bijective on morphisms out of `ℱ`; and
morphisms `ℱ ⟶ lim 𝒢 / ℐ ⁿ⁺¹ 𝒢` are morphisms `ℱ^∧ ⟶ 𝒢^∧` by the adjunction of
`Stacks.Algebraization.completionHomLimitEquiv`, compatibly with the completion functor.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_sheafHom_eq_bot_of_source` — a power of `ℐ`
  annihilating the *source* annihilates the internal hom. The companion statement for the target
  is `Stacks.Algebraization.idealPowerMultiple_sheafHom_eq_bot`.
* `Stacks.Algebraization.isIso_completionToLimit_of_isPowerAnnihilated` — a coherent module
  annihilated by a power of `ℐ` is the limit of its own completion.
* `Stacks.Algebraization.isIso_sheafHomFunctor_map_completionToLimit` — if a power of `ℐ`
  annihilates `SheafHom(ℱ, 𝒢)` then `SheafHom(ℱ, –)` of the canonical map of `𝒢` into the limit
  of its completion is an isomorphism.
* `Stacks.Algebraization.bijective_comp_completionToLimit` — hence postcomposition with that
  canonical map is bijective on morphisms out of `ℱ`.
* `Stacks.Algebraization.homToAdicSystem_comp_completionToLimit` — the adjunct of
  `f` followed by the canonical map is the completion of `f`.
* `Stacks.Algebraization.completionFunctor_map_bijective_of_isPowerAnnihilated` — the map on
  morphisms is bijective.

## Implementation notes

Stacks states the lemma for a Noetherian scheme. Only local Noetherianness is used, as in
`Stacks.Algebraization.completionInternalHomEquiv` (Stacks 0882), so the statements below ask only
for `IsLocallyNoetherian X`; a Noetherian scheme is one.

The conclusion is bijectivity of the canonical map rather than an `AddEquiv`. The map is a
homomorphism of abelian groups for formal reasons — the completion functor is additive — so
bijectivity is the whole of the source's assertion that it is an isomorphism, and stating it this
way keeps the statement about the completion functor's own action on morphisms instead of about a
separately constructed equivalence.

Annihilation of `ℋ = SheafHom(ℱ, 𝒢)` by a power of `ℐ` is proved sectionwise in both cases. For
the target it is `idealPowerMultiple_sheafHom_eq_bot` on main; for the source the same scalar
`r` is moved across the section `α` by linearity, `r • α` being computed componentwise by
`Stacks.SheafOfModules.internalHom_smul_app_apply`, and `r • x = 0` is then checked on the affine
opens refining the component's domain by `Stacks.Algebraization.section_eq_zero_of_affine`.

That a power-annihilated coherent `ℋ` is the limit of its own completion is proved by exhibiting
the inverse, not by showing that the projections form a limit cone: with `ℐ ᵈ⁺¹ ℋ = 0` every
projection `ℋ ⟶ ℋ / ℐ ⁿ⁺¹ ℋ` with `d ≤ n` is invertible, so `lim.π_d` followed by the inverse of
the `d`-th projection is a two-sided inverse, the second identity being checked against each
`lim.π` and splitting into the cases `n ≤ d` and `d ≤ n`.

The composites below are written as explicit `Category.assoc`/`congrArg`/`Eq.trans` chains rather
than `rw` calls: `AlgebraicGeometry.Scheme.Modules` is a `def` for
`SheafOfModules X.ringCatSheaf` and the two presentations carry separate instances, so a rewrite
motive mixing them is not type correct at the transparency `rw` builds it at.

## References

* [Stacks Project, Tag 0EHP](https://stacks.math.columbia.edu/tag/0EHP)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.SheafOfModules.InternalHom

/-! ### The internal hom is annihilated by a power annihilating its source -/

/-- **A power of `ℐ` annihilating the source annihilates the internal hom.** A section of
`SheafHom(G, N)` over `U` is a morphism `G|_U ⟶ N|_U` on the slice site, and `r • α` multiplies
each of its components by a restriction of `r`; by linearity that is `α` applied to `r` times a
section of `G`, which vanishes.

The companion statement for the target is
`Stacks.Algebraization.idealPowerMultiple_sheafHom_eq_bot`. -/
public theorem idealPowerMultiple_sheafHom_eq_bot_of_source {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (G N : X.Modules)
    (hG : idealPowerMultiple I n G = ⊥) :
    idealPowerMultiple I n ((sheafHomFunctor X G).obj N) = ⊥ := by
  refine le_antisymm ((idealPowerMultiple_le_iff I n _ ⊥).2 fun U => ?_) bot_le
  refine Submodule.smul_le.2 fun r hr α _ => ?_
  refine (SheafOfModules.Submodule.bot_obj _ (op U.1)).ge ((Submodule.mem_bot _).mpr ?_)
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  refine Eq.trans
    (Stacks.SheafOfModules.internalHom_smul_app_apply X.presheaf G.val N.val U.1 r α V x) ?_
  refine Eq.trans ((α.app V).hom.map_smul _ _).symm
    (Eq.trans (congrArg (α.app V).hom ?_) (Eq.trans (map_zero _) rfl))
  · apply section_eq_zero_of_affine G
    intro W i
    refine Eq.trans (Scheme.Modules.map_smul G i _ _) ?_
    have hrW : (X.presheaf.map (i ≫ V.unop.hom).op).hom r ∈ I.ideal W ^ n := by
      rw [← I.map_ideal' (i ≫ V.unop.hom).op, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hr
    have hcomp : (X.presheaf.map i.op).hom (fRestr X.presheaf U.1 r V) =
        (X.presheaf.map (i ≫ V.unop.hom).op).hom r := by
      change (X.presheaf.map i.op).hom ((X.presheaf.map V.unop.hom.op).hom r) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [hcomp]
    exact smul_eq_zero_of_idealPowerMultiple_eq_bot I n G hG W hrW _

variable {X : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X] {I : X.IdealSheafData}

/-! ### A torsion coherent module is the limit of its own completion -/

/-- If `ℐ ⁿ⁺¹ H = 0` then the projection of `H` onto the `n`-th term of its completion is an
isomorphism: it is the quotient projection by the zero subsheaf, transported along the object
formula of Stacks 0880. -/
public theorem isIso_completionProjection_of_idealPowerMultiple_eq_bot
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) {n : ℕ}
    (hbot : idealPowerMultiple I (n + 1) H.obj = ⊥) :
    IsIso (completionProjection X I H n) := by
  have h1 : IsIso (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) H.obj).ι) :=
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot I (n + 1) _ hbot
  have h2 : IsIso (eqToHom (completionFunctor_obj X I H n).symm) := inferInstance
  dsimp only [completionProjection]
  exact IsIso.comp_isIso' h1 h2

/-- **A coherent module annihilated by a power of `ℐ` is the limit of its own completion.**

Writing the annihilating exponent as `d + 1`, every projection `H ⟶ H / ℐ ⁿ⁺¹ H` with `d ≤ n` is
an isomorphism, and the `d`-th limit projection followed by the inverse of the `d`-th projection
is a two-sided inverse of the canonical map. -/
public theorem isIso_completionToLimit_of_isPowerAnnihilated
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hH : IsPowerAnnihilated I H.obj) :
    IsIso (completionToLimit X I H) := by
  obtain ⟨c, hc, hann⟩ := hH.exists_pos
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, c = d + 1 := ⟨c - 1, (Nat.succ_pred_eq_of_pos hc).symm⟩
  have hp : ∀ n : ℕ, d ≤ n → IsIso (completionProjection X I H n) := fun n hdn =>
    isIso_completionProjection_of_idealPowerMultiple_eq_bot H
      (idealPowerMultiple_eq_bot_of_le hann (Nat.add_le_add_right hdn 1))
  have hpd : IsIso (completionProjection X I H d) := hp d le_rfl
  refine ⟨limit.π ((completionFunctor X I).obj H).obj (op d) ≫
    inv (completionProjection X I H d), ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ inv (completionProjection X I H d))
          (completionToLimit_projection X I H (op d))).trans (IsIso.hom_inv_id _))
  · refine limit.hom_ext (F := ((completionFunctor X I).obj H).obj) fun n => ?_
    have hkey : inv (completionProjection X I H d) ≫ completionToLimit X I H ≫
        limit.π ((completionFunctor X I).obj H).obj n =
      inv (completionProjection X I H d) ≫ completionProjection X I H n.unop :=
      congrArg (fun k => inv (completionProjection X I H d) ≫ k)
        (completionToLimit_projection X I H n)
    refine Eq.trans (Category.assoc _ _ _) (Eq.trans (congrArg
      (fun k => limit.π ((completionFunctor X I).obj H).obj (op d) ≫ k)
        (Eq.trans (Category.assoc _ _ _) hkey)) ?_)
    refine Eq.trans ?_ (Category.id_comp _).symm
    rcases le_total d n.unop with hdn | hnd
    · -- above the exponent: the transition `H_n ⟶ H_d` is invertible
      have hpn : IsIso (completionProjection X I H n.unop) := hp n.unop hdn
      have hiso : IsIso (((completionFunctor X I).obj H).obj.map (homOfLE hdn).op) :=
        have : IsIso (completionProjection X I H n.unop ≫
            ((completionFunctor X I).obj H).obj.map (homOfLE hdn).op) := by
          rw [completionProjection_map]; exact hpd
        IsIso.of_isIso_comp_left (completionProjection X I H n.unop) _
      refine (cancel_mono (((completionFunctor X I).obj H).obj.map (homOfLE hdn).op)).1 ?_
      refine Eq.trans (Category.assoc _ _ _) (Eq.trans (congrArg
        (fun k => limit.π ((completionFunctor X I).obj H).obj (op d) ≫ k)
          (Eq.trans (Category.assoc _ _ _) (Eq.trans (congrArg
            (fun k => inv (completionProjection X I H d) ≫ k)
              (completionProjection_map X I H (homOfLE hdn).op))
            (IsIso.inv_hom_id _)))) ?_)
      refine Eq.trans (Category.comp_id _) ?_
      exact (limit.w ((completionFunctor X I).obj H).obj
        (homOfLE hdn).op).symm
    · -- below the exponent: the composite is the transition `H_d ⟶ H_n`
      have hfac : inv (completionProjection X I H d) ≫ completionProjection X I H n.unop =
          ((completionFunctor X I).obj H).obj.map (homOfLE hnd).op :=
        (IsIso.inv_comp_eq (completionProjection X I H d)).mpr
          (completionProjection_map X I H (homOfLE hnd).op).symm
      exact Eq.trans (congrArg
        (fun k => limit.π ((completionFunctor X I).obj H).obj (op d) ≫ k) hfac)
        (limit.w ((completionFunctor X I).obj H).obj (homOfLE hnd).op)

/-! ### Postcomposition with the canonical map into the limit -/

variable (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The internal hom of the canonical map into the limit is an isomorphism** as soon as a power
of `ℐ` annihilates the internal hom `SheafHom(G, F)`.

By Stacks 0882 the comparison from the limit of the completion of `SheafHom(G, F)` to
`SheafHom(G, lim F / ℐ ⁿ⁺¹ F)` is an isomorphism, and it carries the canonical map of
`SheafHom(G, F)` into its limit to the internal hom of the canonical map of `F`. The former is an
isomorphism because `SheafHom(G, F)` is annihilated by a power of `ℐ`. -/
public theorem isIso_sheafHomFunctor_map_completionToLimit
    (hH : IsPowerAnnihilated I (internalHomCoherent X G F).obj) :
    IsIso ((sheafHomFunctor X (coherentObj G)).map (completionToLimit X I F)) := by
  have h1 : IsIso (completionToLimit X I (internalHomCoherent X G F)) :=
    isIso_completionToLimit_of_isPowerAnnihilated _ hH
  have h2 : IsIso (completedSheafHomComparison (I := I) G F) :=
    isIso_completedSheafHomComparison G F
  exact completionToLimit_completedSheafHomComparison G F ▸ IsIso.comp_isIso' h1 h2

/-- **Postcomposition with the canonical map into the limit is bijective on morphisms out of
`G`** as soon as a power of `ℐ` annihilates `SheafHom(G, F)`.

The morphisms out of `G` are the global sections of the internal hom with source `G`, naturally
in the target (`Stacks.Algebraization.internalHomSectionsTopEquiv_map`), so this is the previous
isomorphism read on global sections. -/
public theorem bijective_comp_completionToLimit
    (hH : IsPowerAnnihilated I (internalHomCoherent X G F).obj) :
    Function.Bijective (fun g : coherentObj G ⟶ coherentObj F =>
      g ≫ completionToLimit X I F) := by
  have hiso : IsIso ((sheafHomFunctor X (coherentObj G)).map (completionToLimit X I F)) :=
    isIso_sheafHomFunctor_map_completionToLimit G F hH
  have hev : IsIso (((sheafHomFunctor X (coherentObj G)).map
      (completionToLimit X I F)).val.app (op (⊤ : X.Opens))) :=
    ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapIso
      (@asIso _ _ _ _ ((sheafHomFunctor X (coherentObj G)).map
        (completionToLimit X I F)) hiso)).isIso_hom
  have hb : Function.Bijective (((sheafHomFunctor X (coherentObj G)).map
      (completionToLimit X I F)).val.app (op (⊤ : X.Opens))) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hev
  set eM := internalHomSectionsTopEquiv (coherentObj G) (coherentObj F) with heM
  set eN := internalHomSectionsTopEquiv (coherentObj G)
    (limit ((completionFunctor X I).obj F).obj) with heN
  have hfun : (fun g : coherentObj G ⟶ coherentObj F => g ≫ completionToLimit X I F) =
      fun g => eN (((sheafHomFunctor X (coherentObj G)).map
        (completionToLimit X I F)).val.app (op (⊤ : X.Opens)) (eM.symm g)) := by
    refine funext fun g => ?_
    refine Eq.trans ?_ (internalHomSectionsTopEquiv_map (coherentObj G)
      (completionToLimit X I F) (eM.symm g)).symm
    exact congrArg (fun k => k ≫ completionToLimit X I F) (eM.apply_symm_apply g).symm
  rw [hfun]
  exact eN.bijective.comp (hb.comp eM.symm.bijective)

/-! ### Completion is bijective on morphisms -/

/-- The adjunct of a morphism followed by the canonical map of its target into the limit of its
completion is the completion of that morphism. Both sides are determined by their composites with
the epimorphisms `G ⟶ G / ℐ ⁿ⁺¹ G`. -/
public theorem homToAdicSystem_comp_completionToLimit (f : G ⟶ F) :
    homToAdicSystem G ((completionFunctor X I).obj F)
        (f.hom ≫ completionToLimit X I F) = (completionFunctor X I).map f := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  have hepi : Epi (completionProjection X I G n.unop) := epi_completionProjection X I G n.unop
  refine (cancel_epi (completionProjection X I G n.unop)).1 ?_
  refine Eq.trans (completionProjection_homToAdicSystem G ((completionFunctor X I).obj F)
    (f.hom ≫ completionToLimit X I F) n) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k => f.hom ≫ k)
    (completionToLimit_projection X I F n)) ?_
  exact (completionFunctor_map_quotient X I f n.unop).symm

/-- **Completion is bijective on morphisms when one side is ideal-power torsion.** If `ℱ`, `𝒢`
are coherent `𝒪_X`-modules and a power of `ℐ` annihilates `ℱ` or `𝒢`, then the map

`Hom_X(ℱ, 𝒢) ⟶ Hom_{Coh(X, ℐ)}(ℱ^∧, 𝒢^∧)`

of the completion functor of Stacks 0880 is bijective.

Whichever of the two is annihilated, `SheafHom(ℱ, 𝒢)` is annihilated by the same power, so
postcomposition with the canonical map `𝒢 ⟶ lim 𝒢 / ℐ ⁿ⁺¹ 𝒢` is bijective on morphisms out of
`ℱ`; the adjunction of `Stacks.Algebraization.completionHomLimitEquiv` turns those into
morphisms of the completions, and the completion of `f` is the adjunct of `f` followed by that
canonical map. -/
public theorem completionFunctor_map_bijective_of_isPowerAnnihilated
    (h : IsPowerAnnihilated I G.obj ∨ IsPowerAnnihilated I F.obj) :
    Function.Bijective (fun f : G ⟶ F => (completionFunctor X I).map f) := by
  have hH : IsPowerAnnihilated I (internalHomCoherent X G F).obj := by
    rcases h with hG | hF
    · obtain ⟨m, hm⟩ := hG
      exact ⟨m, idealPowerMultiple_sheafHom_eq_bot_of_source I m (coherentObj G) (coherentObj F) hm⟩
    · obtain ⟨m, hm⟩ := hF
      exact ⟨m, idealPowerMultiple_sheafHom_eq_bot m (coherentObj G) (coherentObj F) hm⟩
  have hhom : Function.Bijective (fun f : G ⟶ F => f.hom) :=
    ⟨fun _ _ hfg => ObjectProperty.hom_ext _ hfg,
      fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
  have hadj : Function.Bijective
      (homToAdicSystem G ((completionFunctor X I).obj F)) :=
    (completionHomLimitEquiv G ((completionFunctor X I).obj F)).bijective
  have hfun : (fun f : G ⟶ F => (completionFunctor X I).map f) =
      fun f => homToAdicSystem G ((completionFunctor X I).obj F)
        (f.hom ≫ completionToLimit X I F) :=
    funext fun f => (homToAdicSystem_comp_completionToLimit G F f).symm
  rw [hfun]
  exact hadj.comp ((bijective_comp_completionToLimit G F hH).comp hhom)

end Stacks.Algebraization

end
