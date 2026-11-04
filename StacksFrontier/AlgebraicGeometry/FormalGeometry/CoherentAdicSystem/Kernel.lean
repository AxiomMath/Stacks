module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.StableKernelLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The kernel in the category of coherent adic systems

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf on `X` and `α : F ⟶ G` a
morphism of coherent adic systems along `ℐ`. This file constructs the kernel of `α` in
`Coh(X, ℐ)`, proves its universal property and shows that it commutes with restriction to an
open subscheme. This is part (1) of Tag 087X.

The kernel is *not* the levelwise kernel: the system `n ↦ ker(α_n)` satisfies neither the
annihilation nor the quotient clause of `Stacks.Coherent.IsCoherentAdicSystem`, and Tag 087X
replaces it by two successive stabilizations. The first replaces `ker(α_n)` by the stable image
`Stacks.Coherent.stableKernelImage` in `F_n` of the kernels at higher levels; the second,
`Stacks.Coherent.stableKernelImageQuotientMap_eventually_isIso`, makes the inverse system of the
completions of those stable images eventually constant in each quotient level. Its limit
`Stacks.Coherent.stableKernelImageLimitSystem` is therefore isomorphic, level by level, to a term
of one of those completions, and all three clauses of a coherent adic system transport along such
an isomorphism. That is `Stacks.Coherent.stableKernelImageLimit_isCoherentAdicSystem`, and the
kernel object `Stacks.Coherent.coherentAdicKernel` is that system together with the proof.

The universal property is proved directly. A morphism `β : H ⟶ F` of coherent adic systems killed
by `α` factors through every stable kernel image: at a level `l` above the stabilization level of
`F_m` the component `β_l` factors through `ker(α_l)` and hence through its image in `F_m`, and the
transition `H_l ⟶ H_m` is an epimorphism while the stable kernel image is a subobject of `F_m`, so
the factorization descends to `H_m`. Composing with the projection onto the `(n+1)`-st adic
quotient and descending once more along the transitions of `H` — possible because the target is
annihilated by `ℐ ⁿ⁺¹` — produces a cone on the double system of completions, whose limiting
morphism is the required factorization. Uniqueness holds because a morphism of coherent adic
systems into the limit system is determined by its composite with the inclusion into `F`: the
comparison `Stacks.Coherent.stableKernelImageCompletionToLevel` at equal levels is a
monomorphism, the stable kernel image at level `n` being already annihilated by `ℐ ⁿ⁺¹` and hence
equal to its own `(n+1)`-st adic quotient.

## Main definitions

* `Stacks.Coherent.coherentAdicKernel` — **the kernel of a morphism of coherent adic systems**,
  and `Stacks.Coherent.coherentAdicKernelι` its inclusion into the source.
* `Stacks.Coherent.coherentAdicKernelToLevelwiseKernel` — the canonical comparison from the
  `n`-th term of the kernel to the kernel of `α_n`.
* `Stacks.Coherent.stableKernelImageLimitπ` — the projection of the limit system onto a term of
  one of the completions, as a component of a natural transformation.
* `Stacks.Coherent.stableKernelImageLift` — the factorization of a morphism killed by `α`
  through a stable kernel image.
* `Stacks.Coherent.stableKernelImageCompletionToLevel` — the comparison from a term of the
  completion of a stable kernel image to a term of `F`.
* `Stacks.Coherent.stableKernelImageLimitIncl` — the inclusion of the limit system into `F`.
* `Stacks.Coherent.stableKernelImageLiftCone` — the cone on the double system built from a
  morphism killed by `α`.

## Main results

* `Stacks.Coherent.stableKernelImageLimit_isCoherentAdicSystem` — **the limit of the double
  system is a coherent adic system.** This is where the second stabilization is consumed.
* `Stacks.Coherent.coherentAdicKernelι_comp` and
  `Stacks.Coherent.coherentAdicKernelIsLimit` — **the universal property of the kernel.**
* `Stacks.Coherent.hasKernel_coherentAdicSystems` and
  `Stacks.Coherent.hasKernels_coherentAdicSystems` — `Coh(X, ℐ)` has all kernels.
* `Stacks.Coherent.kernelImageQuotients_eventuallyConstant` — **the terms of the kernel are the
  adic quotients of the stable kernel images**: for each quotient level `n` the `(n+1)`-st adic
  quotient of the stable kernel image at any sufficiently high level `m` is the `n`-th term of
  the kernel, compatibly with the inclusion into `F_n`.
* `Stacks.Coherent.coherentAdicKernel_restrict` — **the kernel commutes with restriction along an
  open immersion**, canonically over the restricted source system.
* `Stacks.Coherent.exists_coherentAdicSystemDesc` — a morphism from a term of a coherent adic
  system to a module annihilated by `ℐ ⁿ⁺¹` descends to the `n`-th term.

## Implementation notes

The kernel in `Coh(X, ℐ)` is not computed levelwise, so the inclusion
`CategoryTheory.ObjectProperty.ι (Stacks.Coherent.IsCoherentAdicSystem I)` does *not* preserve
it; no such instance is declared here, in contrast with the cokernel. What is true is recorded by
`Stacks.Coherent.coherentAdicKernelToLevelwiseKernel`: the `n`-th term of the kernel maps
canonically to `ker(α_n)` over the inclusions into `F_n`, and
`Stacks.Coherent.kernelImageQuotients_eventuallyConstant` identifies that term with an adic
quotient of a stable kernel image instead.

Unlike the construction of the cokernel, the kernel carries the hypothesis `[IsNoetherian X]`:
both stabilizations rest on it, through Artin–Rees and through the existence of a finite affine
cover.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-- **Annihilation by a power of an ideal sheaf transports along an isomorphism.** If `ℐ ⁿ N`
vanishes and `M ≅ N`, then `ℐ ⁿ M` vanishes: the condition is the vanishing of `a • x` for every
section `x` over an affine open and every `a` in the `n`-th power of the ideal there, and the
isomorphism is injective and linear on those sections. -/
public theorem idealPowerMultiple_eq_bot_of_iso {X : Scheme.{u}} (I : X.IdealSheafData)
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) (h : idealPowerMultiple I n N = ⊥) :
    idealPowerMultiple I n M = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun V a ha x => ?_
  let E : X.Modules ⥤ ModuleCat.{u} Γ(X, V.1) :=
    SheafOfModules.evaluation X.ringCatSheaf (op V.1)
  refine (ModuleCat.mono_iff_injective (E.map e.hom)).mp inferInstance ?_
  exact (map_smul (E.map e.hom).hom a x).trans
    ((affine_sections_annihilated_of_idealPowerMultiple_eq_bot h V ha _).trans
      (map_zero _).symm)

end Stacks.Algebraization

namespace Stacks.Coherent

/-! ### Descending a morphism along the transitions of a coherent adic system -/

/-- Transitions of a functor on `ℕᵒᵖ` compose along `≤`. -/
private theorem map_homOfLE_op_comp {C : Type*} [Category C] (T : ℕᵒᵖ ⥤ C) {a b c : ℕ}
    (h : a ≤ b) (g : b ≤ c) :
    T.map (homOfLE g).op ≫ T.map (homOfLE h).op = T.map (homOfLE (h.trans g)).op := by
  rw [← T.map_comp]
  rfl

section Descend

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] (J : Y.IdealSheafData)

/-- The projection onto a term of the completion, followed by the identification of that term with
the adic quotient, is the quotient projection. -/
private theorem completionProjection_comp_eqToHom
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕ)
    (h : ((Stacks.Algebraization.completionFunctor Y J).obj M).obj.obj (op n) =
      Stacks.Algebraization.idealPowerQuotient J (n + 1) M.obj) :
    Stacks.Algebraization.completionProjection Y J M n ≫ eqToHom h =
      cokernel.π ((Stacks.Algebraization.idealPowerMultiple J (n + 1) M.obj).ι) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => cokernel.π ((Stacks.Algebraization.idealPowerMultiple J (n + 1) M.obj).ι)
        ≫ z) ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))

/-- **The projection of a coherent module onto a term of its completion is an epimorphism**,
being the projection onto a sheaf quotient followed by an identification of its target. -/
public theorem epi_completionProjection
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕ) :
    Epi (C := Y.Modules) (Stacks.Algebraization.completionProjection Y J M n) := by
  have h1 : Epi (cokernel.π (C := Y.Modules)
      (Stacks.Algebraization.idealPowerMultiple J (n + 1) M.obj).ι) :=
    Stacks.Algebraization.epi_cokernel_π_submodule_ι _
  have h2 : Epi (C := Y.Modules) (eqToHom
      (Stacks.Algebraization.completionFunctor_obj Y J M n).symm) := inferInstance
  exact epi_comp' h1 h2

/-- **The adic quotients of two isomorphic coherent modules are isomorphic**, compatibly with the
quotient projections. This is the completion functor of Tag 0880 applied to the isomorphism, read
through the identification of the terms of a completion with the adic quotients. -/
public theorem exists_idealPowerQuotientIsoOfIso {M N : Y.Modules}
    (hM : _root_.SheafOfModules.IsCoherent.{u} M) (hN : _root_.SheafOfModules.IsCoherent.{u} N)
    (e : M ≅ N) (n : ℕ) :
    ∃ a : Stacks.Algebraization.idealPowerQuotient J (n + 1) M ≅
        Stacks.Algebraization.idealPowerQuotient J (n + 1) N,
      cokernel.π ((Stacks.Algebraization.idealPowerMultiple J (n + 1) M).ι) ≫ a.hom =
        e.hom ≫ cokernel.π ((Stacks.Algebraization.idealPowerMultiple J (n + 1) N).ι) := by
  let M' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf := ⟨M, hM⟩
  let N' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf := ⟨N, hN⟩
  obtain ⟨a, ha⟩ := completion_iso J M' N' e n
  have h1 : Stacks.Algebraization.idealPowerQuotient J (n + 1) M =
      ((Stacks.Algebraization.completionFunctor Y J).obj M').obj.obj (op n) :=
    (Stacks.Algebraization.completionFunctor_obj Y J M' n).symm
  have h2 : ((Stacks.Algebraization.completionFunctor Y J).obj N').obj.obj (op n) =
      Stacks.Algebraization.idealPowerQuotient J (n + 1) N :=
    Stacks.Algebraization.completionFunctor_obj Y J N' n
  have hfinal := completionProjection_comp_eqToHom J N' n h2
  refine ⟨eqToIso h1 ≪≫ a ≪≫ eqToIso h2, ?_⟩
  show cokernel.π ((Stacks.Algebraization.idealPowerMultiple J (n + 1) M).ι) ≫
    eqToHom h1 ≫ a.hom ≫ eqToHom h2 = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ eqToHom h2) ha).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => e.hom ≫ z) hfinal

omit [IsLocallyNoetherian Y] in
/-- **A morphism to a module annihilated by `ℐ ⁿ⁺¹` descends along the transitions of a coherent
adic system.** For `n ≤ m` every morphism out of `H_m` with such a target factors through the
transition `H_m ⟶ H_n`.

One step of the induction is the quotient clause: `H_n` is `H_{m+1} / ℐ ᵐ⁺¹ H_{m+1}` for
`m + 1 = n + 1`, and a morphism into a module annihilated by `ℐ ⁿ⁺¹ ⊇ ℐ ᵐ⁺¹` kills the subsheaf
being divided out. -/
public theorem exists_coherentAdicSystemDesc (H : CoherentAdicSystems J) (n m : ℕ) (h : n ≤ m)
    {P : Y.Modules}
    (hP : Stacks.Algebraization.idealPowerMultiple J (n + 1) P = ⊥)
    (f : H.obj.obj (op m) ⟶ P) :
    ∃ g : H.obj.obj (op n) ⟶ P, H.obj.map (homOfLE h).op ≫ g = f := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨f, by simp⟩
  | succ m h ih =>
    have hz := Stacks.Algebraization.comp_eq_zero_of_idealPowerMultiple_eq_bot J (m + 1) f
      (Stacks.Algebraization.idealPowerMultiple_eq_bot_of_le hP (by omega))
    have ha : H.obj.map (homOfLE (Nat.le_succ m)).op ≫
        ((H.property.quotientIso m).inv ≫ cokernel.desc _ f hz) = f := by
      refine (congrArg (fun z => z ≫ (H.property.quotientIso m).inv ≫
        cokernel.desc _ f hz) (H.property.cokernel_π_comp_quotientIso m).symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => cokernel.π ((Stacks.Algebraization.idealPowerMultiple J (m + 1)
        (H.obj.obj (op (m + 1)))).ι) ≫ z)
          ((H.property.quotientIso m).hom_inv_id_assoc (cokernel.desc _ f hz))).trans ?_
      exact cokernel.π_desc _ f hz
    obtain ⟨g, hg⟩ := ih ((H.property.quotientIso m).inv ≫ cokernel.desc _ f hz)
    refine ⟨g, ?_⟩
    rw [← map_homOfLE_op_comp H.obj h (Nat.le_succ m), Category.assoc, hg]
    exact ha

end Descend


/-! ### The limit of the double system is a coherent adic system -/

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) {F G : CoherentAdicSystems I}

/-- The projection from the limit of the double system onto a term of one of the completions of
the stable kernel images, as a component of the natural transformation `limit.π`. It differs from
`Stacks.Coherent.stableKernelImageLimitProjection` only by the identification of the term of the
completion with the adic quotient. -/
public abbrev stableKernelImageLimitπ (α : F ⟶ G) (n m : ℕ) :
    (stableKernelImageLimitSystem I α).obj (op n) ⟶
      (stableKernelImageCompletion I α m).obj.obj (op n) :=
  (limit.π (stableKernelImageCompletionDiagram I α) (op m)).app (op n)

/-- The projections of the limit system are compatible with the transitions in the quotient
level. -/
private theorem stableKernelImageLimitπ_naturality (α : F ⟶ G) (n k m : ℕ) (h : n ≤ k) :
    (stableKernelImageLimitSystem I α).map (homOfLE h).op ≫ stableKernelImageLimitπ I α n m =
      stableKernelImageLimitπ I α k m ≫
        (stableKernelImageCompletion I α m).obj.map (homOfLE h).op :=
  (limit.π (stableKernelImageCompletionDiagram I α) (op m)).naturality (homOfLE h).op

/-- The projections of the limit system are compatible with the transitions in the image level. -/
private theorem stableKernelImageLimitπ_comp_project (α : F ⟶ G) (n k m : ℕ) (h : k ≤ m) :
    stableKernelImageLimitπ I α n m ≫ (stableKernelImageCompletion_project I α k m h).hom.app
      (op n) = stableKernelImageLimitπ I α n k :=
  congrArg (fun f => f.app (op n))
    (limit.w (stableKernelImageCompletionDiagram I α) (homOfLE h).op)

/-- **Past the second stabilization the limit system is one of the completions, level by
level.** For each quotient level `n` there is a constant `c` such that the projection of the
limit system onto the `n`-th term of the completion of the stable kernel image at any level
`m ≥ n + c` is an isomorphism. -/
public theorem stableKernelImageLimitπ_eventually_isIso (α : F ⟶ G) (n : ℕ) :
    ∃ c : ℕ, ∀ m : ℕ, n + c ≤ m → IsIso (stableKernelImageLimitπ I α n m) := by
  obtain ⟨c, hc⟩ := stableKernelImageQuotientMap_eventually_isIso I α n
  have h := stableKernelImageQuotientDiagram_eventuallyConstant I α n c hc
  refine ⟨c, fun m hm => ?_⟩
  have : IsIso (limit.π (stableKernelImageQuotientDiagram I α n) (op m)) :=
    (h.precomp (homOfLE hm).op).isIso_π_of_isLimit (limit.isLimit _)
  show IsIso ((limit.π (stableKernelImageCompletionDiagram I α) (op m)).app (op n))
  rw [← limitObjIsoLimitCompEvaluation_hom_π]
  show IsIso ((stableKernelImageLimitSystem_objIso I α n).hom ≫
    limit.π (stableKernelImageQuotientDiagram I α n) (op m))
  infer_instance

/-- **Every term of the limit system is coherent**, being isomorphic to a term of one of the
completions of the stable kernel images. -/
public theorem stableKernelImageLimit_isCoherent (α : F ⟶ G) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} ((stableKernelImageLimitSystem I α).obj (op n)) := by
  have hclosed : ObjectProperty.IsClosedUnderIsomorphisms
      (fun P : SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent) :=
    AlgebraicGeometry.CoherentAbelian.coherentModules_isClosedUnderIsomorphisms
  obtain ⟨c, hc⟩ := stableKernelImageLimitπ_eventually_isIso I α n
  have := hc (n + c) le_rfl
  exact ObjectProperty.prop_of_iso
    (P := fun P : SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)
    (asIso (stableKernelImageLimitπ I α n (n + c))).symm
    ((stableKernelImageCompletion I α (n + c)).property.isCoherent n)

/-- **The limit of the double system of completed stable kernel images is a coherent adic
system.** This is where the second stabilization
`Stacks.Coherent.stableKernelImageQuotientMap_eventually_isIso` is consumed: each term of the
limit is isomorphic to a term of one of the completions, which is a coherent adic system, and all
three defining clauses transport along such isomorphisms.

For the quotient clause the two levels `n` and `n + 1` must be compared inside *one* completion,
so the image level is taken above both stabilization bounds; the projections of the limit are then
isomorphisms at both levels and are compatible with the transition maps, being components of a
natural transformation. -/
public theorem stableKernelImageLimit_isCoherentAdicSystem (α : F ⟶ G) :
    IsCoherentAdicSystem I (stableKernelImageLimitSystem I α) := by
  refine ⟨stableKernelImageLimit_isCoherent I α, fun n => ?_, fun n => ?_⟩
  · obtain ⟨c, hc⟩ := stableKernelImageLimitπ_eventually_isIso I α n
    have := hc (n + c) le_rfl
    exact Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso I
      (asIso (stableKernelImageLimitπ I α n (n + c))) (n + 1)
      ((stableKernelImageCompletion I α (n + c)).property.idealPowerMultiple_eq_bot n)
  · obtain ⟨c, hc⟩ := stableKernelImageLimitπ_eventually_isIso I α n
    obtain ⟨d, hd⟩ := stableKernelImageLimitπ_eventually_isIso I α (n + 1)
    have h₀ := hc (n + c + d + 1) (by omega)
    have h₁ := hd (n + c + d + 1) (by omega)
    set m := n + c + d + 1
    let e₀ := asIso (stableKernelImageLimitπ I α n m)
    let e₁ := asIso (stableKernelImageLimitπ I α (n + 1) m)
    obtain ⟨a, ha⟩ := exists_idealPowerQuotientIsoOfIso I
      (stableKernelImageLimit_isCoherent I α (n + 1))
      ((stableKernelImageCompletion I α m).property.isCoherent (n + 1)) e₁ n
    let b := (stableKernelImageCompletion I α m).property.quotientIso n
    have hb := (stableKernelImageCompletion I α m).property.cokernel_π_comp_quotientIso n
    refine ⟨a ≪≫ b ≪≫ e₀.symm, ?_⟩
    have hn := stableKernelImageLimitπ_naturality I α n (n + 1) m (Nat.le_succ n)
    show cokernel.π _ ≫ a.hom ≫ b.hom ≫ e₀.inv = _
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ b.hom ≫ e₀.inv) ha).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => e₁.hom ≫ z) (Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (fun z => e₁.hom ≫ z ≫ e₀.inv) hb).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ e₀.inv) hn.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => (stableKernelImageLimitSystem I α).map
      (homOfLE (Nat.le_succ n)).op ≫ z) e₀.hom_inv_id).trans ?_
    exact Category.comp_id _

/-! ### The kernel object -/

/-- **The kernel of a morphism of coherent adic systems**, the limit of the double system of the
completed stable kernel images. -/
public def coherentAdicKernel (α : F ⟶ G) : CoherentAdicSystems I :=
  ⟨stableKernelImageLimitSystem I α, stableKernelImageLimit_isCoherentAdicSystem I α⟩

/-- The underlying inverse system of the kernel is the limit system. -/
public theorem coherentAdicKernel_obj (α : F ⟶ G) :
    (coherentAdicKernel I α).obj = stableKernelImageLimitSystem I α :=
  rfl

/-! ### Factoring a morphism killed by `α` -/

/-- **A morphism killed by `α` factors through every stable kernel image.** At a level `l` above
the stabilization level of `F_m` the component `β_l` factors through `ker(α_l)` and hence through
the image of `ker(α_l)` in `F_m`, which is the stable kernel image; the transition `H_l ⟶ H_m` is
an epimorphism, so the factorization descends to `H_m` by the lifting property of a strong
epimorphism against the monomorphism `stableKernelImage ⟶ F_m`. -/
public theorem exists_stableKernelImageLift (α : F ⟶ G) {H : CoherentAdicSystems I} (β : H ⟶ F)
    (hβ : β ≫ α = 0) (m : ℕ) :
    ∃ f : H.obj.obj (op m) ⟶ stableKernelImage I α m,
      f ≫ stableKernelImageIncl I α m = β.hom.app (op m) := by
  let l := kernelStableLevel I α m
  have h : m ≤ l := le_kernelStableLevel I α m
  let t := H.obj.map (homOfLE h).op
  have hepi : Epi t := H.property.epi_map h
  have hz : β.hom.app (op l) ≫ α.hom.app (op l) = 0 :=
    congrArg (fun f : H ⟶ G => f.hom.app (op l)) hβ
  let a := kernel.lift (α.hom.app (op l)) (β.hom.app (op l)) hz ≫
    factorThruImage (kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE h).op)
  have ha : a ≫ stableKernelImageIncl I α m = t ≫ β.hom.app (op m) := by
    show (_ ≫ factorThruImage _) ≫ image.ι _ = _
    rw [Category.assoc, image.fac, ← Category.assoc, kernel.lift_ι]
    exact (β.hom.naturality (homOfLE h).op).symm
  let sq : CommSq a t (stableKernelImageIncl I α m) (β.hom.app (op m)) := ⟨ha⟩
  have : StrongEpi t := strongEpi_of_epi t
  have : sq.HasLift := (StrongEpi.llp (f := t) (stableKernelImageIncl I α m)).sq_hasLift sq
  exact ⟨sq.lift, sq.fac_right⟩

/-- The chosen factorization of a morphism killed by `α` through the stable kernel image at a
level. -/
public def stableKernelImageLift (α : F ⟶ G) {H : CoherentAdicSystems I} (β : H ⟶ F)
    (hβ : β ≫ α = 0) (m : ℕ) : H.obj.obj (op m) ⟶ stableKernelImage I α m :=
  (exists_stableKernelImageLift I α β hβ m).choose

/-- The factorization through the stable kernel image lies over the component of `β`. -/
public theorem stableKernelImageLift_ι (α : F ⟶ G) {H : CoherentAdicSystems I} (β : H ⟶ F)
    (hβ : β ≫ α = 0) (m : ℕ) :
    stableKernelImageLift I α β hβ m ≫ stableKernelImageIncl I α m = β.hom.app (op m) :=
  (exists_stableKernelImageLift I α β hβ m).choose_spec

/-- The factorizations through the stable kernel images form a morphism of inverse systems: both
composites with the inclusion into `F_n` are the component of `β` precomposed with a transition
of `H`, and the inclusion is a monomorphism. -/
public theorem stableKernelImageLift_naturality (α : F ⟶ G) {H : CoherentAdicSystems I}
    (β : H ⟶ F) (hβ : β ≫ α = 0) (n m : ℕ) (h : n ≤ m) :
    H.obj.map (homOfLE h).op ≫ stableKernelImageLift I α β hβ n =
      stableKernelImageLift I α β hβ m ≫ stableKernelImage_project I α n m h := by
  refine (cancel_mono (stableKernelImageIncl I α n)).mp ?_
  rw [Category.assoc, stableKernelImageLift_ι, Category.assoc,
    stableKernelImage_project_comp, ← Category.assoc, stableKernelImageLift_ι]
  exact β.hom.naturality _

/-! ### The comparison maps of the completions -/

/-- The projection from the stable kernel image at level `m` onto the `n`-th term of its
completion. -/
public abbrev stableKernelImageCompletionProjection (α : F ⟶ G) (n m : ℕ) :
    stableKernelImage I α m ⟶ (stableKernelImageCompletion I α m).obj.obj (op n) :=
  Stacks.Algebraization.completionProjection X I (coherentStableKernelImage I α m) n

/-- **The comparison from the `n`-th term of the completion of the stable kernel image at level
`m ≥ n` to `F_n`**: the map `Stacks.Coherent.stableKernelImageQuotientToLevel`, read through the
identification of the term of the completion with the adic quotient. -/
public def stableKernelImageCompletionToLevel (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    (stableKernelImageCompletion I α m).obj.obj (op n) ⟶ F.obj.obj (op n) :=
  eqToHom (stableKernelImageCompletion_obj I α m n) ≫
    stableKernelImageQuotientToLevel I α n m h

/-- On representatives the comparison to `F_n` is the inclusion of the stable kernel image
followed by the transition map of `F`. -/
public theorem stableKernelImageCompletionToLevel_fac (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    stableKernelImageCompletionProjection I α n m ≫
        stableKernelImageCompletionToLevel I α n m h =
      stableKernelImageIncl I α m ≫ F.obj.map (homOfLE h).op := by
  have hπ := completionProjection_comp_eqToHom I (coherentStableKernelImage I α m) n
    (stableKernelImageCompletion_obj I α m n)
  show Stacks.Algebraization.completionProjection X I (coherentStableKernelImage I α m) n ≫
    eqToHom (stableKernelImageCompletion_obj I α m n) ≫
      stableKernelImageQuotientToLevel I α n m h = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ stableKernelImageQuotientToLevel I α n m h) hπ).trans ?_
  exact stableKernelImageQuotientToLevel_comp I α n m h

/-- The comparisons to `F_n` are compatible with the transitions of the double system in the
image level. -/
public theorem stableKernelImageCompletionToLevel_transition (α : F ⟶ G) (n k m : ℕ)
    (hnk : n ≤ k) (hkm : k ≤ m) :
    (stableKernelImageCompletion_project I α k m hkm).hom.app (op n) ≫
        stableKernelImageCompletionToLevel I α n k hnk =
      stableKernelImageCompletionToLevel I α n m (hnk.trans hkm) := by
  have hepi : Epi (stableKernelImageCompletionProjection I α n m) :=
    epi_completionProjection I (coherentStableKernelImage I α m) n
  have hmap := map_homOfLE_op_comp F.obj hnk hkm
  refine (cancel_epi (stableKernelImageCompletionProjection I α n m)).mp ?_
  refine Eq.trans ?_ (stableKernelImageCompletionToLevel_fac I α n m (hnk.trans hkm)).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ stableKernelImageCompletionToLevel I α n k hnk)
    (stableKernelImageCompletion_project_projection I α k m hkm n)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => stableKernelImage_project I α k m hkm ≫ z)
    (stableKernelImageCompletionToLevel_fac I α n k hnk)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ F.obj.map (homOfLE hnk).op)
    (stableKernelImage_project_comp I α k m hkm)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => stableKernelImageIncl I α m ≫ z) hmap

/-- The comparisons to the terms of `F` are compatible with the transitions of the completion in
the quotient level. -/
public theorem stableKernelImageCompletionToLevel_naturality (α : F ⟶ G) (n k m : ℕ)
    (hnk : n ≤ k) (hkm : k ≤ m) :
    (stableKernelImageCompletion I α m).obj.map (homOfLE hnk).op ≫
        stableKernelImageCompletionToLevel I α n m (hnk.trans hkm) =
      stableKernelImageCompletionToLevel I α k m hkm ≫ F.obj.map (homOfLE hnk).op := by
  have hepi : Epi (stableKernelImageCompletionProjection I α k m) :=
    epi_completionProjection I (coherentStableKernelImage I α m) k
  have hmap := map_homOfLE_op_comp F.obj hnk hkm
  have hL : stableKernelImageCompletionProjection I α k m ≫
      ((stableKernelImageCompletion I α m).obj.map (homOfLE hnk).op ≫
        stableKernelImageCompletionToLevel I α n m (hnk.trans hkm)) =
      stableKernelImageIncl I α m ≫ F.obj.map (homOfLE (hnk.trans hkm)).op :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ stableKernelImageCompletionToLevel I α n m (hnk.trans hkm))
          (completionProjection_map I (coherentStableKernelImage I α m) hnk)).trans
        (stableKernelImageCompletionToLevel_fac I α n m (hnk.trans hkm)))
  have hR : stableKernelImageCompletionProjection I α k m ≫
      (stableKernelImageCompletionToLevel I α k m hkm ≫ F.obj.map (homOfLE hnk).op) =
      stableKernelImageIncl I α m ≫ F.obj.map (homOfLE (hnk.trans hkm)).op :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ F.obj.map (homOfLE hnk).op)
          (stableKernelImageCompletionToLevel_fac I α k m hkm)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => stableKernelImageIncl I α m ≫ z) hmap)))
  exact (cancel_epi (stableKernelImageCompletionProjection I α k m)).mp (hL.trans hR.symm)

/-- **At equal levels the comparison to `F_n` is a monomorphism.** The stable kernel image at
level `n` is annihilated by `ℐ ⁿ⁺¹`, so the projection onto the `n`-th term of its completion is
an isomorphism, and the comparison becomes the inclusion of the stable kernel image into `F_n`
precomposed with that isomorphism. -/
public theorem stableKernelImageCompletionToLevel_mono (α : F ⟶ G) (n : ℕ) :
    Mono (stableKernelImageCompletionToLevel I α n n le_rfl) := by
  have hiso : IsIso (stableKernelImageCompletionProjection I α n n) :=
    completionProjection_isIso I (coherentStableKernelImage I α n) n
      (stableKernelImage_idealPowerMultiple_eq_bot I α n)
  have hr : stableKernelImageCompletionProjection I α n n ≫
      stableKernelImageCompletionToLevel I α n n le_rfl = stableKernelImageIncl I α n := by
    simpa using stableKernelImageCompletionToLevel_fac I α n n le_rfl
  have he : stableKernelImageCompletionToLevel I α n n le_rfl =
      inv (stableKernelImageCompletionProjection I α n n) ≫ stableKernelImageIncl I α n := by
    rw [← hr, IsIso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-! ### The inclusion of the limit system into the source -/

/-- The composite of a projection of the limit system with a comparison to `F_n` does not depend
on the image level: the projections are compatible with the transitions of the double system, and
the comparisons are compatible with those same transitions. -/
public theorem stableKernelImageLimitπ_comp_toLevel (α : F ⟶ G) (n m : ℕ) (h : n ≤ m) :
    stableKernelImageLimitπ I α n m ≫ stableKernelImageCompletionToLevel I α n m h =
      stableKernelImageLimitπ I α n n ≫
        stableKernelImageCompletionToLevel I α n n le_rfl := by
  rw [← stableKernelImageCompletionToLevel_transition I α n n m le_rfl h, ← Category.assoc]
  rw [stableKernelImageLimitπ_comp_project I α n n m h]

/-- **The inclusion of the limit system into the source system**, the comparison to `F_n` at
equal levels composed with the projection of the limit. -/
public def stableKernelImageLimitIncl (α : F ⟶ G) :
    stableKernelImageLimitSystem I α ⟶ F.obj where
  app n := stableKernelImageLimitπ I α n.unop n.unop ≫
    stableKernelImageCompletionToLevel I α n.unop n.unop le_rfl
  naturality {k n} f := by
    let h : n.unop ≤ k.unop := leOfHom f.unop
    change (stableKernelImageLimitSystem I α).map (homOfLE h).op ≫
      (stableKernelImageLimitπ I α n.unop n.unop ≫ _) = _
    rw [← stableKernelImageLimitπ_comp_toLevel I α n.unop k.unop h, ← Category.assoc]
    have hn := (limit.π (stableKernelImageCompletionDiagram I α) k).naturality f
    change (stableKernelImageLimitSystem I α).map (homOfLE h).op ≫
        stableKernelImageLimitπ I α n.unop k.unop =
      stableKernelImageLimitπ I α k.unop k.unop ≫
        (stableKernelImageCompletion I α k.unop).obj.map (homOfLE h).op at hn
    rw [hn, Category.assoc, stableKernelImageCompletionToLevel_naturality I α
      n.unop k.unop k.unop h le_rfl, ← Category.assoc]
    congr 2

/-- The inclusion of the limit system into the source is killed by `α`: it factors through the
stable kernel images, which `α` annihilates. -/
public theorem stableKernelImageLimitIncl_comp (α : F ⟶ G) :
    stableKernelImageLimitIncl I α ≫ α.hom = 0 := by
  refine NatTrans.ext (funext fun n => ?_)
  show (stableKernelImageLimitπ I α n.unop n.unop ≫
    (eqToHom _ ≫ stableKernelImageQuotientToLevel I α n.unop n.unop le_rfl)) ≫
      α.hom.app n = 0
  rw [Category.assoc, Category.assoc, stableKernelImageQuotientToLevel_comp_alpha,
    comp_zero, comp_zero]

/-- **A morphism of coherent adic systems into the limit system is determined by its composite
with the inclusion into `F`.** At the quotient level `n` the two candidates agree after
projection to the image level `n` — the comparison to `F_n` being a monomorphism — and every
other projection is reached from that one by a transition of the double system, after
precomposing with a transition of the source, which is an epimorphism. -/
public theorem stableKernelImageLimitIncl_hom_ext (α : F ⟶ G) (H : CoherentAdicSystems I)
    (a b : H.obj ⟶ stableKernelImageLimitSystem I α)
    (h : a ≫ stableKernelImageLimitIncl I α = b ≫ stableKernelImageLimitIncl I α) : a = b := by
  refine limit.hom_ext fun m => NatTrans.ext (funext fun n => ?_)
  let l := max n.unop m.unop
  have hn : n.unop ≤ l := le_max_left _ _
  have hm : m.unop ≤ l := le_max_right _ _
  have hepi : Epi (H.obj.map (homOfLE hn).op) := H.property.epi_map hn
  refine (cancel_epi (H.obj.map (homOfLE hn).op)).mp ?_
  have hd : a.app (op l) ≫ stableKernelImageLimitπ I α l l =
      b.app (op l) ≫ stableKernelImageLimitπ I α l l := by
    have hmono := stableKernelImageCompletionToLevel_mono I α l
    refine (cancel_mono (stableKernelImageCompletionToLevel I α l l le_rfl)).mp ?_
    exact congrArg (fun f => f.app (op l)) h
  have hw := stableKernelImageLimitπ_comp_project I α l m.unop l hm
  have hnπ := stableKernelImageLimitπ_naturality I α n.unop l m.unop hn
  show H.obj.map (homOfLE hn).op ≫ (a.app n ≫ stableKernelImageLimitπ I α n.unop m.unop) =
    H.obj.map (homOfLE hn).op ≫ (b.app n ≫ stableKernelImageLimitπ I α n.unop m.unop)
  simp only [reassoc_of% a.naturality (homOfLE hn).op,
    reassoc_of% b.naturality (homOfLE hn).op, hnπ]
  rw [← hw]
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫
      (stableKernelImageCompletion_project I α m.unop l hm).hom.app (op l) ≫
      (stableKernelImageCompletion I α m.unop).obj.map (homOfLE hn).op) hd

/-! ### The cone built from a morphism killed by `α` -/

/-- The canonical morphism from the `n`-th term of a system `H` mapping to `F` by a morphism
killed by `α` to the `n`-th term of the completion of the stable kernel image at level `m`: the
factorization through the stable kernel image at level `m`, composed with the projection onto the
adic quotient, descended along the transitions of `H`. -/
public def stableKernelImageQuotientLift (α : F ⟶ G) {H : CoherentAdicSystems I} (β : H ⟶ F)
    (hβ : β ≫ α = 0) (n m : ℕ) :
    H.obj.obj (op n) ⟶ (stableKernelImageCompletion I α m).obj.obj (op n) :=
  (exists_coherentAdicSystemDesc I H n (max n m) (le_max_left _ _)
    ((stableKernelImageCompletion I α m).property.idealPowerMultiple_eq_bot n)
    (H.obj.map (homOfLE (le_max_right n m)).op ≫ stableKernelImageLift I α β hβ m ≫
      stableKernelImageCompletionProjection I α n m)).choose

/-- The defining property of `Stacks.Coherent.stableKernelImageQuotientLift`, at any level `l`
above both `n` and `m`. -/
public theorem stableKernelImageQuotientLift_fac (α : F ⟶ G) {H : CoherentAdicSystems I}
    (β : H ⟶ F) (hβ : β ≫ α = 0) (n m l : ℕ) (hn : n ≤ l) (hm : m ≤ l) :
    H.obj.map (homOfLE hn).op ≫ stableKernelImageQuotientLift I α β hβ n m =
      H.obj.map (homOfLE hm).op ≫ stableKernelImageLift I α β hβ m ≫
        stableKernelImageCompletionProjection I α n m := by
  have h := (exists_coherentAdicSystemDesc I H n (max n m) (le_max_left _ _)
    ((stableKernelImageCompletion I α m).property.idealPowerMultiple_eq_bot n)
    (H.obj.map (homOfLE (le_max_right n m)).op ≫ stableKernelImageLift I α β hβ m ≫
      stableKernelImageCompletionProjection I α n m)).choose_spec
  change H.obj.map (homOfLE (le_max_left n m)).op ≫
    stableKernelImageQuotientLift I α β hβ n m = _ at h
  have ht : max n m ≤ l := max_le hn hm
  rw [← map_homOfLE_op_comp H.obj (le_max_left n m) ht, Category.assoc, h, ← Category.assoc,
    map_homOfLE_op_comp H.obj (le_max_right n m) ht]

/-- The morphisms `Stacks.Coherent.stableKernelImageQuotientLift` at a fixed image level are
natural in the quotient level. -/
public theorem stableKernelImageQuotientLift_naturality (α : F ⟶ G) {H : CoherentAdicSystems I}
    (β : H ⟶ F) (hβ : β ≫ α = 0) (n k m : ℕ) (h : n ≤ k) :
    H.obj.map (homOfLE h).op ≫ stableKernelImageQuotientLift I α β hβ n m =
      stableKernelImageQuotientLift I α β hβ k m ≫
        (stableKernelImageCompletion I α m).obj.map (homOfLE h).op := by
  have hk : k ≤ max k m := le_max_left _ _
  have hm : m ≤ max k m := le_max_right _ _
  have hepi : Epi (H.obj.map (homOfLE hk).op) := H.property.epi_map hk
  refine (cancel_epi (H.obj.map (homOfLE hk).op)).mp ?_
  rw [← Category.assoc, ← H.obj.map_comp]
  show H.obj.map (homOfLE (h.trans hk)).op ≫ _ = _
  rw [stableKernelImageQuotientLift_fac I α β hβ n m _ (h.trans hk) hm,
    reassoc_of% stableKernelImageQuotientLift_fac I α β hβ k m _ hk hm]
  exact congrArg (fun z => H.obj.map (homOfLE hm).op ≫ stableKernelImageLift I α β hβ m ≫ z)
    (completionProjection_map I (coherentStableKernelImage I α m) h).symm

/-- The morphisms `Stacks.Coherent.stableKernelImageQuotientLift` at a fixed quotient level are
compatible with the transitions of the double system in the image level. -/
public theorem stableKernelImageQuotientLift_transition (α : F ⟶ G) {H : CoherentAdicSystems I}
    (β : H ⟶ F) (hβ : β ≫ α = 0) (n k m : ℕ) (h : k ≤ m) :
    stableKernelImageQuotientLift I α β hβ n m ≫
        (stableKernelImageCompletion_project I α k m h).hom.app (op n) =
      stableKernelImageQuotientLift I α β hβ n k := by
  have hn : n ≤ max n m := le_max_left _ _
  have hm : m ≤ max n m := le_max_right _ _
  have hepi : Epi (H.obj.map (homOfLE hn).op) := H.property.epi_map hn
  refine (cancel_epi (H.obj.map (homOfLE hn).op)).mp ?_
  have hmap := map_homOfLE_op_comp H.obj h hm
  rw [← Category.assoc, stableKernelImageQuotientLift_fac I α β hβ n m _ hn hm,
    stableKernelImageQuotientLift_fac I α β hβ n k _ hn (h.trans hm), Category.assoc,
    Category.assoc]
  refine (congrArg (fun z => H.obj.map (homOfLE hm).op ≫
    stableKernelImageLift I α β hβ m ≫ z)
      (stableKernelImageCompletion_project_projection I α k m h n)).trans ?_
  refine (congrArg (fun z => H.obj.map (homOfLE hm).op ≫ z)
    (Category.assoc (stableKernelImageLift I α β hβ m)
      (stableKernelImage_project I α k m h)
      (stableKernelImageCompletionProjection I α n k)).symm).trans ?_
  refine (congrArg (fun z => H.obj.map (homOfLE hm).op ≫
    z ≫ stableKernelImageCompletionProjection I α n k)
      (stableKernelImageLift_naturality I α β hβ k m h).symm).trans ?_
  refine (congrArg (fun z => H.obj.map (homOfLE hm).op ≫ z)
    (Category.assoc (H.obj.map (homOfLE h).op) (stableKernelImageLift I α β hβ k)
      (stableKernelImageCompletionProjection I α n k))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun z => z ≫ stableKernelImageLift I α β hβ k ≫
    stableKernelImageCompletionProjection I α n k) hmap

/-- **The cone on the double system built from a morphism killed by `α`**, with summit the source
system of that morphism. -/
public def stableKernelImageLiftCone (α : F ⟶ G) {H : CoherentAdicSystems I} (β : H ⟶ F)
    (hβ : β ≫ α = 0) : Cone (stableKernelImageCompletionDiagram I α) where
  pt := H.obj
  π :=
    { app m :=
        { app n := stableKernelImageQuotientLift I α β hβ n.unop m.unop
          naturality {n k} f := stableKernelImageQuotientLift_naturality I α β hβ
            k.unop n.unop m.unop (leOfHom f.unop) }
      naturality {m k} f := by
        refine NatTrans.ext (funext fun n => ?_)
        change (𝟙 _) ≫ stableKernelImageQuotientLift I α β hβ n.unop k.unop = _
        rw [Category.id_comp]
        exact (stableKernelImageQuotientLift_transition I α β hβ n.unop k.unop m.unop
          (leOfHom f.unop)).symm }

/-- The limiting morphism of `Stacks.Coherent.stableKernelImageLiftCone` is a factorization of
`β` through the inclusion of the limit system into `F`. -/
public theorem stableKernelImageLiftCone_lift_fac (α : F ⟶ G) {H : CoherentAdicSystems I}
    (β : H ⟶ F) (hβ : β ≫ α = 0) :
    limit.lift _ (stableKernelImageLiftCone I α β hβ) ≫ stableKernelImageLimitIncl I α =
      β.hom := by
  refine NatTrans.ext (funext fun n => ?_)
  show (limit.lift _ (stableKernelImageLiftCone I α β hβ)).app n ≫
    (stableKernelImageLimitπ I α n.unop n.unop ≫
      stableKernelImageCompletionToLevel I α n.unop n.unop le_rfl) = _
  have hl := congrArg (fun f => f.app n)
    (limit.lift_π (stableKernelImageLiftCone I α β hβ) n)
  change (limit.lift _ (stableKernelImageLiftCone I α β hβ)).app n ≫
      stableKernelImageLimitπ I α n.unop n.unop =
    stableKernelImageQuotientLift I α β hβ n.unop n.unop at hl
  have hf := stableKernelImageQuotientLift_fac I α β hβ n.unop n.unop n.unop le_rfl le_rfl
  simp only [homOfLE_refl, op_id, H.obj.map_id, Category.id_comp] at hf
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫
    stableKernelImageCompletionToLevel I α n.unop n.unop le_rfl) hl).trans ?_
  refine (congrArg (fun z => z ≫
    stableKernelImageCompletionToLevel I α n.unop n.unop le_rfl) hf).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => stableKernelImageLift I α β hβ n.unop ≫ z)
    (stableKernelImageCompletionToLevel_fac I α n.unop n.unop le_rfl)).trans ?_
  simpa using stableKernelImageLift_ι I α β hβ n.unop

/-! ### The universal property -/

/-- **The inclusion of the kernel into the source system.** -/
public def coherentAdicKernelι (α : F ⟶ G) : coherentAdicKernel I α ⟶ F :=
  ObjectProperty.homMk (stableKernelImageLimitIncl I α)

/-- **The inclusion of the kernel is killed by `α`.** -/
public theorem coherentAdicKernelι_comp (α : F ⟶ G) :
    coherentAdicKernelι I α ≫ α = 0 :=
  ObjectProperty.hom_ext (IsCoherentAdicSystem I) (stableKernelImageLimitIncl_comp I α)

/-- **The universal property of the kernel of a morphism of coherent adic systems.** A morphism
`β : H ⟶ F` killed by `α` factors uniquely through `Stacks.Coherent.coherentAdicKernelι`. -/
public def coherentAdicKernelIsLimit (α : F ⟶ G) :
    IsLimit (KernelFork.ofι (coherentAdicKernelι I α) (coherentAdicKernelι_comp I α)) :=
  KernelFork.IsLimit.ofι _ _
    (fun β hβ => ObjectProperty.homMk (limit.lift _ (stableKernelImageLiftCone I α β hβ)))
    (fun β hβ => ObjectProperty.hom_ext (IsCoherentAdicSystem I)
      (stableKernelImageLiftCone_lift_fac I α β hβ))
    (fun β hβ _a ha => ObjectProperty.hom_ext (IsCoherentAdicSystem I)
      (stableKernelImageLimitIncl_hom_ext I α _ _ _
        ((congrArg InducedCategory.Hom.hom ha).trans
          (stableKernelImageLiftCone_lift_fac I α β hβ).symm)))

/-- The kernel of a morphism of coherent adic systems exists. -/
public instance hasKernel_coherentAdicSystems (α : F ⟶ G) : HasKernel α :=
  ⟨⟨⟨_, coherentAdicKernelIsLimit I α⟩⟩⟩

/-- **The category of coherent adic systems on a Noetherian scheme has all kernels.** -/
public instance hasKernels_coherentAdicSystems {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : HasKernels (CoherentAdicSystems I) where
  has_limit α := hasKernel_coherentAdicSystems I α

/-! ### The relation with the levelwise kernels -/

/-- **The canonical comparison from the `n`-th term of the kernel to the kernel of `α_n`.** The
kernel in `Coh(X, ℐ)` is not the levelwise kernel, and this comparison need not be invertible;
what holds is that it lies over the inclusions into `F_n`. -/
public def coherentAdicKernelToLevelwiseKernel (α : F ⟶ G) (n : ℕ) :
    (coherentAdicKernel I α).obj.obj (op n) ⟶ kernel (α.hom.app (op n)) :=
  kernel.lift _ ((coherentAdicKernelι I α).hom.app (op n))
    (congrArg (fun f : coherentAdicKernel I α ⟶ G => f.hom.app (op n))
      (coherentAdicKernelι_comp I α))

/-- The comparison with the levelwise kernel lies over the inclusion of the kernel into `F_n`. -/
public theorem coherentAdicKernelToLevelwiseKernel_ι (α : F ⟶ G) (n : ℕ) :
    coherentAdicKernelToLevelwiseKernel I α n ≫ kernel.ι (α.hom.app (op n)) =
      (coherentAdicKernelι I α).hom.app (op n) :=
  kernel.lift_ι _ _ _

/-- **The terms of the kernel are the adic quotients of the stable kernel images.** For each
quotient level `n` there is a constant `c` such that, for every image level `m ≥ n + c`, the
`(n+1)`-st adic quotient of the stable kernel image at level `m` is the `n`-th term of the
kernel, by an isomorphism carrying the quotient projection to the inclusion of the stable kernel
image into `F_n`.

This is the second stabilization read off the kernel: the projections of the limit system are
isomorphisms past the bound. -/
public theorem kernelImageQuotients_eventuallyConstant (α : F ⟶ G) (n : ℕ) :
    ∃ c : ℕ, ∀ m : ℕ, ∀ h : n + c ≤ m,
      ∃ e : Stacks.Algebraization.idealPowerQuotient I (n + 1)
          (stableKernelImage I α m) ≅ (coherentAdicKernel I α).obj.obj (op n),
        cokernel.π ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
          (stableKernelImage I α m)).ι) ≫ e.hom ≫
            (coherentAdicKernelι I α).hom.app (op n) =
          stableKernelImageIncl I α m ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right n c) h)).op := by
  obtain ⟨c, hc⟩ := stableKernelImageLimitπ_eventually_isIso I α n
  refine ⟨c, fun m hm => ?_⟩
  have := hc m hm
  let p := asIso (stableKernelImageLimitπ I α n m)
  let q := eqToIso (stableKernelImageCompletion_obj I α m n)
  refine ⟨q.symm ≪≫ p.symm, ?_⟩
  have hnm : n ≤ m := (Nat.le_add_right n c).trans hm
  have hp : p.inv ≫ (stableKernelImageLimitπ I α n m ≫
      stableKernelImageCompletionToLevel I α n m hnm) =
      stableKernelImageCompletionToLevel I α n m hnm :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ stableKernelImageCompletionToLevel I α n m hnm)
        p.inv_hom_id).trans (Category.id_comp _))
  show cokernel.π ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
    (stableKernelImage I α m)).ι) ≫ (q.inv ≫ p.inv) ≫
      (stableKernelImageLimitπ I α n n ≫
        stableKernelImageCompletionToLevel I α n n le_rfl) = _
  refine (congrArg (fun z => cokernel.π ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
    (stableKernelImage I α m)).ι) ≫ (q.inv ≫ p.inv) ≫ z)
      (stableKernelImageLimitπ_comp_toLevel I α n m hnm).symm).trans ?_
  refine (congrArg (fun z => cokernel.π ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
    (stableKernelImage I α m)).ι) ≫ z)
      (Category.assoc q.inv p.inv (stableKernelImageLimitπ I α n m ≫
        stableKernelImageCompletionToLevel I α n m hnm))).trans ?_
  refine (congrArg (fun z => cokernel.π ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
    (stableKernelImage I α m)).ι) ≫ q.inv ≫ z) hp).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact stableKernelImageCompletionToLevel_fac I α n m hnm

/-! ### Restriction along an open immersion -/

/-- **A scheme admitting an open immersion into a Noetherian scheme is Noetherian.** Its space is
homeomorphic to an open subspace of a Noetherian space, hence Noetherian and in particular
quasi-compact, and it is locally Noetherian. -/
@[ega "I 10.4.4" "special case"]
public theorem isNoetherian_of_isOpenImmersion {Y Z : Scheme.{u}} [IsNoetherian Z] (r : Y ⟶ Z)
    [IsOpenImmersion r] : IsNoetherian Y where
  toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion r
  toCompactSpace :=
    have : NoetherianSpace Y := (Scheme.Hom.isOpenEmbedding r).isInducing.noetherianSpace
    inferInstance

/-- **Restriction along an open immersion preserves limits indexed by `ℕᵒᵖ`.** The index category
lives in the bottom universe while `Stacks.Coherent.preservesLimitsOfShape_restrictFunctor` is
stated for a shape in the universe of the schemes; the two are reconciled by the equivalence of
`ℕᵒᵖ` with its lift to that universe. -/
public theorem preservesLimitsOfShapeNatOp_restrictFunctor {Y Z : Scheme.{u}} (r : Y ⟶ Z)
    [IsOpenImmersion r] :
    PreservesLimitsOfShape ℕᵒᵖ (Scheme.Modules.restrictFunctor r) :=
  have : PreservesLimitsOfShape (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
      (Scheme.Modules.restrictFunctor r) :=
    preservesLimitsOfShape_restrictFunctor r (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
  preservesLimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).symm _

/-- **Completion commutes with restriction to an open, as an isomorphism of systems**, compatibly
with the canonical projections out of the module. The termwise comparisons of
`Stacks.Coherent.completion_restrictIso` are natural, which is checked after the projections —
epimorphisms — out of the module. -/
public theorem exists_completionRestrictSystemIso {Y Z : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] (r : Y ⟶ Z) [IsOpenImmersion r] (J : Z.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    ∃ e : ((Stacks.Algebraization.completionFunctor Y (J.comap r)).obj
          (Stacks.Algebraization.restrictCoherentModules r M)).obj ≅
        ((Stacks.Algebraization.completionFunctor Z J).obj M).obj ⋙
          Scheme.Modules.restrictFunctor r,
      ∀ n : ℕ, Stacks.Algebraization.completionProjection Y (J.comap r)
          (Stacks.Algebraization.restrictCoherentModules r M) n ≫ e.hom.app (op n) =
        (Scheme.Modules.restrictFunctor r).map
          (Stacks.Algebraization.completionProjection Z J M n) := by
  choose e he using fun n => completion_restrictIso r J M n
  refine ⟨NatIso.ofComponents (fun n => e n.unop) (fun {k n} f => ?_), he⟩
  have h : n.unop ≤ k.unop := leOfHom f.unop
  have hepi : Epi (Stacks.Algebraization.completionProjection Y (J.comap r)
      (Stacks.Algebraization.restrictCoherentModules r M) k.unop) :=
    epi_completionProjection (J.comap r)
      (Stacks.Algebraization.restrictCoherentModules r M) k.unop
  have hf : f = (homOfLE h).op := Subsingleton.elim _ _
  have hL : Stacks.Algebraization.completionProjection Y (J.comap r)
        (Stacks.Algebraization.restrictCoherentModules r M) k.unop ≫
      (((Stacks.Algebraization.completionFunctor Y (J.comap r)).obj
          (Stacks.Algebraization.restrictCoherentModules r M)).obj.map (homOfLE h).op ≫
        (e n.unop).hom) =
      (Scheme.Modules.restrictFunctor r).map
        (Stacks.Algebraization.completionProjection Z J M n.unop) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (e n.unop).hom)
          (completionProjection_map (J.comap r)
            (Stacks.Algebraization.restrictCoherentModules r M) h)).trans (he n.unop))
  have hR : Stacks.Algebraization.completionProjection Y (J.comap r)
        (Stacks.Algebraization.restrictCoherentModules r M) k.unop ≫
      ((e k.unop).hom ≫ (((Stacks.Algebraization.completionFunctor Z J).obj M).obj ⋙
        Scheme.Modules.restrictFunctor r).map (homOfLE h).op) =
      (Scheme.Modules.restrictFunctor r).map
        (Stacks.Algebraization.completionProjection Z J M n.unop) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor r).map
            (((Stacks.Algebraization.completionFunctor Z J).obj M).obj.map (homOfLE h).op))
          (he k.unop)).trans
        (((Scheme.Modules.restrictFunctor r).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.restrictFunctor r).map
            (completionProjection_map J M h))))
  refine (cancel_epi (Stacks.Algebraization.completionProjection Y (J.comap r)
    (Stacks.Algebraization.restrictCoherentModules r M) k.unop)).mp ?_
  rw [hf]
  exact hL.trans hR.symm

/-- **The completion of the stable kernel image commutes with restriction, as an isomorphism of
systems**, compatibly with the inclusion into the term of `F` and with the canonical projections
out of the stable kernel image. -/
public theorem exists_stableKernelImageCompletionRestrictSystemIso {Y Z : Scheme.{u}}
    [IsNoetherian Y] [IsNoetherian Z] (r : Y ⟶ Z) [IsOpenImmersion r] (J : Z.IdealSheafData)
    {H K : CoherentAdicSystems J} (α : H ⟶ K) (m : ℕ) :
    ∃ (s : (Scheme.Modules.restrictFunctor r).obj (stableKernelImage J α m) ≅
        stableKernelImage (J.comap r) ((restrictFunctor J r).map α) m)
      (e : (stableKernelImageCompletion J α m).obj ⋙ Scheme.Modules.restrictFunctor r ≅
        (stableKernelImageCompletion (J.comap r) ((restrictFunctor J r).map α) m).obj),
      s.hom ≫ stableKernelImageIncl (J.comap r) ((restrictFunctor J r).map α) m =
          (Scheme.Modules.restrictFunctor r).map (stableKernelImageIncl J α m) ∧
        ∀ n : ℕ, (Scheme.Modules.restrictFunctor r).map
            (stableKernelImageCompletionProjection J α n m) ≫ e.hom.app (op n) =
          s.hom ≫ stableKernelImageCompletionProjection (J.comap r)
            ((restrictFunctor J r).map α) n m := by
  let M' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf :=
    Stacks.Algebraization.restrictCoherentModules r (coherentStableKernelImage J α m)
  let N' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf :=
    coherentStableKernelImage (J.comap r) ((restrictFunctor J r).map α) m
  obtain ⟨s, hs⟩ := stableKernelImage_restrictIso r J α m
  obtain ⟨a, ha⟩ := exists_completionRestrictSystemIso r J (coherentStableKernelImage J α m)
  let b := (ObjectProperty.ι (IsCoherentAdicSystem (J.comap r))).mapIso
    ((Stacks.Algebraization.completionFunctor Y (J.comap r)).mapIso
      (ObjectProperty.isoMk _ s : M' ≅ N'))
  refine ⟨s, a.symm ≪≫ b, hs, fun n => ?_⟩
  have hi : a.hom.app (op n) ≫ a.inv.app (op n) = 𝟙 _ :=
    congrArg (fun g => g.app (op n)) a.hom_inv_id
  show (Scheme.Modules.restrictFunctor r).map
      (stableKernelImageCompletionProjection J α n m) ≫
    (a.inv.app (op n) ≫ b.hom.app (op n)) = _
  refine (congrArg (fun z => z ≫ a.inv.app (op n) ≫ b.hom.app (op n)) (ha n).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => Stacks.Algebraization.completionProjection Y (J.comap r) M' n ≫ z)
    (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (fun z => Stacks.Algebraization.completionProjection Y (J.comap r) M' n ≫
    z ≫ b.hom.app (op n)) hi).trans ?_
  refine (congrArg (fun z => Stacks.Algebraization.completionProjection Y (J.comap r) M' n ≫ z)
    (Category.id_comp (b.hom.app (op n)))).trans ?_
  exact Stacks.Algebraization.completionFunctor_map_quotient Y (J.comap r)
    (ObjectProperty.isoMk _ s : M' ≅ N').hom n

/-- **The double system of completed stable kernel images commutes with restriction.** The
termwise identifications of
`Stacks.Coherent.exists_stableKernelImageCompletionRestrictSystemIso` are natural in the image
level, which is checked after the projections out of the stable kernel images — epimorphisms,
preserved by restriction — and, for the stable kernel images themselves, before their inclusions
into the terms of `F`, which are monomorphisms. -/
public theorem exists_stableKernelImageCompletionDiagramRestrictIso {Y Z : Scheme.{u}}
    [IsNoetherian Y] [IsNoetherian Z] (r : Y ⟶ Z) [IsOpenImmersion r] (J : Z.IdealSheafData)
    {H K : CoherentAdicSystems J} (α : H ⟶ K) :
    ∃ e : stableKernelImageCompletionDiagram J α ⋙
        (Functor.whiskeringRight ℕᵒᵖ Z.Modules Y.Modules).obj
          (Scheme.Modules.restrictFunctor r) ≅
        stableKernelImageCompletionDiagram (J.comap r) ((restrictFunctor J r).map α),
      ∀ m : ℕ, ∃ s : (Scheme.Modules.restrictFunctor r).obj (stableKernelImage J α m) ≅
          stableKernelImage (J.comap r) ((restrictFunctor J r).map α) m,
        s.hom ≫ stableKernelImageIncl (J.comap r) ((restrictFunctor J r).map α) m =
            (Scheme.Modules.restrictFunctor r).map (stableKernelImageIncl J α m) ∧
          ∀ n : ℕ, (Scheme.Modules.restrictFunctor r).map
              (stableKernelImageCompletionProjection J α n m) ≫
                (e.hom.app (op m)).app (op n) =
            s.hom ≫ stableKernelImageCompletionProjection (J.comap r)
              ((restrictFunctor J r).map α) n m := by
  have hpe : (Scheme.Modules.restrictFunctor r).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.restrictAdjunction r)
  choose s e hs he using fun m =>
    exists_stableKernelImageCompletionRestrictSystemIso r J α m
  refine ⟨NatIso.ofComponents (fun m => e m.unop) (fun {m k} f => ?_),
    fun m => ⟨s m, hs m, he m⟩⟩
  have h : k.unop ≤ m.unop := leOfHom f.unop
  have hsmap : (Scheme.Modules.restrictFunctor r).map
        (stableKernelImage_project J α k.unop m.unop h) ≫ (s k.unop).hom =
      (s m.unop).hom ≫
        stableKernelImage_project (J.comap r) ((restrictFunctor J r).map α) k.unop m.unop h := by
    refine (cancel_mono (stableKernelImageIncl (J.comap r)
      ((restrictFunctor J r).map α) k.unop)).mp ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => (Scheme.Modules.restrictFunctor r).map
      (stableKernelImage_project J α k.unop m.unop h) ≫ z) (hs k.unop)).trans ?_
    refine ((Scheme.Modules.restrictFunctor r).map_comp _ _).symm.trans ?_
    refine (congrArg (Scheme.Modules.restrictFunctor r).map
      (stableKernelImage_project_comp J α k.unop m.unop h)).trans ?_
    refine ((Scheme.Modules.restrictFunctor r).map_comp _ _).trans ?_
    refine (congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor r).map
      (H.obj.map (homOfLE h).op)) (hs m.unop).symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => (s m.unop).hom ≫ z)
      (stableKernelImage_project_comp (J.comap r) ((restrictFunctor J r).map α)
        k.unop m.unop h).symm).trans ?_
    exact (Category.assoc _ _ _).symm
  refine NatTrans.ext (funext fun n => ?_)
  have hepi : Epi (stableKernelImageCompletionProjection J α n.unop m.unop) :=
    epi_completionProjection J (coherentStableKernelImage J α m.unop) n.unop
  have hepi' : Epi ((Scheme.Modules.restrictFunctor r).map
      (stableKernelImageCompletionProjection J α n.unop m.unop)) := hpe.preserves _
  refine (cancel_epi ((Scheme.Modules.restrictFunctor r).map
    (stableKernelImageCompletionProjection J α n.unop m.unop))).mp ?_
  show (Scheme.Modules.restrictFunctor r).map
      (stableKernelImageCompletionProjection J α n.unop m.unop) ≫
      ((Scheme.Modules.restrictFunctor r).map
        ((stableKernelImageCompletion_project J α k.unop m.unop h).hom.app (op n.unop)) ≫
        (e k.unop).hom.app (op n.unop)) =
    (Scheme.Modules.restrictFunctor r).map
        (stableKernelImageCompletionProjection J α n.unop m.unop) ≫
      ((e m.unop).hom.app (op n.unop) ≫
        (stableKernelImageCompletion_project (J.comap r) ((restrictFunctor J r).map α)
          k.unop m.unop h).hom.app (op n.unop))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (e k.unop).hom.app (op n.unop))
    ((Scheme.Modules.restrictFunctor r).map_comp _ _).symm).trans ?_
  refine (congrArg (fun z => (Scheme.Modules.restrictFunctor r).map z ≫
    (e k.unop).hom.app (op n.unop))
      (stableKernelImageCompletion_project_projection J α k.unop m.unop h n.unop)).trans ?_
  refine (congrArg (fun z => z ≫ (e k.unop).hom.app (op n.unop))
    ((Scheme.Modules.restrictFunctor r).map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (Scheme.Modules.restrictFunctor r).map
    (stableKernelImage_project J α k.unop m.unop h) ≫ z) (he k.unop n.unop)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ stableKernelImageCompletionProjection (J.comap r)
    ((restrictFunctor J r).map α) n.unop k.unop) hsmap).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (s m.unop).hom ≫ z)
    (stableKernelImageCompletion_project_projection (J.comap r) ((restrictFunctor J r).map α)
      k.unop m.unop h n.unop).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (stableKernelImageCompletion_project (J.comap r)
    ((restrictFunctor J r).map α) k.unop m.unop h).hom.app (op n.unop))
      (he m.unop n.unop).symm).trans ?_
  exact Category.assoc _ _ _

/-- **The kernel commutes with restriction along an open immersion**, canonically over the
restricted source system.

Restriction preserves limits of every shape, so it carries the limit of the double system to the
limit of the restricted double system; that diagram is identified with the double system of the
restricted morphism by
`Stacks.Coherent.exists_stableKernelImageCompletionDiagramRestrictIso`, and two limits of
isomorphic diagrams have canonically isomorphic apices. The identification lies over the
inclusions into `F` because those inclusions are built from the projections of the limit and from
the comparisons to the terms of `F`, both of which the identification respects. -/
public theorem coherentAdicKernel_restrict {Y : Scheme.{u}} [IsNoetherian Y] (f : Y ⟶ X)
    [IsOpenImmersion f] (α : F ⟶ G) :
    ∃ e : (restrictFunctor I f).obj (coherentAdicKernel I α) ≅
        coherentAdicKernel (I.comap f) ((restrictFunctor I f).map α),
      e.hom ≫ coherentAdicKernelι (I.comap f) ((restrictFunctor I f).map α) =
        (restrictFunctor I f).map (coherentAdicKernelι I α) := by
  have hpl : PreservesLimitsOfShape ℕᵒᵖ (Scheme.Modules.restrictFunctor f) :=
    preservesLimitsOfShapeNatOp_restrictFunctor f
  have hpe : (Scheme.Modules.restrictFunctor f).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.restrictAdjunction f)
  obtain ⟨d, hd⟩ := exists_stableKernelImageCompletionDiagramRestrictIso f I α
  let W := (Functor.whiskeringRight ℕᵒᵖ X.Modules Y.Modules).obj
    (Scheme.Modules.restrictFunctor f)
  let hc := (IsLimit.postcomposeHomEquiv d
      (W.mapCone (limit.cone (stableKernelImageCompletionDiagram I α)))).symm
    (isLimitOfPreserves W (limit.isLimit (stableKernelImageCompletionDiagram I α)))
  let a := hc.conePointUniqueUpToIso
    (limit.isLimit (stableKernelImageCompletionDiagram (I.comap f)
      ((restrictFunctor I f).map α)))
  refine ⟨ObjectProperty.isoMk _ a, ObjectProperty.hom_ext (IsCoherentAdicSystem (I.comap f))
    (NatTrans.ext (funext fun n => ?_))⟩
  have ha : a.hom.app n ≫
      stableKernelImageLimitπ (I.comap f) ((restrictFunctor I f).map α) n.unop n.unop =
      (Scheme.Modules.restrictFunctor f).map
        (stableKernelImageLimitπ I α n.unop n.unop) ≫ (d.hom.app n).app n :=
    congrArg (fun g => g.app n) (hc.conePointUniqueUpToIso_hom_comp
      (limit.isLimit (stableKernelImageCompletionDiagram (I.comap f)
        ((restrictFunctor I f).map α))) n)
  obtain ⟨s, hs, hq⟩ := hd n.unop
  have hepi : Epi (stableKernelImageCompletionProjection I α n.unop n.unop) :=
    epi_completionProjection I (coherentStableKernelImage I α n.unop) n.unop
  have hepi' : Epi ((Scheme.Modules.restrictFunctor f).map
      (stableKernelImageCompletionProjection I α n.unop n.unop)) := hpe.preserves _
  have hinclmap : stableKernelImageIncl I α n.unop ≫
      F.obj.map (homOfLE (le_refl n.unop)).op = stableKernelImageIncl I α n.unop := by simp
  have hr : (d.hom.app n).app n ≫
      stableKernelImageCompletionToLevel (I.comap f) ((restrictFunctor I f).map α)
        n.unop n.unop le_rfl =
      (Scheme.Modules.restrictFunctor f).map
        (stableKernelImageCompletionToLevel I α n.unop n.unop le_rfl) := by
    have hB : (Scheme.Modules.restrictFunctor f).map
          (stableKernelImageCompletionProjection I α n.unop n.unop) ≫
        (Scheme.Modules.restrictFunctor f).map
          (stableKernelImageCompletionToLevel I α n.unop n.unop le_rfl) =
        (Scheme.Modules.restrictFunctor f).map (stableKernelImageIncl I α n.unop) :=
      (((Scheme.Modules.restrictFunctor f).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.restrictFunctor f).map
            (stableKernelImageCompletionToLevel_fac I α n.unop n.unop le_rfl))).trans
        (congrArg (Scheme.Modules.restrictFunctor f).map hinclmap)
    refine (cancel_epi ((Scheme.Modules.restrictFunctor f).map
      (stableKernelImageCompletionProjection I α n.unop n.unop))).mp (Eq.trans ?_ hB.symm)
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ stableKernelImageCompletionToLevel (I.comap f)
      ((restrictFunctor I f).map α) n.unop n.unop le_rfl) (hq n.unop)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => s.hom ≫ z)
      (stableKernelImageCompletionToLevel_fac (I.comap f) ((restrictFunctor I f).map α)
        n.unop n.unop le_rfl)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ ((restrictFunctor I f).obj F).obj.map
      (homOfLE (le_refl n.unop)).op) hs).trans ?_
    refine ((Scheme.Modules.restrictFunctor f).map_comp _ _).symm.trans ?_
    exact congrArg (Scheme.Modules.restrictFunctor f).map hinclmap
  show a.hom.app n ≫ (stableKernelImageLimitπ (I.comap f) ((restrictFunctor I f).map α)
      n.unop n.unop ≫ stableKernelImageCompletionToLevel (I.comap f)
        ((restrictFunctor I f).map α) n.unop n.unop le_rfl) =
    (Scheme.Modules.restrictFunctor f).map (stableKernelImageLimitπ I α n.unop n.unop ≫
      stableKernelImageCompletionToLevel I α n.unop n.unop le_rfl)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ stableKernelImageCompletionToLevel (I.comap f)
    ((restrictFunctor I f).map α) n.unop n.unop le_rfl) ha).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (Scheme.Modules.restrictFunctor f).map
    (stableKernelImageLimitπ I α n.unop n.unop) ≫ z) hr).trans ?_
  exact ((Scheme.Modules.restrictFunctor f).map_comp _ _).symm

end Stacks.Coherent

end
