module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksCore.Tactic.StacksAttribute

/-!
# A torsion coherent adic system is the completion of one of its own terms

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X` and `(F_n)`
a coherent adic system along `ℐ` in the sense of `Stacks.Coherent.IsCoherentAdicSystem`. If one
power `ℐ ᵈ⁺¹` annihilates every term of the system, then `(F_n)` lies in the essential image of
the completion functor `Coh(𝒪_X) ⥤ Coh(X, ℐ)` of Stacks 0880: it is the completion of its own
`d`-th term.

This is the essential-image assertion that [Stacks, Tag 0EHP] opens with; the tag itself is
registered at `Stacks.Algebraization.essImage_and_bijective_of_isPowerAnnihilated`.

The reason is that the transitions become invertible once the index passes the annihilating
exponent. The transition `F_{n+1} ⟶ F_n` *is* the quotient projection by `ℐ ⁿ⁺¹`, up to the
isomorphism `IsCoherentAdicSystem.quotientIso`, and for `d ≤ n` the subsheaf `ℐ ⁿ⁺¹ F_{n+1}` is
already contained in `ℐ ᵈ⁺¹ F_{n+1} = 0`; a quotient by the zero subsheaf changes nothing. So all
the terms of index `≥ d` are canonically identified with `F_d`, and the system is determined by
that single coherent sheaf.

## Main results

* `Stacks.Algebraization.isIso_map_succ_of_annihilated` and
  `Stacks.Algebraization.isIso_map_of_annihilated` — the transitions of a uniformly
  `ℐ ᵈ⁺¹`-annihilated coherent adic system are isomorphisms above the index `d`.
* `Stacks.Algebraization.mem_essImage_completionFunctor_of_isSystemPowerAnnihilated` — such a
  system is in the essential image of the completion functor.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the Stacks source's
`F_{n+1}`, which is why the exponent annihilating the `n`-th term is `n + 1` and why the
annihilating exponent of the hypothesis is written `d + 1`. The hypothesis is
`Stacks.Algebraization.IsSystemPowerAnnihilated`, whose exponent is made positive by
`IsSystemPowerAnnihilated.exists_pos`, so writing it as `d + 1` loses nothing.

The comparison `F_d ⟶ F_n` is built *without* a case distinction on `n ≤ d`, as
`inv (F_{max d n} ⟶ F_d) ≫ (F_{max d n} ⟶ F_n)`: the first factor is invertible because
`d ≤ max d n`, and routing through `max d n` covers both the descending and the ascending
direction at once. A definition by cases would have to be unfolded separately in each of the
three identities below, and at `n = d` both branches apply.

Each component of the comparison isomorphism is produced by reducing that map modulo `ℐ ⁿ⁺¹`:
`idealPowerQuotientMap` of an isomorphism is an isomorphism, and
`IsCoherentAdicSystem.isIso_idealPowerQuotientMap_map` says that a transition reduced modulo
`ℐ ⁿ⁺¹` is one too, so the reduction of the composite is invertible; its target
`F_n / ℐ ⁿ⁺¹ F_n` is `F_n` itself because `ℐ ⁿ⁺¹ F_n = 0`. The three identities the comparison
has to satisfy — the cone property over the transitions, the normalization against the
projections `F_d ⟶ F_d / ℐ ⁿ⁺¹ F_d`, and the naturality square — are each proved by cancelling
the epimorphism `Stacks.Algebraization.completionProjection`; only the object formula of the
completion functor and its transition compatibility are used.

`completionFunctor` carries `@[no_expose]`, so the object formula
`Stacks.Algebraization.completionFunctor_obj` is not available as a definitional unfolding and
the components of the comparison have to be transported along it by an `eqToHom`. That `eqToHom`
occurs only inside the proof of a `Prop` — `CategoryTheory.Functor.essImage` is an existential
over a `Nonempty` — and in no definition's body; it is cancelled against the one inside
`Stacks.Algebraization.completionProjection` by
`Stacks.Algebraization.comp_eqToHom_symm_comp_eqToHom`.

## References

* [Stacks Project, Tag 0EHP](https://stacks.math.columbia.edu/tag/0EHP)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}} {I : X.IdealSheafData} {F : ℕᵒᵖ ⥤ X.Modules}

/-! ### The transitions above the annihilating exponent are invertible -/

/-- If one power `ℐ ᵈ⁺¹` annihilates every term of a coherent adic system, then the transition
`F_{n+1} ⟶ F_n` is an isomorphism for every `n ≥ d`.

That transition is the projection onto `F_{n+1} / ℐ ⁿ⁺¹ F_{n+1}`, and `ℐ ⁿ⁺¹ F_{n+1}` is
contained in `ℐ ᵈ⁺¹ F_{n+1}`, which vanishes. -/
public theorem isIso_map_succ_of_annihilated (hF : Stacks.Coherent.IsCoherentAdicSystem I F)
    {d : ℕ} (hann : ∀ k : ℕ, idealPowerMultiple I (d + 1) (F.obj (op k)) = ⊥)
    {n : ℕ} (hdn : d ≤ n) : IsIso (F.map (homOfLE (Nat.le_succ n)).op) := by
  have hbot : idealPowerMultiple I (n + 1) (F.obj (op (n + 1))) = ⊥ :=
    idealPowerMultiple_eq_bot_of_le (hann (n + 1)) (Nat.add_le_add_right hdn 1)
  have : IsIso (cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1) (F.obj (op (n + 1)))).ι) :=
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot I (n + 1) _ hbot
  rw [← hF.cokernel_π_comp_quotientIso n]
  infer_instance

/-- If one power `ℐ ᵈ⁺¹` annihilates every term of a coherent adic system, then every transition
`F_n ⟶ F_m` with `d ≤ m ≤ n` is an isomorphism, being a composite of the invertible steps of
`Stacks.Algebraization.isIso_map_succ_of_annihilated`. -/
public theorem isIso_map_of_annihilated (hF : Stacks.Coherent.IsCoherentAdicSystem I F)
    {d : ℕ} (hann : ∀ k : ℕ, idealPowerMultiple I (d + 1) (F.obj (op k)) = ⊥)
    {m n : ℕ} (hdm : d ≤ m) (hmn : m ≤ n) : IsIso (F.map (homOfLE hmn).op) := by
  induction hmn with
  | refl => simpa using (inferInstance : IsIso (𝟙 (F.obj (op m))))
  | @step n hmn ih =>
      have h₁ : IsIso (F.map (homOfLE (Nat.le_succ n)).op) :=
        isIso_map_succ_of_annihilated hF hann (hdm.trans hmn)
      have h₂ : IsIso (F.map (homOfLE hmn).op) := ih
      have hcomp : (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op =
          (homOfLE (Nat.le_trans hmn (Nat.le_succ n))).op := Subsingleton.elim _ _
      rw [← hcomp, Functor.map_comp]
      infer_instance

/-! ### The comparison with the completion of the `d`-th term -/

/-- **An object of `Coh(X, ℐ)` annihilated by a power of `ℐ` is in the essential image of the
completion functor of Stacks 0880.**

Writing the annihilating exponent as `d + 1`, the system is the completion of its own `d`-th
term: above the index `d` the transitions are invertible, so every term is canonically
`F_d / ℐ ⁿ⁺¹ F_d`, which is the `n`-th term of the completion of `F_d`. -/
public theorem mem_essImage_completionFunctor_of_isSystemPowerAnnihilated
    (X : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : Stacks.Coherent.CoherentAdicSystems I) (hF : IsSystemPowerAnnihilated I F.obj) :
    (completionFunctor X I).essImage F := by
  obtain ⟨c, hc, hann⟩ := hF.exists_pos
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, c = d + 1 := ⟨c - 1, (Nat.succ_pred_eq_of_pos hc).symm⟩
  have hFsys : Stacks.Coherent.IsCoherentAdicSystem I F.obj := F.property
  -- the coherent sheaf the system turns out to be the completion of
  let M : X.Modules := F.obj.obj (op d)
  let G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
    ⟨M, hFsys.isCoherent d⟩
  -- the comparison `F_d ⟶ F_n`, routed through the index `max d n`
  let t : ∀ n : ℕ, F.obj.obj (op (max d n)) ⟶ M := fun n =>
    F.obj.map (homOfLE (le_max_left d n)).op
  let u : ∀ n : ℕ, F.obj.obj (op (max d n)) ⟶ F.obj.obj (op n) := fun n =>
    F.obj.map (homOfLE (le_max_right d n)).op
  have htIso : ∀ n : ℕ, IsIso (t n) := fun n =>
    isIso_map_of_annihilated hFsys hann le_rfl (le_max_left d n)
  let s : ∀ n : ℕ, M ⟶ F.obj.obj (op n) := fun n =>
    have := htIso n
    inv (t n) ≫ u n
  -- the projections `F_n ⟶ F_n / ℐ ⁿ⁺¹ F_n`, which are invertible
  let π : ∀ n : ℕ, F.obj.obj (op n) ⟶ idealPowerQuotient I (n + 1) (F.obj.obj (op n)) :=
    fun n => cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) (F.obj.obj (op n))).ι
  have hπIso : ∀ n : ℕ, IsIso (π n) := fun n =>
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot I (n + 1) _
      (hFsys.idealPowerMultiple_eq_bot n)
  -- the reduction of the comparison modulo `ℐ ⁿ⁺¹` is invertible
  have hsIso : ∀ n : ℕ, IsIso (idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl (s n)) := by
    intro n
    have := htIso n
    have hinv : IsIso (idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl (inv (t n))) :=
      isIso_idealPowerQuotientMap I (n + 1) (asIso (inv (t n)))
    have hu : IsIso (idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl (u n)) :=
      hFsys.isIso_idealPowerQuotientMap_map I (n + 1) (le_max_right d n) le_rfl
    have hfac : s n = inv (t n) ≫ u n := rfl
    rw [hfac, idealPowerQuotientMap_comp]
    infer_instance
  -- the comparison is a cone over the transitions of the system
  have hcone : ∀ n : ℕ, s (n + 1) ≫ F.obj.map (homOfLE (Nat.le_add_right n 1)).op = s n := by
    intro n
    have := htIso n
    have := htIso (n + 1)
    have hmm : max d n ≤ max d (n + 1) :=
      max_le_max le_rfl (Nat.le_add_right n 1)
    let w : F.obj.obj (op (max d (n + 1))) ⟶ F.obj.obj (op (max d n)) :=
      F.obj.map (homOfLE hmm).op
    have hwt : w ≫ t n = t (n + 1) := (F.obj.map_comp _ _).symm
    have hwu : w ≫ u n = u (n + 1) ≫ F.obj.map (homOfLE (Nat.le_add_right n 1)).op :=
      (F.obj.map_comp _ _).symm.trans (F.obj.map_comp (homOfLE (le_max_right d (n + 1))).op _)
    refine (cancel_epi (t (n + 1))).1 ?_
    dsimp only [s]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← hwu, ← hwt, Category.assoc, IsIso.hom_inv_id_assoc]
  -- the components of the comparison isomorphism of systems
  let comp : ∀ n : ℕ,
      ((completionFunctor X I).obj G).obj.obj (op n) ⟶ F.obj.obj (op n) := fun n =>
    have := hπIso n
    eqToHom (completionFunctor_obj X I G n) ≫
      idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl (s n) ≫ inv (π n)
  have hcompIso : ∀ n : ℕ, IsIso (comp n) := by
    intro n
    have := hπIso n
    have := hsIso n
    dsimp only [comp]
    infer_instance
  -- the normalization of the components against the projections of the completion
  have hproj : ∀ n : ℕ, completionProjection X I G n ≫ comp n = s n := by
    intro n
    have := hπIso n
    have hq : cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) M).ι ≫
        idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl (s n) = s n ≫ π n :=
      idealPowerQuotientMap_π I I (n + 1) (n + 1) le_rfl (s n)
    dsimp only [comp, completionProjection]
    refine (comp_eqToHom_symm_comp_eqToHom _ (completionFunctor_obj X I G n) _).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ inv (π n)) hq).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => s n ≫ k) (IsIso.hom_inv_id (π n))).trans (Category.comp_id _))))
  -- naturality of the components
  have hnat : ∀ n : ℕ,
      ((completionFunctor X I).obj G).obj.map (homOfLE (Nat.le_add_right n 1)).op ≫ comp n =
        comp (n + 1) ≫ F.obj.map (homOfLE (Nat.le_add_right n 1)).op := by
    intro n
    have hepi : Epi (completionProjection X I G (n + 1)) :=
      epi_completionProjection X I G (n + 1)
    refine (cancel_epi (completionProjection X I G (n + 1))).1 ?_
    have hleft : completionProjection X I G (n + 1) ≫
        ((completionFunctor X I).obj G).obj.map (homOfLE (Nat.le_add_right n 1)).op ≫
          comp n = s n :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ comp n) (completionProjection_transition X I G n)).trans
          (hproj n))
    have hright : completionProjection X I G (n + 1) ≫
        comp (n + 1) ≫ F.obj.map (homOfLE (Nat.le_add_right n 1)).op = s n :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ F.obj.map (homOfLE (Nat.le_add_right n 1)).op)
            (hproj (n + 1))).trans (hcone n))
    exact hleft.trans hright.symm
  -- assemble the isomorphism of inverse systems
  let τ : ((completionFunctor X I).obj G).obj ⟶ F.obj := NatTrans.ofOpSequence comp hnat
  have : ∀ n : ℕᵒᵖ, IsIso (τ.app n) := fun n => hcompIso n.unop
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact ⟨G, ⟨ObjectProperty.isoMk (Stacks.Coherent.IsCoherentAdicSystem I) (asIso τ)⟩⟩

end Stacks.Algebraization

end
