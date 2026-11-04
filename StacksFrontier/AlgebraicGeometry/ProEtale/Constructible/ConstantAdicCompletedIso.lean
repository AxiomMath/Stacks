module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantIsoTowerMittagLeffler
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicReductions
public import StacksFrontier.RingTheory.Module.AdicSystem.CompleteBase
public import StacksCore.Tactic.StacksAttribute

/-!
# A sheaf with constant adic reductions is a completed constant sheaf

Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal and `F` a sheaf of `Λ`-modules on the small
pro-étale site of a scheme `X`, and suppose that `F` is the limit of its adic reductions
`F / IⁿF`, that each of those is a constant sheaf, and that `F / IF` is of finite type. Then
`F ≅ M̲^∧` for a single `I`-adically complete `Λ`-module `M` which is finite over `Λ^∧`: this is
Stacks Tag 09BV.

`AlgebraicGeometry.ProEtale.exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant` produces
the module `M` and isomorphisms `(M / IⁿM)̲ ≅ F / IⁿF` at every level. What this file adds is that
the isomorphisms can be chosen compatibly with the transition maps, so that they assemble into an
isomorphism of towers and hence, in the limit, into `F ≅ M̲^∧`.

## Main results

* `AlgebraicGeometry.ProEtale.isMittagLeffler_isoTower_constantAdicQuotientTower`: the tower of
  self-isomorphisms of the constant sheaves `(M / IⁿM)̲` is Mittag-Leffler.
* `AlgebraicGeometry.ProEtale.nonempty_natIso_constantAdicQuotientTower_of_isConstant`: the
  termwise isomorphisms can be chosen compatibly, i.e. the two towers are isomorphic.
* `AlgebraicGeometry.ProEtale.exists_iso_completedConstantSheaf_of_isConstant`: **Stacks Tag
  09BV**.

## Implementation notes

Weak contractibility of `X` is not used; what the argument needs of the site is a terminal object,
which `AlgebraicGeometry.ProEtale.isTerminalProEtId` provides, and non-emptiness of the topos,
which only the production of the coefficient module consumes. The source instead evaluates its
sheaves of isomorphisms at the weakly contractible `X`, where surjections of sheaves of sets are
surjective on sections; here the comparison with the module system is a bijection on sections over
the terminal object, so no surjectivity of sections is needed.

The section universe is `max (u + 1) w` because Tag 093T (2) is stated at the section universe
`max u' v' x` of its site, and the small pro-étale site of `X : Scheme.{u}` is a category in
`Type (u + 1)` with morphisms in `Type u`.

## References

* [Stacks Project, Tag 09BV](https://stacks.math.columbia.edu/tag/09BV)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w y

namespace AlgebraicGeometry.ProEtale

section Square

variable (Λ : Type v) [CommRing Λ] (I : Ideal Λ) (M : ModuleCat.{y} Λ)

/-- **The reduction maps of the adic quotients commute with a self-isomorphism and its
reduction.** Here the reduction `tr n e` of a self-isomorphism `e` is characterized by its effect
on the class of an element (`htr`). -/
theorem ofHom_comp_adicQuotient_transitionMap
    (tr : ∀ n : ℕ,
        (((adicQuotientModuleSystem Λ I M).obj (op (n + 1)) : Type y) ≃ₗ[Λ]
          ((adicQuotientModuleSystem Λ I M).obj (op (n + 1)) : Type y)) →
        (((adicQuotientModuleSystem Λ I M).obj (op n) : Type y) ≃ₗ[Λ]
          ((adicQuotientModuleSystem Λ I M).obj (op n) : Type y)))
    (htr : ∀ (n : ℕ) (e : _) (x : (M : Type y)),
      tr n e (Submodule.Quotient.mk x) =
        AdicCompletion.transitionMap I (M : Type y) (Nat.le_succ n)
          (e (Submodule.Quotient.mk x)))
    (n : ℕ)
    (e : ((adicQuotientModuleSystem Λ I M).obj (op (n + 1)) : Type y) ≃ₗ[Λ]
      ((adicQuotientModuleSystem Λ I M).obj (op (n + 1)) : Type y)) :
    ModuleCat.ofHom (LinearEquiv.toLinearMap e) ≫
        (adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_add_right n 1)).op =
      (adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_add_right n 1)).op ≫
        ModuleCat.ofHom (tr n e).toLinearMap := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    show ((adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_add_right n 1)).op).hom
        (e (Submodule.Quotient.mk x)) =
      tr n e (((adicQuotientModuleSystem Λ I M).map
        (homOfLE (Nat.le_add_right n 1)).op).hom (Submodule.Quotient.mk x))
    rw [adicQuotient_transitionMap_mk Λ I M n x, htr n e x]
    simp only [adicQuotientModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
    rfl

end Square

variable (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ)
  (M : ModuleCat.{max (u + 1) w} Λ)

section MittagLeffler

variable [HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)]
  [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{max (u + 1) w} Λ)]
  [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{max (u + 1) w} Λ))]

/-- **The tower of self-isomorphisms of the constant sheaves of the adic quotients of `M` is
Mittag-Leffler**, as soon as every reduction `M / IⁿM` is finite over `Λ` and the completion of `M`
is finite over `Λ^∧`. -/
theorem isMittagLeffler_isoTower_constantAdicQuotientTower
    (hMfin : ∀ n : ℕ, Module.Finite Λ
      ((M : Type (max (u + 1) w)) ⧸ (I ^ n • ⊤ : Submodule Λ (M : Type (max (u + 1) w)))))
    (hMcompl : Module.Finite (AdicCompletion I Λ)
      (AdicCompletion I (M : Type (max (u + 1) w)))) :
    (Functor.isoTower (constantAdicQuotientTower X Λ I M) (constantAdicQuotientTower X Λ I M)
      (epi_constantAdicQuotientTower_map X Λ I M)
      (descendsIsos_constantAdicQuotientTower_self X Λ I M)).IsMittagLeffler := by
  have := hMcompl
  obtain ⟨tr, htr, hML⟩ :=
    Stacks.AdicSystem.CompleteBase.isom_quotient_system_isMittagLeffler_of_finite_adicCompletion
      (Λ := Λ) I (M := (M : Type (max (u + 1) w)))
  exact Stacks.ConstantSheaf.isMittagLeffler_isoTower_constantSheaf (Scheme.ProEt.topology X) Λ
    (adicQuotientModuleSystem Λ I M) tr
    (fun n => by
      have : Module.Finite Λ
          (((adicQuotientModuleSystem Λ I M).obj (op n)) : Type (max (u + 1) w)) := hMfin n
      exact Module.finitePresentation_of_finite Λ _)
    (isTerminalProEtId X)
    (ofHom_comp_adicQuotient_transitionMap Λ I M tr htr)
    (epi_constantAdicQuotientTower_map X Λ I M)
    (descendsIsos_constantAdicQuotientTower_self X Λ I M) hML

end MittagLeffler

section Main

variable [HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)]
  [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{max (u + 1) w} Λ)]
  [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{max (u + 1) w} Λ))]

/-- **The termwise isomorphisms of Tag 09BV can be chosen compatibly with the transition maps.**
The tower of constant sheaves of the adic quotients of `M` is isomorphic, as a tower, to the adic
quotient tower of `F`. -/
theorem nonempty_natIso_constantAdicQuotientTower_of_isConstant
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hMfin : ∀ n : ℕ, Module.Finite Λ
      ((M : Type (max (u + 1) w)) ⧸ (I ^ n • ⊤ : Submodule Λ (M : Type (max (u + 1) w)))))
    (hMcompl : Module.Finite (AdicCompletion I Λ)
      (AdicCompletion I (M : Type (max (u + 1) w))))
    (hMiso : ∀ n : ℕ, Nonempty ((constantAdicQuotientTower X Λ I M).obj (op n) ≅ Q.obj (op n))) :
    Nonempty (constantAdicQuotientTower X Λ I M ≅ Q) :=
  Functor.nonempty_natIso_of_isMittagLeffler_isoTower (constantAdicQuotientTower X Λ I M) Q
    (epi_constantAdicQuotientTower_map X Λ I M)
    (descendsIsos_constantAdicQuotientTower_self X Λ I M)
    (descendsIsos_constantAdicQuotientTower X Λ I M F Q q hq)
    (fun n => hMiso n.unop)
    (isMittagLeffler_isoTower_constantAdicQuotientTower X Λ I M hMfin hMcompl)

/-- Let `X` be a scheme whose pro-étale topos is not empty, let `Λ` be a Noetherian ring and
`I ⊆ Λ` an ideal, and let `F` be a sheaf of `Λ`-modules on the small pro-étale site of `X` such
that

1. `F` is the limit of its adic reductions `F / IⁿF`,
2. every `F / IⁿF` is a constant sheaf, and
3. `F / IF` is the constant sheaf of a finite module.

Then `F ≅ M̲^∧` for an `I`-adically complete `Λ`-module `M` which is finite over `Λ^∧`. -/
@[stacks 09BV "the sheaf is the completed constant sheaf of a finite complete module"]
theorem exists_iso_completedConstantSheaf_of_isConstant
    (hne : ∃ U : X.ProEt, (⊥ : Sieve U) ∉ Scheme.ProEt.topology X U)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hlim : IsLimit (Limits.Cone.mk F q))
    (hconst : ∀ n : ℕ, ∃ N : ModuleCat.{max (u + 1) w} Λ,
      Nonempty ((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) w} Λ)).obj N ≅ Q.obj (op n)))
    (hfin : ∃ N : ModuleCat.{max (u + 1) w} Λ,
      Module.Finite Λ (N : Type (max (u + 1) w)) ∧
      Nonempty ((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) w} Λ)).obj N ≅ Q.obj (op 1))) :
    ∃ M : ModuleCat.{max (u + 1) w} Λ,
      IsAdicComplete I (M : Type (max (u + 1) w)) ∧
      Module.Finite (AdicCompletion I Λ) (AdicCompletion I (M : Type (max (u + 1) w))) ∧
      Nonempty (F ≅ completedConstantSheaf X Λ I M) := by
  obtain ⟨M, hMcomplete, -, hMcompl, hMfin, hMiso⟩ :=
    exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant X Λ I hne F Q q hq hconst hfin
  obtain ⟨α⟩ := nonempty_natIso_constantAdicQuotientTower_of_isConstant X Λ I M F Q q hq
    hMfin hMcompl hMiso
  exact ⟨M, hMcomplete, hMcompl,
    ⟨(IsLimit.conePointsIsoOfNatIso (limit.isLimit (constantAdicQuotientTower X Λ I M))
      hlim α).symm⟩⟩

end Main

end AlgebraicGeometry.ProEtale

end
