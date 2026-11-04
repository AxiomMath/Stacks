module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantIsoTowerMittagLeffler
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicCompletedIso
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicQuotientTower
public import StacksFrontier.RingTheory.Module.AdicSystem.CompleteBase

/-!
# A sheaf with constant adic reductions is a limit of constant sheaves, on a site with a terminal
object

Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal and `F` a sheaf of `Λ`-modules on a site with a
terminal object whose topos is not empty, and suppose that `F` is the limit of its adic reductions
`F / IⁿF`, that each of those is a constant sheaf, and that `F / IF` is the constant sheaf of a
finite module. Then `F` is the limit of the constant sheaves `(M / IⁿM)̲` for a single
`I`-adically complete `Λ`-module `M` which is finite over `Λ^∧`. On the small pro-étale site of a
scheme this is Stacks Tag 09BV,
`AlgebraicGeometry.ProEtale.exists_iso_completedConstantSheaf_of_isConstant`; this file states
the argument of
`StacksFrontier/AlgebraicGeometry/ProEtale/Constructible/ConstantAdicCompletedIso.lean` for an
arbitrary site with a terminal object, with the quotient characterized by
`Stacks.ModuleSheaf.IsQuotientBy`, so that it applies to the slices of the pro-étale site too.

`Stacks.ModuleSheaf.exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant` produces
the module `M` and isomorphisms `(M / IⁿM)̲ ≅ F / IⁿF` at every level. What this file adds is that
the isomorphisms can be chosen compatibly with the transition maps, so that they assemble into an
isomorphism of towers and hence, in the limit, into `F ≅ lim (M / IⁿM)̲`.

## Main results

* `Stacks.ModuleSheaf.isMittagLeffler_isoTower_constantAdicQuotientTower`: the tower of
  self-isomorphisms of the constant sheaves `(M / IⁿM)̲` is Mittag-Leffler.
* `Stacks.ModuleSheaf.nonempty_natIso_constantAdicQuotientTower_of_isConstant`: the
  termwise isomorphisms can be chosen compatibly, i.e. the two towers are isomorphic.
* `Stacks.ModuleSheaf.exists_iso_limit_constantAdicQuotientTower_of_isConstant`: `F` is the
  limit of the constant sheaves of the adic quotients of `M`.

## Implementation notes

The compatible choice is `CategoryTheory.Functor.nonempty_natIso_of_isMittagLeffler_isoTower`,
which replaces the source's torsor argument: of its three inputs, that the transition maps of the
tower of constant sheaves are epimorphisms and that isomorphisms descend along them are proved in
`StacksFrontier/AlgebraicGeometry/ProEtale/Constructible/ConstantAdicQuotientTower.lean`, and the
third, that the tower of self-isomorphisms of the constant sheaves is Mittag-Leffler, is assembled
here out of two general statements:

* `Stacks.ConstantSheaf.isMittagLeffler_isoTower_constantSheaf` transfers the condition from the
  system `n ↦ Isom_Λ(M / IⁿM, M / IⁿM)` of module isomorphisms, using Tag 093T (2) and its
  naturality along the reduction maps
  (`AlgebraicGeometry.ProEtale.ofHom_comp_adicQuotient_transitionMap`), and
* `Stacks.AdicSystem.CompleteBase.isom_quotient_system_isMittagLeffler_of_finite_adicCompletion`
  is Tag 09BB for that system — over `Λ^∧` rather than over `Λ`, which is what `M` is finite over.

The section universe is `max u v w` for a site in `Type u` with morphisms in `Type v`, because
Tag 093T (2) is stated at the section universe `max u' v' x` of its site.

## References

* [Stacks Project, Tag 09BV](https://stacks.math.columbia.edu/tag/09BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w r

namespace Stacks.ModuleSheaf

open AlgebraicGeometry.ProEtale (adicQuotientModuleSystem ofHom_comp_adicQuotient_transitionMap)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasTerminal C]
  (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ)
  (M : ModuleCat.{max u v w} Λ)

section MittagLeffler

variable [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{max u v w} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{max u v w} Λ))]

/-- **The tower of self-isomorphisms of the constant sheaves of the adic quotients of `M` is
Mittag-Leffler**, as soon as every reduction `M / IⁿM` is finite over `Λ` and the completion of `M`
is finite over `Λ^∧`. This is the third and last input of
`CategoryTheory.Functor.nonempty_natIso_of_isMittagLeffler_isoTower` at Tag 09BV: Tag 09BB over
the completed base gives the condition for the system of module isomorphisms, and Tag 093T (2)
carries it to the sheaf-level tower. -/
theorem isMittagLeffler_isoTower_constantAdicQuotientTower
    (hMfin : ∀ n : ℕ, Module.Finite Λ
      ((M : Type (max u v w)) ⧸ (I ^ n • ⊤ : Submodule Λ (M : Type (max u v w)))))
    (hMcompl : Module.Finite (AdicCompletion I Λ)
      (AdicCompletion I (M : Type (max u v w)))) :
    (Functor.isoTower (constantAdicQuotientTower J Λ I M) (constantAdicQuotientTower J Λ I M)
      (epi_constantAdicQuotientTower_map J Λ I M)
      (descendsIsos_constantAdicQuotientTower_self J Λ I M)).IsMittagLeffler := by
  have := hMcompl
  obtain ⟨tr, htr, hML⟩ :=
    Stacks.AdicSystem.CompleteBase.isom_quotient_system_isMittagLeffler_of_finite_adicCompletion
      (Λ := Λ) I (M := (M : Type (max u v w)))
  exact Stacks.ConstantSheaf.isMittagLeffler_isoTower_constantSheaf J Λ
    (adicQuotientModuleSystem Λ I M) tr
    (fun n => by
      have : Module.Finite Λ
          (((adicQuotientModuleSystem Λ I M).obj (op n)) : Type (max u v w)) := hMfin n
      exact Module.finitePresentation_of_finite Λ _)
    terminalIsTerminal
    (ofHom_comp_adicQuotient_transitionMap Λ I M tr htr)
    (epi_constantAdicQuotientTower_map J Λ I M)
    (descendsIsos_constantAdicQuotientTower_self J Λ I M) hML

end MittagLeffler

section Main

variable [HasSheafify J (ModuleCat.{max u v w} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{max u v w} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{max u v w} Λ))]

/-- **The termwise isomorphisms of Tag 09BV can be chosen compatibly with the transition maps.**
The tower of constant sheaves of the adic quotients of `M` is isomorphic, as a tower, to the adic
quotient tower of `F`. -/
theorem nonempty_natIso_constantAdicQuotientTower_of_isConstant
    (F : Sheaf J (ModuleCat.{max u v w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{max u v w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy J Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hMfin : ∀ n : ℕ, Module.Finite Λ
      ((M : Type (max u v w)) ⧸ (I ^ n • ⊤ : Submodule Λ (M : Type (max u v w)))))
    (hMcompl : Module.Finite (AdicCompletion I Λ)
      (AdicCompletion I (M : Type (max u v w))))
    (hMiso : ∀ n : ℕ, Nonempty ((constantAdicQuotientTower J Λ I M).obj (op n) ≅ Q.obj (op n))) :
    Nonempty (constantAdicQuotientTower J Λ I M ≅ Q) :=
  Functor.nonempty_natIso_of_isMittagLeffler_isoTower (constantAdicQuotientTower J Λ I M) Q
    (epi_constantAdicQuotientTower_map J Λ I M)
    (descendsIsos_constantAdicQuotientTower_self J Λ I M)
    (descendsIsos_constantAdicQuotientTower J Λ I M F Q q hq)
    (fun n => hMiso n.unop)
    (isMittagLeffler_isoTower_constantAdicQuotientTower J Λ I M hMfin hMcompl)

/-- **A sheaf with constant adic reductions is a completed constant sheaf**, on any site with a
terminal object whose topos is not empty: if `F` is the limit of its reductions `F / IⁿF`, each of
them is constant and `F / IF` is the constant sheaf of a finite module, then `F` is the limit of
the constant sheaves `(M / IⁿM)̲` of an `I`-adically complete module `M` finite over `Λ^∧`. -/
theorem exists_iso_limit_constantAdicQuotientTower_of_isConstant
    (hne : ∃ U : C, (⊥ : Sieve U) ∉ J U)
    (F : Sheaf J (ModuleCat.{max u v w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{max u v w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy J Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hlim : IsLimit (Limits.Cone.mk F q))
    (hconst : ∀ n : ℕ, ∃ N : ModuleCat.{max u v w} Λ,
      Nonempty ((constantSheaf J
        (ModuleCat.{max u v w} Λ)).obj N ≅ Q.obj (op n)))
    (hfin : ∃ N : ModuleCat.{max u v w} Λ,
      Module.Finite Λ (N : Type (max u v w)) ∧
      Nonempty ((constantSheaf J
        (ModuleCat.{max u v w} Λ)).obj N ≅ Q.obj (op 1))) :
    ∃ M : ModuleCat.{max u v w} Λ,
      IsAdicComplete I (M : Type (max u v w)) ∧
      Module.Finite (AdicCompletion I Λ) (AdicCompletion I (M : Type (max u v w))) ∧
      Nonempty (F ≅ limit (constantAdicQuotientTower J Λ I M)) := by
  obtain ⟨M, hMcomplete, -, hMcompl, hMfin, hMiso⟩ :=
    exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant J Λ I hne F Q q hq hconst hfin
  obtain ⟨α⟩ := nonempty_natIso_constantAdicQuotientTower_of_isConstant J Λ I M F Q q hq
    hMfin hMcompl hMiso
  exact ⟨M, hMcomplete, hMcompl,
    ⟨(IsLimit.conePointsIsoOfNatIso (limit.isLimit (constantAdicQuotientTower J Λ I M))
      hlim α).symm⟩⟩

end Main

end Stacks.ModuleSheaf
