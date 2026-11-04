module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSections

/-!
# Sections of a constant sheaf of modules over an irreducible object of the small étale site

`AlgebraicGeometry.SmallEtale.constantModuleSheafSectionsIsoFinal` identifies a module `M` with
the sections of the constant sheaf it generates over the *final* object of the small étale site
of an irreducible scheme. The same holds over any object `U` of that site whose underlying
scheme is irreducible, and that is what this file proves.

The passage from the final object to an arbitrary one is the slice site. Sections over `U` of a
sheaf on the small étale site of `Y` are the sections over the terminal object of the localized
site at `U`, and the constant sheaf is compatible with that localization:
`Stacks.ConstantSheaf.overPullbackConstantSheafIso` identifies the constant sheaf on the
localized site with the restriction of the constant sheaf, compatibly with the canonical map out
of `M`. So the site-level statement
`Stacks.ConstantSheaf.bijective_toSheafify_const_app_of_forall_exists_refinement` applies to the
localized site at `U` and its terminal object, and its two hypotheses hold there: the terminal
object is not sheaf theoretically empty because `U` has a point, and two objects over `U` which
are not sheaf theoretically empty are refined by their fibre product over `U`, which is not
either because the two images are nonempty opens of the irreducible `U`.

## Main results

* `Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso_app` — the compatibility of
  `Stacks.ConstantSheaf.overPullbackConstantSheafIso` with the canonical map out of `M`, read at
  an arbitrary object of the slice site rather than only at the terminal one.
* `AlgebraicGeometry.SmallEtale.exists_refinement_over_not_bot_mem_of_irreducibleSpace` — two
  objects over an irreducible object of the small étale site which are not sheaf theoretically
  empty are refined, over it, by one which is not either.
* `AlgebraicGeometry.SmallEtale.bijective_toSheafify_const_app_of_irreducibleSpace` — **the
  constants are exactly the sections of the constant sheaf of modules over an irreducible object
  of the small étale site.**

## Implementation notes

The statement is about `CategoryTheory.toSheafify` applied to the constant presheaf rather than
about the unit of the constant sheaf adjunction, because the unit is only available at a final
object; at a general object the two notions part company and it is the sheafification map which
the arguments consuming this file use.

No `@[stacks]` attribute appears here: this is the local form of a statement about constant
sheaves, not a numbered result of the source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type*) [Category A] [HasWeakSheafify J A]

/-- The general-object form of `Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso`. -/
theorem toSheafify_overPullbackConstantSheafIso_app (X : C) [HasWeakSheafify (J.over X) A]
    [∀ (F : (Over X)ᵒᵖ ⥤ A), (Over.forget X).op.HasPointwiseRightKanExtension F] (M : A)
    (V : (Over X)ᵒᵖ) :
    (toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj M)).app V ≫
        ((overPullbackConstantSheafIso J A X).hom.app M).hom.app V =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op V.unop.left) :=
  congrArg (fun α => NatTrans.app α V)
    ((Over.forget X).toSheafify_pullbackSheafificationCompatibility A (J.over X) J
      ((Functor.const Cᵒᵖ).obj M))

end Stacks.ConstantSheaf

namespace AlgebraicGeometry.SmallEtale

open Stacks.ConstantSheaf

variable (B : BigEtaleSite.{u}) (Y : Scheme.{u}) (hY : B.Contains Y)

/-- On the small étale site, two objects over an irreducible object which are not sheaf
theoretically empty are refined, over that object, by one which is not either. -/
theorem exists_refinement_over_not_bot_mem_of_irreducibleSpace (U : SmallEtale B Y hY)
    [IrreducibleSpace ((SmallEtale.toScheme B Y hY).obj U)] (P Q : Over U)
    (hP : (⊥ : Sieve P) ∉ ((SmallEtale.topology B Y hY).over U) P)
    (hQ : (⊥ : Sieve Q) ∉ ((SmallEtale.topology B Y hY).over U) Q) :
    ∃ (R : Over U) (_ : R ⟶ P) (_ : R ⟶ Q),
      (⊥ : Sieve R) ∉ ((SmallEtale.topology B Y hY).over U) R := by
  rw [Stacks.EtaleCohomology.bot_mem_over_iff] at hP hQ
  obtain ⟨p⟩ := Stacks.EtaleCohomology.nonempty_of_not_bot_mem_smallEtaleTopology B Y hY hP
  obtain ⟨q⟩ := Stacks.EtaleCohomology.nonempty_of_not_bot_mem_smallEtaleTopology B Y hY hQ
  let F := SmallEtale.toScheme B Y hY
  have _ : Etale (F.map P.hom) := etale_toScheme_map B Y hY P.hom
  have _ : Etale (F.map Q.hom) := etale_toScheme_map B Y hY Q.hom
  obtain ⟨t, ht⟩ := nonempty_preirreducible_inter (F.map P.hom).isOpenMap.isOpen_range
    (F.map Q.hom).isOpenMap.isOpen_range
    ⟨(F.map P.hom).base p, p, rfl⟩ ⟨(F.map Q.hom).base q, q, rfl⟩
  have hne : Nonempty ↑(Limits.pullback (F.map P.hom) (F.map Q.hom)) := by
    rw [← not_isEmpty_iff, AlgebraicGeometry.Scheme.isEmpty_pullback_iff, Set.not_disjoint_iff]
    exact ⟨t, ht.1, ht.2⟩
  refine ⟨Over.mk (Limits.pullback.fst P.hom Q.hom ≫ P.hom),
    Over.homMk (Limits.pullback.fst P.hom Q.hom) rfl,
    Over.homMk (Limits.pullback.snd P.hom Q.hom) (Limits.pullback.condition).symm, ?_⟩
  rw [Stacks.EtaleCohomology.bot_mem_over_iff]
  exact Stacks.EtaleCohomology.not_bot_mem_smallEtaleTopology B Y hY
    ((Limits.PreservesPullback.iso F P.hom Q.hom).inv.base hne.some)

variable (Λ : Type (u + 1)) [CommRing Λ]
  [∀ V : SmallEtale B Y hY,
    HasWeakSheafify ((SmallEtale.topology B Y hY).over V) (ModuleCat.{u + 1} Λ)]

/-- **The constants are exactly the sections of the constant sheaf of modules over an
irreducible object of the small étale site.** -/
theorem bijective_toSheafify_const_app_of_irreducibleSpace (M : ModuleCat.{u + 1} Λ)
    (U : SmallEtale B Y hY) [IrreducibleSpace ((SmallEtale.toScheme B Y hY).obj U)] :
    Function.Bijective ((toSheafify (SmallEtale.topology B Y hY)
      ((Functor.const (SmallEtale B Y hY)ᵒᵖ).obj M)).app (op U)) := by
  have hbot : (⊥ : Sieve (Over.mk (𝟙 U))) ∉
      ((SmallEtale.topology B Y hY).over U) (Over.mk (𝟙 U)) := by
    rw [Stacks.EtaleCohomology.bot_mem_over_iff]
    exact Stacks.EtaleCohomology.not_bot_mem_smallEtaleTopology B Y hY
      (‹IrreducibleSpace ((SmallEtale.toScheme B Y hY).obj U)›.toNonempty.some)
  have hbij := bijective_toSheafify_const_app_of_forall_exists_refinement
    ((SmallEtale.topology B Y hY).over U) M (Over.mkIdTerminal (X := U)) hbot
    (exists_refinement_over_not_bot_mem_of_irreducibleSpace B Y hY U)
  have hcomp : (toSheafify ((SmallEtale.topology B Y hY).over U)
        ((Functor.const (Over U)ᵒᵖ).obj M)).app (op (Over.mk (𝟙 U))) ≫
        ((overPullbackConstantSheafIso (SmallEtale.topology B Y hY)
          (ModuleCat.{u + 1} Λ) U).hom.app M).hom.app (op (Over.mk (𝟙 U))) =
      (toSheafify (SmallEtale.topology B Y hY)
        ((Functor.const (SmallEtale B Y hY)ᵒᵖ).obj M)).app (op U) :=
    toSheafify_overPullbackConstantSheafIso_app
      (SmallEtale.topology B Y hY) (ModuleCat.{u + 1} Λ) U M (op (Over.mk (𝟙 U)))
  have hbij2 := (ConcreteCategory.isIso_iff_bijective
    (((overPullbackConstantSheafIso (SmallEtale.topology B Y hY)
      (ModuleCat.{u + 1} Λ) U).hom.app M).hom.app (op (Over.mk (𝟙 U))))).1 inferInstance
  have hfun : ⇑(ConcreteCategory.hom ((toSheafify (SmallEtale.topology B Y hY)
        ((Functor.const (SmallEtale B Y hY)ᵒᵖ).obj M)).app (op U))) =
      (⇑(ConcreteCategory.hom (((overPullbackConstantSheafIso (SmallEtale.topology B Y hY)
          (ModuleCat.{u + 1} Λ) U).hom.app M).hom.app (op (Over.mk (𝟙 U)))))) ∘
        (⇑(ConcreteCategory.hom ((toSheafify ((SmallEtale.topology B Y hY).over U)
          ((Functor.const (Over U)ᵒᵖ).obj M)).app (op (Over.mk (𝟙 U)))))) := by
    rw [← hcomp]
    rfl
  rw [hfun]
  exact hbij2.comp hbij

end AlgebraicGeometry.SmallEtale

end
