module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.GenericStalk
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.Stalk
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.StalkSpecializes

/-!
# Meromorphic sections on an integral scheme are constant

Let `X` be an integral scheme with generic point `η` and let `F` be a quasi-coherent
`𝒪_X`-module. The sheaf `𝒦_X(F)` of meromorphic sections of `F` is the constant sheaf with value
the generic stalk `F_η`: over every open set containing `η` — that is, over every nonempty open
set — the germ map at `η` is bijective, every restriction map between nonempty opens is an
isomorphism, and the sections over such an open set are canonically the elements of `F_η`.

This is part (2) of Stacks 01X5, and the content of part (2) of Stacks 02OW in the integral
case. The proof runs through the stalks. At a point `x` the stalk of `𝒦_X(F)` is the
localization of `F_x` at the regular germs of `𝒪_X`
(`Stacks.Divisors.isLocalizedModule_toMeromorphicSectionStalk`), and on an integral scheme the
regular germs are exactly the nonzerodivisors of the local ring (Stacks 02OW (3)). The
specialization map `F_x → F_η` of a quasi-coherent module is itself a localization at those same
nonzerodivisors (`Stacks.Divisors.isLocalizedModule_toGenericStalkₗ`), and at the generic point
the nonzerodivisors are units, so `F_η → 𝒦_X(F)_η` is bijective. Uniqueness of localization then
makes the generization map `𝒦_X(F)_x → 𝒦_X(F)_η` bijective for every `x`, and a sheaf all of
whose generization maps are bijective is constant
(`Stacks.ConstantSheaf.bijective_germ_of_bijective_stalkSpecializes`).

## Main results

* `Stacks.Divisors.bijective_stalkSpecializes_meromorphicSectionSheaf` — the generization maps
  of `𝒦_X(F)` are bijective.
* `Stacks.Divisors.bijective_germ_meromorphicSectionSheaf` — the germ map at `η` is bijective
  over every open set containing `η`.
* `Stacks.Divisors.isIso_map_meromorphicSectionSheaf` — every restriction map of `𝒦_X(F)`
  between open sets containing `η` is an isomorphism.
* `Stacks.Divisors.FiniteComponentsOnCompactOpens` and
  `Stacks.Divisors.genericPointStalkModule` — the hypothesis and the summand that the displayed
  decompositions of Stacks 02OW are stated with.
* `Stacks.Divisors.meromorphicSectionsModule` and
  `Stacks.Divisors.isIso_map_meromorphicSectionsModule` — the same statement for the sheaf of
  meromorphic sections regarded as an `𝒪_X`-module.
* `Stacks.Divisors.meromorphicSectionsAddEquivGenericStalk` — the meromorphic sections of `F`
  over an open set containing `η` are canonically the elements of `F_η`. This is the bridge
  between the two models of a meromorphic section: a section of `𝒦_X(F)`, and an element of the
  generic stalk.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry Stacks.ModuleStalk

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- The generic point of an irreducible space specializes to every point. -/
theorem genericPointSpecializes [IrreducibleSpace X] (x : X) : genericPoint X ⤳ x :=
  (genericPoint_spec X).specializes trivial

/-- The generic point of an irreducible space lies in every nonempty open set. -/
theorem genericPoint_mem_of_nonempty_set [IrreducibleSpace X] (V : X.Opens)
    (h : (V : Set X).Nonempty) : genericPoint X ∈ V :=
  ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using h)

/-- On an integral scheme a nonzerodivisor of the function field is a unit, the function field
being a field. -/
theorem isUnit_of_mem_nonZeroDivisors_functionField [IsIntegral X] {s : X.functionField}
    (hs : s ∈ nonZeroDivisors X.functionField) : IsUnit s :=
  isUnit_iff_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hs)

/-- On an integral scheme a regular germ at the generic point is a unit of the function
field. -/
theorem regularGerms_genericPoint_le_isUnit [IsIntegral X]
    {s : ↑(X.sheaf.presheaf.stalk (genericPoint X))}
    (hs : s ∈ regularGerms X.sheaf (genericPoint X)) : IsUnit s :=
  isUnit_of_mem_nonZeroDivisors_functionField
    (regularGerms_le_nonZeroDivisors X.sheaf (genericPoint X) hs)

/-- **The generization maps of the sheaf of meromorphic sections are bijective.** On an integral
scheme the specialization map `𝒦_X(F)_x → 𝒦_X(F)_η` of the sheaf of meromorphic sections of a
quasi-coherent module is bijective at every point.

Both stalks are localizations of `F_x` at the nonzerodivisors of `𝒪_{X, x}`: the first by the
computation of the stalk of `𝒦_X(F)`, the second because `F_η` is such a localization and
`F_η → 𝒦_X(F)_η` is bijective, the regular germs at `η` being units. -/
theorem bijective_stalkSpecializes_meromorphicSectionSheaf [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] (x : X) :
    Function.Bijective (TopCat.Presheaf.stalkSpecializes
      (presheafOn (meromorphicSectionSheaf X.sheaf F).val) (genericPointSpecializes x)) := by
  have h : genericPoint X ⤳ x := genericPointSpecializes x
  let mFx : Module ↑(X.sheaf.presheaf.stalk x) ↑((presheafOn F.val).stalk x) :=
    moduleStalk F.val x
  let mFg : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
      ↑((presheafOn F.val).stalk (genericPoint X)) := moduleStalk F.val (genericPoint X)
  let mKx : Module ↑(X.sheaf.presheaf.stalk x)
      ↑((presheafOn (meromorphicSectionSheaf X.sheaf F).val).stalk x) :=
    moduleStalkMeromorphicSectionSheaf X.sheaf F x
  let mKg : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
      ↑((presheafOn (meromorphicSectionSheaf X.sheaf F).val).stalk (genericPoint X)) :=
    moduleStalkMeromorphicSectionSheaf X.sheaf F (genericPoint X)
  let mFη := specializedStalkModule (O := X.sheaf.presheaf) F.val h
  let mKη : Module ↑(X.sheaf.presheaf.stalk x)
      ↑((presheafOn (meromorphicSectionSheaf X.sheaf F).val).stalk (genericPoint X)) :=
    specializedStalkModule (O := X.sheaf.presheaf) (meromorphicSectionRestrict X.sheaf F) h
  have h1 := isLocalizedModule_toMeromorphicSectionStalk X.sheaf F x
  have hlocg := isLocalizedModule_toMeromorphicSectionStalk X.sheaf F (genericPoint X)
  have h2 : Function.Bijective (toMeromorphicSectionStalk X.sheaf F (genericPoint X)) :=
    Stacks.Localization.bijective_of_isLocalizedModule_of_isUnit
      (S := regularGerms X.sheaf (genericPoint X)) _
      fun _ hs => regularGerms_genericPoint_le_isUnit hs
  let fη : ↑((presheafOn F.val).stalk (genericPoint X)) →ₗ[X.sheaf.presheaf.stalk x]
      ↑((presheafOn (meromorphicSectionSheaf X.sheaf F).val).stalk (genericPoint X)) :=
    { toFun := toMeromorphicSectionStalk X.sheaf F (genericPoint X)
      map_add' := map_add _
      map_smul' := fun _ m =>
        (toMeromorphicSectionStalk X.sheaf F (genericPoint X)).map_smul _ m }
  let eη := LinearEquiv.ofBijective fη h2
  have h3 : IsLocalizedModule (regularGerms X.sheaf x)
      (stalkSpecializesₗ (O := X.sheaf.presheaf) F.val h) := by
    rw [regularGerms_eq_nonZeroDivisors_of_isIntegral X x]
    exact isLocalizedModule_toGenericStalkₗ F x
  have h4 : IsLocalizedModule (regularGerms X.sheaf x)
      (eη.toLinearMap ∘ₗ stalkSpecializesₗ (O := X.sheaf.presheaf) F.val h) :=
    IsLocalizedModule.of_linearEquiv _ _ eη
  let g : ↑((presheafOn (meromorphicSectionSheaf X.sheaf F).val).stalk x)
      →ₗ[X.sheaf.presheaf.stalk x]
      ↑((presheafOn (meromorphicSectionSheaf X.sheaf F).val).stalk (genericPoint X)) :=
    stalkSpecializesₗ (O := X.sheaf.presheaf) (meromorphicSectionRestrict X.sheaf F) h
  have h5 : g ∘ₗ toMeromorphicSectionStalk X.sheaf F x =
      eη.toLinearMap ∘ₗ stalkSpecializesₗ (O := X.sheaf.presheaf) F.val h :=
    LinearMap.ext fun a =>
      (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map_apply
        ((PresheafOfModules.toPresheaf _).map (toMeromorphicSectionSheaf X.sheaf F)) h a).symm
  have h6 : IsLocalizedModule (regularGerms X.sheaf x)
      (g ∘ₗ toMeromorphicSectionStalk X.sheaf F x) := by rwa [h5]
  show Function.Bijective g
  rw [← IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp
    (S := regularGerms X.sheaf x) (f := toMeromorphicSectionStalk X.sheaf F x) g]
  exact (IsLocalizedModule.linearEquiv (regularGerms X.sheaf x)
    (toMeromorphicSectionStalk X.sheaf F x) _).bijective

/-- **The content of Stacks 01X5 (2).** On an integral scheme the sheaf of meromorphic sections
of a quasi-coherent module is the constant sheaf on its generic stalk: the germ map at the
generic point is bijective over every open set containing it.

No declaration here carries the tag `01X5`: its covering set also contains part (1), the
identification of `𝒦_X` itself with the constant sheaf on the function field, which is not
proved here. -/
theorem bijective_germ_meromorphicSectionSheaf [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hηU : genericPoint X ∈ U) :
    Function.Bijective ((presheafOn (meromorphicSectionSheaf X.sheaf F).val).germ U
      (genericPoint X) hηU) :=
  Stacks.ConstantSheaf.bijective_germ_of_bijective_stalkSpecializes _
    (SheafOfModules.isSheaf _) (genericPoint_mem_of_nonempty_set (X := X)) genericPointSpecializes
    (bijective_stalkSpecializes_meromorphicSectionSheaf F) U hηU

/-- **The restriction maps of the sheaf of meromorphic sections are isomorphisms.** On an
integral scheme the restriction map of the sheaf of meromorphic sections of a quasi-coherent
module between two open sets containing the generic point — that is, between two nonempty open
sets — is an isomorphism. -/
theorem isIso_map_meromorphicSectionSheaf [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    {U V : X.Opens} (i : V ⟶ U) (hηV : genericPoint X ∈ V) :
    IsIso ((meromorphicSectionSheaf X.sheaf F).val.presheaf.map i.op) :=
  Stacks.ConstantSheaf.isIso_map_of_bijective_stalkSpecializes _ (SheafOfModules.isSheaf _)
    (genericPoint_mem_of_nonempty_set (X := X)) genericPointSpecializes
    (bijective_stalkSpecializes_meromorphicSectionSheaf F) i hηV

/-- **The two models of a meromorphic section agree.** On an integral scheme the meromorphic
sections of a quasi-coherent module `F` over an open set containing the generic point are
canonically the elements of the generic stalk `F_η`; the bijection sends a section to the germ of
its image at `η`, read through the identification `F_η = 𝒦_X(F)_η`.

Taking `U = ⊤` this identifies a global meromorphic section of `F` with an element of `F_η`,
which is the form in which the order of vanishing of a meromorphic section is defined. -/
def meromorphicSectionsAddEquivGenericStalk [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hηU : genericPoint X ∈ U) :
    ↑((meromorphicSectionSheaf X.sheaf F).val.obj (op U)) ≃+
      ↑((presheafOn F.val).stalk (genericPoint X)) :=
  let _mFg : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
      ↑((presheafOn F.val).stalk (genericPoint X)) := moduleStalk F.val (genericPoint X)
  let _mKg : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
      ↑((presheafOn (meromorphicSectionSheaf X.sheaf F).val).stalk (genericPoint X)) :=
    moduleStalkMeromorphicSectionSheaf X.sheaf F (genericPoint X)
  have _hlocg := isLocalizedModule_toMeromorphicSectionStalk X.sheaf F (genericPoint X)
  have h2 : Function.Bijective (toMeromorphicSectionStalk X.sheaf F (genericPoint X)) :=
    Stacks.Localization.bijective_of_isLocalizedModule_of_isUnit
      (S := regularGerms X.sheaf (genericPoint X)) _
      fun _ hs => regularGerms_genericPoint_le_isUnit hs
  (AddEquiv.ofBijective
      ((presheafOn (meromorphicSectionSheaf X.sheaf F).val).germ U (genericPoint X) hηU).hom
      (bijective_germ_meromorphicSectionSheaf F U hηU)).trans
    (AddEquiv.ofBijective
      (toMeromorphicSectionStalk X.sheaf F (genericPoint X)).toAddMonoidHom h2).symm

/-- The sheaf of meromorphic sections of `F`, regarded as a sheaf of `𝒪_X`-modules by
restriction of scalars along the canonical map `𝒪_X → 𝒦_X` to the sheaf of total quotient
rings. This is the form in which the displayed decompositions of Stacks 02OW (2) are stated. -/
abbrev meromorphicSectionsModule (X : Scheme.{u}) (F : X.Modules) : X.Modules :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat.{u})).map (toTotalQuotientSheaf X.sheaf))).obj
    (meromorphicSectionSheaf X.sheaf F)

/-- The finiteness hypothesis of Stacks 02OW: every quasi-compact open has finitely many
irreducible components. An integral scheme satisfies it, by
`Stacks.Divisors.finite_irreducibleComponents_opens`. -/
abbrev FiniteComponentsOnCompactOpens (X : Scheme.{u}) : Prop :=
  ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite

/-- The contribution of a module at a generic point: the pullback of `F` to the spectrum of the
local ring there, pushed forward to `X`. This is the summand `j_{η,*} F_η` of the decomposition
of Stacks 02OW (2). The structure-sheaf case, `j_{η,*} κ(η)`, is the corresponding summand of the
decomposition of `𝒦_X` itself. -/
abbrev genericPointStalkModule (X : Scheme.{u}) (F : X.Modules) (η : genericPoints X) :
    X.Modules :=
  (Scheme.Modules.pushforward (X.fromSpecStalk η.1)).obj
    ((Scheme.Modules.pullback (X.fromSpecStalk η.1)).obj F)

/-- `Stacks.Divisors.isIso_map_meromorphicSectionSheaf` restated for the sheaf of meromorphic
sections regarded as an `𝒪_X`-module: restriction of scalars does not change the underlying
presheaf of abelian groups, so the two statements are the same. -/
theorem isIso_map_meromorphicSectionsModule [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] {U V : X.Opens} (i : V ⟶ U) (hηV : genericPoint X ∈ V) :
    IsIso ((meromorphicSectionsModule X F).presheaf.map i.op) :=
  isIso_map_meromorphicSectionSheaf F i hηV

end Stacks.Divisors
