module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSectionExistence
public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicSectionsConstant
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic

/-!
# A meromorphic section from an element of the generic stalk

Let `X` be an integral scheme and `F` a quasi-coherent sheaf of `𝒪_X`-modules. Stacks Tag 01X5
part (2) identifies the sheaf `𝒦_X(F)` of meromorphic sections of `F` with the constant sheaf on
the stalk `F_η` at the generic point. This file reads that isomorphism *backwards*: an element of
`F_η` determines a meromorphic section of `F`, and every meromorphic section arises from exactly
one element of `F_η`.

The first paragraph of Stacks Tag 0BD7 uses precisely this passage. It has a trivializing section
of `ℒ` on the generic fibre of a flat morphism, reads it — through
`AlgebraicGeometry.exists_addEquiv_stalk_pullback_fiberι_genericPoint` — as an element of the
stalk of `ℒ` at the generic point of `X`, and then says "hence we can think of `s` as a regular
meromorphic section of `ℒ`". That last step is what is supplied here.

## Main definitions

* `AlgebraicGeometry.meromorphicSectionOfGenericStalk`: the meromorphic section of `F`
  determined by an element of `F_η`.

## Main results

* `AlgebraicGeometry.meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk`: the
  comparison isomorphism of Tag 01X5 part (2) carries that meromorphic section to the constant
  section determined by the same element, which is the property characterizing it.
* `AlgebraicGeometry.meromorphicSectionOfGenericStalk_eq_of_hom_eq` and
  `AlgebraicGeometry.exists_unique_eq_meromorphicSectionOfGenericStalk`: the passage is a
  bijection — a meromorphic section whose comparison image is the constant section at `m` *is*
  the section built from `m`, and every meromorphic section is built from exactly one element of
  the generic stalk. So no meromorphic section of a quasi-coherent module on an integral scheme
  is missed by this construction.
* `AlgebraicGeometry.meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk_eval`:
  its value over an *arbitrary* open, not only over `⊤`.
* `AlgebraicGeometry.meromorphicSectionSheafIsoConstant_smul`: the generic value of a
  `𝒦_X`-multiple `a • σ`, for a scalar `a` that is itself constant.
* `AlgebraicGeometry.eq_toMeromorphicSectionSheafAsModule_iff_eq_germ`, and for the section
  built from `m` the specialisation
  `meromorphicSectionOfGenericStalk_eval_eq_toMeromorphicSectionSheafAsModule_iff`: on an open
  containing the generic point, that section is the image of a regular section `t` exactly when
  `m` is the germ of `t` at the generic point — an equation of sections of `𝒦_X(ℱ)` traded for
  one in a single stalk of `ℱ`.

## Implementation notes

A meromorphic section is an element of `PresheafOfModules.sections`, a compatible family over
*every* open, while the comparison isomorphism is read one open at a time. The two are
reconciled by `Stacks.SheafOfModules.sectionsOfTopOfRingSheaf`: the open `⊤` is terminal, so a
compatible family is the same thing as a single section over `⊤`
(`Stacks.SheafOfModules.sections_ext_of_eval_top`).

That construction existed only as `Stacks.SheafOfModules.sectionsOfTop`, for a module over the
structure sheaf of a ringed space, and it is needed here over the *sheaf of meromorphic
functions*. Generalising it in place does not work, and the reason is worth recording: turning
the ring sheaf into an implicit argument changes how it is inferred at a call site, and a `rw`
in `StacksFrontier/AlgebraicGeometry/NormAmple/Basic.lean` then failed because its pattern and its
target agreed on every printed token and differed in that argument. So the general construction is a
separate declaration and the specialised name is a wrapper over it — one proof, two signatures.

Applying the two halves of an isomorphism of sheaves of modules in succession is the identity on
sections over an open, but not by `simp`: the composite of the two `app`s is the `app` of the
composite by `rfl`, and it is that spelling in which `Iso.inv_hom_id` rewrites.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]

/-- The two halves of the comparison isomorphism of Stacks Tag 01X5 part (2) undo one another on
the constant-sheaf side, over any open. -/
theorem meromorphicSectionSheafIsoConstant_inv_hom_apply (U : X.Opens)
    (x : ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat.{u})).map
            (totalQuotientSheafIsoConstant X).val.hom)).obj
        (constantGenericStalkModuleSheaf X F)).val.obj (op U)) :
    (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op U)
      ((meromorphicSectionSheafIsoConstant X F).val.inv.val.app (op U) x) = x := by
  change (((meromorphicSectionSheafIsoConstant X F).val.inv ≫
    (meromorphicSectionSheafIsoConstant X F).val.hom).val.app (op U)) x = x
  rw [(meromorphicSectionSheafIsoConstant X F).val.inv_hom_id]
  rfl

/-- The two halves of the comparison isomorphism of Stacks Tag 01X5 part (2) undo one another on
the meromorphic-sections side, over any open. -/
theorem meromorphicSectionSheafIsoConstant_hom_inv_apply (U : X.Opens)
    (x : (meromorphicSectionSheaf X.sheaf F).val.obj (op U)) :
    (meromorphicSectionSheafIsoConstant X F).val.inv.val.app (op U)
      ((meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op U) x) = x := by
  change (((meromorphicSectionSheafIsoConstant X F).val.hom ≫
    (meromorphicSectionSheafIsoConstant X F).val.inv).val.app (op U)) x = x
  rw [(meromorphicSectionSheafIsoConstant X F).val.hom_inv_id]
  rfl

/-- The comparison isomorphism of Stacks Tag 01X5 part (2) is injective on sections over any
open. -/
private theorem meromorphicSectionSheafIsoConstant_hom_app_injective (U : X.Opens) :
    Function.Injective ((meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op U)) :=
  fun x y h => (meromorphicSectionSheafIsoConstant_hom_inv_apply X F U x).symm.trans
    ((congrArg _ h).trans (meromorphicSectionSheafIsoConstant_hom_inv_apply X F U y))

/-- **A meromorphic section of `F` from an element of the stalk of `F` at the generic point.**
The constant section of the generic-stalk sheaf with value `m`, carried back along the
isomorphism of Stacks Tag 01X5 part (2). -/
def meromorphicSectionOfGenericStalk (m : F.presheaf.stalk (genericPoint X)) :
    MeromorphicSection X.sheaf F :=
  PresheafOfModules.sectionsMap (meromorphicSectionSheafIsoConstant X F).val.inv.val
    (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf _ (constantGenericStalkModuleSection X F ⊤ m))

/-- The value of `AlgebraicGeometry.meromorphicSectionOfGenericStalk` over `⊤`, which by
terminality of `⊤` determines it. -/
theorem meromorphicSectionOfGenericStalk_eval_top (m : F.presheaf.stalk (genericPoint X)) :
    (meromorphicSectionOfGenericStalk X F m).eval (op ⊤) =
      (meromorphicSectionSheafIsoConstant X F).val.inv.val.app (op (⊤ : X.Opens))
        (constantGenericStalkModuleSection X F ⊤ m) :=
  congrArg _ (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top _ _)

/-- **The characterizing property of `AlgebraicGeometry.meromorphicSectionOfGenericStalk`**: the
comparison isomorphism of Stacks Tag 01X5 part (2) carries it to the constant section with the
same value. -/
theorem meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk
    (m : F.presheaf.stalk (genericPoint X)) :
    (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op (⊤ : X.Opens))
        ((meromorphicSectionOfGenericStalk X F m).eval (op ⊤)) =
      constantGenericStalkModuleSection X F ⊤ m := by
  rw [meromorphicSectionOfGenericStalk_eval_top]
  exact meromorphicSectionSheafIsoConstant_inv_hom_apply X F ⊤ _

/-- A meromorphic section whose image under the comparison isomorphism of Stacks Tag 01X5 part
(2) is the constant section with value `m` is the one built from `m`. -/
theorem meromorphicSectionOfGenericStalk_eq_of_hom_eq
    (m : F.presheaf.stalk (genericPoint X)) (s : MeromorphicSection X.sheaf F)
    (hs : (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op (⊤ : X.Opens))
      (s.eval (op ⊤)) = constantGenericStalkModuleSection X F ⊤ m) :
    s = meromorphicSectionOfGenericStalk X F m := by
  exact Stacks.SheafOfModules.sections_ext_of_eval_top _
    (meromorphicSectionSheafIsoConstant_hom_app_injective X F ⊤
      (hs.trans (meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk X F m).symm))

/-- **Every meromorphic section of a quasi-coherent module on an integral scheme comes from
exactly one element of the stalk at the generic point.** Stacks Tag 01X5 part (2) read as a
statement about sections rather than about sheaves. -/
theorem exists_unique_eq_meromorphicSectionOfGenericStalk (s : MeromorphicSection X.sheaf F) :
    ∃! m : F.presheaf.stalk (genericPoint X), s = meromorphicSectionOfGenericStalk X F m := by
  obtain ⟨m, hm, huniq⟩ := exists_unique_eq_constantGenericStalkModuleSection X F
    ((meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op (⊤ : X.Opens))
      (s.eval (op ⊤)))
  refine ⟨m, meromorphicSectionOfGenericStalk_eq_of_hom_eq X F m s hm,
    fun n hn => (huniq n ?_).symm⟩
  rw [hn]
  exact meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk X F n

/-- The section built from its value over `⊤` is the one built from the compatible family of
constant sections: the agreement predicted by the docstring of
`AlgebraicGeometry.meromorphicSectionOfConstantGenericStalk`. -/
theorem meromorphicSectionOfConstantGenericStalk_eq_meromorphicSectionOfGenericStalk
    (m : F.presheaf.stalk (genericPoint X)) :
    meromorphicSectionOfConstantGenericStalk X F m = meromorphicSectionOfGenericStalk X F m :=
  meromorphicSectionOfGenericStalk_eq_of_hom_eq X F m _
    (meromorphicSectionSheafIsoConstant_inv_hom_apply X F ⊤
      (constantGenericStalkModuleSection X F ⊤ m))

/-- **The value of `AlgebraicGeometry.meromorphicSectionOfGenericStalk` over an arbitrary
open.** `AlgebraicGeometry.meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk`
reads it over `⊤`, which determines the section but says nothing about one open of `X`; the
penultimate paragraph of [Stacks, Tag 0BD7] works on a neighbourhood of a point. -/
theorem meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk_eval (U : X.Opens)
    (m : F.presheaf.stalk (genericPoint X)) :
    (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op U)
        ((meromorphicSectionOfGenericStalk X F m).eval (op U)) =
      constantGenericStalkModuleSection X F U m := by
  rw [← meromorphicSectionOfConstantGenericStalk_eq_meromorphicSectionOfGenericStalk]
  exact meromorphicSectionSheafIsoConstant_inv_hom_apply X F U
    (constantGenericStalkModuleSection X F U m)

/-- **The generic value of a `𝒦_X`-multiple of a meromorphic section.** If the comparison
isomorphism of Stacks Tag 01X5 part (2) carries `σ` to the constant section of `v`, and the
scalar `a ∈ 𝒦_X(U)` is the constant section of `r ∈ K(X)` through part (1), then it carries
`a • σ` to the constant section of `r • v`. -/
theorem meromorphicSectionSheafIsoConstant_smul {U : X.Opens}
    (a : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).obj.obj (op U))
    (σ : (meromorphicSectionSheaf X.sheaf F).val.obj (op U))
    {v : F.presheaf.stalk (genericPoint X)} {r : X.functionField}
    (hr : (totalQuotientSheafIsoConstant X).val.hom.hom.app (op U) a =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U) r)
    (hσ : (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op U) σ =
      constantGenericStalkModuleSection X F U v) :
    (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op U) (a • σ) =
      constantGenericStalkModuleSection X F U (r • v) := by
  rw [map_smul (ConcreteCategory.hom
    ((meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op U))) a σ, hσ]
  exact (constantGenericStalkModuleSection_smul X F U r _ hr v).symm

/-- **A meromorphic section is the image of a given regular section exactly when their generic
values agree.** On an open containing the generic point the comparison isomorphism of Stacks Tag
01X5 part (2) and the constant-section map are both injective, and the comparison carries the
image of a regular section to the constant section of its germ at the generic point. -/
theorem eq_toMeromorphicSectionSheafAsModule_iff_eq_germ {U : X.Opens}
    (hU : genericPoint X ∈ U) (σ : (meromorphicSectionSheaf X.sheaf F).val.obj (op U))
    (t : F.val.obj (op U)) {v : F.presheaf.stalk (genericPoint X)}
    (hσ : (meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op U) σ =
      constantGenericStalkModuleSection X F U v) :
    σ = (toMeromorphicSectionSheafAsModule X F).val.app (op U) t ↔
      v = F.presheaf.germ U (genericPoint X) hU t := by
  have ht := (meromorphicSectionSheafIsoConstant X F).2 U t hU
  refine ⟨fun h => (constantGenericStalkModuleSection_bijective X F U hU).1
    (hσ.symm.trans ((congrArg
      ((meromorphicSectionSheafIsoConstant X F).val.hom.val.app (op U)) h).trans ht)),
    fun h => meromorphicSectionSheafIsoConstant_hom_app_injective X F U
      (hσ.trans ((congrArg (constantGenericStalkModuleSection X F U) h).trans ht.symm))⟩

/-- **The section built from `m` is a given regular section exactly when `m` is its germ.** The
criterion of `AlgebraicGeometry.eq_toMeromorphicSectionSheafAsModule_iff_eq_germ` for the
meromorphic section the first paragraph of [Stacks, Tag 0BD7] builds: no sheaf of meromorphic
sections occurs in the right-hand side, only the stalk of `ℱ` at the generic point. -/
theorem meromorphicSectionOfGenericStalk_eval_eq_toMeromorphicSectionSheafAsModule_iff
    {U : X.Opens} (hU : genericPoint X ∈ U) (m : F.presheaf.stalk (genericPoint X))
    (t : F.val.obj (op U)) :
    (meromorphicSectionOfGenericStalk X F m).eval (op U) =
        (toMeromorphicSectionSheafAsModule X F).val.app (op U) t ↔
      m = F.presheaf.germ U (genericPoint X) hU t :=
  eq_toMeromorphicSectionSheafAsModule_iff_eq_germ X F hU _ t
    (meromorphicSectionSheafIsoConstant_meromorphicSectionOfGenericStalk_eval X F U m)

/-- **The section of the first paragraph of [Stacks, Tag 0BD7] is regular.** The source's "hence
we can think of `s` as a regular meromorphic section of `ℒ`": a generator of the stalk at the
generic point — one by which multiplication is injective — gives a *regular* meromorphic
section. -/
theorem isRegularMeromorphicSection_meromorphicSectionOfGenericStalk
    {m : F.presheaf.stalk (genericPoint X)}
    (hm : Function.Injective fun r : X.presheaf.stalk (genericPoint X) => r • m) :
    IsRegularMeromorphicSection X.sheaf F (meromorphicSectionOfGenericStalk X F m) :=
  meromorphicSectionOfConstantGenericStalk_eq_meromorphicSectionOfGenericStalk X F m ▸
    isRegularMeromorphicSection_meromorphicSectionOfConstantGenericStalk X F hm

end AlgebraicGeometry

end
