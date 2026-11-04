module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.RightDerivedSheafValues

/-!
# A right derived functor into fppf modules is parasitic when its sections at flat objects vanish

Let `𝒴` be an algebraic stack and let `π : 𝒜 ⥤ Mod(𝒪_𝒴)` be an additive functor into the fppf
modules of `𝒴` at module universe `u + 1`, from an abelian category with injective resolutions.
For `M` in `𝒜` and `q ≥ 0`, the module `Rᵠπ(M)` is parasitic (**Stacks 0773**) as soon as, for
every flat object `y` of `𝒴`, the right derived functor `Rᵠ(Γ(y, π(-)))` of the sections over `y`
of `π` vanishes at `M`.

This is how the source reduces part (2) of **Stacks 0775** to part (1): `Rᵠπ(M)` is the
sheafification of the presheaf `y ↦ Rᵠ(Γ(y, π(-)))(M)`
(`Stacks.SheafOfModules.rightDerivedIsoSheafificationForget` and
`Stacks.SheafOfModules.rightDerivedForgetObjObjIso`), that presheaf is parasitic by hypothesis,
and the sheafification of a parasitic presheaf is parasitic, which is part (2)(a) of
**Stacks 0774** (`AlgebraicGeometry.Stack.isParasitic_sheafification`).

## Main results

* `AlgebraicGeometry.Stack.isParasitic_rightDerived_of_isZero_sections`: the criterion.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒴 : AlgebraicStacks.{u, w} B S hS)
  {A : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
  (π : A ⥤ fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴) [π.Additive]

/-- **A right derived functor into fppf modules is parasitic when its sections at the flat objects
vanish.** If for every flat object `y` of `𝒴` the right derived functor of `Γ(y, π(-))` vanishes
at `M` in degree `q`, then `Rᵠπ(M)` is parasitic. -/
theorem isParasitic_rightDerived_of_isZero_sections (M : A) (q : ℕ)
    (h : ∀ y : 𝒴.val.val.obj, flatObject B S hS 𝒴.val y →
      IsZero (((π ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op y)).rightDerived q).obj M)) :
    IsParasitic B S hS 𝒴 .fppf ((π.rightDerived q).obj M).val := by
  let R := FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf
  let Pq := ((π ⋙ SheafOfModules.forget R).rightDerived q).obj M
  have hP : IsParasitic B S hS 𝒴 .fppf Pq := fun y hy =>
    ModuleCat.isZero_iff_subsingleton.1
      (((Stacks.SheafOfModules.rightDerivedForgetObjObjIso R π q M y).isZero_iff).2 (h y hy))
  exact fun y hy => ModuleCat.isZero_iff_subsingleton.1
    (((SheafOfModules.evaluation R (op y)).mapIso
      ((Stacks.SheafOfModules.rightDerivedIsoSheafificationForget R π q).app M)).isZero_iff.2
      (ModuleCat.isZero_iff_subsingleton.2
        (isParasitic_sheafification.{u, w, u + 1} B S hS 𝒴 .fppf Pq hP y hy)))

end AlgebraicGeometry.Stack

end
