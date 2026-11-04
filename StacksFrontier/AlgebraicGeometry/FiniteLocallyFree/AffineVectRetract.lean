module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.AffineVect
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeRetract

/-!
# A vector bundle on an affine scheme is a direct summand of a finite free one

On `Spec R` every finite locally free `𝒪_{Spec R}`-module is a **retract** of a finite free one.
This is the converse of the affine case of [Stacks, Tag 0BCI]
(`Stacks.AffineTilde.exists_finiteProjective_tilde_of_retract_free`), and the route is the same
correspondence read backwards: a finite locally free module on an affine scheme is `N^~` for
`N` its module of global sections, that module is finite projective by
`AlgebraicGeometry.isFiniteLocallyFree_tilde_functor_iff`, a finite projective module is a
retract of `R^n` by `Module.finite_projective_tfae`, and `M ↦ M^~` carries that retract across
and carries `R^n` to the free sheaf by `AlgebraicGeometry.tildeFinsupp`.

Its purpose is to make a statement proved only for *free* modules apply to all of them: fullness
of a functor passes to retracts (`CategoryTheory.Functor.full_of_retract`), so a criterion
established at free sheaves of modules needs no Zariski gluing to reach the general finite
locally free case over an affine base.

## Main definitions

* `AlgebraicGeometry.tildeFinFreeIso`: `(R^n)^~` is the free `𝒪_{Spec R}`-module on
  `ULift (Fin n)`.

## Main results

* `AlgebraicGeometry.exists_retract_free_of_isFiniteLocallyFree`: **a finite locally free
  `𝒪_{Spec R}`-module is a retract of a finite free one.**
* `AlgebraicGeometry.Scheme.Vect.exists_retract_free`: the same, stated inside the category
  `Vect(Spec R)` of finite locally free modules, where the ambient free module is an object of
  that category.

## Implementation notes

The index type of the free sheaf must live in the same universe `u` as the ring, while `Fin n`
lives in `Type 0`, so the free sheaf is indexed by `ULift (Fin n)` and
`AlgebraicGeometry.tildeFinFreeIso` absorbs the reindexing together with the passage from the
function module `Fin n → R` to the finitely supported module `ULift (Fin n) →₀ R` that
`AlgebraicGeometry.tildeFinsupp` is stated for.

The retract inside `Vect(Spec R)` is obtained from the ambient one by
`CategoryTheory.Functor.FullyFaithful.retract` along the inclusion of the full subcategory, so no
morphism has to be rebuilt by hand.

## References

* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})

/-- **The sheaf associated to `R^n` is the free `𝒪_{Spec R}`-module on `ULift (Fin n)`.**

`AlgebraicGeometry.tildeFinsupp` identifies `(ι →₀ R)^~` with the free sheaf on `ι`; what this
adds is the linear equivalence `(Fin n → R) ≃ₗ (ULift (Fin n) →₀ R)`, which reindexes along
`Equiv.ulift` and crosses between functions and finitely supported functions on a finite type. -/
def tildeFinFreeIso (n : ℕ) :
    (tilde.functor R).obj (ModuleCat.of R (Fin n → R)) ≅
      _root_.SheafOfModules.free.{u} (ULift.{u} (Fin n)) :=
  (tilde.functor R).mapIso
      ((LinearEquiv.funCongrLeft R R (Equiv.ulift.{u, 0} (α := Fin n))).trans
        (Finsupp.linearEquivFunOnFinite R R (ULift.{u} (Fin n))).symm).toModuleIso ≪≫
    tildeFinsupp (R := R) (ULift.{u} (Fin n))

/-- **A finite locally free `𝒪_{Spec R}`-module is a retract of a finite free one.**

The module of global sections is finite projective, hence a retract of `R^n`, and `M ↦ M^~`
carries that retract to a retract of `(R^n)^~`, which is the free sheaf on `ULift (Fin n)` by
`AlgebraicGeometry.tildeFinFreeIso`. -/
theorem exists_retract_free_of_isFiniteLocallyFree (E : (Spec R).Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    ∃ n : ℕ, Nonempty (Retract E (_root_.SheafOfModules.free.{u} (ULift.{u} (Fin n)))) := by
  let _ := hE
  obtain ⟨N, ⟨e⟩⟩ : ∃ N : ModuleCat.{u} R, Nonempty ((tilde.functor R).obj N ≅ E) :=
    ⟨moduleSpecΓFunctor.obj E,
      ⟨Stacks.AlgebraicGeometry.AffineBaseChangeLocality.tildeΓIso E⟩⟩
  have hprop : finiteProjectiveProperty R N :=
    (isFiniteLocallyFree_tilde_functor_iff N).mp
      (SheafOfModules.IsFiniteLocallyFree.of_iso e.symm)
  have hFP : Module.Finite R N ∧ Module.Projective R N := ⟨hprop.1, hprop.2⟩
  obtain ⟨n, f, g, hfg⟩ := ((Module.finite_projective_tfae R N).out 2 3).mp hFP
  have hret : Retract N (ModuleCat.of R (Fin n → R)) :=
    { i := ModuleCat.ofHom g
      r := ModuleCat.ofHom f
      retract := by rw [← ModuleCat.ofHom_comp, hfg, ModuleCat.ofHom_id] }
  exact ⟨n, ⟨(Retract.ofIso e.symm).trans
      ((hret.map (tilde.functor R)).trans (Retract.ofIso (tildeFinFreeIso R n)))⟩⟩

namespace Scheme.Vect

/-- **A vector bundle on an affine scheme is a retract of a finite free one**, inside the
category `Vect(Spec R)`.

This is `AlgebraicGeometry.exists_retract_free_of_isFiniteLocallyFree` reflected along the
inclusion of the full subcategory of finite locally free modules, which is fully faithful; the
ambient free module belongs to that subcategory because a free module on a finite index type is
finite locally free. -/
theorem exists_retract_free (E : (Spec R).Vect) :
    ∃ (n : ℕ) (hfree : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (_root_.SheafOfModules.free.{u} (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)))),
      Nonempty (Retract E ⟨_root_.SheafOfModules.free.{u} (ULift.{u} (Fin n)), hfree⟩) := by
  obtain ⟨n, ⟨hret⟩⟩ := exists_retract_free_of_isFiniteLocallyFree R E.obj E.property
  have hfree : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free.{u} (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n))) :=
    ⟨AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData
      (M := _root_.SheafOfModules.free.{u} (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)))⟩
  exact ⟨n, hfree, ⟨(ObjectProperty.fullyFaithfulι _).retract hret⟩⟩

end Scheme.Vect

end AlgebraicGeometry

end
