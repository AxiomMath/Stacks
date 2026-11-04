module

public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealPowerTorsionComplex
public import StacksFrontier.RingTheory.Cech.PresentedCechDatum

/-!
# The injective resolution of the structure presheaf of pairs, and its torsion subcomplex

This file carries out the first and the third constructions of the proof of
[Stacks, Tag 099D] on the category of presented pairs: an injective resolution `𝒪 → 𝒥•` of the
structure presheaf of modules, and the `ℐ`-power-torsion subcomplex `ℱ• = ⋃ₙ 𝒥•[ℐⁿ]` of a
complex of pair-modules.

What the source does with `ℱ•` — recognize `ℱ•(U)` as a representative of `RΓ_{V(I)}(A)` in
`D(A)` — is **not** done here, and cannot be done by the source's argument: it rests on the
claim that `𝒥•(U)` is a resolution of `A` by injective `A`-modules, which is false
(`Stacks.PairSite.exists_injective_not_injective_value`).

## Main results

* `Stacks.PairSite.exists_injectiveResolution_structureSingle` — **construction (1).** The
  structure presheaf, placed in degree zero, has an injective resolution by a complex of
  pair-modules vanishing in the negative degrees.

## Main definitions

* `Stacks.PairSite.torsionComplex` — **construction (3)**, the object `ℱ• = ⋃ₙ 𝒥•[ℐⁿ]`: the
  subcomplex of the `ℐ`-power-torsion sections of a complex of pair-modules, `ℐ ⊆ 𝒪` being the
  ideal subpresheaf `Stacks.PairSite.idealSubmodule`.
* `Stacks.PairSite.torsionComplexι` — its inclusion into the ambient complex, a monomorphism in
  each degree.

## Implementation notes

The torsion subcomplex is formed with the *presheaf* construction
`Stacks.IdealPowerTorsion.presheafTorsion` rather than with the sheaf one
`Stacks.IdealPowerTorsion.sheafTorsion`: on a site carrying the chaotic topology every
presheaf is a sheaf and the sheafification of a submodule is the submodule itself, so the
objectwise union is already the right object, and the presheaf form is the one whose sections
are computed by `Stacks.IdealPowerTorsion.mem_presheafTorsion_iff` with no covering sieve in
the way.

No `@[stacks 099D]` attribute is attached: these are two steps of the tag's *proof*, not parts
of its statement.

## References

* [The Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [The Stacks Project, Tag 013K](https://stacks.math.columbia.edu/tag/013K)
* [The Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.PairSite

/-! ### Construction (1): an injective resolution of the structure presheaf -/

/-- **An injective resolution `𝒪 → 𝒥•` of the structure presheaf of pairs**, by a complex of
pair-modules vanishing in the negative degrees. Presheaves of modules on pairs have enough
injectives (`Stacks.PairSite.enoughInjectives_pairModule`, [Stacks, Tag 01DV]), and `𝒪[0]` is
bounded below, so [Stacks, Tag 013K] applies. -/
theorem exists_injectiveResolution_structureSingle :
    ∃ R : CochainComplex.InjectiveResolution structureSingle.{u}, R.cocomplex.IsStrictlyGE 0 := by
  have := enoughInjectives_pairModule.{u}
  obtain ⟨R, -, hR⟩ :=
    CochainComplex.exists_injectiveResolution_isStrictlyGE 0 structureSingle.{u}
  exact ⟨R, hR⟩

/-! ### Construction (3): the ideal-power-torsion subcomplex -/

/-- The ring of sections of the structure presheaf at a pair is commutative. -/
instance isMulCommutative_structureRings (X : Pair.{u}ᵒᵖᵒᵖ) :
    IsMulCommutative (structureRings.{u}.obj X) :=
  inferInstanceAs (IsMulCommutative X.unop.unop.ring)

/-- **`ℱ• = ⋃ₙ 𝒥•[ℐⁿ]`**, the `ℐ`-power-torsion subcomplex of a complex of pair-modules: in
each degree the submodule of sections annihilated by some power of the ideal subpresheaf
`ℐ ⊆ 𝒪`, with the differentials restricted to it, which is possible because a morphism of
presheaves of modules carries power-torsion sections to power-torsion sections. -/
def torsionComplex (J : CochainComplex PairModule.{u} ℤ) : CochainComplex PairModule.{u} ℤ where
  X n := (IdealPowerTorsion.presheafTorsion idealSubmodule.{u} (J.X n)).toPresheafOfModules
  d n m := Stacks.PresheafOfModules.Submodule.restrictHom (J.d n m)
    (fun _ _ hs => IdealPowerTorsion.map_mem_presheafTorsion idealSubmodule.{u} (J.d n m) hs)
  shape n m h := by
    rw [← cancel_mono (IdealPowerTorsion.presheafTorsion idealSubmodule.{u} (J.X m)).ι,
      Stacks.PresheafOfModules.Submodule.restrictHom_comp_ι, J.shape n m h, comp_zero,
      zero_comp]
  d_comp_d' n m k _ _ := by
    rw [← cancel_mono (IdealPowerTorsion.presheafTorsion idealSubmodule.{u} (J.X k)).ι,
      Category.assoc, Stacks.PresheafOfModules.Submodule.restrictHom_comp_ι, ← Category.assoc,
      Stacks.PresheafOfModules.Submodule.restrictHom_comp_ι, Category.assoc, J.d_comp_d,
      comp_zero, zero_comp]

/-- The degree-`n` term of `torsionComplex J` is the power-torsion submodule of `J.X n`. -/
@[simp]
theorem torsionComplex_X (J : CochainComplex PairModule.{u} ℤ) (n : ℤ) :
    (torsionComplex J).X n =
      (IdealPowerTorsion.presheafTorsion idealSubmodule.{u} (J.X n)).toPresheafOfModules :=
  rfl

/-- **The inclusion `ℱ• ⟶ 𝒥•` of the power-torsion subcomplex.** -/
def torsionComplexι (J : CochainComplex PairModule.{u} ℤ) : torsionComplex J ⟶ J where
  f n := (IdealPowerTorsion.presheafTorsion idealSubmodule.{u} (J.X n)).ι
  comm' n m _ := (Stacks.PresheafOfModules.Submodule.restrictHom_comp_ι (J.d n m) _).symm

/-- In degree `n`, `torsionComplexι J` is the inclusion of the power-torsion submodule of
`J.X n`. -/
@[simp]
theorem torsionComplexι_f (J : CochainComplex PairModule.{u} ℤ) (n : ℤ) :
    (torsionComplexι J).f n = (IdealPowerTorsion.presheafTorsion idealSubmodule.{u} (J.X n)).ι :=
  rfl

/-- The inclusion `torsionComplexι J` of the power-torsion subcomplex is a monomorphism. -/
instance mono_torsionComplexι (J : CochainComplex PairModule.{u} ℤ) :
    Mono (torsionComplexι J) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    inferInstanceAs (Mono (IdealPowerTorsion.presheafTorsion idealSubmodule.{u} (J.X n)).ι)

/-- A section of `ℱ•` at a pair is a section of `𝒥•` annihilated by a power of the pair's
ideal. -/
theorem mem_torsionComplex_X_iff (J : CochainComplex PairModule.{u} ℤ) (n : ℤ) (P : Pair.{u})
    (s : (J.X n).value P) :
    s ∈ (IdealPowerTorsion.presheafTorsion idealSubmodule.{u} (J.X n)).obj P.ix ↔
      ∃ k, s ∈ (IdealPowerTorsion.presheafAnn idealSubmodule.{u} (J.X n) k).obj P.ix :=
  IdealPowerTorsion.mem_presheafTorsion_iff _ _

end Stacks.PairSite

end
