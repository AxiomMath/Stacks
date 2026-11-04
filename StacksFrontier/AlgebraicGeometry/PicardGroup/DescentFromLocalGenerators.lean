module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.ChartDescent
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PullbackHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# Descending an invertible module trivial over the preimages of a cover

Let `f : X ⟶ Y` be a morphism of schemes and `ℒ` an invertible `𝒪_X`-module. Suppose that every
point of `Y` has an open neighbourhood `W` such that

* `f^♯ : Γ(Y, A) ⟶ Γ(X, f⁻¹A)` is bijective for every open `A ⊆ W`, that is `𝒪_W = f_*𝒪_{f⁻¹W}`;
* `ℒ` is trivial over `f⁻¹W`, witnessed by a generating section.

Then `ℒ ≅ f^*ℳ` for an invertible `𝒪_Y`-module `ℳ`. The transition units of `ℒ` between the
generators over two preimages are functions on `f⁻¹(W ∩ W')`, hence come from units on
`W ∩ W'`, and the cocycle they form downstairs descends `ℒ`. This is the assembly step by which
a module trivial on the fibres of a projective space bundle is pulled back from the base, once
it is known to be trivial over the preimages of a cover.

## Main results

* `Stacks.PicardGroup.injective_app_of_forall_bijective`: `f^♯` is injective over every open as
  soon as it is bijective over the opens below the members of a cover.
* `Stacks.PicardGroup.exists_pullbackPicardClass_eq_of_generators`: **the descent**, as an
  equality in `Pic(X)`.

## Implementation notes

The descent itself is
`Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_targetUnits`, which takes the
transition units on the target as data and derives their cocycle laws from injectivity of
`f^♯`. What is supplied here is that datum: the units downstairs are the preimages of the
transition units upstairs under the bijection `f^♯`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace Stacks.PicardGroup

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`f^♯` is injective over every open** when it is bijective over every open below the
members of an open cover: a function killed by `f^♯` vanishes on each member of the cover, by
naturality of `f^♯`, and so vanishes. -/
theorem injective_app_of_forall_bijective (W : Y → Y.Opens) (hW : ∀ y, y ∈ W y)
    (hbij : ∀ y (A : Y.Opens), A ≤ W y → Function.Bijective (f.app A).hom) (A : Y.Opens) :
    Function.Injective (f.app A).hom := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
  refine TopCat.Presheaf.section_ext Y.sheaf A c 0 fun y hy => ?_
  have hle : A ⊓ W y ≤ A := inf_le_left
  have hres : (f.app (A ⊓ W y)).hom (Y.presheaf.map (homOfLE hle).op c) = 0 := by
    have hnat := congrArg (fun q => (CommRingCat.Hom.hom q) c) (f.naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
    rw [hnat, hc, map_zero]
  have h0 : Y.presheaf.map (homOfLE hle).op c = 0 :=
    (injective_iff_map_eq_zero _).mp (hbij y _ inf_le_right).injective _ hres
  have hg := TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hle) y ⟨hy, hW y⟩ c
  rw [h0, map_zero] at hg
  exact hg.symm.trans (map_zero _).symm

/-- **An invertible module trivial over the preimages of a cover on which `f_*𝒪 = 𝒪` is pulled
back from the base.** If every point of `Y` has an open neighbourhood `W` over whose opens
`f^♯` is bijective and over whose preimage `ℒ` has a generating section, then `ℒ ≅ f^*ℳ` for an
invertible `𝒪_Y`-module `ℳ`. -/
theorem exists_pullbackPicardClass_eq_of_generators (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hloc : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧
      (∀ A : Y.Opens, A ≤ W → Function.Bijective (f.app A).hom) ∧
      Nonempty (GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W))) :
    ∃ (M : Y.Modules) (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M),
      pullbackPicardClass f M hM = X.picardClass L hL := by
  choose W hyW hbij hgen using hloc
  let gen : ∀ y, GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W y) := fun y => (hgen y).some
  have hu : ∀ (i j : Y) (A : Y.Opens) (hi : A ≤ W i) (hj : A ≤ W j),
      ∃ w : (Γ(Y, A))ˣ, Stacks.PicFinite.pull f A w.val =
        generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
          (Stacks.InvertiblePullback.chartGen gen j hj)
          (Stacks.InvertiblePullback.chartGen gen i hi) := by
    intro i j A hi hj
    let e := RingEquiv.ofBijective (Stacks.PicFinite.pull f A) (hbij i A hi)
    have hr := isUnit_of_smul_eq_generator (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
      (Stacks.InvertiblePullback.chartGen gen j hj)
      (Stacks.InvertiblePullback.chartGen gen i hi) _
      (generatorRatio_spec (X := X.toRingedSpace) L _ _ _)
    refine ⟨(hr.map e.symm).unit, ?_⟩
    rw [IsUnit.unit_spec]
    exact e.apply_symm_apply _
  obtain ⟨N, hN, ⟨e⟩⟩ :=
    Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_targetUnits gen
      (injective_app_of_forall_bijective f W hyW hbij) hyW hu
  have hN' : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf N :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry Y.presheaf _ N).mpr hN
  refine ⟨N, hN', ?_⟩
  rw [pullbackPicardClass_eq_picardClass f N hN'
    (Stacks.RingedSpace.modulePullback_isInvertible _ N)]
  exact (X.picardClass_eq_iff _ L _ hL).mpr ⟨e⟩

end Stacks.PicardGroup

end
