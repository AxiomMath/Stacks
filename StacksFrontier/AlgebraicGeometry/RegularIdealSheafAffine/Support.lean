module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Basic

/-!
# The support of the quotient avoids the opens on which the ideal sheaf is everything

Let `X` be a ringed space and `J ⊆ O_X` a sheaf of ideals.  If `J` has all of `O_X` as its
sections over every subopen of an open `W`, then no point of `W` lies in the support of
`O_X / J`.

The quotient morphism `O_X ⟶ O_X/J` is an epimorphism of sheaves of modules, hence locally
surjective, so a section of the quotient near a point of `W` is, on some smaller open, the image
of a section of `O_X`; and `J.ι ≫ cokernel.π J.ι = 0` makes that image vanish as soon as the
section of `O_X` lies in `J`, which over a subopen of `W` it does. So the section of the quotient
restricts to zero near the point and its germ vanishes.

## Main results

* `cokernelπ_app_eq_zero_of_mem`: the class in the quotient of a section of the ideal sheaf
  vanishes.
* `notMem_idealQuotientSupport`: a point of `W` is not in the support of the quotient.

## Implementation notes

Local surjectivity is `Stacks.SheafOfModules.EpiMono.exists_covering_of_epi`, which is stated
for an arbitrary site; on the site of opens of a space a covering sieve contains, through
`TopologicalSpace.Opens.mem_grothendieckTopology`, an open neighbourhood of each point of its
base, which is the only thing used.

The germ is computed through `TopCat.Presheaf.germ_res_apply` twice rather than by composing the
two restrictions: morphisms of `Opens X` compose to the unique morphism between their endpoints,
but the two spellings of that composite are not syntactically equal, so a composition step would
need a `Subsingleton.elim`, whereas restricting in two stages needs nothing.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheafAffine

variable (X : RingedSpace.{u}) (J : (structureSheafModule X).Submodule)

/-- The underlying presheaf of abelian groups of the quotient `O_X / J`, whose stalks define the
support of the quotient. -/
noncomputable abbrev quotientAbPresheaf : TopCat.Presheaf Ab X.carrier :=
  RingedSpace.ModuleSheaf.abPresheaf
    (⟨(idealQuotient X J).val, (idealQuotient X J).isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X)

/-- A point lies in the support of `O_X / J` if and only if the stalk of the quotient at that
point has a nonzero element. -/
theorem mem_idealQuotientSupport_iff (x : X) :
    x ∈ idealQuotientSupport X J ↔ ∃ a : (quotientAbPresheaf X J).stalk x, a ≠ 0 :=
  Iff.rfl

/-- The class in `O_X / J` of a section lying in `J` vanishes. -/
theorem cokernelπ_app_eq_zero_of_mem (V : Opens X)
    (s : (structureSheafModule X).val.obj (op V)) (hs : s ∈ J.obj (op V)) :
    (cokernel.π J.ι).val.app (op V) s = 0 := by
  have h : (J.ι ≫ cokernel.π J.ι).val.app (op V) ⟨s, hs⟩ = 0 := by
    rw [cokernel.condition]
    rfl
  exact h

/-- **Where the ideal sheaf is everything, the quotient has empty support.** If `J` has all
sections of `O_X` over every subopen of `W`, no point of `W` is in the support of `O_X / J`. -/
theorem notMem_idealQuotientSupport (W : Opens X)
    (hW : ∀ V : Opens X, V ≤ W → J.obj (op V) = ⊤) (x : X) (hx : x ∈ W) :
    x ∉ idealQuotientSupport X J := by
  rintro ⟨a, ha⟩
  refine ha ?_
  obtain ⟨W₀, hxW₀, σ, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ a
  obtain ⟨S, hS, hSmem⟩ :=
    Stacks.SheafOfModules.EpiMono.exists_covering_of_epi (cokernel.π J.ι) σ
  obtain ⟨V₁, g, hg, hxV₁⟩ := (Opens.mem_grothendieckTopology _).mp hS x hxW₀
  obtain ⟨t, ht⟩ := hSmem g hg
  have hle : V₁ ⊓ W ≤ V₁ := inf_le_left
  have hx₂ : x ∈ V₁ ⊓ W := ⟨hxV₁, hx⟩
  have ht' : (cokernel.π J.ι).val.app (op V₁) t = (quotientAbPresheaf X J).map g.op σ := ht
  have hzeroRes : (cokernel.π J.ι).val.app (op (V₁ ⊓ W))
      ((structureSheafModule X).val.map (homOfLE hle).op t) = 0 :=
    cokernelπ_app_eq_zero_of_mem X J (V₁ ⊓ W) _
      (by rw [hW _ inf_le_right]; exact Submodule.mem_top)
  have hzeroMap : (quotientAbPresheaf X J).map (homOfLE hle).op
      ((cokernel.π J.ι).val.app (op V₁) t) = 0 :=
    (PresheafOfModules.naturality_apply (cokernel.π J.ι).val (homOfLE hle).op t).symm.trans
      hzeroRes
  calc (quotientAbPresheaf X J).germ W₀ x hxW₀ σ
      = (quotientAbPresheaf X J).germ V₁ x hxV₁ ((quotientAbPresheaf X J).map g.op σ) :=
        (TopCat.Presheaf.germ_res_apply _ g x hxV₁ σ).symm
    _ = (quotientAbPresheaf X J).germ (V₁ ⊓ W) x hx₂
          ((quotientAbPresheaf X J).map (homOfLE hle).op
            ((quotientAbPresheaf X J).map g.op σ)) :=
        (TopCat.Presheaf.germ_res_apply _ (homOfLE hle) x hx₂ _).symm
    _ = 0 := by rw [← ht', hzeroMap, map_zero]

end Stacks.AlgebraicGeometry.RegularIdealSheafAffine

end
