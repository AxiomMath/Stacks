module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection

/-!
# Trivializations pull back, and so do local equations

Let `q : T ⟶ Y` be a morphism of schemes and `L` a quasi-coherent `𝒪_Y`-module which is free of
rank one over an affine open `V` of `Y`, the trivialization being recorded as a `Γ(Y, V)`-linear
equivalence `u : Γ(L, V) ≃ₗ Γ(Y, V)`. If the preimage `q⁻¹V` is again affine, the sections of
`q^*L` over `q⁻¹V` are the base change of `Γ(L, V)` along `q.appLE V (q⁻¹V)`, by
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, so base-changing `u` trivializes `q^*L`
over `q⁻¹V`.

The point of this file is not the existence of such a trivialization — which is
`Stacks.Modules.nonempty_linearEquiv_sections_pullback` — but that the trivialization can be
chosen so that its *framing section* is the pullback of the framing section of `u`. A
trivialization is determined by its framing section, so this pins the pulled-back trivialization
down and makes every local-equation identity for it computable; the identity the consumers want,
`Stacks.Divisors.pullbackTrivialization_resTop`, says that **the local equation of the pullback
of a global section is the pullback of its local equation.**

## Main definitions

* `Stacks.Divisors.pullbackTrivializationIso` — the base change of `u` along
  `q.appLE V (q⁻¹V)`, as an isomorphism of `Γ(T, q⁻¹V)`-modules
  `Γ(q^*L, q⁻¹V) ≅ Γ(T, q⁻¹V)`.
* `Stacks.Divisors.pullbackTrivialization` — the same, as a `Γ(T, q⁻¹V)`-linear equivalence.

## Main results

* `AlgebraicGeometry.pullbackSectionHom_resTop` — pulling a global section back and restricting
  to `q⁻¹V` is restricting it to `V` and pulling that back.
* `Stacks.Divisors.pullbackTrivialization_symm_one` — **the framing section of the pulled-back
  trivialization is the pullback of the framing section**: the section of `q^*L` over `q⁻¹V`
  representing `1` is the pullback of the section of `L` over `V` representing `1`.
* `Stacks.Divisors.pullbackTrivialization_pullbackSectionHom` — the pulled-back trivialization
  reads the pullback of a section of `L` over `V` as the pullback of the function `u` reads it
  as.
* `Stacks.Divisors.pullbackTrivialization_resTop` — **the local equation of a pulled-back global
  section is the pullback of its local equation.**
* `Stacks.Divisors.exists_pullbackTrivialization` — the existential packaging of
  `pullbackTrivialization_symm_one`, for consumers that only need a trivialization whose framing
  section is known.

## Implementation notes

The framing identity is proved at the base-change comparison, where the only thing that has to
be known about it is its normalisation
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`: the comparison sends `1 ⊗ a` to
the pullback of the section `a`. The framing section of the base change of `u` is the image of
`1 ⊗ u⁻¹(1)`, so the normalisation computes it with no further input.

The two subsequent statements are then formal consequences and use nothing about the pullback
beyond semilinearity of `AlgebraicGeometry.pullbackSectionHom` over
`AlgebraicGeometry.Scheme.Hom.appLE` and its compatibility with restriction on the target,
`AlgebraicGeometry.pullbackSectionHom_map`: a trivialization is determined by its framing
section, because `x = u⁻¹(1) · r` forces `u(x) = r`.

Everything here is phrased with `AlgebraicGeometry.pullbackSectionHom` rather than
`AlgebraicGeometry.Scheme.Modules.pullbackSection`, so that the sections carry the module
structures the notation `Γ(-, -)` attaches to them; the two agree by
`AlgebraicGeometry.pullbackSectionHom_apply`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

/-- **Pulling a global section back and restricting it is restricting it and pulling that
back.** The left-hand side is the pullback along `q` of the restriction of `s` to an open `V` of
the target; the right-hand side is the restriction to `q⁻¹V` of the pullback of `s` as a global
section. -/
theorem pullbackSectionHom_resTop {T Y : Scheme.{u}} (q : T ⟶ Y) (L : Y.Modules) (V : Y.Opens)
    (s : Γ(L, ⊤)) :
    pullbackSectionHom q L V (q ⁻¹ᵁ V) le_rfl (L.presheaf.map (homOfLE le_top).op s) =
      ((Scheme.Modules.pullback q).obj L).presheaf.map (homOfLE le_top).op
        (pullbackGlobalSections q L s) := by
  have hpre : (q ⁻¹ᵁ V) ≤ q ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  refine Eq.trans (pullbackSectionHom_map q L ⊤ V le_top (q ⁻¹ᵁ V) le_rfl hpre s) ?_
  have hcomp : ((Scheme.Modules.pullback q).obj L).presheaf.map (eqToHom (by simp)).op ≫
      ((Scheme.Modules.pullback q).obj L).presheaf.map
        (homOfLE (le_top : q ⁻¹ᵁ V ≤ ⊤)).op =
      ((Scheme.Modules.pullback q).obj L).presheaf.map (homOfLE hpre).op := by
    rw [← Functor.map_comp, ← op_comp]
    congr 1
  calc pullbackSectionHom q L ⊤ (q ⁻¹ᵁ V) hpre s
      = ((Scheme.Modules.pullback q).obj L).presheaf.map (homOfLE hpre).op
          (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app L).app ⊤ s) :=
        CategoryTheory.comp_apply _ _ s
    _ = (((Scheme.Modules.pullback q).obj L).presheaf.map (eqToHom (by simp)).op ≫
          ((Scheme.Modules.pullback q).obj L).presheaf.map
            (homOfLE (le_top : q ⁻¹ᵁ V ≤ ⊤)).op)
          (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app L).app ⊤ s) := by
        rw [hcomp]
    _ = ((Scheme.Modules.pullback q).obj L).presheaf.map (homOfLE le_top).op
          (pullbackGlobalSections q L s) :=
        (CategoryTheory.comp_apply _ _ _).trans
          (congrArg _ (CategoryTheory.comp_apply _ _ s).symm)

end AlgebraicGeometry

namespace Stacks.Divisors

variable {T Y : Scheme.{u}} (q : T ⟶ Y) (L : Y.Modules) [L.IsQuasicoherent]
  {V : Y.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen (q ⁻¹ᵁ V))
  (u : Γ(L, V) ≃ₗ[Γ(Y, V)] Γ(Y, V))

/-- **The base change of a rank-one trivialization along `q`.** For `V` and `q⁻¹V` affine and `L`
quasi-coherent, `Γ(q^*L, q⁻¹V)` is `Γ(T, q⁻¹V) ⊗_{Γ(Y, V)} Γ(L, V)`; base-changing `u` and
contracting `Γ(T, q⁻¹V) ⊗_{Γ(Y, V)} Γ(Y, V)` to `Γ(T, q⁻¹V)` trivializes `q^*L` over `q⁻¹V`. -/
def pullbackTrivializationIso :
    ModuleCat.of Γ(T, q ⁻¹ᵁ V) Γ((Scheme.Modules.pullback q).obj L, q ⁻¹ᵁ V) ≅
      ModuleCat.of Γ(T, q ⁻¹ᵁ V) Γ(T, q ⁻¹ᵁ V) :=
  (affinePullbackSectionsBaseChangeIso q L hV hW le_rfl).symm ≪≫
    (ModuleCat.extendScalars (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom).mapIso u.toModuleIso ≪≫
      ModuleCat.ExtendScalars.objSelfIso (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom

/-- `Stacks.Divisors.pullbackTrivializationIso` as a `Γ(T, q⁻¹V)`-linear equivalence. -/
def pullbackTrivialization :
    Γ((Scheme.Modules.pullback q).obj L, q ⁻¹ᵁ V) ≃ₗ[Γ(T, q ⁻¹ᵁ V)] Γ(T, q ⁻¹ᵁ V) :=
  (pullbackTrivializationIso q L hV hW u).toLinearEquiv

/-- The framing section of `Stacks.Divisors.pullbackTrivializationIso`: the inverse isomorphism
takes the constant function `1` to the pullback of the section of `L` over `V` that `u` reads as
the constant function `1`. -/
theorem pullbackTrivializationIso_inv_one :
    (pullbackTrivializationIso q L hV hW u).inv (1 : Γ(T, q ⁻¹ᵁ V)) =
      pullbackSectionHom q L V (q ⁻¹ᵁ V) le_rfl (u.symm 1) := by
  simp only [pullbackTrivializationIso, Iso.trans_inv, Iso.symm_inv, CategoryTheory.comp_apply]
  refine Eq.trans ?_ ((affinePullbackSectionsBaseChangeIso_one_tmul q L hV hW le_rfl
    (u.symm 1)).trans (pullbackSectionHom_apply q L V (q ⁻¹ᵁ V) le_rfl (u.symm 1)).symm)
  congr 1

/-- **The framing section of the pulled-back trivialization is the pullback of the framing
section.** The section of `q^*L` over `q⁻¹V` that `Stacks.Divisors.pullbackTrivialization` reads
as the constant function `1` is the pullback of the section of `L` over `V` that `u` reads as
the constant function `1`. -/
theorem pullbackTrivialization_symm_one :
    (pullbackTrivialization q L hV hW u).symm 1 =
      pullbackSectionHom q L V (q ⁻¹ᵁ V) le_rfl (u.symm 1) :=
  pullbackTrivializationIso_inv_one q L hV hW u

/-- **The pulled-back trivialization reads a pulled-back section as the pullback of the function
`u` reads it as.** -/
theorem pullbackTrivialization_pullbackSectionHom (a : Γ(L, V)) :
    pullbackTrivialization q L hV hW u (pullbackSectionHom q L V (q ⁻¹ᵁ V) le_rfl a) =
      q.appLE V (q ⁻¹ᵁ V) le_rfl (u a) := by
  have ha : (u a) • u.symm (1 : Γ(Y, V)) = a :=
    calc (u a) • u.symm (1 : Γ(Y, V))
        = u.symm ((u a) • (1 : Γ(Y, V))) := (u.symm.map_smul _ _).symm
      _ = u.symm (u a) := by rw [smul_eq_mul, mul_one]
      _ = a := u.symm_apply_apply a
  calc pullbackTrivialization q L hV hW u (pullbackSectionHom q L V (q ⁻¹ᵁ V) le_rfl a)
      = pullbackTrivialization q L hV hW u
          (pullbackSectionHom q L V (q ⁻¹ᵁ V) le_rfl ((u a) • u.symm (1 : Γ(Y, V)))) := by
        rw [ha]
    _ = pullbackTrivialization q L hV hW u (q.appLE V (q ⁻¹ᵁ V) le_rfl (u a) •
          pullbackSectionHom q L V (q ⁻¹ᵁ V) le_rfl (u.symm (1 : Γ(Y, V)))) := by
        rw [pullbackSectionHom_smul]
    _ = q.appLE V (q ⁻¹ᵁ V) le_rfl (u a) := by
        rw [← pullbackTrivialization_symm_one q L hV hW u, map_smul,
          LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

/-- **The local equation of a pulled-back global section is the pullback of its local
equation.** On an affine open `V` with affine preimage, `u` reads the restriction of a global
section `s` of `L` as a function on `V`; the pulled-back trivialization reads the restriction of
the pullback of `s` as the pullback of that function. -/
theorem pullbackTrivialization_resTop (s : Γ(L, ⊤)) :
    pullbackTrivialization q L hV hW u
        (((Scheme.Modules.pullback q).obj L).presheaf.map (homOfLE le_top).op
          (pullbackGlobalSections q L s)) =
      q.appLE V (q ⁻¹ᵁ V) le_rfl (u (L.presheaf.map (homOfLE le_top).op s)) := by
  have h := pullbackTrivialization_pullbackSectionHom q L hV hW u
    (L.presheaf.map (homOfLE le_top).op s)
  rwa [pullbackSectionHom_resTop q L V s] at h

include hV hW in
/-- **A trivialization of `q^*L` over `q⁻¹V` whose framing section is the pullback of the framing
section of `u`.** This is the existential packaging of
`Stacks.Divisors.pullbackTrivialization_symm_one`. -/
theorem exists_pullbackTrivialization :
    ∃ e : Γ((Scheme.Modules.pullback q).obj L, q ⁻¹ᵁ V) ≃ₗ[Γ(T, q ⁻¹ᵁ V)] Γ(T, q ⁻¹ᵁ V),
      e.symm 1 = pullbackSectionHom q L V (q ⁻¹ᵁ V) le_rfl (u.symm 1) :=
  ⟨pullbackTrivialization q L hV hW u, pullbackTrivialization_symm_one q L hV hW u⟩

end Stacks.Divisors

end
