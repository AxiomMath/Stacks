module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Linear
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology sheaves of the derived internal Hom on an affine scheme

Let `A` be a commutative ring and let `K`, `L` be objects of `D(A)`. Part (4) of
[Stacks, Tag 0A6H] says that the `n`-th cohomology sheaf of `R𝓗om(K̃, L̃)` on `Spec A` is the sheaf
associated to the presheaf

`D(f) ↦ Ext^n_{A_f}(K ⊗_A A_f, L ⊗_A A_f)`

on the principal opens, whose restriction maps are derived base change along `A_f ⟶ A_g`.

Here `A_f` is the ring of sections `Γ(Spec A, D(f))`, which is the localization of `A` away from
`f`, and `K ⊗_A A_f` is the derived extension of scalars along the flat map `A ⟶ A_f`. The
restriction from `D(f)` to `D(g) ⊆ D(f)` is `AlgebraicGeometry.AffineExt.localizedExtRestrict`.

That a sheaf of `𝒪`-modules `F` is the sheaf associated to a presheaf of modules `P` on the basis
of principal opens means that there is a family of `𝒪(D(f))`-linear maps `P(D(f)) ⟶ F(D(f))`
commuting with restriction which is locally surjective and locally injective: every section of `F`
over `D(f)` is, near every point, the image of a section of `P`, and a section of `P` with zero
image restricts to zero near every point. Here `P(D(f)) = Ext^n_{A_f}(K ⊗_A A_f, L ⊗_A A_f)` is an
`A_f`-module, `A_f = 𝒪(D(f))`, and the maps are the canonical comparison maps
`AlgebraicGeometry.AffineExt.extToCohomologySheafLinear`.

## Main results

* `AlgebraicGeometry.AffineExt.cohomologySheaf_isSheafification_extPresheaf`: the `n`-th
  cohomology sheaf of `R𝓗om(K̃, L̃)` is the sheaf associated to the presheaf
  `D(f) ↦ Ext^n_{A_f}(K ⊗_A A_f, L ⊗_A A_f)`, through the canonical `A_f`-linear comparison maps.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AffineExt

/-- Let `A` be a commutative ring, let `K`, `L` be objects of `D(A)` and let `n` be an integer.
The `n`-th cohomology sheaf of `R𝓗om(K̃, L̃)` on `Spec A` is the sheaf of `𝒪_{Spec A}`-modules
associated to the presheaf `D(f) ↦ Ext^n_{A_f}(K ⊗_A A_f, L ⊗_A A_f)` on the principal opens of
`Spec A`: the canonical maps `Ext^n_{A_f}(K ⊗_A A_f, L ⊗_A A_f) ⟶ Γ(D(f), Hⁿ(R𝓗om(K̃, L̃)))`,
one for every `f : A`, which are `A_f`-linear
(`AlgebraicGeometry.AffineExt.extToCohomologySheafLinear`),
* commute with restriction, the restriction of `Ext` classes from `D(f)` to `D(g) ⊆ D(f)` being
  derived base change along `A_f ⟶ A_g`;
* are locally surjective: every section of `Hⁿ(R𝓗om(K̃, L̃))` over `D(f)` is, around every point of
  `D(f)`, the restriction of the image of an `Ext` class over a smaller principal open;
* are locally injective: an `Ext` class over `D(f)` with zero image restricts to zero over a
  principal open around every point of `D(f)`.

Here `A_f = Γ(Spec A, D(f))` is the localization of `A` away from `f`, which is also the ring of
sections of `𝒪_{Spec A}` over `D(f)`. The objects `K` and `L` are arbitrary. -/
@[stacks 0A6H "(4) the n-th cohomology sheaf of RHom(K~, L~) on Spec A is the sheaf of modules \
associated to the presheaf D(f) ↦ Ext^n_{A_f}(K ⊗ A_f, L ⊗ A_f), through the canonical A_f-linear \
comparison maps"]
theorem cohomologySheaf_isSheafification_extPresheaf (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (∀ (f g : R) (h : basicOpen R g ≤ basicOpen R f) (α : localizedExt R K L f n),
        (cohomologySheaf R K L n).presheaf.map (homOfLE h).op
            (extToCohomologySheafLinear R K L n f α) =
          extToCohomologySheafLinear R K L n g (localizedExtRestrict R K L h n α)) ∧
      (∀ (f : R) (s : Γ(cohomologySheaf R K L n, basicOpen R f)) (x : Spec R),
        x ∈ basicOpen R f → ∃ (g : R) (h : basicOpen R g ≤ basicOpen R f),
          x ∈ basicOpen R g ∧ ∃ α, extToCohomologySheafLinear R K L n g α =
            (cohomologySheaf R K L n).presheaf.map (homOfLE h).op s) ∧
      (∀ (f : R) (α : localizedExt R K L f n), extToCohomologySheafLinear R K L n f α = 0 →
        ∀ x : Spec R, x ∈ basicOpen R f → ∃ (g : R) (h : basicOpen R g ≤ basicOpen R f),
          x ∈ basicOpen R g ∧ localizedExtRestrict R K L h n α = 0) :=
  ⟨fun _ _ h α => extToCohomologySheaf_restrict R K L n h α,
    extToCohomologySheaf_locally_surjective R K L n,
    extToCohomologySheaf_locally_injective R K L n⟩

end AlgebraicGeometry.AffineExt

end
