module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk

/-!
# Finiteness of the cohomology of a proper morphism over a Noetherian ring, and Tag 0897 part (1)

`Stacks.AlgebraicGeometry.GradedProperCohomology.Tag02O6` is the proposition that for a
Noetherian ring `R`, a proper morphism `g : Y ⟶ Spec R` and a coherent `𝒪_Y`-module `G`, the
cohomology `Hⁱ(Y, G)` is a finite `R`-module in every degree. It is stated over a ring rather
than over an affine scheme because that is the shape in which [Stacks, Tag 0897] part (1) uses
it.

This module proves it, so that it need not be assumed by anything downstream.
[Stacks, Tag 02O6] itself is already proved, over an affine locally Noetherian base, as
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`; what is done here is the
transport of scalars from `Γ(Spec R, ⊤)` to `R` along `Stacks.Scheme.ΓSpecIso`.

**[Stacks, Tag 0897] part (1) is therefore stated here rather than in
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic`**: it is the one implication of that
tag whose cohomological input is [Stacks, Tag 02O6], and here that input is a theorem, so the
statement carries no `Tag02O6` hypothesis. Its remaining arguments are the base change
`X' = Spec(B) ×_{Spec(A)} X` of the source's own proof, supplied by the caller. The tag
itself, with that base change constructed, is
`moduleFinite_gradedCohomologySum_and_exists_isZero_pieceTwistCohomology` in
`StacksFrontier.AlgebraicGeometry.GradedProperCohomology.FiniteGradedCohomology`; the vocabulary (`cohomologyOf`, `specAlgebraRingHom`, `pieceModule`, `gradedCohomologySum`) and
part (2) are in `Basic`.

## Main results

* `tag02O6` — the proposition `Tag02O6` is a theorem.
* `moduleFinite_gradedCohomologySum` — part (1) of [Stacks, Tag 0897] read off a given base
  change.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

/-- **[Stacks, Tag 02O6].** The proposition `Tag02O6` holds: for `R` Noetherian,
`g : Y ⟶ Spec R` proper and `G` a coherent `𝒪_Y`-module, `Hⁱ(Y, G)` is a finite `R`-module in
every degree.

`Spec R` is locally Noetherian, so
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology` makes `Hⁱ(Y, G)` a finite
module over `Γ(Spec R, ⊤)`, and the two actions agree under the isomorphism
`Γ(Spec R, ⊤) ≅ R`, along which finiteness transports. -/
theorem tag02O6 : Tag02O6.{u} := by
  intro R _ hR Y g hg G hG i
  have _hR := hR
  have _hg := hg
  have _hG := hG
  have _hN : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of R)) :=
    _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.mpr hR
  have _hfin := _root_.AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology g G i
  -- The `R`-action is the `Γ(Spec R, ⊤)`-action read through `Γ(Spec R, ⊤) ≅ R`.
  have key : ∀ a : Γ(Spec (.of R), ⊤),
      specAlgebraRingHom R g ((Scheme.ΓSpecIso (.of R)).hom a) = g.appTop.hom a :=
    fun a => congrArg g.appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of R)) a)
  exact Module.Finite.of_surjective
    (M := ↥((ModuleCat.restrictScalars g.appTop.hom).obj (cohomologyOf Y i G)))
    (σ := (Scheme.ΓSpecIso (.of R)).hom.hom)
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        change g.appTop.hom a • (show cohomologyOf Y i G from x)
          = specAlgebraRingHom R g ((Scheme.ΓSpecIso (.of R)).hom a) •
            (show cohomologyOf Y i G from x)
        rw [key] }
    Function.surjective_id

/-! ### Tag 0897 part (1) -/

/-- **Part (1) of [Stacks, Tag 0897], read off a given base change.** Let `A` be a Noetherian ring, `B` a
finitely generated graded `A`-algebra, `f : X ⟶ Spec A` proper and `F` a quasi-coherent graded
`𝓑`-module of finite type. Then the graded `B`-module `⨁ₙ H^p(X, Fₙ)` is a finite `B`-module,
for every `p`.

The hypotheses beyond the source's are the base change of the source's proof alone:
`f' : X' ⟶ Spec B` proper with a coherent `F'` on `X'`, the graded `B`-action on
`⨁ₙ H^p(X, Fₙ)`, and the `B`-linear comparison `cmp` with `H^p(X', F')` that
[Stacks, Tag 089W] provides because `X' ⟶ X` is affine. [Stacks, Tag 02O6] is *not* assumed:
it is `tag02O6` above.

"Of finite type" is `SheafOfModules.GradedModule.IsFiniteType`, the local notion of
[Stacks, Tag 03DL] part (5) read for a graded module, which is the source's own hypothesis; it is
inert in this implication (finite type of `F` enters the source's argument only in producing `F'`
and its coherence, which here are binders) and is retained because dropping it would state
something other than [Stacks, Tag 0897]. It is also exactly the predicate
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite_of_isCoherent` has available when it
instantiates this tag for [Stacks, Tag 02O8].

Given the base change, the content is that [Stacks, Tag 02O6] applies to `f'` with the ring `B`:
`B` is Noetherian because it is a finitely generated algebra over the Noetherian ring `A`, and
`F'` is coherent, so `H^p(X', F')` is a finite `B`-module and `cmp` carries that finiteness back
to `⨁ₙ H^p(X, Fₙ)`. -/
theorem moduleFinite_gradedCohomologySum {X : Scheme.{u}}
    {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (A : Type u) [CommRing A] [IsNoetherianRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : _root_.SheafOfModules.GradedModule 𝓑)
    (_hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (_hft : F.IsFiniteType)
    (p : ℕ)
    {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of B)) [IsProper f']
    (F' : X'.Modules) [F'.IsCoherent]
    [Module B (gradedCohomologySum F p)]
    (cmp : gradedCohomologySum F p ≃ₗ[B]
      ↥((ModuleCat.restrictScalars (specAlgebraRingHom B f')).obj
        (cohomologyOf X' p F'))) :
    Module.Finite B (gradedCohomologySum F p) :=
  have hBN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have _hfin : Module.Finite B
      ↥((ModuleCat.restrictScalars (specAlgebraRingHom B f')).obj (cohomologyOf X' p F')) :=
    tag02O6.{u} B hBN X' f' inferInstance F' inferInstance p
  Module.Finite.equiv cmp.symm

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
