module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence
public import StacksFrontier.RingTheory.LocalCohomology.UniformCohomologyBound
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The essential image of the completion functor over a base that is not complete

Let `X` be an affine Noetherian scheme, `A = Γ(X, 𝒪_X)` and `I ⊆ A` an ideal. Stacks 087W,
`Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat`, is an equivalence

`Coh(X, I 𝒪_X) ≌ FGModuleCat A ^∧`

and carries **no completeness hypothesis** on `A`. What does carry one is a different statement:
that the completion functor of Stacks 0880 is essentially surjective onto `Coh(X, I 𝒪_X)`
(`Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete`, Grothendieck existence in the
affine case). This file isolates exactly what completeness is being used for there, by computing
the essential image of the completion functor at an arbitrary `A`: transported across 087W, a
coherent adic system lies in it precisely when the finite `A ^∧`-module 087W attaches to it is
the completion of a finite `A`-module.

## Main results

* `Stacks.Coherent.essImage_iff_essImage_comp_equivalence` — the essential image of a functor is
  computed by its composite with any equivalence of the target.
* `Stacks.Coherent.essImage_completionFunctor_iff_essImage_fgModuleCat` — **the essential image of
  the completion functor over a base that need not be complete**: a coherent adic system is the
  completion of a coherent module exactly when its finite module over `A ^∧` is in the image of
  the completion functor composed with 087W, i.e. exactly when that module descends along
  `A ⟶ A ^∧`.
* `Stacks.Coherent.essImage_completionFunctor_of_fgModuleCat_iso` — the usable direction, with the
  descending module given: a finite `A`-module whose associated system matches under 087W
  algebraizes the given system.
* `Stacks.Algebraization.essImage_completionFunctor_baseIdealSheaf_of_isAdicComplete_sections` —
  Grothendieck existence at the ideal `I · Γ(X, 𝒪_X)` of Stacks 088B, with completeness of
  `Γ(X, 𝒪_X)` as an explicit hypothesis and **no properness of `X ⟶ Spec A` and no completeness
  of `A`**.

## Why the completeness hypothesis of the affine case cannot simply be dropped

The question this file answers negatively is whether
`Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete` holds without its
`[IsAdicComplete I Γ(X, 𝒪_X)]` instance. It does not, and the obstruction is visible through 087W.
Composed with the equivalence, the completion functor is `M ↦ M ^∧ = M ⊗_A A ^∧` on finite
`A`-modules, so essential surjectivity of the completion functor says that *every* finite
`A ^∧`-module is the base change of a finite `A`-module. That fails already for a one-dimensional
Noetherian local domain whose completion is not a domain. Take `A` the local ring at the origin of
the node `y ² = x ²(x + 1)` over a field of characteristic `≠ 2` and `I` its maximal ideal: in
`A ^∧ = k[[x, y]]/(y ² - x ²(x + 1))` the unit `x + 1` has a square root `u`, so `y ² - x ²u ²`
factors and `A ^∧` has two minimal primes. The finite `A ^∧`-module `N = A ^∧/(y - xu)` is not a
base change: if `N ≅ M ⊗_A A ^∧` with `M` a finite `A`-module then, `A ⟶ A ^∧` being flat and `M`
finitely presented, `Ann(N) = Ann(M) · A ^∧`, which is nonzero; `A` being a domain that forces
`Ann(M) ≠ 0`, hence `M` of finite length since `A` is local of dimension one, hence `N` of finite
length, which it is not — `N ≅ k[[x]]`.

So the hypothesis that the base be complete is not bookkeeping that a reorganization removes, and
the reduction of Stacks 088B to an affine base cannot proceed by applying Grothendieck existence
on an affine open of the base. The source does not do this: its step is to *replace* the base
ring `B` by `B ^∧`, where the hypothesis holds by construction, base-change the whole situation
along the flat map `B ⟶ B ^∧`, and transport only the *conclusion* — annihilation of the kernels
and cokernels by a power of `𝒦` — back along `B ⟶ B ^∧`, which is where More on Algebra 05EC
enters. Nothing in that argument descends an algebraization, and
`essImage_completionFunctor_iff_essImage_fgModuleCat` says why it cannot.

`essImage_completionFunctor_baseIdealSheaf_of_isAdicComplete_sections` is the shape such a
reduction needs: it is Grothendieck existence at the ideal sheaf `I · 𝒪_X` of Stacks 088B with
completeness of the sections carried as a hypothesis rather than derived, so that it applies to a
scheme which is affine but not proper over `Spec A` — the situation on an affine open of the base,
where `Stacks.Algebraization.essImage_completionFunctor_baseIdealSheaf_of_isAffine` does not apply
because its route to completeness is that an affine proper morphism is finite.

## Implementation notes

**No `@[stacks 087W]` attribute is attached to anything here.** Tag 087W is the equivalence of
categories, which is already registered on
`Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat` and its satellites in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CoherentAdicSystem/Equivalence.lean`, with no
completeness hypothesis there to remove. Essential surjectivity of the completion functor is not
087W's statement; it belongs to Stacks 0880/088C, and the characterization proved here is a
reformulation of it rather than coverage of a source lemma.

The ideal sheaf `Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f` is by definition
`Scheme.IdealSheafData.ofIdealTop (baseIdeal A I f)`, so the last result is an application of the
affine case at that ideal with no transport.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.Coherent

open Stacks.Algebraization

/-- **The essential image of a functor is computed by its composite with an equivalence of the
target.** An object `G` of `D` is in the essential image of `T : C ⥤ D` exactly when `E.functor`
applied to it is in the essential image of `T ⋙ E.functor`, for any equivalence `E : D ≌ D'`.

One direction applies `E.functor` to a witnessing isomorphism; the other takes the preimage of
one under the fully faithful `E.functor`. -/
public theorem essImage_iff_essImage_comp_equivalence
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {D' : Type u₃} [Category.{v₃} D'] (T : C ⥤ D) (E : D ≌ D') (G : D) :
    T.essImage G ↔ (T ⋙ E.functor).essImage (E.functor.obj G) := by
  constructor
  · rintro ⟨M, ⟨e⟩⟩
    exact ⟨M, ⟨E.functor.mapIso e⟩⟩
  · rintro ⟨M, ⟨e⟩⟩
    exact ⟨M, ⟨E.fullyFaithfulFunctor.preimageIso e⟩⟩

/-- **The essential image of the completion functor over an affine base that need not be
complete.** Let `X` be affine and Noetherian, `A = Γ(X, 𝒪_X)` and `I ⊆ A` an ideal. A coherent
adic system `G` along `I · 𝒪_X` is the completion of a coherent `𝒪_X`-module exactly when the
finite `A ^∧`-module attached to it by Stacks 087W lies in the image of the completion functor
read through 087W — that is, exactly when that module descends along `A ⟶ A ^∧`.

This is the precise content of the completeness hypothesis of
`Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete`: when `A` is `I`-adically complete
the right-hand side is automatic because `A ^∧ = A`, and in general it is a genuine restriction —
see the module docstring for a one-dimensional local domain where it fails. -/
public theorem essImage_completionFunctor_iff_essImage_fgModuleCat
    (X : Scheme.{u}) [IsAffine X] [IsLocallyNoetherian X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).essImage G ↔
      (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I) ⋙
          (coherentAdicSystemsEquivFGModuleCat X I).functor).essImage
        ((coherentAdicSystemsEquivFGModuleCat X I).functor.obj G) :=
  essImage_iff_essImage_comp_equivalence _ _ G

/-- **The descent, with the descending module given.** If a finite `Γ(X, 𝒪_X)`-module `M` has the
property that the completion of `M ~` and the given system `G` agree after Stacks 087W, then `G`
is the completion of a coherent `𝒪_X`-module. No completeness of `Γ(X, 𝒪_X)` is assumed. -/
public theorem essImage_completionFunctor_of_fgModuleCat_iso
    (X : Scheme.{u}) [IsAffine X] [IsLocallyNoetherian X] [IsNoetherianRing Γ(X, ⊤)]
    (I : Ideal Γ(X, ⊤))
    (G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (M : ModuleCat.{u} Γ(X, ⊤)) [Module.Finite Γ(X, ⊤) M]
    (e : (coherentAdicSystemsEquivFGModuleCat X I).functor.obj
          ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj
            ⟨(affineTilde X).obj M, affineTilde_coherent X M⟩) ≅
        (coherentAdicSystemsEquivFGModuleCat X I).functor.obj G) :
    (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).essImage G :=
  (essImage_completionFunctor_iff_essImage_fgModuleCat X I G).mpr ⟨_, ⟨e⟩⟩

end Stacks.Coherent

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-- **Grothendieck existence at the ideal sheaf `I · 𝒪_X` of Stacks 088B, with completeness of the
global functions as a hypothesis.** Let `A` be a ring, `I ⊆ A` an ideal and `f : X ⟶ Spec A` a
morphism with `X` affine and Noetherian. If `Γ(X, 𝒪_X)` is complete with respect to
`baseIdeal A I f = I · Γ(X, 𝒪_X)`, then every object of `Coh(X, I · 𝒪_X)` is the completion of a
coherent `𝒪_X`-module.

Unlike `Stacks.Algebraization.essImage_completionFunctor_baseIdealSheaf_of_isAffine` this assumes
neither properness of `f` nor completeness of `A`: it is the form that applies on an affine open
of the base of Stacks 088B, where no properness is available and completeness has to be arranged
by replacing the base ring with its completion. The ideal sheaf `baseIdealSheaf A I f` is by
definition `Scheme.IdealSheafData.ofIdealTop (baseIdeal A I f)`, so this is the affine case of
Grothendieck existence applied at that ideal, with nothing to transport. -/
@[ega "III 5.1.4" "partial"]
public theorem essImage_completionFunctor_baseIdealSheaf_of_isAdicComplete_sections
    (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsAffine X] [IsLocallyNoetherian X]
    [IsNoetherianRing Γ(X, ⊤)] [IsAdicComplete (baseIdeal A I f) Γ(X, ⊤)]
    (G : CoherentAdicSystems (baseIdealSheaf A I f)) :
    (completionFunctor X (baseIdealSheaf A I f)).essImage G :=
  essImage_completionFunctor_of_isAdicComplete X (baseIdeal A I f) G

end Stacks.Algebraization

end
