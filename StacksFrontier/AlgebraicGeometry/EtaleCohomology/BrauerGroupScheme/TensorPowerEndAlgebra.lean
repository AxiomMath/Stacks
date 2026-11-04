module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.BrauerMonoid
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf

/-!
# The tensor power of an endomorphism algebra sheaf

Let `S` be a scheme and let `E` be a finite locally free sheaf of `𝒪_S`-modules. The comparison
`𝓗om(E,E) ⊗ 𝓗om(F,F) ≅ 𝓗om(E ⊗ F, E ⊗ F)` of
`Stacks.EtaleCohomology.BrauerScheme.endAlgebraTensorIso` compares two factors; this file
iterates it, identifying the `n`-fold tensor power of the endomorphism algebra of `E` with the
endomorphism algebra of the `n`-fold tensor power of `E`,
$$
\mathcal{H}om(E, E)^{\otimes n} \cong \mathcal{H}om(E^{\otimes n}, E^{\otimes n}).
$$
This is the identification [Stacks, Tag 0A2L] uses to read the Saltman projector
`p : E^{\otimes d} \to E^{\otimes d}` as a section of `A^{\otimes d}` on a member of a
trivialising étale covering of an Azumaya algebra `A ≅ 𝓗om(E,E)`.

The powers here start at `1`. The zeroth power of `𝓗om(E,E)` is the unit algebra sheaf `𝒪_S`
and the zeroth power of `E` is `𝒪_S` as a module, so the degree-zero case would be
`𝓗om(𝒪_S, 𝒪_S) ≅ 𝒪_S` as sheaves of algebras — the internal endomorphism monoid of the
monoidal unit — which the library does not identify with the unit monoid; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.BrauerMonoid`.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFree_natTensorPow`: a positive tensor
  power of a finite locally free sheaf of modules is finite locally free.
* `Stacks.EtaleCohomology.BrauerScheme.HasPositiveRank.of_iso` and
  `Stacks.EtaleCohomology.BrauerScheme.hasPositiveRank_natTensorPow`: positive rank only depends
  on the isomorphism class, and a positive tensor power of a sheaf of modules of positive rank
  has positive rank.
* **`Stacks.EtaleCohomology.BrauerScheme.natTensorPowEndAlgebraIso`**:
  `𝓗om(E,E)^{⊗ (n+1)} ≅ 𝓗om(E^{⊗ (n+1)}, E^{⊗ (n+1)})` as sheaves of `𝒪_S`-algebras, for `E`
  finite locally free.
* `Stacks.EtaleCohomology.BrauerScheme.isTrivialClass_natTensorPow_endAlgebra`: a positive
  tensor power of the endomorphism algebra of a finite locally free sheaf of modules of positive
  rank again has trivial Brauer class.

## Implementation notes

`Stacks.TensorPowers.natTensorPow` is defined by `natTensorPow L (n + 1) = natTensorPow L n ⊗ L`,
so the recursion below adds a factor on the right, and the two-factor comparison
`endAlgebraTensorIso` is applied with the already-identified power on the left. Its hypotheses
are the finite local freeness of both factors, which is why
`isFiniteLocallyFree_natTensorPow` comes first.

The degree-one case is the left unitor: `natTensorPow L 1` is `𝟙_ ⊗ L`, not `L`, so it is
`λ_` that identifies the two sides, on the module side under `endAlgebraCongr`.

**What Tag 0A2L still needs, and where this fits.** The tag says that an Azumaya `𝒪_S`-algebra
whose underlying module is finite locally free of rank `d ^ 2` has Brauer class annihilated by
`d`, i.e. `brauerClass A ^ d = 1` for `A : Azumaya S` with
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank A.1.X (d ^ 2)`. Degree `0` is
`pow_zero`, and for `1 ≤ d` the reduction
`Stacks.EtaleCohomology.BrauerScheme.brauerClass_pow_eq_one_of_isTrivialClass_natTensorPow`
leaves exactly one statement open, Saltman's construction:
`IsTrivialClass (Stacks.TensorPowers.natTensorPow A.1 d)`. Four things are missing for it.

* The projector. On a member `U_i` of a trivialising étale covering, `A ≅ 𝓗om(F, F)` with `F`
  free of rank `d`, and the source takes `p : F^{⊗ d} → ∧^d F → F^{⊗ d}`. What the rest of the
  argument uses is only that `p` factors through `𝟙_` as a split epi followed by a split mono,
  so `p` may be taken to be the antisymmetrizer `Σ_σ sgn(σ) · σ` — which needs an action of
  `Equiv.Perm (Fin d)` on `Stacks.TensorPowers.natTensorPow` in a symmetric monoidal category,
  of which the library has nothing. Then `p² = d! · p` is the group-algebra identity.
* Reading `p` as a section of `A^{⊗ d}` over `U_i`: this is `natTensorPowEndAlgebraIso` here,
  together with `Functor.Monoidal.μIso (algebraPullback (𝒰.f i))` and the trivialisation.
* Agreement on `U_i ×_S U_j`, which is what Tag 0A2K is for
  (`Stacks.EtaleCohomology.exists_invertible_tensor_iso_of_endomorphism_algebra_iso`, proved):
  the two trivialisations differ by conjugation by some `F_i ⊗ L ≅ F_j`, and `p` is insensitive
  to that because the braiding is natural and is the identity on `L ⊗ L` for invertible `L`.
  Using it means bridging that lemma's explicit `Stacks.SheafOfModules.SheafHom`/`sectionsEquiv`
  formulation to the internal hom `CategoryTheory.MonoidalClosed.internalEnd` of this
  development; the two are not identified anywhere.
* Gluing and the local calculation. `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_etale'`
  (Tag 03DT, the étale half of Tag 03OG) gives the global section `p`, and
  `AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover` (Tag 05B2, through
  `AlgebraicGeometry.Scheme.etalePrecoverage_le_fpqcPrecoverage`) descends finite local freeness
  of `𝓗 = Im(A^{⊗ d} → A^{⊗ d}, f ↦ f p)`. Both apply to the objects of this file verbatim:
  `ModuleSheaf S` is `S.Modules` and `modulePullback φ` is `Scheme.Modules.pullback φ`, both by
  `rfl`. What is not packaged is that pullback along a flat — hence an étale — morphism
  preserves the image, which is what identifies `𝓗` on `U_i` with `F^{⊗ d}`.

## References

* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

variable {S : Scheme.{u}}

/-- **A positive tensor power of a finite locally free sheaf of `𝒪_S`-modules is finite locally
free.** The first power is `𝟙_ ⊗ E`, handled by the left unitor; each further factor is added
with `isFiniteLocallyFree_tensor`. -/
theorem isFiniteLocallyFree_natTensorPow {E : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E) :
    ∀ n : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) (Stacks.TensorPowers.natTensorPow E (n + 1))
  | 0 =>
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso (h := hE) (λ_ E).symm
  | n + 1 => isFiniteLocallyFree_tensor (isFiniteLocallyFree_natTensorPow hE n) hE

/-- **Positive rank only depends on the isomorphism class** of a sheaf of `𝒪_S`-modules: the
local bases are transported along the isomorphism, keeping their index types. -/
theorem HasPositiveRank.of_iso {E F : ModuleSheaf S} (e : E ≅ F) (h : HasPositiveRank E) :
    HasPositiveRank F := by
  obtain ⟨q, hq, hne⟩ := h
  let q' : SheafOfModules.LocalGeneratorsData.{u, u, u, u} F :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i ↦ (q.generators i).ofEpi
        ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom }
  have hq' : q'.IsLocallyFreeData.{u, u, u, u} := ⟨fun i => by
    have h₀ : IsIso (q.generators i).π := hq.isIso i
    have h₁ : IsIso ((q.generators i).π ≫
        ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom) := inferInstance
    exact Eq.mpr (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
      (q.generators i) ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom)) h₁⟩
  exact ⟨q', hq', hne⟩

/-- **A positive tensor power of a sheaf of `𝒪_S`-modules of positive rank has positive
rank.** -/
theorem hasPositiveRank_natTensorPow {E : ModuleSheaf S} (hE : HasPositiveRank E) :
    ∀ n : ℕ, HasPositiveRank (Stacks.TensorPowers.natTensorPow E (n + 1))
  | 0 => HasPositiveRank.of_iso (λ_ E).symm hE
  | n + 1 => hasPositiveRank_tensor (hasPositiveRank_natTensorPow hE n) hE

/-- **`𝓗om(E,E)^{⊗ (n+1)} ≅ 𝓗om(E^{⊗ (n+1)}, E^{⊗ (n+1)})` as sheaves of `𝒪_S`-algebras**, for a
finite locally free sheaf of `𝒪_S`-modules `E`: the iterate of the two-factor comparison
`endAlgebraTensorIso`. This is the identification
`𝓗om(F,F)^{⊗ d} = 𝓗om(F^{⊗ d}, F^{⊗ d})` of the proof of [Stacks, Tag 0A2L]. -/
def natTensorPowEndAlgebraIso {E : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E) :
    ∀ n : ℕ, Stacks.TensorPowers.natTensorPow (endAlgebra E) (n + 1) ≅
      endAlgebra (Stacks.TensorPowers.natTensorPow E (n + 1))
  | 0 => λ_ (endAlgebra E) ≪≫ endAlgebraCongr (λ_ E).symm
  | n + 1 =>
    tensorIso (natTensorPowEndAlgebraIso hE n) (Iso.refl (endAlgebra E)) ≪≫
      endAlgebraTensorIso (isFiniteLocallyFree_natTensorPow hE n) hE

/-- **A positive tensor power of the endomorphism algebra of a finite locally free sheaf of
`𝒪_S`-modules of positive rank again has trivial Brauer class**: it is the endomorphism algebra
of the corresponding tensor power of the module, which is again finite locally free of positive
rank. -/
theorem isTrivialClass_natTensorPow_endAlgebra {E : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E)
    (hE' : HasPositiveRank E) (n : ℕ) :
    IsTrivialClass (Stacks.TensorPowers.natTensorPow (endAlgebra E) (n + 1)) :=
  ⟨Stacks.TensorPowers.natTensorPow E (n + 1), isFiniteLocallyFree_natTensorPow hE n,
    hasPositiveRank_natTensorPow hE' n, ⟨natTensorPowEndAlgebraIso hE n⟩⟩

end Stacks.EtaleCohomology.BrauerScheme

end

end
