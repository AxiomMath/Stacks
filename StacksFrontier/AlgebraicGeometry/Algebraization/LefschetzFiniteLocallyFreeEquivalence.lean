module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkFreeOfFiniteLocallyFreeAdic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FiniteLocallyFreeAdic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.GlobalProperOverCompleteLocal
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzNeighbourhoodSectionsComplete
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCompletedStalkDepthCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ZeroSchemeOpenNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzFiniteLocallyFreeFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.LefschetzZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzFormalModuleAlgebraization

/-!
# The Lefschetz equivalence for finite locally free objects along an ample section

Let `k` be a field, `X` a proper scheme over `k`, `𝓛` an ample invertible `𝒪_X`-module and
`s ∈ Γ(X, 𝓛)`. Let `Y = Z(s)` be the zero scheme of `s`, `𝓘 ⊆ 𝒪_X` its sheaf of ideals and `𝒱`
the set of open subschemes of `X` containing `Y`, ordered by reverse inclusion. [Stacks, Tag 0EL7]
says that if `depth(𝒪_{X,x}) + dim({x}‾) > 2` for every `x ∈ X ∖ Y`, then the completion functor
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, 𝓘)` is an equivalence on the full subcategories of finite locally free
objects.

## Main results

* `Stacks.Algebraization.completionEquivalence_finiteLocallyFree_of_two_lt_depth_add_dimClosure`
  — if `depth(𝒪_{X,x}) + dim({x}‾) > 2` off `Y`, the completion functor is an equivalence on finite
  locally free objects ([Stacks, Tag 0EL7]).

## Implementation notes

The objects of `colim_𝒱 Coh(𝒪_V)` are the coherent modules on the individual members `V` of `𝒱`,
and a morphism from `𝒢` to `ℱ`, both on `V`, is an element of `colim_{W ⊆ V} Hom(𝒢|_W, ℱ|_W)`. A
*finite locally free object* of `Coh(X, 𝓘)` is, by the source's own definition, one whose `n`-th
term is a finite locally free `𝒪_X/𝓘^{n+1}`-module, i.e. the direct image of a finite locally free
module on the closed subscheme cut out by `𝓘^{n+1}`
(`Stacks.Algebraization.IsFiniteLocallyFreeAdic`). The equivalence is stated, as for
[Stacks, Tag 0EKZ], as its three elementwise halves:

1. the functor carries a finite locally free coherent module on any `V ∈ 𝒱` to a finite locally
   free object of `Coh(V, 𝓘|_V)` (whose infinitesimal neighbourhoods are those of `Y` in `X`);
2. it is fully faithful there:
   `colim_{W ⊆ V} Hom(𝒢|_W, ℱ|_W) ⟶ lim_n Hom(𝒢|_{Y_n}, ℱ|_{Y_n})` is bijective for all finite
   locally free `𝒢`, `ℱ` on any `V ∈ 𝒱`, which is
   `Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete` (condition (4)
   of [Stacks, Tag 0EK2]);
3. it is essentially surjective onto them: every finite locally free object `(𝓕_n)` of `Coh(X, 𝓘)`
   is, for some `V ∈ 𝒱`, the completion of a finite locally free coherent `𝒪_V`-module; the module
   is given as the restriction to `V` of a coherent `𝒪_X`-module `𝒢` with `𝒢^∧ ≅ (𝓕_n)`.

## References

* [Stacks Project, Tag 0EL7](https://stacks.math.columbia.edu/tag/0EL7)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Algebraization

/-- Let `k` be a field, `X` a proper scheme over `k`, `𝓛` an ample invertible `𝒪_X`-module,
`s ∈ Γ(X, 𝓛)`, `Y = Z(s)` its zero scheme with sheaf of ideals `𝓘`, and `𝒱` the open subschemes
of `X` containing `Y`. Assume `depth(𝒪_{X,x}) + dim({x}‾) > 2` for all `x ∈ X ∖ Y`. Then the
completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, 𝓘)` is an equivalence on the full subcategories of
finite locally free objects: it lands in the finite locally free objects, it is fully faithful on
finite locally free objects, and every finite locally free object of `Coh(X, 𝓘)` is the
completion of a finite locally free coherent module on some `V ∈ 𝒱`. See the module documentation
for how each half is written. -/
@[stacks 0EL7]
public theorem completionEquivalence_finiteLocallyFree_of_two_lt_depth_add_dimClosure
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (s : Γ(L, ⊤))
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      ((2 : ℕ) : WithBot ℕ∞) < localDepthAddDimClosure X x) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (∀ (V : X.Opens), ((zeroScheme X L s).support : Set X) ⊆ (V : Set X) →
        ∀ G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf,
          AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj →
          IsFiniteLocallyFreeAdic ((zeroScheme X L s).comap V.ι)
            ((completionFunctor V.toScheme ((zeroScheme X L s).comap V.ι)).obj G)) ∧
      NeighbourhoodCompletion.CompletionFullyFaithfulComplete (zeroScheme X L s).subschemeι ∧
      (∀ F : Stacks.Coherent.CoherentAdicSystems (zeroScheme X L s),
        IsFiniteLocallyFreeAdic (zeroScheme X L s) F →
        ∃ (V : X.Opens) (_ : ((zeroScheme X L s).support : Set X) ⊆ (V : Set X))
          (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf),
          AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree
              (restrictCoherentModules V.ι G).obj ∧
            Nonempty (((completionFunctor X (zeroScheme X L s)).obj G).obj ≅ F.obj) ∧
            Nonempty (((completionFunctor V.toScheme ((zeroScheme X L s).comap V.ι)).obj
                (restrictCoherentModules V.ι G)).obj ≅
              F.obj ⋙ Scheme.Modules.restrictFunctor V.ι)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set I := zeroScheme X L s with hI
  have h0EL1 : ∀ (F : X.Modules) [F.IsCoherent] [F.IsQuasicoherent],
      (∀ x : X, x ∉ (I.support : Set X) →
        enatToEInt (sheafDepthAt F x) + krullDimToEInt (dimClosureAt X x) > ((1 : ℤ) : EInt)) →
      IsIso (zeroSchemeComparison X L s F 0) := fun F _ _ hd =>
    isIso_zeroSchemeComparison_of_isProper k f L hL s F 1 hd 0 (by norm_num)
  have h0EL5 : ∀ F : Stacks.Coherent.CoherentAdicSystems I,
      (∀ q ∈ (I.support : Set X), ∀ p : PrimeSpectrum (completedLocalRing I q),
        ¬ completedLocalIdeal I q ≤ p.asIdeal →
        (2 : EInt) < enatToEInt (completedStalkDepth I F q p) +
          krullDimToEInt (ringKrullDim (completedLocalRing I q ⧸ p.asIdeal)) +
          krullDimToEInt (dimClosureAt X q)) →
      IsCompletionOfCoherent I F := fun F hd =>
    isCompletionOfCoherent_of_two_lt_depth_add_dim k f L hL s F hd
  have hFF : NeighbourhoodCompletion.CompletionFullyFaithfulComplete I.subschemeι := by
    refine completionFullyFaithfulComplete_zeroScheme k X f L hL s fun m => ?_
    have := isCoherent_tensorPowerModules X L (m : ℤ)
    have : (Scheme.Modules.tensorPowerModules L (m : ℤ)).IsQuasicoherent :=
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
    have hd := fun x => @depth_stalk_le_sheafDepthAt X _
      (Scheme.Modules.tensorPowerModules L (m : ℤ)) (isFiniteLocallyFree_tensorPowerModules X L m) x
    have hdep : ∀ x : X, x ∉ (I.support : Set X) →
        enatToEInt (sheafDepthAt (Scheme.Modules.tensorPowerModules L (m : ℤ)) x) +
          krullDimToEInt (dimClosureAt X x) > ((1 : ℤ) : EInt) :=
      fun x hx => one_lt_enatToEInt_add_of_two_lt (hd x) (hdepth x hx)
    exact isNeighbourhoodSectionsComplete_of_isIso_zeroSchemeComparison k X f L hL s _ hdep
      (h0EL1 _ hdep)
  refine ⟨fun V _ G hG => ?_, hFF, fun F hF => ?_⟩
  · have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
    exact isFiniteLocallyFreeAdic_completion V.toScheme (I.comap V.ι) G
      ((AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff G.obj).mp hG)
  · obtain ⟨G, ⟨e⟩⟩ := h0EL5 F fun q hq p hp =>
      two_lt_enatToEInt_add_krullDimToEInt_add
        (two_lt_completedStalkDepth_add_of_two_lt_localDepthAddDimClosure k f I F hdepth hq
          (free_completedStalk_of_isFiniteLocallyFreeAdic I F hF hq) p hp)
    obtain ⟨V, hV, hfree⟩ := exists_isFiniteLocallyFree_restrict_of_completion_iso I F hF G e
    have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
    exact ⟨V, hV, G, hfree, ⟨e⟩,
      ⟨(completionRestrictOpenIso V.ι I G).symm ≪≫ Functor.isoWhiskerRight e _⟩⟩

end Stacks.Algebraization

end
