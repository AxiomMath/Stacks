module

public import StacksFrontier.AlgebraicGeometry.Descent.FiberwiseFreeReducedBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusRepresentable

/-!
# A fibrewise trivial vector bundle over a reduced base is pulled back from the base

[Stacks, Tag 0EX7]: let `f : X ⟶ S` be a flat, proper morphism of finite presentation such that
`f_*𝒪_X = 𝒪_S` and this remains true after arbitrary base change, and let `E` be a finite locally
free `𝒪_X`-module whose restriction to every fibre `X_s` is free of finite rank. If `S` is reduced,
then `E ≅ f^*N` for a finite locally free `𝒪_S`-module `N`.

The proof is the source's: the descent locus `Z ⟶ S` of [Stacks, Tag 0BDP]
(`AlgebraicGeometry.hasDescentLocus_of_flat_of_isProper`) contains every point of `S` by the
fibrewise hypothesis, so it is a surjective immersion, hence a surjective closed immersion, hence
an isomorphism because `S` is reduced; this last step is
`AlgebraicGeometry.exists_finiteLocallyFree_iso_of_fiberwiseFree`.

## References

* [Stacks Project, Tag 0EX7](https://stacks.math.columbia.edu/tag/0EX7)
* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **Stacks Tag 0EX7.** Let `f : X ⟶ S` be a flat, proper morphism of finite presentation such
that `𝒪_S ⟶ f_*𝒪_X` is an isomorphism and remains so after arbitrary base change. Let `E` be a
finite locally free `𝒪_X`-module such that (1) `E|_{X_s} ≅ 𝒪_{X_s}^{⊕ r_s}` for every `s ∈ S`,
and (2) `S` is reduced. Then `E ≅ f^*N` for a finite locally free `𝒪_S`-module `N`. -/
@[stacks 0EX7]
theorem exists_finiteLocallyFree_iso_of_fiberwiseFree_of_isReduced {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] (hfp : FinitePresentation f)
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f g).toLRSHom.toShHom))
    (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hfiber : ∀ s : S, ∃ r : ℕ,
      Nonempty ((modulePullback
          (pullback.fst f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj E ≅
        SheafOfModules.free (ULift.{u} (Fin r))))
    [IsReduced S] :
    ∃ N : SheafOfModules.{u} (structureSheafRing S.toRingedSpace),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
        Nonempty ((modulePullback f.toLRSHom.toShHom).obj N ≅ E) :=
  exists_finiteLocallyFree_iso_of_fiberwiseFree f E
    (hasDescentLocus_of_flat_of_isProper f hfp hO E) hfiber

end AlgebraicGeometry
