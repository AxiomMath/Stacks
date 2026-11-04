module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf

/-!
# Algebraicity of the Hilbert functor (Stacks 0D01)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation and separated. Stacks 0D01 says that the Hilbert functor
`Hilb_{X/B}` of Stacks 0CZY is an algebraic space locally of finite presentation over `B`, and its
proof is a one-line deduction: `Hilb_{X/B} = Quot_{𝒪_X/X/B}` by Stacks 0D00, and the Quot functor
of a finitely presented separated morphism is an algebraic space locally of finite presentation
over the base by Stacks 09TU.

That deduction is what this file carries out. Both of its two inputs are absent from the library
and are therefore hypotheses of the statement, in the form the proof consumes them: Stacks 09TU as
a model of the Quot presheaf which is an algebraic space whose structure morphism to `B` is
locally of finite presentation, and Stacks 0D00 as an isomorphism of the Hilbert presheaf with the
Quot presheaf over `B`. See the implementation notes for what each would take to discharge.

## Main results

* `AlgebraicGeometry.Space.exists_hilbertPresheafModel_isAlgebraicSpace`: **Stacks 0D01**, the
  Hilbert functor is an algebraic space locally of finite presentation over the base.
* `AlgebraicGeometry.Space.HilbertPresheafModel.toBase_eq_of_iso`: the morphism to the base of the
  model the deduction produces is the one the Quot side already had, which is what carries local
  finite presentation across.

## Implementation notes

**The conclusion is about a model.** A section of the Hilbert presheaf over a scheme `T` of the
site is a closed subfunctor of `X_T`, so it lives one universe above the sections of an algebraic
space; the statement of algebraicity is therefore about an
`AlgebraicGeometry.Space.HilbertPresheafModel`, a presheaf of `Type u` whose universe lift is the
Hilbert presheaf, exactly as in Stacks 0CZY. The same device on the Quot side is
`AlgebraicGeometry.Space.QuotSitePresheafModel`. The two models are literally the same presheaf
here: the deduction transports the identification, not the presheaf.

**The carried hypothesis `N`, `halg`, `hlfp` is Stacks 09TU** for the situation at hand. Its proof
in the source runs through the algebraicity of the stack of coherent sheaves (Stacks 09DS), the
algebraicity of a stack carrying a 1-morphism representable by algebraic spaces to an algebraic
stack (Stacks 05UM), the relative Hom space (Stacks 08K6) and the open locus where a map of
modules is surjective (Stacks 09TP), and concludes with the implication (1) ⟹ (3) of Stacks 04SZ.
Of those, Stacks 05UM and Stacks 09TP are in the library; Stacks 09DS, Stacks 08K6, the sheaf
property of the Quot functor (Stacks 09TT) and the implication (1) ⟹ (3) of Stacks 04SZ are not,
and the last is what the final step of Stacks 09TU needs.

**The carried hypotheses `e` and `he` are Stacks 0D00**, the identification
`Hilb_{X/B} = Quot_{𝒪_X/X/B}`, over `B`. Discharging it needs the dictionary between a closed
subspace `Z ⊆ X_T` and the quotient `𝒪_{X_T} ⟶ i_*𝒪_Z` it defines: the bijection between closed
subspaces and quasi-coherent ideal sheaves (Stacks 03MB) and the quasi-coherence of `i_*𝒪_Z` are
in the library, while the three remaining entries are not — that `Z ⟶ T` is of finite
presentation exactly when `i_*𝒪_Z` is a module of finite presentation, that `Z ⟶ T` is flat
exactly when `i_*𝒪_Z` is flat over `T`, and the converse half of the proper-support entry, for
which the containment `Supp(i_*𝒪_Z) ⊆ |Z|` is proved but not the equality.

Accordingly the situation `D` whose Quot functor is compared is not forced to be the
structure-sheaf situation `𝒪_X/X/B`: that is the instance Stacks 0D00 provides, but constructing
it is part of Stacks 0D00, so the statement here is the deduction for an arbitrary situation on
the same morphism, which is the source's argument and applies verbatim to the intended instance.

## References

* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A model of the Hilbert presheaf built from a model of the Quot presheaf has the same
morphism to the base.** The two models share their presheaf, and the morphism to the base is read
off through the identifying isomorphism, so the compatibility `he` of that isomorphism with the
two canonical morphisms to the base is exactly what makes the two agree. -/
theorem HilbertPresheafModel.toBase_eq_of_iso {X : AlgebraicSpaces B S hS}
    (D : QuotSituation B S hS) (f : X ⟶ D.Y)
    (N : QuotSitePresheafModel D) (e : hilbertPresheaf f ≅ D.quotSitePresheaf)
    (he : e.hom ≫ D.quotSitePresheafToBase = hilbertPresheafToBase f) :
    (⟨N.presheaf, N.iso ≪≫ e.symm⟩ : HilbertPresheafModel f).toBase = N.toBase := by
  have hinv : e.inv ≫ hilbertPresheafToBase f = D.quotSitePresheafToBase := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  ext T z
  exact congrArg ULift.down (types_congr_hom (congrArg NatTrans.app hinv ▸ rfl :
    (e.inv ≫ hilbertPresheafToBase f).app T = D.quotSitePresheafToBase.app T)
      (N.iso.hom.app T ⟨z⟩))

/-- **Stacks 0D01.** For a morphism `f : X ⟶ B` of algebraic spaces over `S` which is of finite
presentation and separated, the Hilbert functor `Hilb_{X/B}` of Stacks 0CZY is an algebraic space
locally of finite presentation over `B`: there is a model of the Hilbert presheaf in the universe
of the site which is an algebraic space and whose canonical morphism to `B` is locally of finite
presentation.

This is the source's deduction from Stacks 0D00 and Stacks 09TU, both of which are carried as
hypotheses because neither is in the library. Stacks 09TU is `N` together with `halg` and `hlfp`:
a model of the Quot presheaf of a situation on `f` which is an algebraic space whose morphism to
`B` is locally of finite presentation. Stacks 0D00 is `e` together with `he`: an isomorphism of
the Hilbert presheaf with that Quot presheaf, compatible with the two canonical morphisms to `B`.
The source's standing hypotheses that `f` be of finite presentation and separated are recorded as
`_hfp` and `_hsep`; the deduction itself does not consume them, since they enter through
Stacks 09TU, which is carried. The content delivered is the transport: the Quot model is already a
model of the Hilbert presheaf through `e`, and its morphism to `B` is the Hilbert one by
`AlgebraicGeometry.Space.HilbertPresheafModel.toBase_eq_of_iso`. -/
@[stacks 0D01]
theorem exists_hilbertPresheafModel_isAlgebraicSpace {X : AlgebraicSpaces B S hS}
    (D : QuotSituation B S hS) (f : X ⟶ D.Y)
    (_hfp : IsFinitePresentation B S hS f.hom) (_hsep : IsSeparated B S hS f.hom)
    (N : QuotSitePresheafModel D) (halg : IsAlgebraicSpace B S hS N.presheaf)
    (hlfp : IsLocallyOfFinitePresentation B S hS N.toBase)
    (e : hilbertPresheaf f ≅ D.quotSitePresheaf)
    (he : e.hom ≫ D.quotSitePresheafToBase = hilbertPresheafToBase f) :
    ∃ M : HilbertPresheafModel f,
      IsAlgebraicSpace B S hS M.presheaf ∧
        IsLocallyOfFinitePresentation B S hS M.toBase := by
  refine ⟨⟨N.presheaf, N.iso ≪≫ e.symm⟩, halg, ?_⟩
  rw [HilbertPresheafModel.toBase_eq_of_iso D f N e he]
  exact hlfp

end AlgebraicGeometry.Space

end
