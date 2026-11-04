module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TwoOutOfThreeShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes

/-!
# The two target-side steps of Stacks 0G7E, with the module universe free of the site

Stacks 0G7E — the degreewise pullback of a K-flat complex with flat terms along a morphism of
ringed topoi is again K-flat with flat terms — has two steps which are about the *target* ringed
topos alone and mention no morphism: the terms of a canonical truncation of a complex with flat
terms and flat cycles are flat, and the kernel of a termwise surjective quasi-isomorphism
between K-flat complexes with flat terms is short exact in place, termwise flat, K-flat and
acyclic.

`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackAlongRingedTopoi`
proves both, inside sections whose ringed topoi are at
`AlgebraicGeometry.RingedTopos.{u, u, u}`.  This file proves them with the universe of the
sections of the structure sheaf independent of the two universes of the site, which is what a
consumer at the small étale ringed topos of an algebraic space,
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, needs.

## Main results

* `Stacks.SheafOfModules.KFlatOfSize.isFlat_of_isZero_ofSize`: a zero sheaf of modules is flat.
* `Stacks.SheafOfModules.KFlatOfSize.isFlat_truncLE_X_ofSize`: the terms of `τ_{≤ n}M` are flat
  when the terms and the cycles of `M` are.
* `Stacks.SheafOfModules.KFlatOfSize.kernelSequence_resolution_facts_ofSize`: the four facts
  about the kernel of a resolution.

## Implementation notes

Both proofs are those of the `{u, u, u}` siblings
`Stacks.Sheaves.DerivedPullback.KFlatPullback.isFlat_truncLE_X` and
`kernelSequence_resolution_facts`; only the universe-general spellings of their inputs are
substituted.  Those inputs are all available at independent universes already: Stacks 03EY part (2)
is `Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact`, Stacks 0G7B for the left
complex is `Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_left_of_shortExact`, and the
invariance of flatness under isomorphism is
`Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize`.

`isFlat_of_isZero_ofSize` replaces `AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero`, which
carries `CategoryTheory.SmallCategory` of the site.  It is the zero object of
`Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize` carried along the unique
isomorphism to any other zero object.

## References

* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 0G7B](https://stacks.math.columbia.edu/tag/0G7B)
* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace Stacks.SheafOfModules.KFlatOfSize

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})

/-- **A zero sheaf of modules is flat**, with the module universe independent of the site: it is
isomorphic to the coproduct of the empty family, which
`Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize` exhibits as a flat zero
object. -/
theorem isFlat_of_isZero_ofSize
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (hM : IsZero M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M := by
  obtain ⟨Z, hZ, hflat⟩ := Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize R
  exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize R (hZ.iso hM) hflat

/-- **The terms of a canonical truncation of a complex with flat terms and flat cycles are
flat**, with the module universe independent of the site.  In degree `i < n` the term is `M^i`,
in degree `n` it is the cycles in degree `n`, and above `n` it is zero. -/
theorem isFlat_truncLE_X_ofSize
    (M : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (M.X i))
    (hcyc : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (M.cycles n))
    (n i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) ((M.truncLE n).X i) := by
  rcases lt_trichotomy i n with hi | rfl | hi
  · exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize R
      (M.truncLEXIso n i hi).symm (hflat i)
  · exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize R
      (M.truncLEXIsoCycles i).symm (hcyc i)
  · exact isFlat_of_isZero_ofSize R ((M.truncLE n).isZero_of_isStrictlyLE n i hi)

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).Additive]
  [∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).obj M).Additive]
  [∀ K₁ K₂ : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ,
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **The kernel of a resolution**, with the module universe independent of the site.  Let
`α : L ⟶ K` be a termwise surjective quasi-isomorphism onto a K-flat complex `K` with flat
terms, out of a K-flat `L` with flat terms.  Then the kernel sequence
`0 ⟶ ker α ⟶ L ⟶ K ⟶ 0` is short exact and `ker α` has flat terms (Stacks 03EY), is K-flat
(Stacks 0G7B) and is acyclic. -/
theorem kernelSequence_resolution_facts_ofSize
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (K.X i))
    (hΛflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (L.X i))
    (hΛkflat : Stacks.SheafOfModules.KFlat.KFlat R L)
    (α : L ⟶ K) (hqis : QuasiIso α) (hαepi : Epi α) :
    (ShortComplex.kernelSequence α).ShortExact ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R)
        ((ShortComplex.kernelSequence α).X₁.X i)) ∧
      Stacks.SheafOfModules.KFlat.KFlat R (ShortComplex.kernelSequence α).X₁ ∧
      (ShortComplex.kernelSequence α).X₁.Acyclic := by
  have hS : (ShortComplex.kernelSequence α).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact α) inferInstance hαepi
  refine ⟨hS, fun i ↦ ?_, ?_, hS.acyclic_X₁ hqis⟩
  · exact Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact R
      ((ShortComplex.kernelSequence α).map (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
      (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)) (hΛflat i) (hflatK i)
  · exact Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_left_of_shortExact R
      (ShortComplex.kernelSequence α) hS hflatK hΛkflat hK

end Stacks.SheafOfModules.KFlatOfSize

end

end
