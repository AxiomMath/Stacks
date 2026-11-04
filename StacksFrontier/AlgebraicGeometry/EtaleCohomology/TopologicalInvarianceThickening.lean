module

public import StacksFrontier.AlgebraicGeometry.Etale.LiftAcrossClosedImmersion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Une équivalence remarquable de catégories

Let `S` be a scheme and let `S₀ ⊆ S` be a closed subscheme with the same underlying topological
space — for instance one whose ideal sheaf has square zero. Then base change along the closed
immersion `S₀ ⟶ S` is an equivalence from the category of schemes étale over `S` to the category
of schemes étale over `S₀`.

Full faithfulness holds because an étale scheme sees no difference between a scheme and a
thickening of it on morphisms. Essential surjectivity is local: an étale scheme over `S₀` with
affine source over an affine open of `S` is cut out by finitely many equations whose Jacobian
determinant is invertible, and lifting those equations to `S` lifts the étale scheme; the local
lifts are then glued, the glueing being forced because base change is fully faithful.

## Main results

* `Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective` — a closed immersion
  which is surjective on points is a universal homeomorphism.
* `Stacks.Etale.exists_etale_pullback_iso_of_isClosedImmersion_of_surjective` — every scheme étale
  over a closed subscheme with the same underlying space is the base change of a scheme étale over
  the ambient scheme.
* `Stacks.Etale.etalePullback_isEquivalence_of_surjective_isClosedImmersion` — **base change is an
  equivalence between the schemes étale over `S` and the schemes étale over `S₀`.**

## Implementation notes

The categories of étale schemes are Mathlib's `AlgebraicGeometry.Scheme.Etale`, and the functor is
`CategoryTheory.MorphismProperty.Over.pullback` for the étale morphism property; the two instances
it needs are supplied inline in the statement.

Essential surjectivity is assembled from two inputs. The local lifts come from the Zariski-local
form of lifting an étale morphism across a closed immersion, which rests on the lifting of étale
ring maps along a surjection of rings. The glueing is
`Stacks.Etale.exists_etale_pullback_iso_of_descendedOpens_cover`, whose hypothesis is exactly that
every point lies in an open subscheme which is a base change; it is met by the opens cut out by
the members of the local covering.

## References

* [EGA IV, Theorem 18.1.2]
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 025H](https://stacks.math.columbia.edu/tag/025H)
* [Stacks Project, Tag 04FW](https://stacks.math.columbia.edu/tag/04FW)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open AlgebraicGeometry

variable {S₀ S : Scheme.{u}}

/-- A closed immersion which is surjective on points is a universal homeomorphism: it is integral
and universally injective, being a closed immersion, and surjective by hypothesis. -/
theorem universalHomeomorphism_of_isClosedImmersion_of_surjective (i : S₀ ⟶ S)
    [IsClosedImmersion i] (hi : Function.Surjective i.base) : UniversalHomeomorphism i :=
  (universalHomeomorphism_iff_integral_universallyInjective_surjective i).2
    ⟨inferInstance, inferInstance, ⟨hi⟩⟩

/-- **Étale schemes over a thickening lift.** Let `i : S₀ ⟶ S` be a closed immersion which is
surjective on points and let `p : U ⟶ S₀` be étale. Then `U` is, over `S₀`, the base change along
`i` of a scheme étale over `S`. -/
theorem exists_etale_pullback_iso_of_isClosedImmersion_of_surjective (i : S₀ ⟶ S)
    [IsClosedImmersion i] (hi : Function.Surjective i.base) (U : Scheme.{u}) (p : U ⟶ S₀)
    (hp : Etale p) :
    ∃ (V : Scheme.{u}) (q : V ⟶ S) (_ : Etale q) (e : pullback q i ≅ U),
      e.hom ≫ p = pullback.snd q i := by
  have : Etale p := hp
  have : UniversalHomeomorphism i :=
    universalHomeomorphism_of_isClosedImmersion_of_surjective i hi
  obtain ⟨𝒲, V, g, hg, hiso⟩ :=
    exists_etale_openCover_isomorphic_pullback_of_isClosedImmersion.{u, u} i p
  refine exists_etale_pullback_iso_of_descendedOpens_cover i p fun x ↦ ?_
  obtain ⟨j, y, hy⟩ := 𝒲.exists_eq x
  obtain ⟨e, he⟩ := hiso j
  refine ⟨(𝒲.f j).opensRange, ⟨V j, g j, hg j, e.symm ≪≫ (𝒲.f j).isoOpensRange, ?_⟩, ⟨y, hy⟩⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc, ← he, Iso.inv_hom_id_assoc]

/-- **Une équivalence remarquable de catégories.** Let `S₀ ⊆ S` be a closed subscheme with the same
underlying topological space. Base change along the closed immersion is an equivalence from the
category of schemes étale over `S` to the category of schemes étale over `S₀`. -/
@[stacks 039R, ega "IV 18.1.2", sga "3 X 2.0", sga "1 IX 1.7", sga "1 I 5.5" "special case"]
theorem etalePullback_isEquivalence_of_surjective_isClosedImmersion (i : S₀ ⟶ S)
    [IsClosedImmersion i] (hi : Function.Surjective i.base) :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) i := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) i :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show S.Etale ⥤ S₀.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ i).IsEquivalence :=
  have : UniversalHomeomorphism i :=
    universalHomeomorphism_of_isClosedImmersion_of_surjective i hi
  etalePullback_isEquivalence_of_forall_exists_pullback_iso i
    (exists_etale_pullback_iso_of_isClosedImmersion_of_surjective i hi)

end Stacks.Etale

end

end
