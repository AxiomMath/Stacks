module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange

/-!
# Shrinking to an open on which a morphism is finite étale

Let `f : W ⟶ X` be a finite morphism, locally of finite presentation, and let `Z ⊆ X` be a
subset such that `f` is étale at every point of `f⁻¹(Z)`. Then there is an open `V ⊆ X`
containing `Z` over which `f` is étale, hence finite étale: the locus of étaleness is open in
`W` (`AlgebraicGeometry.isOpen_setOf_etaleAt`), its complement is closed, and a finite morphism
is closed, so the image of that complement is closed and its complement in `X` is the open `V`
wanted.

Combined with part (2) of [Stacks, Tag 0A43]
(`AlgebraicGeometry.etaleAt_of_etale_infinitesimalNeighbourhoods`) this is the last step of the
construction in the proof of [Stacks, Tag 0EK1]: once the relative spectrum of the algebraized
tower is known to be finite locally free over a neighbourhood `V` of the closed subscheme and to
restrict to the étale covers `U_n ⟶ Z_n` over the infinitesimal neighbourhoods, it is étale at
the points over `Z`, and shrinking `V` makes it finite étale.

## Main results

* `AlgebraicGeometry.exists_isOpen_etale_morphismRestrict_of_etaleAt` — the shrinking step.
* `AlgebraicGeometry.exists_isOpen_finiteEtale_of_etale_infinitesimalNeighbourhoods` — the
  shrinking step fed by [Stacks, Tag 0A43]: a finite morphism locally of finite presentation
  whose base change to every infinitesimal neighbourhood of a closed subscheme `Z` is étale is
  finite étale over some open neighbourhood of `Z`.

## References

* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Shrinking the base so that a finite morphism becomes étale.** Let `f : W ⟶ X` be finite and
locally of finite presentation and let `Z ⊆ X` be a subset at every preimage of which `f` is
étale. Then `f` is étale over some open neighbourhood of `Z`.

The étale locus of `f` is open, so its complement is closed in `W`; a finite morphism is closed,
so the image of that complement is closed in `X`, and `V` is taken to be its complement. No point
of `Z` lies in that image, because a preimage of a point of `Z` is a point of étaleness; and every
point of `W` over `V` is a point of étaleness, which is étaleness of the restriction by part (2)
of the étale-locus base-change criterion, applied to the pullback square defining `f ∣_ V` and the
flatness of the open immersion `V ⟶ X`. -/
public theorem exists_isOpen_etale_morphismRestrict_of_etaleAt {W X : Scheme.{u}} (f : W ⟶ X)
    [IsFinite f] [LocallyOfFinitePresentation f] (Z : Set X)
    (hZ : ∀ w : W, f.base w ∈ Z → EtaleAt f w) :
    ∃ V : X.Opens, Z ⊆ (V : Set X) ∧ Etale (f ∣_ V) := by
  have hEopen : IsOpen {w : W | EtaleAt f w} := isOpen_setOf_etaleAt f
  have hclosed : IsClosed (f.base '' {w : W | EtaleAt f w}ᶜ) :=
    Scheme.Hom.isClosedMap f _ hEopen.isClosed_compl
  refine ⟨⟨(f.base '' {w : W | EtaleAt f w}ᶜ)ᶜ, hclosed.isOpen_compl⟩, ?_, ?_⟩
  · rintro z hz ⟨w, hw, hfw⟩
    exact hw (hZ w (hfw ▸ hz))
  · rw [etale_iff_forall_etaleAt]
    intro w
    refine (etaleAt_iff_of_isPullback
      (isPullback_morphismRestrict f ⟨(f.base '' {w : W | EtaleAt f w}ᶜ)ᶜ,
        hclosed.isOpen_compl⟩).flip (Or.inr inferInstance) w).mp ?_
    by_contra hcon
    exact w.2 ⟨_, hcon, rfl⟩

/-- **A finite morphism that is étale over every infinitesimal neighbourhood of a closed
subscheme is finite étale over an open neighbourhood of it.** Part (2) of [Stacks, Tag 0A43]
makes `f` étale at every point over the closed subscheme, and
`AlgebraicGeometry.exists_isOpen_etale_morphismRestrict_of_etaleAt` shrinks the base. The
restriction stays finite because finiteness is stable under base change, so the restriction is
finite étale. -/
public theorem exists_isOpen_finiteEtale_of_etale_infinitesimalNeighbourhoods
    {W X Z : Scheme.{u}} [IsLocallyNoetherian X] (f : W ⟶ X) (i : Z ⟶ X) [IsFinite f]
    [LocallyOfFinitePresentation f] [IsClosedImmersion i]
    (hetale : ∀ n : ℕ, Etale (pullback.snd f (Stacks.Thickenings.nthOrderToBase i n))) :
    ∃ V : X.Opens, Set.range i.base ⊆ (V : Set X) ∧ finiteEtale (f ∣_ V) := by
  obtain ⟨V, hV, hetaleV⟩ :=
    exists_isOpen_etale_morphismRestrict_of_etaleAt f (Set.range i.base)
      fun w hw => etaleAt_of_etale_infinitesimalNeighbourhoods f i hetale w hw
  exact ⟨V, hV, ⟨inferInstance, hetaleV⟩⟩

end AlgebraicGeometry

end
