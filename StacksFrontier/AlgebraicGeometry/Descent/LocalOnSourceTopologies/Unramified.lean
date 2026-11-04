module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Unramifiedness is local on the source for the étale topology

Both unramifiedness and G-unramifiedness of a morphism of schemes can be checked after
precomposing with the members of an étale covering of the source.

These are instances of the étale case of Tag 036H. Unramifiedness is the conjunction of formal
unramifiedness and local finite type, and G-unramifiedness that of formal unramifiedness and
local finite presentation, so both are Zariski local on the source and on the target, and both
are preserved by precomposition with an étale morphism. The affine descent hypothesis splits
along the same conjunction: the finiteness half is Tag 0367 for finite type and Tag 02KK for
finite presentation, and the formal half is descent of the vanishing of the module of
differentials along a faithfully flat étale ring map.

That last statement is the only new input. For `R → A → B` with `A → B` étale, the canonical
map `B ⊗_A Ω_{A/R} → Ω_{B/R}` is an isomorphism, so `Ω_{B/R} = 0` forces `B ⊗_A Ω_{A/R} = 0`,
and faithful flatness of `B` over `A` then forces `Ω_{A/R} = 0`.

## Main results

* `RingHom.formallyUnramified_of_comp_of_faithfullyFlat_of_etale`: formal unramifiedness
  descends along a faithfully flat étale ring map.
* `AlgebraicGeometry.unramified_isLocalAtSource`: **Stacks 03YV**, unramified case.
* `AlgebraicGeometry.gUnramified_isLocalAtSource_etale`: **Stacks 03YV**, G-unramified case.

## Implementation notes

Unramifiedness and G-unramifiedness of morphisms of schemes are
`AlgebraicGeometry.Unramified` and `AlgebraicGeometry.GUnramified`; the ring-homomorphism
properties they are the affine-local properties of are the two conjunctions above. Étale
coverings of the source are the families of `AlgebraicGeometry.Scheme.etalePrecoverage`.

The two `AlgebraicGeometry.HasRingHomProperty` instances are supplied by name rather than by
synthesis, because the ring-homomorphism property they are indexed by is not an output
parameter.

## References

* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 03YV](https://stacks.math.columbia.edu/tag/03YV)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

/-- Formal unramifiedness descends along a faithfully flat étale ring map: if `R → B` is
formally unramified, `A → B` is faithfully flat and étale and `R → B` factors through `A`, then
`R → A` is formally unramified.

The module of differentials `Ω_{B/R}` is the base change of `Ω_{A/R}` along the étale map
`A → B`, so it vanishes only if `B ⊗_A Ω_{A/R}` does, and `B` is faithfully flat over `A`. -/
theorem RingHom.formallyUnramified_of_comp_of_faithfullyFlat_of_etale
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] (φ : R →+* A) (ψ : A →+* B)
    (hcomp : (ψ.comp φ).FormallyUnramified) (hff : ψ.FaithfullyFlat) (hψ : ψ.Etale) :
    φ.FormallyUnramified := by
  let : Algebra R A := φ.toAlgebra
  let : Algebra A B := ψ.toAlgebra
  let : Algebra R B := (ψ.comp φ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FormallyUnramified R B := hcomp
  have : Module.FaithfullyFlat A B := hff
  have : Algebra.Etale A B := hψ
  refine ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B
    (N := Ω[A⁄R])).mp ?_⟩
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).toEquiv.subsingleton

namespace AlgebraicGeometry

/-- An étale morphism of schemes is G-unramified. -/
theorem GUnramified.of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] : GUnramified f :=
  (gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified f).mpr
    ⟨inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 03YV, unramified case.** Unramifiedness of morphisms of schemes is
local on the source for the étale topology. -/
@[stacks 03YV "unramified"]
instance unramified_isLocalAtSource :
    MorphismProperty.IsLocalAtSource (@Unramified.{u}) Scheme.etalePrecoverage := by
  have hrh : HasRingHomProperty (@Unramified.{u})
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        f.FormallyUnramified ∧ f.FiniteType) := hasRingHomProperty_unramified
  have : IsZariskiLocalAtSource (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : IsZariskiLocalAtTarget (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Unramified.{u})
  have : MorphismProperty.RespectsLeft (@Unramified.{u}) (@Etale.{u}) :=
    ⟨fun g hg f hf ↦ by
      have : Etale g := hg
      exact MorphismProperty.comp_mem _ g f (unramified_of_etale g) hf⟩
  refine isLocalAtSource_etale_of_affine_descent _ ?_
  intro X' X Y _ _ _ g f hsurj hetale hcomp
  have : Surjective g := hsurj
  have : Etale g := hetale
  have hQcomp := HasRingHomProperty.appTop (P := @Unramified.{u}) (g ≫ f) hcomp
  have hff : g.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨inferInstance, inferInstance⟩
  have hge : g.appTop.hom.Etale := HasRingHomProperty.appTop (P := @Etale) g inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Unramified.{u})]
  refine ⟨RingHom.formallyUnramified_of_comp_of_faithfullyFlat_of_etale
    f.appTop.hom g.appTop.hom ?_ hff hge,
    RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation ?_ hff
      hge.finitePresentation⟩
  · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using hQcomp.1
  · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using hQcomp.2

/-- **Stacks Project, Tag 03YV, G-unramified case.** G-unramifiedness of morphisms of schemes
is local on the source for the étale topology. -/
@[stacks 03YV "g_unramified", sga "4 IV 8.5.5" "special case"]
instance gUnramified_isLocalAtSource_etale :
    MorphismProperty.IsLocalAtSource (@GUnramified.{u}) Scheme.etalePrecoverage := by
  have hrh : HasRingHomProperty (@GUnramified.{u})
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        f.FormallyUnramified ∧ f.FinitePresentation) := hasRingHomProperty_gUnramified
  have : IsZariskiLocalAtSource (@GUnramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : IsZariskiLocalAtTarget (@GUnramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @GUnramified.{u})
  have : MorphismProperty.RespectsLeft (@GUnramified.{u}) (@Etale.{u}) :=
    ⟨fun g hg f hf ↦ by
      have : Etale g := hg
      exact MorphismProperty.comp_mem _ g f (GUnramified.of_etale g) hf⟩
  refine isLocalAtSource_etale_of_affine_descent _ ?_
  intro X' X Y _ _ _ g f hsurj hetale hcomp
  have : Surjective g := hsurj
  have : Etale g := hetale
  have hQcomp := HasRingHomProperty.appTop (P := @GUnramified.{u}) (g ≫ f) hcomp
  have hff : g.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨inferInstance, inferInstance⟩
  have hge : g.appTop.hom.Etale := HasRingHomProperty.appTop (P := @Etale) g inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @GUnramified.{u})]
  refine ⟨RingHom.formallyUnramified_of_comp_of_faithfullyFlat_of_etale
    f.appTop.hom g.appTop.hom ?_ hff hge,
    RingHom.finitePresentation_of_comp_of_faithfullyFlat f.appTop.hom g.appTop.hom ?_ hff
      hge.finitePresentation⟩
  · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using hQcomp.1
  · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using hQcomp.2

end AlgebraicGeometry

end
