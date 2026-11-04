module

public import StacksFrontier.RingTheory.Cech.CechColimitCechIso
public import StacksFrontier.RingTheory.Cech.PairCechColimit

/-!
# A complex `K(A, I)` depending only on the pair `(A, I)`, functorially in the ring

[Stacks, Tag 099D] asserts that one can construct, for every commutative ring `A` and every
finitely generated ideal `I ⊆ A`, a complex `K(A, I)` of `A`-modules together with an
augmentation `K(A, I) → A`, and for every ring map `A → B` a map of complexes
`K(A, I) → K(B, IB)`, in such a way that (a) the maps are compatible with the augmentations,
(b) the maps compose, (c) the induced map `K(A, I) ⊗^𝐋_A B → K(B, IB)` is an isomorphism in
`D(B)`, and (d) for `I = (f₁, …, f_r)` the complex `K(A, I)` is identified in `D(A)`, over the
identity of `A`, with the extended alternating Čech complex on `f₁, …, f_r`.

All of that data and all four conditions are the fields of
`Stacks.LocalCohomology.FunctorialCechData`. This file produces a term of it, so the tag is
proved here in full.

## Main results

* `Stacks.LocalCohomology.nonempty_functorialCechData` — **[Stacks, Tag 099D]**: a functorial
  Čech datum exists.
* `Stacks.LocalCohomology.exists_pairCechComplex` — **[Stacks, Tag 099D]**, the same statement
  with the three data and the four conditions written out rather than collected into a
  structure.

## Implementation notes

The construction follows the source's two-step shape. Step 3 builds one complex `𝒦•` of
presheaves of modules on the category of presented pairs `(A₀, I₀)` with `A₀` a finite type
`ℤ`-algebra; its output is `Stacks.PairSite.exists_presentedCechDatum`. Step 2 passes to
arbitrary pairs by the filtered colimit over the presentations `φ : (A₀, I₀) → (A, I)`; its
output is `Stacks.PairSite.exists_functorialCechData`. Conditions (a) and (b) hold on the nose
because the transition maps of step 3 are the restriction maps of a presheaf, and the colimit of
step 2 is taken over a filtered category, so they are inherited.

Step 3 is *not* carried out by the source's own argument. The source chooses an injective
resolution `𝒪 → 𝒥•` of the structure presheaf, sets `ℱ• = ⋃ₙ 𝒥•[ℐⁿ]`, and recognizes `𝒥•(U)` as
an injective resolution of `A` on the ground that the topology is chaotic. That ground is false:
`Stacks.PairSite.exists_injective_not_injective_value` exhibits an injective presheaf of modules
on the category of pairs whose sections at a pair are not an injective module. What
`Stacks.PairSite.exists_presentedCechDatum` uses instead is `Stacks.PairSite.cechComplexPair`,
the degreewise filtered colimit of the extended alternating Čech complexes over the finite
generating families of the ideal of the pair; any two families are dominated by their union, and
the transitions are quasi-isomorphisms, which gives conditions (c) and (d) at the presented
pairs.

The rings of a single datum range over one universe `Type u`, and the statement is universe
polymorphic in `u`. A structure field cannot quantify over universes, so this is the
universe-polymorphic form of the tag's "for every pair `(A, I)`", and the construction is
available in every universe.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- **[Stacks, Tag 099D].** There is a way to construct, for every commutative ring `A` and
every finitely generated ideal `I ⊆ A`, a complex `K(A, I)` of `A`-modules, a map of complexes
of `A`-modules `K(A, I) → A`, and for every ring map `φ : A → B` a map of complexes of
`A`-modules `K(A, I) → K(B, IB)`, such that

* (a) for `A → B` and `I ⊆ A` finitely generated the square formed by the two augmentations,
  the map `K(A, I) → K(B, IB)` and `A → B` commutes;
* (b) for `A → B → C` and `I ⊆ A` finitely generated the composition of
  `K(A, I) → K(B, IB)` and `K(B, IB) → K(C, IC)` is the map `K(A, I) → K(C, IC)`;
* (c) for `A → B` and `I ⊆ A` finitely generated the induced map
  `K(A, I) ⊗^𝐋_A B → K(B, IB)` is an isomorphism in `D(B)`;
* (d) if `I = (f₁, …, f_r) ⊆ A` then the extended alternating Čech complex on `f₁, …, f_r` is
  isomorphic to `K(A, I)` in `D(A)` by an isomorphism commuting with the augmentations onto `A`.

These are exactly the data `complex`, `augmentation`, `map` and the conditions
`map_augmentation`, `map_map`, `isIso_derivedBaseChange`, `exists_cech_iso` of
`Stacks.LocalCohomology.FunctorialCechData`. -/
@[stacks 099D "for every ring A and finitely generated ideal I ⊆ A the complex K(A, I) of \
A-modules, its augmentation K(A, I) → A, and for every ring map A → B the map \
K(A, I) → K(B, IB), compatible with the augmentations and composing on the nose, with \
K(A, I) ⊗^𝐋_A B → K(B, IB) an isomorphism in D(B) and with K(A, I) identified in D(A) over A \
with the extended alternating Čech complex on any finite generating family of I"]
theorem nonempty_functorialCechData : Nonempty FunctorialCechData.{u} :=
  PairSite.exists_presentedCechDatum.{u}.elim PairSite.exists_functorialCechData.{u}

/-- **[Stacks, Tag 099D], with the three data and the four conditions written out.** This is
`Stacks.LocalCohomology.nonempty_functorialCechData` with the fields of
`Stacks.LocalCohomology.FunctorialCechData` unfolded into the statement, so that nothing about
the tag is hidden behind a structure.

The three quantified data are the tag's items (1), (2), (3):

* `K A I hI` is the complex of `A`-modules of item (1). It is a function of the pair `(A, I)`
  alone: no generating family of `I` occurs among its arguments, and `hI : I.FG` is a proof, so
  by proof irrelevance `K A I` is determined by `A` and `I`.
* `aug A I hI : K A I hI ⟶ A[0]` is the map of complexes of item (2).
* `mp A B φ I hI J hJ hφ : K A I hI ⟶ (K B J hJ)|_A` is the map of complexes of `A`-modules of
  item (3), for `J = IB`. The ideal `IB` is passed as a separate `J` with the equation
  `hφ : J = Ideal.map φ I`, which is the same data and lets (b) be stated without transporting
  along `Ideal.map_map`.

The four conjuncts are the tag's conditions (a), (b), (c), (d), in order:

* (a) the square formed by `mp`, the two augmentations and `A → B` commutes;
* (b) `mp` for `A → C` is `mp` for `A → B` followed by `mp` for `B → C`;
* (c) the induced map `K(A, I) ⊗^𝐋_A B → K(B, IB)` is an isomorphism in `D(B)`;
* (d) for **every** finite family `f₁, …, f_r` generating `I` there is an isomorphism in `D(A)`
  from the extended alternating Čech complex on `f₁, …, f_r` to `K(A, I)` carrying its
  augmentation onto the augmentation of `K(A, I)`.

Conditions (a) and (b) are equalities of maps of complexes, not merely of their images in the
derived category, which is what makes `K` a functor on the category of pairs. -/
@[stacks 099D "the complex K(A, I) of A-modules attached to the pair (A, I) alone, its \
augmentation K(A, I) → A, and for every ring map φ : A → B the map of complexes of A-modules \
K(A, I) → K(B, IB), with (a) the augmentation square commuting, (b) the maps composing on the \
nose, (c) K(A, I) ⊗^𝐋_A B → K(B, IB) an isomorphism in D(B), and (d) for every finite \
generating family f₁, …, f_r of I an isomorphism in D(A) over A from the extended alternating \
Čech complex on f₁, …, f_r to K(A, I); the data and the conditions written out in the \
statement"]
theorem exists_pairCechComplex :
    ∃ (K : (A : Type u) → [CommRing A] → (I : Ideal A) → I.FG →
            CochainComplex (ModuleCat.{u} A) ℤ)
      (aug : (A : Type u) → [CommRing A] → (I : Ideal A) → (hI : I.FG) →
            (K A I hI ⟶
              (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
      (mp : (A B : Type u) → [CommRing A] → [CommRing B] → (φ : A →+* B) → (I : Ideal A) →
            (hI : I.FG) → (J : Ideal B) → (hJ : J.FG) → J = I.map φ →
            (K A I hI ⟶ (CochainComplex.restrictScalars φ).obj (K B J hJ))),
      (∀ (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hI : I.FG)
          (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ),
          mp A B φ I hI J hJ hφ ≫ (CochainComplex.restrictScalars φ).map (aug B J hJ) =
            aug A I hI ≫ singleRingHom φ) ∧
      (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C)
          (I : Ideal A) (hI : I.FG) (J : Ideal B) (hJ : J.FG) (L : Ideal C) (hL : L.FG)
          (hφ : J = I.map φ) (hψ : L = J.map ψ),
          mp A C (ψ.comp φ) I hI L hL (by rw [hψ, hφ, Ideal.map_map]) =
            mp A B φ I hI J hJ hφ ≫
              (CochainComplex.restrictScalars φ).map (mp B C ψ J hJ L hL hψ) ≫
                (restrictScalarsCompComplexIso φ ψ).hom.app (K C L hL)) ∧
      (∀ (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hI : I.FG)
          (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ),
          IsIso (derivedBaseChange φ (mp A B φ I hI J hJ hφ))) ∧
      (∀ (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (I : Ideal A) (hI : I.FG),
          Ideal.span (Set.range f) = I →
          ∃ e : extendedCechObject f (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (K A I hI),
            e.hom ≫ DerivedCategory.Q.map (aug A I hI) ≫
                ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
                  (ModuleCat.of A A)).inv =
              extendedCechAugmentationHom f (ModuleCat.of A A)) :=
  nonempty_functorialCechData.{u}.elim fun D =>
    ⟨fun A _ I hI => D.complex A I hI, fun A _ I hI => D.augmentation A I hI,
      fun _ _ _ _ φ I hI J hJ hφ => D.map φ I hI J hJ hφ,
      fun _ _ _ _ φ I hI J hJ hφ => D.map_augmentation φ I hI J hJ hφ,
      fun _ _ _ _ _ _ φ ψ I hI J hJ L hL hφ hψ => D.map_map φ ψ I hI J hJ L hL hφ hψ,
      fun _ _ _ _ φ I hI J hJ hφ => D.isIso_derivedBaseChange φ I hI J hJ hφ,
      fun A _ _ f I hI hf => D.exists_cech_iso A f I hI hf⟩

end Stacks.LocalCohomology

end
