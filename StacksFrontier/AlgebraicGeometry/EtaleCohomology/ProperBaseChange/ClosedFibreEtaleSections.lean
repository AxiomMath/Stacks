module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Glue
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair

/-!
# Étale global sections of a proper scheme over a henselian pair are read off the closed fibre

Let `(A, I)` be a henselian pair, let `f : X ⟶ Spec A` be proper and let
`i : Z ⟶ X` be the closed immersion of the closed fibre `Z = X ×_{Spec A} Spec (A ⧸ I)`.
[Stacks, Tag 0A0C] asserts that for every sheaf of sets `ℱ` on the small étale site of `X` the
canonical comparison `Γ(X, ℱ) ⟶ Γ(Z, i_{small}^{-1}ℱ)` is bijective.

The **injectivity** half is proved here outright, with no hypothesis beyond the henselian pair
and properness.  The source deduces the whole tag from [Stacks, Tag 09ZF] and
[Stacks, Tag 0A0B], and the hypothesis of Tag 09ZF that Tag 0A0B supplies — bijectivity of
restriction of global sections along `i` for *every* sheaf of sets on the Zariski site of `X` —
is not available in the import closure of this file.  But injectivity does not need it.
Everything the library's reduction of Tag 09ZF consumes of that hypothesis is its consequence
`Stacks.EtaleCohomology.eq_top_of_zariskiGlobalSectionsMap_surjective`: *the only open of `X`
containing the closed fibre is `X` itself*.  Over a henselian pair that statement is
unconditional:  `I` lies in the Jacobson radical of `A`, so `V(I)` meets every nonempty closed
subset of `Spec A`, and `f` being closed carries this up to `X`
(`AlgebraicGeometry.subset_of_isClosed_of_forall_mem_zeroLocus`).  The equality locus of two
global sections of an étale sheaf is open and, by local agreement over the closed fibre, contains
it;  hence it is all of `X` and the sections are equal.

**Surjectivity** is carried here as the named hypothesis `hsurj`.  It is the surjectivity half
of [Stacks, Tag 09ZF], whose proof passes to a finite surjective `X' ⟶ X` which Zariski-locally
factors through a given étale covering family ([Stacks, Tag 09Z0]) and descends sections of an
étale sheaf of sets along a surjective integral morphism ([Stacks, Tag 09Z3]), consuming
hypothesis (2) of Tag 09ZF — stability of hypothesis (1) under every finite base change, which
over a henselian pair is Tag 0A0B again, every scheme finite over `X` being proper over `Spec A`.
A sharper form of the same input is
`Stacks.EtaleCohomology.surjective_smallEtaleGlobalSectionPullback_of_exists_compatible`, which
asks only that each global section of the inverse image admit a *compatible* presenting family.

[Stacks, Tag 0A0C] itself, with no hypothesis, is
`Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_henselianPair_of_isProper`
in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreEtaleSectionsProper`,
which supplies both Zariski hypotheses of Tag 09ZF from Tag 0A0B.  It lives there and not here
because Tag 0A0B rests on the theorem on formal functions:  importing it into this file would
enlarge the import closure of every module built on this one.

## Main results

* `Stacks.EtaleCohomology.eq_of_forall_exists_globalSectionEqAt_of_eq_top`,
  `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionPullback_of_eq_top` and
  `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionsMapAt_of_eq_top`: the injectivity
  half of Tag 09ZF with hypothesis (1) replaced by the only consequence of it that the argument
  uses, namely that the sole open of `X` containing the image of `i` is `X`.
* `AlgebraicGeometry.eq_top_of_preimage_zeroLocus_subset_of_henselianPair` and
  `AlgebraicGeometry.eq_top_of_range_closedFibre_subset_of_henselianPair`: for a closed morphism
  to the spectrum of a henselian pair, that hypothesis holds — the only open of `X` containing
  the closed fibre is `X`.
* `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionPullback_closedFibre_of_henselianPair`,
  `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianPair`
  and
  `Stacks.EtaleCohomology.injective_globalSectionsComparison_app_closedFibre_of_henselianPair`:
  the injectivity half of Tag 0A0C, unconditionally.
* `Stacks.EtaleCohomology.bijective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianPair`
  and `Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_henselianPair`:
  the statement of Tag 0A0C, with the surjectivity half of Tag 09ZF carried as the named
  hypothesis `hsurj`.  Tag 0A0C without it is
  `Stacks.EtaleCohomology.isIso_globalSectionsComparison_closedFibre_of_henselianPair_of_isProper`.

## Implementation notes

The closed fibre is presented as `pullback f (Spec.map (Ideal.Quotient.mk I))` with `i` its first
projection, the presentation used by the Zariski statement
`AlgebraicGeometry.bijective_globalSectionsRestriction_closedFibre_of_henselianPair` and by
[Stacks, Tag 0CT9] in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair`.

**Why Tag 0A0B is not used.**  The library's Zariski statement, Tag 09ZG in
`Stacks.bijective_globalSectionsRestriction_of_isConnected_inter_closure` and Tag 0A0B on top of
it, is about sheaves of sets valued in the universe `Type u` of the space.  Hypothesis (1) of
Tag 09ZF as the étale theory needs it is about sheaves valued in `Type (max (u + 1) v)`, the
coefficient universe of étale cohomology, which is where the small étale site — objects in
`Type (u + 1)` — forces sheafification to land.  The two are different universes and no
implication between them is formal, so Tag 0A0B cannot discharge hypothesis (1) here however it
is bridged;  a `ULift` of the space to `Type (max (u + 1) v)` and a comparison of
`Stacks.globalSectionsRestriction` with `Stacks.EtaleCohomology.zariskiGlobalSectionsMap` would
be needed.  The route taken here avoids the question: hypothesis (1) is replaced by its
topological consequence, which is universe-free.

Only closedness of `f` is used, so the two `eq_top` lemmas are stated for `IsClosedMap f.base`;
properness enters the statements of the tag through the instance.

## References

* [Stacks Project, Tag 0A0C](https://stacks.math.columbia.edu/tag/0A0C)
* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
* [Stacks Project, Tag 09ZG](https://stacks.math.columbia.edu/tag/09ZG)
* [Stacks Project, Tag 0A0B](https://stacks.math.columbia.edu/tag/0A0B)
* [Stacks Project, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0)
* [Stacks Project, Tag 09Z3](https://stacks.math.columbia.edu/tag/09Z3)
* [Stacks Project, Tag 09XD](https://stacks.math.columbia.edu/tag/09XD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v

namespace Stacks.EtaleCohomology

/-! ### The injectivity half of Tag 09ZF without hypothesis (1) -/

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- **Local agreement near the closed subscheme implies equality, from the only consequence of
hypothesis (1) of [Stacks, Tag 09ZF] that is needed.**  If the only open of `X` containing the
image of `i : Z ⟶ X` is `X` itself, then two global sections of a sheaf of sets on the small
étale site of `X` which agree, near every point of `Z`, over some object of the site whose image
contains that point, are equal.

This is `Stacks.EtaleCohomology.eq_of_forall_exists_globalSectionEqAt` with the Zariski
hypothesis replaced by what that lemma extracts from it through
`Stacks.EtaleCohomology.eq_top_of_zariskiGlobalSectionsMap_surjective`. -/
public theorem eq_of_forall_exists_globalSectionEqAt_of_eq_top
    (hstar : ∀ U : X.Opens, Set.range i.base ⊆ (U : Set X.carrier) → U = ⊤)
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
    {a b : F.obj.obj (op (terminal X.Etale))}
    (hloc : ∀ z : Z, ∃ W : X.Etale,
      GlobalSectionEqAt F a b W ∧ i.base z ∈ smallEtaleImage W) :
    a = b := by
  refine eq_of_globalSectionEqOpen_eq_top F (hstar _ ?_)
  rintro x ⟨z, rfl⟩
  exact (mem_globalSectionEqOpen_iff F a b _).mpr (hloc z)

variable (g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale))
  (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))

/-- **The injectivity half of [Stacks, Tag 09ZF] for the presheaf-level pullback, without
hypothesis (1).**  If the only open of `X` containing the image of `i` is `X`, the presheaf-level
pullback of global sections along `i` is injective:  two global sections with the same pullback
agree near every point of `Z` by
`Stacks.EtaleCohomology.exists_globalSectionEqAt_of_pullback_eq`. -/
public theorem injective_smallEtaleGlobalSectionPullback_of_eq_top
    (hstar : ∀ U : X.Opens, Set.range i.base ⊆ (U : Set X.carrier) → U = ⊤) :
    Function.Injective (smallEtaleGlobalSectionPullback.{u, v} i g F) := fun _ _ hab ↦
  eq_of_forall_exists_globalSectionEqAt_of_eq_top.{u, v} i hstar F
    (exists_globalSectionEqAt_of_pullback_eq i g F hab)

/-- **The injectivity half of [Stacks, Tag 09ZF] without hypothesis (1).**  If the only open of
`X` containing the image of `i` is `X`, the comparison map of Tag 09ZF on étale global sections
is injective. -/
public theorem injective_smallEtaleGlobalSectionsMapAt_of_eq_top
    (hstar : ∀ U : X.Opens, Set.range i.base ⊆ (U : Set X.carrier) → U = ⊤) :
    Function.Injective (smallEtaleGlobalSectionsMapAt.{u, v} i g F) :=
  (injective_smallEtaleGlobalSectionsMapAt_iff i g F).mpr
    (injective_smallEtaleGlobalSectionPullback_of_eq_top.{u, v} i g F hstar)

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

/-! ### No room outside the closed fibre of a proper morphism over a henselian pair -/

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **Over a henselian pair there is no room outside the closed fibre.**  Let `(A, I)` be a
henselian pair and let `f : X ⟶ Spec A` be a closed map — a proper, or merely universally closed,
morphism.  Then the only open of `X` containing the closed fibre `f ⁻¹' V(I)` is `X` itself.

The complement of such an open is closed with closed image in `Spec A`, and a nonempty closed
subset of `Spec A` meets `V(I)` because `I` lies in the Jacobson radical of `A`
([Stacks, Tag 09XD]);  a point of the complement over `V(I)` would then lie in the open. -/
public theorem eq_top_of_preimage_zeroLocus_subset_of_henselianPair (hI : HenselianPair A I)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (hf : IsClosedMap f.base) {U : X.Opens}
    (hU : f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆ (U : Set X.carrier)) : U = ⊤ :=
  top_le_iff.mp fun x _ ↦
    subset_of_isClosed_of_forall_mem_zeroLocus I hI f hf isClosed_univ U.isOpen
      (fun _ hx _ ↦ hU hx) (Set.mem_univ x)

/-- **Over a henselian pair there is no room outside the closed fibre, for the closed fibre as a
fibre product.**  The version of
`AlgebraicGeometry.eq_top_of_preimage_zeroLocus_subset_of_henselianPair` phrased for the image of
the closed immersion `X ×_{Spec A} Spec (A ⧸ I) ⟶ X`, which is the presentation of the closed
fibre used by [Stacks, Tag 0A0B] and [Stacks, Tag 0A0C]. -/
public theorem eq_top_of_range_closedFibre_subset_of_henselianPair (hI : HenselianPair A I)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (hf : IsClosedMap f.base) (U : X.Opens)
    (hU : Set.range (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base ⊆ (U : Set X.carrier)) :
    U = ⊤ := by
  refine eq_top_of_preimage_zeroLocus_subset_of_henselianPair I hI f hf ?_
  rw [show f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)
      = Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base from
    by rw [Scheme.Pullback.range_fst, range_spec_map_quotient_mk I]]
  exact hU

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-! ### Tag 0A0C -/

variable {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A))

/-- **The injectivity half of [Stacks, Tag 0A0C].**  Let `(A, I)` be a henselian pair and let
`f : X ⟶ Spec A` be proper.  The presheaf-level pullback of global sections of a sheaf of sets on
the small étale site of `X` to the closed fibre `X ×_{Spec A} Spec (A ⧸ I)` is injective.

No hypothesis is carried:  two global sections with the same pullback agree near every point of
the closed fibre, so their equality locus is an open containing the closed fibre, and over a
henselian pair the only such open is `X`. -/
public theorem injective_smallEtaleGlobalSectionPullback_closedFibre_of_henselianPair
    (hI : HenselianPair A I) [IsProper f]
    (g : terminal (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Etale ⟶
      (smallEtaleBaseChange (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).obj (terminal X.Etale))
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    Function.Injective (smallEtaleGlobalSectionPullback.{u, v}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) g F) :=
  injective_smallEtaleGlobalSectionPullback_of_eq_top.{u, v} _ g F
    (eq_top_of_range_closedFibre_subset_of_henselianPair I hI f f.isClosedMap)

/-- **The injectivity half of [Stacks, Tag 0A0C].**  Let `(A, I)` be a henselian pair and let
`f : X ⟶ Spec A` be proper.  The comparison map from global sections of a sheaf of sets on the
small étale site of `X` to global sections of its inverse image on the closed fibre
`X ×_{Spec A} Spec (A ⧸ I)` is injective.  No hypothesis is carried. -/
public theorem injective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianPair
    (hI : HenselianPair A I) [IsProper f]
    (g : terminal (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Etale ⟶
      (smallEtaleBaseChange (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).obj (terminal X.Etale))
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    Function.Injective (smallEtaleGlobalSectionsMapAt.{u, v}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) g F) :=
  injective_smallEtaleGlobalSectionsMapAt_of_eq_top.{u, v} _ g F
    (eq_top_of_range_closedFibre_subset_of_henselianPair I hI f f.isClosedMap)

/-- **The injectivity half of [Stacks, Tag 0A0C], for the canonical comparison.**  For a
henselian pair `(A, I)` and a proper `f : X ⟶ Spec A`, the component at `F` of
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageComparison` along the closed fibre is
injective. -/
public theorem injective_globalSectionsComparison_app_closedFibre_of_henselianPair
    (hI : HenselianPair A I) [IsProper f]
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    Function.Injective ((globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).val.app F) := by
  rw [(globalSectionsSmallEtaleInverseImageComparison.{u, v}
    (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).2 F
      ((isTerminalSmallEtaleBaseChangeObj _ terminalIsTerminal).from _)]
  exact injective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianPair.{u, v} I f hI _ F

/-- **[Stacks, Tag 0A0C], with the surjectivity half of [Stacks, Tag 09ZF] carried as the named
hypothesis `hsurj`.**  Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be proper.  Then
the comparison map from global sections of a sheaf of sets `F` on the small étale site of `X` to
global sections of its inverse image on the closed fibre `Z = X ×_{Spec A} Spec (A ⧸ I)` is
bijective:  `Γ(X, F) = Γ(Z, i_{small}^{-1}F)`.

Injectivity is proved here from the henselian pair alone.  `hsurj` is surjectivity of the
presheaf-level pullback, the half of Tag 09ZF that rests on [Stacks, Tag 09Z0] and
[Stacks, Tag 09Z3] and consumes hypothesis (2) of that tag.  [Stacks, Tag 0A0C] with no
hypothesis is `isIso_globalSectionsComparison_closedFibre_of_henselianPair_of_isProper`. -/
public theorem bijective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianPair
    (hI : HenselianPair A I) [IsProper f]
    (hsurj : ∀ (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
      (g : terminal (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Etale ⟶
        (smallEtaleBaseChange (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).obj (terminal X.Etale)),
      Function.Surjective (smallEtaleGlobalSectionPullback.{u, v}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) g F))
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
    (g : terminal (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Etale ⟶
      (smallEtaleBaseChange (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).obj (terminal X.Etale)) :
    Function.Bijective (smallEtaleGlobalSectionsMapAt.{u, v}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) g F) :=
  ⟨injective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianPair.{u, v} I f hI g F,
    (surjective_smallEtaleGlobalSectionsMapAt_iff.{u, v} _ g F).mpr (hsurj F g)⟩

/-- **[Stacks, Tag 0A0C], with the surjectivity half of [Stacks, Tag 09ZF] carried as the named
hypothesis `hsurj`.**  Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be proper.  The
canonical comparison
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageComparison` from global sections on
`X` to global sections on the closed fibre `Z = X ×_{Spec A} Spec (A ⧸ I)` of the étale inverse
image is an isomorphism:  `Γ(X, F) = Γ(Z, i_{small}^{-1}F)` for every sheaf of sets `F` on the
small étale site of `X`, naturally in `F`.

The source proves the tag from Tag 09ZF and [Stacks, Tag 0A0B].  Hypothesis (1) of Tag 09ZF,
which is what Tag 0A0B supplies, is *not* used:  injectivity needs only that the sole open of `X`
containing the closed fibre is `X`, which over a henselian pair is unconditional.  What is
carried is the surjectivity half of Tag 09ZF, through [Stacks, Tag 09Z0] and
[Stacks, Tag 09Z3];  see the module documentation.  [Stacks, Tag 0A0C] with no hypothesis, which
carries the tag, is `isIso_globalSectionsComparison_closedFibre_of_henselianPair_of_isProper`. -/
public theorem isIso_globalSectionsComparison_closedFibre_of_henselianPair
    (hI : HenselianPair A I) [IsProper f]
    (hsurj : ∀ (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
      (g : terminal (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Etale ⟶
        (smallEtaleBaseChange (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).obj (terminal X.Etale)),
      Function.Surjective (smallEtaleGlobalSectionPullback.{u, v}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) g F)) :
    IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, v}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).val :=
  (isIso_globalSectionsSmallEtaleInverseImageComparison_iff.{u, v} _).mpr fun F g ↦
    bijective_smallEtaleGlobalSectionsMapAt_closedFibre_of_henselianPair.{u, v} I f hI hsurj F g

end Stacks.EtaleCohomology

end
