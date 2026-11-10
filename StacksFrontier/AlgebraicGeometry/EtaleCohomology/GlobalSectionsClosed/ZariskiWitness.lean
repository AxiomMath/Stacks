module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.PID
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Injectivity
public import StacksFrontier.RingTheory.Henselian.Pair
public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives
public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocallyInjectiveWide

/-!
# A witness for the Zariski hypothesis of Tag 09ZF

Hypothesis (1) of [Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF) asks that
restriction of global sections along `i : Z ⟶ X` be bijective for *every* sheaf of sets on the
Zariski site of `X`, i.e. that `Stacks.EtaleCohomology.zariskiGlobalSectionsMap i F` be bijective
for all `F`. This file constructs morphisms of schemes for which it holds.

The hypothesis is satisfied as soon as both spaces are *local* with a common closed point: there
is a point `z` of `Z` whose only open neighbourhood in `Z` is `Z`, and whose image in `X` has no
open neighbourhood but `X`. Both conditions hold for `Spec` of a local ring, so the hypothesis
holds for `Spec (A/I) ⟶ Spec A` with `A` local — in particular for a henselian pair `(A, I)` with
`A` local, which is the case Gabber's affine analogue of proper base change
([Stacks, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)) is applied to.

Two things are worth recording about what the proof uses. The condition on `X` is not a
convenience but a necessity: by
`Stacks.EtaleCohomology.eq_top_of_zariskiGlobalSectionsMap_surjective` the hypothesis already
forces every open of `X` containing the image of `i` to be everything, which for `Spec A` is the
requirement that `I` lie in the Jacobson radical — one half of being a henselian pair. The other
half, henselianness itself, is *not* used by anything below: it is the étale half of Tag 09ZF that
needs it, and the statements that mention it do so to record which case of the tag they serve.
`Stacks.EtaleCohomology.not_forall_surjective_zariskiGlobalSectionsMap_intQuotient` records a
closed immersion where that necessary condition fails, and with it the hypothesis: the predicate
is not satisfied by every closed immersion.

Both conditions are conditions on one point, and they imply that the two Zariski sites are *local
sites* in the sense of `CategoryTheory.GrothendieckTopology.IsLocalSite` — a terminal object whose
only covering sieve is the trivial one. That weaker property is all the proof consumes on the `Z`
side.

## Main results

* `Stacks.EtaleCohomology.sieve_eq_top_of_mem_of_isLocalPoint` — on a space with a point whose
  only open neighbourhood is the whole space, every covering sieve of an open containing that
  point is the trivial sieve.
* `Stacks.EtaleCohomology.bijective_toSheafify_app_of_isLocalPoint` — the sheafification map of a
  presheaf of sets is bijective on sections over such an open.
* `Stacks.EtaleCohomology.isIso_lanUnit_app_top` — if the only open of `X` containing the image of
  `i` is `X`, the unit of the left Kan extension along `Opens.map i.base` is an isomorphism at the
  top open.
* `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMap_of_isLocalPoint` — **the witness**:
  restriction of global sections along `i` is bijective for every Zariski sheaf of sets as soon as
  `Z` and `X` are local at a point `z` and at its image.
* `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMap_specQuotient` — the witness at
  `Spec (A/I) ⟶ Spec A` for a local ring `A` and a proper ideal `I`.
* `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMap_henselianPair` and
  `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMap_of_henselianPair` — the same
  statement for a henselian pair `(A, I)` with `A` local, in Mathlib's spelling of the pair and in
  this library's.
* `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMap_padicInt` — a dimensioned instance:
  the henselian pair `(ℤ_p, (p))`, whose `X = Spec ℤ_p` has Krull dimension one and whose ideal is
  nonzero.
* `Stacks.EtaleCohomology.not_forall_surjective_zariskiGlobalSectionsMap_intQuotient` — a
  predicted-failure control: the hypothesis fails for `Spec (ℤ/2ℤ) ⟶ Spec ℤ`, a closed immersion
  whose ideal is not in the Jacobson radical, so the witnesses above are not instances of a
  vacuously true predicate.
* `Stacks.EtaleCohomology.eq_of_forall_exists_globalSectionEqAt_henselianPair` and
  `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionsMapAt_henselianPair` — the consequence
  for the étale theory: at a henselian pair with local `A`, the local-agreement criterion for
  equality of étale global sections and the injectivity half of Tag 09ZF hold with no Zariski
  hypothesis left in them.

## Implementation notes

The map of the tag is the component at the top open of the unit of the abstract adjunction
`CategoryTheory.Functor.sheafAdjunctionContinuous`, whose left adjoint is a chosen one. The proof
compares it with the explicit left adjoint "left Kan extension, then sheafify": the two units
differ by the image under the right adjoint of
`CategoryTheory.Adjunction.leftAdjointUniq`, which is an isomorphism, so bijectivity transfers.
For the explicit adjunction the component at the top open is the Kan extension unit followed by
the sheafification map, and each factor is treated separately.

The Kan extension factor is an isomorphism for a reason that is exactly the geometric hypothesis:
the left Kan extension is computed pointwise as a colimit over the opens `U` of `X` whose preimage
contains `Z`, and the hypothesis says that `⊤` is the only such open, i.e. that the index category
of that colimit has a terminal object.

The sheafification factor is bijective because a covering sieve of an open containing the
distinguished point must contain that open itself, so local surjectivity and local injectivity of
the sheafification map become surjectivity and injectivity. Mathlib's instances for those two
constrain the coefficients to the universe generated by the site, while étale cohomology is
written with coefficients in `Type (max (u + 1) v)` for a free `v`; the two statements used here
are `Stacks.Sheafification.isLocallySurjective_toSheafify_type` and
`Stacks.Sheafification.isLocallyInjective_toSheafify_type`, which carry no such constraint.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v

namespace Stacks.EtaleCohomology

section LocalSpace

/-- **A covering sieve of an open containing a local point is trivial.** If the only open
neighbourhood of `t` is the whole space, then a covering sieve of an open containing `t` is the
maximal sieve.

A covering sieve contains some open around `t`, that open is everything, and so is the open it
covers. -/
public theorem sieve_eq_top_of_mem_of_isLocalPoint {T : Type u} [TopologicalSpace T] (t : T)
    (ht : ∀ U : Opens T, t ∈ U → U = ⊤) {V : Opens T} {S : Sieve V}
    (hS : S ∈ Opens.grothendieckTopology T V) (htV : t ∈ V) : S = ⊤ := by
  obtain ⟨U, f, hf, htU⟩ := hS t htV
  have hle : V ≤ U := ht U htU ▸ le_top
  have hmem := S.downward_closed hf (homOfLE hle)
  rwa [Subsingleton.elim (homOfLE hle ≫ f) (𝟙 V), Sieve.id_mem_iff_eq_top] at hmem

/-- **Sheafification does not change the sections over an open containing a local point.** If the
only open neighbourhood of `t` is the whole space, the sheafification map of a presheaf of sets is
bijective on sections over any open containing `t`.

Every covering sieve of such an open is the maximal sieve, so local surjectivity and local
injectivity of the sheafification map give surjectivity and injectivity outright. -/
public theorem bijective_toSheafify_app_of_isLocalPoint {T : Type u} [TopologicalSpace T] (t : T)
    (ht : ∀ U : Opens T, t ∈ U → U = ⊤) [UnivLE.{u, v}]
    (P : (Opens T)ᵒᵖ ⥤ Type v) {V : Opens T} (htV : t ∈ V) :
    Function.Bijective ((toSheafify (Opens.grothendieckTopology T) P).app (op V)) := by
  constructor
  · intro x y hxy
    exact (Presheaf.equalizerSieve_eq_top_iff (F := P) (X := op V) x y).mp
      (sieve_eq_top_of_mem_of_isLocalPoint t ht (Presheaf.equalizerSieve_mem
        (Opens.grothendieckTopology T) (toSheafify (Opens.grothendieckTopology T) P)
        (X := op V) x y hxy) htV)
  · intro s
    have h := sieve_eq_top_of_mem_of_isLocalPoint t ht
      (Presheaf.IsLocallySurjective.imageSieve_mem (J := Opens.grothendieckTopology T)
        (f := toSheafify (Opens.grothendieckTopology T) P) (U := V)
        (show ToType ((sheafify (Opens.grothendieckTopology T) P).obj (op V)) from s)) htV
    obtain ⟨x, hx⟩ := Sieve.id_mem_iff_eq_top.mpr h
    exact ⟨x, by simpa using hx⟩

end LocalSpace

section Witness

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- **The index category of the Kan extension at the top open has a terminal object.** If the only
open of `X` containing the image of `i` is `X` itself, then the identity of the preimage of the top
open is a terminal object of the category of opens of `X` whose preimage contains `Z`.

An object of that category is an open `U` of `X` together with an inclusion of the preimage of the
top open into the preimage of `U`, which says exactly that `U` contains the image of `i`; the
hypothesis makes `U` the top open, so the unique inclusion `⊤ ≤ U` is the required morphism. -/
public def isTerminal_costructuredArrowMkId
    (hstar : ∀ U : X.Opens, Set.range i.base ⊆ (U : Set X.carrier) → U = ⊤) :
    IsTerminal (CostructuredArrow.mk (𝟙 ((Opens.map i.base).op.obj (op (⊤ : X.Opens))))) := by
  refine IsTerminal.ofUniqueHom (fun j => CostructuredArrow.homMk ?_ ?_) ?_
  · refine (homOfLE (le_of_eq (hstar j.left.unop ?_).symm)).op
    rintro x ⟨z, rfl⟩
    exact (leOfHom j.hom.unop) (Set.mem_univ z)
  · exact Subsingleton.elim _ _
  · exact fun _ _ => CostructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)

/-- **The Kan extension unit is an isomorphism at the top open.** If the only open of `X`
containing the image of `i` is `X` itself, then the unit of the left Kan extension along
`Opens.map i.base` of a presheaf of sets on the opens of `X` is bijective at the top open.

The left Kan extension is computed pointwise as a colimit over the opens of `X` whose preimage
contains `Z`, and by `Stacks.EtaleCohomology.isTerminal_costructuredArrowMkId` that category has a
terminal object, at which the colimit inclusion is an isomorphism. -/
public theorem isIso_lanUnit_app_top
    (hstar : ∀ U : X.Opens, Set.range i.base ⊆ (U : Set X.carrier) → U = ⊤)
    (P : (Opens X.carrier)ᵒᵖ ⥤ Type (max (u + 1) v)) :
    IsIso ((((Opens.map i.base).op.lanUnit).app P).app (op (⊤ : X.Opens))) := by
  have h := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      ((Opens.map i.base).op.lan.obj P) (((Opens.map i.base).op.lanUnit).app P)
      ((Opens.map i.base).op.obj (op (⊤ : X.Opens)))
  have h2 := h.isIso_ι_app_of_isTerminal _ (isTerminal_costructuredArrowMkId i hstar)
  simp only [Functor.LeftExtension.coconeAt_ι_app, Functor.LeftExtension.mk_hom,
    Functor.LeftExtension.mk_right, CostructuredArrow.mk_left,
    CostructuredArrow.mk_hom_eq_self] at h2
  rwa [CategoryTheory.Functor.map_id] at h2

/-- The explicit inverse image of Zariski sheaves of sets along `i`, as a left adjoint to the
direct image: the left Kan extension along `Opens.map i.base`, followed by sheafification. -/
private def zariskiInverseImageAdjunction :
    (sheafToPresheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)) ⋙
        (Opens.map i.base).op.lan ⋙
          presheafToSheaf (Opens.grothendieckTopology Z.carrier) (Type (max (u + 1) v))) ⊣
      (Opens.map i.base).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Z.carrier) :=
  (((Opens.map i.base).op.lanAdjunction (Type (max (u + 1) v))).comp
      (sheafificationAdjunction (Opens.grothendieckTopology Z.carrier)
        (Type (max (u + 1) v)))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- The unit of the explicit inverse-image adjunction is, at the top open, the Kan extension unit
followed by the sheafification map. -/
private theorem zariskiInverseImageAdjunction_unit_app_top
    (F : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v))) :
    ((zariskiInverseImageAdjunction.{u, v} i).unit.app F).hom.app (op (⊤ : X.Opens)) =
      ((Opens.map i.base).op.lanUnit.app F.obj).app (op (⊤ : X.Opens)) ≫
        (toSheafify (Opens.grothendieckTopology Z.carrier)
          ((Opens.map i.base).op.lan.obj F.obj)).app
            ((Opens.map i.base).op.obj (op (⊤ : X.Opens))) := by
  have key := Adjunction.map_restrictFullyFaithful_unit_app
      ((((Opens.map i.base).op.lanAdjunction (Type (max (u + 1) v))).comp
        (sheafificationAdjunction (Opens.grothendieckTopology Z.carrier)
          (Type (max (u + 1) v)))))
      (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X.carrier)
        (Type (max (u + 1) v))) (Functor.FullyFaithful.id _)
      (L := sheafToPresheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)) ⋙
        (Opens.map i.base).op.lan ⋙
          presheafToSheaf (Opens.grothendieckTopology Z.carrier) (Type (max (u + 1) v)))
      (R := (Opens.map i.base).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Z.carrier))
      (Iso.refl _) (Iso.refl _) F
  have key2 := NatTrans.congr_app key (op (⊤ : X.Opens))
  simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit] at key2
  exact key2

/-- **The witness for hypothesis (1) of Tag 09ZF.** Let `i : Z ⟶ X` be a morphism of schemes and
let `z` be a point of `Z` such that the only open of `Z` containing `z` is `Z`, and the only open
of `X` containing the image of `z` is `X`. Then restriction of global sections along `i` is
bijective for every sheaf of sets on the Zariski site of `X`.

Both hypotheses are satisfied by `Spec` of a local ring at its closed point, so this inhabits the
predicate — for instance at a henselian pair with local base, see
`Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMap_henselianPair`.

The map is the component at the top open of the unit of the abstract inverse-image/direct-image
adjunction. It agrees, up to an isomorphism coming from the uniqueness of left adjoints, with the
unit of the explicit adjunction "left Kan extension, then sheafify", whose component at the top
open is bijective in two steps: the Kan extension unit is an isomorphism because the colimit
computing it is indexed by a category with a terminal object, and the sheafification map is
bijective because every covering sieve of the preimage of the top open is trivial. -/
public theorem bijective_zariskiGlobalSectionsMap_of_isLocalPoint (z : Z.carrier)
    (hz : ∀ V : Z.Opens, z ∈ V → V = ⊤)
    (hstar : ∀ U : X.Opens, Set.range i.base ⊆ (U : Set X.carrier) → U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v))) :
    Function.Bijective (zariskiGlobalSectionsMap.{u, v} i F) := by
  have hB : Function.Bijective
      ((((Opens.map i.base).op.lanUnit).app F.obj).app (op (⊤ : X.Opens))) :=
    (isIso_iff_bijective _).mp (isIso_lanUnit_app_top.{u, v} i hstar F.obj)
  have hC : Function.Bijective ((toSheafify (Opens.grothendieckTopology Z.carrier)
      ((Opens.map i.base).op.lan.obj F.obj)).app
        ((Opens.map i.base).op.obj (op (⊤ : X.Opens)))) :=
    bijective_toSheafify_app_of_isLocalPoint.{u, max (u + 1) v} z hz _
      (V := (Opens.map i.base).obj (⊤ : X.Opens)) trivial
  have hconc : Function.Bijective
      (((zariskiInverseImageAdjunction.{u, v} i).unit.app F).hom.app (op (⊤ : X.Opens))) := by
    rw [zariskiInverseImageAdjunction_unit_app_top]
    exact hC.comp hB
  have htrans := Adjunction.unit_leftAdjointUniq_hom_app
    ((Opens.map i.base).sheafAdjunctionContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Z.carrier))
    (zariskiInverseImageAdjunction.{u, v} i) F
  have hiso : IsIso ((((Opens.map i.base).sheafPushforwardContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology Z.carrier)).map
        ((Adjunction.leftAdjointUniq
          ((Opens.map i.base).sheafAdjunctionContinuous (Type (max (u + 1) v))
            (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Z.carrier))
          (zariskiInverseImageAdjunction.{u, v} i)).hom.app F)).hom.app
            (op (⊤ : X.Opens))) := by
    infer_instance
  rw [← htrans] at hconc
  exact ((isIso_iff_bijective _).mp hiso).of_comp_iff' _ |>.mp hconc

end Witness

section Spec

/-- An ideal of a local ring contained in the Jacobson radical is proper. -/
private theorem ne_top_of_le_jacobson_bot {A : Type u} [CommRing A] [IsLocalRing A] {I : Ideal A}
    (h : I ≤ (⊥ : Ideal A).jacobson) : I ≠ ⊤ := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  exact fun htop ↦ (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (htop ▸ h))

/-- **The witness at the closed subscheme of a local affine scheme.** For a local ring `A` and a
proper ideal `I`, restriction of global sections along `Spec (A/I) ⟶ Spec A` is bijective for every
sheaf of sets on the Zariski site of `Spec A`.

`Spec` of a local ring has a point — its closed point — lying in no open but the whole space, and
the closed point of `Spec (A/I)` lies over the closed point of `Spec A` because the quotient map is
a local homomorphism. -/
public theorem bijective_zariskiGlobalSectionsMap_specQuotient
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤)
    (F : Sheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A)).carrier)
      (Type (max (u + 1) v))) :
    Function.Bijective (zariskiGlobalSectionsMap.{u, v}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F) := by
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine bijective_zariskiGlobalSectionsMap_of_isLocalPoint _
    (IsLocalRing.closedPoint (A ⧸ I)) (fun V hV ↦ (IsLocalRing.closedPoint_mem_iff V).mp hV)
    (fun U hU ↦ (IsLocalRing.closedPoint_mem_iff U).mp ?_) F
  exact hU ⟨IsLocalRing.closedPoint (A ⧸ I), Spec_closedPoint⟩

/-- **The witness at a henselian pair with local base.** For a henselian pair `(A, I)` with `A`
local and `I` proper, restriction of global sections along `Spec (A/I) ⟶ Spec A` is bijective for
every sheaf of sets on the Zariski site of `Spec A`: hypothesis (1) of
[Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF) is inhabited there.

This is the case to which Gabber's theorem
([Stacks, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)) is applied. The only part of being
a henselian pair that the proof consumes is that `I` lie in the Jacobson radical, which over a
local ring makes `I` proper; the lifting property is recorded in the statement to say which case of
the tag this witness serves, and is used by the étale half of the tag, not here. -/
public theorem bijective_zariskiGlobalSectionsMap_henselianPair
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) [HenselianRing A I]
    (F : Sheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A)).carrier)
      (Type (max (u + 1) v))) :
    Function.Bijective (zariskiGlobalSectionsMap.{u, v}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F) :=
  bijective_zariskiGlobalSectionsMap_specQuotient.{u, v} A I
    (ne_top_of_le_jacobson_bot HenselianRing.jac) F

/-- **The witness at a henselian pair with local base, in this library's spelling of the pair.**
The same statement as `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMap_henselianPair`
with `HenselianPair` of [Stacks, Tag 09XE](https://stacks.math.columbia.edu/tag/09XE) in place of
Mathlib's `HenselianRing`, for consumers written against this library's henselian-pair
development. Again only the Jacobson condition is consumed. -/
public theorem bijective_zariskiGlobalSectionsMap_of_henselianPair
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) (h : HenselianPair A I)
    (F : Sheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A)).carrier)
      (Type (max (u + 1) v))) :
    Function.Bijective (zariskiGlobalSectionsMap.{u, v}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F) :=
  bijective_zariskiGlobalSectionsMap_specQuotient.{u, v} A I
    (ne_top_of_le_jacobson_bot h.le_jacobson) F

/-- **A dimensioned witness.** The `p`-adic integers with their maximal ideal form a henselian
pair — they are `p`-adically complete — and hypothesis (1) of Tag 09ZF holds there. The scheme
`X = Spec ℤ_p` has Krull dimension one and the ideal cut out by `Z = Spec 𝔽_p` is nonzero, so the
witness is neither the empty scheme nor an isomorphism: the two statements recorded alongside the
bijectivity are what rule those out. -/
public theorem bijective_zariskiGlobalSectionsMap_padicInt (p : ℕ) [Fact p.Prime]
    (F : Sheaf (Opens.grothendieckTopology (Spec (CommRingCat.of ℤ_[p])).carrier)
      (Type (max 1 v))) :
    ringKrullDim ℤ_[p] = 1 ∧ IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ ∧
      Function.Bijective (zariskiGlobalSectionsMap.{0, v}
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])))) F) :=
  ⟨IsPrincipalIdealRing.ringKrullDim_eq_one ℤ_[p]
      (IsDiscreteValuationRing.not_isField ℤ_[p]),
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal ℤ_[p])
      (IsDiscreteValuationRing.not_isField ℤ_[p]),
    bijective_zariskiGlobalSectionsMap_henselianPair.{0, v} ℤ_[p]
      (IsLocalRing.maximalIdeal ℤ_[p]) F⟩

/-- **A predicted-failure control: the hypothesis is not satisfied by every closed immersion.**
For `Z = Spec (ℤ/2ℤ) ⟶ X = Spec ℤ` — a closed immersion, but one whose ideal `(2)` does not lie in
the Jacobson radical of `ℤ`, so `(ℤ, (2))` is not a henselian pair — restriction of global
sections is *not* surjective for every sheaf of sets on the Zariski site of `Spec ℤ`.

So the witnesses above are not instances of a vacuously true predicate. The failure is forced by
`Stacks.EtaleCohomology.eq_top_of_zariskiGlobalSectionsMap_surjective`: the basic open of `3`
contains the image of the closed immersion and is not everything, since it misses the prime
`(3)`. -/
public theorem not_forall_surjective_zariskiGlobalSectionsMap_intQuotient :
    ¬ ∀ F : Sheaf (Opens.grothendieckTopology (Spec (CommRingCat.of ℤ)).carrier)
        (Type (max 1 v)),
      Function.Surjective (zariskiGlobalSectionsMap.{0, v}
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {(2 : ℤ)})))) F) := by
  intro hZar
  have hprime : (Ideal.span {(3 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr
      (by rw [Int.prime_iff_natAbs_prime]; decide)
  have hone : Ideal.Quotient.mk (Ideal.span {(2 : ℤ)}) 3 = 1 := by
    rw [show (1 : ℤ ⧸ Ideal.span {(2 : ℤ)}) = Ideal.Quotient.mk _ 1 from (map_one _).symm,
      Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.mpr ⟨1, by ring⟩
  have hrange : Set.range (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {(2 : ℤ)})))).base ⊆
      ((PrimeSpectrum.basicOpen (3 : ℤ) : Opens (PrimeSpectrum ℤ)) : Set (PrimeSpectrum ℤ)) := by
    rintro x ⟨z, rfl⟩
    change (3 : ℤ) ∉ _
    intro hmem
    have hz : (1 : ℤ ⧸ Ideal.span {(2 : ℤ)}) ∈ z.asIdeal := by
      rw [← hone]
      exact hmem
    exact z.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hz)
  have htop := eq_top_of_zariskiGlobalSectionsMap_surjective _ hZar hrange
  have hmem3 : (⟨Ideal.span {(3 : ℤ)}, hprime⟩ : PrimeSpectrum ℤ) ∈
      PrimeSpectrum.basicOpen (3 : ℤ) := htop ▸ trivial
  rw [PrimeSpectrum.mem_basicOpen] at hmem3
  exact hmem3 (Ideal.mem_span_singleton_self _)

/-- **The Zariski hypothesis discharged inside the étale theory.** At a henselian pair `(A, I)`
with `A` local and `I` proper, two global sections of a sheaf of sets on the small étale site of
`Spec A` which agree, near every point of `Spec (A/I)`, over some object of the site whose image
contains that point, are equal.

This is `Stacks.EtaleCohomology.eq_of_forall_exists_globalSectionEqAt` with its Zariski
hypothesis supplied by `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMap_henselianPair`;
nothing about the Zariski site is assumed any more. -/
public theorem eq_of_forall_exists_globalSectionEqAt_henselianPair
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) [HenselianRing A I]
    (F : Sheaf (Scheme.smallEtaleTopology (Spec (CommRingCat.of A)))
      (Type (max (u + 1) v)))
    {a b : F.obj.obj (op (terminal (Spec (CommRingCat.of A)).Etale))}
    (hloc : ∀ z : Spec (CommRingCat.of (A ⧸ I)),
      ∃ W : (Spec (CommRingCat.of A)).Etale, GlobalSectionEqAt F a b W ∧
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base z ∈ smallEtaleImage W) :
    a = b :=
  eq_of_forall_exists_globalSectionEqAt (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (fun G ↦ (bijective_zariskiGlobalSectionsMap_henselianPair.{u, v} A I G).surjective) F hloc

/-- **The injectivity half of Tag 09ZF at a henselian pair, with no Zariski hypothesis left.** At a
henselian pair `(A, I)` with `A` local and `I` proper, the comparison map on étale global sections
along `Spec (A/I) ⟶ Spec A` is injective as soon as two global sections with the same
presheaf-level pullback agree, near every point of `Spec (A/I)`, over some object of the small
étale site whose image contains that point.

This is `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionsMapAt_of_zariski` — the
injectivity reduction of the tag — with its hypothesis (1) supplied by
`Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMap_henselianPair`, so that what remains
conditional is only the étale local-agreement hypothesis. -/
public theorem injective_smallEtaleGlobalSectionsMapAt_henselianPair
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) [HenselianRing A I]
    (g : terminal (Spec (CommRingCat.of (A ⧸ I))).Etale ⟶
      (smallEtaleBaseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
        (terminal (Spec (CommRingCat.of A)).Etale))
    (F : Sheaf (Scheme.smallEtaleTopology (Spec (CommRingCat.of A)))
      (Type (max (u + 1) v)))
    (hloc : ∀ a b : F.obj.obj (op (terminal (Spec (CommRingCat.of A)).Etale)),
      smallEtaleGlobalSectionPullback.{u, v}
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) g F a =
        smallEtaleGlobalSectionPullback.{u, v}
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) g F b →
        ∀ z : Spec (CommRingCat.of (A ⧸ I)), ∃ W : (Spec (CommRingCat.of A)).Etale,
          GlobalSectionEqAt F a b W ∧
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base z ∈ smallEtaleImage W) :
    Function.Injective (smallEtaleGlobalSectionsMapAt.{u, v}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) g F) :=
  injective_smallEtaleGlobalSectionsMapAt_of_zariski _ g F
    (fun G ↦ (bijective_zariskiGlobalSectionsMap_henselianPair.{u, v} A I G).surjective) hloc

end Spec

end Stacks.EtaleCohomology

end
