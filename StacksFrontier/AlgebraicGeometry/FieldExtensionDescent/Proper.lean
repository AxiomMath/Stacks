module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Basic

/-!
# Tag 0BDF: properness descends along any field extension

Let `k` be a field, `X` a scheme over `k` and `K/k` a field extension. [Stacks Project, Tag 0BDF]
says that `X` is proper over `k` as soon as its base change `X_K` is proper over `K`.

Nothing in the statement is special to fields: `Spec(K) → Spec(k)` is surjective, flat and
quasi-compact, so the assertion is the descent of properness along such a morphism, which is
[Stacks Project, Tag 02L1] — properness is fpqc local on the base. The general statement is
therefore proved first, for a faithfully flat algebra, and the field case is an instance of it,
in the same shape as the finite-type and quasi-separatedness descents of
`StacksFrontier/AlgebraicGeometry/FieldExtensionDescent/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/FieldExtensionDescent/QuasiSeparated.lean`.

## Main results

* `AlgebraicGeometry.isProper_of_faithfullyFlat_baseChange`: properness of a morphism to an
  affine scheme descends along the base change by a faithfully flat algebra.
* `AlgebraicGeometry.isProper_of_fieldExtension`: **[Stacks Project, Tag 0BDF]**.

## Implementation notes

The source introduces Tag 0BDF with the sentence *"the following lemma is a special case of
Descent, Lemma 35.23.16"*, and that lemma is [Stacks Project, Tag 02L1], available here as
`AlgebraicGeometry.isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact`. The route taken
is that special case, so no hypothesis is carried and the statement is the unrestricted one.

The source also gives a self-contained second proof, which descends properness to a finite-type
stage of the presentation `K = colim Aᵢ` ([Stacks Project, Tag 081F]) and then passes to the
residue field of a maximal ideal of `Aᵢ`, finite over `k` by Hilbert's Nullstellensatz. That
route is the one the ample statements of this directory are forced to take, ampleness not being
fpqc local on the base; for properness it would also be weaker as formalized here, since the
available form of Tag 081F,
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`, still carries Chow's
lemma over a quasi-compact quasi-separated base ([Stacks Project, Tag 0202]) as a Noetherian
hypothesis on the stage.

`AlgebraicGeometry.isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact` is a lemma rather
than an instance, so it is introduced into the local context, where it is picked up by the
instance argument of `CategoryTheory.MorphismProperty.of_pullback_snd_of_descendsAlong`. The
covering is `AlgebraicGeometry.surjective_inf_flat_inf_quasiCompact_SpecMap_algebraMap`, which is
stated at exactly the conjunction `(Surjective ⊓ Flat) ⊓ QuasiCompact` that the descent is
indexed by.

## References

* [Stacks Project, Tag 0BDF](https://stacks.math.columbia.edu/tag/0BDF)
* [Stacks Project, Tag 02L1](https://stacks.math.columbia.edu/tag/02L1)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section FaithfullyFlat

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Properness of a morphism to an affine scheme descends along the base change by a faithfully
flat algebra: the spectrum of such an algebra is a surjective flat quasi-compact morphism, and
properness descends along those. -/
public theorem isProper_of_faithfullyFlat_baseChange
    (h : IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))))) :
    IsProper f :=
  have := isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsProper) (Q := (@Surjective ⊓ @Flat) ⊓ @QuasiCompact)
    surjective_inf_flat_inf_quasiCompact_SpecMap_algebraMap h

end FaithfullyFlat

section FieldExtension

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- **[Stacks Project, Tag 0BDF].** Let `k` be a field and `X` a scheme over `k`. If `X_K` is
proper over `K` for some field extension `K/k`, then `X` is proper over `k`.

The field extension is faithfully flat, so `Spec(K) → Spec(k)` is a surjective flat quasi-compact
morphism and the statement is the descent of properness along one; that descent is
[Stacks Project, Tag 02L1], of which the source says this lemma is a special case. -/
@[stacks 0BDF]
public theorem isProper_of_fieldExtension
    (h : IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    IsProper f :=
  isProper_of_faithfullyFlat_baseChange f h

end FieldExtension

end AlgebraicGeometry

end
