module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.FlatInvariants
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.StabilizerBaseChangeMorphism
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.StrictlyHenselianEtaleAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.IsoInvariance
public import StacksFrontier.AlgebraicGeometry.Scheme.ClosedPointSpecSurjection

/-!
# The Claim of Tag 0DT9 on the tensor product presentation of the base change

Let `F : G' ⟶ G` be a morphism of affine groupoid schemes with finite locally free source and
target maps and étale map on object schemes, write `C` and `C'` for the two rings of invariant
functions, and let `C ⟶ C₁` be a flat extension of `C` with `C₁` **strictly henselian local**.
This file transports the "Claim" of [Stacks Project, Tag 0DT9] —
`AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_invariantRingMap_of_strictlyHenselian`, proved
for a morphism whose own invariant ring downstairs is strictly henselian — onto the map
`C₁ ⟶ C' ⊗[C] C₁` of `AlgebraicGeometry.GroupoidScheme.tensorBaseRingMap`.

This is the form in which the source text uses the Claim: the strictly henselian base there is
not the invariant ring of the groupoid at hand but a strict henselization of it, and the groupoid
over that base is the base change.

## Main results

* `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_of_strictlyHenselian_of_bijective`: the
  transport for an arbitrary compatible pair of extensions whose canonical maps to the invariant
  functions of the two base changes are bijective.
* `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_tensorBaseRingMap_of_strictlyHenselian`:
  **over a strictly henselian flat extension `C₁` of the invariant ring, `Spec (C' ⊗[C] C₁) ⟶
  Spec C₁` is étale at every point above the closed point of `Spec C₁`**, which is the previous
  item at the tensor product presentation, where the two bijectivity hypotheses are Tag 03BK and
  the étaleness hypothesis is automatic.

## Implementation notes

Base changing `G` along `C ⟶ C₁` and `G'` along `C' ⟶ C'₁` and taking the induced morphism of base
changes (`AlgebraicGeometry.GroupoidScheme.baseChangeHom`) produces a morphism of affine groupoid
schemes to which the Claim applies: its source, target and stabilizer squares are cartesian because
those of `F` are, and its two rings of invariant functions are `C₁` and `C'₁` under the two
bijectivity hypotheses.

Those last two identifications are isomorphisms of rings, not equalities, so the conclusion of
the Claim is a statement about `Spec` of the map on invariant rings of the induced morphism and
not about `Spec ψ`. The two are carried onto one another by the private
`etaleAt_specMap_of_ringEquiv_square`: étaleness at a point is transported by
`AlgebraicGeometry.etaleAt_of_isIso_square` and the hypothesis on the point by
`AlgebraicGeometry.specMap_base_closedPoint_of_ringEquiv`. That the square of the four spectra
commutes is `AlgebraicGeometry.GroupoidScheme.invariantRingMap_baseChangeHom_comp_ofBijective`.

At the tensor product the two bijectivity hypotheses are Tag 03BK
(`AlgebraicGeometry.GroupoidScheme.canonicalMapToInvariantFunctions_bijective_of_flat`) for the
two extensions, which is why flatness of `C ⟶ C₁` is assumed; flatness of `C' ⟶ C' ⊗[C] C₁`
follows from it by `Module.Flat.baseChange`. Étaleness of the map on object schemes of the induced
morphism is `AlgebraicGeometry.GroupoidScheme.etale_baseChangeMapObjects_tensorBaseRing`, which
needs the tensor product presentation and not merely a compatible pair.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Étaleness above the closed point is transported along a commuting square of ring
isomorphisms: if `φ' ∘ eA = eB ∘ φ` with `eA` and `eB` isomorphisms and `Spec φ'` is étale at
every point above the closed point, then so is `Spec φ`. -/
private theorem etaleAt_specMap_of_ringEquiv_square {A B A' B' : Type u} [CommRing A]
    [CommRing B] [CommRing A'] [CommRing B'] [IsLocalRing A] [IsLocalRing A']
    (φ : A →+* B) (φ' : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (hcomm : φ'.comp eA.toRingHom = eB.toRingHom.comp φ)
    (h : ∀ y : Spec (.of B'), (Spec.map (CommRingCat.ofHom φ')).base y =
        (IsLocalRing.closedPoint A' : Spec (.of A')) →
      EtaleAt (Spec.map (CommRingCat.ofHom φ')) y)
    (x : Spec (.of B))
    (hx : (Spec.map (CommRingCat.ofHom φ)).base x =
      (IsLocalRing.closedPoint A : Spec (.of A))) :
    EtaleAt (Spec.map (CommRingCat.ofHom φ)) x := by
  have : IsIso (CommRingCat.ofHom eA.toRingHom) := eA.toCommRingCatIso.isIso_hom
  have : IsIso (CommRingCat.ofHom eB.toRingHom) := eB.toCommRingCatIso.isIso_hom
  have hsq : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom eA.toRingHom) =
      Spec.map (CommRingCat.ofHom eB.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hcomm]
  have hvinj : Function.Injective (Spec.map (CommRingCat.ofHom eA.toRingHom)).base := by
    intro a b hab
    have h3 : (inv (Spec.map (CommRingCat.ofHom eA.toRingHom))).base
        ((Spec.map (CommRingCat.ofHom eA.toRingHom)).base a) =
        (inv (Spec.map (CommRingCat.ofHom eA.toRingHom))).base
        ((Spec.map (CommRingCat.ofHom eA.toRingHom)).base b) := by rw [hab]
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id] at h3
    simpa using h3
  have hux : (Spec.map (CommRingCat.ofHom eB.toRingHom)).base
      ((inv (Spec.map (CommRingCat.ofHom eB.toRingHom))).base x) = x := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hy : (Spec.map (CommRingCat.ofHom φ')).base
      ((inv (Spec.map (CommRingCat.ofHom eB.toRingHom))).base x) =
      (IsLocalRing.closedPoint A' : Spec (.of A')) := by
    refine hvinj ?_
    rw [specMap_base_closedPoint_of_ringEquiv eA,
      ← Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom φ'))
        (Spec.map (CommRingCat.ofHom eA.toRingHom)),
      hsq, Scheme.Hom.comp_apply, hux, hx]
  have hmain := etaleAt_of_isIso_square (Spec.map (CommRingCat.ofHom eB.toRingHom))
    (Spec.map (CommRingCat.ofHom eA.toRingHom)) hsq (h _ hy)
  rwa [hux] at hmain

/-! ### The transport along a compatible pair of extensions -/

section Induced

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} {C₁ C'₁ : Type u} [CommRing C₁]
  [CommRing C'₁] [Algebra (invariantRing G) C₁] [Algebra (invariantRing G') C'₁]
  (F : GroupoidScheme.Hom G' G) (ψ : C₁ →+* C'₁)
  (hψ : ψ.comp (algebraMap (invariantRing G) C₁) =
    (algebraMap (invariantRing G') C'₁).comp (invariantRingMap F))
  (bc : AffineInvariantBaseChange G C₁) (bc' : AffineInvariantBaseChange G' C'₁)

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
  [StrictlyHenselianLocalRing C₁]

include hψ in
/-- **The Claim of [Stacks Project, Tag 0DT9] read on a compatible pair of extensions.** Let
`C ⟶ C₁` and `C' ⟶ C'₁` be extensions of the two invariant rings compatible through
`ψ : C₁ →+* C'₁`, with `C₁` strictly henselian local, and let the canonical maps from `C₁` and
`C'₁` to the invariant functions of the two base changes be bijective. If the map on object
schemes of the induced morphism of base changes is étale, then `Spec ψ` is étale at every point
of `Spec C'₁` above the closed point of `Spec C₁`. -/
theorem etaleAt_specMap_of_strictlyHenselian_of_bijective
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (hbc : Function.Bijective bc.canonicalMapToInvariantFunctions)
    (hbc' : Function.Bijective bc'.canonicalMapToInvariantFunctions)
    (hobj : Etale (baseChangeHom F ψ hψ bc bc').mapObjects.left)
    (x : Spec (.of C'₁))
    (hx : (Spec.map (CommRingCat.ofHom ψ)).base x =
      (IsLocalRing.closedPoint C₁ : Spec (.of C₁))) :
    EtaleAt (Spec.map (CommRingCat.ofHom ψ)) x := by
  have : StrictlyHenselianLocalRing bc.invariantFunctions :=
    strictlyHenselianLocalRing_of_ringEquiv (RingEquiv.ofBijective _ hbc)
  have : IsFiniteLocallyFree bc.groupoid.source.left := bc.source_isFiniteLocallyFree
  have : IsFiniteLocallyFree bc.groupoid.target.left := bc.target_isFiniteLocallyFree
  have : IsFiniteLocallyFree
      (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).source.left :=
    bc'.source_isFiniteLocallyFree
  have : IsFiniteLocallyFree
      (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).target.left :=
    bc'.target_isFiniteLocallyFree
  have : IsAffine (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).objects.left :=
    inferInstanceAs (IsAffine bc'.groupoid.objects.left)
  have : IsAffine (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).arrows.left :=
    inferInstanceAs (IsAffine bc'.groupoid.arrows.left)
  have := hobj
  exact etaleAt_specMap_of_ringEquiv_square ψ
    (invariantRingMap (baseChangeHom F ψ hψ bc bc'))
    (RingEquiv.ofBijective _ hbc) (RingEquiv.ofBijective _ hbc')
    (invariantRingMap_baseChangeHom_comp_ofBijective F ψ hψ bc bc' hbc hbc')
    (fun y hy => etaleAt_specMap_invariantRingMap_of_strictlyHenselian
      (baseChangeHom F ψ hψ bc bc')
      (source_isPullback_mapArrows_baseChangeHom F ψ hψ bc bc' hsource)
      (target_isPullback_mapArrows_baseChangeHom F ψ hψ bc bc' htarget)
      (isPullback_stabilizerMap_baseChangeHom F ψ hψ bc bc' htarget hstab) y hy)
    x hx

end Induced

/-! ### The transport at the tensor product presentation -/

section Tensor

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  (C₁ : Type u) [CommRing C₁] [Algebra (invariantRing G) C₁]

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
  [Etale F.mapObjects.left] [Module.Flat (invariantRing G) C₁]
  [StrictlyHenselianLocalRing C₁]

/-- **The Claim of [Stacks Project, Tag 0DT9] over a strictly henselian flat extension of the
invariant ring.** If `C₁` is a flat, strictly henselian local extension of the invariant ring `C`
of `G`, then `Spec (C' ⊗[C] C₁) ⟶ Spec C₁` is étale at every point of `Spec (C' ⊗[C] C₁)` lying
over the closed point of `Spec C₁`. -/
theorem etaleAt_specMap_tensorBaseRingMap_of_strictlyHenselian
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left) :
    letI := invariantRingAlgebra F
    ∀ x : Spec (.of (tensorBaseRing F C₁)),
      (Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))).base x =
          (IsLocalRing.closedPoint C₁ : Spec (.of C₁)) →
        EtaleAt (Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁))) x := by
  let := invariantRingAlgebra F
  intro x hx
  obtain ⟨bc⟩ := exists_affineInvariantBaseChange G C₁
  obtain ⟨bc'⟩ := exists_affineInvariantBaseChange G' (tensorBaseRing F C₁)
  exact etaleAt_specMap_of_strictlyHenselian_of_bijective F (tensorBaseRingMap F C₁)
    (tensorBaseRing_compatible F C₁) bc bc' hsource htarget hstab
    (canonicalMapToInvariantFunctions_bijective_of_flat bc)
    (canonicalMapToInvariantFunctions_bijective_of_flat bc')
    (etale_baseChangeMapObjects_tensorBaseRing F C₁ bc bc') x hx

end Tensor

end AlgebraicGeometry.GroupoidScheme

end

end
