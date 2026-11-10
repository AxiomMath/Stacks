module

public import StacksFrontier.AlgebraicGeometry.SeminormalizationIsoIff.Affine
public import StacksFrontier.AlgebraicGeometry.SeminormalizationRingFunctorial.Basic
public import StacksFrontier.AlgebraicGeometry.AffineLocal.Basic

/-!
# The seminormalization commutes with restriction to an affine open

For a ring map `A ⟶ B` whose spectrum morphism is an open immersion, the base change
`B ⊗[A] Aˢⁿ` of the seminormalization of `A` is the seminormalization of `B`.

## Main definitions

* `AlgebraicGeometry.seminormalizationMap`: the map on seminormalizations induced by a ring
  homomorphism, chosen from `AlgebraicGeometry.existsUnique_seminormalizationMap`.

## Main results

* `AlgebraicGeometry.isSeminormalRing_seminormalization`: the seminormalization of a ring is
  seminormal.
* `AlgebraicGeometry.exists_seminormalization_tensorProduct_equiv`: the base-change statement,
  with the identification pinned down by the two canonical maps into the tensor product.

## Implementation notes

The route is shorter than the one
`StacksDraft.AlgebraicGeometry.F3.AbsoluteWeakNormalizationBaseChange` takes for the absolute
weak normalization, because the ingredient that file proves inline is already available here:
`AlgebraicGeometry.isIso_lift_to_seminormalization_iff_isSeminormalRing` -- the
`sn_characterization` label of Tag 0EUR -- says that a subintegral `B`-algebra is *the*
seminormalization of `B` exactly when its underlying ring is seminormal.  So only two things
have to be checked about `C = B ⊗[A] Aˢⁿ`:

* it is a subintegral `B`-algebra, which is
  `AlgebraicGeometry.isSeminormalizationCandidateAlgebra_tensorProduct`; and
* its underlying ring is seminormal, which holds because `Spec C` is an *open* subscheme of
  `Spec Aˢⁿ` -- the base change of the open immersion `Spec B ⟶ Spec A` -- while `Aˢⁿ` is a
  seminormal ring, so `Spec Aˢⁿ` is a seminormal scheme and seminormality passes to opens by
  Tag 0EUP.

The open-immersion hypothesis is therefore used only for the second point, and only through
`AlgebraicGeometry.isSeminormal_open`.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tags 0EUR and 0EUS is used: `A` and `B` are arbitrary
commutative rings, with no Noetherian, reducedness or finiteness assumption.

## References

* [Stacks Project, Tag 0EUP](https://stacks.math.columbia.edu/tag/0EUP)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry

/-! ### The induced map on seminormalizations -/

/-- The unique homomorphism of seminormalizations induced by a ring homomorphism, chosen from
`AlgebraicGeometry.existsUnique_seminormalizationMap`. -/
noncomputable def seminormalizationMap {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    (φ : A →+* A') : Algebra.seminormalization A →+* Algebra.seminormalization A' :=
  Classical.choose (existsUnique_seminormalizationMap φ)

/-- `AlgebraicGeometry.seminormalizationMap` is compatible with the canonical maps into the
seminormalizations. -/
theorem seminormalizationMap_spec {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    (φ : A →+* A') :
    (seminormalizationMap φ).comp (algebraMap A (Algebra.seminormalization A)) =
      (algebraMap A' (Algebra.seminormalization A')).comp φ :=
  (Classical.choose_spec (existsUnique_seminormalizationMap φ)).1

/-- `AlgebraicGeometry.seminormalizationMap` is the only compatible map. -/
theorem seminormalizationMap_unique {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    (φ : A →+* A')
    (ψ : Algebra.seminormalization A →+* Algebra.seminormalization A')
    (hψ : ψ.comp (algebraMap A (Algebra.seminormalization A)) =
      (algebraMap A' (Algebra.seminormalization A')).comp φ) :
    ψ = seminormalizationMap φ :=
  (Classical.choose_spec (existsUnique_seminormalizationMap φ)).2 ψ hψ

/-- The map on seminormalizations induced by the identity is the identity. -/
@[simp]
theorem seminormalizationMap_id (A : Type u) [CommRing A] :
    seminormalizationMap (RingHom.id A) = RingHom.id (Algebra.seminormalization A) :=
  (seminormalizationMap_unique (RingHom.id A) (RingHom.id _) (by simp)).symm

/-- `AlgebraicGeometry.seminormalizationMap` is functorial: the map induced by a composite `ψ ∘ φ`
is the composite of the induced maps. -/
theorem seminormalizationMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    seminormalizationMap (ψ.comp φ) =
      (seminormalizationMap ψ).comp (seminormalizationMap φ) := by
  symm
  apply seminormalizationMap_unique (ψ.comp φ)
    ((seminormalizationMap ψ).comp (seminormalizationMap φ))
  rw [RingHom.comp_assoc, seminormalizationMap_spec, ← RingHom.comp_assoc,
    seminormalizationMap_spec]
  rfl

/-! ### The seminormalization of a ring is seminormal -/

/-- **Stacks 0EUR.** The seminormalization of a commutative ring is a seminormal ring. -/
theorem isSeminormalRing_seminormalization (A : Type u) [CommRing A] :
    IsSeminormalRing (Algebra.seminormalization A) :=
  isSeminormalRing_of_isTerminal A (seminormalizationAlgebraObject A)
    (seminormalizationAlgebraObject_isTerminal A)

/-- A ring is seminormal as soon as its spectrum is a seminormal scheme. -/
theorem isSeminormalRing_of_isSeminormal_spec {R : Type u} [CommRing R]
    (hR : IsSeminormal (Spec (CommRingCat.of R))) : IsSeminormalRing R :=
  Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    ((isSeminormal_iff_forall_affineOpens _).mp hR ⟨⊤, isAffineOpen_top _⟩)

/-- The spectrum of a seminormal ring is a seminormal scheme. -/
theorem isSeminormal_spec_of_isSeminormalRing {R : Type u} [CommRing R]
    (hR : IsSeminormalRing R) : IsSeminormal (Spec (CommRingCat.of R)) := by
  intro x
  refine ⟨⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩, Set.mem_univ _, ?_⟩
  change IsSeminormalRing Γ(Spec (CommRingCat.of R), ⊤)
  exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv hR

/-- A ring whose spectrum is isomorphic to an affine open subscheme of a seminormal scheme is
seminormal. -/
theorem isSeminormalRing_of_isoSeminormalOpen {R : Type u} [CommRing R] {Y : Scheme.{u}}
    [IsAffine Y] (e : Spec (CommRingCat.of R) ≅ Y) (hY : IsSeminormal Y) :
    IsSeminormalRing R :=
  isSeminormalRing_of_isSeminormal_spec (isSeminormal_of_isIso e.inv hY)

/-! ### Base change along an open immersion -/

section BaseChange

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The base change `B ⊗[A] Aˢⁿ` of the seminormalization along a ring map whose spectrum
morphism is an open immersion is a seminormal ring: its spectrum is an open subscheme of
`Spec Aˢⁿ`, which is seminormal because `Aˢⁿ` is. -/
theorem isSeminormalRing_tensorProduct_seminormalization
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    IsSeminormalRing (B ⊗[A] Algebra.seminormalization A) := by
  let N := Algebra.seminormalization A
  let fB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  let fN : Spec (CommRingCat.of N) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A N))
  let iso := pullbackSpecIso A B N
  let jN : Spec (CommRingCat.of (B ⊗[A] N)) ⟶ Spec (CommRingCat.of N) :=
    iso.inv ≫ pullback.snd fB fN
  let U : (Spec (CommRingCat.of N)).Opens := jN.opensRange
  let e : Spec (CommRingCat.of (B ⊗[A] N)) ≅ U.toScheme :=
    IsOpenImmersion.isoOfRangeEq jN U.ι
      (by rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange])
  have _ : IsAffine U.toScheme := IsAffine.of_isIso e.inv
  exact isSeminormalRing_of_isoSeminormalOpen e
    (isSeminormal_open
      (isSeminormal_spec_of_isSeminormalRing (isSeminormalRing_seminormalization A)) U)

/-- **Stacks 0EUS.** The seminormalization commutes with restriction to an affine open: for a
ring map `A ⟶ B` whose spectrum morphism is an open immersion, the base change
`B ⊗[A] Aˢⁿ` is the seminormalization of `B`, with the identification pinned down by the two
canonical maps into the tensor product. -/
theorem exists_seminormalization_tensorProduct_equiv
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    ∃! e : (B ⊗[A] Algebra.seminormalization A) ≃+* Algebra.seminormalization B,
      (e.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := A)
        (A := B) (B := Algebra.seminormalization A)) =
          algebraMap B (Algebra.seminormalization B)) ∧
      (e.toRingHom.comp ((Algebra.TensorProduct.includeRight (R := A)
        (A := B) (B := Algebra.seminormalization A)).toRingHom) =
          seminormalizationMap (algebraMap A B)) := by
  let N := Algebra.seminormalization A
  let C := B ⊗[A] N
  have hC : IsSeminormalizationCandidateAlgebra B (CommAlgCat.of B C) :=
    isSeminormalizationCandidateAlgebra_tensorProduct A N B
      (seminormalization_universalHomeomorphism A)
      (seminormalization_inducesResidueFieldIsomorphisms A)
  let Robj : SeminormalizationAlgebraCategory B := ⟨CommAlgCat.of B C, hC.1, hC.2⟩
  let hterm := seminormalizationAlgebraObject_isTerminal B
  have : IsIso (hterm.from Robj) :=
    (isIso_lift_to_seminormalization_iff_isSeminormalRing B C hC.1 hC.2).mpr
      (isSeminormalRing_tensorProduct_seminormalization A B)
  let isoAlg : CommAlgCat.of B C ≅ CommAlgCat.of B (Algebra.seminormalization B) :=
    (ObjectProperty.ι (IsSeminormalizationCandidateAlgebra B)).mapIso
      (asIso (hterm.from Robj))
  let eAlg : C ≃ₐ[B] Algebra.seminormalization B := CommAlgCat.isoEquivAlgEquiv isoAlg
  let e : C ≃+* Algebra.seminormalization B := eAlg.toRingEquiv
  have hLeft : e.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom
      (R := A) (A := B) (B := N)) = algebraMap B (Algebra.seminormalization B) := by
    ext b
    exact eAlg.commutes b
  have hRightBase :
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := N)).toRingHom.comp
          (algebraMap A N) =
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := N)).comp
          (algebraMap A B) := by
    ext a
    exact ((Algebra.TensorProduct.includeRight (R := A) (A := B) (B := N)).commutes a).trans
      (IsScalarTower.algebraMap_apply A B C a)
  have hRightEq : e.toRingHom.comp ((Algebra.TensorProduct.includeRight
      (R := A) (A := B) (B := N)).toRingHom) = seminormalizationMap (algebraMap A B) :=
    seminormalizationMap_unique _ _ (by
      rw [RingHom.comp_assoc, hRightBase, ← RingHom.comp_assoc, hLeft])
  refine ⟨e, ⟨hLeft, hRightEq⟩, ?_⟩
  intro e' he'
  exact RingEquiv.toRingHom_injective <| Algebra.TensorProduct.ringHom_ext
    (f := e'.toRingHom) (g := e.toRingHom) (he'.1.trans hLeft.symm) (he'.2.trans hRightEq.symm)

end BaseChange

end AlgebraicGeometry
