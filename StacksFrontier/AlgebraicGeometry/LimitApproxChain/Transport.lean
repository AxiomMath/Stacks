module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Basic

/-!
# Transporting a finite-type approximation along an isomorphism of the ambient scheme

Noetherian approximation of a quasi-compact quasi-separated scheme `S` relative to a
quasi-compact open `V ⊆ S` is proved by adding one affine open at a time to `V`.  The chain of
steps runs through the opens `V ⊆ V ⊔ U₁ ⊆ ⋯ ⊆ V ⊔ U₁ ⊔ ⋯ ⊔ Uₘ = ⊤` of `S`, each of which is
used as an *ambient scheme* by way of its associated open subscheme; so the last step of the
chain produces an approximation whose ambient scheme is `(⊤ : S.Opens)` viewed as a scheme, and
not `S` itself.  Getting back to `S` is a transport along Mathlib's
`AlgebraicGeometry.Scheme.topIso`, which is what this file provides.

## Main definitions

* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofIso` transports an approximation along an
  isomorphism `e : S ≅ S'` of ambient schemes, given matching opens: an open `U` of `S`, an open
  `U'` of `S'`, and an isomorphism `ε : U ≅ U'` of the two as schemes commuting with the two
  inclusions and `e`.  Only the two limiting cones move: every component of the new system — the
  index preorder, the reindexing, the ambient and open systems, the inclusion and the comparison
  isomorphism — is the old one unchanged, since none of them mentions the ambient scheme.  The
  two cones are composed with `e.hom` and `ε.hom`, and remain limiting by
  `CategoryTheory.Limits.IsLimit.ofIsoLimit` along `CategoryTheory.Limits.Cone.ext`.  The two
  compatibility fields are reassociations of the corresponding fields of the input against the
  hypothesis relating `ε` to `e`.

* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofPreimageIso` is the case where the open of
  `S'` and the isomorphism of opens are the canonical ones: `U' = e.inv ⁻¹ᵁ U`, and `ε` is the
  inverse of Mathlib's `AlgebraicGeometry.morphismRestrict` of `e.inv` along `U`, which is an
  isomorphism because `e.inv` is.

* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofTopOpen` is the specialization needed at
  the end of the chain: an approximation whose ambient scheme is the top open of `S`, relative to
  the inverse image of `U` under the inclusion of that top open, gives an approximation of `S`
  itself relative to `U`.  It is `ofPreimageIso` at `AlgebraicGeometry.Scheme.topIso`, whose
  `inv` is where the inverse image comes from.

## Implementation notes

Everything lives in the single universe `u` of the schemes, as the structure
`AlgebraicGeometry.Scheme.FiniteTypeApproximation` requires of its index type.  Nothing here
forms a limit or a colimit of rings, so no further restriction is introduced.

Transparency gotchas:

* The three instance-implicit fields of
  `AlgebraicGeometry.Scheme.FiniteTypeApproximation` recording that the index type is a directed
  nonempty preorder are not instances outside the structure, so they are made local instances
  for the duration of the file, exactly as in
  `AlgebraicGeometry.Scheme.FiniteTypeApproximation.comp`.

* The two cones are built as composites with the image of the isomorphism under the constant
  functor, which supplies naturality with nothing to prove; the price is that each field
  mentioning a cone leg needs `CategoryTheory.NatTrans.comp_app` and
  `CategoryTheory.Functor.const_map_app` before anything else fires.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.FiniteTypeApproximation.indexPreorder
  Scheme.FiniteTypeApproximation.indexNonempty Scheme.FiniteTypeApproximation.indexDirected

namespace Scheme.FiniteTypeApproximation

variable {I : Type u} [Preorder I] {D : Iᵒᵈ ⥤ Scheme.{u}}

/-- **Transport of a finite-type approximation along an isomorphism of the ambient scheme.**
Let `A` approximate `S'` relative to an open `U' ⊆ S'`, let `e : S ≅ S'`, and let `ε` identify
an open `U ⊆ S` with `U'` compatibly with `e` and the two inclusions.  Then `S` is approximated
relative to `U`, by the same system of schemes with both limiting cones transported. -/
noncomputable def ofIso
    {S' : Scheme.{u}} {U' : S'.Opens} {p' : (Functor.const Iᵒᵈ).obj (U' : Scheme.{u}) ⟶ D}
    (A : FiniteTypeApproximation D S' U' p')
    {S : Scheme.{u}} (e : S ≅ S') {U : S.Opens} (ε : (U : Scheme.{u}) ≅ (U' : Scheme.{u}))
    (hε : ε.hom ≫ U'.ι = U.ι ≫ e.hom)
    {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D}
    (hp : ∀ i, p.app i = ε.hom ≫ p'.app i) :
    FiniteTypeApproximation D S U p where
  indexType := A.indexType
  index := A.index
  ambient := A.ambient
  openPart := A.openPart
  inclusion := A.inclusion
  comparison := A.comparison
  ambientCone := (Functor.const A.indexTypeᵒᵈ).map e.hom ≫ A.ambientCone
  openCone := (Functor.const A.indexTypeᵒᵈ).map ε.hom ≫ A.openCone
  transition_affine := A.transition_affine
  locallyOfFiniteType := A.locallyOfFiniteType
  quasiCompact := A.quasiCompact
  inclusion_isOpenImmersion := A.inclusion_isOpenImmersion
  transition_isPullback := A.transition_isPullback
  ambientCone_isLimit :=
    IsLimit.ofIsoLimit A.ambientCone_isLimit (Cone.ext e.symm fun j ↦ by simp)
  openCone_isLimit :=
    IsLimit.ofIsoLimit A.openCone_isLimit (Cone.ext ε.symm fun j ↦ by simp)
  inclusion_compatibility := fun j ↦ by
    simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc]
    rw [← reassoc_of% hε, A.inclusion_compatibility j]
  comparison_compatibility := fun j ↦ by
    simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc]
    rw [A.comparison_compatibility j, hp]

/-- **Transport along an isomorphism of the ambient scheme, at the canonical open.**  This is
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofIso` with the open of `S'` taken to be the
inverse image of `U` and the identification of the two opens the canonical one. -/
noncomputable def ofPreimageIso {S S' : Scheme.{u}} (e : S ≅ S') {U : S.Opens}
    {p' : (Functor.const Iᵒᵈ).obj ((e.inv ⁻¹ᵁ U : S'.Opens) : Scheme.{u}) ⟶ D}
    (A : FiniteTypeApproximation D S' (e.inv ⁻¹ᵁ U) p')
    {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D}
    (hp : ∀ i, p.app i = (asIso (e.inv ∣_ U)).inv ≫ p'.app i) :
    FiniteTypeApproximation D S U p :=
  A.ofIso e (asIso (e.inv ∣_ U)).symm (by
    rw [Iso.symm_hom, ← cancel_epi (asIso (e.inv ∣_ U)).hom, Iso.hom_inv_id_assoc,
      asIso_hom, ← Category.assoc, morphismRestrict_ι, Category.assoc, e.inv_hom_id,
      Category.comp_id]) hp

/-- **The last step of the chain proving Noetherian approximation relative to an open.**  An
approximation whose ambient scheme is the top open of `S`, taken relative to the inverse image
of `U` along the inclusion of that top open, is an approximation of `S` itself relative to
`U`. -/
noncomputable def ofTopOpen {S : Scheme.{u}} {U : S.Opens}
    {p' : (Functor.const Iᵒᵈ).obj
      ((S.topIso.hom ⁻¹ᵁ U : ((⊤ : S.Opens) : Scheme.{u}).Opens) : Scheme.{u}) ⟶ D}
    (A : FiniteTypeApproximation D ((⊤ : S.Opens) : Scheme.{u}) (S.topIso.hom ⁻¹ᵁ U) p')
    {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D}
    (hp : ∀ i, p.app i = (asIso (S.topIso.hom ∣_ U)).inv ≫ p'.app i) :
    FiniteTypeApproximation D S U p :=
  ofPreimageIso S.topIso.symm A hp

end Scheme.FiniteTypeApproximation

end AlgebraicGeometry
