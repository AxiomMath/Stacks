module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCech

/-!
# Functoriality of the extended alternating Čech complex

The extended alternating Čech complex `CategoryTheory.AlternatingCech.complex F` of a system
`F : Finset (Fin r) ⥤ 𝒜` of objects indexed by the subsets of `Fin r` is functorial in two
separate ways, and this file proves both.

In the system: a map `F ⟶ F'` of systems induces a map of complexes, and an isomorphism of
systems an isomorphism of complexes.

In the ambient category: an additive functor `G : 𝒜 ⥤ ℬ` which preserves finite products carries
`complex F` to `complex (F ⋙ G)`. Applied degreewise, `G` turns the product
`∏_{|S| = p} F.obj S` into the product of the `G.obj (F.obj S)`, and it commutes with the
alternating differential because that differential is a `ℤ`-linear combination of transition
maps.

## Main definitions

* `CategoryTheory.AlternatingCech.mapTerm`: a map of systems, applied to the degree-`p` term.
* `CategoryTheory.AlternatingCech.complexMap` and
  `CategoryTheory.AlternatingCech.complexMapIso`: the induced map, respectively isomorphism, of
  complexes.
* `CategoryTheory.AlternatingCech.mapTermIso`: the degree-`p` component of the comparison for a
  product-preserving functor, and `CategoryTheory.AlternatingCech.mapComplexIso` the resulting
  **isomorphism `G(Č(F)) ≅ Č(F ⋙ G)` of complexes**.

## Main results

* `CategoryTheory.AlternatingCech.mapTerm_comp_d`: a map of systems commutes with the
  alternating differential.
* `CategoryTheory.AlternatingCech.mapTermIso_hom_comp_d`: so does the comparison for a
  product-preserving additive functor.
* `CategoryTheory.AlternatingCech.mapTermIso_hom_comp_mapTerm_comp_lift`: the two halves
  together, applied to a map into the degree-`p` term assembled from one map per subset.

## Implementation notes

Everything is proved by `CategoryTheory.Limits.Pi.hom_ext` against the components of the
differential, `CategoryTheory.AlternatingCech.d_comp_pi`, together with the description
`CategoryTheory.AlternatingCech.proj` of a projection followed by a transition map. The only
inputs about `G` are `CategoryTheory.Functor.map_sum` and
`CategoryTheory.Functor.map_zsmul` — additivity — and
`CategoryTheory.Limits.piComparison_comp_π` — preservation of the product. No property of the
index type `CategoryTheory.AlternatingCech.Idx` is used beyond its finiteness, which is what
makes the preservation hypothesis a finite one.

These are two of the three things the base change of [Stacks, Tag 099H]'s lower row needs:
compatibility with the finite products that form the terms, and commutation with the alternating
differential. The third, naturality in the subset of the identification
`𝒪_{f_S} ⊗_𝒪 𝒪' ≅ 𝒪'_{f'_S}`, is a statement about the system and not about the complex; it is
`Stacks.Sheaves.CechFlatNeighbourhood.awayLocalizationBaseChangeIso` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodCech.lean`, and `complexMapIso`
here is what consumes it.

## References

* [Stacks Project, Tag 099H](https://stacks.math.columbia.edu/tag/099H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

namespace CategoryTheory.AlternatingCech

variable {r : ℕ} {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasFiniteProducts 𝒜]

section Map

variable {F F' F'' : Finset (Fin r) ⥤ 𝒜}

/-- A map `F ⟶ F'` of systems, applied to the degree-`p` term of the extended alternating Čech
complex: the product over the subsets of cardinality `p` of its components. -/
def mapTerm (α : F ⟶ F') (p : ℤ) : term F p ⟶ term F' p :=
  Pi.lift fun A : Idx r p => Pi.π (fun S : Idx r p => F.obj S.1) A ≫ α.app A.1

omit [Preadditive 𝒜] in
/-- The map of terms induced by `α`, followed by the projection to the factor indexed by `A`, is
that projection followed by the component of `α` at `A`. -/
@[simp]
theorem mapTerm_comp_pi (α : F ⟶ F') (p : ℤ) (A : Idx r p) :
    mapTerm α p ≫ Pi.π (fun S : Idx r p => F'.obj S.1) A =
      Pi.π (fun S : Idx r p => F.obj S.1) A ≫ α.app A.1 :=
  Pi.lift_π _ _

omit [Preadditive 𝒜] in
/-- The map of terms, followed by a transition map out of one factor, is that transition map
followed by the component of `α`. -/
theorem mapTerm_comp_proj (α : F ⟶ F') {p : ℤ} (A : Idx r p) {W : Finset (Fin r)}
    (h : A.1 ⊆ W) : mapTerm α p ≫ proj F' A h = proj F A h ≫ α.app W := by
  rw [proj, proj, ← Category.assoc, mapTerm_comp_pi, Category.assoc, Category.assoc,
    α.naturality (homOfLE h)]

omit [Preadditive 𝒜] in
/-- The identity of a system induces the identity on each term. -/
@[simp]
theorem mapTerm_id (p : ℤ) : mapTerm (𝟙 F) p = 𝟙 (term F p) := by
  refine Pi.hom_ext _ _ fun A => ?_
  rw [mapTerm_comp_pi, Category.id_comp, NatTrans.id_app, Category.comp_id]

omit [Preadditive 𝒜] in
/-- The map of terms induced by a composite of maps of systems is the composite of the induced
maps. -/
theorem mapTerm_comp (α : F ⟶ F') (β : F' ⟶ F'') (p : ℤ) :
    mapTerm (α ≫ β) p = mapTerm α p ≫ mapTerm β p := by
  refine Pi.hom_ext _ _ fun A => ?_
  rw [mapTerm_comp_pi, NatTrans.comp_app, Category.assoc]
  conv_rhs => rw [mapTerm_comp_pi, ← Category.assoc, mapTerm_comp_pi, Category.assoc]

/-- **A map of systems commutes with the alternating differential.** At a subset `T` of
cardinality `p + 1` both sides are the alternating sum, over the elements of `T`, of the
transition maps out of the factors indexed by `T ∖ {k}` followed by the component of `α` at
`T`. -/
theorem mapTerm_comp_d (α : F ⟶ F') (p : ℤ) :
    mapTerm α p ≫ d F' p = d F p ≫ mapTerm α (p + 1) := by
  refine Pi.hom_ext _ _ fun T => ?_
  rw [Category.assoc, d_comp_pi, Preadditive.comp_sum, Category.assoc, mapTerm_comp_pi,
    ← Category.assoc, d_comp_pi, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, mapTerm_comp_proj]

/-- **A map of systems induces a map of extended alternating Čech complexes**, degreewise the
product of its components. -/
def complexMap (α : F ⟶ F') : complex F ⟶ complex F' where
  f p := mapTerm α p
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    rw [complex_d, complex_d]
    exact mapTerm_comp_d α p

/-- The degree-`p` component of `complexMap α` is `mapTerm α p`. -/
@[simp]
theorem complexMap_f (α : F ⟶ F') (p : ℤ) : (complexMap α).f p = mapTerm α p := rfl

/-- **An isomorphism of systems induces an isomorphism of extended alternating Čech
complexes.** -/
def complexMapIso (e : F ≅ F') : complex F ≅ complex F' where
  hom := complexMap e.hom
  inv := complexMap e.inv
  hom_inv_id := by
    refine HomologicalComplex.hom_ext _ _ fun p => ?_
    have h : mapTerm e.hom p ≫ mapTerm e.inv p = 𝟙 (term F p) := by
      rw [← mapTerm_comp, e.hom_inv_id, mapTerm_id]
    exact h
  inv_hom_id := by
    refine HomologicalComplex.hom_ext _ _ fun p => ?_
    have h : mapTerm e.inv p ≫ mapTerm e.hom p = 𝟙 (term F' p) := by
      rw [← mapTerm_comp, e.inv_hom_id, mapTerm_id]
    exact h

end Map

section MapFunctor

variable {ℬ : Type u'} [Category.{v'} ℬ] [Preadditive ℬ] [HasFiniteProducts ℬ]
  (G : 𝒜 ⥤ ℬ) [G.Additive] [PreservesFiniteProducts G] (F : Finset (Fin r) ⥤ 𝒜)

/-- **A finite-product-preserving functor carries the degree-`p` term of the extended
alternating Čech complex of `F` to that of `F ⋙ G`.** -/
def mapTermIso (p : ℤ) : G.obj (term F p) ≅ term (F ⋙ G) p :=
  PreservesProduct.iso G fun S : Idx r p => F.obj S.1

omit [Preadditive 𝒜] [Preadditive ℬ] [G.Additive] in
/-- The comparison `mapTermIso G F p`, followed by the projection to the factor indexed by `A`,
is the image under `G` of the corresponding projection out of `term F p`. -/
theorem mapTermIso_hom_comp_pi (p : ℤ) (A : Idx r p) :
    (mapTermIso G F p).hom ≫ Pi.π (fun S : Idx r p => (F ⋙ G).obj S.1) A =
      G.map (Pi.π (fun S : Idx r p => F.obj S.1) A) := by
  rw [mapTermIso, PreservesProduct.iso_hom]
  exact piComparison_comp_π G _ A

omit [Preadditive 𝒜] [Preadditive ℬ] [G.Additive] in
/-- The comparison `mapTermIso G F p`, followed by a transition map out of the factor indexed by
`A`, is the image under `G` of the corresponding transition map out of `term F p`. -/
theorem mapTermIso_hom_comp_proj {p : ℤ} (A : Idx r p) {W : Finset (Fin r)} (h : A.1 ⊆ W) :
    (mapTermIso G F p).hom ≫ proj (F ⋙ G) A h = G.map (proj F A h) := by
  rw [proj, ← Category.assoc, mapTermIso_hom_comp_pi, proj, G.map_comp]
  rfl

/-- **A finite-product-preserving additive functor commutes with the alternating
differential.** The differential is a `ℤ`-linear combination of transition maps out of the
factors, and an additive functor carries such a combination to the corresponding combination of
the images. -/
theorem mapTermIso_hom_comp_d (p : ℤ) :
    (mapTermIso G F p).hom ≫ d (F ⋙ G) p =
      G.map (d F p) ≫ (mapTermIso G F (p + 1)).hom := by
  refine Pi.hom_ext _ _ fun T => ?_
  rw [Category.assoc, d_comp_pi, Preadditive.comp_sum, Category.assoc,
    mapTermIso_hom_comp_pi, ← G.map_comp, d_comp_pi, G.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Preadditive.comp_zsmul, mapTermIso_hom_comp_proj, Functor.map_zsmul]

/-- **`G(Č(F)) ≅ Č(F ⋙ G)`**: an additive functor preserving finite products commutes with the
formation of the extended alternating Čech complex. -/
def mapComplexIso :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (complex F) ≅ complex (F ⋙ G) :=
  HomologicalComplex.Hom.isoOfComponents (fun p => mapTermIso G F p) fun p q hpq => by
    obtain rfl : p + 1 = q := hpq
    rw [complex_d, Functor.mapHomologicalComplex_obj_d, complex_d]
    exact mapTermIso_hom_comp_d G F p

/-- The degree-`p` component of `mapComplexIso G F` is `mapTermIso G F p`. -/
@[simp]
theorem mapComplexIso_hom_f (p : ℤ) :
    (mapComplexIso G F).hom.f p = (mapTermIso G F p).hom := rfl

omit [Preadditive 𝒜] [Preadditive ℬ] [G.Additive] in
/-- **The two halves of functoriality, applied to a map into the degree-`p` term.** Let `F'` be a
second system, this time in `ℬ`, identified with `F ⋙ G`, and let `Z` be an object of `𝒜` with a
map `a_S : Z ⟶ F.obj S` for every subset. Then the degree-`p` component of the comparison
`G(Č(F)) ≅ Č(F')` carries the image under `G` of the map `Z ⟶ term F p` assembled from the `a_S`
to the map `G.obj Z ⟶ term F' p` assembled from their images. -/
theorem mapTermIso_hom_comp_mapTerm_comp_lift {F' : Finset (Fin r) ⥤ ℬ} (e : F ⋙ G ≅ F')
    {Z : 𝒜} (a : ∀ S : Finset (Fin r), Z ⟶ F.obj S)
    (a' : ∀ S : Finset (Fin r), G.obj Z ⟶ F'.obj S)
    (ha : ∀ S : Finset (Fin r), G.map (a S) ≫ e.hom.app S = a' S) (p : ℤ) :
    G.map (Pi.lift fun A : Idx r p => a A.1) ≫
        (mapTermIso G F p).hom ≫ mapTerm e.hom p =
      Pi.lift fun A : Idx r p => a' A.1 := by
  refine Pi.hom_ext _ _ fun A => ?_
  rw [Pi.lift_π, ← ha, Category.assoc, Category.assoc, mapTerm_comp_pi,
    ← Category.assoc (mapTermIso G F p).hom, mapTermIso_hom_comp_pi, ← Category.assoc,
    ← G.map_comp, Pi.lift_π]

end MapFunctor

end CategoryTheory.AlternatingCech

end
