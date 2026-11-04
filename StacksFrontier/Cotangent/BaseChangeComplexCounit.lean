module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsAlongSurjection
public import StacksFrontier.Cotangent.BaseChangeQuasiIso

/-!
# The two shapes of the base-change functoriality map, on the cotangent complexes

A commutative square of rings `A → B`, `A → A'`, `B → B'`, `A' → B'` gives the functoriality map
of [Stacks, Tag 08PN] in two shapes. The `B`-linear one,
`CommAlgCat.squareCotangentComplexMap`, is a map `L_{B/A} ⟶ L_{B'/A'}` of complexes of
`B`-modules, the target being read over `B` along `B → B'`. The `B'`-linear one,
`CommAlgCat.cotangentExtendScalarsComplexMap`, is its adjoint `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}`, and
it is that shape which [Stacks, Tag 08QQ] inverts.

`CommAlgCat.cotangentExtendScalarsMooreMap_f_eq_counit` compares the two in each *simplicial*
degree, on the alternating-face-map complexes. This file proves it and transports that comparison
through the reindexing which places simplicial degree `n` in cohomological degree `-n`, so that it
becomes an equality of maps of cotangent complexes.

## Main definitions

* `ModuleCat.extendRestrictScalarsAdjCounitComplex`: the counit `S ⊗_R N ⟶ N` of
  `ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f`, applied degreewise to a complex.

## Main results

* `ModuleCat.isIso_extendRestrictScalarsAdjCounitComplex`: for `f` surjective that counit is an
  isomorphism of complexes, every component being invertible by
  `Stacks.ModuleCat.isIso_extendRestrictScalarsAdj_counit_app`.
* `ModuleCat.extendRestrictScalarsAdjCounitComplex_naturality`: the counit is natural in the
  complex.
* `ModuleCat.quasiIso_of_quasiIso_extendScalars_id`: extension of scalars along the identity
  reflects quasi-isomorphisms.
* `ModuleCat.extendMap_extendRestrictScalarsAdjCounitComplex`: **the counit commutes with
  extending a complex along an embedding of complex shapes.**
* `CommAlgCat.cotangentExtendScalarsMooreMap_eq_counit`: the comparison of the two shapes of the
  functoriality map, as an equality of maps of alternating-face-map complexes.
* `CommAlgCat.cotangentExtendScalarsComplexMap_eq_counit`: **the two shapes of the functoriality
  map agree on the cotangent complexes** — the adjoint map out of `ModuleCat.extendScalars` is
  extension of scalars of the `B`-linear map of [Stacks, Tag 08PN] followed by the counit.

## Implementation notes

The two maps of cotangent complexes are built from the corresponding maps of
alternating-face-map complexes by `HomologicalComplex.extendMap` and the comparison isomorphism
`HomologicalComplex.mapHomologicalComplexExtendIso` of
`StacksFrontier/Algebra/Homology/Embedding/ExtendMap.lean`, but in the two possible orders: the
`B`-linear map extends first and compares second, while the adjoint map compares first and
extends second. Equating them is therefore not a degreewise computation with the simplicial
identity substituted in: the comparison isomorphism is cancelled on the left, the simplicial
identity is used as an equality of maps of *complexes*, and the two comparison isomorphisms are
moved past each other by
`HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality`.

All of that happens inside the two lemmas
`ModuleCat.extendMap_extendRestrictScalarsAdjCounitComplex` and
`ModuleCat.extendMap_comp_extendRestrictScalarsAdjCounitComplex`, which are stated for an
arbitrary ring map, an arbitrary embedding of complex shapes and arbitrary complexes, and not in
the proof of the comparison itself. That is deliberate. The cotangent complex is *by definition*
the extension of the Moore complex along `ComplexShape.embeddingUpIntLE 0`, and the ring map
`(CommAlgCat.algebraSquareOfAlgHom b).map` is *by definition* `b.toRingHom`, but neither identity
is visible at `implicit` transparency, which is what `rw` type-checks its motives at: a goal
mixing the two spellings of either -- and the statement of the comparison cannot avoid mixing
them, the two maps being declared in the two spellings -- stops every `rw`, with the matcher
reporting a pattern it is looking at. In the general lemmas no mixing arises, so the whole
category-theoretic computation is carried out there by ordinary `rw`; the comparison itself then
crosses between the spellings exactly once, in a chain of `Eq.trans` and `congrArg` terms, which
elaborate at default transparency and build no motive.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe u

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  {ι : Type*} (c : ComplexShape ι)

/-- **The counit of `ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f` on complexes.** In
each degree it is the map `S ⊗_R N ⟶ N`, `s ⊗ n ↦ s • n`, of the counit; it commutes with the
differentials because the counit is natural. -/
noncomputable def extendRestrictScalarsAdjCounitComplex
    (K : HomologicalComplex (ModuleCat.{u} S) c) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex c).obj
        (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj K) ⟶ K where
  f n := (ModuleCat.extendRestrictScalarsAdj f).counit.app (K.X n)
  comm' i j _ := ((ModuleCat.extendRestrictScalarsAdj f).counit.naturality (K.d i j)).symm

/-- The component of `ModuleCat.extendRestrictScalarsAdjCounitComplex f c K` in degree `n` is the
counit of `ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f` at `K.X n`. -/
@[simp]
theorem extendRestrictScalarsAdjCounitComplex_f
    (K : HomologicalComplex (ModuleCat.{u} S) c) (n : ι) :
    (extendRestrictScalarsAdjCounitComplex f c K).f n =
      (ModuleCat.extendRestrictScalarsAdj f).counit.app (K.X n) :=
  rfl

/-- **The counit is natural in the complex.** -/
theorem extendRestrictScalarsAdjCounitComplex_naturality
    {K L : HomologicalComplex (ModuleCat.{u} S) c} (g : K ⟶ L) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex c).map
          (((ModuleCat.restrictScalars f).mapHomologicalComplex c).map g) ≫
        extendRestrictScalarsAdjCounitComplex f c L =
      extendRestrictScalarsAdjCounitComplex f c K ≫ g :=
  HomologicalComplex.hom_ext _ _ fun n =>
    (ModuleCat.extendRestrictScalarsAdj f).counit.naturality (g.f n)

/-- **For a surjection of rings the counit is an isomorphism of complexes.** Every component is
invertible by `Stacks.ModuleCat.isIso_extendRestrictScalarsAdj_counit_app`. -/
theorem isIso_extendRestrictScalarsAdjCounitComplex (hf : Function.Surjective f)
    (K : HomologicalComplex (ModuleCat.{u} S) c) :
    IsIso (extendRestrictScalarsAdjCounitComplex f c K) :=
  have : ∀ n : ι, IsIso ((extendRestrictScalarsAdjCounitComplex f c K).f n) := fun n =>
    Stacks.ModuleCat.isIso_extendRestrictScalarsAdj_counit_app f hf (K.X n)
  HomologicalComplex.Hom.isIso_of_components _

/-- **Extension of scalars along the identity reflects quasi-isomorphisms.** It is isomorphic to
the identity functor (`ModuleCat.extendScalarsId`), and `Functor.mapHomologicalComplex` carries
that isomorphism to complexes. This is what turns [Stacks, Tag 08QQ] at a square whose top map
is the identity -- where the lemma speaks of `S ⊗_S L_{B/A}` -- into a statement about the
`B`-linear functoriality map itself. -/
theorem quasiIso_of_quasiIso_extendScalars_id {R : Type u} [CommRing R] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex (ModuleCat.{u} R) c} (g : K ⟶ L)
    (h : QuasiIso (((ModuleCat.extendScalars (RingHom.id R)).mapHomologicalComplex c).map g)) :
    QuasiIso g := by
  have := h
  have hcomp : QuasiIso (((ModuleCat.extendScalars (RingHom.id R)).mapHomologicalComplex c).map g
      ≫ (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) c).hom.app L) :=
    quasiIso_comp _ _
  rw [(NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) c).hom.naturality g] at hcomp
  exact quasiIso_of_comp_left
    ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) c).hom.app K)
    (((𝟭 (ModuleCat.{u} R)).mapHomologicalComplex c).map g)

/-- **The counit commutes with extending a complex along an embedding of complex shapes.**
Extending the counit of `K` is the counit of `K.extend e`, read through the two comparison
isomorphisms of `HomologicalComplex.mapHomologicalComplexExtendIso` for extension and for
restriction of scalars. In a degree in the image of the embedding this is the naturality of the
counit at the degree isomorphism of the extension; outside the image the source is a zero
object. -/
theorem extendMap_extendRestrictScalarsAdjCounitComplex {ι' : Type*} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex (ModuleCat.{u} S) c) :
    HomologicalComplex.extendMap (extendRestrictScalarsAdjCounitComplex f c K) e =
      (HomologicalComplex.mapHomologicalComplexExtendIso (ModuleCat.extendScalars f)
          (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj K) e).hom ≫
        ((ModuleCat.extendScalars f).mapHomologicalComplex c').map
            (HomologicalComplex.mapHomologicalComplexExtendIso
              (ModuleCat.restrictScalars f) K e).hom ≫
          extendRestrictScalarsAdjCounitComplex f c' (K.extend e) := by
  refine HomologicalComplex.hom_ext _ _ fun i' => ?_
  rcases hi : e.r i' with _ | i
  · exact ((((ModuleCat.extendScalars f).mapHomologicalComplex c).obj
      (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj K)).isZero_extend_X'
        e i' hi).eq_of_src _ _
  · have h : e.f i = i' := ComplexShape.Embedding.f_eq_of_r_eq_some _ hi
    have hc : (ModuleCat.extendScalars f).map ((ModuleCat.restrictScalars f).map
            (HomologicalComplex.extendXIso K e h).inv) ≫
          (ModuleCat.extendRestrictScalarsAdj f).counit.app ((K.extend e).X i') =
        (ModuleCat.extendRestrictScalarsAdj f).counit.app (K.X i) ≫
          (HomologicalComplex.extendXIso K e h).inv :=
      (ModuleCat.extendRestrictScalarsAdj f).counit.naturality _
    rw [HomologicalComplex.extendMap_f _ _ h, HomologicalComplex.comp_f,
      HomologicalComplex.comp_f,
      HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ h,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ h,
      extendRestrictScalarsAdjCounitComplex_f, extendRestrictScalarsAdjCounitComplex_f,
      Functor.map_comp]
    simp only [Category.assoc, Iso.map_inv_hom_id_assoc]
    rw [hc]

/-- **Extending the adjoint of a map of complexes.** Let `ψ : K ⟶ (restrictScalars f) L` be a map
of complexes of `R`-modules and let `S ⊗_R K ⟶ L` be its `S`-linear adjoint, namely
`extendScalars f` of `ψ` followed by the counit. Extending that adjoint along an embedding of
complex shapes gives the adjoint of the extension of `ψ`, read through the comparison isomorphism
`HomologicalComplex.mapHomologicalComplexExtendIso` for extension of scalars.

Both maps of cotangent complexes of [Stacks, Tag 08PN] are of this shape -- the `B`-linear one is
the extension of the `B`-linear map of alternating-face-map complexes, the `B'`-linear one is the
extension of its adjoint -- so this is what compares them. -/
theorem extendMap_comp_extendRestrictScalarsAdjCounitComplex {ι' : Type*}
    {c' : ComplexShape ι'} (e : c.Embedding c')
    {K : HomologicalComplex (ModuleCat.{u} R) c} {L : HomologicalComplex (ModuleCat.{u} S) c}
    (ψ : K ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj L) :
    HomologicalComplex.extendMap
        (((ModuleCat.extendScalars f).mapHomologicalComplex c).map ψ ≫
          extendRestrictScalarsAdjCounitComplex f c L) e =
      (HomologicalComplex.mapHomologicalComplexExtendIso (ModuleCat.extendScalars f) K e).hom ≫
        (((ModuleCat.extendScalars f).mapHomologicalComplex c').map
            (HomologicalComplex.extendMap ψ e ≫
              (HomologicalComplex.mapHomologicalComplexExtendIso
                (ModuleCat.restrictScalars f) L e).hom) ≫
          extendRestrictScalarsAdjCounitComplex f c' (L.extend e)) := by
  have hnat : (HomologicalComplex.mapHomologicalComplexExtendIso
        (ModuleCat.extendScalars f) K e).hom ≫
      ((ModuleCat.extendScalars f).mapHomologicalComplex c').map
        (HomologicalComplex.extendMap ψ e) =
      HomologicalComplex.extendMap
          (((ModuleCat.extendScalars f).mapHomologicalComplex c).map ψ) e ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso (ModuleCat.extendScalars f)
          (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj L) e).hom := by
    rw [← Iso.comp_inv_eq, Category.assoc,
      HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality, Iso.hom_inv_id_assoc]
  rw [HomologicalComplex.extendMap_comp, extendMap_extendRestrictScalarsAdjCounitComplex,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hnat]

end ModuleCat

namespace CommAlgCat

section Square

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
  [Algebra A (B' : Type u)] [IsScalarTower A A' (B' : Type u)]
  (b : (B : Type u) →ₐ[A] (B' : Type u))

/-- **The two shapes of the functoriality map agree, on the Moore complexes.** In each simplicial
degree the adjoint map out of `ModuleCat.extendScalars` is extension of scalars of the
`B`-linear map of [Stacks, Tag 08PN] followed by the counit of the adjunction: it is defined as
the adjoint, and this is the counit form of the adjunction's bijection. -/
theorem cotangentExtendScalarsMooreMap_f_eq_counit (n : ℕ) :
    (cotangentExtendScalarsMooreMap b).f n =
      (ModuleCat.extendScalars b.toRingHom).map
          ((squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b)).f n) ≫
        (ModuleCat.extendRestrictScalarsAdj b.toRingHom).counit.app
          (((alternatingFaceMapComplex (ModuleCat.{u} B')).obj
            (cotangentSimplicialModule.{u, u} A' B').object).X n) := by
  rw [cotangentExtendScalarsMooreMap_f]
  exact (ModuleCat.extendRestrictScalarsAdj b.toRingHom).homEquiv_counit _ _
    ((squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b)).f n)

/-- **The two shapes of the functoriality map agree, on the alternating-face-map complexes**, as
an equality of maps of complexes. This is
`CommAlgCat.cotangentExtendScalarsMooreMap_f_eq_counit` in every simplicial degree at once. -/
theorem cotangentExtendScalarsMooreMap_eq_counit :
    cotangentExtendScalarsMooreMap b =
      ((ModuleCat.extendScalars b.toRingHom).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex b.toRingHom (ComplexShape.down ℕ)
          ((alternatingFaceMapComplex (ModuleCat.{u} B')).obj
            (cotangentSimplicialModule.{u, u} A' B').object) :=
  HomologicalComplex.hom_ext _ _ fun n => cotangentExtendScalarsMooreMap_f_eq_counit b n

/-- **The two shapes of the functoriality map agree, on the cotangent complexes.** The adjoint
map `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of [Stacks, Tag 08QQ] is extension of scalars along `B → B'` of
the `B`-linear map `L_{B/A} ⟶ L_{B'/A'}` of [Stacks, Tag 08PN], followed by the counit
`B' ⊗_B L_{B'/A'} ⟶ L_{B'/A'}`.

This is `CommAlgCat.cotangentExtendScalarsMooreMap_eq_counit` transported through the reindexing
which places simplicial degree `n` in cohomological degree `-n`, by
`ModuleCat.extendMap_comp_extendRestrictScalarsAdjCounitComplex`. -/
@[stacks 08QQ "the arrow of the lemma is the functoriality map of Tag 08PN: the adjoint map out \
  of extension of scalars is extension of scalars of the B-linear map of Tag 08PN followed by \
  the counit, as an equality of maps of cotangent complexes"]
theorem cotangentExtendScalarsComplexMap_eq_counit :
    cotangentExtendScalarsComplexMap b =
      ((ModuleCat.extendScalars b.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} (algebraSquareOfAlgHom b)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex b.toRingHom (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} A' B') := by
  refine (cancel_epi (HomologicalComplex.mapHomologicalComplexExtendIso
    (ModuleCat.extendScalars b.toRingHom)
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (cotangentSimplicialModule.{u, u} A B).object)
    (ComplexShape.embeddingUpIntLE (0 : ℤ))).hom).1 ?_
  have hlhs : (HomologicalComplex.mapHomologicalComplexExtendIso
        (ModuleCat.extendScalars b.toRingHom)
        ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
          (cotangentSimplicialModule.{u, u} A B).object)
        (ComplexShape.embeddingUpIntLE (0 : ℤ))).hom ≫
      cotangentExtendScalarsComplexMap b =
      HomologicalComplex.extendMap (cotangentExtendScalarsMooreMap b)
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) :=
    Iso.hom_inv_id_assoc _ _
  exact hlhs.trans ((congrArg (fun φ => HomologicalComplex.extendMap φ
      (ComplexShape.embeddingUpIntLE (0 : ℤ))) (cotangentExtendScalarsMooreMap_eq_counit b)).trans
    (ModuleCat.extendMap_comp_extendRestrictScalarsAdjCounitComplex b.toRingHom
      (ComplexShape.down ℕ) (ComplexShape.embeddingUpIntLE (0 : ℤ))
      (squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b))))

end Square

end CommAlgCat

end
