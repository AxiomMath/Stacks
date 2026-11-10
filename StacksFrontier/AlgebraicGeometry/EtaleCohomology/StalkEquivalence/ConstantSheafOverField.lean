module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.CategoryTheory.Sites.DisjointCoverSections

/-!
# Sections of a sheaf on the small étale site of a field

A scheme étale over a field is a disjoint union of spectra of finite separable extensions of that
field. Over the field, those spectra form a covering family of the small étale site whose members
are pairwise disjoint, so the sections of any sheaf over an étale scheme are exactly the families
of sections over its components. For the constant sheaf on an object `M` this produces sections
taking a *different* constant value on each component, which the globally constant sections coming
from `CategoryTheory.toSheafify` alone do not provide.

## Main results

* `AlgebraicGeometry.Scheme.Etale.ofArrows_mem_smallEtaleTopology_of_isoSigma`: a family of
  morphisms of the small étale site realizing an object as a coproduct of schemes is a covering
  family.
* `AlgebraicGeometry.Scheme.Etale.isLimitFanSectionsOfIsoSigma`: such a family exhibits the
  sections of a sheaf over the object as a product of the sections over the members.
* `AlgebraicGeometry.Scheme.Etale.exists_cover_existsUnique_section_of_field`: over a field,
  every object of the small étale site carries such a family, so a family of sections over the
  members comes from a unique section over the object.
* `AlgebraicGeometry.Scheme.Etale.exists_cover_existsUnique_section_constantSheaf_of_field`: over
  a field, a prescribed constant value on each member of that family determines a unique section
  of the constant sheaf.

## Implementation notes

The decomposition is supplied by
`AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable`, which gives an index type in
the same universe as the schemes and no finiteness; none is needed, because gluing along the
decomposition uses the sheaf condition for the whole family at once. The index type is therefore
left unconstrained, matching the source.

Disjointness of the family is `AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne`: an object of the
small étale site mapping to two distinct members over the base has empty underlying scheme, hence
is covered by the empty sieve. That is exactly the hypothesis of
`CategoryTheory.Presheaf.IsSheaf.isLimitFanSectionsOfDisjointArrows`, which turns the covering
family into a product decomposition of the sections with no compatibility condition to check.

The product is stated as a limit fan rather than through a chosen product, so the coefficient
category is not asked for products indexed by the decomposition. The prescribed values are given
as morphisms out of an arbitrary object `T` of the coefficient category, i.e. as generalized
elements; taking `T` to be the coefficient object itself and the morphisms to be multiplication by
integers is what the divisor sequence of Stacks 03RM needs on the summands of its third term.

## References

* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₂ u₂

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}}

/-- An object of the small étale site with empty underlying scheme is covered by the empty
sieve, the empty family of arrows being jointly surjective onto it. -/
theorem bot_mem_smallEtaleTopology_of_isEmpty (Z : Y.Etale) [IsEmpty Z.left] :
    (⊥ : Sieve Z) ∈ Y.smallEtaleTopology Z := by
  have hmem : Sieve.ofArrows (fun i : Empty ↦ i.elim) (fun i ↦ i.elim) ∈
      Y.smallEtaleTopology Z := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    exact isEmptyElim x
  have heq : Sieve.ofArrows (fun i : Empty ↦ i.elim) (fun i ↦ i.elim) = (⊥ : Sieve Z) := by
    ext T g
    simp only [Sieve.bot_apply, iff_false]
    rintro ⟨-, -, -, ⟨i⟩, -⟩
    exact i.elim
  rwa [heq] at hmem

/-- A morphism of the small étale site is a monomorphism as soon as it is one on the underlying
schemes, since a morphism there is determined by its underlying morphism. -/
theorem mono_of_mono_left {Z W : Y.Etale} (f : Z ⟶ W) (h : Mono f.left) : Mono f := by
  constructor
  intro T g₁ g₂ hg
  exact MorphismProperty.Over.Hom.ext ((cancel_mono f.left).1
    (congrArg (fun φ : T ⟶ W ↦ φ.left) hg))

variable {W : Y.Etale} {I : Type u} {V : I → Y.Etale}

/-- **A coproduct decomposition is a covering family of the small étale site.** If the underlying
schemes of a family of morphisms `π i : V i ⟶ W` of the small étale site of `Y` realize `W.left`
as the coproduct of the `(V i).left`, then the family generates a covering sieve. -/
theorem ofArrows_mem_smallEtaleTopology_of_isoSigma (π : ∀ i, V i ⟶ W)
    (e : W.left ≅ ∐ fun i ↦ (V i).left)
    (he : ∀ i, Sigma.ι (fun i ↦ (V i).left) i ≫ e.inv = (π i).left) :
    Sieve.ofArrows V π ∈ Y.smallEtaleTopology W := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk fun i ↦ (V i).left).surjective (e.hom x)
  rw [sigmaMk_mk] at hy
  refine ⟨i, y, ?_⟩
  rw [← he i, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, e.hom_inv_id]
  simp

/-- **The sections of a sheaf over a coproduct decomposition form a product.** If the underlying
schemes of a family of morphisms `π i : V i ⟶ W` of the small étale site of `Y` realize `W.left`
as the coproduct of the `(V i).left`, then the restriction maps exhibit the sections of a sheaf
over `W` as a product of the sections over the `V i`. -/
noncomputable def isLimitFanSectionsOfIsoSigma {A : Type u₂} [Category.{v₂} A]
    (F : Sheaf Y.smallEtaleTopology A) (π : ∀ i, V i ⟶ W)
    (e : W.left ≅ ∐ fun i ↦ (V i).left)
    (he : ∀ i, Sigma.ι (fun i ↦ (V i).left) i ≫ e.inv = (π i).left) :
    IsLimit (Fan.mk (F.obj.obj (op W)) fun i ↦ F.obj.map (π i).op) := by
  refine F.property.isLimitFanSectionsOfDisjointArrows π
    (ofArrows_mem_smallEtaleTopology_of_isoSigma π e he)
    (fun i ↦ mono_of_mono_left _ (by rw [← he i]; infer_instance)) ?_
  intro i j hij Z gi gj hg
  have hleft : gi.left ≫ Sigma.ι (fun i ↦ (V i).left) i =
      gj.left ≫ Sigma.ι (fun i ↦ (V i).left) j := by
    rw [← cancel_mono e.inv, Category.assoc, Category.assoc, he i, he j]
    exact congrArg (fun φ : Z ⟶ W ↦ φ.left) hg
  have : IsEmpty Z.left := isEmpty_of_commSq_sigmaι_of_ne ⟨hleft⟩ hij
  exact bot_mem_smallEtaleTopology_of_isEmpty Z

variable (k : Type u) [Field k]

/-- **Every object of the small étale site of a field is covered by the spectra of the finite
separable extensions it decomposes into, and a sheaf's sections over it are the product of its
sections over them.** This is the small-étale-site form of Stacks 02GL: the decomposition of a
scheme étale over a field is a covering family whose members are pairwise disjoint. -/
theorem exists_cover_existsUnique_section_of_field {A : Type u₂} [Category.{v₂} A]
    (F : Sheaf (Spec (.of k)).smallEtaleTopology A) (W : (Spec (.of k)).Etale) :
    ∃ (I : Type u) (V : I → (Spec (.of k)).Etale) (π : ∀ i, V i ⟶ W),
      Sieve.ofArrows V π ∈ (Spec (.of k)).smallEtaleTopology W ∧
        ∀ (T : A) (t : ∀ i, T ⟶ F.obj.obj (op (V i))),
          ∃! s : T ⟶ F.obj.obj (op W), ∀ i, s ≫ F.obj.map (π i).op = t i := by
  obtain ⟨I, K, hK, hAlg, hFin, hSep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k W.hom).mp W.prop
  let (i : I) : Field (K i) := hK i
  let (i : I) : Algebra k (K i) := hAlg i
  let (i : I) : Module.Finite k (K i) := hFin i
  let (i : I) : Algebra.IsSeparable k (K i) := hSep i
  have hetale (i : I) : Etale (Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap k (K i)).Etale
    rw [RingHom.etale_algebraMap]
    exact ⟨Algebra.FormallyEtale.of_isSeparable k (K i),
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let V (i : I) : (Spec (.of k)).Etale :=
    MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) (hetale i)
  have hw (i : I) : (Sigma.ι (fun i ↦ Spec (.of (K i))) i ≫ e.inv) ≫ W.hom = (V i).hom := by
    change _ = Spec.map (CommRingCat.ofHom (algebraMap k (K i)))
    rw [← he, Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]
  let π (i : I) : V i ⟶ W := MorphismProperty.Over.homMk _ (hw i)
  have hlim := isLimitFanSectionsOfIsoSigma F π e fun i ↦ rfl
  refine ⟨I, V, π, ofArrows_mem_smallEtaleTopology_of_isoSigma π e fun i ↦ rfl,
    fun T t ↦ ⟨hlim.lift (Fan.mk T t), fun i ↦ hlim.fac (Fan.mk T t) ⟨i⟩,
      fun s hs ↦ hlim.uniq (Fan.mk T t) s fun ⟨i⟩ ↦ hs i⟩⟩

/-- **A constant value on each component of a scheme étale over a field determines a unique
section of the constant sheaf.** The values are prescribed as morphisms from an arbitrary object
`T` of the coefficient category, and the section they determine restricts on each member of the
covering family to the globally constant section of that value, given by
`CategoryTheory.toSheafify`. -/
theorem exists_cover_existsUnique_section_constantSheaf_of_field {A : Type u₂} [Category.{v₂} A]
    [HasWeakSheafify (Spec (.of k)).smallEtaleTopology A] (M : A)
    (W : (Spec (.of k)).Etale) :
    ∃ (I : Type u) (V : I → (Spec (.of k)).Etale) (π : ∀ i, V i ⟶ W),
      Sieve.ofArrows V π ∈ (Spec (.of k)).smallEtaleTopology W ∧
        ∀ (T : A) (m : I → (T ⟶ M)),
          ∃! s : T ⟶ ((constantSheaf (Spec (.of k)).smallEtaleTopology A).obj M).obj.obj (op W),
            ∀ i, s ≫ ((constantSheaf (Spec (.of k)).smallEtaleTopology A).obj M).obj.map
                (π i).op =
              m i ≫ (toSheafify (Spec (.of k)).smallEtaleTopology
                ((Functor.const _).obj M)).app (op (V i)) := by
  obtain ⟨I, V, π, hcov, huniq⟩ := exists_cover_existsUnique_section_of_field k
    ((constantSheaf (Spec (.of k)).smallEtaleTopology A).obj M) W
  exact ⟨I, V, π, hcov, fun T m ↦ huniq T fun i ↦
    m i ≫ (toSheafify _ ((Functor.const _).obj M)).app (op (V i))⟩

end AlgebraicGeometry.Scheme.Etale

end
