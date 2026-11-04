module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.RingTheory.Etale.Field
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AffineLimits
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separable extensions base changed to a separably closed field

Let `L / F` be a separable algebraic extension of fields and let `C / F` be an extension with
`C` separably closed. This file proves that `C ⊗[F] L` is a filtered colimit of finite products
of copies of `C`, that is, it produces a term of
`AlgebraicGeometry.IsFilteredColimitOfFiniteProducts C (C ⊗[F] L)`.

The index category is `AlgebraicGeometry.FExt F L`, the finite subextensions `F ⊆ E ⊆ L`
ordered by inclusion. The diagram is `E ↦ C ⊗[F] E` and the cocone is the base change along
`F → C` of the cocone with vertex `L` whose legs are the inclusions `E → L`. Each stage is a
finite product of copies of `C` because `E / F` is finite separable, hence `C ⊗[F] E` is étale
over `C`, and an étale algebra over a separably closed field is a finite product of copies of
that field.

## Main results

* `AlgebraicGeometry.isFilteredColimitOfFiniteProducts_tensorProduct_of_isSeparable`: for
  `L / F` separable algebraic and `C / F` with `C` separably closed, `C ⊗[F] L` is a filtered
  colimit of finite products of copies of `C`.
* `AlgebraicGeometry.IsFilteredColimitOfFiniteProducts.of_algEquiv`: the property is invariant
  under isomorphism of algebras.

## Implementation notes

The diagram and the cocone live in `CommAlgCat C`, as
`AlgebraicGeometry.IsFilteredColimitOfFiniteProducts` requires, rather than in `CommRingCat` as
`AlgebraicGeometry.fextDiagram` and `AlgebraicGeometry.fextCocone` do. Base change along `F → C` is
packaged as a functor `CommAlgCat F ⥤ CommAlgCat C`, the diagram of finite subextensions is built
in `CommAlgCat F`, and the cocone on the composite is `CategoryTheory.Functor.mapCocone`.

That the base-changed cocone is colimiting is the universal property of base change,
`AlgHom.liftEquiv`, combined with the fact that `L` is the directed union of its finite
subextensions, `Subalgebra.iSupLift`.

No `@[stacks]` attribute is attached. Stacks has no tag for this statement; it appears inside
the proofs of Stacks 0B8E and Stacks 0B8G rather than as a numbered result.

## References

* [Stacks Project, Tag 0B7U](https://stacks.math.columbia.edu/tag/0B7U)
* [Stacks Project, Tag 0B8G](https://stacks.math.columbia.edu/tag/0B8G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Being a filtered colimit of finite products of copies of `k` only depends on the
isomorphism class of the `k`-algebra. -/
theorem IsFilteredColimitOfFiniteProducts.of_algEquiv {k A B : Type u} [CommRing k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (h : IsFilteredColimitOfFiniteProducts k A) (e : A ≃ₐ[k] B) :
    IsFilteredColimitOfFiniteProducts k B := by
  obtain ⟨I, hI, hfil, D, c, hc, ⟨eA⟩, hstage⟩ := h
  exact ⟨I, hI, hfil, D, c, hc, ⟨eA.trans (CommAlgCat.isoMk e)⟩, hstage⟩

/-- An étale algebra over a separably closed field is a finite product of copies of that
field. -/
@[ega "IV 18.3.3" "special case",
  sga "1 IX 1.8" "special case",
  sga "1 XIII 2.0" "special case",
  sga "4 VIII 3.2" "partial",
  sga "4½ Arcata 2.1.2" "special case"]
private theorem exists_algEquiv_fun_fin (C A : Type u) [Field C] [IsSepClosed C] [CommRing A]
    [Algebra C A] [Algebra.Etale C A] : ∃ n : ℕ, Nonempty (A ≃ₐ[C] (Fin n → C)) := by
  obtain ⟨I, hI, Ai, hfield, halg, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod C A).1 inferInstance
  let : Finite I := hI
  let : ∀ i, Field (Ai i) := hfield
  let : ∀ i, Algebra C (Ai i) := halg
  let : ∀ i, Algebra.IsSeparable C (Ai i) := fun i => (hfin i).2
  have e1 : (∀ i, Ai i) ≃ₐ[C] (∀ _ : I, C) :=
    AlgEquiv.piCongrRight fun i =>
      (AlgEquiv.ofBijective (Algebra.ofId C (Ai i))
        (IsSepClosed.algebraMap_bijective C (Ai i))).symm
  have e2 : (∀ _ : I, C) ≃ₐ[C] (Fin (Nat.card I) → C) :=
    AlgEquiv.piCongrLeft' C (fun _ : I => C) (Finite.equivFin I)
  exact ⟨Nat.card I, ⟨e.trans (e1.trans e2)⟩⟩

variable (F L C : Type u) [Field F] [Field L] [Field C] [Algebra F L] [Algebra F C]

/-- Base change along `F → C`, as a functor from commutative `F`-algebras to commutative
`C`-algebras. -/
private noncomputable def baseChangeCommAlgCat : CommAlgCat.{u} F ⥤ CommAlgCat.{u} C where
  obj A := CommAlgCat.of C (C ⊗[F] A)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id C C) f.hom)
  map_id _ := CommAlgCat.hom_ext Algebra.TensorProduct.map_id
  map_comp f g := CommAlgCat.hom_ext (Algebra.TensorProduct.map_id_comp g.hom f.hom)

/-- The diagram of the finite subextensions of `L / F` as `F`-algebras, with the inclusions
between them. -/
private def subextensionAlgDiagram : FExt F L ⥤ CommAlgCat.{u} F where
  obj E := CommAlgCat.of F E.1
  map {_ _} h := CommAlgCat.ofHom (IntermediateField.inclusion (leOfHom h))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The cocone on the diagram of finite subextensions whose vertex is `L` itself. -/
private def subextensionAlgCocone : Cocone (subextensionAlgDiagram F L) where
  pt := CommAlgCat.of F L
  ι :=
    { app := fun E => CommAlgCat.ofHom E.1.val
      naturality := by intro E E' h; ext x; rfl }

/-- The diagram `E ↦ C ⊗[F] E` over the finite subextensions of `L / F`. -/
private noncomputable def tensorSubextensionDiagram : FExt F L ⥤ CommAlgCat.{u} C :=
  subextensionAlgDiagram F L ⋙ baseChangeCommAlgCat F C

/-- The cocone on `AlgebraicGeometry.tensorSubextensionDiagram` whose vertex is
`C ⊗[F] L`. -/
private noncomputable def tensorSubextensionCocone :
    Cocone (tensorSubextensionDiagram F L C) :=
  (baseChangeCommAlgCat F C).mapCocone (subextensionAlgCocone F L)

/-- **`C ⊗[F] L` is the filtered colimit of the `C ⊗[F] E` over the finite subextensions `E`
of an algebraic extension `L / F`.** -/
private noncomputable def isColimitTensorSubextensionCocone [Algebra.IsAlgebraic F L] :
    IsColimit (tensorSubextensionCocone F L C) := by
  haveI : Nonempty (FExt F L) := IsFiltered.nonempty
  haveI := IsFiltered.isDirectedOrder (FExt F L)
  refine IsColimit.ofExistsUnique fun s => ?_
  let : Algebra F s.pt := ((algebraMap C s.pt).comp (algebraMap F C)).toAlgebra
  have : IsScalarTower F C s.pt := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hdir : Directed (· ≤ ·) (fun E : FExt F L => E.1.toSubalgebra) :=
    Monotone.directed_le fun _ _ h => IntermediateField.toSubalgebra_le_toSubalgebra.2 h
  let leg : ∀ E : FExt F L, E.1.toSubalgebra →ₐ[F] s.pt :=
    fun E => (AlgHom.liftEquiv F C E.1 s.pt).symm (s.ι.app E).hom
  have hcompat : ∀ (E E' : FExt F L) (h : E.1.toSubalgebra ≤ E'.1.toSubalgebra),
      leg E = (leg E').comp (Subalgebra.inclusion h) := by
    intro E E' h
    refine AlgHom.ext fun x => ?_
    exact (ConcreteCategory.congr_hom
      (s.w (homOfLE (IntermediateField.toSubalgebra_le_toSubalgebra.1 h) : E ⟶ E'))
      ((1 : C) ⊗ₜ[F] x)).symm
  have htop : (⊤ : Subalgebra F L) ≤ ⨆ E : FExt F L, E.1.toSubalgebra := fun x _ =>
    le_iSup (fun E : FExt F L => E.1.toSubalgebra) (fextStage x)
      (IntermediateField.mem_adjoin_simple_self F x)
  let g : L →ₐ[F] s.pt :=
    (Subalgebra.iSupLift (fun E : FExt F L => E.1.toSubalgebra) hdir leg hcompat ⊤ htop).comp
      Subalgebra.topEquiv.symm.toAlgHom
  have hg : ∀ (E : FExt F L) (x : E.1),
      g (x : L) = (s.ι.app E).hom ((1 : C) ⊗ₜ[F] x) := fun E x =>
    Subalgebra.iSupLift_mk (K := fun E : FExt F L => E.1.toSubalgebra) (dir := hdir)
      (f := leg) (hf := hcompat) (T := ⊤) x trivial
  have hfac : ∀ (E : FExt F L) (x : E.1), (AlgHom.liftEquiv F C L s.pt g) ((1 : C) ⊗ₜ[F] (x : L)) =
      (s.ι.app E).hom ((1 : C) ⊗ₜ[F] x) := fun E x => by simpa using hg E x
  refine ⟨CommAlgCat.ofHom (AlgHom.liftEquiv F C L s.pt g), fun E => ?_, ?_⟩
  · exact CommAlgCat.hom_ext (Algebra.TensorProduct.ext_ring (AlgHom.ext (hfac E)))
  · intro m hm
    have key : ∀ x : L, m.hom ((1 : C) ⊗ₜ[F] x) =
        (AlgHom.liftEquiv F C L s.pt g) ((1 : C) ⊗ₜ[F] x) := fun x =>
      (ConcreteCategory.congr_hom (hm (fextStage x)) ((1 : C) ⊗ₜ[F] _)).trans
        (hfac (fextStage x) ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩).symm
    exact CommAlgCat.hom_ext (Algebra.TensorProduct.ext_ring (AlgHom.ext key))

/-- For a separable extension `L / F` and a finite subextension `E`, the `C`-algebra
`C ⊗[F] E` is étale. -/
private theorem etale_tensor_subextension [Algebra.IsSeparable F L]
    (E : IntermediateField F L) [FiniteDimensional F E] : Algebra.Etale C (C ⊗[F] E) := by
  have : Algebra.Etale F E :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable F E
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  infer_instance

/-- **A separable algebraic extension, base changed to a separably closed field, is a filtered
colimit of finite products of copies of that field.** For `L / F` separable algebraic and
`C / F` with `C` separably closed, `C ⊗[F] L` is the filtered colimit over the finite
subextensions `E` of `L / F` of the algebras `C ⊗[F] E`, each of which is a finite product of
copies of `C`. -/
theorem isFilteredColimitOfFiniteProducts_tensorProduct_of_isSeparable
    [Algebra.IsSeparable F L] [IsSepClosed C] :
    IsFilteredColimitOfFiniteProducts C (C ⊗[F] L) := by
  refine ⟨FExt F L, inferInstance, inferInstance, tensorSubextensionDiagram F L C,
    tensorSubextensionCocone F L C, ⟨isColimitTensorSubextensionCocone F L C⟩, ⟨Iso.refl _⟩,
    fun E => ?_⟩
  have : FiniteDimensional F E.1 := E.2
  have : Algebra.Etale C (C ⊗[F] E.1) := etale_tensor_subextension F L C E.1
  obtain ⟨n, ⟨e⟩⟩ := exists_algEquiv_fun_fin C (C ⊗[F] E.1)
  exact ⟨n, ⟨CommAlgCat.isoMk e⟩⟩

end AlgebraicGeometry

end
