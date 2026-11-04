module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksCore.Tactic.StacksAttribute

/-!
# Unramified schemes over a field

A scheme unramified over a field is a disjoint union of spectra of finite separable extensions of
that field. If in addition the structure morphism is quasi-compact, the index set of that
disjoint union is finite, so the scheme is affine, and its coordinate ring is a finite product of
finite separable field extensions. A connected such scheme is the spectrum of a single finite
separable extension. Over a field, unramifiedness and étaleness agree.

## Main results

* `AlgebraicGeometry.unramified_iff_stalkwiseUnramified` identifies the stalkwise and the
  affine-local notions of unramifiedness globally, for a locally finite type morphism to a
  locally Noetherian scheme.
* `AlgebraicGeometry.isAffine_of_unramified_quasiCompact`: a quasi-compact unramified scheme over
  a field is affine.
* `AlgebraicGeometry.unramified_quasiCompact_iff_iso_finite_coproduct_spectra_finite_separable`
  classifies such schemes by finite families of finite separable field extensions.
* `AlgebraicGeometry.exists_iso_spec_finite_separable_of_connected_unramified` is the connected
  case: a single finite separable extension.
* `AlgebraicGeometry.etale_iff_unramified_over_field`: over a field, étaleness and unramifiedness
  coincide.

## References

* [Stacks Project, Tag 024X](https://stacks.math.columbia.edu/tag/024X)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- For a morphism locally of finite type to a locally Noetherian scheme, the stalkwise notion of
unramifiedness agrees with the affine-local one. -/
public theorem unramified_iff_stalkwiseUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    StalkwiseUnramified f ↔ Unramified f :=
  ⟨fun h => ⟨fun x => (unramifiedAt_iff_morphisms_unramifiedAt f x).mp (h.unramifiedAt x)⟩,
    fun h => ⟨fun x => (unramifiedAt_iff_morphisms_unramifiedAt f x).mpr (h.unramifiedAt x)⟩⟩

/-- A compact scheme isomorphic to a coproduct of nonempty schemes has a finite index set. -/
private theorem finite_of_compactSpace_of_iso_coproduct {I : Type u} {X : Scheme.{u}}
    (Y : I → Scheme.{u}) [∀ i, Nonempty (Y i)] [CompactSpace X] (e : X ≅ ∐ Y) : Finite I := by
  let : TopologicalSpace I := ⊥
  let : DiscreteTopology I := ⟨rfl⟩
  let g : X → I := fun x => ((sigmaMk Y).symm (e.hom x)).1
  have hg : Continuous g := by
    refine (continuous_sigma fun _ => continuous_const).comp
      ((sigmaMk Y).symm.continuous.comp ?_)
    fun_prop
  have hsurj : Function.Surjective g := fun i ↦ by
    obtain ⟨x⟩ := (inferInstance : Nonempty ↥(Y i))
    exact ⟨e.inv (sigmaMk Y ⟨i, x⟩), by simp [g, -sigmaMk_mk]⟩
  have hfinite : (Set.range g).Finite := by
    simpa only [Set.image_univ] using (isCompact_univ.image hg).finite_of_discrete
  exact Set.finite_univ_iff.mp (hsurj.range_eq ▸ hfinite)

/-- A morphism to the spectrum of a field that is locally of finite type and stalkwise unramified
decomposes, over that spectrum, as a coproduct of spectra of finite separable field extensions. -/
private theorem exists_iso_coproduct_spectra_finite_separable_of_stalkwiseUnramified
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [StalkwiseUnramified f] :
    ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
      (_ : ∀ i, Algebra.IsSeparable k (K i))
      (e : X ≅ ∐ fun i ↦ Spec (.of (K i))),
      e.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) = f :=
  (unramified_iff_iso_coproduct_spectra_finite_separable k f).mp
    ((unramified_iff_stalkwiseUnramified f).mp inferInstance)

/-- A morphism to the spectrum of a field is locally of finite type and stalkwise unramified
exactly when its source decomposes, over that spectrum, as a coproduct of spectra of finite
separable field extensions. -/
public theorem stalkwiseUnramified_iff_iso_coproduct_spectra_finite_separable
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    (∃ h : LocallyOfFiniteType f, letI := h; StalkwiseUnramified f) ↔
      ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
        (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
        (_ : ∀ i, Algebra.IsSeparable k (K i))
        (e : X ≅ ∐ fun i ↦ Spec (.of (K i))),
        e.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) = f := by
  constructor
  · rintro ⟨hft, hU⟩
    exact exists_iso_coproduct_spectra_finite_separable_of_stalkwiseUnramified k f
  · intro h
    have hU : Unramified f := (unramified_iff_iso_coproduct_spectra_finite_separable k f).mpr h
    have hft := ((unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp hU).1
    exact ⟨hft, (unramified_iff_stalkwiseUnramified f).mpr hU⟩

/-- A quasi-compact scheme unramified over a field is a coproduct of spectra of finite separable
field extensions indexed by a finite set. -/
private theorem exists_finite_iso_coproduct_spectra_finite_separable
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [StalkwiseUnramified f] [QuasiCompact f] :
    ∃ (I : Type u) (_ : Finite I) (K : I → Type u) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
      (_ : ∀ i, Algebra.IsSeparable k (K i))
      (e : X ≅ ∐ fun i ↦ Spec (.of (K i))),
      e.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) = f := by
  obtain ⟨I, K, hK, hA, hF, hS, e, he⟩ :=
    exists_iso_coproduct_spectra_finite_separable_of_stalkwiseUnramified k f
  let (i : I) : Field (K i) := hK i
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨I, finite_of_compactSpace_of_iso_coproduct _ e, K, hK, hA, hF, hS, e, he⟩

/-- A quasi-compact unramified scheme over a field is affine. -/
@[stacks 024X "affineness", ega "IV 17.15.11" "affineness in c)"]
public theorem isAffine_of_unramified_quasiCompact
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [StalkwiseUnramified f] [QuasiCompact f] : IsAffine X := by
  obtain ⟨I, hI, K, hK, hA, hF, hS, e, he⟩ :=
    exists_finite_iso_coproduct_spectra_finite_separable k f
  exact IsAffine.of_isIso e.hom

/-- A morphism to the spectrum of a field is quasi-compact and unramified exactly when its
source is a finite disjoint union of spectra of finite separable field extensions, compatibly
with the map to the base field. -/
@[stacks 024X "finite separable classification"]
public theorem unramified_quasiCompact_iff_iso_finite_coproduct_spectra_finite_separable
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    ((∃ h : LocallyOfFiniteType f, letI := h; StalkwiseUnramified f) ∧ QuasiCompact f) ↔
      ∃ (I : Type u) (_ : Finite I) (K : I → Type u) (_ : ∀ i, Field (K i))
        (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
        (_ : ∀ i, Algebra.IsSeparable k (K i))
        (e : X ≅ ∐ fun i ↦ Spec (.of (K i))),
        e.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) = f := by
  constructor
  · rintro ⟨⟨hft, hU⟩, hqc⟩
    have : StalkwiseUnramified f := hU
    exact exists_finite_iso_coproduct_spectra_finite_separable k f
  · rintro ⟨I, hI, K, hK, hA, hF, hS, e, he⟩
    let := hI
    refine ⟨(stalkwiseUnramified_iff_iso_coproduct_spectra_finite_separable k f).mpr
      ⟨I, K, hK, hA, hF, hS, e, he⟩, ?_⟩
    let (i : I) : Field (K i) := hK i
    have : CompactSpace ↥(∐ fun i ↦ Spec (.of (K i))) :=
      (sigmaMk fun i ↦ Spec (.of (K i))).compactSpace
    have : CompactSpace ↥X := (Scheme.homeoOfIso e.symm).compactSpace
    exact (quasiCompact_iff_compactSpace f).mpr inferInstance

/-- A connected unramified scheme over a field is the spectrum of one finite separable field
extension, over the base field. -/
@[stacks 024X "connected case", ega "IV 17.15.11" "connected X, b) => c)"]
public theorem exists_iso_spec_finite_separable_of_connected_unramified
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [StalkwiseUnramified f] [ConnectedSpace X] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K)
      (_ : Algebra.IsSeparable k K) (e : X ≅ Spec (.of K)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) = f := by
  obtain ⟨I, K, hK, hA, hF, hS, e, he⟩ :=
    exists_iso_coproduct_spectra_finite_separable_of_stalkwiseUnramified k f
  let (i : I) : Field (K i) := hK i
  let (i : I) : Algebra k (K i) := hA i
  have hI : Nonempty I := by
    obtain ⟨x⟩ := (inferInstance : Nonempty ↥X)
    exact ⟨((sigmaMk fun i ↦ Spec (.of (K i))).symm (e.hom x)).1⟩
  have hconn : ConnectedSpace (Σ i, Spec (.of (K i))) :=
    ((sigmaMk fun i ↦ Spec (.of (K i))).trans
      (Scheme.homeoOfIso e.symm)).connectedSpace_iff.mpr ‹ConnectedSpace X›
  have : Subsingleton I := by
    refine ⟨fun i j => ?_⟩
    obtain ⟨a, t, ht, ha⟩ := Sigma.isConnected_iff.mp (connectedSpace_iff_univ.mp hconn)
    have hindex : ∀ i : I, i = a := by
      intro i
      obtain ⟨x⟩ := (inferInstance : Nonempty ↥(Spec (.of (K i))))
      have hx : (⟨i, x⟩ : Σ i, Spec (.of (K i))) ∈ Set.univ := Set.mem_univ _
      rw [ha] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact (congrArg Sigma.fst hxy).symm
    exact (hindex i).trans (hindex j).symm
  let : Unique I := uniqueOfSubsingleton (Classical.choice hI)
  have hmap : (coproductUniqueIso fun i ↦ Spec (.of (K i))).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (K default))) =
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) := by
    refine Sigma.hom_ext _ _ fun i => ?_
    obtain rfl : i = default := Subsingleton.elim _ _
    rw [← Category.assoc, ι_coproductUniqueIso_hom]
    simp
  refine ⟨K default, hK default, hA default, hF default, hS default,
    e.trans (coproductUniqueIso fun i ↦ Spec (.of (K i))), ?_⟩
  rw [Iso.trans_hom, Category.assoc, hmap, he]

/-- Over a field, a morphism is étale exactly when it is locally of finite type and unramified. -/
@[stacks 024X "étale iff unramified", ega "IV 17.15.11" "a) <=> b)"]
public theorem etale_iff_unramified_over_field
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    Etale f ↔ ∃ h : LocallyOfFiniteType f, letI := h; StalkwiseUnramified f :=
  (etale_iff_iso_coproduct_spectra_finite_separable k f).trans
    (stalkwiseUnramified_iff_iso_coproduct_spectra_finite_separable k f).symm

end AlgebraicGeometry
