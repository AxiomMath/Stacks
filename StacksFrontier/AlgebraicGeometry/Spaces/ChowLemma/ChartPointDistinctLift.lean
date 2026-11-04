module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementDistinct
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.FieldExtensionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdPresheafLift
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Distinct field-valued points of an étale chart lift to the complement of the diagonals

Let `X` be an algebraic space over `S`, let `W ⟶ X` be a separated étale chart, and let
`K` be a field whose spectrum lies in the chosen big fppf site. Given `d` **pairwise distinct**
morphisms `w₀, …, w_{d-1} : Spec K ⟶ W` of the site all lying over a single morphism
`Spec K ⟶ X`, this file produces a morphism `Spec K ⟶ V` into the complement of the diagonals
in the `d`-fold self-product of the chart over `X` whose `k`-th projection is `w k`.

This is the converse of
`AlgebraicGeometry.Space.SpacesEtale.comp_yoneda_map_diagonalComplementProj_ne`, which says
that distinct projections of the complement of the diagonals never agree; it is the direction
the surjectivity step of [Stacks, Tag 089J] needs, and it is harder, because membership in the
collision locus `AlgebraicGeometry.Space.SpacesEtale.collisionPoints` is a statement about
*points* — equivalence classes of field-valued points — and so only gives a coincidence of
morphisms after passage to some field extension of `K`. That extension is an arbitrary
compositum, with no finiteness property, and the coincidence is pushed back down along it by
`AlgebraicGeometry.Space.eq_of_comp_eq_of_flat_surjective_quasiCompact`: a morphism of field
spectra is flat, surjective and quasi-compact, hence an effective epimorphism of schemes.

## Main results

* `AlgebraicGeometry.Space.quasiCompact_surjective_flat_of_fieldSpecHom`: **every morphism
  between spectra of fields is quasi-compact, surjective and flat.** No hypothesis relates the
  two fields: the morphism is identified with `Spec` of a ring homomorphism through
  `AlgebraicGeometry.Spec.fullyFaithful`, and a homomorphism out of a field is faithfully flat
  because every module over a field is free.
* `AlgebraicGeometry.Space.eq_of_comp_eq_fieldSpecSite`: a morphism of the big fppf category
  over `S` between objects given by field spectra is an epimorphism.
* `AlgebraicGeometry.Space.SpacesEtale.notMem_collisionPoints_of_ne`: **the point-level
  converse.** If two of the `d` morphisms into the chart differ, then the canonical point of
  `Spec K` is carried by their common lift to the self-product outside the locus where those
  two factors collide.
* `AlgebraicGeometry.Space.SpacesEtale.mem_diagonalComplementPoints_of_injective`: pairwise
  distinct morphisms into the chart give a lift all of whose points avoid every diagonal.
* `AlgebraicGeometry.Space.SpacesEtale.exists_comp_diagonalComplementProj_eq`: **`d` pairwise
  distinct `K`-points of the chart over one `K`-point of `X` give a `K`-point of the complement
  of the diagonals with those projections.**

## Implementation notes

`AlgebraicGeometry.Space.SpacesEtale.exists_lift_underlying_selfProd` supplies the lift of the
family to the self-product, because the universal property of the self-product in the
spaces-étale site is unavailable for a source which is not étale over `X`. What remains is to
show that the lift avoids the diagonals, and the chain is: unfold
`AlgebraicGeometry.Space.SpacesEtale.collisionPoints`, read the resulting equality of points
through `AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff` as a single common field
extension `ε`, translate the two dominations into equalities of morphisms of presheaves with
`CategoryTheory.yonedaEquiv_naturality`, compose with the two projections of `W ×_X W`, and
cancel `ε`.

Two mechanical points are worth recording.

First, `AlgebraicGeometry.Space.FieldValuedPoint.siteObject` hands back an abstract morphism of
field spectra, and the flatness of such a morphism is not an instance; it has to be identified
as `Spec.map φ` for a ring homomorphism `φ` first. That is what
`…quasiCompact_surjective_flat_of_fieldSpecHom` is for.

Second, the chart's underlying presheaf is `yoneda.obj W` only after unfolding
`AlgebraicGeometry.Space.SpacesEtale.chartObj`, which is not reducible, so the two spellings of
that presheaf are interchangeable for the elaborator but not for the matching used by `rw` and
`simp`. The associativity steps below are therefore carried out by explicit `Category.assoc`
terms rather than by rewriting.

That the lift avoids the diagonals *at every point* — which is what the factorisation through
the open subspace needs — is not an extra argument: the point set of the spectrum of a field is
a singleton by `AlgebraicGeometry.Space.subsingleton_points_yoneda_siteObject`.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A morphism of field spectra is an effective epimorphism -/

/-- **Every morphism between spectra of fields is quasi-compact, surjective and flat.**

No relation between the two fields is assumed, and in particular no finiteness: the morphism is
identified with `Spec` of a ring homomorphism `φ : K ⟶ Ω` through
`AlgebraicGeometry.Spec.fullyFaithful`, and `φ` is faithfully flat because `Ω` is a free
`K`-module, `K` being a field. Quasi-compactness is then the affineness of `Spec.map φ`. -/
theorem quasiCompact_surjective_flat_of_fieldSpecHom {Om K : Type u} [Field Om] [Field K]
    (g : Spec (CommRingCat.of Om) ⟶ Spec (CommRingCat.of K)) :
    QuasiCompact g ∧ Surjective g ∧ Flat g := by
  have hpre : Spec.map (Spec.fullyFaithful.preimage g).unop = g :=
    Spec.fullyFaithful.map_preimage _
  set φ : CommRingCat.of K ⟶ CommRingCat.of Om := (Spec.fullyFaithful.preimage g).unop with hφ
  let : Algebra K Om := (CommRingCat.Hom.hom φ).toAlgebra
  have hff : (CommRingCat.Hom.hom φ).FaithfullyFlat :=
    Module.FaithfullyFlat.instOfNontrivialOfFree K Om
  obtain ⟨hflat, hsurj⟩ := (AlgebraicGeometry.flat_and_surjective_SpecMap_iff φ).2 hff
  refine ⟨?_, ?_, ?_⟩ <;> rw [← hpre]
  · infer_instance
  · exact hsurj
  · exact hflat

/-- **A morphism of the big fppf category over `S` between objects given by spectra of fields
can be cancelled on the left.** This is
`AlgebraicGeometry.Space.eq_of_comp_eq_of_flat_surjective_quasiCompact` supplied with the three
properties of a morphism of field spectra, which are
`AlgebraicGeometry.Space.quasiCompact_surjective_flat_of_fieldSpecHom`.

It is the step which turns a coincidence of morphisms detected only after a field extension
back into a coincidence over the original field. The extension is arbitrary — it is the
compositum produced by `AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff` — so no
finiteness hypothesis may be used. -/
theorem eq_of_comp_eq_fieldSpecSite {Om K : Type u} [Field Om] [Field K]
    (hOm : B.Contains (Spec (CommRingCat.of Om))) (hK : B.Contains (Spec (CommRingCat.of K)))
    (bOm : Spec (CommRingCat.of Om) ⟶ S) (bK : Spec (CommRingCat.of K) ⟶ S)
    (ε : siteObject B S hS hOm bOm ⟶ siteObject B S hS hK bK)
    {Z : BigFppfOver B S hS} (a a' : siteObject B S hS hK bK ⟶ Z)
    (h : ε ≫ a = ε ≫ a') : a = a' := by
  obtain ⟨hqc, hsurj, hflat⟩ :=
    quasiCompact_surjective_flat_of_fieldSpecHom (Om := Om) (K := K)
      ((BigFppfOver.toScheme B S hS).map ε)
  exact eq_of_comp_eq_of_flat_surjective_quasiCompact B S hS ε hqc hsurj hflat a a' h

namespace SpacesEtale

variable (X : AlgebraicSpaces B S hS)

/-! ### The point-level converse -/

/-- **Two distinct `K`-points of the chart do not collide.** Let `w : Fin m → (Spec K ⟶ W)` be
morphisms of the site into an étale chart `W ⟶ X` and let `f` be a morphism of presheaves from
`Spec K` into the `m`-fold self-product of the chart over `X` whose `k`-th projection is `w k`.
If `w i ≠ w j`, then the image under `f` of the canonical point of `Spec K` avoids the locus
where the `i`-th and `j`-th factors of the self-product agree.

Membership in that locus means that the pair of projections carries the point into the point
set of the diagonal of `W ×_X W`. Two field-valued points define the same point of an
algebraic space exactly when they admit one common field extension, so there is a field `Ω` in
the site, a morphism `ε : Spec Ω ⟶ Spec K` over `S` and a morphism `v : Spec Ω ⟶ W` with
`ε ≫ f ≫ (πᵢ, πⱼ) = v ≫ Δ` as morphisms of presheaves. Composing with the two projections of
`W ×_X W` gives `ε ≫ w i = v = ε ≫ w j`, and `ε` can be cancelled by
`AlgebraicGeometry.Space.eq_of_comp_eq_fieldSpecSite`.

Note that nothing is asserted about the *images* of the `w k` in the point set of `W`: distinct
`K`-points of the chart over one `K`-point of `X` may perfectly well have the same image
point. -/
theorem notMem_collisionPoints_of_ne
    (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (m : ℕ) {K : Type u} [Field K] (hK : B.Contains (Spec (CommRingCat.of K)))
    (b : Spec (CommRingCat.of K) ⟶ S)
    (w : Fin m → (siteObject B S hS hK b ⟶ W))
    (f : yoneda.obj (siteObject B S hS hK b) ⟶
      (underlying B S hS X (selfProd B S hS X (chartObj B S hS X W c hc) m)).obj)
    (hf : ∀ k, f ≫ ((toSpaces B S hS X).map
        (Pi.π (fun _ : Fin m ↦ chartObj B S hS X W c hc) k)).hom = yoneda.map (w k))
    {i j : Fin m} (hne : w i ≠ w j) :
    pointsMap B S hS _ f (fieldSpecPoint B S hS hK b) ∉
      collisionPoints B S hS X (chartObj B S hS X W c hc) m i j := by
  intro hmem
  rw [collisionPoints, Set.mem_preimage] at hmem
  obtain ⟨y, hy⟩ := hmem
  induction y using Quot.ind with | _ q =>
  rw [← pointsMap_comp_apply] at hy
  have hy2 : FieldValuedPoint.HasCommonExtension B S hS
      (underlying B S hS X (prodTwo B S hS X (chartObj B S hS X W c hc))).obj
      (FieldValuedPoint.map B S hS _
        ((toSpaces B S hS X).map (diagTwo B S hS X (chartObj B S hS X W c hc))).hom q)
      (FieldValuedPoint.map B S hS _
        (f ≫ ((toSpaces B S hS X).map
          (projPair B S hS X (chartObj B S hS X W c hc) m i j)).hom)
        ({ carrier := K, contained := hK, toBase := b, value := 𝟙 _ } :
          FieldValuedPoint B S hS (yoneda.obj (siteObject B S hS hK b)))) :=
    (FieldValuedPoint.class_eq_class_iff B S hS _ _ _).1 hy
  obtain ⟨r, ⟨δ, hδ⟩, ⟨ε, hε⟩⟩ := hy2
  -- the common extension, read as morphisms of the site and of presheaves
  let ε' : FieldValuedPoint.siteObject B S hS
      (underlying B S hS X (prodTwo B S hS X (chartObj B S hS X W c hc))).obj r ⟶
    siteObject B S hS hK b := ε
  let δ' : FieldValuedPoint.siteObject B S hS
      (underlying B S hS X (prodTwo B S hS X (chartObj B S hS X W c hc))).obj r ⟶
    FieldValuedPoint.siteObject B S hS
      (underlying B S hS X (chartObj B S hS X W c hc)).obj q := δ
  obtain ⟨uy, huy⟩ : ∃ uy : yoneda.obj (FieldValuedPoint.siteObject B S hS
      (underlying B S hS X (chartObj B S hS X W c hc)).obj q) ⟶
      ((toSpaces B S hS X).obj (chartObj B S hS X W c hc)).obj, yonedaEquiv uy = q.value :=
    ⟨yonedaEquiv.symm q.value, yonedaEquiv.apply_symm_apply _⟩
  have hεy : yonedaEquiv (yoneda.map ε' ≫ (f ≫ ((toSpaces B S hS X).map
      (projPair B S hS X (chartObj B S hS X W c hc) m i j)).hom)) = r.value :=
    (yonedaEquiv_naturality _ ε').symm.trans hε
  have hvalue : yonedaEquiv (uy ≫ ((toSpaces B S hS X).map
        (diagTwo B S hS X (chartObj B S hS X W c hc))).hom) =
      (FieldValuedPoint.map B S hS _ ((toSpaces B S hS X).map
        (diagTwo B S hS X (chartObj B S hS X W c hc))).hom q).value := by
    rw [yonedaEquiv_comp, huy]
    rfl
  have hδy : yonedaEquiv (yoneda.map δ' ≫ (uy ≫ ((toSpaces B S hS X).map
      (diagTwo B S hS X (chartObj B S hS X W c hc))).hom)) = r.value := by
    rw [← yonedaEquiv_naturality, hvalue]
    exact hδ
  have heq : yoneda.map ε' ≫ (f ≫ ((toSpaces B S hS X).map
        (projPair B S hS X (chartObj B S hS X W c hc) m i j)).hom) =
      (yoneda.map δ' ≫ uy) ≫ ((toSpaces B S hS X).map
        (diagTwo B S hS X (chartObj B S hS X W c hc))).hom :=
    (yonedaEquiv.injective (hεy.trans hδy.symm)).trans (Category.assoc _ _ _).symm
  -- composing with either projection of `W ×_X W` identifies the two `K`-points
  have step : ∀ (pr : prodTwo B S hS X (chartObj B S hS X W c hc) ⟶
        chartObj B S hS X W c hc) (k : Fin m),
      projPair B S hS X (chartObj B S hS X W c hc) m i j ≫ pr =
        Pi.π (fun _ : Fin m ↦ chartObj B S hS X W c hc) k →
      diagTwo B S hS X (chartObj B S hS X W c hc) ≫ pr =
        𝟙 (chartObj B S hS X W c hc) →
      yoneda.map ε' ≫ (f ≫ ((toSpaces B S hS X).map
        (Pi.π (fun _ : Fin m ↦ chartObj B S hS X W c hc) k)).hom) =
          yoneda.map δ' ≫ uy := by
    intro pr k hpr hdg
    have hprh : ((toSpaces B S hS X).map
          (projPair B S hS X (chartObj B S hS X W c hc) m i j)).hom ≫
        ((toSpaces B S hS X).map pr).hom =
        ((toSpaces B S hS X).map
          (Pi.π (fun _ : Fin m ↦ chartObj B S hS X W c hc) k)).hom := by
      rw [← hom_toSpaces_map_comp, hpr]
    have hdgh : ((toSpaces B S hS X).map
          (diagTwo B S hS X (chartObj B S hS X W c hc))).hom ≫
        ((toSpaces B S hS X).map pr).hom = 𝟙 _ := by
      rw [← hom_toSpaces_map_comp, hdg, CategoryTheory.Functor.map_id]
      rfl
    have h := congrArg (· ≫ ((toSpaces B S hS X).map pr).hom) heq
    simpa only [Category.assoc, hprh, hdgh, Category.comp_id] using h
  have hcol : yoneda.map ε' ≫ (f ≫ ((toSpaces B S hS X).map
        (Pi.π (fun _ : Fin m ↦ chartObj B S hS X W c hc) i)).hom) =
      yoneda.map ε' ≫ (f ≫ ((toSpaces B S hS X).map
        (Pi.π (fun _ : Fin m ↦ chartObj B S hS X W c hc) j)).hom) :=
    (step (pullback.fst (toFinal B S hS (chartObj B S hS X W c hc))
          (toFinal B S hS (chartObj B S hS X W c hc))) i
        (projPair_comp_fst B S hS X (chartObj B S hS X W c hc) m i j)
        (diagTwo_comp_fst B S hS X (chartObj B S hS X W c hc))).trans
      (step (pullback.snd (toFinal B S hS (chartObj B S hS X W c hc))
          (toFinal B S hS (chartObj B S hS X W c hc))) j
        (projPair_comp_snd B S hS X (chartObj B S hS X W c hc) m i j)
        (diagTwo_comp_snd B S hS X (chartObj B S hS X W c hc))).symm
  refine hne (eq_of_comp_eq_fieldSpecSite B S hS r.contained hK r.toBase b ε' (w i) (w j)
    (yoneda.map_injective ?_))
  rw [Functor.map_comp, Functor.map_comp, ← hf i, ← hf j]
  exact hcol

/-- **A lift of pairwise distinct `K`-points of the chart lands in the complement of the
diagonals at every point.** The quantification over all points of the spectrum of `K` is not an
extra hypothesis: the point set of the spectrum of a field, read as a representable presheaf, is
a singleton, so there is only the canonical point to check, and
`AlgebraicGeometry.Space.SpacesEtale.notMem_collisionPoints_of_ne` checks it. -/
theorem mem_diagonalComplementPoints_of_injective
    (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (m : ℕ) {K : Type u} [Field K] (hK : B.Contains (Spec (CommRingCat.of K)))
    (b : Spec (CommRingCat.of K) ⟶ S)
    (w : Fin m → (siteObject B S hS hK b ⟶ W)) (hinj : Function.Injective w)
    (f : yoneda.obj (siteObject B S hS hK b) ⟶
      (underlying B S hS X (selfProd B S hS X (chartObj B S hS X W c hc) m)).obj)
    (hf : ∀ k, f ≫ ((toSpaces B S hS X).map
        (Pi.π (fun _ : Fin m ↦ chartObj B S hS X W c hc) k)).hom = yoneda.map (w k))
    (y : points B S hS (yoneda.obj (siteObject B S hS hK b))) :
    pointsMap B S hS _ f y ∈
      diagonalComplementPoints B S hS X (chartObj B S hS X W c hc) m := by
  have hsub : Subsingleton (points B S hS (yoneda.obj (siteObject B S hS hK b))) :=
    subsingleton_points_yoneda_siteObject B S hS
      ({ carrier := K, contained := hK, toBase := b, value := 𝟙 _ } :
        FieldValuedPoint B S hS (yoneda.obj (siteObject B S hS hK b)))
  rw [Subsingleton.elim y (fieldSpecPoint B S hS hK b), mem_diagonalComplementPoints_iff]
  exact fun i j hij ↦
    notMem_collisionPoints_of_ne B S hS X W c hc m hK b w f hf (fun h ↦ hij (hinj h))

/-- **`d` pairwise distinct `K`-points of a separated étale chart, all lying over one
`K`-point of the algebraic space, give a `K`-point of the complement of the diagonals whose
projections are exactly those points.**

Here `V` is an object of the site presented with an identification `e` of the presheaf it
represents with the complement of the diagonals in the `d`-fold self-product of the chart over
`X`, which is how `AlgebraicGeometry.Space.SpacesEtale.exists_diagonalComplementObj` delivers
it; the projections are
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementProj`.

The number of points is written `m + 1` because the empty self-product is a final object of the
spaces-étale site and not the chart, so the lift of a family to the self-product is available
only for a nonempty family.

This is the converse of
`AlgebraicGeometry.Space.SpacesEtale.comp_yoneda_map_diagonalComplementProj_ne` and the
geometric half of the surjectivity step of [Stacks, Tag 089J]. It is *not* that step: nothing
here produces the `d` distinct `K`-points, which over the open where the fibre degree of the
chart is minimal requires a separable extension of the residue field of a point of `X`. -/
theorem exists_comp_diagonalComplementProj_eq
    (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS c) (m : ℕ) (V : BigFppfOver B S hS)
    (e : yoneda.obj V ≅ (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) (m + 1) hsep)).obj)
    {K : Type u} [Field K] (hK : B.Contains (Spec (CommRingCat.of K)))
    (b : Spec (CommRingCat.of K) ⟶ S)
    (w : Fin (m + 1) → (siteObject B S hS hK b ⟶ W)) (hinj : Function.Injective w)
    (hover : ∀ k, yoneda.map (w k) ≫ c = yoneda.map (w 0) ≫ c) :
    ∃ t₀ : siteObject B S hS hK b ⟶ V,
      ∀ k, t₀ ≫ diagonalComplementProj B S hS X W c hc hsep (m + 1) V e k = w k := by
  obtain ⟨f, hf, -⟩ := exists_lift_underlying_selfProd B S hS X (chartObj B S hS X W c hc)
    (F := yoneda.obj (siteObject B S hS hK b)) (yoneda.map (w 0) ≫ c) m
    (fun k ↦ yoneda.map (w k)) hover
  have hle : Subfunctor.range f ≤
      (diagonalComplementSubspace B S hS X (chartObj B S hS X W c hc) (m + 1) hsep).1 :=
    range_le_openSubspaceOfPoints B S hS f _
      (mem_diagonalComplementPoints_of_injective B S hS X W c hc (m + 1) hK b w hinj f hf)
  let lf : yoneda.obj (siteObject B S hS hK b) ⟶ (underlying B S hS X
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) (m + 1) hsep)).obj :=
    Subfunctor.lift f hle
  have hlfι : lf ≫ ((toSpaces B S hS X).map
      (diagonalComplementι B S hS X (chartObj B S hS X W c hc) (m + 1) hsep)).hom = f :=
    Subfunctor.lift_ι f hle
  refine ⟨yoneda.preimage (lf ≫ e.inv), fun k ↦ ?_⟩
  refine yoneda.map_injective ?_
  have hπ : ((toSpaces B S hS X).map (diagonalComplementπ B S hS X
        (chartObj B S hS X W c hc) (m + 1) hsep k)).hom =
      ((toSpaces B S hS X).map
        (diagonalComplementι B S hS X (chartObj B S hS X W c hc) (m + 1) hsep)).hom ≫
      ((toSpaces B S hS X).map
        (Pi.π (fun _ : Fin (m + 1) ↦ chartObj B S hS X W c hc) k)).hom :=
    hom_toSpaces_map_comp B S hS X _ _
  rw [Functor.map_comp, yoneda.map_preimage,
    yoneda_map_diagonalComplementProj B S hS X W c hc hsep (m + 1) V e k, Category.assoc]
  refine Eq.trans (congrArg (fun z ↦ lf ≫ z) (e.inv_hom_id_assoc _)) ?_
  refine Eq.trans (congrArg (fun z ↦ lf ≫ z) hπ) ?_
  refine Eq.trans (Category.assoc lf _ _).symm ?_
  exact Eq.trans (congrArg (fun z ↦ z ≫ ((toSpaces B S hS X).map
    (Pi.π (fun _ : Fin (m + 1) ↦ chartObj B S hS X W c hc) k)).hom) hlfι) (hf k)

end SpacesEtale

end AlgebraicGeometry.Space

end
