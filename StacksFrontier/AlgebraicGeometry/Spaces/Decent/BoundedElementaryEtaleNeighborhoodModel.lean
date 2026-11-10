module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.InducedCategory
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PresheafPointTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A cofiltered initial model with explicit cardinal bounds, over an affine base

Let `x` be a point of an algebraic space `X` over `S` which is represented by an *affine* scheme
`X₀` of the chosen big fppf site. This file produces an initial functor to the category of
elementary étale neighborhoods of `x` from a `u`-small cofiltered category whose type of objects
and whose stage schemes both carry an explicit cardinal bound below the cutoff of the site.

Affineness of the base is what makes both bounds available at once. A morphism to an affine
scheme from an affine scheme that is étale -- hence locally of finite type -- is the spectrum of
a finite type algebra, so the ring of functions of an affine elementary étale neighborhood has
cardinality at most `max ℵ₀ #Γ(X₀, ⊤)` *uniformly*, which is the stage bound; and the finite type
algebras over a fixed ring are indexed up to isomorphism by Mathlib's
`FGAlgCatSkeleton`, a type of presentation data whose cardinality is at most
`2 ^ max ℵ₀ #Γ(X₀, ⊤)`, which is below the cutoff because the cutoff is a strong prelimit. That
is the bound on the index type.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood`
  `.exists_bounded_cofiltered_initial_model_of_iso` -- the bounded cofiltered initial model, for
  a chosen presentation of the space as an affine scheme of the site; the uniform stage bound is
  the size of that affine scheme.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_bounded_cofiltered_initial_model`
  -- the same statement with the presentation taken from
  `AlgebraicGeometry.Space.IsAffineSpace`.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood`
  `.exists_bounded_cofiltered_initial_affine_model_of_iso` -- the model of the first item, with
  affine stages and a fully faithful model functor.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Cardinality of the presentations of the finite type algebras over a ring -/

/-- **The finite type algebras over `R` admit at most `2 ^ max ℵ₀ #R` presentations.** A
presentation is a number of variables together with an ideal of the polynomial ring in that many
variables. -/
private theorem mk_fgAlgCatSkeleton_le (R : Type u) [CommRing R] :
    #(FGAlgCatSkeleton R) ≤ 2 ^ max ℵ₀ #R := by
  have hμ : ℵ₀ ≤ max ℵ₀ #R := le_max_left _ _
  have hpow : ℵ₀ ≤ (2 : Cardinal.{u}) ^ max ℵ₀ #R := hμ.trans (Cardinal.cantor _).le
  have hinj : Function.Injective
      (fun A : FGAlgCatSkeleton R => (⟨ULift.up A.n, A.I⟩ :
        Σ m : ULift.{u} ℕ, Ideal (MvPolynomial (Fin m.down) R))) := by
    intro A A' h
    obtain ⟨n, I⟩ := A
    obtain ⟨n', I'⟩ := A'
    simp only [Sigma.mk.injEq, ULift.up.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simpa using h2
  calc #(FGAlgCatSkeleton R)
      ≤ #(Σ m : ULift.{u} ℕ, Ideal (MvPolynomial (Fin m.down) R)) :=
        Cardinal.mk_le_of_injective hinj
    _ = Cardinal.sum (fun m : ULift.{u} ℕ => #(Ideal (MvPolynomial (Fin m.down) R))) :=
        Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : ULift.{u} ℕ => (2 : Cardinal.{u}) ^ max ℵ₀ #R) := by
        refine Cardinal.sum_le_sum _ _ (fun m => ?_)
        calc #(Ideal (MvPolynomial (Fin m.down) R))
            ≤ #(Set (MvPolynomial (Fin m.down) R)) :=
              Cardinal.mk_le_of_injective SetLike.coe_injective
          _ = 2 ^ #(MvPolynomial (Fin m.down) R) := Cardinal.mk_set
          _ ≤ 2 ^ max ℵ₀ #R :=
              Cardinal.power_le_power_left two_ne_zero
                (Cardinal.mk_mvPolynomial_fin_le R m.down)
    _ = #(ULift.{u} ℕ) * (2 : Cardinal.{u}) ^ max ℵ₀ #R := Cardinal.sum_const' _ _
    _ ≤ 2 ^ max ℵ₀ #R := by
        rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
        exact (Cardinal.mul_le_max _ _).trans (by simp [hpow])

/-- The cardinality of the algebra presented by a presentation datum is at most
`max ℵ₀ #R`. -/
private theorem mk_fgAlgCatSkeleton_eval_le (R : Type u) [CommRing R]
    (T : FGAlgCatSkeleton R) : #(T.eval.obj) ≤ max ℵ₀ #R := by
  have h : #(MvPolynomial (Fin T.n) R ⧸ T.I) ≤ #(MvPolynomial (Fin T.n) R) :=
    Cardinal.mk_le_of_surjective (f := Ideal.Quotient.mk T.I) Ideal.Quotient.mk_surjective
  exact h.trans (Cardinal.mk_mvPolynomial_fin_le R T.n)

/-- The points of an affine scheme are at most `2 ^` the cardinality of its ring. -/
private theorem mk_spec_le (A : CommRingCat.{u}) : #((Spec A) : Type u) ≤ 2 ^ #A := by
  have e : #((Spec A) : Type u) = #(PrimeSpectrum A) := rfl
  rw [e, ← Cardinal.mk_set (α := (A : Type u))]
  exact Cardinal.mk_le_of_injective (f := fun p => ((p.asIdeal : Ideal (A : Type u)) : Set A))
    (fun _ _ h => PrimeSpectrum.ext (SetLike.coe_injective h))

namespace ElementaryEtaleNeighborhood

/-! ### The bounded model over an affine base -/

section Pres

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X₀ : BigFppfOver B S hS)

/-- The ring presented by a presentation datum over the ring of functions of the base. -/
private abbrev presRing
    (T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) :
    CommRingCat.{u} :=
  CommRingCat.of (T.eval.obj : Type u)

/-- The structure morphism of the presented ring over the ring of functions of the base. -/
private def presAlgebraMap
    (T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) :
    Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) ⟶ presRing B S hS X₀ T :=
  CommRingCat.ofHom (algebraMap (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)
    (T.eval.obj : Type u))

/-- The cardinality of a presented ring is at most `max ℵ₀ #Γ(X₀, ⊤)`. -/
private theorem mk_presRing_le
    (T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) :
    #(presRing B S hS X₀ T) ≤
      max ℵ₀ #(Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u) :=
  mk_fgAlgCatSkeleton_eval_le _ T

end Pres

section PresAffine

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X₀ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj X₀)]

/-- The spectrum of a presented ring has size at most the size of the affine base. -/
private theorem size_spec_presRing_le
    (T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) :
    (Spec (presRing B S hS X₀ T)).size ≤ ((BigFppfOver.toScheme B S hS).obj X₀).size := by
  rw [Scheme.size_Spec, Scheme.size_of_isAffine ((BigFppfOver.toScheme B S hS).obj X₀)]
  exact max_le (le_max_left _ _) ((mk_presRing_le B S hS X₀ T).trans le_rfl)

/-- The spectrum of a presented ring belongs to the site. -/
private theorem contains_spec_presRing
    (T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) :
    B.Contains (Spec (presRing B S hS X₀ T)) :=
  lt_of_le_of_lt (size_spec_presRing_le B S hS X₀ T) X₀.left.property

/-- The canonical morphism of schemes from the spectrum of a presented ring to the affine
base. -/
private def presSpecHom
    (T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) :
    Spec (presRing B S hS X₀ T) ⟶ (BigFppfOver.toScheme B S hS).obj X₀ :=
  Spec.map (presAlgebraMap B S hS X₀ T) ≫
    ((BigFppfOver.toScheme B S hS).obj X₀).isoSpec.inv

/-- The object of the site given by the spectrum of a presented ring, with the structure
morphism obtained from the affine base. -/
private def presObj
    (T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) :
    BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (X := B.obj (contains_spec_presRing B S hS X₀ T))
    (Y := X₀.left) (presSpecHom B S hS X₀ T) ≫ X₀.hom)

/-- The canonical morphism of the site from the object presented by a datum to the affine
base. -/
private def presHom
    (T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) :
    presObj B S hS X₀ T ⟶ X₀ :=
  Over.homMk (B.inclusion.preimage (X := B.obj (contains_spec_presRing B S hS X₀ T))
    (Y := X₀.left) (presSpecHom B S hS X₀ T)) rfl

end PresAffine

section Model

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (X₀ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj X₀)]
    (eX : X ≅ yoneda.obj X₀) (x : points B S hS X)

/-- The canonical morphism from the presheaf represented by the object presented by a datum to
the algebraic space. -/
private def presToSpace
    (T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) :
    yoneda.obj (presObj B S hS X₀ T) ⟶ X :=
  yoneda.map (presHom B S hS X₀ T) ≫ eX.inv

/-- **The index type of the bounded model.** A presentation of a finite type algebra over the
ring of functions of the affine base, a point of the spectrum of the presented algebra, and the
three conditions making the canonical morphism to the space an elementary étale neighborhood of
`x` at that point. -/
private def BoundedIndex : Type u :=
  {d : Σ T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u),
      (presObj B S hS X₀ T).left.1 //
    IsEtale B S hS (presToSpace B S hS X₀ eX d.1) ∧
      pointsMap B S hS (yoneda.obj (presObj B S hS X₀ d.1)) (presToSpace B S hS X₀ eX d.1)
          (presheafPoint B S hS (presObj B S hS X₀ d.1) d.2
            (B.residueField_spec_contains (presObj B S hS X₀ d.1).left.property d.2)) = x ∧
        Mono (yoneda.map (residueFieldMap B S hS (presObj B S hS X₀ d.1) d.2
          (B.residueField_spec_contains (presObj B S hS X₀ d.1).left.property d.2)) ≫
          presToSpace B S hS X₀ eX d.1)}

/-- The elementary étale neighborhood presented by an element of the index type. -/
private def boundedModel (d : BoundedIndex B S hS X₀ eX x) :
    ElementaryEtaleNeighborhood B S hS X hX x where
  scheme := presObj B S hS X₀ d.1.1
  point := d.1.2
  residueField_contained :=
    B.residueField_spec_contains (presObj B S hS X₀ d.1.1).left.property d.1.2
  toSpace := presToSpace B S hS X₀ eX d.1.1
  etale_toSpace := d.2.1
  map_point := d.2.2.1
  mono_residueField := d.2.2.2

/-- **The index type of the bounded model has cardinality below the cutoff of the site.** -/
private theorem mk_boundedIndex_lt : #(BoundedIndex B S hS X₀ eX x) < B.cutoff := by
  have hμsize : max ℵ₀ #(Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u) =
      ((BigFppfOver.toScheme B S hS).obj X₀).size :=
    (Scheme.size_of_isAffine ((BigFppfOver.toScheme B S hS).obj X₀)).symm
  have hμlt : max ℵ₀ #(Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u) < B.cutoff := by
    rw [hμsize]
    exact X₀.left.property
  have hpow : ℵ₀ ≤ (2 : Cardinal.{u}) ^
      max ℵ₀ #(Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u) :=
    (le_max_left _ _).trans (Cardinal.cantor _).le
  refine lt_of_le_of_lt ?_ (B.cutoff_isStrongPrelimit hμlt)
  calc #(BoundedIndex B S hS X₀ eX x)
      ≤ #(Σ T : FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u),
          (presObj B S hS X₀ T).left.1) := Cardinal.mk_subtype_le _
    _ = Cardinal.sum (fun T : FGAlgCatSkeleton
          (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u) =>
          #((presObj B S hS X₀ T).left.1)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : FGAlgCatSkeleton
          (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u) =>
          (2 : Cardinal.{u}) ^
            max ℵ₀ #(Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) := by
        refine Cardinal.sum_le_sum _ _ (fun T => ?_)
        refine le_trans (mk_spec_le (presRing B S hS X₀ T)) ?_
        exact Cardinal.power_le_power_left two_ne_zero (mk_presRing_le B S hS X₀ T)
    _ = #(FGAlgCatSkeleton (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)) *
          (2 : Cardinal.{u}) ^
            max ℵ₀ #(Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u) :=
        Cardinal.sum_const' _ _
    _ ≤ (2 : Cardinal.{u}) ^
          max ℵ₀ #(Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u) := by
        refine (Cardinal.mul_le_max _ _).trans ?_
        exact max_le (max_le (mk_fgAlgCatSkeleton_le _) le_rfl) hpow

/-- **The stages of the bounded model have a uniform size bound:** the size of each is at most the
size of the affine base. -/
private theorem size_boundedModel_le (d : BoundedIndex B S hS X₀ eX x) :
    ((BigFppfOver.toScheme B S hS).obj (boundedModel B S hS hX X₀ eX x d).scheme).size ≤
      ((BigFppfOver.toScheme B S hS).obj X₀).size :=
  size_spec_presRing_le B S hS X₀ d.1.1

/-- **Every elementary étale neighborhood of `x` is refined by one in the bounded model.** -/
private theorem exists_boundedIndex_hom (E : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ d : BoundedIndex B S hS X₀ eX x,
      Nonempty (boundedModel B S hS hX X₀ eX x d ⟶ E) := by
  classical
  obtain ⟨W, j, hAff, hjOpen, w₀, hw₀⟩ :
      ∃ (W : BigFppfOver B S hS) (j : W ⟶ E.scheme),
        IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
        ∃ w₀ : (BigFppfOver.toScheme B S hS).obj W,
          (BigFppfOver.toScheme B S hS).map j w₀ = E.point := by
    set cover := ((BigFppfOver.toScheme B S hS).obj E.scheme).affineOpenCover with hcoverDef
    obtain ⟨c₀, hc₀⟩ := cover.covers E.point
    have hWcontains : B.Contains (Spec (cover.X (cover.idx E.point))) :=
      Scheme.size_lt_of_isOpenImmersion (cover.f (cover.idx E.point)) E.scheme.left.property
    let a : B.obj hWcontains ⟶ E.scheme.left :=
      B.inclusion.preimage (cover.f (cover.idx E.point))
    let W : BigFppfOver B S hS := Over.mk (a ≫ E.scheme.hom)
    let j : W ⟶ E.scheme := Over.homMk a (by rfl)
    have hja : (BigFppfOver.toScheme B S hS).map j = cover.f (cover.idx E.point) :=
      B.inclusion.map_preimage _
    refine ⟨W, j, ?_, ?_, c₀, ?_⟩
    · change IsAffine (Spec (cover.X (cover.idx E.point)))
      infer_instance
    · rw [hja]
      exact cover.map_prop (cover.idx E.point)
    · rw [hja]
      exact hc₀
  have hAffW : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hAff
  have hjOpen' : _root_.AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B S hS).map j) := hjOpen
  let g : W ⟶ X₀ := yoneda.preimage (yoneda.map j ≫ E.toSpace ≫ eX.hom)
  have hg : yoneda.map g = yoneda.map j ≫ E.toSpace ≫ eX.hom := yoneda.map_preimage _
  have hresp : MorphismProperty.RespectsIso
      ((MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso
  have hchartj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map j) :=
    (presheaf_yoneda_map_etale_iff B S hS j).2 inferInstance
  have hchartg : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map g) := by
    rw [hg, ← Category.assoc]
    exact MorphismProperty.RespectsIso.postcomp _ eX.hom _
      (E.etale_toSpace W (yoneda.map j) hchartj)
  have hgEtale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g) :=
    (presheaf_yoneda_map_etale_iff B S hS g).1 hchartg
  have hft : RingHom.FiniteType ((BigFppfOver.toScheme B S hS).map g).appTop.hom :=
    HasRingHomProperty.appTop (P := @AlgebraicGeometry.LocallyOfFiniteType) _ inferInstance
  obtain ⟨T, e, hcompat⟩ := hft.exists_smallRepr
  have hiso1 : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
    (RingEquiv.toCommRingCatIso e.symm).isIso_hom
  have hSpecMapIso : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := inferInstance
  have hSpecMapOpen : _root_.AlgebraicGeometry.IsOpenImmersion
    (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := inferInstance
  set α : Spec (presRing B S hS X₀ T) ⟶ (BigFppfOver.toScheme B S hS).obj W :=
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      ((BigFppfOver.toScheme B S hS).obj W).isoSpec.inv with hAlphaDef
  have hAlphaIso : IsIso α := by
    rw [hAlphaDef]
    infer_instance
  have hring0 : (e.symm.toRingHom).comp
      (((BigFppfOver.toScheme B S hS).map g).appTop.hom) =
      algebraMap (Γ((BigFppfOver.toScheme B S hS).obj X₀, ⊤) : Type u)
        (T.eval.obj : Type u) := by
    rw [hcompat]
    exact RingHom.ext (fun z => e.symm_apply_apply _)
  have hring : ((BigFppfOver.toScheme B S hS).map g).appTop ≫
      CommRingCat.ofHom e.symm.toRingHom = presAlgebraMap B S hS X₀ T :=
    CommRingCat.hom_ext hring0
  have hgfac : (BigFppfOver.toScheme B S hS).map g =
      ((BigFppfOver.toScheme B S hS).obj W).isoSpec.hom ≫
        Spec.map (((BigFppfOver.toScheme B S hS).map g).appTop) ≫
          ((BigFppfOver.toScheme B S hS).obj X₀).isoSpec.inv := by
    have hnat := Scheme.toSpecΓ_naturality ((BigFppfOver.toScheme B S hS).map g)
    rw [← Category.assoc]
    change (BigFppfOver.toScheme B S hS).map g =
      (((BigFppfOver.toScheme B S hS).obj W).toSpecΓ ≫
        Spec.map (((BigFppfOver.toScheme B S hS).map g).appTop)) ≫
          ((BigFppfOver.toScheme B S hS).obj X₀).isoSpec.inv
    rw [← hnat, Category.assoc]
    change (BigFppfOver.toScheme B S hS).map g =
      (BigFppfOver.toScheme B S hS).map g ≫
        (((BigFppfOver.toScheme B S hS).obj X₀).isoSpec.hom ≫
          ((BigFppfOver.toScheme B S hS).obj X₀).isoSpec.inv)
    rw [Iso.hom_inv_id, Category.comp_id]
  have hAlphaG : α ≫ (BigFppfOver.toScheme B S hS).map g = presSpecHom B S hS X₀ T := by
    have h1 : α ≫ (BigFppfOver.toScheme B S hS).map g =
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          Spec.map (((BigFppfOver.toScheme B S hS).map g).appTop) ≫
            ((BigFppfOver.toScheme B S hS).obj X₀).isoSpec.inv := by
      conv_lhs => rw [hAlphaDef, hgfac]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [h1, ← Spec.map_comp_assoc, hring]
    rfl
  let aIota : B.obj (contains_spec_presRing B S hS X₀ T) ⟶ W.left :=
    B.inclusion.preimage (X := B.obj (contains_spec_presRing B S hS X₀ T)) (Y := W.left) α
  have haIota : B.inclusion.map aIota = α := B.inclusion.map_preimage _
  have hw : (BigFppfOver.toScheme B S hS).map g ≫ X₀.hom.1 = W.hom.1 :=
    congrArg (fun k ↦ k.1) g.w
  let ι : presObj B S hS X₀ T ⟶ W :=
    Over.homMk aIota (by
      apply ObjectProperty.hom_ext
      change B.inclusion.map aIota ≫ W.hom.1 =
        B.inclusion.map (B.inclusion.preimage
          (X := B.obj (contains_spec_presRing B S hS X₀ T))
          (Y := X₀.left) (presSpecHom B S hS X₀ T)) ≫ X₀.hom.1
      rw [haIota, B.inclusion.map_preimage, ← hw, ← Category.assoc, hAlphaG])
  have hIotaMap : (BigFppfOver.toScheme B S hS).map ι = α := haIota
  have hIotaMapIso : IsIso ((BigFppfOver.toScheme B S hS).map ι) := by
    rw [hIotaMap]
    exact hAlphaIso
  have hIotaIso : IsIso ι := by
    have h₂ : IsIso (B.inclusion.map ((Over.forget (B.obj hS)).map ι)) := hIotaMapIso
    have h₃ : IsIso ((Over.forget (B.obj hS)).map ι) := isIso_of_reflects_iso _ B.inclusion
    exact isIso_of_reflects_iso _ (Over.forget (B.obj hS))
  have hIotaG : ι ≫ g = presHom B S hS X₀ T := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change B.inclusion.map aIota ≫ B.inclusion.map g.left =
      B.inclusion.map (B.inclusion.preimage
        (X := B.obj (contains_spec_presRing B S hS X₀ T))
        (Y := X₀.left) (presSpecHom B S hS X₀ T))
    rw [haIota, B.inclusion.map_preimage]
    exact hAlphaG
  have hinvapp : ∀ p : (BigFppfOver.toScheme B S hS).obj W,
      (BigFppfOver.toScheme B S hS).map ι
        ((BigFppfOver.toScheme B S hS).map (inv ι) p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id]
    simp
  let k : presObj B S hS X₀ T ⟶ E.scheme := ι ≫ j
  let pt : (presObj B S hS X₀ T).left.1 :=
    (BigFppfOver.toScheme B S hS).map (inv ι) w₀
  have hkpt : (BigFppfOver.toScheme B S hS).map k pt = E.point := by
    change (BigFppfOver.toScheme B S hS).map (ι ≫ j) pt = E.point
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    change (BigFppfOver.toScheme B S hS).map j
      ((BigFppfOver.toScheme B S hS).map ι
        ((BigFppfOver.toScheme B S hS).map (inv ι) w₀)) = E.point
    rw [hinvapp w₀]
    exact hw₀
  have hkpt' : k.left.1 pt = E.point := hkpt
  have htoSpace : presToSpace B S hS X₀ eX T = yoneda.map k ≫ E.toSpace := by
    change yoneda.map (presHom B S hS X₀ T) ≫ eX.inv = yoneda.map (ι ≫ j) ≫ E.toSpace
    rw [← hIotaG, Functor.map_comp, Functor.map_comp, hg]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hkOpen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map k) := by
    have hAlphaOpen : _root_.AlgebraicGeometry.IsOpenImmersion α := by
      rw [hAlphaDef]
      infer_instance
    have h : (BigFppfOver.toScheme B S hS).map k =
        (BigFppfOver.toScheme B S hS).map ι ≫ (BigFppfOver.toScheme B S hS).map j :=
      Functor.map_comp _ _ _
    rw [h, hIotaMap]
    exact AlgebraicGeometry.IsOpenImmersion.comp α ((BigFppfOver.toScheme B S hS).map j)
  have hrfiso : IsIso ((k.left.1).residueFieldMap pt) :=
    inferInstanceAs (IsIso (((BigFppfOver.toScheme B S hS).map k).residueFieldMap pt))
  have hetale : IsEtale B S hS (presToSpace B S hS X₀ eX T) := by
    rw [htoSpace]
    have h : yoneda.map k = yoneda.map ι ≫ yoneda.map j := Functor.map_comp _ _ _
    rw [h, Category.assoc]
    refine isEtale_comp B S hS ?_ (isEtale_comp B S hS ?_ E.etale_toSpace)
    · exact isEtale_of_presheaf_etale B S hS
        ((presheaf_yoneda_map_etale_iff B S hS ι).2 inferInstance)
    · exact isEtale_of_presheaf_etale B S hS
        ((presheaf_yoneda_map_etale_iff B S hS j).2 inferInstance)
  have hmem : pointsMap B S hS (yoneda.obj (presObj B S hS X₀ T))
      (presToSpace B S hS X₀ eX T)
      (presheafPoint B S hS (presObj B S hS X₀ T) pt
        (B.residueField_spec_contains (presObj B S hS X₀ T).left.property pt)) = x := by
    rw [htoSpace, pointsMap_comp_apply,
      pointsMap_presheafPoint B S hS (presObj B S hS X₀ T) E.scheme k pt _
        (B.residueField_spec_contains E.scheme.left.property (k.left.1 pt))]
    have hrw : ∀ q : E.scheme.left.1, q = E.point →
        ∀ hc : B.Contains (Spec (.of (E.scheme.left.1.residueField q))),
        pointsMap B S hS (yoneda.obj E.scheme) E.toSpace
          (presheafPoint B S hS E.scheme q hc) = x := by
      rintro q rfl hc
      exact E.map_point
    exact hrw _ hkpt' _
  have hmono : Mono (yoneda.map (residueFieldMap B S hS (presObj B S hS X₀ T) pt
      (B.residueField_spec_contains (presObj B S hS X₀ T).left.property pt)) ≫
      presToSpace B S hS X₀ eX T) := by
    have hmonoE : Mono (yoneda.map (residueFieldMap B S hS E.scheme (k.left.1 pt)
        (B.residueField_spec_contains E.scheme.left.property (k.left.1 pt))) ≫ E.toSpace) := by
      have hrw : ∀ q : E.scheme.left.1, q = E.point →
          ∀ hc : B.Contains (Spec (.of (E.scheme.left.1.residueField q))),
          Mono (yoneda.map (residueFieldMap B S hS E.scheme q hc) ≫ E.toSpace) := by
        rintro q rfl hc
        exact E.mono_residueField
      exact hrw _ hkpt' _
    have hisoRF : IsIso (residueFieldObjectMap B S hS (presObj B S hS X₀ T) E.scheme k pt) :=
      isIso_residueFieldObjectMap B S hS (presObj B S hS X₀ T) E.scheme k pt
    have hmonoRF : Mono (yoneda.map
        (residueFieldObjectMap B S hS (presObj B S hS X₀ T) E.scheme k pt)) := inferInstance
    rw [htoSpace, ← Category.assoc, ← Functor.map_comp,
      ← residueFieldObjectMap_comp B S hS (presObj B S hS X₀ T) E.scheme k pt,
      Functor.map_comp, Category.assoc]
    exact mono_comp _ _
  exact ⟨⟨⟨T, pt⟩, hetale, hmem, hmono⟩, ⟨⟨k, htoSpace.symm, hkpt'⟩⟩⟩

end Model

/-- The bounded model functor is initial, with bounds, affine stages and full faithfulness. -/
private theorem exists_bounded_initial_affine_model (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (X₀ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj X₀)]
    (eX : X ≅ yoneda.obj X₀) (x : points B S hS X) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (G : I ⥤ ElementaryEtaleNeighborhood B S hS X hX x),
      G.Initial ∧ #I < B.cutoff ∧
        (∃ μ : Cardinal.{u}, μ < B.cutoff ∧
          ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ) ∧
        (∀ i, IsAffine (G.obj i).scheme.left.1) ∧ G.Full ∧ G.Faithful := by
  have hne : Nonempty (ElementaryEtaleNeighborhood B S hS X hX x) :=
    ⟨(exists_affine_elementaryEtaleNeighborhood' B S hS hX hXdec x).choose⟩
  have hcof : IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX x) :=
    isCofiltered_of_nonempty B S hS X hX x hne
  have hweak : ∀ E : ElementaryEtaleNeighborhood B S hS X hX x,
      ∃ d : InducedCategory (ElementaryEtaleNeighborhood B S hS X hX x)
          (boundedModel B S hS hX X₀ eX x),
        Nonempty ((inducedFunctor (boundedModel B S hS hX X₀ eX x)).obj d ⟶ E) :=
    fun E => exists_boundedIndex_hom B S hS hX X₀ eX x E
  have hcofI : IsCofiltered (InducedCategory (ElementaryEtaleNeighborhood B S hS X hX x)
      (boundedModel B S hS hX X₀ eX x)) :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful _ hweak
  refine ⟨InducedCategory (ElementaryEtaleNeighborhood B S hS X hX x)
      (boundedModel B S hS hX X₀ eX x), inferInstance, hcofI,
    inducedFunctor (boundedModel B S hS hX X₀ eX x),
    Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ hweak, ?_,
    ⟨((BigFppfOver.toScheme B S hS).obj X₀).size, X₀.left.property, fun i => ?_⟩, fun i => ?_,
    inferInstance, inferInstance⟩
  · exact mk_boundedIndex_lt B S hS X₀ eX x
  · exact size_boundedModel_le B S hS hX X₀ eX x i
  · change IsAffine (Spec (presRing B S hS X₀ i.1.1))
    infer_instance

/-- **A cofiltered initial model with explicit cardinal bounds, over an affine base.** For a
point of a decent algebraic space presented as an affine scheme of the site, the category of
elementary étale neighborhoods admits an initial functor from a `u`-small cofiltered category
whose type of objects has cardinality below the cutoff, and all of whose stage schemes have size
at most a single cardinal below the cutoff -- namely the size of the affine base. -/
theorem exists_bounded_cofiltered_initial_model_of_iso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (X₀ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj X₀)]
    (eX : X ≅ yoneda.obj X₀) (x : points B S hS X) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (G : I ⥤ ElementaryEtaleNeighborhood B S hS X hX x),
      G.Initial ∧ #I < B.cutoff ∧
        ∃ μ : Cardinal.{u}, μ < B.cutoff ∧
          ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ := by
  obtain ⟨I, hI₁, hI₂, G, hG, hI, hμ, -⟩ :=
    exists_bounded_initial_affine_model B S hS hX hXdec X₀ eX x
  exact ⟨I, hI₁, hI₂, G, hG, hI, hμ⟩

/-- **A cofiltered initial model with explicit cardinal bounds and affine stages.** This is
`exists_bounded_cofiltered_initial_model_of_iso` together with the affineness of the schemes of the
stages, each the spectrum of a presented algebra over the ring of functions of the affine base, and
the full faithfulness of the model functor. -/
theorem exists_bounded_cofiltered_initial_affine_model_of_iso (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (X₀ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj X₀)]
    (eX : X ≅ yoneda.obj X₀) (x : points B S hS X) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (G : I ⥤ ElementaryEtaleNeighborhood B S hS X hX x),
      G.Initial ∧ #I < B.cutoff ∧
        (∃ μ : Cardinal.{u}, μ < B.cutoff ∧
          ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ) ∧
        (∀ i, IsAffine (G.obj i).scheme.left.1) ∧ G.Full ∧ G.Faithful := by
  exact exists_bounded_initial_affine_model B S hS hX hXdec X₀ eX x

/-- **A cofiltered initial model with explicit cardinal bounds, for an affine algebraic space.** -/
theorem exists_bounded_cofiltered_initial_model (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (hXaff : IsAffineSpace B S hS X) (x : points B S hS X) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (G : I ⥤ ElementaryEtaleNeighborhood B S hS X hX x),
      G.Initial ∧ #I < B.cutoff ∧
        ∃ μ : Cardinal.{u}, μ < B.cutoff ∧
          ∀ i, ((BigFppfOver.toScheme B S hS).obj (G.obj i).scheme).size ≤ μ := by
  obtain ⟨X₀, hX₀, ⟨eX⟩⟩ := hXaff
  have hX₀' : IsAffine ((BigFppfOver.toScheme B S hS).obj X₀) := hX₀
  exact exists_bounded_cofiltered_initial_model_of_iso B S hS hX hXdec X₀ eX x

end ElementaryEtaleNeighborhood

end AlgebraicGeometry.Space

end
