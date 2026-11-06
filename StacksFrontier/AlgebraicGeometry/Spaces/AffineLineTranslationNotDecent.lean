module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineTranslation.GenericPointFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.RingTheory.Jacobson.Nullstellensatz

/-!
# The affine line modulo the integers is not decent

Over a field of characteristic zero the integers act on the affine line by translation, and
the generic point of the line is the one point of the quotient at which the action is not
free: the integer translations are intertwined with the automorphisms of the field of
rational functions. The resulting algebraic space has a point with no monomorphic
field-valued representative, so it is not decent.

## Main results

* `AffineLineTranslation.not_hasMonomorphicFieldRepresentative_genericQuotientPoint` and
  `AffineLineTranslation.not_exists_mono_factorisation_genericQuotientPoint` (in the namespace
  `AlgebraicGeometry`) are the third assertion of Stacks 02Z7: the generic point of the
  quotient has no monomorphic field-valued representative, so the morphism
  `γ : Spec k(x) ⟶ 𝔸¹_k/ℤ` factors through no monomorphism from the spectrum of a field. Its
  first two assertions are in
  `StacksFrontier/AlgebraicGeometry/Spaces/AffineLineTranslation/GenericPointFibre.lean`.
* `AlgebraicGeometry.AffineLineTranslation.not_isDecentSpace_translationQuotient` is
  Stacks 03ID: the quotient of the affine line over a characteristic-zero field by integer
  translations is not a decent algebraic space. It is a corollary of the previous statement,
  decency asking for a monomorphic field-valued representative at *every* point.
* `Stacks.Groupoids.exists_lift_quotientChart`: a section of a quotient sheaf lifts to the
  chart along an arrow of the big fppf site which is locally of finite presentation and whose
  image contains a prescribed point of the base.
* `AlgebraicGeometry.exists_fieldSpec_finiteType_of_locallyOfFinitePresentation`: a scheme
  locally of finite presentation over the spectrum of a field receives a morphism from the
  spectrum of a field of finite type over it. Together with the previous result this lifts a
  field-valued section of a quotient sheaf to the chart over an algebraic extension of the
  field.
* `AlgebraicGeometry.Space.actionRelation_rel_of_smul` and
  `AlgebraicGeometry.Space.exists_smul_eq_of_actionRelation_rel`: two points of a scheme are
  related by the graph relation of a group action exactly when they differ by the action of a
  group element, the second direction for a one-point source.
* `AlgebraicGeometry.Space.eq_of_mono_fieldMorphism`: a monomorphic field-valued
  representative separates the morphisms into the object of the site it is defined on.
* `Polynomial.Monic.aeval_add_one_ne_zero_of_irreducible`: a monic irreducible polynomial over
  a field of characteristic zero has no two roots differing by one.

## Implementation notes

The proof does not use that the quotient is an algebraic space, so it does not rest on the
effective fppf descent which the quotient machinery of
`StacksFrontier/AlgebraicGeometry/Spaces/QuotientSheafAlgebraic.lean` leaves undischarged. Where
the source factors the generic point through the monomorphism, this argument instead uses the
common field-valued extension supplied by
`AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff`, which is already a field
spectrum, so no representability of a fibre product is needed.

## References

* [Stacks Project, Tag 02Z7](https://stacks.math.columbia.edu/tag/02Z7)
* [Stacks Project, Tag 03ID](https://stacks.math.columbia.edu/tag/03ID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

universe u v

namespace Polynomial

/-- A monic irreducible polynomial over a field of characteristic zero has no two roots
differing by one: shifting the variable by one fixes the polynomial, so all the integer
translates of a root are roots, and there are infinitely many of them. -/
theorem Monic.aeval_add_one_ne_zero_of_irreducible {L : Type u} [Field L] [CharZero L]
    {N : Type v} [Field N] [Algebra L N] {p : L[X]} (hmonic : p.Monic) (hirr : Irreducible p)
    (y : N) (h0 : aeval y p = 0) : aeval (y + 1) p ≠ 0 := by
  classical
  intro h1
  have : CharZero N := charZero_of_injective_algebraMap (algebraMap L N).injective
  have hp : p = minpoly L y := minpoly.eq_of_irreducible_of_monic hirr h0 hmonic
  set q : L[X] := p.comp (X + C 1) with hq
  have hqy : aeval y q = 0 := by
    rw [hq, aeval_comp]
    simpa using h1
  have hqmonic : q.Monic := hmonic.comp_X_add_C 1
  have hdeg : q.natDegree = p.natDegree := by simp [hq, natDegree_comp]
  have hpq : p = q :=
    Polynomial.eq_of_monic_of_associated hmonic hqmonic
      (associated_of_dvd_of_natDegree_le (by rw [hp]; exact minpoly.dvd L y hqy)
        hqmonic.ne_zero (le_of_eq hdeg))
  have hshift : ∀ w : N, aeval w p = 0 → aeval (w + 1) p = 0 := by
    intro w hw
    have h : aeval w q = 0 := hpq ▸ hw
    rw [hq, aeval_comp] at h
    simpa using h
  have key : ∀ n : ℕ, aeval (y + (n : N)) p = 0 := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ m ih =>
        have h := hshift _ ih
        rwa [show y + ((m : ℕ) : N) + 1 = y + ((m + 1 : ℕ) : N) by push_cast; ring] at h
  have hPne : p.map (algebraMap L N) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap L N).injective).mpr hmonic.ne_zero
  have hsub : Set.range (fun n : ℕ ↦ y + (n : N)) ⊆
      ((p.map (algebraMap L N)).roots.toFinset : Set N) := by
    rintro w ⟨n, rfl⟩
    refine Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hPne, ?_⟩)
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact key n
  exact Set.infinite_range_of_injective (fun c d hcd ↦ by simpa using hcd)
    (Set.Finite.subset (Finset.finite_toSet _) hsub)

end Polynomial

/-- Over a field of characteristic zero, two algebra maps out of an algebraic extension never
differ by one at an element. -/
theorem AlgHom.add_one_ne_of_isAlgebraic {L M P : Type*} [Field L] [CharZero L] [Field M]
    [Field P] [Algebra L M] [Algebra L P] [Algebra.IsAlgebraic L M] (ξa ξb : M →ₐ[L] P)
    (z : M) : ξb z + 1 ≠ ξa z := by
  have hz : IsIntegral L z := (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  intro h
  refine (minpoly.monic hz).aeval_add_one_ne_zero_of_irreducible (minpoly.irreducible hz)
    (ξb z) ?_ ?_
  · rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  · rw [h, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

/-- Over a field of characteristic zero, two ring maps out of a field extension of finite type
which agree on the base field never differ by one at an element. -/
theorem RingHom.FiniteType.add_one_ne {L M P : Type*} [Field L] [CharZero L] [Field M]
    [Field P] {φ : L →+* M} (hφ : φ.FiniteType) (ξa ξb : M →+* P)
    (h : ∀ x, ξa (φ x) = ξb (φ x)) (z : M) : ξb z + 1 ≠ ξa z := by
  let := φ.toAlgebra
  let := (ξb.comp φ).toAlgebra
  have : Algebra.FiniteType L M := hφ
  have : Algebra.IsAlgebraic L M := .of_finiteType
  exact AlgHom.add_one_ne_of_isAlgebraic ⟨ξa, h⟩ ⟨ξb, fun _ ↦ rfl⟩ z

namespace AlgebraicGeometry

/-- A morphism from a one-point scheme into a disjoint union of schemes factors through one
of the summands. -/
theorem Scheme.exists_sigmaι_factor {A : Scheme.{u}} [Unique A] {ι : Type u}
    (Y : ι → Scheme.{u}) (f : A ⟶ ∐ Y) :
    ∃ (i : ι) (g : A ⟶ Y i), g ≫ Sigma.ι Y i = f := by
  set w := (AlgebraicGeometry.sigmaMk Y).symm (f.base default) with hw
  have hpoint : f.base default = (Sigma.ι Y w.1).base w.2 := by
    rw [← AlgebraicGeometry.sigmaMk_mk Y w.1 w.2]
    exact ((AlgebraicGeometry.sigmaMk Y).apply_symm_apply (f.base default)).symm
  refine ⟨w.1, IsOpenImmersion.lift (Sigma.ι Y w.1) f ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro v ⟨z, rfl⟩
  exact ⟨w.2, by rw [show z = default from Subsingleton.elim _ _]; exact hpoint.symm⟩

/-- The ring map underlying `Spec` of a ring map computes the pullback of global sections,
read through the canonical isomorphisms with the rings. -/
theorem Scheme.ΓSpecIso_hom_specMap_appTop_apply {A C : CommRingCat.{u}} (g : A ⟶ C) (x : A) :
    (Scheme.ΓSpecIso C).hom ((Spec.map g).appTop ((Scheme.ΓSpecIso A).inv x)) = g.hom x := by
  rw [Scheme.specMap_appTop_ΓSpecIso_inv]
  simp

/-- A scheme locally of finite presentation over the spectrum of a field, with a point,
receives a morphism from the spectrum of a field of finite type over the base field: the
residue field of a maximal ideal of an affine open neighbourhood of the point. -/
theorem exists_fieldSpec_finiteType_of_locallyOfFinitePresentation {L : Type u} [Field L]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of L)) [LocallyOfFinitePresentation g] (y : Y) :
    ∃ (M : Type u) (_ : Field M) (φ : L →+* M) (w : Spec (.of M) ⟶ Y),
      φ.FiniteType ∧ w ≫ g = Spec.map (CommRingCat.ofHom φ) := by
  classical
  have := Y.affineOpenCover.map_prop (Y.affineOpenCover.idx y)
  obtain ⟨x₀, -⟩ := Y.affineOpenCover.covers y
  have : Nontrivial (Y.affineOpenCover.X (Y.affineOpenCover.idx y)) :=
    PrimeSpectrum.nontrivial x₀
  set ι : Spec (Y.affineOpenCover.X (Y.affineOpenCover.idx y)) ⟶ Y :=
    Y.affineOpenCover.f (Y.affineOpenCover.idx y) with hι
  set ψ : CommRingCat.of L ⟶ Y.affineOpenCover.X (Y.affineOpenCover.idx y) :=
    Spec.homEquiv (ι ≫ g) with hψ
  have hspec : Spec.map ψ = ι ≫ g := Spec.homEquiv.symm_apply_apply _
  have hft : ψ.hom.FiniteType := by
    have hlft : LocallyOfFiniteType (Spec.map ψ) := by rw [hspec]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hlft
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Y.affineOpenCover.X (Y.affineOpenCover.idx y))
  have := hm
  refine ⟨_, Ideal.Quotient.field m, (Ideal.Quotient.mk m).comp ψ.hom,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ ι,
    (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hft, ?_⟩
  rw [Category.assoc, ← hspec, ← Spec.map_comp]
  rfl

/-- Morphisms of the big fppf site over `S` are determined by the morphisms of schemes
underlying them. -/
theorem BigFppfOver.hom_ext {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {T T' : BigFppfOver B S hS} {f g : T ⟶ T'}
    (h : (BigFppfOver.toScheme B S hS).map f = (BigFppfOver.toScheme B S hS).map g) : f = g :=
  Over.OverMorphism.ext (B.inclusion.map_injective h)

namespace Space

variable {S : Scheme.{u}}

/-- Two points of a scheme over `S` differing by the action of a group element are related by
the graph relation of the action. -/
theorem actionRelation_rel_of_smul (U : Over S) (G : Type) [Group G] (a : G →* Aut U)
    {T : Over S} (y : T ⟶ U) (g : G) :
    (actionRelation U G a).Rel (y ≫ (a g).asIso.hom) y := by
  refine ⟨y ≫ Sigma.ι (fun _ : G ↦ U) g, ?_, ?_⟩
  · rw [Category.assoc, show (actionRelation U G a).target = actionRelationTarget U G a from
      prod.lift_fst _ _]
    show y ≫ Sigma.ι (fun _ : G ↦ U) g ≫ Sigma.desc (fun h : G ↦ (a h).asIso.hom) = _
    rw [Sigma.ι_desc]
  · rw [Category.assoc, show (actionRelation U G a).source = actionRelationSource U G from
      prod.lift_snd _ _]
    show y ≫ Sigma.ι (fun _ : G ↦ U) g ≫ Sigma.desc (fun _ : G ↦ 𝟙 U) = _
    rw [Sigma.ι_desc, Category.comp_id]

/-- Two points of a scheme over `S` with a one-point source which are related by the graph
relation of a group action differ by the action of a group element: the morphism into the
relation scheme witnessing the relation factors through one of its summands. -/
theorem exists_smul_eq_of_actionRelation_rel (U : Over S) (G : Type) [Group G]
    (a : G →* Aut U) {T : Over S} [Unique T.left] {x y : T ⟶ U}
    (h : (actionRelation U G a).Rel x y) :
    ∃ g : G, x = y ≫ (a g).asIso.hom := by
  obtain ⟨r, hrt, hrs⟩ := h
  have htgt : (actionRelation U G a).target = actionRelationTarget U G a := prod.lift_fst _ _
  have hsrc : (actionRelation U G a).source = actionRelationSource U G := prod.lift_snd _ _
  rw [htgt] at hrt
  rw [hsrc] at hrs
  -- Factor the underlying morphism of schemes through a summand.
  let e : Shrink.{u} G ≃ G := (equivShrink.{u} G).symm
  let eSigma : (∐ fun i : Shrink.{u} G ↦ U.left) ≅ ∐ fun _ : G ↦ U.left :=
    Sigma.reindex e fun _ : G ↦ U.left
  obtain ⟨i, c₀, hc₀⟩ := Scheme.exists_sigmaι_factor (fun _ : Shrink.{u} G ↦ U.left)
    (r.left ≫ (actionRelationUnderlyingIso U G).hom ≫ eSigma.inv)
  set g : G := e i with hg
  have hι : Sigma.ι (fun _ : Shrink.{u} G ↦ U.left) i ≫ eSigma.hom =
      Sigma.ι (fun _ : G ↦ U.left) g :=
    Sigma.ι_reindex_hom e (fun _ : G ↦ U.left) i
  have hc : c₀ ≫ (Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g) = r.left := by
    have h1 : c₀ ≫ (Sigma.ι (fun _ : Shrink.{u} G ↦ U.left) i ≫ eSigma.hom) ≫
        (actionRelationUnderlyingIso U G).inv = r.left := by
      rw [← Category.assoc, ← Category.assoc, hc₀]
      simp
    rw [hι, actionRelationUnderlyingIso_inv_ι] at h1
    exact h1
  -- Lift the factorisation back to the category over `S`.
  have hw : c₀ ≫ U.hom = T.hom := by
    have hιw : (Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g) ≫
        (actionRelationScheme U G).hom = U.hom := Over.w (Sigma.ι (fun _ : G ↦ U) g)
    calc c₀ ≫ U.hom = (c₀ ≫ (Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g)) ≫
          (actionRelationScheme U G).hom := by rw [Category.assoc, hιw]
      _ = T.hom := by rw [hc]; exact Over.w r
  let c : T ⟶ U := Over.homMk c₀ hw
  have hcr : c ≫ Sigma.ι (fun _ : G ↦ U) g = r := Over.OverMorphism.ext hc
  refine ⟨g, ?_⟩
  have hy : y = c := by
    rw [← hrs, ← hcr, Category.assoc]
    show c ≫ Sigma.ι (fun _ : G ↦ U) g ≫ Sigma.desc (fun _ : G ↦ 𝟙 U) = c
    rw [Sigma.ι_desc, Category.comp_id]
  rw [← hrt, ← hcr, Category.assoc, hy]
  show c ≫ Sigma.ι (fun _ : G ↦ U) g ≫ Sigma.desc (fun h : G ↦ (a h).asIso.hom) = _
  rw [Sigma.ι_desc]

/-- A monomorphic field-valued representative separates the morphisms into the object of the
site it is defined on: two of them restricting its section to the same section agree. -/
theorem eq_of_mono_fieldMorphism {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS F)
    [Mono (fieldMorphism B S hS F p)] {T : BigFppfOver B S hS}
    {f g : T ⟶ p.siteObject B S hS F}
    (h : F.map f.op p.value = F.map g.op p.value) : f = g := by
  have key : ∀ u : T ⟶ p.siteObject B S hS F,
      yoneda.map u ≫ fieldMorphism B S hS F p = yonedaEquiv.symm (F.map u.op p.value) :=
    fun u ↦ by simpa using yonedaEquiv_symm_naturality_left u F p.value
  refine yoneda.map_injective ((cancel_mono (fieldMorphism B S hS F p)).mp ?_)
  rw [key f, key g, h]

end Space

end AlgebraicGeometry

namespace Stacks.Groupoids

open AlgebraicGeometry

/-- A morphism out of a represented presheaf commutes with restriction along morphisms. -/
private theorem app_comp_eq_map_app {C : Type*} [Category.{v} C] {V : C}
    {X : Cᵒᵖ ⥤ Type v} (chart : yoneda.obj V ⟶ X) {T T' : C} (f : T' ⟶ T) (x : T ⟶ V) :
    chart.app (op T') (f ≫ x) = X.map f.op (chart.app (op T) x) := by
  simpa using congrArg (fun g ↦ g x) (chart.naturality f.op)

/-- A morphism of the big fppf site, seen as a morphism of schemes, lies over the structure
morphisms of its source and target. -/
private theorem toScheme_map_comp_hom {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c T : BigFppfOver B S hS} (q : c ⟶ T) :
    (BigFppfOver.toScheme B S hS).map q ≫ B.inclusion.map T.hom = B.inclusion.map c.hom := by
  have h := congrArg B.inclusion.map (Over.w q)
  rwa [Functor.map_comp] at h

/-- **A section of a quotient sheaf lifts to the chart locally for the fppf topology.** The
arrow along which it lifts can be taken locally of finite presentation and with a prescribed
point of the base in its image: the chart is locally surjective, and through every point of
the base of a covering sieve of the big fppf site there passes a flat arrow of the sieve
locally of finite presentation. -/
theorem exists_lift_quotientChart (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (V : BigFppfOver B S hS) {R : Over S} (j : PreRelation R ((Over.post B.inclusion).obj V))
    (T : BigFppfOver B S hS)
    (s : ToType ((quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) j).obj.obj (op T)))
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (c : BigFppfOver B S hS) (q : c ⟶ T) (ℓ : c ⟶ V),
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map q).base ∧
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) V j).app (op c) ℓ =
        (quotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).obj.map q.op s := by
  have := isLocallySurjective_quotientChart (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) V j
  obtain ⟨c, q, ⟨ℓ, hℓ⟩, -, hlfp, hrange⟩ := BigFppfOver.exists_mem_of_mem_topology B S hS
    (Presheaf.IsLocallySurjective.imageSieve_mem (J := BigFppfOver.topology B S hS)
      (f := quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) V j) s) x
  exact ⟨c, q, ℓ, hlfp, hrange, hℓ⟩

/-- A field-valued point of a quotient sheaf lifts to the chart over the spectrum of a field
extension of finite type of its field. -/
theorem exists_finiteType_lift_quotientChart (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (V : BigFppfOver B S hS) {R : Over S} (j : PreRelation R ((Over.post B.inclusion).obj V))
    (p : Space.FieldValuedPoint B S hS
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj) :
    ∃ (M : Type u) (_ : Field M) (φ : p.carrier →+* M) (hM : B.Contains (Spec (.of M)))
      (s : (Over.mk (⟨Spec.map (CommRingCat.ofHom φ) ≫ p.toBase⟩ : B.obj hM ⟶ B.obj hS) :
        BigFppfOver B S hS) ⟶ p.siteObject B S hS _)
      (ℓ : (Over.mk (⟨Spec.map (CommRingCat.ofHom φ) ≫ p.toBase⟩ : B.obj hM ⟶ B.obj hS) :
        BigFppfOver B S hS) ⟶ V),
      φ.FiniteType ∧ (BigFppfOver.toScheme B S hS).map s = Spec.map (CommRingCat.ofHom φ) ∧
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) V j).app _ ℓ =
        (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj.map s.op
          p.value := by
  have : Unique ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS _)) := by
    show Unique (Spec (.of p.carrier))
    infer_instance
  obtain ⟨c, q, ℓ, hlfp, ⟨y₀, -⟩, hℓ⟩ :=
    exists_lift_quotientChart B S hS V j (p.siteObject B S hS _) p.value default
  have := hlfp
  obtain ⟨M, hMf, φ, w, hφft, hwcomm⟩ :=
    exists_fieldSpec_finiteType_of_locallyOfFinitePresentation (L := p.carrier)
      ((BigFppfOver.toScheme B S hS).map q) y₀
  let : Algebra p.carrier M := φ.toAlgebra
  have : Algebra.FiniteType p.carrier M := hφft
  have hM : B.Contains (Spec (.of M)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      p.carrier M p.contained
  have hqw : (BigFppfOver.toScheme B S hS).map q ≫ p.toBase = B.inclusion.map c.hom :=
    toScheme_map_comp_hom q
  let wM : (Over.mk (⟨Spec.map (CommRingCat.ofHom φ) ≫ p.toBase⟩ : B.obj hM ⟶ B.obj hS) :
      BigFppfOver B S hS) ⟶ c := Over.homMk (⟨w⟩ : B.obj hM ⟶ c.left) (by
    apply ObjectProperty.hom_ext
    show w ≫ B.inclusion.map c.hom = Spec.map (CommRingCat.ofHom φ) ≫ p.toBase
    rw [← hqw, ← Category.assoc, hwcomm])
  refine ⟨M, hMf, φ, hM, wM ≫ q, wM ≫ ℓ, hφft, hwcomm, ?_⟩
  let X := (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj
  show (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) V j).app _
    (wM ≫ ℓ) = X.map (wM ≫ q).op p.value
  rw [app_comp_eq_map_app, hℓ, op_comp, Functor.map_comp_apply]

end Stacks.Groupoids

namespace AlgebraicGeometry.AffineLineTranslation

open AffineLineInvolution Stacks.Groupoids

section Coordinates

variable (k : Type u) [Field k]

/-- The standard coordinate of a point of the affine line over `k`. -/
def lineCoord {T : Over (Spec (.of k))} (x : T ⟶ affineLine k) : Γ(T.left, ⊤) :=
  x.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)

/-- The coordinate of a point of the affine line restricted along a morphism is the
restriction of its coordinate. -/
theorem lineCoord_comp {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (x : T ⟶ affineLine k) :
    lineCoord k (f ≫ x) = f.left.appTop (lineCoord k x) := by
  rw [lineCoord, lineCoord, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The coordinate of the generic point of the affine line over `k` is the indeterminate. -/
theorem lineCoord_genericPointMap :
    lineCoord k (genericPointMap k) = (Scheme.ΓSpecIso (.of (RatFunc k))).inv RatFunc.X := by
  rw [lineCoord, genericPointMap]
  exact AffineSpace.homOfVector_appTop_coord _ _ _

end Coordinates

/-- **Stacks 02Z7.** The generic point of the affine line over `k`, as a field-valued point of
the quotient `X = 𝔸¹_k/ℤ` with values in the field `k(x)` of rational functions. This is the
morphism `γ` of the example, presented by a section of the quotient sheaf. -/
def genericQuotientPoint (k : Type u) [Field k] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k))) (hG : B.Contains (Spec (.of (RatFunc k))))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    Space.FieldValuedPoint B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS)) :=
  let F : BigFppfOver B (Spec (.of k)) hS ⥤ Over (Spec (.of k)) := Over.post B.inclusion
  haveI : F.Full := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Full
  let V : BigFppfOver B (Spec (.of k)) hS :=
    siteAffineLine k B hS (contains_affineLine k B hS)
  let jr : PreRelation (Space.actionRelationScheme (affineLine k) (Multiplicative ℤ))
      (F.obj V) := Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k)
  let GP : BigFppfOver B (Spec (.of k)) hS :=
    Over.mk (⟨(genericPointOver k).hom⟩ : B.obj hG ⟶ B.obj hS)
  { carrier := RatFunc k
    contained := hG
    toBase := (genericPointOver k).hom
    value := (quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) F V jr).app (op GP)
      (F.preimage (genericPointMap k)) }

/-- Two arrows into the source of a lift to the line of a monomorphic field-valued point of
`𝔸¹_k/ℤ`, along which the lift differs by an integer translation, restrict the point in the
same way. -/
theorem comp_eq_comp_of_translationAction (k : Type u) [Field k] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k))) (hU : B.Contains (affineLine k).left)
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (p : Space.FieldValuedPoint B (Spec (.of k)) hS (translationQuotient k B hS hU))
    [Mono (Space.fieldMorphism B (Spec (.of k)) hS _ p)]
    {T T' : BigFppfOver B (Spec (.of k)) hS}
    (s : T ⟶ p.siteObject B (Spec (.of k)) hS _) (ℓ : T ⟶ siteAffineLine k B hS hU)
    (hℓ : (quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
      (siteAffineLine k B hS hU)
      (Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k))).app
        (op T) ℓ = (translationQuotient k B hS hU).map s.op p.value)
    (e e' : T' ⟶ T) (g : Multiplicative ℤ)
    (h : (Over.post B.inclusion).map (e ≫ ℓ) =
      (Over.post B.inclusion).map (e' ≫ ℓ) ≫ (translationAction k g).asIso.hom) :
    e ≫ s = e' ≫ s := by
  refine Space.eq_of_mono_fieldMorphism p ?_
  have key : ∀ f : T' ⟶ T, (translationQuotient k B hS hU).map (f ≫ s).op p.value =
      (quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
        (siteAffineLine k B hS hU)
        (Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k))).app
          (op T') (f ≫ ℓ) := fun f ↦ by
    rw [op_comp, Functor.map_comp_apply, ← hℓ]
    exact (app_comp_eq_map_app _ f ℓ).symm
  rw [key e, key e']
  refine quotientChart_app_eq_of_rel (BigFppfOver.topology B (Spec (.of k)) hS) _ _ _ ?_
  rw [h]
  exact Space.actionRelation_rel_of_smul (affineLine k) (Multiplicative ℤ) (translationAction k)
    _ g

/-- A lift to the line of a section of `𝔸¹_k/ℤ` over a one-point scheme, presenting the same
section as a lift through the generic point, itself factors through the generic point. -/
theorem exists_comp_genericPointMap_of_quotientChart_eq (k : Type u) [Field k] [CharZero k]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k))) (hU : B.Contains (affineLine k).left)
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    {T : BigFppfOver B (Spec (.of k)) hS} [Unique ((Over.post B.inclusion).obj T).left]
    (ℓ ℓ' : T ⟶ siteAffineLine k B hS hU)
    (μ : (Over.post B.inclusion).obj T ⟶ genericPointOver k)
    (hℓ' : (Over.post B.inclusion).map ℓ' = μ ≫ genericPointMap k)
    (h : (quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
      (siteAffineLine k B hS hU)
      (Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k))).app
        (op T) ℓ =
      (quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
        (siteAffineLine k B hS hU)
        (Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k))).app
          (op T) ℓ') :
    ∃ ν : (Over.post B.inclusion).obj T ⟶ genericPointOver k,
      (Over.post B.inclusion).map ℓ = ν ≫ genericPointMap k := by
  let F : BigFppfOver B (Spec (.of k)) hS ⥤ Over (Spec (.of k)) := Over.post B.inclusion
  let jr : PreRelation (Space.actionRelationScheme (affineLine k) (Multiplicative ℤ))
      (F.obj (siteAffineLine k B hS hU)) :=
    Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k)
  have hjEER : Stacks.Groupoids.IsEtaleEquivalenceRelation jr :=
    isEtaleEquivalenceRelation_translationActionRelation k
  have : Mono jr := @mono_of_isEtaleEquivalenceRelation _ _ _ jr hjEER
  have hrel : jr.Rel (F.map ℓ) (F.map ℓ') :=
    (quotientChart_app_eq_iff_rel (BigFppfOver.topology B (Spec (.of k)) hS) F
      (siteAffineLine k B hS hU) jr (isPreEquivalenceRelation_of_isEtaleEquivalenceRelation jr)
      (isSheaf_points B (Spec (.of k)) hS _) (isSheaf_points B (Spec (.of k)) hS _) ℓ ℓ').1 h
  obtain ⟨g, hg⟩ := Space.exists_smul_eq_of_actionRelation_rel (affineLine k)
    (Multiplicative ℤ) (translationAction k) hrel
  have hg' : (F.map ℓ : F.obj T ⟶ affineLine k) =
      F.map ℓ' ≫ (translationAction k (Multiplicative.ofAdd g.toAdd)).asIso.hom := hg
  have hℓ'' : (F.map ℓ' : F.obj T ⟶ affineLine k) = μ ≫ genericPointMap k := hℓ'
  refine ⟨μ ≫ (genericPointTranslationIso k g.toAdd).hom, hg'.trans ?_⟩
  rw [hℓ'']
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun f ↦ μ ≫ f) (genericPointMap_translation k g.toAdd).symm).trans ?_
  exact (Category.assoc _ _ _).symm

/-- Two arrows into the source of a lift through the generic point of a monomorphic
field-valued point of `𝔸¹_k/ℤ`, along which the generic point differs by the unit
translation, restrict the point in the same way. -/
theorem comp_toScheme_map_eq_of_genericPointTranslation (k : Type u) [Field k]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k))) (hU : B.Contains (affineLine k).left)
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (p : Space.FieldValuedPoint B (Spec (.of k)) hS (translationQuotient k B hS hU))
    [Mono (Space.fieldMorphism B (Spec (.of k)) hS _ p)]
    {T : BigFppfOver B (Spec (.of k)) hS}
    (s : T ⟶ p.siteObject B (Spec (.of k)) hS _) (ℓ : T ⟶ siteAffineLine k B hS hU)
    (hℓ : (quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
      (siteAffineLine k B hS hU)
      (Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k))).app
        (op T) ℓ = (translationQuotient k B hS hU).map s.op p.value)
    (ν : (Over.post B.inclusion).obj T ⟶ genericPointOver k)
    (hν : (Over.post B.inclusion).map ℓ = ν ≫ genericPointMap k)
    {P : Scheme.{u}} (hP : B.Contains P) (ea eb : P ⟶ ((Over.post B.inclusion).obj T).left)
    (h : ea ≫ ν.left = eb ≫ ν.left ≫ (genericPointTranslationIso k (1 : ℤ)).hom.left) :
    ea ≫ (BigFppfOver.toScheme B (Spec (.of k)) hS).map s =
      eb ≫ (BigFppfOver.toScheme B (Spec (.of k)) hS).map s := by
  let F : BigFppfOver B (Spec (.of k)) hS ⥤ Over (Spec (.of k)) := Over.post B.inclusion
  have hν1 : ν.left ≫ (genericPointOver k).hom = (F.obj T).hom := Over.w ν
  have hlt : (genericPointTranslationIso k (1 : ℤ)).hom.left ≫ (genericPointOver k).hom =
      (genericPointOver k).hom := Over.w (genericPointTranslationIso k (1 : ℤ)).hom
  have hbase : ea ≫ (F.obj T).hom = eb ≫ (F.obj T).hom := by
    rw [← hν1, ← Category.assoc, h, Category.assoc, Category.assoc, hlt]
  let Pobj : BigFppfOver B (Spec (.of k)) hS :=
    Over.mk (⟨ea ≫ (F.obj T).hom⟩ : B.obj hP ⟶ B.obj hS)
  let eaP : Pobj ⟶ T := Over.homMk (⟨ea⟩ : B.obj hP ⟶ T.left)
    (by apply ObjectProperty.hom_ext; rfl)
  let ebP : Pobj ⟶ T := Over.homMk (⟨eb⟩ : B.obj hP ⟶ T.left)
    (by apply ObjectProperty.hom_ext; exact hbase.symm)
  have hea_eb : F.map eaP ≫ ν = F.map ebP ≫ ν ≫ (genericPointTranslationIso k (1 : ℤ)).hom :=
    Over.OverMorphism.ext h
  have hν' : (F.map ℓ : F.obj T ⟶ affineLine k) = ν ≫ genericPointMap k := hν
  have hA : ∀ e : Pobj ⟶ T,
      (F.map (e ≫ ℓ) : F.obj Pobj ⟶ affineLine k) = (F.map e ≫ ν) ≫ genericPointMap k := by
    intro e
    rw [Functor.map_comp, hν']
    exact (Category.assoc _ _ _).symm
  have hshift : (F.map (eaP ≫ ℓ) : F.obj Pobj ⟶ affineLine k) =
      F.map (ebP ≫ ℓ) ≫ (translationAction k (Multiplicative.ofAdd (1 : ℤ))).asIso.hom := by
    rw [hA eaP, hA ebP, hea_eb]
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun f ↦ F.map ebP ≫ f) ((Category.assoc _ _ _).trans
      (congrArg (fun g ↦ ν ≫ g) (genericPointMap_translation k (1 : ℤ))))).trans ?_
    exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm
  have := congrArg (BigFppfOver.toScheme B (Spec (.of k)) hS).map
    (comp_eq_comp_of_translationAction k B hS hU p s ℓ hℓ eaP ebP
      (Multiplicative.ofAdd (1 : ℤ)) hshift)
  rwa [Functor.map_comp, Functor.map_comp] at this

/-- A lift to the line of a monomorphic field-valued point of `𝔸¹_k/ℤ`, over a field receiving
an extension of finite type of the field of the point, never factors through the generic point
with its coordinate coming from that extension. -/
theorem false_of_lift_eq_comp_genericPointMap (k : Type u) [Field k] [CharZero k]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k))) (hU : B.Contains (affineLine k).left)
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]
    (p : Space.FieldValuedPoint B (Spec (.of k)) hS (translationQuotient k B hS hU))
    [Mono (Space.fieldMorphism B (Spec (.of k)) hS _ p)]
    {M N : Type u} [Field M] [Field N] {φ : p.carrier →+* M} (hφ : φ.FiniteType)
    (ι : CommRingCat.of M ⟶ CommRingCat.of N) (hN : B.Contains (Spec (.of N)))
    {f : Spec (.of N) ⟶ Spec (.of k)}
    (s : (Over.mk (⟨f⟩ : B.obj hN ⟶ B.obj hS) : BigFppfOver B (Spec (.of k)) hS) ⟶
      p.siteObject B (Spec (.of k)) hS _)
    (ℓ : (Over.mk (⟨f⟩ : B.obj hN ⟶ B.obj hS) : BigFppfOver B (Spec (.of k)) hS) ⟶
      siteAffineLine k B hS hU)
    (hs : (BigFppfOver.toScheme B (Spec (.of k)) hS).map s =
      Spec.map ι ≫ Spec.map (CommRingCat.ofHom φ))
    (hℓ : (quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
      (siteAffineLine k B hS hU)
      (Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k))).app
        (op _) ℓ = (translationQuotient k B hS hU).map s.op p.value)
    (ν : (Over.post B.inclusion).obj
      (Over.mk (⟨f⟩ : B.obj hN ⟶ B.obj hS) : BigFppfOver B (Spec (.of k)) hS) ⟶
        genericPointOver k)
    (hν : (Over.post B.inclusion).map ℓ = ν ≫ genericPointMap k) (z : M)
    (hz : lineCoord k ((Over.post B.inclusion).map ℓ) =
      (Spec.map ι).appTop ((Scheme.ΓSpecIso (.of M)).inv z)) : False := by
  let ρc : CommRingCat.of (RatFunc k) ⟶ CommRingCat.of N := Spec.preimage ν.left
  have hρ : Spec.map ρc = ν.left := Spec.homEquiv.symm_apply_apply _
  have hcoord : ι.hom z = ρc.hom RatFunc.X := by
    have e2 : lineCoord k ((Over.post B.inclusion).map ℓ) =
        (Spec.map ρc).appTop ((Scheme.ΓSpecIso (.of (RatFunc k))).inv RatFunc.X) := by
      rw [hν, hρ, ← lineCoord_genericPointMap k]
      exact lineCoord_comp k ν (genericPointMap k)
    have e := congrArg (fun t ↦ (Scheme.ΓSpecIso (.of N)).hom t) (hz.symm.trans e2)
    rwa [Scheme.ΓSpecIso_hom_specMap_appTop_apply,
      Scheme.ΓSpecIso_hom_specMap_appTop_apply] at e
  -- Two embeddings of `N` differing by one on the generic coordinate.
  obtain ⟨P, hPf, hP, ea, eb, heab⟩ := Space.exists_fieldSpec_common B hN hN
    ν.left (ν.left ≫ (genericPointTranslationIso k (1 : ℤ)).hom.left)
  let := hPf
  have hsch := comp_toScheme_map_eq_of_genericPointTranslation k B hS hU p s ℓ hℓ ν hν hP
    ea eb heab
  rw [hs] at hsch
  let eaC : CommRingCat.of N ⟶ CommRingCat.of P := Spec.preimage ea
  let ebC : CommRingCat.of N ⟶ CommRingCat.of P := Spec.preimage eb
  have hea : Spec.map eaC = ea := Spec.homEquiv.symm_apply_apply _
  have heb : Spec.map ebC = eb := Spec.homEquiv.symm_apply_apply _
  have hcommutes : ∀ x : p.carrier, (ι ≫ eaC).hom (φ x) = (ι ≫ ebC).hom (φ x) := by
    have h : Spec.map (CommRingCat.ofHom φ ≫ ι ≫ eaC) =
        Spec.map (CommRingCat.ofHom φ ≫ ι ≫ ebC) := by
      rw [Spec.map_comp, Spec.map_comp, Spec.map_comp, Spec.map_comp, hea, heb,
        Category.assoc, Category.assoc]
      exact hsch
    exact fun x ↦ congrArg
      (fun ψ : CommRingCat.of p.carrier ⟶ CommRingCat.of P ↦ ψ.hom x)
      (Spec.homEquiv.symm.injective h)
  have hlaurent : eaC.hom (ρc.hom RatFunc.X) = ebC.hom (ρc.hom RatFunc.X) + 1 := by
    have h : Spec.map (ρc ≫ eaC) = Spec.map
        ((CommRingCat.ofHom (RatFunc.laurent (((1 : ℤ) : k))).toRingHom ≫ ρc) ≫ ebC) := by
      rw [Spec.map_comp, Spec.map_comp, Spec.map_comp, hea, heb, hρ,
        ← genericPointTranslationIso_left k (1 : ℤ)]
      exact heab
    have h3 := congrArg (fun ψ : CommRingCat.of (RatFunc k) ⟶ CommRingCat.of P ↦ ψ.hom RatFunc.X)
      (Spec.homEquiv.symm.injective h)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h3
    rw [show ((RatFunc.laurent (((1 : ℤ) : k))).toRingHom RatFunc.X) = RatFunc.X + 1 by
      simp] at h3
    simpa using h3
  -- Conclude with the shifted-root obstruction.
  let : Algebra k p.carrier := (Spec.preimage p.toBase).hom.toAlgebra
  have : CharZero p.carrier :=
    charZero_of_injective_algebraMap (R := k) (A := p.carrier)
      (algebraMap k p.carrier).injective
  exact hφ.add_one_ne (ι ≫ eaC).hom (ι ≫ ebC).hom hcommutes z (by
    show ebC.hom (ι.hom z) + 1 = eaC.hom (ι.hom z)
    rw [hcoord, hlaurent])

/-- **Stacks 02Z7, part 3.** The generic point of the quotient `X = 𝔸¹_k/ℤ` has *no*
monomorphic field-valued representative: no monomorphism `Spec L ⟶ X` from the spectrum of a
field presents it.

If `p` were one, with field `L`, then `p` would lift to the line over an extension `M` of `L`
of finite type, hence algebraic, and the coordinate `z` of that lift would agree, up to an
integer translation, with the indeterminate: so `z` is transcendental over `k`, and `L(z)` has
two embeddings into a single field differing by one on `z`. Monomorphy of `p` forces those two
embeddings to agree on `L`, which makes the minimal polynomial of `z` over `L` invariant under
translating the variable by one. In characteristic zero no nonconstant polynomial is. -/
@[stacks 02Z7 "no monomorphic field-valued representative of the generic point"]
theorem not_hasMonomorphicFieldRepresentative_genericQuotientPoint (k : Type u) [Field k]
    [CharZero k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (hG : B.Contains (Spec (.of (RatFunc k))))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    ¬ Space.HasMonomorphicFieldRepresentative B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS))
      ((genericQuotientPoint k B hS hG).class B (Spec (.of k)) hS
        (translationQuotient k B hS (contains_affineLine k B hS))) := by
  classical
  intro hrep
  have hU : B.Contains (affineLine k).left := contains_affineLine k B hS
  let F : BigFppfOver B (Spec (.of k)) hS ⥤ Over (Spec (.of k)) := Over.post B.inclusion
  have : F.Full := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Full
  let V : BigFppfOver B (Spec (.of k)) hS := siteAffineLine k B hS hU
  let jr : PreRelation (Space.actionRelationScheme (affineLine k) (Multiplicative ℤ))
      (F.obj V) := Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k)
  let X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u := translationQuotient k B hS hU
  let chart : yoneda.obj V ⟶ X :=
    quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) F V jr
  -- The generic point of the line, as a field-valued point of the quotient.
  let GP : BigFppfOver B (Spec (.of k)) hS :=
    Over.mk (⟨(genericPointOver k).hom⟩ : B.obj hG ⟶ B.obj hS)
  let gpm : GP ⟶ V := F.preimage (genericPointMap k)
  have hgpm : (F.map gpm : F.obj GP ⟶ affineLine k) = genericPointMap k := F.map_preimage _
  let generic : Space.FieldValuedPoint B (Spec (.of k)) hS X :=
    { carrier := RatFunc k
      contained := hG
      toBase := (genericPointOver k).hom
      value := chart.app (op GP) gpm }
  obtain ⟨p, hpclass, hmono⟩ := hrep
  have := hmono
  -- A common field-valued extension of `p` and the generic point.
  obtain ⟨rr, ⟨σ, hσ⟩, ⟨τ, hτ⟩⟩ :=
    (Space.FieldValuedPoint.class_eq_class_iff B (Spec (.of k)) hS X p generic).1 hpclass
  -- `p` lifts to the line over an extension of its field of finite type.
  obtain ⟨M, hMf, φ, hM, sM, ℓM, hφft, hsMscheme, hliftM0⟩ :=
    exists_finiteType_lift_quotientChart B (Spec (.of k)) hS V jr p
  let := hMf
  let Mobj : BigFppfOver B (Spec (.of k)) hS :=
    Over.mk (⟨Spec.map (CommRingCat.ofHom φ) ≫ p.toBase⟩ : B.obj hM ⟶ B.obj hS)
  have hliftM : chart.app (op Mobj) ℓM = X.map sM.op p.value := hliftM0
  have hσbase : (BigFppfOver.toScheme B (Spec (.of k)) hS).map σ ≫ p.toBase = rr.toBase :=
    toScheme_map_comp_hom σ
  -- A common field-valued extension of that lift and of the common extension `rr`.
  obtain ⟨N, hNf, hN, ca, cb, hcab⟩ := Space.exists_fieldSpec_common B rr.contained hM
    ((BigFppfOver.toScheme B (Spec (.of k)) hS).map σ)
    ((BigFppfOver.toScheme B (Spec (.of k)) hS).map sM)
  let := hNf
  let Nobj : BigFppfOver B (Spec (.of k)) hS :=
    Over.mk (⟨ca ≫ rr.toBase⟩ : B.obj hN ⟶ B.obj hS)
  let caN : Nobj ⟶ rr.siteObject B (Spec (.of k)) hS X :=
    Over.homMk (⟨ca⟩ : B.obj hN ⟶ B.obj rr.contained) (by apply ObjectProperty.hom_ext; rfl)
  let cbN : Nobj ⟶ Mobj := Over.homMk (⟨cb⟩ : B.obj hN ⟶ B.obj hM) (by
    apply ObjectProperty.hom_ext
    show cb ≫ Spec.map (CommRingCat.ofHom φ) ≫ p.toBase = ca ≫ rr.toBase
    rw [← hσbase, ← hsMscheme, ← Category.assoc, ← hcab, Category.assoc])
  have hcbsM : cbN ≫ sM = caN ≫ σ := by
    refine BigFppfOver.hom_ext ?_
    rw [Functor.map_comp, Functor.map_comp]
    exact hcab.symm
  have hliftN : chart.app (op Nobj) (cbN ≫ ℓM) = X.map (cbN ≫ sM).op p.value := by
    rw [app_comp_eq_map_app chart cbN ℓM, hliftM, op_comp, Functor.map_comp_apply]
  have hNeq : chart.app (op Nobj) (cbN ≫ ℓM) = chart.app (op Nobj) ((caN ≫ τ) ≫ gpm) := by
    have h2 : chart.app (op Nobj) ((caN ≫ τ) ≫ gpm) = X.map (caN ≫ σ).op p.value := by
      rw [app_comp_eq_map_app chart (caN ≫ τ) gpm]
      show X.map (caN ≫ τ).op generic.value = _
      rw [op_comp, Functor.map_comp_apply, hτ, ← hσ, op_comp, Functor.map_comp_apply]
    rw [hliftN, h2, hcbsM]
  -- The lift factors through the generic point, up to an integer translation.
  have : Unique ((Over.post B.inclusion).obj Nobj).left := by
    show Unique (Spec (.of N))
    infer_instance
  obtain ⟨ν, hν⟩ := exists_comp_genericPointMap_of_quotientChart_eq k B hS hU (cbN ≫ ℓM)
    ((caN ≫ τ) ≫ gpm) (F.map (caN ≫ τ)) (by
      rw [← hgpm]
      exact Functor.map_comp F (caN ≫ τ) gpm) hNeq
  let ιMc : CommRingCat.of M ⟶ CommRingCat.of N := Spec.preimage (F.map cbN).left
  have hιM : Spec.map ιMc = (F.map cbN).left := Spec.homEquiv.symm_apply_apply _
  set z : M := (Scheme.ΓSpecIso (.of M)).hom (lineCoord k (F.map ℓM))
  have hzinv : lineCoord k (F.map ℓM) = (Scheme.ΓSpecIso (.of M)).inv z :=
    (congrArg (fun g ↦ g (lineCoord k (F.map ℓM))) (Scheme.ΓSpecIso (.of M)).hom_inv_id).symm
  have hz : lineCoord k (F.map (cbN ≫ ℓM)) =
      (Spec.map ιMc).appTop ((Scheme.ΓSpecIso (.of M)).inv z) := by
    rw [hιM, Functor.map_comp, ← hzinv]
    exact lineCoord_comp k (F.map cbN) (F.map ℓM)
  refine false_of_lift_eq_comp_genericPointMap k B hS hU p hφft ιMc hN (cbN ≫ sM) (cbN ≫ ℓM)
    ?_ hliftN ν hν z hz
  rw [Functor.map_comp, hsMscheme, hιM]
  rfl

/-- The generic point `γ : Spec k(x) ⟶ X = 𝔸¹_k/ℤ` factors through no monomorphism from the
spectrum of a field: there is no field-valued point `p` of `X` whose presenting morphism
`Spec L ⟶ X` is a monomorphism and through which `γ` factors. -/
@[stacks 02Z7 "gamma factors through no monomorphism from a field spectrum"]
theorem not_exists_mono_factorisation_genericQuotientPoint (k : Type u) [Field k] [CharZero k]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (hG : B.Contains (Spec (.of (RatFunc k))))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    ¬ ∃ (p : Space.FieldValuedPoint B (Spec (.of k)) hS
          (translationQuotient k B hS (contains_affineLine k B hS)))
        (f : (genericQuotientPoint k B hS hG).siteObject B (Spec (.of k)) hS
          (translationQuotient k B hS (contains_affineLine k B hS)) ⟶
            p.siteObject B (Spec (.of k)) hS
              (translationQuotient k B hS (contains_affineLine k B hS))),
        Mono (Space.fieldMorphism B (Spec (.of k)) hS
            (translationQuotient k B hS (contains_affineLine k B hS)) p) ∧
          yoneda.map f ≫ Space.fieldMorphism B (Spec (.of k)) hS
              (translationQuotient k B hS (contains_affineLine k B hS)) p =
            Space.fieldMorphism B (Spec (.of k)) hS
              (translationQuotient k B hS (contains_affineLine k B hS))
              (genericQuotientPoint k B hS hG) := by
  rintro ⟨p, f, hmono, hfac⟩
  -- The factorisation says that `γ` is the restriction of `p` along `f`.
  have hvalue : (translationQuotient k B hS (contains_affineLine k B hS)).map f.op p.value =
      (genericQuotientPoint k B hS hG).value := by
    refine yonedaEquiv.symm.injective ?_
    rw [← yonedaEquiv_symm_naturality_left]
    exact hfac
  refine not_hasMonomorphicFieldRepresentative_genericQuotientPoint k B hS hG ⟨p, ?_, hmono⟩
  exact (Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B (Spec (.of k)) hS _
    ⟨genericQuotientPoint k B hS hG,
      Space.FieldValuedPoint.dominates_refl B (Spec (.of k)) hS _ _, ⟨f, hvalue⟩⟩).symm

/-- **Stacks 03ID.** The quotient of the affine line over a field of characteristic zero by
the integer translations is not a decent algebraic space: the point of the quotient
represented by the generic point of the line has no monomorphic field-valued
representative. -/
@[stacks 03ID]
theorem not_isDecentSpace_translationQuotient (k : Type u) [Field k] [CharZero k]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (hG : B.Contains (Spec (.of (RatFunc k))))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    ¬ Space.IsDecentSpace B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS)) := fun hdec ↦
  not_hasMonomorphicFieldRepresentative_genericQuotientPoint k B hS hG
    (Space.IsDecentSpace.hasMonomorphicFieldRepresentative B (Spec (.of k)) hS _ hdec _)

end AlgebraicGeometry.AffineLineTranslation

end
