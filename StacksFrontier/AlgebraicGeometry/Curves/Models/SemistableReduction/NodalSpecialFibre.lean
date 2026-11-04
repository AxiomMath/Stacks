module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.GorensteinGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularProperModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentProperCurve
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NodeBaseChangeFibre
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFieldExtension
public import StacksFrontier.AlgebraicGeometry.FibreStalk.RationalPointClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossGorenstein
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Locality
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Geometric
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.FieldTheory.Separable.PerfectField

/-!
# A regular model with an at-worst-nodal special fibre

Let `X ⟶ Spec(R)` be a regular model of a smooth curve over the fraction field of a discrete
valuation ring. The source (Sections 0CEG and 0CEI of the Stacks project) concludes that `X` is
at-worst-nodal of relative dimension one over `R` from the fact that the special fibre `X_k` has
at-worst-nodal singularities over `k`: the generic fibre is the smooth curve, so this is the
fibrewise criterion of Tag 0C59.

The special fibre of a regular model is the pullback along `Spec(k) ⟶ Spec(R)`, while Tag 0C59
speaks about the scheme-theoretic fibre `X_s` over the residue field `κ(s)` of the closed point
`s`. The two are isomorphic over an isomorphism `Spec(k) ≅ Spec(κ(s))`, and this file transports
the nodal condition along such isomorphisms: for smooth points by base change along an
isomorphism, and for nodes by Tag 0C56 together with the transport of ordinary double points
along isomorphisms of schemes over an algebraically closed field.

## Main results

* `AlgebraicGeometry.exists_iso_fiber_pullback_of_isIso_descResidueField` — the fibre of
  `h : W ⟶ Y` at the image of a field-valued point `Spec F ⟶ Y` whose residue field map is an
  isomorphism is the pullback along that point, compatibly with the structure morphisms.
* `Stacks.Curves.isNode_of_isIso_of_comp_eq` — nodes are preserved by isomorphisms over the base
  field.
* `Stacks.Curves.hasAtWorstNodalSingularities_of_isIso` — at-worst-nodal singularities are
  preserved by isomorphisms of schemes over isomorphisms of their base fields.
* `Stacks.Curves.hasAtWorstNodalSingularities_of_smooth` — a smooth scheme over a field has
  at-worst-nodal singularities.
* `Stacks.Models.RegularProperModelSituation.isAtWorstNodalOfRelativeDimensionOne_of_specialFiber`
  — a regular proper model whose special fibre has at-worst-nodal singularities is
  at-worst-nodal of relative dimension one over `R`.

## References

* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 0C56](https://stacks.math.columbia.edu/tag/0C56)
* [Stacks Project, Section 0CEG](https://stacks.math.columbia.edu/tag/0CEG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The fibre at the image of a field-valued point.** Let `h : W ⟶ Y` be a morphism and
`f : Spec F ⟶ Y` a morphism from the spectrum of a field whose induced map of residue fields
`κ(y) ⟶ F` (at the image point `y`) is an isomorphism. Then the scheme-theoretic fibre of `h` at
`y` is the pullback of `h` along `f`, over `W` and over `Spec κ(y) ≅ Spec F`. -/
theorem exists_iso_fiber_pullback_of_isIso_descResidueField {W Y : Scheme.{u}} (h : W ⟶ Y)
    {F : Type u} [Field F] (f : Spec (.of F) ⟶ Y)
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo f))] :
    ∃ e : h.fiber (f (IsLocalRing.closedPoint F)) ≅ pullback h f,
      e.hom ≫ pullback.fst h f = h.fiberι _ ∧
        e.hom ≫ pullback.snd h f ≫ Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo f)) =
          h.fiberToSpecResidueField _ := by
  set i := Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo f))
  have hfac : i ≫ Y.fromSpecResidueField (f (IsLocalRing.closedPoint F)) = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField F Y f
  obtain ⟨e, he⟩ := exists_iso_fiber_pullback_of_fac h _ hfac
  refine ⟨e, he, ?_⟩
  rw [← cancel_mono (Y.fromSpecResidueField (f (IsLocalRing.closedPoint F))), Category.assoc,
    Category.assoc, hfac, ← pullback.condition, ← Category.assoc, he, Scheme.Hom.fiber_fac]

/-- The residue field map at the image of the point `Spec F ⟶ Spec R` induced by a ring map
`φ : R → F` is compatible with `φ`: composed with the canonical map `R → κ(y)` it is `φ`. -/
theorem descResidueField_residueFieldIso_inv_algebraMap {R F : Type u} [CommRing R] [Field F]
    (φ : R →+* F) (r : R) :
    (Spec (.of R)).descResidueField (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Spec.residueFieldIso (.of R) _).inv (algebraMap R _ r)) = φ r := by
  have hfac := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField F (Spec (.of R))
    (Spec.map (CommRingCat.ofHom φ))
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp,
    ← Spec.map_comp] at hfac
  exact congrArg (fun g => g.hom r) (Spec.map_injective hfac)

/-- **The residue field map is an isomorphism at a surjective point.** If `φ : R → F` is
surjective onto a field, the residue field of `Spec R` at the image of `Spec F` maps
isomorphically onto `F`. -/
theorem isIso_descResidueField_of_surjective {R F : Type u} [CommRing R] [Field F]
    (φ : R →+* F) (hφ : Function.Surjective φ) :
    IsIso ((Spec (.of R)).descResidueField
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ)))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨r, rfl⟩ := hφ z
  exact ⟨_, descResidueField_residueFieldIso_inv_algebraMap φ r⟩

/-- **The residue field map is an isomorphism at the generic point.** For a domain `R` with
fraction field `K`, the residue field of `Spec R` at the image of `Spec K` maps isomorphically
onto `K`. -/
theorem isIso_descResidueField_algebraMap_of_isFractionRing (R K : Type u) [CommRing R]
    [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsIso ((Spec (.of R)).descResidueField
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R K))))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  refine ⟨(Scheme.Spec.residueFieldIso (.of R) _).inv (algebraMap R _ a) /
    (Scheme.Spec.residueFieldIso (.of R) _).inv (algebraMap R _ b), ?_⟩
  rw [map_div₀, descResidueField_residueFieldIso_inv_algebraMap,
    descResidueField_residueFieldIso_inv_algebraMap]

/-- **A Gorenstein scheme locally of finite type over a field stays Gorenstein after any
extension of the field** (Tag 0C03, at every point of the base change). -/
theorem isGorenstein_pullback_specMap_algebraMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [IsGorenstein X] :
    IsGorenstein (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  refine (isGorenstein_iff _).2 ⟨LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))), fun x' => ?_⟩
  exact (isGorensteinLocalRing_stalk_iff_of_locallyOfFiniteType k K X f _ x' rfl).1
    (IsGorenstein.isGorensteinLocalRing _)

end AlgebraicGeometry

namespace Stacks.Curves

/-- **A smooth scheme over a field has at-worst-nodal singularities**: every point is a smooth
point. -/
theorem hasAtWorstNodalSingularities_of_smooth (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [Smooth (X ↘ Spec (.of k))] : HasAtWorstNodalSingularities k X :=
  fun x _ => Or.inl (InfinitesimalLifting.smoothAt_of_smooth _ x)

/-- **Nodes are preserved by isomorphisms over the base field.** If `e : Y ⟶ X` is an
isomorphism and `Y` is viewed over `k` through `e`, then a point of `Y` is a node as soon as its
image in `X` is one. -/
theorem isNode_of_isIso_of_comp_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (e : Y ⟶ X) [IsIso e] (y : Y)
    (h : letI : X.Over (Spec (.of k)) := ⟨f⟩; IsNode k X (e y)) :
    letI : Y.Over (Spec (.of k)) := ⟨e ≫ f⟩; IsNode k Y y := by
  set a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  obtain ⟨hx, xbar, hxbar, hodp⟩ : IsClosed ({e y} : Set X) ∧ ∃ xbar : (pullback f a : Scheme.{u}),
      (pullback.fst f a) xbar = e y ∧
        (let : (pullback f a).Over (Spec (.of (AlgebraicClosure k))) := ⟨pullback.snd f a⟩
         IsOrdinaryDoublePoint (AlgebraicClosure k) (pullback f a) xbar) := h
  show IsClosed ({y} : Set Y) ∧ ∃ ybar : (pullback (e ≫ f) a : Scheme.{u}),
      (pullback.fst (e ≫ f) a) ybar = y ∧
        (let : (pullback (e ≫ f) a).Over (Spec (.of (AlgebraicClosure k))) :=
          ⟨pullback.snd (e ≫ f) a⟩
         IsOrdinaryDoublePoint (AlgebraicClosure k) (pullback (e ≫ f) a) ybar)
  let E : pullback (e ≫ f) a ⟶ pullback f a :=
    pullback.map (e ≫ f) a f a e (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsIso E := by
    dsimp only [E]
    infer_instance
  have hinj : Function.Injective e.base := (Scheme.homeoOfIso (asIso e)).injective
  have hEinv : E (inv E xbar) = xbar := by
    show (inv E ≫ E) xbar = xbar
    rw [IsIso.inv_hom_id]
    rfl
  have hfst : pullback.fst (e ≫ f) a ≫ e = E ≫ pullback.fst f a := by
    simp [E]
  refine ⟨?_, inv E xbar, ?_, ?_⟩
  · have hpre : e.base ⁻¹' {e.base y} = {y} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨rfl, fun z hz => hinj hz⟩
    rw [← hpre]
    exact hx.preimage e.continuous
  · apply hinj
    show (pullback.fst (e ≫ f) a ≫ e) (inv E xbar) = e y
    rw [hfst]
    show (pullback.fst f a) (E (inv E xbar)) = e y
    rwa [hEinv]
  · let : (pullback f a).Over (Spec (.of (AlgebraicClosure k))) := ⟨pullback.snd f a⟩
    let : (pullback (e ≫ f) a).Over (Spec (.of (AlgebraicClosure k))) :=
      ⟨pullback.snd (e ≫ f) a⟩
    have : LocallyOfFiniteType ((pullback f a) ↘ Spec (.of (AlgebraicClosure k))) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd f a))
    have : LocallyOfFiniteType ((pullback (e ≫ f) a) ↘ Spec (.of (AlgebraicClosure k))) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd (e ≫ f) a))
    refine isOrdinaryDoublePoint_of_isIso (AlgebraicClosure k) (AlgebraicClosure k)
      (pullback f a) (pullback (e ≫ f) a) E (inv E xbar) ?_
    rwa [hEinv]

/-- **At-worst-nodal singularities are preserved by isomorphisms over an isomorphism of the base
fields.** Let `X₁` be one-dimensional and locally of finite type over `k₁`, let `e : X₂ ⟶ X₁` be
an isomorphism of schemes and `φ : k₂ ≅ k₁` an isomorphism of fields such that the structure
morphism of `X₂` over `k₂` is `e` followed by that of `X₁` and `Spec(φ)`. If `X₁` has
at-worst-nodal singularities over `k₁`, then `X₂` has at-worst-nodal singularities over `k₂`.

Smooth points move along the cartesian square formed by `e` and `Spec(φ)`; nodes move by Tag
0C56 for the extension `k₁ → k₂` given by `φ⁻¹`, followed by
`Stacks.Curves.isNode_of_isIso_of_comp_eq`. -/
theorem hasAtWorstNodalSingularities_of_isIso {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (.of k₁)) (f₂ : X₂ ⟶ Spec (.of k₂))
    [LocallyOfFiniteType f₁] (hdim : topologicalKrullDim X₁ = 1)
    (e : X₂ ⟶ X₁) [IsIso e] (φ : CommRingCat.of k₂ ⟶ CommRingCat.of k₁) [IsIso φ]
    (he : e ≫ f₁ ≫ Spec.map φ = f₂)
    (h : letI : X₁.Over (Spec (.of k₁)) := ⟨f₁⟩; HasAtWorstNodalSingularities k₁ X₁) :
    letI : X₂.Over (Spec (.of k₂)) := ⟨f₂⟩; HasAtWorstNodalSingularities k₂ X₂ := by
  let : X₁.Over (Spec (.of k₁)) := ⟨f₁⟩
  let : X₂.Over (Spec (.of k₂)) := ⟨f₂⟩
  intro y hy
  have hx : IsClosed ({e y} : Set X₁) := by
    rw [← (Set.image_singleton : e.base '' {y} = {e y})]
    exact (Scheme.homeoOfIso (asIso e)).isClosedMap _ hy
  let : Algebra k₁ k₂ := (inv φ).hom.toAlgebra
  have ha : Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂)) = inv (Spec.map φ) := by
    rw [← Spec.map_inv]
    rfl
  have hw : e ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂)) := by
    rw [ha, ← he]
    simp
  have hsq : IsPullback e f₂ f₁ (Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂))) := by
    rw [ha]
    exact IsPullback.of_horiz_isIso ⟨by rw [← ha, hw]⟩
  rcases h (e y) hx with hs | hn
  · left
    exact (AlgebraicGeometry.smoothAt_iff_smoothAt_of_isPullback hsq
      (Or.inr (by rw [ha]; infer_instance)) y).2 hs
  · right
    have hLfst : (pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂))))
        (hsq.isoPullback.hom y) = e y := by
      show (hsq.isoPullback.hom ≫ pullback.fst _ _) y = e y
      rw [hsq.isoPullback_hom_fst]
    have hnode := (isNode_iff_of_fieldExtension k₁ k₂ X₁ f₁ hdim (e y) _ hLfst).1 hn
    have := isNode_of_isIso_of_comp_eq
      (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂)))) hsq.isoPullback.hom
      y hnode
    rwa [hsq.isoPullback_hom_snd] at this

/-- **Nodes from the base change to an algebraic closure.** Let `X` be locally of finite type
over a field `k`, and suppose every closed point of `X_{k̄}` (for `k̄` the algebraic closure of
`k`) at which `X_{k̄}` is not smooth over `k̄` is an ordinary double point. Then `X` has
at-worst-nodal singularities over `k`: a closed point of `X` at which `X` is not smooth lies under
a closed point of `X_{k̄}` at which `X_{k̄}` is not smooth, and that point is the ordinary double
point that `Stacks.Curves.IsNode` asks for. -/
theorem hasAtWorstNodalSingularities_of_baseChange_algebraicClosure (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (h : ∀ y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) :
          Scheme.{u}), IsClosed ({y} : Set _) →
        ¬ InfinitesimalLifting.SmoothAt
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) y →
        @IsOrdinaryDoublePoint (AlgebraicClosure k) _ _
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
          ⟨pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))⟩ y) :
    letI : X.Over (Spec (.of k)) := ⟨f⟩; HasAtWorstNodalSingularities k X := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  set a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  intro x hx
  by_cases hs : InfinitesimalLifting.SmoothAt f x
  · exact Or.inl hs
  · right
    have : Surjective a := ⟨fun z => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
    obtain ⟨y, hy⟩ := (pullback.fst f a).surjective x
    have hyc : IsClosed ({y} : Set (pullback f a : Scheme.{u})) :=
      isClosed_singleton_baseChange_of_isClosed k (AlgebraicClosure k) X f y (by
        show IsClosed {(pullback.fst f a) y}
        rwa [hy])
    have hns : ¬ InfinitesimalLifting.SmoothAt (pullback.snd f a) y := by
      rwa [AlgebraicGeometry.smoothAt_iff_smoothAt_of_isPullback (IsPullback.of_hasPullback f a)
        (Or.inr (Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance))) y, hy]
    exact ⟨hx, y, hy, h y hyc hns⟩

/-- **Over an algebraically closed field, a non-smooth point of a Gorenstein scheme whose
non-regular points are multicross is an ordinary double point.** Over a perfect field
smoothness at a point is regularity of the local ring (all residue field extensions being
separable), so a non-smooth point is a non-regular point, hence a multicross singularity, hence
an ordinary double point by Tag 0CDZ. -/
theorem isOrdinaryDoublePoint_of_not_smoothAt (K : Type u) [Field K] [IsAlgClosed K]
    (Y : Scheme.{u}) [Y.Over (Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))]
    [IsGorenstein Y]
    (h : ∀ y : Y, ¬ IsRegularLocalRing (Y.presheaf.stalk y) → IsMulticrossSingularity K Y y)
    (y : Y) (hy : ¬ InfinitesimalLifting.SmoothAt (Y ↘ Spec (.of K)) y) :
    IsOrdinaryDoublePoint K Y y := by
  refine isOrdinaryDoublePoint_of_isGorenstein K Y y (h y fun hreg => hy ?_)
  let : Algebra K (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ Spec (.of K)).appTop ≫ Y.Γevaluation y).hom.toAlgebra
  exact (smoothAt_iff_isRegularLocalRing_stalk (Y ↘ Spec (.of K)) y
    (Algebra.isSeparableExtension_of_perfectField K _)).2 hreg

end Stacks.Curves

namespace Stacks.Models

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-- **The two points of `Spec(R)`.** Every point of the spectrum of the discrete valuation ring
is the image of `Spec(K)` (the generic point) or of `Spec(k)` (the closed point). -/
theorem eq_specMap_algebraMap_fraction_or_residue (t : Spec (.of S.R)) :
    t = (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) (IsLocalRing.closedPoint S.K) ∨
      t = (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) (IsLocalRing.closedPoint S.k) := by
  have hK : ((Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))
      (IsLocalRing.closedPoint S.K)).asIdeal = ⊥ := by
    show Ideal.comap (algebraMap S.R S.K) (IsLocalRing.maximalIdeal S.K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective S.R S.K)
  have hk : ((Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))
      (IsLocalRing.closedPoint S.k)).asIdeal = IsLocalRing.maximalIdeal S.R := by
    show Ideal.comap (algebraMap S.R S.k) (IsLocalRing.maximalIdeal S.k) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    have : algebraMap S.R S.k =
        S.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue S.R) := by
      ext r
      exact (S.residueEquiv.commutes r).symm
    rw [this, RingHom.ker_equiv_comp, IsLocalRing.ker_residue]
  by_cases ht : t.asIdeal = ⊥
  · left
    exact PrimeSpectrum.ext (ht.trans hK.symm)
  · right
    exact PrimeSpectrum.ext ((IsLocalRing.eq_maximalIdeal (t.isPrime.isMaximal ht)).trans hk.symm)

end RegularModelSituation

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **A regular proper model with an at-worst-nodal special fibre is at-worst-nodal of
relative dimension one.** In the situation of Tag 0C61, if the special fibre `X_k` has
at-worst-nodal singularities over `k`, then `X ⟶ Spec(R)` is at-worst-nodal of relative
dimension one.

This is the fibrewise criterion of Tag 0C59: the morphism is flat and of finite presentation,
its fibres are equidimensional of dimension one (part (1) of Tag 0C60), the fibre over the
generic point is the smooth curve `C`, and the fibre over the closed point is `X_k`, each over
the residue field of its point through an isomorphism of fields. -/
theorem isAtWorstNodalOfRelativeDimensionOne_of_specialFiber
    (h : letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
      Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber) :
    IsAtWorstNodalOfRelativeDimensionOne S.X_to_R := by
  rw [← Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff]
  have hrd := (relativeDimension_iff _ 1).1 S.relativeDimension_model
  refine ⟨inferInstance, inferInstance, fun t ht => ⟨(hrd t ht).1, (hrd t ht).2, ?_⟩⟩
  rcases S.eq_specMap_algebraMap_fraction_or_residue t with rfl | rfl
  · have := isIso_descResidueField_algebraMap_of_isFractionRing S.R S.K
    obtain ⟨E, -, hE⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField S.X_to_R
      (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))
    let : S.C.Over (Spec (.of S.K)) := ⟨S.C_to_K⟩
    have : Smooth (S.C ↘ Spec (.of S.K)) := S.smooth
    have hC := Stacks.Curves.hasAtWorstNodalSingularities_of_smooth S.K S.C
    refine Stacks.Curves.hasAtWorstNodalSingularities_of_isIso S.C_to_K _
      S.isCurve.topologicalKrullDim_eq_one (E.hom ≫ S.genericFiberIso.inv)
      ((Spec (.of S.R)).descResidueField
        (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))))) ?_ hC
    have hinv : S.genericFiberIso.inv ≫ S.C_to_K =
        pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) := by
      rw [← S.genericFiberIso_over_K, Iso.inv_hom_id_assoc]
    rwa [Category.assoc, reassoc_of% hinv]
  · have := isIso_descResidueField_of_surjective (algebraMap S.R S.k) S.surjective_algebraMap
    obtain ⟨E, -, hE⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField S.X_to_R
      (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))
    exact Stacks.Curves.hasAtWorstNodalSingularities_of_isIso S.specialFiberToSpec _
      (S.topologicalKrullDim_specialFiber S.nonempty_specialFiber) E.hom
      ((Spec (.of S.R)).descResidueField
        (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))))) hE h

/-- The special fibre of a regular model is a Gorenstein scheme (Tag 0C60): it is isomorphic
to the closed subscheme of the model it cuts out. -/
theorem isGorenstein_specialFiber : IsGorenstein S.specialFiber :=
  (isGorenstein_iff_of_iso (asIso S.specialFiberι.toImage)).2 S.isGorenstein_specialFiberIdeal

attribute [local instance] AddSubgroup.torsionBy.zmodModule in
/-- **The closing step of Sections 0CEG and 0CEI.** Let `X̄ = X_k ×_k k̄` be the base change of the
special fibre to an algebraic closure of `k`, and let `ℓ` be a prime invertible in `k`. If `X̄` is
reduced and `dim_{F_ℓ} Pic(X̄)[ℓ] ≥ h¹(X̄, 𝒪_{X̄}) + g_geom(X̄)`, then the special fibre `X_k` has
at-worst-nodal singularities over `k`.

The two hypotheses `h0C20` and `h0C20eq` are the two halves of Tag 0C20 (the bound and the
equality criterion), stated as they are proved in the library; this lemma carries them as
premises only until that tag is available, the source's argument being: equality holds in the
bound, so every singular point of `X̄` is multicross (Tag 0C20); `X_k` is Gorenstein (Tag 0C60)
and so is `X̄` (Tag 0C03), so every multicross singularity of `X̄` is an ordinary double point
(Tag 0CDZ); and a closed point of `X_k` at which `X_k` is not smooth lies under such a point. -/
theorem hasAtWorstNodalSingularities_specialFiber_of_le_finrank
    (h0C20 : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [IsReduced X] (_hdim : topologicalKrullDim (X : Type u) = 1)
      (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ≤
          genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)))
    (h0C20eq : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IsReduced X]
      (_hdim : topologicalKrullDim (X : Type u) = 1) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        (Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) =
            genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)) ↔
          ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
            Stacks.Curves.IsMulticrossSingularity k X x))
    (hred : IsReduced (pullback S.specialFiberToSpec
      (Spec.map (CommRingCat.ofHom (algebraMap S.k (AlgebraicClosure S.k))))))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : S.k) ≠ 0)
    (hge : genus (pullback.snd S.specialFiberToSpec
        (Spec.map (CommRingCat.ofHom (algebraMap S.k (AlgebraicClosure S.k))))) +
      geometricGenus (AlgebraicClosure S.k) (pullback.snd S.specialFiberToSpec
        (Spec.map (CommRingCat.ofHom (algebraMap S.k (AlgebraicClosure S.k))))) ≤
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme (pullback
        S.specialFiberToSpec (Spec.map (CommRingCat.ofHom
          (algebraMap S.k (AlgebraicClosure S.k)))))) (ℓ : ℤ))) :
    letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
    Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber := by
  set a := Spec.map (CommRingCat.ofHom (algebraMap S.k (AlgebraicClosure S.k)))
  let : (pullback S.specialFiberToSpec a).Over (Spec (.of (AlgebraicClosure S.k))) :=
    ⟨pullback.snd S.specialFiberToSpec a⟩
  have : IsProper ((pullback S.specialFiberToSpec a) ↘ Spec (.of (AlgebraicClosure S.k))) :=
    inferInstanceAs (IsProper (pullback.snd S.specialFiberToSpec a))
  have : LocallyOfFiniteType
      ((pullback S.specialFiberToSpec a) ↘ Spec (.of (AlgebraicClosure S.k))) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd S.specialFiberToSpec a))
  have : IsGorenstein S.specialFiber := S.isGorenstein_specialFiber
  have : IsGorenstein (pullback S.specialFiberToSpec a) :=
    isGorenstein_pullback_specMap_algebraMap S.k (AlgebraicClosure S.k) S.specialFiberToSpec
  have hdim : topologicalKrullDim (pullback S.specialFiberToSpec a : Scheme.{u}) = 1 := by
    rw [topologicalKrullDim_baseChange S.k (AlgebraicClosure S.k) (pullback.fst _ _)
      (pullback.snd _ _) S.specialFiberToSpec (IsPullback.of_hasPullback _ _)]
    exact S.topologicalKrullDim_specialFiber S.nonempty_specialFiber
  have hℓ' : (ℓ : AlgebraicClosure S.k) ≠ 0 := by
    rw [← map_natCast (algebraMap S.k (AlgebraicClosure S.k))]
    exact (map_ne_zero _).2 hℓ
  have heq := le_antisymm
    (h0C20 (AlgebraicClosure S.k) (pullback S.specialFiberToSpec a) hdim ℓ hℓ').2 hge
  have hmult := ((h0C20eq (AlgebraicClosure S.k) (pullback S.specialFiberToSpec a) hdim ℓ
    hℓ').2).1 heq
  exact Stacks.Curves.hasAtWorstNodalSingularities_of_baseChange_algebraicClosure S.k
    S.specialFiberToSpec fun y _ hns => Stacks.Curves.isOrdinaryDoublePoint_of_not_smoothAt
      (AlgebraicClosure S.k) (pullback S.specialFiberToSpec a) hmult y hns

end RegularProperModelSituation

end Stacks.Models
